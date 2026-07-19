import JJMath.ComplexProjective.Prerequisites.RiemannSurface
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Subpath

/-!
# Simply connected covers

This file packages the universal-cover data needed for developing maps.  Mathlib
has covering-space and fundamental-groupoid infrastructure, but no project-level
universal-cover object tailored to our use case yet.
-/

namespace JJMath

open unitInterval
open scoped Topology

noncomputable section

namespace Homeomorph

variable {Y : Type*} [TopologicalSpace Y]

instance instOneSelf : One (Y ≃ₜ Y) where
  one := Homeomorph.refl Y

instance instMulSelf : Mul (Y ≃ₜ Y) where
  mul f g := g.trans f

/--
%%handwave
name:
  The identity homeomorphism fixes every point
statement:
  For every point \(y\in Y\), the identity self-homeomorphism satisfies
  \(\operatorname{id}_Y(y)=y\).
proof:
  This is the defining action of the identity homeomorphism.
-/
@[simp]
theorem one_apply (y : Y) : (1 : Y ≃ₜ Y) y = y :=
  rfl

/--
%%handwave
name:
  Multiplication of homeomorphisms acts by composition
statement:
  For self-homeomorphisms \(f,g\) of \(Y\) and \(y\in Y\), one has
  \((fg)(y)=f(g(y))\).
proof:
  Multiplication was defined as composition in this order, so the equality is
  immediate from the definition.
-/
@[simp]
theorem mul_apply (f g : Y ≃ₜ Y) (y : Y) : (f * g) y = f (g y) :=
  rfl

instance instMonoidSelf : Monoid (Y ≃ₜ Y) where
  mul_assoc _ _ _ := by
    ext y
    rfl
  one_mul _ := by
    ext y
    rfl
  mul_one _ := by
    ext y
    rfl
  npow n f :=
    { toEquiv :=
        ⟨f^[n], f.symm^[n], f.left_inv.iterate n, f.right_inv.iterate n⟩
      continuous_toFun := f.continuous_toFun.iterate n
      continuous_invFun := f.continuous_invFun.iterate n }
  npow_succ n f := by
    ext y
    exact Function.iterate_succ_apply (f := f) n y

end Homeomorph

/--
Concrete holomorphic local-section data for a covering projection.

For a lift `y`, this records a local inverse branch of the projection near
`projection y` and a coordinate expression for that branch in complex charts.
The derivative condition is the local-biholomorphism part needed when
descending projective developing branches from the cover to the base surface.
-/
structure CoverLocalHolomorphicSectionData
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (projection : Y → X) (y : Y) where
  /-- A local homeomorphism representing the projection near `y`. -/
  localProjection : OpenPartialHomeomorph Y X
  /-- The selected lift lies in the source of the local projection. -/
  mem_localProjection_source : y ∈ localProjection.source
  /-- The local homeomorphism is the covering projection on its source. -/
  localProjection_eq_projection : projection = localProjection
  /-- A base complex chart in which the local section is expressed. -/
  baseComplexChart : OpenPartialHomeomorph X ℂ
  /-- The base chart belongs to the base Riemann-surface atlas. -/
  baseComplexChart_mem_atlas : baseComplexChart ∈ atlas ℂ X
  /-- A total-space complex chart in which the local section is expressed. -/
  totalComplexChart : OpenPartialHomeomorph Y ℂ
  /-- The total-space chart is the canonical chart at the selected lift. -/
  totalComplexChart_eq_chartAt : totalComplexChart = chartAt ℂ y
  /-- The total chart belongs to the pulled-back complex atlas on the cover. -/
  totalComplexChart_mem_atlas : totalComplexChart ∈ atlas ℂ Y
  /-- The projected base point lies in the selected base chart. -/
  basepoint_mem_baseChart_source : projection y ∈ baseComplexChart.source
  /-- The lift lies in the selected total-space chart. -/
  lift_mem_totalChart_source : y ∈ totalComplexChart.source
  /-- Coordinate neighborhood on which the local section is represented. -/
  coordinateSource : Set ℂ
  /-- The coordinate neighborhood is open. -/
  coordinateSource_open : IsOpen coordinateSource
  /-- The coordinate neighborhood lies in the base chart target. -/
  coordinateSource_subset_baseChart_target :
    coordinateSource ⊆ baseComplexChart.target
  /-- The projected base point belongs to the coordinate neighborhood. -/
  basepoint_coordinate_mem :
    baseComplexChart (projection y) ∈ coordinateSource
  /-- Points in the coordinate neighborhood lie in the target of the local projection. -/
  coordinateSource_lands_in_localProjection_target :
    ∀ z ∈ coordinateSource, baseComplexChart.symm z ∈ localProjection.target
  /-- The lifted section lands in the chosen total-space complex chart. -/
  coordinateSource_lands_in_totalChart_source :
    ∀ z ∈ coordinateSource,
      localProjection.symm (baseComplexChart.symm z) ∈ totalComplexChart.source
  /-- Complex-coordinate expression of the local section. -/
  sectionCoordinate : ℂ → ℂ
  /-- The coordinate expression is the chosen local section in charts. -/
  sectionCoordinate_eq :
    ∀ z ∈ coordinateSource,
      sectionCoordinate z =
        totalComplexChart (localProjection.symm (baseComplexChart.symm z))
  /-- The local section is holomorphic in the chosen coordinates. -/
  sectionCoordinate_holomorphic :
    ∀ z ∈ coordinateSource, DifferentiableAt ℂ sectionCoordinate z
  /-- The local section has nonzero derivative in the chosen coordinates. -/
  sectionCoordinate_deriv_ne_zero :
    ∀ z ∈ coordinateSource, deriv sectionCoordinate z ≠ 0

namespace CoverLocalHolomorphicSectionData

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {projection : Y → X} {y : Y}

/--
%%handwave
name:
  The local projection agrees with the covering projection at its center
statement:
  For local holomorphic section data centered at \(y\), the chosen local
  projection sends \(y\) to the global projection of \(y\).
proof:
  Evaluate the stipulated equality between the global and local projections
  at \(y\).
-/
theorem localProjection_apply_lift
    (S : CoverLocalHolomorphicSectionData projection y) :
    S.localProjection y = projection y :=
  (congrFun S.localProjection_eq_projection y).symm

/--
%%handwave
name:
  The projected center lies in the local projection target
statement:
  If local section data are centered at \(y\), then the projected point
  \(\pi(y)\) belongs to the target of the chosen local projection.
proof:
  The center belongs to the source by assumption, hence its local-projection
  image belongs to the target; this image is \(\pi(y)\).
-/
theorem projection_lift_mem_localProjection_target
    (S : CoverLocalHolomorphicSectionData projection y) :
    projection y ∈ S.localProjection.target := by
  rw [← S.localProjection_apply_lift]
  exact S.localProjection.map_source S.mem_localProjection_source

/--
%%handwave
name:
  The local inverse recovers its center
statement:
  For local section data centered at \(y\), applying the inverse local
  projection to \(\pi(y)\) gives \(y\).
proof:
  Replace \(\pi(y)\) by the local projection of \(y\), then use the inverse
  law on the source of the local homeomorphism.
-/
theorem localProjection_symm_projection_lift
    (S : CoverLocalHolomorphicSectionData projection y) :
    S.localProjection.symm (projection y) = y := by
  rw [← S.localProjection_apply_lift]
  exact S.localProjection.left_inv S.mem_localProjection_source

/--
%%handwave
name:
  The local inverse section is a right inverse to the projection
statement:
  If \(x\) lies in the target of a chosen local projection, then its local
  inverse lift projects globally back to \(x\).
proof:
  Replace the global projection by the local projection at the inverse lift
  and apply the right-inverse law of the local homeomorphism.
-/
theorem projection_localProjection_symm
    (S : CoverLocalHolomorphicSectionData projection y)
    {x : X} (hx : x ∈ S.localProjection.target) :
    projection (S.localProjection.symm x) = x := by
  calc
    projection (S.localProjection.symm x) =
        S.localProjection (S.localProjection.symm x) := by
      exact congrFun S.localProjection_eq_projection (S.localProjection.symm x)
    _ = x := S.localProjection.right_inv hx

/--
%%handwave
name:
  Projection of the coordinate local section
statement:
  For \(z\) in the coordinate source, projecting the lift of the base-chart
  point \(z\) gives the inverse base-chart point itself:
  \[\pi\bigl(s(z)\bigr)=\varphi^{-1}(z).\]
proof:
  The coordinate-source hypothesis places \(\varphi^{-1}(z)\) in the target
  of the local projection, where the inverse section is a right inverse.
-/
theorem projection_section_coordinate_point
    (S : CoverLocalHolomorphicSectionData projection y)
    {z : ℂ} (hz : z ∈ S.coordinateSource) :
    projection (S.localProjection.symm (S.baseComplexChart.symm z)) =
      S.baseComplexChart.symm z :=
  S.projection_localProjection_symm
    (S.coordinateSource_lands_in_localProjection_target z hz)

/--
%%handwave
name:
  The section coordinate at the projected center
statement:
  For local section data centered at \(y\), evaluating the coordinate
  expression at the base coordinate of \(\pi(y)\) yields the canonical cover
  chart coordinate of \(y\).
proof:
  Expand the coordinate expression. The inverse base chart returns
  \(\pi(y)\), the inverse local projection returns \(y\), and the selected
  total chart is the canonical chart at \(y\).
-/
theorem sectionCoordinate_basepoint_eq_chartAt
    (S : CoverLocalHolomorphicSectionData projection y) :
    S.sectionCoordinate (S.baseComplexChart (projection y)) = chartAt ℂ y y := by
  rw [S.sectionCoordinate_eq _ S.basepoint_coordinate_mem]
  have hbase :
      S.baseComplexChart.symm (S.baseComplexChart (projection y)) = projection y :=
    S.baseComplexChart.left_inv S.basepoint_mem_baseChart_source
  calc
    S.totalComplexChart
        (S.localProjection.symm
          (S.baseComplexChart.symm (S.baseComplexChart (projection y)))) =
        S.totalComplexChart (S.localProjection.symm (projection y)) := by
      rw [hbase]
    _ = S.totalComplexChart y := by
      rw [S.localProjection_symm_projection_lift]
    _ = chartAt ℂ y y := by
      rw [S.totalComplexChart_eq_chartAt]

/--
%%handwave
name:
  Continuity of the coordinate local section
statement:
  The coordinate expression of a cover-local holomorphic section is
  continuous on its coordinate source.
proof:
  At every point of the source the expression is complex differentiable, and
  differentiability implies continuity there.
-/
theorem sectionCoordinate_continuousOn
    (S : CoverLocalHolomorphicSectionData projection y) :
    ContinuousOn S.sectionCoordinate S.coordinateSource := by
  intro z hz
  exact (S.sectionCoordinate_holomorphic z hz).continuousAt.continuousWithinAt

end CoverLocalHolomorphicSectionData

universe u

/--
The path-homotopy model underlying the universal cover based at `x₀`.

A point consists of an endpoint `x : X` together with a homotopy class of paths
from `x₀` to `x`.  The topology and local covering charts are supplied later;
this type records the algebraic total space on which those structures should be
built.
-/
def PathHomotopyUniversalCover (X : Type u) [TopologicalSpace X] (x₀ : X) : Type u :=
  Σ x : X, Path.Homotopic.Quotient x₀ x

namespace PathHomotopyUniversalCover

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

/-- The endpoint projection of the path-homotopy universal-cover model. -/
def endpoint (y : PathHomotopyUniversalCover X x₀) : X :=
  y.1

/-- The distinguished lift of the basepoint, represented by the constant path. -/
def baseLift (x₀ : X) : PathHomotopyUniversalCover X x₀ :=
  ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩

/--
%%handwave
name:
  The distinguished lift projects to the basepoint
statement:
  The endpoint of the constant-path class based at \(x_0\) is \(x_0\).
proof:
  The endpoint projection is the first component of the path-class pair, which
  is \(x_0\) by construction.
-/
@[simp]
theorem endpoint_baseLift (x₀ : X) :
    endpoint (baseLift x₀) = x₀ :=
  rfl

/-- A path-connected base gives an algebraic lift of every point. -/
noncomputable def liftOfPoint [PathConnectedSpace X] (x₀ x : X) :
    PathHomotopyUniversalCover X x₀ :=
  ⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)⟩

/--
%%handwave
name:
  A chosen path-class lift has the prescribed endpoint
statement:
  On a path-connected space, the chosen path-class lift of \(x\) based at
  \(x_0\) projects to \(x\).
proof:
  The lift is defined as the pair whose first component is \(x\).
-/
@[simp]
theorem endpoint_liftOfPoint [PathConnectedSpace X] (x₀ x : X) :
    endpoint (liftOfPoint x₀ x) = x :=
  rfl

/--
%%handwave
name:
  Surjectivity of the endpoint projection
statement:
  If \(X\) is path-connected, every \(x\in X\) is the endpoint of a based
  path-homotopy class, so the endpoint projection from the path-class cover is
  surjective.
proof:
  Choose a path from the basepoint to \(x\) and take its homotopy class. The
  associated lift has endpoint \(x\).
-/
theorem endpoint_surjective [PathConnectedSpace X] (x₀ : X) :
    Function.Surjective (endpoint : PathHomotopyUniversalCover X x₀ → X) :=
  fun x ↦ ⟨liftOfPoint x₀ x, rfl⟩

/-- The stored homotopy class of paths from the basepoint to the endpoint. -/
def pathClass (y : PathHomotopyUniversalCover X x₀) :
    Path.Homotopic.Quotient x₀ (endpoint y) :=
  y.2

/-- The initial segment of a path, from its source to the point reached at time `t`. -/
def initialSegment {x : X} (p : Path x₀ x) (t : I) : Path x₀ (p t) :=
  (p.truncateOfLE (show (0 : ℝ) ≤ (t : ℝ) from t.2.1)).cast
    (by exact (p.extend_zero).symm)
    (by exact (Path.extend_apply p t.2).symm)

/-- The algebraic lift of a path obtained by recording its initial path class. -/
def initialSegmentPoint {x : X} (p : Path x₀ x) (t : I) :
    PathHomotopyUniversalCover X x₀ :=
  ⟨p t, Path.Homotopic.Quotient.mk (initialSegment (x₀ := x₀) p t)⟩

/--
%%handwave
name:
  Endpoint of an initial-segment lift
statement:
  If \(p\) is a path from \(x_0\) and \(t\in[0,1]\), the lift represented by
  the initial segment \(p|_{[0,t]}\) projects to \(p(t)\).
proof:
  The endpoint of the initial-segment lift is defined to be \(p(t)\).
-/
@[simp]
theorem endpoint_initialSegmentPoint {x : X} (p : Path x₀ x) (t : I) :
    endpoint (initialSegmentPoint (x₀ := x₀) p t) = p t :=
  rfl

/-- The fiber of the endpoint projection over a point of the base. -/
def Fiber (x₀ x : X) : Type u :=
  {y : PathHomotopyUniversalCover X x₀ // endpoint y = x}

/-- The literal endpoint fiber is equivalent to the stored path-homotopy class. -/
def fiberPathClassEquiv (x : X) :
    Fiber x₀ x ≃ Path.Homotopic.Quotient x₀ x where
  toFun y := y.1.pathClass.cast rfl y.2.symm
  invFun q := ⟨⟨x, q⟩, rfl⟩
  left_inv y := by
    cases y with
    | mk y hy =>
        cases y with
        | mk b q =>
            dsimp [Fiber, endpoint] at hy
            subst b
            simp [pathClass, endpoint]
  right_inv q := by
    simp [pathClass, endpoint]

/--
%%handwave
name:
  Inverse of the fiber path-class equivalence
statement:
  For \(x\in X\) and a homotopy class \([q]\) of paths from \(x_0\) to
  \(x\), the inverse fiber equivalence returns the cover point \((x,[q])\),
  equipped with its evident endpoint equality.
proof:
  This is the defining formula for the inverse equivalence.
-/
@[simp]
theorem fiberPathClassEquiv_symm_apply (x : X)
    (q : Path.Homotopic.Quotient x₀ x) :
    (fiberPathClassEquiv (x₀ := x₀) x).symm q = ⟨⟨x, q⟩, rfl⟩ :=
  rfl

/-- A chosen path inside a path-connected subset, viewed as a path in the ambient space. -/
noncomputable def pathInSet {U : Set X} [PathConnectedSpace U] (a x : U) :
    Path (a : X) (x : X) :=
  (PathConnectedSpace.somePath a x).map continuous_subtype_val

/--
%%handwave
name:
  Concatenation of chosen paths in a simply connected set
statement:
  In a path-connected simply connected set \(U\), the homotopy class of the
  chosen path from \(a\) to \(b\), followed by the chosen path from \(b\) to
  \(x\), equals the class of the chosen path from \(a\) to \(x\).
proof:
  Concatenate the two paths inside \(U\). Simple connectedness makes this path
  homotopic relative endpoints to the chosen path from \(a\) to \(x\); mapping
  the homotopy into \(X\) gives the asserted equality of classes.
-/
theorem pathInSet_trans_eq_of_simplyConnected {U : Set X}
    [PathConnectedSpace U] [SimplyConnectedSpace U] (a b x : U) :
    Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk (pathInSet a b))
        (Path.Homotopic.Quotient.mk (pathInSet b x)) =
      Path.Homotopic.Quotient.mk (pathInSet a x) := by
  rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
  dsimp [pathInSet]
  rw [← Path.map_trans]
  exact (SimplyConnectedSpace.paths_homotopic
    ((PathConnectedSpace.somePath a b).trans (PathConnectedSpace.somePath b x))
    (PathConnectedSpace.somePath a x)).map
      ⟨Subtype.val, continuous_subtype_val⟩

/--
%%handwave
name:
  A chosen loop in a simply connected set is null-homotopic
statement:
  In a path-connected simply connected set \(U\), the chosen path from
  \(a\in U\) back to \(a\) represents the constant-path class in \(X\).
proof:
  Within \(U\), simple connectedness gives a homotopy between the chosen loop
  and the constant loop. Map that homotopy along the inclusion \(U\hookrightarrow X\).
-/
theorem pathInSet_self_eq_refl_of_simplyConnected {U : Set X}
    [PathConnectedSpace U] [SimplyConnectedSpace U] (a : U) :
    Path.Homotopic.Quotient.mk (pathInSet a a) =
      Path.Homotopic.Quotient.refl (a : X) := by
  change Path.Homotopic.Quotient.mk (pathInSet a a) =
    Path.Homotopic.Quotient.mk ((Path.refl a).map continuous_subtype_val)
  rw [Path.Homotopic.Quotient.eq]
  dsimp [pathInSet]
  exact (SimplyConnectedSpace.paths_homotopic
    (PathConnectedSpace.somePath a a) (Path.refl a)).map
      ⟨Subtype.val, continuous_subtype_val⟩

/--
%%handwave
name:
  Uniqueness of path classes inside a simply connected set
statement:
  Let \(a,b\in U\), where \(U\) is path-connected and simply connected. If a
  path \(\gamma\) from \(a\) to \(b\) stays in \(U\), then \(\gamma\) and the
  chosen path inside \(U\) determine the same homotopy class in \(X\).
proof:
  Regard \(\gamma\) as a path in the subtype \(U\). Simple connectedness gives
  a relative-endpoint homotopy to the chosen path, and inclusion into \(X\)
  preserves that homotopy.
-/
theorem pathInSet_eq_path_of_simplyConnected {U : Set X}
    [PathConnectedSpace U] [SimplyConnectedSpace U] (a b : U)
    (γ : Path (a : X) (b : X)) (hγU : Set.range γ ⊆ U) :
    Path.Homotopic.Quotient.mk (pathInSet a b) =
      Path.Homotopic.Quotient.mk γ := by
  rw [Path.Homotopic.Quotient.eq]
  let γU : Path a b :=
    { toFun := fun t => ⟨γ t, hγU ⟨t, rfl⟩⟩
      continuous_toFun := by
        exact Continuous.subtype_mk γ.continuous (fun t => hγU ⟨t, rfl⟩)
      source' := by
        apply Subtype.ext
        exact γ.source
      target' := by
        apply Subtype.ext
        exact γ.target }
  have h := (SimplyConnectedSpace.paths_homotopic
    (PathConnectedSpace.somePath a b) γU).map
      ⟨Subtype.val, continuous_subtype_val⟩
  simpa [pathInSet, γU] using h

/--
%%handwave
name:
  Reversal of a concatenated path class
statement:
  For composable path classes \(p:x\to y\) and \(q:y\to z\),
  \[(p\mathbin{*}q)^{-1}=q^{-1}\mathbin{*}p^{-1}.\]
proof:
  Represent both classes by paths and use the corresponding identity for
  reversal of concatenated paths.
-/
theorem quotient_symm_trans {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.trans p q) =
      Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.symm q)
        (Path.Homotopic.Quotient.symm p) := by
  induction p using Path.Homotopic.Quotient.ind
  induction q using Path.Homotopic.Quotient.ind
  rw [← Path.Homotopic.Quotient.mk_symm]
  rw [← Path.Homotopic.Quotient.mk_symm]
  rw [← Path.Homotopic.Quotient.mk_trans]
  rw [← Path.Homotopic.Quotient.mk_symm]
  rw [← Path.Homotopic.Quotient.mk_trans, Path.trans_symm]

/--
%%handwave
name:
  Left cancellation for path classes
statement:
  If \(p:x\to y\) is a path class and \(p*q=p*r\) for path classes
  \(q,r:y\to z\), then \(q=r\).
proof:
  Concatenate on the left with \(p^{-1}\), use associativity, and cancel
  \(p^{-1}*p\) to the constant class at \(y\).
-/
theorem quotient_trans_left_cancel {x y z : X}
    (p : Path.Homotopic.Quotient x y)
    {q r : Path.Homotopic.Quotient y z}
    (h : Path.Homotopic.Quotient.trans p q =
      Path.Homotopic.Quotient.trans p r) :
    q = r := by
  calc
    q = Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.refl y) q := by
      rw [Path.Homotopic.Quotient.refl_trans]
    _ = Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm p) p) q := by
      rw [Path.Homotopic.Quotient.symm_trans]
    _ = Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm p)
        (Path.Homotopic.Quotient.trans p q) := by
      rw [Path.Homotopic.Quotient.trans_assoc]
    _ = Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm p)
        (Path.Homotopic.Quotient.trans p r) := by
      rw [h]
    _ = Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm p) p) r := by
      rw [Path.Homotopic.Quotient.trans_assoc]
    _ = Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.refl y) r := by
      rw [Path.Homotopic.Quotient.symm_trans]
    _ = r := by
      rw [Path.Homotopic.Quotient.refl_trans]

/--
%%handwave
name:
  Right cancellation for path classes
statement:
  If \(q:y\to z\) is a path class and \(p*q=r*q\) for path classes
  \(p,r:x\to y\), then \(p=r\).
proof:
  Concatenate on the right with \(q^{-1}\), use associativity, and cancel
  \(q*q^{-1}\) to the constant class at \(y\).
-/
theorem quotient_trans_right_cancel {x y z : X}
    (q : Path.Homotopic.Quotient y z)
    {p r : Path.Homotopic.Quotient x y}
    (h : Path.Homotopic.Quotient.trans p q =
      Path.Homotopic.Quotient.trans r q) :
    p = r := by
  calc
    p = Path.Homotopic.Quotient.trans p (Path.Homotopic.Quotient.refl y) := by
      rw [Path.Homotopic.Quotient.trans_refl]
    _ = Path.Homotopic.Quotient.trans p
        (Path.Homotopic.Quotient.trans q (Path.Homotopic.Quotient.symm q)) := by
      rw [Path.Homotopic.Quotient.trans_symm]
    _ = Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.trans p q) (Path.Homotopic.Quotient.symm q) := by
      rw [Path.Homotopic.Quotient.trans_assoc]
    _ = Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.trans r q) (Path.Homotopic.Quotient.symm q) := by
      rw [h]
    _ = Path.Homotopic.Quotient.trans r
        (Path.Homotopic.Quotient.trans q (Path.Homotopic.Quotient.symm q)) := by
      rw [Path.Homotopic.Quotient.trans_assoc]
    _ = Path.Homotopic.Quotient.trans r (Path.Homotopic.Quotient.refl y) := by
      rw [Path.Homotopic.Quotient.trans_symm]
    _ = r := by
      rw [Path.Homotopic.Quotient.trans_refl]

/--
%%handwave
name:
  Transported constant path classes are constant
statement:
  If two endpoint identifications both identify \(x'\) with \(x\), then
  transporting the constant path class at \(x\) along them gives the constant
  path class at \(x'\).
proof:
  Substitute the two endpoint equalities; both transported classes then reduce
  definitionally to the same constant class.
-/
theorem quotient_refl_cast_eq {x x' : X} (hx hy : x' = x) :
    (Path.Homotopic.Quotient.refl x).cast hx hy =
      Path.Homotopic.Quotient.refl x' := by
  cases hx
  cases hy
  rfl

/--
%%handwave
name:
  Concatenating a transported constant path class
statement:
  Let \(q\) be a path class from \(a\) to \(b\), with alternate endpoint
  identifications \(a'=a\) and \(b'=b\). Concatenating \(q\) with the
  transported constant class at \(a'\) agrees, after endpoint transport, with
  \(q\) itself.
proof:
  Substitute both endpoint equalities and apply the left identity law for path
  concatenation.
-/
theorem quotient_refl_cast_trans_heq {a b a' b' : X}
    (q : Path.Homotopic.Quotient a b) (ha : a' = a) (hb : b' = b) :
    HEq
      (Path.Homotopic.Quotient.trans
        ((Path.Homotopic.Quotient.refl a').cast rfl ha.symm) q)
      (q.cast ha hb) := by
  cases ha
  cases hb
  simp

/--
%%handwave
name:
  Compatibility of chosen paths under inclusion
statement:
  Let \(W\subseteq U\), with \(U\) simply connected and both sets
  path-connected. For \(a,x\in W\), the chosen path from \(a\) to \(x\) in
  \(U\) and the chosen path in \(W\) represent the same path class in \(X\).
proof:
  Map the chosen path in \(W\) into \(U\). Simple connectedness of \(U\)
  makes it homotopic to the chosen path in \(U\), and inclusion into \(X\)
  preserves the homotopy.
-/
theorem pathInSet_eq_of_subset_simplyConnected {U W : Set X}
    [PathConnectedSpace U] [SimplyConnectedSpace U] [PathConnectedSpace W]
    (hWU : W ⊆ U) (a x : W) :
    Path.Homotopic.Quotient.mk
        (pathInSet (⟨(a : X), hWU a.2⟩ : U) ⟨(x : X), hWU x.2⟩) =
      Path.Homotopic.Quotient.mk (pathInSet a x) := by
  rw [Path.Homotopic.Quotient.eq]
  let i : W → U := fun y ↦ ⟨(y : X), hWU y.2⟩
  have hi : Continuous i := by
    continuity
  have h := (SimplyConnectedSpace.paths_homotopic
    (PathConnectedSpace.somePath (⟨(a : X), hWU a.2⟩ : U)
      ⟨(x : X), hWU x.2⟩)
    ((PathConnectedSpace.somePath a x).map hi)).map
      ⟨Subtype.val, continuous_subtype_val⟩
  simpa [pathInSet, i, Path.map_map] using h

/--
%%handwave
name:
  Cancellation of nested chosen paths
statement:
  Let \(W\subseteq U\), with \(U\) simply connected and both sets
  path-connected. For \(a\in U\) and \(b,x\in W\), following the chosen path
  \(a\to x\) in \(U\) by the reverse of the chosen path \(b\to x\) in \(W\)
  represents the chosen path \(a\to b\) in \(U\).
proof:
  Replace the path chosen in \(W\) by its equal class chosen in \(U\). The
  concatenation law for the three chosen paths, followed by cancellation of a
  path with its reverse, gives the result.
-/
theorem pathInSet_trans_subset_symm_eq_of_simplyConnected {U W : Set X}
    [PathConnectedSpace U] [SimplyConnectedSpace U] [PathConnectedSpace W]
    (hWU : W ⊆ U) (a : U) (b x : W) :
    Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk
          (pathInSet a ⟨(x : X), hWU x.2⟩))
        (Path.Homotopic.Quotient.symm
          (Path.Homotopic.Quotient.mk (pathInSet b x))) =
      Path.Homotopic.Quotient.mk
        (pathInSet a ⟨(b : X), hWU b.2⟩) := by
  have hcomp := pathInSet_trans_eq_of_simplyConnected
    (U := U) a ⟨(b : X), hWU b.2⟩ ⟨(x : X), hWU x.2⟩
  have hbx := pathInSet_eq_of_subset_simplyConnected
    (U := U) (W := W) hWU b x
  rw [← hcomp, ← hbx]
  rw [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl]

/--
The algebraic local trivialization over a path-connected subset.

Given a basepoint `a ∈ U`, a point of `endpoint ⁻¹' U` is sent to its endpoint
in `U` and the element of the fiber over `a` obtained by returning along the
chosen path in `U`.
-/
noncomputable def localTrivializationEquiv {U : Set X} [PathConnectedSpace U]
    (a : U) :
    {y : PathHomotopyUniversalCover X x₀ // endpoint y ∈ U} ≃
      U × Path.Homotopic.Quotient x₀ (a : X) where
  toFun y :=
    let x : U := ⟨endpoint y.1, y.2⟩
    let p : Path (a : X) (x : X) := pathInSet a x
    (x, Path.Homotopic.Quotient.trans y.1.pathClass
      (Path.Homotopic.Quotient.mk p.symm))
  invFun xp :=
    let p : Path (a : X) (xp.1 : X) := pathInSet a xp.1
    ⟨⟨xp.1, Path.Homotopic.Quotient.trans
      xp.2 (Path.Homotopic.Quotient.mk p)⟩, xp.1.2⟩
  left_inv y := by
    cases y with
    | mk y hyU =>
        cases y with
        | mk x q =>
            dsimp only [pathClass, endpoint]
            change
              (⟨⟨x, Path.Homotopic.Quotient.trans
                (Path.Homotopic.Quotient.trans q
                  (Path.Homotopic.Quotient.symm
                    (Path.Homotopic.Quotient.mk (pathInSet a ⟨x, hyU⟩))))
                (Path.Homotopic.Quotient.mk (pathInSet a ⟨x, hyU⟩))⟩, hyU⟩ :
                {y : PathHomotopyUniversalCover X x₀ // endpoint y ∈ U}) =
                ⟨⟨x, q⟩, hyU⟩
            rw [Path.Homotopic.Quotient.trans_assoc,
              Path.Homotopic.Quotient.symm_trans,
              Path.Homotopic.Quotient.trans_refl]
  right_inv xp := by
    rcases xp with ⟨x, q⟩
    dsimp only [pathClass, endpoint]
    change
      (⟨x, Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.trans q
          (Path.Homotopic.Quotient.mk (pathInSet a x)))
        (Path.Homotopic.Quotient.symm
          (Path.Homotopic.Quotient.mk (pathInSet a x)))⟩ :
        U × Path.Homotopic.Quotient x₀ (a : X)) = ⟨x, q⟩
    rw [Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.trans_refl]

/--
%%handwave
name:
  Base coordinate of the algebraic local trivialization
statement:
  The first coordinate of a lift \(y\) under the local trivialization over \(U\) is its endpoint, regarded as a point of \(U\).
proof:
  This is the first component in the definition of the trivialization.
-/
@[simp]
theorem localTrivializationEquiv_apply_fst {U : Set X} [PathConnectedSpace U]
    (a : U) (y : {y : PathHomotopyUniversalCover X x₀ // endpoint y ∈ U}) :
    ((localTrivializationEquiv (x₀ := x₀) a) y).1 =
      ⟨endpoint y.1, y.2⟩ :=
  rfl

/--
%%handwave
name:
  Endpoint of the inverse algebraic trivialization
statement:
  The lift reconstructed from \((x,q)\) by the local trivialization has endpoint \(x\).
proof:
  The inverse construction stores \(x\) as the endpoint index.
-/
@[simp]
theorem endpoint_localTrivializationEquiv_symm {U : Set X} [PathConnectedSpace U]
    (a : U) (xp : U × Path.Homotopic.Quotient x₀ (a : X)) :
    endpoint ((localTrivializationEquiv (x₀ := x₀) a).symm xp).1 = xp.1 :=
  rfl

/--
The same algebraic local trivialization, but with the fiber written as the
literal endpoint fiber.  This is the shape expected by mathlib's
`IsEvenlyCovered` API.
-/
noncomputable def localTrivializationFiberEquiv {U : Set X} [PathConnectedSpace U]
    (a : U) :
    {y : PathHomotopyUniversalCover X x₀ // endpoint y ∈ U} ≃
      U × Fiber x₀ (a : X) :=
  (localTrivializationEquiv (x₀ := x₀) a).trans
    (Equiv.prodCongr (Equiv.refl U) (fiberPathClassEquiv (x₀ := x₀) (a : X)).symm)

/--
%%handwave
name:
  Base coordinate of the fiber-valued local trivialization
statement:
  In the fiber-valued trivialization over \(U\), the first coordinate of \(y\) is its endpoint in \(U\).
proof:
  Rewriting the second factor as a literal endpoint fiber does not change the first coordinate.
-/
@[simp]
theorem localTrivializationFiberEquiv_apply_fst {U : Set X} [PathConnectedSpace U]
    (a : U) (y : {y : PathHomotopyUniversalCover X x₀ // endpoint y ∈ U}) :
    ((localTrivializationFiberEquiv (x₀ := x₀) a) y).1 =
      ⟨endpoint y.1, y.2⟩ :=
  rfl

/--
%%handwave
name:
  Endpoint of the inverse fiber-valued trivialization
statement:
  Reconstructing a lift from \((x,\eta)\) in the fiber-valued trivialization gives a point with endpoint \(x\).
proof:
  This follows from the corresponding inverse identity in path-class coordinates.
-/
@[simp]
theorem endpoint_localTrivializationFiberEquiv_symm {U : Set X} [PathConnectedSpace U]
    (a : U) (xp : U × Fiber x₀ (a : X)) :
    endpoint ((localTrivializationFiberEquiv (x₀ := x₀) a).symm xp).1 = xp.1 :=
  rfl

/--
%%handwave
name:
  Fiber coordinate of the fiber-valued trivialization
statement:
  The fiber coordinate of \(y\) is the endpoint-fiber point corresponding to its transported path class back to the center \(a\).
proof:
  The fiber-valued trivialization is obtained by postcomposing the path-class trivialization with the inverse fiber-to-path-class equivalence.
-/
@[simp]
theorem localTrivializationFiberEquiv_apply_snd {U : Set X} [PathConnectedSpace U]
    (a : U)
    (y : {y : PathHomotopyUniversalCover X x₀ // endpoint y ∈ U}) :
    ((localTrivializationFiberEquiv (x₀ := x₀) a) y).2 =
      (fiberPathClassEquiv (x₀ := x₀) (a : X)).symm
        (((localTrivializationEquiv (x₀ := x₀) a) y).2) :=
  rfl

/--
%%handwave
name:
  Path class of the local fiber label
statement:
  Converting the fiber label of a locally trivialized lift back to a path class recovers its transported path-class coordinate.
proof:
  The fiber label was defined using the inverse of this equivalence, so the two maps cancel.
-/
@[simp]
theorem fiberPathClassEquiv_localTrivializationFiberEquiv_snd
    {U : Set X} [PathConnectedSpace U] (a : U)
    (y : {y : PathHomotopyUniversalCover X x₀ // endpoint y ∈ U}) :
    (fiberPathClassEquiv (x₀ := x₀) (a : X))
      (((localTrivializationFiberEquiv (x₀ := x₀) a) y).2) =
        ((localTrivializationEquiv (x₀ := x₀) a) y).2 := by
  rw [localTrivializationFiberEquiv_apply_snd, Equiv.apply_symm_apply]

/--
Change of local-trivialization label after restricting from a simply connected
neighborhood `U` to a smaller path-connected neighborhood `W`.

%%handwave
name:
  Fiber labels under restriction of a simply connected trivialization
statement:
  Let \(W\subseteq U\), with \(U\) simply connected, and choose centers \(a\in U\), \(b\in W\). For a lift \(y\) over \(W\), its label at \(a\) is its label at \(b\), followed by the inverse of the chosen path from \(a\) to \(b\).
proof:
  Expand both labels as the stored path class of \(y\) followed by a return path. Simple connectedness identifies the return path in \(U\) with the return through \(b\), and associativity gives the formula.
-/
theorem localTrivializationFiberEquiv_subset_label
    {U W : Set X} [PathConnectedSpace U] [SimplyConnectedSpace U]
    [PathConnectedSpace W] (hWU : W ⊆ U) (a : U) (b : W)
    (y : PathHomotopyUniversalCover X x₀) (hyW : endpoint y ∈ W) :
    (fiberPathClassEquiv (x₀ := x₀) (a : X))
        (((localTrivializationFiberEquiv (x₀ := x₀) a)
          ⟨y, hWU hyW⟩).2) =
      Path.Homotopic.Quotient.trans
        ((fiberPathClassEquiv (x₀ := x₀) (b : X))
          (((localTrivializationFiberEquiv (x₀ := x₀) b)
            ⟨y, hyW⟩).2))
        (Path.Homotopic.Quotient.symm
          (Path.Homotopic.Quotient.mk
            (pathInSet a ⟨(b : X), hWU b.2⟩))) := by
  rw [fiberPathClassEquiv_localTrivializationFiberEquiv_snd]
  rw [fiberPathClassEquiv_localTrivializationFiberEquiv_snd]
  cases y with
  | mk x q =>
      dsimp [localTrivializationEquiv, pathClass, endpoint]
      have hpath := pathInSet_trans_eq_of_simplyConnected
        (U := U) a ⟨(b : X), hWU b.2⟩ ⟨x, hWU hyW⟩
      have hbx := pathInSet_eq_of_subset_simplyConnected
        (U := U) (W := W) hWU b ⟨x, hyW⟩
      have hsymm :
          Path.Homotopic.Quotient.symm
              (Path.Homotopic.Quotient.mk
                (pathInSet a ⟨x, hWU hyW⟩)) =
            Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.symm
                (Path.Homotopic.Quotient.mk
                  (pathInSet b ⟨x, hyW⟩)))
              (Path.Homotopic.Quotient.symm
                (Path.Homotopic.Quotient.mk
                  (pathInSet a ⟨(b : X), hWU b.2⟩))) := by
        rw [← hpath, ← hbx, quotient_symm_trans]
      change
        Path.Homotopic.Quotient.trans q
            (Path.Homotopic.Quotient.symm
              (Path.Homotopic.Quotient.mk
                (pathInSet a ⟨x, hWU hyW⟩))) =
          Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans q
              (Path.Homotopic.Quotient.symm
                (Path.Homotopic.Quotient.mk
                  (pathInSet b ⟨x, hyW⟩))))
            (Path.Homotopic.Quotient.symm
              (Path.Homotopic.Quotient.mk
                (pathInSet a ⟨(b : X), hWU b.2⟩)))
      rw [hsymm, Path.Homotopic.Quotient.trans_assoc]

/-- The sheet over `U` labelled by a chosen element of the fiber over `a`. -/
def localSheet {U : Set X} [PathConnectedSpace U]
    (a : U) (η : Fiber x₀ (a : X)) :
    Set (PathHomotopyUniversalCover X x₀) :=
  {y | ∃ hyU : endpoint y ∈ U,
    ((localTrivializationFiberEquiv (x₀ := x₀) a) ⟨y, hyU⟩).2 = η}

/-- The endpoint of a point in a local sheet lies in the base neighborhood.

%%handwave
name:
  A local-sheet point ends in the sheet base
statement:
  If \(y\) lies in the local sheet over \(U\) labelled at \(a\), then \(\operatorname{end}(y)\in U\).
proof:
  Membership in the local sheet includes this endpoint condition.
-/
theorem endpoint_mem_of_mem_localSheet {U : Set X} [PathConnectedSpace U]
    {a : U} {η : Fiber x₀ (a : X)}
    {y : PathHomotopyUniversalCover X x₀} (hy : y ∈ localSheet a η) :
    endpoint y ∈ U :=
  hy.choose

/--
Over a simply connected base neighborhood, the fiber label itself lies on the
local sheet it labels.

%%handwave
name:
  A sheet label lies in its own local sheet
statement:
  If \(U\) is simply connected and \(\eta\) is a lift over \(a\in U\), then the underlying lift \(\eta\) belongs to the local sheet over \(U\) labelled by \(\eta\).
proof:
  At \(a\), the return path is homotopic to the constant path. Thus the local-trivialization label of \(\eta\) is unchanged.
-/
theorem fiberPoint_mem_localSheet_of_simplyConnected
    {U : Set X} [PathConnectedSpace U] [SimplyConnectedSpace U]
    (a : U) (η : Fiber x₀ (a : X)) :
    η.1 ∈ localSheet a η := by
  have hηU : endpoint η.1 ∈ U := by
    rw [η.2]
    exact a.2
  refine ⟨hηU, ?_⟩
  apply (fiberPathClassEquiv (x₀ := x₀) (a : X)).injective
  rw [fiberPathClassEquiv_localTrivializationFiberEquiv_snd]
  cases η with
  | mk y hy =>
      cases y with
      | mk x q =>
          dsimp [Fiber, endpoint] at hy
          subst x
          have hpt : (⟨(a : X), hηU⟩ : U) = a := Subtype.ext rfl
          cases hpt
          dsimp [localTrivializationEquiv, fiberPathClassEquiv, pathClass, endpoint]
          change
            Path.Homotopic.Quotient.trans q
                (Path.Homotopic.Quotient.symm
                  (Path.Homotopic.Quotient.mk (pathInSet a a))) =
              q.cast _ _
          rw [pathInSet_self_eq_refl_of_simplyConnected]
          rw [show
              Path.Homotopic.Quotient.symm
                  (Path.Homotopic.Quotient.refl (a : X)) =
                Path.Homotopic.Quotient.refl (a : X) by rfl,
            Path.Homotopic.Quotient.trans_refl]
          simp

/--
Restrict a local sheet from a simply connected neighborhood `U` to a smaller
path-connected neighborhood `W`.  If the restricted sheet is labelled by a
point already on the original sheet, then it lies inside the original sheet.

%%handwave
name:
  Restricting a local sheet preserves sheet membership
statement:
  Let \(W\subseteq U\), with \(U\) simply connected. If \(y\) lies in a sheet \(S\) over \(U\), then the sheet over \(W\) through \(y\) is contained in \(S\).
proof:
  Compare the two local-trivialization labels using the restriction formula. Every point with the same \(W\)-label as \(y\) consequently has the same \(U\)-label, hence lies in \(S\).
-/
theorem localSheet_subset_of_subset_of_mem_localSheet
    {U W : Set X} [PathConnectedSpace U] [SimplyConnectedSpace U]
    [PathConnectedSpace W] (hWU : W ⊆ U)
    {a : U} {η : Fiber x₀ (a : X)}
    {y : PathHomotopyUniversalCover X x₀}
    (hyU : y ∈ localSheet a η) (hyW : endpoint y ∈ W) :
    localSheet (⟨endpoint y, hyW⟩ : W)
        (((localTrivializationFiberEquiv (x₀ := x₀)
          (⟨endpoint y, hyW⟩ : W)) ⟨y, hyW⟩).2) ⊆
      localSheet a η := by
  intro z hz
  rcases hyU with ⟨hyU_base, hy_label⟩
  rcases hz with ⟨hzW, hz_label⟩
  refine ⟨hWU hzW, ?_⟩
  have hy_label' :
      ((localTrivializationFiberEquiv (x₀ := x₀) a)
          ⟨y, hWU hyW⟩).2 = η := by
    convert hy_label
  apply (fiberPathClassEquiv (x₀ := x₀) (a : X)).injective
  calc
    (fiberPathClassEquiv (x₀ := x₀) (a : X))
        (((localTrivializationFiberEquiv (x₀ := x₀) a)
          ⟨z, hWU hzW⟩).2) =
        Path.Homotopic.Quotient.trans
          ((fiberPathClassEquiv (x₀ := x₀) (endpoint y))
            (((localTrivializationFiberEquiv (x₀ := x₀)
              (⟨endpoint y, hyW⟩ : W)) ⟨z, hzW⟩).2))
          (Path.Homotopic.Quotient.symm
            (Path.Homotopic.Quotient.mk
              (pathInSet a ⟨endpoint y, hWU hyW⟩))) := by
        exact localTrivializationFiberEquiv_subset_label
          (x₀ := x₀) hWU a (⟨endpoint y, hyW⟩ : W) z hzW
    _ =
        Path.Homotopic.Quotient.trans
          ((fiberPathClassEquiv (x₀ := x₀) (endpoint y))
            (((localTrivializationFiberEquiv (x₀ := x₀)
              (⟨endpoint y, hyW⟩ : W)) ⟨y, hyW⟩).2))
          (Path.Homotopic.Quotient.symm
            (Path.Homotopic.Quotient.mk
              (pathInSet a ⟨endpoint y, hWU hyW⟩))) := by
        rw [hz_label]
    _ =
        (fiberPathClassEquiv (x₀ := x₀) (a : X))
          (((localTrivializationFiberEquiv (x₀ := x₀) a)
            ⟨y, hWU hyW⟩).2) := by
        exact (localTrivializationFiberEquiv_subset_label
          (x₀ := x₀) hWU a (⟨endpoint y, hyW⟩ : W) y hyW).symm
    _ = (fiberPathClassEquiv (x₀ := x₀) (a : X)) η := by
        rw [hy_label']

/-- The local sheet section determined by the algebraic trivialization. -/
noncomputable def localSheetLift {U : Set X} [PathConnectedSpace U]
    (a : U) (η : Fiber x₀ (a : X)) (x : U) :
    PathHomotopyUniversalCover X x₀ :=
  ((localTrivializationFiberEquiv (x₀ := x₀) a).symm (x, η)).1

/--
%%handwave
name:
  Endpoint of the canonical local-sheet lift
statement:
  For \(x\in U\), the canonical lift of \(x\) in the sheet labelled by \(\eta\) has endpoint \(x\).
proof:
  It is reconstructed from the local-trivialization pair \((x,\eta)\).
-/
@[simp]
theorem endpoint_localSheetLift {U : Set X} [PathConnectedSpace U]
    (a : U) (η : Fiber x₀ (a : X)) (x : U) :
    endpoint (localSheetLift a η x) = x :=
  rfl

/--
%%handwave
name:
  Path class of the canonical local-sheet lift
statement:
  If \(\eta\) corresponds to a path class \([q]:x_0\to a\), then the
  canonical lift of \(x\in U\) in the sheet labelled by \(\eta\) has path
  class \([q*\sigma_{a,x}]\), where \(\sigma_{a,x}\) is the chosen path from
  \(a\) to \(x\) inside \(U\).
proof:
  Expand the inverse of the local trivialization: it concatenates the path
  class labelling the sheet with the chosen path inside \(U\).
-/
@[simp]
theorem pathClass_localSheetLift {U : Set X} [PathConnectedSpace U]
    (a : U) (η : Fiber x₀ (a : X)) (x : U) :
    pathClass (localSheetLift (x₀ := x₀) a η x) =
      Path.Homotopic.Quotient.trans
        ((fiberPathClassEquiv (x₀ := x₀) (a : X)) η)
        (Path.Homotopic.Quotient.mk (pathInSet a x)) :=
  rfl

/-- The local sheet section lands in its sheet.

%%handwave
name:
  The canonical local lift lands in its sheet
statement:
  For \(x\in U\), the canonical lift with fixed fiber label \(\eta\) lies in the local sheet labelled by \(\eta\).
proof:
  Applying the local trivialization to its inverse image of \((x,\eta)\) recovers exactly that pair, so the endpoint and label conditions hold.
-/
theorem localSheetLift_mem {U : Set X} [PathConnectedSpace U]
    (a : U) (η : Fiber x₀ (a : X)) (x : U) :
    localSheetLift a η x ∈ localSheet a η := by
  refine ⟨by simp [localSheetLift], ?_⟩
  exact congrArg Prod.snd
    ((localTrivializationFiberEquiv (x₀ := x₀) a).apply_symm_apply (x, η))

/-- A point of a local sheet is recovered from its endpoint by the sheet section.

%%handwave
name:
  A local-sheet point is determined by its endpoint
statement:
  If \(y\) lies in the sheet labelled by \(\eta\), then the canonical \(\eta\)-labelled lift of \(\operatorname{end}(y)\) is \(y\).
proof:
  The local trivialization sends \(y\) to \((\operatorname{end}(y),\eta)\); applying its inverse recovers \(y\).
-/
theorem localSheetLift_endpoint_eq {U : Set X} [PathConnectedSpace U]
    {a : U} {η : Fiber x₀ (a : X)}
    {y : PathHomotopyUniversalCover X x₀} (hy : y ∈ localSheet a η) :
    localSheetLift a η ⟨endpoint y, endpoint_mem_of_mem_localSheet hy⟩ = y := by
  rcases hy with ⟨hyU, hη⟩
  have hchart :
      (localTrivializationFiberEquiv (x₀ := x₀) a) ⟨y, hyU⟩ =
        (⟨endpoint y, hyU⟩, η) := by
    exact Prod.ext rfl hη
  have hsub :
      (localTrivializationFiberEquiv (x₀ := x₀) a).symm
          (⟨endpoint y, hyU⟩, η) = ⟨y, hyU⟩ := by
    rw [← hchart, Equiv.symm_apply_apply]
  exact congrArg Subtype.val hsub

/-- The endpoint projection is injective on each algebraic local sheet.

%%handwave
name:
  The endpoint map is injective on each local sheet
statement:
  If \(y,z\) lie in the same local sheet and have equal endpoints, then \(y=z\).
proof:
  Recover both points as the canonical sheet lift of their endpoint and use the endpoint equality.
-/
theorem localSheet_endpoint_injective {U : Set X} [PathConnectedSpace U]
    {a : U} {η : Fiber x₀ (a : X)}
    {y z : PathHomotopyUniversalCover X x₀}
    (hy : y ∈ localSheet a η) (hz : z ∈ localSheet a η)
    (hyz : endpoint y = endpoint z) :
    y = z := by
  rw [← localSheetLift_endpoint_eq hy, ← localSheetLift_endpoint_eq hz]
  congr

/-- The endpoint projection identifies each algebraic local sheet with `U`. -/
noncomputable def localSheetEndpointEquiv {U : Set X} [PathConnectedSpace U]
    (a : U) (η : Fiber x₀ (a : X)) :
    {y : PathHomotopyUniversalCover X x₀ // y ∈ localSheet a η} ≃ U where
  toFun y := ⟨endpoint y.1, endpoint_mem_of_mem_localSheet y.2⟩
  invFun x := ⟨localSheetLift a η x, localSheetLift_mem a η x⟩
  left_inv y := by
    exact Subtype.ext (localSheetLift_endpoint_eq y.2)
  right_inv x := by
    exact Subtype.ext rfl

/--
%%handwave
name:
  Endpoint equivalence on a local sheet
statement:
  The local-sheet endpoint equivalence sends a lift \(y\) to its endpoint in the base neighborhood.
proof:
  This is the forward map defining the equivalence.
-/
@[simp]
theorem localSheetEndpointEquiv_apply {U : Set X} [PathConnectedSpace U]
    (a : U) (η : Fiber x₀ (a : X))
    (y : {y : PathHomotopyUniversalCover X x₀ // y ∈ localSheet a η}) :
    localSheetEndpointEquiv a η y =
      ⟨endpoint y.1, endpoint_mem_of_mem_localSheet y.2⟩ :=
  rfl

/--
%%handwave
name:
  Inverse endpoint equivalence on a local sheet
statement:
  The inverse endpoint equivalence sends \(x\in U\) to the canonical lift of \(x\) in the chosen local sheet.
proof:
  This is the inverse map defining the equivalence.
-/
@[simp]
theorem localSheetEndpointEquiv_symm_apply {U : Set X} [PathConnectedSpace U]
    (a : U) (η : Fiber x₀ (a : X)) (x : U) :
    (localSheetEndpointEquiv a η).symm x =
      ⟨localSheetLift a η x, localSheetLift_mem a η x⟩ :=
  rfl

/--
A named algebraic sheet chart for the path-homotopy cover.

Adding topology later should amount to declaring these sheet charts to be the
local homeomorphism charts for the endpoint projection.
-/
structure LocalSheetChart (x₀ : X) where
  /-- The base neighborhood. -/
  base : Set X
  /-- The base neighborhood is open in `X`. -/
  base_open : IsOpen base
  /-- The base neighborhood is path connected, so the algebraic trivialization is available. -/
  [base_pathConnected : PathConnectedSpace base]
  /--
  The base neighborhood is simply connected.  This is stronger than the
  path-connectedness needed for the algebraic trivialization, and is the
  mathematical hypothesis used later to make continuation/local-sheet charts
  compatible on overlaps.
  -/
  [base_simplyConnected : SimplyConnectedSpace base]
  /-- A chosen point of the base neighborhood. -/
  center : base
  /-- The sheet label, i.e. an element of the fiber over `center`. -/
  fiberPoint : Fiber x₀ (center : X)

attribute [instance] LocalSheetChart.base_pathConnected
attribute [instance] LocalSheetChart.base_simplyConnected

namespace LocalSheetChart

variable {x₀ : X} (C : LocalSheetChart (X := X) x₀)

/-- The subset of the path-homotopy cover represented by a local sheet chart. -/
def sheet : Set (PathHomotopyUniversalCover X x₀) :=
  localSheet C.center C.fiberPoint

/-- The endpoint equivalence from the chart sheet to its base neighborhood. -/
noncomputable def endpointEquiv :
    {y : PathHomotopyUniversalCover X x₀ // y ∈ C.sheet} ≃ C.base :=
  localSheetEndpointEquiv C.center C.fiberPoint

/--
%%handwave
name:
  Endpoint chart of a named local sheet
statement:
  The endpoint equivalence of a named sheet chart sends a sheet point to its endpoint in the chart base.
proof:
  The named equivalence is the local-sheet endpoint equivalence.
-/
@[simp]
theorem endpointEquiv_apply
    (y : {y : PathHomotopyUniversalCover X x₀ // y ∈ C.sheet}) :
    C.endpointEquiv y =
      ⟨endpoint y.1, endpoint_mem_of_mem_localSheet y.2⟩ :=
  rfl

/--
%%handwave
name:
  Inverse endpoint chart of a named local sheet
statement:
  The inverse endpoint equivalence of a named sheet chart sends a base point to its canonical lift in that sheet.
proof:
  The named equivalence uses the canonical local-sheet lift as its inverse.
-/
@[simp]
theorem endpointEquiv_symm_apply (x : C.base) :
    C.endpointEquiv.symm x =
      ⟨localSheetLift C.center C.fiberPoint x,
        localSheetLift_mem C.center C.fiberPoint x⟩ :=
  rfl

end LocalSheetChart

/--
The sheet subsets used as subbasic opens for the path-homotopy cover topology.

For a sheet chart `C` and an open `V ⊆ X`, the basic open is the part of the
sheet whose endpoint lies in `V`.  Including these endpoint-restricted pieces,
rather than only the whole sheets, is what makes the endpoint map locally
continuous in the resulting topology.
-/
def localSheetChartSets (x₀ : X) : Set (Set (PathHomotopyUniversalCover X x₀)) :=
  {s | ∃ (C : LocalSheetChart (X := X) x₀) (V : Set X),
    IsOpen V ∧ s = C.sheet ∩ (endpoint (x₀ := x₀)) ⁻¹' V}

/--
The topology generated by local sheets over simply connected base neighborhoods.

This is the standard topology on the path-homotopy universal cover, expressed
in a form tailored to the continuation construction.
-/
instance instTopologicalSpace : TopologicalSpace (PathHomotopyUniversalCover X x₀) :=
  TopologicalSpace.generateFrom (localSheetChartSets (X := X) x₀)

instance instTopologicalSpaceFiber (x : X) : TopologicalSpace (Fiber x₀ x) := by
  dsimp [Fiber]
  infer_instance

/-- Every named local sheet chart is open in the generated cover topology.

%%handwave
name:
  Every named local sheet is open
statement:
  The sheet of every local sheet chart is open in the generated topology on the path-homotopy cover.
proof:
  It is one of the generating sets, obtained by restricting the sheet over the open set \(X\).
-/
theorem isOpen_localSheetChart_sheet (C : LocalSheetChart (X := X) x₀) :
    IsOpen C.sheet :=
  TopologicalSpace.isOpen_generateFrom_of_mem
    ⟨C, Set.univ, isOpen_univ, by ext y; simp⟩

/--
The part of a local sheet lying over an open subset of the base is open in the
generated cover topology.

%%handwave
name:
  Open restrictions of local sheets are open
statement:
  If \(C\) is a local sheet chart and \(V\subseteq X\) is open, then \(C\cap\operatorname{end}^{-1}(V)\) is open upstairs.
proof:
  This set is a generator of the path-homotopy cover topology.
-/
theorem isOpen_localSheetChart_sheet_inter_endpoint_preimage
    (C : LocalSheetChart (X := X) x₀) {V : Set X} (hV : IsOpen V) :
    IsOpen (C.sheet ∩ (endpoint (x₀ := x₀)) ⁻¹' V) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨C, V, hV, rfl⟩

/-- A local sheet chart containing a lift is a neighborhood of that lift.

%%handwave
name:
  A local sheet containing a lift is its neighborhood
statement:
  If \(y\) lies in a local sheet \(C\), then \(C\) is a neighborhood of \(y\).
proof:
  The sheet is open and contains \(y\).
-/
theorem localSheetChart_sheet_mem_nhds (C : LocalSheetChart (X := X) x₀)
    {y : PathHomotopyUniversalCover X x₀} (hy : y ∈ C.sheet) :
    C.sheet ∈ nhds y :=
  (isOpen_localSheetChart_sheet C).mem_nhds hy

/-- The preimage of a path-connected set is the union of its algebraic local sheets.

%%handwave
name:
  An endpoint preimage is the union of its local sheets
statement:
  For a path-connected set \(U\) and \(a\in U\), \(\operatorname{end}^{-1}(U)\) is the union of the local sheets indexed by the fiber over \(a\).
proof:
  Every lift over \(U\) has a unique fiber label under the local trivialization and belongs to its labelled sheet; conversely every labelled sheet lies over \(U\).
-/
theorem endpoint_preimage_eq_iUnion_localSheet {U : Set X} [PathConnectedSpace U]
    (a : U) :
    (endpoint (x₀ := x₀)) ⁻¹' U = ⋃ η : Fiber x₀ (a : X), localSheet a η := by
  ext y
  constructor
  · intro hyU
    exact Set.mem_iUnion_of_mem
      (((localTrivializationFiberEquiv (x₀ := x₀) a) ⟨y, hyU⟩).2)
      ⟨hyU, rfl⟩
  · intro hy
    rcases Set.mem_iUnion.mp hy with ⟨η, hη⟩
    exact endpoint_mem_of_mem_localSheet (x₀ := x₀) (a := a) (η := η) hη

/--
The endpoint preimage of the base of a local sheet chart is open in the
generated cover topology.

%%handwave
name:
  The endpoint preimage of a sheet base is open
statement:
  For every local sheet chart \(C\), \(\operatorname{end}^{-1}(C_{\mathrm{base}})\) is open upstairs.
proof:
  Decompose this preimage as the union of all sheets over the chart base, each of which is open.
-/
theorem isOpen_endpoint_preimage_localSheetChart_base
    (C : LocalSheetChart (X := X) x₀) :
    IsOpen ((endpoint (x₀ := x₀)) ⁻¹' C.base) := by
  rw [endpoint_preimage_eq_iUnion_localSheet C.center]
  refine isOpen_iUnion ?_
  intro η
  exact isOpen_localSheetChart_sheet { C with fiberPoint := η }

/--
Choose a local sheet chart around a lift whose base lies inside a prescribed
open neighborhood of its endpoint.
-/
noncomputable def localSheetChartAtWithin [LocallySimplyConnectedSpace X]
    (y : PathHomotopyUniversalCover X x₀) {N : Set X}
    (hyN : endpoint y ∈ N) (hN : IsOpen N) :
    LocalSheetChart (X := X) x₀ :=
  let W := SimplyConnectedOpenNeighborhood.choose hyN hN
  let center : W.carrier := ⟨endpoint y, W.mem_carrier⟩
  { base := W.carrier
    base_open := W.carrier_open
    base_pathConnected := W.carrier_pathConnected
    base_simplyConnected := W.carrier_simplyConnected
    center := center
    fiberPoint := ((localTrivializationFiberEquiv (x₀ := x₀) center)
      ⟨y, W.mem_carrier⟩).2 }

/-- The chosen local sheet chart around a lift contains that lift.

%%handwave
name:
  The chosen local sheet chart contains its lift
statement:
  If \(\operatorname{end}(y)\in N\) with \(N\) open, then the local sheet chart chosen around \(y\) inside \(N\) contains \(y\).
proof:
  Its fiber label is defined to be the local-trivialization label of \(y\), so the sheet-membership conditions hold directly.
-/
theorem localSheetChartAtWithin_mem [LocallySimplyConnectedSpace X]
    (y : PathHomotopyUniversalCover X x₀) {N : Set X}
    (hyN : endpoint y ∈ N) (hN : IsOpen N) :
    y ∈ (localSheetChartAtWithin (x₀ := x₀) y hyN hN).sheet := by
  dsimp [localSheetChartAtWithin, LocalSheetChart.sheet, localSheet]
  exact ⟨(SimplyConnectedOpenNeighborhood.choose hyN hN).mem_carrier, rfl⟩

/--
%%handwave
name:
  Center of the chosen local sheet chart
statement:
  The center of the local sheet chart chosen around \(y\) has underlying base point equal to the endpoint of \(y\).
proof:
  The chosen center is the endpoint of \(y\), equipped with membership in the chosen neighborhood.
-/
@[simp]
theorem localSheetChartAtWithin_center_coe [LocallySimplyConnectedSpace X]
    (y : PathHomotopyUniversalCover X x₀) {N : Set X}
    (hyN : endpoint y ∈ N) (hN : IsOpen N) :
    ((localSheetChartAtWithin (x₀ := x₀) y hyN hN).center : X) = endpoint y := by
  rfl

/-- The base of the chosen local sheet chart lies inside the prescribed open set.

%%handwave
name:
  The chosen sheet base lies in the prescribed neighborhood
statement:
  If the local sheet chart around \(y\) is chosen inside an open set \(N\), then its base is contained in \(N\).
proof:
  The base is the simply connected open neighborhood selected inside \(N\), whose construction records this inclusion.
-/
theorem localSheetChartAtWithin_base_subset [LocallySimplyConnectedSpace X]
    (y : PathHomotopyUniversalCover X x₀) {N : Set X}
    (hyN : endpoint y ∈ N) (hN : IsOpen N) :
    (localSheetChartAtWithin (x₀ := x₀) y hyN hN).base ⊆ N := by
  dsimp [localSheetChartAtWithin]
  exact (SimplyConnectedOpenNeighborhood.choose hyN hN).carrier_subset

/-- The sheet of the chosen local chart lies over the prescribed open set.

%%handwave
name:
  The chosen local sheet lies over the prescribed neighborhood
statement:
  If a local sheet chart around \(y\) is chosen inside \(N\), then every point of its sheet has endpoint in \(N\).
proof:
  A sheet point ends in the chart base, and that base is contained in \(N\).
-/
theorem localSheetChartAtWithin_sheet_subset_endpoint_preimage
    [LocallySimplyConnectedSpace X]
    (y : PathHomotopyUniversalCover X x₀) {N : Set X}
    (hyN : endpoint y ∈ N) (hN : IsOpen N) :
    (localSheetChartAtWithin (x₀ := x₀) y hyN hN).sheet ⊆
      (endpoint (x₀ := x₀)) ⁻¹' N := by
  intro z hz
  exact localSheetChartAtWithin_base_subset (x₀ := x₀) y hyN hN
    (endpoint_mem_of_mem_localSheet hz)

/-- Choose an unrestricted local sheet chart around a lift. -/
noncomputable def localSheetChartAt [LocallySimplyConnectedSpace X]
    (y : PathHomotopyUniversalCover X x₀) :
    LocalSheetChart (X := X) x₀ :=
  localSheetChartAtWithin (x₀ := x₀) y (by simp) isOpen_univ

/-- Every lift lies in some local sheet chart when the base is locally simply connected.

%%handwave
name:
  Every lift lies in a local sheet chart
statement:
  When \(X\) is locally simply connected, every point of the path-homotopy cover belongs to some local sheet chart.
proof:
  Choose a simply connected open neighborhood of its endpoint inside \(X\) and take the sheet through the lift.
-/
theorem exists_localSheetChart_mem [LocallySimplyConnectedSpace X]
    (y : PathHomotopyUniversalCover X x₀) :
    ∃ C : LocalSheetChart (X := X) x₀, y ∈ C.sheet :=
  ⟨localSheetChartAt (x₀ := x₀) y,
    localSheetChartAtWithin_mem (x₀ := x₀) y (by simp) isOpen_univ⟩

/--
The local sheet charts form a basis-like family: if two sheets meet at `y`,
there is a smaller chosen sheet around `y` contained in their intersection.

%%handwave
name:
  Local sheets refine their intersections
statement:
  If a lift \(y\) lies in local sheets \(C\) and \(D\), then there is a local sheet \(E\) containing \(y\) with \(E\subseteq C\cap D\).
proof:
  Choose a smaller simply connected base neighborhood inside the intersection of the two bases. The restricted sheet through \(y\) lies in each original sheet by restriction compatibility.
-/
theorem exists_localSheetChart_subset_inter_of_mem_inter [LocallySimplyConnectedSpace X]
    (C D : LocalSheetChart (X := X) x₀)
    {y : PathHomotopyUniversalCover X x₀}
    (hyC : y ∈ C.sheet) (hyD : y ∈ D.sheet) :
    ∃ E : LocalSheetChart (X := X) x₀,
      y ∈ E.sheet ∧ E.sheet ⊆ C.sheet ∩ D.sheet := by
  let N : Set X := C.base ∩ D.base
  have hN : IsOpen N := C.base_open.inter D.base_open
  have hyN : endpoint y ∈ N :=
    ⟨endpoint_mem_of_mem_localSheet hyC, endpoint_mem_of_mem_localSheet hyD⟩
  let E := localSheetChartAtWithin (x₀ := x₀) y hyN hN
  have hyE : y ∈ E.sheet :=
    localSheetChartAtWithin_mem (x₀ := x₀) y hyN hN
  refine ⟨E, hyE, ?_⟩
  have hyEbase : endpoint y ∈ E.base :=
    endpoint_mem_of_mem_localSheet hyE
  have hEbaseC : E.base ⊆ C.base := by
    intro x hx
    exact (localSheetChartAtWithin_base_subset (x₀ := x₀) y hyN hN hx).1
  have hEbaseD : E.base ⊆ D.base := by
    intro x hx
    exact (localSheetChartAtWithin_base_subset (x₀ := x₀) y hyN hN hx).2
  have hEC :
      localSheet (⟨endpoint y, hyEbase⟩ : E.base)
          (((localTrivializationFiberEquiv (x₀ := x₀)
            (⟨endpoint y, hyEbase⟩ : E.base)) ⟨y, hyEbase⟩).2) ⊆
        C.sheet :=
    localSheet_subset_of_subset_of_mem_localSheet
      (x₀ := x₀) (U := C.base) (W := E.base)
      hEbaseC (a := C.center) (η := C.fiberPoint)
      (y := y) hyC hyEbase
  have hED :
      localSheet (⟨endpoint y, hyEbase⟩ : E.base)
          (((localTrivializationFiberEquiv (x₀ := x₀)
            (⟨endpoint y, hyEbase⟩ : E.base)) ⟨y, hyEbase⟩).2) ⊆
        D.sheet :=
    localSheet_subset_of_subset_of_mem_localSheet
      (x₀ := x₀) (U := D.base) (W := E.base)
      hEbaseD (a := D.center) (η := D.fiberPoint)
      (y := y) hyD hyEbase
  intro z hzE
  have hzE' :
      z ∈ localSheet (⟨endpoint y, hyEbase⟩ : E.base)
          (((localTrivializationFiberEquiv (x₀ := x₀)
            (⟨endpoint y, hyEbase⟩ : E.base)) ⟨y, hyEbase⟩).2) := by
    simpa [E, localSheetChartAtWithin, LocalSheetChart.sheet] using hzE
  exact ⟨hEC hzE', hED hzE'⟩

/--
A chosen local sheet chart inside a base neighborhood contained in `C.base`
has its sheet contained in `C.sheet`, provided it is centred at a point already
lying on `C.sheet`.

%%handwave
name:
  A sufficiently small chosen sheet stays in a given sheet
statement:
  Suppose \(y\in C\), and choose a local sheet chart \(E\) through \(y\) whose base is contained in the base of \(C\). Then \(E\subseteq C\).
proof:
  The chosen chart \(E\) is the restricted local sheet through \(y\); the sheet-restriction theorem places it inside \(C\).
-/
theorem localSheetChartAtWithin_sheet_subset_of_mem_localSheet
    [LocallySimplyConnectedSpace X]
    (C : LocalSheetChart (X := X) x₀)
    {N : Set X} {y : PathHomotopyUniversalCover X x₀}
    (hyC : y ∈ C.sheet) (hyN : endpoint y ∈ N) (hN : IsOpen N)
    (hNC : (localSheetChartAtWithin (x₀ := x₀) y hyN hN).base ⊆ C.base) :
    (localSheetChartAtWithin (x₀ := x₀) y hyN hN).sheet ⊆ C.sheet := by
  let E := localSheetChartAtWithin (x₀ := x₀) y hyN hN
  have hyE : y ∈ E.sheet :=
    localSheetChartAtWithin_mem (x₀ := x₀) y hyN hN
  have hyEbase : endpoint y ∈ E.base :=
    endpoint_mem_of_mem_localSheet hyE
  have hsubset :
      localSheet (⟨endpoint y, hyEbase⟩ : E.base)
          (((localTrivializationFiberEquiv (x₀ := x₀)
            (⟨endpoint y, hyEbase⟩ : E.base)) ⟨y, hyEbase⟩).2) ⊆
        C.sheet :=
    localSheet_subset_of_subset_of_mem_localSheet
      (x₀ := x₀) (U := C.base) (W := E.base)
      hNC (a := C.center) (η := C.fiberPoint)
      (y := y) hyC hyEbase
  intro z hz
  apply hsubset
  simpa [E, localSheetChartAtWithin, LocalSheetChart.sheet] using hz

/--
Against every generated local-sheet open in the cover, the section of a fixed
local sheet has open preimage in the sheet base.

%%handwave
name:
  A local-sheet section has open preimages of restricted sheets
statement:
  For local sheet charts \(C,D\) and open \(V\subseteq X\), the set of \(x\in C_{\mathrm{base}}\) whose canonical \(C\)-lift lies in \(D\cap\operatorname{end}^{-1}(V)\) is open.
proof:
  Around any such \(x\), choose a smaller sheet through its lift with base inside \(C_{\mathrm{base}}\cap D_{\mathrm{base}}\cap V\). Injectivity of endpoint on \(C\) identifies the two local lifts, giving an open base neighborhood contained in the preimage.
-/
theorem isOpen_localSheetLift_preimage_localSheetChart_restrict
    [LocallySimplyConnectedSpace X]
    (C D : LocalSheetChart (X := X) x₀) {V : Set X} (hV : IsOpen V) :
    IsOpen {x : C.base |
      localSheetLift C.center C.fiberPoint x ∈
        D.sheet ∩ (endpoint (x₀ := x₀)) ⁻¹' V} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨hxD, hxV⟩
  let y : PathHomotopyUniversalCover X x₀ :=
    localSheetLift C.center C.fiberPoint x
  have hyC : y ∈ C.sheet :=
    localSheetLift_mem C.center C.fiberPoint x
  have hyD : y ∈ D.sheet := hxD
  let N : Set X := C.base ∩ D.base ∩ V
  have hN : IsOpen N := (C.base_open.inter D.base_open).inter hV
  have hyN : endpoint y ∈ N := by
    change (x : X) ∈ (C.base ∩ D.base) ∩ V
    exact ⟨⟨x.2, endpoint_mem_of_mem_localSheet hyD⟩, by simpa [y] using hxV⟩
  let E := localSheetChartAtWithin (x₀ := x₀) y hyN hN
  have hyE : y ∈ E.sheet :=
    localSheetChartAtWithin_mem (x₀ := x₀) y hyN hN
  have hEbaseN : E.base ⊆ N :=
    localSheetChartAtWithin_base_subset (x₀ := x₀) y hyN hN
  have hEbaseC : E.base ⊆ C.base := fun z hz => (hEbaseN hz).1.1
  have hEbaseD : E.base ⊆ D.base := fun z hz => (hEbaseN hz).1.2
  have hEbaseV : E.base ⊆ V := fun z hz => (hEbaseN hz).2
  have hEC : E.sheet ⊆ C.sheet :=
    localSheetChartAtWithin_sheet_subset_of_mem_localSheet
      (x₀ := x₀) C hyC hyN hN hEbaseC
  have hED : E.sheet ⊆ D.sheet :=
    localSheetChartAtWithin_sheet_subset_of_mem_localSheet
      (x₀ := x₀) D hyD hyN hN hEbaseD
  let O : Set C.base := {x' | (x' : X) ∈ E.base}
  have hOopen : IsOpen O := E.base_open.preimage continuous_subtype_val
  have hxO : x ∈ O := by
    exact endpoint_mem_of_mem_localSheet hyE
  refine Filter.mem_of_superset (hOopen.mem_nhds hxO) ?_
  intro x' hx'O
  have hx'C : (x' : X) ∈ C.base := x'.2
  have hx'E : (x' : X) ∈ E.base := hx'O
  let zE : PathHomotopyUniversalCover X x₀ :=
    localSheetLift E.center E.fiberPoint ⟨(x' : X), hx'E⟩
  have hzE : zE ∈ E.sheet :=
    localSheetLift_mem E.center E.fiberPoint ⟨(x' : X), hx'E⟩
  have hzEC : zE ∈ C.sheet := hEC hzE
  have hzED : zE ∈ D.sheet := hED hzE
  have hx'lift_eq :
      localSheetLift C.center C.fiberPoint x' = zE := by
    exact localSheet_endpoint_injective
      (localSheetLift_mem C.center C.fiberPoint x') hzEC (by simp [zE])
  refine ⟨?_, ?_⟩
  · rw [hx'lift_eq]
    exact hzED
  · simpa using hEbaseV hx'E

/--
Inside the base of `C`, the points whose `C`-sheet lift lies on the chosen
`D`-sheet form an open subset of the base overlap. This is the positive half
of local constancy of sheet labels.

%%handwave
name:
  Membership in another sheet is locally open on a base overlap
statement:
  For sheet charts \(C,D\), the set of \(x\in C_{\mathrm{base}}\cap D_{\mathrm{base}}\) whose \(C\)-sheet lift lies in \(D\) is open in \(C_{\mathrm{base}}\).
proof:
  Apply the restricted-sheet preimage result with the whole base space as the additional open set; endpoint membership supplies the base-overlap condition.
-/
theorem isOpen_localSheetLift_preimage_localSheetChart_sheet_restrict
    [LocallySimplyConnectedSpace X]
    (C D : LocalSheetChart (X := X) x₀) :
    IsOpen {x : C.base |
      (x : X) ∈ D.base ∧
        localSheetLift C.center C.fiberPoint x ∈ D.sheet} := by
  have hOpen :
      IsOpen {x : C.base |
        localSheetLift C.center C.fiberPoint x ∈
          D.sheet ∩ (endpoint (x₀ := x₀)) ⁻¹' Set.univ} :=
    isOpen_localSheetLift_preimage_localSheetChart_restrict
      (x₀ := x₀) C D isOpen_univ
  convert hOpen using 1
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, by simp⟩
  · intro hx
    exact ⟨endpoint_mem_of_mem_localSheet (x₀ := x₀) hx.1, hx.1⟩

/--
Inside the base of `C`, the points lying over `D.base` but not on the
chosen `D`-sheet form an open set.  Equivalently, the `D`-sheet label of the
`C`-sheet section is locally constant.

%%handwave
name:
  Nonmembership in another sheet is locally open on a base overlap
statement:
  For sheet charts \(C,D\), the set of \(x\in C_{\mathrm{base}}\cap D_{\mathrm{base}}\) whose \(C\)-sheet lift does not lie in \(D\) is open in \(C_{\mathrm{base}}\).
proof:
  At such a point, label the lift by its actual \(D\)-fiber coordinate; this label differs from \(D\)'s chosen label. The open set where the lift stays in the alternative labelled sheet cannot meet \(D\), so it lies in the complement.
-/
theorem isOpen_localSheetLift_preimage_localSheetChart_compl_restrict
    [LocallySimplyConnectedSpace X]
    (C D : LocalSheetChart (X := X) x₀) :
    IsOpen {x : C.base |
      (x : X) ∈ D.base ∧
        localSheetLift C.center C.fiberPoint x ∉ D.sheet} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨hxDbase, hxDsheet⟩
  let y : PathHomotopyUniversalCover X x₀ :=
    localSheetLift C.center C.fiberPoint x
  let η : Fiber x₀ (D.center : X) :=
    ((localTrivializationFiberEquiv (x₀ := x₀) D.center)
      ⟨y, by simpa [y] using hxDbase⟩).2
  let Dη : LocalSheetChart (X := X) x₀ := { D with fiberPoint := η }
  have hyDη : y ∈ Dη.sheet := by
    refine ⟨by simpa [y] using hxDbase, ?_⟩
    rfl
  have hη_ne : η ≠ D.fiberPoint := by
    intro hη
    apply hxDsheet
    simpa [Dη, LocalSheetChart.sheet, η, hη] using hyDη
  have hOpen :
      IsOpen {x' : C.base |
        localSheetLift C.center C.fiberPoint x' ∈
          Dη.sheet ∩ (endpoint (x₀ := x₀)) ⁻¹' Set.univ} :=
    isOpen_localSheetLift_preimage_localSheetChart_restrict
      (x₀ := x₀) C Dη isOpen_univ
  have hxOpen :
      x ∈ {x' : C.base |
        localSheetLift C.center C.fiberPoint x' ∈
          Dη.sheet ∩ (endpoint (x₀ := x₀)) ⁻¹' Set.univ} := by
    exact ⟨hyDη, by simp⟩
  refine Filter.mem_of_superset (hOpen.mem_nhds hxOpen) ?_
  intro x' hx'
  rcases hx' with ⟨hx'Dη, _⟩
  have hx'Dbase : (x' : X) ∈ D.base :=
    endpoint_mem_of_mem_localSheet (x₀ := x₀)
      (a := Dη.center) (η := Dη.fiberPoint) hx'Dη
  refine ⟨by simpa [Dη] using hx'Dbase, ?_⟩
  intro hx'D
  have hlabels : η = D.fiberPoint := by
    rcases hx'Dη with ⟨_, hηlabel⟩
    rcases hx'D with ⟨_, hDlabel⟩
    simpa [Dη] using hηlabel.symm.trans hDlabel
  exact hη_ne hlabels

/--
Sheet labels are constant on connected components of the base overlap.

If the `C`-sheet lift of a point of `C.base ∩ D.base` lies on the chosen
`D`-sheet, then the same is true for every point in the same connected
component of the base overlap.

%%handwave
name:
  Sheet labels are constant on connected components of a base overlap
statement:
  Let \(C,D\) be local sheets. If the \(C\)-lift of \(a\in C_{\mathrm{base}}\cap D_{\mathrm{base}}\) lies in \(D\), then the \(C\)-lift of every point in the same connected component of the base overlap also lies in \(D\).
proof:
  Within the overlap, membership and nonmembership in \(D\) are both open, so membership is clopen. A connected component meeting this clopen set is contained in it.
-/
theorem localSheetLift_mem_localSheetChart_of_mem_connectedComponentIn_base_inter
    [LocallySimplyConnectedSpace X]
    (C D : LocalSheetChart (X := X) x₀)
    {a x : C.base}
    (haD : (a : X) ∈ D.base)
    (haSheet : localSheetLift C.center C.fiberPoint a ∈ D.sheet)
    (hxComp :
      x ∈ connectedComponentIn {z : C.base | (z : X) ∈ D.base} a) :
    localSheetLift C.center C.fiberPoint x ∈ D.sheet := by
  classical
  let F : Set C.base := {z : C.base | (z : X) ∈ D.base}
  let A : Set F := {z : F |
    localSheetLift C.center C.fiberPoint z.1 ∈ D.sheet}
  have haF : a ∈ F := by
    simpa [F] using haD
  have hAopen : IsOpen A := by
    have hbase :
        IsOpen {z : C.base |
          (z : X) ∈ D.base ∧
            localSheetLift C.center C.fiberPoint z ∈ D.sheet} :=
      isOpen_localSheetLift_preimage_localSheetChart_sheet_restrict
        (x₀ := x₀) C D
    have hpre :
        IsOpen ((Subtype.val : F → C.base) ⁻¹'
          {z : C.base |
            (z : X) ∈ D.base ∧
              localSheetLift C.center C.fiberPoint z ∈ D.sheet}) :=
      hbase.preimage continuous_subtype_val
    convert hpre using 1
    ext z
    constructor
    · intro hz
      exact ⟨z.2, hz⟩
    · intro hz
      exact hz.2
  have hAcomplOpen : IsOpen Aᶜ := by
    have hbase :
        IsOpen {z : C.base |
          (z : X) ∈ D.base ∧
            localSheetLift C.center C.fiberPoint z ∉ D.sheet} :=
      isOpen_localSheetLift_preimage_localSheetChart_compl_restrict
        (x₀ := x₀) C D
    have hpre :
        IsOpen ((Subtype.val : F → C.base) ⁻¹'
          {z : C.base |
            (z : X) ∈ D.base ∧
              localSheetLift C.center C.fiberPoint z ∉ D.sheet}) :=
      hbase.preimage continuous_subtype_val
    convert hpre using 1
    ext z
    constructor
    · intro hz
      exact ⟨z.2, hz⟩
    · intro hz
      exact hz.2
  have hAclopen : IsClopen A :=
    ⟨⟨hAcomplOpen⟩, hAopen⟩
  have hsubset :
      connectedComponent (⟨a, haF⟩ : F) ⊆ A :=
    isPreconnected_connectedComponent.subset_isClopen hAclopen
      ⟨⟨a, haF⟩, mem_connectedComponent, by simpa [A] using haSheet⟩
  change x ∈ connectedComponentIn F a at hxComp
  rw [connectedComponentIn_eq_image haF] at hxComp
  rcases hxComp with ⟨z, hz, hz_eq⟩
  subst x
  exact hsubset hz

/-- The section of a local sheet is continuous for the generated cover topology.

%%handwave
name:
  The canonical section of a local sheet is continuous
statement:
  For every local sheet chart \(C\), the map sending a base point to its canonical lift in \(C\) is continuous.
proof:
  The cover topology is generated by endpoint-restricted local sheets. The preimage of every generator under the section is open by local constancy of sheet labels.
-/
theorem continuous_localSheetLift [LocallySimplyConnectedSpace X]
    (C : LocalSheetChart (X := X) x₀) :
    Continuous (fun x : C.base => localSheetLift C.center C.fiberPoint x) := by
  apply continuous_generateFrom_iff.mpr
  intro s hs
  rcases hs with ⟨D, V, hV, rfl⟩
  simpa [Set.preimage, endpoint_localSheetLift] using
    isOpen_localSheetLift_preimage_localSheetChart_restrict
      (x₀ := x₀) C D hV

/--
Connected components of base overlaps lift to connected components of sheet
overlaps, as long as both endpoint lifts are taken through the fixed `C`-sheet.

This is the covering-space form of the componentwise-overlap principle used by
the continuation construction: the only topological input is connectedness of
the relevant component in the base overlap.

%%handwave
name:
  Connected base overlaps lift to connected sheet overlaps
statement:
  Suppose \(y_1\in C\cap D\) and \(y\in C\). If the endpoint of \(y\) lies in the same connected component of the base overlap as the endpoint of \(y_1\), then \(y\) lies in the connected component of \(C\cap D\) containing \(y_1\).
proof:
  Lift the relevant base component continuously through the \(C\)-sheet. Sheet-label constancy puts its image inside \(D\), so the image is a preconnected subset of \(C\cap D\) containing both \(y_1\) and \(y\).
-/
theorem mem_connectedComponentIn_localSheetChart_inter_of_endpoint_mem_base_inter
    [LocallySimplyConnectedSpace X]
    (C D : LocalSheetChart (X := X) x₀)
    {y₁ y : PathHomotopyUniversalCover X x₀}
    (hy₁C : y₁ ∈ C.sheet) (hy₁D : y₁ ∈ D.sheet)
    (hyC : y ∈ C.sheet)
    (hbase :
      (⟨endpoint y, endpoint_mem_of_mem_localSheet hyC⟩ : C.base) ∈
        connectedComponentIn {z : C.base | (z : X) ∈ D.base}
          (⟨endpoint y₁, endpoint_mem_of_mem_localSheet hy₁C⟩ : C.base)) :
    y ∈ connectedComponentIn (C.sheet ∩ D.sheet) y₁ := by
  let a : C.base := ⟨endpoint y₁, endpoint_mem_of_mem_localSheet hy₁C⟩
  let x : C.base := ⟨endpoint y, endpoint_mem_of_mem_localSheet hyC⟩
  let F : Set C.base := {z : C.base | (z : X) ∈ D.base}
  let B : Set C.base := connectedComponentIn F a
  let f : C.base → PathHomotopyUniversalCover X x₀ :=
    fun z => localSheetLift C.center C.fiberPoint z
  have haF : a ∈ F := by
    simpa [a, F] using endpoint_mem_of_mem_localSheet (x₀ := x₀) hy₁D
  have haB : a ∈ B := by
    exact mem_connectedComponentIn haF
  have hy₁B : y₁ ∈ f '' B := by
    refine ⟨a, haB, ?_⟩
    simp [f, a, localSheetLift_endpoint_eq (x₀ := x₀) hy₁C]
  have hxB : x ∈ B := by
    simpa [x, a, B, F] using hbase
  have hyB : y ∈ f '' B := by
    refine ⟨x, hxB, ?_⟩
    simp [f, x, localSheetLift_endpoint_eq (x₀ := x₀) hyC]
  have hpre : IsPreconnected B :=
    isPreconnected_connectedComponentIn
  have himagePre : IsPreconnected (f '' B) :=
    hpre.image f (continuous_localSheetLift (x₀ := x₀) C).continuousOn
  have haSheet : f a ∈ D.sheet := by
    simpa [f, a, localSheetLift_endpoint_eq (x₀ := x₀) hy₁C] using hy₁D
  have hsubset : f '' B ⊆ C.sheet ∩ D.sheet := by
    intro z hz
    rcases hz with ⟨b, hbB, rfl⟩
    refine ⟨?_, ?_⟩
    · exact localSheetLift_mem C.center C.fiberPoint b
    · exact localSheetLift_mem_localSheetChart_of_mem_connectedComponentIn_base_inter
        (x₀ := x₀) C D
        (a := a) (x := b)
        (by simpa [a] using endpoint_mem_of_mem_localSheet (x₀ := x₀) hy₁D)
        (by simpa [f] using haSheet)
        (by simpa [B, F] using hbB)
  exact (himagePre.subset_connectedComponentIn hy₁B hsubset) hyB

/-- Endpoint preimages of open sets are open in the path-homotopy cover topology.

%%handwave
name:
  Endpoint preimages of open sets are open
statement:
  If \(V\subseteq X\) is open, then \(\operatorname{end}^{-1}(V)\) is open in the path-homotopy cover.
proof:
  For each lift over \(V\), choose a local sheet whose base lies inside \(V\). These open sheets cover exactly the endpoint preimage.
-/
theorem isOpen_endpoint_preimage_of_isOpen [LocallySimplyConnectedSpace X]
    {V : Set X} (hV : IsOpen V) :
    IsOpen ((endpoint (x₀ := x₀)) ⁻¹' V) := by
  classical
  rw [show
      (endpoint (x₀ := x₀)) ⁻¹' V =
        ⋃ y : {y : PathHomotopyUniversalCover X x₀ // endpoint y ∈ V},
          (localSheetChartAtWithin (x₀ := x₀) y.1 y.2 hV).sheet by
    ext z
    constructor
    · intro hzV
      exact Set.mem_iUnion_of_mem ⟨z, hzV⟩
        (localSheetChartAtWithin_mem (x₀ := x₀) z hzV hV)
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨y, hzy⟩
      exact localSheetChartAtWithin_sheet_subset_endpoint_preimage
        (x₀ := x₀) y.1 y.2 hV hzy]
  exact isOpen_iUnion fun y =>
    isOpen_localSheetChart_sheet (localSheetChartAtWithin (x₀ := x₀) y.1 y.2 hV)

/-- The endpoint projection is continuous for the generated path-homotopy cover topology.

%%handwave
name:
  The endpoint projection is continuous
statement:
  If \(X\) is locally simply connected, the endpoint map from the path-homotopy cover to \(X\) is continuous.
proof:
  The preimage of every open subset of \(X\) is open in the generated local-sheet topology.
-/
theorem continuous_endpoint [LocallySimplyConnectedSpace X] :
    Continuous (endpoint : PathHomotopyUniversalCover X x₀ → X) :=
  continuous_def.mpr fun _ hV => isOpen_endpoint_preimage_of_isOpen (x₀ := x₀) hV

/-- A local sheet, equipped with the endpoint map, is an open partial homeomorphism. -/
noncomputable def localSheetOpenPartialHomeomorph [LocallySimplyConnectedSpace X]
    (C : LocalSheetChart (X := X) x₀) :
    OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) X := by
  classical
  exact
  { toFun := endpoint
    invFun := fun x =>
      if hx : x ∈ C.base then
        localSheetLift C.center C.fiberPoint ⟨x, hx⟩
      else
        localSheetLift C.center C.fiberPoint C.center
    source := C.sheet
    target := C.base
    map_source' := fun _ hy => endpoint_mem_of_mem_localSheet hy
    map_target' := by
      intro x hx
      change
        (if hx' : x ∈ C.base then
          localSheetLift C.center C.fiberPoint ⟨x, hx'⟩
        else
          localSheetLift C.center C.fiberPoint C.center) ∈ C.sheet
      rw [dif_pos hx]
      exact localSheetLift_mem C.center C.fiberPoint ⟨x, hx⟩
    left_inv' := by
      intro y hy
      change
        (if hy' : endpoint y ∈ C.base then
          localSheetLift C.center C.fiberPoint ⟨endpoint y, hy'⟩
        else
          localSheetLift C.center C.fiberPoint C.center) = y
      rw [dif_pos (endpoint_mem_of_mem_localSheet hy)]
      exact localSheetLift_endpoint_eq hy
    right_inv' := by
      intro x hx
      change endpoint
        (if hx' : x ∈ C.base then
          localSheetLift C.center C.fiberPoint ⟨x, hx'⟩
        else
          localSheetLift C.center C.fiberPoint C.center) = x
      rw [dif_pos hx]
      rfl
    open_source := isOpen_localSheetChart_sheet C
    open_target := C.base_open
    continuousOn_toFun := continuous_endpoint.continuousOn
    continuousOn_invFun := by
      refine continuousOn_iff_continuous_restrict.mpr ?_
      convert continuous_localSheetLift (x₀ := x₀) C using 1
      ext x
      simp [Set.restrict] }

/-- The endpoint projection of the path-homotopy cover is a local homeomorphism.

%%handwave
name:
  The endpoint projection is a local homeomorphism
statement:
  If \(X\) is locally simply connected, the endpoint projection from the path-homotopy cover is a local homeomorphism.
proof:
  Every lift lies in a local sheet, and endpoint restricts there to the explicit homeomorphism onto its open simply connected base.
-/
theorem isLocalHomeomorph_endpoint [LocallySimplyConnectedSpace X] :
    IsLocalHomeomorph (endpoint : PathHomotopyUniversalCover X x₀ → X) := by
  intro y
  rcases exists_localSheetChart_mem (x₀ := x₀) y with ⟨C, hyC⟩
  exact ⟨localSheetOpenPartialHomeomorph (x₀ := x₀) C, hyC, rfl⟩

/-- Endpoint fibers are discrete in the generated path-homotopy cover topology.

%%handwave
name:
  Every endpoint fiber is discrete
statement:
  If \(X\) is locally simply connected, each fiber of the endpoint projection has the discrete topology.
proof:
  Around a fiber point choose a simply connected local sheet. Its intersection with the fiber is a singleton by injectivity of endpoint on the sheet, and that singleton is open as the pullback of the open sheet.
-/
theorem discreteTopology_fiber [LocallySimplyConnectedSpace X] (x : X) :
    DiscreteTopology (Fiber x₀ x) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro η
  let W := SimplyConnectedOpenNeighborhood.choose (x := x) (N := Set.univ)
    (by simp) isOpen_univ
  let a : W.carrier := ⟨x, W.mem_carrier⟩
  let C : LocalSheetChart (X := X) x₀ :=
    { base := W.carrier
      base_open := W.carrier_open
      base_pathConnected := W.carrier_pathConnected
      base_simplyConnected := W.carrier_simplyConnected
      center := a
      fiberPoint := η }
  have hηsheet : η.1 ∈ C.sheet := by
    simpa [C, LocalSheetChart.sheet] using
      (fiberPoint_mem_localSheet_of_simplyConnected (x₀ := x₀) a η)
  have hsingleton :
      ({η} : Set (Fiber x₀ x)) = Subtype.val ⁻¹' C.sheet := by
    ext ζ
    constructor
    · intro hζ
      rw [hζ]
      exact hηsheet
    · intro hζ
      apply Subtype.ext
      exact localSheet_endpoint_injective hζ hηsheet (by rw [ζ.2, η.2])
  rw [hsingleton]
  exact (isOpen_localSheetChart_sheet C).preimage continuous_subtype_val

/--
On a simply connected local sheet, openness in the base is equivalent to
openness after taking the corresponding sheetwise preimage.

%%handwave
name:
  Openness is reflected by restriction to a simply connected sheet
statement:
  Let \(U\) be open, path connected, and simply connected, let \(S\) be one local sheet over \(U\), and let \(W\subseteq U\). Then \(W\) is open in \(X\) if and only if \(\operatorname{end}^{-1}(W)\cap S\) is open in the path-homotopy cover.
proof:
  The forward implication is a generating local-sheet open. Conversely, the endpoint map restricts to a homeomorphism from \(S\) to \(U\), and the image of the upstairs open set is exactly \(W\).
-/
theorem isOpen_endpoint_preimage_inter_localSheet_iff
    [LocallySimplyConnectedSpace X]
    {U : Set X} [PathConnectedSpace U] [SimplyConnectedSpace U]
    (hU : IsOpen U) (a : U) (η : Fiber x₀ (a : X))
    {W : Set X} (hWU : W ⊆ U) :
    IsOpen W ↔
      IsOpen ((endpoint (x₀ := x₀)) ⁻¹' W ∩ localSheet a η) := by
  let C : LocalSheetChart (X := X) x₀ :=
    { base := U
      base_open := hU
      base_pathConnected := inferInstance
      base_simplyConnected := inferInstance
      center := a
      fiberPoint := η }
  constructor
  · intro hW
    simpa [C, LocalSheetChart.sheet, Set.inter_comm] using
      (isOpen_localSheetChart_sheet_inter_endpoint_preimage (x₀ := x₀) C hW)
  · intro hS
    let e := localSheetOpenPartialHomeomorph (x₀ := x₀) C
    have hsub :
        ((endpoint (x₀ := x₀)) ⁻¹' W ∩ localSheet a η) ⊆ e.source := by
      intro y hy
      simpa [e, C, LocalSheetChart.sheet] using hy.2
    have hopenImage : IsOpen (e '' ((endpoint (x₀ := x₀)) ⁻¹' W ∩ localSheet a η)) :=
      e.isOpen_image_of_subset_source hS hsub
    have himage :
        e '' ((endpoint (x₀ := x₀)) ⁻¹' W ∩ localSheet a η) = W := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy.1
      · intro hxW
        let xU : U := ⟨x, hWU hxW⟩
        refine ⟨localSheetLift a η xU, ?_, ?_⟩
        · exact ⟨by simpa [xU] using hxW, localSheetLift_mem a η xU⟩
        · rfl
    simpa [himage] using hopenImage

/-- The sheet decomposition over a chosen simply connected neighborhood as a bundle trivialization. -/
noncomputable def endpointTrivializationAt
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X] (x : X) :
    Bundle.Trivialization (Fiber x₀ x)
      (endpoint : PathHomotopyUniversalCover X x₀ → X) := by
  classical
  letI : Nonempty (X → PathHomotopyUniversalCover X x₀) :=
    ⟨fun z => liftOfPoint x₀ z⟩
  letI : Nonempty (Fiber x₀ x) := by
    rcases endpoint_surjective (X := X) x₀ x with ⟨y, hy⟩
    exact ⟨⟨y, hy⟩⟩
  haveI : DiscreteTopology (Fiber x₀ x) :=
    discreteTopology_fiber (x₀ := x₀) x
  let W := SimplyConnectedOpenNeighborhood.choose (x := x) (N := Set.univ)
    (by simp) isOpen_univ
  let a : W.carrier := ⟨x, W.mem_carrier⟩
  refine W.carrier_open.trivializationDiscrete
    (f := (endpoint : PathHomotopyUniversalCover X x₀ → X))
    (fun η : Fiber x₀ x => localSheet a η) W.carrier ?_ ?_ ?_ ?_ ?_
  · intro η S hSW
    exact isOpen_endpoint_preimage_inter_localSheet_iff
      (x₀ := x₀) W.carrier_open a η hSW
  · intro η y hy z hz hyz
    exact localSheet_endpoint_injective hy hz hyz
  · intro η z hz
    let zW : W.carrier := ⟨z, hz⟩
    exact ⟨localSheetLift a η zW, localSheetLift_mem a η zW, rfl⟩
  · intro η η' hne
    change Disjoint (localSheet a η) (localSheet a η')
    rw [Set.disjoint_left]
    intro y hy hy'
    rcases hy with ⟨hyW, hlabel⟩
    rcases hy' with ⟨hyW', hlabel'⟩
    apply hne
    have hlabel_same :
        ((localTrivializationFiberEquiv (x₀ := x₀) a) ⟨y, hyW'⟩).2 = η := by
      convert hlabel
    exact hlabel_same.symm.trans hlabel'
  · simpa using (endpoint_preimage_eq_iUnion_localSheet (x₀ := x₀) a).subset

/-- The selected point lies in the base set of the local endpoint trivialization.

%%handwave
name:
  The endpoint trivialization contains its center
statement:
  The point \(x\) belongs to the base set of the endpoint trivialization chosen at \(x\).
proof:
  The chosen simply connected open neighborhood used as the trivialization base contains its center by construction.
-/
theorem mem_baseSet_endpointTrivializationAt
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X] (x : X) :
    x ∈ (endpointTrivializationAt (x₀ := x₀) x).baseSet := by
  classical
  unfold endpointTrivializationAt
  exact (SimplyConnectedOpenNeighborhood.choose (x := x) (N := Set.univ)
    (by simp) isOpen_univ).mem_carrier

/-- The endpoint projection of the path-homotopy universal cover is a covering map.

%%handwave
name:
  The endpoint projection of the path-class cover is a covering map
statement:
  If \(X\) is path connected and locally simply connected, then the endpoint projection from based path-homotopy classes to \(X\) is a covering map.
proof:
  Around every \(x\), choose a simply connected open neighborhood. Its local sheets are pairwise disjoint, map injectively to the neighborhood, cover the full endpoint preimage, and furnish a discrete-fiber bundle trivialization.
-/
theorem isCoveringMap_endpoint
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X] :
    IsCoveringMap (endpoint : PathHomotopyUniversalCover X x₀ → X) := by
  classical
  letI : ∀ x : X, DiscreteTopology (Fiber x₀ x) :=
    fun x => discreteTopology_fiber (x₀ := x₀) x
  exact IsCoveringMap.mk
    (endpoint : PathHomotopyUniversalCover X x₀ → X)
    (fun x : X => Fiber x₀ x)
    (fun x : X => endpointTrivializationAt (x₀ := x₀) x)
    (fun x : X => mem_baseSet_endpointTrivializationAt (x₀ := x₀) x)

/-- Casting the endpoints of a base path does not change the underlying endpoint
of its lifted monodromy; it only changes the fiber type.

%%handwave
name:
  Changing endpoint types does not change the lifted monodromy point
statement:
  If a path-homotopy class is transported along equalities of its source and target and the starting fiber is transported accordingly, then the underlying endpoint of its monodromy lift is unchanged.
proof:
  After substituting the endpoint equalities, both monodromy expressions are definitionally the same.
-/
theorem monodromy_cast_apply_endpoint
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    {a b a' b' : X} (q : Path.Homotopic.Quotient a b)
    (ha : a' = a) (hb : b' = b)
    (η : (endpoint : PathHomotopyUniversalCover X x₀ → X) ⁻¹' {a'}) :
    ((isCoveringMap_endpoint (x₀ := x₀)).monodromy
        (q.cast ha hb) η).1 =
      ((isCoveringMap_endpoint (x₀ := x₀)).monodromy q
        ⟨η.1, by simpa [Set.mem_singleton_iff, ha] using η.2⟩).1 := by
  cases ha
  cases hb
  simp

/--
Local monodromy inside one simply connected sheet is given by the sheet lift of
the endpoint path.

%%handwave
name:
  Monodromy inside a simply connected neighborhood is the local-sheet lift
statement:
  Let \(\gamma\) be a path from \(a\) to \(b\) contained in an open simply connected set \(U\), and let \(\eta\) be a lift over \(a\). Then monodromy along \(\gamma\) ends at the canonical lift of \(b\) in the local sheet through \(\eta\).
proof:
  Lift \(\gamma\) pointwise using the local-sheet inverse. This is continuous, starts at \(\eta\), and projects to \(\gamma\); uniqueness of path lifting identifies it with the covering lift, whose endpoint gives the claim.
-/
theorem monodromy_localSheetLift
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    {U : Set X} [PathConnectedSpace U] [SimplyConnectedSpace U]
    (hU : IsOpen U) {a b : U} (η : Fiber x₀ (a : X))
    (γ : Path (a : X) (b : X)) (hγU : Set.range γ ⊆ U) :
    (isCoveringMap_endpoint (x₀ := x₀)).monodromy
        (Path.Homotopic.Quotient.mk γ)
        ⟨η.1, by simp⟩ =
      ⟨localSheetLift a η b, by
        simp [endpoint_localSheetLift]⟩ := by
  classical
  let γU : Path a b :=
    { toFun := fun t => ⟨γ t, hγU ⟨t, rfl⟩⟩
      continuous_toFun := by
        exact Continuous.subtype_mk γ.continuous (fun t => hγU ⟨t, rfl⟩)
      source' := by
        apply Subtype.ext
        exact γ.source
      target' := by
        apply Subtype.ext
        exact γ.target }
  let sheetChart : LocalSheetChart (X := X) x₀ :=
    { base := U
      base_open := hU
      base_pathConnected := inferInstance
      base_simplyConnected := inferInstance
      center := a
      fiberPoint := η }
  let Γ : ContinuousMap unitInterval (PathHomotopyUniversalCover X x₀) :=
    { toFun := fun t => localSheetLift a η (γU t)
      continuous_toFun := by
        exact (continuous_localSheetLift (x₀ := x₀) sheetChart).comp γU.continuous }
  have hηsheet : η.1 ∈ localSheet a η :=
    fiberPoint_mem_localSheet_of_simplyConnected (x₀ := x₀) a η
  have hΓ_zero : Γ 0 = η.1 := by
    change localSheetLift a η (γU 0) = η.1
    have hsource : γU 0 = a := γU.source
    rw [hsource]
    simpa [η.2] using localSheetLift_endpoint_eq (x₀ := x₀) hηsheet
  have hstart : γ 0 = endpoint η.1 :=
    γ.source.trans η.2.symm
  have hΓ_lift :
      Γ = (isCoveringMap_endpoint (x₀ := x₀)).liftPath γ η.1 hstart := by
    refine ((isCoveringMap_endpoint (x₀ := x₀)).eq_liftPath_iff'
      (γ := γ) (e := η.1) (γ_0 := hstart)).mpr ?_
    constructor
    · ext t
      simp [Γ, γU, endpoint_localSheetLift]
    · exact hΓ_zero
  apply Subtype.ext
  change
    (isCoveringMap_endpoint (x₀ := x₀)).liftPath γ η.1 hstart 1 =
      localSheetLift a η b
  rw [← hΓ_lift]
  change localSheetLift a η (γU 1) = localSheetLift a η b
  rw [γU.target]

/--
Local monodromy appends the homotopy class of a path contained in one simply
connected chart to the stored path class of the starting lift.

%%handwave
name:
  Local monodromy appends the path class
statement:
  For a path \(\gamma:a\to b\) contained in an open simply connected set and a lift represented by \(q:x_0\to a\), monodromy ends at the lift over \(b\) represented by \(q[\gamma]\).
proof:
  Monodromy is the local-sheet lift. In a simply connected neighborhood the chosen transport path from \(a\) to \(b\) is homotopic to \(\gamma\), so the stored class is \(q[\gamma]\).
-/
theorem monodromy_local_pathClass
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    {U : Set X} [PathConnectedSpace U] [SimplyConnectedSpace U]
    (hU : IsOpen U) {a b : U} (η : Fiber x₀ (a : X))
    (γ : Path (a : X) (b : X)) (hγU : Set.range γ ⊆ U) :
    (isCoveringMap_endpoint (x₀ := x₀)).monodromy
        (Path.Homotopic.Quotient.mk γ)
        ⟨η.1, by simp⟩ =
      ⟨⟨(b : X),
          Path.Homotopic.Quotient.trans
            ((fiberPathClassEquiv (x₀ := x₀) (a : X)) η)
            (Path.Homotopic.Quotient.mk γ)⟩, rfl⟩ := by
  classical
  have hmono :=
    monodromy_localSheetLift (x₀ := x₀) hU (a := a) (b := b) η γ hγU
  rw [hmono]
  apply Subtype.ext
  have hpath :
      Path.Homotopic.Quotient.mk (pathInSet a b) =
        Path.Homotopic.Quotient.mk γ :=
    pathInSet_eq_path_of_simplyConnected a b γ hγU
  change
    localSheetLift a η b =
      (⟨(b : X),
        Path.Homotopic.Quotient.trans
          ((fiberPathClassEquiv (x₀ := x₀) (a : X)) η)
          (Path.Homotopic.Quotient.mk γ)⟩ :
        PathHomotopyUniversalCover X x₀)
  change
    (⟨(b : X),
      Path.Homotopic.Quotient.trans
        ((fiberPathClassEquiv (x₀ := x₀) (a : X)) η)
        (Path.Homotopic.Quotient.mk (pathInSet a b))⟩ :
        PathHomotopyUniversalCover X x₀) =
      ⟨(b : X),
        Path.Homotopic.Quotient.trans
          ((fiberPathClassEquiv (x₀ := x₀) (a : X)) η)
          (Path.Homotopic.Quotient.mk γ)⟩
  rw [hpath]

/--
If a path from the basepoint stays inside one simply connected open set, its
monodromy from the base lift lands at the point storing exactly that path
class.

%%handwave
name:
  Local monodromy from the base lift records the path class
statement:
  If a path \(\gamma:x_0\to x\) lies in one open simply connected set containing \(x_0\), then monodromy along \(\gamma\) sends the constant-path lift to the cover point \((x,[\gamma])\).
proof:
  Apply the local-sheet monodromy formula. The starting fiber class is the constant path, and concatenating it with the chosen local path gives \([\gamma]\).
-/
theorem monodromy_baseLift_of_path_mem_simplyConnected
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    {U : Set X} [PathConnectedSpace U] [SimplyConnectedSpace U]
    (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    {x : X} (γ : Path x₀ x) (hγU : Set.range γ ⊆ U) :
    (isCoveringMap_endpoint (x₀ := x₀)).monodromy
        (Path.Homotopic.Quotient.mk γ)
        ⟨baseLift x₀, by simp⟩ =
      ⟨⟨x, Path.Homotopic.Quotient.mk γ⟩, rfl⟩ := by
  classical
  let a : U := ⟨x₀, hx₀U⟩
  have hxU : x ∈ U := by
    have hγ1 : γ 1 ∈ U := hγU ⟨1, rfl⟩
    simpa [γ.target] using hγ1
  let b : U := ⟨x, hxU⟩
  let η : Fiber x₀ (a : X) := ⟨baseLift x₀, rfl⟩
  have hmono :=
    monodromy_localSheetLift (x₀ := x₀) hU (a := a) (b := b) η γ hγU
  rw [hmono]
  apply Subtype.ext
  have hpath :
      Path.Homotopic.Quotient.mk (pathInSet a b) =
        Path.Homotopic.Quotient.mk γ :=
    pathInSet_eq_path_of_simplyConnected a b γ hγU
  have hηpath :
      ((fiberPathClassEquiv (x₀ := x₀) (a : X)) η) =
        Path.Homotopic.Quotient.refl x₀ := by
    dsimp [fiberPathClassEquiv, pathClass, baseLift, η, a]
    exact quotient_refl_cast_eq _ _
  change
    localSheetLift a η b =
      (⟨x, Path.Homotopic.Quotient.mk γ⟩ :
        PathHomotopyUniversalCover X x₀)
  change
    (⟨(b : X),
      Path.Homotopic.Quotient.trans
        ((fiberPathClassEquiv (x₀ := x₀) (a : X)) η)
        (Path.Homotopic.Quotient.mk (pathInSet a b))⟩ :
        PathHomotopyUniversalCover X x₀) =
      ⟨x, Path.Homotopic.Quotient.mk γ⟩
  simp [a, b, hpath, hηpath]

/--
Monodromy along a finite concatenation of paths, each contained in a simply
connected open set, appends the concatenated path class to the starting lift.

%%handwave
name:
  Monodromy along locally simple pieces appends their concatenation
statement:
  Let a finite chain of paths \(F_k:p_k\to p_{k+1}\) each lie in an open simply connected set. Starting from a lift represented by \(q:x_0\to p_0\), monodromy along their concatenation ends at \((p_n,q[F_0*\cdots*F_{n-1}])\).
proof:
  Induct on the number of pieces. The last step uses the local monodromy formula, while functoriality of monodromy and associativity of path-class concatenation combine it with the induction hypothesis.
-/
theorem monodromy_concat_local_pathClass
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    {n : ℕ} (p : Fin (n + 1) → X)
    (F : (k : Fin n) → Path (p k.castSucc) (p k.succ))
    (η : Fiber x₀ (p 0))
    (hF : ∀ k : Fin n, ∃ U : Set X, IsOpen U ∧
      Nonempty (PathConnectedSpace U) ∧ Nonempty (SimplyConnectedSpace U) ∧
        Set.range (F k) ⊆ U) :
    (isCoveringMap_endpoint (x₀ := x₀)).monodromy
        (Path.Homotopic.Quotient.mk (Path.concat p F))
        ⟨η.1, by simp⟩ =
      ⟨⟨p (Fin.last n),
          Path.Homotopic.Quotient.trans
            ((fiberPathClassEquiv (x₀ := x₀) (p 0)) η)
            (Path.Homotopic.Quotient.mk (Path.concat p F))⟩, rfl⟩ := by
  classical
  induction n with
  | zero =>
      rw [Path.concat_zero]
      change
        (isCoveringMap_endpoint (x₀ := x₀)).monodromy
            (Path.Homotopic.Quotient.refl (p 0)) ⟨η.1, by simp⟩ =
          ⟨⟨p 0,
              Path.Homotopic.Quotient.trans
                ((fiberPathClassEquiv (x₀ := x₀) (p 0)) η)
                (Path.Homotopic.Quotient.refl (p 0))⟩, rfl⟩
      rw [IsCoveringMap.monodromy_refl]
      apply Subtype.ext
      change
        η.1 =
        (⟨p 0,
          Path.Homotopic.Quotient.trans
            ((fiberPathClassEquiv (x₀ := x₀) (p 0)) η)
            (Path.Homotopic.Quotient.refl (p 0))⟩ :
          PathHomotopyUniversalCover X x₀)
      cases η with
      | mk y hy =>
          cases y with
          | mk x q =>
              dsimp [Fiber, endpoint] at hy
              subst x
              simp [fiberPathClassEquiv, pathClass, endpoint]
  | succ n ih =>
      let p' : Fin (n + 1) → X := p ∘ Fin.castSucc
      let F' : (k : Fin n) → Path (p' k.castSucc) (p' k.succ) :=
        fun k => F k.castSucc
      have hF' : ∀ k : Fin n, ∃ U : Set X, IsOpen U ∧
          Nonempty (PathConnectedSpace U) ∧ Nonempty (SimplyConnectedSpace U) ∧
            Set.range (F' k) ⊆ U := by
        intro k
        simpa [F'] using hF k.castSucc
      have ih' := ih p' F' η hF'
      let kLast : Fin (n + 1) := Fin.last n
      rcases hF kLast with ⟨U, hU, hUpc, hUsc, hFrange⟩
      letI : PathConnectedSpace U := hUpc.some
      letI : SimplyConnectedSpace U := hUsc.some
      let a : U := ⟨p kLast.castSucc, by
        have h0 : F kLast 0 ∈ U := hFrange ⟨0, rfl⟩
        simpa using h0⟩
      let b : U := ⟨p kLast.succ, by
        have h1 : F kLast 1 ∈ U := hFrange ⟨1, rfl⟩
        simpa using h1⟩
      let η' : Fiber x₀ (a : X) :=
        ⟨⟨(a : X),
            Path.Homotopic.Quotient.trans
              ((fiberPathClassEquiv (x₀ := x₀) (p 0)) η)
              (Path.Homotopic.Quotient.mk (Path.concat p' F'))⟩, by
          dsimp [endpoint, a]⟩
      have hstep :
          (isCoveringMap_endpoint (x₀ := x₀)).monodromy
              (Path.Homotopic.Quotient.mk (F kLast))
              ⟨η'.1, by
                change endpoint η'.1 = (a : X)
                exact η'.2⟩ =
            ⟨⟨(b : X),
                Path.Homotopic.Quotient.trans
                  ((fiberPathClassEquiv (x₀ := x₀) (a : X)) η')
                  (Path.Homotopic.Quotient.mk (F kLast))⟩, rfl⟩ :=
        monodromy_local_pathClass (x₀ := x₀) hU (a := a) (b := b) η'
          (F kLast) hFrange
      have hη'path :
          ((fiberPathClassEquiv (x₀ := x₀) (a : X)) η') =
            Path.Homotopic.Quotient.trans
              ((fiberPathClassEquiv (x₀ := x₀) (p 0)) η)
              (Path.Homotopic.Quotient.mk (Path.concat p' F')) := by
        dsimp [η', fiberPathClassEquiv, pathClass, endpoint]
        exact Path.Homotopic.Quotient.cast_rfl_rfl _
      rw [Path.concat_succ]
      change
        (isCoveringMap_endpoint (x₀ := x₀)).monodromy
            (Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.mk (Path.concat p' F'))
              (Path.Homotopic.Quotient.mk (F kLast))) ⟨η.1, by simp⟩ =
          ⟨⟨p (Fin.last (n + 1)),
              Path.Homotopic.Quotient.trans
                ((fiberPathClassEquiv (x₀ := x₀) (p 0)) η)
                (Path.Homotopic.Quotient.trans
                  (Path.Homotopic.Quotient.mk (Path.concat p' F'))
                  (Path.Homotopic.Quotient.mk (F kLast)))⟩, rfl⟩
      rw [IsCoveringMap.monodromy_trans_apply]
      rw [ih']
      change
        (isCoveringMap_endpoint (x₀ := x₀)).monodromy
            (Path.Homotopic.Quotient.mk (F kLast)) ⟨η'.1, by
              change endpoint η'.1 = (a : X)
              exact η'.2⟩ =
          ⟨⟨p (Fin.last (n + 1)),
              Path.Homotopic.Quotient.trans
                ((fiberPathClassEquiv (x₀ := x₀) (p 0)) η)
                (Path.Homotopic.Quotient.trans
                  (Path.Homotopic.Quotient.mk (Path.concat p' F'))
                  (Path.Homotopic.Quotient.mk (F kLast)))⟩, rfl⟩
      rw [hstep]
      apply Subtype.ext
      change
        (⟨(b : X),
            Path.Homotopic.Quotient.trans
              ((fiberPathClassEquiv (x₀ := x₀) (a : X)) η')
              (Path.Homotopic.Quotient.mk (F kLast))⟩ :
            PathHomotopyUniversalCover X x₀) =
          ⟨p (Fin.last (n + 1)),
            Path.Homotopic.Quotient.trans
              ((fiberPathClassEquiv (x₀ := x₀) (p 0)) η)
              (Path.Homotopic.Quotient.trans
                (Path.Homotopic.Quotient.mk (Path.concat p' F'))
                (Path.Homotopic.Quotient.mk (F kLast)))⟩
      simp [a, b, η', p', F', kLast, hη'path,
        Path.Homotopic.Quotient.trans_assoc]

/--
Every path admits a finite subdivision whose subpaths lie in simply connected
open neighborhoods.

%%handwave
name:
  Every path has a finite simply connected subdivision
statement:
  In a locally simply connected space, every path \(\gamma:[0,1]\to X\) admits a finite monotone subdivision such that each consecutive subpath is contained in an open path-connected simply connected set.
proof:
  Choose a simply connected open neighborhood around every point of the path. Their inverse images form an open cover of the compact unit interval; a finite monotone subdivision refines this cover.
-/
theorem exists_subdivision_subpaths_mem_simplyConnected
    [LocallySimplyConnectedSpace X] {x y : X} (γ : Path x y) :
    ∃ (m : ℕ) (t : Fin (m + 1) → unitInterval),
      t 0 = 0 ∧ t (Fin.last m) = 1 ∧
      (∀ k : Fin m, (t k.castSucc : ℝ) ≤ (t k.succ : ℝ)) ∧
      ∀ k : Fin m, ∃ U : Set X, IsOpen U ∧
        Nonempty (PathConnectedSpace U) ∧ Nonempty (SimplyConnectedSpace U) ∧
          Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U := by
  classical
  let W : (s : unitInterval) → SimplyConnectedOpenNeighborhood (X := X) (x := γ s) Set.univ :=
    fun s => SimplyConnectedOpenNeighborhood.choose (x := γ s) (N := Set.univ)
      (by simp) isOpen_univ
  let c : unitInterval → Set unitInterval := fun s => γ ⁻¹' (W s).carrier
  have hc_open : ∀ s, IsOpen (c s) := by
    intro s
    exact (W s).carrier_open.preimage γ.continuous
  have hc_cover : Set.univ ⊆ ⋃ s, c s := by
    intro r hr
    exact Set.mem_iUnion.mpr ⟨r, (W r).mem_carrier⟩
  obtain ⟨tNat, ht0, htmono, ⟨m, hm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := c) hc_open hc_cover
  let t : Fin (m + 1) → unitInterval := fun k => tNat k
  refine ⟨m, t, ?_, ?_, ?_, ?_⟩
  · exact ht0
  · exact hm m le_rfl
  · intro k
    exact htmono (Nat.le_succ k)
  · intro k
    rcases hsub k with ⟨s, hs⟩
    refine ⟨(W s).carrier, (W s).carrier_open,
      ⟨(W s).carrier_pathConnected⟩, ⟨(W s).carrier_simplyConnected⟩, ?_⟩
    rw [Path.range_subpath_of_le]
    · rintro z ⟨r, hr, rfl⟩
      exact hs hr
    · exact htmono (Nat.le_succ k)

/--
The path-homotopy class of a finite concatenation of subpaths of `γ` is the
class of the corresponding single subpath of `γ`.

%%handwave
name:
  Concatenated subpaths represent the total subpath
statement:
  For subdivision times \(t_0,\ldots,t_n\), the concatenation of the consecutive subpaths of \(\gamma\) represents the same homotopy class as the single subpath from \(t_0\) to \(t_n\).
proof:
  Use the standard homotopy that reparametrizes a finite concatenation of adjacent subpaths as the corresponding total subpath.
-/
theorem quotient_concat_subpath {x y : X} (γ : Path x y)
    {n : ℕ} (t : Fin (n + 1) → unitInterval) :
    Path.Homotopic.Quotient.mk
        (Path.concat (γ ∘ t)
          (fun k => γ.subpath (t k.castSucc) (t k.succ))) =
      Path.Homotopic.Quotient.mk
        (γ.subpath (t 0) (t (Fin.last n))) := by
  exact (Path.Homotopic.Quotient.eq).mpr
    (Path.Homotopic.concat_subpath γ t)

/-- A subpath from `0` to `1`, with endpoints cast back, has the original path class.

%%handwave
name:
  The full subpath represents the original path
statement:
  If \(t_0=0\) and \(t_1=1\), then after identifying endpoints, the homotopy class of \(\gamma|_{[t_0,t_1]}\) is \([\gamma]\).
proof:
  After the endpoint substitutions, the cast subpath is pointwise equal to \(\gamma\); hence their quotient classes agree.
-/
theorem quotient_subpath_zero_one_cast {x y : X} (γ : Path x y)
    {t₀ t₁ : unitInterval} (ht₀ : t₀ = 0) (ht₁ : t₁ = 1) :
    (Path.Homotopic.Quotient.mk (γ.subpath t₀ t₁)).cast
        (by rw [ht₀, γ.source])
        (by rw [ht₁, γ.target]) =
      Path.Homotopic.Quotient.mk γ := by
  rw [← Path.Homotopic.Quotient.mk_cast]
  apply (Path.Homotopic.Quotient.eq).mpr
  have hpath :
      (γ.subpath t₀ t₁).cast
          (by rw [ht₀, γ.source])
          (by rw [ht₁, γ.target]) = γ := by
    ext s
    simp [Path.subpath, ht₀, ht₁]
  rw [hpath]

/--
Monodromy of the path-homotopy cover from the base lift along an arbitrary
path records exactly that path class.

%%handwave
name:
  Monodromy from the base lift records any path
statement:
  For every path \(\gamma:x_0\to x\), monodromy sends the constant-path lift to the cover point \((x,[\gamma])\).
proof:
  Subdivide \(\gamma\) into pieces contained in simply connected neighborhoods and apply the finite-concatenation monodromy formula. The concatenated pieces represent the full path, including the endpoint identifications.
-/
theorem monodromy_baseLift_path
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    {x : X} (γ : Path x₀ x) :
    (isCoveringMap_endpoint (x₀ := x₀)).monodromy
        (Path.Homotopic.Quotient.mk γ)
        ⟨baseLift x₀, by simp⟩ =
      ⟨⟨x, Path.Homotopic.Quotient.mk γ⟩, rfl⟩ := by
  classical
  obtain ⟨m, t, ht0, htlast, _htmono, hlocal⟩ :=
    exists_subdivision_subpaths_mem_simplyConnected (X := X) γ
  let p : Fin (m + 1) → X := γ ∘ t
  let F : (k : Fin m) → Path (p k.castSucc) (p k.succ) :=
    fun k => γ.subpath (t k.castSucc) (t k.succ)
  have hp0 : x₀ = p 0 := by
    dsimp [p]
    rw [ht0, γ.source]
  have hplast : x = p (Fin.last m) := by
    dsimp [p]
    rw [htlast, γ.target]
  let η : Fiber x₀ (p 0) :=
    ⟨baseLift x₀, by
      simpa [endpoint_baseLift] using hp0⟩
  have hmono :=
    monodromy_concat_local_pathClass (x₀ := x₀) p F η hlocal
  have hq :
      (Path.Homotopic.Quotient.mk (Path.concat p F)).cast hp0 hplast =
        Path.Homotopic.Quotient.mk γ := by
    calc
      (Path.Homotopic.Quotient.mk (Path.concat p F)).cast hp0 hplast =
          (Path.Homotopic.Quotient.mk
            (γ.subpath (t 0) (t (Fin.last m)))).cast hp0 hplast := by
        exact congrArg (fun q => q.cast hp0 hplast)
          (quotient_concat_subpath γ t)
      _ = Path.Homotopic.Quotient.mk γ := by
        simpa [p, hp0, hplast] using
          (quotient_subpath_zero_one_cast γ ht0 htlast)
  have hcast :=
    monodromy_cast_apply_endpoint (x₀ := x₀)
      (q := Path.Homotopic.Quotient.mk (Path.concat p F))
      hp0 hplast
      (η := (⟨baseLift x₀, by simp⟩ :
        (endpoint : PathHomotopyUniversalCover X x₀ → X) ⁻¹' {x₀}))
  rw [hq] at hcast
  apply Subtype.ext
  change
    ((isCoveringMap_endpoint (x₀ := x₀)).monodromy
        (Path.Homotopic.Quotient.mk γ)
        ⟨baseLift x₀, by simp⟩).1 =
      (⟨x, Path.Homotopic.Quotient.mk γ⟩ :
        PathHomotopyUniversalCover X x₀)
  rw [hcast]
  have hmono_val := congrArg Subtype.val hmono
  change
    ((isCoveringMap_endpoint (x₀ := x₀)).monodromy
        (Path.Homotopic.Quotient.mk (Path.concat p F))
        ⟨η.1, by simp⟩).1 =
      (⟨x, Path.Homotopic.Quotient.mk γ⟩ :
        PathHomotopyUniversalCover X x₀)
  rw [hmono_val]
  dsimp [η]
  refine Sigma.ext hplast.symm ?_
  simpa [fiberPathClassEquiv, pathClass, baseLift, endpoint] using
    HEq.trans
      (quotient_refl_cast_trans_heq
        (q := Path.Homotopic.Quotient.mk (Path.concat p F)) hp0 hplast)
      (Eq.heq hq)

/-- Monodromy from the base lift along any path-homotopy class returns the
cover point storing that class.

%%handwave
name:
  Monodromy from the base lift records any path-homotopy class
statement:
  For every path-homotopy class \(q:x_0\to x\), monodromy along \(q\) sends the constant-path lift to \((x,q)\).
proof:
  Choose a path representative of \(q\) and apply the path-level monodromy formula.
-/
theorem monodromy_baseLift
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    {x : X} (q : Path.Homotopic.Quotient x₀ x) :
    (isCoveringMap_endpoint (x₀ := x₀)).monodromy q
        ⟨baseLift x₀, by simp⟩ =
      ⟨⟨x, q⟩, rfl⟩ := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk γ =>
      exact monodromy_baseLift_path (x₀ := x₀) γ

/-- The lifted representative path from the base lift to the cover point
storing that representative path class. -/
noncomputable def pathFromBaseLiftOfPath
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    {x : X} (γ : Path x₀ x) :
    Path (baseLift x₀)
      (⟨x, Path.Homotopic.Quotient.mk γ⟩ :
        PathHomotopyUniversalCover X x₀) := by
  classical
  let cov := isCoveringMap_endpoint (x₀ := x₀)
  let e0 : (endpoint : PathHomotopyUniversalCover X x₀ → X) ⁻¹' {x₀} :=
    ⟨baseLift x₀, by simp⟩
  let h0 : γ 0 = endpoint e0.1 := γ.source.trans e0.2.symm
  let Γ := cov.liftPath γ e0.1 h0
  refine
    { toFun := Γ
      continuous_toFun := Γ.continuous
      source' := ?_
      target' := ?_ }
  · exact cov.liftPath_zero γ e0.1 h0
  · have hmon := monodromy_baseLift_path (x₀ := x₀) γ
    simpa [cov, e0, h0, Γ, IsCoveringMap.monodromy] using
      congrArg Subtype.val hmon

/-- Every point of the path-homotopy cover is joined to the base lift.

%%handwave
name:
  Every point of the path-class cover is joined to the base lift
statement:
  For every cover point \((x,q)\), there exists a path upstairs from the constant-path lift to \((x,q)\).
proof:
  Choose a representative path \(\gamma\) of \(q\) and lift it from the base lift. The monodromy formula identifies the lifted endpoint with \((x,q)\).
-/
theorem exists_path_baseLift
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    (y : PathHomotopyUniversalCover X x₀) :
    Nonempty (Path (baseLift x₀) y) := by
  rcases y with ⟨x, q⟩
  induction q using Path.Homotopic.Quotient.ind with
  | mk γ =>
      exact ⟨pathFromBaseLiftOfPath (x₀ := x₀) γ⟩

/-- The path-homotopy universal cover is path connected. -/
noncomputable instance instPathConnectedSpace
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X] :
    PathConnectedSpace (PathHomotopyUniversalCover X x₀) where
  nonempty := ⟨baseLift x₀⟩
  joined y z := by
    rcases exists_path_baseLift (x₀ := x₀) y with ⟨γy⟩
    rcases exists_path_baseLift (x₀ := x₀) z with ⟨γz⟩
    exact ⟨γy.symm.trans γz⟩

/-- The projection of an upstairs path class is forced by the stored endpoint
path classes of its endpoints.

%%handwave
name:
  The projected class of an upstairs path is determined by its endpoints
statement:
  For an upstairs path class \(\alpha:y\to z\), its projection to \(X\) is \(y^{-1}z\), where \(y\) and \(z\) denote the stored based path classes of the two endpoints.
proof:
  Monodromy of the projected class carries \(y\) to \(z\). Prepend the stored class of \(y\), compare both resulting monodromies from the base lift, use the explicit base-lift formula, and cancel \(y\) on the left.
-/
theorem endpoint_map_pathClass_eq
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    {y z : PathHomotopyUniversalCover X x₀}
    (α : Path.Homotopic.Quotient y z) :
    α.map ⟨endpoint, continuous_endpoint (x₀ := x₀)⟩ =
      Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.symm y.pathClass) z.pathClass := by
  classical
  let cov := isCoveringMap_endpoint (x₀ := x₀)
  let endpointCM : C(PathHomotopyUniversalCover X x₀, X) :=
    ⟨endpoint, continuous_endpoint (x₀ := x₀)⟩
  have hmap :
      cov.monodromy (α.map endpointCM) ⟨y, rfl⟩ = ⟨z, rfl⟩ :=
    cov.monodromy_map α
  have htrans :
      cov.monodromy
          (Path.Homotopic.Quotient.trans y.pathClass (α.map endpointCM))
          ⟨baseLift x₀, by simp⟩ =
        cov.monodromy z.pathClass ⟨baseLift x₀, by simp⟩ := by
    rw [IsCoveringMap.monodromy_trans_apply]
    rw [monodromy_baseLift (x₀ := x₀) y.pathClass]
    rw [monodromy_baseLift (x₀ := x₀) z.pathClass]
    cases y
    simpa [pathClass, endpoint, cov, endpointCM] using hmap
  have hclasses :
      Path.Homotopic.Quotient.trans y.pathClass (α.map endpointCM) =
        z.pathClass := by
    have h := htrans
    rw [monodromy_baseLift (x₀ := x₀)
          (Path.Homotopic.Quotient.trans y.pathClass (α.map endpointCM)),
        monodromy_baseLift (x₀ := x₀) z.pathClass] at h
    have hv := congrArg Subtype.val h
    exact HEq.eq (Sigma.ext_iff.mp hv).2
  calc
    α.map endpointCM =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.refl (endpoint y)) (α.map endpointCM) := by
      rw [Path.Homotopic.Quotient.refl_trans]
    _ =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.symm y.pathClass) y.pathClass)
          (α.map endpointCM) := by
      rw [Path.Homotopic.Quotient.symm_trans]
    _ =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.symm y.pathClass)
          (Path.Homotopic.Quotient.trans y.pathClass (α.map endpointCM)) := by
      rw [Path.Homotopic.Quotient.trans_assoc]
    _ =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.symm y.pathClass) z.pathClass := by
      rw [hclasses]

/-- Path-homotopy classes between two fixed points upstairs are unique. -/
instance instPathHomotopicQuotientSubsingleton
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X]
    (y z : PathHomotopyUniversalCover X x₀) :
    Subsingleton (Path.Homotopic.Quotient y z) where
  allEq α β := by
    let cov := isCoveringMap_endpoint (x₀ := x₀)
    apply cov.injective_path_homotopic_map y z
    simp [endpoint_map_pathClass_eq (x₀ := x₀)]

/-- The path-homotopy universal cover is simply connected. -/
noncomputable instance instSimplyConnectedSpace
    [LocallySimplyConnectedSpace X] [PathConnectedSpace X] :
    SimplyConnectedSpace (PathHomotopyUniversalCover X x₀) := by
  rw [simply_connected_iff_paths_homotopic]
  exact ⟨inferInstance, fun y z => instPathHomotopicQuotientSubsingleton (x₀ := x₀) y z⟩

/-- A complex chart on the cover obtained by a local sheet chart followed by a base chart. -/
noncomputable def coverComplexChart [LocallySimplyConnectedSpace X]
    (C : LocalSheetChart (X := X) x₀)
    (e : OpenPartialHomeomorph X ℂ) :
    OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ :=
  (localSheetOpenPartialHomeomorph (x₀ := x₀) C).trans e

/-- The pulled-back complex charted structure on the path-homotopy cover. -/
noncomputable instance instChartedSpace
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X] :
    ChartedSpace ℂ (PathHomotopyUniversalCover X x₀) where
  atlas := {e | ∃ (C : LocalSheetChart (X := X) x₀)
      (baseChart : OpenPartialHomeomorph X ℂ),
      baseChart ∈ atlas ℂ X ∧ e = coverComplexChart (x₀ := x₀) C baseChart}
  chartAt y :=
    coverComplexChart (x₀ := x₀) (localSheetChartAt (x₀ := x₀) y)
      (chartAt ℂ (endpoint y))
  mem_chart_source y := by
    rw [coverComplexChart, OpenPartialHomeomorph.trans_source]
    exact ⟨localSheetChartAtWithin_mem (x₀ := x₀) y (by simp) isOpen_univ,
      by
        change endpoint y ∈ (chartAt ℂ (endpoint y)).source
        exact mem_chart_source ℂ (endpoint y)⟩
  chart_mem_atlas y := by
    exact ⟨localSheetChartAt (x₀ := x₀) y, chartAt ℂ (endpoint y),
      chart_mem_atlas ℂ (endpoint y), rfl⟩

/--
%%handwave
name:
  Canonical chart on the path-homotopy cover
statement:
  The canonical complex chart at a lift \(y\) is the local-sheet projection around \(y\), followed by the canonical base chart at its endpoint.
proof:
  This is the defining chart of the pulled-back complex atlas.
-/
@[simp]
theorem chartAt_pathHomotopyUniversalCover
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (y : PathHomotopyUniversalCover X x₀) :
    chartAt ℂ y =
      coverComplexChart (x₀ := x₀) (localSheetChartAt (x₀ := x₀) y)
        (chartAt ℂ (endpoint y)) :=
  rfl

/-- The local sheet chart chosen by an arbitrary chart in the pulled-back cover atlas. -/
noncomputable def sheetChartOfCoverChart
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ)
    (he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀)) :
    LocalSheetChart (X := X) x₀ :=
  Classical.choose he

/-- The base complex chart chosen by an arbitrary chart in the pulled-back cover atlas. -/
noncomputable def baseChartOfCoverChart
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ)
    (he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀)) :
    OpenPartialHomeomorph X ℂ :=
  Classical.choose (Classical.choose_spec he)

/-- The base chart extracted from a cover chart belongs to the base atlas.

%%handwave
name:
  The base chart underlying a cover chart belongs to the base atlas
statement:
  If \(e\) is a chart in the pulled-back atlas of the path-homotopy cover, then its extracted base chart is a chart of \(X\).
proof:
  Membership of \(e\) in the pulled-back atlas includes a base chart in the atlas of \(X\); take that chosen chart.
-/
theorem baseChartOfCoverChart_mem_atlas
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ)
    (he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀)) :
    baseChartOfCoverChart (x₀ := x₀) e he ∈ atlas ℂ X :=
  (Classical.choose_spec (Classical.choose_spec he)).1

/-- Every cover chart in the pulled-back atlas is a local sheet chart followed by a base chart.

%%handwave
name:
  Every cover chart is pulled back from a base chart on one sheet
statement:
  Every chart \(e\) in the pulled-back cover atlas factors as the endpoint homeomorphism on an evenly covered local sheet followed by an atlas chart of \(X\).
proof:
  This factorization is exactly the witness encoded by membership in the pulled-back atlas.
-/
theorem coverChart_eq_coverComplexChart
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ)
    (he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀)) :
    e =
      coverComplexChart (x₀ := x₀)
        (sheetChartOfCoverChart (x₀ := x₀) e he)
        (baseChartOfCoverChart (x₀ := x₀) e he) :=
  (Classical.choose_spec (Classical.choose_spec he)).2

/-- A point in a cover-chart target lies in the target of the extracted base chart.

%%handwave
name:
  The target of a cover chart lies in its base-chart target
statement:
  If \(z\) lies in the target of a pulled-back cover chart \(e\), then it lies in the target of the base chart underlying \(e\).
proof:
  Expand the cover chart as a composition of a local sheet projection with the base chart; the target of the composition is contained in the latter chart target.
-/
theorem coverChart_target_subset_baseChart_target
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ)
    (he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀)) {z : ℂ}
    (hz : z ∈ e.target) :
    z ∈ (baseChartOfCoverChart (x₀ := x₀) e he).target := by
  rw [coverChart_eq_coverComplexChart (x₀ := x₀) e he] at hz
  rw [coverComplexChart, OpenPartialHomeomorph.trans_target] at hz
  exact hz.1

/-- A point in a cover-chart source projects into the source of the extracted base chart.

%%handwave
name:
  A cover-chart source projects into its base-chart source
statement:
  If a lift \(y\) belongs to the source of a pulled-back cover chart \(e\), then its endpoint belongs to the source of the base chart underlying \(e\).
proof:
  Under the factorization of \(e\), source membership includes precisely this base-chart source condition.
-/
theorem coverChart_source_projection_mem_baseChart_source
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ)
    (he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀))
    {y : PathHomotopyUniversalCover X x₀} (hy : y ∈ e.source) :
    endpoint y ∈ (baseChartOfCoverChart (x₀ := x₀) e he).source := by
  rw [coverChart_eq_coverComplexChart (x₀ := x₀) e he] at hy
  rw [coverComplexChart, OpenPartialHomeomorph.trans_source] at hy
  exact hy.2

/-- A pulled-back cover chart is the extracted base chart applied after projection.

%%handwave
name:
  A pulled-back cover chart is the base chart after projection
statement:
  For a lift \(y\) in the source of a cover chart \(e\), \(e(y)=b(\operatorname{end}(y))\), where \(b\) is the base chart underlying \(e\).
proof:
  Replace \(e\) by its local-sheet factorization; the first map is the endpoint projection on that sheet.
-/
theorem coverChart_apply_eq_baseChart_apply_endpoint
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ)
    (he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀))
    {y : PathHomotopyUniversalCover X x₀} (_hy : y ∈ e.source) :
    e y = (baseChartOfCoverChart (x₀ := x₀) e he) (endpoint y) := by
  classical
  let C := sheetChartOfCoverChart (x₀ := x₀) e he
  let b := baseChartOfCoverChart (x₀ := x₀) e he
  have heq : e = coverComplexChart (x₀ := x₀) C b :=
    coverChart_eq_coverComplexChart (x₀ := x₀) e he
  change e y = b (endpoint y)
  calc
    e y = (coverComplexChart (x₀ := x₀) C b) y := by
      rw [heq]
    _ = b (endpoint y) := rfl

/-- The canonical cover chart is the base chart applied after endpoint projection.

%%handwave
name:
  The canonical cover chart is the endpoint chart after projection
statement:
  If \(y'\) lies in the canonical cover chart at \(y\), then \(\varphi_y(y')=\varphi_{\operatorname{end}(y)}(\operatorname{end}(y'))\).
proof:
  The canonical cover chart is defined as the local-sheet endpoint homeomorphism followed by the canonical base chart.
-/
theorem chartAt_apply_eq_chartAt_endpoint_apply
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (y y' : PathHomotopyUniversalCover X x₀)
    (_hy' : y' ∈ (chartAt ℂ y).source) :
    (chartAt ℂ y) y' = (chartAt ℂ (endpoint y)) (endpoint y') := by
  rw [chartAt_pathHomotopyUniversalCover (x₀ := x₀) y]
  rfl

/-- The inverse of a pulled-back cover chart projects to the inverse of its extracted base chart.

%%handwave
name:
  The inverse of a cover chart projects to the inverse base chart
statement:
  If \(z\) lies in the target of a cover chart \(e\) with underlying base chart \(b\), then \(\operatorname{end}(e^{-1}(z))=b^{-1}(z)\).
proof:
  Factor \(e\) through a local sheet. Its inverse first applies \(b^{-1}\) and then the unique local-sheet lift, whose endpoint is its base argument.
-/
theorem endpoint_coverChart_symm_eq_baseChart_symm
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ)
    (he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀)) {z : ℂ}
    (hz : z ∈ e.target) :
    endpoint (e.symm z) =
      (baseChartOfCoverChart (x₀ := x₀) e he).symm z := by
  classical
  let C := sheetChartOfCoverChart (x₀ := x₀) e he
  let b := baseChartOfCoverChart (x₀ := x₀) e he
  have heq : e = coverComplexChart (x₀ := x₀) C b :=
    coverChart_eq_coverComplexChart (x₀ := x₀) e he
  have hz0 : z ∈ (coverComplexChart (x₀ := x₀) C b).target := by
    simpa [heq] using hz
  have hz' : z ∈ b.target ∩ b.symm ⁻¹' C.base := by
    simpa [coverComplexChart, OpenPartialHomeomorph.trans_target, C, b] using hz0
  calc
    endpoint (e.symm z) =
        endpoint ((coverComplexChart (x₀ := x₀) C b).symm z) := by
      rw [heq]
    _ = b.symm z := by
      simp only [coverComplexChart, OpenPartialHomeomorph.coe_trans_symm,
        Function.comp_apply, localSheetOpenPartialHomeomorph]
      change endpoint
          (if hx : (b.symm z) ∈ C.base then
            localSheetLift C.center C.fiberPoint ⟨b.symm z, hx⟩
          else
            localSheetLift C.center C.fiberPoint C.center) =
        b.symm z
      have hbz : (b.symm z) ∈ C.base := by
        change z ∈ b.symm ⁻¹' C.base
        exact hz'.2
      rw [dif_pos hbz]
      rfl

/-- The inverse canonical cover chart projects to the inverse base chart.

%%handwave
name:
  The inverse canonical cover chart projects to the inverse endpoint chart
statement:
  If \(z\) lies in the target of the canonical chart at \(y\), then \(\operatorname{end}(\varphi_y^{-1}(z))=\varphi_{\operatorname{end}(y)}^{-1}(z)\).
proof:
  Specialize the local-sheet factorization of the canonical cover chart and use that its inverse lift has the prescribed endpoint.
-/
theorem endpoint_chartAt_symm_eq_chartAt_endpoint_symm
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (y : PathHomotopyUniversalCover X x₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ y).target) :
    endpoint ((chartAt ℂ y).symm z) =
      (chartAt ℂ (endpoint y)).symm z := by
  classical
  let C := localSheetChartAt (x₀ := x₀) y
  let b := chartAt ℂ (endpoint y)
  have hchart : chartAt ℂ y = coverComplexChart (x₀ := x₀) C b :=
    chartAt_pathHomotopyUniversalCover (x₀ := x₀) y
  have hz0 : z ∈ (coverComplexChart (x₀ := x₀) C b).target := by
    simpa [hchart] using hz
  have hz' : z ∈ b.target ∩ b.symm ⁻¹' C.base := by
    simpa [coverComplexChart, OpenPartialHomeomorph.trans_target, C, b] using hz0
  calc
    endpoint ((chartAt ℂ y).symm z) =
        endpoint ((coverComplexChart (x₀ := x₀) C b).symm z) := by
      rw [hchart]
    _ = b.symm z := by
      simp only [coverComplexChart, OpenPartialHomeomorph.coe_trans_symm,
        Function.comp_apply, localSheetOpenPartialHomeomorph]
      change endpoint
          (if hx : (b.symm z) ∈ C.base then
            localSheetLift C.center C.fiberPoint ⟨b.symm z, hx⟩
          else
            localSheetLift C.center C.fiberPoint C.center) =
        b.symm z
      have hbz : (b.symm z) ∈ C.base := by
        change z ∈ b.symm ⁻¹' C.base
        exact hz'.2
      rw [dif_pos hbz]
      rfl

/--
Near a point where two cover charts overlap, their coordinate change is the
same as the coordinate change of the extracted base charts.

%%handwave
name:
  Cover-chart transitions equal the corresponding base-chart transitions locally
statement:
  Let overlapping cover charts \(e,e'\) have underlying base charts \(b,b'\). Near an overlap point \(z\), \(e'\circ e^{-1}\) agrees with \(b'\circ b^{-1}\).
proof:
  On a neighborhood inside both chart domains, \(e'\) is \(b'\) after endpoint projection and the endpoint of \(e^{-1}(w)\) is \(b^{-1}(w)\). Combining the two identities gives equality of germs.
-/
theorem coverChart_transition_eventuallyEq_baseChart_transition
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph (PathHomotopyUniversalCover X x₀) ℂ)
    (he : e ∈ atlas ℂ (PathHomotopyUniversalCover X x₀))
    (he' : e' ∈ atlas ℂ (PathHomotopyUniversalCover X x₀)) {z : ℂ}
    (hz : z ∈ e.target) (hz' : e.symm z ∈ e'.source) :
    (fun w : ℂ => e' (e.symm w)) =ᶠ[nhds z]
      fun w : ℂ =>
        (baseChartOfCoverChart (x₀ := x₀) e' he')
          ((baseChartOfCoverChart (x₀ := x₀) e he).symm w) := by
  classical
  have htarget : e.target ∈ nhds z := e.open_target.mem_nhds hz
  have hsource : e.symm ⁻¹' e'.source ∈ nhds z :=
    (e.continuousAt_symm hz).preimage_mem_nhds (e'.open_source.mem_nhds hz')
  filter_upwards [htarget, hsource] with w hwt hws
  have hendpoint :
      endpoint (e.symm w) =
        (baseChartOfCoverChart (x₀ := x₀) e he).symm w :=
    endpoint_coverChart_symm_eq_baseChart_symm (x₀ := x₀) e he hwt
  calc
    e' (e.symm w) =
        (baseChartOfCoverChart (x₀ := x₀) e' he')
          (endpoint (e.symm w)) := by
      exact coverChart_apply_eq_baseChart_apply_endpoint (x₀ := x₀) e' he' hws
    _ =
        (baseChartOfCoverChart (x₀ := x₀) e' he')
          ((baseChartOfCoverChart (x₀ := x₀) e he).symm w) := by
      rw [hendpoint]

/-- The endpoint projection has holomorphic local inverse sections in the pulled-back atlas. -/
noncomputable def localHolomorphicSectionData
    [LocallySimplyConnectedSpace X] [ChartedSpace ℂ X]
    (y : PathHomotopyUniversalCover X x₀) :
    CoverLocalHolomorphicSectionData
      (endpoint : PathHomotopyUniversalCover X x₀ → X) y := by
  classical
  let C := localSheetChartAt (x₀ := x₀) y
  let localProjection := localSheetOpenPartialHomeomorph (x₀ := x₀) C
  let baseChart := chartAt ℂ (endpoint y)
  let totalChart := chartAt ℂ y
  refine
  { localProjection := localProjection
    mem_localProjection_source := by
      exact localSheetChartAtWithin_mem (x₀ := x₀) y (by simp) isOpen_univ
    localProjection_eq_projection := by
      rfl
    baseComplexChart := baseChart
    baseComplexChart_mem_atlas := chart_mem_atlas ℂ (endpoint y)
    totalComplexChart := totalChart
    totalComplexChart_eq_chartAt := rfl
    totalComplexChart_mem_atlas := chart_mem_atlas ℂ y
    basepoint_mem_baseChart_source := mem_chart_source ℂ (endpoint y)
    lift_mem_totalChart_source := mem_chart_source ℂ y
    coordinateSource := totalChart.target
    coordinateSource_open := totalChart.open_target
    coordinateSource_subset_baseChart_target := ?_
    basepoint_coordinate_mem := ?_
    coordinateSource_lands_in_localProjection_target := ?_
    coordinateSource_lands_in_totalChart_source := ?_
    sectionCoordinate := id
    sectionCoordinate_eq := ?_
    sectionCoordinate_holomorphic := ?_
    sectionCoordinate_deriv_ne_zero := ?_ }
  · intro z hz
    have hz' :
        z ∈ (coverComplexChart (x₀ := x₀) C baseChart).target := by
      simpa [totalChart, C, baseChart] using hz
    rw [coverComplexChart, OpenPartialHomeomorph.trans_target] at hz'
    exact hz'.1
  · simpa [totalChart, baseChart, chartAt_pathHomotopyUniversalCover,
      coverComplexChart, OpenPartialHomeomorph.trans_apply,
      localProjection, localSheetOpenPartialHomeomorph] using
      (mem_chart_target ℂ y)
  · intro z hz
    have hz' :
        z ∈ (coverComplexChart (x₀ := x₀) C baseChart).target := by
      simpa [totalChart, C, baseChart] using hz
    rw [coverComplexChart, OpenPartialHomeomorph.trans_target] at hz'
    simpa [localProjection, baseChart] using hz'.2
  · intro z hz
    have hzsource := totalChart.map_target hz
    simpa [totalChart, chartAt_pathHomotopyUniversalCover, coverComplexChart,
      localProjection, baseChart] using hzsource
  · intro z hz
    simpa [totalChart, chartAt_pathHomotopyUniversalCover, coverComplexChart,
      localProjection, baseChart] using (totalChart.right_inv hz).symm
  · intro z hz
    exact differentiableAt_id
  · intro z hz
    simp

/--
The algebraic deck action on path classes, given by left-concatenating the
inverse of a loop at the basepoint.

Once the covering topology is added, this is the action that should become the
homeomorphism-valued `deckTransformation` field of `SimplyConnectedCover`.
-/
def deckAction (γ : FundamentalGroup X x₀)
    (y : PathHomotopyUniversalCover X x₀) :
    PathHomotopyUniversalCover X x₀ :=
  ⟨endpoint y, Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹) y.pathClass⟩

/--
%%handwave
name:
  Deck transformations preserve endpoints
statement:
  For every \(\gamma\in\pi_1(X,x_0)\) and based path class \(y\), the endpoint of \(\gamma\cdot y\) equals the endpoint of \(y\).
proof:
  Deck action changes only the path class by left concatenation and leaves its endpoint index unchanged.
-/
@[simp]
theorem endpoint_deckAction (γ : FundamentalGroup X x₀)
    (y : PathHomotopyUniversalCover X x₀) :
    endpoint (deckAction γ y) = endpoint y :=
  rfl

/-- Deck action restricts to an action on each endpoint fiber. -/
def deckActionFiber (γ : FundamentalGroup X x₀) {x : X} (η : Fiber x₀ x) :
    Fiber x₀ x :=
  ⟨deckAction γ η.1, by rw [endpoint_deckAction, η.2]⟩

/--
%%handwave
name:
  Underlying lift of the fiberwise deck action
statement:
  The underlying point of \(\gamma\cdot\eta\) in an endpoint fiber is the ordinary deck transform of the underlying lift of \(\eta\).
proof:
  This is the definition of the action restricted to a fiber.
-/
@[simp]
theorem deckActionFiber_val (γ : FundamentalGroup X x₀) {x : X}
    (η : Fiber x₀ x) :
    (deckActionFiber γ η).1 = deckAction γ η.1 :=
  rfl

/--
%%handwave
name:
  Fiberwise deck action in path-class coordinates
statement:
  Under the identification of the fiber over \(x\) with path-homotopy classes from \(x_0\) to \(x\), \(\gamma\cdot\eta\) corresponds to \(\gamma^{-1}\) concatenated on the left with the class of \(\eta\).
proof:
  Unfold the fiber identification and the deck action; both sides are the same concatenated path class.
-/
@[simp]
theorem fiberPathClassEquiv_deckActionFiber (γ : FundamentalGroup X x₀)
    {x : X} (η : Fiber x₀ x) :
    (fiberPathClassEquiv (x₀ := x₀) x) (deckActionFiber γ η) =
      Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹)
        ((fiberPathClassEquiv (x₀ := x₀) x) η) := by
  cases η with
  | mk y hy =>
      cases y with
      | mk b q =>
          dsimp [Fiber, endpoint] at hy
          subst b
          simp [fiberPathClassEquiv, deckActionFiber, deckAction, pathClass, endpoint]

/--
%%handwave
name:
  The identity loop fixes every path class
statement:
  The identity element of \(\pi_1(X,x_0)\) acts trivially on every point of the path-homotopy cover.
proof:
  Its inverse is the constant loop, and left concatenation by the constant path leaves a path class unchanged.
-/
@[simp]
theorem deckAction_one (y : PathHomotopyUniversalCover X x₀) :
    deckAction (1 : FundamentalGroup X x₀) y = y := by
  cases y with
  | mk x q =>
      change
        (⟨x, Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.refl x₀) q⟩ :
          PathHomotopyUniversalCover X x₀) = ⟨x, q⟩
      rw [Path.Homotopic.Quotient.refl_trans]

/--
%%handwave
name:
  Deck action respects loop multiplication
statement:
  For \(\gamma,\delta\in\pi_1(X,x_0)\), \((\gamma\delta)\cdot y=\gamma\cdot(\delta\cdot y)\).
proof:
  Inverting the product reverses the two loops, and associativity of path concatenation identifies the resulting path classes.
-/
theorem deckAction_mul (γ δ : FundamentalGroup X x₀)
    (y : PathHomotopyUniversalCover X x₀) :
    deckAction (γ * δ) y = deckAction γ (deckAction δ y) := by
  cases y with
  | mk x q =>
      unfold deckAction pathClass endpoint
      rw [mul_inv_rev]
      change
        (⟨x, Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.trans
            (FundamentalGroup.toPath γ⁻¹) (FundamentalGroup.toPath δ⁻¹)) q⟩ :
          PathHomotopyUniversalCover X x₀) =
          ⟨x, Path.Homotopic.Quotient.trans
            (FundamentalGroup.toPath γ⁻¹)
            (Path.Homotopic.Quotient.trans (FundamentalGroup.toPath δ⁻¹) q)⟩
      rw [Path.Homotopic.Quotient.trans_assoc]

/--
%%handwave
name:
  The identity loop fixes every point of an endpoint fiber
statement:
  The identity element of \(\pi_1(X,x_0)\) fixes every element of every endpoint fiber.
proof:
  The underlying lift is fixed by the ordinary deck action, hence the fiber elements are equal.
-/
@[simp]
theorem deckActionFiber_one {x : X} (η : Fiber x₀ x) :
    deckActionFiber (1 : FundamentalGroup X x₀) η = η := by
  exact Subtype.ext (deckAction_one η.1)

/--
%%handwave
name:
  Fiberwise deck action respects loop multiplication
statement:
  On every endpoint fiber, \((\gamma\delta)\cdot\eta=\gamma\cdot(\delta\cdot\eta)\).
proof:
  The equality follows from the corresponding equality of the underlying deck-transformed lifts.
-/
theorem deckActionFiber_mul (γ δ : FundamentalGroup X x₀) {x : X}
    (η : Fiber x₀ x) :
    deckActionFiber (γ * δ) η = deckActionFiber γ (deckActionFiber δ η) := by
  exact Subtype.ext (deckAction_mul γ δ η.1)

/--
%%handwave
name:
  An inverse deck transformation cancels on the left
statement:
  For every fiber point \(\eta\), \(\gamma^{-1}\cdot(\gamma\cdot\eta)=\eta\).
proof:
  Combine the two actions using the multiplication law and reduce \(\gamma^{-1}\gamma\) to the identity.
-/
@[simp]
theorem deckActionFiber_inv_apply (γ : FundamentalGroup X x₀) {x : X}
    (η : Fiber x₀ x) :
    deckActionFiber γ⁻¹ (deckActionFiber γ η) = η := by
  rw [← deckActionFiber_mul, inv_mul_cancel, deckActionFiber_one]

/--
%%handwave
name:
  An inverse deck transformation cancels on the right
statement:
  For every fiber point \(\eta\), \(\gamma\cdot(\gamma^{-1}\cdot\eta)=\eta\).
proof:
  Combine the two actions using the multiplication law and reduce \(\gamma\gamma^{-1}\) to the identity.
-/
@[simp]
theorem deckActionFiber_apply_inv (γ : FundamentalGroup X x₀) {x : X}
    (η : Fiber x₀ x) :
    deckActionFiber γ (deckActionFiber γ⁻¹ η) = η := by
  rw [← deckActionFiber_mul, mul_inv_cancel, deckActionFiber_one]

/-- In local trivialization coordinates, deck action only changes the fiber label.

%%handwave
name:
  Deck action changes only the fiber label in a local trivialization
statement:
  In a local trivialization over a path-connected set, the second coordinate of \(\gamma\cdot y\) is \(\gamma\) acting on the second coordinate of \(y\).
proof:
  Translate both fiber labels to path classes. Deck action is left concatenation by \(\gamma^{-1}\), and associativity moves this concatenation past the chosen local transport path.
-/
theorem localTrivializationFiberEquiv_deckAction_snd
    (γ : FundamentalGroup X x₀) {U : Set X} [PathConnectedSpace U]
    (a : U)
    (y : {y : PathHomotopyUniversalCover X x₀ // endpoint y ∈ U}) :
    ((localTrivializationFiberEquiv (x₀ := x₀) a)
        ⟨deckAction γ y.1, by simpa using y.2⟩).2 =
      deckActionFiber γ (((localTrivializationFiberEquiv (x₀ := x₀) a) y).2) := by
  apply (fiberPathClassEquiv (x₀ := x₀) (a : X)).injective
  rw [fiberPathClassEquiv_localTrivializationFiberEquiv_snd]
  rw [fiberPathClassEquiv_deckActionFiber]
  rw [fiberPathClassEquiv_localTrivializationFiberEquiv_snd]
  cases y with
  | mk y hyU =>
      cases y with
      | mk x q =>
          dsimp [localTrivializationEquiv, deckAction, pathClass, endpoint]
          change
            Path.Homotopic.Quotient.trans
                (Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹) q)
                (Path.Homotopic.Quotient.mk (pathInSet a ⟨x, hyU⟩).symm) =
              Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹)
                (Path.Homotopic.Quotient.trans q
                  (Path.Homotopic.Quotient.mk (pathInSet a ⟨x, hyU⟩).symm))
          rw [Path.Homotopic.Quotient.trans_assoc]

/-- Deck action sends local sheets to local sheets by relabelling the fiber.

%%handwave
name:
  Deck action relabels local sheets
statement:
  For a local sheet over \(U\) labelled by \(\eta\), \(\gamma\cdot y\) lies in that sheet if and only if \(y\) lies in the sheet labelled by \(\gamma^{-1}\cdot\eta\).
proof:
  Deck transformations preserve endpoints and act on the local-trivialization fiber label by \(\gamma\). Cancel this fiber action with \(\gamma^{-1}\) in the two directions.
-/
theorem deckAction_mem_localSheet_iff
    (γ : FundamentalGroup X x₀) {U : Set X} [PathConnectedSpace U]
    {a : U} {η : Fiber x₀ (a : X)}
    {y : PathHomotopyUniversalCover X x₀} :
    deckAction γ y ∈ localSheet a η ↔
      y ∈ localSheet a (deckActionFiber γ⁻¹ η) := by
  constructor
  · rintro ⟨hyUγ, hηγ⟩
    have hyU : endpoint y ∈ U := by simpa [endpoint_deckAction] using hyUγ
    have hlabelγ :=
      localTrivializationFiberEquiv_deckAction_snd (x₀ := x₀) γ a ⟨y, hyU⟩
    have hlabel :
        deckActionFiber γ
            (((localTrivializationFiberEquiv (x₀ := x₀) a) ⟨y, hyU⟩).2) = η := by
      rw [← hlabelγ]
      exact hηγ
    refine ⟨hyU, ?_⟩
    calc
      ((localTrivializationFiberEquiv (x₀ := x₀) a) ⟨y, hyU⟩).2 =
          deckActionFiber γ⁻¹
            (deckActionFiber γ
              (((localTrivializationFiberEquiv (x₀ := x₀) a) ⟨y, hyU⟩).2)) := by
        simp
      _ = deckActionFiber γ⁻¹ η := by rw [hlabel]
  · rintro ⟨hyU, hη⟩
    refine ⟨by simpa [endpoint_deckAction] using hyU, ?_⟩
    calc
      ((localTrivializationFiberEquiv (x₀ := x₀) a)
          ⟨deckAction γ y, by simpa [endpoint_deckAction] using hyU⟩).2 =
          deckActionFiber γ
            (((localTrivializationFiberEquiv (x₀ := x₀) a) ⟨y, hyU⟩).2) :=
        localTrivializationFiberEquiv_deckAction_snd (x₀ := x₀) γ a ⟨y, hyU⟩
      _ = deckActionFiber γ (deckActionFiber γ⁻¹ η) := by rw [hη]
      _ = η := by simp

/--
The deck-preimage version of
`mem_connectedComponentIn_localSheetChart_inter_of_endpoint_mem_base_inter`.

Deck action preserves endpoints and only relabels sheets, so the same base
connected-component argument controls intersections of a sheet with the
deck-preimage of another sheet.

%%handwave
name:
  Base connected components control deck-translated sheet intersections
statement:
  Suppose \(y_1\) lies in a sheet \(C\) and \(\gamma y_1\) lies in a sheet \(D\). If the endpoint of \(y\in C\) lies in the same connected component of \(C\)'s base intersection with \(D\)'s base as the endpoint of \(y_1\), then \(y\) lies in the connected component of \(C\cap\gamma^{-1}D\) containing \(y_1\).
proof:
  Relabel \(D\) by \(\gamma^{-1}\) so that its sheet is exactly \(\gamma^{-1}D\). Apply the ordinary two-sheet connected-component lifting result.
-/
theorem mem_connectedComponentIn_localSheetChart_inter_deck_preimage_of_endpoint_mem_base_inter
    [LocallySimplyConnectedSpace X]
    (γ : FundamentalGroup X x₀) (C D : LocalSheetChart (X := X) x₀)
    {y₁ y : PathHomotopyUniversalCover X x₀}
    (hy₁C : y₁ ∈ C.sheet) (hy₁Ddeck : deckAction γ y₁ ∈ D.sheet)
    (hyC : y ∈ C.sheet)
    (hbase :
      (⟨endpoint y, endpoint_mem_of_mem_localSheet hyC⟩ : C.base) ∈
        connectedComponentIn {z : C.base | (z : X) ∈ D.base}
          (⟨endpoint y₁, endpoint_mem_of_mem_localSheet hy₁C⟩ : C.base)) :
    y ∈ connectedComponentIn
      (C.sheet ∩ (deckAction γ) ⁻¹' D.sheet) y₁ := by
  let Dγ : LocalSheetChart (X := X) x₀ :=
    { D with fiberPoint := deckActionFiber γ⁻¹ D.fiberPoint }
  have hy₁Dγ : y₁ ∈ Dγ.sheet := by
    simpa [Dγ, LocalSheetChart.sheet] using
      (deckAction_mem_localSheet_iff (x₀ := x₀)
        (γ := γ) (a := D.center) (η := D.fiberPoint) (y := y₁)).mp
        (by simpa [LocalSheetChart.sheet] using hy₁Ddeck)
  have hbaseDγ :
      (⟨endpoint y, endpoint_mem_of_mem_localSheet hyC⟩ : C.base) ∈
        connectedComponentIn {z : C.base | (z : X) ∈ Dγ.base}
          (⟨endpoint y₁, endpoint_mem_of_mem_localSheet hy₁C⟩ : C.base) := by
    simpa [Dγ] using hbase
  have hcomponent :
      y ∈ connectedComponentIn (C.sheet ∩ Dγ.sheet) y₁ :=
    mem_connectedComponentIn_localSheetChart_inter_of_endpoint_mem_base_inter
      (x₀ := x₀) C Dγ hy₁C hy₁Dγ hyC hbaseDγ
  have hset :
      C.sheet ∩ Dγ.sheet =
        C.sheet ∩ (deckAction γ) ⁻¹' D.sheet := by
    ext z
    simp [Dγ, LocalSheetChart.sheet, deckAction_mem_localSheet_iff]
  simpa [hset] using hcomponent

/-- The algebraic deck action is by equivalences of the path-homotopy total space. -/
def deckEquiv (γ : FundamentalGroup X x₀) :
    PathHomotopyUniversalCover X x₀ ≃ PathHomotopyUniversalCover X x₀ where
  toFun := deckAction γ
  invFun := deckAction γ⁻¹
  left_inv y := by
    rw [← deckAction_mul, inv_mul_cancel, deckAction_one]
  right_inv y := by
    rw [← deckAction_mul, mul_inv_cancel, deckAction_one]

/--
%%handwave
name:
  The deck equivalence acts by path concatenation
statement:
  The permutation associated to \(\gamma\) sends each path-class lift \(y\) to \(\gamma\cdot y\).
proof:
  This is the forward map in the definition of the deck equivalence.
-/
@[simp]
theorem deckEquiv_apply (γ : FundamentalGroup X x₀)
    (y : PathHomotopyUniversalCover X x₀) :
    deckEquiv γ y = deckAction γ y :=
  rfl

/-- The algebraic deck action as a genuine monoid action by permutations. -/
def deckPermutation :
    FundamentalGroup X x₀ →* Equiv.Perm (PathHomotopyUniversalCover X x₀) where
  toFun := deckEquiv
  map_one' := by
    ext y
    exact deckAction_one y
  map_mul' γ δ := by
    ext y
    exact deckAction_mul γ δ y

/--
%%handwave
name:
  The deck permutation acts by path concatenation
statement:
  Evaluating the permutation representation of \(\gamma\) at \(y\) gives the deck transform \(\gamma\cdot y\).
proof:
  This is the underlying map of the permutation representation.
-/
@[simp]
theorem deckPermutation_apply (γ : FundamentalGroup X x₀)
    (y : PathHomotopyUniversalCover X x₀) :
    deckPermutation γ y = deckAction γ y :=
  rfl

/-- The preimage of a generated local-sheet open under deck action is open.

%%handwave
name:
  Deck preimages of restricted local sheets are open
statement:
  For a local sheet \(C\), an open base set \(V\), and \(\gamma\in\pi_1(X,x_0)\), the preimage \(\gamma^{-1}(C\cap\operatorname{end}^{-1}(V))\) is open in the path-homotopy cover.
proof:
  Deck action preserves endpoints and replaces the sheet label by \(\gamma^{-1}\) applied to it. The preimage is therefore another generating restricted local-sheet open.
-/
theorem isOpen_deckAction_preimage_localSheetChart_restrict
    (γ : FundamentalGroup X x₀) (C : LocalSheetChart (X := X) x₀)
    {V : Set X} (hV : IsOpen V) :
    IsOpen ((deckAction γ) ⁻¹'
      (C.sheet ∩ (endpoint (x₀ := x₀)) ⁻¹' V)) := by
  rw [show
      (deckAction γ) ⁻¹' (C.sheet ∩ (endpoint (x₀ := x₀)) ⁻¹' V) =
        ({ C with fiberPoint := deckActionFiber γ⁻¹ C.fiberPoint }).sheet ∩
          (endpoint (x₀ := x₀)) ⁻¹' V by
    ext y
    simp [LocalSheetChart.sheet, deckAction_mem_localSheet_iff, endpoint_deckAction]]
  exact isOpen_localSheetChart_sheet_inter_endpoint_preimage
    ({ C with fiberPoint := deckActionFiber γ⁻¹ C.fiberPoint }) hV

/-- Deck action is continuous for the generated path-homotopy cover topology.

%%handwave
name:
  Deck transformations of the path-homotopy cover are continuous
statement:
  For every \(\gamma\in\pi_1(X,x_0)\), the map \(y\mapsto\gamma\cdot y\) is continuous in the local-sheet topology.
proof:
  The topology is generated by restricted local sheets, and the preimage of every such generator under deck action is open.
-/
theorem continuous_deckAction (γ : FundamentalGroup X x₀) :
    Continuous (deckAction γ : PathHomotopyUniversalCover X x₀ →
      PathHomotopyUniversalCover X x₀) := by
  apply continuous_generateFrom_iff.mpr
  intro s hs
  rcases hs with ⟨C, V, hV, rfl⟩
  exact isOpen_deckAction_preimage_localSheetChart_restrict γ C hV

/-- Deck action as a homeomorphism of the path-homotopy cover. -/
def deckHomeomorph (γ : FundamentalGroup X x₀) :
    Homeomorph (PathHomotopyUniversalCover X x₀)
      (PathHomotopyUniversalCover X x₀) where
  toEquiv := deckEquiv γ
  continuous_toFun := continuous_deckAction γ
  continuous_invFun := continuous_deckAction γ⁻¹

/--
%%handwave
name:
  The deck homeomorphism acts by path concatenation
statement:
  Evaluating the deck homeomorphism associated to \(\gamma\) at \(y\) gives \(\gamma\cdot y\).
proof:
  This is the underlying equivalence in the definition of the deck homeomorphism.
-/
@[simp]
theorem deckHomeomorph_apply (γ : FundamentalGroup X x₀)
    (y : PathHomotopyUniversalCover X x₀) :
    deckHomeomorph γ y = deckAction γ y :=
  rfl

/-- The deck action as a monoid action by homeomorphisms. -/
def deckHomeomorphism :
    FundamentalGroup X x₀ →* Homeomorph
      (PathHomotopyUniversalCover X x₀) (PathHomotopyUniversalCover X x₀) where
  toFun := deckHomeomorph
  map_one' := by
    ext y
    exact deckAction_one y
  map_mul' γ δ := by
    ext y
    exact deckAction_mul γ δ y

/--
%%handwave
name:
  The homeomorphism-valued deck representation has the expected action
statement:
  Evaluating the homeomorphism representation of \(\gamma\) at \(y\) gives the deck transform \(\gamma\cdot y\).
proof:
  This is the underlying map of the homeomorphism-valued representation.
-/
@[simp]
theorem deckHomeomorphism_apply (γ : FundamentalGroup X x₀)
    (y : PathHomotopyUniversalCover X x₀) :
    deckHomeomorphism γ y = deckAction γ y :=
  rfl

/-- Homeomorphic deck transformations preserve endpoint fibers.

%%handwave
name:
  Deck homeomorphisms preserve endpoints
statement:
  For every \(\gamma\in\pi_1(X,x_0)\) and lift \(y\), the endpoint of the deck homeomorphism \(\gamma(y)\) equals the endpoint of \(y\).
proof:
  The underlying map of the homeomorphism is the deck action, which preserves endpoints.
-/
theorem endpoint_deckHomeomorphism (γ : FundamentalGroup X x₀)
    (y : PathHomotopyUniversalCover X x₀) :
    endpoint (deckHomeomorphism γ y) = endpoint y :=
  endpoint_deckAction γ y

/-- Deck transformations act transitively on the algebraic fiber over the basepoint.

%%handwave
name:
  Deck transformations are transitive on the base fiber of the path-class cover
statement:
  If a path class \(y\) ends at \(x_0\), then some \(\gamma\in\pi_1(X,x_0)\) sends the constant-path lift to \(y\).
proof:
  Represent \(y\) by a loop class \(q\) and choose \(\gamma=q^{-1}\). The action concatenates \(q\) with the constant path, yielding \(y\).
-/
theorem deckAction_base_fiber_transitive
    (y : PathHomotopyUniversalCover X x₀) (hy : endpoint y = x₀) :
    ∃ γ : FundamentalGroup X x₀, deckAction γ (baseLift x₀) = y := by
  cases y with
  | mk x q =>
      dsimp [endpoint] at hy
      subst x
      refine ⟨(FundamentalGroup.fromPath q)⁻¹, ?_⟩
      unfold deckAction baseLift pathClass endpoint
      rw [inv_inv]
      change
        (⟨x₀, Path.Homotopic.Quotient.trans
          q
          (Path.Homotopic.Quotient.refl x₀)⟩ :
          PathHomotopyUniversalCover X x₀) = ⟨x₀, q⟩
      rw [Path.Homotopic.Quotient.trans_refl]

/-- Deck transformations act freely on the distinguished lift in the algebraic base fiber.

%%handwave
name:
  The deck action is free at the constant-path lift
statement:
  If \(\gamma\) fixes the constant-path lift over \(x_0\), then \(\gamma=1\).
proof:
  The equality says that \(\gamma^{-1}\) concatenated with the constant path is the constant class. Cancel the constant path and invert.
-/
theorem deckAction_base_fiber_free
    (γ : FundamentalGroup X x₀)
    (hγ : deckAction γ (baseLift x₀) = baseLift x₀) :
    γ = 1 := by
  change
    (⟨x₀, Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹)
      (Path.Homotopic.Quotient.refl x₀)⟩ :
      PathHomotopyUniversalCover X x₀) =
      ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩ at hγ
  rw [Path.Homotopic.Quotient.trans_refl] at hγ
  have hinv : γ⁻¹ = 1 := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp hγ).2
  exact inv_eq_one.mp hinv

/-- Deck transformations act freely on every endpoint fiber.

%%handwave
name:
  The deck action is free on every fiber of the path-class cover
statement:
  If \(\gamma\cdot y=y\) for any path-class lift \(y\), then \(\gamma=1\).
proof:
  Writing \(y\) as a path class \(q\), the equality is \(\gamma^{-1}q=q\). Right cancellation gives \(\gamma^{-1}=1\), hence \(\gamma=1\).
-/
theorem deckAction_fiber_free
    (γ : FundamentalGroup X x₀) (y : PathHomotopyUniversalCover X x₀)
    (hγ : deckAction γ y = y) :
    γ = 1 := by
  cases y with
  | mk x q =>
      change
        (⟨x, Path.Homotopic.Quotient.trans
          (FundamentalGroup.toPath γ⁻¹) q⟩ :
          PathHomotopyUniversalCover X x₀) = ⟨x, q⟩ at hγ
      have hq :
          Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹) q = q := by
        exact eq_of_heq (Sigma.mk.inj_iff.mp hγ).2
      have hcancel :
          FundamentalGroup.toPath γ⁻¹ = Path.Homotopic.Quotient.refl x₀ := by
        exact quotient_trans_right_cancel (x := x₀) (y := x₀) (z := x) q
          (by simpa using hq)
      exact inv_eq_one.mp hcancel

/-- Deck transformations act transitively on every algebraic fiber.

%%handwave
name:
  Deck transformations are transitive on every fiber of the path-class cover
statement:
  If path-class lifts \(y,z\) have the same endpoint, then some \(\gamma\in\pi_1(X,x_0)\) satisfies \(\gamma\cdot y=z\).
proof:
  For path classes \(q_y,q_z\), choose the inverse of the loop \(q_zq_y^{-1}\). Its deck action left-concatenates by \(q_zq_y^{-1}\), which cancels with \(q_y\) to give \(q_z\).
-/
theorem deckAction_same_fiber_transitive
    (y z : PathHomotopyUniversalCover X x₀) (hyz : endpoint y = endpoint z) :
    ∃ γ : FundamentalGroup X x₀, deckAction γ y = z := by
  cases y with
  | mk x qy =>
      cases z with
      | mk z qz =>
          dsimp [endpoint] at hyz
          subst z
          refine
            ⟨(FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.trans qz (Path.Homotopic.Quotient.symm qy)))⁻¹, ?_⟩
          unfold deckAction pathClass endpoint
          rw [inv_inv]
          change
            (⟨x, Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.trans qz (Path.Homotopic.Quotient.symm qy)) qy⟩ :
              PathHomotopyUniversalCover X x₀) = ⟨x, qz⟩
          simp [Path.Homotopic.Quotient.trans_assoc]

/-- Homeomorphic deck transformations act transitively on the base fiber.

%%handwave
name:
  Deck homeomorphisms are transitive on the base fiber
statement:
  Every path-class lift over \(x_0\) is the image of the constant-path lift under some deck homeomorphism.
proof:
  Use transitivity of the underlying deck action; the homeomorphism has that same pointwise action.
-/
theorem deckHomeomorphism_base_fiber_transitive
    (y : PathHomotopyUniversalCover X x₀) (hy : endpoint y = x₀) :
    ∃ γ : FundamentalGroup X x₀, deckHomeomorphism γ (baseLift x₀) = y :=
  deckAction_base_fiber_transitive y hy

/-- Homeomorphic deck transformations act freely on the distinguished base lift.

%%handwave
name:
  The homeomorphic deck action is free at the base lift
statement:
  If the deck homeomorphism associated to \(\gamma\) fixes the constant-path lift, then \(\gamma=1\).
proof:
  Its underlying map is the algebraic deck action, which is free at that lift.
-/
theorem deckHomeomorphism_base_fiber_free
    (γ : FundamentalGroup X x₀)
    (hγ : deckHomeomorphism γ (baseLift x₀) = baseLift x₀) :
    γ = 1 :=
  deckAction_base_fiber_free γ hγ

/-- Homeomorphic deck transformations act transitively on every endpoint fiber.

%%handwave
name:
  Deck homeomorphisms are transitive on every fiber
statement:
  For lifts \(y,z\) with the same endpoint, there is a based loop class \(\gamma\in\pi_1(X,x_0)\) whose deck homeomorphism sends \(y\) to \(z\).
proof:
  Use transitivity of the underlying deck action; the deck homeomorphism has that action as its underlying map.
-/
theorem deckHomeomorphism_same_fiber_transitive
    (y z : PathHomotopyUniversalCover X x₀) (hyz : endpoint y = endpoint z) :
    ∃ γ : FundamentalGroup X x₀, deckHomeomorphism γ y = z :=
  deckAction_same_fiber_transitive y z hyz

/-- Riemann surfaces have surjective algebraic endpoint projection.

%%handwave
name:
  Every point of a Riemann surface is the endpoint of a based path class
statement:
  For a Riemann surface \(X\) and base point \(x_0\), the endpoint map from based path-homotopy classes onto \(X\) is surjective.
proof:
  A Riemann surface is path connected, so every point is joined to \(x_0\) by a path; take its homotopy class.
-/
theorem endpoint_surjective_of_riemannSurface
    (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) :
    Function.Surjective (endpoint : PathHomotopyUniversalCover X x₀ → X) :=
  endpoint_surjective x₀

/-- Riemann surfaces give a continuous path-homotopy endpoint projection.

%%handwave
name:
  The path-class endpoint map of a Riemann surface is continuous
statement:
  For a Riemann surface \(X\), the endpoint projection from its based path-homotopy cover to \(X\) is continuous.
proof:
  Riemann surfaces are locally simply connected, and the endpoint projection is continuous for every locally simply connected base.
-/
theorem continuous_endpoint_of_riemannSurface
    (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) :
    Continuous (endpoint : PathHomotopyUniversalCover X x₀ → X) :=
  continuous_endpoint

/-- Riemann surfaces give a covering-map endpoint projection.

%%handwave
name:
  The path-class endpoint map is a covering map for Riemann surfaces
statement:
  For a Riemann surface \(X\), the endpoint projection from based path-homotopy classes to \(X\) is a covering map.
proof:
  Riemann surfaces are locally simply connected; the local-sheet trivializations of the path-class space therefore exhibit the endpoint projection as a covering map.
-/
theorem isCoveringMap_endpoint_of_riemannSurface
    (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) :
    IsCoveringMap (endpoint : PathHomotopyUniversalCover X x₀ → X) :=
  isCoveringMap_endpoint

end PathHomotopyUniversalCover

/--
A simply connected cover of a based space, together with the deck action of the
fundamental group.

The intended example is the universal cover of `X` based at `x₀`.  The deck
action is stored as actual homeomorphisms, with a chosen lift over the basepoint
and the usual free/transitive action on that base fiber.
-/
structure SimplyConnectedCover (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] (x₀ : X) where
  /-- The total space of the cover. -/
  total : Type*
  /-- The topology on the total space. -/
  [topologicalSpace_total : TopologicalSpace total]
  /-- The pulled-back complex charted structure on the cover. -/
  [chartedSpace_total : ChartedSpace ℂ total]
  /-- The covering projection. -/
  projection : total → X
  /-- The projection is a covering map. -/
  isCovering : IsCoveringMap projection
  /-- The covering projection is onto the base surface. -/
  projection_surjective : Function.Surjective projection
  /-- The total space is simply connected. -/
  simplyConnected : SimplyConnectedSpace total
  /-- Deck transformations of the cover, as a genuine monoid action by homeomorphisms. -/
  deckTransformation : FundamentalGroup X x₀ →* Homeomorph total total
  /-- A chosen lift of the basepoint. -/
  baseLift : total
  /-- The chosen lift lies over the basepoint. -/
  projection_baseLift : projection baseLift = x₀
  /-- Deck transformations preserve fibers of the covering map. -/
  projection_deckTransformation :
    ∀ γ y, projection (deckTransformation γ y) = projection y
  /-- Deck transformations act transitively on the fiber over the basepoint. -/
  deckTransformation_fiber_transitive :
    ∀ y, projection y = x₀ → ∃ γ, deckTransformation γ baseLift = y
  /-- Deck transformations act freely on the chosen lift in the base fiber. -/
  deckTransformation_fiber_free :
    ∀ γ, deckTransformation γ baseLift = baseLift → γ = 1
  /-- Deck transformations act transitively on every fiber. -/
  deckTransformation_same_fiber_transitive :
    ∀ y z, projection y = projection z → ∃ γ, deckTransformation γ y = z
  /--
  The covering projection has holomorphic local inverse sections in the
  pulled-back complex structure.
  -/
  local_holomorphic_section :
    ∀ y : total, CoverLocalHolomorphicSectionData projection y

attribute [instance] SimplyConnectedCover.topologicalSpace_total
attribute [instance] SimplyConnectedCover.chartedSpace_total

namespace PathHomotopyUniversalCover

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] {x₀ : X}

/--
Package the path-homotopy cover as the project-level `SimplyConnectedCover`
once its simple connectedness has been proved.

All fields other than `simplyConnected` are supplied by the concrete
path-homotopy construction in this file.  The remaining input is intentionally
the exact mathematical statement still needed for the universal-cover theorem,
not a weaker substitute.
-/
noncomputable def toSimplyConnectedCover [RiemannSurface X]
    (hsc : SimplyConnectedSpace (PathHomotopyUniversalCover X x₀)) :
    SimplyConnectedCover X x₀ where
  total := PathHomotopyUniversalCover X x₀
  topologicalSpace_total := inferInstance
  chartedSpace_total := inferInstance
  projection := endpoint
  isCovering := isCoveringMap_endpoint_of_riemannSurface X x₀
  projection_surjective := endpoint_surjective_of_riemannSurface X x₀
  simplyConnected := hsc
  deckTransformation := deckHomeomorphism
  baseLift := baseLift x₀
  projection_baseLift := endpoint_baseLift x₀
  projection_deckTransformation := endpoint_deckHomeomorphism
  deckTransformation_fiber_transitive := deckHomeomorphism_base_fiber_transitive
  deckTransformation_fiber_free := deckHomeomorphism_base_fiber_free
  deckTransformation_same_fiber_transitive := deckHomeomorphism_same_fiber_transitive
  local_holomorphic_section := localHolomorphicSectionData

/-- Riemann surfaces have the concrete path-homotopy simply connected cover. -/
noncomputable def simplyConnectedCoverOfRiemannSurface
    [RiemannSurface X] :
    SimplyConnectedCover X x₀ :=
  toSimplyConnectedCover (X := X) (x₀ := x₀) inferInstance

/--
%%handwave
name:
  Projection of the packaged path-homotopy cover
statement:
  After packaging the path-homotopy universal cover as a simply connected cover, its projection is the endpoint map.
proof:
  This is the projection field of the construction.
-/
@[simp]
theorem toSimplyConnectedCover_projection [RiemannSurface X]
    (hsc : SimplyConnectedSpace (PathHomotopyUniversalCover X x₀)) :
    (toSimplyConnectedCover (X := X) (x₀ := x₀) hsc).projection = endpoint :=
  rfl

/--
%%handwave
name:
  Base lift of the packaged path-homotopy cover
statement:
  The chosen lift of \(x_0\) in the packaged path-homotopy cover is the constant-path class at \(x_0\).
proof:
  This is the chosen-lift field of the construction.
-/
@[simp]
theorem toSimplyConnectedCover_baseLift [RiemannSurface X]
    (hsc : SimplyConnectedSpace (PathHomotopyUniversalCover X x₀)) :
    (toSimplyConnectedCover (X := X) (x₀ := x₀) hsc).baseLift = baseLift x₀ :=
  rfl

/--
%%handwave
name:
  Deck action of the packaged path-homotopy cover
statement:
  In the packaged path-homotopy cover, the deck transformation associated to \(\gamma\in\pi_1(X,x_0)\) acts by concatenating \(\gamma\) with the represented based path.
proof:
  This is the deck-transformation field of the construction.
-/
@[simp]
theorem toSimplyConnectedCover_deckAction [RiemannSurface X]
    (hsc : SimplyConnectedSpace (PathHomotopyUniversalCover X x₀))
    (γ : FundamentalGroup X x₀) (y : PathHomotopyUniversalCover X x₀) :
    ((toSimplyConnectedCover (X := X) (x₀ := x₀) hsc).deckTransformation γ) y =
      deckHomeomorphism γ y :=
  rfl

end PathHomotopyUniversalCover

namespace SimplyConnectedCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {x₀ : X}

/-- Deck action of the fundamental group, recovered from the homeomorphism-valued action. -/
def deckAction (cover : SimplyConnectedCover X x₀)
    (γ : FundamentalGroup X x₀) : cover.total → cover.total :=
  cover.deckTransformation γ

/--
%%handwave
name:
  The identity loop acts trivially on a simply connected cover
statement:
  For a simply connected cover and every lift \(y\), the identity element of \(\pi_1(X,x_0)\) fixes \(y\).
proof:
  The deck transformations form a monoid homomorphism, so the identity loop maps to the identity homeomorphism.
-/
@[simp]
theorem deckAction_one (cover : SimplyConnectedCover X x₀) (y : cover.total) :
    cover.deckAction 1 y = y := by
  change (cover.deckTransformation 1) y = y
  rw [cover.deckTransformation.map_one]
  rfl

/--
%%handwave
name:
  Deck actions compose according to loop multiplication
statement:
  For \(\gamma,\delta\in\pi_1(X,x_0)\) and every lift \(y\), \((\gamma\delta)\cdot y=\gamma\cdot(\delta\cdot y)\).
proof:
  The homeomorphism-valued deck transformation map preserves multiplication.
-/
@[simp]
theorem deckAction_mul (cover : SimplyConnectedCover X x₀)
    (γ δ : FundamentalGroup X x₀) (y : cover.total) :
    cover.deckAction (γ * δ) y =
      cover.deckAction γ (cover.deckAction δ y) := by
  change (cover.deckTransformation (γ * δ)) y =
    (cover.deckTransformation γ) ((cover.deckTransformation δ) y)
  rw [cover.deckTransformation.map_mul]
  rfl

/-- Deck transformations preserve fibers of the covering map.

%%handwave
name:
  Deck transformations preserve the covering projection
statement:
  For every \(\gamma\in\pi_1(X,x_0)\) and lift \(y\), \(\pi(\gamma\cdot y)=\pi(y)\).
proof:
  This is the fiber-preservation property of the deck action stored with the cover.
-/
theorem projection_deckAction (cover : SimplyConnectedCover X x₀)
    (γ : FundamentalGroup X x₀) (y : cover.total) :
    cover.projection (cover.deckAction γ y) = cover.projection y :=
  cover.projection_deckTransformation γ y

/-- The projection of a simply connected cover is continuous.

%%handwave
name:
  A simply connected covering projection is continuous
statement:
  The projection \(\pi:\widetilde X\to X\) of a simply connected cover is continuous.
proof:
  A covering map is a local homeomorphism and hence is continuous at every point.
-/
theorem projection_continuous (cover : SimplyConnectedCover X x₀) :
    Continuous cover.projection := by
  rw [continuous_iff_continuousAt]
  intro y
  exact cover.isCovering.isCoveringMapOn.continuousAt (by trivial)

/-- The projection of a simply connected cover is continuous at every lift.

%%handwave
name:
  A simply connected covering projection is continuous at every lift
statement:
  For every \(y\in\widetilde X\), the covering projection \(\pi\) is continuous at \(y\).
proof:
  This is the pointwise form of continuity of the covering projection.
-/
theorem projection_continuousAt (cover : SimplyConnectedCover X x₀) (y : cover.total) :
    ContinuousAt cover.projection y :=
  cover.projection_continuous.continuousAt

/-- Every point of the base has a lift to the cover.

%%handwave
name:
  Every base point has a lift
statement:
  For every \(x\in X\), there exists \(y\in\widetilde X\) with \(\pi(y)=x\).
proof:
  The projection of the simply connected cover is surjective.
-/
theorem exists_lift (cover : SimplyConnectedCover X x₀) (x : X) :
    ∃ y : cover.total, cover.projection y = x :=
  cover.projection_surjective x

/-- Deck transformations act transitively on the fiber over the basepoint.

%%handwave
name:
  Deck transformations are transitive on the chosen base fiber
statement:
  If \(\pi(y)=x_0\), then some \(\gamma\in\pi_1(X,x_0)\) satisfies \(\gamma\cdot\widetilde x_0=y\).
proof:
  This is the base-fiber transitivity property stored with the cover.
-/
theorem deckAction_fiber_transitive (cover : SimplyConnectedCover X x₀)
    (y : cover.total) (hy : cover.projection y = x₀) :
    ∃ γ, cover.deckAction γ cover.baseLift = y :=
  cover.deckTransformation_fiber_transitive y hy

/-- Deck transformations act transitively on any fiber.

%%handwave
name:
  Deck transformations are transitive on every fiber of a simply connected cover
statement:
  If \(\pi(y)=\pi(z)\), then some \(\gamma\in\pi_1(X,x_0)\) satisfies \(\gamma\cdot y=z\).
proof:
  This is the same-fiber transitivity property stored with the cover.
-/
theorem deckAction_same_fiber_transitive (cover : SimplyConnectedCover X x₀)
    (y z : cover.total) (hyz : cover.projection y = cover.projection z) :
    ∃ γ, cover.deckAction γ y = z :=
  cover.deckTransformation_same_fiber_transitive y z hyz

/-- Deck transformations act freely on the chosen lift in the base fiber.

%%handwave
name:
  The deck action is free at the chosen base lift
statement:
  If \(\gamma\cdot\widetilde x_0=\widetilde x_0\), then \(\gamma=1\) in \(\pi_1(X,x_0)\).
proof:
  This is the base-fiber freeness property stored with the cover.
-/
theorem deckAction_fiber_free (cover : SimplyConnectedCover X x₀)
    (γ : FundamentalGroup X x₀)
    (hγ : cover.deckAction γ cover.baseLift = cover.baseLift) :
    γ = 1 :=
  cover.deckTransformation_fiber_free γ hγ

/--
The covering projection is represented near every lift by an open partial
homeomorphism.
-/
noncomputable def localHomeomorphAt (cover : SimplyConnectedCover X x₀)
    (y : cover.total) : OpenPartialHomeomorph cover.total X :=
  Classical.choose (cover.isCovering.isLocalHomeomorph y)

/-- The chosen local homeomorphism around a lift contains that lift.

%%handwave
name:
  The chosen covering chart contains its center
statement:
  For every lift \(y\), the source of the chosen local homeomorphism representing \(\pi\) near \(y\) contains \(y\).
proof:
  Choose the local homeomorphism supplied by the covering-map property; its defining specification includes membership of the center in its source.
-/
theorem mem_localHomeomorphAt_source (cover : SimplyConnectedCover X x₀)
    (y : cover.total) :
    y ∈ (cover.localHomeomorphAt y).source :=
  (Classical.choose_spec (cover.isCovering.isLocalHomeomorph y)).1

/-- The chosen local homeomorphism around a lift is the projection map.

%%handwave
name:
  The chosen covering chart represents the projection
statement:
  For every lift \(y\), the chosen local homeomorphism near \(y\) agrees with the covering projection \(\pi\) on its source.
proof:
  This is the map-identification part of the chosen local-homeomorphism specification.
-/
theorem localHomeomorphAt_eq_projection (cover : SimplyConnectedCover X x₀)
    (y : cover.total) :
    cover.projection = cover.localHomeomorphAt y :=
  (Classical.choose_spec (cover.isCovering.isLocalHomeomorph y)).2

/-- The local inverse of the chosen covering chart projects back to the base point.

%%handwave
name:
  A local inverse section projects to the identity
statement:
  If \(x\) lies in the target of the chosen covering chart at \(y\), then \(\pi((\pi|_y)^{-1}(x))=x\).
proof:
  Replace the local chart map by the projection and apply the right-inverse identity of the local homeomorphism.
-/
theorem projection_localHomeomorphAt_symm (cover : SimplyConnectedCover X x₀)
    (y : cover.total) {x : X} (hx : x ∈ (cover.localHomeomorphAt y).target) :
    cover.projection ((cover.localHomeomorphAt y).symm x) = x := by
  rw [cover.localHomeomorphAt_eq_projection y]
  exact (cover.localHomeomorphAt y).right_inv hx

/--
Local uniqueness of sections of a covering projection, with a deck
transformation applied to the first section.

If two local sections project to the same base map and agree at one point after
applying a fixed deck transformation to the first one, then they agree near
that point.  This is the covering-space local injectivity argument used to make
the real-projective transition representative locally constant.

%%handwave
name:
  Two locally coincident lifted sections agree near a point
statement:
  Let \(s_1,s_2\) be continuous at \(t_0\), with \(\pi\circ s_1=\pi\circ s_2=b\) near \(t_0\). If \(\gamma\cdot s_1(t_0)=s_2(t_0)\), then \(\gamma\cdot s_1=s_2\) on a neighborhood of \(t_0\).
proof:
  Both sections eventually lie in the same evenly covered sheet around \(s_2(t_0)\). Deck transformations preserve projection, so their images under that sheet's injective local projection agree; local injectivity then makes the lifted sections equal.
-/
theorem deckAction_sections_eventuallyEq_of_projection_eq
    (cover : SimplyConnectedCover X x₀)
    {T : Type*} [TopologicalSpace T]
    (s₁ s₂ : T → cover.total) (b : T → X) {t₀ : T}
    (γ : FundamentalGroup X x₀)
    (hs₁ : ContinuousAt s₁ t₀) (hs₂ : ContinuousAt s₂ t₀)
    (hproj₁ : ∀ᶠ t in 𝓝 t₀, cover.projection (s₁ t) = b t)
    (hproj₂ : ∀ᶠ t in 𝓝 t₀, cover.projection (s₂ t) = b t)
    (h0 : cover.deckAction γ (s₁ t₀) = s₂ t₀) :
    (fun t ↦ cover.deckAction γ (s₁ t)) =ᶠ[𝓝 t₀] s₂ := by
  let E : OpenPartialHomeomorph cover.total X :=
    cover.localHomeomorphAt (s₂ t₀)
  let f₁ : T → cover.total := fun t ↦ cover.deckAction γ (s₁ t)
  have hf₁ : ContinuousAt f₁ t₀ :=
    (cover.deckTransformation γ).continuous.continuousAt.comp hs₁
  have hf₁_source : f₁ t₀ ∈ E.source := by
    simpa [E, f₁, h0] using cover.mem_localHomeomorphAt_source (s₂ t₀)
  have hf₂_source : s₂ t₀ ∈ E.source := by
    simpa [E] using cover.mem_localHomeomorphAt_source (s₂ t₀)
  have hsource₁ : ∀ᶠ t in 𝓝 t₀, f₁ t ∈ E.source :=
    hf₁.preimage_mem_nhds (E.open_source.mem_nhds hf₁_source)
  have hsource₂ : ∀ᶠ t in 𝓝 t₀, s₂ t ∈ E.source :=
    hs₂.preimage_mem_nhds (E.open_source.mem_nhds hf₂_source)
  have hproj₁' : ∀ᶠ t in 𝓝 t₀, cover.projection (f₁ t) = b t := by
    filter_upwards [hproj₁] with t ht
    calc
      cover.projection (f₁ t) = cover.projection (s₁ t) := by
        exact cover.projection_deckAction γ (s₁ t)
      _ = b t := ht
  filter_upwards [hsource₁, hsource₂, hproj₁', hproj₂] with t ht₁ ht₂ hp₁ hp₂
  have hEproj : ∀ y, cover.projection y = E y := by
    intro y
    exact congrFun (cover.localHomeomorphAt_eq_projection (s₂ t₀)) y
  have hEeq : E (f₁ t) = E (s₂ t) := by
    calc
      E (f₁ t) = cover.projection (f₁ t) := (hEproj (f₁ t)).symm
      _ = b t := hp₁
      _ = cover.projection (s₂ t) := hp₂.symm
      _ = E (s₂ t) := hEproj (s₂ t)
  calc
    f₁ t = E.symm (E (f₁ t)) := (E.left_inv ht₁).symm
    _ = E.symm (E (s₂ t)) := by rw [hEeq]
    _ = s₂ t := E.left_inv ht₂

/--
The cover-local holomorphic section data: every lift has a holomorphic local
inverse section of the covering projection in complex coordinates.
-/
def localHolomorphicSection
    (cover : SimplyConnectedCover X x₀) (y : cover.total) :
    CoverLocalHolomorphicSectionData cover.projection y :=
  cover.local_holomorphic_section y

/-- Existence form of `localHolomorphicSection`, convenient for branch choices.

%%handwave
name:
  A holomorphic local inverse exists through every lift
statement:
  For every \(y\in\widetilde X\), there exists a local inverse section of \(\pi\) through \(y\) whose coordinate expression is holomorphic with nonzero derivative.
proof:
  Take the local holomorphic section supplied with the simply connected cover.
-/
theorem exists_localHolomorphicSection
    (cover : SimplyConnectedCover X x₀) (y : cover.total) :
    Nonempty (CoverLocalHolomorphicSectionData cover.projection y) :=
  ⟨cover.localHolomorphicSection y⟩

/-- The holomorphic local section projects back to the base point.

%%handwave
name:
  The holomorphic local inverse projects to the identity
statement:
  For a local holomorphic inverse section \(s\) through \(y\), \(\pi(s(x))=x\) throughout the target of its local projection.
proof:
  Apply the right-inverse identity in the local holomorphic section data.
-/
theorem localHolomorphicSection_projects
    (cover : SimplyConnectedCover X x₀) (y : cover.total)
    {x : X} (hx : x ∈ (cover.localHolomorphicSection y).localProjection.target) :
    cover.projection ((cover.localHolomorphicSection y).localProjection.symm x) = x :=
  (cover.localHolomorphicSection y).projection_localProjection_symm hx

/-- The coordinate expression of a cover-local section is holomorphic.

%%handwave
name:
  A local inverse section is holomorphic in coordinates
statement:
  The coordinate expression of the chosen local inverse section through \(y\) is complex differentiable at every point of its coordinate domain.
proof:
  This is the holomorphicity property stored in the local section data.
-/
theorem localHolomorphicSection_coordinate_holomorphic
    (cover : SimplyConnectedCover X x₀) (y : cover.total)
    {z : ℂ} (hz : z ∈ (cover.localHolomorphicSection y).coordinateSource) :
    DifferentiableAt ℂ (cover.localHolomorphicSection y).sectionCoordinate z :=
  (cover.localHolomorphicSection y).sectionCoordinate_holomorphic z hz

/-- The coordinate expression of a cover-local section has nonzero derivative.

%%handwave
name:
  A local inverse section has nonzero coordinate derivative
statement:
  The coordinate derivative of the chosen local inverse section through \(y\) is nonzero at every point of its coordinate domain.
proof:
  This is the local-biholomorphism nonvanishing property stored in the local section data.
-/
theorem localHolomorphicSection_coordinate_deriv_ne_zero
    (cover : SimplyConnectedCover X x₀) (y : cover.total)
    {z : ℂ} (hz : z ∈ (cover.localHolomorphicSection y).coordinateSource) :
    deriv (cover.localHolomorphicSection y).sectionCoordinate z ≠ 0 :=
  (cover.localHolomorphicSection y).sectionCoordinate_deriv_ne_zero z hz

end SimplyConnectedCover

end

end JJMath
