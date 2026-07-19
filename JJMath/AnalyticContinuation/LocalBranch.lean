import JJMath.ComplexProjective.Prerequisites.RiemannSurface
import JJMath.Topology.UnitIntervalSplit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.List.ChainOfFn
import Mathlib.Topology.Subpath
import Mathlib.Topology.UnitInterval

/-!
# Local holomorphic branch continuation

This file isolates the common analytic continuation interface used by the
hyperbolic developing-map construction and by the Radó harmonic-conjugate
argument.  The hard path-continuation and monodromy theorem is stated as an
explicit theorem stub; the local-to-global holomorphicity consequence is
proved here.
-/

namespace JJMath

open scoped Manifold Topology

namespace AnalyticContinuation

universe u v w

/--
%%handwave
name:
  Identity theorem on a plane domain
statement:
  Let two holomorphic functions on a preconnected open subset of the complex
  plane take values in a complex Banach space.  If they agree at points
  accumulating at a point of the domain, then they agree on the whole domain.
proof:
  Mathlib proves that complex differentiability on an open subset of the plane
  implies analyticity there.  The conclusion is then the one-variable identity
  theorem for analytic functions with an accumulation point.
tags:
  milestone
-/
theorem complex_identity_theorem_of_accumulation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f g : ℂ → E} {U : Set ℂ} {z₀ : ℂ}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hz₀ : z₀ ∈ U)
    (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g U)
    (hfg : z₀ ∈ closure ({z : ℂ | f z = g z} \ {z₀})) :
    Set.EqOn f g U := by
  exact
    (hf.analyticOnNhd hU_open).eqOn_of_preconnected_of_mem_closure
      (hg.analyticOnNhd hU_open) hU_preconnected hz₀ hfg

/--
%%handwave
name:
  Homotopy-strip cut path
statement:
  The cut path through a homotopy strip follows one side of the strip, crosses
  through the homotopy at the cut parameter, and then follows the other side.
-/
noncomputable def homotopyStripCutPathRawCore
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r : unitInterval) :
    Path (F (a, 0)) (F (b, 1)) :=
  (((F.eval a).subpath 0 r).trans ((F.evalAt r).subpath a b)).trans
    ((F.eval b).subpath r 1)

/--
%%handwave
name:
  Homotopy-strip cut path with fixed endpoints
statement:
  The cut path through a homotopy strip, regarded as a path with the original
  endpoints.
-/
noncomputable def homotopyStripCutPathRaw
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r : unitInterval) :
    Path x₀ x :=
  (homotopyStripCutPathRawCore F a b r).cast (by simp) (by simp)

/--
%%handwave
name:
  Normalized homotopy-strip cut path
statement:
  The normalized cut path is definitionally equal to the lower row at one end
  and the upper row at the other end.
-/
noncomputable def homotopyStripCutPath
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r : unitInterval) :
    Path x₀ x :=
  if r = 1 then
    F.eval a
  else if r = 0 then
    F.eval b
  else
    homotopyStripCutPathRaw F a b r

/--
%%handwave
name:
  Upper endpoint of a normalized homotopy-strip cut path
statement:
  At interpolation parameter \(1\), the normalized cut path through the
  homotopy strip is the row at parameter \(a\).
proof:
  The endpoint normalization explicitly selects that row when the
  interpolation parameter is one.
-/
@[simp]
theorem homotopyStripCutPath_one
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b : unitInterval) :
    homotopyStripCutPath F a b 1 = F.eval a := by
  simp [homotopyStripCutPath]

/--
%%handwave
name:
  Lower endpoint of a normalized homotopy-strip cut path
statement:
  At interpolation parameter \(0\), the normalized cut path through the
  homotopy strip is the row at parameter \(b\).
proof:
  The endpoint normalization explicitly selects that row when the
  interpolation parameter is zero.
-/
@[simp]
theorem homotopyStripCutPath_zero
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b : unitInterval) :
    homotopyStripCutPath F a b 0 = F.eval b := by
  simp [homotopyStripCutPath]

/--
%%handwave
name:
  Lower-then-right rectangle edge
statement:
  The lower-then-right boundary route across a homotopy rectangle first moves
  vertically along the left edge and then horizontally along the upper edge.
-/
noncomputable def homotopyRectangleBottomRightPath
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path (F (a, r₀)) (F (b, r₁)) :=
  ((F.eval a).subpath r₀ r₁).trans ((F.evalAt r₁).subpath a b)

/--
%%handwave
name:
  Left-then-upper rectangle edge
statement:
  The left-then-upper boundary route across a homotopy rectangle first moves
  horizontally along the lower edge and then vertically along the right edge.
-/
noncomputable def homotopyRectangleLeftTopPath
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path (F (a, r₀)) (F (b, r₁)) :=
  ((F.evalAt r₀).subpath a b).trans ((F.eval b).subpath r₀ r₁)

/--
%%handwave
name:
  Lower-then-right edge stays in a contained rectangle
statement:
  If a homotopy rectangle is contained in a set, then the lower-then-right
  boundary route across that rectangle stays in the set.
proof:
  The image of a concatenated path is the union of the two path images.  The two
  pieces are subpaths of the left and upper rectangle edges, and each subpath
  image is the image of the corresponding interval.
-/
theorem homotopyRectangleBottomRightPath_mem_of_rect_subset
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {s : Set X}
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval | F z ∈ s}) :
    ∀ u, homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈ s := by
  intro u
  have hmem :
      homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
        Set.range (homotopyRectangleBottomRightPath F a b r₀ r₁) :=
    ⟨u, rfl⟩
  have hRange :
      Set.range (homotopyRectangleBottomRightPath F a b r₀ r₁) =
        Set.range ((F.eval a).subpath r₀ r₁) ∪
          Set.range ((F.evalAt r₁).subpath a b) := by
    change
      Set.range
          (((F.eval a).subpath r₀ r₁).trans
            ((F.evalAt r₁).subpath a b)) =
        Set.range ((F.eval a).subpath r₀ r₁) ∪
          Set.range ((F.evalAt r₁).subpath a b)
    exact
      Path.trans_range ((F.eval a).subpath r₀ r₁)
        ((F.evalAt r₁).subpath a b)
  rw [hRange] at hmem
  rcases hmem with hmem | hmem
  · have hSub :
        Set.range ((F.eval a).subpath r₀ r₁) =
          ((⇑(F.eval a)) '' Set.Icc r₀ r₁) :=
      Path.range_subpath_of_le (F.eval a) r₀ r₁ hr
    have hmemImage :
        homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
          ((⇑(F.eval a)) '' Set.Icc r₀ r₁) := by
      rw [← hSub]
      exact hmem
    rcases hmemImage with ⟨v, hv, hEq⟩
    rw [← hEq]
    exact hRect ⟨⟨le_rfl, hab⟩, hv⟩
  · have hSub :
        Set.range ((F.evalAt r₁).subpath a b) =
          ((⇑(F.evalAt r₁)) '' Set.Icc a b) :=
      Path.range_subpath_of_le (F.evalAt r₁) a b hab
    have hmemImage :
        homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
          ((⇑(F.evalAt r₁)) '' Set.Icc a b) := by
      rw [← hSub]
      exact hmem
    rcases hmemImage with ⟨v, hv, hEq⟩
    rw [← hEq]
    exact hRect ⟨hv, ⟨hr, le_rfl⟩⟩

/--
%%handwave
name:
  Left-then-upper edge stays in a contained rectangle
statement:
  If a homotopy rectangle is contained in a set, then the left-then-upper
  boundary route across that rectangle stays in the set.
proof:
  The image of a concatenated path is the union of the two path images.  The two
  pieces are subpaths of the lower and right rectangle edges, and each subpath
  image is the image of the corresponding interval.
-/
theorem homotopyRectangleLeftTopPath_mem_of_rect_subset
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {s : Set X}
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval | F z ∈ s}) :
    ∀ u, homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈ s := by
  intro u
  have hmem :
      homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
        Set.range (homotopyRectangleLeftTopPath F a b r₀ r₁) :=
    ⟨u, rfl⟩
  have hRange :
      Set.range (homotopyRectangleLeftTopPath F a b r₀ r₁) =
        Set.range ((F.evalAt r₀).subpath a b) ∪
          Set.range ((F.eval b).subpath r₀ r₁) := by
    change
      Set.range
          (((F.evalAt r₀).subpath a b).trans
            ((F.eval b).subpath r₀ r₁)) =
        Set.range ((F.evalAt r₀).subpath a b) ∪
          Set.range ((F.eval b).subpath r₀ r₁)
    exact
      Path.trans_range ((F.evalAt r₀).subpath a b)
        ((F.eval b).subpath r₀ r₁)
  rw [hRange] at hmem
  rcases hmem with hmem | hmem
  · have hSub :
        Set.range ((F.evalAt r₀).subpath a b) =
          ((⇑(F.evalAt r₀)) '' Set.Icc a b) :=
      Path.range_subpath_of_le (F.evalAt r₀) a b hab
    have hmemImage :
        homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
          ((⇑(F.evalAt r₀)) '' Set.Icc a b) := by
      rw [← hSub]
      exact hmem
    rcases hmemImage with ⟨v, hv, hEq⟩
    rw [← hEq]
    exact hRect ⟨hv, ⟨le_rfl, hr⟩⟩
  · have hSub :
        Set.range ((F.eval b).subpath r₀ r₁) =
          ((⇑(F.eval b)) '' Set.Icc r₀ r₁) :=
      Path.range_subpath_of_le (F.eval b) r₀ r₁ hr
    have hmemImage :
        homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
          ((⇑(F.eval b)) '' Set.Icc r₀ r₁) := by
      rw [← hSub]
      exact hmem
    rcases hmemImage with ⟨v, hv, hEq⟩
    rw [← hEq]
    exact hRect ⟨⟨hab, le_rfl⟩, hv⟩

/--
%%handwave
name:
  Decomposed upper column path
statement:
  The upper path associated to one homotopy column is the common lower
  prefix, followed by the lower-then-right boundary of the small rectangle,
  followed by the common upper suffix.
-/
noncomputable def homotopyStripColumnTopPathRawCore
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path (F (a, 0)) (F (b, 1)) :=
  (((F.eval a).subpath 0 r₀).trans
      (homotopyRectangleBottomRightPath F a b r₀ r₁)).trans
    ((F.eval b).subpath r₁ 1)

/--
%%handwave
name:
  Decomposed lower column path
statement:
  The lower path associated to one homotopy column is the common lower
  prefix, followed by the left-then-upper boundary of the small rectangle,
  followed by the common upper suffix.
-/
noncomputable def homotopyStripColumnBottomPathRawCore
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path (F (a, 0)) (F (b, 1)) :=
  (((F.eval a).subpath 0 r₀).trans
      (homotopyRectangleLeftTopPath F a b r₀ r₁)).trans
    ((F.eval b).subpath r₁ 1)

/--
%%handwave
name:
  Common lower prefix of a column
statement:
  The common prefix in a column move is the left vertical side from the base
  row to the lower edge of the small rectangle.
-/
noncomputable def homotopyStripColumnPrefix
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a r₀ : unitInterval) :
    Path x₀ (F (a, r₀)) :=
  ((F.eval a).subpath 0 r₀).cast (by simp) rfl

/--
%%handwave
name:
  Common upper suffix of a column
statement:
  The common suffix in a column move is the right vertical side from the upper
  edge of the small rectangle to the terminal row.
-/
noncomputable def homotopyStripColumnSuffix
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (b r₁ : unitInterval) :
    Path (F (b, r₁)) x :=
  ((F.eval b).subpath r₁ 1).cast rfl (by simp)

/--
%%handwave
name:
  Decomposed upper column path with fixed endpoints
statement:
  The decomposed upper column path, regarded as a path with the original
  endpoints.
-/
noncomputable def homotopyStripColumnTopPath
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path x₀ x :=
  (homotopyStripColumnTopPathRawCore F a b r₀ r₁).cast (by simp) (by simp)

/--
%%handwave
name:
  Decomposed lower column path with fixed endpoints
statement:
  The decomposed lower column path, regarded as a path with the original
  endpoints.
-/
noncomputable def homotopyStripColumnBottomPath
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    Path x₀ x :=
  (homotopyStripColumnBottomPathRawCore F a b r₀ r₁).cast (by simp) (by simp)
/--
%%handwave
name:
  Upper column path decomposition
statement:
  Let \(H:[0,1]^2\to X\) be an endpoint-fixed homotopy and let
  \(a,b,r_0,r_1\in[0,1]\). If \(P=H(a,\cdot)|_{[0,r_0]}\),
  \(R=(H(a,\cdot)|_{[r_0,r_1]})*(H(\cdot,r_1)|_{[a,b]})\), and
  \(Q=H(b,\cdot)|_{[r_1,1]}\), then the upper column path is
  \((P*R)*Q\).
proof:
  This is the defining concatenation of the upper column path. The endpoint
  identifications do not change that concatenation.
-/
@[simp]
theorem homotopyStripColumnTopPath_eq_prefix_rectangle_suffix
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    homotopyStripColumnTopPath F a b r₀ r₁ =
      ((homotopyStripColumnPrefix F a r₀).trans
        (homotopyRectangleBottomRightPath F a b r₀ r₁)).trans
          (homotopyStripColumnSuffix F b r₁) := by
  rfl
/--
%%handwave
name:
  Lower column path decomposition
statement:
  Let \(H:[0,1]^2\to X\) be an endpoint-fixed homotopy and let
  \(a,b,r_0,r_1\in[0,1]\). If \(P=H(a,\cdot)|_{[0,r_0]}\),
  \(R=(H(\cdot,r_0)|_{[a,b]})*(H(b,\cdot)|_{[r_0,r_1]})\), and
  \(Q=H(b,\cdot)|_{[r_1,1]}\), then the lower column path is
  \((P*R)*Q\).
proof:
  This is the defining concatenation of the lower column path. The endpoint
  identifications do not change that concatenation.
-/
@[simp]
theorem homotopyStripColumnBottomPath_eq_prefix_rectangle_suffix
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    homotopyStripColumnBottomPath F a b r₀ r₁ =
      ((homotopyStripColumnPrefix F a r₀).trans
        (homotopyRectangleLeftTopPath F a b r₀ r₁)).trans
          (homotopyStripColumnSuffix F b r₁) := by
  rfl

/--
%%handwave
name:
  Decomposed upper column path is homotopic to the cut path
statement:
  The decomposed upper column path is endpoint-fixed homotopic to the raw cut
  path at the upper edge of the small rectangle.
proof:
  Reassociate the concatenations and merge the two adjacent subpaths along the
  left side of the homotopy strip.
-/
theorem homotopyStripColumnTopPathRawCore_homotopic_cutPathRawCore
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    (homotopyStripColumnTopPathRawCore F a b r₀ r₁).Homotopic
      (homotopyStripCutPathRawCore F a b r₁) := by
  let γ := F.eval a
  let δ := (F.evalAt r₁).subpath a b
  let σ := (F.eval b).subpath r₁ 1
  have hAssoc :
      ((γ.subpath 0 r₀).trans ((γ.subpath r₀ r₁).trans δ)).Homotopic
        (((γ.subpath 0 r₀).trans (γ.subpath r₀ r₁)).trans δ) :=
    (Path.Homotopic.trans_assoc
      (γ.subpath 0 r₀) (γ.subpath r₀ r₁) δ).symm
  have hSplit :
      (((γ.subpath 0 r₀).trans (γ.subpath r₀ r₁)).trans δ).Homotopic
        ((γ.subpath 0 r₁).trans δ) := by
    exact
      Path.Homotopic.hcomp
        (⟨Path.Homotopy.subpathTransSubpath γ 0 r₀ r₁⟩ :
          ((γ.subpath 0 r₀).trans (γ.subpath r₀ r₁)).Homotopic
            (γ.subpath 0 r₁))
        (Path.Homotopic.refl δ)
  have hPrefix :
      ((γ.subpath 0 r₀).trans ((γ.subpath r₀ r₁).trans δ)).Homotopic
        ((γ.subpath 0 r₁).trans δ) :=
    hAssoc.trans hSplit
  simpa [homotopyStripColumnTopPathRawCore,
    homotopyStripCutPathRawCore, homotopyRectangleBottomRightPath,
    γ, δ, σ] using
    Path.Homotopic.hcomp hPrefix (Path.Homotopic.refl σ)

/--
%%handwave
name:
  Decomposed lower column path is homotopic to the cut path
statement:
  The decomposed lower column path is endpoint-fixed homotopic to the raw cut
  path at the lower edge of the small rectangle.
proof:
  Reassociate the concatenations and merge the two adjacent subpaths along the
  right side of the homotopy strip.
-/
theorem homotopyStripColumnBottomPathRawCore_homotopic_cutPathRawCore
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    (homotopyStripColumnBottomPathRawCore F a b r₀ r₁).Homotopic
      (homotopyStripCutPathRawCore F a b r₀) := by
  let γ := F.eval a
  let υ := F.eval b
  let δ := (F.evalAt r₀).subpath a b
  let ρ := υ.subpath r₀ r₁
  let σ := υ.subpath r₁ 1
  have hAssocLeft :
      ((γ.subpath 0 r₀).trans (δ.trans ρ)).Homotopic
        (((γ.subpath 0 r₀).trans δ).trans ρ) :=
    (Path.Homotopic.trans_assoc (γ.subpath 0 r₀) δ ρ).symm
  have hWithSuffix :
      (((γ.subpath 0 r₀).trans (δ.trans ρ)).trans σ).Homotopic
        ((((γ.subpath 0 r₀).trans δ).trans ρ).trans σ) :=
    Path.Homotopic.hcomp hAssocLeft (Path.Homotopic.refl σ)
  have hAssocRight :
      ((((γ.subpath 0 r₀).trans δ).trans ρ).trans σ).Homotopic
        (((γ.subpath 0 r₀).trans δ).trans (ρ.trans σ)) :=
    Path.Homotopic.trans_assoc ((γ.subpath 0 r₀).trans δ) ρ σ
  have hSplit :
      (((γ.subpath 0 r₀).trans δ).trans (ρ.trans σ)).Homotopic
        (((γ.subpath 0 r₀).trans δ).trans (υ.subpath r₀ 1)) := by
    exact
      Path.Homotopic.hcomp
        (Path.Homotopic.refl ((γ.subpath 0 r₀).trans δ))
        (⟨Path.Homotopy.subpathTransSubpath υ r₀ r₁ 1⟩ :
          (ρ.trans σ).Homotopic (υ.subpath r₀ 1))
  simpa [homotopyStripColumnBottomPathRawCore,
    homotopyStripCutPathRawCore, homotopyRectangleLeftTopPath,
    γ, υ, δ, ρ, σ] using
    (hWithSuffix.trans hAssocRight).trans hSplit

/--
%%handwave
name:
  Decomposed upper column path is homotopic to the raw cut path
statement:
  For an endpoint-fixed homotopy \(H:p\simeq q\) and
  \(a,b,r_0,r_1\in[0,1]\), the path obtained by following the common prefix,
  the vertical-then-horizontal boundary of the rectangle
  \([a,b]\times[r_0,r_1]\), and the common suffix is homotopic relative to its
  endpoints to the cut path through level \(r_1\).
proof:
  [Before identifying the endpoints with those of \(p\) and \(q\), reassociation and concatenation of adjacent subpaths give precisely this homotopy.](lean:JJMath.AnalyticContinuation.homotopyStripColumnTopPathRawCore_homotopic_cutPathRawCore) Transport that homotopy across the endpoint identifications.
-/
theorem homotopyStripColumnTopPath_homotopic_cutPathRaw
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    (homotopyStripColumnTopPath F a b r₀ r₁).Homotopic
      (homotopyStripCutPathRaw F a b r₁) :=
  (homotopyStripColumnTopPathRawCore_homotopic_cutPathRawCore
    F a b r₀ r₁).pathCast (by simp) (by simp)

/--
%%handwave
name:
  Decomposed lower column path is homotopic to the raw cut path
statement:
  For an endpoint-fixed homotopy \(H:p\simeq q\) and
  \(a,b,r_0,r_1\in[0,1]\), the path obtained by following the common prefix,
  the horizontal-then-vertical boundary of the rectangle
  \([a,b]\times[r_0,r_1]\), and the common suffix is homotopic relative to its
  endpoints to the cut path through level \(r_0\).
proof:
  [Before identifying the endpoints with those of \(p\) and \(q\), reassociation and concatenation of adjacent subpaths give precisely this homotopy.](lean:JJMath.AnalyticContinuation.homotopyStripColumnBottomPathRawCore_homotopic_cutPathRawCore) Transport that homotopy across the endpoint identifications.
-/
theorem homotopyStripColumnBottomPath_homotopic_cutPathRaw
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval) :
    (homotopyStripColumnBottomPath F a b r₀ r₁).Homotopic
      (homotopyStripCutPathRaw F a b r₀) :=
  (homotopyStripColumnBottomPathRawCore_homotopic_cutPathRawCore
    F a b r₀ r₁).pathCast (by simp) (by simp)

/--
%%handwave
name:
  Order-preserving path reparameterization data
statement:
  An order-preserving path reparameterization from one path to another is a
  monotone parameter map which evaluates the new path at the old path values.
  The interval-image condition says that every point of a new parameter
  interval has the same path value as some old parameter in the corresponding
  old interval.
-/
def PathOrderReparamData
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} (p q : Path x₀ x)
    (φ : unitInterval → unitInterval) : Prop :=
  φ 0 = 0 ∧
  φ 1 = 1 ∧
  Monotone φ ∧
  (∀ u : unitInterval, q (φ u) = p u) ∧
  (∀ {a b t : unitInterval},
    a ≤ b → φ a ≤ t → t ≤ φ b →
      ∃ u : unitInterval, a ≤ u ∧ u ≤ b ∧ q t = p u)

namespace PathOrderReparamData

/--
%%handwave
name:
  Constructing an order-preserving path reparameterization
statement:
  Let \(p,q:[0,1]\to X\) have the same endpoints. Suppose
  \(\varphi,\psi:[0,1]\to[0,1]\), where \(\varphi(0)=0\),
  \(\varphi(1)=1\), \(\varphi\) is monotone,
  \(q(\varphi(u))=p(u)\), and \(q(t)=p(\psi(t))\). If
  \(a\le b\) and \(\varphi(a)\le t\le\varphi(b)\) imply
  \(a\le\psi(t)\le b\), then \(\varphi\) is an order-preserving
  reparameterization from \(p\) to \(q\).
proof:
  For \(t\in[\varphi(a),\varphi(b)]\), choose \(u=\psi(t)\); the
  interval-control hypothesis gives \(u\in[a,b]\), and \(q(t)=p(u)\).
-/
theorem of_strong
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (φ ψ : unitInterval → unitInterval)
    (hφ_zero : φ 0 = 0)
    (hφ_one : φ 1 = 1)
    (hφ_mono : Monotone φ)
    (hψ_interval :
      ∀ {a b t : unitInterval},
        a ≤ b → φ a ≤ t → t ≤ φ b → a ≤ ψ t ∧ ψ t ≤ b)
    (hpath_sample : ∀ u : unitInterval, q (φ u) = p u)
    (hpath_all : ∀ t : unitInterval, q t = p (ψ t)) :
    PathOrderReparamData p q φ := by
  refine ⟨hφ_zero, hφ_one, hφ_mono, hpath_sample, ?_⟩
  intro a b t hab hleft hright
  rcases hψ_interval hab hleft hright with ⟨hleft', hright'⟩
  exact ⟨ψ t, hleft', hright', hpath_all t⟩

/--
%%handwave
name:
  Identity path reparameterization
statement:
  For every path \(p:[0,1]\to X\), the identity map of \([0,1]\) is an
  order-preserving reparameterization from \(p\) to itself.
proof:
  The identity fixes \(0\) and \(1\) and is monotone. For
  \(a\le t\le b\), the witness \(u=t\) gives both interval containment and
  \(p(t)=p(u)\).
-/
theorem refl
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} (p : Path x₀ x) :
    PathOrderReparamData p p id := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact monotone_id
  · intro u
    rfl
  · intro a b t _hab hleft hright
    exact ⟨t, hleft, hright, rfl⟩

/--
%%handwave
name:
  Composition of order-preserving path reparameterizations
statement:
  If \(\varphi_1\) is an order-preserving reparameterization from
  \(p:[0,1]\to X\) to \(q\), and \(\varphi_2\) is one from \(q\) to \(r\),
  then \(\varphi_2\circ\varphi_1\) is an order-preserving
  reparameterization from \(p\) to \(r\).
proof:
  Endpoint preservation, monotonicity, and the sampled-path identity compose.
  For an interval of the composite, first use the interval property for
  \(\varphi_2\) to obtain a parameter \(v\), then use it for \(\varphi_1\)
  to obtain \(u\in[a,b]\); the two path equalities give
  \(r(t)=q(v)=p(u)\).
-/
theorem trans
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q r : Path x₀ x}
    {φ₁ φ₂ : unitInterval → unitInterval}
    (hpq : PathOrderReparamData p q φ₁)
    (hqr : PathOrderReparamData q r φ₂) :
    PathOrderReparamData p r (φ₂ ∘ φ₁) := by
  rcases hpq with
    ⟨hφ₁_zero, hφ₁_one, hφ₁_mono, hsample₁, hinterval₁⟩
  rcases hqr with
    ⟨hφ₂_zero, hφ₂_one, hφ₂_mono, hsample₂, hinterval₂⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hφ₁_zero, hφ₂_zero]
  · simp [hφ₁_one, hφ₂_one]
  · exact hφ₂_mono.comp hφ₁_mono
  · intro u
    calc
      r ((φ₂ ∘ φ₁) u) = q (φ₁ u) := hsample₂ (φ₁ u)
      _ = p u := hsample₁ u
  · intro a b t hab hleft hright
    rcases hinterval₂ (hφ₁_mono hab) hleft hright with
      ⟨v, hv_left, hv_right, hrv⟩
    rcases hinterval₁ hab hv_left hv_right with
      ⟨u, hu_left, hu_right, hqv⟩
    exact ⟨u, hu_left, hu_right, hrv.trans hqv⟩

/--
%%handwave
name:
  Transporting ordered reparameterization data across equal paths
statement:
  If \(p\) is order-reparameterized to \(q\), and \(p=p'\) and \(q=q'\),
  then the same parameter map order-reparameterizes \(p'\) to \(q'\).
proof:
  Substitute the two path equalities.
-/
theorem cast
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p p' q q' : Path x₀ x}
    {φ : unitInterval → unitInterval}
    (h : PathOrderReparamData p q φ)
    (hp : p = p') (hq : q = q') :
    PathOrderReparamData p' q' φ := by
  subst p'
  subst q'
  exact h

/--
%%handwave
name:
  Transporting ordered reparameterization data across endpoint identifications
statement:
  An order-preserving reparameterization of two paths remains one after both
  paths are regarded as having propositionally equal source and target
  endpoints.
proof:
  Endpoint preservation and monotonicity are unchanged.  The sampled-path and
  interval-image identities simplify through the endpoint casts.
-/
theorem castEndpoints
    {X : Type*} [TopologicalSpace X]
    {x₀ x y₀ y : X} {p q : Path x₀ x}
    {φ : unitInterval → unitInterval}
    (h : PathOrderReparamData p q φ)
    (hsource : y₀ = x₀) (htarget : y = x) :
    PathOrderReparamData (p.cast hsource htarget)
      (q.cast hsource htarget) φ := by
  rcases h with
    ⟨hφ_zero, hφ_one, hφ_mono, hsample, hinterval⟩
  refine ⟨hφ_zero, hφ_one, hφ_mono, ?_, ?_⟩
  · intro u
    simpa [Path.cast_coe] using hsample u
  · intro a b t hab hleft hright
    rcases hinterval hab hleft hright with ⟨u, hu_left, hu_right, hqt⟩
    exact ⟨u, hu_left, hu_right, by simpa [Path.cast_coe] using hqt⟩

end PathOrderReparamData

/--
%%handwave
name:
  Collapsing a constant terminal path
statement:
  Following a path and then staying at its terminal point is an
  order-preserving reparameterization of the original path.
proof:
  Send the first half of the concatenated path linearly onto the original
  interval and send the second half to the terminal parameter.  The
  interval-image condition follows by either halving the requested target
  parameter or, at the terminal parameter, choosing the right endpoint of the
  old interval.
-/
theorem exists_pathOrderReparamData_trans_refl_right
    {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData (γ.trans (Path.refl y)) γ φ := by
  let φ : unitInterval → unitInterval :=
    fun t ↦
      if ht : (t : ℝ) ≤ (2⁻¹ : ℝ) then
        unitInterval.doubleOfLeHalf t (by simpa [one_div] using ht)
      else
        1
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · ext
    simp [φ, unitInterval.doubleOfLeHalf]
  · unfold φ
    rw [dif_neg]
    norm_num
  · intro a b hab
    change (φ a : ℝ) ≤ (φ b : ℝ)
    by_cases ha : (a : ℝ) ≤ (2⁻¹ : ℝ)
    · by_cases hb : (b : ℝ) ≤ (2⁻¹ : ℝ)
      · have hφa : (φ a : ℝ) = 2 * (a : ℝ) := by
          simp [φ, ha, unitInterval.doubleOfLeHalf]
        have hφb : (φ b : ℝ) = 2 * (b : ℝ) := by
          simp [φ, hb, unitInterval.doubleOfLeHalf]
        rw [hφa, hφb]
        nlinarith [show (a : ℝ) ≤ b from hab]
      · have hφa : (φ a : ℝ) = 2 * (a : ℝ) := by
          simp [φ, ha, unitInterval.doubleOfLeHalf]
        have hφb : (φ b : ℝ) = 1 := by
          simp [φ, hb]
        rw [hφa, hφb]
        nlinarith [unitInterval.le_one a]
    · have hb : ¬ (b : ℝ) ≤ (2⁻¹ : ℝ) := by
        intro hb
        exact ha ((show (a : ℝ) ≤ b from hab).trans hb)
      have hφa : (φ a : ℝ) = 1 := by
        simp [φ, ha]
      have hφb : (φ b : ℝ) = 1 := by
        simp [φ, hb]
      rw [hφa, hφb]
  · intro u
    by_cases hu : (u : ℝ) ≤ (2⁻¹ : ℝ)
    · have hu_half : (u : ℝ) ≤ 1 / 2 := by
        simpa [one_div] using hu
      rw [path_trans_apply_of_le_half γ (Path.refl y) u hu_half]
      have hφu : φ u = unitInterval.doubleOfLeHalf u hu_half := by
        ext
        simp [φ, hu, unitInterval.doubleOfLeHalf]
      rw [hφu]
    · have hu' : (1 / 2 : ℝ) ≤ u := by
        simpa [one_div] using le_of_lt (lt_of_not_ge hu)
      rw [path_trans_apply_of_half_le γ (Path.refl y) u hu']
      have hφu : φ u = 1 := by
        ext
        simp [φ, hu]
      rw [hφu]
      simp
  · intro a b t hab hleft hright
    by_cases ht : t = 1
    · subst t
      refine ⟨b, hab, le_rfl, ?_⟩
      have hφb_one : φ b = 1 := by
        apply le_antisymm
        · exact unitInterval.le_one _
        · exact hright
      by_cases hb : (b : ℝ) ≤ (2⁻¹ : ℝ)
      · have hb_half : (b : ℝ) ≤ 1 / 2 := by
          simpa [one_div] using hb
        rw [path_trans_apply_of_le_half γ (Path.refl y) b hb_half]
        have htwo : (2 * (b : ℝ)) = 1 := by
          have hφb_real := congrArg (fun s : unitInterval ↦ (s : ℝ)) hφb_one
          simpa [φ, hb, unitInterval.doubleOfLeHalf] using hφb_real
        apply congrArg γ
        ext
        simpa [unitInterval.doubleOfLeHalf] using htwo.symm
      · have hb' : (1 / 2 : ℝ) ≤ b := by
          simpa [one_div] using le_of_lt (lt_of_not_ge hb)
        rw [path_trans_apply_of_half_le γ (Path.refl y) b hb']
        simp
    · let u := unitInterval.firstHalf t
      have hu_left : a ≤ u := by
        by_cases ha : (a : ℝ) ≤ (2⁻¹ : ℝ)
        · change (a : ℝ) ≤ (t : ℝ) / 2
          have hφa : (φ a : ℝ) = 2 * (a : ℝ) := by
            simp [φ, ha, unitInterval.doubleOfLeHalf]
          have hleft_real' : (φ a : ℝ) ≤ (t : ℝ) := by
            exact_mod_cast hleft
          have hleft_real : 2 * (a : ℝ) ≤ t := by
            simpa [hφa] using hleft_real'
          nlinarith
        · have hφa : φ a = 1 := by
            ext
            simp [φ, ha]
          have ht_one : t = 1 := by
            apply le_antisymm
            · exact unitInterval.le_one t
            · simpa [hφa] using hleft
          exact False.elim (ht ht_one)
      have hu_right : u ≤ b := by
        by_cases hb : (b : ℝ) ≤ (2⁻¹ : ℝ)
        · change (t : ℝ) / 2 ≤ b
          have hφb : (φ b : ℝ) = 2 * (b : ℝ) := by
            simp [φ, hb, unitInterval.doubleOfLeHalf]
          have hright_real' : (t : ℝ) ≤ (φ b : ℝ) := by
            exact_mod_cast hright
          have hright_real : (t : ℝ) ≤ 2 * (b : ℝ) := by
            simpa [hφb] using hright_real'
          nlinarith
        · change (t : ℝ) / 2 ≤ b
          have hb' : (1 / 2 : ℝ) ≤ b := by
            simpa [one_div] using le_of_lt (lt_of_not_ge hb)
          nlinarith [unitInterval.le_one t, hb']
      refine ⟨u, hu_left, hu_right, ?_⟩
      exact (path_trans_firstHalf_apply γ (Path.refl y) t).symm

/--
%%handwave
name:
  Collapsing a constant initial path
statement:
  First staying at the initial point and then following a path is an
  order-preserving reparameterization of the original path.
proof:
  Send the first half of the concatenated path to the initial parameter and
  send the second half linearly onto the original interval.  The endpoint case
  of the interval-image condition chooses the left endpoint of the old
  interval; otherwise the requested target parameter is shifted into the
  second half.
-/
theorem exists_pathOrderReparamData_refl_trans_left
    {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData ((Path.refl x).trans γ) γ φ := by
  let φ : unitInterval → unitInterval :=
    fun t ↦
      if ht : (t : ℝ) ≤ (2⁻¹ : ℝ) then
        0
      else
        unitInterval.doubleSubOneOfHalfLe t
          (by simpa [one_div] using le_of_lt (lt_of_not_ge ht))
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · unfold φ
    rw [dif_pos]
    norm_num
  · ext
    unfold φ
    rw [dif_neg]
    · simp [unitInterval.doubleSubOneOfHalfLe]
      norm_num
    · norm_num
  · intro a b hab
    change (φ a : ℝ) ≤ (φ b : ℝ)
    by_cases ha : (a : ℝ) ≤ (2⁻¹ : ℝ)
    · by_cases hb : (b : ℝ) ≤ (2⁻¹ : ℝ)
      · have hφa : (φ a : ℝ) = 0 := by
          simp [φ, ha]
        have hφb : (φ b : ℝ) = 0 := by
          simp [φ, hb]
        rw [hφa, hφb]
      · have hφa : (φ a : ℝ) = 0 := by
          simp [φ, ha]
        have hφb : (φ b : ℝ) = 2 * (b : ℝ) - 1 := by
          simp [φ, hb, unitInterval.doubleSubOneOfHalfLe]
        rw [hφa, hφb]
        have hb' : (1 / 2 : ℝ) ≤ b := by
          simpa [one_div] using le_of_lt (lt_of_not_ge hb)
        nlinarith
    · have hb : ¬ (b : ℝ) ≤ (2⁻¹ : ℝ) := by
        intro hb
        exact ha ((show (a : ℝ) ≤ b from hab).trans hb)
      have hφa : (φ a : ℝ) = 2 * (a : ℝ) - 1 := by
        simp [φ, ha, unitInterval.doubleSubOneOfHalfLe]
      have hφb : (φ b : ℝ) = 2 * (b : ℝ) - 1 := by
        simp [φ, hb, unitInterval.doubleSubOneOfHalfLe]
      rw [hφa, hφb]
      nlinarith [show (a : ℝ) ≤ b from hab]
  · intro u
    by_cases hu : (u : ℝ) ≤ (2⁻¹ : ℝ)
    · rw [path_trans_apply_of_le_half (Path.refl x) γ u
        (by simpa [one_div] using hu)]
      have hφu : φ u = 0 := by
        ext
        simp [φ, hu]
      rw [hφu]
      simp
    · have hu_half : (1 / 2 : ℝ) ≤ u := by
        simpa [one_div] using le_of_lt (lt_of_not_ge hu)
      rw [path_trans_apply_of_half_le (Path.refl x) γ u hu_half]
      have hφu : φ u = unitInterval.doubleSubOneOfHalfLe u hu_half := by
        ext
        simp [φ, hu, unitInterval.doubleSubOneOfHalfLe]
      rw [hφu]
  · intro a b t hab hleft hright
    by_cases ht : t = 0
    · subst t
      refine ⟨a, le_rfl, hab, ?_⟩
      have hφa_zero : φ a = 0 := by
        apply le_antisymm
        · exact hleft
        · exact unitInterval.nonneg _
      by_cases ha : (a : ℝ) ≤ (2⁻¹ : ℝ)
      · rw [path_trans_apply_of_le_half (Path.refl x) γ a
          (by simpa [one_div] using ha)]
        simp
      · have ha_half : (1 / 2 : ℝ) ≤ a := by
          simpa [one_div] using le_of_lt (lt_of_not_ge ha)
        rw [path_trans_apply_of_half_le (Path.refl x) γ a ha_half]
        have htwo : 2 * (a : ℝ) - 1 = 0 := by
          have hφa_real := congrArg (fun s : unitInterval ↦ (s : ℝ)) hφa_zero
          simpa [φ, ha, unitInterval.doubleSubOneOfHalfLe] using hφa_real
        apply congrArg γ
        ext
        simpa [unitInterval.doubleSubOneOfHalfLe] using htwo.symm
    · let u := unitInterval.secondHalf t
      have hu_left : a ≤ u := by
        by_cases ha : (a : ℝ) ≤ (2⁻¹ : ℝ)
        · change (a : ℝ) ≤ (1 + (t : ℝ)) / 2
          nlinarith [ha, unitInterval.nonneg t]
        · change (a : ℝ) ≤ (1 + (t : ℝ)) / 2
          have hφa : (φ a : ℝ) = 2 * (a : ℝ) - 1 := by
            simp [φ, ha, unitInterval.doubleSubOneOfHalfLe]
          have hleft_real' : (φ a : ℝ) ≤ (t : ℝ) := by
            exact_mod_cast hleft
          have hleft_real : 2 * (a : ℝ) - 1 ≤ t := by
            simpa [hφa] using hleft_real'
          nlinarith
      have hu_right : u ≤ b := by
        by_cases hb : (b : ℝ) ≤ (2⁻¹ : ℝ)
        · have hφb : φ b = 0 := by
            ext
            simp [φ, hb]
          have ht_zero : t = 0 := by
            apply le_antisymm
            · simpa [hφb] using hright
            · exact unitInterval.nonneg t
          exact False.elim (ht ht_zero)
        · change (1 + (t : ℝ)) / 2 ≤ b
          have hφb : (φ b : ℝ) = 2 * (b : ℝ) - 1 := by
            simp [φ, hb, unitInterval.doubleSubOneOfHalfLe]
          have hright_real' : (t : ℝ) ≤ (φ b : ℝ) := by
            exact_mod_cast hright
          have hright_real : (t : ℝ) ≤ 2 * (b : ℝ) - 1 := by
            simpa [hφb] using hright_real'
          nlinarith
      refine ⟨u, hu_left, hu_right, ?_⟩
      exact (path_trans_secondHalf_apply (Path.refl x) γ t).symm

/--
%%handwave
name:
  Ordered unit split reparameterizes to the merged path
statement:
  If \(0 < r < 1\), then following a path from \(0\) to \(r\) and then from
  \(r\) to \(1\) is an order-preserving reparameterization of the merged
  subpath from \(0\) to \(1\).
proof:
  Use the explicit split maps on the unit interval.  The forward parameter map
  sends a split-path parameter back to the original path parameter; the inverse
  map sends an original parameter to the corresponding point of the split
  path.  The two inverse identities give the subinterval-control condition.
-/
theorem exists_pathOrderReparamData_unitSplit
    {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y) (r : unitInterval)
    (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        ((γ.subpath 0 r).trans (γ.subpath r 1))
        (γ.subpath 0 1) φ := by
  let φ : unitInterval → unitInterval :=
    fun t ↦ unitInterval.splitAtOriginalParameter r t hr0 hr1
  let ψ : unitInterval → unitInterval :=
    fun t ↦ unitInterval.splitAtReparam r t hr0 hr1
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · ext
    rw [show φ 0 =
        unitInterval.splitAtOriginalParameter r 0 hr0 hr1 by rfl]
    rw [unitInterval.splitAtOriginalParameter_of_le_half]
    · simp [unitInterval.doubleOfLeHalf, Set.Icc.convexComb]
    · norm_num
  · ext
    rw [show φ 1 =
        unitInterval.splitAtOriginalParameter r 1 hr0 hr1 by rfl]
    rw [unitInterval.splitAtOriginalParameter_of_half_le]
    · simp [unitInterval.doubleSubOneOfHalfLe, Set.Icc.convexComb]
      ring
    · norm_num
  · intro a b hab
    exact unitInterval.splitAtOriginalParameter_mono r hr0 hr1 hab
  · intro u
    change
      (γ.subpath 0 1)
          (unitInterval.splitAtOriginalParameter r u hr0 hr1) =
        ((γ.subpath 0 r).trans (γ.subpath r 1)) u
    rw [path_splitAt_originalParameter γ r u hr0 hr1]
    simp [Path.subpath]
  · intro a b t _hab hleft hright
    have ht :
        a ≤ ψ t ∧ ψ t ≤ b :=
      unitInterval.splitAtReparam_mem_interval_of_originalParameter_bounds
        r hr0 hr1 hleft hright
    refine ⟨ψ t, ht.1, ht.2, ?_⟩
    change
      (γ.subpath 0 1) t =
        ((γ.subpath 0 r).trans (γ.subpath r 1))
          (unitInterval.splitAtReparam r t hr0 hr1)
    rw [path_splitAt_splitAtReparam γ r t hr0 hr1]
    simp [Path.subpath]

/--
%%handwave
name:
  Ordered adjacent subpaths reparameterize to the merged subpath
statement:
  If \(a < b < c\), then following the subpath from \(a\) to \(b\) and then
  from \(b\) to \(c\) is an order-preserving reparameterization of the single
  subpath from \(a\) to \(c\).
proof:
  Regard the larger subpath from \(a\) to \(c\) as the ambient path and use
  the middle parameter at which it reaches \(b\).  The normalized unit-split
  theorem applies at that parameter, and taking subpaths of subpaths identifies
  the two pieces with the original adjacent subpaths.
-/
theorem exists_pathOrderReparamData_orderedSubpathMerge_of_lt
    {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y) (a b c : unitInterval)
    (hab : a < b) (hbc : b < c) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        ((γ.subpath a b).trans (γ.subpath b c))
        (γ.subpath a c) φ := by
  let r := unitInterval.orderedMiddleParameter a b c hab.le hbc.le
  let η := γ.subpath a c
  have hr0 : (0 : ℝ) < r :=
    unitInterval.orderedMiddleParameter_pos_of_lt a b c hab hbc.le
  have hr1 : (r : ℝ) < 1 :=
    unitInterval.orderedMiddleParameter_lt_one_of_lt a b c hab.le hbc
  have hb : b = Set.Icc.convexComb a c r := by
    simpa [r] using
      unitInterval.orderedMiddleParameter_spec a b c hab.le hbc.le
  rcases exists_pathOrderReparamData_unitSplit η r hr0 hr1 with
    ⟨φ, hdata⟩
  have h0 : γ a = η 0 := by
    simp [η, Path.subpath]
  have h1 : γ c = η 1 := by
    simp [η, Path.subpath]
  have hsplitPath :
      (((η.subpath 0 r).trans (η.subpath r 1)).cast h0 h1) =
        ((γ.subpath a b).trans (γ.subpath b c)) := by
    ext u
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · rw [Path.cast_coe,
        path_trans_apply_of_le_half (η.subpath 0 r) (η.subpath r 1) u hu,
        path_trans_apply_of_le_half (γ.subpath a b) (γ.subpath b c) u hu]
      apply congrArg γ
      ext
      simp [hb, Set.Icc.convexComb]
      ring_nf
    · have hu' : (1 / 2 : ℝ) ≤ u := le_of_not_gt (by
        intro hlt
        exact hu hlt.le)
      rw [Path.cast_coe,
        path_trans_apply_of_half_le (η.subpath 0 r) (η.subpath r 1) u hu',
        path_trans_apply_of_half_le (γ.subpath a b) (γ.subpath b c) u hu']
      apply congrArg γ
      ext
      simp [hb, Set.Icc.convexComb]
      ring_nf
  have hmergedPath :
      ((η.subpath 0 1).cast h0 h1) = γ.subpath a c := by
    ext u
    rw [Path.cast_coe]
    apply congrArg γ
    ext
    simp [Set.Icc.convexComb]
  exact
    ⟨φ,
      (hdata.castEndpoints h0 h1).cast hsplitPath hmergedPath⟩

/--
%%handwave
name:
  Ordered adjacent subpaths reparameterize to the merged subpath, allowing endpoints
statement:
  If \(a \le b \le c\), then following the subpath from \(a\) to \(b\) and
  then from \(b\) to \(c\) is an order-preserving reparameterization of the
  single subpath from \(a\) to \(c\).
proof:
  When both inequalities are strict this is the interior unit-split
  construction.  If one side is an equality, the degenerate subpath is a
  constant initial or terminal path, and the corresponding collapse
  reparameterization applies.
-/
theorem exists_pathOrderReparamData_orderedSubpathMerge_of_le
    {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y) (a b c : unitInterval)
    (hab : a ≤ b) (hbc : b ≤ c) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        ((γ.subpath a b).trans (γ.subpath b c))
        (γ.subpath a c) φ := by
  by_cases hablt : a < b
  · by_cases hbclt : b < c
    · exact exists_pathOrderReparamData_orderedSubpathMerge_of_lt
        γ a b c hablt hbclt
    · have hbc_eq : b = c := le_antisymm hbc (le_of_not_gt hbclt)
      subst c
      rcases exists_pathOrderReparamData_trans_refl_right
          (γ.subpath a b) with
        ⟨φ, hdata⟩
      exact ⟨φ, by simpa using hdata⟩
  · have hab_eq : a = b := le_antisymm hab (le_of_not_gt hablt)
    subst b
    rcases exists_pathOrderReparamData_refl_trans_left
        (γ.subpath a c) with
      ⟨φ, hdata⟩
    exact ⟨φ, by simpa using hdata⟩

/--
%%handwave
name:
  Reassociating three concatenated paths
statement:
  The path \(p * (q * r)\) is an order-preserving reparameterization of
  \((p * q) * r\).
proof:
  Use the piecewise-linear parameter change sending the subdivision
  \(0,\frac12,\frac34,1\) to \(0,\frac14,\frac12,1\).  Its inverse supplies
  the interval-control condition.
-/
theorem exists_pathOrderReparamData_trans_assoc_right_to_left
    {X : Type*} [TopologicalSpace X]
    {x₀ x₁ x₂ x₃ : X}
    (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        (p.trans (q.trans r))
        ((p.trans q).trans r) φ := by
  let φ := unitInterval.reassocRightToLeft
  let ψ := unitInterval.reassocLeftToRight
  refine ⟨φ, PathOrderReparamData.of_strong φ ψ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · exact unitInterval.reassocRightToLeft_zero
  · exact unitInterval.reassocRightToLeft_one
  · exact unitInterval.reassocRightToLeft_mono
  · intro a b t _hab hleft hright
    exact unitInterval.reassocLeftToRight_mem_interval_of_rightToLeft_bounds
      hleft hright
  · intro u
    change ((p.trans q).trans r) (unitInterval.reassocRightToLeft u) =
      (p.trans (q.trans r)) u
    by_cases hu₁ : (u : ℝ) ≤ 1 / 2
    · have hφ :
          (unitInterval.reassocRightToLeft u : ℝ) = (u : ℝ) / 2 :=
        unitInterval.coe_reassocRightToLeft_of_le_half u hu₁
      have hφ_half :
          (unitInterval.reassocRightToLeft u : ℝ) ≤ 1 / 2 := by
        nlinarith [unitInterval.le_one u, hφ]
      rw [path_trans_apply_of_le_half (p.trans q) r
          (unitInterval.reassocRightToLeft u) hφ_half,
        path_trans_apply_of_le_half p (q.trans r) u hu₁]
      have hdouble :
          unitInterval.doubleOfLeHalf
              (unitInterval.reassocRightToLeft u) hφ_half = u := by
        ext
        simp [unitInterval.doubleOfLeHalf, hφ]
        ring
      rw [hdouble]
      rw [path_trans_apply_of_le_half p q u hu₁]
    · by_cases hu₂ : (u : ℝ) ≤ 3 / 4
      · have hφ :
            (unitInterval.reassocRightToLeft u : ℝ) =
              (u : ℝ) - 1 / 4 :=
          unitInterval.coe_reassocRightToLeft_of_half_lt_of_le_three_quarters
            u hu₁ hu₂
        have hφ_half :
            (unitInterval.reassocRightToLeft u : ℝ) ≤ 1 / 2 := by
          nlinarith [hφ, hu₂]
        have hφ_not_quarter :
            ¬ (unitInterval.doubleOfLeHalf
                (unitInterval.reassocRightToLeft u) hφ_half : ℝ) ≤ 1 / 2 := by
          intro h
          have hreal :
              2 * (unitInterval.reassocRightToLeft u : ℝ) ≤ 1 / 2 := by
            simpa [unitInterval.doubleOfLeHalf] using h
          have hu_le : (u : ℝ) ≤ 1 / 2 := by
            nlinarith [hφ, hreal]
          exact hu₁ hu_le
        have hu_half : (1 / 2 : ℝ) ≤ u := le_of_lt (lt_of_not_ge hu₁)
        have hu_inner :
            (unitInterval.doubleSubOneOfHalfLe u hu_half : ℝ) ≤ 1 / 2 := by
          simp [unitInterval.doubleSubOneOfHalfLe]
          nlinarith [hu₂]
        rw [path_trans_apply_of_le_half (p.trans q) r
            (unitInterval.reassocRightToLeft u) hφ_half,
          path_trans_apply_of_half_le p (q.trans r) u hu_half]
        rw [path_trans_apply_of_half_le p q
          (unitInterval.doubleOfLeHalf
            (unitInterval.reassocRightToLeft u) hφ_half)
          (le_of_not_gt (by
            intro hlt
            exact hφ_not_quarter hlt.le))]
        rw [path_trans_apply_of_le_half q r
          (unitInterval.doubleSubOneOfHalfLe u hu_half) hu_inner]
        apply congrArg q
        ext
        simp [unitInterval.doubleOfLeHalf,
          unitInterval.doubleSubOneOfHalfLe, hφ]
        ring
      · have hφ :
            (unitInterval.reassocRightToLeft u : ℝ) =
              2 * (u : ℝ) - 1 :=
          unitInterval.coe_reassocRightToLeft_of_three_quarters_lt
            u hu₁ hu₂
        have hφ_half :
            (1 / 2 : ℝ) ≤ unitInterval.reassocRightToLeft u := by
          change (1 / 2 : ℝ) ≤ (unitInterval.reassocRightToLeft u : ℝ)
          nlinarith [hφ, le_of_lt (lt_of_not_ge hu₂)]
        have hu_half : (1 / 2 : ℝ) ≤ u := le_of_lt (lt_of_not_ge hu₁)
        have hu_inner_half :
            (1 / 2 : ℝ) ≤
              unitInterval.doubleSubOneOfHalfLe u hu_half := by
          change (1 / 2 : ℝ) ≤
            (unitInterval.doubleSubOneOfHalfLe u hu_half : ℝ)
          simp [unitInterval.doubleSubOneOfHalfLe]
          nlinarith [le_of_lt (lt_of_not_ge hu₂)]
        rw [path_trans_apply_of_half_le (p.trans q) r
            (unitInterval.reassocRightToLeft u) hφ_half,
          path_trans_apply_of_half_le p (q.trans r) u hu_half]
        rw [path_trans_apply_of_half_le q r
          (unitInterval.doubleSubOneOfHalfLe u hu_half) hu_inner_half]
        apply congrArg r
        ext
        simp [unitInterval.doubleSubOneOfHalfLe, hφ]
  · intro t
    change ((p.trans q).trans r) t =
      (p.trans (q.trans r)) (unitInterval.reassocLeftToRight t)
    by_cases ht₁ : (t : ℝ) ≤ 1 / 4
    · have hψ :
          (unitInterval.reassocLeftToRight t : ℝ) = 2 * (t : ℝ) :=
        unitInterval.coe_reassocLeftToRight_of_le_quarter t ht₁
      have hψ_half :
          (unitInterval.reassocLeftToRight t : ℝ) ≤ 1 / 2 := by
        nlinarith [hψ, ht₁]
      have ht_half : (t : ℝ) ≤ 1 / 2 := by nlinarith
      rw [path_trans_apply_of_le_half (p.trans q) r t ht_half,
        path_trans_apply_of_le_half p (q.trans r)
          (unitInterval.reassocLeftToRight t) hψ_half]
      have ht_inner :
          (unitInterval.doubleOfLeHalf t ht_half : ℝ) ≤ 1 / 2 := by
        simp [unitInterval.doubleOfLeHalf]
        nlinarith [ht₁]
      rw [path_trans_apply_of_le_half p q
        (unitInterval.doubleOfLeHalf t ht_half) ht_inner]
      apply congrArg p
      ext
      simp [unitInterval.doubleOfLeHalf, hψ]
    · by_cases ht₂ : (t : ℝ) ≤ 1 / 2
      · have hψ :
            (unitInterval.reassocLeftToRight t : ℝ) =
              (t : ℝ) + 1 / 4 :=
          unitInterval.coe_reassocLeftToRight_of_quarter_lt_of_le_half
            t ht₁ ht₂
        have hψ_half :
            ¬ (unitInterval.reassocLeftToRight t : ℝ) ≤ 1 / 2 := by
          intro h
          exact ht₁ (by nlinarith [hψ, h])
        have ht_inner_half :
            (1 / 2 : ℝ) ≤
              unitInterval.doubleOfLeHalf t ht₂ := by
          change (1 / 2 : ℝ) ≤
            (unitInterval.doubleOfLeHalf t ht₂ : ℝ)
          simp [unitInterval.doubleOfLeHalf]
          nlinarith [le_of_lt (lt_of_not_ge ht₁)]
        have hψ_inner :
            (unitInterval.doubleSubOneOfHalfLe
              (unitInterval.reassocLeftToRight t)
              (le_of_not_gt (by
                intro hlt
                exact hψ_half hlt.le)) : ℝ) ≤ 1 / 2 := by
          simp [unitInterval.doubleSubOneOfHalfLe, hψ]
          nlinarith [ht₂]
        rw [path_trans_apply_of_le_half (p.trans q) r t ht₂,
          path_trans_apply_of_half_le p (q.trans r)
            (unitInterval.reassocLeftToRight t)
            (le_of_not_gt (by
              intro hlt
              exact hψ_half hlt.le))]
        rw [path_trans_apply_of_half_le p q
          (unitInterval.doubleOfLeHalf t ht₂) ht_inner_half]
        rw [path_trans_apply_of_le_half q r
          (unitInterval.doubleSubOneOfHalfLe
            (unitInterval.reassocLeftToRight t)
            (le_of_not_gt (by
              intro hlt
              exact hψ_half hlt.le))) hψ_inner]
        apply congrArg q
        ext
        simp [unitInterval.doubleOfLeHalf,
          unitInterval.doubleSubOneOfHalfLe, hψ]
        ring
      · have hψ :
            (unitInterval.reassocLeftToRight t : ℝ) =
              ((t : ℝ) + 1) / 2 :=
          unitInterval.coe_reassocLeftToRight_of_half_lt t ht₁ ht₂
        have hψ_half :
            ¬ (unitInterval.reassocLeftToRight t : ℝ) ≤ 1 / 2 := by
          intro h
          exact ht₂ (by nlinarith [hψ, h])
        have ht_half : (1 / 2 : ℝ) ≤ t :=
          le_of_lt (lt_of_not_ge ht₂)
        have hψ_inner_half :
            (1 / 2 : ℝ) ≤
              unitInterval.doubleSubOneOfHalfLe
                (unitInterval.reassocLeftToRight t)
                (le_of_not_gt (by
                  intro hlt
                  exact hψ_half hlt.le)) := by
          change (1 / 2 : ℝ) ≤
            (unitInterval.doubleSubOneOfHalfLe
              (unitInterval.reassocLeftToRight t)
              (le_of_not_gt (by
                intro hlt
                exact hψ_half hlt.le)) : ℝ)
          simp [unitInterval.doubleSubOneOfHalfLe, hψ]
          nlinarith [ht_half]
        rw [path_trans_apply_of_half_le (p.trans q) r t ht_half,
          path_trans_apply_of_half_le p (q.trans r)
            (unitInterval.reassocLeftToRight t)
            (le_of_not_gt (by
              intro hlt
              exact hψ_half hlt.le))]
        rw [path_trans_apply_of_half_le q r
          (unitInterval.doubleSubOneOfHalfLe
            (unitInterval.reassocLeftToRight t)
            (le_of_not_gt (by
              intro hlt
              exact hψ_half hlt.le))) hψ_inner_half]
        apply congrArg r
        ext
        simp [unitInterval.doubleSubOneOfHalfLe, hψ]
        ring

/--
%%handwave
name:
  Reassociating three concatenated paths in the opposite direction
statement:
  The path \((p * q) * r\) is an order-preserving reparameterization of
  \(p * (q * r)\).
proof:
  Use the inverse piecewise-linear parameter change to the one in the previous
  reassociation theorem.  The inverse map supplies the same interval-control
  condition with the roles reversed.
-/
theorem exists_pathOrderReparamData_trans_assoc_left_to_right
    {X : Type*} [TopologicalSpace X]
    {x₀ x₁ x₂ x₃ : X}
    (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        ((p.trans q).trans r)
        (p.trans (q.trans r)) φ := by
  let φ := unitInterval.reassocLeftToRight
  let ψ := unitInterval.reassocRightToLeft
  refine ⟨φ, PathOrderReparamData.of_strong φ ψ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · exact unitInterval.reassocLeftToRight_zero
  · exact unitInterval.reassocLeftToRight_one
  · exact unitInterval.reassocLeftToRight_mono
  · intro a b t _hab hleft hright
    exact unitInterval.reassocRightToLeft_mem_interval_of_leftToRight_bounds
      hleft hright
  · intro u
    change (p.trans (q.trans r)) (unitInterval.reassocLeftToRight u) =
      ((p.trans q).trans r) u
    by_cases hu₁ : (u : ℝ) ≤ 1 / 4
    · have hφ :
          (unitInterval.reassocLeftToRight u : ℝ) = 2 * (u : ℝ) :=
        unitInterval.coe_reassocLeftToRight_of_le_quarter u hu₁
      have hφ_half :
          (unitInterval.reassocLeftToRight u : ℝ) ≤ 1 / 2 := by
        nlinarith [hφ, hu₁]
      have hu_half : (u : ℝ) ≤ 1 / 2 := by nlinarith
      rw [path_trans_apply_of_le_half p (q.trans r)
          (unitInterval.reassocLeftToRight u) hφ_half,
        path_trans_apply_of_le_half (p.trans q) r u hu_half]
      have hu_inner :
          (unitInterval.doubleOfLeHalf u hu_half : ℝ) ≤ 1 / 2 := by
        simp [unitInterval.doubleOfLeHalf]
        nlinarith [hu₁]
      rw [path_trans_apply_of_le_half p q
        (unitInterval.doubleOfLeHalf u hu_half) hu_inner]
      apply congrArg p
      ext
      simp [unitInterval.doubleOfLeHalf, hφ]
    · by_cases hu₂ : (u : ℝ) ≤ 1 / 2
      · have hφ :
            (unitInterval.reassocLeftToRight u : ℝ) =
              (u : ℝ) + 1 / 4 :=
          unitInterval.coe_reassocLeftToRight_of_quarter_lt_of_le_half
            u hu₁ hu₂
        have hφ_half :
            ¬ (unitInterval.reassocLeftToRight u : ℝ) ≤ 1 / 2 := by
          intro h
          exact hu₁ (by nlinarith [hφ, h])
        have hu_inner_half :
            (1 / 2 : ℝ) ≤
              unitInterval.doubleOfLeHalf u hu₂ := by
          change (1 / 2 : ℝ) ≤
            (unitInterval.doubleOfLeHalf u hu₂ : ℝ)
          simp [unitInterval.doubleOfLeHalf]
          nlinarith [le_of_lt (lt_of_not_ge hu₁)]
        have hφ_inner :
            (unitInterval.doubleSubOneOfHalfLe
              (unitInterval.reassocLeftToRight u)
              (le_of_not_gt (by
                intro hlt
                exact hφ_half hlt.le)) : ℝ) ≤ 1 / 2 := by
          simp [unitInterval.doubleSubOneOfHalfLe, hφ]
          nlinarith [hu₂]
        rw [path_trans_apply_of_half_le p (q.trans r)
            (unitInterval.reassocLeftToRight u)
            (le_of_not_gt (by
              intro hlt
              exact hφ_half hlt.le)),
          path_trans_apply_of_le_half (p.trans q) r u hu₂]
        rw [path_trans_apply_of_le_half q r
          (unitInterval.doubleSubOneOfHalfLe
            (unitInterval.reassocLeftToRight u)
            (le_of_not_gt (by
              intro hlt
              exact hφ_half hlt.le))) hφ_inner]
        rw [path_trans_apply_of_half_le p q
          (unitInterval.doubleOfLeHalf u hu₂) hu_inner_half]
        apply congrArg q
        ext
        simp [unitInterval.doubleOfLeHalf,
          unitInterval.doubleSubOneOfHalfLe, hφ]
        ring
      · have hφ :
            (unitInterval.reassocLeftToRight u : ℝ) =
              ((u : ℝ) + 1) / 2 :=
          unitInterval.coe_reassocLeftToRight_of_half_lt u hu₁ hu₂
        have hφ_half :
            ¬ (unitInterval.reassocLeftToRight u : ℝ) ≤ 1 / 2 := by
          intro h
          exact hu₂ (by nlinarith [hφ, h])
        have hu_half : (1 / 2 : ℝ) ≤ u :=
          le_of_lt (lt_of_not_ge hu₂)
        have hφ_inner_half :
            (1 / 2 : ℝ) ≤
              unitInterval.doubleSubOneOfHalfLe
                (unitInterval.reassocLeftToRight u)
                (le_of_not_gt (by
                  intro hlt
                  exact hφ_half hlt.le)) := by
          change (1 / 2 : ℝ) ≤
            (unitInterval.doubleSubOneOfHalfLe
              (unitInterval.reassocLeftToRight u)
              (le_of_not_gt (by
                intro hlt
                exact hφ_half hlt.le)) : ℝ)
          simp [unitInterval.doubleSubOneOfHalfLe, hφ]
          nlinarith [hu_half]
        rw [path_trans_apply_of_half_le p (q.trans r)
            (unitInterval.reassocLeftToRight u)
            (le_of_not_gt (by
              intro hlt
              exact hφ_half hlt.le)),
          path_trans_apply_of_half_le (p.trans q) r u hu_half]
        rw [path_trans_apply_of_half_le q r
          (unitInterval.doubleSubOneOfHalfLe
            (unitInterval.reassocLeftToRight u)
            (le_of_not_gt (by
              intro hlt
              exact hφ_half hlt.le))) hφ_inner_half]
        apply congrArg r
        ext
        simp [unitInterval.doubleSubOneOfHalfLe, hφ]
        ring
  · intro t
    change (p.trans (q.trans r)) t =
      ((p.trans q).trans r) (unitInterval.reassocRightToLeft t)
    by_cases ht₁ : (t : ℝ) ≤ 1 / 2
    · have hψ :
          (unitInterval.reassocRightToLeft t : ℝ) = (t : ℝ) / 2 :=
        unitInterval.coe_reassocRightToLeft_of_le_half t ht₁
      have hψ_half :
          (unitInterval.reassocRightToLeft t : ℝ) ≤ 1 / 2 := by
        nlinarith [unitInterval.le_one t, hψ]
      rw [path_trans_apply_of_le_half p (q.trans r) t ht₁,
        path_trans_apply_of_le_half (p.trans q) r
          (unitInterval.reassocRightToLeft t) hψ_half]
      have hdouble :
          unitInterval.doubleOfLeHalf
              (unitInterval.reassocRightToLeft t) hψ_half = t := by
        ext
        simp [unitInterval.doubleOfLeHalf, hψ]
        ring
      rw [hdouble]
      rw [path_trans_apply_of_le_half p q t ht₁]
    · by_cases ht₂ : (t : ℝ) ≤ 3 / 4
      · have hψ :
            (unitInterval.reassocRightToLeft t : ℝ) =
              (t : ℝ) - 1 / 4 :=
          unitInterval.coe_reassocRightToLeft_of_half_lt_of_le_three_quarters
            t ht₁ ht₂
        have hψ_half :
            (unitInterval.reassocRightToLeft t : ℝ) ≤ 1 / 2 := by
          nlinarith [hψ, ht₂]
        have hψ_not_quarter :
            ¬ (unitInterval.doubleOfLeHalf
                (unitInterval.reassocRightToLeft t) hψ_half : ℝ) ≤ 1 / 2 := by
          intro h
          have hreal :
              2 * (unitInterval.reassocRightToLeft t : ℝ) ≤ 1 / 2 := by
            simpa [unitInterval.doubleOfLeHalf] using h
          have ht_le : (t : ℝ) ≤ 1 / 2 := by
            nlinarith [hψ, hreal]
          exact ht₁ ht_le
        have ht_half : (1 / 2 : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht₁)
        have ht_inner :
            (unitInterval.doubleSubOneOfHalfLe t ht_half : ℝ) ≤ 1 / 2 := by
          simp [unitInterval.doubleSubOneOfHalfLe]
          nlinarith [ht₂]
        rw [path_trans_apply_of_half_le p (q.trans r) t ht_half,
          path_trans_apply_of_le_half (p.trans q) r
            (unitInterval.reassocRightToLeft t) hψ_half]
        rw [path_trans_apply_of_le_half q r
          (unitInterval.doubleSubOneOfHalfLe t ht_half) ht_inner]
        rw [path_trans_apply_of_half_le p q
          (unitInterval.doubleOfLeHalf
            (unitInterval.reassocRightToLeft t) hψ_half)
          (le_of_not_gt (by
            intro hlt
            exact hψ_not_quarter hlt.le))]
        apply congrArg q
        ext
        simp [unitInterval.doubleOfLeHalf,
          unitInterval.doubleSubOneOfHalfLe, hψ]
        ring
      · have hψ :
            (unitInterval.reassocRightToLeft t : ℝ) =
              2 * (t : ℝ) - 1 :=
          unitInterval.coe_reassocRightToLeft_of_three_quarters_lt
            t ht₁ ht₂
        have hψ_half :
            (1 / 2 : ℝ) ≤ unitInterval.reassocRightToLeft t := by
          change (1 / 2 : ℝ) ≤ (unitInterval.reassocRightToLeft t : ℝ)
          nlinarith [hψ, le_of_lt (lt_of_not_ge ht₂)]
        have ht_half : (1 / 2 : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht₁)
        have ht_inner_half :
            (1 / 2 : ℝ) ≤
              unitInterval.doubleSubOneOfHalfLe t ht_half := by
          change (1 / 2 : ℝ) ≤
            (unitInterval.doubleSubOneOfHalfLe t ht_half : ℝ)
          simp [unitInterval.doubleSubOneOfHalfLe]
          nlinarith [le_of_lt (lt_of_not_ge ht₂)]
        rw [path_trans_apply_of_half_le p (q.trans r) t ht_half,
          path_trans_apply_of_half_le (p.trans q) r
            (unitInterval.reassocRightToLeft t) hψ_half]
        rw [path_trans_apply_of_half_le q r
          (unitInterval.doubleSubOneOfHalfLe t ht_half) ht_inner_half]
        apply congrArg r
        ext
        simp [unitInterval.doubleSubOneOfHalfLe, hψ]

/--
%%handwave
name:
  Appending a common suffix preserves ordered reparameterization
statement:
  If one path order-reparameterizes to another, then appending the same
  suffix to both paths preserves the ordered reparameterization.
proof:
  On the first half of the concatenated paths use the given reparameterization,
  rescaled into the first half.  On the second half use the identity parameter.
  The interval-image condition is checked by splitting according to whether
  the target parameter lies in the first or second half.
-/
theorem exists_pathOrderReparamData_trans_right
    {X : Type*} [TopologicalSpace X]
    {x₀ x₁ x₂ : X} {p q : Path x₀ x₁}
    {φ : unitInterval → unitInterval}
    (hdata : PathOrderReparamData p q φ)
    (s : Path x₁ x₂) :
    ∃ Φ : unitInterval → unitInterval,
      PathOrderReparamData (p.trans s) (q.trans s) Φ := by
  rcases hdata with
    ⟨hφ_zero, hφ_one, hφ_mono, hsample, hinterval⟩
  let Φ : unitInterval → unitInterval :=
    fun u ↦
      if hu : (u : ℝ) ≤ 1 / 2 then
        unitInterval.firstHalf (φ (unitInterval.doubleOfLeHalf u hu))
      else
        u
  have hΦ_of_le :
      ∀ (u : unitInterval) (hu : (u : ℝ) ≤ 1 / 2),
        Φ u = unitInterval.firstHalf
          (φ (unitInterval.doubleOfLeHalf u hu)) := by
    intro u hu
    unfold Φ
    rw [dif_pos hu]
  have hΦ_of_not_le :
      ∀ (u : unitInterval) (hu : ¬ (u : ℝ) ≤ 1 / 2), Φ u = u := by
    intro u hu
    unfold Φ
    rw [dif_neg hu]
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΦ_of_le 0 (by norm_num)]
    simp [hφ_zero, unitInterval.firstHalf, unitInterval.doubleOfLeHalf]
  · rw [hΦ_of_not_le 1 (by norm_num)]
  · intro a b hab
    change (Φ a : ℝ) ≤ (Φ b : ℝ)
    by_cases ha : (a : ℝ) ≤ 1 / 2
    · by_cases hb : (b : ℝ) ≤ 1 / 2
      · have hdouble :
            unitInterval.doubleOfLeHalf a ha ≤
              unitInterval.doubleOfLeHalf b hb := by
          change 2 * (a : ℝ) ≤ 2 * (b : ℝ)
          nlinarith [show (a : ℝ) ≤ b from hab]
        have hφ := hφ_mono hdouble
        have hΦa :
            (Φ a : ℝ) =
              (φ (unitInterval.doubleOfLeHalf a ha) : ℝ) / 2 := by
          rw [hΦ_of_le a ha]
          simp [unitInterval.firstHalf]
        have hΦb :
            (Φ b : ℝ) =
              (φ (unitInterval.doubleOfLeHalf b hb) : ℝ) / 2 := by
          rw [hΦ_of_le b hb]
          simp [unitInterval.firstHalf]
        rw [hΦa, hΦb]
        nlinarith [show
          (φ (unitInterval.doubleOfLeHalf a ha) : ℝ) ≤
            φ (unitInterval.doubleOfLeHalf b hb) from hφ]
      · have hΦa_le : (Φ a : ℝ) ≤ 1 / 2 := by
          have hunit :
              (φ (unitInterval.doubleOfLeHalf a ha) : ℝ) ≤ 1 :=
            unitInterval.le_one _
          have hΦa :
              (Φ a : ℝ) =
                (φ (unitInterval.doubleOfLeHalf a ha) : ℝ) / 2 := by
            rw [hΦ_of_le a ha]
            simp [unitInterval.firstHalf]
          rw [hΦa]
          nlinarith
        have hΦb : (Φ b : ℝ) = (b : ℝ) := by
          rw [hΦ_of_not_le b hb]
        rw [hΦb]
        nlinarith [hΦa_le, le_of_lt (lt_of_not_ge hb)]
    · have hb : ¬ (b : ℝ) ≤ 1 / 2 := by
        intro hb
        exact ha ((show (a : ℝ) ≤ b from hab).trans hb)
      rw [hΦ_of_not_le a ha, hΦ_of_not_le b hb]
      exact hab
  · intro u
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · let u' := unitInterval.doubleOfLeHalf u hu
      have hΦu :
          Φ u = unitInterval.firstHalf (φ u') := by
        rw [hΦ_of_le u hu]
      rw [path_trans_apply_of_le_half p s u hu, hΦu,
        path_trans_firstHalf_apply q s (φ u')]
      exact hsample u'
    · have hu_half : (1 / 2 : ℝ) ≤ u :=
        le_of_lt (lt_of_not_ge hu)
      have hΦu : Φ u = u := by
        exact hΦ_of_not_le u hu
      rw [hΦu, path_trans_apply_of_half_le q s u hu_half,
        path_trans_apply_of_half_le p s u hu_half]
  · intro a b t hab hleft hright
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · by_cases ha : (a : ℝ) ≤ 1 / 2
      · let a' := unitInterval.doubleOfLeHalf a ha
        let t' := unitInterval.doubleOfLeHalf t ht
        by_cases hb : (b : ℝ) ≤ 1 / 2
        · let b' := unitInterval.doubleOfLeHalf b hb
          have hab' : a' ≤ b' := by
            change 2 * (a : ℝ) ≤ 2 * (b : ℝ)
            nlinarith [show (a : ℝ) ≤ b from hab]
          have hleft' : φ a' ≤ t' := by
            change (φ a' : ℝ) ≤ (t' : ℝ)
            have hleft_real : (Φ a : ℝ) ≤ (t : ℝ) := by
              exact_mod_cast hleft
            have hleft_half :
                (φ a' : ℝ) / 2 ≤ (t : ℝ) := by
              rw [hΦ_of_le a ha] at hleft_real
              simpa [unitInterval.firstHalf, a'] using hleft_real
            simp [t', unitInterval.doubleOfLeHalf]
            nlinarith
          have hright' : t' ≤ φ b' := by
            change (t' : ℝ) ≤ (φ b' : ℝ)
            have hright_real : (t : ℝ) ≤ (Φ b : ℝ) := by
              exact_mod_cast hright
            have hright_half :
                (t : ℝ) ≤ (φ b' : ℝ) / 2 := by
              rw [hΦ_of_le b hb] at hright_real
              simpa [unitInterval.firstHalf, b'] using hright_real
            simp [t', unitInterval.doubleOfLeHalf]
            nlinarith
          rcases hinterval hab' hleft' hright' with
            ⟨u', hu_left, hu_right, hqt⟩
          refine ⟨unitInterval.firstHalf u', ?_, ?_, ?_⟩
          · have hmono :
                unitInterval.firstHalf a' ≤ unitInterval.firstHalf u' := by
              change (a' : ℝ) / 2 ≤ (u' : ℝ) / 2
              nlinarith [show (a' : ℝ) ≤ u' from hu_left]
            simpa [a'] using hmono
          · have hmono :
                unitInterval.firstHalf u' ≤ unitInterval.firstHalf b' := by
              change (u' : ℝ) / 2 ≤ (b' : ℝ) / 2
              nlinarith [show (u' : ℝ) ≤ b' from hu_right]
            simpa [b'] using hmono
          · calc
              (q.trans s) t = q t' := by
                rw [path_trans_apply_of_le_half q s t ht]
              _ = p u' := hqt
              _ = (p.trans s) (unitInterval.firstHalf u') := by
                rw [path_trans_firstHalf_apply p s u']
        · have hab' : a' ≤ (1 : unitInterval) := unitInterval.le_one _
          have hleft' : φ a' ≤ t' := by
            change (φ a' : ℝ) ≤ (t' : ℝ)
            have hleft_real : (Φ a : ℝ) ≤ (t : ℝ) := by
              exact_mod_cast hleft
            have hleft_half :
                (φ a' : ℝ) / 2 ≤ (t : ℝ) := by
              rw [hΦ_of_le a ha] at hleft_real
              simpa [unitInterval.firstHalf, a'] using hleft_real
            simp [t', unitInterval.doubleOfLeHalf]
            nlinarith
          have hright' : t' ≤ φ 1 := by
            rw [hφ_one]
            exact unitInterval.le_one t'
          rcases hinterval hab' hleft' hright' with
            ⟨u', hu_left, _hu_right, hqt⟩
          refine ⟨unitInterval.firstHalf u', ?_, ?_, ?_⟩
          · have hmono :
                unitInterval.firstHalf a' ≤ unitInterval.firstHalf u' := by
              change (a' : ℝ) / 2 ≤ (u' : ℝ) / 2
              nlinarith [show (a' : ℝ) ≤ u' from hu_left]
            simpa [a'] using hmono
          · change (u' : ℝ) / 2 ≤ (b : ℝ)
            nlinarith [unitInterval.le_one u',
              le_of_lt (lt_of_not_ge hb)]
          · calc
              (q.trans s) t = q t' := by
                rw [path_trans_apply_of_le_half q s t ht]
              _ = p u' := hqt
              _ = (p.trans s) (unitInterval.firstHalf u') := by
                rw [path_trans_firstHalf_apply p s u']
      · have hΦa : Φ a = a := by
          exact hΦ_of_not_le a ha
        have hleft_real : (a : ℝ) ≤ (t : ℝ) := by
          exact_mod_cast (by simpa [hΦa] using hleft)
        have ha_half_lt : (1 / 2 : ℝ) < a := lt_of_not_ge ha
        exact False.elim (by nlinarith [hleft_real, ht, ha_half_lt])
    · have ht_half : (1 / 2 : ℝ) ≤ t :=
        le_of_lt (lt_of_not_ge ht)
      have hu_left : a ≤ t := by
        by_cases ha : (a : ℝ) ≤ 1 / 2
        · change (a : ℝ) ≤ (t : ℝ)
          nlinarith [ha, ht_half]
        · have hΦa : Φ a = a := by
            exact hΦ_of_not_le a ha
          simpa [hΦa] using hleft
      have hu_right : t ≤ b := by
        by_cases hb : (b : ℝ) ≤ 1 / 2
        · have hright_real : (t : ℝ) ≤ (Φ b : ℝ) := by
            exact_mod_cast hright
          have hΦb_le : (Φ b : ℝ) ≤ 1 / 2 := by
            have hunit :
                (φ (unitInterval.doubleOfLeHalf b hb) : ℝ) ≤ 1 :=
              unitInterval.le_one _
            have hΦb :
                (Φ b : ℝ) =
                  (φ (unitInterval.doubleOfLeHalf b hb) : ℝ) / 2 := by
              rw [hΦ_of_le b hb]
              simp [unitInterval.firstHalf]
            rw [hΦb]
            nlinarith
          exact False.elim (by
            nlinarith [hright_real, hΦb_le, lt_of_not_ge ht])
        · have hΦb : Φ b = b := by
            exact hΦ_of_not_le b hb
          simpa [hΦb] using hright
      refine ⟨t, hu_left, hu_right, ?_⟩
      rw [path_trans_apply_of_half_le q s t ht_half,
        path_trans_apply_of_half_le p s t ht_half]

/--
%%handwave
name:
  Prepending a common prefix preserves ordered reparameterization
statement:
  If one path order-reparameterizes to another, then prepending the same
  prefix to both paths preserves the ordered reparameterization.
proof:
  On the first half of the concatenated paths use the identity parameter.  On
  the second half use the given reparameterization, rescaled into the second
  half.  The interval-image condition is checked by splitting according to
  whether the target parameter lies in the common prefix or in the rescaled
  suffix.
-/
theorem exists_pathOrderReparamData_trans_left
    {X : Type*} [TopologicalSpace X]
    {x₀ x₁ x₂ : X} {p q : Path x₁ x₂}
    {φ : unitInterval → unitInterval}
    (s : Path x₀ x₁)
    (hdata : PathOrderReparamData p q φ) :
    ∃ Φ : unitInterval → unitInterval,
      PathOrderReparamData (s.trans p) (s.trans q) Φ := by
  rcases hdata with
    ⟨hφ_zero, hφ_one, hφ_mono, hsample, hinterval⟩
  let Φ : unitInterval → unitInterval :=
    fun u ↦
      if hu : (u : ℝ) ≤ 1 / 2 then
        u
      else
        unitInterval.secondHalf
          (φ (unitInterval.doubleSubOneOfHalfLe u
            (le_of_lt (lt_of_not_ge hu))))
  have hΦ_of_le :
      ∀ (u : unitInterval) (hu : (u : ℝ) ≤ 1 / 2), Φ u = u := by
    intro u hu
    unfold Φ
    rw [dif_pos hu]
  have hΦ_of_not_le :
      ∀ (u : unitInterval) (hu : ¬ (u : ℝ) ≤ 1 / 2),
        Φ u = unitInterval.secondHalf
          (φ (unitInterval.doubleSubOneOfHalfLe u
            (le_of_lt (lt_of_not_ge hu)))) := by
    intro u hu
    unfold Φ
    rw [dif_neg hu]
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΦ_of_le 0 (by norm_num)]
  · rw [hΦ_of_not_le 1 (by norm_num)]
    have harg :
        unitInterval.doubleSubOneOfHalfLe (1 : unitInterval)
          (by norm_num) = 1 := by
      ext
      norm_num [unitInterval.doubleSubOneOfHalfLe]
    rw [harg, hφ_one]
    exact unitInterval.secondHalf_one
  · intro a b hab
    change (Φ a : ℝ) ≤ (Φ b : ℝ)
    by_cases ha : (a : ℝ) ≤ 1 / 2
    · by_cases hb : (b : ℝ) ≤ 1 / 2
      · rw [hΦ_of_le a ha, hΦ_of_le b hb]
        exact hab
      · have hΦb_ge : (1 / 2 : ℝ) ≤ Φ b := by
          rw [hΦ_of_not_le b hb]
          exact unitInterval.half_le_secondHalf _
        rw [hΦ_of_le a ha]
        nlinarith [ha, hΦb_ge]
    · have hb : ¬ (b : ℝ) ≤ 1 / 2 := by
        intro hb
        exact ha ((show (a : ℝ) ≤ b from hab).trans hb)
      let a' := unitInterval.doubleSubOneOfHalfLe a
        (le_of_lt (lt_of_not_ge ha))
      let b' := unitInterval.doubleSubOneOfHalfLe b
        (le_of_lt (lt_of_not_ge hb))
      have hab' : a' ≤ b' := by
        change 2 * (a : ℝ) - 1 ≤ 2 * (b : ℝ) - 1
        nlinarith [show (a : ℝ) ≤ b from hab]
      have hφ := hφ_mono hab'
      have hΦa :
          (Φ a : ℝ) = (1 + (φ a' : ℝ)) / 2 := by
        rw [hΦ_of_not_le a ha]
        simp [unitInterval.secondHalf, a']
      have hΦb :
          (Φ b : ℝ) = (1 + (φ b' : ℝ)) / 2 := by
        rw [hΦ_of_not_le b hb]
        simp [unitInterval.secondHalf, b']
      rw [hΦa, hΦb]
      nlinarith [show (φ a' : ℝ) ≤ φ b' from hφ]
  · intro u
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · have hΦu : Φ u = u := hΦ_of_le u hu
      rw [hΦu, path_trans_apply_of_le_half s q u hu,
        path_trans_apply_of_le_half s p u hu]
    · have hu_half : (1 / 2 : ℝ) ≤ u :=
        le_of_lt (lt_of_not_ge hu)
      let u' := unitInterval.doubleSubOneOfHalfLe u hu_half
      have hΦu : Φ u = unitInterval.secondHalf (φ u') := by
        rw [hΦ_of_not_le u hu]
      rw [path_trans_apply_of_half_le s p u hu_half, hΦu,
        path_trans_secondHalf_apply s q (φ u')]
      exact hsample u'
  · intro a b t hab hleft hright
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · by_cases ha : (a : ℝ) ≤ 1 / 2
      · have hu_left : a ≤ t := by
          simpa [hΦ_of_le a ha] using hleft
        have hu_right : t ≤ b := by
          by_cases hb : (b : ℝ) ≤ 1 / 2
          · simpa [hΦ_of_le b hb] using hright
          · change (t : ℝ) ≤ (b : ℝ)
            nlinarith [ht, le_of_lt (lt_of_not_ge hb)]
        refine ⟨t, hu_left, hu_right, ?_⟩
        rw [path_trans_apply_of_le_half s q t ht,
          path_trans_apply_of_le_half s p t ht]
      · have ha_half : (1 / 2 : ℝ) ≤ a :=
          le_of_lt (lt_of_not_ge ha)
        let a' := unitInterval.doubleSubOneOfHalfLe a ha_half
        have hΦa_half : (1 / 2 : ℝ) ≤ Φ a := by
          rw [hΦ_of_not_le a ha]
          exact unitInterval.half_le_secondHalf _
        have ht_half : (1 / 2 : ℝ) = (t : ℝ) := by
          have hleft_real : (Φ a : ℝ) ≤ (t : ℝ) := by
            exact_mod_cast hleft
          nlinarith [hΦa_half, ht]
        have hΦa_eq_half : (Φ a : ℝ) = 1 / 2 := by
          have hleft_real : (Φ a : ℝ) ≤ (t : ℝ) := by
            exact_mod_cast hleft
          nlinarith [hΦa_half, ht]
        have hφa_zero : φ a' = 0 := by
          have hΦa :
              (Φ a : ℝ) = (1 + (φ a' : ℝ)) / 2 := by
            rw [hΦ_of_not_le a ha]
            simp [unitInterval.secondHalf, a']
          apply le_antisymm
          · change (φ a' : ℝ) ≤ 0
            nlinarith [hΦa, hΦa_eq_half]
          · exact unitInterval.nonneg (φ a')
        refine ⟨a, le_rfl, hab, ?_⟩
        have ht_half_le : (1 / 2 : ℝ) ≤ t := by
          nlinarith [ht_half]
        rw [path_trans_apply_of_half_le s q t ht_half_le,
          path_trans_apply_of_half_le s p a ha_half]
        have ht_zero :
            unitInterval.doubleSubOneOfHalfLe t ht_half_le = 0 := by
          ext
          simp [unitInterval.doubleSubOneOfHalfLe]
          nlinarith [ht_half]
        rw [ht_zero]
        simpa [hφa_zero] using hsample a'
    · have ht_half : (1 / 2 : ℝ) ≤ t :=
        le_of_lt (lt_of_not_ge ht)
      let t' := unitInterval.doubleSubOneOfHalfLe t ht_half
      by_cases hb : (b : ℝ) ≤ 1 / 2
      · have hΦb : Φ b = b := hΦ_of_le b hb
        have hright_real : (t : ℝ) ≤ (b : ℝ) := by
          exact_mod_cast (by simpa [hΦb] using hright)
        exact False.elim (by
          nlinarith [hright_real, hb, lt_of_not_ge ht])
      · let b' := unitInterval.doubleSubOneOfHalfLe b
          (le_of_lt (lt_of_not_ge hb))
        have hright' : t' ≤ φ b' := by
          change (t' : ℝ) ≤ (φ b' : ℝ)
          have hright_real : (t : ℝ) ≤ (Φ b : ℝ) := by
            exact_mod_cast hright
          have hright_half :
              (t : ℝ) ≤ (1 + (φ b' : ℝ)) / 2 := by
            rw [hΦ_of_not_le b hb] at hright_real
            simpa [unitInterval.secondHalf, b'] using hright_real
          simp [t', unitInterval.doubleSubOneOfHalfLe]
          nlinarith
        by_cases ha : (a : ℝ) ≤ 1 / 2
        · have hleft' : φ 0 ≤ t' := by
            rw [hφ_zero]
            exact unitInterval.nonneg t'
          have hb0 : (0 : unitInterval) ≤ b' := unitInterval.nonneg b'
          rcases hinterval hb0 hleft' hright' with
            ⟨u', hu_left, hu_right, hqt⟩
          refine ⟨unitInterval.secondHalf u', ?_, ?_, ?_⟩
          · change (a : ℝ) ≤ (1 + (u' : ℝ)) / 2
            nlinarith [ha, unitInterval.nonneg u']
          · have hmono :
                unitInterval.secondHalf u' ≤ unitInterval.secondHalf b' := by
              change (1 + (u' : ℝ)) / 2 ≤ (1 + (b' : ℝ)) / 2
              nlinarith [show (u' : ℝ) ≤ b' from hu_right]
            simpa [b'] using hmono
          · calc
              (s.trans q) t = q t' := by
                rw [path_trans_apply_of_half_le s q t ht_half]
              _ = p u' := hqt
              _ = (s.trans p) (unitInterval.secondHalf u') := by
                rw [path_trans_secondHalf_apply s p u']
        · have ha_half : (1 / 2 : ℝ) ≤ a :=
            le_of_lt (lt_of_not_ge ha)
          let a' := unitInterval.doubleSubOneOfHalfLe a ha_half
          have hab' : a' ≤ b' := by
            change 2 * (a : ℝ) - 1 ≤ 2 * (b : ℝ) - 1
            nlinarith [show (a : ℝ) ≤ b from hab]
          have hleft' : φ a' ≤ t' := by
            change (φ a' : ℝ) ≤ (t' : ℝ)
            have hleft_real : (Φ a : ℝ) ≤ (t : ℝ) := by
              exact_mod_cast hleft
            have hleft_half :
                (1 + (φ a' : ℝ)) / 2 ≤ (t : ℝ) := by
              rw [hΦ_of_not_le a ha] at hleft_real
              simpa [unitInterval.secondHalf, a'] using hleft_real
            simp [t', unitInterval.doubleSubOneOfHalfLe]
            nlinarith
          rcases hinterval hab' hleft' hright' with
            ⟨u', hu_left, hu_right, hqt⟩
          refine ⟨unitInterval.secondHalf u', ?_, ?_, ?_⟩
          · have hmono :
                unitInterval.secondHalf a' ≤ unitInterval.secondHalf u' := by
              change (1 + (a' : ℝ)) / 2 ≤ (1 + (u' : ℝ)) / 2
              nlinarith [show (a' : ℝ) ≤ u' from hu_left]
            simpa [a'] using hmono
          · have hmono :
                unitInterval.secondHalf u' ≤ unitInterval.secondHalf b' := by
              change (1 + (u' : ℝ)) / 2 ≤ (1 + (b' : ℝ)) / 2
              nlinarith [show (u' : ℝ) ≤ b' from hu_right]
            simpa [b'] using hmono
          · calc
              (s.trans q) t = q t' := by
                rw [path_trans_apply_of_half_le s q t ht_half]
              _ = p u' := hqt
              _ = (s.trans p) (unitInterval.secondHalf u') := by
                rw [path_trans_secondHalf_apply s p u']

/--
%%handwave
name:
  Upper column raw path reparameterizes to the upper raw cut path
statement:
  Before applying the public endpoint normalization, the decomposed upper
  column path is an order-preserving reparameterization of the raw cut path at
  the upper edge of the small rectangle.
proof:
  First reassociate \(p * (q * r)\) to \((p * q) * r\).  Then merge the two
  adjacent subpaths on the lower side of the strip.  Appending the common
  middle and terminal suffixes preserves the ordered reparameterizations.
-/
theorem exists_pathOrderReparamData_homotopyStripColumnTopPathRawCore_cutPathRawCore
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hr : r₀ ≤ r₁) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        (homotopyStripColumnTopPathRawCore F a b r₀ r₁)
        (homotopyStripCutPathRawCore F a b r₁) φ := by
  let γ := F.eval a
  let δ := (F.evalAt r₁).subpath a b
  let σ := (F.eval b).subpath r₁ 1
  let γ₀ := γ.subpath 0 r₀
  let γ₁ := γ.subpath r₀ r₁
  rcases exists_pathOrderReparamData_trans_assoc_right_to_left
      γ₀ γ₁ δ with
    ⟨φAssoc, hAssoc⟩
  rcases exists_pathOrderReparamData_trans_right hAssoc σ with
    ⟨φAssocSuffix, hAssocSuffix⟩
  have h0r₀ : (0 : unitInterval) ≤ r₀ := unitInterval.nonneg r₀
  rcases exists_pathOrderReparamData_orderedSubpathMerge_of_le
      γ 0 r₀ r₁ h0r₀ hr with
    ⟨φMerge, hMerge⟩
  rcases exists_pathOrderReparamData_trans_right hMerge δ with
    ⟨φMergeδ, hMergeδ⟩
  rcases exists_pathOrderReparamData_trans_right hMergeδ σ with
    ⟨φMergeδσ, hMergeδσ⟩
  refine ⟨φMergeδσ ∘ φAssocSuffix, ?_⟩
  exact
    (PathOrderReparamData.trans hAssocSuffix hMergeδσ).cast
      (by
        rfl)
      (by
        simp [homotopyStripCutPathRawCore, γ, δ, σ])

/--
%%handwave
name:
  Lower column raw path reparameterizes to the lower raw cut path
statement:
  Before applying the public endpoint normalization, the decomposed lower
  column path is an order-preserving reparameterization of the raw cut path at
  the lower edge of the small rectangle.
proof:
  Reassociate the common prefix past the lower-then-right boundary route.
  Then merge the two adjacent subpaths on the right edge, after prepending the
  common prefix.
-/
theorem exists_pathOrderReparamData_homotopyStripColumnBottomPathRawCore_cutPathRawCore
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hr : r₀ ≤ r₁) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        (homotopyStripColumnBottomPathRawCore F a b r₀ r₁)
        (homotopyStripCutPathRawCore F a b r₀) φ := by
  let γ := F.eval a
  let υ := F.eval b
  let δ := (F.evalAt r₀).subpath a b
  let ρ := υ.subpath r₀ r₁
  let σ := υ.subpath r₁ 1
  let γ₀ := γ.subpath 0 r₀
  let P := γ₀.trans δ
  rcases exists_pathOrderReparamData_trans_assoc_right_to_left
      γ₀ δ ρ with
    ⟨φAssoc₁, hAssoc₁⟩
  rcases exists_pathOrderReparamData_trans_right hAssoc₁ σ with
    ⟨φAssoc₁σ, hAssoc₁σ⟩
  rcases exists_pathOrderReparamData_trans_assoc_left_to_right
      P ρ σ with
    ⟨φAssoc₂, hAssoc₂⟩
  have hr₁1 : r₁ ≤ (1 : unitInterval) := unitInterval.le_one r₁
  rcases exists_pathOrderReparamData_orderedSubpathMerge_of_le
      υ r₀ r₁ 1 hr hr₁1 with
    ⟨φMerge, hMerge⟩
  rcases exists_pathOrderReparamData_trans_left P hMerge with
    ⟨φPrefMerge, hPrefMerge⟩
  refine ⟨φPrefMerge ∘ φAssoc₂ ∘ φAssoc₁σ, ?_⟩
  have hdata :
      PathOrderReparamData
        ((γ₀.trans (δ.trans ρ)).trans σ)
        (P.trans (υ.subpath r₀ 1))
        (φPrefMerge ∘ φAssoc₂ ∘ φAssoc₁σ) :=
    PathOrderReparamData.trans
      (PathOrderReparamData.trans hAssoc₁σ hAssoc₂)
      hPrefMerge
  exact hdata.cast
    (by
      rfl)
    (by
      rfl)

/--
%%handwave
name:
  Raw cut at the terminal endpoint collapses to the lower row
statement:
  At cut parameter \(1\), the raw cut path order-reparameterizes to the row
  \(F_a\).
proof:
  The vertical segment at the endpoint and the final row segment are constant
  terminal paths, so two terminal-collapse reparameterizations remove them.
-/
theorem exists_pathOrderReparamData_homotopyStripCutPathRaw_one
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b : unitInterval) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        (homotopyStripCutPathRaw F a b 1)
        (F.eval a) φ := by
  let γ := F.eval a
  rcases exists_pathOrderReparamData_trans_refl_right γ with
    ⟨φ₀, h₀⟩
  rcases exists_pathOrderReparamData_trans_right h₀ (Path.refl x) with
    ⟨φ₁, h₁⟩
  rcases exists_pathOrderReparamData_trans_refl_right γ with
    ⟨φ₂, h₂⟩
  refine ⟨φ₂ ∘ φ₁, ?_⟩
  have hraw :
      ((γ.trans (Path.refl x)).trans (Path.refl x)) =
        homotopyStripCutPathRaw F a b 1 := by
    ext u
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · by_cases hv : 2 * (u : ℝ) ≤ 1 / 2
      · have hu' : (u : ℝ) ≤ 2⁻¹ := by simpa [one_div] using hu
        have hv' : 2 * (u : ℝ) ≤ 2⁻¹ := by simpa [one_div] using hv
        simp [homotopyStripCutPathRaw, homotopyStripCutPathRawCore, γ,
          Path.subpath, Path.cast, Path.trans_apply, Set.Icc.convexComb,
          ContinuousMap.Homotopy.evalAt, Path.Homotopy.eval, hu', hv']
      · have hu' : (u : ℝ) ≤ 2⁻¹ := by simpa [one_div] using hu
        have hv' : ¬ 2 * (u : ℝ) ≤ 2⁻¹ := by simpa [one_div] using hv
        simp [homotopyStripCutPathRaw, homotopyStripCutPathRawCore, γ,
          Path.subpath, Path.cast, Path.trans_apply,
          ContinuousMap.Homotopy.evalAt, Path.Homotopy.eval, hu', hv']
    · have hu' : ¬ (u : ℝ) ≤ 2⁻¹ := by simpa [one_div] using hu
      simp [homotopyStripCutPathRaw, homotopyStripCutPathRawCore, γ,
        Path.subpath, Path.cast, Path.trans_apply, Set.Icc.convexComb,
        ContinuousMap.Homotopy.evalAt, Path.Homotopy.eval, hu']
  exact (PathOrderReparamData.trans h₁ h₂).cast hraw rfl

/--
%%handwave
name:
  Raw cut at the initial endpoint collapses to the upper row
statement:
  At cut parameter \(0\), the raw cut path order-reparameterizes to the row
  \(F_b\).
proof:
  The initial row segment and the vertical segment at the initial endpoint are
  constant initial paths, so first merge them to one constant path and then
  remove that initial constant path.
-/
theorem exists_pathOrderReparamData_homotopyStripCutPathRaw_zero
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b : unitInterval) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        (homotopyStripCutPathRaw F a b 0)
        (F.eval b) φ := by
  let γ := F.eval b
  rcases exists_pathOrderReparamData_trans_refl_right (Path.refl x₀) with
    ⟨φ₀, h₀⟩
  rcases exists_pathOrderReparamData_trans_right h₀ γ with
    ⟨φ₁, h₁⟩
  rcases exists_pathOrderReparamData_refl_trans_left γ with
    ⟨φ₂, h₂⟩
  refine ⟨φ₂ ∘ φ₁, ?_⟩
  have hraw :
      (((Path.refl x₀).trans (Path.refl x₀)).trans γ) =
        homotopyStripCutPathRaw F a b 0 := by
    ext u
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · by_cases hv : 2 * (u : ℝ) ≤ 1 / 2
      · have hu' : (u : ℝ) ≤ 2⁻¹ := by simpa [one_div] using hu
        have hv' : 2 * (u : ℝ) ≤ 2⁻¹ := by simpa [one_div] using hv
        simp [homotopyStripCutPathRaw, homotopyStripCutPathRawCore, γ,
          Path.subpath, Path.cast, Path.trans_apply, Set.Icc.convexComb,
          ContinuousMap.Homotopy.evalAt, Path.Homotopy.eval, hu', hv']
      · have hu' : (u : ℝ) ≤ 2⁻¹ := by simpa [one_div] using hu
        have hv' : ¬ 2 * (u : ℝ) ≤ 2⁻¹ := by simpa [one_div] using hv
        simp [homotopyStripCutPathRaw, homotopyStripCutPathRawCore, γ,
          Path.subpath, Path.cast, Path.trans_apply,
          ContinuousMap.Homotopy.evalAt, Path.Homotopy.eval, hu', hv']
    · have hu' : ¬ (u : ℝ) ≤ 2⁻¹ := by simpa [one_div] using hu
      simp [homotopyStripCutPathRaw, homotopyStripCutPathRawCore, γ,
        Path.subpath, Path.cast, Path.trans_apply, Set.Icc.convexComb,
        ContinuousMap.Homotopy.evalAt, Path.Homotopy.eval, hu']
  exact (PathOrderReparamData.trans h₁ h₂).cast hraw rfl

/--
%%handwave
name:
  Upper column path reparameterizes to the upper cut path
statement:
  The decomposed upper column path is an order-preserving reparameterization
  of the corresponding normalized cut path.
proof:
  Merge the two adjacent subpaths on the lower side of the strip, preserving
  the order of traversal.  Away from the endpoints this is the public cut path.
  At the two endpoints, collapse the constant initial or terminal pieces of the
  raw cut path.
-/
theorem exists_pathOrderReparamData_homotopyStripColumnTopPath_cutPath
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hr : r₀ ≤ r₁) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        (homotopyStripColumnTopPath F a b r₀ r₁)
        (homotopyStripCutPath F a b r₁) φ := by
  rcases
    exists_pathOrderReparamData_homotopyStripColumnTopPathRawCore_cutPathRawCore
      F a b r₀ r₁ hr with
    ⟨φRaw, hRawCore⟩
  have hRaw :
      PathOrderReparamData
        (homotopyStripColumnTopPath F a b r₀ r₁)
        (homotopyStripCutPathRaw F a b r₁) φRaw := by
    simpa [homotopyStripColumnTopPath, homotopyStripCutPathRaw] using
      hRawCore.castEndpoints (by simp) (by simp)
  by_cases h₁ : r₁ = 1
  · subst r₁
    rcases exists_pathOrderReparamData_homotopyStripCutPathRaw_one
        F a b with
      ⟨φEnd, hEnd⟩
    refine ⟨φEnd ∘ φRaw, ?_⟩
    simpa [homotopyStripCutPath] using
      PathOrderReparamData.trans hRaw hEnd
  · by_cases h₀ : r₁ = 0
    · subst r₁
      rcases exists_pathOrderReparamData_homotopyStripCutPathRaw_zero
          F a b with
        ⟨φEnd, hEnd⟩
      refine ⟨φEnd ∘ φRaw, ?_⟩
      simpa [homotopyStripCutPath] using
        PathOrderReparamData.trans hRaw hEnd
    · exact ⟨φRaw, by
        simpa [homotopyStripCutPath, h₁, h₀] using hRaw⟩

/--
%%handwave
name:
  Lower column path reparameterizes to the lower cut path
statement:
  The decomposed lower column path is an order-preserving reparameterization
  of the corresponding normalized cut path.
proof:
  Merge the two adjacent subpaths on the upper side of the strip after the
  common prefix, preserving the order of traversal.  If the cut is at the
  initial endpoint, collapse the constant initial pieces of the raw cut path.
-/
theorem exists_pathOrderReparamData_homotopyStripColumnBottomPath_cutPath
    {X : Type*} [TopologicalSpace X]
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hr : r₀ ≤ r₁) :
    ∃ φ : unitInterval → unitInterval,
      PathOrderReparamData
        (homotopyStripColumnBottomPath F a b r₀ r₁)
        (homotopyStripCutPath F a b r₀) φ := by
  rcases
    exists_pathOrderReparamData_homotopyStripColumnBottomPathRawCore_cutPathRawCore
      F a b r₀ r₁ hr with
    ⟨φRaw, hRawCore⟩
  have hRaw :
      PathOrderReparamData
        (homotopyStripColumnBottomPath F a b r₀ r₁)
        (homotopyStripCutPathRaw F a b r₀) φRaw := by
    simpa [homotopyStripColumnBottomPath, homotopyStripCutPathRaw] using
      hRawCore.castEndpoints (by simp) (by simp)
  by_cases h₁ : r₀ = 1
  · subst r₀
    rcases exists_pathOrderReparamData_homotopyStripCutPathRaw_one
        F a b with
      ⟨φEnd, hEnd⟩
    refine ⟨φEnd ∘ φRaw, ?_⟩
    simpa [homotopyStripCutPath] using
      PathOrderReparamData.trans hRaw hEnd
  · by_cases h₀ : r₀ = 0
    · subst r₀
      rcases exists_pathOrderReparamData_homotopyStripCutPathRaw_zero
          F a b with
        ⟨φEnd, hEnd⟩
      refine ⟨φEnd ∘ φRaw, ?_⟩
      simpa [homotopyStripCutPath] using
        PathOrderReparamData.trans hRaw hEnd
    · exact ⟨φRaw, by
        simpa [homotopyStripCutPath, h₁, h₀] using hRaw⟩

/--
%%handwave
name:
  Holomorphic local branch system
statement:
  A holomorphic local branch system consists of local holomorphic maps into a
  target surface, together with a holomorphic group action on the target that
  is allowed as the transition group between branches.
-/
structure HolomorphicLocalBranchSystem
    (G : Type w) (X : Type u) (Y : Type v) (ι : Type*)
    [Group G]
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] where
  /-- The target transformation associated to a transition element. -/
  act : G → Y → Y
  /-- Every transition transformation is holomorphic. -/
  act_holomorphic : ∀ γ : G, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (act γ)
  /-- The identity transition acts trivially. -/
  act_one : ∀ y, act 1 y = y
  /-- Transition transformations compose according to the group law. -/
  act_mul : ∀ γ δ y, act (γ * δ) y = act γ (act δ y)
  /-- The domain of a local branch. -/
  domain : ι → Set X
  /-- Branch domains are open. -/
  domain_open : ∀ i, IsOpen (domain i)
  /-- The local branch, represented as an ambient function and used only on its domain. -/
  branch : ι → X → Y
  /-- Each local branch is holomorphic on its domain. -/
  branch_holomorphicOn :
    ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (branch i) (domain i)
  /-- The local branch domains cover the source surface. -/
  covers : ∀ x : X, ∃ i, x ∈ domain i

/--
%%handwave
name:
  Rectangular subdivision subordinate to an open cover
statement:
  If a continuous map from the unit square is covered by open sets, then the
  square admits a finite monotone rectangular subdivision whose every
  rectangle maps into one member of the cover.
proof:
  Pull the open cover back to the compact unit square and use the standard
  Lebesgue-number subdivision lemma for the square.
-/
theorem exists_monotone_rectangular_subdivision_subordinate_to_open_cover
    {Z : Type*} {κ : Type*} [TopologicalSpace Z]
    (F : unitInterval × unitInterval → Z)
    (hF : Continuous F)
    (U : κ → Set Z)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i : κ, U i) :
    ∃ t : ℕ → unitInterval,
      t 0 = 0 ∧
      Monotone t ∧
      (∃ N, ∀ n ≥ N, t n = 1) ∧
      ∀ n m,
        ∃ i : κ,
          Set.Icc (t n) (t (n + 1)) ×ˢ
              Set.Icc (t m) (t (m + 1)) ⊆
            {z : unitInterval × unitInterval | F z ∈ U i} := by
  classical
  let V : κ → Set (unitInterval × unitInterval) :=
    fun i => {z : unitInterval × unitInterval | F z ∈ U i}
  have hVopen : ∀ i, IsOpen (V i) := by
    intro i
    exact (hUopen i).preimage hF
  have hVcover : Set.univ ⊆ ⋃ i : κ, V i := by
    intro z _hz
    rcases Set.mem_iUnion.mp (hUcover (Set.mem_univ (F z))) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  rcases exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (c := V) hVopen hVcover with
    ⟨t, ht0, htmono, htEventually, htRect⟩
  exact ⟨t, ht0, htmono, htEventually, htRect⟩

namespace HolomorphicLocalBranchSystem

variable {G : Type w} {X : Type u} {Y : Type v} {ι : Type*}
    [Group G]
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (S : HolomorphicLocalBranchSystem G X Y ι)

/--
%%handwave
name:
  Identity transformation acts trivially
statement:
  The identity element of the transformation group fixes every point of the
  target space.
proof:
  This is the identity law of the group action.
-/
@[simp]
theorem act_one_apply (y : Y) : S.act 1 y = y :=
  S.act_one y

/--
%%handwave
name:
  Product transformation acts by composition
statement:
  For transformations \(\gamma,\delta\) and a target point \(y\),
  \((\gamma\delta)\cdot y=\gamma\cdot(\delta\cdot y)\).
proof:
  This is the multiplication law of the group action.
-/
theorem act_mul_apply (γ δ : G) (y : Y) :
    S.act (γ * δ) y = S.act γ (S.act δ y) :=
  S.act_mul γ δ y

/--
%%handwave
name:
  An inverse transformation undoes the original transformation
statement:
  For every \(\gamma\) and \(y\),
  \(\gamma^{-1}\cdot(\gamma\cdot y)=y\).
proof:
  Combine the action law with \(\gamma^{-1}\gamma=1\).
-/
@[simp]
theorem act_inv_self (γ : G) (y : Y) :
    S.act γ⁻¹ (S.act γ y) = y := by
  rw [← S.act_mul_apply γ⁻¹ γ y, inv_mul_cancel, S.act_one_apply]

/--
%%handwave
name:
  A transformation undoes its inverse
statement:
  For every \(\gamma\) and \(y\),
  \(\gamma\cdot(\gamma^{-1}\cdot y)=y\).
proof:
  Use the action law and \(\gamma\gamma^{-1}=1\).
-/
@[simp]
theorem act_self_inv (γ : G) (y : Y) :
    S.act γ (S.act γ⁻¹ y) = y := by
  rw [← S.act_mul_apply γ γ⁻¹ y, mul_inv_cancel, S.act_one_apply]

/--
%%handwave
name:
  Every target transformation is injective
statement:
  For each group element \(\gamma\), the map \(y\mapsto\gamma\cdot y\) is
  injective.
proof:
  Apply \(\gamma^{-1}\) to an equality of transformed points.
-/
theorem act_injective (γ : G) :
    Function.Injective (S.act γ) := by
  intro y z hyz
  have h := congrArg (S.act γ⁻¹) hyz
  simpa using h

/--
%%handwave
name:
  Every target transformation is surjective
statement:
  For each group element \(\gamma\), the map \(y\mapsto\gamma\cdot y\) is
  surjective.
proof:
  A preimage of \(y\) is \(\gamma^{-1}\cdot y\).
-/
theorem act_surjective (γ : G) :
    Function.Surjective (S.act γ) := by
  intro y
  exact ⟨S.act γ⁻¹ y, S.act_self_inv γ y⟩

/--
%%handwave
name:
  Every target transformation is bijective
statement:
  The action of any group element on the target space is a bijection.
proof:
  It is both injective and surjective by the inverse-action identities.
-/
theorem act_bijective (γ : G) :
    Function.Bijective (S.act γ) :=
  ⟨S.act_injective γ, S.act_surjective γ⟩

/--
%%handwave
name:
  Local transition datum
statement:
  A local transition datum says that near a point of overlap, one local branch
  is obtained from another by a fixed holomorphic target transformation.
-/
structure LocalTransition (i j : ι) (x : X) where
  /-- The neighborhood on which the transition is valid. -/
  neighborhood : Set X
  /-- The transition neighborhood is open. -/
  neighborhood_open : IsOpen neighborhood
  /-- The overlap point belongs to the transition neighborhood. -/
  mem_neighborhood : x ∈ neighborhood
  /-- The transition neighborhood lies in the two branch domains. -/
  subset_overlap : neighborhood ⊆ S.domain i ∩ S.domain j
  /-- The transition element. -/
  transition : G
  /-- The transition relation between the two local branches. -/
  transition_eq :
    ∀ y, y ∈ neighborhood →
      S.branch j y = S.act transition (S.branch i y)

namespace LocalTransition

variable {S} {i j k : ι} {x : X}

/--
%%handwave
name:
  Identity local transition
statement:
  A branch is locally related to itself by the identity transition on its
  branch domain.
-/
def refl (i : ι) {x : X} (hx : x ∈ S.domain i) :
    S.LocalTransition i i x where
  neighborhood := S.domain i
  neighborhood_open := S.domain_open i
  mem_neighborhood := hx
  subset_overlap := by
    intro y hy
    exact ⟨hy, hy⟩
  transition := 1
  transition_eq := by
    intro y hy
    simp

/--
%%handwave
name:
  Inverse local transition
statement:
  A local transition can be reversed by inverting its transition element.
-/
def symm (T : S.LocalTransition i j x) :
    S.LocalTransition j i x where
  neighborhood := T.neighborhood
  neighborhood_open := T.neighborhood_open
  mem_neighborhood := T.mem_neighborhood
  subset_overlap := by
    intro y hy
    exact ⟨(T.subset_overlap hy).2, (T.subset_overlap hy).1⟩
  transition := T.transition⁻¹
  transition_eq := by
    intro y hy
    calc
      S.branch i y = S.act T.transition⁻¹
          (S.act T.transition (S.branch i y)) := by
        rw [S.act_inv_self]
      _ = S.act T.transition⁻¹ (S.branch j y) := by
        rw [← T.transition_eq y hy]

/--
%%handwave
name:
  Composite local transition
statement:
  Two local transitions with matching middle branch compose after shrinking to
  the intersection of their neighborhoods.
-/
def trans (T : S.LocalTransition i j x) (U : S.LocalTransition j k x) :
    S.LocalTransition i k x where
  neighborhood := T.neighborhood ∩ U.neighborhood
  neighborhood_open := T.neighborhood_open.inter U.neighborhood_open
  mem_neighborhood := ⟨T.mem_neighborhood, U.mem_neighborhood⟩
  subset_overlap := by
    intro y hy
    exact ⟨(T.subset_overlap hy.1).1, (U.subset_overlap hy.2).2⟩
  transition := U.transition * T.transition
  transition_eq := by
    intro y hy
    calc
      S.branch k y = S.act U.transition (S.branch j y) :=
        U.transition_eq y hy.2
      _ = S.act U.transition (S.act T.transition (S.branch i y)) := by
        rw [T.transition_eq y hy.1]
      _ = S.act (U.transition * T.transition) (S.branch i y) := by
        rw [S.act_mul_apply]

/-- Transport a local transition across equal branch labels and equal basepoint. -/
def congr {i j i' j' : ι} {x x' : X}
    (T : S.LocalTransition i j x)
    (hi : i = i') (hj : j = j') (hx : x = x') :
    S.LocalTransition i' j' x' := by
  subst i'
  subst j'
  subst x'
  exact T

/--
%%handwave
name:
  Transition element is unchanged under relabeling
statement:
  Transporting a local transition across equal branch labels and an equal
  basepoint leaves its group transition element unchanged.
proof:
  After substituting the equalities, the transported datum is identical to
  the original one.
-/
@[simp]
theorem congr_transition {i j i' j' : ι} {x x' : X}
    (T : S.LocalTransition i j x)
    (hi : i = i') (hj : j = j') (hx : x = x') :
    (T.congr hi hj hx).transition = T.transition := by
  subst i'
  subst j'
  subst x'
  rfl

end LocalTransition

/--
%%handwave
name:
  Local transitions
statement:
  A branch system has local transitions if every point of every branch-domain
  overlap has a transition datum.
-/
def HasLocalTransitions : Prop :=
  ∀ i j x, x ∈ S.domain i ∩ S.domain j →
    Nonempty (S.LocalTransition i j x)

/--
%%handwave
name:
  Terminal path-continuation germ
statement:
  A terminal path-continuation germ records the local branch and transition
  element obtained after continuing from a fixed initial branch along a path.
-/
structure PathContinuationGerm (x₀ : X) (i₀ : ι) {x : X}
    (p : Path x₀ x) where
  /-- The terminal local branch. -/
  branch : ι
  /-- The accumulated transition from the initial branch normalization. -/
  transition : G
  /-- A neighborhood of the endpoint on which this terminal expression is valid. -/
  neighborhood : Set X
  /-- The terminal neighborhood is open. -/
  neighborhood_open : IsOpen neighborhood
  /-- The endpoint belongs to the terminal neighborhood. -/
  mem_neighborhood : x ∈ neighborhood
  /-- The terminal neighborhood lies in the terminal branch domain. -/
  subset_domain : neighborhood ⊆ S.domain branch

namespace PathContinuationGerm

variable {S} {x₀ : X} {i₀ : ι} {x : X} {p : Path x₀ x}

/-- The local map represented by a terminal path-continuation germ. -/
def localMap (A : S.PathContinuationGerm x₀ i₀ p) : X → Y :=
  fun y ↦ S.act A.transition (S.branch A.branch y)

/--
%%handwave
name:
  Terminal path-continuation germs are holomorphic
statement:
  The local map represented by a terminal path-continuation germ is
  holomorphic on its terminal neighborhood.
proof:
  It is a holomorphic branch followed by a holomorphic transition
  transformation.
-/
theorem mdifferentiableOn (A : S.PathContinuationGerm x₀ i₀ p) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) A.localMap A.neighborhood := by
  have hbranch :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        (S.branch A.branch) A.neighborhood :=
    (S.branch_holomorphicOn A.branch).mono A.subset_domain
  have hcomp :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        ((S.act A.transition) ∘ (S.branch A.branch)) A.neighborhood :=
    (S.act_holomorphic A.transition).comp_mdifferentiableOn hbranch
  simpa [localMap, Function.comp_def] using hcomp

/--
%%handwave
name:
  Local agreement of terminal path-continuation germs
statement:
  Two terminal path-continuation germs with the same endpoint locally agree if
  their represented local maps agree on some endpoint neighborhood contained
  in both terminal neighborhoods.
-/
def LocallyAgreesWith {q : Path x₀ x}
    (A : S.PathContinuationGerm x₀ i₀ p)
    (B : S.PathContinuationGerm x₀ i₀ q) : Prop :=
  ∃ U : Set X,
    IsOpen U ∧ x ∈ U ∧ U ⊆ A.neighborhood ∩ B.neighborhood ∧
      ∀ y, y ∈ U → A.localMap y = B.localMap y

/--
%%handwave
name:
  Terminal germ agreement is reflexive
statement:
  If a terminal continuation germ \(A\) at \(x\) represents
  \(f_A:U_A\to Y\), then \(A\sim_x A\).
proof:
  Take \(U_A\) itself as the common endpoint neighborhood; both represented
  maps are \(f_A\), so their values agree identically.
-/
theorem locallyAgreesWith_refl
    (A : S.PathContinuationGerm x₀ i₀ p) :
    A.LocallyAgreesWith A := by
  exact
    ⟨A.neighborhood, A.neighborhood_open, A.mem_neighborhood,
      (by
        intro y hy
        exact ⟨hy, hy⟩),
      fun _ _ ↦ rfl⟩

/--
%%handwave
name:
  Terminal germ agreement is symmetric
statement:
  If terminal path-continuation germs \(A\) and \(B\) locally agree at their
  common endpoint, then \(B\) and \(A\) locally agree there as well.
proof:
  Use the same endpoint neighborhood, interchange the two domain conditions,
  and reverse the pointwise equality of the represented local maps.
-/
theorem locallyAgreesWith_symm {q : Path x₀ x}
    {A : S.PathContinuationGerm x₀ i₀ p}
    {B : S.PathContinuationGerm x₀ i₀ q}
    (h : A.LocallyAgreesWith B) :
    B.LocallyAgreesWith A := by
  rcases h with ⟨U, hU_open, hxU, hU_subset, hEq⟩
  exact
    ⟨U, hU_open, hxU,
      (by
        intro y hy
        exact ⟨(hU_subset hy).2, (hU_subset hy).1⟩),
      fun y hy ↦ (hEq y hy).symm⟩

/--
%%handwave
name:
  Terminal germ agreement is transitive
statement:
  For terminal continuation germs \(A,B,C\) at the same endpoint \(x\), if
  \(A\sim_x B\) and \(B\sim_x C\), then \(A\sim_x C\).
proof:
  If \(A\) and \(B\) agree on \(U\), while \(B\) and \(C\) agree on \(V\),
  use the open endpoint neighborhood \(U\cap V\) and compose the two pointwise
  equalities there.
-/
theorem locallyAgreesWith_trans {q r : Path x₀ x}
    {A : S.PathContinuationGerm x₀ i₀ p}
    {B : S.PathContinuationGerm x₀ i₀ q}
    {C : S.PathContinuationGerm x₀ i₀ r}
    (hAB : A.LocallyAgreesWith B)
    (hBC : B.LocallyAgreesWith C) :
    A.LocallyAgreesWith C := by
  rcases hAB with ⟨U, hU_open, hxU, hU_subset, hU_eq⟩
  rcases hBC with ⟨V, hV_open, hxV, hV_subset, hV_eq⟩
  refine
    ⟨U ∩ V, hU_open.inter hV_open, ⟨hxU, hxV⟩,
      ?_, ?_⟩
  · intro y hy
    exact ⟨(hU_subset hy.1).1, (hV_subset hy.2).2⟩
  · intro y hy
    exact (hU_eq y hy.1).trans (hV_eq y hy.2)

end PathContinuationGerm

/--
%%handwave
name:
  Finite path-continuation chain
statement:
  A finite path-continuation chain subdivides a path into finitely many pieces,
  chooses a local branch on each piece, and records local transition data at
  the basepoint and subdivision vertices.  The accumulated transition is
  initialized by the inverse of the basepoint handoff and then updated by the
  inverse of each handoff transition.
-/
structure PathContinuationChain (x₀ : X) (i₀ : ι) {x : X}
    (p : Path x₀ x) where
  /-- Number of path pieces. -/
  length : ℕ
  /-- Ordered subdivision parameters. -/
  parameterAt : Fin (length + 1) → unitInterval
  /-- The subdivision starts at \(0\). -/
  parameterAt_zero : parameterAt 0 = 0
  /-- The subdivision ends at \(1\). -/
  parameterAt_last : parameterAt (Fin.last length) = 1
  /-- Consecutive parameters are weakly ordered. -/
  parameterAt_mono :
    ∀ k : Fin length,
      (parameterAt k.castSucc : ℝ) ≤ (parameterAt k.succ : ℝ)
  /-- The branch used at each subdivision vertex. -/
  branchAt : Fin (length + 1) → ι
  /-- The local transition from the prescribed initial branch to the first chain branch. -/
  initialTransition : S.LocalTransition i₀ (branchAt 0) x₀
  /-- The accumulated transition at each subdivision vertex. -/
  transitionProductAt : Fin (length + 1) → G
  /-- The initial accumulated transition is supplied by the initial handoff. -/
  transitionProductAt_zero :
    transitionProductAt 0 = initialTransition.transition⁻¹
  /-- The local transition selected at each handoff. -/
  transitionAt :
    ∀ k : Fin length,
      S.LocalTransition (branchAt k.castSucc) (branchAt k.succ)
        (p (parameterAt k.succ))
  /-- The accumulated transition is updated by the local handoff. -/
  transitionProductAt_succ_eq :
    ∀ k : Fin length,
      transitionProductAt k.succ =
        transitionProductAt k.castSucc * (transitionAt k).transition⁻¹
  /-- Each sampled path point lies in its selected branch domain. -/
  sample_mem_domain :
    ∀ i,
      p (parameterAt i) ∈ S.domain (branchAt i)
  /--
  Each path piece lies in the branch domain attached to its initial vertex.
  -/
  path_segment_mem_domain :
    ∀ k : Fin length, ∀ t : unitInterval,
      (parameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (parameterAt k.succ : ℝ) →
      p t ∈ S.domain (branchAt k.castSucc)
  /-- The endpoint lies in the terminal branch domain. -/
  terminal_endpoint_mem_domain :
    x ∈ S.domain (branchAt (Fin.last length))

namespace PathContinuationChain

variable {S} {x₀ : X} {i₀ : ι} {x : X} {p : Path x₀ x}

/-- The terminal branch of a finite path-continuation chain. -/
def terminalBranch (C : S.PathContinuationChain x₀ i₀ p) : ι :=
  C.branchAt (Fin.last C.length)

/-- The terminal accumulated transition of a finite path-continuation chain. -/
def terminalTransition (C : S.PathContinuationChain x₀ i₀ p) : G :=
  C.transitionProductAt (Fin.last C.length)

/--
%%handwave
name:
  Endpoint lies in the terminal branch domain
statement:
  The endpoint of a finite path-continuation chain belongs to the domain of
  its terminal branch.
proof:
  This is the chain's endpoint-domain condition, with the terminal branch
  written as the branch at the last vertex.
-/
theorem endpoint_mem_terminalBranch
    (C : S.PathContinuationChain x₀ i₀ p) :
    x ∈ S.domain C.terminalBranch := by
  simpa [terminalBranch] using C.terminal_endpoint_mem_domain

/-- A finite path-continuation chain determines its terminal germ. -/
def toTerminalGerm
    (C : S.PathContinuationChain x₀ i₀ p) :
    S.PathContinuationGerm x₀ i₀ p where
  branch := C.terminalBranch
  transition := C.terminalTransition
  neighborhood := S.domain C.terminalBranch
  neighborhood_open := S.domain_open C.terminalBranch
  mem_neighborhood := C.endpoint_mem_terminalBranch
  subset_domain := subset_rfl

/--
%%handwave
name:
  Branch of the terminal germ of a chain
statement:
  The germ determined by a continuation chain uses the chain's terminal
  branch.
proof:
  This is the branch field in the construction of the terminal germ.
-/
@[simp]
theorem toTerminalGerm_branch
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.toTerminalGerm.branch = C.terminalBranch :=
  rfl

/--
%%handwave
name:
  Transition of the terminal germ of a chain
statement:
  The germ determined by a continuation chain uses its terminal accumulated
  transition.
proof:
  This is the transition field in the construction of the terminal germ.
-/
@[simp]
theorem toTerminalGerm_transition
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.toTerminalGerm.transition = C.terminalTransition :=
  rfl

/-- Transport a finite continuation chain across an equality of paths. -/
def castPath
    (C : S.PathContinuationChain x₀ i₀ p)
    {q : Path x₀ x} (hpq : p = q) :
    S.PathContinuationChain x₀ i₀ q := by
  subst q
  exact C

/-- Transport a finite continuation chain across an equality of initial branches. -/
def castInitialBranch
    {j₀ : ι}
    (C : S.PathContinuationChain x₀ i₀ p)
    (hij : i₀ = j₀) :
    S.PathContinuationChain x₀ j₀ p := by
  subst j₀
  exact C

/--
%%handwave
name:
  Terminal branch after identifying initial branch labels
statement:
  Transporting a continuation chain across equality of its initial branch
  label does not change its terminal branch.
proof:
  Substitute the equality of initial labels.
-/
@[simp]
theorem castInitialBranch_terminalBranch
    {j₀ : ι}
    (C : S.PathContinuationChain x₀ i₀ p)
    (hij : i₀ = j₀) :
    (C.castInitialBranch hij).terminalBranch = C.terminalBranch := by
  subst j₀
  rfl

/--
%%handwave
name:
  Terminal transition after identifying initial branch labels
statement:
  Transporting a continuation chain across equality of its initial branch
  label does not change its terminal accumulated transition.
proof:
  Substitute the equality of initial labels.
-/
@[simp]
theorem castInitialBranch_terminalTransition
    {j₀ : ι}
    (C : S.PathContinuationChain x₀ i₀ p)
    (hij : i₀ = j₀) :
    (C.castInitialBranch hij).terminalTransition = C.terminalTransition := by
  subst j₀
  rfl

/--
%%handwave
name:
  Changing an equal path representative preserves the terminal germ
statement:
  Let \(C\) be a finite continuation chain along \(p:x_0\to x\). If
  \(p=q\), regarding \(C\) as a chain along \(q\) produces a terminal germ
  locally equal to the original terminal germ at \(x\).
proof:
  After identifying \(p\) with \(q\), the two terminal germs are identical, and [every terminal continuation germ agrees with itself on its terminal neighborhood.](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationGerm.locallyAgreesWith_refl)
-/
theorem castPath_terminalGerms_agree
    (C : S.PathContinuationChain x₀ i₀ p)
    {q : Path x₀ x} (hpq : p = q) :
    C.toTerminalGerm.LocallyAgreesWith
      (C.castPath hpq).toTerminalGerm := by
  subst q
  exact
    PathContinuationGerm.locallyAgreesWith_refl C.toTerminalGerm

/--
%%handwave
name:
  Reparameterizing a continuation chain
statement:
  An order-preserving reparameterization of a path transports any finite
  continuation chain without changing its terminal branch expression.
proof:
  Push the subdivision parameters through the reparameterization and keep the
  same branch labels, local transitions, and accumulated transition products.
  The inverse parameter map sends every new subinterval back into the
  corresponding old subinterval, so the old domain-containment proofs apply.
-/
noncomputable def reparametrize
    (C : S.PathContinuationChain x₀ i₀ p)
    {q : Path x₀ x}
    (φ ψ : unitInterval → unitInterval)
    (hφ_zero : φ 0 = 0)
    (hφ_one : φ 1 = 1)
    (hφ_mono : Monotone φ)
    (hψ_interval :
      ∀ {a b t : unitInterval},
        φ a ≤ t → t ≤ φ b → a ≤ ψ t ∧ ψ t ≤ b)
    (hpath_sample : ∀ u : unitInterval, q (φ u) = p u)
    (hpath_all : ∀ t : unitInterval, q t = p (ψ t)) :
    S.PathContinuationChain x₀ i₀ q where
  length := C.length
  parameterAt := fun i => φ (C.parameterAt i)
  parameterAt_zero := by
    rw [C.parameterAt_zero, hφ_zero]
  parameterAt_last := by
    rw [C.parameterAt_last, hφ_one]
  parameterAt_mono := by
    intro k
    exact_mod_cast hφ_mono (by exact_mod_cast C.parameterAt_mono k)
  branchAt := C.branchAt
  initialTransition := C.initialTransition
  transitionProductAt := C.transitionProductAt
  transitionProductAt_zero := C.transitionProductAt_zero
  transitionAt := by
    intro k
    exact
      (C.transitionAt k).congr rfl rfl
        (hpath_sample (C.parameterAt k.succ)).symm
  transitionProductAt_succ_eq := by
    intro k
    simpa using C.transitionProductAt_succ_eq k
  sample_mem_domain := by
    intro i
    simpa [hpath_sample (C.parameterAt i)] using C.sample_mem_domain i
  path_segment_mem_domain := by
    intro k t ht_left ht_right
    let u := ψ t
    have hu :
        C.parameterAt k.castSucc ≤ u ∧ u ≤ C.parameterAt k.succ :=
      hψ_interval (a := C.parameterAt k.castSucc)
        (b := C.parameterAt k.succ) (t := t)
        (by exact_mod_cast ht_left)
        (by exact_mod_cast ht_right)
    have hmem :
        p u ∈ S.domain (C.branchAt k.castSucc) :=
      C.path_segment_mem_domain k u
        (by exact_mod_cast hu.1)
        (by exact_mod_cast hu.2)
    simpa [u, hpath_all t] using hmem
  terminal_endpoint_mem_domain := C.terminal_endpoint_mem_domain

/--
%%handwave
name:
  Terminal branch under explicit path reparameterization
statement:
  Transporting a continuation chain through an endpoint-preserving monotone
  reparameterization leaves its terminal branch unchanged.
proof:
  The construction changes only subdivision parameters and retains every
  branch label.
-/
@[simp]
theorem reparametrize_terminalBranch
    (C : S.PathContinuationChain x₀ i₀ p)
    {q : Path x₀ x}
    (φ ψ : unitInterval → unitInterval)
    (hφ_zero : φ 0 = 0)
    (hφ_one : φ 1 = 1)
    (hφ_mono : Monotone φ)
    (hψ_interval :
      ∀ {a b t : unitInterval},
        φ a ≤ t → t ≤ φ b → a ≤ ψ t ∧ ψ t ≤ b)
    (hpath_sample : ∀ u : unitInterval, q (φ u) = p u)
    (hpath_all : ∀ t : unitInterval, q t = p (ψ t)) :
    (C.reparametrize φ ψ hφ_zero hφ_one hφ_mono hψ_interval
      hpath_sample hpath_all).terminalBranch = C.terminalBranch := by
  simp [reparametrize, terminalBranch]

/--
%%handwave
name:
  Terminal transition under explicit path reparameterization
statement:
  Transporting a continuation chain through an endpoint-preserving monotone
  reparameterization leaves its terminal accumulated transition unchanged.
proof:
  The construction retains the entire sequence of accumulated transition
  products.
-/
@[simp]
theorem reparametrize_terminalTransition
    (C : S.PathContinuationChain x₀ i₀ p)
    {q : Path x₀ x}
    (φ ψ : unitInterval → unitInterval)
    (hφ_zero : φ 0 = 0)
    (hφ_one : φ 1 = 1)
    (hφ_mono : Monotone φ)
    (hψ_interval :
      ∀ {a b t : unitInterval},
        φ a ≤ t → t ≤ φ b → a ≤ ψ t ∧ ψ t ≤ b)
    (hpath_sample : ∀ u : unitInterval, q (φ u) = p u)
    (hpath_all : ∀ t : unitInterval, q t = p (ψ t)) :
    (C.reparametrize φ ψ hφ_zero hφ_one hφ_mono hψ_interval
      hpath_sample hpath_all).terminalTransition = C.terminalTransition := by
  simp [reparametrize, terminalTransition]

/--
%%handwave
name:
  Reparameterization preserves the terminal germ
statement:
  Let \(C\) be a continuation chain along \(p\), and let an order-preserving
  reparameterization identify \(p\) with a path \(q\) while respecting every
  parameter interval of \(C\). Then the terminal germs of \(C\) and of the
  transported chain along \(q\) locally agree.
proof:
  Reparameterization retains the terminal branch and accumulated transition.
  On the terminal branch domain the two terminal local maps are therefore
  identical, which supplies the required common neighborhood.
-/
theorem reparametrize_terminalGerms_agree
    (C : S.PathContinuationChain x₀ i₀ p)
    {q : Path x₀ x}
    (φ ψ : unitInterval → unitInterval)
    (hφ_zero : φ 0 = 0)
    (hφ_one : φ 1 = 1)
    (hφ_mono : Monotone φ)
    (hψ_interval :
      ∀ {a b t : unitInterval},
        φ a ≤ t → t ≤ φ b → a ≤ ψ t ∧ ψ t ≤ b)
    (hpath_sample : ∀ u : unitInterval, q (φ u) = p u)
    (hpath_all : ∀ t : unitInterval, q t = p (ψ t)) :
    C.toTerminalGerm.LocallyAgreesWith
      (C.reparametrize φ ψ hφ_zero hφ_one hφ_mono hψ_interval
        hpath_sample hpath_all).toTerminalGerm := by
  refine
    ⟨S.domain C.terminalBranch, S.domain_open C.terminalBranch,
      C.endpoint_mem_terminalBranch, ?_, ?_⟩
  · intro z hz
    constructor
    · simpa [PathContinuationChain.toTerminalGerm] using hz
    · simpa [PathContinuationChain.toTerminalGerm] using hz
  · intro z _hz
    simp [PathContinuationGerm.localMap, PathContinuationChain.toTerminalGerm]

/--
%%handwave
name:
  Reparameterizing by ordered interval images
statement:
  An order-preserving path reparameterization whose image sends each new
  parameter interval into the corresponding old path interval transports any
  finite continuation chain without changing its terminal branch expression.
proof:
  Push subdivision parameters through the forward reparameterization and keep
  all branch and transition data.  For a point in a new subinterval, the
  interval-image condition supplies an old parameter in the corresponding old
  subinterval with the same path value, so the old domain-containment proof
  applies.
-/
noncomputable def reparametrizeOrder
    (C : S.PathContinuationChain x₀ i₀ p)
    {q : Path x₀ x}
    (φ : unitInterval → unitInterval)
    (hdata : PathOrderReparamData p q φ) :
    S.PathContinuationChain x₀ i₀ q :=
  let hφ_zero : φ 0 = 0 := hdata.1
  let hφ_one : φ 1 = 1 := hdata.2.1
  let hφ_mono : Monotone φ := hdata.2.2.1
  let hsample : ∀ u : unitInterval, q (φ u) = p u := hdata.2.2.2.1
  let hinterval :
      ∀ {a b t : unitInterval},
        a ≤ b → φ a ≤ t → t ≤ φ b →
          ∃ u : unitInterval, a ≤ u ∧ u ≤ b ∧ q t = p u :=
    hdata.2.2.2.2
  {
    length := C.length
    parameterAt := fun i => φ (C.parameterAt i)
    parameterAt_zero := by
      rw [C.parameterAt_zero, hφ_zero]
    parameterAt_last := by
      rw [C.parameterAt_last, hφ_one]
    parameterAt_mono := by
      intro k
      exact_mod_cast hφ_mono (by exact_mod_cast C.parameterAt_mono k)
    branchAt := C.branchAt
    initialTransition := C.initialTransition
    transitionProductAt := C.transitionProductAt
    transitionProductAt_zero := C.transitionProductAt_zero
    transitionAt := by
      intro k
      exact
        (C.transitionAt k).congr rfl rfl
          (hsample (C.parameterAt k.succ)).symm
    transitionProductAt_succ_eq := by
      intro k
      simpa using C.transitionProductAt_succ_eq k
    sample_mem_domain := by
      intro i
      simpa [hsample (C.parameterAt i)] using C.sample_mem_domain i
    path_segment_mem_domain := by
      intro k t ht_left ht_right
      rcases
        hinterval (a := C.parameterAt k.castSucc)
          (b := C.parameterAt k.succ) (t := t)
          (by exact_mod_cast C.parameterAt_mono k)
          (by exact_mod_cast ht_left)
          (by exact_mod_cast ht_right) with
        ⟨u, hu_left, hu_right, hqt⟩
      have hmem :
          p u ∈ S.domain (C.branchAt k.castSucc) :=
        C.path_segment_mem_domain k u
          (by exact_mod_cast hu_left)
          (by exact_mod_cast hu_right)
      simpa [hqt] using hmem
    terminal_endpoint_mem_domain := C.terminal_endpoint_mem_domain
  }

/--
%%handwave
name:
  Terminal branch under ordered-image reparameterization
statement:
  Reparameterizing a continuation chain by an order-preserving path
  parameter map leaves its terminal branch unchanged.
proof:
  The ordered reparameterization transports the subdivision but reuses all
  branch labels.
-/
@[simp]
theorem reparametrizeOrder_terminalBranch
    (C : S.PathContinuationChain x₀ i₀ p)
    {q : Path x₀ x}
    (φ : unitInterval → unitInterval)
    (hdata : PathOrderReparamData p q φ) :
    (C.reparametrizeOrder φ hdata).terminalBranch = C.terminalBranch := by
  simp [reparametrizeOrder, terminalBranch]

/--
%%handwave
name:
  Terminal transition under ordered-image reparameterization
statement:
  Reparameterizing a continuation chain by an order-preserving path parameter
  map leaves its terminal accumulated transition unchanged.
proof:
  The transported chain retains every accumulated transition product.
-/
@[simp]
theorem reparametrizeOrder_terminalTransition
    (C : S.PathContinuationChain x₀ i₀ p)
    {q : Path x₀ x}
    (φ : unitInterval → unitInterval)
    (hdata : PathOrderReparamData p q φ) :
    (C.reparametrizeOrder φ hdata).terminalTransition =
      C.terminalTransition := by
  simp [reparametrizeOrder, terminalTransition]

/--
%%handwave
name:
  Ordered-image reparameterization preserves the terminal germ
statement:
  Let \(C\) be a finite continuation chain along \(p:x_0\to x\), and let
  \(\varphi:[0,1]\to[0,1]\) be an order-preserving reparameterization from
  \(p\) to \(q\) with the interval-image property. The transported chain
  along \(q\) has a terminal germ locally equal to that of \(C\) at \(x\).
proof:
  Reparameterization leaves the terminal branch \(\beta_N\) and accumulated
  transition \(g_N\) unchanged. On the common domain \(D_{\beta_N}\), both
  terminal germs therefore represent \(g_N\cdot f_{\beta_N}\).
-/
theorem reparametrizeOrder_terminalGerms_agree
    (C : S.PathContinuationChain x₀ i₀ p)
    {q : Path x₀ x}
    (φ : unitInterval → unitInterval)
    (hdata : PathOrderReparamData p q φ) :
    C.toTerminalGerm.LocallyAgreesWith
      (C.reparametrizeOrder φ hdata).toTerminalGerm := by
  refine
    ⟨S.domain C.terminalBranch, S.domain_open C.terminalBranch,
      C.endpoint_mem_terminalBranch, ?_, ?_⟩
  · intro z hz
    constructor
    · simpa [PathContinuationChain.toTerminalGerm] using hz
    · simpa [PathContinuationChain.toTerminalGerm] using hz
  · intro z _hz
    simp [PathContinuationGerm.localMap, PathContinuationChain.toTerminalGerm]

/--
%%handwave
name:
  Initial handoff preserves the local expression
statement:
  Near the basepoint, the initialized accumulated branch expression agrees
  with the prescribed initial branch.
proof:
  The accumulated transition at the first vertex is the inverse of the initial
  handoff transition, and the transition relation identifies the first branch
  with the transformed initial branch.
-/
theorem initialTransitionProduct_localMap_eq
    (C : S.PathContinuationChain x₀ i₀ p) :
    ∃ U : Set X,
      IsOpen U ∧ x₀ ∈ U ∧
        U ⊆ S.domain i₀ ∩ S.domain (C.branchAt 0) ∧
          ∀ z, z ∈ U →
            S.branch i₀ z =
              S.act (C.transitionProductAt 0) (S.branch (C.branchAt 0) z) := by
  refine
    ⟨C.initialTransition.neighborhood,
      C.initialTransition.neighborhood_open,
      C.initialTransition.mem_neighborhood,
      C.initialTransition.subset_overlap, ?_⟩
  intro z hz
  rw [C.transitionProductAt_zero]
  calc
    S.branch i₀ z =
        S.act C.initialTransition.transition⁻¹
          (S.act C.initialTransition.transition (S.branch i₀ z)) := by
      rw [S.act_inv_self]
    _ = S.act C.initialTransition.transition⁻¹
          (S.branch (C.branchAt 0) z) := by
      rw [← C.initialTransition.transition_eq z hz]

/--
%%handwave
name:
  Handoff updates preserve the local expression
statement:
  At each handoff of a finite continuation chain, the accumulated branch
  expression before the handoff locally agrees with the accumulated branch
  expression after the handoff.
proof:
  The next accumulated transition is obtained by multiplying by the inverse of
  the handoff transition.  The handoff transition relation then cancels with
  this inverse under the target action.
-/
theorem transitionProductAt_succ_localMap_eq
    (C : S.PathContinuationChain x₀ i₀ p) (k : Fin C.length) :
    ∃ U : Set X,
      IsOpen U ∧ p (C.parameterAt k.succ) ∈ U ∧
        U ⊆ S.domain (C.branchAt k.castSucc) ∩
            S.domain (C.branchAt k.succ) ∧
          ∀ z, z ∈ U →
            S.act (C.transitionProductAt k.castSucc)
                (S.branch (C.branchAt k.castSucc) z) =
              S.act (C.transitionProductAt k.succ)
                (S.branch (C.branchAt k.succ) z) := by
  let T := C.transitionAt k
  refine
    ⟨T.neighborhood, T.neighborhood_open, T.mem_neighborhood,
      T.subset_overlap, ?_⟩
  intro z hz
  have hcancel :
      S.act T.transition⁻¹ (S.branch (C.branchAt k.succ) z) =
        S.branch (C.branchAt k.castSucc) z := by
    rw [T.transition_eq z hz, S.act_inv_self]
  symm
  calc
    S.act (C.transitionProductAt k.succ)
        (S.branch (C.branchAt k.succ) z)
        = S.act (C.transitionProductAt k.castSucc * T.transition⁻¹)
            (S.branch (C.branchAt k.succ) z) := by
          rw [C.transitionProductAt_succ_eq k]
    _ = S.act (C.transitionProductAt k.castSucc)
          (S.act T.transition⁻¹ (S.branch (C.branchAt k.succ) z)) := by
          rw [S.act_mul_apply]
    _ = S.act (C.transitionProductAt k.castSucc)
          (S.branch (C.branchAt k.castSucc) z) := by
          rw [hcancel]

end PathContinuationChain

/--
%%handwave
name:
  Local agreement of transformed branch expressions
statement:
  Two transformed branch expressions agree near a point if, after shrinking to
  a neighborhood contained in the two branch domains, the two represented maps
  are equal there.
-/
def LocalExpressionAgreesAt
    (i j : ι) (γ δ : G) (x : X) : Prop :=
  ∃ U : Set X,
    IsOpen U ∧ x ∈ U ∧
      U ⊆ S.domain i ∩ S.domain j ∧
        ∀ z, z ∈ U →
          S.act γ (S.branch i z) = S.act δ (S.branch j z)

namespace LocalExpressionAgreesAt

variable {S} {i j k : ι} {γ δ ε : G} {x : X}

/--
%%handwave
name:
  Local expression agreement is symmetric
statement:
  If \(\gamma\!\cdot f_i=\delta\!\cdot f_j\) on a neighborhood of \(x\),
  then \(\delta\!\cdot f_j=\gamma\!\cdot f_i\) on a neighborhood of \(x\).
proof:
  Keep the same neighborhood, interchange its two branch-domain conditions,
  and reverse the pointwise equality.
-/
theorem symm
    (h : S.LocalExpressionAgreesAt i j γ δ x) :
    S.LocalExpressionAgreesAt j i δ γ x := by
  rcases h with ⟨U, hU_open, hxU, hU_subset, hEq⟩
  exact
    ⟨U, hU_open, hxU,
      (by
        intro z hz
        exact ⟨(hU_subset hz).2, (hU_subset hz).1⟩),
      fun z hz ↦ (hEq z hz).symm⟩

/--
%%handwave
name:
  Local expression agreement is transitive
statement:
  Let \(f_i,f_j,f_k\) be local branches and let \(\gamma,\delta,\varepsilon\)
  be transition transformations. If
  \(\gamma\cdot f_i=\delta\cdot f_j\) near \(x\) and
  \(\delta\cdot f_j=\varepsilon\cdot f_k\) near \(x\), then
  \(\gamma\cdot f_i=\varepsilon\cdot f_k\) near \(x\).
proof:
  Intersect the two open neighborhoods of \(x\). On this intersection the
  desired equality follows by transitivity through the common expression
  \(\delta\cdot f_j\).
-/
theorem trans
    (h₁ : S.LocalExpressionAgreesAt i j γ δ x)
    (h₂ : S.LocalExpressionAgreesAt j k δ ε x) :
    S.LocalExpressionAgreesAt i k γ ε x := by
  rcases h₁ with ⟨U, hU_open, hxU, hU_subset, hU_eq⟩
  rcases h₂ with ⟨V, hV_open, hxV, hV_subset, hV_eq⟩
  refine
    ⟨U ∩ V, hU_open.inter hV_open, ⟨hxU, hxV⟩,
      ?_, ?_⟩
  · intro z hz
    exact ⟨(hU_subset hz.1).1, (hV_subset hz.2).2⟩
  · intro z hz
    exact (hU_eq z hz.1).trans (hV_eq z hz.2)

/--
%%handwave
name:
  Local agreement is an open condition
statement:
  The locus where two transformed branch expressions agree locally is open.
proof:
  If the expressions agree on an open neighborhood of a point, the same open
  neighborhood witnesses local agreement at every point in it.
-/
theorem isOpen_locus
    {i j : ι} {γ δ : G} :
    IsOpen {x : X | S.LocalExpressionAgreesAt i j γ δ x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rcases hx with ⟨U, hU_open, hxU, hU_subset, hU_eq⟩
  refine ⟨U, ?_, hU_open, hxU⟩
  intro y hy
  exact ⟨U, hU_open, hy, hU_subset, hU_eq⟩

/--
%%handwave
name:
  Accumulating local agreement gives value equality
statement:
  At a point of the overlap lying in the closure of the local-agreement locus,
  the two transformed branch expressions have the same value.
proof:
  On the overlap, both transformed branch expressions are continuous.  The
  equality locus of two continuous maps into a Hausdorff space is closed.
  Since local agreement implies pointwise equality, any closure point of local
  agreement lies in the pointwise equality locus.
-/
theorem value_eq_of_mem_closure_in_overlap
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (S : HolomorphicLocalBranchSystem G X Y ι)
    {i j : ι} {γ δ : G}
    {x : (S.domain i ∩ S.domain j : Set X)}
    (hx :
      x ∈ closure
        {y : (S.domain i ∩ S.domain j : Set X) |
          S.LocalExpressionAgreesAt i j γ δ (y : X)}) :
    S.act γ (S.branch i (x : X)) =
      S.act δ (S.branch j (x : X)) := by
  let O : Set X := S.domain i ∩ S.domain j
  let F : O → Y := fun y ↦ S.act γ (S.branch i (y : X))
  let H : O → Y := fun y ↦ S.act δ (S.branch j (y : X))
  have hbranch_i :
      Continuous (fun y : O ↦ S.branch i (y : X)) := by
    have hcont :
        ContinuousOn (S.branch i) O :=
      (S.branch_holomorphicOn i).continuousOn.mono (by
        intro y hy
        exact hy.1)
    simpa [O] using hcont.restrict
  have hbranch_j :
      Continuous (fun y : O ↦ S.branch j (y : X)) := by
    have hcont :
        ContinuousOn (S.branch j) O :=
      (S.branch_holomorphicOn j).continuousOn.mono (by
        intro y hy
        exact hy.2)
    simpa [O] using hcont.restrict
  have hF : Continuous F := by
    exact (S.act_holomorphic γ).continuous.comp hbranch_i
  have hH : Continuous H := by
    exact (S.act_holomorphic δ).continuous.comp hbranch_j
  have hEqClosed : IsClosed {y : O | F y = H y} :=
    isClosed_eq hF hH
  have hsubset :
      {y : O | S.LocalExpressionAgreesAt i j γ δ (y : X)} ⊆
        {y : O | F y = H y} := by
    intro y hy
    rcases hy with ⟨U, _hU_open, hyU, _hU_subset, hEq⟩
    exact hEq (y : X) hyU
  have hxEq : x ∈ {y : O | F y = H y} :=
    hEqClosed.closure_subset (closure_mono hsubset hx)
  simpa [F, H, O] using hxEq

/--
%%handwave
name:
  Closure points are approached by agreement points
statement:
  If a point of the overlap lies in the closure of the local-agreement locus,
  then every open neighborhood of that point contains a point at which the two
  transformed branch expressions agree locally.
proof:
  View the overlap as a subspace.  The given ordinary open neighborhood pulls
  back to an open neighborhood in the overlap.  Since the point lies in the
  closure of the local-agreement locus in the overlap, this neighborhood meets
  the local-agreement locus.
-/
theorem exists_localExpressionAgreesAt_in_open_of_mem_closure_in_overlap
    (S : HolomorphicLocalBranchSystem G X Y ι)
    {i j : ι} {γ δ : G}
    {x : (S.domain i ∩ S.domain j : Set X)}
    (hx :
      x ∈ closure
        {y : (S.domain i ∩ S.domain j : Set X) |
          S.LocalExpressionAgreesAt i j γ δ (y : X)})
    {U : Set X} (hU_open : IsOpen U) (hxU : (x : X) ∈ U) :
    ∃ y : X,
      y ∈ U ∧ y ∈ S.domain i ∩ S.domain j ∧
        S.LocalExpressionAgreesAt i j γ δ y := by
  let O : Set X := S.domain i ∩ S.domain j
  let V : Set O := {y : O | (y : X) ∈ U}
  have hV_open : IsOpen V := by
    change IsOpen (((↑) : O → X) ⁻¹' U)
    exact hU_open.preimage continuous_subtype_val
  have hxV : x ∈ V := hxU
  rcases (mem_closure_iff.mp hx V hV_open hxV) with ⟨y, hyV, hyAgree⟩
  exact ⟨(y : X), hyV, y.property, hyAgree⟩

/--
%%handwave
name:
  Chartwise identity theorem for branch expressions
statement:
  Let two transformed branch expressions be defined on the overlap of two
  branch domains of Riemann surfaces.  If points of local agreement accumulate
  at a point of the overlap, then the two expressions agree locally at that
  point.
proof:
  First, [the two transformed branch expressions have the same value at the limiting point](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.LocalExpressionAgreesAt.value_eq_of_mem_closure_in_overlap).
  Choose source and target charts at this common value and shrink the source
  chart so both expressions land in the target chart.  In coordinates they
  become holomorphic functions on a preconnected plane neighborhood.  The
  accumulating points of local agreement give accumulating points of equality
  for the coordinate representatives, so [the two coordinate functions agree on that neighborhood](lean:JJMath.AnalyticContinuation.complex_identity_theorem_of_accumulation).
  Translating back through the charts gives local agreement on the surface.
-/
theorem of_mem_closure_in_overlap
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (S : HolomorphicLocalBranchSystem G X Y ι)
    {i j : ι} {γ δ : G}
    {x : (S.domain i ∩ S.domain j : Set X)}
    (hx :
      x ∈ closure
        {y : (S.domain i ∩ S.domain j : Set X) |
          S.LocalExpressionAgreesAt i j γ δ (y : X)}) :
    S.LocalExpressionAgreesAt i j γ δ (x : X) := by
  let a : X := x
  let O : Set X := S.domain i ∩ S.domain j
  let F : X → Y := fun z ↦ S.act γ (S.branch i z)
  let H : X → Y := fun z ↦ S.act δ (S.branch j z)
  let ex := extChartAt 𝓘(ℂ) a
  let y₀ : Y := F a
  let ey := extChartAt 𝓘(ℂ) y₀
  let z₀ : ℂ := ex a
  have hxO : a ∈ O := x.property
  have hO_open : IsOpen O := (S.domain_open i).inter (S.domain_open j)
  have hF_eq_H_at_a : F a = H a := by
    simpa [F, H, a, O] using
      LocalExpressionAgreesAt.value_eq_of_mem_closure_in_overlap
        S (i := i) (j := j) (γ := γ) (δ := δ) hx
  have hbranch_i_at :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (S.branch i) a :=
    (S.branch_holomorphicOn i).mdifferentiableAt
      ((S.domain_open i).mem_nhds hxO.1)
  have hbranch_j_at :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (S.branch j) a :=
    (S.branch_holomorphicOn j).mdifferentiableAt
      ((S.domain_open j).mem_nhds hxO.2)
  have hF_mdiffAt : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F a := by
    simpa [F, Function.comp_def] using
      (S.act_holomorphic γ).mdifferentiableAt.comp a hbranch_i_at
  have hH_mdiffAt : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H a := by
    simpa [H, Function.comp_def] using
      (S.act_holomorphic δ).mdifferentiableAt.comp a hbranch_j_at
  have hF_source : F a ∈ ey.source := by
    simp [ey, y₀]
  have hH_source : H a ∈ ey.source := by
    simpa [hF_eq_H_at_a] using hF_source
  have hex_target_nhds : ex.target ∈ 𝓝 z₀ := by
    simpa [ex, z₀] using extChartAt_target_mem_nhds (I := 𝓘(ℂ)) a
  have hsymm_cont : ContinuousAt ex.symm z₀ := by
    simpa [ex, z₀] using continuousAt_extChartAt_symm (I := 𝓘(ℂ)) a
  have hsymm_z₀ : ex.symm z₀ = a := by
    simp [ex, z₀, a]
  have hpreO : ex.symm ⁻¹' O ∈ 𝓝 z₀ :=
    hsymm_cont.preimage_mem_nhds
      (by simpa [hsymm_z₀] using hO_open.mem_nhds hxO)
  have hpreFsource_X : F ⁻¹' ey.source ∈ 𝓝 a :=
    hF_mdiffAt.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℂ)) y₀).mem_nhds hF_source)
  have hpreHsource_X : H ⁻¹' ey.source ∈ 𝓝 a :=
    hH_mdiffAt.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℂ)) y₀).mem_nhds hH_source)
  have hpreFsource : ex.symm ⁻¹' (F ⁻¹' ey.source) ∈ 𝓝 z₀ :=
    hsymm_cont.preimage_mem_nhds
      (by simpa [hsymm_z₀] using hpreFsource_X)
  have hpreHsource : ex.symm ⁻¹' (H ⁻¹' ey.source) ∈ 𝓝 z₀ :=
    hsymm_cont.preimage_mem_nhds
      (by simpa [hsymm_z₀] using hpreHsource_X)
  let N : Set ℂ :=
    ex.target ∩ ex.symm ⁻¹' O ∩
      ex.symm ⁻¹' (F ⁻¹' ey.source) ∩
        ex.symm ⁻¹' (H ⁻¹' ey.source)
  have hN_mem : N ∈ 𝓝 z₀ := by
    dsimp [N]
    exact
      Filter.inter_mem
        (Filter.inter_mem
          (Filter.inter_mem hex_target_nhds hpreO)
          hpreFsource)
        hpreHsource
  rcases Metric.mem_nhds_iff.mp hN_mem with ⟨r, hr_pos, hball_subset_N⟩
  let U : Set X := ex.source ∩ ex ⁻¹' Metric.ball z₀ r
  have hU_open : IsOpen U := by
    dsimp [U]
    simpa [ex] using
      isOpen_extChartAt_preimage' (I := 𝓘(ℂ)) a Metric.isOpen_ball
  have hxU : a ∈ U := by
    refine ⟨?_, ?_⟩
    · simp [ex, a]
    · simpa [z₀] using (Metric.mem_ball_self (x := z₀) hr_pos)
  rcases
    LocalExpressionAgreesAt.exists_localExpressionAgreesAt_in_open_of_mem_closure_in_overlap
      S (i := i) (j := j) (γ := γ) (δ := δ) hx hU_open hxU with
    ⟨b, hbU, _hbO, hbAgree⟩
  let z_b : ℂ := ex b
  have hb_ex_source : b ∈ ex.source := hbU.1
  have hzb_ball : z_b ∈ Metric.ball z₀ r := hbU.2
  have hzb_target : z_b ∈ ex.target := ex.map_source hb_ex_source
  rcases hbAgree with ⟨W, hW_open, hbW, _hW_subset, hW_eq⟩
  have hWcoord_nhds :
      ex.target ∩ ex.symm ⁻¹' W ∈ 𝓝 z_b := by
    have hz_mem : z_b ∈ ex.target ∩ ex.symm ⁻¹' W := by
      refine ⟨hzb_target, ?_⟩
      have hb_inv : ex.symm z_b = b := by
        simpa [z_b] using ex.left_inv hb_ex_source
      simpa [hb_inv] using hbW
    have hsymm_contOn : ContinuousOn ex.symm ex.target := by
      simpa [ex] using continuousOn_extChartAt_symm (I := 𝓘(ℂ)) a
    have hWcoord_open : IsOpen (ex.target ∩ ex.symm ⁻¹' W) :=
      hsymm_contOn.isOpen_inter_preimage
        (isOpen_extChartAt_target (I := 𝓘(ℂ)) a) hW_open
    exact hWcoord_open.mem_nhds hz_mem
  let fcoord : ℂ → ℂ := ey ∘ F ∘ ex.symm
  let hcoord : ℂ → ℂ := ey ∘ H ∘ ex.symm
  have hcoord_eventually_eq :
      fcoord =ᶠ[𝓝 z_b] hcoord := by
    filter_upwards [hWcoord_nhds] with z hz
    have hEq : F (ex.symm z) = H (ex.symm z) := by
      simpa [F, H] using hW_eq (ex.symm z) hz.2
    exact congrArg ey hEq
  have hbranch_i_O :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (S.branch i) O :=
    (S.branch_holomorphicOn i).mono (by
      intro z hz
      exact hz.1)
  have hbranch_j_O :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (S.branch j) O :=
    (S.branch_holomorphicOn j).mono (by
      intro z hz
      exact hz.2)
  have hF_mdiffOn :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F O := by
    simpa [F, Function.comp_def] using
      (S.act_holomorphic γ).comp_mdifferentiableOn hbranch_i_O
  have hH_mdiffOn :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) H O := by
    simpa [H, Function.comp_def] using
      (S.act_holomorphic δ).comp_mdifferentiableOn hbranch_j_O
  have hF_coord_diff_large :
      DifferentiableOn ℂ (ey ∘ F ∘ ex.symm)
        (ex.target ∩ ex.symm ⁻¹' (O ∩ F ⁻¹' ey.source)) := by
    simpa [ex, ey, F, O] using
      (mdifferentiableOn_iff.mp hF_mdiffOn).2 a y₀
  have hH_coord_diff_large :
      DifferentiableOn ℂ (ey ∘ H ∘ ex.symm)
        (ex.target ∩ ex.symm ⁻¹' (O ∩ H ⁻¹' ey.source)) := by
    simpa [ex, ey, H, O] using
      (mdifferentiableOn_iff.mp hH_mdiffOn).2 a y₀
  have hball_subset_F :
      Metric.ball z₀ r ⊆
        ex.target ∩ ex.symm ⁻¹' (O ∩ F ⁻¹' ey.source) := by
    intro z hz
    have hN := hball_subset_N hz
    exact ⟨hN.1.1.1, ⟨hN.1.1.2, hN.1.2⟩⟩
  have hball_subset_H :
      Metric.ball z₀ r ⊆
        ex.target ∩ ex.symm ⁻¹' (O ∩ H ⁻¹' ey.source) := by
    intro z hz
    have hN := hball_subset_N hz
    exact ⟨hN.1.1.1, ⟨hN.1.1.2, hN.2⟩⟩
  have hF_coord_diff_ball :
      DifferentiableOn ℂ fcoord (Metric.ball z₀ r) :=
    (by
      simpa [fcoord] using
        hF_coord_diff_large.mono hball_subset_F)
  have hH_coord_diff_ball :
      DifferentiableOn ℂ hcoord (Metric.ball z₀ r) :=
    (by
      simpa [hcoord] using
        hH_coord_diff_large.mono hball_subset_H)
  have hcoord_eq_on_ball :
      Set.EqOn fcoord hcoord (Metric.ball z₀ r) := by
    exact
      (hF_coord_diff_ball.analyticOnNhd Metric.isOpen_ball)
        |>.eqOn_of_preconnected_of_eventuallyEq
          (hH_coord_diff_ball.analyticOnNhd Metric.isOpen_ball)
          (Metric.isPreconnected_ball (x := z₀) (r := r))
          hzb_ball
          hcoord_eventually_eq
  refine ⟨U, hU_open, hxU, ?_, ?_⟩
  · intro z hz
    have hzN := hball_subset_N hz.2
    have hz_inv : ex.symm (ex z) = z := ex.left_inv hz.1
    have hzO : z ∈ O := by
      simpa [hz_inv] using hzN.1.1.2
    exact hzO
  · intro z hz
    have hzN := hball_subset_N hz.2
    have hz_inv : ex.symm (ex z) = z := ex.left_inv hz.1
    have hF_source_z : F z ∈ ey.source := by
      simpa [hz_inv] using hzN.1.2
    have hH_source_z : H z ∈ ey.source := by
      simpa [hz_inv] using hzN.2
    have hcoord_eq := hcoord_eq_on_ball hz.2
    have hcoord_eq' : ey (F z) = ey (H z) := by
      simpa [fcoord, hcoord, hz_inv] using hcoord_eq
    have hFH : F z = H z :=
      ey.injOn hF_source_z hH_source_z hcoord_eq'
    simpa [F, H] using hFH

/--
%%handwave
name:
  Local agreement is closed in an overlap
statement:
  Inside the overlap of two branch domains of Riemann surfaces, the locus
  where two transformed branch expressions agree locally is closed.
proof:
  A point in the closure of the local-agreement locus is a limit point of
  local agreement inside the overlap.  The chartwise identity theorem then
  gives local agreement at that point.
-/
theorem isClosed_locus_in_overlap
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (S : HolomorphicLocalBranchSystem G X Y ι)
    {i j : ι} {γ δ : G} :
    IsClosed
      {x : (S.domain i ∩ S.domain j : Set X) |
        S.LocalExpressionAgreesAt i j γ δ (x : X)} := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  exact
    LocalExpressionAgreesAt.of_mem_closure_in_overlap
      S (i := i) (j := j) (γ := γ) (δ := δ) hx

end LocalExpressionAgreesAt

namespace PathContinuationChain

variable {S} {x₀ : X} {i₀ : ι} {x : X} {p : Path x₀ x}

/--
%%handwave
name:
  Initial accumulated expressions agree
statement:
  At the initial point, the accumulated branch expressions of any two
  continuation chains with the same prescribed initial branch agree locally.
proof:
  For each chain, [the initialized accumulated branch expression agrees with the initial branch](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.initialTransitionProduct_localMap_eq).
  Intersect the two initial neighborhoods and cancel through the common
  initial branch expression.
-/
theorem initial_localExpressionAgreesAt
    (C D : S.PathContinuationChain x₀ i₀ p) :
    S.LocalExpressionAgreesAt
      (C.branchAt 0) (D.branchAt 0)
      (C.transitionProductAt 0) (D.transitionProductAt 0) x₀ := by
  rcases C.initialTransitionProduct_localMap_eq with
    ⟨U, hU_open, hxU, hU_subset, hU_eq⟩
  rcases D.initialTransitionProduct_localMap_eq with
    ⟨V, hV_open, hxV, hV_subset, hV_eq⟩
  refine
    ⟨U ∩ V, hU_open.inter hV_open, ⟨hxU, hxV⟩,
      ?_, ?_⟩
  · intro z hz
    exact ⟨(hU_subset hz.1).2, (hV_subset hz.2).2⟩
  · intro z hz
    exact (hU_eq z hz.1).symm.trans (hV_eq z hz.2)

/--
%%handwave
name:
  Handoff accumulated expressions agree
statement:
  At each handoff, the accumulated branch expression before the handoff and
  the accumulated branch expression after the handoff agree locally.
proof:
  This is just [the handoff update identity for accumulated branch expressions](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.transitionProductAt_succ_localMap_eq)
  repackaged as local agreement.
-/
theorem transitionProductAt_succ_localExpressionAgreesAt
    (C : S.PathContinuationChain x₀ i₀ p) (k : Fin C.length) :
    S.LocalExpressionAgreesAt
      (C.branchAt k.castSucc) (C.branchAt k.succ)
      (C.transitionProductAt k.castSucc)
      (C.transitionProductAt k.succ)
      (p (C.parameterAt k.succ)) := by
  exact C.transitionProductAt_succ_localMap_eq k

/--
%%handwave
name:
  Local agreement is closed along a path segment
statement:
  On a path segment lying in the overlap of two branch domains, the set of
  parameters at which two transformed branch expressions agree locally is
  closed.
proof:
  Let a parameter be a limit point of local agreement.  In a source coordinate
  at the limiting point and a target coordinate at the common value, the two
  transformed branches become holomorphic maps between open subsets of the
  plane.  Local agreement at nearby parameters gives equality on open sets
  accumulating at the limit.  The identity theorem for holomorphic functions
  therefore gives equality in a neighborhood of the limit point.
-/
theorem localExpressionAgreesAt_locus_isClosedOn_path_segment
    [ComplexOneManifold X] [ComplexOneManifold Y]
    {x₀ x : X} (p : Path x₀ x)
    {a b : unitInterval} {i j : ι} {γ δ : G}
    (_hab : (a : ℝ) ≤ (b : ℝ))
    (hi :
      ∀ t : unitInterval,
        (a : ℝ) ≤ (t : ℝ) →
        (t : ℝ) ≤ (b : ℝ) →
          p t ∈ S.domain i)
    (hj :
      ∀ t : unitInterval,
        (a : ℝ) ≤ (t : ℝ) →
        (t : ℝ) ≤ (b : ℝ) →
          p t ∈ S.domain j) :
    IsClosed
      {t : Set.Icc a b |
        S.LocalExpressionAgreesAt i j γ δ (p (t : unitInterval))} := by
  let W : Set unitInterval := Set.Icc a b
  let q : W → (S.domain i ∩ S.domain j : Set X) :=
    fun t =>
      ⟨p (t : unitInterval),
        (by
          constructor
          · exact hi (t : unitInterval)
              (by exact_mod_cast t.property.1)
              (by exact_mod_cast t.property.2)
          · exact hj (t : unitInterval)
              (by exact_mod_cast t.property.1)
              (by exact_mod_cast t.property.2))⟩
  have hq : Continuous q := by
    exact Continuous.subtype_mk
      (p.continuous.comp continuous_subtype_val)
      (fun t =>
        (by
          constructor
          · exact hi (t : unitInterval)
              (by exact_mod_cast t.property.1)
              (by exact_mod_cast t.property.2)
          · exact hj (t : unitInterval)
              (by exact_mod_cast t.property.1)
              (by exact_mod_cast t.property.2)))
  have hclosed :=
    (LocalExpressionAgreesAt.isClosed_locus_in_overlap
      S (i := i) (j := j) (γ := γ) (δ := δ)).preimage hq
  simpa [q, W] using hclosed

/--
%%handwave
name:
  Local equality propagates along a path segment
statement:
  Let two transformed branch expressions be holomorphic on branch domains that
  contain a path segment.  If the two expressions agree near the left endpoint
  of the segment, then they agree near the right endpoint.
proof:
  The path image of the interval is preconnected.  On a preconnected
  neighborhood of this image inside the overlap of the two branch domains, the
  two transformed branch expressions are holomorphic.  The identity theorem
  for holomorphic maps extends equality from the initial neighborhood to the
  whole overlap component, hence to a neighborhood of the right endpoint.
-/
theorem localExpressionAgreesAt_propagates_along_path_segment
    [ComplexOneManifold X] [ComplexOneManifold Y]
    {x₀ x : X} (p : Path x₀ x)
    {a b : unitInterval} {i j : ι} {γ δ : G}
    (hab : (a : ℝ) ≤ (b : ℝ))
    (hi :
      ∀ t : unitInterval,
        (a : ℝ) ≤ (t : ℝ) →
        (t : ℝ) ≤ (b : ℝ) →
          p t ∈ S.domain i)
    (hj :
      ∀ t : unitInterval,
        (a : ℝ) ≤ (t : ℝ) →
        (t : ℝ) ≤ (b : ℝ) →
          p t ∈ S.domain j)
    (hstart : S.LocalExpressionAgreesAt i j γ δ (p a)) :
    S.LocalExpressionAgreesAt i j γ δ (p b) := by
  have habI : a ≤ b := by
    exact_mod_cast hab
  let W : Set unitInterval := Set.Icc a b
  let E : Set W :=
    {t : W | S.LocalExpressionAgreesAt i j γ δ (p (t : unitInterval))}
  have hE_open : IsOpen E := by
    have hOpenUnit :
        IsOpen
          {t : unitInterval |
            S.LocalExpressionAgreesAt i j γ δ (p t)} :=
      (LocalExpressionAgreesAt.isOpen_locus (S := S)
        (i := i) (j := j) (γ := γ) (δ := δ)).preimage p.continuous
    change IsOpen (((↑) : W → unitInterval) ⁻¹'
      {t : unitInterval | S.LocalExpressionAgreesAt i j γ δ (p t)})
    exact hOpenUnit.preimage continuous_subtype_val
  have hE_closed : IsClosed E := by
    simpa [E, W] using
      localExpressionAgreesAt_locus_isClosedOn_path_segment
        (S := S) p (a := a) (b := b) (i := i) (j := j)
        (γ := γ) (δ := δ) hab hi hj
  haveI : PreconnectedSpace W :=
    Subtype.preconnectedSpace (s := W) (by
      simpa [W] using (isPreconnected_Icc : IsPreconnected (Set.Icc a b)))
  have haW : a ∈ W := by
    exact ⟨le_rfl, habI⟩
  have hE_nonempty : E.Nonempty :=
    ⟨⟨a, haW⟩, hstart⟩
  have hE_univ : E = Set.univ :=
    IsClopen.eq_univ ⟨hE_closed, hE_open⟩ hE_nonempty
  have hbW : b ∈ W := by
    exact ⟨habI, le_rfl⟩
  have hbE : (⟨b, hbW⟩ : W) ∈ E := by
    rw [hE_univ]
    exact Set.mem_univ _
  exact hbE

/--
%%handwave
name:
  Handoff update of local expression agreement
statement:
  Suppose \(\gamma\!\cdot f_i=\delta\!\cdot f_j\) near \(x\), while the
  handoffs satisfy \(\gamma\!\cdot f_i=\gamma'\!\cdot f_{i'}\) and
  \(\delta\!\cdot f_j=\delta'\!\cdot f_{j'}\) near \(x\). Then
  \(\gamma'\!\cdot f_{i'}=\delta'\!\cdot f_{j'}\) near \(x\).
proof:
  Reverse the first handoff equality and compose it transitively with the
  original agreement and the second handoff equality.
-/
theorem localExpressionAgreesAt_update_of_handoffs
    {i i' j j' : ι} {γ γ' δ δ' : G} {x : X}
    (h : S.LocalExpressionAgreesAt i j γ δ x)
    (hi : S.LocalExpressionAgreesAt i i' γ γ' x)
    (hj : S.LocalExpressionAgreesAt j j' δ δ' x) :
    S.LocalExpressionAgreesAt i' j' γ' δ' x :=
  (LocalExpressionAgreesAt.symm hi).trans (h.trans hj)

/--
%%handwave
name:
  Aligned chains have equal accumulated expressions at vertices
statement:
  If two continuation chains along the same path have the same subdivision
  parameters, then their accumulated branch expressions agree locally at every
  aligned vertex.
proof:
  Start from the common initial branch, using [the initial accumulated expressions agree](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.initial_localExpressionAgreesAt).
  For the induction step, [local equality propagates along the common path segment](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.localExpressionAgreesAt_propagates_along_path_segment),
  and the handoff identities update the two accumulated expressions.
-/
theorem localExpressionAgreesAt_aligned_vertex
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (C D : S.PathContinuationChain x₀ i₀ p)
    (_hLength : C.length = D.length)
    (hParam :
      ∀ n (hnC : n ≤ C.length) (hnD : n ≤ D.length),
        C.parameterAt ⟨n, Nat.lt_succ_of_le hnC⟩ =
          D.parameterAt ⟨n, Nat.lt_succ_of_le hnD⟩) :
    ∀ n (hnC : n ≤ C.length) (hnD : n ≤ D.length),
      S.LocalExpressionAgreesAt
        (C.branchAt ⟨n, Nat.lt_succ_of_le hnC⟩)
        (D.branchAt ⟨n, Nat.lt_succ_of_le hnD⟩)
        (C.transitionProductAt ⟨n, Nat.lt_succ_of_le hnC⟩)
        (D.transitionProductAt ⟨n, Nat.lt_succ_of_le hnD⟩)
        (p (C.parameterAt ⟨n, Nat.lt_succ_of_le hnC⟩)) := by
  intro n
  induction n with
  | zero =>
      intro hnC hnD
      have hinit := C.initial_localExpressionAgreesAt D
      simpa [C.parameterAt_zero, p.source] using hinit
  | succ n ih =>
      intro hnC hnD
      have hnC_lt : n < C.length := Nat.succ_le_iff.mp hnC
      have hnD_lt : n < D.length := Nat.succ_le_iff.mp hnD
      let kC : Fin C.length := ⟨n, hnC_lt⟩
      let kD : Fin D.length := ⟨n, hnD_lt⟩
      have hnC_prev : n ≤ C.length := Nat.le_of_lt hnC_lt
      have hnD_prev : n ≤ D.length := Nat.le_of_lt hnD_lt
      have hprev :
          S.LocalExpressionAgreesAt
            (C.branchAt kC.castSucc)
            (D.branchAt kD.castSucc)
            (C.transitionProductAt kC.castSucc)
            (D.transitionProductAt kD.castSucc)
            (p (C.parameterAt kC.castSucc)) := by
        simpa [kC, kD] using ih hnC_prev hnD_prev
      have hleftParam :
          C.parameterAt kC.castSucc = D.parameterAt kD.castSucc := by
        simpa [kC, kD] using hParam n hnC_prev hnD_prev
      have hrightParam :
          C.parameterAt kC.succ = D.parameterAt kD.succ := by
        simpa [kC, kD] using hParam (n + 1) hnC hnD
      have hprop :
          S.LocalExpressionAgreesAt
            (C.branchAt kC.castSucc)
            (D.branchAt kD.castSucc)
            (C.transitionProductAt kC.castSucc)
            (D.transitionProductAt kD.castSucc)
            (p (C.parameterAt kC.succ)) := by
        exact
          localExpressionAgreesAt_propagates_along_path_segment (S := S) p
            (a := C.parameterAt kC.castSucc)
            (b := C.parameterAt kC.succ)
            (i := C.branchAt kC.castSucc)
            (j := D.branchAt kD.castSucc)
            (γ := C.transitionProductAt kC.castSucc)
            (δ := D.transitionProductAt kD.castSucc)
            (C.parameterAt_mono kC)
            (fun t ht_left ht_right =>
              C.path_segment_mem_domain kC t ht_left ht_right)
            (fun t ht_left ht_right =>
              D.path_segment_mem_domain kD t
                (by simpa [hleftParam] using ht_left)
                (by simpa [hrightParam] using ht_right))
            hprev
      have hC :
          S.LocalExpressionAgreesAt
            (C.branchAt kC.castSucc) (C.branchAt kC.succ)
            (C.transitionProductAt kC.castSucc)
            (C.transitionProductAt kC.succ)
            (p (C.parameterAt kC.succ)) :=
        C.transitionProductAt_succ_localExpressionAgreesAt kC
      have hD :
          S.LocalExpressionAgreesAt
            (D.branchAt kD.castSucc) (D.branchAt kD.succ)
            (D.transitionProductAt kD.castSucc)
            (D.transitionProductAt kD.succ)
            (p (C.parameterAt kC.succ)) := by
        simpa [hrightParam] using
          (D.transitionProductAt_succ_localExpressionAgreesAt kD)
      have hnext :
          S.LocalExpressionAgreesAt
            (C.branchAt kC.succ) (D.branchAt kD.succ)
            (C.transitionProductAt kC.succ)
            (D.transitionProductAt kD.succ)
            (p (C.parameterAt kC.succ)) :=
        localExpressionAgreesAt_update_of_handoffs (S := S) hprop hC hD
      simpa [kC, kD] using hnext

/--
%%handwave
name:
  Aligned chains have the same terminal germ
statement:
  If two continuation chains along the same path have the same subdivision
  parameters, then their terminal germs locally agree.
proof:
  Apply [local agreement of accumulated expressions at aligned vertices](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.localExpressionAgreesAt_aligned_vertex)
  to the final vertex, where the path value is the endpoint.
-/
theorem terminalGerms_agree_of_alignedSubdivision
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (C D : S.PathContinuationChain x₀ i₀ p)
    (hLength : C.length = D.length)
    (hParam :
      ∀ n (hnC : n ≤ C.length) (hnD : n ≤ D.length),
        C.parameterAt ⟨n, Nat.lt_succ_of_le hnC⟩ =
          D.parameterAt ⟨n, Nat.lt_succ_of_le hnD⟩) :
    C.toTerminalGerm.LocallyAgreesWith D.toTerminalGerm := by
  have hlastD : C.length ≤ D.length := by
    omega
  let iC : Fin (C.length + 1) :=
    ⟨C.length, Nat.lt_succ_of_le le_rfl⟩
  let iD : Fin (D.length + 1) := ⟨C.length, Nat.lt_succ_of_le hlastD⟩
  have hiC : iC = Fin.last C.length := by
    ext
    rfl
  have hiD : iD = Fin.last D.length := by
    ext
    exact hLength
  have hlocal :
      S.LocalExpressionAgreesAt
        (C.branchAt iC) (D.branchAt iD)
        (C.transitionProductAt iC) (D.transitionProductAt iD)
        (p (C.parameterAt iC)) := by
    simpa [iC, iD] using
      C.localExpressionAgreesAt_aligned_vertex D hLength hParam
        C.length le_rfl hlastD
  rcases hlocal with ⟨U, hU_open, hxU, hU_subset, hU_eq⟩
  refine ⟨U, hU_open, ?_, ?_, ?_⟩
  · simpa [iC, hiC, C.parameterAt_last, p.target] using hxU
  · intro z hz
    simpa [PathContinuationGerm.localMap, toTerminalGerm, terminalBranch,
      terminalTransition, iC, hiC, iD, hiD] using hU_subset hz
  · intro z hz
    simpa [PathContinuationGerm.localMap, toTerminalGerm, terminalBranch,
      terminalTransition, iC, hiC, iD, hiD] using hU_eq z hz

/--
Subdivision parameters for appending a path in the terminal branch: the old
subdivision is compressed into the first half and one final endpoint is added
at \(1\).
-/
noncomputable def terminalExtensionParameterAt
    (C : S.PathContinuationChain x₀ i₀ p) :
    Fin (C.length + 2) → unitInterval :=
  fun i =>
    if hi : (i : ℕ) < C.length + 1 then
      unitInterval.firstHalf (C.parameterAt ⟨i, hi⟩)
    else
      1

/--
Branches for appending a path in the terminal branch: the old branch choices
are reused on the compressed part and the added endpoint uses the old terminal
branch.
-/
noncomputable def terminalExtensionBranchAt
    (C : S.PathContinuationChain x₀ i₀ p) :
    Fin (C.length + 2) → ι :=
  fun i =>
    if hi : (i : ℕ) < C.length + 1 then
      C.branchAt ⟨i, hi⟩
    else
      C.terminalBranch

/--
Accumulated transitions for appending a path in the terminal branch: the old
accumulated products are reused and the added final product is unchanged.
-/
noncomputable def terminalExtensionTransitionProductAt
    (C : S.PathContinuationChain x₀ i₀ p) :
    Fin (C.length + 2) → G :=
  fun i =>
    if hi : (i : ℕ) < C.length + 1 then
      C.transitionProductAt ⟨i, hi⟩
    else
      C.terminalTransition

/--
%%handwave
name:
  Old parameters in a terminal path extension
statement:
  At an old subdivision vertex, appending a path in the terminal branch uses
  the original parameter compressed into the first half of the interval.
proof:
  The old vertex satisfies the first clause of the parameter assignment.
-/
@[simp]
theorem terminalExtensionParameterAt_castSucc
    (C : S.PathContinuationChain x₀ i₀ p)
    (i : Fin (C.length + 1)) :
    C.terminalExtensionParameterAt i.castSucc =
      unitInterval.firstHalf (C.parameterAt i) := by
  change
    (if hi : (i : ℕ) < C.length + 1 then
      unitInterval.firstHalf (C.parameterAt ⟨i, hi⟩)
    else 1) = unitInterval.firstHalf (C.parameterAt i)
  rw [dif_pos i.isLt]

/--
%%handwave
name:
  Old branches in a terminal path extension
statement:
  At every old subdivision vertex, a terminal path extension retains the
  original branch choice.
proof:
  Evaluate the old-index clause of the branch assignment.
-/
@[simp]
theorem terminalExtensionBranchAt_castSucc
    (C : S.PathContinuationChain x₀ i₀ p)
    (i : Fin (C.length + 1)) :
    C.terminalExtensionBranchAt i.castSucc = C.branchAt i := by
  change
    (if hi : (i : ℕ) < C.length + 1 then
      C.branchAt ⟨i, hi⟩
    else C.terminalBranch) = C.branchAt i
  rw [dif_pos i.isLt]

/--
%%handwave
name:
  Old transition products in a terminal path extension
statement:
  At every old vertex, a terminal path extension retains the original
  accumulated transition product.
proof:
  This is the old-index clause of the product assignment.
-/
@[simp]
theorem terminalExtensionTransitionProductAt_castSucc
    (C : S.PathContinuationChain x₀ i₀ p)
    (i : Fin (C.length + 1)) :
    C.terminalExtensionTransitionProductAt i.castSucc =
      C.transitionProductAt i := by
  change
    (if hi : (i : ℕ) < C.length + 1 then
      C.transitionProductAt ⟨i, hi⟩
    else C.terminalTransition) = C.transitionProductAt i
  rw [dif_pos i.isLt]

/--
%%handwave
name:
  Final parameter of a terminal path extension
statement:
  The added terminal vertex of the extended subdivision has parameter \(1\).
proof:
  The last index falls in the added-endpoint clause.
-/
@[simp]
theorem terminalExtensionParameterAt_last
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionParameterAt (Fin.last (C.length + 1)) = 1 := by
  simp [terminalExtensionParameterAt]

/--
%%handwave
name:
  Final branch of a terminal path extension
statement:
  The added endpoint of a path appended inside the terminal branch carries
  the original terminal branch.
proof:
  This is how the added endpoint branch is assigned.
-/
@[simp]
theorem terminalExtensionBranchAt_last
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionBranchAt (Fin.last (C.length + 1)) =
      C.terminalBranch := by
  simp [terminalExtensionBranchAt]

/--
%%handwave
name:
  Final transition product of a terminal path extension
statement:
  Appending a path within the terminal branch leaves the terminal accumulated
  transition unchanged.
proof:
  The added endpoint is assigned the old terminal product.
-/
@[simp]
theorem terminalExtensionTransitionProductAt_last
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionTransitionProductAt (Fin.last (C.length + 1)) =
      C.terminalTransition := by
  simp [terminalExtensionTransitionProductAt]

/--
%%handwave
name:
  Initial parameter of a terminal path extension
statement:
  The extended subdivision begins at parameter \(0\).
proof:
  The old initial value is zero and first-half compression fixes zero.
-/
@[simp]
theorem terminalExtensionParameterAt_zero
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionParameterAt 0 = 0 := by
  simp [terminalExtensionParameterAt, C.parameterAt_zero]

/--
%%handwave
name:
  Initial branch of a terminal path extension
statement:
  The extended chain begins with the original initial branch.
proof:
  The zero vertex is retained from the old subdivision.
-/
@[simp]
theorem terminalExtensionBranchAt_zero
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionBranchAt 0 = C.branchAt 0 := by
  simp [terminalExtensionBranchAt]

/--
%%handwave
name:
  Initial transition product of a terminal path extension
statement:
  The extended chain begins with the original initial accumulated transition.
proof:
  The zero vertex lies in the retained old part.
-/
@[simp]
theorem terminalExtensionTransitionProductAt_zero
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionTransitionProductAt 0 = C.transitionProductAt 0 := by
  simp [terminalExtensionTransitionProductAt]

/--
%%handwave
name:
  Successor commutes with finite-index inclusion
statement:
  Including an index in the next finite range and then taking its successor
  gives the same index as taking the successor first and then including it.
proof:
  Both finite indices have the same underlying natural number.
-/
theorem fin_castSucc_succ_eq_succ_castSucc {n : ℕ} (k : Fin n) :
    (k.castSucc : Fin (n + 1)).succ = (k.succ).castSucc := by
  ext
  rfl

/--
%%handwave
name:
  Successor of the last finite index
statement:
  The successor of the last index in a finite range is the last index in the
  next larger range.
proof:
  Both indices have underlying natural number \(n\).
-/
theorem fin_last_succ_eq_last {n : ℕ} :
    (Fin.last n : Fin (n + 1)).succ = Fin.last (n + 1) := by
  ext
  rfl

/--
%%handwave
name:
  List of a finite tuple after inserting one entry
statement:
  If an element \(x\) is inserted at any position in a finite tuple \(f\),
  the list of entries of the resulting tuple is a permutation of
  \(x\) followed by the list of entries of \(f\).
proof:
  Induct on the tuple length and split the insertion position between the
  head and a successor.  In the successor case, use the induction hypothesis
  on the tail and swap \(x\) past the old head.
-/
theorem ofFn_fin_insertNth_perm {α : Type*} :
    ∀ {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α),
      List.Perm (List.ofFn (Fin.insertNth i x f)) (x :: List.ofFn f)
  | 0, ⟨0, _⟩, x, f => by
      simp
  | n + 1, i, x, f => by
      cases i using Fin.cases with
      | zero =>
          simp
      | succ i =>
          rw [← Fin.cons_self_tail f]
          rw [Fin.insertNth_succ_cons, List.ofFn_cons, List.ofFn_cons]
          exact
            (List.Perm.cons (f 0)
              (ofFn_fin_insertNth_perm i x (Fin.tail f))).trans
              (List.Perm.swap (f 0) x (List.ofFn (Fin.tail f))).symm

/--
%%handwave
name:
  A continuation chain has positive length
statement:
  Every finite path-continuation chain contains at least one segment.
proof:
  If its length were zero, the initial and terminal vertex indices would
  coincide, forcing their parameters \(0\) and \(1\) to be equal.
-/
theorem length_pos (C : S.PathContinuationChain x₀ i₀ p) :
    0 < C.length := by
  by_contra hpos
  have hlen : C.length = 0 := Nat.eq_zero_of_not_pos hpos
  have hidx : (0 : Fin (C.length + 1)) = Fin.last C.length := by
    ext
    simp [hlen]
  have h01 : (0 : unitInterval) = 1 := by
    rw [← C.parameterAt_zero, hidx, C.parameterAt_last]
  exact zero_ne_one h01

/--
%%handwave
name:
  Every parameter lies in a subdivision segment
statement:
  For every \(\tau\in[0,1]\) and every finite nondecreasing subdivision
  \(0=t_0\le\cdots\le t_n=1\), there is \(k<n\) such that
  \(t_k\le\tau\le t_{k+1}\).
proof:
  Choose the least vertex index whose parameter is at least \(\tau\).  If it
  is zero, use \(0\le\tau\); otherwise minimality makes the preceding
  parameter at most \(\tau\).
-/
theorem exists_segment_contains_parameter
    (C : S.PathContinuationChain x₀ i₀ p)
    (τ : unitInterval) :
    ∃ k : Fin C.length,
      (C.parameterAt k.castSucc : ℝ) ≤ (τ : ℝ) ∧
        (τ : ℝ) ≤ (C.parameterAt k.succ : ℝ) := by
  classical
  let Q : ℕ → Prop := fun n =>
    ∃ hn : n ≤ C.length,
      (τ : ℝ) ≤
        (C.parameterAt ⟨n, Nat.lt_succ_of_le hn⟩ : ℝ)
  have hQexists : ∃ n, Q n := by
    refine ⟨C.length, le_rfl, ?_⟩
    have hlast :
        (⟨C.length, Nat.lt_succ_of_le le_rfl⟩ : Fin (C.length + 1)) =
          Fin.last C.length := by
      ext
      simp
    simpa [Q, hlast, C.parameterAt_last] using unitInterval.le_one τ
  let n := Nat.find hQexists
  have hnQ : Q n := Nat.find_spec hQexists
  rcases hnQ with ⟨hnle, hnτ⟩
  by_cases hn0 : n = 0
  · let k : Fin C.length := ⟨0, C.length_pos⟩
    refine ⟨k, ?_, ?_⟩
    · simpa [k, hn0, C.parameterAt_zero] using unitInterval.nonneg τ
    · have hmono :
          (C.parameterAt k.castSucc : ℝ) ≤
            (C.parameterAt k.succ : ℝ) :=
        C.parameterAt_mono k
      have hτ0 : (τ : ℝ) ≤ (C.parameterAt k.castSucc : ℝ) := by
        simpa [k, hn0] using hnτ
      exact le_trans hτ0 hmono
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    let k : Fin C.length := ⟨n - 1, by omega⟩
    let iPrev : Fin (C.length + 1) :=
      ⟨n - 1, Nat.lt_succ_of_le (by omega : n - 1 ≤ C.length)⟩
    let iCur : Fin (C.length + 1) :=
      ⟨n, Nat.lt_succ_of_le hnle⟩
    have hprev_lt : n - 1 < n := by omega
    have hnotQprev : ¬ Q (n - 1) :=
      Nat.find_min hQexists hprev_lt
    have hnot_le :
        ¬ (τ : ℝ) ≤ (C.parameterAt iPrev : ℝ) := by
      intro hle
      exact hnotQprev ⟨by omega, by simpa [iPrev] using hle⟩
    have hleft :
        (C.parameterAt iPrev : ℝ) ≤ (τ : ℝ) :=
      le_of_lt (lt_of_not_ge hnot_le)
    have hcast : k.castSucc = iPrev := by
      ext
      simp [k, iPrev]
    have hsucc : k.succ = iCur := by
      ext
      simp [k, iCur]
      omega
    refine ⟨k, ?_, ?_⟩
    · simpa [hcast] using hleft
    · simpa [hsucc, iCur] using hnτ

/-- The vertex at which an interior segment split is inserted. -/
def segmentSplitInsertVertex
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) : Fin (C.length + 2) :=
  (k.succ : Fin (C.length + 1)).castSucc

/--
Subdivision parameters after inserting a point `τ` into segment `k`.

The old vertices are embedded by `succAbove`, while the inserted vertex is
assigned parameter `τ`.
-/
noncomputable def segmentSplitParameterAt
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval) :
    Fin (C.length + 2) → unitInterval :=
  fun i =>
    if i = C.segmentSplitInsertVertex k then
      τ
    else
      C.parameterAt ((k.succ : Fin (C.length + 1)).predAbove i)

/--
Branches after inserting a point `τ` into segment `k`.  The inserted vertex
uses the same branch as the left half of the split segment.
-/
noncomputable def segmentSplitBranchAt
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    Fin (C.length + 2) → ι :=
  fun i =>
    if i = C.segmentSplitInsertVertex k then
      C.branchAt k.castSucc
    else
      C.branchAt ((k.succ : Fin (C.length + 1)).predAbove i)

/--
Accumulated transitions after a segment split.  The inserted vertex has the
same accumulated transition as the old left endpoint.
-/
noncomputable def segmentSplitTransitionProductAt
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    Fin (C.length + 2) → G :=
  fun i =>
    if i = C.segmentSplitInsertVertex k then
      C.transitionProductAt k.castSucc
    else
      C.transitionProductAt ((k.succ : Fin (C.length + 1)).predAbove i)

/--
%%handwave
name:
  Parameter at an inserted subdivision vertex
statement:
  After splitting a segment at \(\tau\), the newly inserted vertex has
  parameter \(\tau\).
proof:
  This is the inserted-vertex clause of the parameter assignment.
-/
@[simp]
theorem segmentSplitParameterAt_insert
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval) :
    C.segmentSplitParameterAt k τ (C.segmentSplitInsertVertex k) = τ := by
  simp [segmentSplitParameterAt]

/--
%%handwave
name:
  Branch at an inserted subdivision vertex
statement:
  The new vertex inserted into segment \(k\) is assigned the branch used at
  the old left endpoint of that segment.
proof:
  This is the inserted-vertex clause of the branch assignment.
-/
@[simp]
theorem segmentSplitBranchAt_insert
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    C.segmentSplitBranchAt k (C.segmentSplitInsertVertex k) =
      C.branchAt k.castSucc := by
  simp [segmentSplitBranchAt]

/--
%%handwave
name:
  Transition product at an inserted subdivision vertex
statement:
  The accumulated transition at a vertex inserted into segment \(k\) equals
  the accumulated transition at the old left endpoint.
proof:
  This is the inserted-vertex clause of the product assignment.
-/
@[simp]
theorem segmentSplitTransitionProductAt_insert
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    C.segmentSplitTransitionProductAt k (C.segmentSplitInsertVertex k) =
      C.transitionProductAt k.castSucc := by
  simp [segmentSplitTransitionProductAt]

/--
%%handwave
name:
  Old parameters after splitting a segment
statement:
  Every old subdivision vertex, embedded around the inserted vertex, retains
  its original parameter.
proof:
  The embedded index is not the insertion index, and deleting the insertion
  recovers the original index.
-/
@[simp]
theorem segmentSplitParameterAt_old
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (i : Fin (C.length + 1)) :
    C.segmentSplitParameterAt k τ
        ((C.segmentSplitInsertVertex k).succAbove i) =
      C.parameterAt i := by
  unfold segmentSplitParameterAt segmentSplitInsertVertex
  rw [if_neg]
  · rw [Fin.predAbove_succAbove]
  · exact Fin.succAbove_ne _ _

/--
%%handwave
name:
  Parameter tuple after splitting a segment
statement:
  The parameter tuple of a segment split is exactly the old tuple with
  \(\tau\) inserted immediately after the left endpoint of the split segment.
proof:
  At the insertion index both tuples equal \(\tau\); at every other index,
  deleting the inserted position recovers the same old parameter.
-/
theorem segmentSplitParameterAt_eq_insertNth
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval) :
    C.segmentSplitParameterAt k τ =
      Fin.insertNth (C.segmentSplitInsertVertex k) τ C.parameterAt := by
  funext i
  by_cases hi : i = C.segmentSplitInsertVertex k
  · subst i
    simp [segmentSplitParameterAt]
  · let old : Fin (C.length + 1) :=
      (k.succ : Fin (C.length + 1)).predAbove i
    have hsucc :
        (C.segmentSplitInsertVertex k).succAbove old = i := by
      simpa [old, segmentSplitInsertVertex] using
        (Fin.succAbove_predAbove (p := (k.succ : Fin (C.length + 1)))
          (i := i) (by simpa [segmentSplitInsertVertex] using hi))
    rw [← hsucc]
    rw [C.segmentSplitParameterAt_old k τ old]
    rw [Fin.insertNth_apply_succAbove]

/--
%%handwave
name:
  Old branches after splitting a segment
statement:
  Every old subdivision vertex retains its branch assignment after one
  segment is split.
proof:
  The embedding avoids the new vertex and deletion recovers the old index.
-/
@[simp]
theorem segmentSplitBranchAt_old
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (i : Fin (C.length + 1)) :
    C.segmentSplitBranchAt k
        ((C.segmentSplitInsertVertex k).succAbove i) =
      C.branchAt i := by
  unfold segmentSplitBranchAt segmentSplitInsertVertex
  rw [if_neg]
  · rw [Fin.predAbove_succAbove]
  · exact Fin.succAbove_ne _ _

/--
%%handwave
name:
  Old transition products after splitting a segment
statement:
  Every old vertex retains its accumulated transition product after a segment
  split.
proof:
  The embedded old index is not the insertion position, so the old-product
  clause applies.
-/
@[simp]
theorem segmentSplitTransitionProductAt_old
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (i : Fin (C.length + 1)) :
    C.segmentSplitTransitionProductAt k
        ((C.segmentSplitInsertVertex k).succAbove i) =
      C.transitionProductAt i := by
  unfold segmentSplitTransitionProductAt segmentSplitInsertVertex
  rw [if_neg]
  · rw [Fin.predAbove_succAbove]
  · exact Fin.succAbove_ne _ _

/--
%%handwave
name:
  Initial vertex embedding under a segment split
statement:
  The old initial vertex remains the initial vertex after inserting a point
  into any segment.
proof:
  The insertion occurs strictly after index zero.
-/
theorem segmentSplitInsertVertex_succAbove_zero
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    (C.segmentSplitInsertVertex k).succAbove (0 : Fin (C.length + 1)) =
      0 := by
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · change (0 : ℕ) < (k : ℕ) + 1
    exact Nat.succ_pos _

/--
%%handwave
name:
  Terminal vertex embedding under a segment split
statement:
  The old terminal vertex becomes the terminal vertex of the enlarged
  subdivision.
proof:
  The insertion occurs at or before the old terminal index, shifting that
  terminal index forward by one.
-/
theorem segmentSplitInsertVertex_succAbove_last
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    (C.segmentSplitInsertVertex k).succAbove (Fin.last C.length) =
      Fin.last (C.length + 1) := by
  rw [Fin.succAbove_of_le_castSucc]
  · exact fin_last_succ_eq_last
  · change (k : ℕ) + 1 ≤ C.length
    exact k.isLt

/--
%%handwave
name:
  Embedding the old left endpoint of a split segment
statement:
  The old left endpoint of segment \(k\) embeds unchanged immediately before
  the newly inserted vertex.
proof:
  Its index is strictly smaller than the insertion position \(k+1\).
-/
theorem segmentSplitInsertVertex_succAbove_left
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    (C.segmentSplitInsertVertex k).succAbove k.castSucc =
      (k.castSucc : Fin (C.length + 1)).castSucc := by
  rw [Fin.succAbove_of_castSucc_lt]
  change (k : ℕ) < (k : ℕ) + 1
  exact Nat.lt_succ_self _

/--
%%handwave
name:
  Embedding the old right endpoint of a split segment
statement:
  The old right endpoint of segment \(k\) embeds one place after the inserted
  vertex.
proof:
  Its old index is the insertion position, so embedding around that position
  shifts it by one.
-/
theorem segmentSplitInsertVertex_succAbove_right
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    (C.segmentSplitInsertVertex k).succAbove k.succ =
      (k.succ : Fin (C.length + 1)).succ := by
  rw [Fin.succAbove_of_le_castSucc]
  rfl

/--
%%handwave
name:
  Left endpoints before a segment split embed unchanged
statement:
  A left endpoint belonging to a segment strictly before the split segment
  keeps the same index after insertion.
proof:
  Its index lies strictly below the insertion position.
-/
theorem segmentSplitInsertVertex_succAbove_before_castSucc
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (j : Fin (C.length + 1))
    (hj : (j : ℕ) < (k : ℕ)) :
    (C.segmentSplitInsertVertex k).succAbove
        ((⟨j, Nat.lt_trans hj k.isLt⟩ : Fin C.length).castSucc) =
      j.castSucc := by
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · exact_mod_cast Nat.lt_succ_of_lt hj

/--
%%handwave
name:
  Right endpoints before a segment split embed unchanged
statement:
  A right endpoint of a segment strictly before the split segment keeps its
  same index in the enlarged subdivision.
proof:
  That endpoint still lies strictly below the insertion position.
-/
theorem segmentSplitInsertVertex_succAbove_before_succ
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (j : Fin (C.length + 1))
    (hj : (j : ℕ) < (k : ℕ)) :
    (C.segmentSplitInsertVertex k).succAbove
        ((⟨j, Nat.lt_trans hj k.isLt⟩ : Fin C.length).succ) =
      j.succ := by
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · exact_mod_cast Nat.succ_lt_succ hj

/--
%%handwave
name:
  Left endpoints after a segment split shift by one
statement:
  A left endpoint belonging strictly after the split segment embeds at its
  old index shifted forward by one.
proof:
  It lies beyond the insertion position, so inserting a new vertex increments
  its index.
-/
theorem segmentSplitInsertVertex_succAbove_after_castSucc
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (j : Fin (C.length + 1))
    (hj : (k : ℕ) + 1 < (j : ℕ)) :
    (C.segmentSplitInsertVertex k).succAbove
        ((⟨(j : ℕ) - 1, by omega⟩ : Fin C.length).castSucc) =
      j.castSucc := by
  rw [Fin.succAbove_of_le_castSucc]
  · ext
    simp
    omega
  · exact_mod_cast Nat.le_pred_of_lt hj

/--
%%handwave
name:
  Right endpoints after a segment split shift by one
statement:
  A right endpoint belonging strictly after the split segment embeds at its
  old index shifted forward by one.
proof:
  The new vertex is inserted earlier, hence all subsequent indices increase
  by one.
-/
theorem segmentSplitInsertVertex_succAbove_after_succ
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (j : Fin (C.length + 1))
    (hj : (k : ℕ) + 1 < (j : ℕ)) :
    (C.segmentSplitInsertVertex k).succAbove
        ((⟨(j : ℕ) - 1, by omega⟩ : Fin C.length).succ) =
      j.succ := by
  rw [Fin.succAbove_of_le_castSucc]
  · ext
    simp
    omega
  · change (k : ℕ) + 1 ≤ (j : ℕ) - 1 + 1
    omega

/--
%%handwave
name:
  Initial parameter after a segment split
statement:
  Splitting a segment leaves the initial subdivision parameter equal to zero.
proof:
  The old initial vertex remains first and retains its parameter.
-/
@[simp]
theorem segmentSplitParameterAt_zero
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval) :
    C.segmentSplitParameterAt k τ 0 = 0 := by
  rw [← C.segmentSplitInsertVertex_succAbove_zero k,
    C.segmentSplitParameterAt_old k τ 0, C.parameterAt_zero]

/--
%%handwave
name:
  Terminal parameter after a segment split
statement:
  Splitting a segment leaves the final subdivision parameter equal to one.
proof:
  The old terminal vertex remains last and retains its parameter.
-/
@[simp]
theorem segmentSplitParameterAt_last
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval) :
    C.segmentSplitParameterAt k τ (Fin.last (C.length + 1)) = 1 := by
  rw [← C.segmentSplitInsertVertex_succAbove_last k,
    C.segmentSplitParameterAt_old k τ (Fin.last C.length),
    C.parameterAt_last]

/--
%%handwave
name:
  Initial branch after a segment split
statement:
  Splitting a segment leaves the initial branch unchanged.
proof:
  The old initial vertex is retained.
-/
@[simp]
theorem segmentSplitBranchAt_zero
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    C.segmentSplitBranchAt k 0 = C.branchAt 0 := by
  rw [← C.segmentSplitInsertVertex_succAbove_zero k,
    C.segmentSplitBranchAt_old k 0]

/--
%%handwave
name:
  Terminal branch after a segment split
statement:
  Splitting a segment leaves the terminal branch unchanged.
proof:
  The old terminal vertex embeds as the new terminal vertex.
-/
@[simp]
theorem segmentSplitBranchAt_last
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    C.segmentSplitBranchAt k (Fin.last (C.length + 1)) =
      C.terminalBranch := by
  rw [← C.segmentSplitInsertVertex_succAbove_last k,
    C.segmentSplitBranchAt_old k (Fin.last C.length)]
  rfl

/--
%%handwave
name:
  Initial transition product after a segment split
statement:
  The accumulated transition at the initial vertex is unchanged by splitting
  a segment.
proof:
  The initial old vertex retains its assigned product.
-/
@[simp]
theorem segmentSplitTransitionProductAt_zero
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    C.segmentSplitTransitionProductAt k 0 = C.transitionProductAt 0 := by
  rw [← C.segmentSplitInsertVertex_succAbove_zero k,
    C.segmentSplitTransitionProductAt_old k 0]

/--
%%handwave
name:
  Terminal transition product after a segment split
statement:
  The terminal accumulated transition is unchanged by splitting a segment.
proof:
  The old terminal vertex becomes the new terminal vertex and retains its
  product.
-/
@[simp]
theorem segmentSplitTransitionProductAt_last
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    C.segmentSplitTransitionProductAt k (Fin.last (C.length + 1)) =
      C.terminalTransition := by
  rw [← C.segmentSplitInsertVertex_succAbove_last k,
    C.segmentSplitTransitionProductAt_old k (Fin.last C.length)]
  rfl

/--
%%handwave
name:
  The inserted point lies in its assigned branch domain
statement:
  If \(\tau\) lies between the endpoints of segment \(k\), then the path point
  \(p(\tau)\) lies in the branch domain assigned to the left endpoint.
proof:
  This is the original chain's domain condition on the whole segment.
-/
theorem segmentSplit_insert_mem_domain
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    p τ ∈ S.domain (C.branchAt k.castSucc) :=
  C.path_segment_mem_domain k τ hτ_left hτ_right

/--
%%handwave
name:
  Vertex-domain condition after a segment split
statement:
  Every vertex of a subdivision obtained by splitting one segment lies in the
  domain of its assigned branch.
proof:
  The inserted vertex uses the original segment-domain condition; every old
  vertex reduces to the original chain's vertex-domain condition.
-/
theorem segmentSplit_sample_mem_domain
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    ∀ i : Fin (C.length + 2),
      p (C.segmentSplitParameterAt k τ i) ∈
        S.domain (C.segmentSplitBranchAt k i) := by
  intro i
  by_cases hi : i = C.segmentSplitInsertVertex k
  · subst i
    simpa using C.segmentSplit_insert_mem_domain k τ hτ_left hτ_right
  · let old : Fin (C.length + 1) :=
      (k.succ : Fin (C.length + 1)).predAbove i
    have hsucc :
        (C.segmentSplitInsertVertex k).succAbove old = i := by
      simpa [old, segmentSplitInsertVertex] using
        (Fin.succAbove_predAbove (p := (k.succ : Fin (C.length + 1)))
          (i := i) (by simpa [segmentSplitInsertVertex] using hi))
    rw [← hsucc, C.segmentSplitParameterAt_old k τ old,
      C.segmentSplitBranchAt_old k old]
    exact C.sample_mem_domain old

/--
%%handwave
name:
  Segment-domain condition after a segment split
statement:
  Every segment of the refined subdivision remains in the branch domain
  attached to its left endpoint.
proof:
  The two pieces of the split segment are contained in its original branch
  domain.  Segments before and after it correspond exactly to old segments
  after the appropriate index embedding.
-/
theorem segmentSplit_path_segment_mem_domain
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    ∀ j : Fin (C.length + 1), ∀ t : unitInterval,
      (C.segmentSplitParameterAt k τ j.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (C.segmentSplitParameterAt k τ j.succ : ℝ) →
      p t ∈ S.domain (C.segmentSplitBranchAt k j.castSucc) := by
  intro j t ht_left ht_right
  by_cases hj_left : j = k.castSucc
  · subst j
    have hleft_index := C.segmentSplitInsertVertex_succAbove_left k
    have hparam_left :
        C.segmentSplitParameterAt k τ (k.castSucc.castSucc) =
          C.parameterAt k.castSucc := by
      rw [← hleft_index, C.segmentSplitParameterAt_old k τ k.castSucc]
    have hbranch_left :
        C.segmentSplitBranchAt k (k.castSucc.castSucc) =
          C.branchAt k.castSucc := by
      rw [← hleft_index, C.segmentSplitBranchAt_old k k.castSucc]
    rw [hparam_left] at ht_left
    rw [fin_castSucc_succ_eq_succ_castSucc k] at ht_right
    change (t : ℝ) ≤
      (C.segmentSplitParameterAt k τ (C.segmentSplitInsertVertex k) : ℝ)
      at ht_right
    rw [C.segmentSplitParameterAt_insert k τ] at ht_right
    rw [hbranch_left]
    exact C.path_segment_mem_domain k t ht_left
      (le_trans ht_right hτ_right)
  by_cases hj_right : j = k.succ
  · subst j
    have hright_index := C.segmentSplitInsertVertex_succAbove_right k
    have hparam_right :
        C.segmentSplitParameterAt k τ (k.succ : Fin (C.length + 1)).succ =
          C.parameterAt k.succ := by
      rw [← hright_index, C.segmentSplitParameterAt_old k τ k.succ]
    change
      (C.segmentSplitParameterAt k τ (C.segmentSplitInsertVertex k) : ℝ) ≤
        (t : ℝ) at ht_left
    rw [C.segmentSplitParameterAt_insert k τ] at ht_left
    rw [hparam_right] at ht_right
    change p t ∈ S.domain
      (C.segmentSplitBranchAt k (C.segmentSplitInsertVertex k))
    rw [C.segmentSplitBranchAt_insert k]
    exact C.path_segment_mem_domain k t
      (le_trans hτ_left ht_left) ht_right
  by_cases hj_before : (j : ℕ) < (k : ℕ)
  · let e : Fin C.length := ⟨j, Nat.lt_trans hj_before k.isLt⟩
    have hleft_index :
        (C.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      C.segmentSplitInsertVertex_succAbove_before_castSucc k j hj_before
    have hright_index :
        (C.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      C.segmentSplitInsertVertex_succAbove_before_succ k j hj_before
    have hparam_left :
        C.segmentSplitParameterAt k τ j.castSucc =
          C.parameterAt e.castSucc := by
      rw [← hleft_index, C.segmentSplitParameterAt_old k τ e.castSucc]
    have hparam_right :
        C.segmentSplitParameterAt k τ j.succ =
          C.parameterAt e.succ := by
      rw [← hright_index, C.segmentSplitParameterAt_old k τ e.succ]
    have hbranch_left :
        C.segmentSplitBranchAt k j.castSucc =
          C.branchAt e.castSucc := by
      rw [← hleft_index, C.segmentSplitBranchAt_old k e.castSucc]
    rw [hparam_left] at ht_left
    rw [hparam_right] at ht_right
    rw [hbranch_left]
    exact C.path_segment_mem_domain e t ht_left ht_right
  · have hne_left_nat : (j : ℕ) ≠ (k : ℕ) := by
      intro h
      exact hj_left (Fin.ext h)
    have hne_right_nat : (j : ℕ) ≠ (k : ℕ) + 1 := by
      intro h
      exact hj_right (Fin.ext h)
    have hj_after : (k : ℕ) + 1 < (j : ℕ) := by
      omega
    let e : Fin C.length := ⟨(j : ℕ) - 1, by omega⟩
    have hleft_index :
        (C.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      C.segmentSplitInsertVertex_succAbove_after_castSucc k j hj_after
    have hright_index :
        (C.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      C.segmentSplitInsertVertex_succAbove_after_succ k j hj_after
    have hparam_left :
        C.segmentSplitParameterAt k τ j.castSucc =
          C.parameterAt e.castSucc := by
      rw [← hleft_index, C.segmentSplitParameterAt_old k τ e.castSucc]
    have hparam_right :
        C.segmentSplitParameterAt k τ j.succ =
          C.parameterAt e.succ := by
      rw [← hright_index, C.segmentSplitParameterAt_old k τ e.succ]
    have hbranch_left :
        C.segmentSplitBranchAt k j.castSucc =
          C.branchAt e.castSucc := by
      rw [← hleft_index, C.segmentSplitBranchAt_old k e.castSucc]
    rw [hparam_left] at ht_left
    rw [hparam_right] at ht_right
    rw [hbranch_left]
    exact C.path_segment_mem_domain e t ht_left ht_right

/--
%%handwave
name:
  Monotonicity after splitting one segment
statement:
  If \(t_k\le\tau\le t_{k+1}\), inserting \(\tau\) into a nondecreasing
  subdivision preserves nondecreasing order.
proof:
  The two new inequalities are precisely
  \(t_k\le\tau\) and \(\tau\le t_{k+1}\); every other adjacent pair is an
  old monotone pair.
-/
theorem segmentSplitParameterAt_mono
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    ∀ j : Fin (C.length + 1),
      (C.segmentSplitParameterAt k τ j.castSucc : ℝ) ≤
        (C.segmentSplitParameterAt k τ j.succ : ℝ) := by
  intro j
  by_cases hj_left : j = k.castSucc
  · subst j
    have hleft_index := C.segmentSplitInsertVertex_succAbove_left k
    have hparam_left :
        C.segmentSplitParameterAt k τ (k.castSucc.castSucc) =
          C.parameterAt k.castSucc := by
      rw [← hleft_index, C.segmentSplitParameterAt_old k τ k.castSucc]
    rw [hparam_left]
    rw [fin_castSucc_succ_eq_succ_castSucc k]
    change (C.parameterAt k.castSucc : ℝ) ≤
      (C.segmentSplitParameterAt k τ (C.segmentSplitInsertVertex k) : ℝ)
    rw [C.segmentSplitParameterAt_insert k τ]
    exact hτ_left
  by_cases hj_right : j = k.succ
  · subst j
    have hright_index := C.segmentSplitInsertVertex_succAbove_right k
    have hparam_right :
        C.segmentSplitParameterAt k τ (k.succ : Fin (C.length + 1)).succ =
          C.parameterAt k.succ := by
      rw [← hright_index, C.segmentSplitParameterAt_old k τ k.succ]
    change
      (C.segmentSplitParameterAt k τ (C.segmentSplitInsertVertex k) : ℝ) ≤
        (C.segmentSplitParameterAt k τ
          ((k.succ : Fin (C.length + 1)).succ) : ℝ)
    rw [C.segmentSplitParameterAt_insert k τ, hparam_right]
    exact hτ_right
  by_cases hj_before : (j : ℕ) < (k : ℕ)
  · let e : Fin C.length := ⟨j, Nat.lt_trans hj_before k.isLt⟩
    have hleft_index :
        (C.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      C.segmentSplitInsertVertex_succAbove_before_castSucc k j hj_before
    have hright_index :
        (C.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      C.segmentSplitInsertVertex_succAbove_before_succ k j hj_before
    have hparam_left :
        C.segmentSplitParameterAt k τ j.castSucc =
          C.parameterAt e.castSucc := by
      rw [← hleft_index, C.segmentSplitParameterAt_old k τ e.castSucc]
    have hparam_right :
        C.segmentSplitParameterAt k τ j.succ =
          C.parameterAt e.succ := by
      rw [← hright_index, C.segmentSplitParameterAt_old k τ e.succ]
    rw [hparam_left, hparam_right]
    exact C.parameterAt_mono e
  · have hne_left_nat : (j : ℕ) ≠ (k : ℕ) := by
      intro h
      exact hj_left (Fin.ext h)
    have hne_right_nat : (j : ℕ) ≠ (k : ℕ) + 1 := by
      intro h
      exact hj_right (Fin.ext h)
    have hj_after : (k : ℕ) + 1 < (j : ℕ) := by
      omega
    let e : Fin C.length := ⟨(j : ℕ) - 1, by omega⟩
    have hleft_index :
        (C.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      C.segmentSplitInsertVertex_succAbove_after_castSucc k j hj_after
    have hright_index :
        (C.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      C.segmentSplitInsertVertex_succAbove_after_succ k j hj_after
    have hparam_left :
        C.segmentSplitParameterAt k τ j.castSucc =
          C.parameterAt e.castSucc := by
      rw [← hleft_index, C.segmentSplitParameterAt_old k τ e.castSucc]
    have hparam_right :
        C.segmentSplitParameterAt k τ j.succ =
          C.parameterAt e.succ := by
      rw [← hright_index, C.segmentSplitParameterAt_old k τ e.succ]
    rw [hparam_left, hparam_right]
    exact C.parameterAt_mono e

/--
%%handwave
name:
  Terminal endpoint remains in the terminal branch after a split
statement:
  After splitting any segment, the path endpoint still belongs to the domain
  of the resulting terminal branch.
proof:
  The terminal branch is unchanged, so use the original terminal endpoint
  condition.
-/
theorem segmentSplit_terminal_endpoint_mem_domain
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) :
    x ∈ S.domain (C.segmentSplitBranchAt k (Fin.last (C.length + 1))) := by
  simpa [C.segmentSplitBranchAt_last k] using C.terminal_endpoint_mem_domain

/--
Transition data for every handoff of a segment-split chain.

The split segment contributes two transitions: an identity transition into the
inserted vertex and the original transition out of it. All other handoffs are
transported from the old chain.
-/
noncomputable def segmentSplitTransitionAt
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    ∀ j : Fin (C.length + 1),
      S.LocalTransition
        (C.segmentSplitBranchAt k j.castSucc)
        (C.segmentSplitBranchAt k j.succ)
        (p (C.segmentSplitParameterAt k τ j.succ)) := by
  intro j
  by_cases hj_left : j = k.castSucc
  · subst j
    have hleft_index := C.segmentSplitInsertVertex_succAbove_left k
    have hU :
        C.segmentSplitBranchAt k k.castSucc.castSucc =
          C.branchAt k.castSucc := by
      rw [← hleft_index, C.segmentSplitBranchAt_old k k.castSucc]
    have hV :
        C.segmentSplitBranchAt k
            ((k.castSucc : Fin (C.length + 1)).succ) =
          C.branchAt k.castSucc := by
      rw [fin_castSucc_succ_eq_succ_castSucc k]
      change
        C.segmentSplitBranchAt k (C.segmentSplitInsertVertex k) =
          C.branchAt k.castSucc
      rw [C.segmentSplitBranchAt_insert k]
    have hpoint :
        p (C.segmentSplitParameterAt k τ
            ((k.castSucc : Fin (C.length + 1)).succ)) =
          p τ := by
      rw [fin_castSucc_succ_eq_succ_castSucc k]
      change
        p (C.segmentSplitParameterAt k τ (C.segmentSplitInsertVertex k)) =
          p τ
      rw [C.segmentSplitParameterAt_insert k τ]
    exact
      (LocalTransition.refl (S := S) (C.branchAt k.castSucc)
        (C.segmentSplit_insert_mem_domain k τ hτ_left hτ_right)).congr
        hU.symm hV.symm hpoint.symm
  by_cases hj_right : j = k.succ
  · subst j
    have hright_index := C.segmentSplitInsertVertex_succAbove_right k
    have hU :
        C.segmentSplitBranchAt k
            ((k.succ : Fin (C.length + 1)).castSucc) =
          C.branchAt k.castSucc := by
      change
        C.segmentSplitBranchAt k (C.segmentSplitInsertVertex k) =
          C.branchAt k.castSucc
      rw [C.segmentSplitBranchAt_insert k]
    have hV :
        C.segmentSplitBranchAt k
            ((k.succ : Fin (C.length + 1)).succ) =
          C.branchAt k.succ := by
      rw [← hright_index, C.segmentSplitBranchAt_old k k.succ]
    have hpoint :
        p (C.segmentSplitParameterAt k τ
            ((k.succ : Fin (C.length + 1)).succ)) =
          p (C.parameterAt k.succ) := by
      rw [← hright_index, C.segmentSplitParameterAt_old k τ k.succ]
    exact (C.transitionAt k).congr hU.symm hV.symm hpoint.symm
  by_cases hj_before : (j : ℕ) < (k : ℕ)
  · let e : Fin C.length := ⟨j, Nat.lt_trans hj_before k.isLt⟩
    have hleft_index :
        (C.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      C.segmentSplitInsertVertex_succAbove_before_castSucc k j hj_before
    have hright_index :
        (C.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      C.segmentSplitInsertVertex_succAbove_before_succ k j hj_before
    have hU :
        C.segmentSplitBranchAt k j.castSucc =
          C.branchAt e.castSucc := by
      rw [← hleft_index, C.segmentSplitBranchAt_old k e.castSucc]
    have hV :
        C.segmentSplitBranchAt k j.succ =
          C.branchAt e.succ := by
      rw [← hright_index, C.segmentSplitBranchAt_old k e.succ]
    have hpoint :
        p (C.segmentSplitParameterAt k τ j.succ) =
          p (C.parameterAt e.succ) := by
      rw [← hright_index, C.segmentSplitParameterAt_old k τ e.succ]
    exact (C.transitionAt e).congr hU.symm hV.symm hpoint.symm
  · have hne_left_nat : (j : ℕ) ≠ (k : ℕ) := by
      intro h
      exact hj_left (Fin.ext h)
    have hne_right_nat : (j : ℕ) ≠ (k : ℕ) + 1 := by
      intro h
      exact hj_right (Fin.ext h)
    have hj_after : (k : ℕ) + 1 < (j : ℕ) := by
      omega
    let e : Fin C.length := ⟨(j : ℕ) - 1, by omega⟩
    have hleft_index :
        (C.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
      C.segmentSplitInsertVertex_succAbove_after_castSucc k j hj_after
    have hright_index :
        (C.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
      C.segmentSplitInsertVertex_succAbove_after_succ k j hj_after
    have hU :
        C.segmentSplitBranchAt k j.castSucc =
          C.branchAt e.castSucc := by
      rw [← hleft_index, C.segmentSplitBranchAt_old k e.castSucc]
    have hV :
        C.segmentSplitBranchAt k j.succ =
          C.branchAt e.succ := by
      rw [← hright_index, C.segmentSplitBranchAt_old k e.succ]
    have hpoint :
        p (C.segmentSplitParameterAt k τ j.succ) =
          p (C.parameterAt e.succ) := by
      rw [← hright_index, C.segmentSplitParameterAt_old k τ e.succ]
    exact (C.transitionAt e).congr hU.symm hV.symm hpoint.symm

/--
Split a single segment of a finite continuation chain.

The inserted vertex uses the branch controlling the left half of the old
segment.  The new handoffs are the identity at the inserted point followed by
the original transition at the old right endpoint.
-/
noncomputable def segmentSplitChain
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    S.PathContinuationChain x₀ i₀ p where
  length := C.length + 1
  parameterAt := C.segmentSplitParameterAt k τ
  parameterAt_zero := C.segmentSplitParameterAt_zero k τ
  parameterAt_last := C.segmentSplitParameterAt_last k τ
  parameterAt_mono := C.segmentSplitParameterAt_mono k τ hτ_left hτ_right
  branchAt := C.segmentSplitBranchAt k
  initialTransition := by
    exact C.initialTransition.congr rfl (by simp [C.segmentSplitBranchAt_zero k]) rfl
  transitionProductAt := C.segmentSplitTransitionProductAt k
  transitionProductAt_zero := by
    simp [C.segmentSplitTransitionProductAt_zero k, C.transitionProductAt_zero]
  transitionAt := C.segmentSplitTransitionAt k τ hτ_left hτ_right
  transitionProductAt_succ_eq := by
    intro j
    by_cases hj_left : j = k.castSucc
    · subst j
      have hleft_index := C.segmentSplitInsertVertex_succAbove_left k
      have hprod_left :
          C.segmentSplitTransitionProductAt k k.castSucc.castSucc =
            C.transitionProductAt k.castSucc := by
        rw [← hleft_index, C.segmentSplitTransitionProductAt_old k k.castSucc]
      have htrans :
          (C.segmentSplitTransitionAt k τ hτ_left hτ_right k.castSucc).transition =
            1 := by
        simp [segmentSplitTransitionAt, LocalTransition.refl]
      have hprod_right :
          C.segmentSplitTransitionProductAt k
              ((k.castSucc : Fin (C.length + 1)).succ) =
            C.transitionProductAt k.castSucc := by
        rw [fin_castSucc_succ_eq_succ_castSucc k]
        exact C.segmentSplitTransitionProductAt_insert k
      rw [hprod_right, hprod_left, htrans]
      simp
    by_cases hj_right : j = k.succ
    · subst j
      have hright_index := C.segmentSplitInsertVertex_succAbove_right k
      have hprod_right :
          C.segmentSplitTransitionProductAt k
              ((k.succ : Fin (C.length + 1)).succ) =
            C.transitionProductAt k.succ := by
        rw [← hright_index, C.segmentSplitTransitionProductAt_old k k.succ]
      have hprod_left :
          C.segmentSplitTransitionProductAt k
              ((k.succ : Fin (C.length + 1)).castSucc) =
            C.transitionProductAt k.castSucc := by
        change
          C.segmentSplitTransitionProductAt k (C.segmentSplitInsertVertex k) =
            C.transitionProductAt k.castSucc
        rw [C.segmentSplitTransitionProductAt_insert k]
      have htrans :
          (C.segmentSplitTransitionAt k τ hτ_left hτ_right k.succ).transition =
            (C.transitionAt k).transition := by
        have hne : (k.succ : Fin (C.length + 1)) ≠ k.castSucc := by
          intro h
          have : (k : ℕ) + 1 = (k : ℕ) := Fin.ext_iff.mp h
          omega
        simp [segmentSplitTransitionAt, hne]
      rw [hprod_right, hprod_left, htrans, C.transitionProductAt_succ_eq k]
    by_cases hj_before : (j : ℕ) < (k : ℕ)
    · let e : Fin C.length := ⟨j, Nat.lt_trans hj_before k.isLt⟩
      have hleft_index :
          (C.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
        C.segmentSplitInsertVertex_succAbove_before_castSucc k j hj_before
      have hright_index :
          (C.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
        C.segmentSplitInsertVertex_succAbove_before_succ k j hj_before
      have hprod_left :
          C.segmentSplitTransitionProductAt k j.castSucc =
            C.transitionProductAt e.castSucc := by
        rw [← hleft_index, C.segmentSplitTransitionProductAt_old k e.castSucc]
      have hprod_right :
          C.segmentSplitTransitionProductAt k j.succ =
            C.transitionProductAt e.succ := by
        rw [← hright_index, C.segmentSplitTransitionProductAt_old k e.succ]
      have htrans :
          (C.segmentSplitTransitionAt k τ hτ_left hτ_right j).transition =
            (C.transitionAt e).transition := by
        have hne_left : j ≠ k.castSucc := by
          intro h
          have : (j : ℕ) = (k : ℕ) := Fin.ext_iff.mp h
          omega
        have hne_right : j ≠ (k.succ : Fin (C.length + 1)) := by
          intro h
          have : (j : ℕ) = (k : ℕ) + 1 := Fin.ext_iff.mp h
          omega
        simp [segmentSplitTransitionAt, hne_left, hne_right, hj_before, e]
      rw [hprod_right, hprod_left, htrans, C.transitionProductAt_succ_eq e]
    · have hne_left_nat : (j : ℕ) ≠ (k : ℕ) := by
        intro h
        exact hj_left (Fin.ext h)
      have hne_right_nat : (j : ℕ) ≠ (k : ℕ) + 1 := by
        intro h
        exact hj_right (Fin.ext h)
      have hj_after : (k : ℕ) + 1 < (j : ℕ) := by
        omega
      let e : Fin C.length := ⟨(j : ℕ) - 1, by omega⟩
      have hleft_index :
          (C.segmentSplitInsertVertex k).succAbove e.castSucc = j.castSucc :=
        C.segmentSplitInsertVertex_succAbove_after_castSucc k j hj_after
      have hright_index :
          (C.segmentSplitInsertVertex k).succAbove e.succ = j.succ :=
        C.segmentSplitInsertVertex_succAbove_after_succ k j hj_after
      have hprod_left :
          C.segmentSplitTransitionProductAt k j.castSucc =
            C.transitionProductAt e.castSucc := by
        rw [← hleft_index, C.segmentSplitTransitionProductAt_old k e.castSucc]
      have hprod_right :
          C.segmentSplitTransitionProductAt k j.succ =
            C.transitionProductAt e.succ := by
        rw [← hright_index, C.segmentSplitTransitionProductAt_old k e.succ]
      have htrans :
          (C.segmentSplitTransitionAt k τ hτ_left hτ_right j).transition =
            (C.transitionAt e).transition := by
        have hne_left : j ≠ k.castSucc := by
          intro h
          have : (j : ℕ) = (k : ℕ) := Fin.ext_iff.mp h
          omega
        have hne_right : j ≠ (k.succ : Fin (C.length + 1)) := by
          intro h
          have : (j : ℕ) = (k : ℕ) + 1 := Fin.ext_iff.mp h
          omega
        have hnot_before : ¬(j : ℕ) < (k : ℕ) := by omega
        simp [segmentSplitTransitionAt, hne_left, hne_right, hnot_before, e]
      rw [hprod_right, hprod_left, htrans, C.transitionProductAt_succ_eq e]
  sample_mem_domain := C.segmentSplit_sample_mem_domain k τ hτ_left hτ_right
  path_segment_mem_domain :=
    C.segmentSplit_path_segment_mem_domain k τ hτ_left hτ_right
  terminal_endpoint_mem_domain := C.segmentSplit_terminal_endpoint_mem_domain k

/--
%%handwave
name:
  Terminal branch of a segment-split chain
statement:
  Inserting a subdivision point into one segment does not change the chain's
  terminal branch.
proof:
  The old terminal vertex remains the terminal vertex and retains its branch.
-/
@[simp]
theorem segmentSplitChain_terminalBranch
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    (C.segmentSplitChain k τ hτ_left hτ_right).terminalBranch =
      C.terminalBranch := by
  simp [segmentSplitChain, terminalBranch]

/--
%%handwave
name:
  Terminal transition of a segment-split chain
statement:
  Inserting a subdivision point into one segment does not change the terminal
  accumulated transition.
proof:
  The old terminal vertex retains its transition product.
-/
@[simp]
theorem segmentSplitChain_terminalTransition
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    (C.segmentSplitChain k τ hτ_left hτ_right).terminalTransition =
      C.terminalTransition := by
  simp [segmentSplitChain, terminalTransition]

/--
%%handwave
name:
  Subdivision of one continuation segment preserves the terminal germ
statement:
  Let \(C\) be a continuation chain along \(p:x_0\to x\), with subdivision
  parameters \(t_0\le\cdots\le t_N\). If
  \(t_k\le\tau\le t_{k+1}\), inserting \(\tau\) into the \(k\)-th segment and
  repeating its branch data gives a chain whose terminal germ is locally
  equal to that of \(C\) at \(x\).
proof:
  The inserted vertex leaves the terminal branch \(\beta_N\) and accumulated
  transition \(g_N\) unchanged. Hence both terminal germs are defined on
  \(D_{\beta_N}\) and represent the same map \(g_N\cdot f_{\beta_N}\) there.
-/
theorem segmentSplitChain_terminalGerms_agree
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    C.toTerminalGerm.LocallyAgreesWith
      (C.segmentSplitChain k τ hτ_left hτ_right).toTerminalGerm := by
  refine
    ⟨S.domain C.terminalBranch, S.domain_open C.terminalBranch,
      C.endpoint_mem_terminalBranch, ?_, ?_⟩
  · intro z hz
    constructor
    · simpa [PathContinuationChain.toTerminalGerm] using hz
    · simpa [PathContinuationChain.toTerminalGerm,
        C.segmentSplitChain_terminalBranch k τ hτ_left hτ_right] using hz
  · intro z _hz
    simp [PathContinuationGerm.localMap, PathContinuationChain.toTerminalGerm,
      C.segmentSplitChain_terminalBranch k τ hτ_left hτ_right,
      C.segmentSplitChain_terminalTransition k τ hτ_left hτ_right]

/--
Split a chain at an arbitrary parameter, choosing a containing segment by the
finite-subdivision locator.
-/
noncomputable def splitAtParameterChain
    (C : S.PathContinuationChain x₀ i₀ p)
    (τ : unitInterval) :
    S.PathContinuationChain x₀ i₀ p :=
  let k := Classical.choose (C.exists_segment_contains_parameter τ)
  let hk := Classical.choose_spec (C.exists_segment_contains_parameter τ)
  C.segmentSplitChain k τ hk.1 hk.2

/--
%%handwave
name:
  Length after splitting at an arbitrary parameter
statement:
  Splitting a continuation chain at one parameter increases its number of
  segments by one.
proof:
  The chosen containing segment is replaced by its two subsegments.
-/
@[simp]
theorem splitAtParameterChain_length
    (C : S.PathContinuationChain x₀ i₀ p)
    (τ : unitInterval) :
    (C.splitAtParameterChain τ).length = C.length + 1 := by
  classical
  unfold splitAtParameterChain
  simp [segmentSplitChain]

/--
%%handwave
name:
  Splitting at an arbitrary parameter preserves the terminal germ
statement:
  A continuation chain and the chain obtained by inserting any parameter
  \(\tau\in[0,1]\) have locally agreeing terminal germs.
proof:
  Choose a subdivision segment containing \(\tau\) and apply invariance of
  the terminal germ under splitting that segment.
-/
theorem splitAtParameterChain_terminalGerms_agree
    (C : S.PathContinuationChain x₀ i₀ p)
    (τ : unitInterval) :
    C.toTerminalGerm.LocallyAgreesWith
      (C.splitAtParameterChain τ).toTerminalGerm := by
  classical
  unfold splitAtParameterChain
  exact
    C.segmentSplitChain_terminalGerms_agree
      (Classical.choose (C.exists_segment_contains_parameter τ)) τ
      (Classical.choose_spec (C.exists_segment_contains_parameter τ)).1
      (Classical.choose_spec (C.exists_segment_contains_parameter τ)).2

/--
Split the first `m` sampled parameters of `D` into `C`.
-/
noncomputable def splitFirstVerticesOfChain
    (C D : S.PathContinuationChain x₀ i₀ p) :
    ℕ → S.PathContinuationChain x₀ i₀ p
  | 0 => C
  | m + 1 =>
      let R := splitFirstVerticesOfChain C D m
      if h : m < D.length + 1 then
        R.splitAtParameterChain (D.parameterAt ⟨m, h⟩)
      else
        R

/-- Split every sampled parameter of `D` into `C`. -/
noncomputable def splitAllVerticesOfChain
    (C D : S.PathContinuationChain x₀ i₀ p) :
    S.PathContinuationChain x₀ i₀ p :=
  C.splitFirstVerticesOfChain D (D.length + 1)

/--
%%handwave
name:
  Length after inserting an initial list of vertices
statement:
  After inserting the first \(m\) sampled parameters of a second chain into a
  chain of length \(n\), where \(m\) does not exceed the available vertices,
  the resulting length is \(n+m\).
proof:
  Induct on \(m\); each permitted parameter split adds exactly one segment.
-/
theorem splitFirstVerticesOfChain_length_of_le
    (C D : S.PathContinuationChain x₀ i₀ p) :
    ∀ m : ℕ, m ≤ D.length + 1 →
      (C.splitFirstVerticesOfChain D m).length = C.length + m := by
  intro m
  induction m with
  | zero =>
      intro _hm
      simp [splitFirstVerticesOfChain]
  | succ m ih =>
      intro hm
      have hm_prev : m ≤ D.length + 1 := by omega
      have hm_lt : m < D.length + 1 := by omega
      simp [splitFirstVerticesOfChain, hm_lt, ih hm_prev,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/--
%%handwave
name:
  Length after inserting every vertex of another chain
statement:
  If chains have lengths \(m\) and \(n\), inserting all \(n+1\) sampled
  vertices of the second into the first produces length \(m+n+1\).
proof:
  Apply the length formula for the first \(n+1\) inserted vertices.
-/
@[simp]
theorem splitAllVerticesOfChain_length
    (C D : S.PathContinuationChain x₀ i₀ p) :
    (C.splitAllVerticesOfChain D).length = C.length + (D.length + 1) := by
  simpa [splitAllVerticesOfChain] using
    C.splitFirstVerticesOfChain_length_of_le D (D.length + 1) le_rfl

/-- The parameter list of a finite continuation chain. -/
def parameterList (C : S.PathContinuationChain x₀ i₀ p) :
    List unitInterval :=
  List.ofFn C.parameterAt

/--
%%handwave
name:
  Sortedness of a continuation chain's parameter list
statement:
  The finite list of subdivision parameters of a continuation chain is
  nondecreasing.
proof:
  Consecutive list entries are consecutive subdivision parameters, ordered by
  the chain's monotonicity condition.
-/
theorem parameterList_sortedLE
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.parameterList.SortedLE := by
  classical
  rw [parameterList, List.sortedLE_iff_isChain, List.isChain_ofFn]
  intro i hi
  exact C.parameterAt_mono ⟨i, by omega⟩

/--
%%handwave
name:
  Permuted sorted parameter lists agree pointwise
statement:
  If two continuation chains have parameter lists that are permutations of
  one another, then their parameters at every common valid index are equal.
proof:
  Both lists are nondecreasing, so a permutation between them is equality.
  Taking the entry at the chosen index gives the pointwise identity.
-/
theorem parameterAt_eq_of_parameterList_perm
    (C D : S.PathContinuationChain x₀ i₀ p)
    (hPerm : List.Perm C.parameterList D.parameterList) :
    ∀ n (hnC : n ≤ C.length) (hnD : n ≤ D.length),
      C.parameterAt ⟨n, Nat.lt_succ_of_le hnC⟩ =
        D.parameterAt ⟨n, Nat.lt_succ_of_le hnD⟩ := by
  classical
  have hList : C.parameterList = D.parameterList :=
    List.Perm.eq_of_sortedLE C.parameterList_sortedLE D.parameterList_sortedLE
      hPerm
  intro n hnC hnD
  have hget := congrArg (fun l : List unitInterval => l[n]?) hList
  change C.parameterList[n]? = D.parameterList[n]? at hget
  have hCget :
      C.parameterList[n]? =
        some (C.parameterAt ⟨n, Nat.lt_succ_of_le hnC⟩) := by
    rw [parameterList, List.getElem?_ofFn]
    simp [Nat.lt_succ_of_le hnC]
  have hDget :
      D.parameterList[n]? =
        some (D.parameterAt ⟨n, Nat.lt_succ_of_le hnD⟩) := by
    rw [parameterList, List.getElem?_ofFn]
    simp [Nat.lt_succ_of_le hnD]
  rw [hCget, hDget] at hget
  exact Option.some.inj hget

/--
%%handwave
name:
  Parameter list after one segment split
statement:
  Splitting one segment at \(\tau\) produces a parameter list that is a
  permutation of \(\tau\) followed by the old parameter list.
proof:
  The new parameter tuple is obtained by inserting \(\tau\) at one finite
  position; listing an insertion differs from prepending only by permutation.
-/
theorem segmentSplitChain_parameterList_perm
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    List.Perm
      (C.segmentSplitChain k τ hτ_left hτ_right).parameterList
      (τ :: C.parameterList) := by
  classical
  change List.Perm (List.ofFn (C.segmentSplitParameterAt k τ))
    (τ :: List.ofFn C.parameterAt)
  rw [C.segmentSplitParameterAt_eq_insertNth k τ]
  exact ofFn_fin_insertNth_perm (C.segmentSplitInsertVertex k) τ C.parameterAt

/--
%%handwave
name:
  Parameter list after splitting at an arbitrary parameter
statement:
  Splitting a chain at \(\tau\) yields a parameter list that is a permutation
  of \(\tau\) followed by the original list.
proof:
  Choose a segment containing \(\tau\) and apply the one-segment insertion
  formula.
-/
theorem splitAtParameterChain_parameterList_perm
    (C : S.PathContinuationChain x₀ i₀ p)
    (τ : unitInterval) :
    List.Perm (C.splitAtParameterChain τ).parameterList
      (τ :: C.parameterList) := by
  classical
  unfold splitAtParameterChain
  exact
    C.segmentSplitChain_parameterList_perm
      (Classical.choose (C.exists_segment_contains_parameter τ)) τ
      (Classical.choose_spec (C.exists_segment_contains_parameter τ)).1
      (Classical.choose_spec (C.exists_segment_contains_parameter τ)).2

/--
The first `m` sampled parameters of a chain, listed in reverse recursive
order.
-/
def firstParameterListOfChain
    (D : S.PathContinuationChain x₀ i₀ p) :
    ℕ → List unitInterval
  | 0 => []
  | m + 1 =>
      if h : m < D.length + 1 then
        D.parameterAt ⟨m, h⟩ :: D.firstParameterListOfChain m
      else
        D.firstParameterListOfChain m

/--
%%handwave
name:
  Successor formula for the recursive parameter prefix
statement:
  When the \(m\)-th vertex exists, the recursively listed first \(m+1\)
  parameters are the \(m\)-th parameter followed by the first \(m\).
proof:
  This is the valid-index branch of the recursive definition.
-/
@[simp]
theorem firstParameterListOfChain_succ_of_lt
    (D : S.PathContinuationChain x₀ i₀ p)
    {m : ℕ} (hm : m < D.length + 1) :
    D.firstParameterListOfChain (m + 1) =
      D.parameterAt ⟨m, hm⟩ :: D.firstParameterListOfChain m := by
  simp [firstParameterListOfChain, hm]

/--
%%handwave
name:
  Recursive parameter prefix is a permutation of the ordered prefix
statement:
  For \(m\) within the vertex count, the recursively accumulated first
  parameter list is a permutation of the ordered list of the first \(m\)
  subdivision parameters.
proof:
  Induct on \(m\).  The recursion prepends the newest parameter, while the
  ordered prefix appends it; moving that element across the preceding list
  gives the required permutation.
-/
theorem firstParameterListOfChain_perm_prefix
    (D : S.PathContinuationChain x₀ i₀ p) :
    ∀ m : ℕ, ∀ hm : m ≤ D.length + 1,
      List.Perm (D.firstParameterListOfChain m)
        (List.ofFn fun i : Fin m =>
          D.parameterAt ⟨i, by omega⟩) := by
  intro m
  induction m with
  | zero =>
      intro _hm
      simp [firstParameterListOfChain]
  | succ m ih =>
      intro hm
      have hm_prev : m ≤ D.length + 1 := by omega
      have hm_lt : m < D.length + 1 := by omega
      have hhead :
          D.firstParameterListOfChain (m + 1) =
            D.parameterAt ⟨m, hm_lt⟩ ::
              D.firstParameterListOfChain m := by
        simp [firstParameterListOfChain, hm_lt]
      have htail :
          (List.ofFn fun i : Fin m =>
              D.parameterAt ⟨i, by omega⟩) ++
            [D.parameterAt ⟨m, hm_lt⟩] =
            (List.ofFn fun i : Fin (m + 1) =>
              D.parameterAt ⟨i, by omega⟩) := by
        rw [List.ofFn_succ']
        simp [List.concat_eq_append]
      rw [hhead]
      exact
        (List.Perm.cons _ (ih hm_prev)).trans
          ((List.perm_append_singleton
            (D.parameterAt ⟨m, hm_lt⟩)
            (List.ofFn fun i : Fin m =>
              D.parameterAt ⟨i, by omega⟩)).symm.trans
            (by rw [htail]))

/--
%%handwave
name:
  The complete recursive parameter list is a permutation of all parameters
statement:
  Recursively listing all sampled parameters of a continuation chain gives a
  permutation of its full ordered parameter list.
proof:
  Specialize the prefix-permutation result to the total vertex count.
-/
theorem firstParameterListOfChain_all_perm_parameterList
    (D : S.PathContinuationChain x₀ i₀ p) :
    List.Perm (D.firstParameterListOfChain (D.length + 1))
      D.parameterList := by
  simpa [parameterList] using
    D.firstParameterListOfChain_perm_prefix (D.length + 1) le_rfl

/--
%%handwave
name:
  Parameter list after repeatedly inserting an initial vertex prefix
statement:
  After splitting a chain at the first \(m\) sampled parameters of another
  chain, the resulting parameter list is a permutation of that recursive
  \(m\)-parameter list followed by the original list.
proof:
  Induct on \(m\).  Each new split prepends its inserted parameter up to
  permutation, and the induction hypothesis identifies the previous list.
-/
theorem splitFirstVerticesOfChain_parameterList_perm_of_le
    (C D : S.PathContinuationChain x₀ i₀ p) :
    ∀ m : ℕ, m ≤ D.length + 1 →
      List.Perm (C.splitFirstVerticesOfChain D m).parameterList
        (D.firstParameterListOfChain m ++ C.parameterList) := by
  intro m
  induction m with
  | zero =>
      intro _hm
      simp [splitFirstVerticesOfChain, firstParameterListOfChain]
  | succ m ih =>
      intro hm
      have hm_prev : m ≤ D.length + 1 := by omega
      have hm_lt : m < D.length + 1 := by omega
      let R := C.splitFirstVerticesOfChain D m
      have hsplit :
          List.Perm
            (R.splitAtParameterChain (D.parameterAt ⟨m, hm_lt⟩)).parameterList
            (D.parameterAt ⟨m, hm_lt⟩ :: R.parameterList) :=
        R.splitAtParameterChain_parameterList_perm
          (D.parameterAt ⟨m, hm_lt⟩)
      have hih :
          List.Perm R.parameterList
            (D.firstParameterListOfChain m ++ C.parameterList) :=
        ih hm_prev
      simpa [splitFirstVerticesOfChain, firstParameterListOfChain, hm_lt,
        R, List.cons_append] using
        hsplit.trans (List.Perm.cons _ hih)

/--
%%handwave
name:
  Parameter list after inserting every vertex of another chain
statement:
  Let \(C\) and \(D\) be continuation chains along the same path, with
  parameter lists \(T_C=(t_0,\ldots,t_m)\) and
  \(T_D=(s_0,\ldots,s_n)\). After successively splitting \(C\) at every
  \(s_j\), the resulting parameter list is a permutation of
  \(T_D\mathbin{+\!+}T_C\).
proof:
  Induction over the vertices of \(D\) shows that each split inserts exactly
  one new parameter at the head of the recursively accumulated list. The
  recursively listed vertices are a permutation of \(T_D\); appending \(T_C\)
  preserves this permutation.
-/
theorem splitAllVerticesOfChain_parameterList_perm
    (C D : S.PathContinuationChain x₀ i₀ p) :
    List.Perm (C.splitAllVerticesOfChain D).parameterList
      (D.parameterList ++ C.parameterList) := by
  have hsplit :
      List.Perm (C.splitAllVerticesOfChain D).parameterList
        (D.firstParameterListOfChain (D.length + 1) ++ C.parameterList) := by
    simpa [splitAllVerticesOfChain] using
      C.splitFirstVerticesOfChain_parameterList_perm_of_le D
        (D.length + 1) le_rfl
  exact hsplit.trans
    (List.Perm.append_right C.parameterList
      D.firstParameterListOfChain_all_perm_parameterList)

/--
%%handwave
name:
  Left parameter at the terminal-extension midpoint
statement:
  The last old vertex of a terminal path extension occurs at the compressed
  parameter \(1/2\).
proof:
  The old terminal parameter is \(1\), whose first-half image is \(1/2\).
-/
@[simp]
theorem terminalExtensionParameterAt_final_left
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionParameterAt
        ((Fin.last C.length : Fin (C.length + 1)).castSucc) =
      unitInterval.firstHalf 1 := by
  simp [C.parameterAt_last]

/--
%%handwave
name:
  Left branch at the terminal-extension midpoint
statement:
  The last old vertex before the appended path carries the original terminal
  branch.
proof:
  Old branch assignments are retained.
-/
@[simp]
theorem terminalExtensionBranchAt_final_left
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionBranchAt
        ((Fin.last C.length : Fin (C.length + 1)).castSucc) =
      C.terminalBranch := by
  simp [terminalBranch]

/--
%%handwave
name:
  Left transition product at the terminal-extension midpoint
statement:
  The last old vertex before the appended path has the original terminal
  transition product.
proof:
  Old accumulated products are retained.
-/
@[simp]
theorem terminalExtensionTransitionProductAt_final_left
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionTransitionProductAt
        ((Fin.last C.length : Fin (C.length + 1)).castSucc) =
      C.terminalTransition := by
  simp [terminalTransition]

/--
%%handwave
name:
  Right parameter of the appended terminal path
statement:
  The endpoint on the right of the appended terminal segment has parameter
  \(1\).
proof:
  This vertex is the new final index.
-/
@[simp]
theorem terminalExtensionParameterAt_final_right
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionParameterAt
        ((Fin.last C.length : Fin (C.length + 1)).succ) = 1 := by
  rw [fin_last_succ_eq_last]
  exact C.terminalExtensionParameterAt_last

/--
%%handwave
name:
  Right branch of the appended terminal path
statement:
  The endpoint on the right of the appended segment uses the original
  terminal branch.
proof:
  The newly appended path remains inside that branch.
-/
@[simp]
theorem terminalExtensionBranchAt_final_right
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionBranchAt
        ((Fin.last C.length : Fin (C.length + 1)).succ) =
      C.terminalBranch := by
  rw [fin_last_succ_eq_last]
  exact C.terminalExtensionBranchAt_last

/--
%%handwave
name:
  Right transition product of the appended terminal path
statement:
  The endpoint on the right of the appended segment has the original terminal
  accumulated transition.
proof:
  No branch handoff occurs along the appended path.
-/
@[simp]
theorem terminalExtensionTransitionProductAt_final_right
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalExtensionTransitionProductAt
        ((Fin.last C.length : Fin (C.length + 1)).succ) =
      C.terminalTransition := by
  rw [fin_last_succ_eq_last]
  exact C.terminalExtensionTransitionProductAt_last

/--
%%handwave
name:
  Monotonicity of terminal-extension parameters
statement:
  Consecutive parameters in the subdivision obtained by appending a path in
  the terminal branch are nondecreasing.
proof:
  Old segments inherit monotonicity after first-half compression.  The last
  compressed parameter is \(1/2\), which is at most the new endpoint \(1\).
-/
theorem terminalExtensionParameterAt_mono
    (C : S.PathContinuationChain x₀ i₀ p) :
    ∀ k : Fin (C.length + 1),
      (C.terminalExtensionParameterAt k.castSucc : ℝ) ≤
        (C.terminalExtensionParameterAt k.succ : ℝ) := by
  intro k
  by_cases hk : (k : ℕ) < C.length
  · let k₀ : Fin C.length := ⟨k, hk⟩
    have hleft :
        k.castSucc = (k₀.castSucc : Fin (C.length + 1)).castSucc := by
      ext
      rfl
    have hright : k.succ = (k₀.succ : Fin (C.length + 1)).castSucc := by
      ext
      rfl
    rw [hleft, hright, C.terminalExtensionParameterAt_castSucc k₀.castSucc,
      C.terminalExtensionParameterAt_castSucc k₀.succ]
    change ((C.parameterAt k₀.castSucc : ℝ) / 2) ≤
      ((C.parameterAt k₀.succ : ℝ) / 2)
    nlinarith [C.parameterAt_mono k₀]
  · have hk_last : k = Fin.last C.length := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
        (Nat.le_of_not_gt hk)
    subst k
    rw [C.terminalExtensionParameterAt_final_left,
      C.terminalExtensionParameterAt_final_right]
    norm_num

noncomputable def terminalExtensionTransitionAt
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈ S.domain C.terminalBranch) :
    ∀ k : Fin (C.length + 1),
      S.LocalTransition
        (C.terminalExtensionBranchAt k.castSucc)
        (C.terminalExtensionBranchAt k.succ)
        ((p.trans ρ) (C.terminalExtensionParameterAt k.succ)) := by
  intro k
  by_cases hk : (k : ℕ) < C.length
  · let k₀ : Fin C.length := ⟨k, hk⟩
    have hleft :
        k.castSucc = (k₀.castSucc : Fin (C.length + 1)).castSucc := by
      ext
      rfl
    have hright : k.succ = (k₀.succ : Fin (C.length + 1)).castSucc := by
      ext
      rfl
    have hpath :
        (p.trans ρ) (C.terminalExtensionParameterAt k.succ) =
          p (C.parameterAt k₀.succ) := by
      rw [hright, C.terminalExtensionParameterAt_castSucc]
      exact path_trans_firstHalf_apply p ρ (C.parameterAt k₀.succ)
    exact
      (C.transitionAt k₀).congr
        (by rw [hleft]; simp)
        (by
          rw [hright]
          exact (C.terminalExtensionBranchAt_castSucc k₀.succ).symm)
        hpath.symm
  · have hk_last : k = Fin.last C.length := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
        (Nat.le_of_not_gt hk)
    subst k
    have hy :
        (p.trans ρ)
            (C.terminalExtensionParameterAt
              ((Fin.last C.length : Fin (C.length + 1)).succ)) ∈
          S.domain C.terminalBranch := by
      simpa [C.terminalExtensionParameterAt_final_right, ρ.target] using hρ 1
    exact
      (LocalTransition.refl (S := S) C.terminalBranch hy).congr
        (by rw [C.terminalExtensionBranchAt_final_left])
        (by rw [C.terminalExtensionBranchAt_final_right])
        rfl

/--
%%handwave
name:
  Exact terminal-branch append
statement:
  If a path starts at the endpoint of a finite continuation chain and stays in
  the terminal branch domain, then it can be appended to the chain without
  changing the terminal branch expression.
proof:
  Compress the old subdivision into the first half of the interval and add one
  final segment on the second half.  The old handoff transitions are reused on
  the compressed part, and the final handoff is the identity transition in the
  terminal branch.
-/
noncomputable def terminalExtensionAlongChain
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈ S.domain C.terminalBranch) :
    S.PathContinuationChain x₀ i₀ (p.trans ρ) where
  length := C.length + 1
  parameterAt := C.terminalExtensionParameterAt
  parameterAt_zero := C.terminalExtensionParameterAt_zero
  parameterAt_last := C.terminalExtensionParameterAt_last
  parameterAt_mono := C.terminalExtensionParameterAt_mono
  branchAt := C.terminalExtensionBranchAt
  initialTransition := by
    exact C.initialTransition.congr rfl (by simp) rfl
  transitionProductAt := C.terminalExtensionTransitionProductAt
  transitionProductAt_zero := by
    simp [C.transitionProductAt_zero]
  transitionAt := C.terminalExtensionTransitionAt ρ hρ
  transitionProductAt_succ_eq := by
    intro k
    by_cases hk : (k : ℕ) < C.length
    · let k₀ : Fin C.length := ⟨k, hk⟩
      have hleft :
          k.castSucc = (k₀.castSucc : Fin (C.length + 1)).castSucc := by
        ext
        rfl
      have hright : k.succ = (k₀.succ : Fin (C.length + 1)).castSucc := by
        ext
        rfl
      have hprod_left :
          C.terminalExtensionTransitionProductAt k.castSucc =
            C.transitionProductAt k₀.castSucc := by
        rw [hleft]
        simp
      have hprod_right :
          C.terminalExtensionTransitionProductAt k.succ =
            C.transitionProductAt k₀.succ := by
        rw [hright]
        exact C.terminalExtensionTransitionProductAt_castSucc k₀.succ
      have hpath :
          (p.trans ρ) (C.terminalExtensionParameterAt k.succ) =
            p (C.parameterAt k₀.succ) := by
        rw [hright, C.terminalExtensionParameterAt_castSucc]
        exact path_trans_firstHalf_apply p ρ (C.parameterAt k₀.succ)
      have htrans :
          (C.terminalExtensionTransitionAt ρ hρ k).transition =
            (C.transitionAt k₀).transition := by
        simp [terminalExtensionTransitionAt, hk, k₀]
      rw [hprod_right, hprod_left, htrans, C.transitionProductAt_succ_eq k₀]
    · have hk_last : k = Fin.last C.length := by
        ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
          (Nat.le_of_not_gt hk)
      subst k
      have htrans :
          (C.terminalExtensionTransitionAt ρ hρ (Fin.last C.length)).transition =
            1 := by
        simp [terminalExtensionTransitionAt, LocalTransition.refl]
      rw [C.terminalExtensionTransitionProductAt_final_left,
        C.terminalExtensionTransitionProductAt_final_right, htrans]
      simp
  sample_mem_domain := by
    intro i
    by_cases hi : (i : ℕ) < C.length + 1
    · let j : Fin (C.length + 1) := ⟨i, hi⟩
      have hij : i = j.castSucc := by
        ext
        rfl
      rw [hij, C.terminalExtensionParameterAt_castSucc,
        C.terminalExtensionBranchAt_castSucc]
      rw [path_trans_firstHalf_apply]
      exact C.sample_mem_domain j
    · have hi_last : i = Fin.last (C.length + 1) := by
        ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ i.isLt)
          (Nat.le_of_not_gt hi)
      rw [hi_last]
      simpa [C.terminalExtensionParameterAt_last,
        C.terminalExtensionBranchAt_last, ρ.target] using hρ 1
  path_segment_mem_domain := by
    intro k t ht_left ht_right
    by_cases hk : (k : ℕ) < C.length
    · let k₀ : Fin C.length := ⟨k, hk⟩
      have hleft_index :
          k.castSucc = (k₀.castSucc : Fin (C.length + 1)).castSucc := by
        ext
        rfl
      have hright_index : k.succ = (k₀.succ : Fin (C.length + 1)).castSucc := by
        ext
        rfl
      rw [hleft_index, C.terminalExtensionParameterAt_castSucc k₀.castSucc] at ht_left
      rw [hright_index, C.terminalExtensionParameterAt_castSucc k₀.succ] at ht_right
      have ht_half : (t : ℝ) ≤ 1 / 2 :=
        le_trans ht_right (unitInterval.firstHalf_le_half (C.parameterAt k₀.succ))
      have h_lower :
          (C.parameterAt k₀.castSucc : ℝ) ≤
            (unitInterval.doubleOfLeHalf t ht_half : ℝ) := by
        change (C.parameterAt k₀.castSucc : ℝ) ≤ 2 * (t : ℝ)
        change ((C.parameterAt k₀.castSucc : ℝ) / 2) ≤ (t : ℝ) at ht_left
        nlinarith
      have h_upper :
          (unitInterval.doubleOfLeHalf t ht_half : ℝ) ≤
            (C.parameterAt k₀.succ : ℝ) := by
        change 2 * (t : ℝ) ≤ (C.parameterAt k₀.succ : ℝ)
        change (t : ℝ) ≤ ((C.parameterAt k₀.succ : ℝ) / 2) at ht_right
        nlinarith
      have hbranch :
          C.terminalExtensionBranchAt k.castSucc = C.branchAt k₀.castSucc := by
        rw [hleft_index]
        simp
      rw [path_trans_apply_of_le_half p ρ t ht_half, hbranch]
      exact C.path_segment_mem_domain k₀
        (unitInterval.doubleOfLeHalf t ht_half) h_lower h_upper
    · have hk_last : k = Fin.last C.length := by
        ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
          (Nat.le_of_not_gt hk)
      subst k
      rw [C.terminalExtensionParameterAt_final_left] at ht_left
      have ht_half : (1 / 2 : ℝ) ≤ t := by
        simpa using ht_left
      rw [path_trans_apply_of_half_le p ρ t ht_half]
      rw [C.terminalExtensionBranchAt_final_left]
      exact hρ (unitInterval.doubleSubOneOfHalfLe t ht_half)
  terminal_endpoint_mem_domain := by
    simpa [terminalExtensionBranchAt, terminalBranch, ρ.target] using hρ 1

/--
%%handwave
name:
  Exact terminal-branch append preserves the terminal branch
statement:
  If a path \(\rho\) begins at the endpoint of a continuation chain \(C\) and
  stays in the domain of its terminal branch, then the chain obtained by
  appending \(\rho\) has the same terminal branch as \(C\).
proof:
  In this extension the appended segment is assigned the existing terminal
  branch, so evaluation of the final branch index gives that branch directly.
-/
@[simp]
theorem terminalExtensionAlongChain_terminalBranch
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈ S.domain C.terminalBranch) :
    (C.terminalExtensionAlongChain ρ hρ).terminalBranch =
      C.terminalBranch := by
  simp [terminalExtensionAlongChain, terminalBranch]

/--
%%handwave
name:
  Exact terminal-branch append preserves the terminal transition
statement:
  If a path \(\rho\) begins at the endpoint of a continuation chain \(C\) and
  stays in the domain of its terminal branch, then appending \(\rho\) leaves
  the accumulated terminal transition unchanged.
proof:
  The appended segment uses the identity handoff, so the final transition
  product reduces to the original terminal transition.
-/
@[simp]
theorem terminalExtensionAlongChain_terminalTransition
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈ S.domain C.terminalBranch) :
    (C.terminalExtensionAlongChain ρ hρ).terminalTransition =
      C.terminalTransition := by
  simp [terminalExtensionAlongChain, terminalTransition]

/--
%%handwave
name:
  Same-branch extensions have the same terminal germ
statement:
  If two paths start at the endpoint of a continuation chain, end at the same
  point, and both stay inside the current terminal branch domain, then appending
  either path gives locally agreeing terminal germs.
proof:
  Exact terminal-branch append preserves both the terminal branch and the
  accumulated terminal transition, so the two resulting local terminal
  expressions are identical on the terminal branch domain.
-/
theorem terminalExtensionsAlong_same_terminalGerms_agree
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} (ρ σ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈ S.domain C.terminalBranch)
    (hσ : ∀ t : unitInterval, σ t ∈ S.domain C.terminalBranch) :
    (C.terminalExtensionAlongChain ρ hρ).toTerminalGerm.LocallyAgreesWith
      (C.terminalExtensionAlongChain σ hσ).toTerminalGerm := by
  refine
    ⟨S.domain C.terminalBranch, S.domain_open C.terminalBranch,
      ?_, ?_, ?_⟩
  · simpa [ρ.target] using hρ 1
  · intro z hz
    constructor
    · simpa [PathContinuationChain.toTerminalGerm] using hz
    · simpa [PathContinuationChain.toTerminalGerm] using hz
  · intro z _hz
    simp [PathContinuationGerm.localMap, PathContinuationChain.toTerminalGerm]

/--
%%handwave
name:
  Equal terminal branch data gives local agreement
statement:
  Let \(C\) and \(D\) be continuation chains ending at the same point \(x\).
  If their terminal branches satisfy \(\beta_C=\beta_D\) and their accumulated
  terminal transitions satisfy \(g_C=g_D\), then their terminal germs locally
  agree at \(x\).
proof:
  Use the common terminal branch domain \(D_{\beta_C}=D_{\beta_D}\) as the
  endpoint neighborhood. The two represented maps are respectively
  \(g_C\cdot f_{\beta_C}\) and \(g_D\cdot f_{\beta_D}\), hence are equal there.
-/
theorem terminalGerms_agree_of_terminalBranch_eq_terminalTransition_eq
    {x₀ : X} {i₀ : ι} {x : X}
    {p q : Path x₀ x}
    (C : S.PathContinuationChain x₀ i₀ p)
    (D : S.PathContinuationChain x₀ i₀ q)
    (hBranch : C.terminalBranch = D.terminalBranch)
    (hTransition : C.terminalTransition = D.terminalTransition) :
    C.toTerminalGerm.LocallyAgreesWith D.toTerminalGerm := by
  refine
    ⟨S.domain C.terminalBranch, S.domain_open C.terminalBranch,
      C.endpoint_mem_terminalBranch, ?_, ?_⟩
  · intro z hz
    constructor
    · simpa [PathContinuationChain.toTerminalGerm] using hz
    · simpa [PathContinuationChain.toTerminalGerm, ← hBranch] using hz
  · intro z _hz
    simp [PathContinuationGerm.localMap, PathContinuationChain.toTerminalGerm,
      hBranch, hTransition]

/--
Subdivision parameters for appending an already-subdivided suffix chain.

The prefix chain is compressed into the first half of the unit interval, and
the suffix chain is compressed into the second half.  The point \(1/2\) is
duplicated: once as the terminal vertex of the prefix and once as the initial
vertex of the suffix.
-/
noncomputable def appendSuffixParameterAt
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    Fin (C.length + D.length + 2) → unitInterval :=
  fun i =>
    if hi : (i : ℕ) < C.length + 1 then
      unitInterval.firstHalf (C.parameterAt ⟨i, hi⟩)
    else
      unitInterval.secondHalf
        (D.parameterAt ⟨(i : ℕ) - (C.length + 1), by omega⟩)

/-- Branches for appending an already-subdivided suffix chain. -/
noncomputable def appendSuffixBranchAt
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    Fin (C.length + D.length + 2) → ι :=
  fun i =>
    if hi : (i : ℕ) < C.length + 1 then
      C.branchAt ⟨i, hi⟩
    else
      D.branchAt ⟨(i : ℕ) - (C.length + 1), by omega⟩

/-- Accumulated transitions for appending an already-subdivided suffix chain. -/
noncomputable def appendSuffixTransitionProductAt
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    Fin (C.length + D.length + 2) → G :=
  fun i =>
    if hi : (i : ℕ) < C.length + 1 then
      C.transitionProductAt ⟨i, hi⟩
    else
      C.terminalTransition *
        D.transitionProductAt ⟨(i : ℕ) - (C.length + 1), by omega⟩

/--
%%handwave
name:
  Prefix parameters in an appended suffix chain
statement:
  At a prefix vertex, the concatenated subdivision parameter is the original
  prefix parameter compressed into the first half of the unit interval.
proof:
  Prefix indices satisfy the left branch of the appended-subdivision
  definition.
-/
@[simp]
theorem appendSuffixParameterAt_left
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix)
    (i : Fin (C.length + 1)) :
    C.appendSuffixParameterAt D
        (⟨i, by omega⟩ : Fin (C.length + D.length + 2)) =
      unitInterval.firstHalf (C.parameterAt i) := by
  simp [appendSuffixParameterAt, i.isLt]

/--
%%handwave
name:
  Prefix branches in an appended suffix chain
statement:
  At every prefix vertex, appending a suffix retains the branch chosen by the
  prefix chain.
proof:
  Evaluate the branch assignment in its prefix-index case.
-/
@[simp]
theorem appendSuffixBranchAt_left
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix)
    (i : Fin (C.length + 1)) :
    C.appendSuffixBranchAt D
        (⟨i, by omega⟩ : Fin (C.length + D.length + 2)) =
      C.branchAt i := by
  simp [appendSuffixBranchAt, i.isLt]

/--
%%handwave
name:
  Prefix transition products in an appended suffix chain
statement:
  At every prefix vertex, the concatenated chain has the prefix chain's
  accumulated transition product.
proof:
  This is the prefix-index clause of the product assignment.
-/
@[simp]
theorem appendSuffixTransitionProductAt_left
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix)
    (i : Fin (C.length + 1)) :
    C.appendSuffixTransitionProductAt D
        (⟨i, by omega⟩ : Fin (C.length + D.length + 2)) =
      C.transitionProductAt i := by
  simp [appendSuffixTransitionProductAt, i.isLt]

/--
%%handwave
name:
  Suffix parameters in an appended suffix chain
statement:
  At a suffix vertex, the concatenated subdivision parameter is the suffix
  parameter compressed into the second half of the unit interval.
proof:
  Subtracting the prefix vertex count recovers the suffix index, so the right
  clause of the definition applies.
-/
@[simp]
theorem appendSuffixParameterAt_right
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix)
    (j : Fin (D.length + 1)) :
    C.appendSuffixParameterAt D
        (⟨C.length + 1 + (j : ℕ), by omega⟩ :
          Fin (C.length + D.length + 2)) =
      unitInterval.secondHalf (D.parameterAt j) := by
  have hnot : ¬ C.length + 1 + (j : ℕ) < C.length + 1 := by
    omega
  have hsub : C.length + 1 + (j : ℕ) - (C.length + 1) = (j : ℕ) := by
    omega
  simp [appendSuffixParameterAt, hnot, hsub]

/--
%%handwave
name:
  Suffix branches in an appended suffix chain
statement:
  At every suffix vertex of the concatenated chain, the assigned branch is
  the corresponding suffix-chain branch.
proof:
  The shifted index lies in the suffix clause of the assignment.
-/
@[simp]
theorem appendSuffixBranchAt_right
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix)
    (j : Fin (D.length + 1)) :
    C.appendSuffixBranchAt D
        (⟨C.length + 1 + (j : ℕ), by omega⟩ :
          Fin (C.length + D.length + 2)) =
      D.branchAt j := by
  have hnot : ¬ C.length + 1 + (j : ℕ) < C.length + 1 := by
    omega
  have hsub : C.length + 1 + (j : ℕ) - (C.length + 1) = (j : ℕ) := by
    omega
  simp [appendSuffixBranchAt, hnot, hsub]

/--
%%handwave
name:
  Suffix transition products in an appended suffix chain
statement:
  If the prefix ends with accumulated transition \(g\), then at a suffix
  vertex with suffix product \(h\), the concatenated product is \(gh\).
proof:
  This is the suffix clause of the concatenated product assignment after
  recovering the shifted suffix index.
-/
@[simp]
theorem appendSuffixTransitionProductAt_right
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix)
    (j : Fin (D.length + 1)) :
    C.appendSuffixTransitionProductAt D
        (⟨C.length + 1 + (j : ℕ), by omega⟩ :
          Fin (C.length + D.length + 2)) =
      C.terminalTransition * D.transitionProductAt j := by
  have hnot : ¬ C.length + 1 + (j : ℕ) < C.length + 1 := by
    omega
  have hsub : C.length + 1 + (j : ℕ) - (C.length + 1) = (j : ℕ) := by
    omega
  simp [appendSuffixTransitionProductAt, hnot, hsub]

/--
%%handwave
name:
  Initial parameter of an appended suffix chain
statement:
  The concatenated subdivision begins at parameter \(0\).
proof:
  The initial prefix parameter is zero, and first-half reparametrization fixes
  zero.
-/
@[simp]
theorem appendSuffixParameterAt_zero
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    C.appendSuffixParameterAt D 0 = 0 := by
  simpa [C.parameterAt_zero] using
    C.appendSuffixParameterAt_left D (0 : Fin (C.length + 1))

/--
%%handwave
name:
  Initial branch of an appended suffix chain
statement:
  The concatenated chain begins with the initial branch of the prefix chain.
proof:
  The zero vertex belongs to the prefix part.
-/
@[simp]
theorem appendSuffixBranchAt_zero
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    C.appendSuffixBranchAt D 0 = C.branchAt 0 := by
  simpa using C.appendSuffixBranchAt_left D (0 : Fin (C.length + 1))

/--
%%handwave
name:
  Initial transition product of an appended suffix chain
statement:
  The concatenated chain begins with the prefix chain's initial accumulated
  transition product.
proof:
  The initial vertex is a prefix vertex.
-/
@[simp]
theorem appendSuffixTransitionProductAt_zero
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    C.appendSuffixTransitionProductAt D 0 = C.transitionProductAt 0 := by
  simpa using
    C.appendSuffixTransitionProductAt_left D (0 : Fin (C.length + 1))

/--
%%handwave
name:
  Final parameter of an appended suffix chain
statement:
  The concatenated subdivision ends at parameter \(1\).
proof:
  The last suffix parameter is one, and second-half reparametrization sends it
  to one.
-/
@[simp]
theorem appendSuffixParameterAt_last
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    C.appendSuffixParameterAt D (Fin.last (C.length + D.length + 1)) = 1 := by
  have hidx :
      (Fin.last (C.length + D.length + 1) : Fin (C.length + D.length + 2)) =
        (⟨C.length + 1 + D.length, by omega⟩ :
          Fin (C.length + D.length + 2)) := by
    ext
    simp
    omega
  rw [hidx]
  simpa [D.parameterAt_last] using
    C.appendSuffixParameterAt_right D (Fin.last D.length)

/--
%%handwave
name:
  Final branch of an appended suffix chain
statement:
  The terminal branch of the concatenated subdivision is the terminal branch
  of the suffix chain.
proof:
  The last combined vertex corresponds to the last suffix vertex.
-/
@[simp]
theorem appendSuffixBranchAt_last
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    C.appendSuffixBranchAt D (Fin.last (C.length + D.length + 1)) =
      D.terminalBranch := by
  have hidx :
      (Fin.last (C.length + D.length + 1) : Fin (C.length + D.length + 2)) =
        (⟨C.length + 1 + D.length, by omega⟩ :
          Fin (C.length + D.length + 2)) := by
    ext
    simp
    omega
  rw [hidx]
  simpa [terminalBranch] using
    C.appendSuffixBranchAt_right D (Fin.last D.length)

/--
%%handwave
name:
  Final transition product of an appended suffix chain
statement:
  The terminal accumulated transition of the concatenation is the product of
  the prefix and suffix terminal transitions.
proof:
  At the final suffix vertex, the general suffix-product formula gives the
  product of the two terminal values.
-/
@[simp]
theorem appendSuffixTransitionProductAt_last
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    C.appendSuffixTransitionProductAt D
        (Fin.last (C.length + D.length + 1)) =
      C.terminalTransition * D.terminalTransition := by
  have hidx :
      (Fin.last (C.length + D.length + 1) : Fin (C.length + D.length + 2)) =
        (⟨C.length + 1 + D.length, by omega⟩ :
          Fin (C.length + D.length + 2)) := by
    ext
    simp
    omega
  rw [hidx]
  simpa [terminalTransition] using
    C.appendSuffixTransitionProductAt_right D (Fin.last D.length)

/--
%%handwave
name:
  Monotonicity of appended suffix parameters
statement:
  Consecutive parameters in the concatenated subdivision are nondecreasing.
proof:
  On prefix and suffix segments this follows from the corresponding chain's
  monotonicity after affine rescaling.  Across the duplicated midpoint, the
  left value is at most \(1/2\) and the right value is exactly \(1/2\).
-/
theorem appendSuffixParameterAt_mono
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    ∀ k : Fin (C.length + D.length + 1),
      (C.appendSuffixParameterAt D k.castSucc : ℝ) ≤
        (C.appendSuffixParameterAt D k.succ : ℝ) := by
  intro k
  by_cases hk_left : (k : ℕ) < C.length
  · let kp : Fin C.length := ⟨k, hk_left⟩
    have hleft :
        (k.castSucc : Fin (C.length + D.length + 2)) =
          (⟨(kp.castSucc : Fin (C.length + 1)), by omega⟩ :
            Fin (C.length + D.length + 2)) := by
      ext
      rfl
    have hright :
        (k.succ : Fin (C.length + D.length + 2)) =
          (⟨(kp.succ : Fin (C.length + 1)), by omega⟩ :
            Fin (C.length + D.length + 2)) := by
      ext
      rfl
    rw [hleft, hright, C.appendSuffixParameterAt_left D kp.castSucc,
      C.appendSuffixParameterAt_left D kp.succ]
    change ((C.parameterAt kp.castSucc : ℝ) / 2) ≤
      ((C.parameterAt kp.succ : ℝ) / 2)
    nlinarith [C.parameterAt_mono kp]
  · by_cases hk_bridge : (k : ℕ) = C.length
    · have hleft :
          (k.castSucc : Fin (C.length + D.length + 2)) =
            (⟨(Fin.last C.length : Fin (C.length + 1)), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        simp [hk_bridge]
      have hright :
          (k.succ : Fin (C.length + D.length + 2)) =
            (⟨C.length + 1 + (0 : ℕ), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        simp [hk_bridge]
      rw [hleft, hright]
      simp [appendSuffixParameterAt, D.parameterAt_zero]
      have hle :
          (C.parameterAt (⟨C.length, by omega⟩ : Fin (C.length + 1)) : ℝ) ≤
            1 := unitInterval.le_one _
      nlinarith
    · let j : Fin D.length := ⟨(k : ℕ) - (C.length + 1), by omega⟩
      have hleft :
          (k.castSucc : Fin (C.length + D.length + 2)) =
            (⟨C.length + 1 + (j.castSucc : ℕ), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        change (k : ℕ) = C.length + 1 + ((k : ℕ) - (C.length + 1))
        omega
      have hright :
          (k.succ : Fin (C.length + D.length + 2)) =
            (⟨C.length + 1 + (j.succ : ℕ), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        change (k : ℕ) + 1 =
          C.length + 1 + (((k : ℕ) - (C.length + 1)) + 1)
        omega
      rw [hleft, hright, C.appendSuffixParameterAt_right D j.castSucc,
        C.appendSuffixParameterAt_right D j.succ]
      change (1 + (D.parameterAt j.castSucc : ℝ)) / 2 ≤
        (1 + (D.parameterAt j.succ : ℝ)) / 2
      nlinarith [D.parameterAt_mono j]

/--
%%handwave
name:
  Vertex-domain condition for an appended suffix chain
statement:
  Every subdivision vertex of a concatenated prefix and suffix path belongs
  to the domain of its assigned branch.
proof:
  Prefix vertices reduce through first-half reparametrization to the prefix
  chain's vertex condition; suffix vertices reduce through second-half
  reparametrization to the suffix chain's condition.
-/
theorem appendSuffix_sample_mem_domain
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    ∀ i : Fin (C.length + D.length + 2),
      (p.trans suffix) (C.appendSuffixParameterAt D i) ∈
        S.domain (C.appendSuffixBranchAt D i) := by
  intro i
  by_cases hi : (i : ℕ) < C.length + 1
  · let j : Fin (C.length + 1) := ⟨i, hi⟩
    have hij :
        i =
          (⟨(j : ℕ), by omega⟩ :
            Fin (C.length + D.length + 2)) := by
      ext
      rfl
    rw [hij, C.appendSuffixParameterAt_left D j,
      C.appendSuffixBranchAt_left D j]
    rw [path_trans_firstHalf_apply]
    exact C.sample_mem_domain j
  · let j : Fin (D.length + 1) :=
      ⟨(i : ℕ) - (C.length + 1), by omega⟩
    have hij :
        i =
          (⟨C.length + 1 + (j : ℕ), by omega⟩ :
            Fin (C.length + D.length + 2)) := by
      ext
      change (i : ℕ) = C.length + 1 + ((i : ℕ) - (C.length + 1))
      omega
    rw [hij, C.appendSuffixParameterAt_right D j,
      C.appendSuffixBranchAt_right D j]
    rw [path_trans_secondHalf_apply]
    exact D.sample_mem_domain j

/--
%%handwave
name:
  Segment-domain condition for an appended suffix chain
statement:
  Each segment of the concatenated subdivision remains in the branch domain
  assigned at its left endpoint.
proof:
  Segments strictly inside either half reduce by affine reparametrization to
  the corresponding prefix or suffix segment.  The bridge segment is
  degenerate at the common endpoint, which lies in the shared terminal branch
  domain.
-/
theorem appendSuffix_path_segment_mem_domain
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    ∀ k : Fin (C.length + D.length + 1), ∀ t : unitInterval,
      (C.appendSuffixParameterAt D k.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (C.appendSuffixParameterAt D k.succ : ℝ) →
      (p.trans suffix) t ∈
        S.domain (C.appendSuffixBranchAt D k.castSucc) := by
  intro k t ht_left ht_right
  by_cases hk_left : (k : ℕ) < C.length
  · let kp : Fin C.length := ⟨k, hk_left⟩
    have hleft :
        (k.castSucc : Fin (C.length + D.length + 2)) =
          (⟨(kp.castSucc : Fin (C.length + 1)), by omega⟩ :
            Fin (C.length + D.length + 2)) := by
      ext
      rfl
    have hright :
        (k.succ : Fin (C.length + D.length + 2)) =
          (⟨(kp.succ : Fin (C.length + 1)), by omega⟩ :
            Fin (C.length + D.length + 2)) := by
      ext
      rfl
    rw [hleft, C.appendSuffixParameterAt_left D kp.castSucc] at ht_left
    rw [hright, C.appendSuffixParameterAt_left D kp.succ] at ht_right
    have ht_half : (t : ℝ) ≤ 1 / 2 :=
      le_trans ht_right (unitInterval.firstHalf_le_half (C.parameterAt kp.succ))
    have h_lower :
        (C.parameterAt kp.castSucc : ℝ) ≤
          (unitInterval.doubleOfLeHalf t ht_half : ℝ) := by
      change (C.parameterAt kp.castSucc : ℝ) ≤ 2 * (t : ℝ)
      change ((C.parameterAt kp.castSucc : ℝ) / 2) ≤ (t : ℝ) at ht_left
      nlinarith
    have h_upper :
        (unitInterval.doubleOfLeHalf t ht_half : ℝ) ≤
          (C.parameterAt kp.succ : ℝ) := by
      change 2 * (t : ℝ) ≤ (C.parameterAt kp.succ : ℝ)
      change (t : ℝ) ≤ ((C.parameterAt kp.succ : ℝ) / 2) at ht_right
      nlinarith
    rw [path_trans_apply_of_le_half p suffix t ht_half]
    have hbranch :
        C.appendSuffixBranchAt D k.castSucc = C.branchAt kp.castSucc := by
      rw [hleft, C.appendSuffixBranchAt_left D kp.castSucc]
    rw [hbranch]
    exact C.path_segment_mem_domain kp
      (unitInterval.doubleOfLeHalf t ht_half) h_lower h_upper
  · by_cases hk_bridge : (k : ℕ) = C.length
    · have hleft :
          (k.castSucc : Fin (C.length + D.length + 2)) =
            (⟨(Fin.last C.length : Fin (C.length + 1)), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        simp [hk_bridge]
      have hright :
          (k.succ : Fin (C.length + D.length + 2)) =
            (⟨C.length + 1 + (0 : ℕ), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        simp [hk_bridge]
      rw [hleft] at ht_left
      rw [hright] at ht_right
      have hleft_param :
          C.appendSuffixParameterAt D
              (⟨(Fin.last C.length : Fin (C.length + 1)), by omega⟩ :
                Fin (C.length + D.length + 2)) =
            unitInterval.firstHalf (C.parameterAt (Fin.last C.length)) := by
        exact C.appendSuffixParameterAt_left D (Fin.last C.length)
      have hright_param :
          C.appendSuffixParameterAt D
              (⟨C.length + 1 + (0 : ℕ), by omega⟩ :
                Fin (C.length + D.length + 2)) =
            unitInterval.secondHalf (D.parameterAt (0 : Fin (D.length + 1))) := by
        exact C.appendSuffixParameterAt_right D (0 : Fin (D.length + 1))
      rw [hleft_param, C.parameterAt_last, unitInterval.firstHalf_one] at ht_left
      rw [hright_param, D.parameterAt_zero, unitInterval.secondHalf_zero] at ht_right
      have hle : (t : ℝ) ≤ 1 / 2 := by simpa using ht_right
      have hge : (1 / 2 : ℝ) ≤ t := by simpa using ht_left
      have ht_double : unitInterval.doubleOfLeHalf t hle = 1 := by
        ext
        have ht_eq : (t : ℝ) = 1 / 2 := le_antisymm hle hge
        simp [unitInterval.coe_doubleOfLeHalf, ht_eq]
      rw [path_trans_apply_of_le_half p suffix t hle]
      have hbranch :
          C.appendSuffixBranchAt D k.castSucc = C.terminalBranch := by
        rw [hleft, C.appendSuffixBranchAt_left D (Fin.last C.length)]
        rfl
      rw [hbranch, ht_double]
      simpa [p.target] using C.endpoint_mem_terminalBranch
    · let j : Fin D.length := ⟨(k : ℕ) - (C.length + 1), by omega⟩
      have hleft :
          (k.castSucc : Fin (C.length + D.length + 2)) =
            (⟨C.length + 1 + (j.castSucc : ℕ), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        change (k : ℕ) = C.length + 1 + ((k : ℕ) - (C.length + 1))
        omega
      have hright :
          (k.succ : Fin (C.length + D.length + 2)) =
            (⟨C.length + 1 + (j.succ : ℕ), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        change (k : ℕ) + 1 =
          C.length + 1 + (((k : ℕ) - (C.length + 1)) + 1)
        omega
      rw [hleft, C.appendSuffixParameterAt_right D j.castSucc] at ht_left
      rw [hright, C.appendSuffixParameterAt_right D j.succ] at ht_right
      have ht_half : (1 / 2 : ℝ) ≤ t :=
        le_trans (unitInterval.half_le_secondHalf (D.parameterAt j.castSucc))
          ht_left
      have h_lower :
          (D.parameterAt j.castSucc : ℝ) ≤
            (unitInterval.doubleSubOneOfHalfLe t ht_half : ℝ) := by
        change (D.parameterAt j.castSucc : ℝ) ≤ 2 * (t : ℝ) - 1
        change (1 + (D.parameterAt j.castSucc : ℝ)) / 2 ≤ (t : ℝ) at ht_left
        nlinarith
      have h_upper :
          (unitInterval.doubleSubOneOfHalfLe t ht_half : ℝ) ≤
            (D.parameterAt j.succ : ℝ) := by
        change 2 * (t : ℝ) - 1 ≤ (D.parameterAt j.succ : ℝ)
        change (t : ℝ) ≤ (1 + (D.parameterAt j.succ : ℝ)) / 2 at ht_right
        nlinarith
      rw [path_trans_apply_of_half_le p suffix t ht_half]
      have hbranch :
          C.appendSuffixBranchAt D k.castSucc = D.branchAt j.castSucc := by
        rw [hleft, C.appendSuffixBranchAt_right D j.castSucc]
      rw [hbranch]
      exact D.path_segment_mem_domain j
        (unitInterval.doubleSubOneOfHalfLe t ht_half) h_lower h_upper

/-- Transition data for appending an already-subdivided suffix chain. -/
noncomputable def appendSuffixTransitionAt
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    ∀ k : Fin (C.length + D.length + 1),
      S.LocalTransition
        (C.appendSuffixBranchAt D k.castSucc)
        (C.appendSuffixBranchAt D k.succ)
        ((p.trans suffix) (C.appendSuffixParameterAt D k.succ)) := by
  intro k
  by_cases hk_left : (k : ℕ) < C.length
  · let kp : Fin C.length := ⟨k, hk_left⟩
    have hleft :
        (k.castSucc : Fin (C.length + D.length + 2)) =
          (⟨(kp.castSucc : Fin (C.length + 1)), by omega⟩ :
            Fin (C.length + D.length + 2)) := by
      ext
      rfl
    have hright :
        (k.succ : Fin (C.length + D.length + 2)) =
          (⟨(kp.succ : Fin (C.length + 1)), by omega⟩ :
            Fin (C.length + D.length + 2)) := by
      ext
      rfl
    have hpath :
        (p.trans suffix) (C.appendSuffixParameterAt D k.succ) =
          p (C.parameterAt kp.succ) := by
      rw [hright, C.appendSuffixParameterAt_left D kp.succ]
      exact path_trans_firstHalf_apply p suffix (C.parameterAt kp.succ)
    exact
      (C.transitionAt kp).congr
        (by rw [hleft, C.appendSuffixBranchAt_left D kp.castSucc])
        (by rw [hright, C.appendSuffixBranchAt_left D kp.succ])
        hpath.symm
  · by_cases hk_bridge : (k : ℕ) = C.length
    · have hleft :
          (k.castSucc : Fin (C.length + D.length + 2)) =
            (⟨(Fin.last C.length : Fin (C.length + 1)), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        simp [hk_bridge]
      have hright :
          (k.succ : Fin (C.length + D.length + 2)) =
            (⟨C.length + 1 + (0 : ℕ), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        simp [hk_bridge]
      have hpath :
          (p.trans suffix) (C.appendSuffixParameterAt D k.succ) = x := by
        have hparam :
            C.appendSuffixParameterAt D k.succ =
              unitInterval.secondHalf (D.parameterAt (0 : Fin (D.length + 1))) := by
          rw [hright]
          exact C.appendSuffixParameterAt_right D (0 : Fin (D.length + 1))
        rw [hparam, D.parameterAt_zero]
        simpa [suffix.source] using
          path_trans_secondHalf_apply p suffix (0 : unitInterval)
      have hbranch_left :
          C.terminalBranch = C.appendSuffixBranchAt D k.castSucc := by
        rw [hleft, C.appendSuffixBranchAt_left D (Fin.last C.length)]
        rfl
      have hbranch_right :
          D.branchAt 0 = C.appendSuffixBranchAt D k.succ := by
        rw [hright]
        exact (C.appendSuffixBranchAt_right D (0 : Fin (D.length + 1))).symm
      exact
        D.initialTransition.congr
          hbranch_left hbranch_right
          hpath.symm
    · let j : Fin D.length := ⟨(k : ℕ) - (C.length + 1), by omega⟩
      have hleft :
          (k.castSucc : Fin (C.length + D.length + 2)) =
            (⟨C.length + 1 + (j.castSucc : ℕ), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        change (k : ℕ) = C.length + 1 + ((k : ℕ) - (C.length + 1))
        omega
      have hright :
          (k.succ : Fin (C.length + D.length + 2)) =
            (⟨C.length + 1 + (j.succ : ℕ), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        change (k : ℕ) + 1 =
          C.length + 1 + (((k : ℕ) - (C.length + 1)) + 1)
        omega
      have hpath :
          (p.trans suffix) (C.appendSuffixParameterAt D k.succ) =
            suffix (D.parameterAt j.succ) := by
        rw [hright, C.appendSuffixParameterAt_right D j.succ]
        exact path_trans_secondHalf_apply p suffix (D.parameterAt j.succ)
      exact
        (D.transitionAt j).congr
          (by rw [hleft, C.appendSuffixBranchAt_right D j.castSucc])
          (by rw [hright, C.appendSuffixBranchAt_right D j.succ])
          hpath.symm

/--
%%handwave
name:
  Exact suffix-chain append
statement:
  A finite continuation chain can be followed by another finite continuation
  chain whose prescribed initial branch is the terminal branch of the first
  chain, producing a continuation chain over the concatenated path.
proof:
  Compress the first chain into the first half of the interval and the suffix
  chain into the second half.  The duplicated midpoint carries the initial
  handoff of the suffix chain.
-/
noncomputable def appendSuffixChain
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    S.PathContinuationChain x₀ i₀ (p.trans suffix) where
  length := C.length + D.length + 1
  parameterAt := C.appendSuffixParameterAt D
  parameterAt_zero := C.appendSuffixParameterAt_zero D
  parameterAt_last := C.appendSuffixParameterAt_last D
  parameterAt_mono := C.appendSuffixParameterAt_mono D
  branchAt := C.appendSuffixBranchAt D
  initialTransition := by
    exact C.initialTransition.congr rfl (by simp) rfl
  transitionProductAt := C.appendSuffixTransitionProductAt D
  transitionProductAt_zero := by
    simp [C.transitionProductAt_zero]
  transitionAt := C.appendSuffixTransitionAt D
  transitionProductAt_succ_eq := by
    intro k
    by_cases hk_left : (k : ℕ) < C.length
    · let kp : Fin C.length := ⟨k, hk_left⟩
      have hleft :
          (k.castSucc : Fin (C.length + D.length + 2)) =
            (⟨(kp.castSucc : Fin (C.length + 1)), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        rfl
      have hright :
          (k.succ : Fin (C.length + D.length + 2)) =
            (⟨(kp.succ : Fin (C.length + 1)), by omega⟩ :
              Fin (C.length + D.length + 2)) := by
        ext
        rfl
      have hprod_left :
          C.appendSuffixTransitionProductAt D k.castSucc =
            C.transitionProductAt kp.castSucc := by
        rw [hleft, C.appendSuffixTransitionProductAt_left D kp.castSucc]
      have hprod_right :
          C.appendSuffixTransitionProductAt D k.succ =
            C.transitionProductAt kp.succ := by
        rw [hright, C.appendSuffixTransitionProductAt_left D kp.succ]
      have htrans :
          (C.appendSuffixTransitionAt D k).transition =
            (C.transitionAt kp).transition := by
        simp [appendSuffixTransitionAt, hk_left, kp]
      rw [hprod_right, hprod_left, htrans, C.transitionProductAt_succ_eq kp]
    · by_cases hk_bridge : (k : ℕ) = C.length
      · have hleft :
            (k.castSucc : Fin (C.length + D.length + 2)) =
              (⟨(Fin.last C.length : Fin (C.length + 1)), by omega⟩ :
                Fin (C.length + D.length + 2)) := by
          ext
          simp [hk_bridge]
        have hright :
            (k.succ : Fin (C.length + D.length + 2)) =
              (⟨C.length + 1 + (0 : ℕ), by omega⟩ :
                Fin (C.length + D.length + 2)) := by
          ext
          simp [hk_bridge]
        have hprod_left :
            C.appendSuffixTransitionProductAt D k.castSucc =
              C.terminalTransition := by
          rw [hleft, C.appendSuffixTransitionProductAt_left D (Fin.last C.length)]
          rfl
        have hprod_right :
            C.appendSuffixTransitionProductAt D k.succ =
              C.terminalTransition * D.transitionProductAt 0 := by
          rw [hright]
          exact
            C.appendSuffixTransitionProductAt_right D
              (0 : Fin (D.length + 1))
        have htrans :
            (C.appendSuffixTransitionAt D k).transition =
              D.initialTransition.transition := by
          simp [appendSuffixTransitionAt, hk_bridge]
        rw [hprod_right, hprod_left, htrans, D.transitionProductAt_zero]
      · let j : Fin D.length := ⟨(k : ℕ) - (C.length + 1), by omega⟩
        have hleft :
            (k.castSucc : Fin (C.length + D.length + 2)) =
              (⟨C.length + 1 + (j.castSucc : ℕ), by omega⟩ :
                Fin (C.length + D.length + 2)) := by
          ext
          change (k : ℕ) = C.length + 1 + ((k : ℕ) - (C.length + 1))
          omega
        have hright :
            (k.succ : Fin (C.length + D.length + 2)) =
              (⟨C.length + 1 + (j.succ : ℕ), by omega⟩ :
                Fin (C.length + D.length + 2)) := by
          ext
          change (k : ℕ) + 1 =
            C.length + 1 + (((k : ℕ) - (C.length + 1)) + 1)
          omega
        have hprod_left :
            C.appendSuffixTransitionProductAt D k.castSucc =
              C.terminalTransition * D.transitionProductAt j.castSucc := by
          rw [hleft, C.appendSuffixTransitionProductAt_right D j.castSucc]
        have hprod_right :
            C.appendSuffixTransitionProductAt D k.succ =
              C.terminalTransition * D.transitionProductAt j.succ := by
          rw [hright, C.appendSuffixTransitionProductAt_right D j.succ]
        have htrans :
            (C.appendSuffixTransitionAt D k).transition =
              (D.transitionAt j).transition := by
          simp [appendSuffixTransitionAt, hk_left, hk_bridge, j]
        rw [hprod_right, hprod_left, htrans, D.transitionProductAt_succ_eq j]
        simp [mul_assoc]
  sample_mem_domain := C.appendSuffix_sample_mem_domain D
  path_segment_mem_domain := C.appendSuffix_path_segment_mem_domain D
  terminal_endpoint_mem_domain := by
    simpa [appendSuffixBranchAt_last, suffix.target] using
      D.terminal_endpoint_mem_domain

/--
%%handwave
name:
  Terminal branch of an appended suffix chain
statement:
  Appending a continuation chain along a suffix path produces a chain whose
  terminal branch is the suffix chain's terminal branch.
proof:
  The last combined vertex is the last suffix vertex.
-/
@[simp]
theorem appendSuffixChain_terminalBranch
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    (C.appendSuffixChain D).terminalBranch = D.terminalBranch := by
  simp [appendSuffixChain, terminalBranch]

/--
%%handwave
name:
  Terminal transition of an appended suffix chain
statement:
  The terminal transition of the concatenated chain is the product of the
  prefix terminal transition and the suffix terminal transition.
proof:
  Apply the final-vertex formula for concatenated transition products.
-/
@[simp]
theorem appendSuffixChain_terminalTransition
    (C : S.PathContinuationChain x₀ i₀ p)
    {y : X} {suffix : Path x y}
    (D : S.PathContinuationChain x C.terminalBranch suffix) :
    (C.appendSuffixChain D).terminalTransition =
      C.terminalTransition * D.terminalTransition := by
  simp [appendSuffixChain, terminalTransition]

/--
%%handwave
name:
  Exact suffix append preserves equal terminal branch data
statement:
  Let \(C,E\) be continuation chains from \(x_0\) to \(x\), and let \(D,F\)
  be continuation chains along the same suffix \(\sigma:x\to y\), initialized
  at the respective terminal branches of \(C,E\). If
  \(g_C=g_E\), \(\beta_D=\beta_F\), and \(g_D=g_F\), then the terminal germs
  of the appended chains \(C*D\) and \(E*F\) locally agree at \(y\).
proof:
  Appending gives terminal branches \(\beta_D,\beta_F\) and terminal transitions \(g_Cg_D,g_Eg_F\), so the hypotheses make both pairs equal; [chains with equal terminal branch and equal terminal transition have locally agreeing terminal germs.](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.terminalGerms_agree_of_terminalBranch_eq_terminalTransition_eq)
-/
theorem appendSuffixChain_terminalGerms_agree_of_terminalBranchData
    {x₀ : X} {i₀ : ι} {x y : X}
    {p q : Path x₀ x} {suffix : Path x y}
    (C : S.PathContinuationChain x₀ i₀ p)
    (E : S.PathContinuationChain x₀ i₀ q)
    (D : S.PathContinuationChain x C.terminalBranch suffix)
    (F : S.PathContinuationChain x E.terminalBranch suffix)
    (hPrefixTransition : C.terminalTransition = E.terminalTransition)
    (hSuffixBranch : D.terminalBranch = F.terminalBranch)
    (hSuffixTransition : D.terminalTransition = F.terminalTransition) :
    (C.appendSuffixChain D).toTerminalGerm.LocallyAgreesWith
      (E.appendSuffixChain F).toTerminalGerm := by
  apply
    terminalGerms_agree_of_terminalBranch_eq_terminalTransition_eq
      (C.appendSuffixChain D) (E.appendSuffixChain F)
  · simpa using hSuffixBranch
  · rw [C.appendSuffixChain_terminalTransition D,
      E.appendSuffixChain_terminalTransition F,
      hPrefixTransition, hSuffixTransition]

/--
Subdivision parameters for changing only the terminal branch: keep the old
subdivision and add one final endpoint at \(1\).
-/
noncomputable def terminalHandoffParameterAt
    (C : S.PathContinuationChain x₀ i₀ p) :
    Fin (C.length + 2) → unitInterval :=
  fun i =>
    if hi : (i : ℕ) < C.length + 1 then
      C.parameterAt ⟨i, hi⟩
    else
      1

/--
Branches for changing only the terminal branch: keep the old branch choices
and use the requested branch at the added final endpoint.
-/
noncomputable def terminalHandoffBranchAt
    (C : S.PathContinuationChain x₀ i₀ p) (j : ι) :
    Fin (C.length + 2) → ι :=
  fun i =>
    if hi : (i : ℕ) < C.length + 1 then
      C.branchAt ⟨i, hi⟩
    else
      j

/--
Accumulated transitions for changing only the terminal branch: keep the old
products and update the added final product by the terminal handoff.
-/
noncomputable def terminalHandoffTransitionProductAt
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x) :
    Fin (C.length + 2) → G :=
  fun i =>
    if hi : (i : ℕ) < C.length + 1 then
      C.transitionProductAt ⟨i, hi⟩
    else
      C.terminalTransition * T.transition⁻¹

/--
%%handwave
name:
  Old parameters inside a terminal handoff subdivision
statement:
  At every old vertex, viewed among all but the newly appended endpoint, the
  terminal-handoff subdivision has the original parameter value.
proof:
  Such an index satisfies the old-index branch of the defining case split.
-/
@[simp]
theorem terminalHandoffParameterAt_castSucc
    (C : S.PathContinuationChain x₀ i₀ p)
    (i : Fin (C.length + 1)) :
    C.terminalHandoffParameterAt i.castSucc = C.parameterAt i := by
  change
    (if hi : (i : ℕ) < C.length + 1 then
      C.parameterAt ⟨i, hi⟩
    else 1) = C.parameterAt i
  rw [dif_pos i.isLt]

/--
%%handwave
name:
  Old branches inside a terminal handoff subdivision
statement:
  At every old vertex, the terminal-handoff subdivision retains the original
  branch choice.
proof:
  The old vertex lies in the first case of the branch assignment.
-/
@[simp]
theorem terminalHandoffBranchAt_castSucc
    (C : S.PathContinuationChain x₀ i₀ p) (j : ι)
    (i : Fin (C.length + 1)) :
    C.terminalHandoffBranchAt j i.castSucc = C.branchAt i := by
  change
    (if hi : (i : ℕ) < C.length + 1 then
      C.branchAt ⟨i, hi⟩
    else j) = C.branchAt i
  rw [dif_pos i.isLt]

/--
%%handwave
name:
  Old transition products inside a terminal handoff subdivision
statement:
  At every old vertex, the terminal-handoff construction retains the original
  accumulated transition product.
proof:
  Evaluate the defining case split at an old index.
-/
@[simp]
theorem terminalHandoffTransitionProductAt_castSucc
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x)
    (i : Fin (C.length + 1)) :
    C.terminalHandoffTransitionProductAt T i.castSucc =
      C.transitionProductAt i := by
  change
    (if hi : (i : ℕ) < C.length + 1 then
      C.transitionProductAt ⟨i, hi⟩
    else C.terminalTransition * T.transition⁻¹) = C.transitionProductAt i
  rw [dif_pos i.isLt]

/--
%%handwave
name:
  Final parameter of a terminal handoff subdivision
statement:
  The newly appended final vertex of a terminal handoff has parameter \(1\).
proof:
  The last index is outside the old vertex range, so the new endpoint clause
  applies.
-/
@[simp]
theorem terminalHandoffParameterAt_last
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalHandoffParameterAt (Fin.last (C.length + 1)) = 1 := by
  simp [terminalHandoffParameterAt]

/--
%%handwave
name:
  Final branch of a terminal handoff subdivision
statement:
  The newly appended final vertex is assigned the requested handoff branch
  \(j\).
proof:
  This is the new-endpoint clause of the branch assignment.
-/
@[simp]
theorem terminalHandoffBranchAt_last
    (C : S.PathContinuationChain x₀ i₀ p) (j : ι) :
    C.terminalHandoffBranchAt j (Fin.last (C.length + 1)) = j := by
  simp [terminalHandoffBranchAt]

/--
%%handwave
name:
  Final transition product of a terminal handoff subdivision
statement:
  If the old terminal product is \(g\) and the endpoint transition is \(h\),
  the new final accumulated product is \(gh^{-1}\).
proof:
  This is the new-endpoint clause of the accumulated-product assignment.
-/
@[simp]
theorem terminalHandoffTransitionProductAt_last
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x) :
    C.terminalHandoffTransitionProductAt T (Fin.last (C.length + 1)) =
      C.terminalTransition * T.transition⁻¹ := by
  simp [terminalHandoffTransitionProductAt]

/--
%%handwave
name:
  Initial parameter of a terminal handoff subdivision
statement:
  The terminal-handoff subdivision begins at parameter \(0\).
proof:
  Its initial vertex is an old vertex, whose original parameter is zero.
-/
@[simp]
theorem terminalHandoffParameterAt_zero
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalHandoffParameterAt 0 = 0 := by
  simp [terminalHandoffParameterAt, C.parameterAt_zero]

/--
%%handwave
name:
  Initial branch of a terminal handoff subdivision
statement:
  The terminal-handoff subdivision has the same branch as the original chain
  at its initial vertex.
proof:
  The initial index belongs to the retained old vertex range.
-/
@[simp]
theorem terminalHandoffBranchAt_zero
    (C : S.PathContinuationChain x₀ i₀ p) (j : ι) :
    C.terminalHandoffBranchAt j 0 = C.branchAt 0 := by
  simp [terminalHandoffBranchAt]

/--
%%handwave
name:
  Initial transition product of a terminal handoff subdivision
statement:
  The terminal-handoff subdivision retains the original accumulated
  transition product at parameter zero.
proof:
  The zero index is handled by the old-vertex clause.
-/
@[simp]
theorem terminalHandoffTransitionProductAt_zero
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x) :
    C.terminalHandoffTransitionProductAt T 0 = C.transitionProductAt 0 := by
  simp [terminalHandoffTransitionProductAt]

/--
%%handwave
name:
  Left parameter at the duplicated terminal endpoint
statement:
  The last old vertex, regarded as the left endpoint of the newly appended
  handoff segment, has parameter \(1\).
proof:
  It retains the original chain's terminal parameter.
-/
@[simp]
theorem terminalHandoffParameterAt_final_left
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalHandoffParameterAt
        ((Fin.last C.length : Fin (C.length + 1)).castSucc) = 1 := by
  simp [C.parameterAt_last]

/--
%%handwave
name:
  Left branch at the terminal handoff
statement:
  The last old vertex on the left of the appended handoff segment carries the
  original terminal branch.
proof:
  Old branch assignments are retained, including the terminal one.
-/
@[simp]
theorem terminalHandoffBranchAt_final_left
    (C : S.PathContinuationChain x₀ i₀ p) (j : ι) :
    C.terminalHandoffBranchAt j
        ((Fin.last C.length : Fin (C.length + 1)).castSucc) =
      C.terminalBranch := by
  simp [terminalBranch]

/--
%%handwave
name:
  Left transition product at the terminal handoff
statement:
  At the last old vertex, the handoff construction has the original terminal
  transition product.
proof:
  The construction retains accumulated products on all old vertices.
-/
@[simp]
theorem terminalHandoffTransitionProductAt_final_left
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x) :
    C.terminalHandoffTransitionProductAt T
        ((Fin.last C.length : Fin (C.length + 1)).castSucc) =
      C.terminalTransition := by
  simp [terminalTransition]

/--
%%handwave
name:
  Right parameter at the terminal handoff
statement:
  The newly appended vertex on the right of the handoff segment also has
  parameter \(1\).
proof:
  This successor index is the new last index, whose parameter is defined to
  be one.
-/
@[simp]
theorem terminalHandoffParameterAt_final_right
    (C : S.PathContinuationChain x₀ i₀ p) :
    C.terminalHandoffParameterAt
        ((Fin.last C.length : Fin (C.length + 1)).succ) = 1 := by
  rw [fin_last_succ_eq_last]
  exact C.terminalHandoffParameterAt_last

/--
%%handwave
name:
  Right branch at the terminal handoff
statement:
  The vertex on the right of the appended endpoint segment carries the new
  branch \(j\).
proof:
  It is the newly appended last vertex.
-/
@[simp]
theorem terminalHandoffBranchAt_final_right
    (C : S.PathContinuationChain x₀ i₀ p) (j : ι) :
    C.terminalHandoffBranchAt j
        ((Fin.last C.length : Fin (C.length + 1)).succ) = j := by
  rw [fin_last_succ_eq_last]
  exact C.terminalHandoffBranchAt_last j

/--
%%handwave
name:
  Right transition product at the terminal handoff
statement:
  The right endpoint of the handoff segment has accumulated transition
  \(gh^{-1}\), where \(g\) is the old terminal product and \(h\) is the local
  branch transition.
proof:
  The right endpoint is the newly appended last vertex.
-/
@[simp]
theorem terminalHandoffTransitionProductAt_final_right
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x) :
    C.terminalHandoffTransitionProductAt T
        ((Fin.last C.length : Fin (C.length + 1)).succ) =
      C.terminalTransition * T.transition⁻¹ := by
  rw [fin_last_succ_eq_last]
  exact C.terminalHandoffTransitionProductAt_last T

/--
%%handwave
name:
  Monotonicity of terminal handoff parameters
statement:
  Consecutive parameters in the terminal-handoff subdivision are
  nondecreasing.
proof:
  On old segments this is the original chain's monotonicity.  The final
  segment has both endpoints at parameter \(1\).
-/
theorem terminalHandoffParameterAt_mono
    (C : S.PathContinuationChain x₀ i₀ p) :
    ∀ k : Fin (C.length + 1),
      (C.terminalHandoffParameterAt k.castSucc : ℝ) ≤
        (C.terminalHandoffParameterAt k.succ : ℝ) := by
  intro k
  by_cases hk : (k : ℕ) < C.length
  · let k₀ : Fin C.length := ⟨k, hk⟩
    have hleft :
        k.castSucc = (k₀.castSucc : Fin (C.length + 1)).castSucc := by
      ext
      rfl
    have hright : k.succ = (k₀.succ : Fin (C.length + 1)).castSucc := by
      ext
      rfl
    rw [hleft, hright, C.terminalHandoffParameterAt_castSucc k₀.castSucc,
      C.terminalHandoffParameterAt_castSucc k₀.succ]
    exact C.parameterAt_mono k₀
  · have hk_last : k = Fin.last C.length := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
        (Nat.le_of_not_gt hk)
    subst k
    rw [C.terminalHandoffParameterAt_final_left,
      C.terminalHandoffParameterAt_final_right]

noncomputable def terminalHandoffTransitionAt
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x) :
    ∀ k : Fin (C.length + 1),
      S.LocalTransition
        (C.terminalHandoffBranchAt j k.castSucc)
        (C.terminalHandoffBranchAt j k.succ)
        (p (C.terminalHandoffParameterAt k.succ)) := by
  intro k
  by_cases hk : (k : ℕ) < C.length
  · let k₀ : Fin C.length := ⟨k, hk⟩
    have hleft :
        k.castSucc = (k₀.castSucc : Fin (C.length + 1)).castSucc := by
      ext
      rfl
    have hright : k.succ = (k₀.succ : Fin (C.length + 1)).castSucc := by
      ext
      rfl
    have hpath :
        p (C.terminalHandoffParameterAt k.succ) =
          p (C.parameterAt k₀.succ) := by
      rw [hright, C.terminalHandoffParameterAt_castSucc]
    exact
      (C.transitionAt k₀).congr
        (by rw [hleft]; simp)
        (by
          rw [hright]
          exact (C.terminalHandoffBranchAt_castSucc j k₀.succ).symm)
        hpath.symm
  · have hk_last : k = Fin.last C.length := by
      ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
        (Nat.le_of_not_gt hk)
    subst k
    have hpath :
        p (C.terminalHandoffParameterAt
            ((Fin.last C.length : Fin (C.length + 1)).succ)) = x := by
      simp [p.target]
    exact
      T.congr
        (by rw [C.terminalHandoffBranchAt_final_left])
        (by rw [C.terminalHandoffBranchAt_final_right])
        hpath.symm

/--
%%handwave
name:
  Terminal branch handoff
statement:
  A continuation chain can change only its terminal branch by appending a
  zero-length final handoff at the endpoint.
proof:
  Add one final subdivision point, again at \(1\).  The old subdivision,
  branches, and transition products are reused before the final point; the
  final transition product is updated by the inverse of the terminal handoff.
-/
noncomputable def terminalHandoffAlongChain
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x) :
    S.PathContinuationChain x₀ i₀ p where
  length := C.length + 1
  parameterAt := C.terminalHandoffParameterAt
  parameterAt_zero := C.terminalHandoffParameterAt_zero
  parameterAt_last := C.terminalHandoffParameterAt_last
  parameterAt_mono := C.terminalHandoffParameterAt_mono
  branchAt := C.terminalHandoffBranchAt j
  initialTransition := by
    exact C.initialTransition.congr rfl (by simp) rfl
  transitionProductAt := C.terminalHandoffTransitionProductAt T
  transitionProductAt_zero := by
    simp [C.transitionProductAt_zero]
  transitionAt := C.terminalHandoffTransitionAt T
  transitionProductAt_succ_eq := by
    intro k
    by_cases hk : (k : ℕ) < C.length
    · let k₀ : Fin C.length := ⟨k, hk⟩
      have hleft :
          k.castSucc = (k₀.castSucc : Fin (C.length + 1)).castSucc := by
        ext
        rfl
      have hright : k.succ = (k₀.succ : Fin (C.length + 1)).castSucc := by
        ext
        rfl
      have hprod_left :
          C.terminalHandoffTransitionProductAt T k.castSucc =
            C.transitionProductAt k₀.castSucc := by
        rw [hleft]
        simp
      have hprod_right :
          C.terminalHandoffTransitionProductAt T k.succ =
            C.transitionProductAt k₀.succ := by
        rw [hright]
        exact C.terminalHandoffTransitionProductAt_castSucc T k₀.succ
      have htrans :
          (C.terminalHandoffTransitionAt T k).transition =
            (C.transitionAt k₀).transition := by
        simp [terminalHandoffTransitionAt, hk, k₀]
      rw [hprod_right, hprod_left, htrans, C.transitionProductAt_succ_eq k₀]
    · have hk_last : k = Fin.last C.length := by
        ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
          (Nat.le_of_not_gt hk)
      subst k
      have htrans :
          (C.terminalHandoffTransitionAt T (Fin.last C.length)).transition =
            T.transition := by
        simp [terminalHandoffTransitionAt]
      rw [C.terminalHandoffTransitionProductAt_final_left,
        C.terminalHandoffTransitionProductAt_final_right, htrans]
  sample_mem_domain := by
    intro i
    by_cases hi : (i : ℕ) < C.length + 1
    · let k : Fin (C.length + 1) := ⟨i, hi⟩
      have hik : i = k.castSucc := by
        ext
        rfl
      rw [hik, C.terminalHandoffParameterAt_castSucc,
        C.terminalHandoffBranchAt_castSucc]
      exact C.sample_mem_domain k
    · have hi_last : i = Fin.last (C.length + 1) := by
        ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ i.isLt)
          (Nat.le_of_not_gt hi)
      rw [hi_last]
      simpa [p.target] using (T.subset_overlap T.mem_neighborhood).2
  path_segment_mem_domain := by
    intro k t ht_left ht_right
    by_cases hk : (k : ℕ) < C.length
    · let k₀ : Fin C.length := ⟨k, hk⟩
      have hleft_index :
          k.castSucc = (k₀.castSucc : Fin (C.length + 1)).castSucc := by
        ext
        rfl
      have hright_index : k.succ = (k₀.succ : Fin (C.length + 1)).castSucc := by
        ext
        rfl
      rw [hleft_index, C.terminalHandoffParameterAt_castSucc k₀.castSucc] at ht_left
      rw [hright_index, C.terminalHandoffParameterAt_castSucc k₀.succ] at ht_right
      have hbranch :
          C.terminalHandoffBranchAt j k.castSucc = C.branchAt k₀.castSucc := by
        rw [hleft_index]
        simp
      rw [hbranch]
      exact C.path_segment_mem_domain k₀ t ht_left ht_right
    · have hk_last : k = Fin.last C.length := by
        ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ k.isLt)
          (Nat.le_of_not_gt hk)
      subst k
      rw [C.terminalHandoffParameterAt_final_left] at ht_left
      have ht_eq : t = 1 := by
        ext
        exact le_antisymm t.property.2 ht_left
      rw [C.terminalHandoffBranchAt_final_left, ht_eq]
      simpa [p.target] using C.terminal_endpoint_mem_domain
  terminal_endpoint_mem_domain := by
    simpa [terminalHandoffBranchAt, p.target] using
      (T.subset_overlap T.mem_neighborhood).2

/--
%%handwave
name:
  Terminal branch after a handoff
statement:
  If a continuation chain ending in branch \(i\) is handed off at its endpoint
  to a locally related branch \(j\), then the resulting chain terminates in
  branch \(j\).
proof:
  The newly appended terminal vertex is assigned branch \(j\) by construction.
-/
@[simp]
theorem terminalHandoffAlongChain_terminalBranch
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x) :
    (C.terminalHandoffAlongChain T).terminalBranch = j := by
  simp [terminalHandoffAlongChain, terminalBranch]

/--
%%handwave
name:
  Terminal transition after a handoff
statement:
  If the original terminal transition is \(g\) and the local handoff from
  branch \(i\) to branch \(j\) has transition \(h\), then the handed-off
  chain has terminal transition \(gh^{-1}\).
proof:
  The appended endpoint vertex is defined with transition product
  \(gh^{-1}\).
-/
@[simp]
theorem terminalHandoffAlongChain_terminalTransition
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x) :
    (C.terminalHandoffAlongChain T).terminalTransition =
      C.terminalTransition * T.transition⁻¹ := by
  simp [terminalHandoffAlongChain, terminalTransition]

/--
%%handwave
name:
  Terminal branch handoff preserves the terminal germ
statement:
  The old terminal expression and the expression after a terminal branch
  handoff agree locally at the endpoint.
proof:
  This is exactly the local transition relation used for the appended
  zero-length handoff, combined with the transition-product update rule.
-/
theorem terminalHandoffAlongChain_terminalGerms_agree
    (C : S.PathContinuationChain x₀ i₀ p)
    {j : ι} (T : S.LocalTransition C.terminalBranch j x) :
    C.toTerminalGerm.LocallyAgreesWith
      (C.terminalHandoffAlongChain T).toTerminalGerm := by
  let D : S.PathContinuationChain x₀ i₀ p := C.terminalHandoffAlongChain T
  let k : Fin D.length := Fin.last C.length
  have hlocal :
      S.LocalExpressionAgreesAt
        C.terminalBranch D.terminalBranch
        C.terminalTransition D.terminalTransition
        x := by
    have h :=
      D.transitionProductAt_succ_localExpressionAgreesAt k
    simpa [D, k, terminalHandoffAlongChain, terminalBranch,
      terminalTransition, p.target] using h
  rcases hlocal with ⟨U, hU_open, hxU, hU_subset, hU_eq⟩
  refine ⟨U, hU_open, hxU, ?_, ?_⟩
  · intro z hz
    simpa [D, PathContinuationChain.toTerminalGerm] using hU_subset hz
  · intro z hz
    simpa [D, PathContinuationGerm.localMap,
      PathContinuationChain.toTerminalGerm] using hU_eq z hz

/--
%%handwave
name:
  Common terminal handoff preserves local agreement
statement:
  If two terminal germs locally agree at a common endpoint, then after changing
  both terminal branches to a common branch by local handoffs, the resulting
  terminal germs still locally agree.
proof:
  Each terminal handoff locally agrees with the germ before the handoff, so the
  conclusion follows by symmetry and transitivity of local agreement.
-/
theorem terminalHandoffAlongChain_commonBranch_terminalGerms_agree
    {x₀ : X} {i₀ : ι} {x : X}
    {p q : Path x₀ x}
    (C : S.PathContinuationChain x₀ i₀ p)
    (D : S.PathContinuationChain x₀ i₀ q)
    (H : C.toTerminalGerm.LocallyAgreesWith D.toTerminalGerm)
    {j : ι}
    (TC : S.LocalTransition C.terminalBranch j x)
    (TD : S.LocalTransition D.terminalBranch j x) :
    (C.terminalHandoffAlongChain TC).toTerminalGerm.LocallyAgreesWith
      (D.terminalHandoffAlongChain TD).toTerminalGerm := by
  exact
    PathContinuationGerm.locallyAgreesWith_trans
      (PathContinuationGerm.locallyAgreesWith_symm
        (C.terminalHandoffAlongChain_terminalGerms_agree TC))
      (PathContinuationGerm.locallyAgreesWith_trans H
        (D.terminalHandoffAlongChain_terminalGerms_agree TD))

/--
%%handwave
name:
  Rectangle-edge extensions agree after terminal branch handoff
statement:
  Suppose a homotopy rectangle lies in one branch domain.  If a continuation
  chain has reached the lower-left corner, then after changing its terminal
  branch to that rectangle branch, extending along the two boundary routes
  around the rectangle gives locally agreeing terminal germs.
proof:
  The terminal handoff changes the current terminal branch to the rectangle
  branch.  Both rectangle-edge paths stay in that branch domain, so the two
  exact terminal-branch appends preserve the same terminal branch and transition.
-/
theorem exists_terminalGerms_agree_after_homotopyRectangle_edges
    {xA xB : X} {p q : Path xA xB}
    (F : Path.Homotopy p q) (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {branch : ι}
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval | F z ∈ S.domain branch})
    {base : X} {ibase : ι}
    {pref : Path base (F (a, r₀))}
    (C : S.PathContinuationChain base ibase pref)
    (T : S.LocalTransition C.terminalBranch branch (F (a, r₀))) :
    ∃ (CbottomRight :
        S.PathContinuationChain base ibase
          (pref.trans (homotopyRectangleBottomRightPath F a b r₀ r₁)))
      (CleftTop :
        S.PathContinuationChain base ibase
          (pref.trans (homotopyRectangleLeftTopPath F a b r₀ r₁))),
      CbottomRight.toTerminalGerm.LocallyAgreesWith
        CleftTop.toTerminalGerm := by
  let Cbranch : S.PathContinuationChain base ibase pref :=
    C.terminalHandoffAlongChain T
  have hBR :
      ∀ u : unitInterval,
        homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
          S.domain Cbranch.terminalBranch := by
    intro u
    have hmem :
        homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
          S.domain branch :=
      homotopyRectangleBottomRightPath_mem_of_rect_subset
        F a b r₀ r₁ hab hr hRect u
    simpa [Cbranch] using hmem
  have hLT :
      ∀ u : unitInterval,
        homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
          S.domain Cbranch.terminalBranch := by
    intro u
    have hmem :
        homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
          S.domain branch :=
      homotopyRectangleLeftTopPath_mem_of_rect_subset
        F a b r₀ r₁ hab hr hRect u
    simpa [Cbranch] using hmem
  exact
    ⟨Cbranch.terminalExtensionAlongChain
        (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR,
      Cbranch.terminalExtensionAlongChain
        (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT,
      Cbranch.terminalExtensionsAlong_same_terminalGerms_agree
        (homotopyRectangleBottomRightPath F a b r₀ r₁)
        (homotopyRectangleLeftTopPath F a b r₀ r₁) hBR hLT⟩

end PathContinuationChain

/--
%%handwave
name:
  Single-domain path-continuation chain
statement:
  If a path stays inside one branch domain, it admits a one-piece continuation
  chain with identity transition.
proof:
  Use the subdivision \(0,1\), keep the same branch on both vertices, and use
  the identity local transition at the terminal vertex.
-/
theorem pathContinuationChain_of_path_mem_single_domain
    {x₀ : X} {i₀ : ι} {x : X} (p : Path x₀ x)
    (hpath : ∀ t : unitInterval, p t ∈ S.domain i₀) :
    Nonempty (S.PathContinuationChain x₀ i₀ p) := by
  let parameterAt : Fin (1 + 1) → unitInterval :=
    fun k ↦ if k = 0 then 0 else 1
  refine
    ⟨
      { length := 1
        parameterAt := parameterAt
        parameterAt_zero := by
          simp [parameterAt]
        parameterAt_last := by
          simp [parameterAt]
        parameterAt_mono := ?_
        branchAt := fun _ ↦ i₀
        initialTransition := LocalTransition.refl (S := S) i₀
          (by simpa [p.source] using hpath 0)
        transitionProductAt := fun _ ↦ 1
        transitionProductAt_zero := by
          simp [LocalTransition.refl]
        transitionAt := ?_
        transitionProductAt_succ_eq := ?_
        sample_mem_domain := ?_
        path_segment_mem_domain := ?_
        terminal_endpoint_mem_domain := ?_ }⟩
  · intro k
    fin_cases k
    simp [parameterAt]
  · intro k
    exact LocalTransition.refl (S := S) i₀ (hpath (parameterAt k.succ))
  · intro k
    fin_cases k
    simp [LocalTransition.refl]
  · intro i
    exact hpath (parameterAt i)
  · intro k t _ht0 _ht1
    exact hpath t
  · simpa using hpath 1

/--
%%handwave
name:
  Existence of finite path-continuation chains
statement:
  Given local transitions, every path starting in a chosen branch admits a
  finite path-continuation chain subordinate to the branch-domain cover.
proof:
  Cover the compact interval by inverse images of branch domains along the
  path.  Choose a finite ordered subdivision subordinate to this cover.  At
  each internal vertex use the local-transition hypothesis to choose the
  handoff transition, and accumulate transition elements by multiplying by the
  inverse handoff.
-/
theorem exists_pathContinuationChain_of_localTransitions
    (htransitions : S.HasLocalTransitions)
    {x₀ : X} {i₀ : ι} (hx₀ : x₀ ∈ S.domain i₀)
    {x : X} (p : Path x₀ x) :
    Nonempty (S.PathContinuationChain x₀ i₀ p) := by
  classical
  let branchNear : unitInterval → ι :=
    fun t ↦ Classical.choose (S.covers (p t))
  have hbranchNear : ∀ t : unitInterval, p t ∈ S.domain (branchNear t) := by
    intro t
    exact Classical.choose_spec (S.covers (p t))
  let c : unitInterval → Set unitInterval :=
    fun t ↦ p ⁻¹' S.domain (branchNear t)
  have hc_open : ∀ t, IsOpen (c t) := by
    intro t
    exact (S.domain_open (branchNear t)).preimage p.continuous
  have hc_cover : Set.univ ⊆ ⋃ t, c t := by
    intro r _hr
    exact Set.mem_iUnion.mpr ⟨r, hbranchNear r⟩
  obtain ⟨tNat, ht0, htmono, ⟨m, hm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := c) hc_open hc_cover
  let parameterAt : Fin (m + 1) → unitInterval := fun k ↦ tNat k
  let coverParameterAt : ℕ → unitInterval := fun n ↦ Classical.choose (hsub n)
  have hcoverParameterAt :
      ∀ n, Set.Icc (tNat n) (tNat (n + 1)) ⊆ c (coverParameterAt n) := by
    intro n
    exact Classical.choose_spec (hsub n)
  let branchAt : Fin (m + 1) → ι :=
    fun k ↦ branchNear (coverParameterAt k)
  have hsample : ∀ i, p (parameterAt i) ∈ S.domain (branchAt i) := by
    intro i
    have hmem :
        tNat (i : ℕ) ∈ Set.Icc (tNat (i : ℕ)) (tNat ((i : ℕ) + 1)) := by
      exact ⟨le_rfl, htmono (Nat.le_succ (i : ℕ))⟩
    exact hcoverParameterAt (i : ℕ) hmem
  have hsegment :
      ∀ k : Fin m, ∀ t : unitInterval,
        (parameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
        (t : ℝ) ≤ (parameterAt k.succ : ℝ) →
        p t ∈ S.domain (branchAt k.castSucc) := by
    intro k t hleft hright
    have ht :
        t ∈ Set.Icc (tNat (k : ℕ)) (tNat ((k : ℕ) + 1)) :=
      ⟨hleft, hright⟩
    exact hcoverParameterAt (k : ℕ) ht
  have hfirst : x₀ ∈ S.domain (branchAt 0) := by
    have h0 : p (parameterAt 0) ∈ S.domain (branchAt 0) := hsample 0
    simpa [parameterAt, ht0, p.source] using h0
  let initialTransition : S.LocalTransition i₀ (branchAt 0) x₀ :=
    Classical.choice (htransitions i₀ (branchAt 0) x₀ ⟨hx₀, hfirst⟩)
  let transitionAt :
      ∀ k : Fin m,
        S.LocalTransition (branchAt k.castSucc) (branchAt k.succ)
          (p (parameterAt k.succ)) :=
    fun k ↦
      Classical.choice
        (htransitions (branchAt k.castSucc) (branchAt k.succ)
          (p (parameterAt k.succ))
          ⟨
            (by
              exact hsegment k (parameterAt k.succ)
                (by
                  exact_mod_cast htmono (Nat.le_succ (k : ℕ)))
                le_rfl),
            hsample k.succ⟩)
  let transitionProductNat : ℕ → G :=
    Nat.rec initialTransition.transition⁻¹
      (fun n acc ↦
        if h : n < m then acc * (transitionAt ⟨n, h⟩).transition⁻¹ else acc)
  let transitionProductAt : Fin (m + 1) → G :=
    fun k ↦ transitionProductNat k
  refine
    ⟨
      { length := m
        parameterAt := parameterAt
        parameterAt_zero := ht0
        parameterAt_last := hm m le_rfl
        parameterAt_mono := ?_
        branchAt := branchAt
        initialTransition := initialTransition
        transitionProductAt := transitionProductAt
        transitionProductAt_zero := ?_
        transitionAt := transitionAt
        transitionProductAt_succ_eq := ?_
        sample_mem_domain := hsample
        path_segment_mem_domain := hsegment
        terminal_endpoint_mem_domain := ?_ }⟩
  · intro k
    exact htmono (Nat.le_succ (k : ℕ))
  · simp [transitionProductAt, transitionProductNat]
  · intro k
    simp [transitionProductAt, transitionProductNat, k.isLt]
  · have hlast :
        p (parameterAt (Fin.last m)) ∈
          S.domain (branchAt (Fin.last m)) :=
      hsample (Fin.last m)
    simpa [parameterAt, hm m le_rfl, p.target] using hlast

/--
%%handwave
name:
  Branch-domain grid for a path homotopy
statement:
  An endpoint-fixed path homotopy admits a finite rectangular subdivision
  whose every rectangle lies in one branch domain.
proof:
  Pull back the branch-domain cover along the homotopy map and apply compactness
  of the unit square.
-/
theorem pathHomotopy_exists_monotone_branch_grid
    {x₀ x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) :
    ∃ t : ℕ → unitInterval,
      t 0 = 0 ∧
      Monotone t ∧
      (∃ N, ∀ n ≥ N, t n = 1) ∧
      ∀ n m,
        ∃ i : ι,
          Set.Icc (t n) (t (n + 1)) ×ˢ
              Set.Icc (t m) (t (m + 1)) ⊆
            {z : unitInterval × unitInterval | F z ∈ S.domain i} := by
  classical
  let U : ι → Set X := S.domain
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    exact S.domain_open i
  have hUcover : Set.univ ⊆ ⋃ i : ι, U i := by
    intro z _hz
    rcases S.covers z with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  rcases
    exists_monotone_rectangular_subdivision_subordinate_to_open_cover
      F F.continuous U hUopen hUcover with
    ⟨t, ht0, htmono, htEventually, htRect⟩
  exact ⟨t, ht0, htmono, htEventually, htRect⟩

/--
%%handwave
name:
  Branch-domain grid for homotopic paths
statement:
  Endpoint-fixed homotopic paths admit a finite rectangular subdivision of a
  representing homotopy whose every rectangle lies in one branch domain.
proof:
  Apply the branch-domain grid theorem to a representative homotopy.
-/
theorem pathHomotopic_exists_monotone_branch_grid
    {x₀ x : X} {p q : Path x₀ x}
    (hpq : Path.Homotopic p q) :
    ∃ t : ℕ → unitInterval,
      t 0 = 0 ∧
      Monotone t ∧
      (∃ N, ∀ n ≥ N, t n = 1) ∧
      ∀ n m,
        ∃ i : ι,
          Set.Icc (t n) (t (n + 1)) ×ˢ
              Set.Icc (t m) (t (m + 1)) ⊆
            {z : unitInterval × unitInterval | hpq.some z ∈ S.domain i} :=
  S.pathHomotopy_exists_monotone_branch_grid hpq.some

/--
%%handwave
name:
  Path-continuation chain state
statement:
  A path-continuation chain state packages a representative path together with
  a finite continuation chain along it.
-/
structure PathContinuationChainState (x₀ : X) (i₀ : ι) (x : X) where
  /-- The representative path. -/
  path : Path x₀ x
  /-- The continuation chain along the representative path. -/
  chain : S.PathContinuationChain x₀ i₀ path

namespace PathContinuationChainState

variable {S} {x₀ : X} {i₀ : ι} {x : X}

/-- Build a path-continuation state from a chain along a chosen path. -/
def ofChain {p : Path x₀ x}
    (C : S.PathContinuationChain x₀ i₀ p) :
    S.PathContinuationChainState x₀ i₀ x where
  path := p
  chain := C

/-- The terminal germ of a path-continuation state. -/
def terminalGerm
    (A : S.PathContinuationChainState x₀ i₀ x) :
    S.PathContinuationGerm x₀ i₀ A.path :=
  A.chain.toTerminalGerm

/--
%%handwave
name:
  Terminal germ of a chain state
statement:
  The path-continuation state built from a continuation chain has exactly the
  terminal germ of that chain.
proof:
  This is immediate from the construction of the state.
-/
@[simp]
theorem ofChain_terminalGerm {p : Path x₀ x}
    (C : S.PathContinuationChain x₀ i₀ p) :
    (PathContinuationChainState.ofChain C).terminalGerm =
      C.toTerminalGerm :=
  rfl

end PathContinuationChainState

/--
%%handwave
name:
  Elementary terminal-germ move
statement:
  An elementary terminal-germ move between continuation-chain states records
  that their terminal germs locally agree.
-/
structure PathContinuationChainGermMove
    {x₀ : X} {i₀ : ι} {x : X}
    (A B : S.PathContinuationChainState x₀ i₀ x) where
  /-- The elementary move preserves the terminal germ. -/
  terminalGerms_agree :
    A.terminalGerm.LocallyAgreesWith B.terminalGerm

namespace PathContinuationChainGermMove

variable {S} {x₀ : X} {i₀ : ι} {x : X}
    {A B : S.PathContinuationChainState x₀ i₀ x}

/-- The identity terminal-germ move. -/
def refl (A : S.PathContinuationChainState x₀ i₀ x) :
    S.PathContinuationChainGermMove A A where
  terminalGerms_agree :=
    PathContinuationGerm.locallyAgreesWith_refl A.terminalGerm

/-- Reverse an elementary terminal-germ move. -/
def symm (M : S.PathContinuationChainGermMove A B) :
    S.PathContinuationChainGermMove B A where
  terminalGerms_agree :=
    PathContinuationGerm.locallyAgreesWith_symm M.terminalGerms_agree

/-- Compose elementary terminal-germ moves. -/
def trans
    {C : S.PathContinuationChainState x₀ i₀ x}
    (M₁ : S.PathContinuationChainGermMove A B)
    (M₂ : S.PathContinuationChainGermMove B C) :
    S.PathContinuationChainGermMove A C where
  terminalGerms_agree :=
    PathContinuationGerm.locallyAgreesWith_trans
      M₁.terminalGerms_agree M₂.terminalGerms_agree

end PathContinuationChainGermMove

/--
%%handwave
name:
  Terminal-germ walk
statement:
  A terminal-germ walk is a finite sequence of continuation-chain states whose
  adjacent terminal germs locally agree.
-/
structure PathContinuationChainGermWalk
    {x₀ : X} {i₀ : ι} {x : X}
    (A B : S.PathContinuationChainState x₀ i₀ x) where
  /-- Number of elementary moves. -/
  length : ℕ
  /-- The continuation state after `n` moves. -/
  stateAt : ℕ → S.PathContinuationChainState x₀ i₀ x
  /-- The walk starts at the given state. -/
  stateAt_zero : stateAt 0 = A
  /-- The walk ends at the given state. -/
  stateAt_length : stateAt length = B
  /-- Each step preserves the terminal germ. -/
  moveAt :
    ∀ n, n < length →
      S.PathContinuationChainGermMove (stateAt n) (stateAt (n + 1))

namespace PathContinuationChainGermWalk

variable {S} {x₀ : X} {i₀ : ι} {x : X}
    {A B C : S.PathContinuationChainState x₀ i₀ x}

/-- The constant terminal-germ walk. -/
def refl (A : S.PathContinuationChainState x₀ i₀ x) :
    S.PathContinuationChainGermWalk A A where
  length := 0
  stateAt := fun _ => A
  stateAt_zero := rfl
  stateAt_length := rfl
  moveAt := by
    intro n hn
    omega

/-- Append one terminal-germ move to a terminal-germ walk. -/
def snoc
    (W : S.PathContinuationChainGermWalk A B)
    (M : S.PathContinuationChainGermMove B C) :
    S.PathContinuationChainGermWalk A C where
  length := W.length + 1
  stateAt := fun n =>
    if h : n ≤ W.length then
      W.stateAt n
    else
      C
  stateAt_zero := by
    simp [W.stateAt_zero]
  stateAt_length := by
    simp
  moveAt := by
    intro n hn
    by_cases hnlt : n < W.length
    · have hnle : n ≤ W.length := Nat.le_of_lt hnlt
      have hsuccle : n + 1 ≤ W.length := Nat.succ_le_of_lt hnlt
      simpa [hnle, hsuccle] using W.moveAt n hnlt
    · have hn_eq : n = W.length := by omega
      subst n
      have hnot : ¬ W.length + 1 ≤ W.length := by omega
      simpa [hnot, W.stateAt_length] using M

/-- A single terminal-germ move as a walk. -/
def ofMove (M : S.PathContinuationChainGermMove A B) :
    S.PathContinuationChainGermWalk A B :=
  (refl A).snoc M

/-- Change only the named endpoint states of a terminal-germ walk. -/
def cast
    (W : S.PathContinuationChainGermWalk A B)
    {A' B' : S.PathContinuationChainState x₀ i₀ x}
    (hA : A' = A) (hB : B' = B) :
    S.PathContinuationChainGermWalk A' B' where
  length := W.length
  stateAt := W.stateAt
  stateAt_zero := W.stateAt_zero.trans hA.symm
  stateAt_length := W.stateAt_length.trans hB.symm
  moveAt := W.moveAt

/--
%%handwave
name:
  Terminal-germ walks preserve terminal germs
statement:
  The endpoints of a terminal-germ walk have locally agreeing terminal germs.
proof:
  Compose the local agreements along the finite walk.
-/
theorem terminalGerms_agree
    (W : S.PathContinuationChainGermWalk A B) :
    A.terminalGerm.LocallyAgreesWith B.terminalGerm := by
  have hprefix :
      ∀ n, n ≤ W.length →
        (W.stateAt 0).terminalGerm.LocallyAgreesWith
          (W.stateAt n).terminalGerm := by
    intro n hn
    induction n with
    | zero =>
        exact
          PathContinuationGerm.locallyAgreesWith_refl
            (W.stateAt 0).terminalGerm
    | succ n ih =>
        have hn_le : n ≤ W.length := by omega
        have hn_lt : n < W.length := by omega
        exact
          PathContinuationGerm.locallyAgreesWith_trans
            (ih hn_le)
            (W.moveAt n hn_lt).terminalGerms_agree
  have h := hprefix W.length le_rfl
  rw [W.stateAt_zero, W.stateAt_length] at h
  exact h

/-- Concatenate two terminal-germ walks. -/
def trans
    (W₁ : S.PathContinuationChainGermWalk A B)
    (W₂ : S.PathContinuationChainGermWalk B C) :
    S.PathContinuationChainGermWalk A C :=
  ofMove
    { terminalGerms_agree :=
        PathContinuationGerm.locallyAgreesWith_trans
          W₁.terminalGerms_agree W₂.terminalGerms_agree }

/-- Reverse a terminal-germ walk. -/
def symm
    (W : S.PathContinuationChainGermWalk A B) :
    S.PathContinuationChainGermWalk B A :=
  ofMove
    { terminalGerms_agree :=
        PathContinuationGerm.locallyAgreesWith_symm W.terminalGerms_agree }

variable {p : Path x₀ x}

/-- Splitting one segment as a one-step terminal-germ walk. -/
noncomputable def segmentSplit
    (C : S.PathContinuationChain x₀ i₀ p)
    (k : Fin C.length) (τ : unitInterval)
    (hτ_left : (C.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ C.parameterAt k.succ) :
    S.PathContinuationChainGermWalk
      (PathContinuationChainState.ofChain C)
      (PathContinuationChainState.ofChain
        (C.segmentSplitChain k τ hτ_left hτ_right)) :=
  ofMove
    { terminalGerms_agree :=
        C.segmentSplitChain_terminalGerms_agree k τ hτ_left hτ_right }

/-- Splitting at an arbitrary parameter as a one-step terminal-germ walk. -/
noncomputable def splitAtParameter
    (C : S.PathContinuationChain x₀ i₀ p)
    (τ : unitInterval) :
    S.PathContinuationChainGermWalk
      (PathContinuationChainState.ofChain C)
      (PathContinuationChainState.ofChain (C.splitAtParameterChain τ)) :=
  ofMove
    { terminalGerms_agree := C.splitAtParameterChain_terminalGerms_agree τ }

/--
Finite terminal-germ walk splitting at the first `m` sampled parameters of
another chain.
-/
noncomputable def splitFirstVerticesOf
    (C D : S.PathContinuationChain x₀ i₀ p) :
    ∀ m : ℕ,
      S.PathContinuationChainGermWalk
        (PathContinuationChainState.ofChain C)
        (PathContinuationChainState.ofChain
          (C.splitFirstVerticesOfChain D m))
  | 0 => PathContinuationChainGermWalk.refl (PathContinuationChainState.ofChain C)
  | m + 1 => by
      classical
      by_cases h : m < D.length + 1
      · let R := C.splitFirstVerticesOfChain D m
        simpa [PathContinuationChain.splitFirstVerticesOfChain, h, R] using
          (splitFirstVerticesOf C D m).trans
            (PathContinuationChainGermWalk.splitAtParameter
              R (D.parameterAt ⟨m, h⟩))
      · simpa [PathContinuationChain.splitFirstVerticesOfChain, h] using
          splitFirstVerticesOf C D m

/-- Finite terminal-germ walk splitting at every sampled parameter of another chain. -/
noncomputable def splitAllVerticesOf
    (C D : S.PathContinuationChain x₀ i₀ p) :
    S.PathContinuationChainGermWalk
      (PathContinuationChainState.ofChain C)
      (PathContinuationChainState.ofChain (C.splitAllVerticesOfChain D)) := by
  simpa [PathContinuationChain.splitAllVerticesOfChain] using
    splitFirstVerticesOf C D (D.length + 1)

end PathContinuationChainGermWalk

/--
%%handwave
name:
  Common aligned refinement for two chains on one path
statement:
  Any two finite continuation chains along the same path admit refinements
  whose subdivision parameters agree, and the original terminal germs locally
  agree with the corresponding refined terminal germs.
proof:
  Insert every sampled vertex of each chain into the other, then split the
  resulting chains until both parameter lists are the same sorted finite list.
  Endpoint chart insertions are justified by local transitions at the inserted
  vertices.  Segment splittings preserve the accumulated local expression, and
  the final parameter lists agree by sorted-list uniqueness.
-/
theorem exists_common_aligned_refinement_same_path
    (_htransitions : S.HasLocalTransitions)
    {x₀ : X} {i₀ : ι} (_hx₀ : x₀ ∈ S.domain i₀)
    {x : X} {p : Path x₀ x}
    (C D : S.PathContinuationChain x₀ i₀ p) :
    ∃ (C' D' : S.PathContinuationChain x₀ i₀ p),
      Nonempty
        (S.PathContinuationChainGermWalk
          (PathContinuationChainState.ofChain C)
          (PathContinuationChainState.ofChain C')) ∧
      Nonempty
        (S.PathContinuationChainGermWalk
          (PathContinuationChainState.ofChain D)
          (PathContinuationChainState.ofChain D')) ∧
      ∃ _hLength : C'.length = D'.length,
        ∀ n (hnC : n ≤ C'.length) (hnD : n ≤ D'.length),
          C'.parameterAt ⟨n, Nat.lt_succ_of_le hnC⟩ =
            D'.parameterAt ⟨n, Nat.lt_succ_of_le hnD⟩ := by
  classical
  let C' := C.splitAllVerticesOfChain D
  let D' := D.splitAllVerticesOfChain C
  refine
    ⟨C', D',
      ⟨PathContinuationChainGermWalk.splitAllVerticesOf C D⟩,
      ⟨PathContinuationChainGermWalk.splitAllVerticesOf D C⟩,
      ?_⟩
  have hLength : C'.length = D'.length := by
    simp [C', D']
    omega
  have hCperm :
      List.Perm C'.parameterList
        (D.parameterList ++ C.parameterList) := by
    simpa [C'] using C.splitAllVerticesOfChain_parameterList_perm D
  have hDperm :
      List.Perm D'.parameterList
        (C.parameterList ++ D.parameterList) := by
    simpa [D'] using D.splitAllVerticesOfChain_parameterList_perm C
  have hMiddle :
      List.Perm (D.parameterList ++ C.parameterList)
        (C.parameterList ++ D.parameterList) :=
    (List.perm_append_comm :
      List.Perm (D.parameterList ++ C.parameterList)
        (C.parameterList ++ D.parameterList))
  have hPerm : List.Perm C'.parameterList D'.parameterList :=
    hCperm.trans (hMiddle.trans hDperm.symm)
  refine ⟨hLength, ?_⟩
  exact C'.parameterAt_eq_of_parameterList_perm D' hPerm

/--
%%handwave
name:
  Same-path continuation chains have the same terminal germ
statement:
  Any two finite continuation chains along the same path have locally agreeing
  terminal germs.
proof:
  Refine the two subdivisions to a common subdivision.  On each common segment,
  both chains represent continuations through branches containing the same path
  image.  The local transition laws show that [the initialized accumulated branch expression agrees with the initial branch](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.initialTransitionProduct_localMap_eq)
  and that [each handoff preserves the accumulated branch expression](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.transitionProductAt_succ_localMap_eq).
  Induction over the common subdivision identifies the terminal germs.
-/
theorem exists_pathContinuationChainGermWalk_same_path
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (htransitions : S.HasLocalTransitions)
    {x₀ : X} {i₀ : ι} (hx₀ : x₀ ∈ S.domain i₀)
    {x : X} {p : Path x₀ x}
    (Cp Cq : S.PathContinuationChain x₀ i₀ p) :
    Nonempty
      (S.PathContinuationChainGermWalk
        (PathContinuationChainState.ofChain Cp)
        (PathContinuationChainState.ofChain Cq)) := by
  rcases
    S.exists_common_aligned_refinement_same_path
      htransitions hx₀ Cp Cq with
    ⟨Cp', Cq', ⟨Wleft⟩, ⟨Wright⟩, hLength, hParam⟩
  have hAligned :
      Cp'.toTerminalGerm.LocallyAgreesWith Cq'.toTerminalGerm :=
    Cp'.terminalGerms_agree_of_alignedSubdivision Cq' hLength hParam
  let Waligned :
      S.PathContinuationChainGermWalk
        (PathContinuationChainState.ofChain Cp')
        (PathContinuationChainState.ofChain Cq') :=
    PathContinuationChainGermWalk.ofMove
      { terminalGerms_agree := hAligned }
  exact ⟨Wleft.trans (Waligned.trans Wright.symm)⟩

/--
%%handwave
name:
  Homotopy-strip column move principle
statement:
  A branch-domain rectangle in a homotopy strip gives a terminal-germ walk
  between the two adjacent cut paths.
-/
def PathContinuationChainHomotopyStripColumnMovePrinciple
    {x₀ : X} {i₀ : ι}
    (chainAlong :
      ∀ {x : X} (p : Path x₀ x),
        S.PathContinuationChain x₀ i₀ p) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (i m : ℕ) →
      (∃ branch : ι,
        Set.Icc (t i) (t (i + 1)) ×ˢ
            Set.Icc (t m) (t (m + 1)) ⊆
          {z : unitInterval × unitInterval | F z ∈ S.domain branch}) →
      Nonempty
        (S.PathContinuationChainGermWalk
          (PathContinuationChainState.ofChain
            (chainAlong
              (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1)))))
          (PathContinuationChainState.ofChain
            (chainAlong
              (homotopyStripCutPath F (t i) (t (i + 1)) (t m)))))

/--
%%handwave
name:
  Homotopy-strip move principle
statement:
  Column moves across the rectangle subdivision of one strip give a
  terminal-germ walk from the lower row of the strip to the upper row.
-/
def PathContinuationChainHomotopyStripMovePrinciple
    {x₀ : X} {i₀ : ι}
    (chainAlong :
      ∀ {x : X} (p : Path x₀ x),
        S.PathContinuationChain x₀ i₀ p) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (∃ N, ∀ n ≥ N, t n = 1) →
      (i : ℕ) →
      (∀ m,
        ∃ branch : ι,
          Set.Icc (t i) (t (i + 1)) ×ˢ
              Set.Icc (t m) (t (m + 1)) ⊆
            {z : unitInterval × unitInterval | F z ∈ S.domain branch}) →
      Nonempty
        (S.PathContinuationChainGermWalk
          (PathContinuationChainState.ofChain (chainAlong (F.eval (t i))))
          (PathContinuationChainState.ofChain (chainAlong (F.eval (t (i + 1))))))

/--
%%handwave
name:
  Homotopy-grid move principle
statement:
  Strip moves across the rectangle subdivision of a homotopy square give a
  terminal-germ walk from the bottom path to the top path.
-/
def PathContinuationChainHomotopyGridMovePrinciple
    {x₀ : X} {i₀ : ι}
    (chainAlong :
      ∀ {x : X} (p : Path x₀ x),
        S.PathContinuationChain x₀ i₀ p) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (∃ N, ∀ n ≥ N, t n = 1) →
      (∀ n m,
        ∃ branch : ι,
          Set.Icc (t n) (t (n + 1)) ×ˢ
              Set.Icc (t m) (t (m + 1)) ⊆
            {z : unitInterval × unitInterval | F z ∈ S.domain branch}) →
      Nonempty
        (S.PathContinuationChainGermWalk
          (PathContinuationChainState.ofChain (chainAlong p))
          (PathContinuationChainState.ofChain (chainAlong q)))

/--
%%handwave
name:
  Finite column sweep
statement:
  Fix a homotopy \(H\), an increasing sequence
  \(t_0,t_1,\ldots\in[0,1]\), and a strip
  \([t_i,t_{i+1}]\times[0,1]\). If, for every \(m<N\), there is a terminal-germ
  walk from the cut at height \(t_{m+1}\) to the cut at height \(t_m\), then
  there is a terminal-germ walk from the cut at \(t_N\) to the cut at \(t_0\).
proof:
  Induct on \(N\). The case \(N=0\) is the constant walk. At \(N+1\), compose
  the given last-column walk from \(t_{N+1}\) to \(t_N\) with the inductively
  constructed walk from \(t_N\) to \(t_0\).
-/
theorem pathContinuationChainGermWalk_stripColumns
    {x₀ : X} {i₀ : ι}
    {chainAlong :
      ∀ {x : X} (p : Path x₀ x),
        S.PathContinuationChain x₀ i₀ p}
    {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (t : ℕ → unitInterval) (i : ℕ) :
    ∀ N : ℕ,
      (∀ m, m < N →
        Nonempty
          (S.PathContinuationChainGermWalk
            (PathContinuationChainState.ofChain
              (chainAlong
                (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1)))))
            (PathContinuationChainState.ofChain
              (chainAlong
                (homotopyStripCutPath F (t i) (t (i + 1)) (t m)))))) →
      Nonempty
        (S.PathContinuationChainGermWalk
          (PathContinuationChainState.ofChain
            (chainAlong
              (homotopyStripCutPath F (t i) (t (i + 1)) (t N))))
          (PathContinuationChainState.ofChain
            (chainAlong
              (homotopyStripCutPath F (t i) (t (i + 1)) (t 0)))))
  | 0, _ =>
      ⟨PathContinuationChainGermWalk.refl
        (PathContinuationChainState.ofChain
          (chainAlong
            (homotopyStripCutPath F (t i) (t (i + 1)) (t 0))))⟩
  | N + 1, hColumns => by
      rcases hColumns N (Nat.lt_succ_self N) with ⟨W₀⟩
      rcases
        pathContinuationChainGermWalk_stripColumns
          (chainAlong := chainAlong) (F := F) (t := t) (i := i) N
          (fun m hm => hColumns m (Nat.lt_trans hm (Nat.lt_succ_self N))) with
        ⟨W₁⟩
      exact ⟨W₀.trans W₁⟩

/--
%%handwave
name:
  Column moves imply strip moves
statement:
  Let \(H:p\simeq q\), let \(t_0=0\le t_1\le\cdots\) be eventually equal to
  \(1\), and choose a continuation chain along every row and cut path. If each
  rectangle in a fixed strip \([t_i,t_{i+1}]\times[0,1]\) supplies a
  terminal-germ walk between its adjacent cuts, then there is a terminal-germ
  walk from the row \(H(t_i,\cdot)\) to the row
  \(H(t_{i+1},\cdot)\).
proof:
  Choose \(N\) with \(t_N=1\), apply the column hypothesis for
  \(m=0,\ldots,N-1\), and compose the resulting walks. The cut at \(t_N=1\)
  is the first boundary row, while the cut at \(t_0=0\) is the second;
  transport the composed walk across these two path equalities.
-/
theorem pathContinuationChainHomotopyStripMovePrinciple_of_columnMovePrinciple
    {x₀ : X} {i₀ : ι}
    {chainAlong :
      ∀ {x : X} (p : Path x₀ x),
        S.PathContinuationChain x₀ i₀ p}
    (hColumn :
      S.PathContinuationChainHomotopyStripColumnMovePrinciple chainAlong) :
    S.PathContinuationChainHomotopyStripMovePrinciple chainAlong := by
  intro x p q F t ht0 htmono htEventually i hStrip
  rcases htEventually with ⟨N, hN⟩
  have hColumns :
      ∀ m, m < N →
        Nonempty
          (S.PathContinuationChainGermWalk
            (PathContinuationChainState.ofChain
              (chainAlong
                (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1)))))
            (PathContinuationChainState.ofChain
              (chainAlong
                (homotopyStripCutPath F (t i) (t (i + 1)) (t m))))) := by
    intro m _hm
    exact hColumn F t ht0 htmono i m (hStrip m)
  rcases
    pathContinuationChainGermWalk_stripColumns
      S (chainAlong := chainAlong) (F := F) (t := t) (i := i) N hColumns with
    ⟨W⟩
  have hcutStart :
      homotopyStripCutPath F (t i) (t (i + 1)) (t N) =
        F.eval (t i) := by
    rw [hN N le_rfl]
    simp
  have hStart :
      PathContinuationChainState.ofChain (chainAlong (F.eval (t i))) =
        PathContinuationChainState.ofChain
          (chainAlong
            (homotopyStripCutPath F (t i) (t (i + 1)) (t N))) :=
    (congrArg
      (fun r : Path x₀ x =>
        PathContinuationChainState.ofChain (chainAlong r)) hcutStart).symm
  have hcutEnd :
      homotopyStripCutPath F (t i) (t (i + 1)) (t 0) =
        F.eval (t (i + 1)) := by
    rw [ht0]
    simp
  have hEnd :
      PathContinuationChainState.ofChain (chainAlong (F.eval (t (i + 1)))) =
        PathContinuationChainState.ofChain
          (chainAlong
            (homotopyStripCutPath F (t i) (t (i + 1)) (t 0))) :=
    (congrArg
      (fun r : Path x₀ x =>
        PathContinuationChainState.ofChain (chainAlong r)) hcutEnd).symm
  exact ⟨W.cast hStart hEnd⟩

/--
%%handwave
name:
  Finite row sweep
statement:
  Fix a homotopy \(H\) and parameters \(t_0,t_1,\ldots\in[0,1]\). If, for
  every \(i<N\), there is a terminal-germ walk from the row
  \(H(t_i,\cdot)\) to \(H(t_{i+1},\cdot)\), then there is a terminal-germ walk
  from \(H(t_0,\cdot)\) to \(H(t_N,\cdot)\).
proof:
  Induct on \(N\). The case \(N=0\) is the constant walk; the successor case
  concatenates the walk through the first \(N\) rows with the given walk from
  row \(N\) to row \(N+1\).
-/
theorem pathContinuationChainGermWalk_rows
    {x₀ : X} {i₀ : ι}
    {chainAlong :
      ∀ {x : X} (p : Path x₀ x),
        S.PathContinuationChain x₀ i₀ p}
    {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (t : ℕ → unitInterval) :
    ∀ N : ℕ,
      (∀ i, i < N →
        Nonempty
          (S.PathContinuationChainGermWalk
            (PathContinuationChainState.ofChain (chainAlong (F.eval (t i))))
            (PathContinuationChainState.ofChain (chainAlong (F.eval (t (i + 1))))))) →
      Nonempty
        (S.PathContinuationChainGermWalk
          (PathContinuationChainState.ofChain (chainAlong (F.eval (t 0))))
          (PathContinuationChainState.ofChain (chainAlong (F.eval (t N)))))
  | 0, _ =>
      ⟨PathContinuationChainGermWalk.refl
        (PathContinuationChainState.ofChain (chainAlong (F.eval (t 0))))⟩
  | N + 1, hRows => by
      rcases
        pathContinuationChainGermWalk_rows
          (chainAlong := chainAlong) (F := F) (t := t) N
          (fun i hi => hRows i (Nat.lt_trans hi (Nat.lt_succ_self N))) with
        ⟨W₀⟩
      rcases hRows N (Nat.lt_succ_self N) with ⟨W₁⟩
      exact ⟨W₀.trans W₁⟩

/--
%%handwave
name:
  Strip moves imply grid moves
statement:
  Let \(H:p\simeq q\) and let
  \(t_0=0\le t_1\le\cdots\) be eventually equal to \(1\). If every horizontal
  strip of a rectangular subdivision admits a terminal-germ walk between its
  boundary rows, then the whole grid admits a terminal-germ walk from the
  chain along \(p\) to the chain along \(q\).
proof:
  Choose \(N\) with \(t_N=1\), obtain one walk for each of the first \(N\)
  strips, and concatenate them by the finite row sweep. Since
  \(H(t_0,\cdot)=p\) and \(H(t_N,\cdot)=q\), transport the resulting endpoint
  states to the prescribed boundary chains.
-/
theorem pathContinuationChainHomotopyGridMovePrinciple_of_stripMovePrinciple
    {x₀ : X} {i₀ : ι}
    {chainAlong :
      ∀ {x : X} (p : Path x₀ x),
        S.PathContinuationChain x₀ i₀ p}
    (hStrip :
      S.PathContinuationChainHomotopyStripMovePrinciple chainAlong) :
    S.PathContinuationChainHomotopyGridMovePrinciple chainAlong := by
  intro x p q F t ht0 htmono htEventually htRect
  have htEventually' : ∃ N, ∀ n ≥ N, t n = 1 := htEventually
  rcases htEventually with ⟨N, hN⟩
  have hRows :
      ∀ i, i < N →
        Nonempty
          (S.PathContinuationChainGermWalk
            (PathContinuationChainState.ofChain (chainAlong (F.eval (t i))))
            (PathContinuationChainState.ofChain (chainAlong (F.eval (t (i + 1)))))) := by
    intro i _hi
    exact hStrip F t ht0 htmono htEventually' i (fun m => htRect i m)
  rcases
    pathContinuationChainGermWalk_rows
      S (chainAlong := chainAlong) (F := F) (t := t) N hRows with
    ⟨W⟩
  have hevalStart : F.eval (t 0) = p := by
    rw [ht0]
    exact F.eval_zero
  have hStart :
      PathContinuationChainState.ofChain (chainAlong p) =
        PathContinuationChainState.ofChain (chainAlong (F.eval (t 0))) :=
    (congrArg
      (fun r : Path x₀ x =>
        PathContinuationChainState.ofChain (chainAlong r)) hevalStart).symm
  have hevalEnd : F.eval (t N) = q := by
    rw [hN N le_rfl]
    exact F.eval_one
  have hEnd :
      PathContinuationChainState.ofChain (chainAlong q) =
        PathContinuationChainState.ofChain (chainAlong (F.eval (t N))) :=
    (congrArg
      (fun r : Path x₀ x =>
        PathContinuationChainState.ofChain (chainAlong r)) hevalEnd).symm
  exact ⟨W.cast hStart hEnd⟩

/--
%%handwave
name:
  Decomposed homotopy-column terminal-germ witness
statement:
  If one homotopy rectangle lies in a single branch domain, then the two
  explicitly decomposed column paths obtained by going around the rectangle in
  the two possible ways admit continuation chains with locally agreeing
  terminal germs.
proof:
  Continue along the common prefix, change to the rectangle branch at the
  lower-left corner, and extend through the two rectangle boundary paths inside
  that branch.  The two rectangle continuations have the same terminal branch
  and accumulated transition.  Append the same subdivided suffix chain to both
  sides.
-/
theorem exists_homotopyStripColumn_decomposed_terminalGerm_agreement
    (htransitions : S.HasLocalTransitions)
    {x₀ : X} {i₀ : ι} (hx₀ : x₀ ∈ S.domain i₀)
    {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (a b r₀ r₁ : unitInterval)
    (hab : a ≤ b) (hr : r₀ ≤ r₁)
    {branch : ι}
    (hRect :
      Set.Icc a b ×ˢ Set.Icc r₀ r₁ ⊆
        {z : unitInterval × unitInterval | F z ∈ S.domain branch}) :
    ∃ (Ctop :
        S.PathContinuationChain x₀ i₀
          (homotopyStripColumnTopPath F a b r₀ r₁))
      (Cbottom :
        S.PathContinuationChain x₀ i₀
          (homotopyStripColumnBottomPath F a b r₀ r₁)),
      Ctop.toTerminalGerm.LocallyAgreesWith Cbottom.toTerminalGerm := by
  classical
  let pref : Path x₀ (F (a, r₀)) :=
    homotopyStripColumnPrefix F a r₀
  rcases
    S.exists_pathContinuationChain_of_localTransitions
      htransitions hx₀ pref with
    ⟨Cpref⟩
  have hLowerLeft : F (a, r₀) ∈ S.domain branch :=
    hRect ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hr⟩⟩
  let T : S.LocalTransition Cpref.terminalBranch branch (F (a, r₀)) :=
    Classical.choice
      (htransitions Cpref.terminalBranch branch (F (a, r₀))
        ⟨Cpref.endpoint_mem_terminalBranch, hLowerLeft⟩)
  let Cbranch : S.PathContinuationChain x₀ i₀ pref :=
    Cpref.terminalHandoffAlongChain T
  have hBR :
      ∀ u : unitInterval,
        homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
          S.domain Cbranch.terminalBranch := by
    intro u
    have hmem :
        homotopyRectangleBottomRightPath F a b r₀ r₁ u ∈
          S.domain branch :=
      homotopyRectangleBottomRightPath_mem_of_rect_subset
        F a b r₀ r₁ hab hr hRect u
    simpa [Cbranch] using hmem
  have hLT :
      ∀ u : unitInterval,
        homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
          S.domain Cbranch.terminalBranch := by
    intro u
    have hmem :
        homotopyRectangleLeftTopPath F a b r₀ r₁ u ∈
          S.domain branch :=
      homotopyRectangleLeftTopPath_mem_of_rect_subset
        F a b r₀ r₁ hab hr hRect u
    simpa [Cbranch] using hmem
  let CrectTop :
      S.PathContinuationChain x₀ i₀
        (pref.trans (homotopyRectangleBottomRightPath F a b r₀ r₁)) :=
    Cbranch.terminalExtensionAlongChain
      (homotopyRectangleBottomRightPath F a b r₀ r₁) hBR
  let CrectBottom :
      S.PathContinuationChain x₀ i₀
        (pref.trans (homotopyRectangleLeftTopPath F a b r₀ r₁)) :=
    Cbranch.terminalExtensionAlongChain
      (homotopyRectangleLeftTopPath F a b r₀ r₁) hLT
  let suffixPath : Path (F (b, r₁)) x :=
    homotopyStripColumnSuffix F b r₁
  rcases
    S.exists_pathContinuationChain_of_localTransitions
      htransitions CrectTop.endpoint_mem_terminalBranch suffixPath with
    ⟨DsuffixTop⟩
  have hRectBranch :
      CrectBottom.terminalBranch = CrectTop.terminalBranch := by
    simp [CrectTop, CrectBottom]
  let DsuffixBottom :
      S.PathContinuationChain (F (b, r₁)) CrectBottom.terminalBranch
        suffixPath :=
    DsuffixTop.castInitialBranch hRectBranch.symm
  have hRectTransition :
      CrectTop.terminalTransition = CrectBottom.terminalTransition := by
    simp [CrectTop, CrectBottom]
  have hSuffixBranch :
      DsuffixTop.terminalBranch = DsuffixBottom.terminalBranch := by
    simp [DsuffixBottom]
  have hSuffixTransition :
      DsuffixTop.terminalTransition = DsuffixBottom.terminalTransition := by
    simp [DsuffixBottom]
  let CtopRaw : S.PathContinuationChain x₀ i₀
      ((pref.trans (homotopyRectangleBottomRightPath F a b r₀ r₁)).trans
        suffixPath) :=
    CrectTop.appendSuffixChain DsuffixTop
  let CbottomRaw : S.PathContinuationChain x₀ i₀
      ((pref.trans (homotopyRectangleLeftTopPath F a b r₀ r₁)).trans
        suffixPath) :=
    CrectBottom.appendSuffixChain DsuffixBottom
  have hTopPath :
      ((pref.trans (homotopyRectangleBottomRightPath F a b r₀ r₁)).trans
          suffixPath) =
        homotopyStripColumnTopPath F a b r₀ r₁ := by
    rw [homotopyStripColumnTopPath_eq_prefix_rectangle_suffix]
  have hBottomPath :
      ((pref.trans (homotopyRectangleLeftTopPath F a b r₀ r₁)).trans
          suffixPath) =
        homotopyStripColumnBottomPath F a b r₀ r₁ := by
    rw [homotopyStripColumnBottomPath_eq_prefix_rectangle_suffix]
  let Ctop : S.PathContinuationChain x₀ i₀
      (homotopyStripColumnTopPath F a b r₀ r₁) :=
    CtopRaw.castPath hTopPath
  let Cbottom : S.PathContinuationChain x₀ i₀
      (homotopyStripColumnBottomPath F a b r₀ r₁) :=
    CbottomRaw.castPath hBottomPath
  have hRaw :
      CtopRaw.toTerminalGerm.LocallyAgreesWith
        CbottomRaw.toTerminalGerm := by
    exact
      PathContinuationChain.appendSuffixChain_terminalGerms_agree_of_terminalBranchData
        CrectTop CrectBottom DsuffixTop DsuffixBottom
        hRectTransition hSuffixBranch hSuffixTransition
  have hTopCast :
      CtopRaw.toTerminalGerm.LocallyAgreesWith Ctop.toTerminalGerm :=
    CtopRaw.castPath_terminalGerms_agree hTopPath
  have hBottomCast :
      CbottomRaw.toTerminalGerm.LocallyAgreesWith Cbottom.toTerminalGerm :=
    CbottomRaw.castPath_terminalGerms_agree hBottomPath
  exact
    ⟨Ctop, Cbottom,
      PathContinuationGerm.locallyAgreesWith_trans
        (PathContinuationGerm.locallyAgreesWith_symm hTopCast)
        (PathContinuationGerm.locallyAgreesWith_trans hRaw hBottomCast)⟩

/--
%%handwave
name:
  Cut-path reparameterization transfer for a homotopy column
statement:
  If the explicitly decomposed upper and lower column paths have locally
  agreeing terminal germs, then the corresponding public cut paths have
  locally agreeing terminal germs.
proof:
  This is the remaining one-dimensional path bookkeeping.  The decomposed top
  path differs from the raw upper cut path by merging two adjacent subpaths of
  the left edge; the decomposed bottom path differs from the raw lower cut path
  by merging two adjacent subpaths of the right edge after a common prefix.
  The endpoint cases of the public cut-path normalization add only constant
  initial or terminal pieces, which do not change the terminal germ.
-/
theorem exists_homotopyStripColumn_cutPath_terminalGerm_agreement_of_decomposed
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (_htransitions : S.HasLocalTransitions)
    {x₀ : X} {i₀ : ι} (_hx₀ : x₀ ∈ S.domain i₀)
    {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval)
    (_ht0 : t 0 = 0)
    (_htmono : Monotone t)
    (i m : ℕ)
    (CtopDecomposed :
      S.PathContinuationChain x₀ i₀
        (homotopyStripColumnTopPath
          F (t i) (t (i + 1)) (t m) (t (m + 1))))
    (CbottomDecomposed :
      S.PathContinuationChain x₀ i₀
        (homotopyStripColumnBottomPath
          F (t i) (t (i + 1)) (t m) (t (m + 1))))
    (hDecomposed :
      CtopDecomposed.toTerminalGerm.LocallyAgreesWith
        CbottomDecomposed.toTerminalGerm) :
    ∃ (Ctop :
        S.PathContinuationChain x₀ i₀
          (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1))))
      (Cbottom :
        S.PathContinuationChain x₀ i₀
          (homotopyStripCutPath F (t i) (t (i + 1)) (t m))),
      Ctop.toTerminalGerm.LocallyAgreesWith Cbottom.toTerminalGerm := by
  classical
  let a := t i
  let b := t (i + 1)
  let r₀ := t m
  let r₁ := t (m + 1)
  have hr : r₀ ≤ r₁ := _htmono (Nat.le_succ m)
  rcases
    exists_pathOrderReparamData_homotopyStripColumnTopPath_cutPath
      F a b r₀ r₁ hr with
    ⟨φTop, hTopData⟩
  rcases
    exists_pathOrderReparamData_homotopyStripColumnBottomPath_cutPath
      F a b r₀ r₁ hr with
    ⟨φBottom, hBottomData⟩
  let Ctop :
      S.PathContinuationChain x₀ i₀
        (homotopyStripCutPath F a b r₁) :=
    CtopDecomposed.reparametrizeOrder φTop hTopData
  let Cbottom :
      S.PathContinuationChain x₀ i₀
        (homotopyStripCutPath F a b r₀) :=
    CbottomDecomposed.reparametrizeOrder φBottom hBottomData
  have hTop :
      CtopDecomposed.toTerminalGerm.LocallyAgreesWith
        Ctop.toTerminalGerm :=
    CtopDecomposed.reparametrizeOrder_terminalGerms_agree φTop hTopData
  have hBottom :
      CbottomDecomposed.toTerminalGerm.LocallyAgreesWith
        Cbottom.toTerminalGerm :=
    CbottomDecomposed.reparametrizeOrder_terminalGerms_agree
      φBottom hBottomData
  refine ⟨?_, ?_, ?_⟩
  · simpa [a, b, r₁] using Ctop
  · simpa [a, b, r₀] using Cbottom
  · exact
      PathContinuationGerm.locallyAgreesWith_trans
        (PathContinuationGerm.locallyAgreesWith_symm hTop)
        (PathContinuationGerm.locallyAgreesWith_trans hDecomposed hBottom)

/--
%%handwave
name:
  Canonical terminal-germ witness for one homotopy column
statement:
  If one rectangle in the homotopy square lies in a single branch domain, then
  there are continuation chains over the two adjacent cut paths whose terminal
  germs locally agree.
proof:
  First build [continuation chains over the explicitly decomposed column paths whose terminal germs locally agree](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_homotopyStripColumn_decomposed_terminalGerm_agreement).
  Then use [the cut-path reparameterization transfer](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_homotopyStripColumn_cutPath_terminalGerm_agreement_of_decomposed)
  to pass from the decomposed paths to the public cut paths.
-/
theorem exists_homotopyStripColumn_canonical_terminalGerm_agreement
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (htransitions : S.HasLocalTransitions)
    {x₀ : X} {i₀ : ι} (hx₀ : x₀ ∈ S.domain i₀)
    {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval)
    (ht0 : t 0 = 0)
    (htmono : Monotone t)
    (i m : ℕ)
    (hRect :
      ∃ branch : ι,
        Set.Icc (t i) (t (i + 1)) ×ˢ
            Set.Icc (t m) (t (m + 1)) ⊆
          {z : unitInterval × unitInterval | F z ∈ S.domain branch}) :
    ∃ (Ctop :
        S.PathContinuationChain x₀ i₀
          (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1))))
      (Cbottom :
        S.PathContinuationChain x₀ i₀
          (homotopyStripCutPath F (t i) (t (i + 1)) (t m))),
      Ctop.toTerminalGerm.LocallyAgreesWith Cbottom.toTerminalGerm := by
  classical
  rcases hRect with ⟨branch, hRectBranch⟩
  have hab : t i ≤ t (i + 1) := htmono (Nat.le_succ i)
  have hr : t m ≤ t (m + 1) := htmono (Nat.le_succ m)
  rcases
    S.exists_homotopyStripColumn_decomposed_terminalGerm_agreement
      htransitions hx₀ F (t i) (t (i + 1)) (t m) (t (m + 1))
      hab hr (branch := branch) hRectBranch with
    ⟨CtopDecomposed, CbottomDecomposed, hDecomposed⟩
  exact
    S.exists_homotopyStripColumn_cutPath_terminalGerm_agreement_of_decomposed
      htransitions hx₀ F t ht0 htmono i m
      CtopDecomposed CbottomDecomposed hDecomposed

/--
%%handwave
name:
  Local transitions give column moves
statement:
  Local transition data identify the terminal germs obtained by crossing a
  small homotopy rectangle along its two boundary routes.
proof:
  First build [canonical continuations over the two adjacent cut paths whose terminal germs agree](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_homotopyStripColumn_canonical_terminalGerm_agreement).
  Then compare the chosen continuations with these canonical ones by
  [same-path comparison](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_pathContinuationChainGermWalk_same_path),
  and concatenate the three terminal-germ walks.
-/
theorem pathContinuationChainHomotopyStripColumnMovePrinciple_of_localTransitions
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (htransitions : S.HasLocalTransitions)
    {x₀ : X} {i₀ : ι} (hx₀ : x₀ ∈ S.domain i₀)
    (chainAlong :
      ∀ {x : X} (p : Path x₀ x),
        S.PathContinuationChain x₀ i₀ p) :
    S.PathContinuationChainHomotopyStripColumnMovePrinciple chainAlong := by
  intro x p q F t ht0 htmono i m hRect
  let ptop : Path x₀ x :=
    homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1))
  let pbottom : Path x₀ x :=
    homotopyStripCutPath F (t i) (t (i + 1)) (t m)
  rcases
    S.exists_homotopyStripColumn_canonical_terminalGerm_agreement
      htransitions hx₀ F t ht0 htmono i m hRect with
    ⟨Ctop, Cbottom, hCanonical⟩
  rcases
    S.exists_pathContinuationChainGermWalk_same_path
      htransitions hx₀ (chainAlong ptop) Ctop with
    ⟨Wtop⟩
  rcases
    S.exists_pathContinuationChainGermWalk_same_path
      htransitions hx₀ Cbottom (chainAlong pbottom) with
    ⟨Wbottom⟩
  let Wcanonical :
      S.PathContinuationChainGermWalk
        (PathContinuationChainState.ofChain Ctop)
        (PathContinuationChainState.ofChain Cbottom) :=
    PathContinuationChainGermWalk.ofMove
      { terminalGerms_agree := hCanonical }
  exact ⟨Wtop.trans (Wcanonical.trans Wbottom)⟩

/--
%%handwave
name:
  Local transitions give homotopy-grid moves
statement:
  Local transition data give a terminal-germ walk between the chosen
  continuation chains of endpoint-fixed homotopic paths.
proof:
  First prove column moves from local transition data, then sweep columns
  through each strip and strips through the whole homotopy square.
-/
theorem pathContinuationChainHomotopyGridMovePrinciple_of_localTransitions
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (htransitions : S.HasLocalTransitions)
    {x₀ : X} {i₀ : ι} (hx₀ : x₀ ∈ S.domain i₀)
    (chainAlong :
      ∀ {x : X} (p : Path x₀ x),
        S.PathContinuationChain x₀ i₀ p) :
    S.PathContinuationChainHomotopyGridMovePrinciple chainAlong :=
  S.pathContinuationChainHomotopyGridMovePrinciple_of_stripMovePrinciple
    (S.pathContinuationChainHomotopyStripMovePrinciple_of_columnMovePrinciple
      (S.pathContinuationChainHomotopyStripColumnMovePrinciple_of_localTransitions
        htransitions hx₀ chainAlong))

/--
%%handwave
name:
  Short paths in a terminal branch extend terminal germs
statement:
  If a finite continuation chain terminates in a branch and a short path starts
  at the endpoint and stays in that terminal branch domain, then continuing
  along the concatenated path has a terminal germ locally agreeing with the
  original terminal branch expression at the new endpoint.
proof:
  Use [an appended continuation chain with unchanged terminal branch expression](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.terminalExtensionAlongChain).
  The endpoint neighborhood is the terminal branch domain.
-/
theorem exists_terminalGerm_extensionAlong_pathIn_terminalBranch
    {x₀ : X} {i₀ : ι}
    {x y : X} {p : Path x₀ x}
    (C : S.PathContinuationChain x₀ i₀ p)
    (ρ : Path x y)
    (hρ : ∀ t : unitInterval, ρ t ∈ S.domain C.terminalBranch) :
    ∃ Cρ : S.PathContinuationChain x₀ i₀ (p.trans ρ),
      ∃ U : Set X,
        IsOpen U ∧ y ∈ U ∧
          U ⊆ C.toTerminalGerm.neighborhood ∩ Cρ.toTerminalGerm.neighborhood ∧
            ∀ z, z ∈ U →
              C.toTerminalGerm.localMap z = Cρ.toTerminalGerm.localMap z := by
  let Cρ : S.PathContinuationChain x₀ i₀ (p.trans ρ) :=
    C.terminalExtensionAlongChain ρ hρ
  refine
    ⟨Cρ, S.domain C.terminalBranch, S.domain_open C.terminalBranch,
      ?_, ?_, ?_⟩
  · simpa [ρ.target] using hρ 1
  · intro z hz
    constructor
    · exact hz
    · simpa [Cρ, PathContinuationChain.toTerminalGerm] using hz
  · intro z _hz
    simp [Cρ, PathContinuationGerm.localMap,
      PathContinuationChain.toTerminalGerm]

/--
%%handwave
name:
  Homotopic chains admit a terminal-germ walk
statement:
  For endpoint-fixed homotopic paths, any two finite continuation chains can
  be joined by a finite walk of elementary terminal-germ moves.
proof:
  Use [the rectangular branch-domain subdivision of the homotopy](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.pathHomotopic_exists_monotone_branch_grid).
  Each small rectangle gives an elementary move by replacing one side of the
  rectangle by the other while keeping the common prefix and suffix fixed.
  The finite grid walk is obtained by sweeping through the rectangles.
-/
theorem exists_pathContinuationChainGermWalk_of_homotopic
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (htransitions : S.HasLocalTransitions)
    {x₀ : X} {i₀ : ι} (hx₀ : x₀ ∈ S.domain i₀)
    {x : X} {p q : Path x₀ x}
    (hpq : Path.Homotopic p q)
    (Cp : S.PathContinuationChain x₀ i₀ p)
    (Cq : S.PathContinuationChain x₀ i₀ q) :
    Nonempty
      (S.PathContinuationChainGermWalk
        (PathContinuationChainState.ofChain Cp)
        (PathContinuationChainState.ofChain Cq)) := by
  classical
  let chainAlong :
      ∀ {x : X} (p : Path x₀ x),
        S.PathContinuationChain x₀ i₀ p :=
    fun {x} p ↦
      Classical.choice
        (S.exists_pathContinuationChain_of_localTransitions htransitions hx₀ p)
  rcases
    S.exists_pathContinuationChainGermWalk_same_path
      htransitions hx₀ Cp (chainAlong p) with
    ⟨Wleft⟩
  rcases S.pathHomotopic_exists_monotone_branch_grid hpq with
    ⟨t, ht0, htmono, htEventually, htRect⟩
  rcases
    S.pathContinuationChainHomotopyGridMovePrinciple_of_localTransitions
      htransitions hx₀ chainAlong hpq.some t ht0 htmono htEventually htRect with
    ⟨Wmiddle⟩
  rcases
    S.exists_pathContinuationChainGermWalk_same_path
      htransitions hx₀ (chainAlong q) Cq with
    ⟨Wright⟩
  exact ⟨Wleft.trans (Wmiddle.trans Wright)⟩

/--
%%handwave
name:
  Homotopic path-continuation chains have the same terminal germ
statement:
  If two paths with the same endpoints are endpoint-fixed homotopic, then any
  finite continuation chains along them have locally agreeing terminal germs.
proof:
  Subdivide the homotopy square so that each small rectangle lies in one
  branch domain and adjacent rectangles are related by local transitions.  The
  elementary square moves use the inverse and composite transition laws, and
  the analytic identity theorem identifies terminal germs after each move.
  Walking across the finite grid transports the terminal germ from one side of
  the homotopy to the other.
-/
theorem pathContinuationChain_terminalGerms_agree_of_homotopic
    [ComplexOneManifold X] [ComplexOneManifold Y]
    (htransitions : S.HasLocalTransitions)
    {x₀ : X} {i₀ : ι} (hx₀ : x₀ ∈ S.domain i₀)
    {x : X} {p q : Path x₀ x}
    (hpq : Path.Homotopic p q)
    (Cp : S.PathContinuationChain x₀ i₀ p)
    (Cq : S.PathContinuationChain x₀ i₀ q) :
    Cp.toTerminalGerm.LocallyAgreesWith Cq.toTerminalGerm := by
  rcases
    exists_pathContinuationChainGermWalk_of_homotopic
      (S := S) htransitions hx₀ hpq Cp Cq with
    ⟨W⟩
  simpa using W.terminalGerms_agree

/--
%%handwave
name:
  Single-valued continuation
statement:
  A single-valued continuation of a branch system is a global map that locally
  agrees with one of the local branches after applying a transition
  transformation.
-/
structure SingleValuedContinuation where
  /-- The global continued map. -/
  global : X → Y
  /-- Local agreement with transformed branches. -/
  local_agreement :
    ∀ x : X, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧
        ∃ (i : ι) (γ : G),
          U ⊆ S.domain i ∧
            ∀ y, y ∈ U → global y = S.act γ (S.branch i y)

/--
%%handwave
name:
  Coherent local continuation family
statement:
  A coherent local continuation family assigns to each point one local branch
  expression for the continued function, together with a neighborhood on which
  all nearby assigned expressions agree with it.
-/
structure CoherentLocalContinuationFamily where
  /-- The local branch assigned at each point. -/
  branchAt : X → ι
  /-- The transition element assigned at each point. -/
  transitionAt : X → G
  /-- The neighborhood on which the assigned local expression controls the continuation. -/
  neighborhoodAt : X → Set X
  /-- The assigned neighborhood is open. -/
  neighborhoodAt_open : ∀ x, IsOpen (neighborhoodAt x)
  /-- The assigned neighborhood contains its point. -/
  mem_neighborhoodAt : ∀ x, x ∈ neighborhoodAt x
  /-- The assigned neighborhood lies in the assigned branch domain. -/
  neighborhoodAt_subset_domain :
    ∀ x, neighborhoodAt x ⊆ S.domain (branchAt x)
  /-- Nearby assigned local expressions agree with the expression at the center point. -/
  coherent :
    ∀ x y, y ∈ neighborhoodAt x →
      S.act (transitionAt y) (S.branch (branchAt y) y) =
        S.act (transitionAt x) (S.branch (branchAt x) y)

namespace CoherentLocalContinuationFamily

variable {S}

/-- The global function determined by a coherent local continuation family. -/
def global (F : S.CoherentLocalContinuationFamily) : X → Y :=
  fun x ↦ S.act (F.transitionAt x) (S.branch (F.branchAt x) x)

/--
%%handwave
name:
  Coherent local continuation families glue to single-valued continuations
statement:
  A coherent family of local continuation germs determines a single-valued
  continuation.
proof:
  Define the global value at a point using that point's assigned local
  expression.  On the assigned neighborhood, coherence identifies all nearby
  pointwise definitions with the center expression.
-/
def toSingleValuedContinuation
    (F : S.CoherentLocalContinuationFamily) :
    S.SingleValuedContinuation where
  global := F.global
  local_agreement := by
    intro x
    refine
      ⟨F.neighborhoodAt x, F.neighborhoodAt_open x,
        F.mem_neighborhoodAt x, F.branchAt x, F.transitionAt x,
        F.neighborhoodAt_subset_domain x, ?_⟩
    intro y hy
    exact F.coherent x y hy

/--
%%handwave
name:
  Global function of the continuation induced by a coherent family
statement:
  The global function underlying the single-valued continuation associated to
  a coherent local family is the pointwise function determined by that family.
proof:
  This is the defining global field of the constructed continuation.
-/
@[simp]
theorem toSingleValuedContinuation_global
    (F : S.CoherentLocalContinuationFamily) :
    F.toSingleValuedContinuation.global = F.global :=
  rfl

end CoherentLocalContinuationFamily

namespace SingleValuedContinuation

variable {S}

/--
%%handwave
name:
  Single-valued continuations are holomorphic
statement:
  A single-valued continuation locally equal to transformed holomorphic
  branches is holomorphic.
proof:
  Near any point the continuation agrees with a composition of a holomorphic
  branch and a holomorphic target transformation.  Differentiability is local.
-/
theorem mdifferentiable (C : S.SingleValuedContinuation) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) C.global := by
  intro x
  rcases C.local_agreement x with
    ⟨U, hU_open, hxU, i, γ, hU_domain, hglobal_eq⟩
  have hbranchU :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (S.branch i) U :=
    (S.branch_holomorphicOn i).mono hU_domain
  have hformulaU :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        ((S.act γ) ∘ (S.branch i)) U :=
    (S.act_holomorphic γ).comp_mdifferentiableOn hbranchU
  have hformulaAt :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        ((S.act γ) ∘ (S.branch i)) x :=
    hformulaU.mdifferentiableAt (hU_open.mem_nhds hxU)
  have heq :
      C.global =ᶠ[𝓝 x] ((S.act γ) ∘ (S.branch i)) := by
    filter_upwards [hU_open.mem_nhds hxU] with y hy
    exact hglobal_eq y hy
  exact hformulaAt.congr_of_eventuallyEq heq

end SingleValuedContinuation

/--
%%handwave
name:
  Simply connected path choices give coherent local continuations
statement:
  Fix a basepoint, an initial branch at it, and for every endpoint choose a
  path and a finite continuation chain.  If terminal germs are invariant under
  endpoint-fixed homotopy and short paths inside terminal branch domains extend
  terminal germs, then the chosen terminal germs form a coherent local
  continuation family.
proof:
  At each point use the terminal branch domain of the chosen chain as the local
  neighborhood.  For a nearby point, connect it to the center by a short path
  inside a path-connected refinement of this domain.  Then [extend the center chain along that short path without changing its terminal expression](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_terminalGerm_extensionAlong_pathIn_terminalBranch),
  and compare the extension with the separately chosen chain by [endpoint-fixed homotopy invariance of terminal germs](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.pathContinuationChain_terminalGerms_agree_of_homotopic).
-/
theorem exists_coherentLocalContinuationFamily_of_chosen_path_chains
    [RiemannSurface X] [SimplyConnectedSpace X] [ComplexOneManifold Y]
    (htransitions : S.HasLocalTransitions)
    (x₀ : X) (i₀ : ι) (hx₀ : x₀ ∈ S.domain i₀)
    (pathTo : ∀ x : X, Path x₀ x)
    (chainTo :
      ∀ x : X, S.PathContinuationChain x₀ i₀ (pathTo x)) :
    Nonempty S.CoherentLocalContinuationFamily := by
  classical
  let W :
      ∀ x : X,
        SimplyConnectedOpenNeighborhood x
          (S.domain (chainTo x).terminalBranch) :=
    fun x ↦
      SimplyConnectedOpenNeighborhood.choose
        ((chainTo x).endpoint_mem_terminalBranch)
        (S.domain_open (chainTo x).terminalBranch)
  refine
    ⟨
      { branchAt := fun x ↦ (chainTo x).terminalBranch
        transitionAt := fun x ↦ (chainTo x).terminalTransition
        neighborhoodAt := fun x ↦ (W x).carrier
        neighborhoodAt_open := fun x ↦ (W x).carrier_open
        mem_neighborhoodAt := fun x ↦ (W x).mem_carrier
        neighborhoodAt_subset_domain := fun x ↦ (W x).carrier_subset
        coherent := ?_ }⟩
  intro x y hy
  let Cx := chainTo x
  let Cy := chainTo y
  let ρSubtype :
      Path (⟨x, (W x).mem_carrier⟩ : (W x).carrier) ⟨y, hy⟩ :=
    PathConnectedSpace.somePath
      (⟨x, (W x).mem_carrier⟩ : (W x).carrier) ⟨y, hy⟩
  let ρ : Path x y := ρSubtype.map continuous_subtype_val
  have hρ :
      ∀ t : unitInterval, ρ t ∈ S.domain Cx.terminalBranch := by
    intro t
    exact (W x).carrier_subset (ρSubtype t).property
  rcases
    S.exists_terminalGerm_extensionAlong_pathIn_terminalBranch
      Cx ρ hρ with
    ⟨Cρ, Uext, _hUext_open, hyUext, _hUext_subset, hEqExt⟩
  have hpq : Path.Homotopic ((pathTo x).trans ρ) (pathTo y) :=
    SimplyConnectedSpace.paths_homotopic ((pathTo x).trans ρ) (pathTo y)
  rcases
    S.pathContinuationChain_terminalGerms_agree_of_homotopic
      htransitions hx₀ hpq Cρ Cy with
    ⟨Uhom, _hUhom_open, hyUhom, _hUhom_subset, hEqHom⟩
  have hlocal :
      Cy.toTerminalGerm.localMap y = Cx.toTerminalGerm.localMap y :=
    (hEqHom y hyUhom).symm.trans (hEqExt y hyUext).symm
  simpa [Cx, Cy, PathContinuationGerm.localMap,
    PathContinuationChain.toTerminalGerm] using hlocal

/--
%%handwave
name:
  Simply connected monodromy gives a coherent continuation family
statement:
  On a simply connected Riemann surface, finite path-continuation
  chains with homotopy-invariant terminal germs determine a coherent local
  continuation family.
proof:
  Choose a basepoint and an initial branch.  For each point, choose a path from
  the basepoint and [a finite continuation chain](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_pathContinuationChain_of_localTransitions),
  and use its terminal germ as the local expression.  To compare nearby points,
  shrink the terminal neighborhood to a path-connected surface neighborhood,
  append the short local path, and use that [homotopic continuation chains have locally agreeing terminal germs](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.pathContinuationChain_terminalGerms_agree_of_homotopic).
  Since the surface is simply connected, endpoint-fixed homotopy is independent
  of the chosen path.
-/
theorem exists_coherentLocalContinuationFamily_of_simplyConnected_localTransitions
    [RiemannSurface X] [SimplyConnectedSpace X] [ComplexOneManifold Y]
    (htransitions : S.HasLocalTransitions) :
    Nonempty S.CoherentLocalContinuationFamily := by
  classical
  let x₀ : X := Classical.choice (PathConnectedSpace.nonempty : Nonempty X)
  rcases S.covers x₀ with ⟨i₀, hx₀⟩
  let pathTo : ∀ x : X, Path x₀ x :=
    fun x ↦ PathConnectedSpace.somePath x₀ x
  let chainTo :
      ∀ x : X, S.PathContinuationChain x₀ i₀ (pathTo x) :=
    fun x ↦
      Classical.choice
        (S.exists_pathContinuationChain_of_localTransitions
          htransitions hx₀ (pathTo x))
  exact
    S.exists_coherentLocalContinuationFamily_of_chosen_path_chains
      htransitions x₀ i₀ hx₀ pathTo chainTo

/--
%%handwave
name:
  Simply connected branch-continuation principle
statement:
  On a simply connected Riemann surface, a holomorphic local branch
  system with coherent local transitions has a single-valued continuation.
proof:
  First produce [a coherent local continuation family](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_coherentLocalContinuationFamily_of_simplyConnected_localTransitions)
  from path continuation and monodromy.  Then [coherent local expressions glue to a single-valued continuation](lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.CoherentLocalContinuationFamily.toSingleValuedContinuation).
-/
theorem exists_singleValuedContinuation_of_simplyConnected_localTransitions
    [RiemannSurface X] [SimplyConnectedSpace X] [ComplexOneManifold Y]
    (htransitions : S.HasLocalTransitions) :
    Nonempty S.SingleValuedContinuation := by
  exact
    (S.exists_coherentLocalContinuationFamily_of_simplyConnected_localTransitions
      htransitions).map
      CoherentLocalContinuationFamily.toSingleValuedContinuation

end HolomorphicLocalBranchSystem

end AnalyticContinuation

end JJMath
