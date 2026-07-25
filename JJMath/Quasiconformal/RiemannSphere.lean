import JJMath.Quasiconformal.ChangeOfVariables
import JJMath.Quasiconformal.Mobius
import JJMath.Quasiconformal.Surface

/-!
# Quasiconformal maps of the Riemann sphere

This file defines the sphere-level predicate by checking every representation
in the two standard complex charts.  Open partial homeomorphisms automatically
restrict a sphere homeomorphism to the planar domains on which a chosen source
and target chart are simultaneously valid.
-/

namespace JJMath

open Set
open scoped MatrixGroups Topology

namespace Quasiconformal

noncomputable section

/-- The two standard complex charts of the Riemann sphere. -/
inductive RiemannSphereChartIndex
  | finite
  | infinity
  deriving DecidableEq

/--
%%handwave
name:
  Exchange of the standard sphere charts
statement:
  The chart-index involution exchanges the finite standard chart with the
  reciprocal chart at infinity.
-/
def RiemannSphereChartIndex.swap :
    RiemannSphereChartIndex → RiemannSphereChartIndex
  | .finite => .infinity
  | .infinity => .finite

/--
%%handwave
name:
  Inversion conjugate of a sphere homeomorphism
statement:
  For a sphere homeomorphism $F$, its inversion conjugate is
  $\iota\circ F\circ\iota$, where $\iota(z)=z^{-1}$ in finite coordinates
  and exchanges $0$ with $\infty$.
-/
def riemannSphereInvConjugate
    (F : RiemannSphere ≃ₜ RiemannSphere) :
    RiemannSphere ≃ₜ RiemannSphere :=
  riemannSphereInvHomeomorph.trans
    (F.trans riemannSphereInvHomeomorph)

/--
%%handwave
name:
  Standard chart selected on the Riemann sphere
statement:
  Associate to the finite chart index the usual finite coordinate
  $z:\widehat{\mathbb C}\setminus\{\infty\}\to\mathbb C$, and to the
  reciprocal chart index the coordinate
  $z^{-1}:\widehat{\mathbb C}\setminus\{0\}\to\mathbb C$.
-/
def riemannSphereStandardChart :
    RiemannSphereChartIndex → OpenPartialHomeomorph RiemannSphere ℂ
  | .finite => riemannSphereFiniteChart
  | .infinity => riemannSphereInfinityChart

/--
%%handwave
name:
  Standard-chart representation of a sphere homeomorphism
statement:
  For a sphere homeomorphism $F$ and standard source and target charts
  $\phi_s,\phi_t$, define its planar coordinate representation by
  $$
    \phi_t\circ F\circ\phi_s^{-1}
  $$
  on its maximal planar source.
-/
def riemannSphereChartRepresentation
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (sourceChart targetChart : RiemannSphereChartIndex) :
    OpenPartialHomeomorph ℂ ℂ :=
  (riemannSphereStandardChart sourceChart).symm.trans
    (F.toOpenPartialHomeomorph.trans
      (riemannSphereStandardChart targetChart))

/--
%%handwave
name:
  Standard-chart representation of an inverse sphere homeomorphism
statement:
  For a sphere homeomorphism $F$ and standard charts $s,t$, the
  $(s,t)$-coordinate representation of $F^{-1}$ is the inverse of the
  $(t,s)$-coordinate representation of $F$.
proof:
  Invert the three-factor chart composition and reassociate it.
-/
theorem riemannSphereChartRepresentation_symm
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (sourceChart targetChart : RiemannSphereChartIndex) :
    riemannSphereChartRepresentation F.symm sourceChart targetChart =
      (riemannSphereChartRepresentation F targetChart sourceChart).symm := by
  simp only [riemannSphereChartRepresentation,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  rw [OpenPartialHomeomorph.trans_assoc]
  rw [Homeomorph.symm_toOpenPartialHomeomorph]
  simp

/--
%%handwave
name:
  Standard charts of an inversion conjugate
statement:
  Let $J(z)=z^{-1}$ on the Riemann sphere, with $J(0)=\infty$ and
  $J(\infty)=0$. For every sphere homeomorphism $F$ and standard-chart
  indices $s,t$, the $(s,t)$-coordinate representation of $J\circ F\circ J$
  is the coordinate representation of $F$ obtained by exchanging the finite
  and reciprocal charts at both ends.
proof:
  The reciprocal chart is spherical inversion followed by the finite chart.
  Expand both coordinate representations, use $J^2=\mathrm{id}$, and
  reassociate the partial-homeomorphism compositions.
-/
theorem riemannSphereChartRepresentation_invConjugate
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (sourceChart targetChart : RiemannSphereChartIndex) :
    riemannSphereChartRepresentation (riemannSphereInvConjugate F)
        sourceChart targetChart =
      riemannSphereChartRepresentation F sourceChart.swap targetChart.swap := by
  have hJ : riemannSphereInvHomeomorph.symm =
      riemannSphereInvHomeomorph := rfl
  have hJop : riemannSphereInvHomeomorph.toOpenPartialHomeomorph.symm =
      riemannSphereInvHomeomorph.toOpenPartialHomeomorph := by
    rw [← Homeomorph.symm_toOpenPartialHomeomorph]
    exact congrArg Homeomorph.toOpenPartialHomeomorph hJ
  have hJJ : riemannSphereInvHomeomorph.trans
      riemannSphereInvHomeomorph = Homeomorph.refl RiemannSphere := by
    ext z
    exact riemannSphereInv_inv z
  have hcancel (e : OpenPartialHomeomorph RiemannSphere ℂ) :
      riemannSphereInvHomeomorph.toOpenPartialHomeomorph.trans
        (riemannSphereInvHomeomorph.toOpenPartialHomeomorph.trans e) = e := by
    rw [← OpenPartialHomeomorph.trans_assoc,
      ← Homeomorph.trans_toOpenPartialHomeomorph, hJJ]
    simp
  cases sourceChart <;> cases targetChart <;>
    simp only [riemannSphereInvConjugate,
      RiemannSphereChartIndex.swap, riemannSphereChartRepresentation,
      riemannSphereStandardChart, riemannSphereInfinityChart,
      Homeomorph.trans_toOpenPartialHomeomorph,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, hJop, hcancel]

/--
%%handwave
name:
  Homeomorphism underlying a standard-chart representation
statement:
  The planar coordinate representation
  $\phi_t\circ F\circ\phi_s^{-1}$ of a sphere homeomorphism restricts to a
  homeomorphism between its planar source and target domains.
-/
def riemannSphereChartHomeomorph
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (sourceChart targetChart : RiemannSphereChartIndex) :
    (riemannSphereChartRepresentation F sourceChart targetChart).source ≃ₜ
      (riemannSphereChartRepresentation F sourceChart targetChart).target :=
  (riemannSphereChartRepresentation F sourceChart targetChart).toHomeomorphSourceTarget

/--
%%handwave
name:
  Normalized homeomorphism of the Riemann sphere
statement:
  A self-homeomorphism $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ is
  normalized when it fixes the three marked points $0$, $1$, and $\infty$.
-/
def IsNormalizedRiemannSphereHomeomorph
    (F : RiemannSphere ≃ₜ RiemannSphere) : Prop :=
  F ((0 : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere) ∧
    F ((1 : ℂ) : RiemannSphere) = ((1 : ℂ) : RiemannSphere) ∧
    F OnePoint.infty = OnePoint.infty

/--
%%handwave
name:
  Inversion conjugation preserves normalization
statement:
  If $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ fixes $0$, $1$, and
  $\infty$, then $J\circ F\circ J$, where $J(z)=z^{-1}$ on the sphere, fixes
  the same three points.
proof:
  Spherical inversion exchanges $0$ and $\infty$ and fixes $1$. Apply the
  corresponding fixed-point identity for $F$ in each case.
-/
theorem IsNormalizedRiemannSphereHomeomorph.invConjugate
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    IsNormalizedRiemannSphereHomeomorph (riemannSphereInvConjugate F) := by
  constructor
  · simp [riemannSphereInvConjugate, hF.2.2]
  constructor
  · simp [riemannSphereInvConjugate, hF.2.1]
  · simp [riemannSphereInvConjugate, hF.1]

/--
%%handwave
name:
  Finite source chart of a homeomorphism fixing infinity
statement:
  If a self-homeomorphism $F$ of $\widehat{\mathbb C}$ fixes $\infty$, then
  every $z\in\mathbb C$ belongs to the source of the finite-to-finite planar
  representation of $F$.
proof:
  A finite point could leave this source only by mapping to $\infty$.
  Injectivity and $F(\infty)=\infty$ would then identify that finite point
  with $\infty$, a contradiction.
-/
theorem riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hInf : F OnePoint.infty = OnePoint.infty) :
    (riemannSphereChartRepresentation F .finite .finite).source = Set.univ := by
  ext z
  simp only [Set.mem_univ, iff_true]
  simp [riemannSphereChartRepresentation, riemannSphereStandardChart]
  intro h
  have hz := F.injective (h.trans hInf.symm)
  exact OnePoint.coe_ne_infty z hz

/--
%%handwave
name:
  Finite target chart of a homeomorphism fixing infinity
statement:
  If a self-homeomorphism $F$ of $\widehat{\mathbb C}$ fixes $\infty$, then
  every $z\in\mathbb C$ belongs to the target of the finite-to-finite planar
  representation of $F$.
proof:
  If the preimage of a finite point were $\infty$, applying $F$ and using
  $F(\infty)=\infty$ would make that finite point equal to $\infty$.
-/
theorem riemannSphere_finiteChartRepresentation_target_eq_univ_of_map_infty
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hInf : F OnePoint.infty = OnePoint.infty) :
    (riemannSphereChartRepresentation F .finite .finite).target = Set.univ := by
  ext z
  simp only [Set.mem_univ, iff_true]
  simp [riemannSphereChartRepresentation, riemannSphereStandardChart]
  intro h
  have hback : F.symm ((z : ℂ) : RiemannSphere) = OnePoint.infty := h
  have hz := congrArg F hback
  simp [hInf] at hz

/--
%%handwave
name:
  Whole-plane finite chart of a homeomorphism fixing infinity
statement:
  A self-homeomorphism $F$ of $\widehat{\mathbb C}$ fixing $\infty$ induces
  a homeomorphism of the whole complex plane, obtained by using the finite
  chart in both source and target.
-/
def riemannSphereFiniteChartHomeomorph
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hInf : F OnePoint.infty = OnePoint.infty) : ℂ ≃ₜ ℂ :=
  OpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
    (riemannSphereChartRepresentation F .finite .finite)
    (riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty F hInf)
    (riemannSphere_finiteChartRepresentation_target_eq_univ_of_map_infty F hInf)

/--
%%handwave
name:
  Formula for the whole-plane finite chart
statement:
  If $F(\infty)=\infty$, then its whole-plane finite-chart homeomorphism is
  $$
    z\longmapsto \phi_{\mathrm{fin}}\bigl(F(z)\bigr),
  $$
  where a finite $z\in\mathbb C$ is viewed as a point of
  $\widehat{\mathbb C}$ and $\phi_{\mathrm{fin}}$ is the standard finite
  chart.
proof:
  Expand the whole-plane homeomorphism and the finite-to-finite chart
  representation, then evaluate the inverse finite chart at $z$.
-/
@[simp]
theorem riemannSphereFiniteChartHomeomorph_apply
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hInf : F OnePoint.infty = OnePoint.infty) (z : ℂ) :
    riemannSphereFiniteChartHomeomorph F hInf z =
      riemannSphereFiniteChart (F ((z : ℂ) : RiemannSphere)) := by
  simp [riemannSphereFiniteChartHomeomorph,
    riemannSphereChartRepresentation, riemannSphereStandardChart]

/--
%%handwave
name:
  Returning from the whole-plane finite chart
statement:
  If $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ fixes infinity, then for
  every $z\in\mathbb C$ the finite-chart value represents the original
  spherical value:
  $$
    \bigl[f(z)\bigr]=F([z]).
  $$
proof:
  Injectivity and $F(\infty)=\infty$ show that $F([z])$ is finite.  The
  finite chart and its inverse then cancel at that point.
-/
theorem coe_riemannSphereFiniteChartHomeomorph_apply
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hInf : F OnePoint.infty = OnePoint.infty) (z : ℂ) :
    ((riemannSphereFiniteChartHomeomorph F hInf z : ℂ) : RiemannSphere) =
      F ((z : ℂ) : RiemannSphere) := by
  rw [riemannSphereFiniteChartHomeomorph_apply]
  have hfinite : F ((z : ℂ) : RiemannSphere) ≠ OnePoint.infty := by
    intro h
    exact OnePoint.coe_ne_infty z (F.injective (h.trans hInf.symm))
  induction hval : F ((z : ℂ) : RiemannSphere) using OnePoint.rec with
  | infty => exact (hfinite hval).elim
  | coe w => simp

/--
%%handwave
name:
  Agreement of the two finite-chart representatives
statement:
  If $F(\infty)=\infty$, then the ambient representative of the
  finite-to-finite chart homeomorphism agrees at every $z\in\mathbb C$ with
  the induced whole-plane finite-chart homeomorphism.
proof:
  The finite-to-finite source is all of $\mathbb C$, so the ambient
  zero-extension always uses its inside-source branch.  Both sides then
  evaluate the same chart representation.
-/
theorem ambientMap_finiteChartHomeomorph_apply
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hInf : F OnePoint.infty = OnePoint.infty) (z : ℂ) :
    ambientMap (riemannSphereChartHomeomorph F .finite .finite) z =
      riemannSphereFiniteChartHomeomorph F hInf z := by
  let zSource :
      (riemannSphereChartRepresentation F .finite .finite).source :=
    ⟨z, by
      rw [riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
        F hInf]
      exact Set.mem_univ z⟩
  rw [ambientMap_apply _ zSource]
  exact riemannSphereFiniteChartHomeomorph_apply F hInf z |>.symm.trans rfl

/--
%%handwave
name:
  Finite chart of a normalized sphere homeomorphism fixes zero and one
statement:
  If $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ fixes $0$, $1$, and
  $\infty$, then the induced whole-plane homeomorphism fixes $0$ and $1$.
proof:
  Evaluate the finite-chart formula at the two fixed finite points.
-/
theorem IsNormalizedRiemannSphereHomeomorph.finiteChart_fixes_zero_one
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    riemannSphereFiniteChartHomeomorph F hF.2.2 0 = 0 ∧
      riemannSphereFiniteChartHomeomorph F hF.2.2 1 = 1 := by
  constructor
  · simp [hF.1]
  · simp [hF.2.1]

/--
%%handwave
name:
  Reciprocal source chart of a homeomorphism fixing zero
statement:
  If a self-homeomorphism $F$ of $\widehat{\mathbb C}$ fixes $0$, then every
  reciprocal coordinate $z\in\mathbb C$ belongs to the source of the
  reciprocal-to-reciprocal planar representation of $F$.
proof:
  The inverse reciprocal chart never represents $0$. If its image under $F$
  were $0$, injectivity and $F(0)=0$ would identify it with $0$, which is
  impossible after applying spherical inversion.
-/
theorem riemannSphere_infinityChartRepresentation_source_eq_univ_of_map_zero
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hZero : F ((0 : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere)) :
    (riemannSphereChartRepresentation F .infinity .infinity).source =
      Set.univ := by
  ext z
  simp only [Set.mem_univ, iff_true]
  simp [riemannSphereChartRepresentation, riemannSphereStandardChart]
  intro h
  have heq := F.injective (h.trans hZero.symm)
  have hback := congrArg riemannSphereInv heq
  exact OnePoint.coe_ne_infty z (by simpa using hback)

/--
%%handwave
name:
  Reciprocal target chart of a homeomorphism fixing zero
statement:
  If a self-homeomorphism $F$ of $\widehat{\mathbb C}$ fixes $0$, then every
  reciprocal coordinate belongs to the target of its
  reciprocal-to-reciprocal planar representation.
proof:
  If the inverse image of an inverse-reciprocal point were $0$, applying $F$
  and then spherical inversion would identify a finite point with infinity.
-/
theorem riemannSphere_infinityChartRepresentation_target_eq_univ_of_map_zero
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hZero : F ((0 : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere)) :
    (riemannSphereChartRepresentation F .infinity .infinity).target =
      Set.univ := by
  ext z
  simp only [Set.mem_univ, iff_true]
  simp [riemannSphereChartRepresentation, riemannSphereStandardChart]
  intro h
  have heq := congrArg F h
  have hback := congrArg riemannSphereInv heq
  exact OnePoint.coe_ne_infty z (by simpa [hZero] using hback)

/--
%%handwave
name:
  Whole-plane reciprocal chart of a homeomorphism fixing zero
statement:
  A self-homeomorphism $F$ of $\widehat{\mathbb C}$ fixing $0$ induces a
  homeomorphism of the whole complex plane by using reciprocal coordinates
  in both source and target.
-/
def riemannSphereInfinityChartHomeomorph
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hZero : F ((0 : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere)) :
    ℂ ≃ₜ ℂ :=
  OpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
    (riemannSphereChartRepresentation F .infinity .infinity)
    (riemannSphere_infinityChartRepresentation_source_eq_univ_of_map_zero
      F hZero)
    (riemannSphere_infinityChartRepresentation_target_eq_univ_of_map_zero
      F hZero)

/--
%%handwave
name:
  Formula for the whole-plane reciprocal chart
statement:
  If $F(0)=0$, its whole-plane reciprocal-chart homeomorphism is
  $$
    z\longmapsto\phi_\infty\bigl(F(\phi_\infty^{-1}(z))\bigr),
  $$
  where $\phi_\infty$ is the reciprocal standard chart.
proof:
  Expand the whole-plane homeomorphism and evaluate the reciprocal source and
  target charts.
-/
@[simp]
theorem riemannSphereInfinityChartHomeomorph_apply
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hZero : F ((0 : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere))
    (z : ℂ) :
    riemannSphereInfinityChartHomeomorph F hZero z =
      riemannSphereInfinityChart
        (F (riemannSphereInfinityChart.symm z)) := by
  simp [riemannSphereInfinityChartHomeomorph,
    riemannSphereChartRepresentation, riemannSphereStandardChart]

/--
%%handwave
name:
  Finite chart of an inversion conjugate
statement:
  Let $F$ fix $0$, $1$, and $\infty$, let $J(z)=z^{-1}$ on the Riemann
  sphere, and put $G=J\circ F\circ J$. If $f_\infty$ is the whole-plane
  reciprocal-chart representative of $F$, then the whole-plane finite-chart
  representative of $G$ equals $f_\infty$ pointwise.
proof:
  Expand both chart formulas. The inverse reciprocal source chart is
  spherical inversion of the finite point, and the reciprocal target chart
  is spherical inversion followed by the finite chart.
-/
theorem riemannSphereFiniteChartHomeomorph_invConjugate_apply
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F) (z : ℂ) :
    riemannSphereFiniteChartHomeomorph (riemannSphereInvConjugate F)
        hF.invConjugate.2.2 z =
      riemannSphereInfinityChartHomeomorph F hF.1 z := by
  rw [riemannSphereFiniteChartHomeomorph_apply,
    riemannSphereInfinityChartHomeomorph_apply]
  simp [riemannSphereInvConjugate, riemannSphereInfinityChart,
    riemannSphereInvHomeomorph]

/--
%%handwave
name:
  Returning from the whole-plane reciprocal chart
statement:
  If $F(0)=0$, then the inverse reciprocal chart of the reciprocal-coordinate
  value at $z$ is the original spherical value:
  $$
    \phi_\infty^{-1}(g(z))=F(\phi_\infty^{-1}(z)).
  $$
proof:
  The source-domain theorem shows that the spherical value lies in the
  reciprocal chart. Apply the chart's inverse identity.
-/
theorem riemannSphereInfinityChart_symm_riemannSphereInfinityChartHomeomorph_apply
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hZero : F ((0 : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere))
    (z : ℂ) :
    riemannSphereInfinityChart.symm
        (riemannSphereInfinityChartHomeomorph F hZero z) =
      F (riemannSphereInfinityChart.symm z) := by
  rw [riemannSphereInfinityChartHomeomorph_apply]
  apply riemannSphereInfinityChart.left_inv
  have hz : z ∈
      (riemannSphereChartRepresentation F .infinity .infinity).source := by
    rw [riemannSphere_infinityChartRepresentation_source_eq_univ_of_map_zero
      F hZero]
    exact Set.mem_univ z
  simpa [riemannSphereChartRepresentation, riemannSphereStandardChart]
    using hz

/--
%%handwave
name:
  Agreement of reciprocal-chart representatives
statement:
  If $F(0)=0$, the ambient representative of its reciprocal-to-reciprocal
  chart homeomorphism agrees everywhere with its induced whole-plane
  reciprocal-chart homeomorphism.
proof:
  The reciprocal chart representation has source all of $\mathbb C$, so the
  ambient zero-extension always takes its inside-source branch.
-/
theorem ambientMap_infinityChartHomeomorph_apply
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hZero : F ((0 : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere))
    (z : ℂ) :
    ambientMap (riemannSphereChartHomeomorph F .infinity .infinity) z =
      riemannSphereInfinityChartHomeomorph F hZero z := by
  let zSource :
      (riemannSphereChartRepresentation F .infinity .infinity).source :=
    ⟨z, by
      rw [riemannSphere_infinityChartRepresentation_source_eq_univ_of_map_zero
        F hZero]
      exact Set.mem_univ z⟩
  rw [ambientMap_apply _ zSource]
  exact riemannSphereInfinityChartHomeomorph_apply F hZero z |>.symm.trans rfl

/--
%%handwave
name:
  Reciprocal chart of a normalized sphere homeomorphism fixes zero and one
statement:
  If $F$ fixes $0$, $1$, and $\infty$, then its whole-plane reciprocal-chart
  homeomorphism fixes $0$ and $1$.
proof:
  Reciprocal coordinate $0$ represents $\infty$, while reciprocal coordinate
  $1$ represents $1$. Evaluate the chart formula using the corresponding
  fixed-point identities.
-/
theorem IsNormalizedRiemannSphereHomeomorph.infinityChart_fixes_zero_one
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    riemannSphereInfinityChartHomeomorph F hF.1 0 = 0 ∧
      riemannSphereInfinityChartHomeomorph F hF.1 1 = 1 := by
  constructor
  · simp [hF.2.2]
  · simp [hF.2.1]

/--
%%handwave
name:
  Quantitative quasiconformality on the Riemann sphere
statement:
  A homeomorphism $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ is
  $K$-quasiconformal if every planar representation obtained from the finite
  and reciprocal standard charts is an orientation-preserving local
  $W^{1,2}$ homeomorphism whose weak differential satisfies
  $$
  \|DF(z)\|_{\mathrm{op}}^2\leq K\operatorname{Jac}F(z)
  $$
  almost everywhere on its planar source domain, with $K\geq1$.
-/
def IsKQuasiconformalRiemannSphere
    (K : ℝ) (F : RiemannSphere ≃ₜ RiemannSphere) : Prop :=
  ∀ sourceChart targetChart : RiemannSphereChartIndex,
    IsKQuasiconformalBetween K
      (riemannSphereChartHomeomorph F sourceChart targetChart)

/--
%%handwave
name:
  A spherical quasiconformal constant is at least one
statement:
  If a sphere homeomorphism is $K$-quasiconformal in standard charts, then
  $1\leq K$.
proof:
  Apply the lower-bound clause in the planar quasiconformal definition to the
  finite-source, finite-target chart representation.
-/
theorem IsKQuasiconformalRiemannSphere.one_le
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (h : IsKQuasiconformalRiemannSphere K F) : 1 ≤ K := by
  exact (h .finite .finite).1

/--
%%handwave
name:
  Standard-chart criterion for spherical quasiconformality
statement:
  If a homeomorphism $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ is
  $K$-quasiconformal in every pair of the finite and reciprocal standard
  charts, then it is $K$-quasiconformal.
proof:
  The complex chart selected at a finite point is the finite chart, and the
  chart selected at infinity is the reciprocal chart. Thus every
  point-selected coordinate representation is one of the four assumed
  standard-chart representations.
-/
theorem IsKQuasiconformalRiemannSphere.toRiemannSurfaces
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsKQuasiconformalRiemannSphere K F) :
    IsKQuasiconformalBetweenRiemannSurfaces K F := by
  refine ⟨hF.one_le, ?_⟩
  intro x y
  induction x using OnePoint.rec with
  | infty =>
      induction y using OnePoint.rec with
      | infty =>
          change IsKQuasiconformalBetween K
            (((chartAt ℂ (OnePoint.infty : RiemannSphere)).symm.trans
              (F.toOpenPartialHomeomorph.trans
                (chartAt ℂ (OnePoint.infty : RiemannSphere)))).toHomeomorphSourceTarget)
          rw [chartAt_riemannSphere_infty]
          simpa [riemannSphereChartHomeomorph,
            riemannSphereChartRepresentation,
            riemannSphereStandardChart] using hF .infinity .infinity
      | coe w =>
          change IsKQuasiconformalBetween K
            (((chartAt ℂ (OnePoint.infty : RiemannSphere)).symm.trans
              (F.toOpenPartialHomeomorph.trans
                (chartAt ℂ (w : RiemannSphere)))).toHomeomorphSourceTarget)
          rw [chartAt_riemannSphere_infty, chartAt_riemannSphere_coe]
          simpa [riemannSphereChartHomeomorph,
            riemannSphereChartRepresentation,
            riemannSphereStandardChart] using hF .infinity .finite
  | coe z =>
      induction y using OnePoint.rec with
      | infty =>
          change IsKQuasiconformalBetween K
            (((chartAt ℂ (z : RiemannSphere)).symm.trans
              (F.toOpenPartialHomeomorph.trans
                (chartAt ℂ (OnePoint.infty : RiemannSphere)))).toHomeomorphSourceTarget)
          rw [chartAt_riemannSphere_coe, chartAt_riemannSphere_infty]
          simpa [riemannSphereChartHomeomorph,
            riemannSphereChartRepresentation,
            riemannSphereStandardChart] using hF .finite .infinity
      | coe w =>
          change IsKQuasiconformalBetween K
            (((chartAt ℂ (z : RiemannSphere)).symm.trans
              (F.toOpenPartialHomeomorph.trans
                (chartAt ℂ (w : RiemannSphere)))).toHomeomorphSourceTarget)
          rw [chartAt_riemannSphere_coe, chartAt_riemannSphere_coe]
          simpa [riemannSphereChartHomeomorph,
            riemannSphereChartRepresentation,
            riemannSphereStandardChart] using hF .finite .finite

/--
%%handwave
name:
  Spherical quasiconformality gives the standard-chart conditions
statement:
  If a sphere homeomorphism is $K$-quasiconformal, then all four
  representations in the finite and reciprocal standard charts are planar
  $K$-quasiconformal maps.
proof:
  Evaluate the chartwise surface condition at the finite point $0$ to
  select the finite chart and at $\infty$ to select the reciprocal chart.
-/
theorem IsKQuasiconformalBetweenRiemannSurfaces.toRiemannSphere
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsKQuasiconformalBetweenRiemannSurfaces K F) :
    IsKQuasiconformalRiemannSphere K F := by
  intro sourceChart targetChart
  cases sourceChart <;> cases targetChart
  · have h := hF.2 ((0 : ℂ) : RiemannSphere) ((0 : ℂ) : RiemannSphere)
    change IsKQuasiconformalBetween K
      (((chartAt ℂ ((0 : ℂ) : RiemannSphere)).symm.trans
        (F.toOpenPartialHomeomorph.trans
          (chartAt ℂ ((0 : ℂ) : RiemannSphere)))).toHomeomorphSourceTarget) at h
    rw [chartAt_riemannSphere_coe] at h
    simpa [riemannSphereChartHomeomorph,
      riemannSphereChartRepresentation,
      riemannSphereStandardChart] using h
  · have h :=
      hF.2 ((0 : ℂ) : RiemannSphere) (OnePoint.infty : RiemannSphere)
    change IsKQuasiconformalBetween K
      (((chartAt ℂ ((0 : ℂ) : RiemannSphere)).symm.trans
        (F.toOpenPartialHomeomorph.trans
          (chartAt ℂ (OnePoint.infty : RiemannSphere)))).toHomeomorphSourceTarget) at h
    rw [chartAt_riemannSphere_coe, chartAt_riemannSphere_infty] at h
    simpa [riemannSphereChartHomeomorph,
      riemannSphereChartRepresentation,
      riemannSphereStandardChart] using h
  · have h :=
      hF.2 (OnePoint.infty : RiemannSphere) ((0 : ℂ) : RiemannSphere)
    change IsKQuasiconformalBetween K
      (((chartAt ℂ (OnePoint.infty : RiemannSphere)).symm.trans
        (F.toOpenPartialHomeomorph.trans
          (chartAt ℂ ((0 : ℂ) : RiemannSphere)))).toHomeomorphSourceTarget) at h
    rw [chartAt_riemannSphere_infty, chartAt_riemannSphere_coe] at h
    simpa [riemannSphereChartHomeomorph,
      riemannSphereChartRepresentation,
      riemannSphereStandardChart] using h
  · have h :=
      hF.2 (OnePoint.infty : RiemannSphere) (OnePoint.infty : RiemannSphere)
    change IsKQuasiconformalBetween K
      (((chartAt ℂ (OnePoint.infty : RiemannSphere)).symm.trans
        (F.toOpenPartialHomeomorph.trans
          (chartAt ℂ (OnePoint.infty : RiemannSphere)))).toHomeomorphSourceTarget) at h
    rw [chartAt_riemannSphere_infty] at h
    simpa [riemannSphereChartHomeomorph,
      riemannSphereChartRepresentation,
      riemannSphereStandardChart] using h

/--
%%handwave
name:
  Inversion conjugation preserves spherical quasiconformality
statement:
  If $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ is
  $K$-quasiconformal, then $J\circ F\circ J$, where $J(z)=z^{-1}$ on the
  sphere, is also $K$-quasiconformal.
proof:
  In every standard-chart pair, conjugation by $J$ merely exchanges the
  finite and reciprocal source and target charts. Apply the corresponding
  chartwise quasiconformality assertion for $F$.
-/
theorem IsKQuasiconformalRiemannSphere.invConjugate
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsKQuasiconformalRiemannSphere K F) :
    IsKQuasiconformalRiemannSphere K (riemannSphereInvConjugate F) := by
  intro sourceChart targetChart
  rw [riemannSphereChartHomeomorph,
    riemannSphereChartRepresentation_invConjugate]
  exact hF sourceChart.swap targetChart.swap

/--
%%handwave
name:
  Inverse of a normalized sphere homeomorphism
statement:
  If a self-homeomorphism of $\widehat{\mathbb C}$ fixes $0$, $1$, and
  $\infty$, then its inverse fixes the same three points.
proof:
  Apply the homeomorphism to each desired identity and use the corresponding
  fixed-point identity for the original map.
-/
theorem IsNormalizedRiemannSphereHomeomorph.symm
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    IsNormalizedRiemannSphereHomeomorph F.symm := by
  constructor
  · apply F.injective
    simpa using hF.1.symm
  constructor
  · apply F.injective
    simpa using hF.2.1.symm
  · apply F.injective
    simpa using hF.2.2.symm

/--
%%handwave
name:
  Reciprocal coordinate identity for a normalized inverse
statement:
  Let $F$ be a normalized sphere homeomorphism, let $f$ be its finite-chart
  representative, and let $g$ be the reciprocal-chart representative of
  $F^{-1}$. For every $x\in\mathbb C\setminus\{0\}$,
  $$
    g\bigl(f(x)^{-1}\bigr)=x^{-1}.
  $$
proof:
  The reciprocal coordinate $f(x)^{-1}$ represents the spherical point
  $F(x)$. Apply $F^{-1}$ and return to reciprocal coordinates.
-/
theorem infinityChartHomeomorph_symm_apply_inv_finiteChartHomeomorph
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F) {x : ℂ} (hx : x ≠ 0) :
    riemannSphereInfinityChartHomeomorph F.symm hF.symm.1
        (riemannSphereFiniteChartHomeomorph F hF.2.2 x)⁻¹ = x⁻¹ := by
  let f := riemannSphereFiniteChartHomeomorph F hF.2.2
  have hcoe : (f x : RiemannSphere) = F (x : RiemannSphere) :=
    coe_riemannSphereFiniteChartHomeomorph_apply F hF.2.2 x
  have hy : f x ≠ 0 := by
    intro hy
    have heq : F (x : RiemannSphere) =
        F ((0 : ℂ) : RiemannSphere) := by
      rw [← hcoe, hy, hF.1]
    have hxeq := F.injective heq
    exact hx (by simpa using hxeq)
  rw [riemannSphereInfinityChartHomeomorph_apply]
  rw [riemannSphereInfinityChart_symm_apply,
    riemannSphereInv_coe_of_ne_zero (inv_ne_zero hy), inv_inv]
  rw [hcoe, F.symm_apply_apply]
  exact riemannSphereInfinityChart_coe_of_ne_zero hx

/--
%%handwave
name:
  Inverse of a quasiconformal sphere homeomorphism
statement:
  If $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ is
  $K$-quasiconformal in the standard charts, then $F^{-1}$ is also
  $K$-quasiconformal.
proof:
  The $(s,t)$-coordinate representation of $F^{-1}$ is the inverse of the
  $(t,s)$-coordinate representation of $F$. Apply the [planar inverse theorem](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.symm) in every pair of standard charts.
-/
theorem IsKQuasiconformalRiemannSphere.symm
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsKQuasiconformalRiemannSphere K F) :
    IsKQuasiconformalRiemannSphere K F.symm := by
  intro sourceChart targetChart
  change IsKQuasiconformalBetween K
    ((riemannSphereChartRepresentation F.symm sourceChart
      targetChart).toHomeomorphSourceTarget)
  rw [riemannSphereChartRepresentation_symm]
  exact (hF targetChart sourceChart).symm

/--
%%handwave
name:
  Projective representative of spherical inversion
statement:
  Define the projective matrix
  $$
    J=\begin{pmatrix}0&1\\1&0\end{pmatrix},
  $$
  whose action on $\widehat{\mathbb C}$ exchanges $0$ and $\infty$ and sends
  each nonzero finite point $z$ to $z^{-1}$.
-/
def standardChartInversionRepresentative : MobiusRepresentative :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(0 : ℂ), 1; 1, 0] (by simp [Matrix.det_fin_two])

end

end Quasiconformal

end JJMath
