import JJMath.Uniformization.AnnularLogarithm
import JJMath.Uniformization.GlobalHolomorphicPrimitive
import JJMath.Uniformization.PuncturedAngularForm

/-!
# The residue of the Green conjugate differential

This file computes the local cohomology class of the conjugate differential
of a Green potential.  In a pole coordinate, the distinguished holomorphic
branch factors as a simple zero times a nonvanishing holomorphic function.
The latter has a single-valued logarithm after shrinking the coordinate disk;
the only remaining transition is therefore the annular logarithm transition.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

open JJMath.Manifold

noncomputable section

attribute [local instance] finrank_real_complex_fact'

local instance greenResidue_isScalarTowerRealComplexComplex :
    IsScalarTower ℝ ℂ ℂ := IsScalarTower.right

/--
%%handwave
name:
  A nonvanishing holomorphic germ admits a local logarithm
statement:
  Let \(A\) be holomorphic on \(B(z_0,r)\), with \(r>0\) and
  \(A(z_0)\ne0\).  There are \(0<R<r\) and a holomorphic function \(B\) on
  \(B(z_0,R)\) such that
  \[
    e^{B(z)}=A(z),\qquad \operatorname{Re}B(z)=\log|A(z)|.
  \]
proof:
  By continuity, after shrinking the ball either \(A\) or \(-A\) takes values
  in the slit plane.  In the first case use the principal logarithm.  In the
  second use \(\log(-A)+\pi i\); its exponential is \(A\), and the added term
  is purely imaginary.
-/
theorem exists_ball_holomorphicLog_of_differentiableOn
    {A : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hA : DifferentiableOn ℂ A (Metric.ball z₀ r))
    (hA_ne : A z₀ ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ R < r ∧
      ∃ B : ℂ → ℂ,
        DifferentiableOn ℂ B (Metric.ball z₀ R) ∧
          ∀ z ∈ Metric.ball z₀ R,
            Complex.exp (B z) = A z ∧
              (B z).re = Real.log ‖A z‖ := by
  have hzball : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hAat : DifferentiableAt ℂ A z₀ :=
    hA.differentiableAt (Metric.isOpen_ball.mem_nhds hzball)
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hA_ne with hslit | hnegslit
  · have hpre : A ⁻¹' Complex.slitPlane ∈ 𝓝 z₀ :=
      hAat.continuousAt.preimage_mem_nhds
        (Complex.isOpen_slitPlane.mem_nhds hslit)
    have hinter : Metric.ball z₀ r ∩ A ⁻¹' Complex.slitPlane ∈ 𝓝 z₀ :=
      Filter.inter_mem (Metric.isOpen_ball.mem_nhds hzball) hpre
    rcases Metric.mem_nhds_iff.mp hinter with ⟨ρ, hρ, hρsub⟩
    let R : ℝ := min ρ (r / 2)
    have hR : 0 < R := lt_min hρ (half_pos hr)
    have hRr : R < r := (min_le_right ρ (r / 2)).trans_lt (half_lt_self hr)
    have hRρ : Metric.ball z₀ R ⊆ Metric.ball z₀ ρ :=
      Metric.ball_subset_ball (min_le_left ρ (r / 2))
    have hRsub : Metric.ball z₀ R ⊆
        Metric.ball z₀ r ∩ A ⁻¹' Complex.slitPlane := hRρ.trans hρsub
    let B : ℂ → ℂ := fun z => Complex.log (A z)
    refine ⟨R, hR, hRr, B, ?_, ?_⟩
    · exact (hA.mono (fun z hz => (hRsub hz).1)).clog
        (fun z hz => (hRsub hz).2)
    · intro z hz
      have hzslit : A z ∈ Complex.slitPlane := (hRsub hz).2
      exact ⟨Complex.exp_log (Complex.slitPlane_ne_zero hzslit), by
        simp [B, Complex.log_re]⟩
  · have hnegAat : DifferentiableAt ℂ (fun z => -A z) z₀ := hAat.neg
    have hpre : (fun z => -A z) ⁻¹' Complex.slitPlane ∈ 𝓝 z₀ :=
      hnegAat.continuousAt.preimage_mem_nhds
        (Complex.isOpen_slitPlane.mem_nhds hnegslit)
    have hinter : Metric.ball z₀ r ∩
        (fun z => -A z) ⁻¹' Complex.slitPlane ∈ 𝓝 z₀ :=
      Filter.inter_mem (Metric.isOpen_ball.mem_nhds hzball) hpre
    rcases Metric.mem_nhds_iff.mp hinter with ⟨ρ, hρ, hρsub⟩
    let R : ℝ := min ρ (r / 2)
    have hR : 0 < R := lt_min hρ (half_pos hr)
    have hRr : R < r := (min_le_right ρ (r / 2)).trans_lt (half_lt_self hr)
    have hRρ : Metric.ball z₀ R ⊆ Metric.ball z₀ ρ :=
      Metric.ball_subset_ball (min_le_left ρ (r / 2))
    have hRsub : Metric.ball z₀ R ⊆
        Metric.ball z₀ r ∩ (fun z => -A z) ⁻¹' Complex.slitPlane :=
      hRρ.trans hρsub
    let B : ℂ → ℂ := fun z =>
      Complex.log (-A z) + (Real.pi : ℂ) * Complex.I
    refine ⟨R, hR, hRr, B, ?_, ?_⟩
    · have hlog : DifferentiableOn ℂ (fun z => Complex.log (-A z))
          (Metric.ball z₀ R) :=
        ((hA.mono (fun z hz => (hRsub hz).1)).neg).clog
          (fun z hz => (hRsub hz).2)
      exact hlog.add
        (differentiableOn_const (c := (Real.pi : ℂ) * Complex.I))
    · intro z hz
      have hzslit : -A z ∈ Complex.slitPlane := (hRsub hz).2
      have hz_ne : -A z ≠ 0 := Complex.slitPlane_ne_zero hzslit
      constructor
      · calc
          Complex.exp (B z) =
              Complex.exp (Complex.log (-A z)) *
                Complex.exp ((Real.pi : ℂ) * Complex.I) := by
            simp only [B, Complex.exp_add]
          _ = (-A z) * (-1) := by
            rw [Complex.exp_log hz_ne, Complex.exp_pi_mul_I]
          _ = A z := by ring
      · simp [B, Complex.log_re, norm_neg]

/--
%%handwave
name:
  Logarithmic pole-coordinate data
statement:
  Near the pole, a distinguished exponential branch has the form
  \((z-z_0)\exp B(z)\) on a coordinate disk, where (B) is holomorphic and
  its real part is the logarithm of the norm of the nonvanishing factor.
-/
structure CompactSuperlevelGreenFunctionPoleCoordinateLogData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G) where
  coordinate : PointedSurfaceCoordinate X p
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset_target :
    Metric.ball (coordinate.chart p) radius ⊆ coordinate.chart.target
  ball_symm_mem_domain :
    ∀ z ∈ Metric.ball (coordinate.chart p) radius,
      coordinate.chart.symm z ∈ P.domain
  logFactor : ℂ → ℂ
  logFactor_differentiableOn :
    DifferentiableOn ℂ logFactor
      (Metric.ball (coordinate.chart p) radius)
  exp_logFactor_eq :
    ∀ z ∈ Metric.ball (coordinate.chart p) radius,
      z ≠ coordinate.chart p →
      Complex.exp (logFactor z) =
        P.branch (coordinate.chart.symm z) /
          (z - coordinate.chart p)
  logFactor_re_eq_log_norm :
    ∀ z ∈ Metric.ball (coordinate.chart p) radius,
      z ≠ coordinate.chart p →
      (logFactor z).re =
        Real.log ‖P.branch (coordinate.chart.symm z) /
          (z - coordinate.chart p)‖
  branch_factorization :
    ∀ z ∈ Metric.ball (coordinate.chart p) radius,
      z ≠ coordinate.chart p →
        P.branch (coordinate.chart.symm z) =
          (z - coordinate.chart p) * Complex.exp (logFactor z)

/--
%%handwave
name:
  A logarithmic pole coordinate exists
statement:
  Every distinguished exponential branch at a Green pole admits a smaller
  coordinate disk on which its nonvanishing first-order factor has a
  single-valued holomorphic logarithm.
proof:
  Intersect a factorization disk with the branch domain, then shrink once more
  so the nonvanishing holomorphic factor lies in a slit plane.  The principal
  logarithm, after changing sign when necessary, supplies the logarithm.
-/
theorem compactSuperlevelGreenFunction_poleCoordinateLogData_nonempty
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p)
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G) :
    Nonempty (CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) := by
  classical
  let χ : PointedSurfaceCoordinate X p :=
    chartAtPointedSurfaceCoordinate X p
  let z₀ : ℂ := χ.chart p
  let S : Set ℂ := χ.chart.target ∩ χ.chart.symm ⁻¹' P.domain
  have hS_open : IsOpen S := by
    simpa [S] using
      χ.chart.isOpen_inter_preimage_symm P.domain_open
  have hz₀S : z₀ ∈ S := by
    refine ⟨?_, ?_⟩
    · exact χ.chart.map_source χ.base_mem_source
    · simpa [z₀, χ.chart.left_inv χ.base_mem_source] using P.mem_domain
  rcases Metric.isOpen_iff.mp hS_open z₀ hz₀S with
    ⟨rDomain, hrDomain, hballDomain⟩
  rcases P.pole_factorizations χ with
    ⟨rFactor, hrFactor, hballFactor, A, hA, hA_ne, hfactor⟩
  let r : ℝ := min rDomain rFactor
  have hr : 0 < r := lt_min hrDomain hrFactor
  have hrDomain_le : r ≤ rDomain := min_le_left _ _
  have hrFactor_le : r ≤ rFactor := min_le_right _ _
  have hball_r_domain : Metric.ball z₀ r ⊆ S :=
    (Metric.ball_subset_ball hrDomain_le).trans hballDomain
  have hball_r_factor : Metric.ball z₀ r ⊆
      Metric.ball z₀ rFactor := Metric.ball_subset_ball hrFactor_le
  have hA_r : DifferentiableOn ℂ A (Metric.ball z₀ r) :=
    hA.mono hball_r_factor
  rcases exists_ball_holomorphicLog_of_differentiableOn
      hr hA_r hA_ne with
    ⟨R, hR, hRr, B, hB, hB_spec⟩
  have hball_R_r : Metric.ball z₀ R ⊆ Metric.ball z₀ r :=
    Metric.ball_subset_ball hRr.le
  have hball_R_factor : Metric.ball z₀ R ⊆
      Metric.ball z₀ rFactor := hball_R_r.trans hball_r_factor
  refine ⟨{
    coordinate := χ
    radius := R
    radius_pos := hR
    ball_subset_target := ?_
    ball_symm_mem_domain := ?_
    logFactor := B
    logFactor_differentiableOn := hB
    exp_logFactor_eq := ?_
    logFactor_re_eq_log_norm := ?_
    branch_factorization := ?_ }⟩
  · exact hball_R_factor.trans hballFactor
  · intro z hz
    exact (hball_r_domain (hball_R_r hz)).2
  · intro z hz
    rcases hB_spec z hz with ⟨hexp, _hre⟩
    intro hz₀
    rw [hfactor z (hball_R_factor hz) hz₀, mul_div_cancel_left₀]
    · exact hexp
    · exact sub_ne_zero.mpr hz₀
  · intro z hz
    rcases hB_spec z hz with ⟨hexp, hre⟩
    intro hz₀
    rw [hfactor z (hball_R_factor hz) hz₀, mul_div_cancel_left₀]
    · exact hre
    · exact sub_ne_zero.mpr hz₀
  · intro z hz hz₀
    rw [hfactor z (hball_R_factor hz) hz₀]
    rw [(hB_spec z hz).1]

namespace CompactSuperlevelGreenFunctionPoleCoordinateLogData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [RiemannSurface X]
  {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
  {P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G}

/-- The closed half-radius disk associated to logarithmic pole-coordinate
data. -/
noncomputable def closedDisk
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    ClosedCoordinateDisk X :=
  closedCoordinateDiskOfChartBall
    D.coordinate.chart D.coordinate.chart_mem_atlas
    (D.coordinate.chart p)
    (half_pos D.radius_pos) (half_lt_self D.radius_pos)
    D.ball_subset_target

/--
%%handwave
name:
  Chart of the closed pole-coordinate disk
statement:
  The open coordinate disk underlying the chosen closed pole disk uses the
  original pointed coordinate chart.
proof:
  This is part of the defining closed-disk construction.
-/
@[simp]
theorem closedDisk_openDisk_chart
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    D.closedDisk.openDisk.chart = D.coordinate.chart := by
  simp [closedDisk, closedCoordinateDiskOfChartBall]

/--
%%handwave
name:
  Center of the closed pole-coordinate disk
statement:
  The center of the chosen pole-coordinate disk is the coordinate
  \(\chi(p)\) of the pole.
proof:
  This is immediate from the construction of the disk from the chart ball
  centered at \(\chi(p)\).
-/
@[simp]
theorem closedDisk_openDisk_center
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    D.closedDisk.openDisk.center = D.coordinate.chart p := by
  simp [closedDisk, closedCoordinateDiskOfChartBall]

/--
%%handwave
name:
  Open radius of the closed pole-coordinate disk
statement:
  The open disk underlying the chosen closed pole disk has radius \(r\), the
  radius of the logarithmic coordinate data.
proof:
  Unfold the chart-ball construction of the closed disk.
-/
@[simp]
theorem closedDisk_openDisk_radius
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    D.closedDisk.openDisk.radius = D.radius := by
  simp [closedDisk, closedCoordinateDiskOfChartBall]

/--
%%handwave
name:
  Closed radius of the pole-coordinate disk
statement:
  The closed core of the pole-coordinate disk has radius \(r/2\).
proof:
  The disk was constructed using the half-radius closed core.
-/
@[simp]
theorem closedDisk_closedRadius
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    D.closedDisk.closedRadius = D.radius / 2 := by
  simp [closedDisk, closedCoordinateDiskOfChartBall]

/--
%%handwave
name:
  The pole lies in the source chart of its coordinate disk
statement:
  The pole \(p\) belongs to the source of the chart used by the chosen closed
  coordinate disk.
proof:
  That chart is the original pointed coordinate, whose base point lies in its
  source.
-/
theorem pole_mem_closedDisk_chart_source
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    p ∈ D.closedDisk.openDisk.chart.source := by
  simpa [D.closedDisk_openDisk_chart] using D.coordinate.base_mem_source

/--
%%handwave
name:
  The pole maps to the disk center
statement:
  The chart of the closed pole-coordinate disk sends \(p\) to the center of
  the disk.
proof:
  Both sides reduce to the original coordinate value \(\chi(p)\).
-/
theorem closedDisk_chart_p_eq_center
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    D.closedDisk.openDisk.chart p = D.closedDisk.openDisk.center := by
  simp

/--
%%handwave
name:
  Doubling the closed radius gives the open radius
statement:
  For the chosen pole-coordinate disk, twice the closed-core radius equals
  the radius of its underlying open disk.
proof:
  The two radii are \(r/2\) and \(r\), respectively.
-/
@[simp]
theorem closedDisk_double_closedRadius
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    2 * D.closedDisk.closedRadius = D.closedDisk.openDisk.radius := by
  rw [D.closedDisk_closedRadius, D.closedDisk_openDisk_radius]
  ring

/--
%%handwave
name:
  Shrinking logarithmic pole data inside a prescribed neighborhood
statement:
  Given logarithmic pole-coordinate data and an open neighborhood \(O\) of
  the pole, one may decrease its radius, keeping the same coordinate and
  logarithmic factor, so that the associated open coordinate disk lies in
  \(O\).
proof:
  In the coordinate plane, intersect the chart target with the inverse image
  of \(O\) and choose a small ball about \(\chi(p)\) inside it.  Take the
  minimum of this radius and half the old radius; all factorization and
  logarithm identities restrict to the smaller ball.
-/
theorem exists_shrink_closedDisk_openDisk_subset_open
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (O : TopologicalSpace.Opens X) (hpO : p ∈ O) :
    ∃ D' : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P,
      D'.coordinate = D.coordinate ∧
        D'.logFactor = D.logFactor ∧
          D'.closedDisk.openDisk.carrier ⊆ O := by
  classical
  let e : OpenPartialHomeomorph X ℂ := D.coordinate.chart
  let z₀ : ℂ := e p
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' O
  have hSopen : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm O.isOpen
  have hz₀S : z₀ ∈ S := by
    refine ⟨e.map_source D.coordinate.base_mem_source, ?_⟩
    have hleft : e.symm (e p) = p :=
      e.left_inv D.coordinate.base_mem_source
    simpa [z₀, hleft] using hpO
  rcases Metric.isOpen_iff.mp hSopen z₀ hz₀S with
    ⟨r, hr, hballS⟩
  let R : ℝ := min r (D.radius / 2)
  have hRpos : 0 < R := lt_min hr (half_pos D.radius_pos)
  have hRleRadius : R ≤ D.radius :=
    (min_le_right r (D.radius / 2)).trans (half_le_self D.radius_pos.le)
  have hballOld : Metric.ball z₀ R ⊆
      Metric.ball (D.coordinate.chart p) D.radius := by
    simpa [z₀] using Metric.ball_subset_ball hRleRadius
  have hballNew : Metric.ball z₀ R ⊆ S :=
    (Metric.ball_subset_ball (min_le_left r (D.radius / 2))).trans hballS
  let D' : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P := {
    coordinate := D.coordinate
    radius := R
    radius_pos := hRpos
    ball_subset_target := by
      intro z hz
      exact (hballNew (by simpa [z₀] using hz)).1
    ball_symm_mem_domain := by
      intro z hz
      exact D.ball_symm_mem_domain z (hballOld (by simpa [z₀] using hz))
    logFactor := D.logFactor
    logFactor_differentiableOn :=
      D.logFactor_differentiableOn.mono hballOld
    exp_logFactor_eq := by
      intro z hz
      exact D.exp_logFactor_eq z (hballOld (by simpa [z₀] using hz))
    logFactor_re_eq_log_norm := by
      intro z hz
      exact D.logFactor_re_eq_log_norm z
        (hballOld (by simpa [z₀] using hz))
    branch_factorization := by
      intro z hz
      exact D.branch_factorization z (hballOld (by simpa [z₀] using hz)) }
  refine ⟨D', rfl, rfl, ?_⟩
  intro x hx
  change x ∈ e.source ∩ e ⁻¹' Metric.ball z₀ R at hx
  have hxS : e x ∈ S := hballNew hx.2
  have hleft : e.symm (e x) = x := e.left_inv hx.1
  simpa [S, hleft] using hxS.2

/-- The punctured pole-coordinate disk on which the logarithmic
factorization is valid. -/
def puncturedPoleDisk (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    TopologicalSpace.Opens X :=
  D.closedDisk.puncturedExpandedOpenDisk p
    (2 * D.closedDisk.closedRadius)

/--
%%handwave
name:
  Inner part of the doubled punctured pole disk
statement:
  Intersecting the punctured coordinate disk of radius \(2R\) with the inner
  disk of radius \(R\) yields exactly that inner disk with the pole removed.
proof:
  The non-pole and inner-radius conditions remain unchanged.  The inner ball
  is contained in the doubled ball because \(R>0\).
-/
theorem puncturedPoleDisk_inf_innerDomain_eq (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    D.puncturedPoleDisk ⊓
        ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
          D.closedDisk.toSmoothBoundaryDomain.isOpen⟩ =
      puncturedSurfaceOpen p ⊓
        ⟨D.closedDisk.expandedOpenDisk D.closedDisk.closedRadius,
          D.closedDisk.expandedOpenDisk_isOpen
            D.closedDisk.closedRadius⟩ := by
  ext x
  simp only [puncturedPoleDisk,
    ClosedCoordinateDisk.puncturedExpandedOpenDisk,
    ClosedCoordinateDisk.toSmoothBoundaryDomain,
    TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hxp, _houter⟩, hinner⟩
    exact ⟨hxp, hinner⟩
  · rintro ⟨hxp, hinner⟩
    refine ⟨⟨hxp, ?_⟩, hinner⟩
    rcases hinner with ⟨hsource, hball⟩
    refine ⟨hsource, ?_⟩
    change D.closedDisk.openDisk.chart x ∈
        Metric.ball D.closedDisk.openDisk.center
          D.closedDisk.closedRadius at hball
    change D.closedDisk.openDisk.chart x ∈
      Metric.ball D.closedDisk.openDisk.center
        (2 * D.closedDisk.closedRadius)
    rw [Metric.mem_ball] at hball ⊢
    linarith [D.closedDisk.closedRadius_pos]

/-- Radial coordinates on the punctured pole disk. -/
noncomputable def radialDiffeomorph (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] :
    D.puncturedPoleDisk ≃ₘ⟮SurfaceRealModel,
      AnnularCylinderModel⟯ Circle × ℝ :=
  D.closedDisk.radialPuncturedCollarDiffeomorph p
    D.pole_mem_closedDisk_chart_source
    D.closedDisk_chart_p_eq_center
    D.closedDisk_double_closedRadius.le

/--
%%handwave
name:
  Angular component of the radial pole coordinate
statement:
  The first component of the radial diffeomorphism at \(y\) is the unit
  direction \((\chi(y)-\chi(p))/|\chi(y)-\chi(p)|\).
proof:
  This is the angular component in the defining radial collar coordinate,
  after substituting the pole chart and center.
-/
@[simp]
theorem radialDiffeomorph_first_coe (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (y : D.puncturedPoleDisk) :
    ((D.radialDiffeomorph y).1 : ℂ) =
      NormedSpace.normalize
        (D.coordinate.chart (y : X) - D.coordinate.chart p) := by
  change NormedSpace.normalize
      (D.closedDisk.openDisk.chart (y : X) -
        D.closedDisk.openDisk.center) = _
  rw [D.closedDisk_openDisk_chart, D.closedDisk_openDisk_center]

/-- The inverse image of an open subset of the annular cylinder under the
radial pole coordinate. -/
def radialPreimageOpen (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (V : TopologicalSpace.Opens (Circle × ℝ)) :
    TopologicalSpace.Opens D.puncturedPoleDisk :=
  ⟨D.radialDiffeomorph ⁻¹' V,
    V.isOpen.preimage D.radialDiffeomorph.continuous⟩

/-- Restricting the radial pole coordinate to the inverse image of an open
set gives a diffeomorphism onto that open set. -/
noncomputable def radialPreimageDiffeomorph (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (V : TopologicalSpace.Opens (Circle × ℝ)) :
    D.radialPreimageOpen V ≃ₘ⟮SurfaceRealModel,
      AnnularCylinderModel⟯ V := by
  let toV : D.radialPreimageOpen V → V := fun x =>
    ⟨D.radialDiffeomorph (x : D.puncturedPoleDisk), x.2⟩
  have hto : ContMDiff SurfaceRealModel AnnularCylinderModel ∞ toV :=
    ContMDiff.codRestrict_open
      (D.radialDiffeomorph.contMDiff.comp contMDiff_subtype_val) V
      (fun x => x.2)
  let fromW : V → D.puncturedPoleDisk := fun y =>
    D.radialDiffeomorph.symm (y : Circle × ℝ)
  have hfromW : ContMDiff AnnularCylinderModel SurfaceRealModel ∞ fromW :=
    D.radialDiffeomorph.symm.contMDiff.comp contMDiff_subtype_val
  let fromV : V → D.radialPreimageOpen V := fun y =>
    ⟨fromW y, by
      change D.radialDiffeomorph
          (D.radialDiffeomorph.symm (y : Circle × ℝ)) ∈ V
      simpa using y.2⟩
  have hfrom : ContMDiff AnnularCylinderModel SurfaceRealModel ∞ fromV :=
    ContMDiff.codRestrict_open hfromW (D.radialPreimageOpen V)
      (fun y => (fromV y).2)
  exact
    { toEquiv :=
        { toFun := toV
          invFun := fromV
          left_inv := by intro x; apply Subtype.ext; simp [toV, fromV, fromW]
          right_inv := by intro y; apply Subtype.ext; simp [toV, fromV, fromW] }
      contMDiff_toFun := hto
      contMDiff_invFun := hfrom }

def radialLeftCut (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    TopologicalSpace.Opens D.puncturedPoleDisk :=
  D.radialPreimageOpen (annularPunctureOpen v)

def radialRightCut (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    TopologicalSpace.Opens D.puncturedPoleDisk :=
  D.radialPreimageOpen (annularPunctureOpen (annularOpposite v))

/--
%%handwave
name:
  The two radial cuts cover the punctured pole disk
statement:
  For every direction \(v\in S^1\), the two radial slit domains obtained by
  deleting \(v\) and \(-v\) from the angular coordinate cover the punctured
  pole disk.
proof:
  Pull the covering of the annular cylinder by its two complementary angular
  cuts back along the radial-coordinate diffeomorphism.
-/
theorem radialCuts_cover (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    D.radialLeftCut v ⊔ D.radialRightCut v = ⊤ := by
  ext x
  change D.radialDiffeomorph x ∈ annularPunctureOpen v ∨
      D.radialDiffeomorph x ∈
        annularPunctureOpen (annularOpposite v) ↔ True
  simpa only [iff_true] using
    (show D.radialDiffeomorph x ∈
        annularPunctureOpen v ⊔
          annularPunctureOpen (annularOpposite v) by
      rw [annularPunctures_cover]
      trivial)

/--
%%handwave
name:
  Membership in the punctured pole-coordinate disk
statement:
  A point \(x\) belongs to the punctured pole-coordinate disk of radius \(r\)
  if and only if \(x\ne p\), \(x\) lies in the coordinate-chart source, and
  its coordinate lies in \(B(\chi(p),r)\).
proof:
  Expand the punctured expanded disk and use \(2(r/2)=r\).
-/
theorem puncturedPoleDisk_mem_iff (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    {x : X} :
    x ∈ D.puncturedPoleDisk ↔
      x ≠ p ∧ x ∈ D.coordinate.chart.source ∧
        D.coordinate.chart x ∈
          Metric.ball (D.coordinate.chart p) D.radius := by
  have htwo : 2 * (D.radius / 2) = D.radius := by ring
  simp [puncturedPoleDisk,
    ClosedCoordinateDisk.puncturedExpandedOpenDisk,
    puncturedSurfaceOpen, ClosedCoordinateDisk.expandedOpenDisk, htwo]

/--
%%handwave
name:
  Positive scaling preserves the slit plane
statement:
  If \(r>0\), then \(rz\) lies in the complex plane slit along the
  nonpositive real axis if and only if \(z\) does.
proof:
  Positive multiplication preserves the sign of the imaginary part and
  preserves nonvanishing on the positive real axis.
-/
theorem positiveReal_mul_mem_slitPlane_iff
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (r : ℂ) * z ∈ Complex.slitPlane ↔ z ∈ Complex.slitPlane := by
  simp only [Complex.mem_slitPlane_iff, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by
        intro hz
        apply h
        simp [hz])
  · rintro (h | h)
    · exact Or.inl (mul_pos hr h)
    · exact Or.inr (mul_ne_zero hr.ne' h)

/--
%%handwave
name:
  Slit-plane criterion for a rotated pole coordinate
statement:
  For \(v\in S^1\) and \(w\ne0\), the number \(-v^{-1}w\) lies in the
  principal slit plane if and only if the direction \(w/|w|\) is not \(v\).
proof:
  Write \(w=|w|(w/|w|)\).  Positive scaling does not affect slit-plane
  membership, and the remaining unit-circle rotation meets the slit exactly
  away from the deleted direction \(v\).
-/
theorem rotatedCoordinate_mem_slitPlane_iff_direction_ne
    (v : Circle) {w : ℂ} (hw : w ≠ 0) :
    -((v⁻¹ : Circle) : ℂ) * w ∈ Complex.slitPlane ↔
      complexPuncturedPlaneDirection ⟨w, hw⟩ ≠ v := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwdecomp :
      (‖w‖ : ℂ) * NormedSpace.normalize w = w := by
    simpa only [Complex.real_smul] using
      NormedSpace.norm_smul_normalize w
  have hdecomp :
      -((v⁻¹ : Circle) : ℂ) * w =
        (‖w‖ : ℂ) *
          (annularCutRotation v
            (complexPuncturedPlaneDirection ⟨w, hw⟩) : ℂ) := by
    calc
      -((v⁻¹ : Circle) : ℂ) * w =
          -((v⁻¹ : Circle) : ℂ) *
            ((‖w‖ : ℂ) * NormedSpace.normalize w) := by rw [hwdecomp]
      _ = _ := by
        simp [complexPuncturedPlaneDirection, annularCutRotation,
          circleAntipode]
        ring
  rw [hdecomp, positiveReal_mul_mem_slitPlane_iff hnorm,
    annularCutRotation_mem_slitPlane_iff]

/--
%%handwave
name:
  Slit-plane criterion for the opposite rotated pole coordinate
statement:
  For \(v\in S^1\) and \(w\ne0\), the number \(v^{-1}w\) lies in the
  principal slit plane if and only if the direction \(w/|w|\) is not the
  antipode \(-v\).
proof:
  Factor \(w\) as its positive norm times its direction.  Remove the positive
  factor, then apply the complementary unit-circle cut criterion.
-/
theorem oppositeRotatedCoordinate_mem_slitPlane_iff_direction_ne
    (v : Circle) {w : ℂ} (hw : w ≠ 0) :
    ((v⁻¹ : Circle) : ℂ) * w ∈ Complex.slitPlane ↔
      complexPuncturedPlaneDirection ⟨w, hw⟩ ≠ annularOpposite v := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwdecomp :
      (‖w‖ : ℂ) * NormedSpace.normalize w = w := by
    simpa only [Complex.real_smul] using
      NormedSpace.norm_smul_normalize w
  have hdecomp :
      ((v⁻¹ : Circle) : ℂ) * w =
        (‖w‖ : ℂ) *
          (circleAntipode
            (annularCutRotation v
              (complexPuncturedPlaneDirection ⟨w, hw⟩)) : ℂ) := by
    calc
      ((v⁻¹ : Circle) : ℂ) * w =
          ((v⁻¹ : Circle) : ℂ) *
            ((‖w‖ : ℂ) * NormedSpace.normalize w) := by rw [hwdecomp]
      _ = _ := by
        simp [complexPuncturedPlaneDirection, annularCutRotation,
          circleAntipode]
        ring
  rw [hdecomp, positiveReal_mul_mem_slitPlane_iff hnorm,
    secondCut_mem_slitPlane_iff]

/-- The first slit in the pole coordinate, obtained by rotating the chosen
radial direction to the principal-logarithm cut. -/
def leftCoordinateSlit (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) : Set ℂ :=
  Metric.ball (D.coordinate.chart p) D.radius ∩
    (fun z : ℂ =>
      -((v⁻¹ : Circle) : ℂ) * (z - D.coordinate.chart p)) ⁻¹'
        Complex.slitPlane

/-- The opposite slit in the pole coordinate. -/
def rightCoordinateSlit (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) : Set ℂ :=
  Metric.ball (D.coordinate.chart p) D.radius ∩
    (fun z : ℂ =>
      ((v⁻¹ : Circle) : ℂ) * (z - D.coordinate.chart p)) ⁻¹'
        Complex.slitPlane

/--
%%handwave
name:
  Openness of the first slit coordinate disk
statement:
  The coordinate disk on which \(-v^{-1}(z-\chi(p))\) lies in the principal
  slit plane is open.
proof:
  It is the intersection of an open ball with the inverse image of the open
  slit plane under a continuous affine map.
-/
theorem isOpen_leftCoordinateSlit (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) : IsOpen (D.leftCoordinateSlit v) := by
  apply Metric.isOpen_ball.inter
  apply Complex.isOpen_slitPlane.preimage
  fun_prop

/--
%%handwave
name:
  Openness of the opposite slit coordinate disk
statement:
  The coordinate disk on which \(v^{-1}(z-\chi(p))\) lies in the principal
  slit plane is open.
proof:
  It is the intersection of an open ball with the inverse image of the open
  slit plane under a continuous affine map.
-/
theorem isOpen_rightCoordinateSlit (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) : IsOpen (D.rightCoordinateSlit v) := by
  apply Metric.isOpen_ball.inter
  apply Complex.isOpen_slitPlane.preimage
  fun_prop

/-- The surface part of the first slit pole disk. -/
def leftPoleCut (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) : TopologicalSpace.Opens X :=
  ⟨D.coordinate.chart.source ∩
      D.coordinate.chart ⁻¹' D.leftCoordinateSlit v,
    D.coordinate.chart.isOpen_inter_preimage
      (D.isOpen_leftCoordinateSlit v)⟩

/-- The surface part of the opposite slit pole disk. -/
def rightPoleCut (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) : TopologicalSpace.Opens X :=
  ⟨D.coordinate.chart.source ∩
      D.coordinate.chart ⁻¹' D.rightCoordinateSlit v,
    D.coordinate.chart.isOpen_inter_preimage
      (D.isOpen_rightCoordinateSlit v)⟩

/--
%%handwave
name:
  The first pole cut omits the pole
statement:
  Every point of the first slit pole-coordinate disk is different from
  \(p\).
proof:
  At \(p\) the translated and rotated coordinate is zero, whereas the slit
  plane contains only nonzero points.
-/
theorem leftPoleCut_ne_p (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) {x : X} (hx : x ∈ D.leftPoleCut v) : x ≠ p := by
  intro hxp
  subst x
  have hne := Complex.slitPlane_ne_zero hx.2.2
  simp at hne

/--
%%handwave
name:
  The opposite pole cut omits the pole
statement:
  Every point of the opposite slit pole-coordinate disk is different from
  \(p\).
proof:
  At \(p\) the translated and rotated coordinate is zero, which is excluded
  from the slit plane.
-/
theorem rightPoleCut_ne_p (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) {x : X} (hx : x ∈ D.rightPoleCut v) : x ≠ p := by
  intro hxp
  subst x
  have hne := Complex.slitPlane_ne_zero hx.2.2
  simp at hne

/--
%%handwave
name:
  The first pole cut lies in the branch domain
statement:
  Every point of the first slit pole-coordinate disk belongs to the domain of
  the distinguished holomorphic branch.
proof:
  Its coordinate lies in the logarithmic ball, whose inverse-chart image is
  contained in the branch domain.
-/
theorem leftPoleCut_mem_branch_domain (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) {x : X} (hx : x ∈ D.leftPoleCut v) : x ∈ P.domain := by
  have hsymm := D.coordinate.chart.left_inv hx.1
  simpa [hsymm] using
    D.ball_symm_mem_domain (D.coordinate.chart x) hx.2.1

/--
%%handwave
name:
  The opposite pole cut lies in the branch domain
statement:
  Every point of the opposite slit pole-coordinate disk belongs to the
  domain of the distinguished holomorphic branch.
proof:
  Its coordinate lies in the logarithmic ball, whose inverse-chart image is
  contained in the branch domain.
-/
theorem rightPoleCut_mem_branch_domain (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) {x : X} (hx : x ∈ D.rightPoleCut v) : x ∈ P.domain := by
  have hsymm := D.coordinate.chart.left_inv hx.1
  simpa [hsymm] using
    D.ball_symm_mem_domain (D.coordinate.chart x) hx.2.1

/--
%%handwave
name:
  Radial and coordinate descriptions of the first pole cut
statement:
  A point of the punctured pole disk lies in the radial cut deleting
  \(v\in S^1\) if and only if its underlying surface point lies in the first
  slit pole-coordinate disk.
proof:
  The angular component of the radial coordinate is the direction of
  \(\chi(x)-\chi(p)\).  The first radial cut deletes \(v\), and the rotated
  slit-plane criterion gives the identical condition in the coordinate disk.
-/
theorem radialLeftCut_mem_iff_leftPoleCut (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle)
    (y : D.puncturedPoleDisk) :
    y ∈ D.radialLeftCut v ↔ (y : X) ∈ D.leftPoleCut v := by
  let w : ℂ := D.coordinate.chart (y : X) - D.coordinate.chart p
  have hy := (D.puncturedPoleDisk_mem_iff).mp y.2
  have hw : w ≠ 0 := by
    intro hzero
    exact hy.1 (D.coordinate.chart.injOn hy.2.1
      D.coordinate.base_mem_source (sub_eq_zero.mp hzero))
  have hdir : (D.radialDiffeomorph y).1 =
      complexPuncturedPlaneDirection ⟨w, hw⟩ := by
    apply Circle.ext
    simpa [w, complexPuncturedPlaneDirection] using
      D.radialDiffeomorph_first_coe y
  constructor
  · intro hrad
    have hne : (D.radialDiffeomorph y).1 ≠ v :=
      (mem_annularPunctureOpen_iff v _).mp hrad
    have hdirne : complexPuncturedPlaneDirection ⟨w, hw⟩ ≠ v := by
      simpa [hdir] using hne
    refine ⟨hy.2.1, hy.2.2, ?_⟩
    simpa [w] using
      (rotatedCoordinate_mem_slitPlane_iff_direction_ne v hw).mpr hdirne
  · intro hx
    apply (mem_annularPunctureOpen_iff v _).mpr
    rw [hdir]
    apply (rotatedCoordinate_mem_slitPlane_iff_direction_ne v hw).mp
    simpa [w] using hx.2.2

/--
%%handwave
name:
  Radial and coordinate descriptions of the opposite pole cut
statement:
  A point of the punctured pole disk lies in the radial cut deleting
  \(-v\in S^1\) if and only if its underlying surface point lies in the
  opposite slit pole-coordinate disk.
proof:
  Identify the angular radial coordinate with the direction of
  \(\chi(x)-\chi(p)\).  Excluding \(-v\) is precisely the complementary
  rotated slit-plane condition.
-/
theorem radialRightCut_mem_iff_rightPoleCut (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle)
    (y : D.puncturedPoleDisk) :
    y ∈ D.radialRightCut v ↔ (y : X) ∈ D.rightPoleCut v := by
  let w : ℂ := D.coordinate.chart (y : X) - D.coordinate.chart p
  have hy := (D.puncturedPoleDisk_mem_iff).mp y.2
  have hw : w ≠ 0 := by
    intro hzero
    exact hy.1 (D.coordinate.chart.injOn hy.2.1
      D.coordinate.base_mem_source (sub_eq_zero.mp hzero))
  have hdir : (D.radialDiffeomorph y).1 =
      complexPuncturedPlaneDirection ⟨w, hw⟩ := by
    apply Circle.ext
    simpa [w, complexPuncturedPlaneDirection] using
      D.radialDiffeomorph_first_coe y
  constructor
  · intro hrad
    have hne : (D.radialDiffeomorph y).1 ≠ annularOpposite v :=
      (mem_annularPunctureOpen_iff (annularOpposite v) _).mp hrad
    have hdirne : complexPuncturedPlaneDirection ⟨w, hw⟩ ≠
        annularOpposite v := by
      simpa [hdir] using hne
    refine ⟨hy.2.1, hy.2.2, ?_⟩
    simpa [w] using
      (oppositeRotatedCoordinate_mem_slitPlane_iff_direction_ne
        v hw).mpr hdirne
  · intro hx
    apply (mem_annularPunctureOpen_iff (annularOpposite v) _).mpr
    rw [hdir]
    apply (oppositeRotatedCoordinate_mem_slitPlane_iff_direction_ne
      v hw).mp
    simpa [w] using hx.2.2

/-- The first holomorphic logarithm of the pole branch. -/
noncomputable def leftPoleLog (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) (x : X) : ℂ :=
  Complex.log
      (-((v⁻¹ : Circle) : ℂ) *
        (D.coordinate.chart x - D.coordinate.chart p)) +
    Complex.log (-((v : Circle) : ℂ)) +
    D.logFactor (D.coordinate.chart x)

/-- The opposite holomorphic logarithm of the pole branch. -/
noncomputable def rightPoleLog (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) (x : X) : ℂ :=
  Complex.log
      (((v⁻¹ : Circle) : ℂ) *
        (D.coordinate.chart x - D.coordinate.chart p)) +
    (Real.pi : ℂ) * Complex.I +
    Complex.log (-((v : Circle) : ℂ)) +
    D.logFactor (D.coordinate.chart x)

/--
%%handwave
name:
  Holomorphicity of the first slit logarithm
statement:
  On the first slit pole disk, the function
  \[
    x\longmapsto \log\!\bigl(-v^{-1}(\chi(x)-\chi(p))\bigr)
      +\log(-v)+B(\chi(x))
  \]
  is holomorphic, where \(B\) is the local logarithm of the nonvanishing
  factor in the pole branch.
proof:
  The rotated coordinate remains in the principal slit plane, so its
  principal logarithm is holomorphic.  Add the constant and the holomorphic
  factor logarithm, then compose with the holomorphic chart.
-/
theorem leftPoleLog_mdifferentiableOn (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (D.leftPoleLog v) (D.leftPoleCut v) := by
  let S := D.leftCoordinateSlit v
  let F : ℂ → ℂ := fun z =>
    Complex.log
        (-((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p)) +
      Complex.log (-((v : Circle) : ℂ)) + D.logFactor z
  have harg : DifferentiableOn ℂ
      (fun z : ℂ =>
        -((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p)) S :=
    (differentiableOn_id.sub_const _).const_mul _
  have hlog : DifferentiableOn ℂ
      (fun z : ℂ => Complex.log
        (-((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p))) S :=
    harg.clog (fun z hz => hz.2)
  have hFdiff : DifferentiableOn ℂ F S := by
    exact (hlog.add (differentiableOn_const
      (c := Complex.log (-((v : Circle) : ℂ))))).add
      (D.logFactor_differentiableOn.mono (fun z hz => hz.1))
  have hFmdiff : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F S :=
    mdifferentiableOn_iff_differentiableOn.mpr hFdiff
  have hchart : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      D.coordinate.chart (D.leftPoleCut v) :=
    (mdifferentiableOn_atlas (I := 𝓘(ℂ))
      D.coordinate.chart_mem_atlas).mono (fun _ hx => hx.1)
  have hmaps : (D.leftPoleCut v : Set X) ⊆
      D.coordinate.chart ⁻¹' S := fun _ hx => hx.2
  change MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
    (fun x : X =>
      Complex.log
          (-((v⁻¹ : Circle) : ℂ) *
            (D.coordinate.chart x - D.coordinate.chart p)) +
        Complex.log (-((v : Circle) : ℂ)) +
        D.logFactor (D.coordinate.chart x)) (D.leftPoleCut v)
  simpa only [F, Function.comp_def] using
    hFmdiff.comp hchart hmaps

/--
%%handwave
name:
  Holomorphicity of the opposite slit logarithm
statement:
  On the opposite slit pole disk, the function
  \[
    x\longmapsto \log\!\bigl(v^{-1}(\chi(x)-\chi(p))\bigr)
      +\pi i+\log(-v)+B(\chi(x))
  \]
  is holomorphic.
proof:
  The rotated coordinate lies in the principal slit plane, hence its
  principal logarithm is holomorphic.  Add the constant terms and the local
  holomorphic factor logarithm, then compose with the chart.
-/
theorem rightPoleLog_mdifferentiableOn (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (D.rightPoleLog v) (D.rightPoleCut v) := by
  let S := D.rightCoordinateSlit v
  let F : ℂ → ℂ := fun z =>
    Complex.log
        (((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p)) +
      (Real.pi : ℂ) * Complex.I +
      Complex.log (-((v : Circle) : ℂ)) + D.logFactor z
  have harg : DifferentiableOn ℂ
      (fun z : ℂ =>
        ((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p)) S :=
    (differentiableOn_id.sub_const _).const_mul _
  have hlog : DifferentiableOn ℂ
      (fun z : ℂ => Complex.log
        (((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p))) S :=
    harg.clog (fun z hz => hz.2)
  have hFdiff : DifferentiableOn ℂ F S := by
    exact (((hlog.add (differentiableOn_const
      (c := (Real.pi : ℂ) * Complex.I))).add
        (differentiableOn_const
          (c := Complex.log (-((v : Circle) : ℂ))))).add
      (D.logFactor_differentiableOn.mono (fun z hz => hz.1)))
  have hFmdiff : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F S :=
    mdifferentiableOn_iff_differentiableOn.mpr hFdiff
  have hchart : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      D.coordinate.chart (D.rightPoleCut v) :=
    (mdifferentiableOn_atlas (I := 𝓘(ℂ))
      D.coordinate.chart_mem_atlas).mono (fun _ hx => hx.1)
  have hmaps : (D.rightPoleCut v : Set X) ⊆
      D.coordinate.chart ⁻¹' S := fun _ hx => hx.2
  change MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
    (fun x : X =>
      Complex.log
          (((v⁻¹ : Circle) : ℂ) *
            (D.coordinate.chart x - D.coordinate.chart p)) +
        (Real.pi : ℂ) * Complex.I +
        Complex.log (-((v : Circle) : ℂ)) +
        D.logFactor (D.coordinate.chart x)) (D.rightPoleCut v)
  simpa only [F, Function.comp_def] using
    hFmdiff.comp hchart hmaps

/--
%%handwave
name:
  Exponential of the first slit logarithm
statement:
  On the first slit pole disk, exponentiating
  \(\log(-v^{-1}(\chi(x)-\chi(p)))+\log(-v)+B(\chi(x))\) gives the
  distinguished holomorphic branch at \(x\).
proof:
  Exponentiate each summand using the principal-logarithm identities.  The
  two rotation factors cancel, leaving
  \((\chi(x)-\chi(p))e^{B(\chi(x))}\), which is the local factorization of
  the branch.
-/
theorem leftPoleLog_exp_eq_branch (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) {x : X} (hx : x ∈ D.leftPoleCut v) :
    Complex.exp (D.leftPoleLog v x) = P.branch x := by
  let z := D.coordinate.chart x
  let z₀ := D.coordinate.chart p
  have hxne : x ≠ p := D.leftPoleCut_ne_p v hx
  have hz_ne : z ≠ z₀ := by
    intro hz
    exact hxne (D.coordinate.chart.injOn hx.1
      D.coordinate.base_mem_source hz)
  have hfactor := D.branch_factorization z hx.2.1 hz_ne
  have hsymm := D.coordinate.chart.left_inv hx.1
  have hbranch : P.branch x =
      (z - z₀) * Complex.exp (D.logFactor z) := by
    simpa [z, z₀, hsymm] using hfactor
  have hrot_ne :
      -((v⁻¹ : Circle) : ℂ) * (z - z₀) ≠ 0 :=
    Complex.slitPlane_ne_zero hx.2.2
  have hv_ne : -((v : Circle) : ℂ) ≠ 0 :=
    neg_ne_zero.mpr v.coe_ne_zero
  rw [leftPoleLog, Complex.exp_add, Complex.exp_add,
    Complex.exp_log hrot_ne, Complex.exp_log hv_ne]
  rw [hbranch]
  simp [z, z₀]
  simp [mul_comm]

/--
%%handwave
name:
  Exponential of the opposite slit logarithm
statement:
  On the opposite slit pole disk, exponentiating
  \(\log(v^{-1}(\chi(x)-\chi(p)))+\pi i+\log(-v)+B(\chi(x))\) gives the
  distinguished holomorphic branch at \(x\).
proof:
  Exponentiate term by term.  Since \(e^{\pi i}=-1\), the constants and
  rotations cancel to give
  \((\chi(x)-\chi(p))e^{B(\chi(x))}\), the local branch factorization.
-/
theorem rightPoleLog_exp_eq_branch (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) {x : X} (hx : x ∈ D.rightPoleCut v) :
    Complex.exp (D.rightPoleLog v x) = P.branch x := by
  let z := D.coordinate.chart x
  let z₀ := D.coordinate.chart p
  have hxne : x ≠ p := D.rightPoleCut_ne_p v hx
  have hz_ne : z ≠ z₀ := by
    intro hz
    exact hxne (D.coordinate.chart.injOn hx.1
      D.coordinate.base_mem_source hz)
  have hfactor := D.branch_factorization z hx.2.1 hz_ne
  have hsymm := D.coordinate.chart.left_inv hx.1
  have hbranch : P.branch x =
      (z - z₀) * Complex.exp (D.logFactor z) := by
    simpa [z, z₀, hsymm] using hfactor
  have hrot_ne :
      ((v⁻¹ : Circle) : ℂ) * (z - z₀) ≠ 0 :=
    Complex.slitPlane_ne_zero hx.2.2
  have hv_ne : -((v : Circle) : ℂ) ≠ 0 :=
    neg_ne_zero.mpr v.coe_ne_zero
  rw [rightPoleLog, Complex.exp_add, Complex.exp_add, Complex.exp_add,
    Complex.exp_log hrot_ne, Complex.exp_pi_mul_I,
    Complex.exp_log hv_ne]
  rw [hbranch]
  simp [z, z₀]
  simp [mul_comm]

/--
%%handwave
name:
  Real part of the first slit logarithm
statement:
  On the first slit pole disk, the real part of the local logarithm equals
  \(-G(x)\).
proof:
  Its exponential is the distinguished branch, so its real part is the
  logarithm of the branch modulus.  The branch normalization identifies that
  logarithm with \(-G(x)\).
-/
theorem leftPoleLog_re_eq_neg_green (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) {x : X} (hx : x ∈ D.leftPoleCut v) :
    (D.leftPoleLog v x).re = -G.toFun x := by
  have hexp := D.leftPoleLog_exp_eq_branch v hx
  calc
    (D.leftPoleLog v x).re =
        Real.log ‖Complex.exp (D.leftPoleLog v x)‖ := by
      simp [Complex.norm_exp]
    _ = Real.log ‖P.branch x‖ := by rw [hexp]
    _ = -G.toFun x :=
      P.log_norm_eq x (D.leftPoleCut_mem_branch_domain v hx)
        (D.leftPoleCut_ne_p v hx)

/--
%%handwave
name:
  Real part of the opposite slit logarithm
statement:
  On the opposite slit pole disk, the real part of the local logarithm equals
  \(-G(x)\).
proof:
  Its exponential is the distinguished branch, hence its real part is the
  logarithm of the branch modulus.  The branch normalization gives
  \(\log|P(x)|=-G(x)\).
-/
theorem rightPoleLog_re_eq_neg_green (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) {x : X} (hx : x ∈ D.rightPoleCut v) :
    (D.rightPoleLog v x).re = -G.toFun x := by
  have hexp := D.rightPoleLog_exp_eq_branch v hx
  calc
    (D.rightPoleLog v x).re =
        Real.log ‖Complex.exp (D.rightPoleLog v x)‖ := by
      simp [Complex.norm_exp]
    _ = Real.log ‖P.branch x‖ := by rw [hexp]
    _ = -G.toFun x :=
      P.log_norm_eq x (D.rightPoleCut_mem_branch_domain v hx)
        (D.rightPoleCut_ne_p v hx)

/-- The first slit logarithm, packaged as a holomorphic branch with real part
the negative Green potential. -/
noncomputable def leftPoleLogBranch (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) :
    SurfaceHolomorphicRealPartBranch X (fun x => -G.toFun x) := by
  let F : ℂ → ℂ := fun z =>
    Complex.log
        (-((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p)) +
      Complex.log (-((v : Circle) : ℂ)) + D.logFactor z
  have harg : DifferentiableOn ℂ
      (fun z : ℂ =>
        -((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p)) (D.leftCoordinateSlit v) :=
    (differentiableOn_id.sub_const _).const_mul _
  have hlog : DifferentiableOn ℂ
      (fun z : ℂ => Complex.log
        (-((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p))) (D.leftCoordinateSlit v) :=
    harg.clog (fun z hz => hz.2)
  have hF : DifferentiableOn ℂ F (D.leftCoordinateSlit v) := by
    exact (hlog.add (differentiableOn_const
      (c := Complex.log (-((v : Circle) : ℂ))))).add
      (D.logFactor_differentiableOn.mono (fun z hz => hz.1))
  refine
    { source := D.leftPoleCut v
      source_open := (D.leftPoleCut v).isOpen
      chart := D.coordinate.chart
      chart_mem_atlas := D.coordinate.chart_mem_atlas
      coordinateSource := D.leftCoordinateSlit v
      coordinateSource_open := D.isOpen_leftCoordinateSlit v
      coordinateSource_subset_chart_target := fun z hz =>
        D.ball_subset_target hz.1
      source_eq := rfl
      potential := F
      potential_holomorphic :=
        hF.analyticOnNhd (D.isOpen_leftCoordinateSlit v)
      potential_re_eq := ?_ }
  intro z hz
  have hzTarget : z ∈ D.coordinate.chart.target :=
    D.ball_subset_target hz.1
  have hx : D.coordinate.chart.symm z ∈ D.leftPoleCut v := by
    refine ⟨D.coordinate.chart.map_target hzTarget, ?_⟩
    change D.coordinate.chart (D.coordinate.chart.symm z) ∈
      D.leftCoordinateSlit v
    simpa [D.coordinate.chart.right_inv hzTarget] using hz
  have hre := D.leftPoleLog_re_eq_neg_green v hx
  simpa [F, leftPoleLog, D.coordinate.chart.right_inv hzTarget] using hre

/-- The opposite slit logarithm, packaged as a holomorphic branch with real
part the negative Green potential. -/
noncomputable def rightPoleLogBranch (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) :
    SurfaceHolomorphicRealPartBranch X (fun x => -G.toFun x) := by
  let F : ℂ → ℂ := fun z =>
    Complex.log
        (((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p)) +
      (Real.pi : ℂ) * Complex.I +
      Complex.log (-((v : Circle) : ℂ)) + D.logFactor z
  have harg : DifferentiableOn ℂ
      (fun z : ℂ =>
        ((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p)) (D.rightCoordinateSlit v) :=
    (differentiableOn_id.sub_const _).const_mul _
  have hlog : DifferentiableOn ℂ
      (fun z : ℂ => Complex.log
        (((v⁻¹ : Circle) : ℂ) *
          (z - D.coordinate.chart p))) (D.rightCoordinateSlit v) :=
    harg.clog (fun z hz => hz.2)
  have hF : DifferentiableOn ℂ F (D.rightCoordinateSlit v) := by
    exact (((hlog.add (differentiableOn_const
      (c := (Real.pi : ℂ) * Complex.I))).add
        (differentiableOn_const
          (c := Complex.log (-((v : Circle) : ℂ))))).add
      (D.logFactor_differentiableOn.mono (fun z hz => hz.1)))
  refine
    { source := D.rightPoleCut v
      source_open := (D.rightPoleCut v).isOpen
      chart := D.coordinate.chart
      chart_mem_atlas := D.coordinate.chart_mem_atlas
      coordinateSource := D.rightCoordinateSlit v
      coordinateSource_open := D.isOpen_rightCoordinateSlit v
      coordinateSource_subset_chart_target := fun z hz =>
        D.ball_subset_target hz.1
      source_eq := rfl
      potential := F
      potential_holomorphic :=
        hF.analyticOnNhd (D.isOpen_rightCoordinateSlit v)
      potential_re_eq := ?_ }
  intro z hz
  have hzTarget : z ∈ D.coordinate.chart.target :=
    D.ball_subset_target hz.1
  have hx : D.coordinate.chart.symm z ∈ D.rightPoleCut v := by
    refine ⟨D.coordinate.chart.map_target hzTarget, ?_⟩
    change D.coordinate.chart (D.coordinate.chart.symm z) ∈
      D.rightCoordinateSlit v
    simpa [D.coordinate.chart.right_inv hzTarget] using hz
  have hre := D.rightPoleLog_re_eq_neg_green v hx
  simpa [F, rightPoleLog, D.coordinate.chart.right_inv hzTarget] using hre

/--
%%handwave
name:
  Underlying function of the first logarithm branch
statement:
  The total function underlying the holomorphic branch on the first slit is
  the explicit first slit logarithm.
proof:
  This is immediate from the construction of the branch.
-/
@[simp]
theorem leftPoleLogBranch_toSurfaceTotalFunction (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) (x : X) :
    (D.leftPoleLogBranch v).toSurfaceTotalFunction x =
      D.leftPoleLog v x := by
  rfl

/--
%%handwave
name:
  Underlying function of the opposite logarithm branch
statement:
  The total function underlying the holomorphic branch on the opposite slit
  is the explicit opposite slit logarithm.
proof:
  This is immediate from the construction of the branch.
-/
@[simp]
theorem rightPoleLogBranch_toSurfaceTotalFunction (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) (x : X) :
    (D.rightPoleLogBranch v).toSurfaceTotalFunction x =
      D.rightPoleLog v x := by
  rfl

/--
%%handwave
name:
  The first pole cut lies in the punctured surface
statement:
  The first slit pole-coordinate disk is contained in \(X\setminus\{p\}\).
proof:
  The slit-plane condition excludes the zero coordinate and hence excludes
  the pole.
-/
theorem leftPoleCut_le_puncturedSurfaceOpen (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) :
    D.leftPoleCut v ≤ puncturedSurfaceOpen p := by
  intro x hx
  exact D.leftPoleCut_ne_p v hx

/--
%%handwave
name:
  The opposite pole cut lies in the punctured surface
statement:
  The opposite slit pole-coordinate disk is contained in
  \(X\setminus\{p\}\).
proof:
  The slit-plane condition excludes the zero coordinate and therefore the
  pole.
-/
theorem rightPoleCut_le_puncturedSurfaceOpen (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) :
    D.rightPoleCut v ≤ puncturedSurfaceOpen p := by
  intro x hx
  exact D.rightPoleCut_ne_p v hx

/--
%%handwave
name:
  The punctured pole disk lies in the punctured surface
statement:
  The punctured pole-coordinate disk is contained in \(X\setminus\{p\}\).
proof:
  Nonmembership of \(p\) is part of the defining membership condition for
  the punctured disk.
-/
theorem puncturedPoleDisk_le_puncturedSurfaceOpen (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P) :
    D.puncturedPoleDisk ≤ puncturedSurfaceOpen p := by
  intro x hx
  exact (D.puncturedPoleDisk_mem_iff.mp hx).1

/--
%%handwave
name:
  The first pole cut lies in the punctured pole disk
statement:
  The first slit pole-coordinate disk is contained in the punctured
  pole-coordinate disk of the same radius.
proof:
  A point on the cut lies in the chart ball and is not the pole, which are
  exactly the membership conditions for the punctured disk.
-/
theorem leftPoleCut_le_puncturedPoleDisk (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) : D.leftPoleCut v ≤ D.puncturedPoleDisk := by
  intro x hx
  exact D.puncturedPoleDisk_mem_iff.mpr
    ⟨D.leftPoleCut_ne_p v hx, hx.1, hx.2.1⟩

/--
%%handwave
name:
  The opposite pole cut lies in the punctured pole disk
statement:
  The opposite slit pole-coordinate disk is contained in the punctured
  pole-coordinate disk of the same radius.
proof:
  Its points lie in the chart ball and differ from the pole, so they satisfy
  the punctured-disk criterion.
-/
theorem rightPoleCut_le_puncturedPoleDisk (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) : D.rightPoleCut v ≤ D.puncturedPoleDisk := by
  intro x hx
  exact D.puncturedPoleDisk_mem_iff.mpr
    ⟨D.rightPoleCut_ne_p v hx, hx.1, hx.2.1⟩

/--
%%handwave
name:
  Relative first pole cut lies in the relative punctured disk
statement:
  Viewed as open sets of \(X\setminus\{p\}\), the first slit pole disk is
  contained in the punctured pole-coordinate disk.
proof:
  Restrict the ambient inclusion of the first pole cut into the punctured
  pole disk to the punctured surface.
-/
theorem puncturedLeftPoleCut_le_puncturedPoleDisk (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) :
    openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v) ≤
      openWithinOpen (puncturedSurfaceOpen p) D.puncturedPoleDisk := by
  intro x hx
  exact D.leftPoleCut_le_puncturedPoleDisk v hx

/--
%%handwave
name:
  Relative opposite pole cut lies in the relative punctured disk
statement:
  Viewed as open sets of \(X\setminus\{p\}\), the opposite slit pole disk is
  contained in the punctured pole-coordinate disk.
proof:
  Restrict the ambient inclusion of the opposite pole cut into the punctured
  pole disk to the punctured surface.
-/
theorem puncturedRightPoleCut_le_puncturedPoleDisk (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) :
    openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v) ≤
      openWithinOpen (puncturedSurfaceOpen p) D.puncturedPoleDisk := by
  intro x hx
  exact D.rightPoleCut_le_puncturedPoleDisk v hx

/-- A radial slit in the punctured pole disk is the corresponding slit in
the ambient pole coordinate. -/
noncomputable def radialLeftCutPoleCutDiffeomorph (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    D.radialLeftCut v ≃ₘ⟮SurfaceRealModel,
      SurfaceRealModel⟯ D.leftPoleCut v := by
  let toRaw : D.radialLeftCut v → X := fun x => (x.1.1 : X)
  have htoRaw : ContMDiff SurfaceRealModel SurfaceRealModel ∞ toRaw :=
    (contMDiff_subtype_val (I := SurfaceRealModel) (n := ∞)
      (U := D.puncturedPoleDisk)).comp
      (contMDiff_subtype_val (I := SurfaceRealModel) (n := ∞)
        (U := D.radialLeftCut v))
  let toCut : D.radialLeftCut v → D.leftPoleCut v := fun x =>
    ⟨toRaw x, (D.radialLeftCut_mem_iff_leftPoleCut v x.1).mp x.2⟩
  have hto : ContMDiff SurfaceRealModel SurfaceRealModel ∞ toCut :=
    ContMDiff.codRestrict_open htoRaw (D.leftPoleCut v)
      (fun x => (toCut x).2)
  have hmemPole : ∀ y : D.leftPoleCut v,
      (y : X) ∈ D.puncturedPoleDisk := by
    intro y
    exact D.puncturedPoleDisk_mem_iff.mpr
      ⟨D.leftPoleCut_ne_p v y.2, y.2.1, y.2.2.1⟩
  let fromPole : D.leftPoleCut v → D.puncturedPoleDisk := fun y =>
    ⟨(y : X), hmemPole y⟩
  have hfromPole : ContMDiff SurfaceRealModel SurfaceRealModel ∞ fromPole :=
    ContMDiff.codRestrict_open
      (contMDiff_subtype_val (I := SurfaceRealModel) (n := ∞))
      D.puncturedPoleDisk hmemPole
  let fromCut : D.leftPoleCut v → D.radialLeftCut v := fun y =>
    ⟨fromPole y,
      (D.radialLeftCut_mem_iff_leftPoleCut v (fromPole y)).mpr y.2⟩
  have hfrom : ContMDiff SurfaceRealModel SurfaceRealModel ∞ fromCut :=
    ContMDiff.codRestrict_open hfromPole (D.radialLeftCut v)
      (fun y => (fromCut y).2)
  exact
    { toEquiv :=
        { toFun := toCut
          invFun := fromCut
          left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := by intro y; apply Subtype.ext; rfl }
      contMDiff_toFun := hto
      contMDiff_invFun := hfrom }

/-- The opposite radial slit is the corresponding opposite pole-coordinate
slit. -/
noncomputable def radialRightCutPoleCutDiffeomorph (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    D.radialRightCut v ≃ₘ⟮SurfaceRealModel,
      SurfaceRealModel⟯ D.rightPoleCut v := by
  let toRaw : D.radialRightCut v → X := fun x => (x.1.1 : X)
  have htoRaw : ContMDiff SurfaceRealModel SurfaceRealModel ∞ toRaw :=
    (contMDiff_subtype_val (I := SurfaceRealModel) (n := ∞)
      (U := D.puncturedPoleDisk)).comp
      (contMDiff_subtype_val (I := SurfaceRealModel) (n := ∞)
        (U := D.radialRightCut v))
  let toCut : D.radialRightCut v → D.rightPoleCut v := fun x =>
    ⟨toRaw x, (D.radialRightCut_mem_iff_rightPoleCut v x.1).mp x.2⟩
  have hto : ContMDiff SurfaceRealModel SurfaceRealModel ∞ toCut :=
    ContMDiff.codRestrict_open htoRaw (D.rightPoleCut v)
      (fun x => (toCut x).2)
  have hmemPole : ∀ y : D.rightPoleCut v,
      (y : X) ∈ D.puncturedPoleDisk := by
    intro y
    exact D.puncturedPoleDisk_mem_iff.mpr
      ⟨D.rightPoleCut_ne_p v y.2, y.2.1, y.2.2.1⟩
  let fromPole : D.rightPoleCut v → D.puncturedPoleDisk := fun y =>
    ⟨(y : X), hmemPole y⟩
  have hfromPole : ContMDiff SurfaceRealModel SurfaceRealModel ∞ fromPole :=
    ContMDiff.codRestrict_open
      (contMDiff_subtype_val (I := SurfaceRealModel) (n := ∞))
      D.puncturedPoleDisk hmemPole
  let fromCut : D.rightPoleCut v → D.radialRightCut v := fun y =>
    ⟨fromPole y,
      (D.radialRightCut_mem_iff_rightPoleCut v (fromPole y)).mpr y.2⟩
  have hfrom : ContMDiff SurfaceRealModel SurfaceRealModel ∞ fromCut :=
    ContMDiff.codRestrict_open hfromPole (D.radialRightCut v)
      (fun y => (fromCut y).2)
  exact
    { toEquiv :=
        { toFun := toCut
          invFun := fromCut
          left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := by intro y; apply Subtype.ext; rfl }
      contMDiff_toFun := hto
      contMDiff_invFun := hfrom }

/-- Radial coordinates followed by the inclusion into the punctured surface. -/
noncomputable def annularToPuncturedPoleWithinDiffeomorph (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] :
    (Circle × ℝ) ≃ₘ⟮AnnularCylinderModel,
      SurfaceRealModel⟯
      openWithinOpen (puncturedSurfaceOpen p) D.puncturedPoleDisk :=
  D.radialDiffeomorph.symm.trans
    (openWithinOpenDiffeomorph (puncturedSurfaceOpen p)
      D.puncturedPoleDisk D.puncturedPoleDisk_le_puncturedSurfaceOpen).symm

/-- On the first slit, radial coordinates identify the standard annular chart
with the same slit regarded inside the punctured surface. -/
noncomputable def annularLeftCutToPuncturedCutDiffeomorph (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    annularPunctureOpen v ≃ₘ⟮AnnularCylinderModel,
      SurfaceRealModel⟯
      openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v) :=
  (D.radialPreimageDiffeomorph (annularPunctureOpen v)).symm |>.trans
    (D.radialLeftCutPoleCutDiffeomorph v) |>.trans
      (openWithinOpenDiffeomorph (puncturedSurfaceOpen p)
        (D.leftPoleCut v) (D.leftPoleCut_le_puncturedSurfaceOpen v)).symm

/-- The analogous radial identification on the opposite slit. -/
noncomputable def annularRightCutToPuncturedCutDiffeomorph (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    annularPunctureOpen (annularOpposite v) ≃ₘ⟮AnnularCylinderModel,
      SurfaceRealModel⟯
      openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v) :=
  (D.radialPreimageDiffeomorph
      (annularPunctureOpen (annularOpposite v))).symm |>.trans
    (D.radialRightCutPoleCutDiffeomorph v) |>.trans
      (openWithinOpenDiffeomorph (puncturedSurfaceOpen p)
        (D.rightPoleCut v) (D.rightPoleCut_le_puncturedSurfaceOpen v)).symm

/-- The imaginary part of the first pole logarithm in standard annular
coordinates. -/
noncomputable def annularLeftPoleLogImaginarySmoothFunction (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    C^∞⟮AnnularCylinderModel, annularPunctureOpen v; ℝ⟯ := by
  let B := D.leftPoleLogBranch v
  let psi := (D.radialPreimageDiffeomorph
    (annularPunctureOpen v)).symm.trans
      (D.radialLeftCutPoleCutDiffeomorph v)
  exact ⟨fun q => B.imaginarySmoothFunction (psi q),
    B.imaginarySmoothFunction.property.comp psi.contMDiff⟩

/-- The imaginary part of the opposite pole logarithm in standard annular
coordinates. -/
noncomputable def annularRightPoleLogImaginarySmoothFunction (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    C^∞⟮AnnularCylinderModel,
      annularPunctureOpen (annularOpposite v); ℝ⟯ := by
  let B := D.rightPoleLogBranch v
  let psi := (D.radialPreimageDiffeomorph
    (annularPunctureOpen (annularOpposite v))).symm.trans
      (D.radialRightCutPoleCutDiffeomorph v)
  exact ⟨fun q => B.imaginarySmoothFunction (psi q),
    B.imaginarySmoothFunction.property.comp psi.contMDiff⟩

/--
%%handwave
name:
  Evaluation of the left annular pole-logarithm imaginary part
statement:
  At a point \(q\) of the left slit annulus, the transported smooth function
  equals the imaginary part of the left pole logarithm at the inverse radial
  coordinate of \(q\).
proof:
  This is the defining formula for the transported smooth function.
-/
@[simp]
theorem annularLeftPoleLogImaginarySmoothFunction_apply (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle)
    (q : annularPunctureOpen v) :
    D.annularLeftPoleLogImaginarySmoothFunction v q =
      (D.leftPoleLog v
        ((D.radialDiffeomorph.symm (q : Circle × ℝ) :
          D.puncturedPoleDisk) : X)).im := by
  rfl

/--
%%handwave
name:
  Evaluation of the right annular pole-logarithm imaginary part
statement:
  At a point of the opposite slit annulus, the transported smooth function is
  the imaginary part of the right pole logarithm at its inverse radial
  coordinate.
proof:
  This is immediate from the definition by radial transport.
-/
@[simp]
theorem annularRightPoleLogImaginarySmoothFunction_apply (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle)
    (q : annularPunctureOpen (annularOpposite v)) :
    D.annularRightPoleLogImaginarySmoothFunction v q =
      (D.rightPoleLog v
        ((D.radialDiffeomorph.symm (q : Circle × ℝ) :
          D.puncturedPoleDisk) : X)).im := by
  rfl

noncomputable def annularLeftPoleLogZeroForm (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    SmoothForms (I := AnnularCylinderModel)
      (M := annularPunctureOpen v) ℝ 0 :=
  smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
    (D.annularLeftPoleLogImaginarySmoothFunction v)

noncomputable def annularRightPoleLogZeroForm (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    SmoothForms (I := AnnularCylinderModel)
      (M := annularPunctureOpen (annularOpposite v)) ℝ 0 :=
  smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
    (D.annularRightPoleLogImaginarySmoothFunction v)

/-- The first logarithm's imaginary part on the corresponding open subset of
the punctured surface. -/
noncomputable def puncturedLeftPoleLogImaginarySmoothFunction (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    C^∞⟮SurfaceRealModel,
      openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v); ℝ⟯ := by
  let B := D.leftPoleLogBranch v
  let psi := openWithinOpenDiffeomorph (puncturedSurfaceOpen p)
    (D.leftPoleCut v) (D.leftPoleCut_le_puncturedSurfaceOpen v)
  exact ⟨fun x => B.imaginarySmoothFunction (psi x),
    B.imaginarySmoothFunction.property.comp psi.contMDiff⟩

/-- The opposite logarithm's imaginary part on the punctured surface. -/
noncomputable def puncturedRightPoleLogImaginarySmoothFunction (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle) :
    C^∞⟮SurfaceRealModel,
      openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v); ℝ⟯ := by
  let B := D.rightPoleLogBranch v
  let psi := openWithinOpenDiffeomorph (puncturedSurfaceOpen p)
    (D.rightPoleCut v) (D.rightPoleCut_le_puncturedSurfaceOpen v)
  exact ⟨fun x => B.imaginarySmoothFunction (psi x),
    B.imaginarySmoothFunction.property.comp psi.contMDiff⟩

/--
%%handwave
name:
  Evaluation of the left punctured pole-logarithm imaginary part
statement:
  On the left pole cut, the corresponding smooth function evaluates to the
  imaginary part of the left logarithmic branch.
proof:
  This is the defining formula after identifying the open subset with its
  ambient pole cut.
-/
@[simp]
theorem puncturedLeftPoleLogImaginarySmoothFunction_apply (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle)
    (x : openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v)) :
    D.puncturedLeftPoleLogImaginarySmoothFunction v x =
      (D.leftPoleLog v (x.1 : X)).im := by
  rfl

/--
%%handwave
name:
  Evaluation of the right punctured pole-logarithm imaginary part
statement:
  On the right pole cut, the associated smooth function evaluates to the
  imaginary part of the right logarithmic branch.
proof:
  This is the defining evaluation formula for the transported function.
-/
@[simp]
theorem puncturedRightPoleLogImaginarySmoothFunction_apply (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X] (v : Circle)
    (x : openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v)) :
    D.puncturedRightPoleLogImaginarySmoothFunction v x =
      (D.rightPoleLog v (x.1 : X)).im := by
  rfl

/--
%%handwave
name:
  Green conjugate as a logarithmic imaginary differential on the left cut
statement:
  On the left pole-coordinate cut, the punctured Green-conjugate one-form is
  \(\omega_G=d\,\operatorname{Im}L_v\), where \(L_v\) is the left
  holomorphic logarithmic branch.
proof:
  The branch is holomorphic on the cut and has real part \(-G\).  The local
  harmonic-conjugate identity identifies the glued conjugate differential with
  the differential of its imaginary part.
-/
theorem puncturedConjugate_restrict_leftPoleCut (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
        (openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v)) 1
        C.conjugate.omega =
      deRhamDifferential (I := SurfaceRealModel)
        (M := openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v))
        (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
          (D.puncturedLeftPoleLogImaginarySmoothFunction v)) := by
  let U : TopologicalSpace.Opens (puncturedSurfaceOpen p) :=
    openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v)
  let L : puncturedSurfaceOpen p → ℂ := fun x =>
    D.leftPoleLog v (x : X)
  have hsub : MDifferentiableOn (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ)
      (fun x : puncturedSurfaceOpen p => (x : X)) U :=
    (contMDiff_subtype_val (I := modelWithCornersSelf ℂ ℂ) (n := ∞)
      (U := puncturedSurfaceOpen p)).contMDiffOn.mdifferentiableOn (by simp)
  have hL : MDifferentiableOn (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) L U := by
    exact (D.leftPoleLog_mdifferentiableOn v).comp hsub
      (fun x hx => hx)
  apply C.conjugate.restrict_eq_globalHolomorphicRealPart U L hL
      (D.puncturedLeftPoleLogImaginarySmoothFunction v)
  · intro x
    rfl
  · intro x
    exact D.leftPoleLog_re_eq_neg_green v x.2

/--
%%handwave
name:
  Green conjugate as a logarithmic imaginary differential on the right cut
statement:
  On the opposite pole-coordinate cut, the punctured Green-conjugate one-form
  equals \(d\,\operatorname{Im}R_v\), where \(R_v\) is the right logarithmic
  branch.
proof:
  The right branch is holomorphic and has real part \(-G\) on its cut.  Apply
  the same harmonic-conjugate differential identity.
-/
theorem puncturedConjugate_restrict_rightPoleCut (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
        (openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v)) 1
        C.conjugate.omega =
      deRhamDifferential (I := SurfaceRealModel)
        (M := openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v))
        (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
          (D.puncturedRightPoleLogImaginarySmoothFunction v)) := by
  let U : TopologicalSpace.Opens (puncturedSurfaceOpen p) :=
    openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v)
  let L : puncturedSurfaceOpen p → ℂ := fun x =>
    D.rightPoleLog v (x : X)
  have hsub : MDifferentiableOn (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ)
      (fun x : puncturedSurfaceOpen p => (x : X)) U :=
    (contMDiff_subtype_val (I := modelWithCornersSelf ℂ ℂ) (n := ∞)
      (U := puncturedSurfaceOpen p)).contMDiffOn.mdifferentiableOn (by simp)
  have hL : MDifferentiableOn (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) L U := by
    exact (D.rightPoleLog_mdifferentiableOn v).comp hsub
      (fun x hx => hx)
  apply C.conjugate.restrict_eq_globalHolomorphicRealPart U L hL
      (D.puncturedRightPoleLogImaginarySmoothFunction v)
  · intro x
    rfl
  · intro x
    exact D.rightPoleLog_re_eq_neg_green v x.2

/-- The Green conjugate differential near its pole, transported to the
standard annular cylinder by the radial pole coordinate. -/
noncomputable def greenConjugateAnnularClosedForm (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G) :
    DeRhamClosedForms (I := AnnularCylinderModel)
      (M := Circle × ℝ) (A := ℝ) 1 :=
  let W := openWithinOpen (puncturedSurfaceOpen p) D.puncturedPoleDisk
  let omegaW : DeRhamClosedForms (I := SurfaceRealModel)
      (M := W) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionToOpen (I := SurfaceRealModel) (A := ℝ)
      W 1 C.toClosedForm
  deRhamClosedFormsPullbackDiffeomorph AnnularCylinderModel
    SurfaceRealModel D.annularToPuncturedPoleWithinDiffeomorph 1 omegaW

/--
%%handwave
name:
  Radial pullback of the Green conjugate on the left slit
statement:
  Pulling the punctured Green-conjugate one-form on the left pole cut back to
  the left slit annulus gives the exterior derivative of the transported left
  logarithmic imaginary part.
proof:
  Pull back \(\omega_G=d\,\operatorname{Im}L_v\).  Naturality moves \(d\)
  through the radial diffeomorphism, and the pulled-back zero-form is the
  annular logarithmic imaginary function.
-/
theorem puncturedConjugate_leftPoleCut_radialPullback (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    smoothFormsPullbackDiffeomorph AnnularCylinderModel SurfaceRealModel
        (D.annularLeftCutToPuncturedCutDiffeomorph v) 1
        (restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
          (openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v)) 1
          C.conjugate.omega) =
      deRhamDifferential (I := AnnularCylinderModel)
        (M := annularPunctureOpen v) (A := ℝ) 0
        (D.annularLeftPoleLogZeroForm v) := by
  let psi := D.annularLeftCutToPuncturedCutDiffeomorph v
  let thetaP : SmoothForms (I := SurfaceRealModel)
      (M := openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v))
      ℝ 0 :=
    smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
      (D.puncturedLeftPoleLogImaginarySmoothFunction v)
  have hlocal := D.puncturedConjugate_restrict_leftPoleCut C v
  have hzero :
      smoothFormsPullbackDiffeomorph AnnularCylinderModel SurfaceRealModel
          psi 0 thetaP = D.annularLeftPoleLogZeroForm v := by
    apply DifferentialForm.ext
    intro q
    ext w
    rw [show w = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
    rfl
  calc
    smoothFormsPullbackDiffeomorph AnnularCylinderModel SurfaceRealModel
        psi 1
        (restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
          (openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v)) 1
          C.conjugate.omega) =
      smoothFormsPullbackDiffeomorph AnnularCylinderModel SurfaceRealModel
        psi 1
        (deRhamDifferential (I := SurfaceRealModel)
          (M := openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v))
          (A := ℝ) 0 thetaP) := by rw [hlocal]
    _ = deRhamDifferential (I := AnnularCylinderModel)
        (M := annularPunctureOpen v) (A := ℝ) 0
        (smoothFormsPullbackDiffeomorph AnnularCylinderModel
          SurfaceRealModel psi 0 thetaP) := by
      rw [deRhamDifferential_smoothFormsPullbackDiffeomorph]
    _ = deRhamDifferential (I := AnnularCylinderModel)
        (M := annularPunctureOpen v) (A := ℝ) 0
        (D.annularLeftPoleLogZeroForm v) := by rw [hzero]

/--
%%handwave
name:
  Radial pullback of the Green conjugate on the right slit
statement:
  Pulling the punctured Green-conjugate form on the right pole cut back to the
  opposite slit annulus gives the derivative of the transported right
  logarithmic imaginary part.
proof:
  Pull back the right-cut primitive identity and use naturality of \(d\); the
  pulled-back zero-form is the right annular logarithmic function.
-/
theorem puncturedConjugate_rightPoleCut_radialPullback (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    smoothFormsPullbackDiffeomorph AnnularCylinderModel SurfaceRealModel
        (D.annularRightCutToPuncturedCutDiffeomorph v) 1
        (restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
          (openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v)) 1
          C.conjugate.omega) =
      deRhamDifferential (I := AnnularCylinderModel)
        (M := annularPunctureOpen (annularOpposite v)) (A := ℝ) 0
        (D.annularRightPoleLogZeroForm v) := by
  let psi := D.annularRightCutToPuncturedCutDiffeomorph v
  let thetaP : SmoothForms (I := SurfaceRealModel)
      (M := openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v))
      ℝ 0 :=
    smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
      (D.puncturedRightPoleLogImaginarySmoothFunction v)
  have hlocal := D.puncturedConjugate_restrict_rightPoleCut C v
  have hzero :
      smoothFormsPullbackDiffeomorph AnnularCylinderModel SurfaceRealModel
          psi 0 thetaP = D.annularRightPoleLogZeroForm v := by
    apply DifferentialForm.ext
    intro q
    ext w
    rw [show w = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
    rfl
  calc
    smoothFormsPullbackDiffeomorph AnnularCylinderModel SurfaceRealModel
        psi 1
        (restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
          (openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v)) 1
          C.conjugate.omega) =
      smoothFormsPullbackDiffeomorph AnnularCylinderModel SurfaceRealModel
        psi 1
        (deRhamDifferential (I := SurfaceRealModel)
          (M := openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v))
          (A := ℝ) 0 thetaP) := by rw [hlocal]
    _ = deRhamDifferential (I := AnnularCylinderModel)
        (M := annularPunctureOpen (annularOpposite v)) (A := ℝ) 0
        (smoothFormsPullbackDiffeomorph AnnularCylinderModel
          SurfaceRealModel psi 0 thetaP) := by
      rw [deRhamDifferential_smoothFormsPullbackDiffeomorph]
    _ = deRhamDifferential (I := AnnularCylinderModel)
        (M := annularPunctureOpen (annularOpposite v)) (A := ℝ) 0
        (D.annularRightPoleLogZeroForm v) := by rw [hzero]

/--
%%handwave
name:
  Left restriction of the annular Green form as a radial pullback
statement:
  Restricting the annular representative of the Green conjugate to the left
  slit equals the radial pullback of the punctured Green conjugate restricted
  to the corresponding left pole cut.
proof:
  Expand both sides as restrictions and pullbacks.  Their composite maps to
  the punctured surface agree pointwise; the chain rule identifies the tangent
  pullbacks and hence the forms.
-/
theorem greenConjugateAnnularClosedForm_restrict_left_eq_radialPullback (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
        (annularPunctureOpen v) 1 (D.greenConjugateAnnularClosedForm C).1 =
      smoothFormsPullbackDiffeomorph AnnularCylinderModel SurfaceRealModel
        (D.annularLeftCutToPuncturedCutDiffeomorph v) 1
        (restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
          (openWithinOpen (puncturedSurfaceOpen p) (D.leftPoleCut v)) 1
          C.conjugate.omega) := by
  let U := puncturedSurfaceOpen p
  let W := openWithinOpen U D.puncturedPoleDisk
  let A := openWithinOpen U (D.leftPoleCut v)
  let S := annularPunctureOpen v
  let phi := D.annularToPuncturedPoleWithinDiffeomorph
  let psi := D.annularLeftCutToPuncturedCutDiffeomorph v
  let incS : S → Circle × ℝ := fun x => (x : Circle × ℝ)
  let incW : W → U := fun x => (x : U)
  let incA : A → U := fun x => (x : U)
  let f : S → U := fun x => incW (phi (incS x))
  let g : S → U := fun x => incA (psi x)
  have hfg : f = g := by
    funext x
    apply Subtype.ext
    rfl
  apply DifferentialForm.ext
  intro x
  ext q
  have hphiInc :
      mfderiv AnnularCylinderModel SurfaceRealModel
          (fun y : S => phi (incS y)) x =
        (mfderiv AnnularCylinderModel SurfaceRealModel phi (incS x)).comp
          (mfderiv AnnularCylinderModel AnnularCylinderModel incS x) := by
    exact mfderiv_comp x
      (phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (I := AnnularCylinderModel)
        (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
  have hfDeriv :
      mfderiv AnnularCylinderModel SurfaceRealModel f x =
        (mfderiv SurfaceRealModel SurfaceRealModel incW
          (phi (incS x))).comp
          ((mfderiv AnnularCylinderModel SurfaceRealModel phi
            (incS x)).comp
            (mfderiv AnnularCylinderModel AnnularCylinderModel incS x)) := by
    have houter :
        mfderiv AnnularCylinderModel SurfaceRealModel
            (incW ∘ (fun y : S => phi (incS y))) x =
          (mfderiv SurfaceRealModel SurfaceRealModel incW
            (phi (incS x))).comp
            (mfderiv AnnularCylinderModel SurfaceRealModel
              (fun y : S => phi (incS y)) x) := mfderiv_comp x
      ((contMDiff_subtype_val (I := SurfaceRealModel)
        (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
      ((phi.contMDiff.comp
        (contMDiff_subtype_val (I := AnnularCylinderModel)
          (n := ∞))).contMDiffAt.mdifferentiableAt (by simp))
    change mfderiv AnnularCylinderModel SurfaceRealModel
      (incW ∘ (fun y : S => phi (incS y))) x = _
    rw [houter, hphiInc]
  have hgDeriv :
      mfderiv AnnularCylinderModel SurfaceRealModel g x =
        (mfderiv SurfaceRealModel SurfaceRealModel incA (psi x)).comp
          (mfderiv AnnularCylinderModel SurfaceRealModel psi x) := by
    have h := mfderiv_comp x
      ((contMDiff_subtype_val (I := SurfaceRealModel)
        (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
      (psi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    change mfderiv AnnularCylinderModel SurfaceRealModel g x = _
    simpa [g, Function.comp_def] using h
  have hDeriv :
      (mfderiv SurfaceRealModel SurfaceRealModel incW (phi (incS x))).comp
          ((mfderiv AnnularCylinderModel SurfaceRealModel phi
            (incS x)).comp
            (mfderiv AnnularCylinderModel AnnularCylinderModel incS x)) =
        (mfderiv SurfaceRealModel SurfaceRealModel incA (psi x)).comp
          (mfderiv AnnularCylinderModel SurfaceRealModel psi x) := by
    rw [← hfDeriv, ← hgDeriv, hfg]
  change
    ((((C.conjugate.omega.toFun (incW (phi (incS x)))).compContinuousLinearMap
          (mfderiv SurfaceRealModel SurfaceRealModel incW
            (phi (incS x)))).compContinuousLinearMap
          (mfderiv AnnularCylinderModel SurfaceRealModel phi (incS x))).compContinuousLinearMap
        (mfderiv AnnularCylinderModel AnnularCylinderModel incS x)) q =
      (((C.conjugate.omega.toFun (incA (psi x))).compContinuousLinearMap
          (mfderiv SurfaceRealModel SurfaceRealModel incA (psi x))).compContinuousLinearMap
        (mfderiv AnnularCylinderModel SurfaceRealModel psi x)) q
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hpoint : incW (phi (incS x)) = incA (psi x) :=
    congrFun hfg x
  rw [hpoint]
  congr 1
  funext i
  exact congrArg (fun L => L (q i)) hDeriv

/--
%%handwave
name:
  Right restriction of the annular Green form as a radial pullback
statement:
  Restricting the annular Green-conjugate representative to the opposite slit
  equals the radial pullback of the punctured form on the right pole cut.
proof:
  The relevant restriction and radial-coordinate composites agree as maps.
  Apply the manifold chain rule to identify their pullbacks pointwise.
-/
theorem greenConjugateAnnularClosedForm_restrict_right_eq_radialPullback (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
        (annularPunctureOpen (annularOpposite v)) 1
        (D.greenConjugateAnnularClosedForm C).1 =
      smoothFormsPullbackDiffeomorph AnnularCylinderModel SurfaceRealModel
        (D.annularRightCutToPuncturedCutDiffeomorph v) 1
        (restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
          (openWithinOpen (puncturedSurfaceOpen p) (D.rightPoleCut v)) 1
          C.conjugate.omega) := by
  let U := puncturedSurfaceOpen p
  let W := openWithinOpen U D.puncturedPoleDisk
  let A := openWithinOpen U (D.rightPoleCut v)
  let S := annularPunctureOpen (annularOpposite v)
  let phi := D.annularToPuncturedPoleWithinDiffeomorph
  let psi := D.annularRightCutToPuncturedCutDiffeomorph v
  let incS : S → Circle × ℝ := fun x => (x : Circle × ℝ)
  let incW : W → U := fun x => (x : U)
  let incA : A → U := fun x => (x : U)
  let f : S → U := fun x => incW (phi (incS x))
  let g : S → U := fun x => incA (psi x)
  have hfg : f = g := by
    funext x
    apply Subtype.ext
    rfl
  apply DifferentialForm.ext
  intro x
  ext q
  have hphiInc :
      mfderiv AnnularCylinderModel SurfaceRealModel
          (fun y : S => phi (incS y)) x =
        (mfderiv AnnularCylinderModel SurfaceRealModel phi (incS x)).comp
          (mfderiv AnnularCylinderModel AnnularCylinderModel incS x) := by
    exact mfderiv_comp x
      (phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (I := AnnularCylinderModel)
        (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
  have hfDeriv :
      mfderiv AnnularCylinderModel SurfaceRealModel f x =
        (mfderiv SurfaceRealModel SurfaceRealModel incW
          (phi (incS x))).comp
          ((mfderiv AnnularCylinderModel SurfaceRealModel phi
            (incS x)).comp
            (mfderiv AnnularCylinderModel AnnularCylinderModel incS x)) := by
    have houter :
        mfderiv AnnularCylinderModel SurfaceRealModel
            (incW ∘ (fun y : S => phi (incS y))) x =
          (mfderiv SurfaceRealModel SurfaceRealModel incW
            (phi (incS x))).comp
            (mfderiv AnnularCylinderModel SurfaceRealModel
              (fun y : S => phi (incS y)) x) := mfderiv_comp x
      ((contMDiff_subtype_val (I := SurfaceRealModel)
        (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
      ((phi.contMDiff.comp
        (contMDiff_subtype_val (I := AnnularCylinderModel)
          (n := ∞))).contMDiffAt.mdifferentiableAt (by simp))
    change mfderiv AnnularCylinderModel SurfaceRealModel
      (incW ∘ (fun y : S => phi (incS y))) x = _
    rw [houter, hphiInc]
  have hgDeriv :
      mfderiv AnnularCylinderModel SurfaceRealModel g x =
        (mfderiv SurfaceRealModel SurfaceRealModel incA (psi x)).comp
          (mfderiv AnnularCylinderModel SurfaceRealModel psi x) := by
    have h := mfderiv_comp x
      ((contMDiff_subtype_val (I := SurfaceRealModel)
        (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
      (psi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    change mfderiv AnnularCylinderModel SurfaceRealModel g x = _
    simpa [g, Function.comp_def] using h
  have hDeriv :
      (mfderiv SurfaceRealModel SurfaceRealModel incW (phi (incS x))).comp
          ((mfderiv AnnularCylinderModel SurfaceRealModel phi
            (incS x)).comp
            (mfderiv AnnularCylinderModel AnnularCylinderModel incS x)) =
        (mfderiv SurfaceRealModel SurfaceRealModel incA (psi x)).comp
          (mfderiv AnnularCylinderModel SurfaceRealModel psi x) := by
    rw [← hfDeriv, ← hgDeriv, hfg]
  change
    ((((C.conjugate.omega.toFun (incW (phi (incS x)))).compContinuousLinearMap
          (mfderiv SurfaceRealModel SurfaceRealModel incW
            (phi (incS x)))).compContinuousLinearMap
          (mfderiv AnnularCylinderModel SurfaceRealModel phi (incS x))).compContinuousLinearMap
        (mfderiv AnnularCylinderModel AnnularCylinderModel incS x)) q =
      (((C.conjugate.omega.toFun (incA (psi x))).compContinuousLinearMap
          (mfderiv SurfaceRealModel SurfaceRealModel incA (psi x))).compContinuousLinearMap
        (mfderiv AnnularCylinderModel SurfaceRealModel psi x)) q
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hpoint : incW (phi (incS x)) = incA (psi x) :=
    congrFun hfg x
  rw [hpoint]
  congr 1
  funext i
  exact congrArg (fun L => L (q i)) hDeriv

/--
%%handwave
name:
  Left slit primitive of the annular Green conjugate
statement:
  On the annulus cut along the direction \(v\), the restriction of the Green
  conjugate one-form is the exterior derivative of the imaginary part of the
  left logarithmic branch.
proof:
  The annular Green form restricts to the radial pullback of the punctured
  conjugate.  The left logarithmic-branch identity identifies that pullback
  with the derivative of the left logarithmic zero-form.
-/
theorem greenConjugateAnnularClosedForm_restrict_left (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
        (annularPunctureOpen v) 1 (D.greenConjugateAnnularClosedForm C).1 =
      deRhamDifferential (I := AnnularCylinderModel)
        (M := annularPunctureOpen v) (A := ℝ) 0
        (D.annularLeftPoleLogZeroForm v) := by
  rw [D.greenConjugateAnnularClosedForm_restrict_left_eq_radialPullback C v]
  exact D.puncturedConjugate_leftPoleCut_radialPullback C v

/--
%%handwave
name:
  Right slit primitive of the annular Green conjugate
statement:
  On the annulus cut along the opposite direction, the restriction of the
  Green conjugate one-form is the exterior derivative of the imaginary part
  of the right logarithmic branch.
proof:
  Restrict the annular form to the right cut, identify it with the radial
  pullback of the punctured conjugate, and use the right logarithmic-branch
  differential identity.
-/
theorem greenConjugateAnnularClosedForm_restrict_right (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
        (annularPunctureOpen (annularOpposite v)) 1
        (D.greenConjugateAnnularClosedForm C).1 =
      deRhamDifferential (I := AnnularCylinderModel)
        (M := annularPunctureOpen (annularOpposite v)) (A := ℝ) 0
        (D.annularRightPoleLogZeroForm v) := by
  rw [D.greenConjugateAnnularClosedForm_restrict_right_eq_radialPullback C v]
  exact D.puncturedConjugate_rightPoleCut_radialPullback C v

/--
%%handwave
name:
  Imaginary logarithm of a rotated nonzero complex number
statement:
  For \(w\ne0\) and \(v\in S^1\),
  \[
    \operatorname{Im}\log(-v^{-1}w)
      =\operatorname{Im}\log\!\left(-v^{-1}\frac{w}{|w|}\right).
  \]
proof:
  Factor \(-v^{-1}w\) as the positive real scalar \(|w|\) times its rotated
  unit direction.  The logarithm of the positive factor is real, so it does
  not affect the imaginary part.
-/
theorem complexLog_rotated_im_eq_direction
    (v : Circle) {w : ℂ} (hw : w ≠ 0) :
    (Complex.log (-((v⁻¹ : Circle) : ℂ) * w)).im =
      (Complex.log
        (annularCutRotation v
          (complexPuncturedPlaneDirection ⟨w, hw⟩) : ℂ)).im := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwdecomp :
      (‖w‖ : ℂ) * NormedSpace.normalize w = w := by
    simpa only [Complex.real_smul] using
      NormedSpace.norm_smul_normalize w
  have hdecomp :
      -((v⁻¹ : Circle) : ℂ) * w =
        (‖w‖ : ℂ) *
          (annularCutRotation v
            (complexPuncturedPlaneDirection ⟨w, hw⟩) : ℂ) := by
    calc
      -((v⁻¹ : Circle) : ℂ) * w =
          -((v⁻¹ : Circle) : ℂ) *
            ((‖w‖ : ℂ) * NormedSpace.normalize w) := by
        rw [hwdecomp]
      _ = (‖w‖ : ℂ) *
          (annularCutRotation v
            (complexPuncturedPlaneDirection ⟨w, hw⟩) : ℂ) := by
        simp [complexPuncturedPlaneDirection, annularCutRotation,
          circleAntipode]
        ring
  rw [hdecomp, Complex.log_ofReal_mul hnorm
    (Circle.coe_ne_zero _)]
  simp

/--
%%handwave
name:
  Imaginary logarithm in the opposite rotated direction
statement:
  For \(w\ne0\) and \(v\in S^1\), the imaginary part of
  \(\log(v^{-1}w)\) equals the imaginary part of the logarithm of the antipode
  of the rotated unit direction \(-v^{-1}w/|w|\).
proof:
  Factor \(v^{-1}w\) as \(|w|\) times that antipodal unit direction.  The
  positive real factor contributes only a real logarithm.
-/
theorem complexLog_oppositeRotated_im_eq_direction
    (v : Circle) {w : ℂ} (hw : w ≠ 0) :
    (Complex.log (((v⁻¹ : Circle) : ℂ) * w)).im =
      (Complex.log
        (circleAntipode
          (annularCutRotation v
            (complexPuncturedPlaneDirection ⟨w, hw⟩)) : ℂ)).im := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwdecomp :
      (‖w‖ : ℂ) * NormedSpace.normalize w = w := by
    simpa only [Complex.real_smul] using
      NormedSpace.norm_smul_normalize w
  have hdecomp :
      ((v⁻¹ : Circle) : ℂ) * w =
        (‖w‖ : ℂ) *
          (circleAntipode
            (annularCutRotation v
              (complexPuncturedPlaneDirection ⟨w, hw⟩)) : ℂ) := by
    calc
      ((v⁻¹ : Circle) : ℂ) * w =
          ((v⁻¹ : Circle) : ℂ) *
            ((‖w‖ : ℂ) * NormedSpace.normalize w) := by
        rw [hwdecomp]
      _ = (‖w‖ : ℂ) *
          (circleAntipode
            (annularCutRotation v
              (complexPuncturedPlaneDirection ⟨w, hw⟩)) : ℂ) := by
        simp [complexPuncturedPlaneDirection, annularCutRotation,
          circleAntipode]
        ring
  rw [hdecomp, Complex.log_ofReal_mul hnorm
    (Circle.coe_ne_zero _)]
  simp

/--
%%handwave
name:
  Difference of the two pole logarithm arguments
statement:
  On the overlap of the two pole cuts, the difference between the imaginary
  parts of the left and right logarithmic branches equals the annular angle
  transition determined by the cut direction \(v\).
proof:
  Write the nonzero coordinate difference from the pole as its norm times its
  unit direction.  The two preceding logarithm identities reduce the branch
  imaginary parts to the left and right annular angle lifts; their difference
  is the angle transition by definition.
-/
theorem poleLog_im_difference_eq_annularAngleTransition
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (v : Circle) {x : X}
    (hxL : x ∈ D.leftPoleCut v) (_hxR : x ∈ D.rightPoleCut v)
    (q : annularDoublePunctureOpen v)
    (hqdir : ((q : Circle × ℝ).1) =
      complexPuncturedPlaneDirection
        ⟨D.coordinate.chart x - D.coordinate.chart p, by
          intro hzero
          exact D.leftPoleCut_ne_p v hxL
            (D.coordinate.chart.injOn hxL.1
              D.coordinate.base_mem_source (sub_eq_zero.mp hzero))⟩) :
    (D.leftPoleLog v x).im - (D.rightPoleLog v x).im =
      annularAngleTransition v q := by
  let w : ℂ := D.coordinate.chart x - D.coordinate.chart p
  have hw : w ≠ 0 := by
    intro hzero
    exact D.leftPoleCut_ne_p v hxL
      (D.coordinate.chart.injOn hxL.1 D.coordinate.base_mem_source
        (sub_eq_zero.mp hzero))
  have hleft := complexLog_rotated_im_eq_direction v hw
  have hright := complexLog_oppositeRotated_im_eq_direction v hw
  simp only [leftPoleLog, rightPoleLog, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one,
    annularAngleTransition, annularLeftAngleLift,
    annularRightAngleLift]
  rw [show ((q : Circle × ℝ).1) =
      complexPuncturedPlaneDirection ⟨w, hw⟩ by
        simpa [w] using hqdir]
  rw [show
      (Complex.log
        (-((v⁻¹ : Circle) : ℂ) *
          (D.coordinate.chart x - D.coordinate.chart p))).im =
        (Complex.log
          (annularCutRotation v
            (complexPuncturedPlaneDirection ⟨w, hw⟩) : ℂ)).im by
      simpa [w] using hleft]
  rw [show
      (Complex.log
        (((v⁻¹ : Circle) : ℂ) *
          (D.coordinate.chart x - D.coordinate.chart p))).im =
        (Complex.log
          (circleAntipode
            (annularCutRotation v
              (complexPuncturedPlaneDirection ⟨w, hw⟩)) : ℂ)).im by
      simpa [w] using hright]
  ring

/--
%%handwave
name:
  Pole logarithm transition in radial annular coordinates
statement:
  On the overlap of the two radial cuts in the punctured pole disk, the
  difference of the left and right logarithmic imaginary parts is the annular
  angle transition at the radial coordinate of the point.
proof:
  Convert radial-cut membership to membership in the two pole cuts.  The first
  component of the radial diffeomorphism is the unit coordinate direction, so
  the pole-logarithm transition identity applies.
-/
theorem radialPoleLog_im_difference_eq_annularAngleTransition
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (v : Circle)
    (x : (D.radialLeftCut v ⊓ D.radialRightCut v :
      TopologicalSpace.Opens D.puncturedPoleDisk)) :
    let y : D.puncturedPoleDisk := (x : D.puncturedPoleDisk)
    let q : annularDoublePunctureOpen v :=
      ⟨D.radialDiffeomorph y, ⟨x.2.1, x.2.2⟩⟩
    (D.leftPoleLog v (y : X)).im -
        (D.rightPoleLog v (y : X)).im =
      annularAngleTransition v q := by
  dsimp only
  let y : D.puncturedPoleDisk := (x : D.puncturedPoleDisk)
  have hxL : (y : X) ∈ D.leftPoleCut v :=
    (D.radialLeftCut_mem_iff_leftPoleCut v y).mp x.2.1
  have hxR : (y : X) ∈ D.rightPoleCut v :=
    (D.radialRightCut_mem_iff_rightPoleCut v y).mp x.2.2
  let q : annularDoublePunctureOpen v :=
    ⟨D.radialDiffeomorph y, ⟨x.2.1, x.2.2⟩⟩
  apply D.poleLog_im_difference_eq_annularAngleTransition v hxL hxR q
  apply Circle.ext
  simpa [q, y, complexPuncturedPlaneDirection] using
    D.radialDiffeomorph_first_coe y

/--
%%handwave
name:
  The two slit logarithms lift the annular angle transition
statement:
  The Mayer--Vietoris difference of the left and right logarithmic zero-forms
  on the two punctured annuli is exactly the closed zero-form associated with
  the locally constant annular angle transition.
proof:
  Evaluate both zero-forms at a point of the double overlap.  Their difference
  is the difference of the two pole-logarithm imaginary parts, which equals
  the annular angle transition by the radial transition identity.
-/
theorem annularPoleLogZeroForms_difference_eq_transition
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (v : Circle) :
    deRhamMayerVietorisSmoothDifference
        (I := AnnularCylinderModel) (A := ℝ)
        (annularPunctureOpen v)
        (annularPunctureOpen (annularOpposite v)) 0
        (D.annularLeftPoleLogZeroForm v,
          D.annularRightPoleLogZeroForm v) =
      (annularAngleTransitionClosedForm v).1 := by
  apply DifferentialForm.ext
  intro q
  ext w
  rw [show w = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
  let y : D.puncturedPoleDisk :=
    D.radialDiffeomorph.symm (q : Circle × ℝ)
  have hyL : y ∈ D.radialLeftCut v := by
    change D.radialDiffeomorph y ∈ annularPunctureOpen v
    simpa [y] using q.2.1
  have hyR : y ∈ D.radialRightCut v := by
    change D.radialDiffeomorph y ∈
      annularPunctureOpen (annularOpposite v)
    simpa [y] using q.2.2
  have hxL : (y : X) ∈ D.leftPoleCut v :=
    (D.radialLeftCut_mem_iff_leftPoleCut v y).mp hyL
  have hxR : (y : X) ∈ D.rightPoleCut v :=
    (D.radialRightCut_mem_iff_rightPoleCut v y).mp hyR
  have htransition :
      (D.leftPoleLog v (y : X)).im -
          (D.rightPoleLog v (y : X)).im =
        annularAngleTransition v q := by
    apply D.poleLog_im_difference_eq_annularAngleTransition v hxL hxR q
    apply Circle.ext
    have hfirst := D.radialDiffeomorph_first_coe y
    simpa [y, complexPuncturedPlaneDirection] using hfirst
  simpa [deRhamMayerVietorisSmoothDifference,
    annularLeftPoleLogZeroForm, annularRightPoleLogZeroForm,
    annularAngleTransitionClosedForm,
    restrictSmoothFormsOfLE, restrictSmoothFormOfLE,
    smoothRealFunctionToZeroForm,
    smoothRealFunctionOfIsLocallyConstant, y] using htransition

/--
%%handwave
name:
  Green conjugate on the inner pole disk in negative annular coordinates
statement:
  On the part of the punctured pole disk inside the chosen closed coordinate
  disk, the punctured Green-conjugate one-form is the pullback, through the
  side-preserving radial coordinate, of its annular representative restricted
  to the negative half-cylinder.
proof:
  Both sides are successive restrictions and pullbacks of the same punctured
  conjugate form.  Expand the inclusion and radial coordinate maps; the
  side-preserving restriction identifies their point maps, and the chain rule
  identifies the induced tangent pullbacks.
-/
theorem puncturedConjugate_restrict_innerPoleDisk_eq_pullback_negativeAnnular
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G) :
    let W := D.puncturedPoleDisk
    let Q := W ⊓
      ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
        D.closedDisk.toSmoothBoundaryDomain.isOpen⟩
    let phi := D.radialDiffeomorph
    let hside : ∀ y : W,
        ((y : X) ∈ D.closedDisk.toSmoothBoundaryDomain.carrier ↔
          (phi y).2 < 0) := fun y =>
      (D.closedDisk.radialPuncturedCollarDiffeomorph_second_lt_zero_iff
        p D.pole_mem_closedDisk_chart_source
        D.closedDisk_chart_p_eq_center
        D.closedDisk_double_closedRadius.le y).symm
    let psi := sidePreservingAnnularCollarDomainRestriction
      D.closedDisk.toSmoothBoundaryDomain W phi hside
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := Q) (V := puncturedSurfaceOpen p)
        (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen) 1
        C.conjugate.omega =
      smoothFormsPullbackDiffeomorph SurfaceRealModel AnnularCylinderModel
        psi 1
        (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
          negativeAnnularCylinderOpen 1
          (D.greenConjugateAnnularClosedForm C).1) := by
  dsimp only
  let U := puncturedSurfaceOpen p
  let W := D.puncturedPoleDisk
  let WU := openWithinOpen U W
  let Q := W ⊓
    ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
      D.closedDisk.toSmoothBoundaryDomain.isOpen⟩
  let phi := D.annularToPuncturedPoleWithinDiffeomorph
  let hside : ∀ y : W,
      ((y : X) ∈ D.closedDisk.toSmoothBoundaryDomain.carrier ↔
        (D.radialDiffeomorph y).2 < 0) := fun y =>
    (D.closedDisk.radialPuncturedCollarDiffeomorph_second_lt_zero_iff
      p D.pole_mem_closedDisk_chart_source
      D.closedDisk_chart_p_eq_center
      D.closedDisk_double_closedRadius.le y).symm
  let psi := sidePreservingAnnularCollarDomainRestriction
    D.closedDisk.toSmoothBoundaryDomain W D.radialDiffeomorph hside
  let incNeg : negativeAnnularCylinderOpen → Circle × ℝ :=
    fun z => (z : Circle × ℝ)
  let incW : WU → U := fun y => (y : U)
  let incQ : Q → U := fun y =>
    ⟨(y : X), D.puncturedPoleDisk_le_puncturedSurfaceOpen y.2.1⟩
  let f : Q → U := incQ
  let g : Q → U := fun y => incW (phi (incNeg (psi y)))
  have hfg : f = g := by
    funext y
    apply Subtype.ext
    change (y : X) = ((phi (incNeg (psi y)) : WU) : X)
    let yW : W := ⟨(y : X), y.2.1⟩
    have hpsi : incNeg (psi y) = D.radialDiffeomorph yW := by
      rfl
    rw [hpsi]
    change (y : X) =
      (((openWithinOpenDiffeomorph U W
        D.puncturedPoleDisk_le_puncturedSurfaceOpen).symm
          (D.radialDiffeomorph.symm (D.radialDiffeomorph yW)) : WU) : X)
    rw [D.radialDiffeomorph.symm_apply_apply]
    rfl
  apply DifferentialForm.ext
  intro x
  ext q
  have hphiNeg :
      mfderiv SurfaceRealModel SurfaceRealModel
          (fun y : Q => phi (incNeg (psi y))) x =
        (mfderiv AnnularCylinderModel SurfaceRealModel phi
          (incNeg (psi x))).comp
          ((mfderiv AnnularCylinderModel AnnularCylinderModel incNeg
            (psi x)).comp
            (mfderiv SurfaceRealModel AnnularCylinderModel psi x)) := by
    have hneg :
        mfderiv SurfaceRealModel AnnularCylinderModel
            (fun y : Q => incNeg (psi y)) x =
          (mfderiv AnnularCylinderModel AnnularCylinderModel incNeg
            (psi x)).comp
            (mfderiv SurfaceRealModel AnnularCylinderModel psi x) := by
      exact mfderiv_comp x
        ((contMDiff_subtype_val (I := AnnularCylinderModel)
          (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
        (psi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    calc
      mfderiv SurfaceRealModel SurfaceRealModel
          (fun y : Q => phi (incNeg (psi y))) x =
        (mfderiv AnnularCylinderModel SurfaceRealModel phi
          (incNeg (psi x))).comp
          (mfderiv SurfaceRealModel AnnularCylinderModel
            (fun y : Q => incNeg (psi y)) x) := by
        simpa only [Function.comp_apply] using mfderiv_comp x
          (phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (((contMDiff_subtype_val (I := AnnularCylinderModel)
            (n := ∞)).comp psi.contMDiff).contMDiffAt.mdifferentiableAt
              (by simp))
      _ = _ := by rw [hneg]
  have hgDeriv :
      mfderiv SurfaceRealModel SurfaceRealModel g x =
        (mfderiv SurfaceRealModel SurfaceRealModel incW
          (phi (incNeg (psi x)))).comp
          ((mfderiv AnnularCylinderModel SurfaceRealModel phi
            (incNeg (psi x))).comp
            ((mfderiv AnnularCylinderModel AnnularCylinderModel incNeg
              (psi x)).comp
              (mfderiv SurfaceRealModel AnnularCylinderModel psi x))) := by
    calc
      mfderiv SurfaceRealModel SurfaceRealModel g x =
        (mfderiv SurfaceRealModel SurfaceRealModel incW
          (phi (incNeg (psi x)))).comp
          (mfderiv SurfaceRealModel SurfaceRealModel
            (fun y : Q => phi (incNeg (psi y))) x) := by
        simpa only [g, Function.comp_apply] using mfderiv_comp x
          ((contMDiff_subtype_val (I := SurfaceRealModel)
            (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
          ((phi.contMDiff.comp
            ((contMDiff_subtype_val (I := AnnularCylinderModel)
              (n := ∞)).comp psi.contMDiff)).contMDiffAt.mdifferentiableAt
                (by simp))
      _ = _ := by rw [hphiNeg]
  have hDeriv :
      mfderiv SurfaceRealModel SurfaceRealModel incQ x =
        (mfderiv SurfaceRealModel SurfaceRealModel incW
          (phi (incNeg (psi x)))).comp
          ((mfderiv AnnularCylinderModel SurfaceRealModel phi
            (incNeg (psi x))).comp
            ((mfderiv AnnularCylinderModel AnnularCylinderModel incNeg
              (psi x)).comp
              (mfderiv SurfaceRealModel AnnularCylinderModel psi x))) := by
    change mfderiv SurfaceRealModel SurfaceRealModel f x = _
    rw [hfg, hgDeriv]
  simp only [greenConjugateAnnularClosedForm,
    restrictSmoothFormsOfLE,
    restrictSmoothFormsToOpen,
    smoothFormsPullbackDiffeomorph]
  change C.conjugate.omega.toFun (incQ x)
      ((mfderiv SurfaceRealModel SurfaceRealModel incQ x) ∘ q) =
    C.conjugate.omega.toFun (incW (phi (incNeg (psi x))))
      (((mfderiv SurfaceRealModel SurfaceRealModel incW
        (phi (incNeg (psi x)))).comp
        ((mfderiv AnnularCylinderModel SurfaceRealModel phi
          (incNeg (psi x))).comp
          ((mfderiv AnnularCylinderModel AnnularCylinderModel incNeg
            (psi x)).comp
            (mfderiv SurfaceRealModel AnnularCylinderModel psi x)))) ∘ q)
  have hpoint : incQ x = incW (phi (incNeg (psi x))) := congrFun hfg x
  rw [hpoint, hDeriv]

/-- The Green conjugate itself is the Mayer--Vietoris connecting form of its
two logarithmic branches. -/
noncomputable def greenConjugateAnnularConnectingData
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    DeRhamMayerVietorisConnectingData (I := AnnularCylinderModel) (A := ℝ)
      (annularPunctureOpen v)
      (annularPunctureOpen (annularOpposite v))
      (annularPunctures_cover v) 0 (annularAngleTransitionClosedForm v) where
  lift := (D.annularLeftPoleLogZeroForm v,
    D.annularRightPoleLogZeroForm v)
  lift_difference := D.annularPoleLogZeroForms_difference_eq_transition v
  glued := D.greenConjugateAnnularClosedForm C
  glued_restriction := by
    apply Prod.ext
    · simpa [deRhamMayerVietorisSmoothRestriction] using
        D.greenConjugateAnnularClosedForm_restrict_left C v
    · simpa [deRhamMayerVietorisSmoothRestriction] using
        D.greenConjugateAnnularClosedForm_restrict_right C v

/--
%%handwave
name:
  Cohomology class of the Green conjugate in a radial pole coordinate
statement:
  On the annular cylinder around the pole, the de Rham class of the Green
  conjugate one-form is
  \([\omega_G]=c_v[\omega_{\mathrm{ang}}]\), where \(c_v\) is the coefficient
  of the transition between the two logarithmic branches determined by the cut
  direction \(v\).
proof:
  The local logarithmic imaginary parts are primitives whose difference is the
  annular angle transition.  Mayer--Vietoris identifies the glued Green
  conjugate with its connecting class, and the annular calculation makes this
  \(c_v\) times the angular class.
-/
theorem greenConjugateAnnularClosedForm_class (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    (DeRhamExactClosedForms (I := AnnularCylinderModel)
      (M := Circle × ℝ) (A := ℝ) 1).mkQ
        (D.greenConjugateAnnularClosedForm C) =
      annularAngleTransitionCoefficient v •
        (DeRhamExactClosedForms (I := AnnularCylinderModel)
          (M := Circle × ℝ) (A := ℝ) 1).mkQ
            (annularAngularClosedForm v) := by
  let connecting :=
    deRhamMayerVietorisConnectingOfPartitionOfUnity (A := ℝ)
      AnnularCylinderModel (annularPunctureOpen v)
      (annularPunctureOpen (annularOpposite v))
      (annularPunctures_cover v) 0
  calc
    (DeRhamExactClosedForms (I := AnnularCylinderModel)
        (M := Circle × ℝ) (A := ℝ) 1).mkQ
          (D.greenConjugateAnnularClosedForm C) =
        connecting (annularAngleTransitionClass v) := by
      symm
      exact deRhamMayerVietorisConnectingOfPartitionOfUnity_eq_mk_glued
        (A := ℝ) AnnularCylinderModel
        (annularPunctureOpen v)
        (annularPunctureOpen (annularOpposite v))
        (annularPunctures_cover v) 0
        (annularAngleTransitionClosedForm v)
        (D.greenConjugateAnnularConnectingData C v)
    _ = annularAngleTransitionCoefficient v •
        (DeRhamExactClosedForms (I := AnnularCylinderModel)
          (M := Circle × ℝ) (A := ℝ) 1).mkQ
            (annularAngularClosedForm v) := by
      exact annularAngleTransition_connecting_eq_angular_class v

/--
%%handwave
name:
  Global Green-conjugate class with a normalized local angular representative
statement:
  Suppose the ambient surface is noncompact and has vanishing first de Rham
  cohomology.  Then there is a closed one-form \(\eta\) on the punctured
  surface such that \([\omega_G]=c_v[\eta]\), whose restriction near the pole
  is the standard cutoff angular form and which has period \(-1\) on a smooth
  local cycle.
proof:
  Construct the punctured angular class from the exhaustion and coordinate
  disk.  The local Green-conjugate class formula gives equality after
  restriction; injectivity of punctured-disk restriction promotes it to the
  global class.  Pull back the standard negative annular cycle for the period.
-/
theorem exists_puncturedAngularForm_greenConjugate_class_with_local
    [IsManifold SurfaceRealModel ∞ X] [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1,
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ
          C.toClosedForm =
        annularAngleTransitionCoefficient v •
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ eta ∧
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := D.puncturedPoleDisk ⊓
            ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
              D.closedDisk.toSmoothBoundaryDomain.isOpen⟩)
          (V := puncturedSurfaceOpen p)
          (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen)
          1 eta.1 =
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := D.puncturedPoleDisk ⊓
            ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
              D.closedDisk.toSmoothBoundaryDomain.isOpen⟩)
          (V := D.puncturedPoleDisk) inf_le_left 1
          (exteriorCutoffAngularCollarOneForm D.puncturedPoleDisk
            D.radialDiffeomorph v) ∧
      ∃ c : SingularChain (I := SurfaceRealModel)
          (M := (D.puncturedPoleDisk ⊓
            ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
              D.closedDisk.toSmoothBoundaryDomain.isOpen⟩ :
                TopologicalSpace.Opens X)) 1 ∞,
        boundary (I := SurfaceRealModel) c = 0 ∧
          integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ)
              (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen)
              1 eta).1 c = -1 := by
  let U := puncturedSurfaceOpen p
  let D₀ := D.closedDisk
  let W := D.puncturedPoleDisk
  let Q := W ⊓
    ⟨D₀.toSmoothBoundaryDomain.carrier,
      D₀.toSmoothBoundaryDomain.isOpen⟩
  let phi := D.radialDiffeomorph
  have hside : ∀ y : W,
      ((y : X) ∈ D₀.toSmoothBoundaryDomain.carrier ↔
        (phi y).2 < 0) := by
    intro y
    exact (D₀.radialPuncturedCollarDiffeomorph_second_lt_zero_iff
      p D.pole_mem_closedDisk_chart_source
      D.closedDisk_chart_p_eq_center
      D.closedDisk_double_closedRadius.le y).symm
  let psi := sidePreservingAnnularCollarDomainRestriction
    D₀.toSmoothBoundaryDomain W phi hside
  rcases D₀.exists_closed_puncturedAngularForm E p
      D.pole_mem_closedDisk_chart_source D.closedDisk_chart_p_eq_center
      D.closedDisk_double_closedRadius.le v with ⟨eta, heta⟩
  let omegaNeg : DeRhamClosedForms (I := AnnularCylinderModel)
      (M := negativeAnnularCylinderOpen) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionToOpen (I := AnnularCylinderModel)
      (A := ℝ) negativeAnnularCylinderOpen 1
      (D.greenConjugateAnnularClosedForm C)
  let betaNeg : DeRhamClosedForms (I := AnnularCylinderModel)
      (M := negativeAnnularCylinderOpen) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionToOpen (I := AnnularCylinderModel)
      (A := ℝ) negativeAnnularCylinderOpen 1
      (annularAngularClosedForm v)
  let omegaQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsPullbackDiffeomorph SurfaceRealModel
      AnnularCylinderModel psi 1 omegaNeg
  let betaQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsPullbackDiffeomorph SurfaceRealModel
      AnnularCylinderModel psi 1 betaNeg
  let omegaU := C.toClosedForm
  let omegaUQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
      (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen) 1 omegaU
  let etaQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
      (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen) 1 eta
  have homegaUQ : omegaUQ = omegaQ := by
    apply Subtype.ext
    change
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Q) (V := U)
          (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen) 1
          C.conjugate.omega =
        smoothFormsPullbackDiffeomorph SurfaceRealModel AnnularCylinderModel
          psi 1
          (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
            negativeAnnularCylinderOpen 1
            (D.greenConjugateAnnularClosedForm C).1)
    simpa [U, D₀, W, Q, phi, psi] using
      D.puncturedConjugate_restrict_innerPoleDisk_eq_pullback_negativeAnnular C
  have hetaQ : etaQ = betaQ := by
    apply Subtype.ext
    calc
      etaQ.1 = restrictSmoothFormsOfLE (I := SurfaceRealModel)
          (M := X) (A := ℝ) (W := Q) (V := U)
          (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen)
          1 eta.1 := rfl
      _ = restrictSmoothFormsOfLE (I := SurfaceRealModel)
          (M := X) (A := ℝ) (W := Q) (V := W) inf_le_left 1
            (exteriorCutoffAngularCollarOneForm W phi v) := by
              simpa [U, D₀, W, Q, phi] using heta
      _ = betaQ.1 := by
        exact restrict_exteriorCutoffAngularCollarOneForm_domain_eq_pullback_negative
          D₀.toSmoothBoundaryDomain W phi hside v
  have hclassNeg :
      (DeRhamExactClosedForms (I := AnnularCylinderModel)
          (M := negativeAnnularCylinderOpen) (A := ℝ) 1).mkQ omegaNeg =
        annularAngleTransitionCoefficient v •
          (DeRhamExactClosedForms (I := AnnularCylinderModel)
            (M := negativeAnnularCylinderOpen) (A := ℝ) 1).mkQ betaNeg := by
    let resNeg :
        DeRhamCohomology (I := AnnularCylinderModel)
            (M := Circle × ℝ) (A := ℝ) 1 →ₗ[ℝ]
          DeRhamCohomology (I := AnnularCylinderModel)
            (M := negativeAnnularCylinderOpen) (A := ℝ) 1 :=
      deRhamCohomologyRestrictionToOpen (I := AnnularCylinderModel)
        (M := Circle × ℝ) (A := ℝ) negativeAnnularCylinderOpen 1
    have h := congrArg
      (fun a : DeRhamCohomology (I := AnnularCylinderModel)
          (M := Circle × ℝ) (A := ℝ) 1 => resNeg a)
      (D.greenConjugateAnnularClosedForm_class C v)
    simpa [resNeg, omegaNeg, betaNeg, deRhamCohomologyRestrictionToOpen,
      deRhamClosedFormsRestrictionToOpen,
      Submodule.mapQ_apply] using h
  have hclassQ :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ omegaQ =
        annularAngleTransitionCoefficient v •
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := Q) (A := ℝ) 1).mkQ betaQ := by
    have h := congrArg
      (deRhamCohomologyPullbackDiffeomorph SurfaceRealModel
        AnnularCylinderModel psi 1) hclassNeg
    simpa [omegaQ, betaQ, deRhamCohomologyPullbackDiffeomorph,
      Submodule.mapQ_apply] using h
  have hlocal :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ omegaUQ =
        annularAngleTransitionCoefficient v •
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := Q) (A := ℝ) 1).mkQ etaQ := by
    rw [homegaUQ, hetaQ]
    exact hclassQ
  have hinj :=
    (puncturedSurfaceOpen_coordinateDisk_restriction_bijective
      E D₀ p D.pole_mem_closedDisk_chart_source
        D.closedDisk_chart_p_eq_center
        D.closedDisk_double_closedRadius.le v).1
  refine ⟨eta, ?_, ?_, ?_⟩
  · apply hinj
    simpa [U, D₀, W, Q, omegaUQ, omegaU, etaQ,
      deRhamCohomologyRestrictionOfLE, Submodule.mapQ_apply] using hlocal
  · simpa [U, D₀, W, Q, phi] using heta
  · rcases
        exists_sidePreservingAnnularCollarDomainCycle_angular_period_eq_neg_one
          D₀.toSmoothBoundaryDomain W phi hside v with
      ⟨c, hcycle, hperiod⟩
    refine ⟨c, hcycle, ?_⟩
    rw [show (deRhamClosedFormsRestrictionOfLE
        (I := SurfaceRealModel) (A := ℝ)
        (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen)
        1 eta).1 = etaQ.1 by rfl, hetaQ]
    simpa [D₀, W, Q, phi, psi, betaQ, betaNeg] using hperiod

/--
%%handwave
name:
  Global Green-conjugate class and normalized angular cycle
statement:
  Under vanishing ambient first de Rham cohomology, there is a closed one-form
  \(\eta\) on the punctured surface satisfying \([\omega_G]=c_v[\eta]\),
  together with a local smooth cycle \(c\) around the pole such that
  \(\partial c=0\) and \(\int_c\eta=-1\).
proof:
  Apply the stronger construction which also specifies the local restriction
  of \(\eta\), and retain the global class identity and normalized cycle.
-/
theorem exists_puncturedAngularForm_greenConjugate_class
    [IsManifold SurfaceRealModel ∞ X] [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1,
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ
          C.toClosedForm =
        annularAngleTransitionCoefficient v •
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ eta ∧
      ∃ c : SingularChain (I := SurfaceRealModel)
          (M := (D.puncturedPoleDisk ⊓
            ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
              D.closedDisk.toSmoothBoundaryDomain.isOpen⟩ :
                TopologicalSpace.Opens X)) 1 ∞,
        boundary (I := SurfaceRealModel) c = 0 ∧
          integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ)
              (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen)
              1 eta).1 c = -1 := by
  rcases D.exists_puncturedAngularForm_greenConjugate_class_with_local
      E C v with ⟨eta, hclass, _hlocal, hcycle⟩
  exact ⟨eta, hclass, hcycle⟩

/--
%%handwave
name:
  Exact decomposition of the punctured Green conjugate
statement:
  Under vanishing ambient first de Rham cohomology, there are a closed
  punctured angular one-form \(\eta\) and a smooth function \(\theta\) such
  that \(\omega_G=c_v\eta+d\theta\).
proof:
  The global class identity says \([\omega_G-c_v\eta]=0\).  By the definition
  of de Rham cohomology, the difference is exact and therefore equals
  \(d\theta\).
-/
theorem exists_puncturedAngularForm_greenConjugate_exact_decomposition
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
              (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta := by
  rcases D.exists_puncturedAngularForm_greenConjugate_class E C v with
    ⟨eta, hclass, _hnormalized⟩
  have hexact :
      (C.toClosedForm - annularAngleTransitionCoefficient v • eta :
          DeRhamClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1) ∈
        DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) (A := ℝ) 1 := by
    have hclass' :
        (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ
            C.toClosedForm =
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ
            (annularAngleTransitionCoefficient v • eta) := by
      simpa using hclass
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq] at hclass'
    exact hclass'
  change
    (C.conjugate.omega - annularAngleTransitionCoefficient v • eta.1) ∈
      DeRhamExactForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1 at hexact
  rw [DeRhamExactForms] at hexact
  rcases hexact with ⟨theta, htheta⟩
  refine ⟨eta, theta, ?_⟩
  rw [htheta]
  module

/--
%%handwave
name:
  Normalized exact decomposition of the punctured Green conjugate
statement:
  The decomposition \(\omega_G=c_v\eta+d\theta\) may be chosen together with
  a smooth local cycle \(c\) around the pole satisfying
  \(\partial c=0\) and \(\int_c\eta=-1\).
proof:
  Use the global class construction with its normalized local cycle.  The
  vanishing of \([\omega_G-c_v\eta]\) supplies \(\theta\); retain the cycle
  and period from the same construction.
-/
theorem exists_puncturedAngularForm_greenConjugate_exact_decomposition_normalized
    [IsManifold SurfaceRealModel ∞ X] [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    let Q := D.puncturedPoleDisk ⊓
      ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
        D.closedDisk.toSmoothBoundaryDomain.isOpen⟩
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1,
      ∃ theta : SmoothForms (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) ℝ 0,
        ∃ c : SingularChain (I := SurfaceRealModel) (M := Q) 1 ∞,
          C.conjugate.omega =
              annularAngleTransitionCoefficient v • eta.1 +
                deRhamDifferential (I := SurfaceRealModel)
                  (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta ∧
            boundary (I := SurfaceRealModel) c = 0 ∧
              integrateSmoothChain (I := SurfaceRealModel)
                (deRhamClosedFormsRestrictionOfLE
                  (I := SurfaceRealModel) (A := ℝ)
                  (inf_le_left.trans
                    D.puncturedPoleDisk_le_puncturedSurfaceOpen) 1 eta).1 c =
                -1 := by
  dsimp only
  rcases D.exists_puncturedAngularForm_greenConjugate_class E C v with
    ⟨eta, hclass, c, hcycle, hperiod⟩
  have hexact :
      (C.toClosedForm - annularAngleTransitionCoefficient v • eta :
          DeRhamClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1) ∈
        DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) (A := ℝ) 1 := by
    have hclass' :
        (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ
            C.toClosedForm =
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 1).mkQ
            (annularAngleTransitionCoefficient v • eta) := by
      simpa using hclass
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq] at hclass'
    exact hclass'
  change
    (C.conjugate.omega - annularAngleTransitionCoefficient v • eta.1) ∈
      DeRhamExactForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1 at hexact
  rw [DeRhamExactForms] at hexact
  rcases hexact with ⟨theta, htheta⟩
  refine ⟨eta, theta, c, ?_, hcycle, hperiod⟩
  rw [htheta]
  module

/--
%%handwave
name:
  The Green-conjugate residue is plus or minus two pi
statement:
  In a radial pole coordinate, the Green-conjugate class is either
  \(2\pi[\omega_{\mathrm{ang}}]\) or
  \(-2\pi[\omega_{\mathrm{ang}}]\).
proof:
  The local class is the angular class multiplied by the logarithmic
  transition coefficient, and that coefficient is \(2\pi\) or \(-2\pi\),
  according to orientation.
-/
theorem greenConjugateAnnularClosedForm_class_eq_two_pi_or_neg (D :
    CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    let angular :=
      (DeRhamExactClosedForms (I := AnnularCylinderModel)
        (M := Circle × ℝ) (A := ℝ) 1).mkQ
          (annularAngularClosedForm v)
    (DeRhamExactClosedForms (I := AnnularCylinderModel)
        (M := Circle × ℝ) (A := ℝ) 1).mkQ
          (D.greenConjugateAnnularClosedForm C) =
        (2 * Real.pi) • angular ∨
      (DeRhamExactClosedForms (I := AnnularCylinderModel)
        (M := Circle × ℝ) (A := ℝ) 1).mkQ
          (D.greenConjugateAnnularClosedForm C) =
        -(2 * Real.pi) • angular := by
  dsimp only
  rcases annularAngleTransitionCoefficient_eq_two_pi_or_neg v with h | h
  · left
    rw [D.greenConjugateAnnularClosedForm_class C v, h]
  · right
    rw [D.greenConjugateAnnularClosedForm_class C v, h]

end CompactSuperlevelGreenFunctionPoleCoordinateLogData

end
end Uniformization
end JJMath
