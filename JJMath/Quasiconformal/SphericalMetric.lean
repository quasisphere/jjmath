import JJMath.Quasiconformal.RiemannSphere
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# A compatible metric on the Riemann sphere

The one-point compactification model of the Riemann sphere initially carries
only its topology.  This file chooses a compatible metric by transporting the
Euclidean metric from the unit sphere in three-dimensional Euclidean space.
The choice is auxiliary: compact Hausdorff spaces have at most one compatible
uniformity, so subsequent equicontinuity statements do not depend on these
coordinates.
-/

namespace JJMath

open scoped Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  A unit-sphere model of the Riemann sphere
statement:
  The one-point compactification $\widehat{\mathbb C}$ is homeomorphic to the
  unit sphere
  $$
    S^2=\{x\in\mathbb R^3:\lVert x\rVert=1\}.
  $$
-/
def riemannSphereEquivUnitSphere :
    RiemannSphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by norm_num)

/--
%%handwave
name:
  A compatible metric on the Riemann sphere
statement:
  The metric on $\widehat{\mathbb C}$ is the pullback of Euclidean distance
  on $S^2$ through the chosen homeomorphism
  $\widehat{\mathbb C}\simeq S^2$.  Its induced topology is the original
  one-point-compactification topology.
-/
@[reducible]
noncomputable def riemannSphereMetricSpace : MetricSpace RiemannSphere :=
  riemannSphereEquivUnitSphere.isEmbedding.comapMetricSpace
    riemannSphereEquivUnitSphere

attribute [instance] riemannSphereMetricSpace

/--
%%handwave
name:
  Continuity of the inverse reciprocal chart
statement:
  The map $\phi_\infty^{-1}:\mathbb C\to\widehat{\mathbb C}$ from
  reciprocal coordinates back to the Riemann sphere is continuous.
proof:
  It is the composition of the open finite-point inclusion with spherical
  inversion, both of which are continuous.
-/
theorem continuous_riemannSphereInfinityChart_symm :
    Continuous
      (riemannSphereInfinityChart.symm : ℂ → RiemannSphere) := by
  change Continuous
    (fun z : ℂ ↦ riemannSphereInvHomeomorph (z : RiemannSphere))
  exact riemannSphereInvHomeomorph.continuous.comp OnePoint.continuous_coe

/--
%%handwave
name:
  Reciprocal disks are neighborhoods of infinity
statement:
  If $r>0$, then
  $$
    \phi_\infty^{-1}(B(0,r))
  $$
  is a neighborhood of $\infty$ in $\widehat{\mathbb C}$.
proof:
  The finite-point inclusion is open, spherical inversion is a homeomorphism,
  and reciprocal coordinate $0$ represents $\infty$.
-/
theorem riemannSphereInfinityChart_symm_image_ball_mem_nhds_infty
    {r : ℝ} (hr : 0 < r) :
    riemannSphereInfinityChart.symm '' Metric.ball (0 : ℂ) r ∈
      𝓝 (OnePoint.infty : RiemannSphere) := by
  have hcoe : IsOpen
      (((↑) : ℂ → RiemannSphere) '' Metric.ball (0 : ℂ) r) :=
    OnePoint.isOpenMap_coe _ Metric.isOpen_ball
  have hopen : IsOpen
      (riemannSphereInfinityChart.symm '' Metric.ball (0 : ℂ) r) := by
    have hinv := riemannSphereInvHomeomorph.isOpenMap _ hcoe
    simpa [Set.image_image] using hinv
  apply hopen.mem_nhds
  refine ⟨0, ?_, ?_⟩
  · simpa [Metric.mem_ball]
  · simp

end

end Quasiconformal

end JJMath
