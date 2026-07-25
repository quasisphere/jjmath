import JJMath.Hyperbolic.Converse.Continuation
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Projective atlas assembly targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/-- The finite affine inclusion `ℂ ↪ ℂP¹` as an open partial homeomorphism.

%%handwave
name: The finite affine inclusion ℂ ↪ ℂP¹ as an open partial homeomorphism
statement:
  The inclusion $\mathbb C\hookrightarrow\mathbb{CP}^1$ identifies the
  complex plane homeomorphically with the open finite locus
  $\mathbb{CP}^1\setminus\{\infty\}$.
-/
def finiteRiemannSphereOpenPartialHomeomorph :
    OpenPartialHomeomorph ℂ RiemannSphere :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph
    ((↑) : ℂ → RiemannSphere) OnePoint.isOpenEmbedding_coe

/--
%%handwave
name: Source of the finite affine chart of the Riemann sphere
statement:
  The standard inclusion of \(\mathbb C\) as the finite part of the Riemann sphere is defined on all of \(\mathbb C\).
proof:
  This is immediate from the definition of the finite affine chart.
-/
@[simp]
theorem finiteRiemannSphereOpenPartialHomeomorph_source :
    finiteRiemannSphereOpenPartialHomeomorph.source = Set.univ := by
  simp [finiteRiemannSphereOpenPartialHomeomorph]

namespace ProjectiveBranchConstruction

variable {x₀ : X} {g : HyperbolicMetric X}
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g)

/-- The selected finite local biholomorphic branch of the developing map at a lift.

%%handwave
name: The selected finite local biholomorphic branch of the developing map at a lift
statement:
  At a lift $y\in\widetilde X$, choose a finite local biholomorphic branch
  $f_y$ of the projectivized developing map in the complex coordinate
  centered at $y$.
-/
def finiteBranchAt (y : D.hyperbolicDevelopingMap.cover.total) :
    OpenPartialHomeomorph ℂ ℂ :=
  Classical.choose (D.projective_regular.finite_local_biholomorphism_data y)

/--
%%handwave
name: The selected finite developing branch contains its base coordinate
statement:
  For a lift \(y\) in the simply connected cover, the coordinate \(\varphi_y(y)\) lies in the domain of the selected finite local branch of the projectivized developing map.
proof:
  This is the base-point membership supplied by the selected finite local-biholomorphism data at \(y\).
-/
theorem mem_finiteBranchAt_source
    (y : D.hyperbolicDevelopingMap.cover.total) :
    (chartAt ℂ y y) ∈ (finiteBranchAt D y).source :=
  (Classical.choose_spec
    (D.projective_regular.finite_local_biholomorphism_data y)).1

/--
%%handwave
name: Local finite branch of a projectivized developing map
statement:
  On its selected domain near a lift \(y\), the finite branch equals the coordinate expression of the developing map, is holomorphic, and has nonzero derivative.
proof:
  These are exactly the equality, holomorphicity, and regularity properties of the selected finite local-biholomorphism data at \(y\).
-/
theorem finiteBranchAt_eq_coordinateExpression
    (y : D.hyperbolicDevelopingMap.cover.total) {z : ℂ}
    (hz : z ∈ (finiteBranchAt D y).source) :
    finiteBranchAt D y z =
        HyperbolicDevelopingMapCoordinateExpression
          D.hyperbolicDevelopingMap.cover D.hyperbolicDevelopingMap.dev y z ∧
      DifferentiableAt ℂ (finiteBranchAt D y) z ∧
        deriv (finiteBranchAt D y) z ≠ 0 :=
  (Classical.choose_spec
    (D.projective_regular.finite_local_biholomorphism_data y)).2.2 z hz

/--
The base coordinate source where a cover-local section and the selected
developing finite branch are simultaneously valid.

%%handwave
name: The base coordinate source where a cover-local section and the selected developing finite branch are simultaneously valid
statement:
  For the local section at $y$, define
  $\Omega_y$ as the intersection of its coordinate source with the inverse
  image of the domain of the selected finite branch $f_y$.
-/
def fixedCoordinateSource (y : D.hyperbolicDevelopingMap.cover.total) :
    Set ℂ :=
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  S.coordinateSource ∩ S.sectionCoordinate ⁻¹' (finiteBranchAt D y).source

/--
%%handwave
name: Openness of the fixed coordinate source
statement:
  The set of base-chart coordinates on which the local cover section lands in the selected finite developing branch is open.
proof:
  It is the intersection of the open coordinate source with the inverse image of the open finite-branch domain under the continuous section-coordinate map.
-/
theorem fixedCoordinateSource_open
    (y : D.hyperbolicDevelopingMap.cover.total) :
    IsOpen (fixedCoordinateSource D y) := by
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  change IsOpen (S.coordinateSource ∩ S.sectionCoordinate ⁻¹' (finiteBranchAt D y).source)
  exact S.sectionCoordinate_continuousOn.isOpen_inter_preimage
    S.coordinateSource_open (finiteBranchAt D y).open_source

/--
%%handwave
name: The projected lift belongs to its fixed coordinate source
statement:
  For a cover point \(y\), the base coordinate of its projection lies in the fixed coordinate source attached to \(y\).
proof:
  The base coordinate belongs to the section-coordinate domain, the section sends it back to the chart coordinate of \(y\), and that coordinate lies in the selected finite branch.
-/
theorem projection_mem_fixedCoordinateSource
    (y : D.hyperbolicDevelopingMap.cover.total) :
    let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
    S.baseComplexChart (D.hyperbolicDevelopingMap.cover.projection y) ∈
      fixedCoordinateSource D y := by
  intro S
  change
    S.baseComplexChart (D.hyperbolicDevelopingMap.cover.projection y) ∈
      S.coordinateSource ∩ S.sectionCoordinate ⁻¹' (finiteBranchAt D y).source
  constructor
  · exact S.basepoint_coordinate_mem
  · change
      S.sectionCoordinate
          (S.baseComplexChart (D.hyperbolicDevelopingMap.cover.projection y)) ∈
        (finiteBranchAt D y).source
    rw [S.sectionCoordinate_basepoint_eq_chartAt]
    exact mem_finiteBranchAt_source D y

/--
The base-space source where the eventual projective branch chart is expressed
in the fixed base coordinate source.

%%handwave
name: The base-space source where the eventual projective branch chart is expressed in the fixed base coordinate source
statement:
  Define $U_y$ as the points in the source of the selected base chart whose
  base coordinates lie in $\Omega_y$.
-/
def baseChartDomain (y : D.hyperbolicDevelopingMap.cover.total) :
    Set X :=
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  S.baseComplexChart.source ∩ S.baseComplexChart ⁻¹' fixedCoordinateSource D y

/--
%%handwave
name: Openness of the base domain of a projective branch chart
statement:
  The base-space points whose base-chart coordinates lie in the fixed coordinate source form an open set.
proof:
  Intersect the open source of the base chart with the inverse image of the open fixed coordinate source under the continuous chart map.
-/
theorem baseChartDomain_open
    (y : D.hyperbolicDevelopingMap.cover.total) :
    IsOpen (baseChartDomain D y) := by
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  change IsOpen (S.baseComplexChart.source ∩
    S.baseComplexChart ⁻¹' fixedCoordinateSource D y)
  exact S.baseComplexChart.continuousOn.isOpen_inter_preimage
    S.baseComplexChart.open_source (fixedCoordinateSource_open D y)

/--
%%handwave
name: The projected lift belongs to the base branch domain
statement:
  The projection of a selected cover point \(y\) lies in the base domain of the projective branch chart constructed from \(y\).
proof:
  The projection lies in the selected base chart, and its base coordinate belongs to the fixed coordinate source.
-/
theorem projection_mem_baseChartDomain
    (y : D.hyperbolicDevelopingMap.cover.total) :
    D.hyperbolicDevelopingMap.cover.projection y ∈ baseChartDomain D y := by
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  change D.hyperbolicDevelopingMap.cover.projection y ∈
    S.baseComplexChart.source ∩ S.baseComplexChart ⁻¹' fixedCoordinateSource D y
  exact ⟨S.basepoint_mem_baseChart_source, projection_mem_fixedCoordinateSource D y⟩

/-- The unshrunk projective branch chart associated to a lift.

%%handwave
name: The unshrunk projective branch chart associated to a lift
statement:
  The raw projective branch at $y$ is the composition of the inverse local
  projection, the ambient complex chart at $y$, the finite developing branch
  $f_y$, and the affine inclusion $\mathbb C\hookrightarrow\mathbb{CP}^1$.
-/
def rawProjectiveBranchChart
    (y : D.hyperbolicDevelopingMap.cover.total) :
    ProjectiveChart X :=
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  (((S.localProjection.symm.trans (chartAt ℂ y)).trans (finiteBranchAt D y)).trans
    finiteRiemannSphereOpenPartialHomeomorph)

/--
%%handwave
name: The raw projective branch is defined at its projected lift
statement:
  The unshrunk projective branch chart associated with a cover point \(y\) is defined at the projection of \(y\).
proof:
  The local inverse section sends the projection back to \(y\); its cover coordinate belongs to the selected finite branch, and the finite affine chart of the sphere is defined everywhere.
-/
theorem projection_mem_rawProjectiveBranchChart_source
    (y : D.hyperbolicDevelopingMap.cover.total) :
    D.hyperbolicDevelopingMap.cover.projection y ∈
      (rawProjectiveBranchChart D y).source := by
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  simp only [rawProjectiveBranchChart, OpenPartialHomeomorph.trans_source,
    finiteRiemannSphereOpenPartialHomeomorph_source, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_univ, and_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact S.projection_lift_mem_localProjection_target
  · rw [S.localProjection_symm_projection_lift]
    exact mem_chart_source ℂ y
  · have hsym :
        (D.hyperbolicDevelopingMap.cover.localHolomorphicSection y).localProjection.symm
            (D.hyperbolicDevelopingMap.cover.projection y) = y :=
      (D.hyperbolicDevelopingMap.cover.localHolomorphicSection y).localProjection_symm_projection_lift
    simpa [OpenPartialHomeomorph.trans_apply, hsym] using
      mem_finiteBranchAt_source D y

/--
The projective branch chart restricted to the fixed base-coordinate domain
where its finite-coordinate expression is controlled.

%%handwave
name: The projective branch chart restricted to the fixed base-coordinate domain where its finite-coordinate expression is controlled
statement:
  Restrict the raw projective branch at $y$ to the open base domain $U_y$ on
  which its finite-coordinate expression is valid.
-/
def projectiveBranchChart
    (y : D.hyperbolicDevelopingMap.cover.total) :
    ProjectiveChart X :=
  (rawProjectiveBranchChart D y).restrOpen (baseChartDomain D y)
    (baseChartDomain_open D y)

/--
%%handwave
name: The restricted projective branch contains its base point
statement:
  After restricting the raw projective branch to its base-chart domain, the projection of the defining lift remains in the chart source.
proof:
  The projection belongs both to the raw branch source and to the restricting base domain.
-/
theorem projection_mem_projectiveBranchChart_source
    (y : D.hyperbolicDevelopingMap.cover.total) :
    D.hyperbolicDevelopingMap.cover.projection y ∈
      (projectiveBranchChart D y).source := by
  rw [projectiveBranchChart, OpenPartialHomeomorph.restrOpen_source]
  exact ⟨projection_mem_rawProjectiveBranchChart_source D y,
    projection_mem_baseChartDomain D y⟩

/--
%%handwave
name: A projective branch source lies in the local section image
statement:
  Every point in the source of the restricted projective branch chart lies in the target of the local projection chart used to lift it to the cover.
proof:
  Membership in the restricted source implies membership in the raw composite-chart source, whose first defining condition is precisely membership in that target.
-/
theorem projectiveBranchChart_source_subset_localProjection_target
    (y : D.hyperbolicDevelopingMap.cover.total) :
    (projectiveBranchChart D y).source ⊆
      (D.hyperbolicDevelopingMap.cover.localHolomorphicSection y).localProjection.target := by
  intro x hx
  have hxRaw : x ∈ (rawProjectiveBranchChart D y).source := by
    simpa [projectiveBranchChart, OpenPartialHomeomorph.restrOpen_source] using hx.1
  simp only [rawProjectiveBranchChart, OpenPartialHomeomorph.trans_source,
    finiteRiemannSphereOpenPartialHomeomorph_source, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_univ, and_true] at hxRaw
  exact hxRaw.1.1

/--
%%handwave
name: A projective branch lift lies in the canonical cover chart
statement:
  If \(x\) belongs to the projective branch source associated with \(y\), then its selected local lift lies in the source of the canonical complex chart at \(y\).
proof:
  This membership is the second source condition in the raw composition defining the projective branch chart.
-/
theorem projectiveBranchChart_source_lift_mem_chartAt_source
    (y : D.hyperbolicDevelopingMap.cover.total)
    {x : X} (hx : x ∈ (projectiveBranchChart D y).source) :
    (D.hyperbolicDevelopingMap.cover.localHolomorphicSection y).localProjection.symm x ∈
      (chartAt ℂ y).source := by
  have hxRaw : x ∈ (rawProjectiveBranchChart D y).source := by
    simpa [projectiveBranchChart, OpenPartialHomeomorph.restrOpen_source] using hx.1
  simp only [rawProjectiveBranchChart, OpenPartialHomeomorph.trans_source,
    finiteRiemannSphereOpenPartialHomeomorph_source, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_univ, and_true] at hxRaw
  exact hxRaw.1.2

/--
%%handwave
name: Lifted branch coordinates lie in the selected finite developing branch
statement:
  If \(x\) lies in the projective branch source associated with \(y\), then the canonical coordinate of its local lift belongs to the domain of the selected finite developing branch at \(y\).
proof:
  This is the remaining source condition in the composite raw branch chart.
-/
theorem projectiveBranchChart_source_coordinate_mem_finiteBranch
    (y : D.hyperbolicDevelopingMap.cover.total)
    {x : X} (hx : x ∈ (projectiveBranchChart D y).source) :
    (chartAt ℂ y)
        ((D.hyperbolicDevelopingMap.cover.localHolomorphicSection y).localProjection.symm x) ∈
      (finiteBranchAt D y).source := by
  have hxRaw : x ∈ (rawProjectiveBranchChart D y).source := by
    simpa [projectiveBranchChart, OpenPartialHomeomorph.restrOpen_source] using hx.1
  simp only [rawProjectiveBranchChart, OpenPartialHomeomorph.trans_source,
    finiteRiemannSphereOpenPartialHomeomorph_source, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_univ, and_true] at hxRaw
  simpa [OpenPartialHomeomorph.trans_apply] using hxRaw.2

/--
%%handwave
name: Base coordinates of projective branch points lie in the fixed source
statement:
  Every point in a restricted projective branch source has base-chart coordinate in the corresponding fixed coordinate source.
proof:
  The restricted source includes membership in the base branch domain, whose second condition is the asserted coordinate membership.
-/
theorem projectiveBranchChart_source_baseCoordinate_mem_fixed
    (y : D.hyperbolicDevelopingMap.cover.total)
    {x : X} (hx : x ∈ (projectiveBranchChart D y).source) :
    let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
    S.baseComplexChart x ∈ fixedCoordinateSource D y := by
  intro S
  have hxDomain : x ∈ baseChartDomain D y := by
    simpa [projectiveBranchChart, OpenPartialHomeomorph.restrOpen_source] using hx.2
  simpa [baseChartDomain] using hxDomain.2

/--
%%handwave
name: A projective branch source lies in its base complex chart
statement:
  Every point in the restricted projective branch source lies in the source of the selected base complex chart.
proof:
  Membership in the restricting base domain includes membership in the base chart source.
-/
theorem projectiveBranchChart_source_mem_baseChart_source
    (y : D.hyperbolicDevelopingMap.cover.total)
    {x : X} (hx : x ∈ (projectiveBranchChart D y).source) :
    let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
    x ∈ S.baseComplexChart.source := by
  intro S
  have hxDomain : x ∈ baseChartDomain D y := by
    simpa [projectiveBranchChart, OpenPartialHomeomorph.restrOpen_source] using hx.2
  simpa [baseChartDomain] using hxDomain.1

/-- The local lift attached to the restricted projective branch chart.

%%handwave
name: The local lift attached to the restricted projective branch chart
statement:
  For $x$ in the restricted projective branch source at $y$, define its
  local lift as the inverse image of $x$ under the local projection chart
  centered at $y$.
-/
def projectiveBranchLift
    (y : D.hyperbolicDevelopingMap.cover.total) :
    (projectiveBranchChart D y).source →
      D.hyperbolicDevelopingMap.cover.total :=
  fun x ↦
    (D.hyperbolicDevelopingMap.cover.localHolomorphicSection y).localProjection.symm
      (x : X)

/--
%%handwave
name: Projection of the local projective-branch lift
statement:
  The local lift assigned to a point \(x\) of a projective branch source projects back to \(x\).
proof:
  The branch source lies in the target of the local projection chart, so its inverse is a right inverse there.
-/
theorem projectiveBranchLift_projects
    (y : D.hyperbolicDevelopingMap.cover.total)
    (x : (projectiveBranchChart D y).source) :
    D.hyperbolicDevelopingMap.cover.projection (projectiveBranchLift D y x) =
      (x : X) := by
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  change D.hyperbolicDevelopingMap.cover.projection (S.localProjection.symm (x : X)) =
    (x : X)
  exact S.projection_localProjection_symm
    (projectiveBranchChart_source_subset_localProjection_target D y x.2)

/--
%%handwave
name: Continuity of the local projective-branch lift
statement:
  The map lifting a projective branch source into the simply connected cover is continuous.
proof:
  It is the inverse of the local projection chart restricted to a subset of that chart's target; compose its continuity there with the continuous subtype inclusion.
-/
theorem projectiveBranchLift_continuous
    (y : D.hyperbolicDevelopingMap.cover.total) :
    Continuous (projectiveBranchLift D y) := by
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  change Continuous (fun x : (projectiveBranchChart D y).source ↦
    S.localProjection.symm (x : X))
  exact S.localProjection.symm.continuousOn.comp_continuous continuous_subtype_val
    (fun x ↦ projectiveBranchChart_source_subset_localProjection_target D y x.2)

/--
%%handwave
name: A projective branch is the descended projectivized developing map
statement:
  For a point \(x\) in the branch source associated with \(y\), the value of the projective branch chart at \(x\) equals the projectivized developing map evaluated at the selected local lift of \(x\).
proof:
  Write the branch chart as the selected finite branch evaluated in the canonical cover coordinate of the lift. The finite branch agrees with the developing-map coordinate expression there, which is exactly the projectivized developing value.
-/
theorem projectiveBranchChart_eq_projectiveDev
    (y : D.hyperbolicDevelopingMap.cover.total)
    (x : (projectiveBranchChart D y).source) :
    projectiveBranchChart D y (x : X) =
      D.projectiveDev (projectiveBranchLift D y x) := by
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  let u : D.hyperbolicDevelopingMap.cover.total :=
    (D.hyperbolicDevelopingMap.cover.localHolomorphicSection y).localProjection.symm
      (x : X)
  have hu : u ∈ (chartAt ℂ y).source := by
    simpa [u] using
      projectiveBranchChart_source_lift_mem_chartAt_source D y x.2
  have hz : (chartAt ℂ y) u ∈ (finiteBranchAt D y).source := by
    simpa [u] using
      projectiveBranchChart_source_coordinate_mem_finiteBranch D y x.2
  have hbranch := finiteBranchAt_eq_coordinateExpression D y hz
  have hsymm : (chartAt ℂ y).symm ((chartAt ℂ y) u) = u :=
    (chartAt ℂ y).left_inv hu
  calc
    projectiveBranchChart D y (x : X) =
        ((finiteBranchAt D y ((chartAt ℂ y) u) : ℂ) : RiemannSphere) := by
      simp [projectiveBranchChart, rawProjectiveBranchChart,
        OpenPartialHomeomorph.trans_apply,
        finiteRiemannSphereOpenPartialHomeomorph, u]
    _ =
        (((D.hyperbolicDevelopingMap.dev u : ℍ) : ℂ) : RiemannSphere) := by
      rw [hbranch.1]
      simp [HyperbolicDevelopingMapCoordinateExpression, hsymm]
    _ = D.projectiveDev u := by
      exact (D.projective_regular.finite_coordinate_eq u).symm
    _ = D.projectiveDev (projectiveBranchLift D y x) := by
      rfl

/--
%%handwave
name: Continuity of a descended projectivized developing branch
statement:
  On each projective branch source, the projectivized developing map evaluated along the selected local lift is continuous.
proof:
  This function equals the projective branch chart on its source, and an open partial homeomorphism is continuous on its source.
-/
theorem projectiveBranch_projectiveDev_continuous
    (y : D.hyperbolicDevelopingMap.cover.total) :
    Continuous
      (fun x : (projectiveBranchChart D y).source ↦
        D.projectiveDev (projectiveBranchLift D y x)) := by
  have hEq :
      (fun x : (projectiveBranchChart D y).source ↦
          D.projectiveDev (projectiveBranchLift D y x)) =
        fun x : (projectiveBranchChart D y).source ↦
          projectiveBranchChart D y (x : X) := by
    funext x
    exact (projectiveBranchChart_eq_projectiveDev D y x).symm
  rw [hEq]
  exact (projectiveBranchChart D y).continuousOn.comp_continuous
    continuous_subtype_val (fun x ↦ x.2)

/-- Finite coordinate expression of the descended projective branch.

%%handwave
name: Finite coordinate expression of the descended projective branch
statement:
  In the fixed base coordinate, define the finite branch by
  $z\mapsto f_y(s_y(z))$, where $s_y$ is the coordinate expression of the
  local cover section.
-/
def branchFiniteCoordinate
    (y : D.hyperbolicDevelopingMap.cover.total) : ℂ → ℂ :=
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  fun z ↦ finiteBranchAt D y (S.sectionCoordinate z)

/--
%%handwave
name: Compatibility of base, section, and cover coordinates
statement:
  For a point \(x\) in a projective branch source, applying the local section coordinate to the base-chart coordinate of \(x\) gives the canonical cover-chart coordinate of the selected lift of \(x\).
proof:
  Use the defining formula for the section-coordinate transition, cancel the base chart with its inverse, and identify the selected total-space chart with the canonical chart at the lift.
-/
theorem sectionCoordinate_base_eq_chartAt_lift
    (y : D.hyperbolicDevelopingMap.cover.total)
    (x : (projectiveBranchChart D y).source) :
    let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
    S.sectionCoordinate (S.baseComplexChart (x : X)) =
      (chartAt ℂ y) (projectiveBranchLift D y x) := by
  intro S
  have hfixed := projectiveBranchChart_source_baseCoordinate_mem_fixed D y x.2
  have hbase := projectiveBranchChart_source_mem_baseChart_source D y x.2
  rw [S.sectionCoordinate_eq _ hfixed.1]
  rw [S.baseComplexChart.left_inv hbase]
  rw [S.totalComplexChart_eq_chartAt]
  rfl

/--
%%handwave
name: Finite coordinate formula for a projectivized developing branch
statement:
  On a projective branch source, the projectivized developing map at the local lift equals the finite branch coordinate, viewed in the Riemann sphere, evaluated at the base coordinate.
proof:
  The selected finite branch equals the coordinate expression of the developing map at the lifted point. Replace its cover coordinate by the compatible section coordinate of the base point.
-/
theorem branchFiniteCoordinate_eq_projective_branch
    (y : D.hyperbolicDevelopingMap.cover.total)
    (x : (projectiveBranchChart D y).source) :
    let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
    D.projectiveDev (projectiveBranchLift D y x) =
      (branchFiniteCoordinate D y (S.baseComplexChart (x : X)) : RiemannSphere) := by
  intro S
  let u : D.hyperbolicDevelopingMap.cover.total := projectiveBranchLift D y x
  have hu : u ∈ (chartAt ℂ y).source := by
    simpa [u, projectiveBranchLift] using
      projectiveBranchChart_source_lift_mem_chartAt_source D y x.2
  have hz : (chartAt ℂ y) u ∈ (finiteBranchAt D y).source := by
    simpa [u, projectiveBranchLift] using
      projectiveBranchChart_source_coordinate_mem_finiteBranch D y x.2
  have hbranch := finiteBranchAt_eq_coordinateExpression D y hz
  have hsymm : (chartAt ℂ y).symm ((chartAt ℂ y) u) = u :=
    (chartAt ℂ y).left_inv hu
  have hsection :
      (D.hyperbolicDevelopingMap.cover.localHolomorphicSection y).sectionCoordinate
          (S.baseComplexChart (x : X)) =
        (chartAt ℂ y) u := by
    simpa [S, u] using sectionCoordinate_base_eq_chartAt_lift D y x
  calc
    D.projectiveDev (projectiveBranchLift D y x) =
        (((D.hyperbolicDevelopingMap.dev u : ℍ) : ℂ) : RiemannSphere) := by
      exact D.projective_regular.finite_coordinate_eq u
    _ = ((finiteBranchAt D y ((chartAt ℂ y) u) : ℂ) : RiemannSphere) := by
      rw [hbranch.1]
      simp [HyperbolicDevelopingMapCoordinateExpression, hsymm]
    _ =
        (branchFiniteCoordinate D y (S.baseComplexChart (x : X)) : RiemannSphere) := by
      simp [branchFiniteCoordinate, hsection]

/--
%%handwave
name: Finite coordinate formula on the fixed source
statement:
  Let \(z\) lie in the fixed coordinate source, and suppose the inverse base-chart point determined by \(z\) lies in the projective branch source. Then the projectivized developing map at its selected lift equals the finite branch coordinate at \(z\), viewed in the Riemann sphere.
proof:
  Apply the branch-source finite coordinate formula to the inverse base-chart point, then use the right-inverse identity of the base chart at \(z\).
-/
theorem branchFiniteCoordinate_eq_on_source
    (y : D.hyperbolicDevelopingMap.cover.total)
    {z : ℂ} (hz : z ∈ fixedCoordinateSource D y)
    (hzsource :
      let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
      S.baseComplexChart.symm z ∈ (projectiveBranchChart D y).source) :
    let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
    D.projectiveDev
        (projectiveBranchLift D y ⟨S.baseComplexChart.symm z, hzsource⟩) =
      (branchFiniteCoordinate D y z : RiemannSphere) := by
  intro S
  have htarget : z ∈ S.baseComplexChart.target :=
    S.coordinateSource_subset_baseChart_target hz.1
  have hright :
      (D.hyperbolicDevelopingMap.cover.localHolomorphicSection y).baseComplexChart
          (S.baseComplexChart.symm z) = z := by
    exact S.baseComplexChart.right_inv htarget
  have h :=
    branchFiniteCoordinate_eq_projective_branch D y
      ⟨S.baseComplexChart.symm z, hzsource⟩
  simpa [hright] using h

/--
%%handwave
name: Holomorphicity of the finite projective branch coordinate
statement:
  The finite coordinate expression of a projective developing branch is holomorphic at every point of its fixed coordinate source.
proof:
  It is the composition of the holomorphic section-coordinate map with the selected finite developing branch, which is holomorphic on its domain.
-/
theorem branchFiniteCoordinate_holomorphic
    (y : D.hyperbolicDevelopingMap.cover.total)
    {z : ℂ} (hz : z ∈ fixedCoordinateSource D y) :
    DifferentiableAt ℂ (branchFiniteCoordinate D y) z := by
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  have hsection : DifferentiableAt ℂ S.sectionCoordinate z :=
    S.sectionCoordinate_holomorphic z hz.1
  have hbranch :
      DifferentiableAt ℂ (finiteBranchAt D y) (S.sectionCoordinate z) :=
    (finiteBranchAt_eq_coordinateExpression D y hz.2).2.1
  simpa [branchFiniteCoordinate] using hbranch.comp z hsection

/--
%%handwave
name: Regularity of the finite projective branch coordinate
statement:
  The derivative of the finite coordinate expression of a projective developing branch is nonzero throughout its fixed coordinate source.
proof:
  The chain rule factors the derivative into the derivative of the selected finite developing branch and that of the section-coordinate transition. Both factors are nonzero.
-/
theorem branchFiniteCoordinate_deriv_ne_zero
    (y : D.hyperbolicDevelopingMap.cover.total)
    {z : ℂ} (hz : z ∈ fixedCoordinateSource D y) :
    deriv (branchFiniteCoordinate D y) z ≠ 0 := by
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  have hsection : DifferentiableAt ℂ S.sectionCoordinate z :=
    S.sectionCoordinate_holomorphic z hz.1
  have hsection_deriv : deriv S.sectionCoordinate z ≠ 0 :=
    S.sectionCoordinate_deriv_ne_zero z hz.1
  have hbranchData := finiteBranchAt_eq_coordinateExpression D y hz.2
  have hderiv :
      deriv (branchFiniteCoordinate D y) z =
        deriv (finiteBranchAt D y) (S.sectionCoordinate z) *
          deriv S.sectionCoordinate z := by
    simpa [branchFiniteCoordinate] using
      deriv_comp z hbranchData.2.1 hsection
  rw [hderiv]
  exact mul_ne_zero hbranchData.2.2 hsection_deriv

/-- The constructed projective branch carries the required local-homeomorphism data.

%%handwave
name: The constructed projective branch carries the required local-homeomorphism data
statement:
  The restricted projective branch at $y$ is represented in a compatible
  source chart by a holomorphic function with nonzero derivative, agrees
  with the projectivized developing map along its local lift, and is therefore
  a local projective homeomorphism.
-/
def projectiveBranchLocalHomeomorphismData
    (y : D.hyperbolicDevelopingMap.cover.total) :
    ProjectiveDevelopingBranchLocalHomeomorphismData X D
      (projectiveBranchChart D y) (projectiveBranchLift D y) :=
  let S := D.hyperbolicDevelopingMap.cover.localHolomorphicSection y
  ProjectiveDevelopingBranchLocalHomeomorphismData.of_chart_eq_projective_branch
    (D := D)
    (chart := projectiveBranchChart D y)
    (lift := projectiveBranchLift D y)
    (projectiveBranchChart_eq_projectiveDev D y)
    (projectiveBranch_projectiveDev_continuous D y)
    (branchFiniteCoordinate D y)
    S.baseComplexChart
    S.baseComplexChart_mem_atlas
    (fixedCoordinateSource D y)
    (fixedCoordinateSource_open D y)
    (fun _z hz ↦ S.coordinateSource_subset_baseChart_target hz.1)
    (fun _x hx ↦ projectiveBranchChart_source_mem_baseChart_source D y hx)
    (fun x ↦ projectiveBranchChart_source_baseCoordinate_mem_fixed D y x.2)
    (fun x ↦ branchFiniteCoordinate_eq_projective_branch D y x)
    (fun _z hz hzsource ↦ branchFiniteCoordinate_eq_on_source D y hz hzsource)
    (fun _z hz ↦ branchFiniteCoordinate_holomorphic D y hz)
    (fun _z hz ↦ branchFiniteCoordinate_deriv_ne_zero D y hz)

/-- The local projective chart obtained from the projectivized developing map at a lift.

%%handwave
name: The local projective chart obtained from the projectivized developing map at a lift
statement:
  A lift $y\in\widetilde X$ determines a local projective chart on $X$,
  together with a continuous local lift back to $\widetilde X$, on which the
  chart equals the projectivized developing map.
-/
def projectiveLocalChartFromLift
    (y : D.hyperbolicDevelopingMap.cover.total) :
    ProjectiveLocalChartFromDevelopingMap X D where
  chart := projectiveBranchChart D y
  lift := projectiveBranchLift D y
  lift_projects := projectiveBranchLift_projects D y
  chart_eq_projectiveDev := projectiveBranchChart_eq_projectiveDev D y
  lift_continuous := projectiveBranchLift_continuous D y
  branch_local_homeomorphism := projectiveBranchLocalHomeomorphismData D y

/--
%%handwave
name: Real-Mobius transitions between projective developing branches
statement:
  Any two projective branch charts descended from a projectivized hyperbolic developing map have transition germs in \(\mathrm{PSL}_2(\mathbb R)\) at every point of their overlap.
proof:
  Lift an overlap point through the two local cover sections. A deck transformation carries one lift to the other, and local deck compatibility persists near the point. Equivariance of the projectivized developing map identifies the two branch values through the real projective holonomy element of that deck transformation.
-/
theorem projectiveBranchChart_hasTransitionInGroup
    (y z : D.hyperbolicDevelopingMap.cover.total) :
    HasTransitionInGroup psl2rMobiusSubgroup
      (projectiveBranchChart D y) (projectiveBranchChart D z) := by
  intro x hx
  rcases hx with ⟨hxy, hxz⟩
  let cover := D.hyperbolicDevelopingMap.cover
  let Sy := cover.localHolomorphicSection y
  let Sz := cover.localHolomorphicSection z
  let uy : cover.total := projectiveBranchLift D y ⟨x, hxy⟩
  let uz : cover.total := projectiveBranchLift D z ⟨x, hxz⟩
  have hfiber : cover.projection uy = cover.projection uz := by
    rw [projectiveBranchLift_projects D y ⟨x, hxy⟩,
      projectiveBranchLift_projects D z ⟨x, hxz⟩]
  rcases cover.deckAction_same_fiber_transitive uy uz hfiber with ⟨γ, hγ⟩
  rcases D.projective_equivariant γ with ⟨A, hA, hAdev⟩
  have hA_mem : Matrix.ProjGenLinGroup.mk A ∈ psl2rMobiusSubgroup := by
    rw [hA]
    refine ⟨D.hyperbolicDevelopingMap.holonomy γ, ?_⟩
    exact (congrArg (fun ρ : FundamentalGroup X x₀ →* MobiusGroup ↦ ρ γ)
      D.projectiveHolonomy_eq_complexified_real).symm
  let deckSection : X → cover.total :=
    fun u ↦ cover.deckAction γ (Sy.localProjection.symm u)
  let deckSourceNeighborhood : Set X :=
    Sy.localProjection.target ∩ deckSection ⁻¹' Sz.localProjection.source
  let neighborhood : Set X :=
    (projectiveBranchChart D y).source ∩
      ((projectiveBranchChart D z).source ∩ deckSourceNeighborhood)
  have hdeckCont :
      ContinuousOn deckSection Sy.localProjection.target := by
    change
      ContinuousOn
        (fun u : X ↦ (cover.deckTransformation γ) (Sy.localProjection.symm u))
        Sy.localProjection.target
    exact (cover.deckTransformation γ).continuous.comp_continuousOn
      Sy.localProjection.symm.continuousOn
  have hdeckSourceNeighborhood_open : IsOpen deckSourceNeighborhood := by
    exact hdeckCont.isOpen_inter_preimage Sy.localProjection.open_target
      Sz.localProjection.open_source
  have hneighborhood_open : IsOpen neighborhood :=
    (projectiveBranchChart D y).open_source.inter
      ((projectiveBranchChart D z).open_source.inter hdeckSourceNeighborhood_open)
  have hxSyTarget : x ∈ Sy.localProjection.target := by
    simpa [Sy] using projectiveBranchChart_source_subset_localProjection_target D y hxy
  have hxSzTarget : x ∈ Sz.localProjection.target := by
    simpa [Sz] using projectiveBranchChart_source_subset_localProjection_target D z hxz
  have hxDeckSource : deckSection x ∈ Sz.localProjection.source := by
    have huzSource : projectiveBranchLift D z ⟨x, hxz⟩ ∈ Sz.localProjection.source := by
      simpa [projectiveBranchLift, Sz] using
        Sz.localProjection.symm_mapsTo hxSzTarget
    simpa [deckSection, uy, uz, projectiveBranchLift, Sy, Sz] using
      hγ.symm ▸ huzSource
  have hxNeighborhood : x ∈ neighborhood :=
    ⟨hxy, ⟨hxz, ⟨hxSyTarget, hxDeckSource⟩⟩⟩
  have hsubset : neighborhood ⊆
      (projectiveBranchChart D y).source ∩ (projectiveBranchChart D z).source := by
    intro u hu
    exact ⟨hu.1, hu.2.1⟩
  refine ⟨
    { neighborhood := neighborhood
      isOpen_neighborhood := hneighborhood_open
      mem_neighborhood := hxNeighborhood
      subset_overlap := hsubset
      representative := A
      representative_mem := hA_mem
      transition_eq := ?_ }⟩
  intro w hw hwNeighborhood
  rw [OpenPartialHomeomorph.trans_source] at hw
  let b : X := (projectiveBranchChart D y).symm w
  have hwTarget : w ∈ (projectiveBranchChart D y).target := by
    simpa [OpenPartialHomeomorph.symm_source] using hw.1
  have hb_y : b ∈ (projectiveBranchChart D y).source := by
    simpa [b, OpenPartialHomeomorph.symm_target] using
      (projectiveBranchChart D y).symm_mapsTo hw.1
  have hb_z : b ∈ (projectiveBranchChart D z).source := hw.2
  have hDeckLifts :
      cover.deckAction γ (projectiveBranchLift D y ⟨b, hb_y⟩) =
        projectiveBranchLift D z ⟨b, hb_z⟩ := by
    have hbDeckSource : deckSection b ∈ Sz.localProjection.source := hwNeighborhood.2.2.2
    have hbSyTarget : b ∈ Sy.localProjection.target := hwNeighborhood.2.2.1
    have hbSzTarget : b ∈ Sz.localProjection.target := by
      simpa [Sz] using projectiveBranchChart_source_subset_localProjection_target D z hb_z
    have hprojDeck :
        cover.projection (cover.deckAction γ (Sy.localProjection.symm b)) = b := by
      rw [cover.projection_deckAction]
      exact Sy.projection_localProjection_symm hbSyTarget
    have hlocalDeck :
        Sz.localProjection (cover.deckAction γ (Sy.localProjection.symm b)) = b := by
      rw [← congrFun Sz.localProjection_eq_projection
        (cover.deckAction γ (Sy.localProjection.symm b))]
      exact hprojDeck
    have hdeck_eq_symm :
        cover.deckAction γ (Sy.localProjection.symm b) =
          Sz.localProjection.symm b := by
      calc
        cover.deckAction γ (Sy.localProjection.symm b) =
            Sz.localProjection.symm
              (Sz.localProjection
                (cover.deckAction γ (Sy.localProjection.symm b))) := by
          exact (Sz.localProjection.left_inv hbDeckSource).symm
        _ = Sz.localProjection.symm b := by
          rw [hlocalDeck]
    simpa [projectiveBranchLift, Sy, Sz] using hdeck_eq_symm
  have hright :
      (projectiveBranchChart D y)
          ((projectiveBranchChart D y).symm w) = w :=
    (projectiveBranchChart D y).right_inv hwTarget
  calc
    ((projectiveBranchChart D y).symm.trans (projectiveBranchChart D z)) w =
        (projectiveBranchChart D z) b := by
      simp [OpenPartialHomeomorph.trans_apply, b]
    _ = D.projectiveDev (projectiveBranchLift D z ⟨b, hb_z⟩) := by
      exact projectiveBranchChart_eq_projectiveDev D z ⟨b, hb_z⟩
    _ = D.projectiveDev
        (cover.deckAction γ (projectiveBranchLift D y ⟨b, hb_y⟩)) := by
      rw [hDeckLifts]
    _ = A • D.projectiveDev (projectiveBranchLift D y ⟨b, hb_y⟩) := by
      exact hAdev (projectiveBranchLift D y ⟨b, hb_y⟩)
    _ = A • (projectiveBranchChart D y b) := by
      rw [projectiveBranchChart_eq_projectiveDev D y ⟨b, hb_y⟩]
    _ = A • w := by
      rw [hright]

/--
%%handwave
name: Local Mobius transitions between projective developing branches
statement:
  Any two projective branch charts descended from the developing map are locally related by a Mobius transformation on their overlap.
proof:
  Their transition germs lie in the real projective Mobius subgroup, hence in the full Mobius group.
-/
theorem projectiveBranchChart_hasLocalMobiusTransition
    (y z : D.hyperbolicDevelopingMap.cover.total) :
    HasLocalMobiusTransition (projectiveBranchChart D y) (projectiveBranchChart D z) :=
  hasLocalMobiusTransition_of_hasTransitionInGroup
    (projectiveBranchChart_hasTransitionInGroup D y z)

end ProjectiveBranchConstruction




/--
Pointed local branch data: a selected projective branch near each point,
together with the fact that the branch chosen at `x` is actually defined at
`x`.
-/
structure ProjectivePointedLocalBranchData {x₀ : X} {g : HyperbolicMetric X}
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) where
  /-- A projective developing chart near each point of `X`. -/
  chartAt : X → ProjectiveLocalChartFromDevelopingMap X D
  /-- The selected chart near `x` contains `x`. -/
  mem_chartAt_source : ∀ x, x ∈ (chartAt x).chart.source

namespace ProjectivePointedLocalBranchData

variable {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}

end ProjectivePointedLocalBranchData

namespace ProjectiveBranchConstruction

variable {x₀ : X} {g : HyperbolicMetric X}
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g)

/-- A selected lift of a base point to the simply connected cover.

%%handwave
name: A selected lift of a base point to the simply connected cover
statement:
  For each $x\in X$, choose a point $\widetilde x\in\widetilde X$ satisfying
  $\pi(\widetilde x)=x$.
-/
def selectedLift (x : X) : D.hyperbolicDevelopingMap.cover.total :=
  Classical.choose (D.hyperbolicDevelopingMap.cover.exists_lift x)

/--
%%handwave
name: Projection of a selected cover lift
statement:
  For every base point \(x\), its selected lift to the simply connected cover projects to \(x\).
proof:
  This is the defining property of the chosen lift.
-/
theorem selectedLift_projects (x : X) :
    D.hyperbolicDevelopingMap.cover.projection (selectedLift D x) = x :=
  Classical.choose_spec (D.hyperbolicDevelopingMap.cover.exists_lift x)

/-- The selected local projective branch chart near a base point.

%%handwave
name: The selected local projective branch chart near a base point
statement:
  The selected projective chart at $x\in X$ is the descended developing
  branch associated with the chosen lift $\widetilde x$.
-/
def projectiveLocalChartAtBasePoint (x : X) :
    ProjectiveLocalChartFromDevelopingMap X D :=
  projectiveLocalChartFromLift D (selectedLift D x)

/--
%%handwave
name: A selected projective chart contains its base point
statement:
  The local projective chart obtained from the selected lift of \(x\) is defined at \(x\).
proof:
  The projective branch associated with a lift contains its projection, and the selected lift projects to \(x\).
-/
theorem mem_projectiveLocalChartAtBasePoint_source (x : X) :
    x ∈ (projectiveLocalChartAtBasePoint D x).chart.source := by
  have hmem :=
    projection_mem_projectiveBranchChart_source D (selectedLift D x)
  simpa [projectiveLocalChartAtBasePoint, selectedLift_projects D x] using hmem

/-- Pointed local projective branch data from the constructed local branches.

%%handwave
name: Pointed local projective branch data from the constructed local branches
statement:
  Assigning to every $x\in X$ the projective branch associated with its
  chosen lift gives pointed local branch data, and each selected chart
  contains its center.
-/
def projectivePointedLocalBranchData :
    ProjectivePointedLocalBranchData D where
  chartAt := projectiveLocalChartAtBasePoint D
  mem_chartAt_source := mem_projectiveLocalChartAtBasePoint_source D

end ProjectiveBranchConstruction



/--
Pointed projective branch atlas data with only genuinely overlapping
off-diagonal transitions as input.

This bundles the branch choice, source coverage, local Mobius transition
condition on nonempty overlaps, and Riemann-surface compatibility into one
object.
-/
structure ProjectivePointedOverlappingBranchAtlasData
    {x₀ : X} {g : HyperbolicMetric X}
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) where
  /-- Pointed local branches of the projectivized developing map. -/
  branchData : ProjectivePointedLocalBranchData D
  /-- Distinct selected branches with nonempty chart-source overlap have local Mobius transitions. -/
  overlapping_transition_mobius :
    ∀ x y, x ≠ y →
      Set.Nonempty ((branchData.chartAt x).chart.source ∩ (branchData.chartAt y).chart.source) →
      HasLocalMobiusTransition (branchData.chartAt x).chart (branchData.chartAt y).chart
  /-- The selected branches are compatible with the Riemann-surface structure. -/
  compatible_with_riemann_surface :
    ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData X
      branchData.chartAt


namespace ProjectivePointedOverlappingBranchAtlasData

variable {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}

/-- Fold bundled pointed overlap-only branch data into developing atlas data.

%%handwave
name: Fold bundled pointed overlap-only branch data into developing atlas data
statement:
  Pointed projective branches that cover $X$, have Möbius transitions on
  every nonempty off-diagonal overlap, and are compatible with the Riemann
  surface determine a projective developing atlas; equal-chart and empty
  overlaps supply the remaining transition cases.
-/
def toProjectiveDevelopingAtlasData
    (A : ProjectivePointedOverlappingBranchAtlasData D) :
    ProjectiveDevelopingAtlasData X D where
  chartAt := A.branchData.chartAt
  mem_chartAt_source := A.branchData.mem_chartAt_source
  transition_mobius := by
    intro x y
    by_cases hxy : x = y
    · subst y
      exact hasLocalMobiusTransition_self (A.branchData.chartAt x).chart
    · let e := (A.branchData.chartAt x).chart
      let e' := (A.branchData.chartAt y).chart
      change HasLocalMobiusTransition e e'
      by_cases hOverlap : Set.Nonempty (e.source ∩ e'.source)
      · exact A.overlapping_transition_mobius x y hxy hOverlap
      · exact hasLocalMobiusTransition_of_not_nonempty_source_inter e e' hOverlap
  compatible_with_riemann_surface := A.compatible_with_riemann_surface

end ProjectivePointedOverlappingBranchAtlasData


/--
The constructed branches form the pointed overlap branch atlas used by the
split assembly path.

%%handwave
name: The constructed branches form the pointed overlap branch atlas used by the split assembly path
statement:
  The local branches descended from a projectivized developing map cover
  $X$, have real Möbius transition germs on every nonempty overlap, and are
  compatible with the original Riemann-surface charts.
-/
def projectivePointedOverlappingBranchAtlasData
    {x₀ : X} {g : HyperbolicMetric X}
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    ProjectivePointedOverlappingBranchAtlasData D where
  branchData := ProjectiveBranchConstruction.projectivePointedLocalBranchData D
  overlapping_transition_mobius := by
    intro x y _hxy _hOverlap
    simpa [ProjectiveBranchConstruction.projectiveLocalChartAtBasePoint] using
      ProjectiveBranchConstruction.projectiveBranchChart_hasLocalMobiusTransition D
        (ProjectiveBranchConstruction.selectedLift D x)
        (ProjectiveBranchConstruction.selectedLift D y)
  compatible_with_riemann_surface :=
    ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData.ofChartAt
      (ProjectiveBranchConstruction.projectivePointedLocalBranchData D).chartAt




/--
The `PSL(2, ℝ)`-projective structure generated by a developing atlas whose
selected chart transitions lie in the complexified real Mobius subgroup.

%%handwave
name: The PSL(2, ℝ)-projective structure generated by a developing atlas whose selected chart transitions lie in the complexified real Möbius subgroup
statement:
  A projective developing atlas whose every chart transition lies in
  $\mathrm{PSL}_2(\mathbb R)$ determines a
  $\mathrm{PSL}_2(\mathbb R)$-projective structure with the same charts and
  underlying Riemann-surface compatibility.
-/
def psl2rProjectiveStructureOfDevelopingAtlas
    {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}
    (developingAtlas : ProjectiveDevelopingAtlasData X D)
    (transition_in_group :
      ∀ x y, HasTransitionInGroup psl2rMobiusSubgroup
        (developingAtlas.chartAt x).chart (developingAtlas.chartAt y).chart) :
    PSL2RProjectiveStructure X := by
  let projectiveChartedSpace : ChartedSpace RiemannSphere X :=
    { atlas := Set.range fun x ↦ (developingAtlas.chartAt x).chart
      chartAt := fun x ↦ (developingAtlas.chartAt x).chart
      mem_chart_source := developingAtlas.mem_chartAt_source
      chart_mem_atlas := fun x ↦ ⟨x, rfl⟩ }
  exact
    { projectiveChartedSpace := projectiveChartedSpace
      transition_mobius := by
        intro e he e' he'
        rcases he with ⟨x, rfl⟩
        rcases he' with ⟨y, rfl⟩
        exact hasLocalMobiusTransition_of_hasTransitionInGroup
          (transition_in_group x y)
      compatible_with_riemann_surface :=
        { projective_source_open := by
            intro e he
            rcases he with ⟨x, rfl⟩
            exact developingAtlas.compatible_with_riemann_surface.projective_source_open x
          complex_source_open :=
            developingAtlas.compatible_with_riemann_surface.complex_source_open
          projective_complex_compatible := by
            intro e he
            let x := Classical.choose he
            have hx : (developingAtlas.chartAt x).chart = e :=
              Classical.choose_spec he
            refine
              { complexChart :=
                  (developingAtlas.chartAt x).branch_local_homeomorphism.sourceComplexChart
                complexChart_mem_atlas :=
                  (developingAtlas.chartAt x).branch_local_homeomorphism.sourceComplexChart_mem_atlas
                projective_source_subset_complex_source := ?_
                compatibility := ?_ }
            · simpa [hx] using
                (developingAtlas.chartAt x).source_subset_sourceComplexChart_source
            · simpa [hx] using
                developingAtlas.compatible_with_riemann_surface.projective_complex_compatible
                  x }
      transition_in_group := by
        intro e he e' he'
        rcases he with ⟨x, rfl⟩
        rcases he' with ⟨y, rfl⟩
        exact transition_in_group x y }

/--
The same generated `PSL(2, ℝ)` atlas, packaged as the ordinary projective
atlas-from-developing-map data used by the existing induced-metric API.

%%handwave
name: The same generated PSL(2, ℝ) atlas, packaged as the ordinary projective atlas-from-developing-map data used by the existing induced-metric API
statement:
  From a developing atlas with transitions in
  $\mathrm{PSL}_2(\mathbb R)$, retain the same charts, projectivized
  developing map, and projective holonomy as a complex projective developing
  atlas.
-/
def projectiveAtlasFromPsl2rDevelopingAtlas
    {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}
    (developingAtlas : ProjectiveDevelopingAtlasData X D)
    (transition_in_group :
      ∀ x y, HasTransitionInGroup psl2rMobiusSubgroup
        (developingAtlas.chartAt x).chart (developingAtlas.chartAt y).chart) :
    ProjectiveAtlasFromDevelopingMap X D where
  developingAtlas := developingAtlas
  projectiveStructure :=
    (psl2rProjectiveStructureOfDevelopingAtlas developingAtlas
      transition_in_group).toComplexProjectiveStructure
  projectiveHolonomy := D.projectiveHolonomy
  projectiveHolonomy_eq := rfl
  charts_are_local_inverse_branches := by
    intro x
    change
      (developingAtlas.chartAt x).chart ∈
        Set.range (fun x ↦ (developingAtlas.chartAt x).chart)
    exact ⟨x, rfl⟩
  transition_mobius_from_equivariance := by
    intro x y
    exact hasLocalMobiusTransition_of_hasTransitionInGroup
      (transition_in_group x y)
  atlas_charts_locally_mobius_equiv_to_developing_branches := by
    intro e he x _hx
    refine ⟨x, developingAtlas.mem_chartAt_source x, ?_⟩
    exact
      (psl2rProjectiveStructureOfDevelopingAtlas developingAtlas
        transition_in_group).toComplexProjectiveStructure.transition_mobius_of_mem
        he ⟨x, rfl⟩
  compatible_with_riemann_surface_from_developing_map :=
    developingAtlas.compatible_with_riemann_surface

/--
%%handwave
name: Real projective transitions in the selected branch atlas
statement:
  The projective charts obtained from the selected lift at each point have pairwise transition germs in \(\mathrm{PSL}_2(\mathbb R)\).
proof:
  Each selected chart is the projective branch associated with its chosen lift. Apply the real-Mobius transition theorem for the two selected lifts.
-/
theorem projectivePointedLocalBranchData_hasTransitionInGroup
    {x₀ : X} {g : HyperbolicMetric X}
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    ∀ x y, HasTransitionInGroup psl2rMobiusSubgroup
      ((ProjectiveBranchConstruction.projectivePointedLocalBranchData D).chartAt x).chart
      ((ProjectiveBranchConstruction.projectivePointedLocalBranchData D).chartAt y).chart := by
  intro x y
  simpa [ProjectiveBranchConstruction.projectivePointedLocalBranchData,
    ProjectiveBranchConstruction.projectiveLocalChartAtBasePoint] using
    ProjectiveBranchConstruction.projectiveBranchChart_hasTransitionInGroup D
      (ProjectiveBranchConstruction.selectedLift D x)
      (ProjectiveBranchConstruction.selectedLift D y)

/--
%%handwave
name:
  Projective structure descended from a developing map
statement:
  An equivariant holomorphic local biholomorphism
  $\operatorname{dev}:\widetilde X_{x_0}\to\mathbb H\subset\mathbb{CP}^1$
  with holonomy $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$ determines
  a projective atlas on $X$. Its charts are local branches
  $\operatorname{dev}\circ s$ for local sections $s$ of the covering map,
  and all transition functions lie in $\mathrm{PSL}_2(\mathbb R)$.
proof:
  Choose a local section through a lift of each point and compose it with the
  projectivized developing map. Local biholomorphicity gives projective
  charts; two sections differ by a deck transformation, so equivariance makes
  their transition the corresponding real Möbius transformation.
-/
def psl2rProjectiveStructureOfProjectivizedDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    PSL2RProjectiveStructure X :=
  psl2rProjectiveStructureOfDevelopingAtlas
    (ProjectivePointedOverlappingBranchAtlasData.toProjectiveDevelopingAtlasData
      (projectivePointedOverlappingBranchAtlasData D))
    (by
      intro x y
      simpa [ProjectivePointedOverlappingBranchAtlasData.toProjectiveDevelopingAtlasData] using
        projectivePointedLocalBranchData_hasTransitionInGroup D x y)

/--
%%handwave
name: The descended real projective structure is induced by the hyperbolic metric
statement:
  Let a hyperbolic metric \(g\) have a projectivized developing map with holonomy in \(\mathrm{PSL}_2(\mathbb R)\). The complex projective structure obtained by descending its selected local branches is induced by \(g\).
proof:
  Assemble the selected overlapping branches into a projective developing atlas. Their transitions lie in \(\mathrm{PSL}_2(\mathbb R)\); the projective structure constructed from this atlas uses the given projectivized developing map, which is the required witness that the structure is induced by \(g\).
-/
theorem psl2rProjectiveStructureOfProjectivizedDevelopingMap_isInducedByHyperbolicMetric
    {x₀ : X} {g : HyperbolicMetric X}
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    ComplexProjectiveStructure.IsInducedByHyperbolicMetric
      (psl2rProjectiveStructureOfProjectivizedDevelopingMap D).toComplexProjectiveStructure
      g := by
  let developingAtlas :=
    ProjectivePointedOverlappingBranchAtlasData.toProjectiveDevelopingAtlasData
      (projectivePointedOverlappingBranchAtlasData D)
  let transition_in_group :
      ∀ x y, HasTransitionInGroup psl2rMobiusSubgroup
        (developingAtlas.chartAt x).chart (developingAtlas.chartAt y).chart := by
    intro x y
    simpa [developingAtlas,
      ProjectivePointedOverlappingBranchAtlasData.toProjectiveDevelopingAtlasData] using
      projectivePointedLocalBranchData_hasTransitionInGroup D x y
  refine ⟨x₀, D, projectiveAtlasFromPsl2rDevelopingAtlas developingAtlas
    transition_in_group, ?_⟩
  rfl



end HyperbolicMetric

end

end JJMath
