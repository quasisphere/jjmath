# Poisson Extension On A Disk

This note isolates the Euclidean calculation used as the local Dirichlet
solver in Perron's method.  The goal is the classical theorem that continuous
boundary data on a circle has a harmonic extension to the disk, continuous up
to the closed disk, given by the Poisson integral.

## Dirichlet Problem

The disk Dirichlet problem asks for a harmonic function in the open disk,
continuous on the closed disk, with the prescribed boundary values on the
circle.

@include{lean:JJMath.Uniformization.SolvesEuclideanDiskDirichletProblem}

The Poisson extension is the circle average of the boundary data weighted by
the Poisson kernel.

@include{lean:JJMath.Uniformization.poissonDiskExtension}

The Dirichlet candidate uses this extension in the open disk and the original
boundary function outside the open disk.  This makes the closed-disk
continuity and boundary-value statements precise without introducing a subtype
for the closed disk.

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate}

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_eq_extension_of_mem}

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_eq_data_of_not_mem}

## Kernel Estimates

At the center, the Poisson kernel is identically one on the boundary circle,
so the Poisson extension is the ordinary circle average there.

@include{lean:JJMath.Uniformization.poissonKernel_center_eq_one_of_mem_frontier}

@include{lean:JJMath.Uniformization.poissonDiskExtension_center_eq_circleAverage}

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_center_eq_circleAverage}

For an interior pole, the Poisson kernel has average one, is nonnegative on
the boundary circle, and satisfies the standard disk bound.

@include{lean:JJMath.Uniformization.circleAverage_poissonKernel_eq_one}

@include{lean:JJMath.Uniformization.poissonKernel_nonneg_of_mem_sphere_of_mem_ball}

@include{lean:JJMath.Uniformization.poissonKernel_pos_of_mem_sphere_of_mem_ball}

@include{lean:JJMath.Uniformization.poissonKernel_le_disk_bound_of_mem_sphere_of_mem_ball}

The boundary-variable continuity of the kernel gives circle integrability of
the weighted boundary data.

@include{lean:JJMath.Uniformization.poissonKernel_continuousOn_sphere_of_mem_ball}

@include{lean:JJMath.Uniformization.poissonKernel_mul_boundaryData_circleIntegrable}

## Order Properties

The Poisson extension preserves constant boundary data.

@include{lean:JJMath.Uniformization.poissonDiskExtension_const_of_mem_ball}

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_const}

@include{lean:JJMath.Uniformization.constant_solves_euclidean_disk_dirichlet_problem}

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_const_solves}

Because the kernel is nonnegative and has average one, the extension preserves
upper and lower constant bounds from the boundary circle.

@include{lean:JJMath.Uniformization.poissonDiskExtension_le_of_boundaryData_le}

@include{lean:JJMath.Uniformization.le_poissonDiskExtension_of_le_boundaryData}

The same order estimates imply preservation of uniform closeness to a
constant.  This is the quantitative form needed in the boundary-continuity
argument.

@include{lean:JJMath.Uniformization.poissonDiskExtension_sub_const_eq_circleAverage}

@include{lean:JJMath.Uniformization.abs_poissonDiskExtension_sub_const_le_of_boundaryData}

The same positivity argument gives continuity of the Poisson extension with
respect to the boundary data itself.

@include{lean:JJMath.Uniformization.poissonDiskExtension_sub_eq_circleAverage}

@include{lean:JJMath.Uniformization.abs_poissonDiskExtension_sub_poissonDiskExtension_le_of_boundaryData}

The closed-disk candidate inherits the corresponding upper and lower bounds
on the closed disk.

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_le_of_boundaryData_le}

@include{lean:JJMath.Uniformization.le_poissonDiskDirichletCandidate_of_le_boundaryData}

## Harmonicity And Boundary Values

The harmonicity proof is most efficient through the Schwarz integral.  First
we package the boundary Cauchy average and the associated holomorphic
potential whose real part is the Poisson integral.

@include{lean:JJMath.Uniformization.cauchyBoundaryAverage}

@include{lean:JJMath.Uniformization.poissonDiskComplexPotential}

The Cauchy kernels are integrable against continuous boundary data, and the
average is the normalized Cauchy integral of the weighted boundary data.

@include{lean:JJMath.Uniformization.boundaryData_complex_circleIntegrable}

@include{lean:JJMath.Uniformization.cauchyBoundaryAverage_integrand_circleIntegrable}

@include{lean:JJMath.Uniformization.cauchyWeightedBoundaryData_circleIntegrable}

@include{lean:JJMath.Uniformization.cauchyBoundaryAverage_eq_cauchyIntegral}

Mathlib's Cauchy integral power-series theorem then gives analyticity of the
Cauchy average, hence of the complex potential.  A pointwise algebraic
identity identifies its real part with the Poisson extension inside the disk.

@include{lean:JJMath.Uniformization.cauchyBoundaryAverage_analyticOnNhd}

@include{lean:JJMath.Uniformization.poissonDiskComplexPotential_analyticOnNhd}

@include{lean:JJMath.Uniformization.poissonDiskComplexPotential_re_eq_poissonDiskExtension_of_mem_ball}

Since the real part of a holomorphic function is harmonic, the Poisson
extension is harmonic in the open disk.  The candidate is harmonic there
because it agrees locally with the extension.

@include{lean:JJMath.Uniformization.poissonDiskExtension_harmonicOn}

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_harmonicOn}

At boundary points, the Poisson kernels form an approximate identity on the
circle.  Away from the chosen boundary point, the kernel is controlled by the
pole's distance to that point.  Combining that estimate with local small
oscillation of the boundary data and a global boundary bound shows that the
Poisson extension at a nearby interior point is close to the boundary value.

@include{lean:JJMath.Uniformization.poissonKernel_le_far_of_mem_closedBall}

@include{lean:JJMath.Uniformization.abs_poissonDiskExtension_sub_boundary_value_le}

This gives continuity from within the closed disk.

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_continuousWithinAt_frontier}

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_continuousOn_closedBall}

The boundary values themselves are immediate from the definition of the
candidate outside the open disk.

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_boundary_eq}

Combining harmonicity, closed-disk continuity, and the boundary equality gives
the disk Dirichlet solution.

@include{lean:JJMath.Uniformization.poissonDiskDirichletCandidate_solves}

@include{lean:JJMath.Uniformization.euclidean_disk_dirichlet_solution_by_poisson}
