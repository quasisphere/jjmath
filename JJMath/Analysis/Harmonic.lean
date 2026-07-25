import JJMath.Analysis.Harmonic.CalderonZygmund
import JJMath.Analysis.Harmonic.CalderonZygmundDecomposition
import JJMath.Analysis.Harmonic.CalderonZygmundEnlargement
import JJMath.Analysis.Harmonic.CalderonZygmundPieces
import JJMath.Analysis.Harmonic.ComplexInterpolation
import JJMath.Analysis.Harmonic.Dyadic
import JJMath.Analysis.Harmonic.DyadicDifferentiation
import JJMath.Analysis.Harmonic.FourierMode
import JJMath.Analysis.Harmonic.Kernel
import JJMath.Analysis.Harmonic.LpDuality
import JJMath.Analysis.Harmonic.OperatorBounds
import JJMath.Analysis.Harmonic.Polar
import JJMath.Analysis.Harmonic.Truncation

/-!
# Harmonic analysis

This umbrella module exports the repository's reusable harmonic-analysis
infrastructure. It begins with translation-invariant Calderón--Zygmund kernel
conditions, full-period Fourier cancellation, and vector-valued polar
integration on planar annuli and exteriors. It also contains radial
truncations, weak/strong operator-bound predicates, and the integrated
first-difference tail estimates used for Calderón--Zygmund bad parts. The
measurable half-open dyadic grid, its maximal-square geometry, and the
bad-average stopping time through the countable disjoint maximal family and
its two-sided average estimates are also included. Ball comparison supplies
Lebesgue differentiation along the dyadic grid, the almost-everywhere
high-value covering, and the total-area estimate for the exceptional region.
The resulting good and bad pieces have their cancellation, summability,
integrability, essential bound, and $L^1$/$L^2$ estimates. Countable kernel
tails are aggregated outside a controlled enlargement whose area is bounded
explicitly. The scalar analytic deformation, finite value-fiber expansion,
uniform strip boundedness, and bilinear simple-core Riesz--Thorin estimate
needed for complex interpolation are also included. Instantiating that
theorem for operators and completing the interpolated operator by density
remain in progress.
-/
