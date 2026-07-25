import JJMath.PotentialTheory.EnergyMethod.Regularity
import JJMath.PotentialTheory.EnergyMethod.MazurLemma
import JJMath.Uniformization.GreenFunctionCompactSuperlevel
import JJMath.AnalyticContinuation.LocalBranch
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Energy method for Green functions

This module re-exports the split energy-method development.  The declaration
names remain in `JJMath.Uniformization`; the implementation is organized under
`JJMath/PotentialTheory/EnergyMethod/` because it is an alternative potential-
theoretic construction rather than part of the current uniformization route.
-/
