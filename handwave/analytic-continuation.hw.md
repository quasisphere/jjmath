# Analytic Continuation

Analytic continuation begins with holomorphic branches \(f_i\) on open sets
\(U_i\), together with holomorphic transition transformations relating them
on overlaps.  A path is covered by finitely many branch domains; composing the
successive transitions produces a terminal germ.  The monodromy problem is to
show that this germ depends only on the endpoint-fixed homotopy class of the
path.

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem}

## Continuation Along One Path

A continuation chain records a subdivision
\[
  0=t_0<t_1<\cdots<t_m=1
\]
and a branch valid on each subpath.  At every \(t_j\), a local transition
passes from the preceding branch to the next.  Their product transports the
initial branch to the terminal germ.

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.toTerminalGerm}

Compactness of the parameter interval produces such a finite chain whenever
local transitions are available.

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_pathContinuationChain_of_localTransitions}

Two different subdivisions of the same path are compared by passing to a
common refinement.  Once their vertices are aligned, equality of the
accumulated branch expressions propagates from one vertex to the next.
The analytic input is the identity theorem: the locus where two holomorphic
expressions agree is both open and closed in a connected overlap.

@include{lean:JJMath.AnalyticContinuation.complex_identity_theorem_of_accumulation}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.LocalExpressionAgreesAt.of_mem_closure_in_overlap}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.localExpressionAgreesAt_propagates_along_path_segment}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChain.terminalGerms_agree_of_alignedSubdivision}

The common-refinement argument is encoded as a finite walk between
continuation chains, each step preserving the terminal germ.

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChainGermWalk}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.PathContinuationChainGermWalk.terminalGerms_agree}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_pathContinuationChainGermWalk_same_path}

## The Homotopy Grid

Let \(H:[0,1]^2\to X\) be an endpoint-fixed homotopy from \(p_0\) to \(p_1\).
Compactness gives a finite rectangular grid subordinate to the branch-domain
cover: every small rectangle is mapped into one branch domain.

@include{lean:JJMath.AnalyticContinuation.exists_monotone_rectangular_subdivision_subordinate_to_open_cover}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.pathHomotopic_exists_monotone_branch_grid}

The proof then has three scales.

### One rectangle

Two adjacent cut paths have a common prefix and suffix and differ only in how
they go around one small rectangle.  Because the entire rectangle lies in a
single branch domain, both incoming continuation chains can be handed into
that common branch.  Continuing along either pair of boundary edges therefore
produces locally agreeing germs at the opposite corner.  Appending the common
suffix preserves this agreement.

The geometric cut paths are convenient parametrizations of these
prefix--rectangle--suffix decompositions.  A monotone reparametrization
transfers the rectangle comparison to the actual cut paths without changing
their terminal germs.

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_homotopyStripColumn_decomposed_terminalGerm_agreement}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_homotopyStripColumn_cutPath_terminalGerm_agreement_of_decomposed}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_homotopyStripColumn_canonical_terminalGerm_agreement}

### One strip

Move the cut path across the rectangles of a row, one column at a time.  Each
rectangle move supplies the next continuation chain and a terminal-germ
agreement.  Concatenating these moves gives a germ walk from the lower
boundary path of the strip to its upper boundary path.

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.pathContinuationChainGermWalk_stripColumns}

### The whole grid

Repeat the strip move row by row.  Concatenating the row walks gives a single
germ walk from a continuation of \(p_0\) to a continuation of \(p_1\).
The same-path refinement theorem aligns the chosen endpoint chains with the
grid chains at the beginning and end.  Thus the arbitrary terminal germs of
the two homotopic paths agree.

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.pathContinuationChainGermWalk_rows}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.pathContinuationChainHomotopyGridMovePrinciple_of_localTransitions}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_pathContinuationChainGermWalk_of_homotopic}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.pathContinuationChain_terminalGerms_agree_of_homotopic}

This column--row organization is the essential monodromy argument: analytic
uniqueness handles one continuation segment, a common branch handles one
rectangle, and finite concatenation handles the whole homotopy.

## Gluing on a Simply Connected Surface

Fix an initial branch at a basepoint.  For each \(x\), choose a path from the
basepoint to \(x\) and continue the initial branch along it.  On a simply
connected surface, any two such paths are endpoint-fixed homotopic, so the
monodromy theorem makes the resulting germ independent of the choice.

Nearby points may be reached by appending short paths inside one terminal
branch domain.  This makes the chosen germs locally compatible and hence a
coherent family.

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_coherentLocalContinuationFamily_of_simplyConnected_localTransitions}

Compatible local germs glue to a single holomorphic continuation on the whole
surface.

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.CoherentLocalContinuationFamily.toSingleValuedContinuation}

@include{lean:JJMath.AnalyticContinuation.HolomorphicLocalBranchSystem.exists_singleValuedContinuation_of_simplyConnected_localTransitions}
