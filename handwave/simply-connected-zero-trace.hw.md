# Zero Trace at Infinity and Compact Green Superlevels

Let \(G\) be a Green potential on a noncompact simply connected Riemann
surface \(X\), with logarithmic pole at \(p\).  The boundary condition needed
for uniformization is

\[
  \{p\}\cup\{x\in X:G(x)\ge a\}\quad\text{compact for every }a>0.
\]

Homogeneous zero trace is not a pointwise assertion along every end.  Its
effective form is capacitary: a fixed superlevel component is tested by a
truncation which still belongs to the homogeneous Dirichlet space.

## Truncating a homogeneous zero-trace function

If \(u\) represents a pure homogeneous zero-trace class and
\(T:\mathbb R\to\mathbb R\) is Lipschitz with \(T(0)=0\), then \(T\circ u\)
represents another such class.  Approximate \(T\) by smooth contractions and
use the chain rule on compactly supported smooth approximants to \(u\).  The
uniform derivative bound controls the Dirichlet norm, while the Lipschitz
bound preserves compact-local \(L^2\) convergence.

@include{lean:JJMath.Uniformization.pureH10_normalContraction_has_scalarRepresentative}

For \(0<b<a\), take

\[
  T_{b,a}(t)=\min\!\left(1,
    \max\!\left(0,\frac{t-b}{a-b}\right)\right),
  \qquad
  v_{\sigma,b,a}(x)=T_{b,a}(\sigma G(x)),
\]

where \(\sigma=1\) tests positive superlevels and \(\sigma=-1\) tests
negative ones.  The logarithmic model makes the clip constant near the pole,
so it can be spliced across the puncture.  Away from the pole it is a normal
contraction of the regular energy representative.

@include{lean:JJMath.Uniformization.fixedLevelSignedClip_has_pureH10_scalarRepresentative}

## Excluding an escaping level component

Suppose a connected open set \(\Omega\) escapes every compact subset of
\(X\), lies in \(\{\sigma G>b\}\), has frontier on the level
\(\sigma G=b\) away from the pole, and contains a point where
\(\sigma G\ge a\).  The clip is zero on the finite-level frontier and one at
the high point.  If its pure Dirichlet class were zero, positive capacity at
infinity would force compact-local \(L^2\) vanishing.  The maximum principle
on a compact piece joining the frontier to the high point gives a nonzero
contribution, a contradiction.

@include{lean:JJMath.Uniformization.fixedLevelSignedClip_zero_completion_forbidden_escaping_domain}

This is the operative meaning of zero trace: it forbids an escaping crossing
between two fixed levels.

If \(\{p\}\cup\{G\ge a\}\) is noncompact, a component of
\(\{G>a/2\}\) containing a point of height at least \(a\) escapes every
compact set.  Components whose closures avoid \(p\) are controlled by the
maximum principle.  Near \(p\), the logarithmic singularity gives a connected
punctured neighborhood, so all pole-adjacent high components coincide and
the pole is the only possible exceptional frontier point.

@include{lean:JJMath.Uniformization.noncompact_poleNormalized_positive_superlevel_has_poleAware_escaping_level_domain}

The preceding fixed-level test rules out this component.  Hence every
positive superlevel adjoined to the pole is compact.

## From the Green function to a proper disk map

Package the result as a positive Green function, harmonic away from \(p\),
with logarithmic singularity and compact positive superlevels.

@include{lean:JJMath.Uniformization.CompactSuperlevelGreenFunctionWithPole}

Choose local harmonic conjugates \(P\) of \(G\).  The logarithmic term has one
integral period around the puncture, which exponentiation removes, and simple
connectedness removes all other periods.  Thus

\[
  F=\exp(-G-iP),\qquad \log|F|=-G
\]

is globally holomorphic away from \(p\) and extends across \(p\) with a simple
zero.

@include{lean:JJMath.Uniformization.compactSuperlevelGreenFunction_exponential_planeMap}

Positivity gives \(|F|<1\) away from the pole.  If a compact subset of the
disk lies in \(\{|w|\le r\}\), with \(r<1\), then

\[
  F^{-1}(K)\subseteq \{p\}\cup\{G\ge-\log r\},
\]

and the right-hand side is compact.  Thus the compact-superlevel condition is
exactly what makes the resulting pointed disk map proper.

@include{lean:JJMath.Uniformization.compactSuperlevelGreenFunction_exponential_proper_pointedDiskMap}
