# Differential Forms on Manifolds

A differential \(n\)-form assigns to each point \(x\) an alternating
\(n\)-linear functional on \(T_xM\).  This pointwise description is
coordinate-free.  Smoothness is checked in charts: after transporting the
form to the model vector space, its coefficients must have the prescribed
regularity.

The model-space object is a coefficient field
\[
  x\longmapsto \omega_x\in\operatorname{Alt}^n(E;A),
\]
where \(E\) is the model vector space and \(A\) is the coefficient space.  A
manifold form is the corresponding family
\[
  \omega_x\in\operatorname{Alt}^n(T_xM;A)
\]
whose coordinate expressions are compatible and smooth.

@include{lean:JJMath.Manifold.ModelForm}

@include{lean:JJMath.Manifold.DifferentialForm}

@include{lean:JJMath.Manifold.IsContMDiffForm}

Finite regularity, smoothness, and analyticity use the same underlying notion
of form.  Only the regularity index changes; in particular analytic forms are
smooth forms with analytic coordinate coefficient fields.

@include{lean:JJMath.Manifold.AnalyticDifferentialForm}

## Exterior Derivative

For a \(C^{r+1}\) \(n\)-form \(\omega\), the exterior derivative
\[
  d\omega\in\Omega^{n+1}(M)
\]
is defined in a chart by taking the ordinary exterior derivative of the
model-space coefficient form and transporting it back to the manifold.
Naturality of the model-space exterior derivative under smooth coordinate
changes makes this independent of the chosen chart.

@include{lean:JJMath.Manifold.exteriorDerivative}

The fundamental structural identity is
\[
  d(d\omega)=0.
\]
It is proved locally in charts from the corresponding identity for forms on
normed vector spaces.  Consequently the spaces of smooth forms assemble into
the cochain complex
\[
  \Omega^0(M)\xrightarrow{d}\Omega^1(M)
  \xrightarrow{d}\Omega^2(M)\xrightarrow{d}\cdots .
\]

@include{lean:JJMath.Manifold.exteriorDerivative_exteriorDerivative_eq_zero}

## Smooth Chains

Integration pairs differential forms with smooth singular chains.  A smooth
singular \(k\)-simplex is a continuous map from the standard simplex
\(\Delta^k\) to \(M\) which extends smoothly to a neighborhood in the ambient
affine space.  This is the usual extension criterion for smoothness on a
closed simplex and avoids introducing a separate manifold-with-corners
structure on \(\Delta^k\).

@include{lean:JJMath.Manifold.ContMDiffSingularSimplex}

@include{lean:JJMath.Manifold.SmoothSingularSimplex}

A singular chain is a finite integer linear combination of parameterized
smooth simplices.  Its boundary is the alternating sum of the restrictions to
the codimension-one faces, extended linearly:
\[
  \partial[v_0,\ldots,v_k]
  =\sum_{i=0}^k(-1)^i[v_0,\ldots,\widehat v_i,\ldots,v_k].
\]

@include{lean:JJMath.Manifold.SingularChain}

@include{lean:JJMath.Manifold.boundary}

## Integration Over Simplices And Chains

Let \(\sigma:\Delta^k\to M\) be a \(C^1\) singular simplex and let
\(\omega\) be a continuous \(k\)-form.  Pull \(\omega\) back along a \(C^1\)
extension of \(\sigma\), evaluate the resulting top-degree form on the
standard coordinate frame, and integrate its coefficient over \(\Delta^k\):
\[
  \int_\sigma\omega
  =\int_{\Delta^k}\sigma^*\omega.
\]

@include{lean:JJMath.Manifold.integrateSimplexByPullback}

The value is independent of the chosen ambient extension.  Two extensions
which agree on \(\Delta^k\) have the same derivatives in tangent directions
to the affine simplex, and hence give the same pulled-back top-degree
coefficient there.

@include{lean:JJMath.Manifold.integral_simplexPullbackCoefficientUsingExtension_eq_of_eqOn}

Permuting the vertices reparametrizes the simplex and changes the integral by
the sign of the permutation.  The integral of a chain is then the finite
signed sum of its simplex integrals.

@include{lean:JJMath.Manifold.integrateSimplexByPullback_reparametrizeVertexPermutation}

@include{lean:JJMath.Manifold.integrateChain}

Parameterized simplices have redundant representatives.  Quotienting by
oriented vertex reparametrizations gives geometric chains, and the
change-of-variables formula ensures that integration descends to this
quotient.

@include{lean:JJMath.Manifold.GeometricChain}

@include{lean:JJMath.Manifold.integrateGeometricChain}

## Stokes' Theorem

For a \(C^2\) singular simplex \(\sigma\) and a \(C^1\)
\((k-1)\)-form \(\omega\), the simplex identity is
\[
  \int_{\partial\sigma}\omega=\int_\sigma d\omega.
\]
After pulling back to the standard simplex, this is ordinary Stokes together
with the naturality of the exterior derivative.

@include{lean:JJMath.Manifold.integrateSimplexByPullback_boundary_eq_exteriorDerivative}

Linearity then gives the chain-level theorem
\[
  \int_{\partial c}\omega=\int_c d\omega.
\]
This is the fundamental compatibility between the singular boundary and the
de Rham differential.

@include{lean:JJMath.Manifold.integrateChain_boundary_eq_integrateChain_exteriorDerivative}

The quotient theory of this complex, its Mayer--Vietoris sequence, the
Poincare lemma, and its sheaf interpretation are developed separately in the
article on de Rham cohomology.
