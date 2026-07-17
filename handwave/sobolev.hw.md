# Sobolev Theory on Riemannian Manifolds

This note collects the Sobolev input used by the variational construction of
Green functions.  The natural first-order Sobolev setting is a \(C^1\)
Riemannian manifold equipped with its Borel \(\sigma\)-algebra and a measure
compatible with the coordinate charts.  The target may be any real normed
vector space when one only wants to state weak derivatives, and a complete
real Hilbert space when one wants the \(W^{1,2}\) space itself to carry a
Hilbert structure.

For a target Hilbert space \(H\), a Sobolev map consists, after passing to
\(L^2\)-classes, of a map \(u\colon M\to H\) and a weak differential
\(du_x\colon T_xM\to H\).  The scalar weak-gradient theory is obtained by
taking \(H=\mathbb R\), where the weak differential is a cotangent field.
The surface theory used for Green functions is a specialization of this
Riemannian-manifold picture.  The analytic theorems are kept as explicit
assumptions where they have not yet been formalized: local Rellich
compactness and the Poincare inequality needed to pass from small energy to
near-constant behavior on compact sets.  The closed-graph theorem for weak
derivatives is now part of the Hilbert-space construction below.

## Coordinate Tests And Weak Derivatives

Smooth compactly supported coordinate functions are the tests used to define
weak derivatives.  In each chart, one tests against a scalar compactly
supported coordinate function and a model tangent direction.  For a map
\(u\colon M\to E\) into a real normed vector space, a differential field
\(du_x\colon T_xM\to E\) is a weak derivative when the coordinate
integration-by-parts identity
\[
  \int_\Omega d\varphi_z(v)\,u(z)\,dz
    = -\int_\Omega \varphi(z)\,du_z(v)\,dz
\]
holds for every chart, every compactly supported coordinate test, and every
model tangent vector \(v\).  The integrals are Bochner integrals in the target
space.

The measure used for the closed-graph theorem is assumed to have smooth
positive local densities with respect to Lebesgue measure in charts and to be
finite on compact sets.  This hypothesis is what allows \(L^2\)-convergence
with respect to the manifold measure to pass to the distributional chart
identities.

@include{lean:JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction}

@include{lean:JJMath.Uniformization.manifoldChartRegion}

@include{lean:JJMath.Uniformization.ManifoldDifferentialFiber}

@include{lean:JJMath.Uniformization.ManifoldDifferentialField}

@include{lean:JJMath.Uniformization.manifoldChartTangentVector}

@include{lean:JJMath.Uniformization.ManifoldDifferentialField.evalChart}

@include{lean:JJMath.Uniformization.SmoothPositiveMeasureOnManifold}

@include{lean:JJMath.Uniformization.IsWeakDerivativeOnManifoldRegionBundle}

@include{lean:JJMath.Uniformization.IsWeakDerivativeOnManifoldBundle}

## Local Sobolev Regularity

For elliptic regularity and compactness arguments, the local theory is stated
on a finite-dimensional \(C^1\) real Riemannian manifold with a smooth positive
measure.  A map \(u\colon U\to E\) into a normed vector space is locally
\(W^{1,2}\) on an open region \(U\) when it satisfies the distributional
weak-derivative identity in every coordinate chart and when both the value and
the differential field are square-integrable on every compact subset of
\(U\).  The scalar theory is obtained by taking \(E=\mathbb R\).

@include{lean:JJMath.Uniformization.IsLocalSobolevH1OnManifoldWithValues}

The compactness and Poincare statements use local \(L^2\), differential, and
\(W^{1,2}\) seminorms.  A sequence is locally \(W^{1,2}\)-bounded on a compact
set when the local \(W^{1,2}\) seminorms of its values and weak differentials
are uniformly bounded, and local \(L^2\)-convergence is measured by the
corresponding restricted measure.

@include{lean:JJMath.Uniformization.manifoldLocalValueL2SeminormSq}

@include{lean:JJMath.Uniformization.manifoldLocalDifferentialSeminormSq}

@include{lean:JJMath.Uniformization.manifoldLocalH1SeminormSq}

@include{lean:JJMath.Uniformization.BoundedInLocalSobolevH1OnManifoldWithValues}

@include{lean:JJMath.Uniformization.TendstoInLocalL2OnManifoldWithValues}

## Hilbert Structure

The Hilbert-space theorem assumes a finite-dimensional \(C^1\) Riemannian
manifold \((M,g)\), its Borel \(\sigma\)-algebra, a measure \(\mu\), and a
complete real Hilbert target \(H\).  The closed-graph theorem is formulated
for measures with smooth positive coordinate densities; the Riemannian volume
case is a specialization supplied by the metric geometry.  The abstract
\(L^2\)-section theorem is formulated for continuous Hilbert bundles over a
Borel manifold with complete fibers and the usual topological regularity
needed to make Borel measurable sections behave well.  For the first-order
Sobolev model, the two bundles are the trivial bundle \(M\times H\) and the
differential bundle \(T^\ast M\otimes H\).

The value space is
\[
  L^2(M;H),
\]
with inner product
\[
  \langle u,v\rangle_{L^2}
    = \int_M \langle u(x),v(x)\rangle_H\,d\mu(x).
\]

The first-derivative fiber at \(x\) is
\(\operatorname{Hom}(T_xM,H)\).  Its natural Hilbert inner product is the
Hilbert-Schmidt inner product determined by \(g_x\) and the inner product of
\(H\):
\[
  \langle A,B\rangle_{\mathrm{HS},x}
    = \sum_{a=1}^n \langle A e_a, B e_a\rangle_H,
\]
where \(e_1,\ldots,e_n\) is any \(g_x\)-orthonormal basis of \(T_xM\).  The
value of this sum is independent of the chosen orthonormal basis.
Equivalently, in an orthonormal frame the differential is an \(n\)-tuple of
\(H\)-vectors and the fiber norm is the square-sum of their norms.

In arbitrary local coordinates, if \(D_i u\) and \(D_i v\) are the coordinate
derivative components and \((g^{ij})\) is the inverse metric matrix, the same
pointwise pairing is
\[
  \sum_{i,j=1}^n g^{ij}(x)\,
    \langle D_i u(x),D_j v(x)\rangle_H .
\]
For the Riemannian volume measure this expression is integrated against
\(d\operatorname{vol}_g=\sqrt{\det(g_{ij})}\,dx^1\cdots dx^n\).  In an
orthonormal frame, the matrix \((g^{ij})\) is the identity and the formula
reduces to the square-sum pairing.

The \(L^2\) space of weak differentials has inner product
\[
  \langle \alpha,\beta\rangle_{L^2}
    = \int_M \langle \alpha_x,\beta_x\rangle_{\mathrm{HS},x}
      \,d\mu(x).
\]
The ambient first-order Hilbert space is therefore
\[
  L^2(M;H)\oplus L^2(M;T^\ast M\otimes H),
\]
with square-sum inner product
\[
  \langle (u,\alpha),(v,\beta)\rangle
    =
    \int_M \langle u,v\rangle_H\,d\mu
    +
    \int_M \langle \alpha,\beta\rangle_{\mathrm{HS}}\,d\mu .
\]
Both terms are best regarded as \(L^2\)-spaces of Borel bundle sections.  The
value term is the \(L^2\)-space of sections of the trivial Hilbert bundle
\(M\times H\), canonically identified with the usual Bochner space
\(L^2(M;H)\).  The differential term is the \(L^2\)-space of sections of
\(T^\ast M\otimes H\).  More generally, the same construction applies to any
continuous real Hilbert vector bundle over a Borel manifold: representatives
are almost everywhere Borel measurable sections with integrable fiberwise
square norm, and the \(L^2\) inner product is the integral of the fiberwise
inner product.  This is important on noncompact manifolds: the metric
dependent Hilbert-Schmidt norm is part of the definition, and it need not be
globally equivalent to a norm from one preferred coordinate model.

For the differential bundle \(T^\ast M\otimes H\), the present formulation
uses finite-dimensional Riemannian manifolds.  In that setting every
continuous linear map \(T_xM\to H\) is Hilbert-Schmidt once \(T_xM\) is given
the Riemannian inner product.  For infinite-dimensional manifolds the
appropriate object would instead be a bundle of Hilbert-Schmidt operators,
not the full bundle of bounded linear maps.

The Sobolev space is not this whole product.  The first Hilbert object is the
graph
\[
  \Gamma(d)=
    \{(u,\alpha)\in L^2(M;H)\oplus L^2(M;T^\ast M\otimes H)
      : \alpha \text{ is the weak differential of } u\}.
\]
The closed-graph theorem says that \(\Gamma(d)\) is a closed linear subspace
of the ambient product.  We therefore define \(W^{1,2}(M;H)\), at the Hilbert
space level, as this closed graph with the inherited inner product.  Its norm
is the graph norm
\[
  \|u\|_{W^{1,2}}^2
    = \int_M \|u\|_H^2\,d\mu
      + \int_M \|du\|_{\mathrm{HS}}^2\,d\mu .
\]
This definition avoids pretending that every \(L^2\)-class has a weak
differential: the domain of the derivative is precisely the projection of the
closed graph.  Once weak differentials are unique almost everywhere, this
graph model may be identified with the separated space of \(L^2\)-classes
which admit an \(L^2\) weak differential.

The zero-trace space \(W^{1,2}_0(M;H)\) is the closed linear subspace of this
graph Hilbert space generated by compactly supported smooth \(H\)-valued maps,
inserted into the graph by taking their classical differentials.  Equivalently,
it is the closure of compactly supported smooth maps in the graph norm.  On a
manifold with boundary this is the usual zero boundary trace condition; on a
noncompact boundaryless manifold it is the corresponding vanishing-at-infinity
condition.  Being a closed linear subspace of \(W^{1,2}(M;H)\), it is again a
real Hilbert space.

For maps with values in a Banach space, the same weak-derivative identity can
also be checked after applying continuous linear functionals on the target:
\(\lambda\circ u\) has scalar weak gradient \(\lambda\circ du\) for every
\(\lambda\in E^\ast\).  For Hilbert targets, the Riesz representation theorem
identifies these functionals with inner products against vectors in \(H\).

The Hilbert structure of the ambient first-order product only uses the
\(L^2\)-section construction.  The closedness of the weak-derivative graph is
the analytic statement that limits in
\(L^2(M;H)\oplus L^2(T^\ast M\otimes H)\) preserve all compactly supported
coordinate integration-by-parts identities.  For Riemannian volume this rests
on the smooth positive local density of the measure, but the volume-form
construction itself is recorded elsewhere.  The formal existence statement
packages this as follows: under the finite-dimensional Riemannian hypotheses,
the weak-derivative graph model of \(W^{1,2}(M;H)\) is a real Hilbert space.

@include{lean:JJMath.Uniformization.AdmitsRealHilbertStructure}

@include{lean:JJMath.Uniformization.HilbertBundleGeometry}

@include{lean:JJMath.Uniformization.HilbertBundleSectionMemL2}

@include{lean:JJMath.Uniformization.SquareIntegrableHilbertBundleSection}

@include{lean:JJMath.Uniformization.L2HilbertBundle}

@include{lean:JJMath.Uniformization.l2HilbertBundle_admits_normed_add_comm_group}

@include{lean:JJMath.Uniformization.l2HilbertBundle_admits_inner_product_space}

@include{lean:JJMath.Uniformization.l2HilbertBundle_admits_complete_space}

@include{lean:JJMath.Uniformization.l2HilbertBundle_admits_hilbert_structure}

@include{lean:JJMath.Uniformization.trivialHilbertBundleGeometry}

@include{lean:JJMath.Uniformization.ValueL2Section}

@include{lean:JJMath.Uniformization.SquareIntegrableValueSection}

@include{lean:JJMath.Uniformization.manifoldValueL2Sections_admit_hilbert_structure}

@include{lean:JJMath.Uniformization.ManifoldDifferentialTotalSpace}

@include{lean:JJMath.Uniformization.manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric}

@include{lean:JJMath.Uniformization.manifoldDifferentialHilbertBundleGeometry}

@include{lean:JJMath.Uniformization.ManifoldDifferentialFieldMemHilbertSchmidtL2}

@include{lean:JJMath.Uniformization.ManifoldDifferentialL2Section}

@include{lean:JJMath.Uniformization.SquareIntegrableManifoldDifferentialField}

@include{lean:JJMath.Uniformization.manifoldDifferentialL2Sections_admit_hilbert_structure}

@include{lean:JJMath.Uniformization.SobolevH1OnManifoldWithValuesIntrinsicAmbientModel}

@include{lean:JJMath.Uniformization.manifoldH1WithValuesIntrinsicAmbientModel_admits_hilbert_structure}

@include{lean:JJMath.Uniformization.WeakDerivativeIntrinsicGraphOnManifoldWithValues}

@include{lean:JJMath.Uniformization.SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel}

@include{lean:JJMath.Uniformization.SmoothCompactlySupportedManifoldMap}

@include{lean:JJMath.Uniformization.SmoothCompactlySupportedManifoldMap.differential}

@include{lean:JJMath.Uniformization.IsSmoothCompactlySupportedManifoldSobolevGraphElement}

@include{lean:JJMath.Uniformization.smoothCompactlySupportedManifoldSobolevGraphElements}

@include{lean:JJMath.Uniformization.SobolevH1ZeroOnManifoldWithValuesIntrinsicClosedSubmodule}

@include{lean:JJMath.Uniformization.SobolevH1ZeroOnManifoldWithValuesIntrinsicHilbertModel}

@include{lean:JJMath.Uniformization.sobolevH1ZeroOnManifoldWithValuesIntrinsic_isClosed}

@include{lean:JJMath.Uniformization.manifoldWeakDerivative_coordinateTest_identity_of_tendsto_l2_sections}

@include{lean:JJMath.Uniformization.weakDerivativeIntrinsicGraphOnManifoldWithValues_isClosed_of_smoothPositiveMeasure}

@include{lean:JJMath.Uniformization.sobolevH1OnRiemannianManifoldWithValuesIntrinsicGraph_admits_hilbert_structure}

## Compactness And Poincare

Local Rellich compactness says that a \(W^{1,2}\)-bounded sequence has an
\(L^2\)-convergent subsequence on compact subsets.  For vector-valued maps,
this strong compactness requires a finite-dimensional target, or an equivalent
compactness hypothesis on the target side; bounded sequences of constant maps
into an infinite-dimensional Hilbert space already give counterexamples.  The
formal statement below is therefore made for finite-dimensional Hilbert
targets.

The Euclidean theorem is the local compactness input.  On a
finite-dimensional coordinate domain, uniform \(W^{1,2}\)-control on an outer
compact set gives a strongly \(L^2\)-convergent subsequence on each compact
subset of its interior.  The scalar theorem is the compactness core, and the
finite-dimensional Hilbert-valued theorem follows by applying the scalar
result to finitely many orthonormal target coordinates.

On a manifold, choose coordinate charts and intermediate compact coordinate
neighborhoods contained in the outer compact set.  The smooth positive density
and the Riemannian metric are uniformly comparable with Euclidean data on each
compact chart patch, so the global \(W^{1,2}\)-bound controls the Euclidean
chart norms.  Apply Euclidean Rellich locally and diagonalize over the finite
cover.  The global \(L^2(K)\)-distance is bounded by a finite sum of the
chartwise \(L^2\)-distances, so the diagonal subsequence is Cauchy in
\(L^2(K)\); completeness gives the local Rellich subsequence.

@include{lean:JJMath.Uniformization.scalarEuclideanRellichKondrachov_subsequence_on_compact}

@include{lean:JJMath.Uniformization.euclideanRellichKondrachov_subsequence_on_compact}

@include{lean:JJMath.Uniformization.localRellich_subsequence_on_compact}

The rigidity statement identifies the possible zero-energy limits: on a
preconnected open region, a locally Sobolev function with zero weak gradient
is almost everywhere constant.

@include{lean:JJMath.Uniformization.localSobolev_zero_gradient_constant_on_preconnected}

Combining Rellich compactness with vanishing gradients gives the extraction
principle needed in contradiction arguments: after passing to a subsequence,
the functions converge in local \(L^2\) to a constant.

@include{lean:JJMath.Uniformization.localRellich_zeroGradient_subsequence_constant}

## Surface Dirichlet Capacity

For the Green-function application on surfaces, the homogeneous zero-trace
space is also used with the Dirichlet seminorm, where the \(L^2\) term is
omitted and only the metric energy of the weak gradient is measured.  Positive
capacity at infinity is the assertion that every compact set of positive
Riemannian area has a positive energy cost for zero-trace functions that are
at least one on that set.

@include{lean:JJMath.Uniformization.greenDirichletSeminormSq}

@include{lean:JJMath.Uniformization.greenDirichletSeminormSq_nonneg}

@include{lean:JJMath.Uniformization.greenLocalL2SeminormSq}

@include{lean:JJMath.Uniformization.greenLocalL2SeminormSq_nonneg}

@include{lean:JJMath.Uniformization.HasPositiveCapacityAtInfinity}

Capacitary Poincare makes the Dirichlet seminorm definite.  The direction
needed in the Green-function construction is recorded in the finite-energy
form: positive capacity at infinity controls local \(L^2\) mass by Dirichlet
energy for functions whose geometric gradient energy is integrable.

@include{lean:JJMath.Uniformization.DirichletSeminormIsNormOnH10}

@include{lean:JJMath.Uniformization.HasCapacitaryPoincareInequality}

@include{lean:JJMath.Uniformization.dirichletSeminorm_isNorm_of_capacitary_poincare}

The finite-energy contradiction argument is expressed directly in the form
used by the energy method.  If the local \(L^2\) estimate failed on a compact
set in the finite-energy class, first enlarge to a relatively compact open
neighborhood whose closure still has failed control.  A bad sequence on this
closure is localized to chart balls carrying retained mass.  Rellich
compactness gives a nonzero zero-gradient limit on a positive-measure piece,
and Egorov plus inner regularity give a compact set on which bounded
rescalings are uniformly at least one.  These rescalings give capacity
competitors with arbitrarily small energy, contradicting positive capacity at
infinity.

@include{lean:JJMath.Uniformization.greenLocalL2SeminormSq_le_const_mul_dirichlet_of_positive_capacity_of_integrable}

@include{lean:JJMath.Uniformization.greenLocalL2SeminormSq_sqrt_le_const_mul_sqrt_dirichlet_of_capacitary_poincare}

@include{lean:JJMath.Uniformization.greenLocalL2SeminormSq_sqrt_le_const_mul_sqrt_dirichlet_of_positive_capacity_of_integrable}
