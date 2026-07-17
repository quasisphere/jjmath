# De Rham Cohomology

The exterior derivative turns the smooth real differential forms on a smooth
manifold \(M\) into a cochain complex
\[
  \Omega^0(M)\xrightarrow{d}\Omega^1(M)
  \xrightarrow{d}\Omega^2(M)\xrightarrow{d}\cdots .
\]
Its degree-\(n\) cohomology is
\[
  H^n_{\mathrm{dR}}(M)
  =
  \frac{\ker(d:\Omega^n(M)\to\Omega^{n+1}(M))}
       {\operatorname{im}(d:\Omega^{n-1}(M)\to\Omega^n(M))},
\]
the space of closed \(n\)-forms modulo exact \(n\)-forms.

@include{lean:JJMath.Manifold.deRhamDifferential}

@include{lean:JJMath.Manifold.deRhamDifferential_comp_eq_zero}

@include{lean:JJMath.Manifold.DeRhamCohomology}

## Mayer--Vietoris

For a two-open cover \(M=U\cup V\), restriction and difference of
restrictions give a short exact sequence of complexes
\[
  0\longrightarrow\Omega^\bullet(M)
  \xrightarrow{\rho}
  \Omega^\bullet(U)\oplus\Omega^\bullet(V)
  \xrightarrow{\Delta}
  \Omega^\bullet(U\cap V)
  \longrightarrow0,
\]
where
\[
  \rho(\omega)=(\omega|_U,\omega|_V),\qquad
  \Delta(\alpha,\beta)
    =\alpha|_{U\cap V}-\beta|_{U\cap V}.
\]
The only substantial surjectivity step uses a smooth partition of unity:
multiply an overlap form by the two partition functions and extend the two
pieces by zero.

@include{lean:JJMath.Manifold.deRham_mayerVietoris_smooth_shortExact_of_partitionOfUnity}

If \(\gamma\) is closed on \(U\cap V\), choose a lift
\((\alpha,\beta)\) with \(\Delta(\alpha,\beta)=\gamma\).  The pair
\((d\alpha,d\beta)\) agrees on the overlap and therefore glues to a closed
form \(\eta\) on \(M\).  The connecting homomorphism is
\[
  \partial[\gamma]=[\eta].
\]
Changing the representative, the lift, or the partition of unity changes
\(\eta\) only by an exact form.

@include{lean:JJMath.Manifold.deRham_mayerVietoris_connectingData_nonempty_of_partitionOfUnity}

These maps form the long exact sequence
\[
  0\to H^0_{\mathrm{dR}}(M)
  \to H^0_{\mathrm{dR}}(U)\oplus H^0_{\mathrm{dR}}(V)
  \to H^0_{\mathrm{dR}}(U\cap V)
  \xrightarrow{\partial}H^1_{\mathrm{dR}}(M)\to\cdots .
\]

@include{lean:JJMath.Manifold.deRham_mayerVietoris_longExact}

## The Poincare Homotopy

Let \(U\) be a nonempty convex open subset of a finite-dimensional real vector
space and choose \(x_0\in U\).  The straight-line contraction
\[
  H_t(x)=x_0+t(x-x_0)
\]
stays inside \(U\).  Contracting the pullback of a form with the time
direction and integrating gives the homotopy operator
\[
  K\omega=\int_0^1\iota_{\partial_tH_t}H_t^*\omega\,dt.
\]

@include{lean:JJMath.Manifold.convexOpenStraightLineHomotopy}

@include{lean:JJMath.Manifold.convexOpenPoincareHomotopyOperator}

The central calculation is Cartan's homotopy identity
\[
  dK\omega+Kd\omega
  =\omega-H_0^*\omega.
\]
For a positive-degree form, \(H_0\) is constant and \(H_0^*\omega=0\).  Hence
a closed form satisfies \(\omega=d(K\omega)\).

@include{lean:JJMath.Manifold.deRham_convex_open_homotopy_operator_formula}

@include{lean:JJMath.Manifold.deRham_convex_open_closed_succ_form_has_primitive}

@include{lean:JJMath.Manifold.deRham_poincareLemma_convex_open}

Restricted boundaryless charts identify sufficiently small manifold
neighborhoods with convex model opens.  Diffeomorphism invariance transports
the convex calculation back to the manifold, giving arbitrarily small
neighborhoods on which every positive-degree closed form has a primitive.

@include{lean:JJMath.Manifold.deRham_local_poincareBasis_boundarylessModel}

@include{lean:JJMath.Manifold.DeRhamLocalPoincareBasis.exists_primitive_on_smaller_open}

## Naturality

A smooth diffeomorphism \(\varphi:M\to N\) acts contravariantly on forms by
pullback.  The identity
\[
  d(\varphi^*\omega)=\varphi^*(d\omega)
\]
shows that pullback preserves closed and exact forms and therefore descends to
de Rham cohomology.  Pullback by \(\varphi^{-1}\) is the inverse map.

@include{lean:JJMath.Manifold.smoothDifferentialFormPullbackDiffeomorph}

@include{lean:JJMath.Manifold.exteriorDerivative_smoothDifferentialFormPullbackDiffeomorph}

@include{lean:JJMath.Manifold.deRhamCohomology_linearEquiv_of_diffeomorphic}

The sheaf resolution built from smooth forms and the resulting comparison
with constant-sheaf cohomology are treated in a separate article.
