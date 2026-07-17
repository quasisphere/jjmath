# The Sheaf De Rham Comparison

The local Poincare lemma has a global sheaf-theoretic consequence.  Smooth
real differential forms glue uniquely across open covers, so for each degree
they form a sheaf \(\Omega^n\).  Exterior differentiation commutes with
restriction and gives the augmented sheaf complex
\[
  0\longrightarrow\underline{\mathbb R}
  \longrightarrow\Omega^0
  \xrightarrow{d}\Omega^1
  \xrightarrow{d}\Omega^2\longrightarrow\cdots .
\]

@include{lean:JJMath.Manifold.smoothFormsAddPresheaf_isSheaf}

@include{lean:JJMath.Manifold.smoothFormsAddSheafCochainComplex}

## Exactness

At degree \(0\), exactness says that a smooth function has zero differential
exactly when it is locally constant.  In positive degree, exactness is the
local Poincare lemma: near every point, every closed form has a primitive.
Thus the augmented complex is a resolution of the constant real sheaf.

@include{lean:JJMath.Manifold.exists_realConstantAddSheaf_to_smoothFormsAddSheaf_exact}

## Fineness And Acyclicity

On a finite-dimensional Hausdorff sigma-compact smooth manifold, choose a
smooth partition of unity subordinate to a locally finite open cover.
Multiplication by the partition functions gives endomorphisms of
\(\Omega^n\), each supported in the corresponding open set, whose locally
finite sum is the identity.  Hence every \(\Omega^n\) is fine and therefore
acyclic for global sections.

@include{lean:JJMath.Manifold.smoothFormsAddSheaf_isFine}

## Comparing The Two Cohomologies

Evaluating the sheaf complex on the whole manifold recovers the ordinary
complex of global smooth forms.  Its cohomology is therefore ordinary de Rham
cohomology.

@include{lean:JJMath.Manifold.deRhamCohomology_addEquiv_smoothFormsAddSheafGlobalSectionsCohomology}

The general acyclic-resolution theorem identifies the cohomology of this
global-sections complex with the sheaf cohomology of the constant real sheaf.

@include{lean:JJMath.Manifold.smoothFormsAddSheafGlobalSectionsCohomology_addEquiv_realConstantSheafSmoothFormsUniverseCohomology_of_acyclic_deRham_resolution}

Composing the two identifications gives
\[
  H^n_{\mathrm{dR}}(M)
  \cong H^n(M;\underline{\mathbb R}).
\]
The further identification of constant-sheaf cohomology with real singular
cohomology is a separate topological comparison.
