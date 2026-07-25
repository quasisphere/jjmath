# The Sheaf De Rham Comparison

The local Poincare lemma has a global sheaf-theoretic consequence.  Smooth
real differential forms glue uniquely across open covers, so for each degree
they form a sheaf $\Omega^n$.  Exterior differentiation commutes with
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

At degree $0$, exactness says that a smooth function has zero differential
exactly when it is locally constant.  In positive degree, exactness is the
local Poincare lemma: near every point, every closed form has a primitive.
Thus the augmented complex is a resolution of the constant real sheaf.


@include{lean:JJMath.Manifold.realConstantAddSheafToSmoothFormsAddSheaf_mono}

## Fineness And Acyclicity

On a finite-dimensional Hausdorff sigma-compact smooth manifold, choose a
smooth partition of unity subordinate to a locally finite open cover.
Multiplication by the partition functions gives endomorphisms of
$\Omega^n$, each supported in the corresponding open set, whose locally
finite sum is the identity.  Hence every $\Omega^n$ is fine and therefore
acyclic for global sections.

@include{lean:JJMath.Manifold.smoothFormsAddSheaf_isFine}

The acyclicity theorem is proved without a Čech comparison.  Embed a fine
sheaf $\mathcal F$ into the flasque sheaf $\mathcal D(\mathcal F)$ of
discontinuous sections, whose sections are products of stalks.  Its quotient
$\mathcal Q(\mathcal F)$ is again fine: choose a locally finite shrinking and
a partition of the identity, descend the partition endomorphisms to the
quotient, and use the shrinking to control their germ supports.

@include{lean:TopCat.Sheaf.discontinuousSheaf}

@include{lean:TopCat.Sheaf.discontinuousSheaf_isFlasque}

@include{lean:TopCat.Sheaf.fineQuotient}

@include{lean:TopCat.Sheaf.fineQuotient_isFine}

A quotient section lifts locally by the skyscraper adjunction and the
filtered-colimit description of stalks.  Multiplying local lifts by the
partition endomorphisms and summing the locally finite family gives a global
lift to $\mathcal D(\mathcal F)$.  Thus global sections are exact on the
resulting short exact sequence.  Flasque acyclicity and dimension shifting,
with the fine quotient as the inductive step, now kill all positive sheaf
cohomology of $\mathcal F$.

@include{lean:TopCat.Sheaf.fineQuotient_globalSections_map_epi}

@include{lean:TopCat.Sheaf.cohomology_subsingleton_of_isFine}

## Comparing The Two Cohomologies

Evaluating the sheaf complex on the whole manifold recovers the ordinary
complex of global smooth forms.  Its cohomology is therefore ordinary de Rham
cohomology.


The general acyclic-resolution theorem identifies the cohomology of this
global-sections complex with the sheaf cohomology of the constant real sheaf.

@include{lean:JJMath.Manifold.smoothFormsAddSheafGlobalSectionsCohomology_addEquiv_realConstantSheafSmoothFormsUniverseCohomology_of_acyclic_deRham_resolution}

Smooth forms may live in a larger coefficient universe than the underlying
manifold.  To compare coefficient universes, lift the sheafified singular
cochain resolution objectwise.  Exactness survives universe lift, its terms
remain flasque, and global sections of the lifted complex are naturally the
lift of the ordinary global-section complex.  Applying the acyclic-resolution
comparison on both sides therefore identifies the large- and ordinary-universe
constant-sheaf cohomology groups, compatibly with scalar multiplication.

@include{lean:JJMath.Manifold.exists_liftedRealSingularCochainGlobalSections_homology_iso_with_scalar}

@include{lean:JJMath.Manifold.exists_liftedRealSingularCochainSheafGlobalSectionsCohomology_addEquiv_with_map_smul}

@include{lean:JJMath.Manifold.exists_sheafCompose_ulift_realConstantAddSheaf_cohomology_addEquiv_realConstantSheafCohomology_with_smul}

@include{lean:JJMath.Manifold.exists_realConstantSheafSmoothFormsUniverseCohomology_addEquiv_realConstantSheafCohomology_with_smul}

Composing these identifications gives
\[
  H^n_{\mathrm{dR}}(M)
  \cong H^n(M;\underline{\mathbb R}).
\]

@include{lean:JJMath.Manifold.exists_deRhamCohomology_addEquiv_realConstantSheafCohomology_with_smul}

On the singular side, barycentric subdivision identifies ordinary singular
cohomology with the global cohomology of the flasque singular-cochain
resolution.  Thus it computes the same constant-sheaf cohomology.  Composing
the two scalar-compatible comparisons gives the de Rham comparison theorem.

@include{lean:JJMath.Cohomology.exists_realSingularCohomology_addEquiv_realConstantSheafCohomology_with_smul_of_open_paracompact}

@include{lean:JJMath.Manifold.deRhamCohomology_nonempty_linearEquiv_realSingularCohomology}
