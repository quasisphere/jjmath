# Acyclic Resolutions

An acyclic resolution of a sheaf is an exact augmented cochain complex whose
terms have no positive sheaf cohomology.  Such a resolution computes the
derived functors of global sections: the cohomology of the global-sections
complex is the sheaf cohomology of the resolved sheaf.

The comparison is also functorial in the augmented resolution.  In particular,
a family of endomorphisms of the resolved sheaf which extends to a family of
endomorphisms of the resolution induces the same maps after passing either
through global-section cohomology or through sheaf cohomology.  This is the
form needed to track scalar multiplication in the de Rham resolution using
one comparison isomorphism for all scalars.

@include{lean:CategoryTheory.Sheaf.cohomology_addEquiv_of_iso}

@include{lean:CategoryTheory.Sheaf.exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_family_map_core}

@include{lean:CategoryTheory.Sheaf.exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_map_core}

@include{lean:CategoryTheory.Sheaf.globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution}

@include{lean:CategoryTheory.Sheaf.exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_map}
