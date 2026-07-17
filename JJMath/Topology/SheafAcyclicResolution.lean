import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Acyclic resolutions of sheaves

This file records the standard sheaf-cohomological theorem that an acyclic
resolution computes sheaf cohomology after applying global sections.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory
namespace Sheaf

noncomputable section

universe uC vC w w'

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

/--
%%handwave
name:
  Isomorphic sheaves have isomorphic sheaf cohomology
statement:
  Isomorphic sheaves of abelian groups have additively isomorphic sheaf
  cohomology groups in every degree.
proof:
  Apply the sheaf-cohomology functor to the sheaf isomorphism and read the
  resulting isomorphism of abelian-group objects as an additive equivalence.
-/
theorem cohomology_addEquiv_of_iso
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (n : ℕ) :
    Nonempty (F.H n ≃+ G.H n) := by
  exact ⟨((functorH J n).mapIso e).addCommGroupIsoToAddEquiv⟩

/--
%%handwave
name:
  Morphisms from the lifted integers are evaluation at one
statement:
  For an abelian group \(G\), homomorphisms from the universe-lifted copy of
  \(\mathbb Z\) to \(G\) are additively equivalent to elements of \(G\), by
  evaluating a homomorphism at \(1\).
proof:
  A homomorphism \(\mathbb Z\to G\) is determined by the image of \(1\).  The
  universe lift changes only the formal universe of the source group.
-/
def intULiftHomAddEquiv (G : AddCommGrpCat.{w}) :
    (AddCommGrpCat.of (ULift.{w} ℤ) ⟶ G) ≃+ G where
  toFun f := f (ULift.up (1 : ℤ))
  invFun g :=
    AddCommGrpCat.ofHom
      ((zmultiplesHom G g).comp
        ((AddEquiv.ulift : ULift.{w} ℤ ≃+ ℤ).toAddMonoidHom))
  left_inv f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    rcases x with ⟨n⟩
    have hcomp :
        f.hom.comp ((AddEquiv.ulift.symm : ℤ ≃+ ULift.{w} ℤ).toAddMonoidHom) =
          ((AddCommGrpCat.ofHom
            ((zmultiplesHom G (f (ULift.up (1 : ℤ)))).comp
              ((AddEquiv.ulift : ULift.{w} ℤ ≃+ ℤ).toAddMonoidHom))) :
              AddCommGrpCat.of (ULift.{w} ℤ) ⟶ G).hom.comp
            ((AddEquiv.ulift.symm : ℤ ≃+ ULift.{w} ℤ).toAddMonoidHom) := by
      apply AddMonoidHom.ext_int
      change f (AddEquiv.ulift.symm (1 : ℤ)) = (1 : ℤ) • f (ULift.up (1 : ℤ))
      rw [show AddEquiv.ulift.symm (1 : ℤ) = ULift.up (1 : ℤ) by rfl]
      simp
    have happ := congrArg (fun h : ℤ →+ G => h n) hcomp
    exact happ.symm
  right_inv g := by
    change (1 : ℤ) • g = g
    simp
  map_add' f g := by
    rfl

/--
%%handwave
name:
  Evaluation at one is natural in the target group
statement:
  The identification of homomorphisms \(\mathbb Z\to G\) with elements of
  \(G\) commutes with homomorphisms \(G\to H\).
proof:
  Both sides send \(n\in\mathbb Z\) to \(n\) times the image of the chosen
  element.
-/
theorem intULiftHomAddEquiv_symm_natural {G H : AddCommGrpCat.{w}} (f : G ⟶ H)
    (x : G) :
    (intULiftHomAddEquiv H).symm (f x) =
      (intULiftHomAddEquiv G).symm x ≫ f := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro y
  rcases y with ⟨n⟩
  change (n : ℤ) • f x = f ((n : ℤ) • x)
  simp

/--
%%handwave
name:
  The constant-sheaf functor is additive for abelian groups
statement:
  For abelian-group-valued sheaves, the constant-sheaf functor preserves
  addition of morphisms.
proof:
  The constant presheaf functor is additive objectwise, and sheafification is
  additive in abelian categories.
-/
theorem constantSheaf_addCommGrp_additive
    [HasSheafify J AddCommGrpCat.{w}] :
    (constantSheaf J AddCommGrpCat.{w}).Additive := by
  let constPresheaf : AddCommGrpCat.{w} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
    Functor.const Cᵒᵖ
  change (constPresheaf ⋙ presheafToSheaf J AddCommGrpCat.{w}).Additive
  haveI : constPresheaf.Additive := by
    constructor
    intro X Y f g
    ext U
    rfl
  infer_instance

/--
%%handwave
name:
  Zeroth sheaf cohomology is global sections
statement:
  The zeroth cohomology of an abelian sheaf is additively equivalent to its
  group of global sections.
proof:
  Since sheaf cohomology is defined as \(\operatorname{Ext}\) from the
  constant integer sheaf, degree zero is morphisms from that constant sheaf.
  The constant-sheaf/global-sections adjunction identifies those morphisms
  with homomorphisms from \(\mathbb Z\) to the global sections, and evaluation
  at \(1\) identifies these homomorphisms with global sections.
tags:
  milestone
-/
def cohomology_zero_addEquiv_globalSections
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) :
    F.H 0 ≃+ (Sheaf.Γ J AddCommGrpCat.{w}).obj F := by
  letI : (constantSheaf J AddCommGrpCat.{w}).Additive :=
    constantSheaf_addCommGrp_additive (J := J)
  exact
    Abelian.Ext.addEquiv₀.trans
      (((constantSheafΓAdj J AddCommGrpCat.{w}).homAddEquiv _ _).trans
        (intULiftHomAddEquiv _))

/--
%%handwave
name:
  The inverse zeroth comparison is represented by a degree-zero Ext class
statement:
  Under the identification \(H^0=\Gamma\), a global section corresponds to
  the degree-zero Ext class represented by the adjoint morphism from the
  constant sheaf.
proof:
  This is just the definition of the comparison: degree-zero Ext is morphisms
  out of the constant sheaf, then the constant-sheaf/global-sections
  adjunction and evaluation at \(1\) identify such morphisms with global
  sections.
-/
theorem cohomology_zero_addEquiv_globalSections_symm_apply
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (x : (Sheaf.Γ J AddCommGrpCat.{w}).obj F) :
    (cohomology_zero_addEquiv_globalSections (J := J) F).symm x =
      Abelian.Ext.mk₀
        (((constantSheafΓAdj J AddCommGrpCat.{w}).homEquiv
            (AddCommGrpCat.of (ULift ℤ)) F).symm
          ((intULiftHomAddEquiv ((Sheaf.Γ J AddCommGrpCat.{w}).obj F)).symm x)) := by
  letI : (constantSheaf J AddCommGrpCat.{w}).Additive :=
    constantSheaf_addCommGrp_additive (J := J)
  let Cℤ : Sheaf J AddCommGrpCat.{w} :=
    (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  let m : Cℤ ⟶ F :=
    (((constantSheafΓAdj J AddCommGrpCat.{w}).homEquiv
        (AddCommGrpCat.of (ULift ℤ)) F).symm
      ((intULiftHomAddEquiv ((Sheaf.Γ J AddCommGrpCat.{w}).obj F)).symm x))
  change (Abelian.Ext.addEquiv₀ (X := Cℤ) (Y := F)).symm m = Abelian.Ext.mk₀ m
  have hmk : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ m) = m := by
    apply (Abelian.Ext.mk₀_bijective Cℤ F).1
    exact Abelian.Ext.mk₀_addEquiv₀_apply (Abelian.Ext.mk₀ m)
  apply (Abelian.Ext.addEquiv₀ (X := Cℤ) (Y := F)).injective
  rw [hmk]
  exact (Abelian.Ext.addEquiv₀ (X := Cℤ) (Y := F)).right_inv m

/--
%%handwave
name:
  The zeroth cohomology/global-sections comparison is natural
statement:
  For a morphism of abelian sheaves \(F\to G\), the identification
  \(H^0=\Gamma\) intertwines the induced map on zeroth sheaf cohomology with
  the induced map on global sections.
proof:
  Unfold \(H^0\) as morphisms out of the constant integer sheaf.  Naturality
  is postcomposition by the sheaf morphism, followed through the
  constant-sheaf/global-sections adjunction and evaluation at \(1\).
-/
theorem cohomology_zero_addEquiv_globalSections_symm_natural
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G)
    (x : (Sheaf.Γ J AddCommGrpCat.{w}).obj F) :
    (cohomology_zero_addEquiv_globalSections (J := J) G).symm
        ((Sheaf.Γ J AddCommGrpCat.{w}).map f x) =
      ((functorH J 0).map f)
        ((cohomology_zero_addEquiv_globalSections (J := J) F).symm x) := by
  rw [cohomology_zero_addEquiv_globalSections_symm_apply (J := J) G,
    cohomology_zero_addEquiv_globalSections_symm_apply (J := J) F]
  let Cℤ : Sheaf J AddCommGrpCat.{w} :=
    (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  let mF : Cℤ ⟶ F :=
    (((constantSheafΓAdj J AddCommGrpCat.{w}).homEquiv
        (AddCommGrpCat.of (ULift ℤ)) F).symm
      ((intULiftHomAddEquiv ((Sheaf.Γ J AddCommGrpCat.{w}).obj F)).symm x))
  let mG : Cℤ ⟶ G :=
    (((constantSheafΓAdj J AddCommGrpCat.{w}).homEquiv
        (AddCommGrpCat.of (ULift ℤ)) G).symm
      ((intULiftHomAddEquiv ((Sheaf.Γ J AddCommGrpCat.{w}).obj G)).symm
        ((Sheaf.Γ J AddCommGrpCat.{w}).map f x)))
  change Abelian.Ext.mk₀ mG =
    (Abelian.Ext.mk₀ mF).comp (Abelian.Ext.mk₀ f) (add_zero 0)
  rw [Abelian.Ext.mk₀_comp_mk₀]
  congr 1
  have hint :
      (intULiftHomAddEquiv ((Sheaf.Γ J AddCommGrpCat.{w}).obj G)).symm
          ((Sheaf.Γ J AddCommGrpCat.{w}).map f x) =
        (intULiftHomAddEquiv ((Sheaf.Γ J AddCommGrpCat.{w}).obj F)).symm x ≫
          (Sheaf.Γ J AddCommGrpCat.{w}).map f :=
    intULiftHomAddEquiv_symm_natural
      ((Sheaf.Γ J AddCommGrpCat.{w}).map f) x
  dsimp [mF, mG]
  rw [hint]
  exact
    (constantSheafΓAdj J AddCommGrpCat.{w}).homEquiv_naturality_right_symm
      ((intULiftHomAddEquiv ((Sheaf.Γ J AddCommGrpCat.{w}).obj F)).symm x) f

/--
%%handwave
name:
  Sheaf-cohomology maps commute with degree casts
statement:
  If two natural-number degrees are equal, then transporting cohomology groups
  across that equality commutes with the map induced by a morphism of sheaves.
proof:
  Induct on the equality of degrees.
-/
theorem sheafCohomology_cast_map
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G)
    {n m : ℕ} (h : n = m) (x : F.H n) :
    (AddEquiv.cast (M := fun k : ℕ => G.H k) h)
      (((functorH J n).map f) x) =
    ((functorH J m).map f)
      ((AddEquiv.cast (M := fun k : ℕ => F.H k) h) x) := by
  cases h
  rfl

/--
%%handwave
name:
  Global sections are left exact on the first augmented short complex
statement:
  If \(F\to K^0\to K^1\) is exact, then applying global sections gives an
  exact sequence \(\Gamma(F)\to\Gamma(K^0)\to\Gamma(K^1)\), and the first
  map is a monomorphism.
proof:
  Global sections are a right adjoint to the constant-sheaf functor, hence
  preserve finite limits.  In an abelian category, preserving finite limits is
  equivalent to preserving exactness on the left of short exact sequences.
-/
theorem globalSections_first_augmented_shortComplex_exact_and_mono
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε) :
    ((({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).map
      (Sheaf.Γ J AddCommGrpCat.{w})).Exact ∧
      Mono ((Sheaf.Γ J AddCommGrpCat.{w}).map ε)) := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    { f := ε, g := K.d 0 1, zero := hε }
  letI : (constantSheaf J AddCommGrpCat.{w}).Additive :=
    constantSheaf_addCommGrp_additive (J := J)
  haveI : (Sheaf.Γ J AddCommGrpCat.{w}).Additive :=
    (constantSheafΓAdj J AddCommGrpCat.{w}).right_adjoint_additive
  haveI : PreservesFiniteLimits (Sheaf.Γ J AddCommGrpCat.{w}) := by
    infer_instance
  have hΓ_preservesFiniteLimits :
      PreservesFiniteLimits (Sheaf.Γ J AddCommGrpCat.{w}) :=
    inferInstance
  have hleft' :
      ∀ (T : ShortComplex (Sheaf J AddCommGrpCat.{w})), T.Exact ∧ Mono T.f →
        (T.map (Sheaf.Γ J AddCommGrpCat.{w})).Exact ∧
          Mono ((Sheaf.Γ J AddCommGrpCat.{w}).map T.f) :=
    ((Functor.preservesFiniteLimits_tfae
      (Sheaf.Γ J AddCommGrpCat.{w})).out 3 1).1 hΓ_preservesFiniteLimits
  exact hleft' S ⟨hexact_zero, hmono_ε⟩

/--
%%handwave
name:
  Zeroth homology of a left-exact augmented cochain complex
statement:
  Let \(A\to K^0\to K^1\) be exact with \(A\to K^0\) a monomorphism in
  abelian groups.  If a family of endomorphisms of \(A\) extends to the
  cochain complex \(K^\bullet\), then \(H^0(K^\bullet)\) is additively
  isomorphic to \(A\), compatibly with that family.
proof:
  Since there is no incoming differential at degree zero, \(H^0(K^\bullet)\)
  is the kernel of \(K^0\to K^1\).  Exactness and monicity identify this
  kernel with \(A\).  The compatibility with endomorphisms follows by the
  uniqueness of maps into a kernel and the commutative square at the
  augmentation.
tags:
  milestone
-/
theorem exists_homology_zero_addEquiv_of_left_exact_augmented_cochain_with_family_map
    (A : AddCommGrpCat.{w})
    (K : CochainComplex AddCommGrpCat.{w} ℕ)
    (ε : A ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex AddCommGrpCat.{w}).Exact)
    (hmono_ε : Mono ε)
    {ι : Type*}
    (φA : ι → (A ⟶ A)) (φK : ι → (K ⟶ K))
    (hε_map : ∀ i, ε ≫ (φK i).f 0 = φA i ≫ ε) :
    ∃ e : ↥(K.homology 0) ≃+ A,
      ∀ (i : ι) (x : ↥(K.homology 0)),
        e ((HomologicalComplex.homologyMap (φK i) 0) x) = φA i (e x) := by
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by
    simp
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 := by
    simp
  let S01 : ShortComplex AddCommGrpCat.{w} := K.sc' 0 0 1
  let kf01 : KernelFork S01.g := KernelFork.ofι ε (by simpa [S01] using hε)
  haveI : Mono ε := hmono_ε
  have hkf01 : IsLimit kf01 := by
    simpa [S01, kf01] using hexact_zero.fIsKernel
  let isoCycles01 : A ≅ S01.cycles :=
    S01.isoCyclesOfIsLimit (kf := kf01) hkf01
  let isoSc : K.cycles 0 ≅ S01.cycles :=
    K.cyclesIsoSc' 0 0 1 hprev hnext
  let isoCycles : A ≅ K.cycles 0 :=
    isoCycles01 ≪≫ isoSc.symm
  let iso : K.homology 0 ≅ A :=
    K.isoHomologyπ₀.symm ≪≫ isoCycles.symm
  refine ⟨iso.addCommGroupIsoToAddEquiv, ?_⟩
  intro i x
  have hiso_inv : isoCycles.inv ≫ ε = K.iCycles 0 := by
    have h01 : isoCycles01.inv ≫ ε = S01.iCycles := by
      simpa [isoCycles01, kf01] using
        (ShortComplex.isoCyclesOfIsLimit_inv_ι (S := S01) (kf := kf01) hkf01)
    have hSc : isoSc.hom ≫ S01.iCycles = K.iCycles 0 := by
      simpa [isoSc, S01] using
        (HomologicalComplex.cyclesIsoSc'_hom_iCycles (K := K) 0 0 1 hprev hnext)
    simpa [isoCycles, Category.assoc, h01] using hSc
  have hcycles :
      HomologicalComplex.cyclesMap (φK i) 0 ≫ isoCycles.inv =
        isoCycles.inv ≫ φA i := by
    apply (cancel_mono ε).1
    calc
      HomologicalComplex.cyclesMap (φK i) 0 ≫ isoCycles.inv ≫ ε
          = HomologicalComplex.cyclesMap (φK i) 0 ≫ K.iCycles 0 := by
              simp [hiso_inv]
      _ = K.iCycles 0 ≫ (φK i).f 0 := by
              simp
      _ = isoCycles.inv ≫ ε ≫ (φK i).f 0 := by
              simpa [Category.assoc] using
                congrArg (fun q => q ≫ (φK i).f 0) hiso_inv.symm
      _ = isoCycles.inv ≫ (φA i ≫ ε) := by
              simpa [Category.assoc] using congrArg (fun q : A ⟶ K.X 0 => isoCycles.inv ≫ q)
                (hε_map i)
      _ = isoCycles.inv ≫ φA i ≫ ε := by
              simp
  have hmorph :
      HomologicalComplex.homologyMap (φK i) 0 ≫ iso.hom =
        iso.hom ≫ φA i := by
    calc
      HomologicalComplex.homologyMap (φK i) 0 ≫ iso.hom
          = (HomologicalComplex.homologyMap (φK i) 0 ≫ K.isoHomologyπ₀.inv) ≫
              isoCycles.inv := by
                simp [iso, Category.assoc]
      _ = (K.isoHomologyπ₀.inv ≫ HomologicalComplex.cyclesMap (φK i) 0) ≫
              isoCycles.inv := by
                rw [CochainComplex.isoHomologyπ₀_inv_naturality]
      _ = K.isoHomologyπ₀.inv ≫
              (HomologicalComplex.cyclesMap (φK i) 0 ≫ isoCycles.inv) := by
                simp [Category.assoc]
      _ = K.isoHomologyπ₀.inv ≫ (isoCycles.inv ≫ φA i) := by
                rw [hcycles]
      _ = iso.hom ≫ φA i := by
                simp [iso, Category.assoc]
  exact congrArg (fun g : K.homology 0 ⟶ A => g x) hmorph

/--
%%handwave
name:
  Zeroth global-section homology is the kernel of the augmentation
statement:
  Let \(F\to K^0\to K^1\) be exact with \(F\to K^0\) a monomorphism.  If a
  family of endomorphisms of \(F\) extends to \(K^\bullet\), then the zeroth
  homology of \(\Gamma(K^\bullet)\) is additively isomorphic to
  \(\Gamma(F)\), compatibly with all endomorphisms in the family.
proof:
  Applying global sections preserves the exactness and monomorphism at the
  left end, so \(\Gamma(F)\) is the kernel of
  \(\Gamma(K^0)\to\Gamma(K^1)\).  In a cochain complex indexed by
  \(\mathbb N\), there is no incoming differential into degree zero, hence
  zeroth homology is precisely this kernel.  Naturality follows from the
  commutative square between the augmentations.
tags:
  milestone
-/
theorem exists_globalSections_homology_zero_addEquiv_globalSections_of_left_exact_resolution_with_family_map
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    {ι : Type*}
    (φF : ι → (F ⟶ F)) (φK : ι → (K ⟶ K))
    (hε_map : ∀ i, ε ≫ (φK i).f 0 = φF i ≫ ε) :
    ∃ e :
      ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology 0) ≃+
        (Sheaf.Γ J AddCommGrpCat.{w}).obj F,
      ∀ (i : ι)
        (x :
          ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj K).homology 0)),
        e ((HomologicalComplex.homologyMap
      (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (φK i)) 0) x) =
          ((Sheaf.Γ J AddCommGrpCat.{w}).map (φF i)) (e x) := by
  let Γ : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
    Sheaf.Γ J AddCommGrpCat.{w}
  let ΓK : CochainComplex AddCommGrpCat.{w} ℕ :=
    (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  have hleft :=
    globalSections_first_augmented_shortComplex_exact_and_mono
      (J := J) F K ε hε hexact_zero hmono_ε
  have hεΓ : Γ.map ε ≫ ΓK.d 0 1 = 0 := by
    simpa [ΓK, Γ, Functor.map_comp] using congrArg (fun g => Γ.map g) hε
  have hexactΓ :
      ({ f := Γ.map ε, g := ΓK.d 0 1, zero := hεΓ } :
        ShortComplex AddCommGrpCat.{w}).Exact := by
    simpa [ΓK, Γ] using hleft.1
  have hεΓ_map :
      ∀ i, Γ.map ε ≫
          (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map (φK i)).f 0) =
        Γ.map (φF i) ≫ Γ.map ε := by
    intro i
    simpa [ΓK, Γ, Functor.map_comp] using congrArg (fun g => Γ.map g) (hε_map i)
  exact
    exists_homology_zero_addEquiv_of_left_exact_augmented_cochain_with_family_map
      (A := Γ.obj F) (K := ΓK) (ε := Γ.map ε) hεΓ hexactΓ hleft.2
      (fun i => Γ.map (φF i))
      (fun i => (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map (φK i))
      hεΓ_map

/--
%%handwave
name:
  Zeroth acyclic-resolution comparison is natural for a family of endomorphisms
statement:
  Let \(F\to K^0\to K^1\) be exact with \(F\to K^0\) a monomorphism.  If a
  family of endomorphisms of \(F\) extends to \(K^\bullet\), then the
  canonical comparison from the zeroth cohomology of \(\Gamma(K^\bullet)\)
  to \(H^0(F)\) may be chosen to intertwine all endomorphisms.
proof:
  Apply left exactness of global sections to identify
  \(H^0(\Gamma(K^\bullet))\) with \(\Gamma(F)\).  Then use the degree-zero
  identification \(H^0(F)=\Gamma(F)\).  Naturality of kernels and of this
  degree-zero identification gives compatibility with the endomorphisms.
tags:
  milestone
-/
theorem exists_globalSections_zero_homology_addEquiv_sheafCohomology_of_left_exact_resolution_with_family_map
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    {ι : Type*}
    (φF : ι → (F ⟶ F)) (φK : ι → (K ⟶ K))
    (hε_map : ∀ i, ε ≫ (φK i).f 0 = φF i ≫ ε) :
    ∃ e :
      ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology 0) ≃+
        F.H 0,
      ∀ (i : ι)
        (x :
          ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj K).homology 0)),
        e ((HomologicalComplex.homologyMap
              (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
                (ComplexShape.up ℕ)).map (φK i)) 0) x) =
          ((functorH J 0).map (φF i)) (e x) := by
  rcases
      exists_globalSections_homology_zero_addEquiv_globalSections_of_left_exact_resolution_with_family_map
        (J := J) (F := F) (K := K) ε hε hexact_zero hmono_ε φF φK hε_map with
    ⟨eΓ, heΓ⟩
  let e0 : F.H 0 ≃+ (Sheaf.Γ J AddCommGrpCat.{w}).obj F :=
    cohomology_zero_addEquiv_globalSections (J := J) F
  refine ⟨eΓ.trans e0.symm, ?_⟩
  intro i x
  dsimp [e0]
  rw [heΓ i x]
  exact
    cohomology_zero_addEquiv_globalSections_symm_natural
      (J := J) (F := F) (G := F) (φF i) (eΓ x)

/--
%%handwave
name:
  Dimension shifting across an acyclic middle term
statement:
  In a short exact sequence of sheaves
  \(0\to A\to B\to C\to0\), if \(B\) has vanishing positive sheaf
  cohomology, then the connecting morphism gives an additive isomorphism
  \(H^q(C)\simeq H^{q+1}(A)\) for every \(q>0\).
proof:
  Use the long exact Ext sequence attached to the short exact sequence.  The
  two neighbouring groups involving \(B\) vanish in the relevant positive
  degrees, so exactness makes the connecting morphism both injective and
  surjective.
tags:
  milestone
-/
noncomputable def sheafCohomology_connecting_addEquiv_of_middle_acyclic_pos
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact)
    (hacyclic₂ : ∀ q : ℕ, 0 < q → Subsingleton (S.X₂.H q))
    (q : ℕ) (hq : 0 < q) :
    S.X₃.H q ≃+ S.X₁.H (q + 1) := by
  let Cℤ : Sheaf J AddCommGrpCat.{w} :=
    (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  let δ : S.X₃.H q →+ S.X₁.H (q + 1) :=
    hS.extClass.postcomp Cℤ (show q + 1 = q + 1 by rfl)
  haveI hmiddle_q : Subsingleton (Abelian.Ext Cℤ S.X₂ q) := by
    dsimp [Cℤ, Sheaf.H]
    exact hacyclic₂ q hq
  haveI hmiddle_succ : Subsingleton (Abelian.Ext Cℤ S.X₂ (q + 1)) := by
    dsimp [Cℤ, Sheaf.H]
    exact hacyclic₂ (q + 1) (Nat.succ_pos q)
  refine AddEquiv.ofBijective δ ⟨?_, ?_⟩
  · intro x y hxy
    have hδ_sub : δ (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨u, hu⟩ :=
      Abelian.Ext.covariant_sequence_exact₃ (X := Cℤ) hS
        (x - y) (hn₁ := rfl) hδ_sub
    have hu_zero : u = 0 := Subsingleton.elim _ _
    have hsub_zero : x - y = 0 := by
      simpa [hu_zero] using hu.symm
    exact sub_eq_zero.mp hsub_zero
  · intro y
    have hy :
        y.comp (Abelian.Ext.mk₀ S.f) (add_zero (q + 1)) = 0 := by
      exact Subsingleton.elim _ _
    obtain ⟨x, hx⟩ :=
      Abelian.Ext.covariant_sequence_exact₁ (X := Cℤ) hS
        y hy (hn₀ := rfl)
    exact ⟨x, hx⟩

/--
%%handwave
name:
  Connecting isomorphisms are natural
statement:
  The dimension-shifting isomorphism attached to a short exact sequence with
  acyclic middle term commutes with an endomorphism of that short exact
  sequence.
proof:
  The isomorphism is induced by composition with the extension class of the
  short exact sequence.  Naturality of extension classes for morphisms of
  short exact sequences identifies the two possible composites.
-/
theorem sheafCohomology_connecting_addEquiv_of_middle_acyclic_pos_natural_self
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact)
    (hacyclic₂ : ∀ q : ℕ, 0 < q → Subsingleton (S.X₂.H q))
    (φ : S ⟶ S)
    (q : ℕ) (hq : 0 < q)
    (x : S.X₃.H q) :
    (sheafCohomology_connecting_addEquiv_of_middle_acyclic_pos
        (J := J) hS hacyclic₂ q hq)
      (((functorH J q).map φ.τ₃) x) =
    ((functorH J (q + 1)).map φ.τ₁)
      ((sheafCohomology_connecting_addEquiv_of_middle_acyclic_pos
        (J := J) hS hacyclic₂ q hq) x) := by
  let Cℤ : Sheaf J AddCommGrpCat.{w} :=
    (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  change
    (x.comp (Abelian.Ext.mk₀ φ.τ₃) (add_zero q)).comp
        hS.extClass (show q + 1 = q + 1 by rfl) =
      (x.comp hS.extClass (show q + 1 = q + 1 by rfl)).comp
        (Abelian.Ext.mk₀ φ.τ₁) (add_zero (q + 1))
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [← hS.extClass_naturality hS φ]

/--
%%handwave
name:
  Boundaries embed in the next cycles under exactness
statement:
  If a cochain complex of sheaves is exact in degree \(p\), then the natural
  map from boundaries in degree \(p\) to cycles in degree \(p+1\) is a
  monomorphism.
proof:
  Use the exact four-term sequence
  \(H^p\to B^{p+1}\to Z^{p+1}\to H^{p+1}\).  Exactness in degree \(p\)
  makes \(H^p\) vanish, so exactness at the middle term makes the boundary-to-
  cycle map a monomorphism.
-/
theorem cochain_mono_opcyclesToCycles_of_exactAt
    [HasSheafify J AddCommGrpCat.{w}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (p : ℕ) (hp : K.ExactAt p) :
    Mono (K.opcyclesToCycles p (p + 1)) := by
  have hrel : (ComplexShape.up ℕ).Rel p (p + 1) := by simp
  have hseq :=
    HomologicalComplex.HomologySequence.composableArrows₃_exact
      (K := K) p (p + 1) hrel
  have hshort :
      (ShortComplex.mk (K.homologyι p) (K.opcyclesToCycles p (p + 1))
        (by simp)).Exact := by
    simpa [HomologicalComplex.HomologySequence.composableArrows₃] using
      hseq.exact 0
  have hzero : K.homologyι p = 0 :=
    (HomologicalComplex.ExactAt.isZero_homology (K := K) hp).eq_of_src _ _
  exact hshort.mono_g hzero

/--
%%handwave
name:
  Boundaries cover the next cycles under exactness
statement:
  If a cochain complex of sheaves is exact in degree \(p+1\), then the
  natural map from boundaries in degree \(p\) to cycles in degree \(p+1\) is
  an epimorphism.
proof:
  Use the exact four-term sequence
  \(H^p\to B^{p+1}\to Z^{p+1}\to H^{p+1}\).  Exactness in degree \(p+1\)
  makes \(H^{p+1}\) vanish, so exactness at \(Z^{p+1}\) makes the
  boundary-to-cycle map an epimorphism.
-/
theorem cochain_epi_opcyclesToCycles_of_exactAt_succ
    [HasSheafify J AddCommGrpCat.{w}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (p : ℕ) (hsucc : K.ExactAt (p + 1)) :
    Epi (K.opcyclesToCycles p (p + 1)) := by
  have hrel : (ComplexShape.up ℕ).Rel p (p + 1) := by simp
  have hseq :=
    HomologicalComplex.HomologySequence.composableArrows₃_exact
      (K := K) p (p + 1) hrel
  have hshort :
      (ShortComplex.mk (K.opcyclesToCycles p (p + 1)) (K.homologyπ (p + 1))
        (by simp)).Exact := by
    simpa [HomologicalComplex.HomologySequence.composableArrows₃] using
      hseq.exact 1
  have hzero : K.homologyπ (p + 1) = 0 :=
    (HomologicalComplex.ExactAt.isZero_homology (K := K) hsucc).eq_of_tgt _ _
  exact hshort.epi_f hzero

/--
%%handwave
name:
  The cycles-to-next-cycles short sequence
statement:
  For a cochain complex of sheaves that is exact in degrees \(p\) and
  \(p+1\), the sequence \(0\to Z^p\to K^p\to Z^{p+1}\to0\) is short exact.
proof:
  Exactness in degree \(p\) gives the short exact sequence
  \(0\to Z^p\to K^p\to B^{p+1}\to0\).  The preceding two lemmas identify
  \(B^{p+1}\to Z^{p+1}\) as both mono and epi, hence as an isomorphism in
  the balanced abelian category of sheaves.  Transport exactness across this
  isomorphism.
tags:
  milestone
-/
theorem cochain_cycles_shortExact_of_exactAt_and_succ
    [HasSheafify J AddCommGrpCat.{w}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (p : ℕ) (hp : K.ExactAt p) (hsucc : K.ExactAt (p + 1)) :
    (ShortComplex.mk (K.iCycles p) (K.toCycles p (p + 1))
      (by
        rw [← cancel_mono (K.iCycles (p + 1)), Category.assoc,
          HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d, zero_comp])).ShortExact := by
  have hmono_bridge : Mono (K.opcyclesToCycles p (p + 1)) :=
    cochain_mono_opcyclesToCycles_of_exactAt (J := J) K p hp
  have hepi_bridge : Epi (K.opcyclesToCycles p (p + 1)) :=
    cochain_epi_opcyclesToCycles_of_exactAt_succ (J := J) K p hsucc
  haveI : Mono (K.opcyclesToCycles p (p + 1)) := hmono_bridge
  haveI : Epi (K.opcyclesToCycles p (p + 1)) := hepi_bridge
  haveI : IsIso (K.opcyclesToCycles p (p + 1)) := isIso_of_mono_of_epi _
  have hbase_short :
      (ShortComplex.mk (K.iCycles p) (K.pOpcycles p)
        (by
          simpa [HomologicalComplex.iCycles, HomologicalComplex.pOpcycles] using
            ((ShortComplex.exact_iff_iCycles_pOpcycles_zero (S := K.sc p)).mp hp))).ShortExact := by
    let S : ShortComplex (Sheaf J AddCommGrpCat.{w}) := K.sc p
    let h : S.HomologyData := S.homologyData
    let Sabs : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
      ShortComplex.mk h.left.i h.right.p (h.exact_iff_i_p_zero.1 (show S.Exact from hp))
    let Scan : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
      ShortComplex.mk (K.iCycles p) (K.pOpcycles p)
        (by
          simpa [S, HomologicalComplex.iCycles, HomologicalComplex.pOpcycles] using
            ((ShortComplex.exact_iff_iCycles_pOpcycles_zero (S := K.sc p)).mp hp))
    have hSabs : Sabs.ShortExact :=
      (show S.Exact from hp).shortExact h
    let e : Sabs ≅ Scan :=
      ShortComplex.isoMk h.left.cyclesIso.symm (Iso.refl _) h.right.opcyclesIso.symm
        (by
          dsimp [Sabs, Scan]
          simpa [S, HomologicalComplex.iCycles] using h.left.cyclesIso_inv_comp_iCycles)
        (by
          dsimp [Sabs, Scan]
          simpa [S, HomologicalComplex.pOpcycles] using h.right.p_comp_opcyclesIso_inv.symm)
    exact ShortComplex.shortExact_of_iso e hSabs
  let S₀ : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk (K.iCycles p) (K.pOpcycles p)
      (by
        simpa [HomologicalComplex.iCycles, HomologicalComplex.pOpcycles] using
          ((ShortComplex.exact_iff_iCycles_pOpcycles_zero (S := K.sc p)).mp hp))
  let S₁ : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk (K.iCycles p) (K.toCycles p (p + 1))
      (by
        rw [← cancel_mono (K.iCycles (p + 1)), Category.assoc,
          HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d, zero_comp])
  let φ : S₀ ⟶ S₁ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.opcyclesToCycles p (p + 1)
      comm₁₂ := by simp [S₀, S₁]
      comm₂₃ := by
        dsimp [S₀, S₁]
        rw [Category.id_comp]
        exact (HomologicalComplex.pOpcycles_opcyclesToCycles (K := K) p (p + 1)).symm }
  have hexact₁ : S₁.Exact := by
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hbase_short.exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · simpa [S₁] using hexact₁
  · dsimp
    infer_instance
  · dsimp
    rw [← HomologicalComplex.pOpcycles_opcyclesToCycles (K := K) p (p + 1)]
    infer_instance

/--
%%handwave
name:
  The augmented cycles short sequence
statement:
  If \(F\to K^0\to K^1\) is exact, the first map is a monomorphism, and the
  cochain complex is exact in degree \(1\), then
  \(0\to F\to K^0\to Z^1\to0\) is short exact.
proof:
  Replace the target \(K^1\) in the given exact sequence by the kernel
  \(Z^1\subset K^1\).  Exactness is transported along the monomorphism
  \(Z^1\to K^1\), while exactness in degree \(1\) makes
  \(K^0\to Z^1\) an epimorphism.
tags:
  milestone
-/
theorem cochain_augmented_cycles_shortExact_of_exactAt_one
    [HasSheafify J AddCommGrpCat.{w}]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_one : K.ExactAt 1) :
    (ShortComplex.mk ε (K.toCycles 0 1)
      (by
        rw [← cancel_mono (K.iCycles 1), Category.assoc,
          HomologicalComplex.toCycles_i, hε, zero_comp])).ShortExact := by
  have hepi_bridge : Epi (K.opcyclesToCycles 0 1) :=
    cochain_epi_opcyclesToCycles_of_exactAt_succ (J := J) K 0 hexact_one
  haveI : Epi (K.opcyclesToCycles 0 1) := hepi_bridge
  let S₁ : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk ε (K.toCycles 0 1)
      (by
        rw [← cancel_mono (K.iCycles 1), Category.assoc,
          HomologicalComplex.toCycles_i, hε, zero_comp])
  let S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    { f := ε, g := K.d 0 1, zero := hε }
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles 1
      comm₁₂ := by simp [S₁, S₂]
      comm₂₃ := by
        dsimp [S₁, S₂]
        rw [Category.id_comp]
        exact (HomologicalComplex.toCycles_i (K := K) 0 1).symm }
  have hexact₁ : S₁.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hexact_zero
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · simpa [S₁] using hexact₁
  · exact hmono_ε
  · dsimp
    rw [← HomologicalComplex.pOpcycles_opcyclesToCycles (K := K) 0 1]
    infer_instance

/--
%%handwave
name:
  The map into cycles is natural
statement:
  An endomorphism of a cochain complex carries the differential-induced map
  into cycles to the corresponding map on cycles.
proof:
  Compose both sides with the inclusion of cycles into the next term.  The
  defining property of the map into cycles rewrites both composites as the
  two sides of the chain-map square.
-/
theorem cochain_toCycles_cyclesMap
    [HasSheafify J AddCommGrpCat.{w}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (φ : K ⟶ K) (n : ℕ) :
    K.toCycles n (n + 1) ≫ HomologicalComplex.cyclesMap φ (n + 1) =
      φ.f n ≫ K.toCycles n (n + 1) := by
  apply (cancel_mono (K.iCycles (n + 1))).1
  calc
    (K.toCycles n (n + 1) ≫ HomologicalComplex.cyclesMap φ (n + 1)) ≫
          K.iCycles (n + 1)
        = K.toCycles n (n + 1) ≫
            (HomologicalComplex.cyclesMap φ (n + 1) ≫ K.iCycles (n + 1)) := by
            rw [Category.assoc]
    _ = K.toCycles n (n + 1) ≫ (K.iCycles (n + 1) ≫ φ.f (n + 1)) := by
            rw [HomologicalComplex.cyclesMap_i]
    _ = (K.toCycles n (n + 1) ≫ K.iCycles (n + 1)) ≫ φ.f (n + 1) := by
            rw [Category.assoc]
    _ = K.d n (n + 1) ≫ φ.f (n + 1) := by
            rw [HomologicalComplex.toCycles_i]
    _ = φ.f n ≫ K.d n (n + 1) := by
            exact (HomologicalComplex.Hom.comm φ n (n + 1)).symm
    _ = φ.f n ≫ (K.toCycles n (n + 1) ≫ K.iCycles (n + 1)) := by
            rw [HomologicalComplex.toCycles_i]
    _ = (φ.f n ≫ K.toCycles n (n + 1)) ≫ K.iCycles (n + 1) := by
            rw [Category.assoc]

/--
%%handwave
name:
  Dimension shifting from the augmented term
statement:
  For an augmented acyclic resolution \(F\to K^\bullet\), the short exact
  sequence \(0\to F\to K^0\to Z^1\to0\) identifies \(H^q(Z^1)\) with
  \(H^{q+1}(F)\) for every \(q>0\).
proof:
  Apply the connecting-isomorphism lemma to the augmented cycles short exact
  sequence.  The middle term is \(K^0\), which is acyclic in positive
  degrees by hypothesis.
tags:
  milestone
-/
noncomputable def cochain_augmented_dimensionShift_addEquiv
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_one : K.ExactAt 1)
    (hacyclic₀ : ∀ q : ℕ, 0 < q → Subsingleton ((K.X 0).H q))
    (q : ℕ) (hq : 0 < q) :
    (K.cycles 1).H q ≃+ F.H (q + 1) := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk ε (K.toCycles 0 1)
      (by
        rw [← cancel_mono (K.iCycles 1), Category.assoc,
          HomologicalComplex.toCycles_i, hε, zero_comp])
  have hS : S.ShortExact :=
    cochain_augmented_cycles_shortExact_of_exactAt_one
      (J := J) F K ε hε hexact_zero hmono_ε hexact_one
  exact
    sheafCohomology_connecting_addEquiv_of_middle_acyclic_pos
      (J := J) hS (by intro r hr; exact hacyclic₀ r hr) q hq

/--
%%handwave
name:
  Dimension shifting from the augmented term is natural
statement:
  The dimension-shifting isomorphism attached to
  \(0\to F\to K^0\to Z^1\to0\) commutes with endomorphisms of the augmented
  resolution.
proof:
  The endomorphisms of \(F\), \(K^0\), and \(Z^1\) form an endomorphism of
  the short exact sequence.  Apply naturality of the connecting isomorphism.
-/
theorem cochain_augmented_dimensionShift_addEquiv_natural_with_map
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_one : K.ExactAt 1)
    (hacyclic₀ : ∀ q : ℕ, 0 < q → Subsingleton ((K.X 0).H q))
    (φF : F ⟶ F) (φK : K ⟶ K)
    (hε_map : ε ≫ φK.f 0 = φF ≫ ε)
    (q : ℕ) (hq : 0 < q)
    (x : (K.cycles 1).H q) :
    (cochain_augmented_dimensionShift_addEquiv
      (J := J) F K ε hε hexact_zero hmono_ε hexact_one hacyclic₀ q hq)
        (((functorH J q).map
          (HomologicalComplex.cyclesMap φK 1)) x) =
      ((functorH J (q + 1)).map φF)
        ((cochain_augmented_dimensionShift_addEquiv
          (J := J) F K ε hε hexact_zero hmono_ε hexact_one hacyclic₀ q hq) x) := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk ε (K.toCycles 0 1)
      (by
        rw [← cancel_mono (K.iCycles 1), Category.assoc,
          HomologicalComplex.toCycles_i, hε, zero_comp])
  have hS : S.ShortExact :=
    cochain_augmented_cycles_shortExact_of_exactAt_one
      (J := J) F K ε hε hexact_zero hmono_ε hexact_one
  let φS : S ⟶ S :=
    ShortComplex.homMk φF (φK.f 0) (HomologicalComplex.cyclesMap φK 1)
      (by simpa [S] using hε_map.symm)
      (by
        simpa [S] using
          (cochain_toCycles_cyclesMap (J := J) K φK 0).symm)
  simpa [cochain_augmented_dimensionShift_addEquiv, S, φS] using
    sheafCohomology_connecting_addEquiv_of_middle_acyclic_pos_natural_self
      (J := J) hS (by intro r hr; exact hacyclic₀ r hr) φS q hq x

/--
%%handwave
name:
  Dimension shifting along the cycles
statement:
  For a cochain complex of acyclic sheaves exact in degrees \(p\) and
  \(p+1\), the short exact sequence
  \(0\to Z^p\to K^p\to Z^{p+1}\to0\) identifies \(H^q(Z^{p+1})\) with
  \(H^{q+1}(Z^p)\) for every \(q>0\).
proof:
  Apply the connecting-isomorphism lemma to the cycles-to-next-cycles short
  exact sequence.  The middle term is \(K^p\), which is acyclic in positive
  degrees by hypothesis.
tags:
  milestone
-/
noncomputable def cochain_cycles_dimensionShift_addEquiv
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (p : ℕ) (hp : K.ExactAt p) (hsucc : K.ExactAt (p + 1))
    (hacyclic_p : ∀ q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    (q : ℕ) (hq : 0 < q) :
    (K.cycles (p + 1)).H q ≃+ (K.cycles p).H (q + 1) := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk (K.iCycles p) (K.toCycles p (p + 1))
      (by
        rw [← cancel_mono (K.iCycles (p + 1)), Category.assoc,
          HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d, zero_comp])
  have hS : S.ShortExact :=
    cochain_cycles_shortExact_of_exactAt_and_succ
      (J := J) K p hp hsucc
  exact
    sheafCohomology_connecting_addEquiv_of_middle_acyclic_pos
      (J := J) hS (by intro r hr; exact hacyclic_p r hr) q hq

/--
%%handwave
name:
  Dimension shifting along cycles is natural
statement:
  The dimension-shifting isomorphism attached to
  \(0\to Z^p\to K^p\to Z^{p+1}\to0\) commutes with endomorphisms of the
  cochain complex.
proof:
  The maps on \(Z^p\), \(K^p\), and \(Z^{p+1}\) form an endomorphism of the
  short exact sequence.  Apply naturality of the connecting isomorphism.
-/
theorem cochain_cycles_dimensionShift_addEquiv_natural_with_map
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (p : ℕ) (hp : K.ExactAt p) (hsucc : K.ExactAt (p + 1))
    (hacyclic_p : ∀ q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    (φK : K ⟶ K)
    (q : ℕ) (hq : 0 < q)
    (x : (K.cycles (p + 1)).H q) :
    (cochain_cycles_dimensionShift_addEquiv
      (J := J) K p hp hsucc hacyclic_p q hq)
        (((functorH J q).map
          (HomologicalComplex.cyclesMap φK (p + 1))) x) =
      ((functorH J (q + 1)).map
        (HomologicalComplex.cyclesMap φK p))
        ((cochain_cycles_dimensionShift_addEquiv
          (J := J) K p hp hsucc hacyclic_p q hq) x) := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk (K.iCycles p) (K.toCycles p (p + 1))
      (by
        rw [← cancel_mono (K.iCycles (p + 1)), Category.assoc,
          HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d, zero_comp])
  have hS : S.ShortExact :=
    cochain_cycles_shortExact_of_exactAt_and_succ
      (J := J) K p hp hsucc
  let φS : S ⟶ S :=
    ShortComplex.homMk
      (HomologicalComplex.cyclesMap φK p) (φK.f p)
      (HomologicalComplex.cyclesMap φK (p + 1))
      (by simp [S])
      (by
        simpa [S] using
          (cochain_toCycles_cyclesMap (J := J) K φK p).symm)
  simpa [cochain_cycles_dimensionShift_addEquiv, S, φS] using
    sheafCohomology_connecting_addEquiv_of_middle_acyclic_pos_natural_self
      (J := J) hS (by intro r hr; exact hacyclic_p r hr) φS q hq x

/--
%%handwave
name:
  Iterated dimension shifting from cycles to the augmentation
statement:
  For an augmented acyclic resolution, the cycles in degree \(m+1\) satisfy
  \(H^q(Z^{m+1})\simeq H^{q+m+1}(F)\) for every \(q>0\).
proof:
  Induct on \(m\).  The base case is the dimension shift for
  \(0\to F\to K^0\to Z^1\to0\).  The induction step first shifts across
  \(0\to Z^{m+1}\to K^{m+1}\to Z^{m+2}\to0\), then applies the induction
  hypothesis.
-/
noncomputable def cochain_cycles_to_augmented_dimensionShift_addEquiv
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_pos : ∀ n : ℕ, K.ExactAt (n + 1))
    (hacyclic : ∀ p q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    (m q : ℕ) (hq : 0 < q) :
    (K.cycles (m + 1)).H q ≃+ F.H (q + (m + 1)) := by
  induction m generalizing q with
  | zero =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        cochain_augmented_dimensionShift_addEquiv
          (J := J) F K ε hε hexact_zero hmono_ε (hexact_pos 0)
          (fun r hr => hacyclic 0 r hr) q hq
  | succ m ih =>
      let e₁ :
          (K.cycles ((m + 1) + 1)).H q ≃+
            (K.cycles (m + 1)).H (q + 1) :=
        cochain_cycles_dimensionShift_addEquiv
          (J := J) K (m + 1) (hexact_pos m) (hexact_pos (m + 1))
          (fun r hr => hacyclic (m + 1) r hr) q hq
      let e₂ : (K.cycles (m + 1)).H (q + 1) ≃+ F.H ((q + 1) + (m + 1)) :=
        ih (q + 1) (Nat.succ_pos q)
      have hidx : (q + 1) + (m + 1) = q + ((m + 1) + 1) := by omega
      let ecast : F.H ((q + 1) + (m + 1)) ≃+ F.H (q + ((m + 1) + 1)) :=
        AddEquiv.cast (M := fun k : ℕ => F.H k) hidx
      exact e₁.trans (e₂.trans ecast)

/--
%%handwave
name:
  Iterated dimension shifting is natural
statement:
  The dimension-shifting isomorphism from \(H^q(Z^{m+1})\) to
  \(H^{q+m+1}(F)\) may be chosen to commute with any family of endomorphisms
  of the augmented resolution.
proof:
  Induct on \(m\).  The base case is naturality of the connecting
  isomorphism for \(0\to F\to K^0\to Z^1\to0\).  The induction step combines
  naturality of the connecting isomorphism for
  \(0\to Z^{m+1}\to K^{m+1}\to Z^{m+2}\to0\) with the induction hypothesis.
-/
theorem cochain_cycles_to_augmented_dimensionShift_addEquiv_natural_with_family_map
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_pos : ∀ n : ℕ, K.ExactAt (n + 1))
    (hacyclic : ∀ p q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    {ι : Type*}
    (φF : ι → (F ⟶ F)) (φK : ι → (K ⟶ K))
    (hε_map : ∀ i, ε ≫ (φK i).f 0 = φF i ≫ ε)
    (m q : ℕ) (hq : 0 < q)
    (i : ι) (x : (K.cycles (m + 1)).H q) :
    (cochain_cycles_to_augmented_dimensionShift_addEquiv
      (J := J) F K ε hε hexact_zero hmono_ε hexact_pos hacyclic m q hq)
        (((functorH J q).map
          (HomologicalComplex.cyclesMap (φK i) (m + 1))) x) =
      ((functorH J (q + (m + 1))).map (φF i))
        ((cochain_cycles_to_augmented_dimensionShift_addEquiv
          (J := J) F K ε hε hexact_zero hmono_ε hexact_pos hacyclic m q hq) x) := by
  induction m generalizing q with
  | zero =>
      simpa [cochain_cycles_to_augmented_dimensionShift_addEquiv,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        cochain_augmented_dimensionShift_addEquiv_natural_with_map
          (J := J) F K ε hε hexact_zero hmono_ε (hexact_pos 0)
          (fun r hr => hacyclic 0 r hr) (φF i) (φK i) (hε_map i) q hq x
  | succ m ih =>
      let e₁ :
          (K.cycles ((m + 1) + 1)).H q ≃+
            (K.cycles (m + 1)).H (q + 1) :=
        cochain_cycles_dimensionShift_addEquiv
          (J := J) K (m + 1) (hexact_pos m) (hexact_pos (m + 1))
          (fun r hr => hacyclic (m + 1) r hr) q hq
      let e₂ : (K.cycles (m + 1)).H (q + 1) ≃+ F.H ((q + 1) + (m + 1)) :=
        cochain_cycles_to_augmented_dimensionShift_addEquiv
          (J := J) F K ε hε hexact_zero hmono_ε hexact_pos hacyclic
          m (q + 1) (Nat.succ_pos q)
      have hidx : (q + 1) + (m + 1) = q + ((m + 1) + 1) := by omega
      let ecast : F.H ((q + 1) + (m + 1)) ≃+ F.H (q + ((m + 1) + 1)) :=
        AddEquiv.cast (M := fun k : ℕ => F.H k) hidx
      have h₁ :
          e₁ (((functorH J q).map
              (HomologicalComplex.cyclesMap (φK i) ((m + 1) + 1))) x) =
            ((functorH J (q + 1)).map
              (HomologicalComplex.cyclesMap (φK i) (m + 1))) (e₁ x) :=
        cochain_cycles_dimensionShift_addEquiv_natural_with_map
          (J := J) K (m + 1) (hexact_pos m) (hexact_pos (m + 1))
          (fun r hr => hacyclic (m + 1) r hr) (φK i) q hq x
      have h₂ :
          e₂ (((functorH J (q + 1)).map
              (HomologicalComplex.cyclesMap (φK i) (m + 1))) (e₁ x)) =
            ((functorH J ((q + 1) + (m + 1))).map (φF i)) (e₂ (e₁ x)) := by
        simpa [e₂] using ih (q + 1) (Nat.succ_pos q) (e₁ x)
      have hcast :
          ecast (((functorH J ((q + 1) + (m + 1))).map (φF i))
              (e₂ (e₁ x))) =
            ((functorH J (q + ((m + 1) + 1))).map (φF i))
              (ecast (e₂ (e₁ x))) := by
        simpa [ecast] using
          sheafCohomology_cast_map (J := J) (φF i) hidx (e₂ (e₁ x))
      have hmain :
          ecast (e₂ (e₁ (((functorH J q).map
              (HomologicalComplex.cyclesMap (φK i) ((m + 1) + 1))) x))) =
            ((functorH J (q + ((m + 1) + 1))).map (φF i))
              (ecast (e₂ (e₁ x))) :=
        (congrArg ecast ((congrArg e₂ h₁).trans h₂)).trans hcast
      simpa [cochain_cycles_to_augmented_dimensionShift_addEquiv,
        e₁, e₂, ecast, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmain

/--
%%handwave
name:
  The low-degree edge for an acyclic middle term
statement:
  For a short exact sequence \(0\to A\to B\to C\to0\) of sheaves of abelian
  groups, if \(H^1(B)=0\), then the cokernel of
  \(\Gamma(B)\to\Gamma(C)\) is additively isomorphic to \(H^1(A)\).
proof:
  Use the low-degree part of the long exact Ext sequence:
  \(H^0(B)\to H^0(C)\to H^1(A)\to H^1(B)\).  The identification
  \(H^0=\Gamma\) rewrites the first map as the map on global sections.  Since
  \(H^1(B)\) vanishes, exactness says that the connecting map induces an
  isomorphism from the cokernel of \(\Gamma(B)\to\Gamma(C)\) onto
  \(H^1(A)\).
-/
theorem nonempty_globalSections_cokernel_addEquiv_sheafCohomology_one_of_shortExact_middle_acyclic
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact)
    (hacyclic₂_one : Subsingleton (S.X₂.H 1)) :
    Nonempty (↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map S.g)) ≃+ S.X₁.H 1) := by
  let Γ := Sheaf.Γ J AddCommGrpCat.{w}
  let Cℤ : Sheaf J AddCommGrpCat.{w} :=
    (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  let e₂ : S.X₂.H 0 ≃+ Γ.obj S.X₂ :=
    cohomology_zero_addEquiv_globalSections (J := J) S.X₂
  let e₃ : S.X₃.H 0 ≃+ Γ.obj S.X₃ :=
    cohomology_zero_addEquiv_globalSections (J := J) S.X₃
  let δ : S.X₃.H 0 →+ S.X₁.H 1 :=
    hS.extClass.postcomp Cℤ (show 0 + 1 = 1 by rfl)
  let boundary : Γ.obj S.X₃ →+ S.X₁.H 1 :=
    δ.comp e₃.symm.toAddMonoidHom
  have hboundary_g : ∀ x : Γ.obj S.X₂, boundary (Γ.map S.g x) = 0 := by
    intro x
    change δ (e₃.symm (Γ.map S.g x)) = 0
    rw [show e₃.symm (Γ.map S.g x) =
        ((functorH J 0).map S.g) (e₂.symm x) by
      simpa [Γ, e₂, e₃] using
        cohomology_zero_addEquiv_globalSections_symm_natural (J := J) S.g x]
    change
      ((e₂.symm x).comp (Abelian.Ext.mk₀ S.g) (add_zero 0)).comp
        hS.extClass (show 0 + 1 = 1 by rfl) = 0
    simp
  let edgeQuotient :
      (Γ.obj S.X₃ ⧸ AddMonoidHom.range (Γ.map S.g).hom) →+ S.X₁.H 1 :=
    QuotientAddGroup.lift _ boundary (by
      rintro _ ⟨x, rfl⟩
      exact hboundary_g x)
  have hedge_surjective : Function.Surjective edgeQuotient := by
    intro y
    haveI hmiddle_one : Subsingleton (Abelian.Ext Cℤ S.X₂ 1) := by
      dsimp [Cℤ, Sheaf.H] at hacyclic₂_one ⊢
      exact hacyclic₂_one
    have hy : y.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := by
      exact Subsingleton.elim _ _
    obtain ⟨x₃, hx₃⟩ :=
      Abelian.Ext.covariant_sequence_exact₁ (X := Cℤ) hS y hy
        (hn₀ := (show 0 + 1 = 1 by rfl))
    refine ⟨QuotientAddGroup.mk' _ (e₃ x₃), ?_⟩
    change δ (e₃.symm (e₃ x₃)) = y
    simpa [δ] using hx₃
  have hedge_injective : Function.Injective edgeQuotient := by
    intro q₁ q₂ hq
    induction q₁ using QuotientAddGroup.induction_on with
    | H y₁ =>
        induction q₂ using QuotientAddGroup.induction_on with
        | H y₂ =>
            rw [QuotientAddGroup.eq_iff_sub_mem]
            have hboundary_sub : boundary (y₁ - y₂) = 0 := by
              simpa [edgeQuotient, map_sub] using sub_eq_zero.mpr hq
            let x₃ : S.X₃.H 0 := e₃.symm (y₁ - y₂)
            have hx₃ : x₃.comp hS.extClass (show 0 + 1 = 1 by rfl) = 0 := by
              change δ (e₃.symm (y₁ - y₂)) = 0
              simpa [boundary] using hboundary_sub
            obtain ⟨x₂, hx₂⟩ :=
              Abelian.Ext.covariant_sequence_exact₃ (X := Cℤ) hS x₃
                (hn₁ := (show 0 + 1 = 1 by rfl)) hx₃
            refine ⟨e₂ x₂, ?_⟩
            apply e₃.symm.injective
            rw [show e₃.symm (Γ.map S.g (e₂ x₂)) =
                ((functorH J 0).map S.g) (e₂.symm (e₂ x₂)) by
              simpa [Γ, e₂, e₃] using
                cohomology_zero_addEquiv_globalSections_symm_natural (J := J) S.g (e₂ x₂)]
            simpa [x₃] using hx₂
  let edgeQuotientEquiv :
      (Γ.obj S.X₃ ⧸ AddMonoidHom.range (Γ.map S.g).hom) ≃+ S.X₁.H 1 :=
    AddEquiv.ofBijective edgeQuotient ⟨hedge_injective, hedge_surjective⟩
  exact
    ⟨(AddCommGrpCat.cokernelIsoQuotient (Γ.map S.g)).addCommGroupIsoToAddEquiv.trans
      edgeQuotientEquiv⟩

/--
The endomorphism induced on the cokernel of \(\Gamma(S_2)\to\Gamma(S_3)\)
by an endomorphism of a short complex \(S\).
-/
noncomputable abbrev globalSections_shortComplex_cokernelEnd
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (φ : S ⟶ S) :
    cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map S.g) ⟶
      cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map S.g) := by
  let Γ := Sheaf.Γ J AddCommGrpCat.{w}
  exact
    cokernel.map (Γ.map S.g) (Γ.map S.g)
      (Γ.map φ.τ₂) (Γ.map φ.τ₃) (by
        rw [← Γ.map_comp, ← Γ.map_comp]
        congr 1
        exact φ.comm₂₃.symm)

/--
%%handwave
name:
  The low-degree edge for an acyclic middle term is natural
statement:
  For a short exact sequence \(0\to A\to B\to C\to0\) of sheaves with
  \(H^1(B)=0\), the edge isomorphism from the cokernel of
  \(\Gamma(B)\to\Gamma(C)\) to \(H^1(A)\) may be chosen to commute with any
  family of endomorphisms of the short exact sequence.
proof:
  Use the explicit edge map induced by the connecting morphism
  \(H^0(C)\to H^1(A)\).  Naturality of the connecting morphism and of the
  identification \(H^0=\Gamma\) shows that it descends to a natural map on
  cokernels, and the exactness proof of bijectivity is preserved by these
  endomorphisms.
-/
theorem exists_globalSections_cokernel_addEquiv_sheafCohomology_one_of_shortExact_middle_acyclic_natural_with_family_map
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact)
    (hacyclic₂_one : Subsingleton (S.X₂.H 1))
    {ι : Type*} (φS : ι → (S ⟶ S)) :
    ∃ e : ↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map S.g)) ≃+ S.X₁.H 1,
      ∀ (i : ι)
        (x : ↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map S.g))),
        e ((globalSections_shortComplex_cokernelEnd (J := J) (φS i)) x) =
          ((functorH J 1).map (φS i).τ₁) (e x) := by
  let Γ := Sheaf.Γ J AddCommGrpCat.{w}
  let Cℤ : Sheaf J AddCommGrpCat.{w} :=
    (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  let e₂ : S.X₂.H 0 ≃+ Γ.obj S.X₂ :=
    cohomology_zero_addEquiv_globalSections (J := J) S.X₂
  let e₃ : S.X₃.H 0 ≃+ Γ.obj S.X₃ :=
    cohomology_zero_addEquiv_globalSections (J := J) S.X₃
  let δ : S.X₃.H 0 →+ S.X₁.H 1 :=
    hS.extClass.postcomp Cℤ (show 0 + 1 = 1 by rfl)
  let boundary : Γ.obj S.X₃ →+ S.X₁.H 1 :=
    δ.comp e₃.symm.toAddMonoidHom
  have hboundary_g : ∀ x : Γ.obj S.X₂, boundary (Γ.map S.g x) = 0 := by
    intro x
    change δ (e₃.symm (Γ.map S.g x)) = 0
    rw [show e₃.symm (Γ.map S.g x) =
        ((functorH J 0).map S.g) (e₂.symm x) by
      simpa [Γ, e₂, e₃] using
        cohomology_zero_addEquiv_globalSections_symm_natural (J := J) S.g x]
    change
      ((e₂.symm x).comp (Abelian.Ext.mk₀ S.g) (add_zero 0)).comp
        hS.extClass (show 0 + 1 = 1 by rfl) = 0
    simp
  let edgeQuotient :
      (Γ.obj S.X₃ ⧸ AddMonoidHom.range (Γ.map S.g).hom) →+ S.X₁.H 1 :=
    QuotientAddGroup.lift _ boundary (by
      rintro _ ⟨x, rfl⟩
      exact hboundary_g x)
  have hedge_surjective : Function.Surjective edgeQuotient := by
    intro y
    haveI hmiddle_one : Subsingleton (Abelian.Ext Cℤ S.X₂ 1) := by
      dsimp [Cℤ, Sheaf.H] at hacyclic₂_one ⊢
      exact hacyclic₂_one
    have hy : y.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := by
      exact Subsingleton.elim _ _
    obtain ⟨x₃, hx₃⟩ :=
      Abelian.Ext.covariant_sequence_exact₁ (X := Cℤ) hS y hy
        (hn₀ := (show 0 + 1 = 1 by rfl))
    refine ⟨QuotientAddGroup.mk' _ (e₃ x₃), ?_⟩
    change δ (e₃.symm (e₃ x₃)) = y
    simpa [δ] using hx₃
  have hedge_injective : Function.Injective edgeQuotient := by
    intro q₁ q₂ hq
    induction q₁ using QuotientAddGroup.induction_on with
    | H y₁ =>
        induction q₂ using QuotientAddGroup.induction_on with
        | H y₂ =>
            rw [QuotientAddGroup.eq_iff_sub_mem]
            have hboundary_sub : boundary (y₁ - y₂) = 0 := by
              simpa [edgeQuotient, map_sub] using sub_eq_zero.mpr hq
            let x₃ : S.X₃.H 0 := e₃.symm (y₁ - y₂)
            have hx₃ : x₃.comp hS.extClass (show 0 + 1 = 1 by rfl) = 0 := by
              change δ (e₃.symm (y₁ - y₂)) = 0
              simpa [boundary] using hboundary_sub
            obtain ⟨x₂, hx₂⟩ :=
              Abelian.Ext.covariant_sequence_exact₃ (X := Cℤ) hS x₃
                (hn₁ := (show 0 + 1 = 1 by rfl)) hx₃
            refine ⟨e₂ x₂, ?_⟩
            apply e₃.symm.injective
            rw [show e₃.symm (Γ.map S.g (e₂ x₂)) =
                ((functorH J 0).map S.g) (e₂.symm (e₂ x₂)) by
              simpa [Γ, e₂, e₃] using
                cohomology_zero_addEquiv_globalSections_symm_natural (J := J) S.g (e₂ x₂)]
            simpa [x₃] using hx₂
  let edgeQuotientEquiv :
      (Γ.obj S.X₃ ⧸ AddMonoidHom.range (Γ.map S.g).hom) ≃+ S.X₁.H 1 :=
    AddEquiv.ofBijective edgeQuotient ⟨hedge_injective, hedge_surjective⟩
  let cokerQuotientEquiv :
      ↥(cokernel (Γ.map S.g)) ≃+
        (Γ.obj S.X₃ ⧸ AddMonoidHom.range (Γ.map S.g).hom) :=
    (AddCommGrpCat.cokernelIsoQuotient (Γ.map S.g)).addCommGroupIsoToAddEquiv
  let eFinal : ↥(cokernel (Γ.map S.g)) ≃+ S.X₁.H 1 :=
    cokerQuotientEquiv.trans edgeQuotientEquiv
  have hboundary_nat :
      ∀ (i : ι) (y : Γ.obj S.X₃),
        boundary (Γ.map (φS i).τ₃ y) =
          ((functorH J 1).map (φS i).τ₁) (boundary y) := by
    intro i y
    change δ (e₃.symm (Γ.map (φS i).τ₃ y)) =
      ((functorH J 1).map (φS i).τ₁) (δ (e₃.symm y))
    rw [show e₃.symm (Γ.map (φS i).τ₃ y) =
        ((functorH J 0).map (φS i).τ₃) (e₃.symm y) by
      simpa [Γ, e₃] using
        cohomology_zero_addEquiv_globalSections_symm_natural
          (J := J) (φS i).τ₃ y]
    change
      (((e₃.symm y).comp (Abelian.Ext.mk₀ (φS i).τ₃) (add_zero 0)).comp
          hS.extClass (show 0 + 1 = 1 by rfl)) =
        ((e₃.symm y).comp hS.extClass (show 0 + 1 = 1 by rfl)).comp
          (Abelian.Ext.mk₀ (φS i).τ₁) (add_zero 1)
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
    rw [← hS.extClass_naturality hS (φS i)]
  have hπ_shortEnd :
      ∀ i : ι,
        cokernel.π (Γ.map S.g) ≫
            globalSections_shortComplex_cokernelEnd (J := J) (φS i) =
          Γ.map (φS i).τ₃ ≫ cokernel.π (Γ.map S.g) := by
    intro i
    dsimp [globalSections_shortComplex_cokernelEnd]
    rw [cokernel.π_desc]
  have hcokerQuotient_apply :
      ∀ y : Γ.obj S.X₃,
        cokerQuotientEquiv ((cokernel.π (Γ.map S.g)) y) =
          QuotientAddGroup.mk' (AddMonoidHom.range (Γ.map S.g).hom) y := by
    intro y
    change ((AddCommGrpCat.cokernelIsoQuotient (Γ.map S.g)).hom
        ((cokernel.π (Γ.map S.g)) y)) =
      QuotientAddGroup.mk' (AddMonoidHom.range (Γ.map S.g).hom) y
    dsimp [AddCommGrpCat.cokernelIsoQuotient]
    exact cokernel.π_desc_apply (Γ.map S.g)
      (AddCommGrpCat.ofHom (QuotientAddGroup.mk' _)) _ y
  refine ⟨eFinal, ?_⟩
  intro i x
  rcases (AddCommGrpCat.epi_iff_surjective (cokernel.π (Γ.map S.g))).mp
      inferInstance x with ⟨y, rfl⟩
  have hleft :
      eFinal
          (globalSections_shortComplex_cokernelEnd (J := J) (φS i)
            ((cokernel.π (Γ.map S.g)) y)) =
        boundary (Γ.map (φS i).τ₃ y) := by
    have hπ :
        globalSections_shortComplex_cokernelEnd (J := J) (φS i)
            ((cokernel.π (Γ.map S.g)) y) =
          (cokernel.π (Γ.map S.g)) (Γ.map (φS i).τ₃ y) := by
      change ((cokernel.π (Γ.map S.g) ≫
          globalSections_shortComplex_cokernelEnd (J := J) (φS i)) y) =
        ((Γ.map (φS i).τ₃ ≫ cokernel.π (Γ.map S.g)) y)
      rw [hπ_shortEnd i]
    rw [hπ]
    change edgeQuotientEquiv
        (cokerQuotientEquiv ((cokernel.π (Γ.map S.g))
          (Γ.map (φS i).τ₃ y))) =
      boundary (Γ.map (φS i).τ₃ y)
    rw [hcokerQuotient_apply]
    simp [edgeQuotientEquiv, edgeQuotient]
  have hright :
      eFinal ((cokernel.π (Γ.map S.g)) y) = boundary y := by
    change edgeQuotientEquiv
        (cokerQuotientEquiv ((cokernel.π (Γ.map S.g)) y)) = boundary y
    rw [hcokerQuotient_apply]
    simp [edgeQuotientEquiv, edgeQuotient]
  calc
    eFinal
        (globalSections_shortComplex_cokernelEnd (J := J) (φS i)
          ((cokernel.π (Γ.map S.g)) y))
        = boundary (Γ.map (φS i).τ₃ y) := hleft
    _ = ((functorH J 1).map (φS i).τ₁) (boundary y) :=
        hboundary_nat i y
    _ = ((functorH J 1).map (φS i).τ₁)
        (eFinal ((cokernel.π (Γ.map S.g)) y)) := by
        rw [hright]

/--
%%handwave
name:
  Global sections identify cycles
statement:
  For a cochain complex of sheaves, global sections carry the cycles in degree
  \(n+1\) to the cycles of the global-section complex, compatibly with the
  incoming differential from degree \(n\).
proof:
  The cycles are a kernel of the next differential.  The global-section
  functor is a right adjoint, hence preserves kernels.  The induced
  isomorphism of kernels is characterized by the displayed compatibility with
  the incoming differential.
-/
theorem exists_globalSections_cycles_iso_compatible_toCycles
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (n : ℕ) :
    ∃ e :
        (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).cycles (n + 1) ≅
          (Sheaf.Γ J AddCommGrpCat.{w}).obj (K.cycles (n + 1)),
      (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).toCycles n (n + 1) ≫ e.hom =
        (Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles n (n + 1)) := by
  let Γ := Sheaf.Γ J AddCommGrpCat.{w}
  let ΓK := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let j := n + 1
  let k := n + 2
  let mappedCyclesFork : KernelFork (ΓK.d j k) :=
    KernelFork.ofι (Γ.map (K.iCycles j)) (by
      simpa [Γ, ΓK, j, k] using
        (by
          rw [← Γ.map_comp, HomologicalComplex.iCycles_d (K := K) j k,
            Functor.map_zero] :
          Γ.map (K.iCycles j) ≫ Γ.map (K.d j k) = 0))
  have hmappedCyclesFork : IsLimit mappedCyclesFork := by
    have hpres : PreservesLimit (parallelPair (K.d j k) 0) Γ := by
      infer_instance
    simpa [mappedCyclesFork, Γ, ΓK, j, k] using
      (isLimitForkMapOfIsLimit' Γ
        (HomologicalComplex.iCycles_d (K := K) j k)
        (K.cyclesIsKernel j k (by simp [j, k])))
  let e : ΓK.cycles j ≅ Γ.obj (K.cycles j) :=
    IsLimit.conePointUniqueUpToIso
      (ΓK.cyclesIsKernel j k (by simp [j, k]))
      hmappedCyclesFork
  have he_iCycles : e.hom ≫ Γ.map (K.iCycles j) = ΓK.iCycles j := by
    simpa [e, mappedCyclesFork, ΓK] using
      (IsLimit.conePointUniqueUpToIso_hom_comp
        (ΓK.cyclesIsKernel j k (by simp [j, k]))
        hmappedCyclesFork WalkingParallelPair.zero)
  haveI : Mono (Γ.map (K.iCycles j)) := Fork.IsLimit.mono hmappedCyclesFork
  refine ⟨e, ?_⟩
  apply (cancel_mono (Γ.map (K.iCycles j))).1
  rw [Category.assoc, he_iCycles]
  change ΓK.toCycles n (n + 1) ≫ ΓK.iCycles (n + 1) =
    Γ.map (K.toCycles n (n + 1)) ≫ Γ.map (K.iCycles (n + 1))
  rw [HomologicalComplex.toCycles_i (K := ΓK) n (n + 1)]
  change Γ.map (K.d n (n + 1)) =
    Γ.map (K.toCycles n (n + 1)) ≫ Γ.map (K.iCycles (n + 1))
  rw [← Functor.map_comp]
  congr 1
  exact (HomologicalComplex.toCycles_i (K := K) n (n + 1)).symm

/--
%%handwave
name:
  Global sections identify cycles naturally
statement:
  The identification of the cycles of the global-section complex with the
  global sections of the cycle sheaf may be chosen compatibly with any family
  of endomorphisms of the complex.
proof:
  Construct the identification from the fact that global sections preserve
  kernels.  To prove naturality, compose the two candidate maps with the
  inclusion of cycles into the next term.  The two composites agree by
  functoriality of kernels, and the inclusion is monic.
-/
theorem exists_globalSections_cycles_iso_compatible_toCycles_natural_with_family_map
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    {ι : Type*} (φK : ι → (K ⟶ K))
    (n : ℕ) :
    ∃ e :
        (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).cycles (n + 1) ≅
          (Sheaf.Γ J AddCommGrpCat.{w}).obj (K.cycles (n + 1)),
      (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).toCycles n (n + 1) ≫ e.hom =
        (Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles n (n + 1)) ∧
      ∀ i : ι,
        HomologicalComplex.cyclesMap
            (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
              (ComplexShape.up ℕ)).map (φK i)) (n + 1) ≫ e.hom =
          e.hom ≫
            (Sheaf.Γ J AddCommGrpCat.{w}).map
              (HomologicalComplex.cyclesMap (φK i) (n + 1)) := by
  let Γ := Sheaf.Γ J AddCommGrpCat.{w}
  let ΓK := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let j := n + 1
  let k := n + 2
  let mappedCyclesFork : KernelFork (ΓK.d j k) :=
    KernelFork.ofι (Γ.map (K.iCycles j)) (by
      simpa [Γ, ΓK, j, k] using
        (by
          rw [← Γ.map_comp, HomologicalComplex.iCycles_d (K := K) j k,
            Functor.map_zero] :
          Γ.map (K.iCycles j) ≫ Γ.map (K.d j k) = 0))
  have hmappedCyclesFork : IsLimit mappedCyclesFork := by
    have hpres : PreservesLimit (parallelPair (K.d j k) 0) Γ := by
      infer_instance
    simpa [mappedCyclesFork, Γ, ΓK, j, k] using
      (isLimitForkMapOfIsLimit' Γ
        (HomologicalComplex.iCycles_d (K := K) j k)
        (K.cyclesIsKernel j k (by simp [j, k])))
  let e : ΓK.cycles j ≅ Γ.obj (K.cycles j) :=
    IsLimit.conePointUniqueUpToIso
      (ΓK.cyclesIsKernel j k (by simp [j, k]))
      hmappedCyclesFork
  have he_iCycles : e.hom ≫ Γ.map (K.iCycles j) = ΓK.iCycles j := by
    simpa [e, mappedCyclesFork, ΓK] using
      (IsLimit.conePointUniqueUpToIso_hom_comp
        (ΓK.cyclesIsKernel j k (by simp [j, k]))
        hmappedCyclesFork WalkingParallelPair.zero)
  haveI : Mono (Γ.map (K.iCycles j)) := Fork.IsLimit.mono hmappedCyclesFork
  have he_toCycles :
      ΓK.toCycles n (n + 1) ≫ e.hom =
        Γ.map (K.toCycles n (n + 1)) := by
    apply (cancel_mono (Γ.map (K.iCycles j))).1
    rw [Category.assoc, he_iCycles]
    change ΓK.toCycles n (n + 1) ≫ ΓK.iCycles (n + 1) =
      Γ.map (K.toCycles n (n + 1)) ≫ Γ.map (K.iCycles (n + 1))
    rw [HomologicalComplex.toCycles_i (K := ΓK) n (n + 1)]
    change Γ.map (K.d n (n + 1)) =
      Γ.map (K.toCycles n (n + 1)) ≫ Γ.map (K.iCycles (n + 1))
    rw [← Functor.map_comp]
    congr 1
    exact (HomologicalComplex.toCycles_i (K := K) n (n + 1)).symm
  refine ⟨e, he_toCycles, ?_⟩
  intro i
  apply (cancel_mono (Γ.map (K.iCycles j))).1
  rw [Category.assoc, he_iCycles]
  change HomologicalComplex.cyclesMap
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map (φK i)) j ≫
        ΓK.iCycles j =
    (e.hom ≫ Γ.map (HomologicalComplex.cyclesMap (φK i) j)) ≫
      Γ.map (K.iCycles j)
  rw [HomologicalComplex.cyclesMap_i]
  change ΓK.iCycles j ≫ Γ.map ((φK i).f j) =
    (e.hom ≫ Γ.map (HomologicalComplex.cyclesMap (φK i) j)) ≫ Γ.map (K.iCycles j)
  rw [← he_iCycles, Category.assoc, ← Functor.map_comp,
    HomologicalComplex.cyclesMap_i]
  exact
    (Category.assoc e.hom (Γ.map (K.iCycles j)) (Γ.map ((φK i).f j))).trans
      (congrArg (fun q => e.hom ≫ q)
        ((Functor.map_comp Γ (K.iCycles j) ((φK i).f j)).symm))

/--
The endomorphism induced on the cokernel of
\(\Gamma(K^n)\to\Gamma(Z^{n+1})\) by an endomorphism of \(K^\bullet\).
-/
noncomputable abbrev globalSections_toCycles_cokernelEnd
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (φ : K ⟶ K) (n : ℕ) :
    cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles n (n + 1))) ⟶
      cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles n (n + 1))) := by
  let Γ := Sheaf.Γ J AddCommGrpCat.{w}
  exact
    cokernel.map (Γ.map (K.toCycles n (n + 1))) (Γ.map (K.toCycles n (n + 1)))
      (Γ.map (φ.f n)) (Γ.map (HomologicalComplex.cyclesMap φ (n + 1))) (by
        rw [← Γ.map_comp, ← Γ.map_comp]
        congr 1
        exact cochain_toCycles_cyclesMap (J := J) K φ n)

/--
%%handwave
name:
  Global-section homology is a cokernel onto cycles
statement:
  For a cochain complex of sheaves \(K^\bullet\), the \((n+1)\)-st homology
  of the global-section complex is additively isomorphic to the cokernel of
  \(\Gamma(K^n)\to\Gamma(Z^{n+1})\).
proof:
  Global sections preserve kernels, so the cycles of
  \(\Gamma(K^\bullet)\) in degree \(n+1\) identify with
  \(\Gamma(Z^{n+1})\).  Homology in degree \(n+1\) is the cokernel of the
  previous differential into these cycles.
tags:
  milestone
-/
theorem nonempty_globalSections_homology_succ_addEquiv_cokernel_to_cycles
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (n : ℕ) :
    Nonempty
      (↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).homology (n + 1)) ≃+
        ↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles n (n + 1))))) := by
  let Γ := Sheaf.Γ J AddCommGrpCat.{w}
  let ΓK := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  obtain ⟨e, he⟩ :=
    exists_globalSections_cycles_iso_compatible_toCycles (J := J) (K := K) n
  let cokerCofork : CokernelCofork (ΓK.toCycles n (n + 1)) :=
    CokernelCofork.ofπ (cokernel.π (ΓK.toCycles n (n + 1))) (by simp)
  have hcokerCofork : IsColimit cokerCofork := by
    dsimp [cokerCofork]
    exact cokernelIsCokernel (ΓK.toCycles n (n + 1))
  let ehomologyCokernel :
      ΓK.homology (n + 1) ≅ cokernel (ΓK.toCycles n (n + 1)) :=
    CokernelCofork.mapIsoOfIsColimit
      (cc' := cokerCofork)
      (ΓK.homologyIsCokernel n (n + 1) (by simp))
      hcokerCofork
      (Iso.refl (Arrow.mk (ΓK.toCycles n (n + 1))))
  let ecokernel :
      cokernel (ΓK.toCycles n (n + 1)) ≅
        cokernel (Γ.map (K.toCycles n (n + 1))) :=
    cokernel.mapIso (f := ΓK.toCycles n (n + 1))
      (Γ.map (K.toCycles n (n + 1))) (Iso.refl _) e (by
      simpa [Γ, ΓK] using he)
  exact ⟨(ehomologyCokernel ≪≫ ecokernel).addCommGroupIsoToAddEquiv⟩

/--
%%handwave
name:
  Global-section homology-to-cokernel comparison is natural
statement:
  The identification of \(H^{n+1}(\Gamma K^\bullet)\) with the cokernel of
  \(\Gamma(K^n)\to\Gamma(Z^{n+1})\) may be chosen to commute with any family
  of endomorphisms of the complex.
proof:
  Use the functoriality of homology as a cokernel and the naturality of the
  kernel isomorphism identifying \(\Gamma(Z^{n+1})\) with the cycles of
  \(\Gamma(K^\bullet)\).
-/
theorem exists_globalSections_homology_succ_addEquiv_cokernel_to_cycles_natural_with_family_map
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    {ι : Type*} (φK : ι → (K ⟶ K))
    (n : ℕ) :
    ∃ e :
      ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology (n + 1)) ≃+
        ↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles n (n + 1)))),
      ∀ (i : ι)
        (x :
          ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj K).homology (n + 1))),
        e ((HomologicalComplex.homologyMap
              (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
                (ComplexShape.up ℕ)).map (φK i)) (n + 1)) x) =
          (globalSections_toCycles_cokernelEnd (J := J) K (φK i) n) (e x) := by
  let Γ := Sheaf.Γ J AddCommGrpCat.{w}
  let ΓK := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let j := n + 1
  obtain ⟨eCycles, heToCycles, heCyclesNat⟩ :=
    exists_globalSections_cycles_iso_compatible_toCycles_natural_with_family_map
      (J := J) (K := K) φK n
  let cokerCofork : CokernelCofork (ΓK.toCycles n (n + 1)) :=
    CokernelCofork.ofπ (cokernel.π (ΓK.toCycles n (n + 1))) (by simp)
  have hcokerCofork : IsColimit cokerCofork := by
    dsimp [cokerCofork]
    exact cokernelIsCokernel (ΓK.toCycles n (n + 1))
  let ehomologyCokernel :
      ΓK.homology (n + 1) ≅ cokernel (ΓK.toCycles n (n + 1)) :=
    CokernelCofork.mapIsoOfIsColimit
      (cc' := cokerCofork)
      (ΓK.homologyIsCokernel n (n + 1) (by simp))
      hcokerCofork
      (Iso.refl (Arrow.mk (ΓK.toCycles n (n + 1))))
  let ecokernel :
      cokernel (ΓK.toCycles n (n + 1)) ≅
        cokernel (Γ.map (K.toCycles n (n + 1))) :=
    cokernel.mapIso (f := ΓK.toCycles n (n + 1))
      (Γ.map (K.toCycles n (n + 1))) (Iso.refl _) eCycles (by
      simpa [Γ, ΓK] using heToCycles)
  let eComparison : ΓK.homology (n + 1) ≅
      cokernel (Γ.map (K.toCycles n (n + 1))) :=
    ehomologyCokernel ≪≫ ecokernel
  refine ⟨eComparison.addCommGroupIsoToAddEquiv, ?_⟩
  intro i x
  let Γφ : ΓK ⟶ ΓK :=
    (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map (φK i)
  have hΓ_toCycles_cyclesMap :
      ΓK.toCycles n (n + 1) ≫
          HomologicalComplex.cyclesMap Γφ (n + 1) =
        Γφ.f n ≫ ΓK.toCycles n (n + 1) := by
    apply (cancel_mono (ΓK.iCycles (n + 1))).1
    calc
      (ΓK.toCycles n (n + 1) ≫ HomologicalComplex.cyclesMap Γφ (n + 1)) ≫
            ΓK.iCycles (n + 1)
          = ΓK.toCycles n (n + 1) ≫
              (HomologicalComplex.cyclesMap Γφ (n + 1) ≫ ΓK.iCycles (n + 1)) := by
              rw [Category.assoc]
      _ = ΓK.toCycles n (n + 1) ≫ (ΓK.iCycles (n + 1) ≫ Γφ.f (n + 1)) := by
              rw [HomologicalComplex.cyclesMap_i]
      _ = (ΓK.toCycles n (n + 1) ≫ ΓK.iCycles (n + 1)) ≫ Γφ.f (n + 1) := by
              rw [Category.assoc]
      _ = ΓK.d n (n + 1) ≫ Γφ.f (n + 1) := by
              rw [HomologicalComplex.toCycles_i]
      _ = Γφ.f n ≫ ΓK.d n (n + 1) := by
              exact (HomologicalComplex.Hom.comm Γφ n (n + 1)).symm
      _ = Γφ.f n ≫ (ΓK.toCycles n (n + 1) ≫ ΓK.iCycles (n + 1)) := by
              rw [HomologicalComplex.toCycles_i]
      _ = (Γφ.f n ≫ ΓK.toCycles n (n + 1)) ≫ ΓK.iCycles (n + 1) := by
              rw [Category.assoc]
  let cokerEndΓK :
      cokernel (ΓK.toCycles n (n + 1)) ⟶
        cokernel (ΓK.toCycles n (n + 1)) :=
    cokernel.map (ΓK.toCycles n (n + 1)) (ΓK.toCycles n (n + 1))
      (Γφ.f n) (HomologicalComplex.cyclesMap Γφ (n + 1))
      hΓ_toCycles_cyclesMap
  have hπ_ehomologyCokernel :
      ΓK.homologyπ (n + 1) ≫ ehomologyCokernel.hom =
        cokernel.π (ΓK.toCycles n (n + 1)) := by
    simpa [ehomologyCokernel, cokerCofork] using
      (CokernelCofork.π_mapOfIsColimit
        (ΓK.homologyIsCokernel n (n + 1) (by simp))
        cokerCofork
        (𝟙 (Arrow.mk (ΓK.toCycles n (n + 1)))))
  have hhomologyCokernel_nat :
      HomologicalComplex.homologyMap Γφ (n + 1) ≫ ehomologyCokernel.hom =
        ehomologyCokernel.hom ≫ cokerEndΓK := by
    apply (cancel_epi (ΓK.homologyπ (n + 1))).1
    calc
      ΓK.homologyπ (n + 1) ≫
          (HomologicalComplex.homologyMap Γφ (n + 1) ≫ ehomologyCokernel.hom)
          = (ΓK.homologyπ (n + 1) ≫
              HomologicalComplex.homologyMap Γφ (n + 1)) ≫ ehomologyCokernel.hom := by
              rw [Category.assoc]
      _ = (HomologicalComplex.cyclesMap Γφ (n + 1) ≫
              ΓK.homologyπ (n + 1)) ≫ ehomologyCokernel.hom := by
              rw [HomologicalComplex.homologyπ_naturality]
      _ = HomologicalComplex.cyclesMap Γφ (n + 1) ≫
              (ΓK.homologyπ (n + 1) ≫ ehomologyCokernel.hom) := by
              rw [Category.assoc]
      _ = HomologicalComplex.cyclesMap Γφ (n + 1) ≫
              cokernel.π (ΓK.toCycles n (n + 1)) := by
              rw [hπ_ehomologyCokernel]
      _ = cokernel.π (ΓK.toCycles n (n + 1)) ≫ cokerEndΓK := by
              simp [cokerEndΓK]
      _ = (ΓK.homologyπ (n + 1) ≫ ehomologyCokernel.hom) ≫ cokerEndΓK := by
              rw [hπ_ehomologyCokernel]
      _ = ΓK.homologyπ (n + 1) ≫ (ehomologyCokernel.hom ≫ cokerEndΓK) := by
              rw [Category.assoc]
  have hπ_globalEnd :
      cokernel.π (Γ.map (K.toCycles n (n + 1))) ≫
          globalSections_toCycles_cokernelEnd (J := J) K (φK i) n =
        Γ.map (HomologicalComplex.cyclesMap (φK i) (n + 1)) ≫
          cokernel.π (Γ.map (K.toCycles n (n + 1))) := by
    dsimp [globalSections_toCycles_cokernelEnd]
    rw [cokernel.π_desc]
  have hcokernel_nat :
      cokerEndΓK ≫ ecokernel.hom =
        ecokernel.hom ≫ globalSections_toCycles_cokernelEnd (J := J) K (φK i) n := by
    apply (cancel_epi (cokernel.π (ΓK.toCycles n (n + 1)))).1
    calc
      cokernel.π (ΓK.toCycles n (n + 1)) ≫ (cokerEndΓK ≫ ecokernel.hom)
          = (cokernel.π (ΓK.toCycles n (n + 1)) ≫ cokerEndΓK) ≫
              ecokernel.hom := by
              rw [Category.assoc]
      _ = (HomologicalComplex.cyclesMap Γφ (n + 1) ≫
              cokernel.π (ΓK.toCycles n (n + 1))) ≫ ecokernel.hom := by
              simp [cokerEndΓK]
      _ = HomologicalComplex.cyclesMap Γφ (n + 1) ≫
              (cokernel.π (ΓK.toCycles n (n + 1)) ≫ ecokernel.hom) := by
              rw [Category.assoc]
      _ = HomologicalComplex.cyclesMap Γφ (n + 1) ≫
              (eCycles.hom ≫ cokernel.π (Γ.map (K.toCycles n (n + 1)))) := by
              simp [ecokernel]
      _ = (HomologicalComplex.cyclesMap Γφ (n + 1) ≫ eCycles.hom) ≫
              cokernel.π (Γ.map (K.toCycles n (n + 1))) := by
              rw [Category.assoc]
      _ = (eCycles.hom ≫ Γ.map
              (HomologicalComplex.cyclesMap (φK i) (n + 1))) ≫
              cokernel.π (Γ.map (K.toCycles n (n + 1))) := by
              rw [heCyclesNat i]
      _ = eCycles.hom ≫
              (Γ.map (HomologicalComplex.cyclesMap (φK i) (n + 1)) ≫
                cokernel.π (Γ.map (K.toCycles n (n + 1)))) := by
              rw [Category.assoc]
      _ = eCycles.hom ≫
              (cokernel.π (Γ.map (K.toCycles n (n + 1))) ≫
                globalSections_toCycles_cokernelEnd (J := J) K (φK i) n) := by
              rw [hπ_globalEnd]
      _ = (eCycles.hom ≫ cokernel.π (Γ.map (K.toCycles n (n + 1)))) ≫
              globalSections_toCycles_cokernelEnd (J := J) K (φK i) n := by
              rw [Category.assoc]
      _ = (cokernel.π (ΓK.toCycles n (n + 1)) ≫ ecokernel.hom) ≫
              globalSections_toCycles_cokernelEnd (J := J) K (φK i) n := by
              simp [ecokernel]
      _ = cokernel.π (ΓK.toCycles n (n + 1)) ≫
              (ecokernel.hom ≫ globalSections_toCycles_cokernelEnd (J := J) K (φK i) n) := by
              rw [Category.assoc]
  have hcomparison_nat :
      HomologicalComplex.homologyMap Γφ (n + 1) ≫ eComparison.hom =
        eComparison.hom ≫ globalSections_toCycles_cokernelEnd (J := J) K (φK i) n := by
    calc
      HomologicalComplex.homologyMap Γφ (n + 1) ≫ eComparison.hom
          = (HomologicalComplex.homologyMap Γφ (n + 1) ≫ ehomologyCokernel.hom) ≫
              ecokernel.hom := by
              rfl
      _ = (ehomologyCokernel.hom ≫ cokerEndΓK) ≫ ecokernel.hom := by
              rw [hhomologyCokernel_nat]
      _ = ehomologyCokernel.hom ≫ (cokerEndΓK ≫ ecokernel.hom) := by
              rw [Category.assoc]
      _ = ehomologyCokernel.hom ≫
              (ecokernel.hom ≫ globalSections_toCycles_cokernelEnd (J := J) K (φK i) n) := by
              rw [hcokernel_nat]
      _ = eComparison.hom ≫ globalSections_toCycles_cokernelEnd (J := J) K (φK i) n := by
              rfl
  exact congrArg
    (fun f : ΓK.homology (n + 1) ⟶
        cokernel (Γ.map (K.toCycles n (n + 1))) => f x)
    hcomparison_nat

/--
%%handwave
name:
  The low-degree edge for the augmented resolution
statement:
  For an augmented acyclic resolution \(F\to K^\bullet\), the cokernel of
  \(\Gamma(K^0)\to\Gamma(Z^1)\) is additively isomorphic to \(H^1(F)\).
proof:
  Apply the low-degree edge theorem to the short exact sequence
  \(0\to F\to K^0\to Z^1\to0\).
-/
theorem nonempty_augmented_cokernel_addEquiv_sheafCohomology_one
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_one : K.ExactAt 1)
    (hacyclic₀ : ∀ q : ℕ, 0 < q → Subsingleton ((K.X 0).H q)) :
    Nonempty
      (↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles 0 1))) ≃+
        F.H 1) := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk ε (K.toCycles 0 1)
      (by
        rw [← cancel_mono (K.iCycles 1), Category.assoc,
          HomologicalComplex.toCycles_i, hε, zero_comp])
  have hS : S.ShortExact :=
    cochain_augmented_cycles_shortExact_of_exactAt_one
      (J := J) F K ε hε hexact_zero hmono_ε hexact_one
  exact
    nonempty_globalSections_cokernel_addEquiv_sheafCohomology_one_of_shortExact_middle_acyclic
      (J := J) hS (hacyclic₀ 1 (by omega))

/--
%%handwave
name:
  The augmented low-degree edge is natural
statement:
  The low-degree edge isomorphism from the cokernel of
  \(\Gamma(K^0)\to\Gamma(Z^1)\) to \(H^1(F)\) may be chosen to commute with
  any family of endomorphisms of the augmented resolution.
proof:
  Apply naturality of the long exact sequence in cohomology to the short
  exact sequence \(0\to F\to K^0\to Z^1\to0\), together with naturality of
  the cokernel presentation of the edge map.
-/
theorem exists_augmented_cokernel_addEquiv_sheafCohomology_one_natural_with_family_map
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_one : K.ExactAt 1)
    (hacyclic₀ : ∀ q : ℕ, 0 < q → Subsingleton ((K.X 0).H q))
    {ι : Type*}
    (φF : ι → (F ⟶ F)) (φK : ι → (K ⟶ K))
    (hε_map : ∀ i, ε ≫ (φK i).f 0 = φF i ≫ ε) :
    ∃ e :
      ↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles 0 1))) ≃+
        F.H 1,
      ∀ (i : ι)
        (x : ↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles 0 1)))),
        e ((globalSections_toCycles_cokernelEnd (J := J) K (φK i) 0) x) =
          ((functorH J 1).map (φF i)) (e x) := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk ε (K.toCycles 0 1)
      (by
        rw [← cancel_mono (K.iCycles 1), Category.assoc,
          HomologicalComplex.toCycles_i, hε, zero_comp])
  have hS : S.ShortExact :=
    cochain_augmented_cycles_shortExact_of_exactAt_one
      (J := J) F K ε hε hexact_zero hmono_ε hexact_one
  let ψ : ι → (S ⟶ S) := fun i =>
    ShortComplex.homMk (φF i) ((φK i).f 0)
      (HomologicalComplex.cyclesMap (φK i) 1)
      (by simpa [S] using (hε_map i).symm)
      (by
        simpa [S] using
          (cochain_toCycles_cyclesMap (J := J) K (φK i) 0).symm)
  obtain ⟨e, he⟩ :=
    exists_globalSections_cokernel_addEquiv_sheafCohomology_one_of_shortExact_middle_acyclic_natural_with_family_map
      (J := J) hS (hacyclic₀ 1 (by omega)) ψ
  refine ⟨e, ?_⟩
  intro i x
  simpa [S, ψ, globalSections_shortComplex_cokernelEnd,
    globalSections_toCycles_cokernelEnd] using he i x

/--
%%handwave
name:
  The low-degree edge along the cycles
statement:
  For a cochain complex of acyclic sheaves exact in degrees \(p\) and
  \(p+1\), the cokernel of \(\Gamma(K^p)\to\Gamma(Z^{p+1})\) is additively
  isomorphic to \(H^1(Z^p)\).
proof:
  Apply the low-degree edge theorem to the short exact sequence
  \(0\to Z^p\to K^p\to Z^{p+1}\to0\).
-/
theorem nonempty_cycles_cokernel_addEquiv_sheafCohomology_one
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (p : ℕ) (hp : K.ExactAt p) (hsucc : K.ExactAt (p + 1))
    (hacyclic_p : ∀ q : ℕ, 0 < q → Subsingleton ((K.X p).H q)) :
    Nonempty
      (↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles p (p + 1)))) ≃+
        (K.cycles p).H 1) := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk (K.iCycles p) (K.toCycles p (p + 1))
      (by
        rw [← cancel_mono (K.iCycles (p + 1)), Category.assoc,
          HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d, zero_comp])
  have hS : S.ShortExact :=
    cochain_cycles_shortExact_of_exactAt_and_succ
      (J := J) K p hp hsucc
  exact
    nonempty_globalSections_cokernel_addEquiv_sheafCohomology_one_of_shortExact_middle_acyclic
      (J := J) hS (hacyclic_p 1 (by omega))

/--
%%handwave
name:
  The cycle low-degree edge is natural
statement:
  The low-degree edge isomorphism from the cokernel of
  \(\Gamma(K^p)\to\Gamma(Z^{p+1})\) to \(H^1(Z^p)\) may be chosen to commute
  with any family of endomorphisms of the complex.
proof:
  Apply naturality of the long exact sequence in cohomology to
  \(0\to Z^p\to K^p\to Z^{p+1}\to0\), together with naturality of the
  cokernel presentation of the edge map.
-/
theorem exists_cycles_cokernel_addEquiv_sheafCohomology_one_natural_with_family_map
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (p : ℕ) (hp : K.ExactAt p) (hsucc : K.ExactAt (p + 1))
    (hacyclic_p : ∀ q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    {ι : Type*} (φK : ι → (K ⟶ K)) :
    ∃ e :
      ↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles p (p + 1)))) ≃+
        (K.cycles p).H 1,
      ∀ (i : ι)
        (x : ↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map (K.toCycles p (p + 1))))),
        e ((globalSections_toCycles_cokernelEnd (J := J) K (φK i) p) x) =
          ((functorH J 1).map
            (HomologicalComplex.cyclesMap (φK i) p)) (e x) := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
    ShortComplex.mk (K.iCycles p) (K.toCycles p (p + 1))
      (by
        rw [← cancel_mono (K.iCycles (p + 1)), Category.assoc,
          HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d, zero_comp])
  have hS : S.ShortExact :=
    cochain_cycles_shortExact_of_exactAt_and_succ
      (J := J) K p hp hsucc
  let ψ : ι → (S ⟶ S) := fun i =>
    ShortComplex.homMk
      (HomologicalComplex.cyclesMap (φK i) p) ((φK i).f p)
      (HomologicalComplex.cyclesMap (φK i) (p + 1))
      (by simp [S])
      (by
        simpa [S] using
          (cochain_toCycles_cyclesMap (J := J) K (φK i) p).symm)
  obtain ⟨e, he⟩ :=
    exists_globalSections_cokernel_addEquiv_sheafCohomology_one_of_shortExact_middle_acyclic_natural_with_family_map
      (J := J) hS (hacyclic_p 1 (by omega)) ψ
  refine ⟨e, ?_⟩
  intro i x
  simpa [S, ψ, globalSections_shortComplex_cokernelEnd,
    globalSections_toCycles_cokernelEnd] using he i x

/--
%%handwave
name:
  The positive cycle edge is natural
statement:
  In degree \(m+2\), the cokernel of
  \(\Gamma(K^{m+1})\to\Gamma(Z^{m+2})\) may be identified with
  \(H^{m+2}(F)\), compatibly with any family of endomorphisms of the
  augmented resolution.
proof:
  Compose the natural low-degree edge
  \(\operatorname{coker}(\Gamma K^{m+1}\to\Gamma Z^{m+2})\simeq
  H^1(Z^{m+1})\) with the natural iterated dimension-shifting isomorphism
  \(H^1(Z^{m+1})\simeq H^{m+2}(F)\).
-/
theorem exists_cycles_cokernel_addEquiv_sheafCohomology_succ_natural_with_family_map
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_pos : ∀ n : ℕ, K.ExactAt (n + 1))
    (hacyclic : ∀ p q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    {ι : Type*}
    (φF : ι → (F ⟶ F)) (φK : ι → (K ⟶ K))
    (hε_map : ∀ i, ε ≫ (φK i).f 0 = φF i ≫ ε)
    (m : ℕ) :
    ∃ e :
      ↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map
        (K.toCycles (m + 1) ((m + 1) + 1)))) ≃+
        F.H ((m + 1) + 1),
      ∀ (i : ι)
        (x : ↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{w}).map
          (K.toCycles (m + 1) ((m + 1) + 1))))),
        e ((globalSections_toCycles_cokernelEnd (J := J) K (φK i) (m + 1)) x) =
          ((functorH J ((m + 1) + 1)).map (φF i)) (e x) := by
  obtain ⟨eedge, hedge⟩ :=
    exists_cycles_cokernel_addEquiv_sheafCohomology_one_natural_with_family_map
      (J := J) K (m + 1) (hexact_pos m) (hexact_pos (m + 1))
      (fun q hq => hacyclic (m + 1) q hq) φK
  let eshift : (K.cycles (m + 1)).H 1 ≃+ F.H (1 + (m + 1)) :=
    cochain_cycles_to_augmented_dimensionShift_addEquiv
      (J := J) F K ε hε hexact_zero hmono_ε hexact_pos hacyclic m 1
      (by omega)
  have hidx : 1 + (m + 1) = (m + 1) + 1 := by omega
  let ecast : F.H (1 + (m + 1)) ≃+ F.H ((m + 1) + 1) :=
    AddEquiv.cast (M := fun k : ℕ => F.H k) hidx
  refine ⟨eedge.trans (eshift.trans ecast), ?_⟩
  intro i x
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, hedge i x]
  rw [cochain_cycles_to_augmented_dimensionShift_addEquiv_natural_with_family_map
      (J := J) F K ε hε hexact_zero hmono_ε hexact_pos hacyclic
      φF φK hε_map m 1 (by omega) i (eedge x)]
  simpa [ecast] using
    sheafCohomology_cast_map (J := J) (φF i) hidx (eshift (eedge x))

/--
%%handwave
name:
  Positive-degree acyclic-resolution comparison
statement:
  Let \(F\to K^\bullet\) be an exact augmented cochain complex with
  \(F\to K^0\) a monomorphism, and suppose every \(K^p\) has vanishing
  positive sheaf cohomology.  In every positive degree, the cohomology of
  \(\Gamma(K^\bullet)\) is additively isomorphic to the sheaf cohomology of
  \(F\).
proof:
  Identify \(H^{n+1}(\Gamma(K^\bullet))\) with the cokernel of
  \(\Gamma(K^n)\to\Gamma(Z^{n+1})\).  For \(n=0\), the low-degree edge of
  \(0\to F\to K^0\to Z^1\to0\) identifies this cokernel with \(H^1(F)\).
  For \(n>0\), the low-degree edge of
  \(0\to Z^n\to K^n\to Z^{n+1}\to0\) identifies it with \(H^1(Z^n)\), and
  iterated dimension shifting identifies \(H^1(Z^n)\) with \(H^{n+1}(F)\).
-/
theorem nonempty_globalSections_positive_homology_addEquiv_sheafCohomology_of_acyclic_resolution
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_pos : ∀ n : ℕ, K.ExactAt (n + 1))
    (hacyclic : ∀ p q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    (n : ℕ) :
    Nonempty
      (↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology (n + 1)) ≃+
        F.H (n + 1)) := by
  obtain ⟨ehom⟩ :=
    nonempty_globalSections_homology_succ_addEquiv_cokernel_to_cycles
      (J := J) K n
  cases n with
  | zero =>
      obtain ⟨eedge⟩ :=
        nonempty_augmented_cokernel_addEquiv_sheafCohomology_one
          (J := J) F K ε hε hexact_zero hmono_ε (hexact_pos 0)
          (fun q hq => hacyclic 0 q hq)
      exact ⟨ehom.trans eedge⟩
  | succ m =>
      obtain ⟨eedge⟩ :=
        nonempty_cycles_cokernel_addEquiv_sheafCohomology_one
          (J := J) K (m + 1) (hexact_pos m) (hexact_pos (m + 1))
          (fun q hq => hacyclic (m + 1) q hq)
      let eshift : (K.cycles (m + 1)).H 1 ≃+ F.H (1 + (m + 1)) :=
        cochain_cycles_to_augmented_dimensionShift_addEquiv
          (J := J) F K ε hε hexact_zero hmono_ε hexact_pos hacyclic m 1
          (by omega)
      have hidx : 1 + (m + 1) = (m + 1) + 1 := by omega
      exact ⟨hidx ▸ ehom.trans (eedge.trans eshift)⟩

/--
%%handwave
name:
  Positive-degree acyclic-resolution comparison is natural for a family of endomorphisms
statement:
  Let \(F\to K^\bullet\) be an exact augmented cochain complex with
  \(F\to K^0\) a monomorphism, and suppose every \(K^p\) has vanishing
  positive sheaf cohomology.  In every positive degree, the cohomology of
  \(\Gamma(K^\bullet)\) is additively isomorphic to the sheaf cohomology of
  \(F\), compatibly with any family of endomorphisms of the augmented
  resolution.
proof:
  Write \(Z^p=\ker(K^p\to K^{p+1})\), with \(Z^0=F\).  Exactness gives short
  exact sequences \(0\to Z^p\to K^p\to Z^{p+1}\to0\).  Since the \(K^p\) are
  acyclic, the long exact Ext sequences identify \(H^{q+1}(Z^p)\) with
  \(H^q(Z^{p+1})\) for \(q>0\).  Iterating reduces \(H^{n+1}(F)\) to
  \(H^1(Z^n)\).  The remaining part of the long exact sequence identifies
  \(H^1(Z^n)\) with the cokernel of
  \(\Gamma(K^n)\to\Gamma(Z^{n+1})\), and left exactness identifies
  \(\Gamma(Z^{n+1})\) with the cycles in degree \(n+1\) of
  \(\Gamma(K^\bullet)\).  This cokernel is the \((n+1)\)-st homology of
  \(\Gamma(K^\bullet)\).  Naturality of the long exact sequences and kernels
  gives the stated compatibility with endomorphisms.
tags:
  milestone
-/
theorem exists_globalSections_positive_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_family_map
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_pos : ∀ n : ℕ, K.ExactAt (n + 1))
    (hacyclic : ∀ p q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    {ι : Type*}
    (φF : ι → (F ⟶ F)) (φK : ι → (K ⟶ K))
    (hε_map : ∀ i, ε ≫ (φK i).f 0 = φF i ≫ ε)
    (n : ℕ) :
    ∃ e :
      ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology (n + 1)) ≃+
        F.H (n + 1),
      ∀ (i : ι)
        (x :
          ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj K).homology (n + 1))),
        e ((HomologicalComplex.homologyMap
              (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
                (ComplexShape.up ℕ)).map (φK i)) (n + 1)) x) =
          ((functorH J (n + 1)).map (φF i)) (e x) := by
  obtain ⟨ehom, hehom⟩ :=
    exists_globalSections_homology_succ_addEquiv_cokernel_to_cycles_natural_with_family_map
      (J := J) (K := K) φK n
  cases n with
  | zero =>
      obtain ⟨eedge, hedge⟩ :=
        exists_augmented_cokernel_addEquiv_sheafCohomology_one_natural_with_family_map
          (J := J) F K ε hε hexact_zero hmono_ε (hexact_pos 0)
          (fun q hq => hacyclic 0 q hq) φF φK hε_map
      refine ⟨ehom.trans eedge, ?_⟩
      intro i x
      rw [AddEquiv.trans_apply, hehom i x, hedge i (ehom x)]
      rfl
  | succ m =>
      obtain ⟨etail, hetail⟩ :=
        exists_cycles_cokernel_addEquiv_sheafCohomology_succ_natural_with_family_map
          (J := J) F K ε hε hexact_zero hmono_ε hexact_pos hacyclic
          φF φK hε_map m
      refine ⟨ehom.trans etail, ?_⟩
      intro i x
      rw [AddEquiv.trans_apply, hehom i x, hetail i (ehom x)]
      rfl

/--
%%handwave
name:
  Acyclic-resolution comparison is natural for a family of endomorphisms, core theorem
statement:
  Let \(F\to K^\bullet\) be an acyclic resolution of an abelian sheaf, with
  \(F\to K^0\) a monomorphism.  If a family of endomorphisms of \(F\) extends
  to a family of endomorphisms of the augmented resolution, then the
  comparison from the cohomology of global sections of \(K^\bullet\) to the
  sheaf cohomology of \(F\) may be chosen to intertwine all endomorphisms in
  the family simultaneously.
proof:
  In degree zero, use left exactness of global sections and the identification
  \(H^0=\Gamma\).  In positive degree, use the standard dimension-shifting
  argument along the cycles of the acyclic resolution.  These two comparisons
  are natural for morphisms of augmented resolutions, so they give the stated
  simultaneous compatibility.
tags:
  milestone
-/
theorem exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_family_map_core
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_pos : ∀ n : ℕ, K.ExactAt (n + 1))
    (hacyclic : ∀ p q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    {ι : Type*}
    (φF : ι → (F ⟶ F)) (φK : ι → (K ⟶ K))
    (hε_map : ∀ i, ε ≫ (φK i).f 0 = φF i ≫ ε)
    (n : ℕ) :
    ∃ e :
      ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology n) ≃+
        F.H n,
      ∀ (i : ι)
        (x :
          ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj K).homology n)),
        e ((HomologicalComplex.homologyMap
              (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
                (ComplexShape.up ℕ)).map (φK i)) n) x) =
          ((functorH J n).map (φF i)) (e x) := by
  cases n with
  | zero =>
      exact
        exists_globalSections_zero_homology_addEquiv_sheafCohomology_of_left_exact_resolution_with_family_map
          (J := J) (F := F) (K := K) ε hε hexact_zero hmono_ε φF φK hε_map
  | succ n =>
      exact
        exists_globalSections_positive_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_family_map
          (J := J) (F := F) (K := K) ε hε hexact_zero hmono_ε hexact_pos hacyclic
          φF φK hε_map n

/--
%%handwave
name:
  Acyclic-resolution comparison is natural for endomorphisms, core theorem
statement:
  Let \(F\to K^\bullet\) be an acyclic resolution of an abelian sheaf, with
  \(F\to K^0\) a monomorphism.  If an endomorphism of \(F\) extends to an
  endomorphism of the augmented resolution, then the comparison from the
  cohomology of global sections of \(K^\bullet\) to the sheaf cohomology of
  \(F\) may be chosen to intertwine the induced maps.
proof:
  Use the functoriality of the derived-functor construction.  The comparison
  is the edge isomorphism obtained by replacing \(F\) with the acyclic
  resolution \(K^\bullet\); functoriality of this replacement identifies the
  homology map of global sections with the sheaf-cohomology map.
-/
theorem exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_map_core
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_pos : ∀ n : ℕ, K.ExactAt (n + 1))
    (hacyclic : ∀ p q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    (φF : F ⟶ F) (φK : K ⟶ K)
    (hε_map : ε ≫ φK.f 0 = φF ≫ ε)
    (n : ℕ) :
    ∃ e :
      ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology n) ≃+
        F.H n,
      ∀ x :
        ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).homology n),
        e ((HomologicalComplex.homologyMap
              (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
                (ComplexShape.up ℕ)).map φK) n) x) =
          ((functorH J n).map φF) (e x) := by
  rcases
    exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_family_map_core
      (F := F) (K := K) ε hε hexact_zero hmono_ε hexact_pos hacyclic
      (ι := Unit) (fun _ => φF) (fun _ => φK) (fun _ => hε_map) n with
    ⟨e, he⟩
  exact ⟨e, fun x => by simpa using he () x⟩

/--
%%handwave
name:
  Acyclic resolutions compute sheaf cohomology
statement:
  Let \(F\) be a sheaf of abelian groups and let
  \(F\to K^0\to K^1\to\cdots\) be an exact augmented cochain complex of
  sheaves whose first map is a monomorphism.  If every \(K^p\) has vanishing
  positive sheaf cohomology, then
  the cohomology of the global-sections complex \(\Gamma(K^\bullet)\) is
  naturally additively isomorphic to the sheaf cohomology of \(F\).
proof:
  This is the standard acyclic-resolution theorem for the right derived
  functors of global sections.  Filter the augmented resolution by brutal
  truncations, use acyclicity of the terms to identify the derived
  global-sections spectral sequence, and read off that its edge map is an
  isomorphism in every degree.
tags:
  milestone
-/
theorem globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_pos : ∀ n : ℕ, K.ExactAt (n + 1))
    (hacyclic : ∀ p q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    (n : ℕ) :
    Nonempty
      (↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology n) ≃+
        F.H n) := by
  cases n with
  | zero =>
      rcases
        exists_globalSections_zero_homology_addEquiv_sheafCohomology_of_left_exact_resolution_with_family_map
          (J := J) (F := F) (K := K) ε hε hexact_zero hmono_ε
          (ι := Unit) (fun _ => 𝟙 F) (fun _ => 𝟙 K) (fun _ => by simp) with
        ⟨e, _⟩
      exact ⟨e⟩
  | succ n =>
      exact
        nonempty_globalSections_positive_homology_addEquiv_sheafCohomology_of_acyclic_resolution
          (J := J) F K ε hε hexact_zero hmono_ε hexact_pos hacyclic n

/--
%%handwave
name:
  Acyclic-resolution comparison is natural for endomorphisms
statement:
  Let \(F\to K^\bullet\) be an acyclic resolution of an abelian sheaf, with
  \(F\to K^0\) a monomorphism.  If an endomorphism of \(F\) extends to an
  endomorphism of the augmented resolution, then the comparison from the
  cohomology of global sections of \(K^\bullet\) to the sheaf cohomology of
  \(F\) may be chosen to intertwine the induced maps.
proof:
  Use the functoriality of the derived-functor construction.  The comparison
  is the edge isomorphism obtained by replacing \(F\) with the acyclic
  resolution \(K^\bullet\); functoriality of this replacement identifies the
  homology map of global sections with the sheaf-cohomology map.
-/
theorem exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_map
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
    (ε : F ⟶ K.X 0)
    (hε : ε ≫ K.d 0 1 = 0)
    (hexact_zero :
      ({ f := ε, g := K.d 0 1, zero := hε } :
        ShortComplex (Sheaf J AddCommGrpCat.{w})).Exact)
    (hmono_ε : Mono ε)
    (hexact_pos : ∀ n : ℕ, K.ExactAt (n + 1))
    (hacyclic : ∀ p q : ℕ, 0 < q → Subsingleton ((K.X p).H q))
    (φF : F ⟶ F) (φK : K ⟶ K)
    (hε_map : ε ≫ φK.f 0 = φF ≫ ε)
    (n : ℕ) :
    ∃ e :
      ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology n) ≃+
        F.H n,
      ∀ x :
        ↥((((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).homology n),
        e ((HomologicalComplex.homologyMap
              (((Sheaf.Γ J AddCommGrpCat.{w}).mapHomologicalComplex
                (ComplexShape.up ℕ)).map φK) n) x) =
          ((functorH J n).map φF) (e x) := by
  exact
    exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_map_core
      (F := F) (K := K) ε hε hexact_zero hmono_ε hexact_pos hacyclic
      φF φK hε_map n

end

end Sheaf
end CategoryTheory
