import JJMath.Manifold.DeRhamComparison.Base

open scoped Manifold ContDiff Topology ZeroObject

namespace JJMath
namespace Manifold

open Set
open Topology
open Filter
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 80000

universe v w m uC vC tSmall tBig

variable {E : Type v} [NormedAddCommGroup E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]





/--
%%handwave
name:
  Sheafification in the smooth-form coefficient universe
statement:
  The open-set site of a topological space has sheafification for
  abelian-group-valued presheaves in the coefficient universe large enough for
  smooth differential forms.
proof:
  The open-cover categories are filtered and live in the space universe.  The
  forgetful functor from abelian groups preserves filtered colimits in the
  enlarged coefficient universe after shrinking the preservation universe, so
  the standard sheafification instance applies.
-/
theorem opens_addCommGrp_hasSheafify_smoothFormsUniverse (X : TopCat.{m}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m} := by
  classical
  haveI : PreservesFilteredColimitsOfSize.{m, m}
      (forget AddCommGrpCat.{max v m}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max v m})
  infer_instance

/--
%%handwave
name:
  Ext groups in the smooth-form coefficient universe
statement:
  The category of abelian-group sheaves on the open-set site has the Ext
  groups used for sheaf cohomology in the coefficient universe large enough
  for smooth differential forms.
proof:
  Once sheafification is available in that universe, abelian-group sheaves form
  an abelian category and, by passage to an essentially small open-set site, a
  Grothendieck abelian category in the same universe.  The general Ext
  construction for Grothendieck abelian categories then applies.
-/
theorem opens_addCommGrp_hasExt_smoothFormsUniverse (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    HasExt.{max v m}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}) := by
  letI : Abelian (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}) :=
    CategoryTheory.sheafIsAbelian
  letI : IsGrothendieckAbelian.{max v m}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}) :=
    CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}
  infer_instance

/--
%%handwave
name:
  Global sections of the lifted singular resolution are the lift of ordinary global sections
statement:
  Let $K^\bullet$ be the sheafified real singular-cochain complex on a space
  $X$.  In every degree $n$, the cohomology of the global sections of the
  universe lift of $K^\bullet$ is naturally isomorphic to the universe lift
  of the cohomology of the ordinary global-section complex.  The isomorphism
  intertwines every cochainwise real-scalar endomorphism.
proof:
  Global sections commute naturally with objectwise universe lift.  Apply
  this natural isomorphism degreewise to the singular-cochain complex, then
  use exactness of universe lift to commute it with homology.  Naturality of
  both isomorphisms gives compatibility with scalar endomorphisms.
-/
theorem
    exists_liftedRealSingularCochainGlobalSections_homology_iso_with_scalar
    (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{m}]
    [HasGlobalSectionsFunctor
      (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max v m}]
    [HasGlobalSectionsFunctor
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{max v m}]
    (n : ℕ) :
    let J := Opens.grothendieckTopology X
    let U := sheafCompose J AddCommGrpCat.uliftFunctor.{v, m}
    let Γsmall := Sheaf.Γ J AddCommGrpCat.{m}
    let Γbig := Sheaf.Γ J AddCommGrpCat.{max v m}
    let Ksmall := JJMath.Cohomology.realSingularCochainSheafComplex X
    let Kbig := (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj Ksmall
    let Lsmall :=
      (Γsmall.mapHomologicalComplex (ComplexShape.up ℕ)).obj Ksmall
    let Lbig :=
      (Γbig.mapHomologicalComplex (ComplexShape.up ℕ)).obj Kbig
    ∃ e : Lbig.homology n ≅
        AddCommGrpCat.uliftFunctor.{v, m}.obj (Lsmall.homology n),
      ∀ r : ℝ,
        HomologicalComplex.homologyMap
              ((Γbig.mapHomologicalComplex (ComplexShape.up ℕ)).map
                ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map
                  (JJMath.Cohomology.sheafifiedOpenRealSingularCochainSheafScalarEndConcrete
                    X r))) n ≫
            e.hom =
          e.hom ≫
            AddCommGrpCat.uliftFunctor.{v, m}.map
              (HomologicalComplex.homologyMap
                ((Γsmall.mapHomologicalComplex (ComplexShape.up ℕ)).map
                  (JJMath.Cohomology.sheafifiedOpenRealSingularCochainSheafScalarEndConcrete
                    X r)) n) := by
  dsimp only
  let J := Opens.grothendieckTopology X
  let U := sheafCompose J AddCommGrpCat.uliftFunctor.{v, m}
  let Γsmall := Sheaf.Γ J AddCommGrpCat.{m}
  let Γbig := Sheaf.Γ J AddCommGrpCat.{max v m}
  let UGrp := AddCommGrpCat.uliftFunctor.{v, m}
  let Ksmall := JJMath.Cohomology.realSingularCochainSheafComplex X
  let Kbig := (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj Ksmall
  let Lsmall :=
    (Γsmall.mapHomologicalComplex (ComplexShape.up ℕ)).obj Ksmall
  let Lbig :=
    (Γbig.mapHomologicalComplex (ComplexShape.up ℕ)).obj Kbig
  let γ :=
    sheafCompose_uliftFunctor_comp_globalSectionsIso X
  let γHC :=
    NatIso.mapHomologicalComplex γ (ComplexShape.up ℕ)
  let e₁ :
      Lbig.homology n ≅
        ((UGrp.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          Lsmall).homology n := by
    change
      (((((U ⋙ Γbig).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj Ksmall).homology n) ≅
        ((((Γsmall ⋙ UGrp).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj Ksmall).homology n))
    exact
      (HomologicalComplex.homologyFunctor
        AddCommGrpCat.{max v m} (ComplexShape.up ℕ) n).mapIso
          (γHC.app Ksmall)
  let e₂ :
      ((UGrp.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          Lsmall).homology n ≅
        UGrp.obj (Lsmall.homology n) :=
    (Lsmall.sc n).mapHomologyIso UGrp
  let e := e₁ ≪≫ e₂
  refine ⟨e, ?_⟩
  intro r
  let σ :=
    JJMath.Cohomology.sheafifiedOpenRealSingularCochainSheafScalarEndConcrete
      X r
  let σsmall :=
    (Γsmall.mapHomologicalComplex (ComplexShape.up ℕ)).map σ
  have hγchain := γHC.hom.naturality σ
  have hγhom :=
    congrArg
      (fun f =>
        (HomologicalComplex.homologyFunctor
          AddCommGrpCat.{max v m} (ComplexShape.up ℕ) n).map f)
      hγchain
  have he₁ :
      HomologicalComplex.homologyMap
            ((Γbig.mapHomologicalComplex (ComplexShape.up ℕ)).map
              ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map σ)) n ≫
          e₁.hom =
        e₁.hom ≫
          HomologicalComplex.homologyMap
            ((UGrp.mapHomologicalComplex (ComplexShape.up ℕ)).map σsmall) n := by
    simpa only [HomologicalComplex.homologyFunctor_map,
      HomologicalComplex.homologyMap_comp] using hγhom
  have he₂ :
      HomologicalComplex.homologyMap
            ((UGrp.mapHomologicalComplex (ComplexShape.up ℕ)).map σsmall) n ≫
          e₂.hom =
        e₂.hom ≫
          UGrp.map (HomologicalComplex.homologyMap σsmall n) := by
    exact
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor
          AddCommGrpCat.{m} (ComplexShape.up ℕ) n).map σsmall) UGrp
  change
    HomologicalComplex.homologyMap
          ((Γbig.mapHomologicalComplex (ComplexShape.up ℕ)).map
            ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map σ)) n ≫
        e.hom =
      e.hom ≫
        UGrp.map (HomologicalComplex.homologyMap σsmall n)
  simp only [e, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, he₁, Category.assoc, he₂]

/--
%%handwave
name:
  The lifted singular-cochain resolution computes lifted constant-sheaf cohomology
statement:
  Let $X$ be a paracompact Hausdorff locally contractible space whose open
  subspaces are paracompact.  After universe-lifting the sheafified real
  singular-cochain resolution, the cohomology of its global sections is
  additively equivalent to the sheaf cohomology of the lifted constant real
  sheaf.  This equivalence intertwines multiplication by every
  $r\in\mathbb R$ on the resolution and on sheaf cohomology.
proof:
  Universe lift is exact, so it preserves the augmented singular resolution.
  Its terms remain flasque, and flasque sheaves are acyclic even when the
  coefficient universe is larger than the space universe.  Apply the
  scalar-natural acyclic-resolution comparison theorem to the lifted
  augmentation.
-/
theorem
    exists_liftedRealSingularCochainSheafGlobalSectionsCohomology_addEquiv_with_map_smul
    (X : TopCat.{m}) [T2Space X] [ParacompactSpace X]
    (hopen : ∀ V : TopologicalSpace.Opens X, ParacompactSpace V)
    (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasGlobalSectionsFunctor
      (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasExt.{m}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})]
    [HasWeakSheafify
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasGlobalSectionsFunctor
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasSheafify
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasExt.{max v m}
      (Sheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})]
    (n : ℕ) :
    let J := Opens.grothendieckTopology X
    let U :=
      sheafCompose J AddCommGrpCat.uliftFunctor.{v, m}
    let Ksmall := JJMath.Cohomology.realSingularCochainSheafComplex X
    let Kbig :=
      (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj Ksmall
    ∃ e :
        ↥((((Sheaf.Γ J AddCommGrpCat.{max v m}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj Kbig).homology n) ≃+
          ((U.obj (JJMath.Cohomology.RealConstantAddSheaf X)).H n),
      ∀ (r : ℝ)
        (x :
          ↥((((Sheaf.Γ J AddCommGrpCat.{max v m}).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj Kbig).homology n)),
        e
            ((HomologicalComplex.homologyMap
              (((Sheaf.Γ J
                    AddCommGrpCat.{max v m}).mapHomologicalComplex
                  (ComplexShape.up ℕ)).map
                ((U.mapHomologicalComplex
                    (ComplexShape.up ℕ)).map
                  (JJMath.Cohomology.sheafifiedOpenRealSingularCochainSheafScalarEndConcrete
                    X r)))
              n) x) =
          ((CategoryTheory.Sheaf.functorH J n).map
            (U.map
              (JJMath.Cohomology.realConstantSheafScalarEnd X r)))
            (e x) := by
  dsimp only
  let J := Opens.grothendieckTopology X
  let U :=
    sheafCompose J AddCommGrpCat.uliftFunctor.{v, m}
  let Ksmall := JJMath.Cohomology.realSingularCochainSheafComplex X
  let Kbig :=
    (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj Ksmall
  rcases
      JJMath.Cohomology.exists_sheafifiedOpenRealSingularCochainSheafAugmentation_with_resolution_properties
        X hloc with
    ⟨ε, hε, hscalar, hexact_zero, hmono, hexact_pos⟩
  let εBig : U.obj (JJMath.Cohomology.RealConstantAddSheaf X) ⟶
      Kbig.X 0 :=
    U.map ε
  have hεBig : εBig ≫ Kbig.d 0 1 = 0 := by
    simpa [εBig, Kbig, Ksmall] using congrArg U.map hε
  have hscalarBig :
      ∀ r : ℝ,
        εBig ≫
            ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map
              (JJMath.Cohomology.sheafifiedOpenRealSingularCochainSheafScalarEndConcrete
                X r)).f 0 =
          U.map (JJMath.Cohomology.realConstantSheafScalarEnd X r) ≫
            εBig := by
    intro r
    simpa [εBig, Kbig, Ksmall] using
      congrArg U.map (hscalar r)
  have hUExact :
      ∀ S : ShortComplex
          (Sheaf J AddCommGrpCat.{m}),
        S.Exact → (S.map U).Exact :=
    ((Functor.exact_tfae U).out 1 3 rfl rfl).mpr
      ⟨inferInstance, inferInstance⟩
  have hexact_zero_big :
      ({ f := εBig, g := Kbig.d 0 1, zero := hεBig } :
        ShortComplex
          (Sheaf J AddCommGrpCat.{max v m})).Exact := by
    simpa [εBig, Kbig, Ksmall] using
      hUExact
        ({ f := ε, g := Ksmall.d 0 1, zero := hε } :
          ShortComplex (Sheaf J AddCommGrpCat.{m}))
        hexact_zero
  have hmono_big : Mono εBig := by
    letI : Mono ε := hmono
    change Mono (U.map ε)
    exact
      (U.preservesMonomorphisms_of_map_exact hUExact).preserves ε
  have hexact_pos_big : ∀ p : ℕ, Kbig.ExactAt (p + 1) := by
    intro p
    change ((Ksmall.sc (p + 1)).map U).Exact
    exact hUExact (Ksmall.sc (p + 1)) (hexact_pos p)
  have hacyclic :
      ∀ p q : ℕ, 0 < q →
        Subsingleton ((Kbig.X p).H q) := by
    intro p q hq
    letI :
        TopCat.Sheaf.IsFlasque (Ksmall.X p) :=
      JJMath.Cohomology.realSingularCochainSheafComplex_isFlasque_of_open_paracompact
        X hopen p
    letI :
        TopCat.Sheaf.IsFlasque (Kbig.X p) := by
      change
        TopCat.Sheaf.IsFlasque (U.obj (Ksmall.X p))
      exact sheafCompose_uliftFunctor_isFlasque
        (X := X) (Ksmall.X p)
    exact
      JJMath.Cohomology.sheafCohomology_subsingleton_of_flasque
        X (Kbig.X p) q hq
  rcases
      CategoryTheory.Sheaf.exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_family_map_core
        (F := U.obj (JJMath.Cohomology.RealConstantAddSheaf X))
        (K := Kbig)
        εBig hεBig hexact_zero_big hmono_big hexact_pos_big hacyclic
        (fun r : ℝ =>
          U.map (JJMath.Cohomology.realConstantSheafScalarEnd X r))
        (fun r : ℝ =>
          (U.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (JJMath.Cohomology.sheafifiedOpenRealSingularCochainSheafScalarEndConcrete
              X r))
        hscalarBig n with
    ⟨e, he⟩
  exact ⟨e, he⟩

/--
%%handwave
name:
  Lifted constant-sheaf cohomology agrees with ordinary constant-sheaf cohomology compatibly with scalars
statement:
  Let $X$ be a paracompact Hausdorff locally contractible space whose open
  subspaces are paracompact.  The cohomology of the universe lift of its
  ordinary constant real sheaf is additively equivalent to ordinary real
  constant-sheaf cohomology.  The equivalence intertwines the cohomology map
  induced by the lifted multiplication-by-$r$ endomorphism with multiplication
  by $r$ for every $r\in\mathbb R$.
proof:
  Compute both groups using the same sheafified singular-cochain resolution.
  The lifted resolution remains exact and flasque, hence acyclic.  Global
  sections commute naturally with universe lift, and exactness of universe
  lift identifies the homology of the lifted global-section complex with the
  ordinary homology.  Compose the two scalar-natural acyclic-resolution
  comparisons with this middle identification.
-/
theorem
    exists_sheafCompose_ulift_realConstantAddSheaf_cohomology_addEquiv_realConstantSheafCohomology_with_smul
    (X : TopCat.{m}) [T2Space X] [ParacompactSpace X]
    (hopen : ∀ V : TopologicalSpace.Opens X, ParacompactSpace V)
    (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify
      (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasGlobalSectionsFunctor
      (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasExt.{m}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})]
    [HasWeakSheafify
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasGlobalSectionsFunctor
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasSheafify
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasExt.{max v m}
      (Sheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})]
    (n : ℕ) :
    ∃ e :
      ((sheafCompose (Opens.grothendieckTopology X)
        AddCommGrpCat.uliftFunctor.{v, m}).obj
          (JJMath.Cohomology.RealConstantAddSheaf X)).H n ≃+
        JJMath.Cohomology.RealConstantSheafCohomology X n,
      ∀ (r : ℝ)
        (α :
          ((sheafCompose (Opens.grothendieckTopology X)
            AddCommGrpCat.uliftFunctor.{v, m}).obj
              (JJMath.Cohomology.RealConstantAddSheaf X)).H n),
        e (((CategoryTheory.Sheaf.functorH
              (Opens.grothendieckTopology X) n).map
              ((sheafCompose (Opens.grothendieckTopology X)
                AddCommGrpCat.uliftFunctor.{v, m}).map
                (JJMath.Cohomology.realConstantSheafScalarEnd X r))) α) =
          r • e α := by
  let J := Opens.grothendieckTopology X
  let U := sheafCompose J AddCommGrpCat.uliftFunctor.{v, m}
  let Γsmall := Sheaf.Γ J AddCommGrpCat.{m}
  let Γbig := Sheaf.Γ J AddCommGrpCat.{max v m}
  let UGrp := AddCommGrpCat.uliftFunctor.{v, m}
  let Ksmall := JJMath.Cohomology.realSingularCochainSheafComplex X
  let Kbig := (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj Ksmall
  let Lsmall :=
    (Γsmall.mapHomologicalComplex (ComplexShape.up ℕ)).obj Ksmall
  let Lbig :=
    (Γbig.mapHomologicalComplex (ComplexShape.up ℕ)).obj Kbig
  rcases
      exists_liftedRealSingularCochainSheafGlobalSectionsCohomology_addEquiv_with_map_smul
        X hopen hloc n with
    ⟨eBig, hBig⟩
  rcases
      JJMath.Cohomology.exists_realSingularCochainSheafGlobalSectionsCohomology_addEquiv_realConstantSheafCohomology_with_map_smul_of_open_paracompact
        X hopen hloc n with
    ⟨eSmall, hSmall⟩
  rcases
      exists_liftedRealSingularCochainGlobalSections_homology_iso_with_scalar
        X n with
    ⟨eGlobalIso, hGlobalIso⟩
  let eGlobal : Lbig.homology n ≃+ Lsmall.homology n :=
    eGlobalIso.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift
  let e := eBig.symm.trans (eGlobal.trans eSmall)
  refine ⟨e, ?_⟩
  intro r α
  let σ :=
    JJMath.Cohomology.sheafifiedOpenRealSingularCochainSheafScalarEndConcrete
      X r
  let σBig :=
    (Γbig.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map σ)
  let σSmall :=
    (Γsmall.mapHomologicalComplex (ComplexShape.up ℕ)).map σ
  have hBigInv :
      eBig.symm
          (((CategoryTheory.Sheaf.functorH J n).map
            (U.map
              (JJMath.Cohomology.realConstantSheafScalarEnd X r))) α) =
        (HomologicalComplex.homologyMap σBig n)
          (eBig.symm α) := by
    apply eBig.injective
    simpa using (hBig r (eBig.symm α)).symm
  have hGlobal :
      ∀ x : Lbig.homology n,
        eGlobal ((HomologicalComplex.homologyMap σBig n) x) =
          (HomologicalComplex.homologyMap σSmall n) (eGlobal x) := by
    intro x
    have hx :=
      ConcreteCategory.congr_hom (hGlobalIso r) x
    change
      eGlobalIso.hom ((HomologicalComplex.homologyMap σBig n) x) =
        UGrp.map (HomologicalComplex.homologyMap σSmall n)
          (eGlobalIso.hom x) at hx
    change
      (eGlobalIso.hom
        ((HomologicalComplex.homologyMap σBig n) x)).down =
        (HomologicalComplex.homologyMap σSmall n)
          (eGlobalIso.hom x).down
    rw [hx]
    rfl
  change
    e
        (((CategoryTheory.Sheaf.functorH J n).map
          (U.map
            (JJMath.Cohomology.realConstantSheafScalarEnd X r))) α) =
      r • e α
  simp only [e, AddEquiv.trans_apply]
  rw [hBigInv, hGlobal, hSmall]

/--
%%handwave
name:
  Smooth-universe and ordinary real constant-sheaf cohomology agree compatibly with scalars
statement:
  For every paracompact Hausdorff locally contractible space $X$ whose open
  subspaces are paracompact, and every $n\geq0$, the cohomology of the real
  constant sheaf formed in the smooth-form coefficient universe is additively
  equivalent to ordinary real constant-sheaf cohomology.  The equivalence
  intertwines multiplication by each $r\in\mathbb R$.
proof:
  First use [the scalar-compatible identification with the universe lift of the ordinary constant sheaf](lean:JJMath.Manifold.exists_realConstantSheafSmoothFormsUniverseCohomology_addEquiv_sheafCompose_ulift_realConstantAddSheaf_cohomology_with_map_smul).  Then use [the scalar-compatible invariance of constant-sheaf cohomology under universe lift](lean:JJMath.Manifold.exists_sheafCompose_ulift_realConstantAddSheaf_cohomology_addEquiv_realConstantSheafCohomology_with_smul), and compose the two equivalences.
-/
theorem
    exists_realConstantSheafSmoothFormsUniverseCohomology_addEquiv_realConstantSheafCohomology_with_smul
    (X : TopCat.{m}) [T2Space X] [ParacompactSpace X]
    (hopen : ∀ V : TopologicalSpace.Opens X, ParacompactSpace V)
    (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify
      (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasGlobalSectionsFunctor
      (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m}]
    [HasExt.{m}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{m})]
    [HasWeakSheafify
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasGlobalSectionsFunctor
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasSheafify
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}]
    [HasExt.{max v m}
      (Sheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{max v m})]
    (n : ℕ) :
    ∃ e :
      (realConstantAddSheafSmoothFormsUniverse X).H n ≃+
        JJMath.Cohomology.RealConstantSheafCohomology X n,
      ∀ (r : ℝ)
        (α : (realConstantAddSheafSmoothFormsUniverse X).H n),
        e (((CategoryTheory.Sheaf.functorH
            (Opens.grothendieckTopology X) n).map
              (realConstantAddSheafSmoothFormsUniverseScalarEnd X r)) α) =
          r • e α := by
  rcases
      exists_realConstantSheafSmoothFormsUniverseCohomology_addEquiv_sheafCompose_ulift_realConstantAddSheaf_cohomology_with_map_smul
        (X := X) n with
    ⟨eBigLift, hBigLift⟩
  rcases
      exists_sheafCompose_ulift_realConstantAddSheaf_cohomology_addEquiv_realConstantSheafCohomology_with_smul
        (X := X) hopen hloc n with
    ⟨eLiftSmall, hLiftSmall⟩
  refine ⟨eBigLift.trans eLiftSmall, ?_⟩
  intro r α
  rw [AddEquiv.trans_apply, hBigLift]
  exact hLiftSmall r (eBigLift α)

/--
%%handwave
name:
  De Rham cohomology computes smooth-universe constant-sheaf cohomology
statement:
  Let $M$ be a finite-dimensional Hausdorff sigma-compact smooth manifold
  without boundary.  For every $n\geq0$, there is an additive equivalence
  \[
    H_{\mathrm{dR}}^n(M;\mathbb R)
      \cong H^n(M;\underline{\mathbb R})
  \]
  in the coefficient universe of smooth forms, and it intertwines
  multiplication by every real scalar.
proof:
  The local Poincaré lemma makes the augmented sheaf de Rham complex exact.
  Smooth partitions of unity make every sheaf of smooth forms fine, and
  fine sheaves on a paracompact Hausdorff space are acyclic.  Apply the
  scalar-natural acyclic-resolution comparison, then compose it with the
  scalar-compatible identification of de Rham cohomology with the homology of
  the global smooth-form complex.
-/
theorem
    exists_deRhamCohomology_addEquiv_realConstantSheafSmoothFormsUniverseCohomology_with_smul
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    [T2Space M] [SigmaCompactSpace M]
    [HasSheafify
      (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}]
    [HasExt.{max v m}
      (Sheaf
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m})]
    (n : ℕ) :
    ∃ e :
      DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃+
        (realConstantAddSheafSmoothFormsUniverse
          (TopCat.of M : TopCat.{m})).H n,
      ∀ (r : ℝ)
        (α : DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n),
        e (r • α) =
          ((CategoryTheory.Sheaf.functorH
            (Opens.grothendieckTopology (TopCat.of M : TopCat.{m})) n).map
              (realConstantAddSheafSmoothFormsUniverseScalarEnd
                (TopCat.of M : TopCat.{m}) r)) (e α) := by
  letI : ParacompactSpace M :=
    smoothManifold_paracompactSpace_of_t2_sigmaCompact (M := M) Iℝ
  letI :
      PreservesFilteredColimitsOfSize.{m, m}
        (forget AddCommGrpCat.{max v m}) :=
    preservesFilteredColimitsOfSize_shrink
      (forget AddCommGrpCat.{max v m})
  let ε :=
    realConstantAddSheafToSmoothFormsAddSheaf (M := M) Iℝ
  have hε :
      ε ≫ (smoothFormsAddSheafCochainComplex (M := M) Iℝ).d 0 1 =
        0 :=
    realConstantAddSheafToSmoothFormsAddSheaf_comp_d (M := M) Iℝ
  have hexact_zero :
      ({ f := ε,
         g := (smoothFormsAddSheafCochainComplex (M := M) Iℝ).d 0 1,
         zero := hε } :
        ShortComplex
          (Sheaf
            (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
            AddCommGrpCat.{max v m})).Exact := by
    simpa [ε, smoothFormsAddSheafCochainComplex_d_succ] using
      realConstantAddSheaf_to_smoothFormsAddSheaf_exact
        (M := M) Iℝ
  have hmono :
      Mono ε := by
    dsimp [ε]
    exact
      realConstantAddSheafToSmoothFormsAddSheaf_mono
        (M := M) Iℝ
  have hlocal : DeRhamLocalPoincareBasis (M := M) Iℝ :=
    deRham_local_poincareBasis_boundarylessModel (M := M) Iℝ
  have hexact_pos :
      ∀ p : ℕ,
        (smoothFormsAddSheafCochainComplex (M := M) Iℝ).ExactAt
          (p + 1) :=
    fun p =>
      smoothFormsAddSheafCochainComplex_exactAt_succ_of_local_poincare
        (M := M) Iℝ hlocal p
  have hacyclic :
      ∀ p q : ℕ, 0 < q →
        Subsingleton ((smoothFormsAddSheaf (M := M) Iℝ p).H q) := by
    intro p q hq
    letI :
        TopCat.Sheaf.IsFine (X := TopCat.of M)
          (smoothFormsAddSheaf (M := M) Iℝ p) :=
      smoothFormsAddSheaf_isFine (M := M) Iℝ p
    exact
      TopCat.Sheaf.cohomology_subsingleton_of_isFine
        (X := TopCat.of M)
        (smoothFormsAddSheaf (M := M) Iℝ p) q hq
  rcases
      CategoryTheory.Sheaf.exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_family_map_core
        (F := realConstantAddSheafSmoothFormsUniverse
          (TopCat.of M : TopCat.{m}))
        (K := smoothFormsAddSheafCochainComplex (M := M) Iℝ)
        ε hε hexact_zero hmono hexact_pos hacyclic
        (fun r : ℝ =>
          realConstantAddSheafSmoothFormsUniverseScalarEnd
            (TopCat.of M : TopCat.{m}) r)
        (fun r : ℝ =>
          smoothFormsAddSheafCochainComplexScalarEnd (M := M) Iℝ r)
        (fun r =>
          by
            simpa [ε] using
              realConstantAddSheafToSmoothFormsAddSheaf_comp_scalarEnd
                (M := M) Iℝ r)
        n with
    ⟨eSheaf, hSheaf⟩
  rcases
      exists_deRhamCohomology_addEquiv_smoothFormsAddSheafGlobalSectionsCohomology_with_map_smul
        (M := M) Iℝ n with
    ⟨eDeRham, hDeRham⟩
  refine ⟨eDeRham.trans eSheaf, ?_⟩
  intro r α
  rw [AddEquiv.trans_apply, hDeRham]
  simpa using hSheaf r (eDeRham α)

/--
%%handwave
name:
  De Rham cohomology computes ordinary real constant-sheaf cohomology
statement:
  Let $M$ be a finite-dimensional Hausdorff sigma-compact smooth manifold
  without boundary.  For every $n\geq0$, there is an additive equivalence
  \[
    H_{\mathrm{dR}}^n(M;\mathbb R)
      \cong H^n(M;\underline{\mathbb R}),
  \]
  and it commutes with multiplication by every $r\in\mathbb R$.
proof:
  Compose [the scalar-compatible de Rham comparison in the smooth-form coefficient universe](lean:JJMath.Manifold.exists_deRhamCohomology_addEquiv_realConstantSheafSmoothFormsUniverseCohomology_with_smul) with [the scalar-compatible comparison from that universe to ordinary constant-sheaf cohomology](lean:JJMath.Manifold.exists_realConstantSheafSmoothFormsUniverseCohomology_addEquiv_realConstantSheafCohomology_with_smul).
-/
theorem
    exists_deRhamCohomology_addEquiv_realConstantSheafCohomology_with_smul
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    [T2Space M] [SigmaCompactSpace M]
    [HasSheafify
      (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{m}]
    [HasExt.{m}
      (Sheaf
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{m})]
    [HasSheafify
      (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m}]
    [HasExt.{max v m}
      (Sheaf
        (Opens.grothendieckTopology (TopCat.of M : TopCat.{m}))
        AddCommGrpCat.{max v m})]
    (n : ℕ) :
    ∃ e :
      DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃+
        JJMath.Cohomology.RealConstantSheafCohomology
          (TopCat.of M : TopCat.{m}) n,
      ∀ (r : ℝ)
        (α : DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n),
        e (r • α) =
          JJMath.Cohomology.realConstantSheafCohomologySMul
            (TopCat.of M : TopCat.{m}) n r (e α) := by
  letI : ParacompactSpace M :=
    smoothManifold_paracompactSpace_of_t2_sigmaCompact (M := M) Iℝ
  have hopen :
      ∀ U : TopologicalSpace.Opens M, ParacompactSpace U := by
    intro U
    exact smoothManifold_open_paracompactSpace (M := M) Iℝ U
  have hloc : LocallyContractibleSpace M :=
    smoothManifold_locallyContractibleSpace (M := M) Iℝ
  rcases
      exists_deRhamCohomology_addEquiv_realConstantSheafSmoothFormsUniverseCohomology_with_smul
        (M := M) Iℝ n with
    ⟨eDeRhamBig, hDeRhamBig⟩
  rcases
      exists_realConstantSheafSmoothFormsUniverseCohomology_addEquiv_realConstantSheafCohomology_with_smul.{v, m}
        (X := (TopCat.of M : TopCat.{m})) hopen hloc n with
    ⟨eBigSmall, hBigSmall⟩
  refine ⟨eDeRhamBig.trans eBigSmall, ?_⟩
  intro r α
  rw [AddEquiv.trans_apply, hDeRhamBig]
  exact hBigSmall r (eDeRhamBig α)











end

end Manifold
end JJMath
