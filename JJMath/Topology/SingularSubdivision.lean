import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.Convex.Contractible
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Topology.Sets.OpenCover

/-!
# Small singular chains and barycentric subdivision

This file contains the geometric part of the comparison between ordinary
singular cohomology and the cohomology of sheafified singular cochains.

For an open cover of a space, we first define the simplicial subset consisting
of singular simplices whose images lie in one member of the cover.  Its
simplicial chain complex is the complex of small singular chains.  The main
remaining theorem is that inclusion of small chains into all singular chains
is a chain-homotopy equivalence, proved by iterated barycentric subdivision.
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Simplicial
open TopologicalSpace

namespace stdSimplex

noncomputable section

/--
%%handwave
name:
  Affine map determined by vertices of a standard simplex
statement:
  If a point $v_i$ of the standard simplex $\Delta^J$ is specified for every
  vertex $i$ of $\Delta^I$, the associated affine map
  $A_v:\Delta^I\to\Delta^J$ is
  $A_v(x)_j=\sum_{i\in I}x_i(v_i)_j$.
-/
noncomputable def affineMap {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (x : stdSimplex ℝ I) :
    stdSimplex ℝ J := by
  classical
  refine ⟨fun j => ∑ i, x i * v i j, ?_, ?_⟩
  · intro j
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (stdSimplex.zero_le x i) (stdSimplex.zero_le (v i) j)
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, stdSimplex.sum_eq_one]
    simpa using stdSimplex.sum_eq_one x

/--
%%handwave
name:
  Continuity of the affine map determined by simplex vertices
statement:
  The affine map $A_v:\Delta^I\to\Delta^J$ determined by finitely many
  vertices is continuous.
proof:
  Each coordinate of $A_v$ is a finite sum of the continuous coordinate
  functions $x_i$ multiplied by constants $(v_i)_j$.
-/
theorem continuous_affineMap {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) :
    Continuous (affineMap v) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun j => continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

/--
%%handwave
name:
  Values of the affine simplex map at vertices
statement:
  For every vertex $i$ of $\Delta^I$, the affine map determined by
  $(v_i)_{i\in I}$ satisfies $A_v(e_i)=v_i$.
proof:
  At the vertex $e_i$, all barycentric coordinates except the $i$th are
  zero and the $i$th coordinate is one, so the defining sum reduces to
  $v_i$.
-/
theorem affineMap_vertex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (v : I → stdSimplex ℝ J) (i : I) :
    affineMap v (vertex i) = v i := by
  apply Subtype.ext
  funext j
  change (∑ k, (Pi.single i (1 : ℝ) : I → ℝ) k * (v k) j) = (v i) j
  simp [Pi.single_apply]

/--
%%handwave
name:
  Affine simplex maps commute with maps of vertex sets
statement:
  If $f:I\to J$, $v_j\in\Delta^K$, and $x\in\Delta^I$, then applying the
  simplex map induced by $f$ before taking the affine combination with
  vertices $(v_j)$ gives the affine combination with vertices
  $(v_{f(i)})$: $A_v(f_*x)=A_{v\circ f}(x)$.
proof:
  Expand both affine combinations coordinatewise.  The induced simplex map
  sums the coordinates of $x$ over every fiber of $f$; regrouping the finite
  double sum by those fibers gives the asserted identity.
-/
theorem affineMap_map {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J) (v : J → stdSimplex ℝ K) (x : stdSimplex ℝ I) :
    affineMap v (stdSimplex.map f x) = affineMap (v ∘ f) x := by
  classical
  apply Subtype.ext
  funext k
  simp only [affineMap, stdSimplex.map_coe, Function.comp_apply]
  simp_rw [FunOnFinite.linearMap_apply_apply]
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f (fun i => x i * v (f i) k)]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [hi.2]

/--
%%handwave
name:
  Maps of vertex sets commute with affine simplex combinations
statement:
  If $f:J\to K$, $v_i\in\Delta^J$, and $x\in\Delta^I$, then mapping the
  affine combination of the $v_i$ along $f$ equals the affine combination
  of their images:
  $f_*(A_v(x))=A_{f_*\circ v}(x)$.
proof:
  Expand the two sides coordinatewise.  Distribute multiplication over each
  finite fiber sum and interchange the two finite sums.
-/
theorem map_affineMap
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : J → K) (v : I → stdSimplex ℝ J)
    (x : stdSimplex ℝ I) :
    stdSimplex.map f (affineMap v x) =
      affineMap (stdSimplex.map f ∘ v) x := by
  classical
  apply Subtype.ext
  funext k
  simp only [affineMap, stdSimplex.map_coe, Function.comp_apply]
  change
    (FunOnFinite.linearMap ℝ ℝ f)
        (fun j => ∑ i, x i * v i j) k =
      ∑ i, x i *
        (FunOnFinite.linearMap ℝ ℝ f) (v i) k
  simp_rw [FunOnFinite.linearMap_apply_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/--
%%handwave
name:
  Initial-face barycenter associated to an ordering
statement:
  Let $p$ order the vertices of $\Delta^n$.  For
  $0\leq k\leq n$, the initial-face barycenter $b_{p,k}$ has coordinate
  $1/(k+1)$ at the vertices $p(0),\ldots,p(k)$ and coordinate zero at all
  other vertices.
-/
noncomputable def permutationInitialBarycenter {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    stdSimplex ℝ (Fin (n + 1)) := by
  classical
  let c : ℝ := ((k.val + 1 : ℕ) : ℝ)⁻¹
  refine ⟨fun j => if p.symm j ≤ k then c else 0, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  · have hreindex :
        (∑ j : Fin (n + 1), if p.symm j ≤ k then c else 0) =
          ∑ i : Fin (n + 1), if i ≤ k then c else 0 := by
      simpa using
        (Equiv.sum_comp p.symm
          (fun i : Fin (n + 1) => if i ≤ k then c else 0))
    rw [hreindex, ← Finset.sum_filter]
    have hfilter :
        Finset.univ.filter (fun i : Fin (n + 1) => i ≤ k) =
          Finset.Iic k := by
      ext i
      simp
    rw [hfilter, Finset.sum_const, Fin.card_Iic]
    simp only [nsmul_eq_mul, c, Nat.cast_add, Nat.cast_one]
    exact mul_inv_cancel₀ (by positivity)

/--
%%handwave
name:
  Affine simplex in the barycentric subdivision
statement:
  Every permutation $p$ of the vertices of $\Delta^n$ determines the affine
  simplex $\beta_p:\Delta^n\to\Delta^n$ that sends its $k$th vertex to the
  barycenter of the face spanned by $p(0),\ldots,p(k)$.
-/
noncomputable def barycentricSubdivisionMap {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) :
    stdSimplex ℝ (Fin (n + 1)) → stdSimplex ℝ (Fin (n + 1)) :=
  affineMap (permutationInitialBarycenter p)

/--
%%handwave
name:
  Continuity of a barycentric subdivision simplex
statement:
  For every ordering $p$ of the vertices of $\Delta^n$, the associated
  affine simplex $\beta_p:\Delta^n\to\Delta^n$ is continuous.
proof:
  This is the continuity of the affine map determined by the sequence of
  initial-face barycenters.
-/
theorem continuous_barycentricSubdivisionMap {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) :
    Continuous (barycentricSubdivisionMap p) :=
  continuous_affineMap _

/--
%%handwave
name:
  Vertices of a barycentric subdivision simplex
statement:
  The $k$th vertex of the barycentric subdivision simplex associated to $p$
  is the barycenter of the face spanned by
  $p(0),\ldots,p(k)$.
proof:
  An affine map determined by its vertex values sends the $k$th standard
  vertex to the prescribed $k$th initial-face barycenter.
-/
theorem barycentricSubdivisionMap_vertex {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    barycentricSubdivisionMap p (vertex k) =
      permutationInitialBarycenter p k :=
  affineMap_vertex _ _

/--
%%handwave
name:
  Adjacent swaps preserve the barycenters on an omitted internal face
statement:
  Let $j$ and $j+1$ be adjacent positions in an ordering $p$ of the vertices
  of $\Delta^{N+1}$.  After the $j$th vertex of the associated barycentric
  simplex is omitted, swapping positions $j$ and $j+1$ in $p$ leaves every
  remaining initial-face barycenter unchanged.
proof:
  The only initial segment changed by swapping adjacent positions $j$ and
  $j+1$ is the segment ending at $j$.  The face that omits position $j$
  never uses that initial segment, so the coordinatewise membership
  conditions defining all its barycenters agree.
-/
theorem permutationInitialBarycenter_mul_swap_succAbove
    {N : ℕ} (p : Equiv.Perm (Fin (N + 2))) (j : Fin (N + 1))
    (k : Fin (N + 1)) :
    permutationInitialBarycenter
        (p * Equiv.swap j.castSucc j.succ)
        (j.castSucc.succAbove k) =
      permutationInitialBarycenter p (j.castSucc.succAbove k) := by
  classical
  apply Subtype.ext
  funext x
  simp only [permutationInitialBarycenter]
  congr 1
  change
    (Equiv.swap j.castSucc j.succ (p.symm x) ≤
        j.castSucc.succAbove k) =
      (p.symm x ≤ j.castSucc.succAbove k)
  apply propext
  have ht :
      j.castSucc.succAbove k ≠ j.castSucc :=
    Fin.succAbove_ne _ _
  by_cases hz₀ : p.symm x = j.castSucc
  · rw [hz₀, Equiv.swap_apply_left]
    change
      j.val + 1 ≤ (j.castSucc.succAbove k).val ↔
        j.val ≤ (j.castSucc.succAbove k).val
    have htval : (j.castSucc.succAbove k).val ≠ j.val := by
      intro h
      apply ht
      exact Fin.ext h
    omega
  by_cases hz₁ : p.symm x = j.succ
  · rw [hz₁, Equiv.swap_apply_right]
    change
      j.val ≤ (j.castSucc.succAbove k).val ↔
        j.val + 1 ≤ (j.castSucc.succAbove k).val
    have htval : (j.castSucc.succAbove k).val ≠ j.val := by
      intro h
      apply ht
      exact Fin.ext h
    omega
  rw [Equiv.swap_apply_of_ne_of_ne hz₀ hz₁]

end

end stdSimplex

namespace JJMath
namespace Cohomology

noncomputable section

universe v

/--
%%handwave
name:
  Real coefficient module for singular chains
statement:
  The coefficient object for real singular chains of a space in universe
  $\mathcal U_v$ is the real line, transported to the corresponding universe
  of real modules.
-/
noncomputable abbrev realSingularChainCoefficient :
    ModuleCat.{v} ℝ :=
  (ModuleCat.uliftFunctor.{v, 0} ℝ).obj (ModuleCat.of ℝ ℝ)

/--
%%handwave
name:
  Real singular-chain complex
statement:
  The real singular-chain complex $C_\bullet(X;\mathbb R)$ is the simplicial
  chain complex freely generated in degree $n$ by continuous maps
  $\Delta^n\to X$.
-/
noncomputable abbrev realSingularChains (X : TopCat.{v}) :
    ChainComplex (ModuleCat.{v} ℝ) ℕ :=
  (TopCat.toSSet.obj X).chainComplex realSingularChainCoefficient

/--
%%handwave
name:
  Real singular-chain functor
statement:
  The assignment $X\mapsto C_\bullet(X;\mathbb R)$ and the induced maps on
  singular chains form a functor from topological spaces to nonnegative
  chain complexes of real modules.
-/
noncomputable abbrev realSingularChainFunctor :
    TopCat.{v} ⥤ ChainComplex (ModuleCat.{v} ℝ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor
    (ModuleCat.{v} ℝ)).obj realSingularChainCoefficient)

/--
%%handwave
name:
  Singular chains preserve homotopy equivalences
statement:
  A homotopy equivalence $X\simeq_hY$ induces a chain-homotopy equivalence
  $C_\bullet(X;\mathbb R)\simeq_h C_\bullet(Y;\mathbb R)$.
proof:
  Apply the singular-chain functor to the forward and inverse maps.  The two
  homotopies in the homotopy equivalence induce chain homotopies from the two
  composites to the identity chain maps.
-/
noncomputable def singularChainsHomotopyEquivOfSpace
    {X Y : TopCat.{v}}
    (e : ContinuousMap.HomotopyEquiv (X : Type v) (Y : Type v)) :
    HomotopyEquiv (realSingularChains X) (realSingularChains Y) := by
  let F :=
    ((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{v} ℝ)).obj realSingularChainCoefficient)
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  refine
    { hom := F.map f
      inv := F.map g
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · exact
      (Homotopy.ofEq (F.map_comp f g).symm).trans
        ((TopCat.Homotopy.singularChainComplexFunctorObjMap
            e.left_inv.some realSingularChainCoefficient).trans
          (Homotopy.ofEq (F.map_id X)))
  · exact
      (Homotopy.ofEq (F.map_comp g f).symm).trans
        ((TopCat.Homotopy.singularChainComplexFunctorObjMap
            e.right_inv.some realSingularChainCoefficient).trans
          (Homotopy.ofEq (F.map_id Y)))

/--
%%handwave
name:
  Singular chains of a standard simplex contract to degree zero
statement:
  For every $n$, the real singular-chain complex of the universe lift of
  $\Delta^n$ is chain-homotopy equivalent to a complex concentrated in
  degree zero.
proof:
  The standard simplex is convex and nonempty, hence contractible.  Its
  singular chains are therefore homotopy equivalent to the singular chains
  of a point.  The singular simplicial set of a point is the terminal
  simplicial set, hence isomorphic to $\Delta[0]$.  The standard extra
  degeneracy contracts the alternating face complex of $\Delta[0]$ to its
  augmentation in degree zero.
-/
theorem standardSimplexRealSingularChains_homotopyEquiv_singleZero
    (n : ℕ) :
    ∃ B : ModuleCat.{v} ℝ,
      Nonempty
        (HomotopyEquiv
          (realSingularChains
            (TopCat.of
              (ULift.{v} (stdSimplex ℝ (Fin (n + 1)))) :
              TopCat.{v}))
          ((ChainComplex.single₀ (ModuleCat.{v} ℝ)).obj B)) := by
  letI : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨stdSimplex.vertex 0, (stdSimplex.vertex 0).property⟩
  letI :
      ContractibleSpace
        (ULift.{v} (stdSimplex ℝ (Fin (n + 1)))) :=
    Homeomorph.ulift.contractibleSpace
  rcases
      ContractibleSpace.hequiv
        (ULift.{v} (stdSimplex ℝ (Fin (n + 1)))) PUnit with
    ⟨e⟩
  let pointIsTerminal :
      IsTerminal
        (TopCat.toSSet.obj (TopCat.of PUnit : TopCat.{v})) := by
    exact
      isLimitChangeEmptyCone _
        (isLimitOfPreserves TopCat.toSSet TopCat.isTerminalPUnit)
        _ (Iso.refl _)
  let pointIsoDeltaZero :
      TopCat.toSSet.obj (TopCat.of PUnit : TopCat.{v}) ≅
        (Δ[0] : SSet.{v}) :=
    pointIsTerminal.uniqueUpToIso
      SSet.stdSimplex.isTerminalObj₀
  let pointChainsIsoDeltaZero :
      realSingularChains (TopCat.of PUnit : TopCat.{v}) ≅
        (Δ[0] : SSet.{v}).chainComplex
          realSingularChainCoefficient :=
    ((SSet.chainComplexFunctor (ModuleCat.{v} ℝ)).obj
      realSingularChainCoefficient).mapIso pointIsoDeltaZero
  let ed :=
    ((SSet.Augmented.StandardSimplex.extraDegeneracy.{v}
      ⦋0⦌).map (sigmaConst.obj realSingularChainCoefficient))
  let B : ModuleCat.{v} ℝ :=
    SimplicialObject.Augmented.point.obj
      (((SimplicialObject.Augmented.whiskering
        (Type v) (ModuleCat.{v} ℝ)).obj
          (sigmaConst.obj realSingularChainCoefficient)).obj
        (SSet.Augmented.stdSimplex.obj ⦋0⦌))
  have e₀ :
      HomotopyEquiv
        ((Δ[0] : SSet.{v}).chainComplex
          realSingularChainCoefficient)
        ((ChainComplex.single₀ (ModuleCat.{v} ℝ)).obj B) := by
    simpa only [SSet.chainComplex, SSet.chainComplexFunctor] using
      ed.homotopyEquiv
  exact
    ⟨B,
      ⟨(singularChainsHomotopyEquivOfSpace e).trans
        ((HomotopyEquiv.ofIso pointChainsIsoDeltaZero).trans e₀)⟩⟩

/--
%%handwave
name:
  Positive cycles bound in a complex contracted to degree zero
statement:
  Let $K_\bullet$ be chain-homotopy equivalent to a complex concentrated in
  degree zero.  If $z:A\to K_{m+1}$ satisfies
  $z\,\partial_{m+1}=0$, then there is
  $w:A\to K_{m+2}$ with $w\,\partial_{m+2}=z$.
proof:
  Write the homotopy from the forward-inverse composite to the identity in
  degree $m+1$.  The forward map has zero component in that positive degree,
  while the term involving the outgoing differential vanishes on $z$.
  The negative of the remaining homotopy component is the required lift.
-/
theorem chainComplex_exists_boundary_of_homotopyEquiv_singleZero
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    (K : ChainComplex C ℕ) (B A : C)
    (e :
      HomotopyEquiv K
        ((ChainComplex.single₀ C).obj B))
    (m : ℕ) (z : A ⟶ K.X (m + 1))
    (hz : z ≫ K.d (m + 1) m = 0) :
    ∃ w : A ⟶ K.X (m + 2),
      w ≫ K.d (m + 2) (m + 1) = z := by
  let h := e.homotopyHomInvId
  refine ⟨-(z ≫ h.hom (m + 1) (m + 2)), ?_⟩
  have hc :=
    congrArg (fun q => z ≫ q) (h.comm (m + 1))
  rw [Homotopy.dNext_succ_chainComplex,
    Homotopy.prevD_chainComplex] at hc
  have hehom : e.hom.f (m + 1) = 0 := by
    apply
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0 B (m + 1) (by omega)).eq_of_tgt
  rw [HomologicalComplex.comp_f, hehom, zero_comp] at hc
  dsimp only at hc
  rw [Preadditive.comp_add, Preadditive.comp_add] at hc
  rw [← Category.assoc, hz, zero_comp, zero_add] at hc
  rw [Preadditive.neg_comp]
  apply (neg_eq_iff_add_eq_zero).2
  simpa using hc.symm

/--
%%handwave
name:
  Universe-lifted standard simplex
statement:
  The space $\widetilde{\Delta}^n$ is the universe lift of the standard
  topological simplex $\Delta^n$.
-/
noncomputable abbrev liftedStandardSimplex (n : ℕ) : TopCat.{v} :=
  TopCat.of (ULift.{v} (stdSimplex ℝ (Fin (n + 1))))

/--
%%handwave
name:
  Fundamental singular simplex of a lifted standard simplex
statement:
  The fundamental singular $n$-simplex of
  $\widetilde{\Delta}^n$ is the continuous map
  $\Delta^n\to\widetilde{\Delta}^n$ given by the inverse of the universe
  lifting homeomorphism.
-/
noncomputable def liftedStandardSimplexFundamentalSimplex (n : ℕ) :
    TopCat.toSSet.obj (liftedStandardSimplex n : TopCat.{v}) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv (liftedStandardSimplex n : TopCat.{v}) _).symm
    ⟨Homeomorph.ulift.symm, Homeomorph.ulift.symm.continuous⟩

/--
%%handwave
name:
  Map represented by a singular simplex
statement:
  Every singular $n$-simplex $\sigma:\Delta^n\to X$ determines a
  continuous map $\widetilde{\Delta}^n\to X$ by composing $\sigma$ with
  the universe-lifting homeomorphism.
-/
noncomputable def singularSimplexLiftedStandardMap
    (X : TopCat.{v}) (n : ℕ) (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (liftedStandardSimplex n : TopCat.{v}) ⟶ X :=
  TopCat.ofHom ((TopCat.toSSetObjEquiv X _ σ).comp
    ⟨Homeomorph.ulift, Homeomorph.ulift.continuous⟩)

/--
%%handwave
name:
  Evaluation of the represented map on the fundamental simplex
statement:
  If $\sigma:\Delta^n\to X$ is a singular simplex, then the induced map
  $\widetilde{\Delta}^n\to X$ sends the fundamental singular simplex of
  $\widetilde{\Delta}^n$ to $\sigma$.
proof:
  Under the equivalence between singular simplices and continuous maps from
  the standard simplex, the two universe-lifting homeomorphisms cancel.
-/
theorem singularSimplexLiftedStandardMap_fundamental
    (X : TopCat.{v}) (n : ℕ) (σ : TopCat.toSSet.obj X _⦋n⦌) :
    ((TopCat.toSSet.map (singularSimplexLiftedStandardMap X n σ)).app _)
      (liftedStandardSimplexFundamentalSimplex n) = σ := by
  apply (TopCat.toSSetObjEquiv X _).injective
  rw [show TopCat.toSSetObjEquiv X _
      (((TopCat.toSSet.map (singularSimplexLiftedStandardMap X n σ)).app _)
        (liftedStandardSimplexFundamentalSimplex n)) =
      (singularSimplexLiftedStandardMap X n σ).hom.comp
        (TopCat.toSSetObjEquiv (liftedStandardSimplex n : TopCat.{v}) _
          (liftedStandardSimplexFundamentalSimplex n)) by
    ext x
    rfl]
  dsimp [singularSimplexLiftedStandardMap,
    liftedStandardSimplexFundamentalSimplex]
  ext x
  rfl

/--
%%handwave
name:
  Naturality of the map represented by a singular simplex
statement:
  If $\sigma:\Delta^n\to X$ is a singular simplex and $f:X\to Y$ is
  continuous, then the map represented by $f\circ\sigma$ is the composite
  of the map represented by $\sigma$ with $f$.
proof:
  Both sides are the same composite of the universe-lifting homeomorphism,
  $\sigma$, and $f$.
-/
theorem singularSimplexLiftedStandardMap_natural
    {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    singularSimplexLiftedStandardMap X n σ ≫ f =
      singularSimplexLiftedStandardMap Y n
        (((TopCat.toSSet.map f).app _) σ) := by
  ext x
  change f ((TopCat.toSSetObjEquiv X _ σ) x.down) =
    (TopCat.toSSetObjEquiv Y _ (((TopCat.toSSet.map f).app _) σ)) x.down
  congr 1

/--
%%handwave
name:
  Universal degree of a subdivision prism
statement:
  A universal prism operator in degree $n$ is a singular $(n+1)$-chain in
  $\widetilde{\Delta}^n$, with coefficients in $\mathbb R$.
-/
structure SubdivisionPrismDegree (n : ℕ) where
  universal : realSingularChainCoefficient ⟶
    (realSingularChains (liftedStandardSimplex n : TopCat.{v})).X (n + 1)

/--
%%handwave
name:
  Prism operator induced by a universal simplex chain
statement:
  A universal prism chain in degree $n$ induces, for every space $X$, a
  linear map $C_n(X;\mathbb R)\to C_{n+1}(X;\mathbb R)$ by sending a
  generator $\sigma$ to the image of the universal chain under the
  represented map $\widetilde{\Delta}^n\to X$.
-/
noncomputable def SubdivisionPrismDegree.map {n : ℕ}
    (T : SubdivisionPrismDegree n) (X : TopCat.{v}) :
    (realSingularChains X).X n ⟶ (realSingularChains X).X (n + 1) :=
  Sigma.desc fun σ => T.universal ≫
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{v} ℝ)).obj
      realSingularChainCoefficient).map
      (singularSimplexLiftedStandardMap X n σ)).f (n + 1)

/--
%%handwave
name:
  Formula for a universal prism operator on generators
statement:
  For a singular $n$-simplex $\sigma$, the induced prism operator sends
  $[\sigma]$ to the pushforward of its universal $(n+1)$-chain along the
  map represented by $\sigma$.
proof:
  This is the direct-sum universal-property equation defining the induced
  linear map.
-/
theorem SubdivisionPrismDegree.generator_map {n : ℕ}
    (T : SubdivisionPrismDegree n) (X : TopCat.{v})
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient) σ ≫ T.map X =
      T.universal ≫
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{v} ℝ)).obj
          realSingularChainCoefficient).map
          (singularSimplexLiftedStandardMap X n σ)).f (n + 1) := by
  apply Sigma.ι_desc

/--
%%handwave
name:
  Naturality of a universal prism operator
statement:
  For every continuous map $f:X\to Y$, the square formed by
  $C_n(f)$, $C_{n+1}(f)$, and the prism operators induced by one universal
  degree commutes.
proof:
  Check the equation on a generating simplex.  The represented map of its
  image under $f$ is the composite of its represented map with $f$, and
  singular chains are functorial.
-/
theorem SubdivisionPrismDegree.map_natural {n : ℕ}
    (T : SubdivisionPrismDegree n) {X Y : TopCat.{v}} (f : X ⟶ Y) :
    T.map X ≫
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{v} ℝ)).obj
          realSingularChainCoefficient).map f).f (n + 1) =
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{v} ℝ)).obj
          realSingularChainCoefficient).map f).f n ≫ T.map Y := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{v} ℝ)).obj
    realSingularChainCoefficient)
  apply SSet.chainComplex_hom_ext
  intro σ
  have hgen :
      (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫ (F.map f).f n =
      (TopCat.toSSet.obj Y).ιChainComplex
        (R := realSingularChainCoefficient)
        (((TopCat.toSSet.map f).app _) σ) := by
    exact SSet.ι_chainComplexMap_f
      (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map f) realSingularChainCoefficient σ
  calc
    (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫
        (T.map X ≫ (F.map f).f (n + 1)) =
      (T.universal ≫
          (F.map (singularSimplexLiftedStandardMap X n σ)).f (n + 1)) ≫
        (F.map f).f (n + 1) := by
          rw [← Category.assoc, T.generator_map]
          rfl
    _ = T.universal ≫
        (F.map (singularSimplexLiftedStandardMap X n σ ≫ f)).f (n + 1) := by
      rw [Category.assoc]
      congr 1
      exact (congrArg (fun q => q.f (n + 1))
        (F.map_comp (singularSimplexLiftedStandardMap X n σ) f)).symm
    _ = T.universal ≫
        (F.map (singularSimplexLiftedStandardMap Y n
          (((TopCat.toSSet.map f).app _) σ))).f (n + 1) := by
      rw [singularSimplexLiftedStandardMap_natural]
    _ = (TopCat.toSSet.obj Y).ιChainComplex
          (R := realSingularChainCoefficient)
          (((TopCat.toSSet.map f).app _) σ) ≫ T.map Y := by
      rw [T.generator_map]
    _ = (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫
        ((F.map f).f n ≫ T.map Y) := by
      rw [← hgen]
      exact Category.assoc _ _ _

/--
%%handwave
name:
  A barycentrically subdivided singular simplex
statement:
  If $\sigma:\Delta^n\to X$ is a singular simplex and $p$ is a permutation
  of its vertices, the corresponding simplex in the barycentric subdivision
  is the composite $\sigma\circ\beta_p:\Delta^n\to X$.
-/
noncomputable def barycentricSubdivisionSingularSimplex
    (X : TopCat.{v}) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌)
    (p : Equiv.Perm (Fin (n + 1))) :
    TopCat.toSSet.obj X _⦋n⦌ :=
  (TopCat.toSSetObjEquiv X _).symm
    ((TopCat.toSSetObjEquiv X _ σ).comp
      ⟨stdSimplex.barycentricSubdivisionMap p,
        stdSimplex.continuous_barycentricSubdivisionMap p⟩)

/--
%%handwave
name:
  Naturality of a barycentrically subdivided singular simplex
statement:
  For every continuous map $f:X\to Y$, the image under $f$ of the
  barycentric subsimplex of $\sigma$ indexed by $p$ is the barycentric
  subsimplex indexed by $p$ of the image of $\sigma$.
proof:
  Both singular simplices are the composite
  $\Delta^n\xrightarrow{\beta_p}\Delta^n\xrightarrow{\sigma}X
  \xrightarrow{f}Y$.
-/
theorem barycentricSubdivisionSingularSimplex_natural
    {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌)
    (p : Equiv.Perm (Fin (n + 1))) :
    ((TopCat.toSSet.map f).app _)
        (barycentricSubdivisionSingularSimplex X n σ p) =
      barycentricSubdivisionSingularSimplex Y n
        (((TopCat.toSSet.map f).app _) σ) p := by
  apply (TopCat.toSSetObjEquiv Y _).injective
  ext x
  rfl

/--
%%handwave
name:
  Paired internal faces of barycentric singular simplices
statement:
  For an $(n+1)$-simplex $\sigma$, an ordering $p$, and
  $0\leq j\leq n$, the $j$th face of the barycentric simplex indexed by $p$
  equals the $j$th face of the simplex indexed by the ordering obtained by
  swapping positions $j$ and $j+1$.
proof:
  Precomposition with the $j$th face map omits the $j$th barycenter.  The
  adjacent-swap barycenter identity shows that all remaining vertices of the
  two affine maps agree, hence the two singular simplices agree.
-/
theorem barycentricSubdivisionSingularSimplex_delta_mul_swap
    (X : TopCat.{v}) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n + 1⦌)
    (p : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 1)) :
    (TopCat.toSSet.obj X).δ j.castSucc
        (barycentricSubdivisionSingularSimplex X (n + 1) σ p) =
      (TopCat.toSSet.obj X).δ j.castSucc
        (barycentricSubdivisionSingularSimplex X (n + 1) σ
          (p * Equiv.swap j.castSucc j.succ)) := by
  apply (TopCat.toSSetObjEquiv X _).injective
  ext z
  simp only [TopCat.toSSetObjEquiv_δ_apply]
  change
    (TopCat.toSSetObjEquiv X _ σ)
        (stdSimplex.barycentricSubdivisionMap p
          (stdSimplex.map j.castSucc.succAbove z)) =
      (TopCat.toSSetObjEquiv X _ σ)
        (stdSimplex.barycentricSubdivisionMap
          (p * Equiv.swap j.castSucc j.succ)
          (stdSimplex.map j.castSucc.succAbove z))
  rw [stdSimplex.barycentricSubdivisionMap, stdSimplex.affineMap_map]
  rw [stdSimplex.barycentricSubdivisionMap, stdSimplex.affineMap_map]
  congr 2
  funext k
  exact
    (stdSimplex.permutationInitialBarycenter_mul_swap_succAbove
      p j k).symm

/--
%%handwave
name:
  Ordering a simplex by a prescribed last vertex
statement:
  Given a vertex $i$ of $\Delta^{n+1}$ and an ordering $q$ of the other
  $n+1$ vertices, this permutation orders those other vertices as
  $i\uparrow q(0),\ldots,i\uparrow q(n)$ and places $i$ last.
-/
noncomputable def lastVertexOrderedPermutation {n : ℕ}
    (i : Fin (n + 2)) (q : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) :=
  i.cycleRange.symm *
    Equiv.Perm.decomposeFin.symm (0, q) *
      (Fin.last (n + 1)).cycleRange

/--
%%handwave
name:
  Last value of an ordering with prescribed last vertex
statement:
  The ordering of the vertices of $\Delta^{n+1}$ with prescribed last
  vertex $i$ sends its final position to $i$.
proof:
  The final cyclic rotation sends the last position to zero, the lifted
  ordering fixes zero, and the inverse cyclic rotation at $i$ sends zero to
  $i$.
-/
theorem lastVertexOrderedPermutation_last {n : ℕ} (i : Fin (n + 2))
    (q : Equiv.Perm (Fin (n + 1))) :
    lastVertexOrderedPermutation i q (Fin.last (n + 1)) = i := by
  simp [lastVertexOrderedPermutation]

/--
%%handwave
name:
  Nonfinal values of an ordering with prescribed last vertex
statement:
  At a nonfinal position $k$, the ordering with prescribed last vertex $i$
  takes the value $i\uparrow q(k)$, the image of $q(k)$ under the
  order-preserving inclusion that omits $i$.
proof:
  Evaluate the two cyclic rotations and the lifted permutation in the
  defining composite.
-/
theorem lastVertexOrderedPermutation_castSucc {n : ℕ} (i : Fin (n + 2))
    (q : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    lastVertexOrderedPermutation i q k.castSucc =
      i.succAbove (q k) := by
  simp [lastVertexOrderedPermutation]

/--
%%handwave
name:
  Initial barycenters for an ordering with prescribed last vertex
statement:
  Before the final position, the initial-face barycenter for the ordering
  with last vertex $i$ is the image under the face inclusion omitting $i$ of
  the corresponding initial-face barycenter for the ordering $q$.
proof:
  At the omitted coordinate $i$, both sides are zero.  Every other
  coordinate is uniquely $i\uparrow z$; the inverse ordering places it at
  the same nonfinal position as $z$ under $q$, so the two coordinate
  formulas agree.
-/
theorem lastVertexOrderedPermutation_barycenter_castSucc
    {n : ℕ} (i : Fin (n + 2))
    (q : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    stdSimplex.permutationInitialBarycenter
        (lastVertexOrderedPermutation i q) k.castSucc =
      stdSimplex.map i.succAbove
        (stdSimplex.permutationInitialBarycenter q k) := by
  classical
  apply Subtype.ext
  funext y
  simp only [stdSimplex.permutationInitialBarycenter]
  by_cases hy : y = i
  · subst y
    have hp :
        (lastVertexOrderedPermutation i q).symm i =
          Fin.last (n + 1) := by
      apply (lastVertexOrderedPermutation i q).injective
      simp [lastVertexOrderedPermutation]
    rw [hp]
    simp [stdSimplex.map, FunOnFinite.linearMap_apply_apply,
      Fin.succAbove_ne]
  · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hy
    subst y
    have hp :
        (lastVertexOrderedPermutation i q).symm (i.succAbove z) =
          (q.symm z).castSucc := by
      apply (lastVertexOrderedPermutation i q).injective
      simp [lastVertexOrderedPermutation]
    rw [hp]
    simp only [Fin.val_castSucc, Fin.castSucc_le_castSucc_iff,
      Nat.cast_add, Nat.cast_one]
    change
      (if q.symm z ≤ k then ((k.val : ℝ) + 1)⁻¹ else 0) =
        (FunOnFinite.linearMap ℝ ℝ i.succAbove)
          (fun x => if q.symm x ≤ k then ((k.val : ℝ) + 1)⁻¹ else 0)
          (i.succAbove z)
    rw [FunOnFinite.linearMap_apply_apply]
    change
      (if q.symm z ≤ k then ((k.val : ℝ) + 1)⁻¹ else 0) =
        ∑ x ∈ Finset.univ.filter
            (fun x => i.succAbove x = i.succAbove z),
          if q.symm x ≤ k then ((k.val : ℝ) + 1)⁻¹ else 0
    have hfilter :
        Finset.univ.filter
            (fun x => i.succAbove x = i.succAbove z) =
          {z} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Fin.succAbove_right_inj]
    rw [hfilter]
    simp

/--
%%handwave
name:
  Sign of an ordering with prescribed last vertex
statement:
  If $p$ lists the vertices other than $i$ in the order $q$ and places $i$
  last, then
  $\operatorname{sign}(p)=(-1)^i\operatorname{sign}(q)(-1)^{n+1}$.
proof:
  Use multiplicativity of the sign in the three-factor construction.  The
  two cyclic rotations have signs $(-1)^i$ and $(-1)^{n+1}$, while the
  lifted ordering has sign $\operatorname{sign}(q)$.
-/
theorem lastVertexOrderedPermutation_sign {n : ℕ} (i : Fin (n + 2))
    (q : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm.sign (lastVertexOrderedPermutation i q) =
      (-1) ^ i.val * Equiv.Perm.sign q * (-1) ^ (n + 1) := by
  simp [lastVertexOrderedPermutation, Equiv.Perm.sign_mul]

/--
%%handwave
name:
  Final face of a barycentric simplex
statement:
  Let an ordering of $\Delta^{n+1}$ list the vertices other than $i$ in
  the order $q$ and put $i$ last.  The final face of its barycentric simplex
  is the barycentric simplex indexed by $q$ in the $i$th face of the
  original simplex.
proof:
  Omitting the final barycenter leaves exactly the initial barycenters before
  the prescribed last vertex.  These are the images of the barycenters
  indexed by $q$ under the $i$th face inclusion, and affine combinations
  commute with that inclusion.
-/
theorem barycentricSubdivisionSingularSimplex_delta_last
    (X : TopCat.{v}) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n + 1⦌)
    (i : Fin (n + 2)) (q : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.obj X).δ (Fin.last (n + 1))
        (barycentricSubdivisionSingularSimplex X (n + 1) σ
          (lastVertexOrderedPermutation i q)) =
      barycentricSubdivisionSingularSimplex X n
        ((TopCat.toSSet.obj X).δ i σ) q := by
  apply (TopCat.toSSetObjEquiv X _).injective
  ext z
  simp only [TopCat.toSSetObjEquiv_δ_apply]
  change
    (TopCat.toSSetObjEquiv X _ σ)
        (stdSimplex.barycentricSubdivisionMap
          (lastVertexOrderedPermutation i q)
          (stdSimplex.map
            (Fin.last (n + 1)).succAbove z)) =
      (TopCat.toSSetObjEquiv X _ σ)
        (stdSimplex.map i.succAbove
          (stdSimplex.barycentricSubdivisionMap q z))
  rw [Fin.succAbove_last]
  rw [stdSimplex.barycentricSubdivisionMap,
    stdSimplex.affineMap_map]
  rw [stdSimplex.barycentricSubdivisionMap]
  rw [stdSimplex.map_affineMap]
  congr 2
  funext k
  exact lastVertexOrderedPermutation_barycenter_castSucc i q k

/--
%%handwave
name:
  Decomposition of vertex orderings by their final vertex
statement:
  Orderings of the $n+2$ vertices of $\Delta^{n+1}$ are in bijection with
  pairs consisting of their final vertex $i$ and an ordering of the remaining
  $n+1$ vertices.
-/
noncomputable def lastVertexOrderedPermutationEquiv (n : ℕ) :
    (Fin (n + 2) × Equiv.Perm (Fin (n + 1))) ≃
      Equiv.Perm (Fin (n + 2)) :=
  Equiv.ofBijective
    (fun iq => lastVertexOrderedPermutation iq.1 iq.2)
    (by
      constructor
      · rintro ⟨i, q⟩ ⟨i', q'⟩ h
        have hi : i = i' := by
          have hlast := Equiv.congr_fun h (Fin.last (n + 1))
          simpa only [lastVertexOrderedPermutation_last] using hlast
        subst i'
        have hq : q = q' := by
          apply Equiv.ext
          intro k
          apply Fin.succAbove_right_injective
          have hk := Equiv.congr_fun h k.castSucc
          simpa only [lastVertexOrderedPermutation_castSucc] using hk
        subst q'
        rfl
      · intro p
        let i := p (Fin.last (n + 1))
        let c := (Fin.last (n + 1)).cycleRange
        let r : Equiv.Perm (Fin (n + 2)) :=
          i.cycleRange * p * c.symm
        let q : Equiv.Perm (Fin (n + 1)) :=
          (Equiv.Perm.decomposeFin r).2
        refine ⟨(i, q), ?_⟩
        have hr0 : r 0 = 0 := by
          change i.cycleRange (p (c.symm 0)) = 0
          have hc0 : c.symm 0 = Fin.last (n + 1) := by
            simpa only [c] using
              Fin.cycleRange_symm_zero (Fin.last (n + 1))
          rw [hc0]
          change i.cycleRange i = 0
          simp
        have hfirst :
            (Equiv.Perm.decomposeFin r).1 = r 0 := by
          rw [← Equiv.Perm.decomposeFin_symm_apply_zero
            (Equiv.Perm.decomposeFin r).1
            (Equiv.Perm.decomposeFin r).2]
          exact Equiv.congr_fun
            (Equiv.symm_apply_apply Equiv.Perm.decomposeFin r) 0
        have hpair :
            Equiv.Perm.decomposeFin r = (0, q) := by
          apply Prod.ext
          · exact hfirst.trans hr0
          · rfl
        have hlift :
            Equiv.Perm.decomposeFin.symm (0, q) = r := by
          rw [← hpair, Equiv.symm_apply_apply]
        change
          i.cycleRange.symm *
              Equiv.Perm.decomposeFin.symm (0, q) * c =
            p
        rw [hlift]
        simp only [r, c]
        change
          i.cycleRange⁻¹ *
              (i.cycleRange * (p *
                ((Fin.last (n + 1)).cycleRange⁻¹ *
                  (Fin.last (n + 1)).cycleRange))) =
            p
        group)

/--
%%handwave
name:
  Evaluation of the final-vertex decomposition
statement:
  The ordering corresponding to a pair $(i,q)$ under the final-vertex
  decomposition is the ordering that lists the other vertices according to
  $q$ and places $i$ last.
proof:
  This is the defining forward map of the equivalence.
-/
@[simp]
theorem lastVertexOrderedPermutationEquiv_apply
    (n : ℕ) (i : Fin (n + 2))
    (q : Equiv.Perm (Fin (n + 1))) :
    lastVertexOrderedPermutationEquiv n (i, q) =
      lastVertexOrderedPermutation i q :=
  rfl

/--
%%handwave
name:
  Barycentric subdivision in one chain degree
statement:
  In degree $n$, barycentric subdivision sends a generating singular simplex
  $\sigma$ to
  $\sum_{p\in S_{n+1}}\operatorname{sign}(p)\,
  (\sigma\circ\beta_p)$ and extends this assignment linearly to
  $C_n(X;\mathbb R)$.
-/
noncomputable def barycentricSubdivisionDegree
    (X : TopCat.{v}) (n : ℕ) :
    (realSingularChains X).X n ⟶ (realSingularChains X).X n := by
  classical
  exact Sigma.desc fun σ =>
    ∑ p : Equiv.Perm (Fin (n + 1)),
      ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
        (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient)
          (barycentricSubdivisionSingularSimplex X n σ p)

/--
%%handwave
name:
  Barycentric subdivision formula on a singular simplex
statement:
  On the chain generator $[\sigma]$, degree-$n$ barycentric subdivision is
  $\sum_{p\in S_{n+1}}\operatorname{sign}(p)
  [\sigma\circ\beta_p]$.
proof:
  This is the universal-property equation for the map from the direct sum
  freely generated by the singular $n$-simplices.
-/
theorem singularSimplex_comp_barycentricSubdivisionDegree
    (X : TopCat.{v}) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient) σ ≫
      barycentricSubdivisionDegree X n =
      ∑ p : Equiv.Perm (Fin (n + 1)),
        ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
          (TopCat.toSSet.obj X).ιChainComplex
            (R := realSingularChainCoefficient)
            (barycentricSubdivisionSingularSimplex X n σ p) :=
  Sigma.ι_desc _ _

/--
%%handwave
name:
  Barycentric subdivision fixes singular points
statement:
  Every barycentric subsimplex of a singular $0$-simplex $\sigma$ is
  $\sigma$ itself.
proof:
  The standard $0$-simplex has a unique point.  Consequently its unique
  initial-face barycenter is that point, so precomposition with the
  barycentric affine map does not change $\sigma$.
-/
theorem barycentricSubdivisionSingularSimplex_zero
    (X : TopCat.{v})
    (σ : TopCat.toSSet.obj X _⦋0⦌)
    (p : Equiv.Perm (Fin 1)) :
    barycentricSubdivisionSingularSimplex X 0 σ p = σ := by
  apply (TopCat.toSSetObjEquiv X _).injective
  dsimp only [barycentricSubdivisionSingularSimplex]
  rw [Equiv.apply_symm_apply]
  ext x
  have hx : x = stdSimplex.vertex 0 := Subsingleton.elim _ _
  subst x
  change (TopCat.toSSetObjEquiv X _ σ)
      (stdSimplex.barycentricSubdivisionMap p (stdSimplex.vertex 0)) =
    (TopCat.toSSetObjEquiv X _ σ) (stdSimplex.vertex 0)
  rw [stdSimplex.barycentricSubdivisionMap_vertex]
  congr 1
  exact Subsingleton.elim _ _

/--
%%handwave
name:
  Barycentric subdivision is the identity in degree zero
statement:
  The degree-zero subdivision operator on real singular chains is the
  identity map on $C_0(X;\mathbb R)$.
proof:
  There is only one permutation of the single vertex.  Its sign is one,
  and its barycentric subsimplex is the original singular point.
-/
theorem barycentricSubdivisionDegree_zero
    (X : TopCat.{v}) :
    barycentricSubdivisionDegree X 0 = 𝟙 _ := by
  classical
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [singularSimplex_comp_barycentricSubdivisionDegree]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin 1))]
  · rw [barycentricSubdivisionSingularSimplex_zero]
    rw [Category.comp_id]
    exact one_zsmul _
  · intro p _ hp
    exact (hp (Subsingleton.elim _ _)).elim
  · simp

/--
%%handwave
name:
  Cancellation of the internal faces in barycentric subdivision
statement:
  Fix an $(n+1)$-simplex $\sigma$ and an internal face position
  $0\leq j\leq n$.  In the signed sum defining barycentric subdivision, the
  sum of all $j$th faces is zero.
proof:
  Pair an ordering $p$ with the ordering obtained by swapping positions
  $j$ and $j+1$.  The two resulting $j$th faces are equal, while the
  permutation signs are opposite.  This fixed-point-free involution
  therefore cancels the entire finite sum.
-/
theorem barycentricSubdivision_internalFace_sum_eq_zero
    (X : TopCat.{v}) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n + 1⦌)
    (j : Fin (n + 1)) :
    ∑ p : Equiv.Perm (Fin (n + 2)),
        ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
          (TopCat.toSSet.obj X).ιChainComplex
            (R := realSingularChainCoefficient)
            ((TopCat.toSSet.obj X).δ j.castSucc
              (barycentricSubdivisionSingularSimplex
                X (n + 1) σ p)) =
      0 := by
  classical
  apply Finset.sum_involution
    (fun p _ => p * Equiv.swap j.castSucc j.succ)
  · intro p _
    rw [barycentricSubdivisionSingularSimplex_delta_mul_swap X n σ p j]
    rw [Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (Fin.ne_of_lt j.castSucc_lt_succ)]
    simp only [Units.val_neg, Int.cast_neg, mul_neg, mul_one]
    rw [neg_smul, add_neg_cancel]
  · intro p _ _
    exact (not_congr Equiv.mul_swap_eq_iff).mpr
      (Fin.ne_of_lt j.castSucc_lt_succ)
  · intro p _
    exact Finset.mem_univ _
  · intro p _
    exact Equiv.mul_swap_involutive j.castSucc j.succ p

/--
%%handwave
name:
  Barycentric subdivision commutes with the singular boundary
statement:
  For every $n\geq0$, the degreewise subdivision operators satisfy
  $\operatorname{Sd}_{n+1}\partial_{n+1}
  =\partial_{n+1}\operatorname{Sd}_n$.
proof:
  Expand both sides on a generating $(n+1)$-simplex.  The faces of the
  barycentric simplices that omit an intermediate barycenter occur in
  pairs with opposite signs.  The remaining faces are precisely the
  barycentric subdivisions of the original boundary faces, with the
  induced permutation signs.
-/
theorem barycentricSubdivisionDegree_comm
    (X : TopCat.{v}) (n : ℕ) :
    barycentricSubdivisionDegree X (n + 1) ≫
        (realSingularChains X).d (n + 1) n =
      (realSingularChains X).d (n + 1) n ≫
        barycentricSubdivisionDegree X n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  simp only [← Category.assoc]
  rw [singularSimplex_comp_barycentricSubdivisionDegree]
  rw [Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  simp_rw [SSet.ιChainComplex_d]
  rw [Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  simp_rw [singularSimplex_comp_barycentricSubdivisionDegree]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  rw [Fin.sum_univ_castSucc]
  have hinternal :
      ∑ j : Fin (n + 1),
          ∑ p : Equiv.Perm (Fin (n + 2)),
            (((Equiv.Perm.sign p : ℤˣ) : ℤ) *
                (-1 : ℤ) ^ j.castSucc.val) •
              (TopCat.toSSet.obj X).ιChainComplex
                (R := realSingularChainCoefficient)
                ((TopCat.toSSet.obj X).δ j.castSucc
                  (barycentricSubdivisionSingularSimplex
                    X (n + 1) σ p)) =
        0 := by
    apply Finset.sum_eq_zero
    intro j _
    calc
      (∑ p : Equiv.Perm (Fin (n + 2)),
          (((Equiv.Perm.sign p : ℤˣ) : ℤ) *
              (-1 : ℤ) ^ j.castSucc.val) •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := realSingularChainCoefficient)
              ((TopCat.toSSet.obj X).δ j.castSucc
                (barycentricSubdivisionSingularSimplex
                  X (n + 1) σ p))) =
          ((-1 : ℤ) ^ j.castSucc.val) •
            (∑ p : Equiv.Perm (Fin (n + 2)),
              ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
                (TopCat.toSSet.obj X).ιChainComplex
                  (R := realSingularChainCoefficient)
                  ((TopCat.toSSet.obj X).δ j.castSucc
                    (barycentricSubdivisionSingularSimplex
                      X (n + 1) σ p))) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro p _
            rw [smul_smul, mul_comm]
      _ = 0 := by
        rw [barycentricSubdivision_internalFace_sum_eq_zero
          X n σ j, smul_zero]
  rw [hinternal, zero_add]
  rw [← (lastVertexOrderedPermutationEquiv n).sum_comp
    (fun p : Equiv.Perm (Fin (n + 2)) =>
      (((Equiv.Perm.sign p : ℤˣ) : ℤ) *
          (-1 : ℤ) ^ (Fin.last (n + 1)).val) •
        (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient)
          ((TopCat.toSSet.obj X).δ (Fin.last (n + 1))
            (barycentricSubdivisionSingularSimplex
              X (n + 1) σ p)))]
  rw [Fintype.sum_prod_type]
  simp_rw [lastVertexOrderedPermutationEquiv_apply,
    lastVertexOrderedPermutation_sign]
  simp_rw [barycentricSubdivisionSingularSimplex_delta_last X n σ]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  simp only [Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one]
  rw [show (Fin.last (n + 1)).val = n + 1 by rfl]
  have hn :
      (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [mul_assoc, hn, mul_one]

/--
%%handwave
name:
  Barycentric subdivision chain map
statement:
  The degreewise barycentric subdivision operators assemble to a chain
  endomorphism
  $\operatorname{Sd}:C_\bullet(X;\mathbb R)\to
  C_\bullet(X;\mathbb R)$.
-/
noncomputable def barycentricSubdivision
    (X : TopCat.{v}) :
    realSingularChains X ⟶ realSingularChains X :=
  ChainComplex.ofHom
    (barycentricSubdivisionDegree X)
    (barycentricSubdivisionDegree_comm X)

/--
%%handwave
name:
  Components of the barycentric subdivision chain map
statement:
  The degree-$n$ component of the barycentric subdivision chain map is the
  degreewise operator $\operatorname{Sd}_n$ defined by the signed sum of
  barycentric subsimplices.
proof:
  This is the component supplied to the chain-map constructor.
-/
@[simp]
theorem barycentricSubdivision_f
    (X : TopCat.{v}) (n : ℕ) :
    (barycentricSubdivision X).f n =
      barycentricSubdivisionDegree X n :=
  rfl

/--
%%handwave
name:
  Naturality of barycentric subdivision
statement:
  For every continuous map $f:X\to Y$, barycentric subdivision commutes
  with the induced singular chain map:
  $\operatorname{Sd}_X C_\bullet(f)=
  C_\bullet(f)\operatorname{Sd}_Y$.
proof:
  Check the equality on each generating singular simplex.  Pushforward
  commutes with the signed sum, and each barycentric subsimplex is natural
  under postcomposition by $f$.
-/
theorem barycentricSubdivision_natural
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    barycentricSubdivision X ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{v} ℝ)).obj
          realSingularChainCoefficient).map f =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{v} ℝ)).obj
          realSingularChainCoefficient).map f ≫
        barycentricSubdivision Y := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{v} ℝ)).obj
    realSingularChainCoefficient)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro σ
  have hmap (τ : TopCat.toSSet.obj X _⦋n⦌) :
      (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫ (F.map f).f n =
        (TopCat.toSSet.obj Y).ιChainComplex
          (R := realSingularChainCoefficient)
          (((TopCat.toSSet.map f).app _) τ) := by
    exact SSet.ι_chainComplexMap_f
      (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map f) realSingularChainCoefficient τ
  calc
    (TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient) σ ≫
          (barycentricSubdivision X ≫ F.map f).f n =
      (∑ p : Equiv.Perm (Fin (n + 1)),
        ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
          (TopCat.toSSet.obj X).ιChainComplex
            (R := realSingularChainCoefficient)
            (barycentricSubdivisionSingularSimplex X n σ p)) ≫
        (F.map f).f n := by
          rw [HomologicalComplex.comp_f, ← Category.assoc,
            barycentricSubdivision_f,
            singularSimplex_comp_barycentricSubdivisionDegree]
    _ = ∑ p : Equiv.Perm (Fin (n + 1)),
        ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
          ((TopCat.toSSet.obj X).ιChainComplex
            (R := realSingularChainCoefficient)
            (barycentricSubdivisionSingularSimplex X n σ p) ≫
              (F.map f).f n) := by
          rw [Preadditive.sum_comp]
          simp only [Preadditive.zsmul_comp]
    _ = ∑ p : Equiv.Perm (Fin (n + 1)),
        ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
          (TopCat.toSSet.obj Y).ιChainComplex
            (R := realSingularChainCoefficient)
            (barycentricSubdivisionSingularSimplex Y n
              (((TopCat.toSSet.map f).app _) σ) p) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [hmap, barycentricSubdivisionSingularSimplex_natural]
          rfl
    _ = (TopCat.toSSet.obj Y).ιChainComplex
          (R := realSingularChainCoefficient)
          (((TopCat.toSSet.map f).app _) σ) ≫
        (barycentricSubdivision Y).f n := by
          rw [barycentricSubdivision_f,
            singularSimplex_comp_barycentricSubdivisionDegree]
    _ = ((TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫ (F.map f).f n) ≫
        (barycentricSubdivision Y).f n := by
          rw [hmap]
          rfl
    _ = (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫
        (F.map f ≫ barycentricSubdivision Y).f n := by
          rw [HomologicalComplex.comp_f, Category.assoc]
          rfl

/--
%%handwave
name:
  Zero universal prism degree
statement:
  In every degree $n$, the zero singular $(n+1)$-chain in
  $\widetilde{\Delta}^n$ defines a universal prism operator.
-/
noncomputable def SubdivisionPrismDegree.zero (n : ℕ) :
    SubdivisionPrismDegree n :=
  ⟨0⟩

/--
%%handwave
name:
  The zero universal prism induces the zero operator
statement:
  The prism map $C_n(X;\mathbb R)\to C_{n+1}(X;\mathbb R)$ induced by the
  zero universal chain is the zero linear map.
proof:
  On every singular-simplex generator, its value is the pushforward of the
  zero chain, which is zero.
-/
theorem SubdivisionPrismDegree.zero_map
    (n : ℕ) (X : TopCat.{v}) :
    (SubdivisionPrismDegree.zero n).map X = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [SubdivisionPrismDegree.generator_map]
  change 0 ≫ _ = _ ≫ 0
  rw [zero_comp]
  ext x
  rfl

/--
%%handwave
name:
  Finite initial segment of a universal subdivision prism
statement:
  A subdivision prism through degree $N$ consists of universal operators
  $T_k:C_k(X;\mathbb R)\to C_{k+1}(X;\mathbb R)$ for
  $0\leq k\leq N$, natural in $X$, satisfying
  $1-\operatorname{Sd}=T_0\partial$ in degree zero and
  $1-\operatorname{Sd}=\partial T_k+T_{k+1}\partial$ in every degree
  $k+1\leq N$.
-/
structure SubdivisionPrismPartial (N : ℕ) where
  degree : ∀ k, k ≤ N → SubdivisionPrismDegree k
  comm_zero : ∀ X : TopCat.{v},
    (𝟙 (realSingularChains X) - barycentricSubdivision X).f 0 =
      (degree 0 (Nat.zero_le N)).map X ≫
        (realSingularChains X).d 1 0
  comm_succ : ∀ k (hk : k + 1 ≤ N), ∀ X : TopCat.{v},
    (𝟙 (realSingularChains X) - barycentricSubdivision X).f (k + 1) =
      (realSingularChains X).d (k + 1) k ≫
          (degree k (by omega)).map X +
        (degree (k + 1) hk).map X ≫
          (realSingularChains X).d (k + 2) (k + 1)

/--
%%handwave
name:
  Degree-zero subdivision prism
statement:
  There is a universal subdivision prism through degree zero, with zero
  prism operator.
proof:
  Barycentric subdivision is the identity on singular $0$-chains, so
  $1-\operatorname{Sd}$ and the boundary of the zero prism are both zero.
-/
noncomputable def subdivisionPrismPartialZero :
    SubdivisionPrismPartial 0 where
  degree k hk := by
    have : k = 0 := by omega
    subst k
    exact SubdivisionPrismDegree.zero 0
  comm_zero X := by
    change
      (𝟙 ((realSingularChains X).X 0) -
          barycentricSubdivisionDegree X 0) =
        (SubdivisionPrismDegree.zero 0).map X ≫
          (realSingularChains X).d 1 0
    rw [barycentricSubdivisionDegree_zero, sub_self,
      SubdivisionPrismDegree.zero_map, zero_comp]
  comm_succ k hk := by omega

/--
%%handwave
name:
  Obstruction cycle for extending the subdivision prism
statement:
  Suppose the subdivision prism has been constructed through degree $N$.
  In the singular chains of $\widetilde{\Delta}^{N+1}$, its extension
  obstruction is
  \[
    z=[\iota](1-\operatorname{Sd})
      -[\iota]\,\partial T_N,
  \]
  where $\iota$ is the fundamental $(N+1)$-simplex.
-/
noncomputable def subdivisionPrismExtensionCycle
    {N : ℕ} (P : SubdivisionPrismPartial N) :
    realSingularChainCoefficient ⟶
      (realSingularChains
        (liftedStandardSimplex (N + 1) : TopCat.{v})).X (N + 1) :=
  (TopCat.toSSet.obj
      (liftedStandardSimplex (N + 1) : TopCat.{v})).ιChainComplex
      (R := realSingularChainCoefficient)
      (liftedStandardSimplexFundamentalSimplex (N + 1)) ≫
        (𝟙 _ - barycentricSubdivision
          (liftedStandardSimplex (N + 1) : TopCat.{v})).f (N + 1) -
    (TopCat.toSSet.obj
      (liftedStandardSimplex (N + 1) : TopCat.{v})).ιChainComplex
      (R := realSingularChainCoefficient)
      (liftedStandardSimplexFundamentalSimplex (N + 1)) ≫
        (realSingularChains
          (liftedStandardSimplex (N + 1) : TopCat.{v})).d (N + 1) N ≫
            (P.degree N le_rfl).map
              (liftedStandardSimplex (N + 1) : TopCat.{v})

/--
%%handwave
name:
  The subdivision-prism extension obstruction is a cycle
statement:
  For a subdivision prism constructed through degree $N$, its extension
  obstruction $z\in C_{N+1}(\widetilde{\Delta}^{N+1};\mathbb R)$ satisfies
  $\partial z=0$.
proof:
  The chain-map identity for $1-\operatorname{Sd}$ changes the boundary of
  its first term to
  $[\iota]\partial(1-\operatorname{Sd})$.  Substitute the prism identity in
  degree $N$.  The term containing two consecutive boundaries vanishes and
  the remaining term cancels the boundary of
  $[\iota]\partial T_N$.
-/
theorem subdivisionPrismExtensionCycle_boundary
    {N : ℕ} (P : SubdivisionPrismPartial N) :
    subdivisionPrismExtensionCycle P ≫
        (realSingularChains
          (liftedStandardSimplex (N + 1) : TopCat.{v})).d
            (N + 1) N =
      0 := by
  let X := (liftedStandardSimplex (N + 1) : TopCat.{v})
  let C := realSingularChains X
  let D : C ⟶ C := 𝟙 C - barycentricSubdivision X
  let u : realSingularChainCoefficient ⟶ C.X (N + 1) :=
    (TopCat.toSSet.obj X).ιChainComplex
      (R := realSingularChainCoefficient)
      (liftedStandardSimplexFundamentalSimplex (N + 1))
  let T := (P.degree N le_rfl).map X
  change (u ≫ D.f (N + 1) - u ≫ C.d (N + 1) N ≫ T) ≫
      C.d (N + 1) N = 0
  rw [Preadditive.sub_comp, Category.assoc]
  rw [D.comm (N + 1) N]
  rw [← Category.assoc u (C.d (N + 1) N) (D.f N)]
  cases N with
  | zero =>
      rw [P.comm_zero]
      dsimp only [T]
      simp only [Category.assoc]
      abel
  | succ k =>
      rw [P.comm_succ k (by omega)]
      dsimp only [T]
      rw [Preadditive.comp_add]
      simp only [Category.assoc]
      rw [← Category.assoc
        (C.d (k + 2) (k + 1)) (C.d (k + 1) k)]
      rw [C.d_comp_d, zero_comp, comp_zero, zero_add]
      abel

/--
%%handwave
name:
  Existence of the next universal subdivision-prism chain
statement:
  The extension obstruction for a prism through degree $N$ is the boundary
  of an $(N+2)$-chain in
  $C_\bullet(\widetilde{\Delta}^{N+1};\mathbb R)$.
proof:
  The lifted standard simplex is contractible, so its singular-chain
  complex is homotopy equivalent to a complex concentrated in degree zero.
  Every positive-dimensional cycle therefore bounds, and the obstruction
  is a cycle by the preceding result.
-/
theorem exists_subdivisionPrismExtensionFiller
    {N : ℕ} (P : SubdivisionPrismPartial N) :
    ∃ w : realSingularChainCoefficient ⟶
        (realSingularChains
          (liftedStandardSimplex (N + 1) : TopCat.{v})).X (N + 2),
      w ≫
          (realSingularChains
            (liftedStandardSimplex (N + 1) : TopCat.{v})).d
              (N + 2) (N + 1) =
        subdivisionPrismExtensionCycle P := by
  rcases
      standardSimplexRealSingularChains_homotopyEquiv_singleZero
        (N + 1) with
    ⟨B, ⟨e⟩⟩
  exact
    chainComplex_exists_boundary_of_homotopyEquiv_singleZero
      (realSingularChains
        (liftedStandardSimplex (N + 1) : TopCat.{v}))
      B realSingularChainCoefficient e N
      (subdivisionPrismExtensionCycle P)
      (subdivisionPrismExtensionCycle_boundary P)

/--
%%handwave
name:
  Chosen filler for the subdivision-prism extension cycle
statement:
  For every subdivision prism through degree $N$, choose an
  $(N+2)$-chain $w$ in $\widetilde{\Delta}^{N+1}$ whose boundary is the
  extension obstruction.
-/
noncomputable def subdivisionPrismExtensionFiller
    {N : ℕ} (P : SubdivisionPrismPartial N) :
    realSingularChainCoefficient ⟶
      (realSingularChains
        (liftedStandardSimplex (N + 1) : TopCat.{v})).X (N + 2) :=
  Classical.choose (exists_subdivisionPrismExtensionFiller P)

/--
%%handwave
name:
  Boundary of the chosen subdivision-prism filler
statement:
  The chosen extension filler $w$ satisfies
  $\partial w=z$, where $z$ is the extension obstruction.
proof:
  This is the defining property of the chosen filler.
-/
theorem subdivisionPrismExtensionFiller_boundary
    {N : ℕ} (P : SubdivisionPrismPartial N) :
    subdivisionPrismExtensionFiller P ≫
        (realSingularChains
          (liftedStandardSimplex (N + 1) : TopCat.{v})).d
            (N + 2) (N + 1) =
      subdivisionPrismExtensionCycle P :=
  Classical.choose_spec (exists_subdivisionPrismExtensionFiller P)

/--
%%handwave
name:
  Next universal degree of the subdivision prism
statement:
  The chosen filler in
  $C_{N+2}(\widetilde{\Delta}^{N+1};\mathbb R)$ defines the universal prism
  operator in degree $N+1$.
-/
noncomputable def subdivisionPrismNextDegree
    {N : ℕ} (P : SubdivisionPrismPartial N) :
    SubdivisionPrismDegree (N + 1) :=
  ⟨subdivisionPrismExtensionFiller P⟩

/--
%%handwave
name:
  Fundamental simplex generates an arbitrary singular simplex
statement:
  If $\sigma:\Delta^n\to X$ and
  $\widetilde{\sigma}:\widetilde{\Delta}^n\to X$ is its represented map,
  then the induced chain map sends the fundamental generator
  $[\iota_n]$ to $[\sigma]$.
proof:
  The simplicial-chain functor sends a generating simplex to its simplicial
  image, and the represented map sends the fundamental simplex to
  $\sigma$.
-/
theorem liftedStandardSimplexFundamental_chainMap
    (X : TopCat.{v}) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj (liftedStandardSimplex n : TopCat.{v})).ιChainComplex
        (R := realSingularChainCoefficient)
        (liftedStandardSimplexFundamentalSimplex n) ≫
      (realSingularChainFunctor.map
        (singularSimplexLiftedStandardMap X n σ)).f n =
      (TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient) σ := by
  calc
    _ = (TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient)
        (((TopCat.toSSet.map
          (singularSimplexLiftedStandardMap X n σ)).app _)
          (liftedStandardSimplexFundamentalSimplex n)) := by
      exact SSet.ι_chainComplexMap_f
        (TopCat.toSSet.obj (liftedStandardSimplex n : TopCat.{v}))
        (TopCat.toSSet.obj X)
        (TopCat.toSSet.map (singularSimplexLiftedStandardMap X n σ))
        realSingularChainCoefficient
        (liftedStandardSimplexFundamentalSimplex n)
    _ = _ := by
      rw [singularSimplexLiftedStandardMap_fundamental]

/--
%%handwave
name:
  Prism identity in the newly extended degree
statement:
  If a universal subdivision prism has been constructed through degree
  $N$, adjoining the chosen filler as $T_{N+1}$ gives
  \[
    1-\operatorname{Sd}
      =\partial T_N+T_{N+1}\partial
  \]
  on $C_{N+1}(X;\mathbb R)$ for every space $X$.
proof:
  Check the identity on a singular simplex $\sigma$.  Express $\sigma$ as
  the image of the fundamental simplex of
  $\widetilde{\Delta}^{N+1}$.  Naturality of subdivision and of the
  universal prism operators pushes the boundary equation for the chosen
  filler along the represented map
  $\widetilde{\Delta}^{N+1}\to X$.
-/
theorem subdivisionPrismNextDegree_comm
    {N : ℕ} (P : SubdivisionPrismPartial N)
    (X : TopCat.{v}) :
    (𝟙 (realSingularChains X) - barycentricSubdivision X).f (N + 1) =
      (realSingularChains X).d (N + 1) N ≫
          (P.degree N le_rfl).map X +
        (subdivisionPrismNextDegree P).map X ≫
          (realSingularChains X).d (N + 2) (N + 1) := by
  let L := (liftedStandardSimplex (N + 1) : TopCat.{v})
  let CL := realSingularChains L
  let CX := realSingularChains X
  let DL : CL ⟶ CL := 𝟙 CL - barycentricSubdivision L
  let DX : CX ⟶ CX := 𝟙 CX - barycentricSubdivision X
  let u : realSingularChainCoefficient ⟶ CL.X (N + 1) :=
    (TopCat.toSSet.obj L).ιChainComplex
      (R := realSingularChainCoefficient)
      (liftedStandardSimplexFundamentalSimplex (N + 1))
  let F := realSingularChainFunctor
  apply SSet.chainComplex_hom_ext
  intro σ
  let g : L ⟶ X :=
    singularSimplexLiftedStandardMap X (N + 1) σ
  let G : CL ⟶ CX := F.map g
  have hgen :
      u ≫ G.f (N + 1) =
        (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ := by
    dsimp only [G]
    exact liftedStandardSimplexFundamental_chainMap X (N + 1) σ
  have hD :
      DL.f (N + 1) ≫ G.f (N + 1) =
        G.f (N + 1) ≫ DX.f (N + 1) := by
    change
      (𝟙 (CL.X (N + 1)) -
          (barycentricSubdivision L).f (N + 1)) ≫
          G.f (N + 1) =
        G.f (N + 1) ≫
          (𝟙 (CX.X (N + 1)) -
            (barycentricSubdivision X).f (N + 1))
    rw [Preadditive.sub_comp, Category.id_comp]
    change
      G.f (N + 1) -
          (barycentricSubdivision L).f (N + 1) ≫
            G.f (N + 1) =
        G.f (N + 1) -
          G.f (N + 1) ≫
            (barycentricSubdivision X).f (N + 1)
    congr 1
    dsimp only [G]
    exact congrArg (fun q => q.f (N + 1))
      (barycentricSubdivision_natural g)
  have hT :
      (P.degree N le_rfl).map L ≫ G.f (N + 1) =
        G.f N ≫ (P.degree N le_rfl).map X := by
    dsimp only [G]
    exact (P.degree N le_rfl).map_natural g
  have hnew :
      (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫
          (subdivisionPrismNextDegree P).map X =
        subdivisionPrismExtensionFiller P ≫ G.f (N + 2) := by
    dsimp only [G]
    exact (subdivisionPrismNextDegree P).generator_map X σ
  have hfill :
      u ≫ DL.f (N + 1) =
        u ≫ CL.d (N + 1) N ≫ (P.degree N le_rfl).map L +
          subdivisionPrismExtensionFiller P ≫
            CL.d (N + 2) (N + 1) := by
    rw [subdivisionPrismExtensionFiller_boundary]
    change
      u ≫ DL.f (N + 1) =
        u ≫ CL.d (N + 1) N ≫ (P.degree N le_rfl).map L +
          (u ≫ DL.f (N + 1) -
            u ≫ CL.d (N + 1) N ≫ (P.degree N le_rfl).map L)
    abel
  calc
    (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫ DX.f (N + 1) =
      (u ≫ G.f (N + 1)) ≫ DX.f (N + 1) := by
        rw [hgen]
    _ = (u ≫ DL.f (N + 1)) ≫ G.f (N + 1) := by
      simp only [Category.assoc]
      rw [hD]
    _ = (u ≫ CL.d (N + 1) N ≫
            (P.degree N le_rfl).map L +
          subdivisionPrismExtensionFiller P ≫
            CL.d (N + 2) (N + 1)) ≫
        G.f (N + 1) := by rw [hfill]
    _ = (u ≫ CL.d (N + 1) N ≫
            (P.degree N le_rfl).map L) ≫ G.f (N + 1) +
          (subdivisionPrismExtensionFiller P ≫
            CL.d (N + 2) (N + 1)) ≫ G.f (N + 1) := by
      rw [Preadditive.add_comp]
    _ = (u ≫ G.f (N + 1)) ≫
            CX.d (N + 1) N ≫ (P.degree N le_rfl).map X +
          (subdivisionPrismExtensionFiller P ≫ G.f (N + 2)) ≫
            CX.d (N + 2) (N + 1) := by
      simp only [Category.assoc]
      rw [hT]
      rw [← Category.assoc
        (CL.d (N + 1) N) (G.f N)
          ((P.degree N le_rfl).map X)]
      rw [← G.comm (N + 1) N]
      rw [← G.comm (N + 2) (N + 1)]
      simp only [Category.assoc]
    _ = (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫
        (CX.d (N + 1) N ≫ (P.degree N le_rfl).map X +
          (subdivisionPrismNextDegree P).map X ≫
            CX.d (N + 2) (N + 1)) := by
      rw [hgen, ← hnew]
      simp only [Preadditive.comp_add, Category.assoc]

/--
%%handwave
name:
  Extension of a finite universal subdivision prism
statement:
  Every universal subdivision prism through degree $N$ extends to one
  through degree $N+1$.
proof:
  Retain all existing universal degrees and use the chosen filler for the
  new degree.  The old prism equations remain unchanged, while the new
  equation is the preceding naturality argument.
-/
noncomputable def subdivisionPrismPartialSucc
    {N : ℕ} (P : SubdivisionPrismPartial N) :
    SubdivisionPrismPartial (N + 1) where
  degree k hk :=
    if h : k ≤ N then
      P.degree k h
    else by
      have hk' : k = N + 1 := by omega
      subst k
      exact subdivisionPrismNextDegree P
  comm_zero X := by
    simpa [dif_pos (Nat.zero_le N)] using P.comm_zero X
  comm_succ k hk X := by
    by_cases h : k + 1 ≤ N
    · have hlt : k < N := by omega
      simpa [h, hlt, dif_pos (by omega : k ≤ N)] using
        P.comm_succ k h X
    · have hk' : k = N := by omega
      subst k
      simpa [dif_pos le_rfl,
        dif_neg (by omega : ¬ N + 1 ≤ N)] using
        subdivisionPrismNextDegree_comm P X

/--
%%handwave
name:
  Universal subdivision prisms in every finite range
statement:
  For every $N$, there is a universal subdivision prism satisfying the
  prism identity in all degrees at most $N$.
-/
noncomputable def subdivisionPrismPartial (N : ℕ) :
    SubdivisionPrismPartial N := by
  induction N with
  | zero =>
      exact subdivisionPrismPartialZero
  | succ N P =>
      exact subdivisionPrismPartialSucc P

/--
%%handwave
name:
  Universal subdivision-prism operator in one degree
statement:
  For every $n$, the universal prism degree $T_n$ is the final degree of
  the universal subdivision prism constructed through degree $n$.
-/
noncomputable def subdivisionPrismDegree (n : ℕ) :
    SubdivisionPrismDegree n :=
  (subdivisionPrismPartial n).degree n le_rfl

/--
%%handwave
name:
  Degree-zero equation for the universal subdivision prism
statement:
  On $C_0(X;\mathbb R)$, the universal prism satisfies
  $1-\operatorname{Sd}=T_0\partial$.
proof:
  This is the degree-zero equation in the universal prism constructed
  through degree zero.
-/
theorem subdivisionPrismDegree_comm_zero
    (X : TopCat.{v}) :
    (𝟙 (realSingularChains X) - barycentricSubdivision X).f 0 =
      (subdivisionPrismDegree 0).map X ≫
        (realSingularChains X).d 1 0 := by
  exact (subdivisionPrismPartial 0).comm_zero X

/--
%%handwave
name:
  Successor equation for the universal subdivision prism
statement:
  For every $n$ and every space $X$, the universal prism operators satisfy
  \[
    (1-\operatorname{Sd})_{n+1}
      =\partial_{n+1}T_n+T_{n+1}\partial_{n+2}.
  \]
proof:
  Use the degree-$(n+1)$ equation in the universal prism constructed
  through that degree.  Its inherited degree $n$ is the previously
  constructed universal degree, while its last degree is the newly chosen
  filler.
-/
theorem subdivisionPrismDegree_comm_succ
    (n : ℕ) (X : TopCat.{v}) :
    (𝟙 (realSingularChains X) - barycentricSubdivision X).f (n + 1) =
      (realSingularChains X).d (n + 1) n ≫
          (subdivisionPrismDegree n).map X +
        (subdivisionPrismDegree (n + 1)).map X ≫
          (realSingularChains X).d (n + 2) (n + 1) := by
  simpa [subdivisionPrismDegree, subdivisionPrismPartial,
    subdivisionPrismPartialSucc, dif_pos le_rfl,
    dif_neg (by omega : ¬ n + 1 ≤ n)] using
    (subdivisionPrismPartial (n + 1)).comm_succ n le_rfl X

/--
%%handwave
name:
  Components of the universal subdivision homotopy
statement:
  For a space $X$, define $H_{i,j}:C_i(X;\mathbb R)\to
  C_j(X;\mathbb R)$ to be the universal prism map $T_i$ when
  $j=i+1$, and zero otherwise.
-/
noncomputable def subdivisionPrismHomFamily
    (X : TopCat.{v}) (i j : ℕ) :
    (realSingularChains X).X i ⟶ (realSingularChains X).X j :=
  if h : i + 1 = j then by
    subst j
    exact (subdivisionPrismDegree i).map X
  else 0

/--
%%handwave
name:
  Adjacent-degree component of the universal subdivision homotopy
statement:
  The homotopy component from degree $i$ to degree $i+1$ is the universal
  prism operator $T_i$.
proof:
  This is the positive branch of the definition of the homotopy family.
-/
@[simp]
theorem subdivisionPrismHomFamily_succ
    (X : TopCat.{v}) (i : ℕ) :
    subdivisionPrismHomFamily X i (i + 1) =
      (subdivisionPrismDegree i).map X := by
  simp [subdivisionPrismHomFamily]

/--
%%handwave
name:
  Nonadjacent components of the universal subdivision homotopy vanish
statement:
  If degree $j$ is not the successor of degree $i$, then the homotopy
  component $H_{i,j}$ is zero.
proof:
  The relation for a nonnegative chain complex holds precisely when
  $j=i+1$, so the defining conditional takes its zero branch.
-/
theorem subdivisionPrismHomFamily_zero
    (X : TopCat.{v}) (i j : ℕ)
    (h : ¬(ComplexShape.down ℕ).Rel j i) :
    subdivisionPrismHomFamily X i j = 0 := by
  rw [subdivisionPrismHomFamily]
  split_ifs with hij
  · subst j
    simp at h
  · rfl

/--
%%handwave
name:
  Null-homotopy of identity minus barycentric subdivision
statement:
  The universal prism family is a chain homotopy from
  $1-\operatorname{Sd}$ to the zero chain map on
  $C_\bullet(X;\mathbb R)$.
proof:
  In degree zero the homotopy equation is the universal degree-zero
  equation.  In every successor degree it is the corresponding successor
  prism equation.  All nonadjacent homotopy components vanish by
  definition.
-/
noncomputable def subdivisionPrismSubZeroHomotopy
    (X : TopCat.{v}) :
    Homotopy
      (𝟙 (realSingularChains X) - barycentricSubdivision X) 0 where
  hom := subdivisionPrismHomFamily X
  zero := subdivisionPrismHomFamily_zero X
  comm i := by
    rw [HomologicalComplex.zero_f_apply, add_zero]
    cases i with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex, zero_add,
          Homotopy.prevD_chainComplex, subdivisionPrismHomFamily_succ]
        exact subdivisionPrismDegree_comm_zero X
    | succ n =>
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex,
          subdivisionPrismHomFamily_succ,
          subdivisionPrismHomFamily_succ]
        exact subdivisionPrismDegree_comm_succ n X

/--
%%handwave
name:
  Universal homotopy from identity to barycentric subdivision
statement:
  On the real singular-chain complex of every space $X$, the identity
  chain map is chain-homotopic to barycentric subdivision.
proof:
  The universal prism null-homotopes
  $1-\operatorname{Sd}$; the standard equivalence between such a
  null-homotopy and a homotopy from $1$ to
  $\operatorname{Sd}$ gives the result.
-/
noncomputable def subdivisionPrismHomotopy
    (X : TopCat.{v}) :
    Homotopy (𝟙 (realSingularChains X)) (barycentricSubdivision X) :=
  Homotopy.equivSubZero.symm (subdivisionPrismSubZeroHomotopy X)

/--
%%handwave
name:
  Singular simplices subordinate to an open cover
statement:
  Given an open cover $(U_i)_{i\in\iota}$ of a space $X$, the singular
  simplices whose images are contained in some $U_i$ form a simplicial
  subcomplex of the singular simplicial set of $X$.
proof:
  A face or degeneracy of a singular simplex is obtained by precomposition
  with a map between standard simplices.  Precomposition can only shrink the
  image, so a simplex subordinate to one member of the cover remains
  subordinate to that member.
-/
noncomputable def openCoverSmallSingularSet
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) :
    (TopCat.toSSet.obj X).Subcomplex where
  obj n :=
    {σ | ∃ i : ι,
      Set.range (TopCat.toSSetObjEquiv X n σ) ⊆ (U i : Set X)}
  map {n m} f σ hσ := by
    rcases hσ with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rintro y ⟨z, rfl⟩
    change
      (TopCat.toSSetObjEquiv X m
        (((TopCat.toSSet.obj X).map (Quiver.Hom.op f.unop)) σ)) z ∈ U i
    rw [TopCat.toSSetObjEquiv_naturality_apply]
    exact hi ⟨stdSimplex.map f.unop z, rfl⟩

/--
%%handwave
name:
  The real chain complex subordinate to an open cover
statement:
  The small real singular-chain complex associated to an open cover is the
  simplicial chain complex freely generated in degree $n$ by the singular
  $n$-simplices whose images lie in one member of the cover.
proof:
  Apply the simplicial chain-complex construction with real coefficients to
  the cover-small singular simplicial set.
-/
noncomputable abbrev smallRealSingularChains
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) :
    ChainComplex (ModuleCat.{v} ℝ) ℕ :=
  (openCoverSmallSingularSet X U : SSet.{v}).chainComplex
    realSingularChainCoefficient

/--
%%handwave
name:
  Inclusion of cover-small real singular chains
statement:
  Inclusion of the cover-small singular simplicial set into the full singular
  simplicial set induces a chain map from cover-small real singular chains to
  all real singular chains.
proof:
  Apply the simplicial chain-complex functor to the inclusion of the
  cover-small simplicial subcomplex.
-/
noncomputable def smallRealSingularChainsInclusion
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) :
    smallRealSingularChains X U ⟶
      realSingularChains X :=
  SSet.chainComplexMap (openCoverSmallSingularSet X U).ι
    realSingularChainCoefficient

end

end Cohomology
end JJMath
