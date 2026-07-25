import JJMath.Uniformization.CompactH1Uniformization
import JJMath.Uniformization.GreenFunction
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# The Riemann mapping theorem

A nonempty simply connected proper open subset of the complex plane is
biholomorphic to the unit disk.  The proof applies simply connected
uniformization after constructing a bounded injective holomorphic function
from a square-root branch.  Compactness excludes the sphere and Liouville's
theorem excludes the plane.
-/

namespace JJMath

open Function Filter Metric Set
open scoped Manifold Topology

namespace Uniformization

noncomputable section

/--
%%handwave
name:
  A square-root coordinate with nondense image
statement:
  Let $U\subsetneq\mathbb C$ be open and simply connected. There is an
  injective function $f:\mathbb C\to\mathbb C$ such that $f(U)$ is not dense
  and $f$ is holomorphic on $U$ with $f'(z)\ne0$ for every $z\in U$.
proof:
  Choose $a\notin U$ and translate so that $a=0$. Simple connectedness gives
  a continuous branch $f$ of $\sqrt z$ on $U$. The identity $f(z)^2=z$ makes
  $f$ injective and the local inverse theorem makes it holomorphic with
  derivative $(2f(z))^{-1}$. The image cannot approach both $f(x)$ and
  $-f(x)$: equality $f(u)=-f(v)$ would imply $u=v$ and then $f(u)=0$, which
  is impossible because $0\notin U$. Thus $-f(x)$ is outside the closure of
  $f(U)$.
-/
theorem exists_injective_planeMap_not_dense_image_of_proper_simplyConnected
    {U : Set ℂ} (hUopen : IsOpen U) (hUsc : IsSimplyConnected U)
    (hUproper : U ≠ Set.univ) :
    ∃ f : ℂ → ℂ,
      Function.Injective f ∧ ¬ Dense (f '' U) ∧
        ∀ z ∈ U, deriv f z ≠ 0 := by
  wlog hUzero : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hUproper
    rcases hUproper with ⟨a, ha⟩
    specialize this (hUopen.vadd (-a)) (by simpa) (by simp [hUproper])
      (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf_injective, hf_not_dense, hf_deriv⟩
    refine ⟨f ∘ (-a + ·), hf_injective.comp (add_right_injective (-a)), ?_,
      fun z hz ↦ ?_⟩
    · simpa only [← image_vadd, Set.image_image] using hf_not_dense
    · simpa [Function.comp_def, deriv_comp_const_add] using
        hf_deriv (-a + z) (mapsTo_image _ _ hz)
  rcases Complex.exists_continuousOn_pow_eq hUsc hUopen continuousOn_id
      (by rwa [image_id]) two_ne_zero with ⟨f, hf_continuous, hf_square⟩
  replace hf_square : LeftInverse (· ^ 2) f := hf_square
  have hf_ne_zero : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hUzero).symm] using hf_square z
  have hf_strictDeriv :
      ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hf_continuous.continuousAt <| hUopen.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf_ne_zero z hz
    · exact .of_forall hf_square
  refine ⟨f, hf_square.injective, ?_, fun z hz ↦ ?_⟩
  · simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
    rcases hUsc.nonempty with ⟨x, hx⟩
    use -f x
    have hf_image_nhds : f '' U ∈ 𝓝 (f x) := by
      rw [← (hf_strictDeriv x hx).map_nhds_eq
        (by simpa using hf_ne_zero x hx)]
      exact Filter.image_mem_map <| hUopen.mem_nhds hx
    rw [nhds_neg, eventually_neg]
    filter_upwards [hf_image_nhds]
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
    obtain rfl : u = v := by
      rw [← hf_square v, huv]
      simp [hf_square u]
    refine hf_ne_zero u hu ?_
    linear_combination huv / 2
  · simpa [(hf_strictDeriv z hz).hasDerivAt.deriv] using hf_ne_zero z hz

/--
%%handwave
name:
  A proper simply connected plane domain has a bounded holomorphic coordinate
statement:
  Let $U\subsetneq\mathbb C$ be open and simply connected. Then $U$ carries a
  bounded nonconstant holomorphic function; indeed, one can choose it
  injective with image in the unit disk.
proof:
  Start with the injective square-root coordinate whose image is not dense.
  Choose a closed disk $\overline{B(c,\varepsilon)}$ disjoint from its image.
  The function $g(z)=\varepsilon/(f(z)-c)$ is injective and holomorphic on
  $U$, has nonzero derivative, and satisfies $|g(z)|<1$. Since every nonempty
  open subset of $\mathbb C$ contains two points, its range is nontrivial.
-/
theorem properSimplyConnectedPlaneDomain_has_boundedNonconstantHolomorphicFunction
    (U : TopologicalSpace.Opens ℂ)
    (hUsc : IsSimplyConnected (U : Set ℂ))
    (hUproper : (U : Set ℂ) ≠ Set.univ) :
    HasBoundedNonconstantHolomorphicFunction U := by
  rcases
      exists_injective_planeMap_not_dense_image_of_proper_simplyConnected
        U.isOpen hUsc hUproper with
    ⟨f, hf_injective, hf_not_dense, hf_deriv⟩
  obtain ⟨c, ε, hε, hsep⟩ :
      ∃ (c : ℂ) (ε : ℝ), 0 < ε ∧ ∀ z ∈ U, ε < dist (f z) c := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall]
      using hf_not_dense
  have hfc : ∀ z ∈ U, f z ≠ c := fun z hz ↦ by
    simpa using hε.trans (hsep z hz)
  let g : ℂ → ℂ := fun z ↦ ε / (f z - c)
  have hg_ball : MapsTo g U (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hε.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hsep z hz
    · simpa [sub_eq_zero] using hfc z hz
  have hg_injective : InjOn g U := by
    intro z hz w hw heq
    simpa [g, div_eq_mul_inv, hε.ne', hf_injective.eq_iff] using heq
  have hg_deriv : ∀ z ∈ U, deriv g z ≠ 0 := by
    intro z hz
    have hf_diff : DifferentiableAt ℂ f z :=
      differentiableAt_of_deriv_ne_zero (hf_deriv z hz)
    change deriv (fun w ↦ (ε : ℂ) / (f w - c)) z ≠ 0
    rw [(hasDerivAt_const z (ε : ℂ)).fun_div
      (hf_diff.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [hfc z hz, hε.ne', hf_deriv z hz, sub_eq_zero]
  let G : U → ℂ := fun z ↦ g z
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z
    have hg_mdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) g (z : ℂ) :=
      (differentiableAt_of_deriv_ne_zero (hg_deriv z z.2)).mdifferentiableAt
    have hsub_smooth : ContMDiff (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) ⊤ (Subtype.val : U → ℂ) :=
      contMDiff_subtype_val
    have hsub : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) (Subtype.val : U → ℂ) z :=
      hsub_smooth.contMDiffAt.mdifferentiableAt (by simp)
    change MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) (g ∘ Subtype.val) z
    exact hg_mdiff.comp z hsub
  · refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact le_of_lt
      (by simpa [Metric.mem_ball, dist_eq_norm] using hg_ball z.2)
  · rcases hUsc.nonempty with ⟨x, hx⟩
    rcases Metric.isOpen_iff.mp U.isOpen x hx with ⟨δ, hδ, hball⟩
    let y : ℂ := x + (δ / 2 : ℝ)
    have hy_ball : y ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, dist_eq_norm,
        show x + (δ / 2 : ℝ) - x = (δ / 2 : ℝ) by ring]
      simpa [Real.norm_eq_abs, abs_of_pos hδ] using half_lt_self hδ
    have hy : y ∈ U := hball hy_ball
    refine Set.nontrivial_of_mem_mem_ne
      (show G ⟨x, hx⟩ ∈ Set.range G from ⟨⟨x, hx⟩, rfl⟩)
      (show G ⟨y, hy⟩ ∈ Set.range G from ⟨⟨y, hy⟩, rfl⟩) ?_
    intro hGxy
    have hxy : x = y := hg_injective hx hy hGxy
    have hhalf : ((δ / 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (half_pos hδ).ne'
    apply hhalf
    dsimp [y] at hxy
    linear_combination -hxy

/--
%%handwave
name:
  A proper simply connected plane domain is noncompact
statement:
  If $U\subsetneq\mathbb C$ is open and simply connected, then $U$, with its
  subspace topology, is not compact.
proof:
  If $U$ were compact, its image under the inclusion into the Hausdorff plane
  would be closed. It is open and nonempty as well, so connectedness of
  $\mathbb C$ would give $U=\mathbb C$, contradicting properness.
-/
theorem properSimplyConnectedPlaneDomain_not_compactSpace
    (U : TopologicalSpace.Opens ℂ)
    (hUsc : IsSimplyConnected (U : Set ℂ))
    (hUproper : (U : Set ℂ) ≠ Set.univ) :
    ¬ CompactSpace U := by
  intro hcompact
  letI : CompactSpace U := hcompact
  have hUcompact : IsCompact (U : Set ℂ) := by
    have h := isCompact_univ.image
      (continuous_subtype_val : Continuous ((↑) : U → ℂ))
    simpa using h
  exact hUproper
    (IsClopen.eq_univ ⟨hUcompact.isClosed, U.isOpen⟩ hUsc.nonempty)

/--
%%handwave
name:
  Riemann mapping theorem
statement:
  Every nonempty simply connected proper open subset
  $U\subsetneq\mathbb C$ is biholomorphic to the unit disk $\mathbb D$.
proof:
  Regard $U$ as a Riemann surface and apply simply connected uniformization. The spherical alternative would make $U$ compact, contradicting that a proper simply connected plane domain is noncompact. For the planar alternative, [the square-root construction gives $U$ a bounded nonconstant holomorphic function](lean:JJMath.Uniformization.properSimplyConnectedPlaneDomain_has_boundedNonconstantHolomorphicFunction); pulling it back through a biholomorphism $\mathbb C\simeq U$ would contradict Liouville's theorem. Hence only the unit-disk alternative remains.
tags:
  milestone
-/
theorem riemannMappingTheorem
    (U : TopologicalSpace.Opens ℂ)
    (hUsc : IsSimplyConnected (U : Set ℂ))
    (hUproper : (U : Set ℂ) ≠ Set.univ) :
    BiholomorphicSurfaces U Complex.UnitDisc := by
  letI : SimplyConnectedSpace U := hUsc
  letI : RiemannSurface U :=
    riemannSurface_openSubset U hUsc.nonempty
      hUsc.isPathConnected.isConnected.isPreconnected
  rcases simplyConnected_riemannSurface_uniformization U with
    hsphere | hplane | hdisk
  · rcases hsphere with ⟨B⟩
    letI : CompactSpace U := Homeomorph.compactSpace B.toHomeomorph.symm
    exact
      (properSimplyConnectedPlaneDomain_not_compactSpace
        U hUsc hUproper inferInstance).elim
  · have hboundedU :=
      properSimplyConnectedPlaneDomain_has_boundedNonconstantHolomorphicFunction
        U hUsc hUproper
    have hboundedC : HasBoundedNonconstantHolomorphicFunction ℂ :=
      biholomorphicSurfaces_preserves_bounded_nonconstant_holomorphicFunction
        (BiholomorphicSurfaces.symm hplane) hboundedU
    exact
      (complexPlane_has_no_bounded_nonconstant_holomorphicFunction
        hboundedC).elim
  · exact hdisk

end

end Uniformization

end JJMath
