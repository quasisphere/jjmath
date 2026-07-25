import JJMath.ProjectiveGeometry.RiemannSphere
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Subpath

/-!
# Simple connectedness of the Riemann sphere

This file proves that the Riemann sphere is simply connected using its two
standard affine charts.  A loop is subdivided into finitely many pieces, each
contained in one chart.  After choosing a point away from the subdivision
vertices, every piece is replaced inside its chart by a path avoiding that
point.  The resulting loop omits one point and therefore contracts in an
affine coordinate after that point is moved to infinity.
-/

namespace JJMath

open Set
open scoped Topology unitInterval

noncomputable section

/--
%%handwave
name: Standard two-chart atlas of the Riemann sphere
statement:
  Index the standard sphere charts by a truth value: use the finite affine
  coordinate for one chart and the reciprocal coordinate at infinity for
  the other.
-/
def riemannSphereStandardChart : Bool → OpenPartialHomeomorph RiemannSphere ℂ
  | false => riemannSphereFiniteChart
  | true => riemannSphereInfinityChart

/--
%%handwave
name:
  Inverse standard sphere coordinates are continuous
statement:
  The inverse of either standard affine coordinate
  $z:\widehat{\mathbb C}\setminus\{\infty\}\to\mathbb C$ or
  $w:\widehat{\mathbb C}\setminus\{0\}\to\mathbb C$ is continuous on all
  of $\mathbb C$.
proof:
  Both standard coordinates have target equal to the whole complex plane, so
  the inverse-continuity property of an open partial homeomorphism applies
  globally.
-/
private theorem riemannSphereStandardChart_symm_continuous (i : Bool) :
    Continuous (riemannSphereStandardChart i).symm := by
  cases i with
  | false =>
      rw [← continuousOn_univ]
      simpa [riemannSphereStandardChart] using
        riemannSphereFiniteChart.continuousOn_symm
  | true =>
      rw [← continuousOn_univ]
      simpa [riemannSphereStandardChart] using
        riemannSphereInfinityChart.continuousOn_symm

/--
%%handwave
name:
  Paths in one standard sphere chart are homotopic
statement:
  Let $p,q:x\rightsquigarrow y$ be two paths on the Riemann sphere whose
  images lie in the same one of the affine coordinates $z$ or $w=1/z$.
  Then $p$ and $q$ are homotopic with their endpoints fixed.
proof:
  Express both paths in the selected coordinate. Since its target is all of
  $\mathbb C$, the two coordinate paths are endpoint-fixed homotopic in the
  contractible plane. Composing that homotopy with the inverse chart gives
  the required homotopy on the sphere.
-/
theorem riemannSphere_paths_homotopic_in_standardChart
    (i : Bool) {x y : RiemannSphere} (p q : Path x y)
    (hp : Set.range p ⊆ (riemannSphereStandardChart i).source)
    (hq : Set.range q ⊆ (riemannSphereStandardChart i).source) :
    Path.Homotopic p q := by
  let e := riemannSphereStandardChart i
  let pcoord : Path (e x) (e y) :=
    p.map' (e.continuousOn.mono hp)
  let qcoord : Path (e x) (e y) :=
    q.map' (e.continuousOn.mono hq)
  have hcoord : Path.Homotopic pcoord qcoord :=
    SimplyConnectedSpace.paths_homotopic pcoord qcoord
  rcases hcoord with ⟨F⟩
  refine ⟨{
    toFun := fun z ↦ e.symm (F z)
    continuous_toFun :=
      (riemannSphereStandardChart_symm_continuous i).comp F.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_
  }⟩
  · intro t
    calc
      e.symm (F (0, t)) = e.symm (pcoord t) :=
        congrArg e.symm (F.map_zero_left t)
      _ = p t := e.left_inv (hp ⟨t, rfl⟩)
  · intro t
    calc
      e.symm (F (1, t)) = e.symm (qcoord t) :=
        congrArg e.symm (F.map_one_left t)
      _ = q t := e.left_inv (hq ⟨t, rfl⟩)
  · intro s t ht
    calc
      e.symm (F (s, t)) = e.symm (pcoord t) :=
        congrArg e.symm (F.eq_fst s ht)
      _ = p t := e.left_inv (hp ⟨t, rfl⟩)

/--
%%handwave
name:
  Every spherical path has a finite two-chart subdivision
statement:
  Every path $\gamma:[0,1]\to\widehat{\mathbb C}$ admits subdivision times
  $0=t_0\leq\cdots\leq t_m=1$ such that the image of each restricted path
  $\gamma|_{[t_j,t_{j+1}]}$ lies entirely in either the affine chart
  $\widehat{\mathbb C}\setminus\{\infty\}$ or the reciprocal chart
  $\widehat{\mathbb C}\setminus\{0\}$.
proof:
  The inverse images of the two chart domains form an open cover of the
  compact unit interval. Apply the finite monotone subdivision theorem for an
  open cover and translate containment of each parameter interval into
  containment of the corresponding subpath range.
-/
theorem riemannSphere_path_exists_standardChart_subdivision
    {x y : RiemannSphere} (gamma : Path x y) :
    ∃ (m : ℕ) (t : Fin (m + 1) → unitInterval),
      t 0 = 0 ∧ t (Fin.last m) = 1 ∧
      (∀ k : Fin m, (t k.castSucc : ℝ) ≤ (t k.succ : ℝ)) ∧
      ∀ k : Fin m, ∃ i : Bool,
        Set.range (gamma.subpath (t k.castSucc) (t k.succ)) ⊆
          (riemannSphereStandardChart i).source := by
  classical
  let c : Bool → Set unitInterval := fun i ↦
    gamma ⁻¹' (riemannSphereStandardChart i).source
  have hc_open : ∀ i, IsOpen (c i) := by
    intro i
    exact (riemannSphereStandardChart i).open_source.preimage gamma.continuous
  have hc_cover : Set.univ ⊆ ⋃ i, c i := by
    intro s _hs
    induction hvalue : gamma s using OnePoint.rec with
    | infty =>
        refine Set.mem_iUnion.mpr ⟨true, ?_⟩
        simp [c, riemannSphereStandardChart, hvalue]
    | coe z =>
        refine Set.mem_iUnion.mpr ⟨false, ?_⟩
        simp [c, riemannSphereStandardChart, hvalue]
  obtain ⟨tNat, ht0, htmono, ⟨m, hm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := c) hc_open hc_cover
  let t : Fin (m + 1) → unitInterval := fun k ↦ tNat k
  refine ⟨m, t, ht0, hm m le_rfl, ?_, ?_⟩
  · intro k
    exact htmono (Nat.le_succ k)
  · intro k
    rcases hsub k with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [Path.range_subpath_of_le]
    · rintro z ⟨s, hs, rfl⟩
      exact hi hs
    · exact htmono (Nat.le_succ k)

/--
%%handwave
name:
  A path in one sphere chart can be pushed off a nonendpoint
statement:
  Let $\gamma:x\rightsquigarrow y$ lie in one standard affine chart of the
  Riemann sphere, and let $p$ differ from both $x$ and $y$. Then $\gamma$ is
  endpoint-fixed homotopic, inside that chart, to a path that avoids $p$.
proof:
  If $p$ is outside the chart, keep the original path. Otherwise pass to the
  affine coordinate. The punctured plane $\mathbb C\setminus\{p\}$ is path
  connected, so join the two endpoint coordinates by a path avoiding the
  puncture. Mapping it back gives the replacement, and contractibility of the
  full coordinate plane gives the endpoint-fixed homotopy.
-/
theorem riemannSphere_path_homotopic_avoiding_point_in_standardChart
    (i : Bool) {x y p : RiemannSphere} (gamma : Path x y)
    (hgamma : Set.range gamma ⊆ (riemannSphereStandardChart i).source)
    (hxp : x ≠ p) (hyp : y ≠ p) :
    ∃ eta : Path x y, Path.Homotopic gamma eta ∧ ∀ s, eta s ≠ p := by
  let e := riemannSphereStandardChart i
  have hxsource : x ∈ e.source := hgamma gamma.source_mem_range
  have hysource : y ∈ e.source := hgamma gamma.target_mem_range
  by_cases hpsource : p ∈ e.source
  · have hxcoord : e x ≠ e p := by
      intro h
      exact hxp (e.injOn hxsource hpsource h)
    have hycoord : e y ≠ e p := by
      intro h
      exact hyp (e.injOn hysource hpsource h)
    have hpunctured : IsPathConnected ({e p}ᶜ : Set ℂ) :=
      isPathConnected_compl_singleton_of_one_lt_rank
        (Complex.rank_real_complex ▸ (by norm_num : (1 : Cardinal) < 2))
        (e p)
    have hjoined : JoinedIn ({e p}ᶜ : Set ℂ) (e x) (e y) :=
      hpunctured.joinedIn (e x) (by simpa) (e y) (by simpa)
    let beta : Path (e x) (e y) := hjoined.somePath
    let eta : Path x y :=
      { toFun := fun s ↦ e.symm (beta s)
        continuous_toFun :=
          (riemannSphereStandardChart_symm_continuous i).comp beta.continuous
        source' := by
          rw [beta.source]
          exact e.left_inv hxsource
        target' := by
          rw [beta.target]
          exact e.left_inv hysource }
    have heta_source : Set.range eta ⊆ e.source := by
      rintro z ⟨s, rfl⟩
      apply e.map_target
      cases i <;> simp [e, riemannSphereStandardChart]
    refine ⟨eta,
      riemannSphere_paths_homotopic_in_standardChart i gamma eta
        hgamma heta_source, ?_⟩
    intro s heta_p
    have hbeta_target : beta s ∈ e.target := by
      cases i <;> simp [e, riemannSphereStandardChart]
    have hcoord_eq : beta s = e p := by
      calc
        beta s = e (e.symm (beta s)) := (e.right_inv hbeta_target).symm
        _ = e p := congrArg e heta_p
    exact hjoined.somePath_mem s (by simpa [hcoord_eq])
  · refine ⟨gamma, Path.Homotopic.refl gamma, ?_⟩
    intro s hgamma_p
    apply hpsource
    rw [← hgamma_p]
    exact hgamma ⟨s, rfl⟩

/--
%%handwave
name:
  A finite concatenation of avoiding paths avoids the point
statement:
  Let $x_0,\ldots,x_n$ all differ from $p$, and for every $j<n$ let
  $\gamma_j:x_j\rightsquigarrow x_{j+1}$ avoid $p$. Then the finite
  concatenation $\gamma_0*\cdots*\gamma_{n-1}$ also avoids $p$.
proof:
  Induct on the number of paths. A concatenation takes all its values in the
  union of the ranges of its prefix and its last path, and both ranges avoid
  $p$ by the induction hypothesis.
-/
theorem path_concat_avoids_point
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (vertices : Fin (n + 1) → X)
    (paths : (k : Fin n) → Path (vertices k.castSucc) (vertices k.succ))
    {p : X} (hvertices : ∀ k, vertices k ≠ p)
    (hpaths : ∀ k s, paths k s ≠ p) :
    ∀ s, Path.concat vertices paths s ≠ p := by
  induction n with
  | zero =>
      intro s
      rw [Path.concat_zero]
      exact hvertices 0
  | succ n ih =>
      rw [Path.concat_succ]
      intro s hs
      have hsrange :
          ((Path.concat (vertices ∘ Fin.castSucc)
              (fun k ↦ paths k.castSucc)).trans (paths (Fin.last n))) s ∈
            Set.range
              ((Path.concat (vertices ∘ Fin.castSucc)
                (fun k ↦ paths k.castSucc)).trans (paths (Fin.last n))) :=
        ⟨s, rfl⟩
      rw [Path.trans_range] at hsrange
      rcases hsrange with hprefix | hlast
      · rcases hprefix with ⟨u, hu⟩
        exact (ih (vertices := vertices ∘ Fin.castSucc)
          (paths := fun k ↦ paths k.castSucc)
          (fun k ↦ hvertices k.castSucc)
          (fun k t ↦ hpaths k.castSucc t) u) (hu.trans hs)
      · rcases hlast with ⟨u, hu⟩
        exact hpaths (Fin.last n) u (hu.trans hs)

/--
%%handwave
name:
  Every spherical loop is homotopic to a loop omitting a point
statement:
  For every loop $\gamma:x\rightsquigarrow x$ on the Riemann sphere, there
  are a point $p\in\widehat{\mathbb C}$ and a loop
  $\eta:x\rightsquigarrow x$ such that $\gamma$ is endpoint-fixed homotopic
  to $\eta$ and $\eta(t)\ne p$ for every $t\in[0,1]$.
proof:
  Subdivide $\gamma$ into finitely many pieces lying in the two standard
  affine charts. Choose $p$ away from the finitely many subdivision vertices.
  In each selected chart replace the corresponding subpath by an
  endpoint-matching path that avoids $p$. Concatenate the local homotopies;
  the standard concatenation homotopy identifies the concatenated original
  pieces with $\gamma$.
-/
theorem riemannSphere_loop_homotopic_avoiding_point
    {x : RiemannSphere} (gamma : Path x x) :
    ∃ (p : RiemannSphere) (eta : Path x x),
      Path.Homotopic gamma eta ∧ ∀ s, eta s ≠ p := by
  classical
  rcases riemannSphere_path_exists_standardChart_subdivision gamma with
    ⟨m, t, ht0, ht1, _htmono, hcharts⟩
  let vertices : Fin (m + 1) → RiemannSphere := gamma ∘ t
  obtain ⟨p, hp⟩ : ∃ p : RiemannSphere, p ∈ (Set.range vertices)ᶜ :=
    (Set.finite_range vertices).infinite_compl.nonempty
  have hvertices : ∀ k, vertices k ≠ p := by
    intro k hk
    exact hp ⟨k, hk⟩
  let original : (k : Fin m) →
      Path (vertices k.castSucc) (vertices k.succ) :=
    fun k ↦ gamma.subpath (t k.castSucc) (t k.succ)
  have hlocal : ∀ k : Fin m,
      ∃ eta : Path (vertices k.castSucc) (vertices k.succ),
        Path.Homotopic (original k) eta ∧ ∀ s, eta s ≠ p := by
    intro k
    rcases hcharts k with ⟨i, hi⟩
    exact
      riemannSphere_path_homotopic_avoiding_point_in_standardChart
        i (original k) hi (hvertices k.castSucc) (hvertices k.succ)
  choose replacement hreplacement_hom hreplacement_avoids using hlocal
  have hconcat :
      Path.Homotopic
        (Path.concat vertices original)
        (Path.concat vertices replacement) :=
    Path.Homotopic.concat_hcomp vertices original replacement
      hreplacement_hom
  have hx0 : x = vertices 0 := by
    simp [vertices, ht0]
  have hx1 : x = vertices (Fin.last m) := by
    simp [vertices, ht1]
  let eta : Path x x :=
    (Path.concat vertices replacement).cast hx0 hx1
  have hconcat_original :
      Path.Homotopic (Path.concat vertices original)
        (gamma.subpath (t 0) (t (Fin.last m))) := by
    exact Path.Homotopic.concat_subpath gamma t
  have hfull :
      (gamma.subpath (t 0) (t (Fin.last m))).cast hx0 hx1 = gamma := by
    ext s
    simp [Path.subpath, ht0, ht1]
  have hcast_original :
      Path.Homotopic
        ((Path.concat vertices original).cast hx0 hx1) gamma := by
    have h := hconcat_original.pathCast hx0 hx1
    exact hfull ▸ h
  have hcast_replacement :
      Path.Homotopic
        ((Path.concat vertices original).cast hx0 hx1) eta := by
    simpa [eta] using hconcat.pathCast hx0 hx1
  refine ⟨p, eta, hcast_original.symm.trans hcast_replacement, ?_⟩
  intro s
  exact path_concat_avoids_point vertices replacement hvertices
    hreplacement_avoids s

/--
%%handwave
name:
  A spherical loop avoiding infinity is null-homotopic
statement:
  If a loop $\gamma:x\rightsquigarrow x$ on the Riemann sphere satisfies
  $\gamma(t)\ne\infty$ for every $t$, then $\gamma$ is endpoint-fixed
  homotopic to the constant loop at $x$.
proof:
  The loop and the constant loop both lie in the affine chart
  $\widehat{\mathbb C}\setminus\{\infty\}\cong\mathbb C$. Any two paths with
  the same endpoints in the contractible plane are homotopic.
-/
theorem riemannSphere_loop_nullhomotopic_of_avoids_infty
    {x : RiemannSphere} (gamma : Path x x)
    (hgamma : ∀ s, gamma s ≠ OnePoint.infty) :
    Path.Homotopic gamma (Path.refl x) := by
  apply riemannSphere_paths_homotopic_in_standardChart false gamma (Path.refl x)
  · rintro z ⟨s, rfl⟩
    simp [riemannSphereStandardChart, hgamma s]
  · rintro z ⟨s, rfl⟩
    have hx : x ≠ OnePoint.infty := by
      simpa using hgamma 0
    simp [riemannSphereStandardChart, hx]

/--
%%handwave
name:
  A spherical loop omitting one point is null-homotopic
statement:
  Let $p\in\widehat{\mathbb C}$. If a loop
  $\gamma:x\rightsquigarrow x$ satisfies $\gamma(t)\ne p$ for every
  $t\in[0,1]$, then $\gamma$ is endpoint-fixed homotopic to the constant loop
  at $x$.
proof:
  If $p=\infty$, use the affine chart directly. If $p=c\in\mathbb C$,
  translate by $-c$ and then apply spherical inversion; this sends $p$ to
  infinity. The transformed loop contracts in the affine chart, and composing
  the contraction with the inverse homeomorphism contracts the original
  loop.
-/
theorem riemannSphere_loop_nullhomotopic_of_avoids_point
    {x p : RiemannSphere} (gamma : Path x x)
    (hgamma : ∀ s, gamma s ≠ p) :
    Path.Homotopic gamma (Path.refl x) := by
  induction p using OnePoint.rec with
  | infty =>
      exact riemannSphere_loop_nullhomotopic_of_avoids_infty gamma hgamma
  | coe c =>
      let T : RiemannSphere ≃ₜ RiemannSphere :=
        Homeomorph.onePointCongr (complexTranslationHomeomorph (-c))
      let A : RiemannSphere ≃ₜ RiemannSphere :=
        T.trans riemannSphereInvHomeomorph
      have hAc : A (c : RiemannSphere) = OnePoint.infty := by
        change
          riemannSphereInv (((c + -c : ℂ) : ℂ) : RiemannSphere) =
            OnePoint.infty
        simp
      let transformed : Path (A x) (A x) := gamma.map A.continuous
      have htransformed : ∀ s, transformed s ≠ OnePoint.infty := by
        intro s hs
        apply hgamma s
        apply A.injective
        simpa [transformed, hAc] using hs
      have hnull :
          Path.Homotopic transformed (Path.refl (A x)) :=
        riemannSphere_loop_nullhomotopic_of_avoids_infty
          transformed htransformed
      have hback := hnull.map (⟨A.symm, A.symm.continuous⟩ :
        C(RiemannSphere, RiemannSphere))
      have hxx : A.symm (A x) = x := A.symm_apply_apply x
      have hback' := hback.pathCast hxx.symm hxx.symm
      have hleft :
          (transformed.map A.symm.continuous).cast hxx.symm hxx.symm =
            gamma := by
        apply Path.ext
        funext s
        change A.symm (A (gamma s)) = gamma s
        exact A.symm_apply_apply (gamma s)
      have hright :
          ((Path.refl (A x)).map A.symm.continuous).cast
              hxx.symm hxx.symm =
            Path.refl x := by
        apply Path.ext
        funext s
        change A.symm (A x) = x
        exact hxx
      rw [hleft, hright] at hback'
      exact hback'

/--
%%handwave
name:
  The Riemann sphere is simply connected
statement:
  The Riemann sphere $\widehat{\mathbb C}$ is simply connected.
proof:
  Every loop is homotopic to a loop omitting one point. Move that point to
  infinity by a spherical translation and inversion. The resulting loop lies
  in the affine plane and contracts there by a convex homotopy. Therefore
  every loop is null-homotopic, and the sphere is path connected.
tags:
  milestone
-/
theorem riemannSphere_simplyConnectedSpace :
    SimplyConnectedSpace RiemannSphere := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro x gamma
  rcases riemannSphere_loop_homotopic_avoiding_point gamma with
    ⟨p, eta, hgamma_eta, heta⟩
  exact hgamma_eta.trans
    (riemannSphere_loop_nullhomotopic_of_avoids_point eta heta)

end

end JJMath
