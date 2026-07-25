import JJMath.Quasiconformal.LocalSobolev
import JJMath.Topology.PlanarDegree

/-!
# Planar maps of bounded distortion

This file separates the almost-everywhere analytic condition of bounded
distortion from the public notions of quasiregular and quasiconformal maps.
The former is invariant under changing a representative on a null set.  A
quasiregular map additionally names a continuous, nonconstant representative,
while a quasiconformal map is an orientation-preserving homeomorphism.
-/

namespace JJMath

open MeasureTheory Set
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Ambient representative of a planar homeomorphism
statement:
  For a homeomorphism $F:\Omega\to\Omega'$ between planar sets, define its
  ambient representative $\widetilde F:\mathbb C\to\mathbb C$ by
  $$
    \widetilde F(z)=
      \begin{cases}
        F(z),&z\in\Omega,\\
        0,&z\notin\Omega.
      \end{cases}
  $$
-/
def ambientMap {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') : ℂ → ℂ := by
  classical
  exact fun z ↦ if hz : z ∈ Ω then (F ⟨z, hz⟩ : ℂ) else 0

/--
%%handwave
name:
  Ambient representative agrees with the planar homeomorphism
statement:
  For every $z\in\Omega$, the ambient representative of
  $F:\Omega\to\Omega'$ takes the value $F(z)$.
proof:
  This is the inside-source branch of the extension by zero.
-/
@[simp]
theorem ambientMap_apply {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (z : Ω) :
    ambientMap F z = F z := by
  simp [ambientMap, z.2]

/--
%%handwave
name:
  Ambient representatives of inverse homeomorphisms cancel on the source
statement:
  If $F:\Omega\to\Omega'$ is a homeomorphism and $z\in\Omega$, then
  $$
    F^{-1}(F(z))=z
  $$
  for the ambient representatives of $F$ and $F^{-1}$.
proof:
  Both ambient representatives agree with their subtype homeomorphisms at the relevant points, where the usual inverse identity applies.
-/
@[simp]
theorem ambientMap_symm_apply_ambientMap
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (z : Ω) :
    ambientMap F.symm (ambientMap F z) = z := by
  rw [ambientMap_apply F z]
  rw [ambientMap_apply F.symm (F z)]
  exact congrArg Subtype.val (F.symm_apply_apply z)

/--
%%handwave
name:
  Ambient representative is continuous on its source
statement:
  If $F:\Omega\to\Omega'$ is a homeomorphism, then its ambient
  representative is continuous on $\Omega$.
proof:
  Restrict to $\Omega$. There the ambient representative is the composition
  of $F$ with the continuous inclusion $\Omega'\hookrightarrow\mathbb C$.
-/
theorem continuousOn_ambientMap {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') :
    ContinuousOn (ambientMap F) Ω := by
  rw [continuousOn_iff_continuous_restrict]
  have h : Continuous (fun z : Ω => ((F z : Ω') : ℂ)) :=
    continuous_subtype_val.comp F.continuous
  convert h using 1
  funext z
  exact ambientMap_apply F z

/--
%%handwave
name:
  Ambient image of an open source subset is open
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism and suppose $\Omega'$ is
  open in $\mathbb C$. If $U$ is open in $\mathbb C$ and $U\subseteq\Omega$,
  then $F(U)$ is open in $\mathbb C$.
proof:
  Regard $U$ as an open subset of the subtype $\Omega$. Its image under $F$
  is open in $\Omega'$, and the inclusion of the open set $\Omega'$ into
  $\mathbb C$ is an open map.
-/
theorem isOpen_ambientMap_image
    {Ω Ω' U : Set ℂ} (F : Ω ≃ₜ Ω')
    (hΩ' : IsOpen Ω') (hU : IsOpen U) (hUΩ : U ⊆ Ω) :
    IsOpen (ambientMap F '' U) := by
  let UΩ : Set Ω := ((↑) : Ω → ℂ) ⁻¹' U
  have hUΩ_open : IsOpen UΩ := hU.preimage continuous_subtype_val
  have hFU_open : IsOpen (F '' UΩ) := F.isOpenMap _ hUΩ_open
  have hval_open : IsOpen (((↑) : Ω' → ℂ) '' (F '' UΩ)) :=
    hΩ'.isOpenMap_subtype_val _ hFU_open
  have heq : ((↑) : Ω' → ℂ) '' (F '' UΩ) = ambientMap F '' U := by
    ext y
    constructor
    · rintro ⟨w, ⟨z, hzU, rfl⟩, rfl⟩
      refine ⟨z, hzU, ?_⟩
      exact ambientMap_apply F z
    · rintro ⟨x, hxU, rfl⟩
      let z : Ω := ⟨x, hUΩ hxU⟩
      refine ⟨F z, ⟨z, ?_, rfl⟩, ?_⟩
      · exact hxU
      · exact (ambientMap_apply F z).symm
  rwa [heq] at hval_open

/--
%%handwave
name:
  Measurability of an ambient homeomorphic image
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism between measurable planar
  domains. If $A\subseteq\Omega$ is measurable, then $F(A)$ is measurable
  in $\mathbb C$.
proof:
  Regard $A$ as a measurable subset of the subtype $\Omega$. Its image under the measurable equivalence $F$ is measurable in $\Omega'$, and the inclusion of the measurable subtype $\Omega'$ into $\mathbb C$ is a measurable embedding.
-/
theorem MeasurableSet.ambientMap_image
    {Ω Ω' A : Set ℂ} (F : Ω ≃ₜ Ω')
    (hΩ' : MeasurableSet Ω') (hA : MeasurableSet A) (hAΩ : A ⊆ Ω) :
    MeasurableSet (ambientMap F '' A) := by
  let AΩ : Set Ω := ((↑) : Ω → ℂ) ⁻¹' A
  have hAΩ_meas : MeasurableSet AΩ := measurable_subtype_coe hA
  have hFA_meas : MeasurableSet (F '' AΩ) :=
    F.toMeasurableEquiv.measurableSet_image.mpr hAΩ_meas
  have hval_meas : MeasurableSet (((↑) : Ω' → ℂ) '' (F '' AΩ)) :=
    (MeasurableEmbedding.subtype_coe hΩ').measurableSet_image' hFA_meas
  have heq : ((↑) : Ω' → ℂ) '' (F '' AΩ) = ambientMap F '' A := by
    ext y
    constructor
    · rintro ⟨w, ⟨z, hzA, rfl⟩, rfl⟩
      refine ⟨z, hzA, ?_⟩
      exact ambientMap_apply F z
    · rintro ⟨x, hxA, rfl⟩
      let z : Ω := ⟨x, hAΩ hxA⟩
      refine ⟨F z, ⟨z, ?_, rfl⟩, ?_⟩
      · exact hxA
      · exact (ambientMap_apply F z).symm
  rwa [heq] at hval_meas

/--
%%handwave
name:
  Frontier of a compact domain image comes from the source frontier
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism with $\Omega'$ open in
  $\mathbb C$. If $A\subseteq\Omega$ is compact, then
  $$
  \partial F(A)\subseteq F(\partial A),
  $$
  where both frontiers are taken in $\mathbb C$.
proof:
  The image is compact, so each of its frontier points lies in the image.
  If its source point were interior to $A$, [the image of that open interior is open](lean:JJMath.Quasiconformal.isOpen_ambientMap_image) and would put the image point in the interior of $F(A)$, a contradiction.
-/
theorem frontier_ambientMap_image_subset
    {Ω Ω' s : Set ℂ} (F : Ω ≃ₜ Ω')
    (hΩ' : IsOpen Ω') (hs : IsCompact s) (hsΩ : s ⊆ Ω) :
    frontier (ambientMap F '' s) ⊆ ambientMap F '' frontier s := by
  have himage_compact : IsCompact (ambientMap F '' s) :=
    hs.image_of_continuousOn ((continuousOn_ambientMap F).mono hsΩ)
  intro y hy
  have hy_image : y ∈ ambientMap F '' s := by
    rw [← himage_compact.isClosed.closure_eq]
    exact frontier_subset_closure hy
  rcases hy_image with ⟨x, hxs, rfl⟩
  refine ⟨x, ?_, rfl⟩
  rw [frontier, mem_diff]
  refine ⟨?_, ?_⟩
  · rw [hs.isClosed.closure_eq]
    exact hxs
  · intro hxint
    have hopen : IsOpen (ambientMap F '' interior s) :=
      isOpen_ambientMap_image F hΩ' isOpen_interior
        (interior_subset.trans hsΩ)
    have hxmapped : ambientMap F x ∈ ambientMap F '' interior s :=
      ⟨x, hxint, rfl⟩
    have himage_subset : ambientMap F '' interior s ⊆ ambientMap F '' s :=
      image_mono interior_subset
    have hxint_image : ambientMap F x ∈ interior (ambientMap F '' s) :=
      mem_interior_iff_mem_nhds.mpr <|
        Filter.mem_of_superset (hopen.mem_nhds hxmapped) himage_subset
    rw [frontier, mem_diff] at hy
    exact hy.2 hxint_image

/--
%%handwave
name:
  Source translation of a planar homeomorphism
statement:
  For a homeomorphism $F:\Omega\to\Omega'$ and $c\in\mathbb C$, define
  $F_c:\{z:z+c\in\Omega\}\to\Omega'$ by
  $$
    F_c(z)=F(z+c).
  $$
-/
def precompAddRightHomeomorph {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (c : ℂ) :
    ((fun z : ℂ => z + c) ⁻¹' Ω) ≃ₜ Ω' :=
  ((Homeomorph.addRight c).subtype (fun _ => Iff.rfl)).trans F

/--
%%handwave
name:
  Value of a source-translated planar homeomorphism
statement:
  If $F:\Omega\to\Omega'$ is a homeomorphism and
  $F_c(z)=F(z+c)$ on $\{z:z+c\in\Omega\}$, then $F_c(z)=F(z+c)$ for every
  point of its source.
proof:
  Expand the subtype homeomorphism induced by translation and then its
  composition with $F$.
-/
@[simp]
theorem precompAddRightHomeomorph_apply
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (c : ℂ)
    (z : ((fun w : ℂ => w + c) ⁻¹' Ω)) :
    (precompAddRightHomeomorph F c z : ℂ) = F ⟨z + c, z.2⟩ := by
  rfl

/--
%%handwave
name:
  Ambient representative of a source-translated homeomorphism
statement:
  For every $z\in\mathbb C$, the ambient representative of the translated
  homeomorphism $F_c$ satisfies
  $$
  F_c(z)=F(z+c),
  $$
  where both sides are extended by zero outside their respective sources.
proof:
  If $z+c\in\Omega$, both sides equal the homeomorphism value $F(z+c)$. If
  $z+c\notin\Omega$, both zero extensions vanish.
-/
theorem ambientMap_precompAddRightHomeomorph
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (c z : ℂ) :
    ambientMap (precompAddRightHomeomorph F c) z = ambientMap F (z + c) := by
  by_cases hz : z + c ∈ Ω
  · have hz' : z ∈ (fun w : ℂ => w + c) ⁻¹' Ω := hz
    simp only [ambientMap, dif_pos hz', dif_pos hz]
    exact precompAddRightHomeomorph_apply F c ⟨z, hz'⟩
  · have hz' : z ∉ (fun w : ℂ => w + c) ⁻¹' Ω := hz
    simp [ambientMap, hz, hz']

/--
%%handwave
name:
  Ambient representative is injective on its source
statement:
  If $F:\Omega\to\Omega'$ is a homeomorphism, then its ambient
  representative is injective when restricted to $\Omega$.
proof:
  On $\Omega$ the ambient representative agrees with $F$, which is
  injective.
-/
theorem ambientMap_injOn {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') :
    Set.InjOn (ambientMap F) Ω := by
  intro x hx y hy hxy
  have hFxy : F ⟨x, hx⟩ = F ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa [ambientMap, hx, hy] using hxy
  exact congrArg Subtype.val (F.injective hFxy)

/--
%%handwave
name:
  Quantitative bounded distortion on a planar domain
statement:
  A map $f:\Omega\to\mathbb C$ has $K$-bounded distortion if it belongs to
  $W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ with some weak differential
  $Df$ satisfying
  $$
    \lVert Df(z)\rVert_{\mathrm{op}}^2
      \leq K\,\operatorname{Jac}f(z)
  $$
  for almost every $z\in\Omega$.
-/
def HasKBoundedDistortionOn (K : ℝ) (Ω : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ df : ℂ → ℂ →L[ℝ] ℂ,
    IsLocalW12On Ω f df ∧
      ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
        ‖df z‖ ^ 2 ≤ K * weakJacobian (df z)

/--
%%handwave
name:
  Independence of bounded distortion from the weak differential
statement:
  Suppose $f:\Omega\to\mathbb C$ has $K$-bounded distortion. Then every weak
  differential $Dg$ witnessing
  $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ satisfies
  $$
    \lVert Dg(z)\rVert_{\mathrm{op}}^2
      \leq K\,\operatorname{Jac}g(z)
  $$
  for almost every $z\in\Omega$.
proof:
  Weak differentials of the same local Sobolev map agree almost everywhere,
  so their operator norms and real Jacobians agree almost everywhere.
-/
theorem HasKBoundedDistortionOn.distortion_of_weakDifferential
    {K : ℝ} {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HasKBoundedDistortionOn K Ω f)
    {dg : ℂ → ℂ →L[ℝ] ℂ} (hdg : IsLocalW12On Ω f dg) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
      ‖dg z‖ ^ 2 ≤ K * weakJacobian (dg z) := by
  obtain ⟨df, hdf, hdist⟩ := hf
  have heq := hdf.weakDifferential_ae_eq hdg
  filter_upwards [heq, hdist] with z hz hdistz
  rw [← hz]
  exact hdistz

/--
%%handwave
name:
  Quantitative bounded distortion of a planar homeomorphism
statement:
  A homeomorphism $F:\Omega\to\Omega'$ has $K$-bounded distortion when,
  regarded as a complex-valued map on $\Omega$, it belongs locally to
  $W^{1,2}$ and has a weak differential $DF$ satisfying
  $$
    \lVert DF(z)\rVert_{\mathrm{op}}^2
      \leq K\,\operatorname{Jac}F(z)
  $$
  for almost every $z\in\Omega$.
-/
def HasKBoundedDistortionBetween (K : ℝ) {Ω Ω' : Set ℂ}
    (F : Ω ≃ₜ Ω') : Prop :=
  HasKBoundedDistortionOn K Ω (ambientMap F)

/--
%%handwave
name:
  Quantitative planar quasiconformality
statement:
  A homeomorphism $F:\Omega\to\Omega'$ between open planar domains is
  $K$-quasiconformal if $K\geq1$, it preserves planar orientation, and it has
  $K$-bounded distortion.
-/
def IsKQuasiconformalBetween (K : ℝ) {Ω Ω' : Set ℂ}
    (F : Ω ≃ₜ Ω') : Prop :=
  1 ≤ K ∧
    IsOpen Ω' ∧
      PreservesPlanarOrientation F ∧
        HasKBoundedDistortionBetween K F

/--
%%handwave
name:
  A quasiconformal homeomorphism has bounded distortion between its domains
statement:
  Every $K$-quasiconformal homeomorphism
  $F:\Omega\to\Omega'$ has $K$-bounded distortion as a homeomorphism between
  the two planar domains.
proof:
  This is the bounded-distortion clause in the definition of
  $K$-quasiconformality.
-/
theorem IsKQuasiconformalBetween.hasKBoundedDistortionBetween
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) :
    HasKBoundedDistortionBetween K F :=
  hF.2.2.2

/--
%%handwave
name:
  A quasiconformal homeomorphism has bounded distortion
statement:
  Every $K$-quasiconformal homeomorphism
  $F:\Omega\to\Omega'$ has $K$-bounded distortion on $\Omega$ when regarded
  as a complex-valued map.
proof:
  This is the analytic clause in the definition of quasiconformality.
-/
theorem IsKQuasiconformalBetween.hasKBoundedDistortionOn
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) :
    HasKBoundedDistortionOn K Ω (ambientMap F) :=
  hF.hasKBoundedDistortionBetween

/--
%%handwave
name:
  Planar quasiconformality is local under restriction
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal, let $U\subseteq\Omega$ and
  $V$ be open, and let $G:U\to V$ be a homeomorphism satisfying $G(z)=F(z)$
  for every $z\in U$. Then $G$ is $K$-quasiconformal.
proof:
  Use [orientation preservation is local under restriction](lean:JJMath.Quasiconformal.PreservesPlanarOrientation.restrict). Restrict the local Sobolev data and distortion inequality to $U$; the two ambient representatives agree there, so almost-everywhere representative invariance supplies the required weak differential for $G$.
-/
theorem IsKQuasiconformalBetween.restrict
    {K : ℝ} {Ω Ω' U V : Set ℂ} {F : Ω ≃ₜ Ω'} {G : U ≃ₜ V}
    (hF : IsKQuasiconformalBetween K F)
    (hU : IsOpen U) (hV : IsOpen V) (hUΩ : U ⊆ Ω)
    (hG : ∀ z : U, (G z : ℂ) = F ⟨z, hUΩ z.2⟩) :
    IsKQuasiconformalBetween K G := by
  refine ⟨hF.1, hV, hF.2.2.1.restrict hU hUΩ hG, ?_⟩
  obtain ⟨df, hW, hdist⟩ := hF.hasKBoundedDistortionBetween
  have hWmono := hW.mono hU hUΩ
  have hambient :
      ambientMap G =ᵐ[MeasureTheory.volume.restrict U] ambientMap F := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    simp only [ambientMap]
    rw [dif_pos hz, dif_pos (hUΩ hz)]
    exact hG ⟨z, hz⟩
  refine ⟨df, hWmono.congr_ae hambient, ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset hUΩ hdist

/--
%%handwave
name:
  The metric distortion inequality is independent of the weak differential
statement:
  If a planar homeomorphism is $K$-quasiconformal using one weak differential,
  then every other local $W^{1,2}$ weak differential of the same ambient map
  satisfies the same inequality almost everywhere.
proof:
  Weak differentials are unique almost everywhere, so their operator norms and
  real Jacobians agree almost everywhere.
-/
theorem IsKQuasiconformalBetween.distortion_of_weakDifferential
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {dg : ℂ → ℂ →L[ℝ] ℂ}
    (hdg : IsLocalW12On Ω (ambientMap F) dg) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
      ‖dg z‖ ^ 2 ≤ K * weakJacobian (dg z) :=
  hF.hasKBoundedDistortionOn.distortion_of_weakDifferential hdg

/--
%%handwave
name:
  The bounded Beltrami equation gives a quasiconformal homeomorphism
statement:
  Let $F:\Omega\to\Omega'$ be an orientation-preserving homeomorphism with a
  local $W^{1,2}$ weak differential satisfying
  $\partial_{\bar z}f=\mu\,\partial_z f$. If $|\mu|\leq k$ almost everywhere and
  $0\leq k<1$, then $F$ is $K$-quasiconformal for
  $$K=\frac{1+k}{1-k}.$$
proof:
  The pointwise Wirtinger calculation converts the essential coefficient
  bound into the metric distortion inequality; the displayed value of $K$ is
  at least one.
-/
theorem isKQuasiconformalBetween_of_weakBeltrami
    {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'} {df : ℂ → ℂ →L[ℝ] ℂ}
    {μ : ℂ → ℂ} {k : ℝ}
    (hΩ' : IsOpen Ω')
    (horient : PreservesPlanarOrientation F)
    (hW : IsLocalW12On Ω (ambientMap F) df)
    (heq : WeakBeltramiEquationOn Ω μ df)
    (hμ : HasEssentialNormLEOn Ω μ k) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    IsKQuasiconformalBetween ((1 + k) / (1 - k)) F := by
  have hden : 0 < 1 - k := sub_pos.mpr hk1
  have hK : 1 ≤ (1 + k) / (1 - k) := by
    rw [le_div_iff₀ hden]
    nlinarith
  exact ⟨hK, hΩ', horient, df, hW,
    heq.norm_sq_le_distortion_mul_weakJacobian hμ hk0 hk1⟩

end

end Quasiconformal

end JJMath
