import JJMath.AnalyticContinuation.LocalBranch
import JJMath.Uniformization.CirclePrimitiveIntegralPeriods
import JJMath.Uniformization.RadoSecondCountable
import JJMath.Uniformization.SmoothPathConnectivity

/-!
# Closed one-forms on simply connected Riemann surfaces

This file proves the degree-one de Rham consequence of simple connectedness
directly.  The proof uses local Poincare primitives and a finite rectangular
grid subordinate to such primitive neighborhoods.  A continuous null-homotopy
is sufficient: smoothness is needed only on the two boundary curves.  On each
small rectangle the four formal edge integrals are endpoint differences of one
local primitive; adjacent rectangles give the same difference on a shared edge.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold SurfaceRealModel ∞ X]

/-- A smooth singular simplex obtained by evaluating a globally smooth real
curve at an affine combination of the simplex vertices. -/
noncomputable def smoothCurveAffineSimplex
    {k : ℕ} (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a : Fin (k + 1) → ℝ) :
    ContMDiffSingularSimplex
      (I := SurfaceRealModel) (M := X) k ∞ := by
  let L : SimplexAmbient k → ℝ := fun q ↦ ∑ i, q i * a i
  have hL : ContDiff ℝ ∞ L := by
    dsimp [L]
    fun_prop
  exact
    { toContinuousMap :=
        ⟨fun q ↦ γ (L q),
          hγ.continuous.comp (hL.continuous.comp continuous_subtype_val)⟩
      contMDiff :=
        ⟨fun q ↦ γ (L q),
          (hγ.comp hL.contMDiff).contMDiffOn,
          fun _ ↦ rfl⟩ }

/--
%%handwave
name:
  Value of an affine simplex along a smooth curve
statement:
  The simplex determined by a smooth curve \(\gamma\) and vertex parameters
  \(a_i\) sends barycentric coordinates \(q\) to
  \(\gamma(\sum_i q_i a_i)\).
proof:
  This is the defining evaluation formula.
-/
@[simp]
theorem smoothCurveAffineSimplex_apply
    {k : ℕ} (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a : Fin (k + 1) → ℝ) (q : StandardSimplex k) :
    smoothCurveAffineSimplex γ hγ a q = γ (∑ i, q i * a i) :=
  rfl

/-- The oriented smooth one-simplex which follows `γ` from parameter `a`
to parameter `b`. -/
noncomputable def smoothCurveSegmentSimplex
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b : ℝ) :
    ContMDiffSingularSimplex
      (I := SurfaceRealModel) (M := X) 1 ∞ :=
  smoothCurveAffineSimplex γ hγ ![a, b]

/-- The degenerate smooth two-simplex used to subdivide a curve at an
intermediate parameter. -/
noncomputable def smoothCurveSubdivisionSimplex
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b c : ℝ) :
    ContMDiffSingularSimplex
      (I := SurfaceRealModel) (M := X) 2 ∞ :=
  smoothCurveAffineSimplex γ hγ ![a, b, c]

/--
%%handwave
name:
  Zeroth face of the curve-subdivision simplex
statement:
  The zeroth face of the degenerate two-simplex with curve parameters
  \((a,b,c)\) is the oriented curve segment from \(b\) to \(c\).
proof:
  The zeroth face sets the first barycentric coordinate to zero, leaving the
  affine combination of \(b\) and \(c\).
-/
theorem smoothCurveSubdivisionSimplex_face_zero
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b c : ℝ) :
    (smoothCurveSubdivisionSimplex γ hγ a b c).face 0 =
      smoothCurveSegmentSimplex γ hγ b c := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  change γ (∑ i : Fin 3,
      (simplexFaceMap 0 q : SimplexAmbient 2) i * ![a, b, c] i) =
    γ (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![b, c] i)
  have hface :
      (simplexFaceMap 0 q : SimplexAmbient 2) = ![0, q 0, q 1] := by
    funext i
    fin_cases i
    · exact simplexAmbientMap_succAbove_apply_omitted 0 q
    · simpa using simplexAmbientMap_succAbove_apply_succAbove 0 q 0
    · simpa using simplexAmbientMap_succAbove_apply_succAbove 0 q 1
  congr 1
  rw [hface]
  simp [Fin.sum_univ_succ]

/--
%%handwave
name:
  First face of the curve-subdivision simplex
statement:
  The first face of the degenerate two-simplex with parameters \((a,b,c)\)
  is the curve segment from \(a\) to \(c\).
proof:
  The first face deletes the barycentric coordinate multiplying \(b\).
-/
theorem smoothCurveSubdivisionSimplex_face_one
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b c : ℝ) :
    (smoothCurveSubdivisionSimplex γ hγ a b c).face 1 =
      smoothCurveSegmentSimplex γ hγ a c := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  change γ (∑ i : Fin 3,
      (simplexFaceMap 1 q : SimplexAmbient 2) i * ![a, b, c] i) =
    γ (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, c] i)
  have hface :
      (simplexFaceMap 1 q : SimplexAmbient 2) = ![q 0, 0, q 1] := by
    funext i
    fin_cases i
    · simpa using simplexAmbientMap_succAbove_apply_succAbove 1 q 0
    · exact simplexAmbientMap_succAbove_apply_omitted 1 q
    · simpa using simplexAmbientMap_succAbove_apply_succAbove 1 q 1
  congr 1
  rw [hface]
  simp [Fin.sum_univ_succ]

/--
%%handwave
name:
  Second face of the curve-subdivision simplex
statement:
  The second face of the degenerate two-simplex with parameters \((a,b,c)\)
  is the curve segment from \(a\) to \(b\).
proof:
  The second face sets the coordinate multiplying \(c\) to zero.
-/
theorem smoothCurveSubdivisionSimplex_face_two
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b c : ℝ) :
    (smoothCurveSubdivisionSimplex γ hγ a b c).face 2 =
      smoothCurveSegmentSimplex γ hγ a b := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  change γ (∑ i : Fin 3,
      (simplexFaceMap 2 q : SimplexAmbient 2) i * ![a, b, c] i) =
    γ (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, b] i)
  have hface :
      (simplexFaceMap 2 q : SimplexAmbient 2) = ![q 0, q 1, 0] := by
    funext i
    fin_cases i
    · simpa using simplexAmbientMap_succAbove_apply_succAbove 2 q 0
    ·
      change
        (simplexAmbientMap (2 : Fin 3).succAbove (q : SimplexAmbient 1))
            (1 : Fin 3) = q 1
      rw [show (1 : Fin 3) = (2 : Fin 3).succAbove (1 : Fin 2) by decide]
      exact simplexAmbientMap_succAbove_apply_succAbove (2 : Fin 3) q (1 : Fin 2)
    · exact simplexAmbientMap_succAbove_apply_omitted 2 q
  congr 1
  rw [hface]
  simp [Fin.sum_univ_succ]

/--
%%handwave
name:
  Additivity of a closed one-form integral under curve subdivision
statement:
  For a closed one-form \(\omega\) and a smooth curve \(\gamma\),
  \[
    \int_a^c\gamma^*\omega=
      \int_a^b\gamma^*\omega+\int_b^c\gamma^*\omega.
  \]
proof:
  Apply Stokes' theorem to the degenerate two-simplex along \(\gamma\) with
  vertices \(a,b,c\), and identify its three oriented faces.
-/
theorem integrate_smoothCurveSegmentSimplex_subdivision
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b c : ℝ) :
    integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex γ hγ a c) (1 : ℤ)) =
      integrateSmoothChain (I := SurfaceRealModel) omega.1
          (Finsupp.single (smoothCurveSegmentSimplex γ hγ a b) (1 : ℤ)) +
        integrateSmoothChain (I := SurfaceRealModel) omega.1
          (Finsupp.single (smoothCurveSegmentSimplex γ hγ b c) (1 : ℤ)) := by
  have hstokes := integrateSmoothChain_boundary_eq_zero_of_closed
    (I := SurfaceRealModel) omega
    (Finsupp.single (smoothCurveSubdivisionSimplex γ hγ a b c) (1 : ℤ))
  simp [boundary, Fin.sum_univ_succ,
    smoothCurveSubdivisionSimplex_face_zero,
    smoothCurveSubdivisionSimplex_face_one,
    smoothCurveSubdivisionSimplex_face_two,
    integrateSmoothChain_add] at hstokes
  simp [integrateSmoothChain, integrateChain, integrateChainHom] at hstokes
  simp [integrateSmoothChain, integrateChain, integrateChainHom]
  linarith

/--
%%handwave
name:
  Smooth codomain restriction to an open subset
statement:
  If a smooth map \(f:M\to N\) has image in an open subset \(V\subseteq N\),
  then the same map regarded as \(M\to V\) is smooth.
proof:
  Near each image point, use the smooth local retraction that returns points
  of \(V\) unchanged; composing it with \(f\) gives the restricted map.
-/
theorem contMDiffCodRestrictOpen
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G M N : Type*}
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [TopologicalSpace N]
    {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F G}
    [ChartedSpace H M] [ChartedSpace G N]
    {n : WithTop ℕ∞} {f : M → N}
    (hf : ContMDiff I J n f) (V : TopologicalSpace.Opens N)
    (hmem : ∀ x, f x ∈ V) :
    ContMDiff I J n (fun x ↦ (⟨f x, hmem x⟩ : V)) := by
  classical
  intro x
  let qV : V := ⟨f x, hmem x⟩
  let retract : N → V := fun y ↦
    if hy : y ∈ V then ⟨y, hy⟩ else qV
  have hretract : ContMDiffAt J J n retract (f x) := by
    rw [← contMDiffAt_subtype_iff (U := V) (x := qV)]
    have heq : (fun y : V ↦ retract y) = id := by
      funext y
      simp [retract]
    rw [heq]
    exact contMDiffAt_id
  have hcomp := hretract.comp x (hf x)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [retract, hmem]

/-- Restrict a map to an open codomain where possible, and use a fixed
fallback point elsewhere. -/
noncomputable def fallbackCodRestrictOpen
    {M N : Type*} [TopologicalSpace N]
    (f : M → N) (V : TopologicalSpace.Opens N) (qV : V) : M → V := by
  classical
  exact fun x ↦ if hx : f x ∈ V then ⟨f x, hx⟩ else qV

/--
%%handwave
name:
  Smoothness of a fallback codomain restriction on its valid set
statement:
  Let \(f:M\to N\) be smooth, let \(V\subseteq N\) be open, and define a
  map to \(V\) by using \(f(x)\) whenever it lies in \(V\) and a fixed point
  otherwise.  On every set where \(f\) is known to lie in \(V\), this map is
  smooth.
proof:
  Near each point of the valid set, the inverse image \(f^{-1}(V)\) is open
  and the fallback map agrees with the ordinary smooth codomain restriction.
-/
theorem contMDiffOn_fallbackCodRestrictOpen
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G M N : Type*}
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [TopologicalSpace N]
    {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F G}
    [ChartedSpace H M] [ChartedSpace G N]
    {n : WithTop ℕ∞} {f : M → N}
    (hf : ContMDiff I J n f) (V : TopologicalSpace.Opens N)
    (qV : V) (s : Set M) (hmem : ∀ x ∈ s, f x ∈ V) :
    ContMDiffOn I J n (fallbackCodRestrictOpen f V qV) s := by
  classical
  intro x hx
  let W : TopologicalSpace.Opens M :=
    ⟨f ⁻¹' V, V.is_open'.preimage hf.continuous⟩
  let xW : W := ⟨x, hmem x hx⟩
  let fW : W → N := fun y ↦ f y
  have hfW : ContMDiff I J n fW :=
    hf.comp (contMDiff_subtype_val (I := I) (n := n) (U := W))
  have hlift : ContMDiff I J n
      (fun y : W ↦ (⟨fW y, y.2⟩ : V)) :=
    contMDiffCodRestrictOpen hfW V (fun y ↦ y.2)
  have heq :
      (fun y : W ↦ fallbackCodRestrictOpen f V qV (y : M)) =
        fun y : W ↦ (⟨fW y, y.2⟩ : V) := by
    funext y
    change (if hy : f (y : M) ∈ V then ⟨f y, hy⟩ else qV) =
      (⟨f y, y.2⟩ : V)
    have hyV : f (y : M) ∈ V := y.2
    rw [dif_pos hyV]
  have hsource : ContMDiffAt I J n
      (fun y : W ↦ fallbackCodRestrictOpen f V qV (y : M)) xW := by
    rw [heq]
    exact hlift.contMDiffAt
  exact (contMDiffAt_subtype_iff (U := W) (x := xW)).mp hsource |>.contMDiffWithinAt

/-- A smooth curve segment regarded as a smooth singular simplex in an open
subset containing its image. -/
noncomputable def smoothCurveSegmentSimplexInOpen
    (U : TopologicalSpace.Opens X) (xU : U)
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b : ℝ)
    (hsegment : ∀ q : StandardSimplex 1,
      γ (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, b] i) ∈ U) :
    ContMDiffSingularSimplex
      (I := SurfaceRealModel) (M := U) 1 ∞ := by
  classical
  let L : SimplexAmbient 1 → ℝ := fun q ↦ ∑ i, q i * ![a, b] i
  have hL : ContDiff ℝ ∞ L := by
    dsimp [L]
    fun_prop
  let f : SimplexAmbient 1 → X := fun q ↦ γ (L q)
  have hf : ContMDiff (modelWithCornersSelf ℝ (SimplexAmbient 1))
      SurfaceRealModel ∞ f :=
    hγ.comp hL.contMDiff
  let F : SimplexAmbient 1 → U := fallbackCodRestrictOpen f U xU
  have hF : ContMDiffOn (modelWithCornersSelf ℝ (SimplexAmbient 1))
      SurfaceRealModel ∞ F (stdSimplex ℝ (Fin 2)) := by
    exact contMDiffOn_fallbackCodRestrictOpen hf U xU _ (by
      intro q hq
      exact hsegment ⟨q, hq⟩)
  exact
    { toContinuousMap :=
        ⟨fun q ↦ ⟨γ (L q), hsegment q⟩,
          Continuous.subtype_mk
            (hγ.continuous.comp (hL.continuous.comp continuous_subtype_val)) _⟩
      contMDiff :=
        ⟨F, hF, fun q ↦ by
          change
            (if hq : γ (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, b] i) ∈ U
              then ⟨γ (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, b] i), hq⟩
              else xU) =
            ⟨γ (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, b] i), hsegment q⟩
          rw [dif_pos (hsegment q)]⟩ }

/--
%%handwave
name:
  Value of a curve-segment simplex in an open subset
statement:
  If a smooth curve segment lies in an open set \(U\), evaluating the simplex
  regarded in \(U\) and then including into \(X\) gives the original
  curve-segment simplex.
proof:
  Both evaluate the same affine curve parameter.
-/
@[simp]
theorem smoothCurveSegmentSimplexInOpen_apply
    (U : TopologicalSpace.Opens X) (xU : U)
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b : ℝ)
    (hsegment : ∀ q : StandardSimplex 1,
      γ (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, b] i) ∈ U)
    (q : StandardSimplex 1) :
    (smoothCurveSegmentSimplexInOpen U xU γ hγ a b hsegment q : X) =
      smoothCurveSegmentSimplex γ hγ a b q := by
  simp [smoothCurveSegmentSimplexInOpen, smoothCurveSegmentSimplex,
    smoothCurveAffineSimplex]

/--
%%handwave
name:
  Including an open-valued curve simplex recovers the ambient simplex
statement:
  The open inclusion of a curve-segment simplex whose image lies in \(U\)
  equals the original simplex in the ambient manifold.
proof:
  The two simplices agree at every barycentric point by their evaluation
  formulas.
-/
theorem smoothCurveSegmentSimplexInOpen_openInclusion
    (U : TopologicalSpace.Opens X) (xU : U)
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b : ℝ)
    (hsegment : ∀ q : StandardSimplex 1,
      γ (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, b] i) ∈ U) :
    (smoothCurveSegmentSimplexInOpen U xU γ hγ a b hsegment).openInclusion
        (I := SurfaceRealModel) U =
      smoothCurveSegmentSimplex γ hγ a b := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  simp [ContMDiffSingularSimplex.openInclusion,
    smoothCurveSegmentSimplexInOpen, smoothCurveSegmentSimplex,
    smoothCurveAffineSimplex]

/--
%%handwave
name:
  Terminal face of a smooth curve segment
statement:
  The zeroth face of the oriented curve segment from parameter \(a\) to
  parameter \(b\) is \(\gamma(b)\).
proof:
  The zeroth face of the standard one-simplex has barycentric coordinates
  \((0,1)\).
-/
@[simp]
theorem smoothCurveSegmentSimplex_face_zero_apply
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b : ℝ) :
    (smoothCurveSegmentSimplex γ hγ a b).face 0
        standardZeroSimplexVertex = γ b := by
  simp only [ContMDiffSingularSimplex.face, smoothCurveSegmentSimplex,
    smoothCurveAffineSimplex, ContinuousMap.comp_apply]
  change γ (∑ i : Fin 2,
      (simplexFaceMap 0 standardZeroSimplexVertex : SimplexAmbient 1) i *
        ![a, b] i) = γ b
  have hq : (standardZeroSimplexVertex : SimplexAmbient 0) 0 = 1 := by
    simp [standardZeroSimplexVertex]
  have hface :
      (simplexFaceMap 0 standardZeroSimplexVertex : SimplexAmbient 1) =
        ![0, standardZeroSimplexVertex 0] := by
    funext i
    fin_cases i
    · exact simplexAmbientMap_succAbove_apply_omitted 0 standardZeroSimplexVertex
    · exact simplexAmbientMap_succAbove_apply_succAbove 0 standardZeroSimplexVertex 0
  rw [hface]
  simp [Fin.sum_univ_succ, hq]

/--
%%handwave
name:
  Initial face of a smooth curve segment
statement:
  The first face of the oriented curve segment from parameter \(a\) to
  parameter \(b\) is \(\gamma(a)\).
proof:
  The first face has barycentric coordinates \((1,0)\).
-/
@[simp]
theorem smoothCurveSegmentSimplex_face_one_apply
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b : ℝ) :
    (smoothCurveSegmentSimplex γ hγ a b).face 1
        standardZeroSimplexVertex = γ a := by
  simp only [ContMDiffSingularSimplex.face, smoothCurveSegmentSimplex,
    smoothCurveAffineSimplex, ContinuousMap.comp_apply]
  change γ (∑ i : Fin 2,
      (simplexFaceMap 1 standardZeroSimplexVertex : SimplexAmbient 1) i *
        ![a, b] i) = γ a
  have hq : (standardZeroSimplexVertex : SimplexAmbient 0) 0 = 1 := by
    simp [standardZeroSimplexVertex]
  have hface :
      (simplexFaceMap 1 standardZeroSimplexVertex : SimplexAmbient 1) =
        ![standardZeroSimplexVertex 0, 0] := by
    funext i
    fin_cases i
    · exact simplexAmbientMap_succAbove_apply_succAbove 1 standardZeroSimplexVertex 0
    · exact simplexAmbientMap_succAbove_apply_omitted 1 standardZeroSimplexVertex
  rw [hface]
  simp [Fin.sum_univ_succ, hq]

/--
%%handwave
name:
  Integral of a one-form on a local primitive segment
statement:
  If a smooth curve segment from \(a\) to \(b\) lies in an open set where
  \(\omega=d\theta\), then
  \[
    \int_{\gamma|_{[a,b]}}\omega=\theta(\gamma(b))-\theta(\gamma(a)).
  \]
proof:
  Regard the simplex inside the primitive neighborhood, replace the form by
  \(d\theta\), and apply the fundamental theorem for an exact one-form on a
  one-simplex.
-/
theorem integrate_smoothCurveSegmentSimplex_eq_localPrimitive_sub
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
    (U : TopologicalSpace.Opens X)
    (theta : C^∞⟮SurfaceRealModel, U; ℝ⟯)
    (hexact :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U 1 omega =
        deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta))
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (a b : ℝ) (ha : γ a ∈ U) (hb : γ b ∈ U)
    (hsegment : ∀ q : StandardSimplex 1,
      γ (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, b] i) ∈ U) :
    integrateSmoothChain (I := SurfaceRealModel) omega
        (Finsupp.single (smoothCurveSegmentSimplex γ hγ a b) (1 : ℤ)) =
      theta ⟨γ b, hb⟩ - theta ⟨γ a, ha⟩ := by
  let sigmaU := smoothCurveSegmentSimplexInOpen U ⟨γ a, ha⟩ γ hγ a b hsegment
  rw [← smoothCurveSegmentSimplexInOpen_openInclusion
    U ⟨γ a, ha⟩ γ hγ a b hsegment]
  rw [integrateSmoothChain_openInclusion_single, hexact,
    integrateSmoothChain_deRhamDifferential_zero_single_eq_endpoint_sub]
  have hterminal : sigmaU.face 0 standardZeroSimplexVertex = ⟨γ b, hb⟩ := by
    apply Subtype.ext
    change (smoothCurveSegmentSimplex γ hγ a b).face 0
      standardZeroSimplexVertex = γ b
    exact smoothCurveSegmentSimplex_face_zero_apply γ hγ a b
  have hinitial : sigmaU.face 1 standardZeroSimplexVertex = ⟨γ a, ha⟩ := by
    apply Subtype.ext
    change (smoothCurveSegmentSimplex γ hγ a b).face 1
      standardZeroSimplexVertex = γ a
    exact smoothCurveSegmentSimplex_face_one_apply γ hγ a b
  rw [hterminal, hinitial]

/--
%%handwave
name:
  Integral over a finite subdivision of a smooth curve
statement:
  For \(N>0\), the integral of a closed one-form along the curve segment from
  \(t_0\) to \(t_N\) equals
  \[
    \sum_{j=0}^{N-1}\int_{t_j}^{t_{j+1}}\gamma^*\omega.
  \]
proof:
  Induct on \(N\), applying the one-step subdivision identity at the last
  intermediate parameter.
-/
theorem integrate_smoothCurveSegmentSimplex_eq_sum_subsegments
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (γ : ℝ → X)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ γ)
    (t : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex γ hγ (t 0) (t N)) (1 : ℤ)) =
      ∑ j ∈ Finset.range N,
        integrateSmoothChain (I := SurfaceRealModel) omega.1
          (Finsupp.single
            (smoothCurveSegmentSimplex γ hγ (t j) (t (j + 1))) (1 : ℤ)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  induction n with
  | zero => simp
  | succ n ih =>
      rw [integrate_smoothCurveSegmentSimplex_subdivision
        omega γ hγ (t 0) (t (n + 1)) (t (n + 2))]
      rw [Finset.sum_range_succ]
      rw [ih (by omega)]

/--
%%handwave
name:
  Evaluation of a restricted smooth zero-form
statement:
  If \(V\subseteq U\) and a zero-form on \(U\) is induced by a smooth
  function \(\theta\), then its restriction to \(V\) evaluates at
  \(x\in V\) as \(\theta(x)\), viewed in \(U\).
proof:
  This is the definition of restriction for a zero-form.
-/
theorem restrict_smoothRealFunctionToZeroForm_apply
    {U V : TopologicalSpace.Opens X} (hVU : V ≤ U)
    (theta : C^∞⟮SurfaceRealModel, U; ℝ⟯) (x : V) :
    (restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ) hVU 0
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta)).toFun x
          (fun i : Fin 0 ↦ nomatch i) =
      theta (TopologicalSpace.Opens.inclusion hVU x) := by
  rfl

/--
%%handwave
name:
  Two-stage restriction of an ambient differential form
statement:
  Let \(W\subseteq U\subseteq X\).  If the restriction of an ambient form
  \(\omega\) to \(U\) is \(\alpha\), then the direct restriction of
  \(\omega\) to \(W\) equals the restriction of \(\alpha\) from \(U\) to
  \(W\).
proof:
  Evaluate both forms at a point of \(W\).  The derivative of the inclusion
  \(W\hookrightarrow X\) factors through \(U\), so the pullback multilinear
  maps agree.
-/
theorem restrictSmoothFormsToOpen_eq_restrictSmoothFormsOfLE_of_restrict_eq_surface
    (W U : TopologicalSpace.Opens X) (hWU : W ≤ U) {n : ℕ}
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ n)
    (alpha : SmoothForms (I := SurfaceRealModel) (M := U) ℝ n)
    (heq : restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U n omega =
      alpha) :
    restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) W n omega =
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ) hWU n alpha := by
  apply DifferentialForm.ext
  intro x
  let xU : U := TopologicalSpace.Opens.inclusion hWU x
  let LU : TangentSpace SurfaceRealModel xU →L[ℝ]
      TangentSpace SurfaceRealModel (x : X) :=
    mfderiv SurfaceRealModel SurfaceRealModel (fun y : U ↦ (y : X)) xU
  let LWU : TangentSpace SurfaceRealModel x →L[ℝ]
      TangentSpace SurfaceRealModel xU :=
    mfderiv SurfaceRealModel SurfaceRealModel
      (TopologicalSpace.Opens.inclusion hWU) x
  let LW : TangentSpace SurfaceRealModel x →L[ℝ]
      TangentSpace SurfaceRealModel (x : X) :=
    mfderiv SurfaceRealModel SurfaceRealModel (fun y : W ↦ (y : X)) x
  have hpoint := congrArg
    (fun eta : SmoothForms (I := SurfaceRealModel) (M := U) ℝ n ↦ eta.toFun xU) heq
  have hfactor : LU.comp LWU = LW := by
    simpa [LU, LWU, LW, xU] using
      mfderiv_subtypeVal_comp_inclusion_eq
        (I := SurfaceRealModel) W U hWU x
  change (omega.toFun (x : X)).compContinuousLinearMap LW =
    (alpha.toFun xU).compContinuousLinearMap LWU
  rw [← hfactor]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hpoint' :
      (omega.toFun (x : X)).compContinuousLinearMap LU = alpha.toFun xU := by
    simpa [restrictSmoothFormsToOpen, restrictSmoothFormToOpen, LU, xU] using hpoint
  exact congrArg
    (fun eta : FormAt (I := SurfaceRealModel) (M := U) ℝ n xU ↦ eta (LWU ∘ v))
    hpoint'

/--
%%handwave
name:
  Local primitives agree on endpoint increments along an overlap path
statement:
  If \(d\theta_U=d\theta_V=\omega\) and a path \(\rho:x\to y\) lies in
  \(U\cap V\), then
  \[
    \theta_U(y)-\theta_U(x)=\theta_V(y)-\theta_V(x).
  \]
proof:
  Restrict both primitives to the path component of \(x\) in \(U\cap V\).
  Their difference has zero differential there and is constant on this
  connected set, which contains the entire path and both endpoints.
-/
theorem localPrimitive_endpoint_sub_eq_of_path_in_overlap
    [RiemannSurface X]
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
    (U V : TopologicalSpace.Opens X)
    (thetaU : C^∞⟮SurfaceRealModel, U; ℝ⟯)
    (thetaV : C^∞⟮SurfaceRealModel, V; ℝ⟯)
    (hexactU :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U 1 omega =
        deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) thetaU))
    (hexactV :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) V 1 omega =
        deRhamDifferential (I := SurfaceRealModel) (M := V) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) thetaV))
    {x y : X} (rho : Path x y)
    (hrho : ∀ t : unitInterval, rho t ∈ U ∧ rho t ∈ V) :
    thetaU ⟨y, by simpa using (hrho 1).1⟩ -
        thetaU ⟨x, by simpa using (hrho 0).1⟩ =
      thetaV ⟨y, by simpa using (hrho 1).2⟩ -
        thetaV ⟨x, by simpa using (hrho 0).2⟩ := by
  let O : TopologicalSpace.Opens X := U ⊓ V
  have hxO : x ∈ O := by simpa [O] using hrho 0
  let W : TopologicalSpace.Opens X :=
    ⟨pathComponentIn (O : Set X) x, O.is_open'.pathComponentIn x⟩
  have hxW : x ∈ W := by
    exact mem_pathComponentIn_self hxO
  have hrangeO : range rho ⊆ (O : Set X) := by
    rintro z ⟨t, rfl⟩
    simpa [O] using hrho t
  have hrangeW : range rho ⊆ (W : Set X) := by
    letI : PathConnectedSpace unitInterval :=
      isPathConnected_iff_pathConnectedSpace.mp
        ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
    exact (isPathConnected_range rho.continuous).subset_pathComponentIn
      rho.source_mem_range hrangeO
  have hyW : y ∈ W := hrangeW rho.target_mem_range
  have hWU : W ≤ U := by
    intro z hz
    exact (pathComponentIn_subset hz).1
  have hWV : W ≤ V := by
    intro z hz
    exact (pathComponentIn_subset hz).2
  letI : RiemannSurface W :=
    riemannSurface_openSubset W ⟨x, hxW⟩
      (isPathConnected_pathComponentIn hxO).isConnected.isPreconnected
  let thetaUW : SmoothForms
      (I := SurfaceRealModel) (M := W) ℝ 0 :=
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ) hWU 0
      (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) thetaU)
  let thetaVW : SmoothForms
      (I := SurfaceRealModel) (M := W) ℝ 0 :=
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ) hWV 0
      (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) thetaV)
  have hdU :
      deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 0 thetaUW =
        restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) W 1 omega := by
    rw [deRhamDifferential_restrictSmoothFormsOfLE]
    exact
      (restrictSmoothFormsToOpen_eq_restrictSmoothFormsOfLE_of_restrict_eq_surface
        W U hWU omega _ hexactU).symm
  have hdV :
      deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 0 thetaVW =
        restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) W 1 omega := by
    rw [deRhamDifferential_restrictSmoothFormsOfLE]
    exact
      (restrictSmoothFormsToOpen_eq_restrictSmoothFormsOfLE_of_restrict_eq_surface
        W V hWV omega _ hexactV).symm
  let xW : W := ⟨x, hxW⟩
  let yW : W := ⟨y, hyW⟩
  let c : ℝ :=
    thetaUW.toFun xW (fun i : Fin 0 ↦ nomatch i) -
      thetaVW.toFun xW (fun i : Fin 0 ↦ nomatch i)
  let constW : SmoothForms (I := SurfaceRealModel) (M := W) ℝ 0 :=
    smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
      (smoothRealConstantFunction (I0 := SurfaceRealModel) c)
  let eta : SmoothForms (I := SurfaceRealModel) (M := W) ℝ 0 :=
    thetaVW + constW
  have hdeta :
      deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 0 thetaUW =
        deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 0 eta := by
    change deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 0 thetaUW =
      deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 0
        (thetaVW + constW)
    rw [map_add]
    dsimp only [constW]
    rw [deRhamDifferential_smoothRealFunctionToZeroForm_const,
      add_zero, hdU, hdV]
  have hbase :
      thetaUW.toFun xW (fun i : Fin 0 ↦ nomatch i) =
        eta.toFun xW (fun i : Fin 0 ↦ nomatch i) := by
    change _ = thetaVW.toFun xW (fun i : Fin 0 ↦ nomatch i) + c
    dsimp [c]
    ring
  have heq : thetaUW = eta :=
    SmoothChainConnectivity.smoothZeroForm_eq_of_differential_eq_of_eq_at
      thetaUW eta xW hdeta hbase
  have hyEq := congrArg
    (fun alpha : SmoothForms (I := SurfaceRealModel) (M := W) ℝ 0 ↦
      alpha.toFun yW (fun i : Fin 0 ↦ nomatch i)) heq
  change
    thetaU (TopologicalSpace.Opens.inclusion hWU yW) -
        thetaU (TopologicalSpace.Opens.inclusion hWU xW) =
      thetaV (TopologicalSpace.Opens.inclusion hWV yW) -
        thetaV (TopologicalSpace.Opens.inclusion hWV xW)
  have hUy : thetaUW.toFun yW (fun i : Fin 0 ↦ nomatch i) =
      thetaU (TopologicalSpace.Opens.inclusion hWU yW) :=
    restrict_smoothRealFunctionToZeroForm_apply hWU thetaU yW
  have hUx : thetaUW.toFun xW (fun i : Fin 0 ↦ nomatch i) =
      thetaU (TopologicalSpace.Opens.inclusion hWU xW) :=
    restrict_smoothRealFunctionToZeroForm_apply hWU thetaU xW
  have hVy : thetaVW.toFun yW (fun i : Fin 0 ↦ nomatch i) =
      thetaV (TopologicalSpace.Opens.inclusion hWV yW) :=
    restrict_smoothRealFunctionToZeroForm_apply hWV thetaV yW
  have hVx : thetaVW.toFun xW (fun i : Fin 0 ↦ nomatch i) =
      thetaV (TopologicalSpace.Opens.inclusion hWV xW) :=
    restrict_smoothRealFunctionToZeroForm_apply hWV thetaV xW
  change thetaUW.toFun yW (fun i : Fin 0 ↦ nomatch i) =
      thetaVW.toFun yW (fun i : Fin 0 ↦ nomatch i) + c at hyEq
  dsimp [c] at hyEq
  rw [← hUy, ← hUx, ← hVy, ← hVx]
  linarith

/--
%%handwave
name:
  Horizontal cancellation across a row of grid cells
statement:
  Suppose each cell in a finite row satisfies
  \(b_j+r_j=t_j+\ell_j\), adjacent vertical contributions satisfy
  \(r_j=\ell_{j+1}\), and the two outer vertical contributions vanish.  Then
  \(\sum_j b_j=\sum_j t_j\).
proof:
  Sum the cell identities.  The right-edge sum equals the left-edge sum by
  telescoping the adjacent matches and using the vanishing outer edges, so
  these terms cancel.
-/
theorem sum_cell_bottom_eq_sum_cell_top
    (N : ℕ) (hN : 0 < N)
    (bottom right top left : ℕ → ℝ)
    (hcell : ∀ j < N, bottom j + right j = top j + left j)
    (hleft : left 0 = 0)
    (hmatch : ∀ j, j + 1 < N → right j = left (j + 1))
    (hright : right (N - 1) = 0) :
    ∑ j ∈ Finset.range N, bottom j =
      ∑ j ∈ Finset.range N, top j := by
  have hsumCell :
      (∑ j ∈ Finset.range N, bottom j) +
          (∑ j ∈ Finset.range N, right j) =
        (∑ j ∈ Finset.range N, top j) +
          (∑ j ∈ Finset.range N, left j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hcell j (Finset.mem_range.mp hj)
  have hsumSides :
      ∑ j ∈ Finset.range N, right j =
        ∑ j ∈ Finset.range N, left j := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    rw [Finset.sum_range_succ, Finset.sum_range_succ', hleft]
    have hlast : right n = 0 := by simpa using hright
    rw [hlast, add_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    exact hmatch j (by
      have hjn : j < n := Finset.mem_range.mp hj
      omega)
  linarith

/--
%%handwave
name:
  Vertical cancellation across a rectangular grid
statement:
  If the sum along the bottom of each grid row equals the sum along its top,
  and the top of every row agrees cellwise with the bottom of the next, then
  the bottom sum of the first row equals the top sum of the last row.
proof:
  Induct upward through the rows, replacing each bottom sum by the matching
  preceding top sum and then by the next row's bottom sum.
-/
theorem sum_grid_bottom_eq_sum_grid_top
    (N : ℕ) (hN : 0 < N)
    (bottom top : ℕ → ℕ → ℝ)
    (hrow : ∀ i < N,
      ∑ j ∈ Finset.range N, bottom i j =
        ∑ j ∈ Finset.range N, top i j)
    (hmatch : ∀ i, i + 1 < N → ∀ j < N,
      top i j = bottom (i + 1) j) :
    ∑ j ∈ Finset.range N, bottom 0 j =
      ∑ j ∈ Finset.range N, top (N - 1) j := by
  have hwalk : ∀ k, k < N →
      (∑ j ∈ Finset.range N, bottom 0 j) =
        ∑ j ∈ Finset.range N, bottom k j := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        have hkN : k < N := by omega
        calc
          (∑ j ∈ Finset.range N, bottom 0 j) =
              ∑ j ∈ Finset.range N, bottom k j := ih hkN
          _ = ∑ j ∈ Finset.range N, top k j := hrow k hkN
          _ = ∑ j ∈ Finset.range N, bottom (k + 1) j := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hmatch k (by omega) j (Finset.mem_range.mp hj)
  calc
    (∑ j ∈ Finset.range N, bottom 0 j) =
        ∑ j ∈ Finset.range N, bottom (N - 1) j :=
      hwalk (N - 1) (by omega)
    _ = ∑ j ∈ Finset.range N, top (N - 1) j :=
      hrow (N - 1) (by omega)

/-- Evaluation of a local primitive on a grid cell, with an irrelevant
fallback value away from its domain. -/
noncomputable def primitiveGridValue
    (F : unitInterval × unitInterval → X)
    (U : TopologicalSpace.Opens X)
    (theta : C^∞⟮SurfaceRealModel, U; ℝ⟯)
    (z : unitInterval × unitInterval) : ℝ := by
  classical
  exact if hz : F z ∈ U then theta ⟨F z, hz⟩ else 0

/--
%%handwave
name:
  Grid primitive value inside its domain
statement:
  If a homotopy-grid point \(z\) maps into a primitive neighborhood \(U\),
  then its grid value is \(\theta(F(z))\).
proof:
  The valid-domain branch of the defining case split applies.
-/
theorem primitiveGridValue_eq
    (F : unitInterval × unitInterval → X)
    (U : TopologicalSpace.Opens X)
    (theta : C^∞⟮SurfaceRealModel, U; ℝ⟯)
    (z : unitInterval × unitInterval) (hz : F z ∈ U) :
    primitiveGridValue F U theta z = theta ⟨F z, hz⟩ := by
  simp [primitiveGridValue, hz]

/--
%%handwave
name:
  A horizontal subpath remains in its homotopy rectangle
statement:
  If a parameter rectangle maps into a set \(U\), then every point of a
  horizontal subpath across that rectangle also maps into \(U\).
proof:
  Every point on the subpath has a horizontal parameter in the prescribed
  interval; together with the fixed vertical parameter it lies in the
  rectangle.
-/
theorem homotopy_horizontal_subpath_mem_of_rect
    {x₀ x₁ : X} {p q : Path x₀ x₁}
    (F : Path.Homotopy p q) (t : ℕ → unitInterval) (ht : Monotone t)
    (i j : ℕ) (r : unitInterval)
    (hr : r ∈ Icc (t i) (t (i + 1)))
    (U : Set X)
    (hrect : Icc (t i) (t (i + 1)) ×ˢ Icc (t j) (t (j + 1)) ⊆
      {z : unitInterval × unitInterval | F z ∈ U})
    (u : unitInterval) :
    ((F.eval r).subpath (t j) (t (j + 1))) u ∈ U := by
  let edge := (F.eval r).subpath (t j) (t (j + 1))
  have huRange : edge u ∈ range edge := ⟨u, rfl⟩
  rw [Path.range_subpath_of_le (F.eval r) (t j) (t (j + 1))
    (ht (Nat.le_succ j))] at huRange
  rcases huRange with ⟨s, hs, hsEq⟩
  rw [← hsEq]
  exact hrect ⟨hr, hs⟩

/--
%%handwave
name:
  A vertical subpath remains in its homotopy rectangle
statement:
  If a parameter rectangle maps into a set \(U\), then every point of a
  vertical subpath across that rectangle maps into \(U\).
proof:
  The variable vertical parameter lies in the row interval and the fixed
  horizontal parameter lies in the column interval, so the corresponding
  pair belongs to the rectangle.
-/
theorem homotopy_vertical_subpath_mem_of_rect
    {x₀ x₁ : X} {p q : Path x₀ x₁}
    (F : Path.Homotopy p q) (t : ℕ → unitInterval) (ht : Monotone t)
    (i j : ℕ) (r : unitInterval)
    (hr : r ∈ Icc (t j) (t (j + 1)))
    (U : Set X)
    (hrect : Icc (t i) (t (i + 1)) ×ˢ Icc (t j) (t (j + 1)) ⊆
      {z : unitInterval × unitInterval | F z ∈ U})
    (u : unitInterval) :
    ((F.evalAt r).subpath (t i) (t (i + 1))) u ∈ U := by
  let edge := (F.evalAt r).subpath (t i) (t (i + 1))
  have huRange : edge u ∈ range edge := ⟨u, rfl⟩
  rw [Path.range_subpath_of_le (F.evalAt r) (t i) (t (i + 1))
    (ht (Nat.le_succ i))] at huRange
  rcases huRange with ⟨s, hs, hsEq⟩
  rw [← hsEq]
  exact hrect ⟨hs, hr⟩

/--
%%handwave
name:
  Boundary increment equality for a grid of local primitives
statement:
  Subdivide an endpoint-fixed path homotopy into finitely many rectangles,
  each contained in a neighborhood where \(\omega=d\theta_{ij}\).  Then the
  sum of primitive increments along the bottom boundary equals the
  corresponding sum along the top boundary.
proof:
  On each cell the four oriented primitive increments sum to zero.  Along
  shared edges, increments computed using neighboring local primitives agree.
  Horizontal cancellation eliminates interior vertical edges and the fixed
  side boundaries; sweeping through the rows eliminates interior horizontal
  edges.
-/
theorem localPrimitive_grid_boundary_increments_eq
    [RiemannSurface X]
    {x₀ x₁ : X} {p q : Path x₀ x₁}
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval) (ht : Monotone t)
    (N : ℕ) (hN : 0 < N) (ht0 : t 0 = 0) (htN : t N = 1)
    (U : ℕ → ℕ → TopologicalSpace.Opens X)
    (theta : ∀ i j, C^∞⟮SurfaceRealModel, U i j; ℝ⟯)
    (hexact : ∀ i j,
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) (U i j) 1 omega.1 =
        deRhamDifferential (I := SurfaceRealModel) (M := U i j) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) (theta i j)))
    (hrect : ∀ i j,
      Icc (t i) (t (i + 1)) ×ˢ Icc (t j) (t (j + 1)) ⊆
        {z : unitInterval × unitInterval | F z ∈ U i j}) :
    ∑ j ∈ Finset.range N,
        (primitiveGridValue F (U 0 j) (theta 0 j) (t 0, t (j + 1)) -
          primitiveGridValue F (U 0 j) (theta 0 j) (t 0, t j)) =
      ∑ j ∈ Finset.range N,
        (primitiveGridValue F (U (N - 1) j) (theta (N - 1) j)
            (t ((N - 1) + 1), t (j + 1)) -
          primitiveGridValue F (U (N - 1) j) (theta (N - 1) j)
            (t ((N - 1) + 1), t j)) := by
  let value (i j : ℕ) (z : unitInterval × unitInterval) : ℝ :=
    primitiveGridValue F (U i j) (theta i j) z
  let bottom (i j : ℕ) : ℝ :=
    value i j (t i, t (j + 1)) - value i j (t i, t j)
  let top (i j : ℕ) : ℝ :=
    value i j (t (i + 1), t (j + 1)) - value i j (t (i + 1), t j)
  let left (i j : ℕ) : ℝ :=
    value i j (t (i + 1), t j) - value i j (t i, t j)
  let right (i j : ℕ) : ℝ :=
    value i j (t (i + 1), t (j + 1)) - value i j (t i, t (j + 1))
  have hcell (i j : ℕ) : bottom i j + right i j = top i j + left i j := by
    dsimp [bottom, right, top, left]
    ring
  have hhorizontal : ∀ i, i + 1 < N → ∀ j < N,
      top i j = bottom (i + 1) j := by
    intro i hi j hj
    let edge : Path (F (t (i + 1), t j)) (F (t (i + 1), t (j + 1))) :=
      (F.eval (t (i + 1))).subpath (t j) (t (j + 1))
    have hedgeU : ∀ u : unitInterval, edge u ∈ U i j := by
      exact homotopy_horizontal_subpath_mem_of_rect F t ht i j (t (i + 1))
        ⟨ht (Nat.le_succ i), le_rfl⟩ (U i j) (hrect i j)
    have hedgeV : ∀ u : unitInterval, edge u ∈ U (i + 1) j := by
      exact homotopy_horizontal_subpath_mem_of_rect F t ht (i + 1) j (t (i + 1))
        ⟨le_rfl, ht (Nat.le_succ (i + 1))⟩ (U (i + 1) j) (hrect (i + 1) j)
    have hedge := localPrimitive_endpoint_sub_eq_of_path_in_overlap
      omega.1 (U i j) (U (i + 1) j) (theta i j) (theta (i + 1) j)
      (hexact i j) (hexact (i + 1) j) edge (fun u ↦ ⟨hedgeU u, hedgeV u⟩)
    dsimp [top, bottom, value]
    rw [primitiveGridValue_eq F (U i j) (theta i j)
      (t (i + 1), t (j + 1)) (hrect i j
        ⟨⟨ht (Nat.le_succ i), le_rfl⟩, ⟨ht (Nat.le_succ j), le_rfl⟩⟩)]
    rw [primitiveGridValue_eq F (U i j) (theta i j)
      (t (i + 1), t j) (hrect i j
        ⟨⟨ht (Nat.le_succ i), le_rfl⟩, ⟨le_rfl, ht (Nat.le_succ j)⟩⟩)]
    rw [primitiveGridValue_eq F (U (i + 1) j) (theta (i + 1) j)
      (t (i + 1), t (j + 1)) (hrect (i + 1) j
        ⟨⟨le_rfl, ht (Nat.le_succ (i + 1))⟩, ⟨ht (Nat.le_succ j), le_rfl⟩⟩)]
    rw [primitiveGridValue_eq F (U (i + 1) j) (theta (i + 1) j)
      (t (i + 1), t j) (hrect (i + 1) j
        ⟨⟨le_rfl, ht (Nat.le_succ (i + 1))⟩, ⟨le_rfl, ht (Nat.le_succ j)⟩⟩)]
    simpa [edge, Path.subpath, Set.Icc.convexComb] using hedge
  have hvertical : ∀ i, i < N → ∀ j, j + 1 < N →
      right i j = left i (j + 1) := by
    intro i hi j hj
    let edge : Path (F (t i, t (j + 1))) (F (t (i + 1), t (j + 1))) :=
      (F.evalAt (t (j + 1))).subpath (t i) (t (i + 1))
    have hedgeU : ∀ u : unitInterval, edge u ∈ U i j := by
      exact homotopy_vertical_subpath_mem_of_rect F t ht i j (t (j + 1))
        ⟨ht (Nat.le_succ j), le_rfl⟩ (U i j) (hrect i j)
    have hedgeV : ∀ u : unitInterval, edge u ∈ U i (j + 1) := by
      exact homotopy_vertical_subpath_mem_of_rect F t ht i (j + 1) (t (j + 1))
        ⟨le_rfl, ht (Nat.le_succ (j + 1))⟩ (U i (j + 1)) (hrect i (j + 1))
    have hedge := localPrimitive_endpoint_sub_eq_of_path_in_overlap
      omega.1 (U i j) (U i (j + 1)) (theta i j) (theta i (j + 1))
      (hexact i j) (hexact i (j + 1)) edge (fun u ↦ ⟨hedgeU u, hedgeV u⟩)
    dsimp [right, left, value]
    rw [primitiveGridValue_eq F (U i j) (theta i j)
      (t (i + 1), t (j + 1)) (hrect i j
        ⟨⟨ht (Nat.le_succ i), le_rfl⟩, ⟨ht (Nat.le_succ j), le_rfl⟩⟩)]
    rw [primitiveGridValue_eq F (U i j) (theta i j)
      (t i, t (j + 1)) (hrect i j
        ⟨⟨le_rfl, ht (Nat.le_succ i)⟩, ⟨ht (Nat.le_succ j), le_rfl⟩⟩)]
    rw [primitiveGridValue_eq F (U i (j + 1)) (theta i (j + 1))
      (t (i + 1), t (j + 1)) (hrect i (j + 1)
        ⟨⟨ht (Nat.le_succ i), le_rfl⟩, ⟨le_rfl, ht (Nat.le_succ (j + 1))⟩⟩)]
    rw [primitiveGridValue_eq F (U i (j + 1)) (theta i (j + 1))
      (t i, t (j + 1)) (hrect i (j + 1)
        ⟨⟨le_rfl, ht (Nat.le_succ i)⟩, ⟨le_rfl, ht (Nat.le_succ (j + 1))⟩⟩)]
    simpa [edge, Path.subpath, Set.Icc.convexComb] using hedge
  have hrow : ∀ i < N,
      ∑ j ∈ Finset.range N, bottom i j =
        ∑ j ∈ Finset.range N, top i j := by
    intro i hi
    apply sum_cell_bottom_eq_sum_cell_top N hN
      (bottom i) (right i) (top i) (left i)
    · intro j hj
      exact hcell i j
    · dsimp [left, value]
      rw [primitiveGridValue_eq F (U i 0) (theta i 0) (t (i + 1), t 0)
        (hrect i 0 ⟨⟨ht (Nat.le_succ i), le_rfl⟩, ⟨le_rfl, ht (Nat.le_succ 0)⟩⟩)]
      rw [primitiveGridValue_eq F (U i 0) (theta i 0) (t i, t 0)
        (hrect i 0 ⟨⟨le_rfl, ht (Nat.le_succ i)⟩, ⟨le_rfl, ht (Nat.le_succ 0)⟩⟩)]
      have hpoints :
          (⟨F (t (i + 1), t 0), hrect i 0
              ⟨⟨ht (Nat.le_succ i), le_rfl⟩, ⟨le_rfl, ht (Nat.le_succ 0)⟩⟩⟩ : U i 0) =
            ⟨F (t i, t 0), hrect i 0
              ⟨⟨le_rfl, ht (Nat.le_succ i)⟩, ⟨le_rfl, ht (Nat.le_succ 0)⟩⟩⟩ := by
        apply Subtype.ext
        change F (t (i + 1), t 0) = F (t i, t 0)
        rw [ht0, F.source, F.source]
      rw [hpoints, sub_self]
    · intro j hj
      exact hvertical i hi j hj
    · dsimp [right, value]
      rw [primitiveGridValue_eq F (U i (N - 1)) (theta i (N - 1))
        (t (i + 1), t ((N - 1) + 1)) (hrect i (N - 1)
          ⟨⟨ht (Nat.le_succ i), le_rfl⟩,
            ⟨ht (Nat.le_succ (N - 1)), le_rfl⟩⟩)]
      rw [primitiveGridValue_eq F (U i (N - 1)) (theta i (N - 1))
        (t i, t ((N - 1) + 1)) (hrect i (N - 1)
          ⟨⟨le_rfl, ht (Nat.le_succ i)⟩,
            ⟨ht (Nat.le_succ (N - 1)), le_rfl⟩⟩)]
      have hindex : (N - 1) + 1 = N := by omega
      have hpoints :
          (⟨F (t (i + 1), t ((N - 1) + 1)), hrect i (N - 1)
              ⟨⟨ht (Nat.le_succ i), le_rfl⟩,
                ⟨ht (Nat.le_succ (N - 1)), le_rfl⟩⟩⟩ : U i (N - 1)) =
            ⟨F (t i, t ((N - 1) + 1)), hrect i (N - 1)
              ⟨⟨le_rfl, ht (Nat.le_succ i)⟩,
                ⟨ht (Nat.le_succ (N - 1)), le_rfl⟩⟩⟩ := by
        apply Subtype.ext
        change F (t (i + 1), t ((N - 1) + 1)) =
          F (t i, t ((N - 1) + 1))
        rw [hindex, htN, F.target, F.target]
      rw [hpoints, sub_self]
  have hsweep := sum_grid_bottom_eq_sum_grid_top N hN bottom top hrow hhorizontal
  simpa [bottom, top, value] using hsweep

/-- A fixed coordinate primitive neighborhood for a closed one-form at a
point. -/
structure ClosedOneFormLocalPrimitive
    [RiemannSurface X]
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x : X) where
  carrier : TopologicalSpace.Opens X
  mem_carrier : x ∈ carrier
  primitive : C^∞⟮SurfaceRealModel, carrier; ℝ⟯
  differential_eq :
    restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) carrier 1 omega.1 =
      deRhamDifferential (I := SurfaceRealModel) (M := carrier) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) primitive)

/-- Choose one local primitive neighborhood at every point. -/
noncomputable def chosenClosedOneFormLocalPrimitive
    [RiemannSurface X]
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x : X) : ClosedOneFormLocalPrimitive omega x :=
  Classical.choice (by
    rcases exists_coordinateOpen_realPrimitive_and_smoothChains omega x with
      ⟨U, hxU, theta, hexact, _⟩
    exact ⟨⟨U, hxU, theta, hexact⟩⟩)

/-- A globally smooth real curve, restricted to the unit interval, is a
continuous path. -/
def smoothCurveUnitPath
    (gamma : ℝ → X)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma) :
    Path (gamma 0) (gamma 1) where
  toContinuousMap :=
    ⟨fun s : unitInterval ↦ gamma s,
      hgamma.continuous.comp continuous_subtype_val⟩
  source' := rfl
  target' := rfl

/--
%%handwave
name:
  Value of the unit path of a smooth curve
statement:
  The path obtained by restricting a smooth real curve \(\gamma\) to
  \([0,1]\) has value \(\gamma(s)\) at every unit-interval parameter \(s\).
proof:
  This is its defining evaluation.
-/
@[simp]
theorem smoothCurveUnitPath_apply
    (gamma : ℝ → X)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma)
    (s : unitInterval) :
    smoothCurveUnitPath gamma hgamma s = gamma s :=
  rfl

/--
%%handwave
name:
  An affine one-simplex parameter lies between its endpoints
statement:
  If \(a\le b\) and \((q_0,q_1)\) are barycentric coordinates on the standard
  one-simplex, then \(q_0a+q_1b\in[a,b]\).
proof:
  Use \(q_0,q_1\ge0\) and \(q_0+q_1=1\) to bound the convex combination below
  by \((q_0+q_1)a=a\) and above by \((q_0+q_1)b=b\).
-/
theorem oneSimplex_affine_parameter_mem_Icc_real
    (a b : ℝ) (hab : a ≤ b) (q : StandardSimplex 1) :
    ∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, b] i ∈ Icc a b := by
  have hq0 : 0 ≤ q.1 0 := q.2.1 0
  have hq1 : 0 ≤ q.1 1 := q.2.1 1
  have hqsum : q.1 0 + q.1 1 = 1 := by
    simpa [Fin.sum_univ_succ] using q.2.2
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · calc
      (a : ℝ) = 1 * a := by ring
      _ = (q.1 0 + q.1 1) * a := by rw [hqsum]
      _ = q.1 0 * a + q.1 1 * a := by ring
      _ ≤ q.1 0 * a + q.1 1 * b :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hab hq1)
  · calc
      q.1 0 * a + q.1 1 * b ≤ q.1 0 * b + q.1 1 * b :=
        add_le_add (mul_le_mul_of_nonneg_left hab hq0) le_rfl
      _ = (q.1 0 + q.1 1) * b := by ring
      _ = (b : ℝ) := by rw [hqsum]; ring

/--
%%handwave
name:
  Affine parameter bound for unit-interval endpoints
statement:
  If \(a\le b\) in \([0,1]\), every barycentric affine combination of \(a\)
  and \(b\) lies in the real interval \([a,b]\).
proof:
  Apply the real convex-combination bound to the underlying real numbers.
-/
theorem oneSimplex_affine_parameter_mem_Icc
    (a b : unitInterval) (hab : a ≤ b) (q : StandardSimplex 1) :
    ∑ i : Fin 2, (q : SimplexAmbient 1) i * ![(a : ℝ), (b : ℝ)] i ∈
      Icc (a : ℝ) (b : ℝ) :=
  oneSimplex_affine_parameter_mem_Icc_real (a : ℝ) (b : ℝ) hab q

/--
%%handwave
name:
  Bottom grid increment equals the first boundary-curve integral
statement:
  For a bottom-row grid cell contained in a primitive neighborhood, the local
  primitive increment between its horizontal endpoints equals the integral of
  \(\omega\) along the corresponding segment of the lower boundary curve.
proof:
  The bottom edge of the homotopy is the first boundary curve, and the entire
  affine segment lies in the cell's primitive neighborhood.  Apply the local
  primitive integral formula and identify the two endpoint values.
-/
theorem primitiveGrid_bottom_increment_eq_integral_segment
    [RiemannSurface X]
    {x₀ x₁ : X} {p q : Path x₀ x₁}
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (gamma : ℝ → X)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma)
    (F : Path.Homotopy p q)
    (hp : ∀ s : unitInterval, p s = gamma s)
    (t : ℕ → unitInterval) (ht : Monotone t) (ht0 : t 0 = 0)
    (j : ℕ)
    (U : TopologicalSpace.Opens X)
    (theta : C^∞⟮SurfaceRealModel, U; ℝ⟯)
    (hexact :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U 1 omega.1 =
        deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta))
    (hrect :
      Icc (t 0) (t 1) ×ˢ Icc (t j) (t (j + 1)) ⊆
        {z : unitInterval × unitInterval | F z ∈ U}) :
    primitiveGridValue F U theta (t 0, t (j + 1)) -
        primitiveGridValue F U theta (t 0, t j) =
      integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single
          (smoothCurveSegmentSimplex gamma hgamma (t j) (t (j + 1))) (1 : ℤ)) := by
  have hleft : t 0 ≤ t 1 := ht (Nat.zero_le 1)
  have hj : t j ≤ t (j + 1) := ht (Nat.le_succ j)
  have hstartF : F (t 0, t j) ∈ U :=
    hrect ⟨⟨le_rfl, hleft⟩, ⟨le_rfl, hj⟩⟩
  have hendF : F (t 0, t (j + 1)) ∈ U :=
    hrect ⟨⟨le_rfl, hleft⟩, ⟨hj, le_rfl⟩⟩
  have hstartEq : F (t 0, t j) = gamma (t j : ℝ) := by
    rw [ht0, F.apply_zero]
    exact hp (t j)
  have hendEq : F (t 0, t (j + 1)) = gamma (t (j + 1) : ℝ) := by
    rw [ht0, F.apply_zero]
    exact hp (t (j + 1))
  have hstart : gamma (t j : ℝ) ∈ U := by
    exact hstartEq ▸ hstartF
  have hend : gamma (t (j + 1) : ℝ) ∈ U := by
    exact hendEq ▸ hendF
  have hsegment : ∀ r : StandardSimplex 1,
      gamma (∑ i : Fin 2, (r : SimplexAmbient 1) i *
        ![(t j : ℝ), (t (j + 1) : ℝ)] i) ∈ U := by
    intro r
    let sReal : ℝ := ∑ i : Fin 2, (r : SimplexAmbient 1) i *
      ![(t j : ℝ), (t (j + 1) : ℝ)] i
    have hsIcc : sReal ∈ Icc (t j : ℝ) (t (j + 1) : ℝ) :=
      oneSimplex_affine_parameter_mem_Icc (t j) (t (j + 1)) hj r
    let s : unitInterval :=
      ⟨sReal, le_trans (t j).2.1 hsIcc.1,
        le_trans hsIcc.2 (t (j + 1)).2.2⟩
    have hsCell : (t 0, s) ∈
        Icc (t 0) (t 1) ×ˢ Icc (t j) (t (j + 1)) := by
      exact ⟨⟨le_rfl, hleft⟩, hsIcc⟩
    have hsF := hrect hsCell
    change gamma sReal ∈ U
    have hsEq : F (t 0, s) = gamma sReal := by
      rw [ht0, F.apply_zero]
      exact hp s
    exact hsEq ▸ hsF
  rw [primitiveGridValue_eq F U theta (t 0, t (j + 1)) hendF,
    primitiveGridValue_eq F U theta (t 0, t j) hstartF]
  have hendSubtype :
      (⟨F (t 0, t (j + 1)), hendF⟩ : U) =
        ⟨gamma (t (j + 1) : ℝ), hend⟩ := Subtype.ext hendEq
  have hstartSubtype :
      (⟨F (t 0, t j), hstartF⟩ : U) =
        ⟨gamma (t j : ℝ), hstart⟩ := Subtype.ext hstartEq
  rw [hendSubtype, hstartSubtype]
  exact (integrate_smoothCurveSegmentSimplex_eq_localPrimitive_sub
    omega.1 U theta hexact gamma hgamma (t j) (t (j + 1))
      hstart hend hsegment).symm

/--
%%handwave
name:
  Top grid increment equals the second boundary-curve integral
statement:
  For a top-row grid cell contained in a primitive neighborhood, the local
  primitive increment between its horizontal endpoints equals the integral of
  \(\omega\) along the corresponding segment of the upper boundary curve.
proof:
  The top edge of the homotopy is the second boundary curve.  The rectangle
  containment places its affine subsegment in the primitive neighborhood, so
  the local primitive integral formula gives the equality.
-/
theorem primitiveGrid_top_increment_eq_integral_segment
    [RiemannSurface X]
    {x₀ x₁ : X} {p q : Path x₀ x₁}
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (delta : ℝ → X)
    (hdelta : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ delta)
    (F : Path.Homotopy p q)
    (hq : ∀ s : unitInterval, q s = delta s)
    (t : ℕ → unitInterval) (ht : Monotone t)
    (N : ℕ) (hN : 0 < N) (htN : t N = 1)
    (j : ℕ)
    (U : TopologicalSpace.Opens X)
    (theta : C^∞⟮SurfaceRealModel, U; ℝ⟯)
    (hexact :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U 1 omega.1 =
        deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta))
    (hrect :
      Icc (t (N - 1)) (t ((N - 1) + 1)) ×ˢ
          Icc (t j) (t (j + 1)) ⊆
        {z : unitInterval × unitInterval | F z ∈ U}) :
    primitiveGridValue F U theta (t ((N - 1) + 1), t (j + 1)) -
        primitiveGridValue F U theta (t ((N - 1) + 1), t j) =
      integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single
          (smoothCurveSegmentSimplex delta hdelta (t j) (t (j + 1))) (1 : ℤ)) := by
  have hindex : (N - 1) + 1 = N := by omega
  have hfinal : t ((N - 1) + 1) = 1 := by rw [hindex, htN]
  have htop : t (N - 1) ≤ t ((N - 1) + 1) := ht (Nat.le_succ (N - 1))
  have hj : t j ≤ t (j + 1) := ht (Nat.le_succ j)
  have hstartF : F (t ((N - 1) + 1), t j) ∈ U :=
    hrect ⟨⟨htop, le_rfl⟩, ⟨le_rfl, hj⟩⟩
  have hendF : F (t ((N - 1) + 1), t (j + 1)) ∈ U :=
    hrect ⟨⟨htop, le_rfl⟩, ⟨hj, le_rfl⟩⟩
  have hstartEq : F (t ((N - 1) + 1), t j) = delta (t j : ℝ) := by
    rw [hfinal, F.apply_one]
    exact hq (t j)
  have hendEq : F (t ((N - 1) + 1), t (j + 1)) =
      delta (t (j + 1) : ℝ) := by
    rw [hfinal, F.apply_one]
    exact hq (t (j + 1))
  have hstart : delta (t j : ℝ) ∈ U := hstartEq ▸ hstartF
  have hend : delta (t (j + 1) : ℝ) ∈ U := hendEq ▸ hendF
  have hsegment : ∀ r : StandardSimplex 1,
      delta (∑ i : Fin 2, (r : SimplexAmbient 1) i *
        ![(t j : ℝ), (t (j + 1) : ℝ)] i) ∈ U := by
    intro r
    let sReal : ℝ := ∑ i : Fin 2, (r : SimplexAmbient 1) i *
      ![(t j : ℝ), (t (j + 1) : ℝ)] i
    have hsIcc : sReal ∈ Icc (t j : ℝ) (t (j + 1) : ℝ) :=
      oneSimplex_affine_parameter_mem_Icc (t j) (t (j + 1)) hj r
    let s : unitInterval :=
      ⟨sReal, le_trans (t j).2.1 hsIcc.1,
        le_trans hsIcc.2 (t (j + 1)).2.2⟩
    have hsCell : (t ((N - 1) + 1), s) ∈
        Icc (t (N - 1)) (t ((N - 1) + 1)) ×ˢ
          Icc (t j) (t (j + 1)) := by
      exact ⟨⟨htop, le_rfl⟩, hsIcc⟩
    have hsF := hrect hsCell
    change delta sReal ∈ U
    have hsEq : F (t ((N - 1) + 1), s) = delta sReal := by
      rw [hfinal, F.apply_one]
      exact hq s
    exact hsEq ▸ hsF
  rw [primitiveGridValue_eq F U theta (t ((N - 1) + 1), t (j + 1)) hendF,
    primitiveGridValue_eq F U theta (t ((N - 1) + 1), t j) hstartF]
  have hendSubtype :
      (⟨F (t ((N - 1) + 1), t (j + 1)), hendF⟩ : U) =
        ⟨delta (t (j + 1) : ℝ), hend⟩ := Subtype.ext hendEq
  have hstartSubtype :
      (⟨F (t ((N - 1) + 1), t j), hstartF⟩ : U) =
        ⟨delta (t j : ℝ), hstart⟩ := Subtype.ext hstartEq
  rw [hendSubtype, hstartSubtype]
  exact (integrate_smoothCurveSegmentSimplex_eq_localPrimitive_sub
    omega.1 U theta hexact delta hdelta (t j) (t (j + 1))
      hstart hend hsegment).symm

/--
%%handwave
name:
  Homotopy invariance of closed one-form integrals
statement:
  If two smooth curves on a Riemann surface have the same endpoints
  and are homotopic relative to those endpoints, then every closed real
  one-form has the same integral along the two curves.
proof:
  Cover the homotopy square by finitely many rectangles, each mapping into a
  neighborhood on which the form has a primitive.  Primitive differences
  cancel around every rectangle and agree along shared edges; the fixed side
  edges contribute zero.  Subdivision of the two smooth boundary curves is
  justified by Stokes' theorem on degenerate two-simplices.
tags:
  milestone
-/
theorem integrate_smoothCurveSegmentSimplex_eq_of_pathHomotopy
    [RiemannSurface X]
    {x₀ x₁ : X} {p q : Path x₀ x₁}
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (gamma delta : ℝ → X)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma)
    (hdelta : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ delta)
    (hp : ∀ s : unitInterval, p s = gamma s)
    (hq : ∀ s : unitInterval, q s = delta s)
    (F : Path.Homotopy p q) :
    integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex gamma hgamma 0 1) (1 : ℤ)) =
      integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex delta hdelta 0 1) (1 : ℤ)) := by
  let localPrimitive (x : X) := chosenClosedOneFormLocalPrimitive omega x
  let cover : X → Set X := fun x ↦ (localPrimitive x).carrier
  have hcoverOpen : ∀ x, IsOpen (cover x) := fun x ↦ (localPrimitive x).carrier.isOpen
  have hcover : univ ⊆ ⋃ x, cover x := by
    intro x _hx
    exact mem_iUnion.mpr ⟨x, (localPrimitive x).mem_carrier⟩
  rcases AnalyticContinuation.exists_monotone_rectangular_subdivision_subordinate_to_open_cover
      F F.continuous cover hcoverOpen hcover with
    ⟨t, ht0, ht, ⟨N₀, htEventually⟩, htRect⟩
  let N := N₀ + 1
  have hN : 0 < N := Nat.zero_lt_succ N₀
  have hNlarge : N₀ ≤ N := Nat.le_succ N₀
  have htN : t N = 1 := htEventually N hNlarge
  let center (i j : ℕ) : X := Classical.choose (htRect i j)
  have hcenter (i j : ℕ) :
      Icc (t i) (t (i + 1)) ×ˢ Icc (t j) (t (j + 1)) ⊆
        {z : unitInterval × unitInterval |
          F z ∈ cover (center i j)} :=
    Classical.choose_spec (htRect i j)
  let U (i j : ℕ) : TopologicalSpace.Opens X :=
    (localPrimitive (center i j)).carrier
  let theta (i j : ℕ) : C^∞⟮SurfaceRealModel, U i j; ℝ⟯ :=
    (localPrimitive (center i j)).primitive
  have hexact (i j : ℕ) :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) (U i j) 1 omega.1 =
        deRhamDifferential (I := SurfaceRealModel) (M := U i j) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) (theta i j)) :=
    (localPrimitive (center i j)).differential_eq
  have hrect (i j : ℕ) :
      Icc (t i) (t (i + 1)) ×ˢ Icc (t j) (t (j + 1)) ⊆
        {z : unitInterval × unitInterval | F z ∈ U i j} := by
    exact hcenter i j
  have hgrid := localPrimitive_grid_boundary_increments_eq
    omega F t ht N hN ht0 htN U theta hexact hrect
  have hbottom :
      ∑ j ∈ Finset.range N,
          (primitiveGridValue F (U 0 j) (theta 0 j) (t 0, t (j + 1)) -
            primitiveGridValue F (U 0 j) (theta 0 j) (t 0, t j)) =
        ∑ j ∈ Finset.range N,
          integrateSmoothChain (I := SurfaceRealModel) omega.1
            (Finsupp.single
              (smoothCurveSegmentSimplex gamma hgamma (t j) (t (j + 1)))
              (1 : ℤ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact primitiveGrid_bottom_increment_eq_integral_segment
      omega gamma hgamma F hp t ht ht0 j (U 0 j) (theta 0 j)
        (hexact 0 j) (hrect 0 j)
  have htop :
      ∑ j ∈ Finset.range N,
          (primitiveGridValue F (U (N - 1) j) (theta (N - 1) j)
              (t ((N - 1) + 1), t (j + 1)) -
            primitiveGridValue F (U (N - 1) j) (theta (N - 1) j)
              (t ((N - 1) + 1), t j)) =
        ∑ j ∈ Finset.range N,
          integrateSmoothChain (I := SurfaceRealModel) omega.1
            (Finsupp.single
              (smoothCurveSegmentSimplex delta hdelta (t j) (t (j + 1)))
              (1 : ℤ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact primitiveGrid_top_increment_eq_integral_segment
      omega delta hdelta F hq t ht N hN htN j (U (N - 1) j) (theta (N - 1) j)
        (hexact (N - 1) j) (hrect (N - 1) j)
  have hgammaSubdivision :=
    integrate_smoothCurveSegmentSimplex_eq_sum_subsegments
      omega gamma hgamma (fun n ↦ (t n : ℝ)) N hN
  have hdeltaSubdivision :=
    integrate_smoothCurveSegmentSimplex_eq_sum_subsegments
      omega delta hdelta (fun n ↦ (t n : ℝ)) N hN
  have hgammaSubdivision' :
      integrateSmoothChain (I := SurfaceRealModel) omega.1
          (Finsupp.single (smoothCurveSegmentSimplex gamma hgamma 0 1) (1 : ℤ)) =
        ∑ j ∈ Finset.range N,
          integrateSmoothChain (I := SurfaceRealModel) omega.1
            (Finsupp.single
              (smoothCurveSegmentSimplex gamma hgamma (t j) (t (j + 1)))
              (1 : ℤ)) := by
    simpa [ht0, htN] using hgammaSubdivision
  have hdeltaSubdivision' :
      integrateSmoothChain (I := SurfaceRealModel) omega.1
          (Finsupp.single (smoothCurveSegmentSimplex delta hdelta 0 1) (1 : ℤ)) =
        ∑ j ∈ Finset.range N,
          integrateSmoothChain (I := SurfaceRealModel) omega.1
            (Finsupp.single
              (smoothCurveSegmentSimplex delta hdelta (t j) (t (j + 1)))
              (1 : ℤ)) := by
    simpa [ht0, htN] using hdeltaSubdivision
  calc
    integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex gamma hgamma 0 1) (1 : ℤ)) =
        ∑ j ∈ Finset.range N,
          integrateSmoothChain (I := SurfaceRealModel) omega.1
            (Finsupp.single
              (smoothCurveSegmentSimplex gamma hgamma (t j) (t (j + 1)))
              (1 : ℤ)) := hgammaSubdivision'
    _ = ∑ j ∈ Finset.range N,
          (primitiveGridValue F (U 0 j) (theta 0 j) (t 0, t (j + 1)) -
            primitiveGridValue F (U 0 j) (theta 0 j) (t 0, t j)) := hbottom.symm
    _ = ∑ j ∈ Finset.range N,
          (primitiveGridValue F (U (N - 1) j) (theta (N - 1) j)
              (t ((N - 1) + 1), t (j + 1)) -
            primitiveGridValue F (U (N - 1) j) (theta (N - 1) j)
              (t ((N - 1) + 1), t j)) := hgrid
    _ = ∑ j ∈ Finset.range N,
          integrateSmoothChain (I := SurfaceRealModel) omega.1
            (Finsupp.single
              (smoothCurveSegmentSimplex delta hdelta (t j) (t (j + 1)))
              (1 : ℤ)) := htop
    _ = integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex delta hdelta 0 1) (1 : ℤ)) :=
      hdeltaSubdivision'.symm

/--
%%handwave
name:
  Endpoint invariance of closed one-form integrals on a simply connected surface
statement:
  If \(\gamma,\delta:\mathbb R\to X\) are smooth curves with the same values
  at \(0\) and \(1\), and \(X\) is simply connected, then every closed real
  one-form \(\omega\) satisfies
  \[
    \int_{\gamma|_{[0,1]}}\omega=\int_{\delta|_{[0,1]}}\omega.
  \]
proof:
  Regard the restrictions as paths with common endpoints.  Simple
  connectedness gives a path homotopy, and homotopy invariance of the integral
  gives the equality.
-/
theorem integrate_smoothCurveSegmentSimplex_eq_of_simplyConnected
    [RiemannSurface X] [SimplyConnectedSpace X]
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (gamma delta : ℝ → X)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma)
    (hdelta : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ delta)
    (hsource : gamma 0 = delta 0) (htarget : gamma 1 = delta 1) :
    integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex gamma hgamma 0 1) (1 : ℤ)) =
      integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex delta hdelta 0 1) (1 : ℤ)) := by
  let p : Path (gamma 0) (gamma 1) := smoothCurveUnitPath gamma hgamma
  let q : Path (gamma 0) (gamma 1) :=
    (smoothCurveUnitPath delta hdelta).cast hsource htarget
  let F : Path.Homotopy p q := SimplyConnectedSpace.paths_homotopic p q |>.some
  apply integrate_smoothCurveSegmentSimplex_eq_of_pathHomotopy
    omega gamma delta hgamma hdelta (p := p) (q := q) (F := F)
  · intro s
    rfl
  · intro s
    simp [q, Path.cast_coe, smoothCurveUnitPath]

/--
%%handwave
name:
  A constant curve segment has zero closed-form integral
statement:
  If a smooth curve \(\gamma\) is constant on \([a,b]\), with \(a\le b\),
  then the integral of any closed real one-form along that segment is zero.
proof:
  Choose a local primitive near the constant value.  The segment stays in its
  domain, so the integral is the primitive's endpoint difference, which
  vanishes because the endpoints coincide.
-/
theorem integrate_smoothCurveSegmentSimplex_eq_zero_of_constant
    [RiemannSurface X]
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (gamma : ℝ → X)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma)
    (a b : ℝ) (hab : a ≤ b)
    (hconstant : ∀ s ∈ Icc a b, gamma s = gamma a) :
    integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex gamma hgamma a b) (1 : ℤ)) = 0 := by
  let P := chosenClosedOneFormLocalPrimitive omega (gamma a)
  have ha : gamma a ∈ P.carrier := P.mem_carrier
  have hbEq : gamma b = gamma a := hconstant b ⟨hab, le_rfl⟩
  have hb : gamma b ∈ P.carrier := hbEq.symm ▸ ha
  have hsegment : ∀ q : StandardSimplex 1,
      gamma (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![a, b] i) ∈ P.carrier := by
    intro q
    have hs := oneSimplex_affine_parameter_mem_Icc_real a b hab q
    rw [hconstant _ hs]
    exact ha
  have hintegral := integrate_smoothCurveSegmentSimplex_eq_localPrimitive_sub
    omega.1 P.carrier P.primitive P.differential_eq gamma hgamma a b ha hb hsegment
  have hpoints : (⟨gamma b, hb⟩ : P.carrier) = ⟨gamma a, ha⟩ :=
    Subtype.ext hbEq
  rw [hpoints, sub_self] at hintegral
  exact hintegral

/-- The explicit smooth concatenation of two sitting curves used below.  The
switch is made while both curves are constant. -/
def smoothSittingJoin (gamma delta : ℝ → X) : ℝ → X := fun t ↦
  piecewise (Iic (2 : ℝ)) gamma (fun s ↦ delta (s - 3)) (4 * t)

/--
%%handwave
name:
  Smoothness of the sitting-curve join
statement:
  Let \(\gamma\) be smoothly constant at \(y\) for parameters at least one,
  and let \(\delta\) be smoothly constant at \(y\) for nonpositive
  parameters.  The rescaled piecewise curve that follows \(\gamma\) and then
  a shifted \(\delta\) is smooth.
proof:
  Near the switching parameter both pieces equal \(y\), so smooth piecewise
  gluing applies.  Composition with the affine rescaling preserves
  smoothness.
-/
theorem smoothSittingJoin_contMDiff
    {y : X} (gamma delta : ℝ → X)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma)
    (hdelta : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ delta)
    (hgamma_right : ∀ t, 1 ≤ t → gamma t = y)
    (hdelta_left : ∀ t, t ≤ 0 → delta t = y) :
    ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞
      (smoothSittingJoin gamma delta) := by
  let shiftedDelta : ℝ → X := fun t ↦ delta (t - 3)
  have hshiftedDelta :
      ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ shiftedDelta := by
    exact hdelta.comp (by
      rw [contMDiff_iff_contDiff]
      fun_prop)
  have hagree : gamma =ᶠ[nhds 2] shiftedDelta := by
    filter_upwards [Ioo_mem_nhds (show (1 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) < 3 by norm_num)] with t ht
    change gamma t = delta (t - 3)
    rw [hgamma_right t ht.1.le,
      hdelta_left (t - 3) (sub_nonpos.mpr ht.2.le)]
  have hpiece : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞
      (piecewise (Iic (2 : ℝ)) gamma shiftedDelta) :=
    ContMDiff.piecewise_Iic hgamma hshiftedDelta hagree
  exact hpiece.comp (by
    rw [contMDiff_iff_contDiff]
    fun_prop)

/--
%%handwave
name:
  Left half of the sitting-curve join
statement:
  For \(t\le\tfrac12\), the joined curve has value \(\gamma(4t)\).
proof:
  In this range the rescaled parameter \(4t\) lies on the left side of the
  piecewise switch.
-/
theorem smoothSittingJoin_eq_left
    (gamma delta : ℝ → X) (t : ℝ) (ht : t ≤ 1 / 2) :
    smoothSittingJoin gamma delta t = gamma (4 * t) := by
  simp [smoothSittingJoin, show 4 * t ≤ (2 : ℝ) by linarith]

/--
%%handwave
name:
  Right half of the sitting-curve join
statement:
  Under the sitting assumptions, for \(t\ge\tfrac12\) the joined curve has
  value \(\delta(4t-3)\).
proof:
  Above the switch this is the right piece by definition.  At the switch both
  curves equal their common sitting value.
-/
theorem smoothSittingJoin_eq_right
    {y : X} (gamma delta : ℝ → X)
    (hgamma_right : ∀ t, 1 ≤ t → gamma t = y)
    (hdelta_left : ∀ t, t ≤ 0 → delta t = y)
    (t : ℝ) (ht : 1 / 2 ≤ t) :
    smoothSittingJoin gamma delta t = delta (4 * t - 3) := by
  by_cases hswitch : 4 * t ≤ (2 : ℝ)
  · have htEq : t = 1 / 2 := by linarith
    rw [htEq]
    norm_num [smoothSittingJoin, hgamma_right, hdelta_left]
  · simp [smoothSittingJoin, hswitch]

/--
%%handwave
name:
  Simplex of the left half of a sitting-curve join
statement:
  The one-simplex traced by the joined curve on \([0,\tfrac12]\) equals the
  simplex traced by \(\gamma\) on \([0,2]\).
proof:
  On the left half the join is \(\gamma(4t)\); the affine simplex parameter
  rescales \([0,\tfrac12]\) to \([0,2]\).
-/
theorem smoothCurveSegmentSimplex_smoothSittingJoin_left
    (gamma delta : ℝ → X)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma)
    (hjoin : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞
      (smoothSittingJoin gamma delta)) :
    smoothCurveSegmentSimplex (smoothSittingJoin gamma delta) hjoin 0 (1 / 2) =
      smoothCurveSegmentSimplex gamma hgamma 0 2 := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  change smoothSittingJoin gamma delta
      (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![(0 : ℝ), (1 / 2 : ℝ)] i) =
    gamma (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![(0 : ℝ), (2 : ℝ)] i)
  have hs := oneSimplex_affine_parameter_mem_Icc_real
    (0 : ℝ) (1 / 2 : ℝ) (by norm_num) q
  rw [smoothSittingJoin_eq_left gamma delta _ hs.2]
  congr 1
  simp [Fin.sum_univ_two]
  ring

/--
%%handwave
name:
  Simplex of the right half of a sitting-curve join
statement:
  The one-simplex traced by the joined curve on \([\tfrac12,1]\) equals the
  simplex traced by \(\delta\) on \([-1,1]\).
proof:
  On the right half the join is \(\delta(4t-3)\), and this affine map sends
  \([\tfrac12,1]\) to \([-1,1]\).
-/
theorem smoothCurveSegmentSimplex_smoothSittingJoin_right
    {y : X} (gamma delta : ℝ → X)
    (hdelta : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ delta)
    (hjoin : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞
      (smoothSittingJoin gamma delta))
    (hgamma_right : ∀ t, 1 ≤ t → gamma t = y)
    (hdelta_left : ∀ t, t ≤ 0 → delta t = y) :
    smoothCurveSegmentSimplex (smoothSittingJoin gamma delta) hjoin (1 / 2) 1 =
      smoothCurveSegmentSimplex delta hdelta (-1) 1 := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  change smoothSittingJoin gamma delta
      (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![(1 / 2 : ℝ), (1 : ℝ)] i) =
    delta (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![(-1 : ℝ), (1 : ℝ)] i)
  have hs := oneSimplex_affine_parameter_mem_Icc_real
    (1 / 2 : ℝ) (1 : ℝ) (by norm_num) q
  rw [smoothSittingJoin_eq_right gamma delta hgamma_right hdelta_left _ hs.1]
  congr 1
  have hqsum : q.1 0 + q.1 1 = 1 := by
    simpa [Fin.sum_univ_two] using q.2.2
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    4 * (q.1 0 * (1 / 2 : ℝ) + q.1 1 * 1) - 3 =
        2 * q.1 0 + 4 * q.1 1 - 3 := by ring
    _ = -q.1 0 + q.1 1 := by linarith
    _ = q.1 0 * (-1) + q.1 1 * 1 := by ring

/--
%%handwave
name:
  Integral along a smooth sitting join
statement:
  If two sitting smooth curves meet at their common sitting value, then the
  integral of a closed one-form along their smooth join is the sum of the
  integrals along the original unit segments.
proof:
  Subdivide the join at \(1/2\), identify its halves with extended segments
  of the two curves, and discard the constant tails, whose integrals vanish.
-/
theorem integrate_smoothSittingJoin_eq_add
    [RiemannSurface X]
    {y : X}
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (gamma delta : ℝ → X)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma)
    (hdelta : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ delta)
    (hgamma_right : ∀ t, 1 ≤ t → gamma t = y)
    (hdelta_left : ∀ t, t ≤ 0 → delta t = y) :
    integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single
          (smoothCurveSegmentSimplex (smoothSittingJoin gamma delta)
            (smoothSittingJoin_contMDiff gamma delta hgamma hdelta
              hgamma_right hdelta_left) 0 1) (1 : ℤ)) =
      integrateSmoothChain (I := SurfaceRealModel) omega.1
          (Finsupp.single (smoothCurveSegmentSimplex gamma hgamma 0 1) (1 : ℤ)) +
        integrateSmoothChain (I := SurfaceRealModel) omega.1
          (Finsupp.single (smoothCurveSegmentSimplex delta hdelta 0 1) (1 : ℤ)) := by
  let hjoin := smoothSittingJoin_contMDiff gamma delta hgamma hdelta
    hgamma_right hdelta_left
  have hjoinSubdivision := integrate_smoothCurveSegmentSimplex_subdivision
    omega (smoothSittingJoin gamma delta) hjoin 0 (1 / 2) 1
  rw [smoothCurveSegmentSimplex_smoothSittingJoin_left gamma delta hgamma hjoin,
    smoothCurveSegmentSimplex_smoothSittingJoin_right gamma delta hdelta hjoin
      hgamma_right hdelta_left] at hjoinSubdivision
  have hgammaTail :
      integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex gamma hgamma 1 2) (1 : ℤ)) = 0 := by
    apply integrate_smoothCurveSegmentSimplex_eq_zero_of_constant
      omega gamma hgamma 1 2 (by norm_num)
    intro s hs
    exact (hgamma_right s hs.1).trans (hgamma_right 1 le_rfl).symm
  have hdeltaHead :
      integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single (smoothCurveSegmentSimplex delta hdelta (-1) 0) (1 : ℤ)) = 0 := by
    apply integrate_smoothCurveSegmentSimplex_eq_zero_of_constant
      omega delta hdelta (-1) 0 (by norm_num)
    intro s hs
    have hs0 : s ≤ 0 := hs.2
    exact (hdelta_left s hs0).trans (hdelta_left (-1) (by norm_num)).symm
  have hgammaSubdivision := integrate_smoothCurveSegmentSimplex_subdivision
    omega gamma hgamma 0 1 2
  have hdeltaSubdivision := integrate_smoothCurveSegmentSimplex_subdivision
    omega delta hdelta (-1) 0 1
  rw [hgammaTail, add_zero] at hgammaSubdivision
  rw [hdeltaHead, zero_add] at hdeltaSubdivision
  rw [hgammaSubdivision, hdeltaSubdivision] at hjoinSubdivision
  exact hjoinSubdivision

/-- A globally smooth curve with sitting half-lines at prescribed endpoints. -/
structure SmoothSittingCurve (x y : X) where
  curve : ℝ → X
  contMDiff_curve :
    ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ curve
  eq_source : ∀ t, t ≤ 0 → curve t = x
  eq_target : ∀ t, 1 ≤ t → curve t = y

/-- Choose a sitting smooth curve between any two points of a connected
surface. -/
noncomputable def chosenSmoothSittingCurve
    [ConnectedSpace X] (x y : X) : SmoothSittingCurve x y :=
  Classical.choice (by
    rcases smoothSittingJoined_all_exists x y with ⟨gamma, hgamma, hleft, hright⟩
    exact ⟨⟨gamma, hgamma, hleft, hright⟩⟩)

/--
%%handwave
name:
  Source of the chosen sitting curve
statement:
  The chosen sitting smooth curve from \(x\) to \(y\) has value \(x\) at
  parameter \(0\).
proof:
  It is constant at its source on the nonpositive half-line.
-/
@[simp]
theorem chosenSmoothSittingCurve_source
    [ConnectedSpace X] (x y : X) :
    (chosenSmoothSittingCurve x y).curve 0 = x :=
  (chosenSmoothSittingCurve x y).eq_source 0 le_rfl

/--
%%handwave
name:
  Target of the chosen sitting curve
statement:
  The chosen sitting smooth curve from \(x\) to \(y\) has value \(y\) at
  parameter \(1\).
proof:
  It is constant at its target from parameter one onward.
-/
@[simp]
theorem chosenSmoothSittingCurve_target
    [ConnectedSpace X] (x y : X) :
    (chosenSmoothSittingCurve x y).curve 1 = y :=
  (chosenSmoothSittingCurve x y).eq_target 1 le_rfl

/-- The candidate primitive obtained by integrating from a fixed basepoint
along a chosen sitting smooth curve. -/
noncomputable def closedOneFormPathPrimitive
    [RiemannSurface X]
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x₀ x : X) : ℝ :=
  let gamma := chosenSmoothSittingCurve x₀ x
  integrateSmoothChain (I := SurfaceRealModel) omega.1
    (Finsupp.single
      (smoothCurveSegmentSimplex gamma.curve gamma.contMDiff_curve 0 1) (1 : ℤ))

/--
%%handwave
name:
  The path-integral primitive differs locally by a constant
statement:
  Let \(d\theta=\omega\) on a connected open neighborhood \(V\).  For a fixed
  basepoint \(x_0\) and any \(x,y\in V\), the path-integral function satisfies
  \[
    F(y)=\theta(y)+F(x)-\theta(x).
  \]
proof:
  Join the chosen path from \(x_0\) to \(x\) to a sitting path inside \(V\)
  from \(x\) to \(y\).  Path independence identifies this join with the
  chosen path to \(y\), additivity splits its integral, and the local
  primitive theorem evaluates the final piece as \(\theta(y)-\theta(x)\).
-/
theorem closedOneFormPathPrimitive_eq_localPrimitive_add_const
    [RiemannSurface X] [SimplyConnectedSpace X]
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x₀ : X)
    (U V : TopologicalSpace.Opens X) (hVU : V ≤ U)
    [RiemannSurface V]
    (theta : C^∞⟮SurfaceRealModel, U; ℝ⟯)
    (hexact :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U 1 omega.1 =
        deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta))
    (x y : V) :
    closedOneFormPathPrimitive omega x₀ (y : X) =
      theta (TopologicalSpace.Opens.inclusion hVU y) +
        (closedOneFormPathPrimitive omega x₀ (x : X) -
          theta (TopologicalSpace.Opens.inclusion hVU x)) := by
  let gammaX := chosenSmoothSittingCurve x₀ (x : X)
  let gammaY := chosenSmoothSittingCurve x₀ (y : X)
  let etaV := chosenSmoothSittingCurve x y
  let eta : ℝ → X := fun t ↦ (etaV.curve t : X)
  have heta : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ eta :=
    (contMDiff_subtype_val (I := SurfaceRealModel)).comp etaV.contMDiff_curve
  have heta_left : ∀ t, t ≤ 0 → eta t = (x : X) := by
    intro t ht
    exact congrArg Subtype.val (etaV.eq_source t ht)
  have heta_right : ∀ t, 1 ≤ t → eta t = (y : X) := by
    intro t ht
    exact congrArg Subtype.val (etaV.eq_target t ht)
  let joined : ℝ → X := smoothSittingJoin gammaX.curve eta
  have hjoined : ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ joined :=
    smoothSittingJoin_contMDiff gammaX.curve eta gammaX.contMDiff_curve heta
      gammaX.eq_target heta_left
  have hsource : gammaY.curve 0 = joined 0 := by
    rw [show joined 0 = gammaX.curve 0 by
      simpa [joined] using
        smoothSittingJoin_eq_left gammaX.curve eta 0 (by norm_num)]
    rw [gammaY.eq_source 0 le_rfl, gammaX.eq_source 0 le_rfl]
  have htarget : gammaY.curve 1 = joined 1 := by
    rw [show joined 1 = eta 1 by
      have h := smoothSittingJoin_eq_right gammaX.curve eta gammaX.eq_target
        heta_left 1 (by norm_num)
      change joined 1 = eta 1
      change smoothSittingJoin gammaX.curve eta 1 = eta 1
      convert h using 1 <;> norm_num]
    rw [gammaY.eq_target 1 le_rfl, heta_right 1 le_rfl]
  have hpathIndependent :=
    integrate_smoothCurveSegmentSimplex_eq_of_simplyConnected
      omega gammaY.curve joined gammaY.contMDiff_curve hjoined hsource htarget
  have hjoinAdd := integrate_smoothSittingJoin_eq_add
    omega gammaX.curve eta gammaX.contMDiff_curve heta gammaX.eq_target heta_left
  have hxU : (x : X) ∈ U := hVU x.2
  have hyU : (y : X) ∈ U := hVU y.2
  have heta0U : eta 0 ∈ U := (heta_left 0 le_rfl).symm ▸ hxU
  have heta1U : eta 1 ∈ U := (heta_right 1 le_rfl).symm ▸ hyU
  have hetaSegment : ∀ q : StandardSimplex 1,
      eta (∑ i : Fin 2, (q : SimplexAmbient 1) i * ![(0 : ℝ), (1 : ℝ)] i) ∈ U := by
    intro q
    exact hVU (etaV.curve _).2
  have hetaIntegral := integrate_smoothCurveSegmentSimplex_eq_localPrimitive_sub
    omega.1 U theta hexact eta heta 0 1 heta0U heta1U hetaSegment
  have hetaSource : eta 0 = (x : X) := heta_left 0 le_rfl
  have hetaTarget : eta 1 = (y : X) := heta_right 1 le_rfl
  have hsourceSubtype : (⟨eta 0, heta0U⟩ : U) =
      TopologicalSpace.Opens.inclusion hVU x := Subtype.ext hetaSource
  have htargetSubtype : (⟨eta 1, heta1U⟩ : U) =
      TopologicalSpace.Opens.inclusion hVU y := Subtype.ext hetaTarget
  rw [htargetSubtype, hsourceSubtype] at hetaIntegral
  change
    integrateSmoothChain (I := SurfaceRealModel) omega.1
        (Finsupp.single
          (smoothCurveSegmentSimplex gammaY.curve gammaY.contMDiff_curve 0 1) (1 : ℤ)) = _
  rw [hpathIndependent, hjoinAdd, hetaIntegral]
  dsimp only [gammaX, closedOneFormPathPrimitive]
  ring

/--
%%handwave
name:
  Smoothness of the path-integral primitive
statement:
  On a simply connected Riemann surface, the function obtained by integrating
  a closed real one-form from a fixed basepoint to each point is smooth.
proof:
  Around every point choose a connected local primitive neighborhood.  There
  the path-integral function equals the smooth local primitive plus a
  constant, so smoothness follows locally.
-/
theorem closedOneFormPathPrimitive_contMDiff
    [RiemannSurface X] [SimplyConnectedSpace X]
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x₀ : X) :
    ContMDiff SurfaceRealModel (modelWithCornersSelf ℝ ℝ) ∞
      (closedOneFormPathPrimitive omega x₀) := by
  intro x
  let P := chosenClosedOneFormLocalPrimitive omega x
  let V : TopologicalSpace.Opens X :=
    ⟨pathComponentIn (P.carrier : Set X) x,
      P.carrier.isOpen.pathComponentIn x⟩
  have hxV : x ∈ V := mem_pathComponentIn_self P.mem_carrier
  have hVU : V ≤ P.carrier := fun z hz ↦ pathComponentIn_subset hz
  letI : RiemannSurface V :=
    riemannSurface_openSubset V ⟨x, hxV⟩
      (isPathConnected_pathComponentIn P.mem_carrier).isConnected.isPreconnected
  let xV : V := ⟨x, hxV⟩
  let xU : P.carrier := ⟨x, P.mem_carrier⟩
  let offset : ℝ :=
    closedOneFormPathPrimitive omega x₀ x - P.primitive xU
  let liftToU : X → P.carrier :=
    fallbackCodRestrictOpen id P.carrier xU
  let localModel : X → ℝ := fun z ↦ P.primitive (liftToU z) + offset
  have hliftOn : ContMDiffOn SurfaceRealModel SurfaceRealModel ∞ liftToU P.carrier := by
    exact contMDiffOn_fallbackCodRestrictOpen contMDiff_id P.carrier xU
      (P.carrier : Set X) (fun z hz ↦ by simpa using hz)
  have hliftAt : ContMDiffAt SurfaceRealModel SurfaceRealModel ∞ liftToU x :=
    (hliftOn x P.mem_carrier).contMDiffAt
      (P.carrier.isOpen.mem_nhds P.mem_carrier)
  have hlocalAt : ContMDiffAt SurfaceRealModel (modelWithCornersSelf ℝ ℝ) ∞
      localModel x := by
    exact (P.primitive.contMDiff.contMDiffAt.comp x hliftAt).add contMDiffAt_const
  have heq : closedOneFormPathPrimitive omega x₀ =ᶠ[nhds x] localModel := by
    filter_upwards [V.isOpen.mem_nhds hxV] with y hyV
    let yV : V := ⟨y, hyV⟩
    have hformula := closedOneFormPathPrimitive_eq_localPrimitive_add_const
      omega x₀ P.carrier V hVU P.primitive P.differential_eq xV yV
    have hyU : y ∈ P.carrier := hVU hyV
    simpa [localModel, liftToU, fallbackCodRestrictOpen, dif_pos hyU,
      offset, xU, xV, yV] using hformula
  exact hlocalAt.congr_of_eventuallyEq heq

/-- The smooth function obtained from the path integral. -/
noncomputable def closedOneFormPathPrimitiveSmooth
    [RiemannSurface X] [SimplyConnectedSpace X]
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x₀ : X) : C^∞⟮SurfaceRealModel, X; ℝ⟯ :=
  ⟨closedOneFormPathPrimitive omega x₀,
    closedOneFormPathPrimitive_contMDiff omega x₀⟩

/--
%%handwave
name:
  Differential of the path-integral primitive
statement:
  On a simply connected Riemann surface, if
  \(F(x)=\int_{x_0}^x\omega\) for a closed real one-form \(\omega\), then
  \[
    dF=\omega.
  \]
proof:
  On a connected local primitive neighborhood, \(F\) differs from a local
  primitive \(\theta\) by a constant.  Hence \(dF=d\theta=\omega\) there.
  Since this holds near every point, the global forms are equal.
-/
theorem deRhamDifferential_closedOneFormPathPrimitive_eq
    [RiemannSurface X] [SimplyConnectedSpace X]
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x₀ : X) :
    deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
          (closedOneFormPathPrimitiveSmooth omega x₀)) =
      omega.1 := by
  let globalTheta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 0 :=
    smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
      (closedOneFormPathPrimitiveSmooth omega x₀)
  let globalD : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1 :=
    deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 0 globalTheta
  change globalD = omega.1
  apply DifferentialForm.ext
  intro x
  let P := chosenClosedOneFormLocalPrimitive omega x
  let V : TopologicalSpace.Opens X :=
    ⟨pathComponentIn (P.carrier : Set X) x,
      P.carrier.isOpen.pathComponentIn x⟩
  have hxV : x ∈ V := mem_pathComponentIn_self P.mem_carrier
  have hVU : V ≤ P.carrier := fun z hz ↦ pathComponentIn_subset hz
  letI : RiemannSurface V :=
    riemannSurface_openSubset V ⟨x, hxV⟩
      (isPathConnected_pathComponentIn P.mem_carrier).isConnected.isPreconnected
  let xV : V := ⟨x, hxV⟩
  let offset : ℝ :=
    closedOneFormPathPrimitive omega x₀ x -
      P.primitive (TopologicalSpace.Opens.inclusion hVU xV)
  let localTheta : C^∞⟮SurfaceRealModel, V; ℝ⟯ :=
    { val := fun y ↦ P.primitive (TopologicalSpace.Opens.inclusion hVU y) + offset
      property :=
        (P.primitive.contMDiff.comp
          (contMDiff_inclusion (I := SurfaceRealModel) hVU)).add contMDiff_const }
  have hlocalValue (y : V) :
      closedOneFormPathPrimitive omega x₀ (y : X) = localTheta y := by
    have hformula := closedOneFormPathPrimitive_eq_localPrimitive_add_const
      omega x₀ P.carrier V hVU P.primitive P.differential_eq xV y
    simpa [localTheta, offset, xV] using hformula
  have hzeroRestrict :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) V 0 globalTheta =
        smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) localTheta := by
    apply DifferentialForm.ext
    intro y
    ext v
    rw [show v = (fun i : Fin 0 ↦ nomatch i) from Subsingleton.elim _ _]
    change closedOneFormPathPrimitive omega x₀ (y : X) = localTheta y
    exact hlocalValue y
  let thetaU : SmoothForms (I := SurfaceRealModel) (M := P.carrier) ℝ 0 :=
    smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) P.primitive
  let thetaV : SmoothForms (I := SurfaceRealModel) (M := V) ℝ 0 :=
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ) hVU 0 thetaU
  let constV : SmoothForms (I := SurfaceRealModel) (M := V) ℝ 0 :=
    smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
      (smoothRealConstantFunction (I0 := SurfaceRealModel) offset)
  have hlocalZero :
      smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) localTheta =
        thetaV + constV := by
    apply DifferentialForm.ext
    intro y
    ext v
    rw [show v = (fun i : Fin 0 ↦ nomatch i) from Subsingleton.elim _ _]
    have hthetaV := restrict_smoothRealFunctionToZeroForm_apply hVU P.primitive y
    change P.primitive (TopologicalSpace.Opens.inclusion hVU y) + offset =
      thetaV.toFun y (fun i : Fin 0 ↦ nomatch i) + offset
    rw [hthetaV]
  have hdlocal :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) V 1 globalD =
        restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) V 1 omega.1 := by
    calc
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) V 1 globalD =
          deRhamDifferential (I := SurfaceRealModel) (M := V) (A := ℝ) 0
            (restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) V 0
              globalTheta) :=
        (deRhamDifferential_restrictSmoothFormsToOpen
          (I := SurfaceRealModel) (A := ℝ) V globalTheta).symm
      _ = deRhamDifferential (I := SurfaceRealModel) (M := V) (A := ℝ) 0
            (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) localTheta) := by
        rw [hzeroRestrict]
      _ = deRhamDifferential (I := SurfaceRealModel) (M := V) (A := ℝ) 0
            (thetaV + constV) := by rw [hlocalZero]
      _ = deRhamDifferential (I := SurfaceRealModel) (M := V) (A := ℝ) 0
            thetaV := by
        rw [map_add, deRhamDifferential_smoothRealFunctionToZeroForm_const, add_zero]
      _ = restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) V 1 omega.1 := by
        dsimp only [thetaV]
        rw [deRhamDifferential_restrictSmoothFormsOfLE]
        exact (restrictSmoothFormsToOpen_eq_restrictSmoothFormsOfLE_of_restrict_eq_surface
          V P.carrier hVU omega.1 _ P.differential_eq).symm
  let L : TangentSpace SurfaceRealModel xV →L[ℝ] TangentSpace SurfaceRealModel x :=
    mfderiv SurfaceRealModel SurfaceRealModel (fun y : V ↦ (y : X)) xV
  have hpoint := congrArg
    (fun eta : SmoothForms (I := SurfaceRealModel) (M := V) ℝ 1 ↦ eta.toFun xV)
    hdlocal
  change (globalD.toFun x).compContinuousLinearMap L =
    (omega.1.toFun x).compContinuousLinearMap L at hpoint
  exact continuousAlternatingMap_compContinuousLinearMap_injective L
    (mfderiv_subtypeVal_bijective (I := SurfaceRealModel) V xV).2 hpoint

/--
%%handwave
name:
  Closed one-forms on a simply connected surface have primitives
statement:
  Every closed real one-form on a simply connected Riemann surface
  is the differential of a globally defined smooth function.
proof:
  Fix a base point and integrate the form along a chosen smooth path to each
  point.  Homotopy invariance makes this independent of the chosen path.  On a
  local primitive neighborhood the resulting function differs from the local
  primitive by a constant, so it is smooth and has the prescribed
  differential.
tags:
  milestone
-/
theorem simplyConnected_surface_closedOneForm_has_primitive
    [RiemannSurface X] [SimplyConnectedSpace X]
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1) :
    ∃ theta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 0,
      deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 0 theta =
        omega.1 := by
  let x₀ : X := Classical.choice (PathConnectedSpace.nonempty : Nonempty X)
  exact ⟨smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
      (closedOneFormPathPrimitiveSmooth omega x₀),
    deRhamDifferential_closedOneFormPathPrimitive_eq omega x₀⟩

/--
%%handwave
name:
  Vanishing of real smooth first de Rham cohomology on a simply connected surface
statement:
  If \(X\) is a simply connected Riemann surface, then
  \(H^1_{\mathrm{dR}}(X;\mathbb R)=0\) for the real smooth structure.
proof:
  Every closed real one-form has the global path-integral primitive constructed
  above, so every closed one-form is exact.
-/
theorem simplyConnected_surface_deRhamH1_zero_of_realSmooth
    [RiemannSurface X] [SimplyConnectedSpace X] :
    Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1) := by
  apply deRhamCohomology_subsingleton_of_closedForms_succ_le_exactForms
    (I := SurfaceRealModel) (M := X) (A := ℝ) (n := 0)
  intro omega
  rcases simplyConnected_surface_closedOneForm_has_primitive omega with
    ⟨theta, htheta⟩
  change omega.1 ∈ LinearMap.range
    (deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 0)
  exact ⟨theta, htheta⟩

omit [IsManifold SurfaceRealModel ∞ X] in
/--
%%handwave
name:
  First de Rham cohomology of a simply connected Riemann surface
statement:
  The first real de Rham cohomology of a simply connected Riemann
  surface is zero.
proof:
  Use the canonical underlying real smooth structure.  The path-integral
  construction gives a smooth global primitive for every closed real
  one-form, so every degree-one cocycle is exact.
tags:
  milestone
-/
theorem simplyConnected_surface_deRhamH1_zero
    [RiemannSurface X] [SimplyConnectedSpace X] :
    letI : IsManifold SurfaceRealModel ∞ X :=
      complexOneManifold_has_real_smooth_structure X
    Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1) := by
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  exact simplyConnected_surface_deRhamH1_zero_of_realSmooth (X := X)

end

end JJMath.Uniformization
