import JJMath.Uniformization.SmoothPathConnectivity
import JJMath.Uniformization.SurfaceEndPath

/-!
# Smooth locally finite chains of paths on surfaces

The proper rays obtained from an exhaustion are initially assembled from
arbitrary continuous paths.  For the proper-line construction we instead use
smooth paths with sitting ends.  The sitting intervals make a countable path
chain globally smooth, including at all of its joining times.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Manifold

open JJMath.Uniformization

noncomputable section

/-- The negative constant patch and the open time patches used by a smooth
countable path chain. -/
def smoothPathChainPatch : Option ℕ → Set ℝ
  | none => Set.Iio (1 / 4 : ℝ)
  | some n =>
      {t | (n : ℝ) - 1 / 4 < t ∧ t < (n : ℝ) + 5 / 4}

/--
%%handwave
name:
  Openness of the time patches for a smooth path chain
statement:
  The initial patch \((-\infty,1/4)\) and every path patch
  \((n-1/4,n+5/4)\) are open subsets of \(\mathbb R\).
proof:
  They are open intervals, with each path patch written as the intersection
  of two open half-lines.
-/
theorem isOpen_smoothPathChainPatch (i : Option ℕ) :
    IsOpen (smoothPathChainPatch i) := by
  cases i with
  | none => exact isOpen_Iio
  | some n =>
      change IsOpen
        ({t : ℝ | (n : ℝ) - 1 / 4 < t} ∩
          {t : ℝ | t < (n : ℝ) + 5 / 4})
      exact (isOpen_lt continuous_const continuous_id).inter
        (isOpen_lt continuous_id continuous_const)

/-- The local representative of a smooth path chain.  The affine
reparametrization traverses the path in the middle half of each unit time
interval, leaving a sitting quarter-interval at each end. -/
def smoothPathChainLocalMap
    {X : Type*} [TopologicalSpace X]
    (x : ℕ → X) (gamma : ℕ → ℝ → X)
    (hgamma_cont : ∀ n, Continuous (gamma n))
    (i : Option ℕ) : C(smoothPathChainPatch i, X) := by
  cases i with
  | none => exact ContinuousMap.const _ (x 0)
  | some n =>
      exact
        { toFun := fun t => gamma n
            (2 * ((t.1 : ℝ) - (n : ℝ)) - 1 / 2)
          continuous_toFun := (hgamma_cont n).comp (by fun_prop) }

/--
%%handwave
name:
  Agreement of local maps in a sitting path chain
statement:
  Suppose each path \(\gamma_n\) is constant at \(x_n\) before time \(0\)
  and at \(x_{n+1}\) after time \(1\).  Then any two local representatives of
  the countable path chain agree wherever their time patches overlap.
proof:
  The initial patch overlaps only the zeroth path patch, where both maps equal
  \(x_0\).  Two numbered patches can overlap only when their indices are equal
  or adjacent; in the adjacent case the sitting-end hypotheses make both
  values the common vertex.
-/
theorem smoothPathChainLocalMap_agree
    {X : Type*} [TopologicalSpace X]
    (x : ℕ → X) (gamma : ℕ → ℝ → X)
    (hgamma_cont : ∀ n, Continuous (gamma n))
    (hleft : ∀ n t, t ≤ 0 → gamma n t = x n)
    (hright : ∀ n t, 1 ≤ t → gamma n t = x (n + 1))
    (i j : Option ℕ) (t : ℝ)
    (hti : t ∈ smoothPathChainPatch i)
    (htj : t ∈ smoothPathChainPatch j) :
    smoothPathChainLocalMap x gamma hgamma_cont i ⟨t, hti⟩ =
      smoothPathChainLocalMap x gamma hgamma_cont j ⟨t, htj⟩ := by
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some n =>
          cases n with
          | zero =>
              simp only [smoothPathChainLocalMap, ContinuousMap.const_apply,
                ContinuousMap.coe_mk]
              symm
              apply hleft
              simp only [Nat.cast_zero, sub_zero]
              change t < (1 / 4 : ℝ) at hti
              linarith
          | succ n =>
              exfalso
              change t < (1 / 4 : ℝ) at hti
              change ((n + 1 : ℕ) : ℝ) - 1 / 4 < t ∧
                t < ((n + 1 : ℕ) : ℝ) + 5 / 4 at htj
              have hn : (0 : ℝ) ≤ n := by positivity
              push_cast at htj
              linarith
  | some i =>
      cases j with
      | none =>
          cases i with
          | zero =>
              simp only [smoothPathChainLocalMap, ContinuousMap.const_apply,
                ContinuousMap.coe_mk]
              apply hleft
              simp only [Nat.cast_zero, sub_zero]
              change t < (1 / 4 : ℝ) at htj
              linarith
          | succ i =>
              exfalso
              change t < (1 / 4 : ℝ) at htj
              change ((i + 1 : ℕ) : ℝ) - 1 / 4 < t ∧
                t < ((i + 1 : ℕ) : ℝ) + 5 / 4 at hti
              have hi : (0 : ℝ) ≤ i := by positivity
              push_cast at hti
              linarith
      | some j =>
          have adjacent_of_lt (hij : i < j) : j = i + 1 := by
            have hlt : j < i + 2 := by
              by_contra hnot
              have hle : i + 2 ≤ j := Nat.le_of_not_gt hnot
              have hle' : (i : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hle
              change (i : ℝ) - 1 / 4 < t ∧
                t < (i : ℝ) + 5 / 4 at hti
              change (j : ℝ) - 1 / 4 < t ∧
                t < (j : ℝ) + 5 / 4 at htj
              linarith
            omega
          have adjacent_of_gt (hji : j < i) : i = j + 1 := by
            have hlt : i < j + 2 := by
              by_contra hnot
              have hle : j + 2 ≤ i := Nat.le_of_not_gt hnot
              have hle' : (j : ℝ) + 2 ≤ (i : ℝ) := by exact_mod_cast hle
              change (i : ℝ) - 1 / 4 < t ∧
                t < (i : ℝ) + 5 / 4 at hti
              change (j : ℝ) - 1 / 4 < t ∧
                t < (j : ℝ) + 5 / 4 at htj
              linarith
            omega
          rcases lt_trichotomy i j with hij | hij | hij
          · have hji : j = i + 1 := adjacent_of_lt hij
            subst j
            simp only [smoothPathChainLocalMap]
            change gamma i (2 * (t - (i : ℝ)) - 1 / 2) =
              gamma (i + 1)
                (2 * (t - ((i + 1 : ℕ) : ℝ)) - 1 / 2)
            rw [hright i _ (by
                change (i : ℝ) - 1 / 4 < t ∧
                  t < (i : ℝ) + 5 / 4 at hti
                change (((i + 1 : ℕ) : ℝ) - 1 / 4 < t ∧
                  t < ((i + 1 : ℕ) : ℝ) + 5 / 4) at htj
                push_cast at htj
                linarith),
              hleft (i + 1) _ (by
                change (i : ℝ) - 1 / 4 < t ∧
                  t < (i : ℝ) + 5 / 4 at hti
                push_cast
                linarith)]
          · subst j
            rfl
          · have hij' : i = j + 1 := adjacent_of_gt hij
            subst i
            simp only [smoothPathChainLocalMap]
            change gamma (j + 1)
                (2 * (t - ((j + 1 : ℕ) : ℝ)) - 1 / 2) =
              gamma j (2 * (t - (j : ℝ)) - 1 / 2)
            rw [hleft (j + 1) _ (by
                change (j : ℝ) - 1 / 4 < t ∧
                  t < (j : ℝ) + 5 / 4 at htj
                push_cast
                linarith),
              hright j _ (by
                change (((j + 1 : ℕ) : ℝ) - 1 / 4 < t ∧
                  t < ((j + 1 : ℕ) : ℝ) + 5 / 4) at hti
                push_cast at hti
                linarith)]

/--
%%handwave
name:
  The time patches cover the real line
statement:
  Every \(t\in\mathbb R\) has a neighborhood contained in one of the sitting
  path-chain patches.
proof:
  If \(t<1/4\), use the initial patch.  Otherwise choose
  \(n=\lfloor t\rfloor\); then
  \(n-1/4<t<n+5/4\), so the \(n\)-th open patch is a neighborhood of \(t\).
-/
theorem smoothPathChainPatch_cover (t : ℝ) :
    ∃ i : Option ℕ, smoothPathChainPatch i ∈ 𝓝 t := by
  by_cases ht : t < 1 / 4
  · exact ⟨none, isOpen_Iio.mem_nhds ht⟩
  · have ht0 : 0 ≤ t := by linarith
    let n : ℕ := ⌊ t ⌋₊
    have hfloor : (n : ℝ) ≤ t := Nat.floor_le ht0
    have hnext : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
    refine ⟨some n, (isOpen_smoothPathChainPatch (some n)).mem_nhds ?_⟩
    change (n : ℝ) - 1 / 4 < t ∧ t < (n : ℝ) + 5 / 4
    constructor <;> linarith

/-- A countable chain of smooth paths with sitting ends, assembled as a
globally continuous map on the real line.  It is constant at `x 0` on the
negative end. -/
noncomputable def smoothSittingPathChainLine
    {X : Type*} [TopologicalSpace X]
    (x : ℕ → X) (gamma : ℕ → ℝ → X)
    (hgamma_cont : ∀ n, Continuous (gamma n))
    (hleft : ∀ n t, t ≤ 0 → gamma n t = x n)
    (hright : ∀ n t, 1 ≤ t → gamma n t = x (n + 1)) : C(ℝ, X) :=
  ContinuousMap.liftCover smoothPathChainPatch
    (smoothPathChainLocalMap x gamma hgamma_cont)
    (smoothPathChainLocalMap_agree x gamma hgamma_cont hleft hright)
    smoothPathChainPatch_cover

/--
%%handwave
name:
  A glued sitting path chain equals each local representative
statement:
  On every time patch, the globally glued countable path chain agrees with
  the corresponding local path-chain map.
proof:
  This is the defining local equality supplied by gluing continuous maps that
  agree on overlaps.
-/
theorem smoothSittingPathChainLine_eq_local
    {X : Type*} [TopologicalSpace X]
    (x : ℕ → X) (gamma : ℕ → ℝ → X)
    (hgamma_cont : ∀ n, Continuous (gamma n))
    (hleft : ∀ n t, t ≤ 0 → gamma n t = x n)
    (hright : ∀ n t, 1 ≤ t → gamma n t = x (n + 1))
    (i : Option ℕ) (t : ℝ) (ht : t ∈ smoothPathChainPatch i) :
    smoothSittingPathChainLine x gamma hgamma_cont hleft hright t =
      smoothPathChainLocalMap x gamma hgamma_cont i ⟨t, ht⟩ := by
  exact ContinuousMap.liftCover_coe ⟨t, ht⟩

/--
%%handwave
name:
  Smoothness of a countable sitting path chain
statement:
  If every \(\gamma_n:\mathbb R\to X\) is smooth and has the prescribed
  sitting ends, then the glued map \(\Gamma:\mathbb R\to X\) is smooth.
proof:
  Smoothness is local.  On the initial patch, \(\Gamma\) is constant; on the
  \(n\)-th patch, it is \(\gamma_n\) composed with an affine time change.
  The local agreement theorem transfers these smooth descriptions to the
  glued map.
-/
theorem contMDiff_smoothSittingPathChainLine
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (x : ℕ → X) (gamma : ℕ → ℝ → X)
    (hgamma : ∀ n,
      ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ (gamma n))
    (hleft : ∀ n t, t ≤ 0 → gamma n t = x n)
    (hright : ∀ n t, 1 ≤ t → gamma n t = x (n + 1)) :
    ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞
      (smoothSittingPathChainLine x gamma (fun n => (hgamma n).continuous)
        hleft hright) := by
  apply contMDiff_of_locally_contMDiffOn
  intro t
  rcases smoothPathChainPatch_cover t with ⟨i, hi⟩
  let S := smoothPathChainPatch i
  have htS : t ∈ S := mem_of_mem_nhds hi
  refine ⟨S, isOpen_smoothPathChainPatch i, htS, ?_⟩
  cases i with
  | none =>
      apply ContMDiffOn.congr contMDiffOn_const
      intro y hy
      exact smoothSittingPathChainLine_eq_local x gamma
        (fun n => (hgamma n).continuous) hleft hright none y hy
  | some n =>
      have hlocal : ContMDiff (modelWithCornersSelf ℝ ℝ)
          SurfaceRealModel ∞
          (fun y : ℝ => gamma n (2 * (y - (n : ℝ)) - 1 / 2)) := by
        exact (hgamma n).comp (by
          rw [contMDiff_iff_contDiff]
          fun_prop)
      apply ContMDiffOn.congr hlocal.contMDiffOn
      intro y hy
      exact smoothSittingPathChainLine_eq_local x gamma
        (fun n => (hgamma n).continuous) hleft hright (some n) y hy

/--
%%handwave
name:
  Tail containment for a countable sitting path chain
statement:
  Let \(U_0\supseteq U_1\supseteq\cdots\), with the image of \(\gamma_k\)
  contained in \(U_k\).  If \(n\le t\), then the glued path-chain value
  \(\Gamma(t)\) lies in \(U_n\).
proof:
  Put \(k=\lfloor t\rfloor\).  The local formula places \(\Gamma(t)\) on
  \(\gamma_k\), hence in \(U_k\); since \(n\le k\) and the family is
  decreasing, \(U_k\subseteq U_n\).
-/
theorem smoothSittingPathChainLine_mem_of_le
    {X : Type*} [TopologicalSpace X]
    {U : ℕ → Set X} (x : ℕ → X) (gamma : ℕ → ℝ → X)
    (hgamma_cont : ∀ n, Continuous (gamma n))
    (hleft : ∀ n t, t ≤ 0 → gamma n t = x n)
    (hright : ∀ n t, 1 ≤ t → gamma n t = x (n + 1))
    (hU : Antitone U)
    (hgamma_mem : ∀ n t, gamma n t ∈ U n)
    (n : ℕ) (t : ℝ) (hnt : (n : ℝ) ≤ t) :
    smoothSittingPathChainLine x gamma hgamma_cont hleft hright t ∈ U n := by
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg n) hnt
  let k : ℕ := ⌊ t ⌋₊
  have hfloor : (k : ℝ) ≤ t := Nat.floor_le ht0
  have hnext : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  have htk : t ∈ smoothPathChainPatch (some k) := by
    change (k : ℝ) - 1 / 4 < t ∧ t < (k : ℝ) + 5 / 4
    constructor <;> linarith
  rw [smoothSittingPathChainLine_eq_local x gamma hgamma_cont
    hleft hright (some k) t htk]
  apply hU
  · exact Nat.le_floor hnt
  · exact hgamma_mem k _

end

end JJMath.Manifold
