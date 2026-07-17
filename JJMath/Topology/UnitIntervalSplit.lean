import Mathlib.Topology.Subpath
import Mathlib.Topology.UnitInterval

/-!
# Splitting the unit interval

Elementary reparametrizations of the unit interval used to compare a
concatenated path with its two halves.
-/

namespace JJMath

noncomputable section

namespace unitInterval

/--
If `b` lies between `a` and `c`, this is the parameter at which the subpath
from `a` to `c` reaches `b`.
-/
def orderedMiddleParameter
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) : unitInterval :=
  ⟨((b - a) / (c - a) : ℝ),
    by
      by_cases h : (c - a : ℝ) = 0
      · have hac : (a : ℝ) = c := by linarith
        simp [hac]
      · have hba : 0 ≤ ((b : ℝ) - (a : ℝ)) := sub_nonneg.mpr hab
        have hca : 0 ≤ ((c : ℝ) - (a : ℝ)) := sub_nonneg.mpr (hab.trans hbc)
        exact div_nonneg hba hca,
    by
      by_cases h : (c - a : ℝ) = 0
      · have hac : (a : ℝ) = c := by linarith
        simp [hac]
      · have hba_ca : ((b : ℝ) - (a : ℝ)) ≤ ((c : ℝ) - (a : ℝ)) := by
          linarith [show (b : ℝ) ≤ c from hbc]
        have hca : 0 ≤ ((c : ℝ) - (a : ℝ)) := sub_nonneg.mpr (hab.trans hbc)
        exact div_le_one_of_le₀ hba_ca hca⟩

@[simp]
theorem coe_orderedMiddleParameter
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) :
    (orderedMiddleParameter a b c hab hbc : ℝ) =
      ((b : ℝ) - (a : ℝ)) / ((c : ℝ) - (a : ℝ)) :=
  rfl

/-- The ordered middle parameter recovers the middle point by convex combination. -/
theorem orderedMiddleParameter_spec
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) :
    b = Set.Icc.convexComb a c
      (orderedMiddleParameter a b c hab hbc) :=
  Set.Icc.eq_convexComb hab hbc

theorem orderedMiddleParameter_pos_of_lt
    (a b c : unitInterval) (hab : a < b) (hbc : b ≤ c) :
    (0 : ℝ) < orderedMiddleParameter a b c hab.le hbc := by
  change (0 : ℝ) < ((b : ℝ) - (a : ℝ)) / ((c : ℝ) - (a : ℝ))
  apply div_pos
  · linarith [show (a : ℝ) < b from hab]
  · linarith [show (a : ℝ) < b from hab, show (b : ℝ) ≤ c from hbc]

theorem orderedMiddleParameter_lt_one_of_lt
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b < c) :
    (orderedMiddleParameter a b c hab hbc.le : ℝ) < 1 := by
  change ((b : ℝ) - (a : ℝ)) / ((c : ℝ) - (a : ℝ)) < 1
  have hden : 0 < ((c : ℝ) - (a : ℝ)) := by
    linarith [show (a : ℝ) ≤ b from hab, show (b : ℝ) < c from hbc]
  have hnum : ((b : ℝ) - (a : ℝ)) < ((c : ℝ) - (a : ℝ)) := by
    linarith [show (b : ℝ) < c from hbc]
  calc
    ((b : ℝ) - (a : ℝ)) / ((c : ℝ) - (a : ℝ))
        < ((c : ℝ) - (a : ℝ)) / ((c : ℝ) - (a : ℝ)) :=
          div_lt_div_of_pos_right hnum hden
    _ = 1 := by
      field_simp [ne_of_gt hden]

/-- The first-half reparametrization `t ↦ t / 2` of the unit interval. -/
def firstHalf (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2, by
    constructor
    · nlinarith [unitInterval.nonneg t]
    · nlinarith [unitInterval.le_one t]⟩

/-- The second-half reparametrization `t ↦ (1 + t) / 2` of the unit interval. -/
def secondHalf (t : unitInterval) : unitInterval :=
  ⟨(1 + (t : ℝ)) / 2, by
    constructor
    · nlinarith [unitInterval.nonneg t]
    · nlinarith [unitInterval.le_one t]⟩

@[simp]
theorem coe_firstHalf (t : unitInterval) :
    (firstHalf t : ℝ) = (t : ℝ) / 2 :=
  rfl

@[simp]
theorem coe_secondHalf (t : unitInterval) :
    (secondHalf t : ℝ) = (1 + (t : ℝ)) / 2 :=
  rfl

@[simp]
theorem firstHalf_zero : firstHalf 0 = 0 := by
  ext
  norm_num [firstHalf]

@[simp]
theorem firstHalf_one : firstHalf 1 = (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval) := by
  ext
  norm_num [firstHalf]

@[simp]
theorem secondHalf_zero : secondHalf 0 = (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval) := by
  ext
  norm_num [secondHalf]

@[simp]
theorem secondHalf_one : secondHalf 1 = 1 := by
  ext
  norm_num [secondHalf]

theorem firstHalf_le_half (t : unitInterval) :
    (firstHalf t : ℝ) ≤ 1 / 2 := by
  change (t : ℝ) / 2 ≤ 1 / 2
  nlinarith [unitInterval.le_one t]

theorem half_le_secondHalf (t : unitInterval) :
    (1 / 2 : ℝ) ≤ secondHalf t := by
  change (1 / 2 : ℝ) ≤ (1 + (t : ℝ)) / 2
  nlinarith [unitInterval.nonneg t]

/-- Double a unit-interval point known to lie in the first half. -/
def doubleOfLeHalf (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    unitInterval :=
  ⟨2 * (t : ℝ), by
    constructor
    · nlinarith [unitInterval.nonneg t]
    · nlinarith⟩

/--
Convert a unit-interval point known to lie in the second half to the
corresponding parameter on the second path.
-/
def doubleSubOneOfHalfLe (t : unitInterval) (ht : (1 / 2 : ℝ) ≤ t) :
    unitInterval :=
  ⟨2 * (t : ℝ) - 1, by
    constructor
    · nlinarith
    · nlinarith [unitInterval.le_one t]⟩

@[simp]
theorem coe_doubleOfLeHalf (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    (doubleOfLeHalf t ht : ℝ) = 2 * (t : ℝ) :=
  rfl

@[simp]
theorem coe_doubleSubOneOfHalfLe
    (t : unitInterval) (ht : (1 / 2 : ℝ) ≤ t) :
    (doubleSubOneOfHalfLe t ht : ℝ) = 2 * (t : ℝ) - 1 :=
  rfl

@[simp]
theorem doubleOfLeHalf_firstHalf (t : unitInterval)
    (ht : (unitInterval.firstHalf t : ℝ) ≤ 1 / 2 := firstHalf_le_half t) :
    doubleOfLeHalf (firstHalf t) ht = t := by
  ext
  change 2 * ((t : ℝ) / 2) = (t : ℝ)
  ring

@[simp]
theorem firstHalf_doubleOfLeHalf (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    firstHalf (doubleOfLeHalf t ht) = t := by
  ext
  change (2 * (t : ℝ)) / 2 = (t : ℝ)
  ring

@[simp]
theorem doubleSubOneOfHalfLe_secondHalf (t : unitInterval)
    (ht : (1 / 2 : ℝ) ≤ unitInterval.secondHalf t := half_le_secondHalf t) :
    doubleSubOneOfHalfLe (secondHalf t) ht = t := by
  ext
  change 2 * ((1 + (t : ℝ)) / 2) - 1 = (t : ℝ)
  ring

@[simp]
theorem secondHalf_doubleSubOneOfHalfLe (t : unitInterval)
    (ht : (1 / 2 : ℝ) ≤ t) :
    secondHalf (doubleSubOneOfHalfLe t ht) = t := by
  ext
  change (1 + (2 * (t : ℝ) - 1)) / 2 = (t : ℝ)
  ring

/-- Rescale a parameter `u ∈ [0,r]` back to the unit interval. -/
def splitAtRescaleLeft
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hu : u ≤ r) :
    unitInterval :=
  ⟨(u : ℝ) / r,
    div_nonneg (unitInterval.nonneg u) hr0.le,
    div_le_one_of_le₀ hu hr0.le⟩

@[simp]
theorem coe_splitAtRescaleLeft
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hu : u ≤ r) :
    (splitAtRescaleLeft r u hr0 hu : ℝ) = (u : ℝ) / r :=
  rfl

/-- Rescaling inverts the left subinterval parametrization. -/
theorem convexCombo_zero_right_splitAtRescaleLeft
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hu : u ≤ r) :
    Set.Icc.convexComb 0 r (splitAtRescaleLeft r u hr0 hu) = u := by
  ext
  simp [splitAtRescaleLeft, Set.Icc.convexComb]
  field_simp [ne_of_gt hr0]

/-- Rescale a parameter `u ∈ [r,1]` back to the unit interval. -/
def splitAtRescaleRight
    (r u : unitInterval) (hr1 : (r : ℝ) < 1) (hu : r ≤ u) :
    unitInterval :=
  ⟨((u : ℝ) - r) / (1 - r),
    by exact div_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hr1.le),
    by
      have hur : ((u : ℝ) - r) ≤ 1 - (r : ℝ) := by
        linarith [unitInterval.le_one u]
      exact div_le_one_of_le₀ hur (sub_nonneg.mpr hr1.le)⟩

@[simp]
theorem coe_splitAtRescaleRight
    (r u : unitInterval) (hr1 : (r : ℝ) < 1) (hu : r ≤ u) :
    (splitAtRescaleRight r u hr1 hu : ℝ) =
      ((u : ℝ) - r) / (1 - r) :=
  rfl

/-- Rescaling inverts the right subinterval parametrization. -/
theorem convexCombo_left_one_splitAtRescaleRight
    (r u : unitInterval) (hr1 : (r : ℝ) < 1) (hu : r ≤ u) :
    Set.Icc.convexComb r 1 (splitAtRescaleRight r u hr1 hu) = u := by
  ext
  have hne : (1 - (r : ℝ)) ≠ 0 := by linarith
  simp [splitAtRescaleRight, Set.Icc.convexComb]
  field_simp [hne]
  ring

/--
The split-path parameter corresponding to an original parameter `u`, for an
interior breakpoint `r`.
-/
noncomputable def splitAtReparam
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    unitInterval :=
  if hu : u ≤ r then
    firstHalf (splitAtRescaleLeft r u hr0 hu)
  else
    secondHalf
      (splitAtRescaleRight r u hr1 (le_of_lt (lt_of_not_ge hu)))

theorem splitAtReparam_of_le
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (hu : u ≤ r) :
    splitAtReparam r u hr0 hr1 =
      firstHalf (splitAtRescaleLeft r u hr0 hu) := by
  simp [splitAtReparam, hu]

theorem splitAtReparam_of_ge
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (hu : r ≤ u) :
    splitAtReparam r u hr0 hr1 =
      secondHalf (splitAtRescaleRight r u hr1 hu) := by
  by_cases hur : u ≤ r
  · have hru : u = r := le_antisymm hur hu
    subst u
    have hleft :
        firstHalf (splitAtRescaleLeft r r hr0 le_rfl) =
          secondHalf (splitAtRescaleRight r r hr1 le_rfl) := by
      ext
      simp [firstHalf, secondHalf, splitAtRescaleLeft, splitAtRescaleRight]
      field_simp [ne_of_gt hr0, sub_ne_zero.mpr (ne_of_lt hr1)]
    rw [splitAtReparam_of_le r r hr0 hr1 le_rfl, hleft]
  · simp [splitAtReparam, hur]

/-- The split reparameterization is monotone. -/
theorem splitAtReparam_mono
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    {u v : unitInterval} (huv : u ≤ v) :
    splitAtReparam r u hr0 hr1 ≤
      splitAtReparam r v hr0 hr1 := by
  by_cases hur : u ≤ r
  · by_cases hvr : v ≤ r
    · rw [splitAtReparam_of_le r u hr0 hr1 hur,
        splitAtReparam_of_le r v hr0 hr1 hvr]
      change ((u : ℝ) / r) / 2 ≤ ((v : ℝ) / r) / 2
      have hdiv : (u : ℝ) / r ≤ (v : ℝ) / r :=
        div_le_div_of_nonneg_right huv hr0.le
      nlinarith
    · have hrv : r ≤ v := le_of_lt (lt_of_not_ge hvr)
      rw [splitAtReparam_of_le r u hr0 hr1 hur,
        splitAtReparam_of_ge r v hr0 hr1 hrv]
      change
        (firstHalf (splitAtRescaleLeft r u hr0 hur) : ℝ) ≤
          (secondHalf (splitAtRescaleRight r v hr1 hrv) : ℝ)
      exact le_trans (firstHalf_le_half _) (half_le_secondHalf _)
  · have hru : r ≤ u := le_of_lt (lt_of_not_ge hur)
    have hrv : r ≤ v := hru.trans huv
    rw [splitAtReparam_of_ge r u hr0 hr1 hru,
      splitAtReparam_of_ge r v hr0 hr1 hrv]
    change
      (1 + (((u : ℝ) - r) / (1 - r))) / 2 ≤
        (1 + (((v : ℝ) - r) / (1 - r))) / 2
    have hnum : ((u : ℝ) - r) ≤ ((v : ℝ) - r) := by
      linarith [show (u : ℝ) ≤ v from huv]
    have hdiv :
        ((u : ℝ) - r) / (1 - r) ≤
          ((v : ℝ) - r) / (1 - r) :=
      div_le_div_of_nonneg_right hnum (sub_nonneg.mpr hr1.le)
    nlinarith

@[simp]
theorem splitAtReparam_zero
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    splitAtReparam r 0 hr0 hr1 = 0 := by
  rw [splitAtReparam_of_le r 0 hr0 hr1
    (show (0 : unitInterval) ≤ r from hr0.le)]
  ext
  simp [firstHalf, splitAtRescaleLeft]

@[simp]
theorem splitAtReparam_one
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    splitAtReparam r 1 hr0 hr1 = 1 := by
  rw [splitAtReparam_of_ge r 1 hr0 hr1
    (show r ≤ (1 : unitInterval) from hr1.le)]
  ext
  have hne : (1 - (r : ℝ)) ≠ 0 := by linarith
  simp [secondHalf, splitAtRescaleRight]
  field_simp [hne]
  norm_num

/--
The original-path parameter corresponding to a parameter on the split path.
-/
noncomputable def splitAtOriginalParameter
    (r t : unitInterval) (_hr0 : (0 : ℝ) < r) (_hr1 : (r : ℝ) < 1) :
    unitInterval :=
  if ht : (t : ℝ) ≤ 1 / 2 then
    Set.Icc.convexComb 0 r (doubleOfLeHalf t ht)
  else
    Set.Icc.convexComb r 1
      (doubleSubOneOfHalfLe t (le_of_lt (lt_of_not_ge ht)))

theorem splitAtOriginalParameter_of_le_half
    (r t : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (ht : (t : ℝ) ≤ 1 / 2) :
    splitAtOriginalParameter r t hr0 hr1 =
      Set.Icc.convexComb 0 r (doubleOfLeHalf t ht) := by
  unfold splitAtOriginalParameter
  rw [dif_pos ht]

theorem splitAtOriginalParameter_of_half_le
    (r t : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (ht : (1 / 2 : ℝ) ≤ t) :
    splitAtOriginalParameter r t hr0 hr1 =
      Set.Icc.convexComb r 1 (doubleSubOneOfHalfLe t ht) := by
  by_cases ht' : (t : ℝ) ≤ 1 / 2
  · have ht_eq : (t : ℝ) = 1 / 2 := le_antisymm ht' ht
    unfold splitAtOriginalParameter
    rw [dif_pos ht']
    ext
    simp [Set.Icc.convexComb, doubleOfLeHalf, doubleSubOneOfHalfLe]
    nlinarith [ht_eq]
  · ext
    unfold splitAtOriginalParameter
    rw [dif_neg ht']

/-- The inverse split parameter is monotone. -/
theorem splitAtOriginalParameter_mono
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    {s t : unitInterval} (hst : s ≤ t) :
    splitAtOriginalParameter r s hr0 hr1 ≤
      splitAtOriginalParameter r t hr0 hr1 := by
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [splitAtOriginalParameter_of_le_half r s hr0 hr1 hs,
        splitAtOriginalParameter_of_le_half r t hr0 hr1 ht]
      change
        ((Set.Icc.convexComb 0 r (doubleOfLeHalf s hs) : unitInterval) : ℝ) ≤
          ((Set.Icc.convexComb 0 r (doubleOfLeHalf t ht) : unitInterval) : ℝ)
      simp [Set.Icc.convexComb]
      nlinarith [show (0 : ℝ) ≤ r from hr0.le, show (s : ℝ) ≤ t from hst]
    · have ht' : (1 / 2 : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht)
      rw [splitAtOriginalParameter_of_le_half r s hr0 hr1 hs,
        splitAtOriginalParameter_of_half_le r t hr0 hr1 ht']
      exact Set.Icc.convexComb_le (show (0 : unitInterval) ≤ r from hr0.le) _
        |>.trans (Set.Icc.le_convexComb (show r ≤ (1 : unitInterval) from hr1.le) _)
  · have hs' : (1 / 2 : ℝ) ≤ s := le_of_lt (lt_of_not_ge hs)
    have ht' : (1 / 2 : ℝ) ≤ t := hs'.trans hst
    rw [splitAtOriginalParameter_of_half_le r s hr0 hr1 hs',
      splitAtOriginalParameter_of_half_le r t hr0 hr1 ht']
    change
      ((Set.Icc.convexComb r 1 (doubleSubOneOfHalfLe s hs') :
          unitInterval) : ℝ) ≤
        ((Set.Icc.convexComb r 1 (doubleSubOneOfHalfLe t ht') :
          unitInterval) : ℝ)
    simp [Set.Icc.convexComb]
    nlinarith [show (r : ℝ) ≤ 1 from hr1.le, show (s : ℝ) ≤ t from hst]

/-- Inverting the split reparameterization recovers the original parameter. -/
theorem splitAtOriginalParameter_splitAtReparam
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    splitAtOriginalParameter r (splitAtReparam r u hr0 hr1) hr0 hr1 = u := by
  by_cases hu : u ≤ r
  · rw [splitAtReparam_of_le r u hr0 hr1 hu]
    rw [splitAtOriginalParameter_of_le_half]
    · rw [doubleOfLeHalf_firstHalf]
      exact convexCombo_zero_right_splitAtRescaleLeft r u hr0 hu
    · exact firstHalf_le_half _
  · have hru : r ≤ u := le_of_lt (lt_of_not_ge hu)
    rw [splitAtReparam_of_ge r u hr0 hr1 hru]
    rw [splitAtOriginalParameter_of_half_le]
    · rw [doubleSubOneOfHalfLe_secondHalf]
      exact convexCombo_left_one_splitAtRescaleRight r u hr1 hru
    · exact half_le_secondHalf _

/-- Reparameterizing the original parameter of a split path recovers the split parameter. -/
theorem splitAtReparam_splitAtOriginalParameter
    (r t : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    splitAtReparam r (splitAtOriginalParameter r t hr0 hr1) hr0 hr1 = t := by
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [splitAtOriginalParameter_of_le_half r t hr0 hr1 ht]
    have hu :
        (Set.Icc.convexComb 0 r (doubleOfLeHalf t ht) : unitInterval) ≤ r :=
      Set.Icc.convexComb_le (show (0 : unitInterval) ≤ r from hr0.le) _
    rw [splitAtReparam_of_le r
      (Set.Icc.convexComb 0 r (doubleOfLeHalf t ht)) hr0 hr1 hu]
    ext
    simp [firstHalf, splitAtRescaleLeft, Set.Icc.convexComb]
    field_simp [ne_of_gt hr0]
  · have ht' : (1 / 2 : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht)
    rw [splitAtOriginalParameter_of_half_le r t hr0 hr1 ht']
    have hu :
        r ≤
          (Set.Icc.convexComb r 1 (doubleSubOneOfHalfLe t ht') :
            unitInterval) :=
      Set.Icc.le_convexComb (show r ≤ (1 : unitInterval) from hr1.le) _
    rw [splitAtReparam_of_ge r
      (Set.Icc.convexComb r 1 (doubleSubOneOfHalfLe t ht')) hr0 hr1 hu]
    ext
    have hne : (1 - (r : ℝ)) ≠ 0 := by linarith
    simp [secondHalf, splitAtRescaleRight, Set.Icc.convexComb]
    field_simp [hne]
    ring

/--
If a split parameter lies between the split images of two original
parameters, its original inverse lies between those original parameters.
-/
theorem splitAtOriginalParameter_mem_interval_of_reparam_bounds
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    {a b t : unitInterval}
    (hleft : splitAtReparam r a hr0 hr1 ≤ t)
    (hright : t ≤ splitAtReparam r b hr0 hr1) :
    a ≤ splitAtOriginalParameter r t hr0 hr1 ∧
      splitAtOriginalParameter r t hr0 hr1 ≤ b := by
  constructor
  · have hmono := splitAtOriginalParameter_mono r hr0 hr1 hleft
    simpa [splitAtOriginalParameter_splitAtReparam] using hmono
  · have hmono := splitAtOriginalParameter_mono r hr0 hr1 hright
    simpa [splitAtOriginalParameter_splitAtReparam] using hmono

/--
If an original parameter lies between original images of two split parameters,
its split inverse lies between those split parameters.
-/
theorem splitAtReparam_mem_interval_of_originalParameter_bounds
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    {a b t : unitInterval}
    (hleft : splitAtOriginalParameter r a hr0 hr1 ≤ t)
    (hright : t ≤ splitAtOriginalParameter r b hr0 hr1) :
    a ≤ splitAtReparam r t hr0 hr1 ∧
      splitAtReparam r t hr0 hr1 ≤ b := by
  constructor
  · have hmono := splitAtReparam_mono r hr0 hr1 hleft
    simpa [splitAtReparam_splitAtOriginalParameter] using hmono
  · have hmono := splitAtReparam_mono r hr0 hr1 hright
    simpa [splitAtReparam_splitAtOriginalParameter] using hmono

/--
The parameter change from `p.trans (q.trans r)` to `(p.trans q).trans r`.
-/
def reassocRightToLeft (t : unitInterval) : unitInterval :=
  if ht₁ : (t : ℝ) ≤ 1 / 2 then
    ⟨(t : ℝ) / 2, by
      constructor
      · nlinarith [unitInterval.nonneg t]
      · nlinarith [unitInterval.le_one t]⟩
  else if ht₂ : (t : ℝ) ≤ 3 / 4 then
    ⟨(t : ℝ) - 1 / 4, by
      constructor
      · nlinarith [le_of_lt (lt_of_not_ge ht₁)]
      · nlinarith [ht₂]⟩
  else
    ⟨2 * (t : ℝ) - 1, by
      constructor
      · nlinarith [le_of_lt (lt_of_not_ge ht₂)]
      · nlinarith [unitInterval.le_one t]⟩

/--
The inverse parameter change from `(p.trans q).trans r` to
`p.trans (q.trans r)`.
-/
def reassocLeftToRight (t : unitInterval) : unitInterval :=
  if ht₁ : (t : ℝ) ≤ 1 / 4 then
    ⟨2 * (t : ℝ), by
      constructor
      · nlinarith [unitInterval.nonneg t]
      · nlinarith [ht₁]⟩
  else if ht₂ : (t : ℝ) ≤ 1 / 2 then
    ⟨(t : ℝ) + 1 / 4, by
      constructor
      · nlinarith [unitInterval.nonneg t]
      · nlinarith [ht₂]⟩
  else
    ⟨((t : ℝ) + 1) / 2, by
      constructor
      · nlinarith [unitInterval.nonneg t]
      · nlinarith [unitInterval.le_one t]⟩

@[simp]
theorem reassocRightToLeft_zero :
    reassocRightToLeft 0 = 0 := by
  ext
  simp [reassocRightToLeft]

@[simp]
theorem reassocRightToLeft_one :
    reassocRightToLeft 1 = 1 := by
  ext
  simp [reassocRightToLeft]
  norm_num

@[simp]
theorem reassocLeftToRight_zero :
    reassocLeftToRight 0 = 0 := by
  ext
  simp [reassocLeftToRight]

@[simp]
theorem reassocLeftToRight_one :
    reassocLeftToRight 1 = 1 := by
  ext
  simp [reassocLeftToRight]
  norm_num

theorem coe_reassocRightToLeft_of_le_half
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    (reassocRightToLeft t : ℝ) = (t : ℝ) / 2 := by
  unfold reassocRightToLeft
  rw [dif_pos ht]

theorem coe_reassocRightToLeft_of_half_lt_of_le_three_quarters
    (t : unitInterval) (ht₁ : ¬ (t : ℝ) ≤ 1 / 2)
    (ht₂ : (t : ℝ) ≤ 3 / 4) :
    (reassocRightToLeft t : ℝ) = (t : ℝ) - 1 / 4 := by
  unfold reassocRightToLeft
  rw [dif_neg ht₁, dif_pos ht₂]

theorem coe_reassocRightToLeft_of_three_quarters_lt
    (t : unitInterval) (ht₁ : ¬ (t : ℝ) ≤ 1 / 2)
    (ht₂ : ¬ (t : ℝ) ≤ 3 / 4) :
    (reassocRightToLeft t : ℝ) = 2 * (t : ℝ) - 1 := by
  unfold reassocRightToLeft
  rw [dif_neg ht₁, dif_neg ht₂]

theorem coe_reassocLeftToRight_of_le_quarter
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 4) :
    (reassocLeftToRight t : ℝ) = 2 * (t : ℝ) := by
  unfold reassocLeftToRight
  rw [dif_pos ht]

theorem coe_reassocLeftToRight_of_quarter_lt_of_le_half
    (t : unitInterval) (ht₁ : ¬ (t : ℝ) ≤ 1 / 4)
    (ht₂ : (t : ℝ) ≤ 1 / 2) :
    (reassocLeftToRight t : ℝ) = (t : ℝ) + 1 / 4 := by
  unfold reassocLeftToRight
  rw [dif_neg ht₁, dif_pos ht₂]

theorem coe_reassocLeftToRight_of_half_lt
    (t : unitInterval) (ht₁ : ¬ (t : ℝ) ≤ 1 / 4)
    (ht₂ : ¬ (t : ℝ) ≤ 1 / 2) :
    (reassocLeftToRight t : ℝ) = ((t : ℝ) + 1) / 2 := by
  unfold reassocLeftToRight
  rw [dif_neg ht₁, dif_neg ht₂]

theorem reassocRightToLeft_mono :
    Monotone reassocRightToLeft := by
  intro a b hab
  change (reassocRightToLeft a : ℝ) ≤ (reassocRightToLeft b : ℝ)
  by_cases ha₁ : (a : ℝ) ≤ 1 / 2
  · by_cases hb₁ : (b : ℝ) ≤ 1 / 2
    · rw [coe_reassocRightToLeft_of_le_half a ha₁,
        coe_reassocRightToLeft_of_le_half b hb₁]
      nlinarith [show (a : ℝ) ≤ b from hab]
    · by_cases hb₂ : (b : ℝ) ≤ 3 / 4
      · rw [coe_reassocRightToLeft_of_le_half a ha₁,
          coe_reassocRightToLeft_of_half_lt_of_le_three_quarters b hb₁ hb₂]
        nlinarith [unitInterval.le_one a, le_of_lt (lt_of_not_ge hb₁)]
      · rw [coe_reassocRightToLeft_of_le_half a ha₁,
          coe_reassocRightToLeft_of_three_quarters_lt b hb₁ hb₂]
        nlinarith [unitInterval.le_one a, le_of_lt (lt_of_not_ge hb₂)]
  · have hb₁ : ¬ (b : ℝ) ≤ 1 / 2 := by
      intro hb₁
      exact ha₁ ((show (a : ℝ) ≤ b from hab).trans hb₁)
    by_cases ha₂ : (a : ℝ) ≤ 3 / 4
    · by_cases hb₂ : (b : ℝ) ≤ 3 / 4
      · rw [coe_reassocRightToLeft_of_half_lt_of_le_three_quarters a ha₁ ha₂,
          coe_reassocRightToLeft_of_half_lt_of_le_three_quarters b hb₁ hb₂]
        nlinarith [show (a : ℝ) ≤ b from hab]
      · rw [coe_reassocRightToLeft_of_half_lt_of_le_three_quarters a ha₁ ha₂,
          coe_reassocRightToLeft_of_three_quarters_lt b hb₁ hb₂]
        nlinarith [unitInterval.le_one a, le_of_lt (lt_of_not_ge hb₂)]
    · have hb₂ : ¬ (b : ℝ) ≤ 3 / 4 := by
        intro hb₂
        exact ha₂ ((show (a : ℝ) ≤ b from hab).trans hb₂)
      rw [coe_reassocRightToLeft_of_three_quarters_lt a ha₁ ha₂,
        coe_reassocRightToLeft_of_three_quarters_lt b hb₁ hb₂]
      nlinarith [show (a : ℝ) ≤ b from hab]

theorem reassocLeftToRight_mono :
    Monotone reassocLeftToRight := by
  intro a b hab
  change (reassocLeftToRight a : ℝ) ≤ (reassocLeftToRight b : ℝ)
  by_cases ha₁ : (a : ℝ) ≤ 1 / 4
  · by_cases hb₁ : (b : ℝ) ≤ 1 / 4
    · rw [coe_reassocLeftToRight_of_le_quarter a ha₁,
        coe_reassocLeftToRight_of_le_quarter b hb₁]
      nlinarith [show (a : ℝ) ≤ b from hab]
    · by_cases hb₂ : (b : ℝ) ≤ 1 / 2
      · rw [coe_reassocLeftToRight_of_le_quarter a ha₁,
          coe_reassocLeftToRight_of_quarter_lt_of_le_half b hb₁ hb₂]
        nlinarith [unitInterval.nonneg a, le_of_lt (lt_of_not_ge hb₁)]
      · rw [coe_reassocLeftToRight_of_le_quarter a ha₁,
          coe_reassocLeftToRight_of_half_lt b hb₁ hb₂]
        nlinarith [unitInterval.nonneg a, le_of_lt (lt_of_not_ge hb₂)]
  · have hb₁ : ¬ (b : ℝ) ≤ 1 / 4 := by
      intro hb₁
      exact ha₁ ((show (a : ℝ) ≤ b from hab).trans hb₁)
    by_cases ha₂ : (a : ℝ) ≤ 1 / 2
    · by_cases hb₂ : (b : ℝ) ≤ 1 / 2
      · rw [coe_reassocLeftToRight_of_quarter_lt_of_le_half a ha₁ ha₂,
          coe_reassocLeftToRight_of_quarter_lt_of_le_half b hb₁ hb₂]
        nlinarith [show (a : ℝ) ≤ b from hab]
      · rw [coe_reassocLeftToRight_of_quarter_lt_of_le_half a ha₁ ha₂,
          coe_reassocLeftToRight_of_half_lt b hb₁ hb₂]
        nlinarith [unitInterval.le_one a, le_of_lt (lt_of_not_ge hb₂)]
    · have hb₂ : ¬ (b : ℝ) ≤ 1 / 2 := by
        intro hb₂
        exact ha₂ ((show (a : ℝ) ≤ b from hab).trans hb₂)
      rw [coe_reassocLeftToRight_of_half_lt a ha₁ ha₂,
        coe_reassocLeftToRight_of_half_lt b hb₁ hb₂]
      nlinarith [show (a : ℝ) ≤ b from hab]

theorem reassocLeftToRight_reassocRightToLeft
    (t : unitInterval) :
    reassocLeftToRight (reassocRightToLeft t) = t := by
  ext
  by_cases ht₁ : (t : ℝ) ≤ 1 / 2
  · have hleft : ((t : ℝ) / 2) ≤ 1 / 4 := by nlinarith
    rw [coe_reassocLeftToRight_of_le_quarter _ (by
        simpa [coe_reassocRightToLeft_of_le_half t ht₁] using hleft),
      coe_reassocRightToLeft_of_le_half t ht₁]
    ring
  · by_cases ht₂ : (t : ℝ) ≤ 3 / 4
    · have hnot_left : ¬ ((t : ℝ) - 1 / 4 ≤ 1 / 4) := by
        intro h
        exact ht₁ (by nlinarith)
      have hmid : ((t : ℝ) - 1 / 4) ≤ 1 / 2 := by nlinarith
      rw [coe_reassocLeftToRight_of_quarter_lt_of_le_half _ (by
          simpa [coe_reassocRightToLeft_of_half_lt_of_le_three_quarters
            t ht₁ ht₂] using hnot_left) (by
          simpa [coe_reassocRightToLeft_of_half_lt_of_le_three_quarters
            t ht₁ ht₂] using hmid),
        coe_reassocRightToLeft_of_half_lt_of_le_three_quarters t ht₁ ht₂]
      ring
    · have hnot_left : ¬ (2 * (t : ℝ) - 1 ≤ 1 / 4) := by
        intro h
        exact ht₂ (by nlinarith)
      have hnot_mid : ¬ (2 * (t : ℝ) - 1 ≤ 1 / 2) := by
        intro h
        exact ht₂ (by nlinarith)
      rw [coe_reassocLeftToRight_of_half_lt _ (by
          simpa [coe_reassocRightToLeft_of_three_quarters_lt
            t ht₁ ht₂] using hnot_left) (by
          simpa [coe_reassocRightToLeft_of_three_quarters_lt
            t ht₁ ht₂] using hnot_mid),
        coe_reassocRightToLeft_of_three_quarters_lt t ht₁ ht₂]
      ring

theorem reassocRightToLeft_reassocLeftToRight
    (t : unitInterval) :
    reassocRightToLeft (reassocLeftToRight t) = t := by
  ext
  by_cases ht₁ : (t : ℝ) ≤ 1 / 4
  · have hleft : 2 * (t : ℝ) ≤ 1 / 2 := by nlinarith
    rw [coe_reassocRightToLeft_of_le_half _ (by
        simpa [coe_reassocLeftToRight_of_le_quarter t ht₁] using hleft),
      coe_reassocLeftToRight_of_le_quarter t ht₁]
    ring
  · by_cases ht₂ : (t : ℝ) ≤ 1 / 2
    · have hnot_left : ¬ ((t : ℝ) + 1 / 4 ≤ 1 / 2) := by
        intro h
        exact ht₁ (by nlinarith)
      have hmid : ((t : ℝ) + 1 / 4) ≤ 3 / 4 := by nlinarith
      rw [coe_reassocRightToLeft_of_half_lt_of_le_three_quarters _ (by
          simpa [coe_reassocLeftToRight_of_quarter_lt_of_le_half
            t ht₁ ht₂] using hnot_left) (by
          simpa [coe_reassocLeftToRight_of_quarter_lt_of_le_half
            t ht₁ ht₂] using hmid),
        coe_reassocLeftToRight_of_quarter_lt_of_le_half t ht₁ ht₂]
      ring
    · have hnot_left : ¬ (((t : ℝ) + 1) / 2 ≤ 1 / 2) := by
        intro h
        exact ht₂ (by nlinarith)
      have hnot_mid : ¬ (((t : ℝ) + 1) / 2 ≤ 3 / 4) := by
        intro h
        exact ht₂ (by nlinarith)
      rw [coe_reassocRightToLeft_of_three_quarters_lt _ (by
          simpa [coe_reassocLeftToRight_of_half_lt
            t ht₁ ht₂] using hnot_left) (by
          simpa [coe_reassocLeftToRight_of_half_lt
            t ht₁ ht₂] using hnot_mid),
        coe_reassocLeftToRight_of_half_lt t ht₁ ht₂]
      ring

theorem reassocLeftToRight_mem_interval_of_rightToLeft_bounds
    {a b t : unitInterval}
    (hleft : reassocRightToLeft a ≤ t)
    (hright : t ≤ reassocRightToLeft b) :
    a ≤ reassocLeftToRight t ∧ reassocLeftToRight t ≤ b := by
  constructor
  · have hmono := reassocLeftToRight_mono hleft
    simpa [reassocLeftToRight_reassocRightToLeft] using hmono
  · have hmono := reassocLeftToRight_mono hright
    simpa [reassocLeftToRight_reassocRightToLeft] using hmono

theorem reassocRightToLeft_mem_interval_of_leftToRight_bounds
    {a b t : unitInterval}
    (hleft : reassocLeftToRight a ≤ t)
    (hright : t ≤ reassocLeftToRight b) :
    a ≤ reassocRightToLeft t ∧ reassocRightToLeft t ≤ b := by
  constructor
  · have hmono := reassocRightToLeft_mono hleft
    simpa [reassocRightToLeft_reassocLeftToRight] using hmono
  · have hmono := reassocRightToLeft_mono hright
    simpa [reassocRightToLeft_reassocLeftToRight] using hmono

end unitInterval

/-- On the first half of a concatenated path, `Path.trans` is the first path. -/
theorem path_trans_firstHalf_apply
    {X : Type*} [TopologicalSpace X]
    {x₀ x y : X} (p : Path x₀ x) (q : Path x y)
    (t : unitInterval) :
    (p.trans q) (unitInterval.firstHalf t) = p t := by
  rw [Path.trans_apply]
  rw [dif_pos (unitInterval.firstHalf_le_half t)]
  congr 1
  ext
  change 2 * ((t : ℝ) / 2) = (t : ℝ)
  ring

/-- On the second half of a concatenated path, `Path.trans` is the second path. -/
theorem path_trans_secondHalf_apply
    {X : Type*} [TopologicalSpace X]
    {x₀ x y : X} (p : Path x₀ x) (q : Path x y)
    (t : unitInterval) :
    (p.trans q) (unitInterval.secondHalf t) = q t := by
  rw [Path.trans_apply]
  by_cases ht0 : t = 0
  · subst t
    rw [dif_pos]
    · simp [unitInterval.secondHalf]
    · norm_num [unitInterval.secondHalf]
  · have htpos : (0 : ℝ) < t := by
      exact_mod_cast (unitInterval.pos_iff_ne_zero).2 ht0
    have hgt : (1 / 2 : ℝ) < unitInterval.secondHalf t := by
      change (1 / 2 : ℝ) < (1 + (t : ℝ)) / 2
      nlinarith
    rw [dif_neg (not_le_of_gt hgt)]
    congr 1
    ext
    change 2 * ((1 + (t : ℝ)) / 2) - 1 = (t : ℝ)
    ring

/--
A point of a concatenated path in the first half is the first path at the
doubled parameter.
-/
theorem path_trans_apply_of_le_half
    {X : Type*} [TopologicalSpace X]
    {x₀ x y : X} (p : Path x₀ x) (q : Path x y)
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    (p.trans q) t = p (unitInterval.doubleOfLeHalf t ht) := by
  rw [Path.trans_apply]
  rw [dif_pos ht]
  congr 1

/--
A point of a concatenated path in the second half is the second path at the
re-centered doubled parameter.
-/
theorem path_trans_apply_of_half_le
    {X : Type*} [TopologicalSpace X]
    {x₀ x y : X} (p : Path x₀ x) (q : Path x y)
    (t : unitInterval) (ht : (1 / 2 : ℝ) ≤ t) :
    (p.trans q) t = q (unitInterval.doubleSubOneOfHalfLe t ht) := by
  rw [Path.trans_apply]
  by_cases h : (t : ℝ) ≤ 1 / 2
  · have ht_eq : (t : ℝ) = 1 / 2 := le_antisymm h ht
    rw [dif_pos h]
    have hleft :
        (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨t.2.1, h⟩⟩ : unitInterval) = 1 := by
      ext
      simp [ht_eq]
    have hright :
        unitInterval.doubleSubOneOfHalfLe t ht = 0 := by
      ext
      simp [unitInterval.doubleSubOneOfHalfLe, ht_eq]
    rw [hleft, hright]
    simp
  · rw [dif_neg h]
    congr 1

/-- Taking a subpath of a subpath is the corresponding subpath of the original path. -/
theorem path_subpath_subpath
    {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y)
    (a b s t : unitInterval) :
    (γ.subpath a b).subpath s t =
      γ.subpath (Set.Icc.convexComb a b s)
        (Set.Icc.convexComb a b t) := by
  ext u
  simp only [Path.subpath]
  change
    γ (Set.Icc.convexComb a b (Set.Icc.convexComb s t u)) =
      γ (Set.Icc.convexComb (Set.Icc.convexComb a b s)
          (Set.Icc.convexComb a b t) u)
  apply congrArg γ
  ext
  simp [Set.Icc.convexComb]
  ring_nf

/--
On the first half of the split path, the left rescaling recovers the original
path value at `u`.
-/
theorem path_splitAt_firstHalf_rescaleLeft
    {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y)
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hu : u ≤ r) :
    ((γ.subpath 0 r).trans (γ.subpath r 1))
        (unitInterval.firstHalf
          (unitInterval.splitAtRescaleLeft r u hr0 hu)) =
      γ u := by
  rw [path_trans_firstHalf_apply]
  change γ (Set.Icc.convexComb 0 r
      (unitInterval.splitAtRescaleLeft r u hr0 hu)) = γ u
  rw [unitInterval.convexCombo_zero_right_splitAtRescaleLeft]

/--
On the second half of the split path, the right rescaling recovers the
original path value at `u`.
-/
theorem path_splitAt_secondHalf_rescaleRight
    {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y)
    (r u : unitInterval) (hr1 : (r : ℝ) < 1) (hu : r ≤ u) :
    ((γ.subpath 0 r).trans (γ.subpath r 1))
        (unitInterval.secondHalf
          (unitInterval.splitAtRescaleRight r u hr1 hu)) =
      γ u := by
  rw [path_trans_secondHalf_apply]
  change γ (Set.Icc.convexComb r 1
      (unitInterval.splitAtRescaleRight r u hr1 hu)) = γ u
  rw [unitInterval.convexCombo_left_one_splitAtRescaleRight]

/-- The combined split reparameterization recovers the original path value. -/
theorem path_splitAt_splitAtReparam
    {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y)
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    ((γ.subpath 0 r).trans (γ.subpath r 1))
        (unitInterval.splitAtReparam r u hr0 hr1) =
      γ u := by
  by_cases hu : u ≤ r
  · rw [unitInterval.splitAtReparam_of_le r u hr0 hr1 hu]
    exact path_splitAt_firstHalf_rescaleLeft γ r u hr0 hu
  · have hru : r ≤ u := le_of_lt (lt_of_not_ge hu)
    rw [unitInterval.splitAtReparam_of_ge r u hr0 hr1 hru]
    exact path_splitAt_secondHalf_rescaleRight γ r u hr1 hru

/--
Evaluating the split path and then inverting its parameter recovers the same
point of the original path.
-/
theorem path_splitAt_originalParameter
    {X : Type*} [TopologicalSpace X]
    {x y : X} (γ : Path x y)
    (r t : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    ((γ.subpath 0 r).trans (γ.subpath r 1)) t =
      γ (unitInterval.splitAtOriginalParameter r t hr0 hr1) := by
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [unitInterval.splitAtOriginalParameter_of_le_half r t hr0 hr1 ht,
      path_trans_apply_of_le_half (γ.subpath 0 r) (γ.subpath r 1) t ht]
    rfl
  · have ht' : (1 / 2 : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht)
    rw [unitInterval.splitAtOriginalParameter_of_half_le r t hr0 hr1 ht',
      path_trans_apply_of_half_le (γ.subpath 0 r) (γ.subpath r 1) t ht']
    rfl

end

end JJMath
