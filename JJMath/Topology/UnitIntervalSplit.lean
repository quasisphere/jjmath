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

/--
%%handwave
name:
  Coordinate of the ordered middle parameter
statement:
  If \(a\le b\le c\) in \([0,1]\), the parameter locating \(b\) on the affine
  segment from \(a\) to \(c\) is \((b-a)/(c-a)\).
proof:
  This is the defining coordinate of the ordered middle parameter.
-/
@[simp]
theorem coe_orderedMiddleParameter
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) :
    (orderedMiddleParameter a b c hab hbc : ℝ) =
      ((b : ℝ) - (a : ℝ)) / ((c : ℝ) - (a : ℝ)) :=
  rfl

/--
%%handwave
name:
  Affine recovery of an ordered middle point
statement:
  If \(a\le b\le c\) and \(m=(b-a)/(c-a)\), then
  \(b=(1-m)a+mc\), with the degenerate case \(a=c\) included.
proof:
  Apply the standard convex-combination representation of a point between two
  ordered endpoints.
-/
theorem orderedMiddleParameter_spec
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) :
    b = Set.Icc.convexComb a c
      (orderedMiddleParameter a b c hab hbc) :=
  Set.Icc.eq_convexComb hab hbc

/--
%%handwave
name:
  Positivity of the ordered middle parameter
statement:
  If \(a<b\le c\), then \(m=(b-a)/(c-a)\) satisfies \(m>0\).
proof:
  Both \(b-a\) and \(c-a\) are positive, so their quotient is positive.
-/
theorem orderedMiddleParameter_pos_of_lt
    (a b c : unitInterval) (hab : a < b) (hbc : b ≤ c) :
    (0 : ℝ) < orderedMiddleParameter a b c hab.le hbc := by
  change (0 : ℝ) < ((b : ℝ) - (a : ℝ)) / ((c : ℝ) - (a : ℝ))
  apply div_pos
  · linarith [show (a : ℝ) < b from hab]
  · linarith [show (a : ℝ) < b from hab, show (b : ℝ) ≤ c from hbc]

/--
%%handwave
name:
  Strict upper bound for the ordered middle parameter
statement:
  If \(a\le b<c\), then \(m=(b-a)/(c-a)\) satisfies \(m<1\).
proof:
  The denominator is positive and \(b-a<c-a\); division by \(c-a\) preserves
  the strict inequality.
-/
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

/--
%%handwave
name:
  Formula for the first-half embedding
statement:
  For \(t\in[0,1]\), the first-half embedding has real coordinate \(t/2\).
proof:
  This is its defining coordinate.
-/
@[simp]
theorem coe_firstHalf (t : unitInterval) :
    (firstHalf t : ℝ) = (t : ℝ) / 2 :=
  rfl

/--
%%handwave
name:
  Formula for the second-half embedding
statement:
  For \(t\in[0,1]\), the second-half embedding has real coordinate
  \((1+t)/2\).
proof:
  This is its defining coordinate.
-/
@[simp]
theorem coe_secondHalf (t : unitInterval) :
    (secondHalf t : ℝ) = (1 + (t : ℝ)) / 2 :=
  rfl

/--
%%handwave
name:
  First-half embedding at zero
statement:
  The first-half embedding sends \(0\) to \(0\).
proof:
  Substitute \(t=0\) into \(t/2\).
-/
@[simp]
theorem firstHalf_zero : firstHalf 0 = 0 := by
  ext
  norm_num [firstHalf]

/--
%%handwave
name:
  First-half embedding at one
statement:
  The first-half embedding sends \(1\) to \(1/2\).
proof:
  Substitute \(t=1\) into \(t/2\).
-/
@[simp]
theorem firstHalf_one : firstHalf 1 = (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval) := by
  ext
  norm_num [firstHalf]

/--
%%handwave
name:
  Second-half embedding at zero
statement:
  The second-half embedding sends \(0\) to \(1/2\).
proof:
  Substitute \(t=0\) into \((1+t)/2\).
-/
@[simp]
theorem secondHalf_zero : secondHalf 0 = (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval) := by
  ext
  norm_num [secondHalf]

/--
%%handwave
name:
  Second-half embedding at one
statement:
  The second-half embedding sends \(1\) to \(1\).
proof:
  Substitute \(t=1\) into \((1+t)/2\).
-/
@[simp]
theorem secondHalf_one : secondHalf 1 = 1 := by
  ext
  norm_num [secondHalf]

/--
%%handwave
name:
  Range of the first-half embedding
statement:
  For every \(t\in[0,1]\), one has \(t/2\le 1/2\).
proof:
  Divide the bound \(t\le1\) by \(2\).
-/
theorem firstHalf_le_half (t : unitInterval) :
    (firstHalf t : ℝ) ≤ 1 / 2 := by
  change (t : ℝ) / 2 ≤ 1 / 2
  nlinarith [unitInterval.le_one t]

/--
%%handwave
name:
  Range of the second-half embedding
statement:
  For every \(t\in[0,1]\), one has \(1/2\le(1+t)/2\).
proof:
  This follows from \(t\ge0\).
-/
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

/--
%%handwave
name:
  Formula for doubling a first-half parameter
statement:
  If \(t\in[0,1/2]\), its rescaling to \([0,1]\) has real coordinate \(2t\).
proof:
  This is the defining coordinate of the rescaling.
-/
@[simp]
theorem coe_doubleOfLeHalf (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    (doubleOfLeHalf t ht : ℝ) = 2 * (t : ℝ) :=
  rfl

/--
%%handwave
name:
  Formula for recentering a second-half parameter
statement:
  If \(t\in[1/2,1]\), its rescaling to \([0,1]\) has real coordinate \(2t-1\).
proof:
  This is the defining coordinate of the rescaling.
-/
@[simp]
theorem coe_doubleSubOneOfHalfLe
    (t : unitInterval) (ht : (1 / 2 : ℝ) ≤ t) :
    (doubleSubOneOfHalfLe t ht : ℝ) = 2 * (t : ℝ) - 1 :=
  rfl

/--
%%handwave
name:
  Doubling inverts the first-half embedding
statement:
  For every \(t\in[0,1]\), doubling the embedded parameter \(t/2\) recovers
  \(t\).
proof:
  The coordinate identity is \(2(t/2)=t\).
-/
@[simp]
theorem doubleOfLeHalf_firstHalf (t : unitInterval)
    (ht : (unitInterval.firstHalf t : ℝ) ≤ 1 / 2 := firstHalf_le_half t) :
    doubleOfLeHalf (firstHalf t) ht = t := by
  ext
  change 2 * ((t : ℝ) / 2) = (t : ℝ)
  ring

/--
%%handwave
name:
  The first-half embedding inverts doubling
statement:
  For \(t\in[0,1/2]\), embedding the doubled parameter \(2t\) into the first
  half recovers \(t\).
proof:
  The coordinate identity is \((2t)/2=t\).
-/
@[simp]
theorem firstHalf_doubleOfLeHalf (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    firstHalf (doubleOfLeHalf t ht) = t := by
  ext
  change (2 * (t : ℝ)) / 2 = (t : ℝ)
  ring

/--
%%handwave
name:
  Recentering inverts the second-half embedding
statement:
  For every \(t\in[0,1]\), recentering \((1+t)/2\) by \(s\mapsto2s-1\)
  recovers \(t\).
proof:
  Expand \(2(1+t)/2-1=t\).
-/
@[simp]
theorem doubleSubOneOfHalfLe_secondHalf (t : unitInterval)
    (ht : (1 / 2 : ℝ) ≤ unitInterval.secondHalf t := half_le_secondHalf t) :
    doubleSubOneOfHalfLe (secondHalf t) ht = t := by
  ext
  change 2 * ((1 + (t : ℝ)) / 2) - 1 = (t : ℝ)
  ring

/--
%%handwave
name:
  The second-half embedding inverts recentering
statement:
  For \(t\in[1/2,1]\), embedding \(2t-1\) into the second half recovers \(t\).
proof:
  Expand \((1+(2t-1))/2=t\).
-/
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

/--
%%handwave
name:
  Formula for left-subinterval rescaling
statement:
  If \(0<r\le1\) and \(0\le u\le r\), rescaling \([0,r]\) to \([0,1]\)
  sends \(u\) to \(u/r\).
proof:
  This is the defining coordinate of the left rescaling.
-/
@[simp]
theorem coe_splitAtRescaleLeft
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hu : u ≤ r) :
    (splitAtRescaleLeft r u hr0 hu : ℝ) = (u : ℝ) / r :=
  rfl

/--
%%handwave
name:
  Left-subinterval rescaling recovers the original parameter
statement:
  If \(0<r\) and \(u\le r\), then the affine interpolation from \(0\) to
  \(r\) at parameter \(u/r\) equals \(u\).
proof:
  The interpolation is \(0+(u/r)r=u\), since \(r\ne0\).
-/
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

/--
%%handwave
name:
  Formula for right-subinterval rescaling
statement:
  If \(r<1\) and \(r\le u\le1\), rescaling \([r,1]\) to \([0,1]\)
  sends \(u\) to \((u-r)/(1-r)\).
proof:
  This is the defining coordinate of the right rescaling.
-/
@[simp]
theorem coe_splitAtRescaleRight
    (r u : unitInterval) (hr1 : (r : ℝ) < 1) (hu : r ≤ u) :
    (splitAtRescaleRight r u hr1 hu : ℝ) =
      ((u : ℝ) - r) / (1 - r) :=
  rfl

/--
%%handwave
name:
  Right-subinterval rescaling recovers the original parameter
statement:
  If \(r<1\) and \(r\le u\), then the affine interpolation from \(r\) to
  \(1\) at parameter \((u-r)/(1-r)\) equals \(u\).
proof:
  Expand the interpolation and cancel the nonzero factor \(1-r\).
-/
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

/--
%%handwave
name:
  Split reparametrization on the left subinterval
statement:
  For an interior breakpoint \(r\), if \(u\le r\), then the split-path
  parameter of \(u\) is \(\frac12(u/r)\).
proof:
  The left branch of the piecewise definition applies.
-/
theorem splitAtReparam_of_le
    (r u : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (hu : u ≤ r) :
    splitAtReparam r u hr0 hr1 =
      firstHalf (splitAtRescaleLeft r u hr0 hu) := by
  simp [splitAtReparam, hu]

/--
%%handwave
name:
  Split reparametrization on the right subinterval
statement:
  For an interior breakpoint \(r\), if \(r\le u\), then the split-path
  parameter of \(u\) is
  \(\frac12\bigl(1+(u-r)/(1-r)\bigr)\).
proof:
  Away from \(u=r\) this is the right branch of the definition.  At \(u=r\),
  both branch formulas equal \(1/2\).
-/
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

/--
%%handwave
name:
  Monotonicity of the split reparametrization
statement:
  For fixed \(0<r<1\), the map sending an original parameter \(u\) to its
  split-path parameter is monotone on \([0,1]\).
proof:
  On each side of \(r\) the map is affine with positive slope.  Across the
  breakpoint, the left values are at most \(1/2\) and the right values are at
  least \(1/2\).
-/
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

/--
%%handwave
name:
  Split reparametrization at zero
statement:
  For every interior breakpoint \(r\), the split reparametrization sends
  \(0\) to \(0\).
proof:
  Use the left formula and substitute \(u=0\).
-/
@[simp]
theorem splitAtReparam_zero
    (r : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1) :
    splitAtReparam r 0 hr0 hr1 = 0 := by
  rw [splitAtReparam_of_le r 0 hr0 hr1
    (show (0 : unitInterval) ≤ r from hr0.le)]
  ext
  simp [firstHalf, splitAtRescaleLeft]

/--
%%handwave
name:
  Split reparametrization at one
statement:
  For every interior breakpoint \(r\), the split reparametrization sends
  \(1\) to \(1\).
proof:
  Use the right formula and simplify \((1-r)/(1-r)=1\).
-/
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

/--
%%handwave
name:
  Original parameter on the first half of a split path
statement:
  If \(t\le1/2\), the original parameter corresponding to the split-path
  parameter \(t\) is the affine interpolation from \(0\) to \(r\) at \(2t\),
  equivalently \(2rt\).
proof:
  The first branch of the inverse reparametrization applies.
-/
theorem splitAtOriginalParameter_of_le_half
    (r t : unitInterval) (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (ht : (t : ℝ) ≤ 1 / 2) :
    splitAtOriginalParameter r t hr0 hr1 =
      Set.Icc.convexComb 0 r (doubleOfLeHalf t ht) := by
  unfold splitAtOriginalParameter
  rw [dif_pos ht]

/--
%%handwave
name:
  Original parameter on the second half of a split path
statement:
  If \(1/2\le t\), the original parameter corresponding to \(t\) is the affine
  interpolation from \(r\) to \(1\) at \(2t-1\).
proof:
  Above \(1/2\) this is the second branch by definition; at \(t=1/2\), both
  affine formulas equal \(r\).
-/
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

/--
%%handwave
name:
  Monotonicity of the original-parameter map
statement:
  For fixed \(0<r<1\), the map from a split-path parameter \(t\) back to the
  original parameter is monotone on \([0,1]\).
proof:
  Each affine branch has positive slope.  Across \(t=1/2\), the first branch
  is at most \(r\) and the second branch is at least \(r\).
-/
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

/--
%%handwave
name:
  The original-parameter map is a left inverse
statement:
  For \(0<r<1\) and \(u\in[0,1]\), converting \(u\) to a split-path parameter
  and back recovers \(u\).
proof:
  Split at \(u\le r\).  On each branch, half-interval rescaling is inverted
  and the corresponding affine subinterval interpolation recovers \(u\).
-/
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

/--
%%handwave
name:
  The split reparametrization is a left inverse
statement:
  For \(0<r<1\) and \(t\in[0,1]\), converting \(t\) to its original parameter
  and then back to a split-path parameter recovers \(t\).
proof:
  Split at \(t\le1/2\), substitute the appropriate affine branch, and cancel
  \(r\) or \(1-r\), both of which are nonzero.
-/
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
%%handwave
name:
  Pulling split-parameter bounds back to original parameters
statement:
  Let \(F\) be the split reparametrization for \(0<r<1\), with inverse
  \(G\).  If \(F(a)\le t\le F(b)\), then \(a\le G(t)\le b\).
proof:
  Apply monotonicity of \(G\) to both inequalities and use
  \(G(F(u))=u\).
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
%%handwave
name:
  Pulling original-parameter bounds back to split parameters
statement:
  Let \(G\) send split-path parameters to original parameters for
  \(0<r<1\), with inverse \(F\).  If \(G(a)\le t\le G(b)\), then
  \(a\le F(t)\le b\).
proof:
  Apply monotonicity of \(F\) to both inequalities and use
  \(F(G(u))=u\).
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

/--
%%handwave
name:
  Right-associated to left-associated reparametrization at zero
statement:
  The reparametrization from \(p*(q*r)\) to \((p*q)*r\) fixes \(0\).
proof:
  Substitute \(t=0\) into its first affine branch.
-/
@[simp]
theorem reassocRightToLeft_zero :
    reassocRightToLeft 0 = 0 := by
  ext
  simp [reassocRightToLeft]

/--
%%handwave
name:
  Right-associated to left-associated reparametrization at one
statement:
  The reparametrization from \(p*(q*r)\) to \((p*q)*r\) fixes \(1\).
proof:
  Substitute \(t=1\) into its last affine branch.
-/
@[simp]
theorem reassocRightToLeft_one :
    reassocRightToLeft 1 = 1 := by
  ext
  simp [reassocRightToLeft]
  norm_num

/--
%%handwave
name:
  Left-associated to right-associated reparametrization at zero
statement:
  The reparametrization from \((p*q)*r\) to \(p*(q*r)\) fixes \(0\).
proof:
  Substitute \(t=0\) into its first affine branch.
-/
@[simp]
theorem reassocLeftToRight_zero :
    reassocLeftToRight 0 = 0 := by
  ext
  simp [reassocLeftToRight]

/--
%%handwave
name:
  Left-associated to right-associated reparametrization at one
statement:
  The reparametrization from \((p*q)*r\) to \(p*(q*r)\) fixes \(1\).
proof:
  Substitute \(t=1\) into its last affine branch.
-/
@[simp]
theorem reassocLeftToRight_one :
    reassocLeftToRight 1 = 1 := by
  ext
  simp [reassocLeftToRight]
  norm_num

/--
%%handwave
name:
  First branch of right-to-left reassociation
statement:
  For \(0\le t\le1/2\), the right-to-left reassociation parameter is \(t/2\).
proof:
  The first branch of the piecewise definition applies.
-/
theorem coe_reassocRightToLeft_of_le_half
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    (reassocRightToLeft t : ℝ) = (t : ℝ) / 2 := by
  unfold reassocRightToLeft
  rw [dif_pos ht]

/--
%%handwave
name:
  Middle branch of right-to-left reassociation
statement:
  For \(1/2<t\le3/4\), the right-to-left reassociation parameter is
  \(t-1/4\).
proof:
  The middle branch of the piecewise definition applies.
-/
theorem coe_reassocRightToLeft_of_half_lt_of_le_three_quarters
    (t : unitInterval) (ht₁ : ¬ (t : ℝ) ≤ 1 / 2)
    (ht₂ : (t : ℝ) ≤ 3 / 4) :
    (reassocRightToLeft t : ℝ) = (t : ℝ) - 1 / 4 := by
  unfold reassocRightToLeft
  rw [dif_neg ht₁, dif_pos ht₂]

/--
%%handwave
name:
  Last branch of right-to-left reassociation
statement:
  For \(3/4<t\le1\), the right-to-left reassociation parameter is \(2t-1\).
proof:
  The final branch of the piecewise definition applies.
-/
theorem coe_reassocRightToLeft_of_three_quarters_lt
    (t : unitInterval) (ht₁ : ¬ (t : ℝ) ≤ 1 / 2)
    (ht₂ : ¬ (t : ℝ) ≤ 3 / 4) :
    (reassocRightToLeft t : ℝ) = 2 * (t : ℝ) - 1 := by
  unfold reassocRightToLeft
  rw [dif_neg ht₁, dif_neg ht₂]

/--
%%handwave
name:
  First branch of left-to-right reassociation
statement:
  For \(0\le t\le1/4\), the left-to-right reassociation parameter is \(2t\).
proof:
  The first branch of the piecewise definition applies.
-/
theorem coe_reassocLeftToRight_of_le_quarter
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 4) :
    (reassocLeftToRight t : ℝ) = 2 * (t : ℝ) := by
  unfold reassocLeftToRight
  rw [dif_pos ht]

/--
%%handwave
name:
  Middle branch of left-to-right reassociation
statement:
  For \(1/4<t\le1/2\), the left-to-right reassociation parameter is
  \(t+1/4\).
proof:
  The middle branch of the piecewise definition applies.
-/
theorem coe_reassocLeftToRight_of_quarter_lt_of_le_half
    (t : unitInterval) (ht₁ : ¬ (t : ℝ) ≤ 1 / 4)
    (ht₂ : (t : ℝ) ≤ 1 / 2) :
    (reassocLeftToRight t : ℝ) = (t : ℝ) + 1 / 4 := by
  unfold reassocLeftToRight
  rw [dif_neg ht₁, dif_pos ht₂]

/--
%%handwave
name:
  Last branch of left-to-right reassociation
statement:
  For \(1/2<t\le1\), the left-to-right reassociation parameter is
  \((t+1)/2\).
proof:
  The final branch of the piecewise definition applies.
-/
theorem coe_reassocLeftToRight_of_half_lt
    (t : unitInterval) (ht₁ : ¬ (t : ℝ) ≤ 1 / 4)
    (ht₂ : ¬ (t : ℝ) ≤ 1 / 2) :
    (reassocLeftToRight t : ℝ) = ((t : ℝ) + 1) / 2 := by
  unfold reassocLeftToRight
  rw [dif_neg ht₁, dif_neg ht₂]

/--
%%handwave
name:
  Monotonicity of right-to-left reassociation
statement:
  The piecewise affine map
  \(t/2,\ t-1/4,\ 2t-1\) on the intervals cut at \(1/2\) and \(3/4\)
  is monotone on \([0,1]\).
proof:
  Compare the affine formulas in each possible pair of branches.  Every
  branch has positive slope and adjacent formulas agree at their breakpoint.
-/
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

/--
%%handwave
name:
  Monotonicity of left-to-right reassociation
statement:
  The piecewise affine map
  \(2t,\ t+1/4,\ (t+1)/2\) on the intervals cut at \(1/4\) and \(1/2\)
  is monotone on \([0,1]\).
proof:
  Compare the affine formulas branch by branch.  Their slopes are positive
  and adjacent formulas meet at the breakpoints.
-/
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

/--
%%handwave
name:
  Left-to-right reassociation inverts right-to-left reassociation
statement:
  For every \(t\in[0,1]\), applying the right-to-left reassociation and then
  the left-to-right reassociation recovers \(t\).
proof:
  Split at \(t=1/2\) and \(t=3/4\).  The image lands respectively in the
  intervals cut at \(1/4\) and \(1/2\), where the paired affine formulas
  compose to the identity.
-/
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

/--
%%handwave
name:
  Right-to-left reassociation inverts left-to-right reassociation
statement:
  For every \(t\in[0,1]\), applying the left-to-right reassociation and then
  the right-to-left reassociation recovers \(t\).
proof:
  Split at \(t=1/4\) and \(t=1/2\).  On each resulting interval, substitute
  the matching affine branch formulas and simplify.
-/
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

/--
%%handwave
name:
  Transporting right-to-left reassociation bounds through the inverse
statement:
  If \(R(a)\le t\le R(b)\), where \(R\) is right-to-left reassociation and
  \(L\) its inverse, then \(a\le L(t)\le b\).
proof:
  Apply monotonicity of \(L\) to both bounds and use \(L(R(u))=u\).
-/
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

/--
%%handwave
name:
  Transporting left-to-right reassociation bounds through the inverse
statement:
  If \(L(a)\le t\le L(b)\), where \(L\) is left-to-right reassociation and
  \(R\) its inverse, then \(a\le R(t)\le b\).
proof:
  Apply monotonicity of \(R\) to both bounds and use \(R(L(u))=u\).
-/
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

/--
%%handwave
name:
  A concatenated path on its first half
statement:
  For composable paths \(p,q\) and \(t\in[0,1]\),
  \((p*q)(t/2)=p(t)\).
proof:
  The parameter \(t/2\) lies in the first half, where path concatenation
  evaluates \(p\) at the doubled parameter \(2(t/2)=t\).
-/
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

/--
%%handwave
name:
  A concatenated path on its second half
statement:
  For composable paths \(p,q\) and \(t\in[0,1]\),
  \((p*q)((1+t)/2)=q(t)\).
proof:
  If \(t>0\), the parameter is in the second half and recentering gives
  \(2(1+t)/2-1=t\).  At \(t=0\), the common endpoint identifies the two
  branch values.
-/
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
%%handwave
name:
  Evaluation of a concatenated path before the midpoint
statement:
  For composable paths \(p,q\), if \(t\le1/2\), then
  \((p*q)(t)=p(2t)\).
proof:
  Select the first branch of the definition of path concatenation.
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
%%handwave
name:
  Evaluation of a concatenated path after the midpoint
statement:
  For composable paths \(p,q\), if \(1/2\le t\), then
  \((p*q)(t)=q(2t-1)\).
proof:
  Above the midpoint this is the second branch of concatenation.  At the
  midpoint, the terminal value of \(p\) and initial value of \(q\) agree.
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

/--
%%handwave
name:
  Subpath of a subpath
statement:
  For a path \(\gamma\) and \(a,b,s,t\in[0,1]\),
  \[
    (\gamma|_{[a,b]})|_{[s,t]}
    =\gamma|_{[(1-s)a+sb,\,(1-t)a+tb]}.
  \]
proof:
  Evaluate both paths at \(u\) and use associativity of affine interpolation:
  interpolating from \(a\) to \(b\) at the interpolation from \(s\) to \(t\)
  gives the same affine polynomial as interpolating between the two displayed
  endpoints at \(u\).
-/
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
%%handwave
name:
  Left half of a path split at an interior parameter
statement:
  Let \(0<r<1\) and \(u\le r\).  Concatenate the subpaths of \(\gamma\) from
  \(0\) to \(r\) and from \(r\) to \(1\).  At split-path parameter
  \(\frac12(u/r)\), the resulting path has value \(\gamma(u)\).
proof:
  First-half evaluation reduces to the left subpath at parameter \(u/r\);
  affine interpolation from \(0\) to \(r\) at \(u/r\) equals \(u\).
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
%%handwave
name:
  Right half of a path split at an interior parameter
statement:
  Let \(0<r<1\) and \(r\le u\).  Concatenate the subpaths of \(\gamma\) from
  \(0\) to \(r\) and from \(r\) to \(1\).  At split-path parameter
  \(\frac12(1+(u-r)/(1-r))\), the resulting path has value \(\gamma(u)\).
proof:
  Second-half evaluation reduces to the right subpath at parameter
  \((u-r)/(1-r)\), whose affine interpolation between \(r\) and \(1\) is \(u\).
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

/--
%%handwave
name:
  Reparametrizing a split path recovers the original path
statement:
  Let \(0<r<1\).  If the two subpaths of \(\gamma\) cut at \(r\) are
  concatenated and evaluated at the split reparametrization of \(u\), the
  result is \(\gamma(u)\).
proof:
  Split into \(u\le r\) and \(r\le u\), then apply the corresponding
  left- or right-half recovery formula.
-/
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
%%handwave
name:
  A split path as an inverse reparametrization of the original path
statement:
  Let \(0<r<1\).  The concatenation of the subpaths of \(\gamma\) cut at \(r\)
  satisfies
  \[
    (\gamma|_{[0,r]}*\gamma|_{[r,1]})(t)=\gamma(G_r(t)),
  \]
  where \(G_r\) sends split-path parameters back to original parameters.
proof:
  For \(t\le1/2\), use first-half evaluation and the affine formula on
  \([0,r]\).  For \(t\ge1/2\), use second-half evaluation and the affine
  formula on \([r,1]\).
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
