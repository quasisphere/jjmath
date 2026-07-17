import JJMath.Hyperbolic.Schwarzian.Wirtinger

/-!
# Frobenius solution machinery for the Schwarzian equation

This module contains the symbolic Schwarzian expression, the linear ODE
reduction, and the Frobenius/series packages used to solve it locally.
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

def schwarzianExpression (f' f'' f''' : ℂ → ℂ) (z : ℂ) : ℂ :=
  f''' z / f' z - (3 / 2 : ℂ) * (f'' z / f' z) ^ 2

/--
Local symbolic data for the reduction of the Schwarzian equation
`{f,z} = q` to the second-order linear ODE

`y'' + (1 / 2) q y = 0`.

The intended developing coordinate is `localMap = numerator / denominator`.
The fields record the quotient derivative identities for this ratio.  The
theorem below proves the remaining algebraic fact: these identities and the
linear ODE force the Schwarzian of `localMap` to be `q`.
-/
structure SchwarzianLinearODEFrame (q : ℂ → ℂ) (U : Set ℂ) where
  /-- One solution of the linear ODE, used as numerator. -/
  numerator : ℂ → ℂ
  /-- A second solution of the linear ODE, used as denominator. -/
  denominator : ℂ → ℂ
  /-- The derivative of the denominator solution. -/
  denominatorDeriv : ℂ → ℂ
  /-- The second derivative of the denominator solution. -/
  denominatorSecondDeriv : ℂ → ℂ
  /-- The Wronskian of the two solutions. -/
  wronskian : ℂ → ℂ
  /-- The ratio `numerator / denominator`. -/
  localMap : ℂ → ℂ
  /-- Symbolic first derivative of `localMap`. -/
  localMapDeriv : ℂ → ℂ
  /-- Symbolic second derivative of `localMap`. -/
  localMapSecondDeriv : ℂ → ℂ
  /-- Symbolic third derivative of `localMap`. -/
  localMapThirdDeriv : ℂ → ℂ
  /-- The denominator solution does not vanish on the local domain. -/
  denominator_ne_zero : ∀ z, z ∈ U → denominator z ≠ 0
  /-- The Wronskian is nonzero, so the ratio is locally nonconstant. -/
  wronskian_ne_zero : ∀ z, z ∈ U → wronskian z ≠ 0
  /-- The local map is the ratio of the two linear ODE solutions. -/
  localMap_eq_ratio : ∀ z, z ∈ U → localMap z = numerator z / denominator z
  /-- The denominator solves `y'' + (1 / 2) q y = 0`. -/
  denominator_solves_ode : ∀ z, z ∈ U →
    denominatorSecondDeriv z = -((1 / 2 : ℂ) * q z * denominator z)
  /-- Quotient rule for the first derivative of the solution ratio. -/
  localMapDeriv_eq : ∀ z, z ∈ U →
    localMapDeriv z = wronskian z / denominator z ^ 2
  /-- Quotient rule for the second derivative of the solution ratio. -/
  localMapSecondDeriv_eq : ∀ z, z ∈ U →
    localMapSecondDeriv z =
      -2 * wronskian z * denominatorDeriv z / denominator z ^ 3
  /-- Quotient rule for the third derivative of the solution ratio. -/
  localMapThirdDeriv_eq : ∀ z, z ∈ U →
    localMapThirdDeriv z =
      -2 * wronskian z * denominatorSecondDeriv z / denominator z ^ 3 +
        6 * wronskian z * denominatorDeriv z ^ 2 / denominator z ^ 4

namespace SchwarzianLinearODEFrame

/-- The Schwarzian of the ratio of two linear ODE solutions is the coefficient `q`. -/
theorem schwarzianExpression_eq_coefficient
    {q : ℂ → ℂ} {U : Set ℂ} (F : SchwarzianLinearODEFrame q U) :
    ∀ z, z ∈ U →
      schwarzianExpression F.localMapDeriv F.localMapSecondDeriv
        F.localMapThirdDeriv z = q z := by
  intro z hz
  have hy : F.denominator z ≠ 0 := F.denominator_ne_zero z hz
  have hW : F.wronskian z ≠ 0 := F.wronskian_ne_zero z hz
  rw [schwarzianExpression, F.localMapThirdDeriv_eq z hz,
    F.localMapSecondDeriv_eq z hz, F.localMapDeriv_eq z hz,
    F.denominator_solves_ode z hz]
  field_simp [hy, hW]
  ring

/-- The first derivative of the developing ratio is nonzero on the frame domain. -/
theorem localMapDeriv_ne_zero
    {q : ℂ → ℂ} {U : Set ℂ} (F : SchwarzianLinearODEFrame q U) :
    ∀ z, z ∈ U → F.localMapDeriv z ≠ 0 := by
  intro z hz
  rw [F.localMapDeriv_eq z hz]
  exact div_ne_zero (F.wronskian_ne_zero z hz) (pow_ne_zero 2 (F.denominator_ne_zero z hz))

end SchwarzianLinearODEFrame

/--
A symbolic pair of local solutions of the second-order linear equation
`y'' + (1 / 2) q y = 0`.

This is closer to the usual ODE existence theorem than
`SchwarzianLinearODEFrame`: it stores the two solution functions and their first
and second derivatives.  Its Wronskian is defined from those first derivatives,
and the quotient-derivative expressions are then chosen canonically.
-/
structure SchwarzianLinearODESolutionPair (q : ℂ → ℂ) (U : Set ℂ) where
  /-- The numerator solution. -/
  numerator : ℂ → ℂ
  /-- The denominator solution. -/
  denominator : ℂ → ℂ
  /-- Symbolic derivative of the numerator solution. -/
  numeratorDeriv : ℂ → ℂ
  /-- Symbolic derivative of the denominator solution. -/
  denominatorDeriv : ℂ → ℂ
  /-- Symbolic second derivative of the numerator solution. -/
  numeratorSecondDeriv : ℂ → ℂ
  /-- Symbolic second derivative of the denominator solution. -/
  denominatorSecondDeriv : ℂ → ℂ
  /-- The denominator is nonzero on the domain where the quotient is used. -/
  denominator_ne_zero : ∀ z, z ∈ U → denominator z ≠ 0
  /-- The Wronskian is nonzero on the local domain. -/
  wronskian_ne_zero : ∀ z, z ∈ U →
    numeratorDeriv z * denominator z - numerator z * denominatorDeriv z ≠ 0
  /-- The numerator solves `y'' + (1 / 2) q y = 0`. -/
  numerator_solves_ode : ∀ z, z ∈ U →
    numeratorSecondDeriv z = -((1 / 2 : ℂ) * q z * numerator z)
  /-- The denominator solves `y'' + (1 / 2) q y = 0`. -/
  denominator_solves_ode : ∀ z, z ∈ U →
    denominatorSecondDeriv z = -((1 / 2 : ℂ) * q z * denominator z)

namespace SchwarzianLinearODESolutionPair

/-- The Wronskian `y_1' y_0 - y_1 y_0'` of a solution pair. -/
def wronskian {q : ℂ → ℂ} {U : Set ℂ}
    (P : SchwarzianLinearODESolutionPair q U) : ℂ → ℂ :=
  fun z ↦ P.numeratorDeriv z * P.denominator z - P.numerator z * P.denominatorDeriv z

/-- The quotient map `y_1 / y_0` associated to a solution pair. -/
def localMap {q : ℂ → ℂ} {U : Set ℂ}
    (P : SchwarzianLinearODESolutionPair q U) : ℂ → ℂ :=
  fun z ↦ P.numerator z / P.denominator z

/-- The canonical first quotient derivative expression. -/
def localMapDeriv {q : ℂ → ℂ} {U : Set ℂ}
    (P : SchwarzianLinearODESolutionPair q U) : ℂ → ℂ :=
  fun z ↦ P.wronskian z / P.denominator z ^ 2

/-- The canonical second quotient derivative expression. -/
def localMapSecondDeriv {q : ℂ → ℂ} {U : Set ℂ}
    (P : SchwarzianLinearODESolutionPair q U) : ℂ → ℂ :=
  fun z ↦ -2 * P.wronskian z * P.denominatorDeriv z / P.denominator z ^ 3

/-- The canonical third quotient derivative expression. -/
def localMapThirdDeriv {q : ℂ → ℂ} {U : Set ℂ}
    (P : SchwarzianLinearODESolutionPair q U) : ℂ → ℂ :=
  fun z ↦
    -2 * P.wronskian z * P.denominatorSecondDeriv z / P.denominator z ^ 3 +
      6 * P.wronskian z * P.denominatorDeriv z ^ 2 / P.denominator z ^ 4

/--
Turn a pair of local solutions into the Schwarzian ODE frame used by the
projective-coordinate construction.
-/
def toSchwarzianLinearODEFrame {q : ℂ → ℂ} {U : Set ℂ}
    (P : SchwarzianLinearODESolutionPair q U) :
    SchwarzianLinearODEFrame q U where
  numerator := P.numerator
  denominator := P.denominator
  denominatorDeriv := P.denominatorDeriv
  denominatorSecondDeriv := P.denominatorSecondDeriv
  wronskian := P.wronskian
  localMap := P.localMap
  localMapDeriv := P.localMapDeriv
  localMapSecondDeriv := P.localMapSecondDeriv
  localMapThirdDeriv := P.localMapThirdDeriv
  denominator_ne_zero := P.denominator_ne_zero
  wronskian_ne_zero := P.wronskian_ne_zero
  localMap_eq_ratio := by
    intro z hz
    rfl
  denominator_solves_ode := P.denominator_solves_ode
  localMapDeriv_eq := by
    intro z hz
    rfl
  localMapSecondDeriv_eq := by
    intro z hz
    rfl
  localMapThirdDeriv_eq := by
    intro z hz
    rfl

/--
%%handwave
name:
  Schwarzian of a ratio of ODE solutions
statement:
  Let $Q$ be a complex function on $V$, and let $y_0,y_1$ solve
  $y''+\tfrac12Qy=0$. Wherever $y_0$ and the Wronskian
  $W=y_1'y_0-y_1y_0'$ are nonzero, the quotient $f=y_1/y_0$ has Schwarzian
  derivative $\{f,z\}=Q$.
proof:
  The quotient rule gives $f'=W/y_0^2$,
  $f''=-2Wy_0'/y_0^3$, and
  $f'''=-2Wy_0''/y_0^3+6W(y_0')^2/y_0^4$. Substitution into
  $\{f,z\}=f'''/f'-\tfrac32(f''/f')^2$ leaves
  $-2y_0''/y_0=Q$.
tags:
  milestone
-/
theorem schwarzianExpression_eq_coefficient
    {q : ℂ → ℂ} {U : Set ℂ} (P : SchwarzianLinearODESolutionPair q U) :
    ∀ z, z ∈ U →
      schwarzianExpression P.localMapDeriv P.localMapSecondDeriv
        P.localMapThirdDeriv z = q z :=
  P.toSchwarzianLinearODEFrame.schwarzianExpression_eq_coefficient

/--
For two solutions of the same linear Schwarzian ODE, the Wronskian has zero
derivative.
-/
theorem wronskian_hasDerivAt_zero
    {q : ℂ → ℂ} {U : Set ℂ} (P : SchwarzianLinearODESolutionPair q U)
    {z : ℂ} (hz : z ∈ U)
    (hnum : HasDerivAt P.numerator (P.numeratorDeriv z) z)
    (hden : HasDerivAt P.denominator (P.denominatorDeriv z) z)
    (hnum' : HasDerivAt (fun w : ℂ ↦ P.numeratorDeriv w)
      (P.numeratorSecondDeriv z) z)
    (hden' : HasDerivAt (fun w : ℂ ↦ P.denominatorDeriv w)
      (P.denominatorSecondDeriv z) z) :
    HasDerivAt P.wronskian 0 z := by
  have h₁ :
      HasDerivAt
        (fun w : ℂ ↦ P.numeratorDeriv w * P.denominator w)
        (P.numeratorSecondDeriv z * P.denominator z +
          P.numeratorDeriv z * P.denominatorDeriv z) z :=
    hnum'.mul hden
  have h₂ :
      HasDerivAt
        (fun w : ℂ ↦ P.numerator w * P.denominatorDeriv w)
        (P.numeratorDeriv z * P.denominatorDeriv z +
          P.numerator z * P.denominatorSecondDeriv z) z :=
    hnum.mul hden'
  have hsub := h₁.sub h₂
  have hsub' :
      HasDerivAt P.wronskian
        ((P.numeratorSecondDeriv z * P.denominator z +
            P.numeratorDeriv z * P.denominatorDeriv z) -
          (P.numeratorDeriv z * P.denominatorDeriv z +
            P.numerator z * P.denominatorSecondDeriv z)) z := by
    simpa [wronskian] using hsub
  convert hsub' using 1
  rw [P.numerator_solves_ode z hz, P.denominator_solves_ode z hz]
  ring

/--
The canonical first quotient derivative `W/y₀²` has derivative
`-2Wy₀'/y₀³`.
-/
theorem localMapDeriv_hasDerivAt
    {q : ℂ → ℂ} {U : Set ℂ} (P : SchwarzianLinearODESolutionPair q U)
    {z : ℂ} (hz : z ∈ U)
    (hnum : HasDerivAt P.numerator (P.numeratorDeriv z) z)
    (hden : HasDerivAt P.denominator (P.denominatorDeriv z) z)
    (hnum' : HasDerivAt (fun w : ℂ ↦ P.numeratorDeriv w)
      (P.numeratorSecondDeriv z) z)
    (hden' : HasDerivAt (fun w : ℂ ↦ P.denominatorDeriv w)
      (P.denominatorSecondDeriv z) z) :
    HasDerivAt P.localMapDeriv (P.localMapSecondDeriv z) z := by
  have hW : HasDerivAt P.wronskian 0 z :=
    P.wronskian_hasDerivAt_zero hz hnum hden hnum' hden'
  have hden_sq :
      HasDerivAt (fun w : ℂ ↦ P.denominator w ^ 2)
        (2 * P.denominator z * P.denominatorDeriv z) z := by
    convert hden.pow 2 using 1
    ring
  have hden_ne : P.denominator z ≠ 0 := P.denominator_ne_zero z hz
  have hden_sq_ne : P.denominator z ^ 2 ≠ 0 := pow_ne_zero 2 hden_ne
  have hquot :
      HasDerivAt
        (fun w : ℂ ↦ P.wronskian w / P.denominator w ^ 2)
        ((0 * P.denominator z ^ 2 -
            P.wronskian z * (2 * P.denominator z * P.denominatorDeriv z)) /
          (P.denominator z ^ 2) ^ 2) z :=
    hW.fun_div hden_sq hden_sq_ne
  have hquot' :
      HasDerivAt P.localMapDeriv
        ((0 * P.denominator z ^ 2 -
            P.wronskian z * (2 * P.denominator z * P.denominatorDeriv z)) /
          (P.denominator z ^ 2) ^ 2) z := by
    simpa [localMapDeriv] using hquot
  convert hquot' using 1
  simp [localMapSecondDeriv]
  field_simp [hden_ne]

set_option maxHeartbeats 800000

/--
The canonical second quotient derivative `-2Wy₀'/y₀³` has derivative the stored
third quotient derivative.
-/
theorem localMapSecondDeriv_hasDerivAt
    {q : ℂ → ℂ} {U : Set ℂ} (P : SchwarzianLinearODESolutionPair q U)
    {z : ℂ} (hz : z ∈ U)
    (hnum : HasDerivAt P.numerator (P.numeratorDeriv z) z)
    (hden : HasDerivAt P.denominator (P.denominatorDeriv z) z)
    (hnum' : HasDerivAt (fun w : ℂ ↦ P.numeratorDeriv w)
      (P.numeratorSecondDeriv z) z)
    (hden' : HasDerivAt (fun w : ℂ ↦ P.denominatorDeriv w)
      (P.denominatorSecondDeriv z) z) :
    HasDerivAt P.localMapSecondDeriv (P.localMapThirdDeriv z) z := by
  have hW : HasDerivAt P.wronskian 0 z :=
    P.wronskian_hasDerivAt_zero hz hnum hden hnum' hden'
  have hnum₂ :
      HasDerivAt
        (fun w : ℂ ↦ -2 * (P.wronskian w * P.denominatorDeriv w))
        (-2 * (0 * P.denominatorDeriv z +
          P.wronskian z * P.denominatorSecondDeriv z)) z := by
    simpa using ((hW.mul hden').const_mul (-2))
  have hden_cube :
      HasDerivAt (fun w : ℂ ↦ P.denominator w ^ 3)
        (3 * P.denominator z ^ 2 * P.denominatorDeriv z) z := by
    convert hden.pow 3 using 1
  have hden_ne : P.denominator z ≠ 0 := P.denominator_ne_zero z hz
  have hden_cube_ne : P.denominator z ^ 3 ≠ 0 := pow_ne_zero 3 hden_ne
  have hquot :
      HasDerivAt
        (fun w : ℂ ↦
          (-2 * (P.wronskian w * P.denominatorDeriv w)) /
            P.denominator w ^ 3)
        (((-2 * (0 * P.denominatorDeriv z +
            P.wronskian z * P.denominatorSecondDeriv z)) *
            P.denominator z ^ 3 -
          (-2 * (P.wronskian z * P.denominatorDeriv z)) *
            (3 * P.denominator z ^ 2 * P.denominatorDeriv z)) /
          (P.denominator z ^ 3) ^ 2) z :=
    hnum₂.fun_div hden_cube hden_cube_ne
  have hquot' :
      HasDerivAt P.localMapSecondDeriv
        (((-2 * (0 * P.denominatorDeriv z +
              P.wronskian z * P.denominatorSecondDeriv z)) *
            P.denominator z ^ 3 -
          (-2 * (P.wronskian z * P.denominatorDeriv z)) *
            (3 * P.denominator z ^ 2 * P.denominatorDeriv z)) /
          (P.denominator z ^ 3) ^ 2) z := by
    convert hquot using 1
    funext w
    simp [localMapSecondDeriv]
    ring
  convert hquot' using 1
  simp [localMapThirdDeriv]
  field_simp [hden_ne]
  ring

set_option maxHeartbeats 200000

end SchwarzianLinearODESolutionPair

/--
A normalized local solution pair for the linear Schwarzian ODE at a basepoint.

The intended initial data are `y_0(z₀)=1`, `y_0'(z₀)=0`, `y_1(z₀)=0`,
`y_1'(z₀)=1`, so the Wronskian is `1` at the basepoint.
-/
structure NormalizedSchwarzianLinearODESolutionPair
    (q : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ)
    extends SchwarzianLinearODESolutionPair q U where
  /-- The basepoint lies in the local domain. -/
  base_mem : z₀ ∈ U
  /-- First normalized initial condition. -/
  denominator_base : denominator z₀ = 1
  /-- Second normalized initial condition. -/
  denominatorDeriv_base : denominatorDeriv z₀ = 0
  /-- Third normalized initial condition. -/
  numerator_base : numerator z₀ = 0
  /-- Fourth normalized initial condition. -/
  numeratorDeriv_base : numeratorDeriv z₀ = 1

namespace NormalizedSchwarzianLinearODESolutionPair

/-- The normalized solution pair has Wronskian `1` at the basepoint. -/
theorem wronskian_base
    {q : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (P : NormalizedSchwarzianLinearODESolutionPair q U z₀) :
    P.toSchwarzianLinearODESolutionPair.wronskian z₀ = 1 := by
  rw [SchwarzianLinearODESolutionPair.wronskian, P.numeratorDeriv_base,
    P.denominator_base, P.numerator_base, P.denominatorDeriv_base]
  ring

/-- Forget normalized initial data, retaining the local Schwarzian ODE frame. -/
def toSchwarzianLinearODEFrame
    {q : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (P : NormalizedSchwarzianLinearODESolutionPair q U z₀) :
    SchwarzianLinearODEFrame q U :=
  P.toSchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame

end NormalizedSchwarzianLinearODESolutionPair

/--
The coefficient of `w^n` in the product of two formal scalar power series with
coefficients `a` and `b`.
-/
def powerSeriesCoeffProduct (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/--
The coefficient of `w^n` in `y'' + (1 / 2) q y`, when `q` has coefficients
`a` and `y` has coefficients `b`.
-/
def schwarzianLinearODECoeff (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) * b (n + 2) +
    (1 / 2 : ℂ) * powerSeriesCoeffProduct a b n

/--
Frobenius/power-series recurrence for the scalar equation
`y'' + (1 / 2) q y = 0`.
-/
def SolvesSchwarzianFrobeniusRecurrence (a b : ℕ → ℂ) : Prop :=
  ∀ n, schwarzianLinearODECoeff a b n = 0

/--
The next coefficient dictated by the recurrence, assuming all earlier
coefficients are already known.
-/
def nextSchwarzianFrobeniusCoefficient (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  -((1 / 2 : ℂ) * powerSeriesCoeffProduct a b n) /
    (((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ))

/--
The product coefficient only depends on the coefficients of the second factor
up to degree `n`.
-/
theorem powerSeriesCoeffProduct_congr_of_eq_on_le
    {a b c : ℕ → ℂ} {n : ℕ}
    (h : ∀ m, m ≤ n → b m = c m) :
    powerSeriesCoeffProduct a b n = powerSeriesCoeffProduct a c n := by
  rw [powerSeriesCoeffProduct, powerSeriesCoeffProduct]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [h (n - k) (Nat.sub_le n k)]

/--
The next Frobenius coefficient only depends on the previously constructed
coefficients `b_0, ..., b_n`.
-/
theorem nextSchwarzianFrobeniusCoefficient_congr_of_eq_on_le
    {a b c : ℕ → ℂ} {n : ℕ}
    (h : ∀ m, m ≤ n → b m = c m) :
    nextSchwarzianFrobeniusCoefficient a b n =
      nextSchwarzianFrobeniusCoefficient a c n := by
  rw [nextSchwarzianFrobeniusCoefficient, nextSchwarzianFrobeniusCoefficient,
    powerSeriesCoeffProduct_congr_of_eq_on_le (a := a) h]

/--
The normalized Frobenius coefficients obtained recursively from
`y'' + (1 / 2) q y = 0`, with initial coefficients `b_0 = 1` and `b_1 = 0`.

The recursive branch uses an auxiliary sequence that agrees with the already
constructed coefficients below degree `n + 2` and is arbitrary afterwards.
The congruence lemma above removes this truncation from the final recurrence.
-/
noncomputable def schwarzianFrobeniusCoefficients (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 0
  | n + 2 =>
      nextSchwarzianFrobeniusCoefficient a
        (fun k => if _h : k < n + 2 then schwarzianFrobeniusCoefficients a k else 0) n
termination_by m => m
decreasing_by
  exact _h

/--
The Frobenius coefficients with arbitrary initial data `b_0` and `b_1`.

This is the linear ODE version used for the numerator and denominator solution
simultaneously.  The earlier normalized sequence is the specialization
`b_0 = 1`, `b_1 = 0`.
-/
noncomputable def schwarzianFrobeniusCoefficientsWithInitial
    (a : ℕ → ℂ) (b₀ b₁ : ℂ) : ℕ → ℂ
  | 0 => b₀
  | 1 => b₁
  | n + 2 =>
      nextSchwarzianFrobeniusCoefficient a
        (fun k =>
          if _h : k < n + 2 then
            schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁ k
          else
            0) n
termination_by m => m
decreasing_by
  exact _h

/-- The normalized Frobenius sequence has constant coefficient `1`. -/
theorem schwarzianFrobeniusCoefficients_zero (a : ℕ → ℂ) :
    schwarzianFrobeniusCoefficients a 0 = 1 := by
  simp [schwarzianFrobeniusCoefficients]

/-- The normalized Frobenius sequence has linear coefficient `0`. -/
theorem schwarzianFrobeniusCoefficients_one (a : ℕ → ℂ) :
    schwarzianFrobeniusCoefficients a 1 = 0 := by
  simp [schwarzianFrobeniusCoefficients]

/-- The normalized Frobenius coefficients satisfy the intended recurrence. -/
theorem schwarzianFrobeniusCoefficients_succ_succ (a : ℕ → ℂ) (n : ℕ) :
    schwarzianFrobeniusCoefficients a (n + 2) =
      nextSchwarzianFrobeniusCoefficient a (schwarzianFrobeniusCoefficients a) n := by
  rw [schwarzianFrobeniusCoefficients]
  apply nextSchwarzianFrobeniusCoefficient_congr_of_eq_on_le
  intro m hm
  have hlt : m < n + 2 := by omega
  simp [hlt]

/-- The arbitrary-initial-data Frobenius sequence has constant coefficient `b₀`. -/
theorem schwarzianFrobeniusCoefficientsWithInitial_zero
    (a : ℕ → ℂ) (b₀ b₁ : ℂ) :
    schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁ 0 = b₀ := by
  simp [schwarzianFrobeniusCoefficientsWithInitial]

/-- The arbitrary-initial-data Frobenius sequence has linear coefficient `b₁`. -/
theorem schwarzianFrobeniusCoefficientsWithInitial_one
    (a : ℕ → ℂ) (b₀ b₁ : ℂ) :
    schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁ 1 = b₁ := by
  simp [schwarzianFrobeniusCoefficientsWithInitial]

/-- The arbitrary-initial-data Frobenius coefficients satisfy the recurrence. -/
theorem schwarzianFrobeniusCoefficientsWithInitial_succ_succ
    (a : ℕ → ℂ) (b₀ b₁ : ℂ) (n : ℕ) :
    schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁ (n + 2) =
      nextSchwarzianFrobeniusCoefficient a
        (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁) n := by
  rw [schwarzianFrobeniusCoefficientsWithInitial]
  apply nextSchwarzianFrobeniusCoefficient_congr_of_eq_on_le
  intro m hm
  have hlt : m < n + 2 := by omega
  simp [hlt]

/-- The earlier normalized sequence is the arbitrary-initial-data sequence with `b₀=1,b₁=0`. -/
theorem schwarzianFrobeniusCoefficients_eq_withInitial (a : ℕ → ℂ) :
    schwarzianFrobeniusCoefficients a =
      schwarzianFrobeniusCoefficientsWithInitial a 1 0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          simp [schwarzianFrobeniusCoefficients,
            schwarzianFrobeniusCoefficientsWithInitial]
      | 1 =>
          simp [schwarzianFrobeniusCoefficients,
            schwarzianFrobeniusCoefficientsWithInitial]
      | n + 2 =>
          rw [schwarzianFrobeniusCoefficients_succ_succ,
            schwarzianFrobeniusCoefficientsWithInitial_succ_succ]
          apply nextSchwarzianFrobeniusCoefficient_congr_of_eq_on_le
          intro m hm
          exact ih m (by omega)

/--
The Frobenius recurrence coefficient really makes the `w^n` coefficient of the
linear ODE vanish.
-/
theorem schwarzianLinearODECoeff_eq_zero_of_nextCoeff
    (a b : ℕ → ℂ) (n : ℕ)
    (hnext : b (n + 2) = nextSchwarzianFrobeniusCoefficient a b n) :
    schwarzianLinearODECoeff a b n = 0 := by
  rw [schwarzianLinearODECoeff, hnext, nextSchwarzianFrobeniusCoefficient]
  have hnonzero :
      (((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero
      (by exact_mod_cast Nat.succ_ne_zero (n + 1))
      (by exact_mod_cast Nat.succ_ne_zero n)
  have htwo_add : ((2 + n : ℕ) : ℂ) ≠ 0 := by
    have hnat : 2 + n ≠ 0 := by omega
    exact_mod_cast hnat
  field_simp [hnonzero, htwo_add]
  have hn_two : ((n + 2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (n + 1)
  field_simp [hn_two]
  ring

/--
The coefficient of a product of two formal power series is bounded by the
convolution of the coefficient norms.
-/
theorem norm_powerSeriesCoeffProduct_le (a b : ℕ → ℂ) (n : ℕ) :
    ‖powerSeriesCoeffProduct a b n‖ ≤
      ∑ k ∈ Finset.range (n + 1), ‖a k‖ * ‖b (n - k)‖ := by
  rw [powerSeriesCoeffProduct]
  calc
    ‖∑ k ∈ Finset.range (n + 1), a k * b (n - k)‖
        ≤ ∑ k ∈ Finset.range (n + 1), ‖a k * b (n - k)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1), ‖a k‖ * ‖b (n - k)‖ := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [norm_mul]

/-- The real norm of the Frobenius denominator. -/
theorem norm_schwarzianFrobeniusDenominator (n : ℕ) :
    ‖(((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ))‖ =
      ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
  rw [norm_mul, norm_natCast, norm_natCast]

/--
The next Frobenius coefficient is bounded by the norm convolution divided by
`(n+2)(n+1)`.
-/
theorem norm_nextSchwarzianFrobeniusCoefficient_le
    (a b : ℕ → ℂ) (n : ℕ) :
    ‖nextSchwarzianFrobeniusCoefficient a b n‖ ≤
      ((1 / 2 : ℝ) *
          (∑ k ∈ Finset.range (n + 1), ‖a k‖ * ‖b (n - k)‖)) /
        (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
  rw [nextSchwarzianFrobeniusCoefficient, norm_div, norm_neg]
  have hprod := norm_powerSeriesCoeffProduct_le a b n
  have hnum : ‖(1 / 2 : ℂ) * powerSeriesCoeffProduct a b n‖ ≤
      (1 / 2 : ℝ) *
        (∑ k ∈ Finset.range (n + 1), ‖a k‖ * ‖b (n - k)‖) := by
    rw [norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    exact mul_le_mul_of_nonneg_left hprod (by norm_num)
  have hden_nonneg :
      0 ≤ ‖(((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ))‖ :=
    norm_nonneg _
  calc
    ‖(1 / 2 : ℂ) * powerSeriesCoeffProduct a b n‖ /
        ‖(((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ))‖
        ≤ ((1 / 2 : ℝ) *
            (∑ k ∈ Finset.range (n + 1), ‖a k‖ * ‖b (n - k)‖)) /
          ‖(((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ))‖ :=
          div_le_div_of_nonneg_right hnum hden_nonneg
    _ = ((1 / 2 : ℝ) *
            (∑ k ∈ Finset.range (n + 1), ‖a k‖ * ‖b (n - k)‖)) /
          (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
          rw [norm_schwarzianFrobeniusDenominator]

/--
Majorized coefficient bounds propagate through the next Frobenius coefficient.
-/
theorem norm_nextSchwarzianFrobeniusCoefficient_le_of_bounds
    {a b : ℕ → ℂ} {A B : ℕ → ℝ} {n : ℕ}
    (hA_nonneg : ∀ k, k ≤ n → 0 ≤ A k)
    (ha : ∀ k, k ≤ n → ‖a k‖ ≤ A k)
    (hb : ∀ k, k ≤ n → ‖b k‖ ≤ B k) :
    ‖nextSchwarzianFrobeniusCoefficient a b n‖ ≤
      ((1 / 2 : ℝ) *
          (∑ k ∈ Finset.range (n + 1), A k * B (n - k))) /
        (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
  have hsum :
      (∑ k ∈ Finset.range (n + 1), ‖a k‖ * ‖b (n - k)‖) ≤
        ∑ k ∈ Finset.range (n + 1), A k * B (n - k) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hk_le : k ≤ n := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    exact mul_le_mul (ha k hk_le) (hb (n - k) (Nat.sub_le n k))
      (norm_nonneg _) (hA_nonneg k hk_le)
  have hmul :
      (1 / 2 : ℝ) *
          (∑ k ∈ Finset.range (n + 1), ‖a k‖ * ‖b (n - k)‖) ≤
        (1 / 2 : ℝ) *
          (∑ k ∈ Finset.range (n + 1), A k * B (n - k)) :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hden_nonneg :
      0 ≤ (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
    positivity
  exact
    le_trans (norm_nextSchwarzianFrobeniusCoefficient_le a b n)
      (div_le_div_of_nonneg_right hmul hden_nonneg)

/-- A real sequence `B` coefficientwise majorizes a complex sequence `b`. -/
def CoefficientNormMajorizes (B : ℕ → ℝ) (b : ℕ → ℂ) : Prop :=
  ∀ n, ‖b n‖ ≤ B n

/--
A real majorant recurrence for the Frobenius coefficients relative to a
coefficient bound `A`.
-/
def SchwarzianFrobeniusMajorantRecurrence (A B : ℕ → ℝ) : Prop :=
  ∀ n,
    ((1 / 2 : ℝ) *
        (∑ k ∈ Finset.range (n + 1), A k * B (n - k))) /
      (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ≤ B (n + 2)

/-- The convolution of two geometric coefficient bounds is again explicit. -/
theorem geometric_frobeniusConvolution_sum
    (C D T : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), C * T ^ k * (D * T ^ (n - k))) =
      ((n + 1 : ℕ) : ℝ) * (C * D * T ^ n) := by
  calc
    (∑ k ∈ Finset.range (n + 1), C * T ^ k * (D * T ^ (n - k)))
        = ∑ k ∈ Finset.range (n + 1), C * D * T ^ n := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          have hp : T ^ k * T ^ (n - k) = T ^ n := by
            rw [← pow_add, Nat.add_sub_of_le hk_le]
          calc
            C * T ^ k * (D * T ^ (n - k))
                = C * D * (T ^ k * T ^ (n - k)) := by ring
            _ = C * D * T ^ n := by rw [hp]
    _ = ((n + 1 : ℕ) : ℝ) * (C * D * T ^ n) := by
          simp

/--
A geometric coefficient majorant satisfies the Frobenius majorant recurrence
once the coefficient bound `C` is controlled by `T^2`.
-/
theorem geometric_schwarzianFrobeniusMajorantRecurrence
    {C D T : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hCT : C ≤ 4 * T ^ 2) :
    SchwarzianFrobeniusMajorantRecurrence
      (fun n ↦ C * T ^ n) (fun n ↦ D * T ^ n) := by
  intro n
  rw [geometric_frobeniusConvolution_sum C D T n]
  have hden_pos : 0 < (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
    positivity
  have hn1_pos : 0 < ((n + 1 : ℕ) : ℝ) := by
    positivity
  have hT2 : 0 ≤ T ^ 2 := by
    positivity
  have hn4 : (4 : ℝ) ≤ 2 * ((n + 2 : ℕ) : ℝ) := by
    have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    norm_num
    linarith
  have hC_le : C ≤ 2 * ((n + 2 : ℕ) : ℝ) * T ^ 2 := by
    have h4T : 4 * T ^ 2 ≤ (2 * ((n + 2 : ℕ) : ℝ)) * T ^ 2 :=
      mul_le_mul_of_nonneg_right hn4 hT2
    nlinarith
  have hDT : 0 ≤ D * T ^ n := mul_nonneg hD (pow_nonneg hT n)
  have hmain :
      C * (D * T ^ n) ≤
        (2 * ((n + 2 : ℕ) : ℝ) * T ^ 2) * (D * T ^ n) :=
    mul_le_mul_of_nonneg_right hC_le hDT
  change
    ((1 / 2 : ℝ) * (((n + 1 : ℕ) : ℝ) * (C * D * T ^ n))) /
      (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ≤ D * T ^ (n + 2)
  rw [pow_succ, pow_succ]
  field_simp [ne_of_gt hden_pos, ne_of_gt hn1_pos]
  nlinarith

/--
If `A` bounds the Schwarzian-coefficient series and `B` satisfies the real
majorant recurrence, then `B` bounds the recursively constructed Frobenius
coefficients with arbitrary initial data.
-/
theorem coefficientNormMajorizes_schwarzianFrobeniusCoefficientsWithInitial
    {a : ℕ → ℂ} {A B : ℕ → ℝ} {b₀ b₁ : ℂ}
    (hA_nonneg : ∀ n, 0 ≤ A n)
    (ha : ∀ n, ‖a n‖ ≤ A n)
    (hB₀ : ‖b₀‖ ≤ B 0)
    (hB₁ : ‖b₁‖ ≤ B 1)
    (hBstep : SchwarzianFrobeniusMajorantRecurrence A B) :
    CoefficientNormMajorizes B
      (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          simpa [schwarzianFrobeniusCoefficientsWithInitial] using hB₀
      | 1 =>
          simpa [schwarzianFrobeniusCoefficientsWithInitial] using hB₁
      | n + 2 =>
          rw [schwarzianFrobeniusCoefficientsWithInitial_succ_succ]
          exact le_trans
            (norm_nextSchwarzianFrobeniusCoefficient_le_of_bounds
              (a := a)
              (b := schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)
              (A := A) (B := B)
              (n := n)
              (fun k _hk ↦ hA_nonneg k)
              (fun k _hk ↦ ha k)
              (fun k hk ↦ ih k (by omega)))
            (hBstep n)

/--
Geometric majorants bound the recursively constructed Frobenius coefficients,
provided the initial coefficients are bounded by the same geometric sequence.
-/
theorem coefficientNormMajorizes_schwarzianFrobeniusCoefficientsWithInitial_geometric
    {a : ℕ → ℂ} {C D T : ℝ} {b₀ b₁ : ℂ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hCT : C ≤ 4 * T ^ 2)
    (ha : ∀ n, ‖a n‖ ≤ C * T ^ n)
    (hB₀ : ‖b₀‖ ≤ D)
    (hB₁ : ‖b₁‖ ≤ D * T) :
    CoefficientNormMajorizes (fun n ↦ D * T ^ n)
      (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁) :=
  coefficientNormMajorizes_schwarzianFrobeniusCoefficientsWithInitial
    (A := fun n ↦ C * T ^ n)
    (B := fun n ↦ D * T ^ n)
    (b₀ := b₀) (b₁ := b₁)
    (fun n ↦ mul_nonneg hC (pow_nonneg hT n))
    ha
    (by simpa using hB₀)
    (by simpa using hB₁)
    (geometric_schwarzianFrobeniusMajorantRecurrence hD hT hCT)

/--
A formal Frobenius solution for `y'' + (1 / 2) q y = 0`, with prescribed
initial coefficients.

This is the formal-power-series part of the ODE existence proof.  The analytic
part still to be supplied is convergence of these coefficients on a nonzero
disc and identification with the analytic Taylor series.
-/
structure SchwarzianFrobeniusSeries (a : ℕ → ℂ) where
  /-- Formal coefficients of the solution. -/
  coeff : ℕ → ℂ
  /-- The constant coefficient. -/
  coeff_zero : coeff 0 = 1
  /-- The linear coefficient. -/
  coeff_one : coeff 1 = 0
  /-- The recurrence for all higher coefficients. -/
  coeff_succ_succ : ∀ n, coeff (n + 2) = nextSchwarzianFrobeniusCoefficient a coeff n

/-- A formal Frobenius solution with arbitrary prescribed initial coefficients. -/
structure SchwarzianFrobeniusSeriesWithInitial
    (a : ℕ → ℂ) (b₀ b₁ : ℂ) where
  /-- Formal coefficients of the solution. -/
  coeff : ℕ → ℂ
  /-- The constant coefficient. -/
  coeff_zero : coeff 0 = b₀
  /-- The linear coefficient. -/
  coeff_one : coeff 1 = b₁
  /-- The recurrence for all higher coefficients. -/
  coeff_succ_succ : ∀ n, coeff (n + 2) = nextSchwarzianFrobeniusCoefficient a coeff n

namespace SchwarzianFrobeniusSeries

/-- A Frobenius series solves the coefficient recurrence for the linear ODE. -/
theorem solves_recurrence {a : ℕ → ℂ} (Y : SchwarzianFrobeniusSeries a) :
    SolvesSchwarzianFrobeniusRecurrence a Y.coeff := by
  intro n
  exact schwarzianLinearODECoeff_eq_zero_of_nextCoeff a Y.coeff n (Y.coeff_succ_succ n)

end SchwarzianFrobeniusSeries

namespace SchwarzianFrobeniusSeriesWithInitial

/-- A Frobenius series with arbitrary initial data solves the coefficient recurrence. -/
theorem solves_recurrence {a : ℕ → ℂ} {b₀ b₁ : ℂ}
    (Y : SchwarzianFrobeniusSeriesWithInitial a b₀ b₁) :
    SolvesSchwarzianFrobeniusRecurrence a Y.coeff := by
  intro n
  exact schwarzianLinearODECoeff_eq_zero_of_nextCoeff a Y.coeff n (Y.coeff_succ_succ n)

end SchwarzianFrobeniusSeriesWithInitial

/--
Existence target for the Frobenius recurrence with prescribed initial data.

This is deliberately formal: it asks only for the coefficient sequence.  A
later analytic theorem should prove convergence and build actual holomorphic
solutions from these coefficients.
-/
def SchwarzianFrobeniusRecurrenceExistenceTheorem : Prop :=
  ∀ a : ℕ → ℂ, Nonempty (SchwarzianFrobeniusSeries a)

/-- Existence target for the Frobenius recurrence with arbitrary initial data. -/
def SchwarzianFrobeniusRecurrenceWithInitialExistenceTheorem : Prop :=
  ∀ (a : ℕ → ℂ) (b₀ b₁ : ℂ),
    Nonempty (SchwarzianFrobeniusSeriesWithInitial a b₀ b₁)

/-- The recursively constructed normalized Frobenius series. -/
noncomputable def normalizedSchwarzianFrobeniusSeries (a : ℕ → ℂ) :
    SchwarzianFrobeniusSeries a where
  coeff := schwarzianFrobeniusCoefficients a
  coeff_zero := schwarzianFrobeniusCoefficients_zero a
  coeff_one := schwarzianFrobeniusCoefficients_one a
  coeff_succ_succ := schwarzianFrobeniusCoefficients_succ_succ a

/-- The recursively constructed Frobenius series with arbitrary initial data. -/
noncomputable def schwarzianFrobeniusSeriesWithInitial
    (a : ℕ → ℂ) (b₀ b₁ : ℂ) :
    SchwarzianFrobeniusSeriesWithInitial a b₀ b₁ where
  coeff := schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁
  coeff_zero := schwarzianFrobeniusCoefficientsWithInitial_zero a b₀ b₁
  coeff_one := schwarzianFrobeniusCoefficientsWithInitial_one a b₀ b₁
  coeff_succ_succ := schwarzianFrobeniusCoefficientsWithInitial_succ_succ a b₀ b₁

/--
Formal existence of normalized Frobenius coefficients for
`y'' + (1 / 2) q y = 0`.

This closes the purely algebraic recurrence-existence boundary.  Convergence of
the resulting series remains a separate analytic theorem.
-/
theorem schwarzianFrobeniusRecurrenceExistence :
    SchwarzianFrobeniusRecurrenceExistenceTheorem := by
  intro a
  exact ⟨normalizedSchwarzianFrobeniusSeries a⟩

/--
Formal existence of Frobenius coefficients for arbitrary initial data.

This supplies both normalized solutions needed for the Schwarzian ratio:
`(b₀,b₁)=(1,0)` for the denominator and `(b₀,b₁)=(0,1)` for the numerator.
-/
theorem schwarzianFrobeniusRecurrenceWithInitialExistence :
    SchwarzianFrobeniusRecurrenceWithInitialExistenceTheorem := by
  intro a b₀ b₁
  exact ⟨schwarzianFrobeniusSeriesWithInitial a b₀ b₁⟩

/-- Scalar formal multilinear series associated to ordinary one-variable coefficients. -/
def scalarFormalPowerSeries (b : ℕ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ b

/-- Coefficients of the formal first derivative of a scalar power series. -/
def powerSeriesDerivativeCoefficients (b : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ ((n + 1 : ℕ) : ℂ) * b (n + 1)

/-- Coefficients of the formal second derivative of a scalar power series. -/
def powerSeriesSecondDerivativeCoefficients (b : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) * b (n + 2)

/-- Taking formal derivative coefficients twice gives the second-derivative coefficients. -/
theorem powerSeriesDerivativeCoefficients_derivative
    (b : ℕ → ℂ) :
    powerSeriesDerivativeCoefficients (powerSeriesDerivativeCoefficients b) =
      powerSeriesSecondDerivativeCoefficients b := by
  funext n
  simp [powerSeriesDerivativeCoefficients, powerSeriesSecondDerivativeCoefficients]
  ring

/--
A geometric bound on scalar coefficients gives summability of the norm-weighted
formal multilinear series inside the corresponding geometric radius.
-/
theorem scalarFormalPowerSeries_summable_norm_of_geometric_bound
    {b : ℕ → ℂ} {D T : ℝ} {r : NNReal}
    (hT : 0 ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ D * T ^ n)
    (hTr : T * (r : ℝ) < 1) :
    Summable fun n : ℕ => ‖scalarFormalPowerSeries b n‖ * (r : ℝ) ^ n := by
  have hgeom_nonneg : 0 ≤ T * (r : ℝ) := mul_nonneg hT r.2
  have hgeom : Summable fun n : ℕ => D * (T * (r : ℝ)) ^ n :=
    (summable_geometric_of_lt_one hgeom_nonneg hTr).mul_left D
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro n
    positivity
  · intro n
    rw [scalarFormalPowerSeries, FormalMultilinearSeries.ofScalars_norm]
    calc
      ‖b n‖ * (r : ℝ) ^ n ≤ (D * T ^ n) * (r : ℝ) ^ n := by
        exact mul_le_mul_of_nonneg_right (hb n) (pow_nonneg r.2 n)
      _ = D * (T * (r : ℝ)) ^ n := by
        rw [mul_assoc, ← mul_pow]

/--
A geometric coefficient bound gives a lower bound on the radius of convergence
of the associated scalar formal power series.
-/
theorem scalarFormalPowerSeries_radius_ge_of_geometric_bound
    {b : ℕ → ℂ} {D T : ℝ} {r : NNReal}
    (hT : 0 ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ D * T ^ n)
    (hTr : T * (r : ℝ) < 1) :
    (r : ENNReal) ≤ (scalarFormalPowerSeries b).radius :=
  FormalMultilinearSeries.le_radius_of_summable_norm (scalarFormalPowerSeries b)
    (scalarFormalPowerSeries_summable_norm_of_geometric_bound hT hb hTr)

/--
A geometric coefficient bound gives an actual convergent power-series expansion
for the canonical sum of the scalar formal power series.
-/
theorem scalarFormalPowerSeries_hasFPowerSeriesOnBall_of_geometric_bound
    {b : ℕ → ℂ} {D T : ℝ} {r : NNReal}
    (hr : 0 < r) (hT : 0 ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ D * T ^ n)
    (hTr : T * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall
      (scalarFormalPowerSeries b).sum (scalarFormalPowerSeries b) 0 (r : ENNReal) := by
  have hle : (r : ENNReal) ≤ (scalarFormalPowerSeries b).radius :=
    scalarFormalPowerSeries_radius_ge_of_geometric_bound hT hb hTr
  have hpos : 0 < (scalarFormalPowerSeries b).radius :=
    lt_of_lt_of_le (by exact_mod_cast hr) hle
  exact (scalarFormalPowerSeries b).hasFPowerSeriesOnBall hpos |>.mono
    (by exact_mod_cast hr) hle

/--
A geometric bound on scalar coefficients gives summability for the termwise
first derivative series on the same geometric radius.
-/
theorem scalarFormalPowerSeries_derivative_summable_norm_of_geometric_bound
    {b : ℕ → ℂ} {D T : ℝ} {r : NNReal}
    (hT : 0 ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ D * T ^ n)
    (hTr : T * (r : ℝ) < 1) :
    Summable fun n : ℕ =>
      ‖scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b) n‖ * (r : ℝ) ^ n := by
  have hx0 : 0 ≤ T * (r : ℝ) := mul_nonneg hT r.2
  have hxnorm : ‖T * (r : ℝ)‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have hpoly :
      Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (T * (r : ℝ)) ^ n := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := T * (r : ℝ)) hxnorm)
  have hdom : Summable fun n : ℕ =>
      (D * T) * (((n + 1 : ℕ) : ℝ) * (T * (r : ℝ)) ^ n) :=
    hpoly.mul_left (D * T)
  refine Summable.of_nonneg_of_le ?_ ?_ hdom
  · intro n
    positivity
  · intro n
    rw [scalarFormalPowerSeries, FormalMultilinearSeries.ofScalars_norm,
      powerSeriesDerivativeCoefficients]
    calc
      ‖((n + 1 : ℕ) : ℂ) * b (n + 1)‖ * (r : ℝ) ^ n
          ≤ (((n + 1 : ℕ) : ℝ) * (D * T ^ (n + 1))) * (r : ℝ) ^ n := by
            rw [norm_mul, Complex.norm_natCast]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hb (n + 1)) (by positivity))
              (pow_nonneg r.2 n)
      _ = (D * T) * (((n + 1 : ℕ) : ℝ) * (T * (r : ℝ)) ^ n) := by
            rw [pow_succ, mul_pow]
            ring

/--
A geometric bound on scalar coefficients gives summability for the termwise
second derivative series on the same geometric radius.
-/
theorem scalarFormalPowerSeries_second_derivative_summable_norm_of_geometric_bound
    {b : ℕ → ℂ} {D T : ℝ} {r : NNReal}
    (hT : 0 ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ D * T ^ n)
    (hTr : T * (r : ℝ) < 1) :
    Summable fun n : ℕ =>
      ‖scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b) n‖ *
        (r : ℝ) ^ n := by
  have hx0 : 0 ≤ T * (r : ℝ) := mul_nonneg hT r.2
  have hxnorm : ‖T * (r : ℝ)‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have hpoly : Summable fun n : ℕ =>
      (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) *
        (T * (r : ℝ)) ^ n := by
    let h := summable_descFactorial_mul_geometric_of_norm_lt_one
      (R := ℝ) 2 (r := T * (r : ℝ)) hxnorm
    refine h.congr ?_
    intro n
    simp [mul_comm]
  have hdom : Summable fun n : ℕ =>
      (D * T ^ 2) *
        ((((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) *
          (T * (r : ℝ)) ^ n) :=
    hpoly.mul_left (D * T ^ 2)
  refine Summable.of_nonneg_of_le ?_ ?_ hdom
  · intro n
    positivity
  · intro n
    rw [scalarFormalPowerSeries, FormalMultilinearSeries.ofScalars_norm,
      powerSeriesSecondDerivativeCoefficients]
    calc
      ‖((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) * b (n + 2)‖ *
          (r : ℝ) ^ n
          ≤ ((((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) *
              (D * T ^ (n + 2))) * (r : ℝ) ^ n := by
            rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hb (n + 2)) (by positivity))
              (pow_nonneg r.2 n)
      _ = (D * T ^ 2) *
            ((((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) *
              (T * (r : ℝ)) ^ n) := by
            rw [show T ^ (n + 2) = T ^ 2 * T ^ n by ring_nf, mul_pow]
            ring

/-- A geometric coefficient bound gives a radius lower bound for the first derivative series. -/
theorem scalarFormalPowerSeries_derivative_radius_ge_of_geometric_bound
    {b : ℕ → ℂ} {D T : ℝ} {r : NNReal}
    (hT : 0 ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ D * T ^ n)
    (hTr : T * (r : ℝ) < 1) :
    (r : ENNReal) ≤ (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)).radius :=
  FormalMultilinearSeries.le_radius_of_summable_norm
    (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b))
    (scalarFormalPowerSeries_derivative_summable_norm_of_geometric_bound hT hb hTr)

/-- A geometric coefficient bound gives a radius lower bound for the second derivative series. -/
theorem scalarFormalPowerSeries_second_derivative_radius_ge_of_geometric_bound
    {b : ℕ → ℂ} {D T : ℝ} {r : NNReal}
    (hT : 0 ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ D * T ^ n)
    (hTr : T * (r : ℝ) < 1) :
    (r : ENNReal) ≤
      (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b)).radius :=
  FormalMultilinearSeries.le_radius_of_summable_norm
    (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b))
    (scalarFormalPowerSeries_second_derivative_summable_norm_of_geometric_bound hT hb hTr)

/-- A geometric coefficient bound gives a convergent first derivative power series. -/
theorem scalarFormalPowerSeries_derivative_hasFPowerSeriesOnBall_of_geometric_bound
    {b : ℕ → ℂ} {D T : ℝ} {r : NNReal}
    (hr : 0 < r) (hT : 0 ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ D * T ^ n)
    (hTr : T * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall
      (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)).sum
      (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)) 0
      (r : ENNReal) := by
  have hle : (r : ENNReal) ≤
      (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)).radius :=
    scalarFormalPowerSeries_derivative_radius_ge_of_geometric_bound hT hb hTr
  have hpos : 0 < (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)).radius :=
    lt_of_lt_of_le (by exact_mod_cast hr) hle
  exact (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)).hasFPowerSeriesOnBall
    hpos |>.mono (by exact_mod_cast hr) hle

/--
Scalar power-series termwise differentiation boundary.

Mathlib proves that Frechet derivatives of analytic functions have a power
series via `HasFPowerSeriesOnBall.fderiv`.  This project-local boundary is the
one-variable scalar specialization identifying that Frechet derivative series
with the explicit coefficient sequence `(n+1)b_{n+1}`.
-/
def ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem : Prop :=
  ∀ {f : ℂ → ℂ} {b : ℕ → ℂ} {r : ENNReal},
    HasFPowerSeriesOnBall f (scalarFormalPowerSeries b) 0 r →
      HasFPowerSeriesOnBall (deriv f)
        (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)) 0 r

/--
The Frechet derivative series of a scalar formal power series, evaluated in
the unit tangent direction, is the scalar formal power series with coefficients
`(n+1)b_{n+1}`.
-/
theorem scalarFormalPowerSeries_derivSeries_apply_eq
    (b : ℕ → ℂ) :
    ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (scalarFormalPowerSeries b).derivSeries) =
      scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b) := by
  apply FormalMultilinearSeries.ext
  intro n
  apply ContinuousMultilinearMap.ext
  intro v
  have hcoeff :
      (((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
          (scalarFormalPowerSeries b).derivSeries).coeff n) =
        (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)).coeff n := by
    rw [FormalMultilinearSeries.coeff,
      ContinuousLinearMap.compFormalMultilinearSeries_apply',
      ContinuousLinearMap.apply_apply]
    change (((scalarFormalPowerSeries b).derivSeries n)
        (fun _ : Fin n => (1 : ℂ))) (1 : ℂ) =
      (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b) n)
        (fun _ : Fin n => (1 : ℂ))
    rw [FormalMultilinearSeries.derivSeries_apply_diag]
    simp [scalarFormalPowerSeries, powerSeriesDerivativeCoefficients]
  calc
    (((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (scalarFormalPowerSeries b).derivSeries) n) v
        = (∏ i, v i) •
            (((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
              (scalarFormalPowerSeries b).derivSeries).coeff n) := by
          rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    _ = (∏ i, v i) •
            (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)).coeff n := by
          rw [hcoeff]
    _ = (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b) n) v := by
          rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]

/--
Termwise differentiation for scalar complex formal power series.

This is the project-local specialization of mathlib's
`HasFPowerSeriesOnBall.fderiv`: after taking the Frechet derivative of the
analytic function and evaluating it on the unit tangent vector, the resulting
one-variable derivative has coefficient sequence `(n+1)b_{n+1}`.
-/
theorem scalarFormalPowerSeries_deriv_hasFPowerSeriesOnBall
    {f : ℂ → ℂ} {b : ℕ → ℂ} {r : ENNReal}
    (h : HasFPowerSeriesOnBall f (scalarFormalPowerSeries b) 0 r) :
    HasFPowerSeriesOnBall (deriv f)
      (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)) 0 r := by
  have hfderiv :
      HasFPowerSeriesOnBall (fderiv ℂ f) (scalarFormalPowerSeries b).derivSeries 0 r :=
    h.fderiv
  have happ :
      HasFPowerSeriesOnBall ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) ∘ (fderiv ℂ f))
        ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
          (scalarFormalPowerSeries b).derivSeries) 0 r :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall hfderiv
  simpa [deriv, scalarFormalPowerSeries_derivSeries_apply_eq b] using happ

/-- The scalar termwise-derivative boundary is now discharged from mathlib. -/
theorem scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem :
    ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem := by
  intro f b r h
  exact scalarFormalPowerSeries_deriv_hasFPowerSeriesOnBall h

/-- A geometric coefficient bound gives a convergent second derivative power series. -/
theorem scalarFormalPowerSeries_second_derivative_hasFPowerSeriesOnBall_of_geometric_bound
    {b : ℕ → ℂ} {D T : ℝ} {r : NNReal}
    (hr : 0 < r) (hT : 0 ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ D * T ^ n)
    (hTr : T * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall
      (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b)).sum
      (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b)) 0
      (r : ENNReal) := by
  have hle : (r : ENNReal) ≤
      (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b)).radius :=
    scalarFormalPowerSeries_second_derivative_radius_ge_of_geometric_bound hT hb hTr
  have hpos :
      0 < (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b)).radius :=
    lt_of_lt_of_le (by exact_mod_cast hr) hle
  exact (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b)).hasFPowerSeriesOnBall
    hpos |>.mono (by exact_mod_cast hr) hle

/-- The sum of a scalar formal power series at the center is its constant coefficient. -/
theorem scalarFormalPowerSeries_sum_zero
    {b : ℕ → ℂ} {r : ENNReal}
    (h : HasFPowerSeriesOnBall
      (scalarFormalPowerSeries b).sum (scalarFormalPowerSeries b) 0 r) :
    (scalarFormalPowerSeries b).sum 0 = b 0 := by
  have hz := h.coeff_zero (fun _ : Fin 0 => (0 : ℂ))
  simpa [scalarFormalPowerSeries, FormalMultilinearSeries.ofScalars] using hz.symm

/--
The sum of the termwise first derivative series at the center is the original
linear coefficient.
-/
theorem scalarFormalPowerSeries_derivative_sum_zero
    {b : ℕ → ℂ} {r : ENNReal}
    (h : HasFPowerSeriesOnBall
      (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)).sum
      (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)) 0 r) :
    (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)).sum 0 = b 1 := by
  have hz := h.coeff_zero (fun _ : Fin 0 => (0 : ℂ))
  simpa [scalarFormalPowerSeries, FormalMultilinearSeries.ofScalars,
    powerSeriesDerivativeCoefficients] using hz.symm

/--
The recurrence `y'' + (1 / 2) q y = 0` implies the corresponding identity for
ordinary sums at one point, provided the two input series are absolutely
summable there.

This is the analytic Cauchy-product step: the coefficient recurrence identifies
the second derivative coefficients with `-1/2` times the convolution
coefficients, while absolute summability identifies the convolution series with
the product of the two sums.
-/
theorem schwarzianFrobenius_tsum_ode_identity_of_recurrence
    {a b : ℕ → ℂ} {w qv yv yddv : ℂ}
    (hqsum : HasSum (fun n : ℕ => a n * w ^ n) qv)
    (hysum : HasSum (fun n : ℕ => b n * w ^ n) yv)
    (hddsum : HasSum
      (fun n : ℕ => powerSeriesSecondDerivativeCoefficients b n * w ^ n) yddv)
    (hqa : Summable fun n : ℕ => ‖a n * w ^ n‖)
    (hyb : Summable fun n : ℕ => ‖b n * w ^ n‖)
    (hrec : SolvesSchwarzianFrobeniusRecurrence a b) :
    yddv = -((1 / 2 : ℂ) * qv * yv) := by
  have hprod :
      HasSum (fun n : ℕ => powerSeriesCoeffProduct a b n * w ^ n) (qv * yv) := by
    have hp := hasSum_sum_range_mul_of_summable_norm (R := ℂ) hqa hyb
    have hp2 : HasSum
        (fun n : ℕ =>
          ∑ k ∈ Finset.range (n + 1), (a k * w ^ k) * (b (n - k) * w ^ (n - k)))
        (qv * yv) := by
      convert hp using 1
      · rw [hqsum.tsum_eq, hysum.tsum_eq]
    refine hp2.congr_fun ?_
    intro n
    rw [powerSeriesCoeffProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hpow : w ^ k * w ^ (n - k) = w ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hk_le]
    rw [← hpow]
    ring
  have hscaled :
      HasSum (fun n : ℕ => -((1 / 2 : ℂ) * (powerSeriesCoeffProduct a b n * w ^ n)))
        (-((1 / 2 : ℂ) * (qv * yv))) := by
    simpa [mul_assoc] using hprod.mul_left (-(1 / 2 : ℂ))
  have hdd_scaled :
      HasSum (fun n : ℕ => -((1 / 2 : ℂ) * (powerSeriesCoeffProduct a b n * w ^ n)))
        yddv := by
    refine hddsum.congr_fun ?_
    intro n
    have hcoeff :
        powerSeriesSecondDerivativeCoefficients b n =
          -((1 / 2 : ℂ) * powerSeriesCoeffProduct a b n) := by
      have h := hrec n
      rw [schwarzianLinearODECoeff] at h
      rw [powerSeriesSecondDerivativeCoefficients]
      exact eq_neg_of_add_eq_zero_left h
    rw [hcoeff]
    ring
  have huniq := hdd_scaled.unique hscaled
  simpa [mul_assoc] using huniq

/--
On a power-series ball, the Frobenius coefficient recurrence gives the analytic
ODE identity for the canonical sums.
-/
theorem schwarzianFrobenius_sum_ode_identityOnBall_of_recurrence
    {q : ℂ → ℂ} {z₀ : ℂ} {a b : ℕ → ℂ} {r : ENNReal}
    (hq : HasFPowerSeriesOnBall (fun w : ℂ => q (z₀ + w)) (scalarFormalPowerSeries a) 0 r)
    (hy : HasFPowerSeriesOnBall (scalarFormalPowerSeries b).sum (scalarFormalPowerSeries b) 0 r)
    (hdd : HasFPowerSeriesOnBall
      (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b)).sum
      (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b)) 0 r)
    (hrec : SolvesSchwarzianFrobeniusRecurrence a b) :
    ∀ w, w ∈ Metric.eball (0 : ℂ) r →
      (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b)).sum w =
        -((1 / 2 : ℂ) * q (z₀ + w) * (scalarFormalPowerSeries b).sum w) := by
  intro w hw
  have hqsum : HasSum (fun n : ℕ => a n * w ^ n) (q (z₀ + w)) := by
    have hraw := hq.hasSum hw
    have htarget := hraw.congr_fun (g := fun n : ℕ => a n * w ^ n) (fun n => by
      simp [scalarFormalPowerSeries, smul_eq_mul, mul_comm])
    simpa using htarget
  have hysum : HasSum (fun n : ℕ => b n * w ^ n) ((scalarFormalPowerSeries b).sum w) := by
    have hraw := hy.hasSum hw
    have htarget := hraw.congr_fun (g := fun n : ℕ => b n * w ^ n) (fun n => by
      simp [scalarFormalPowerSeries, smul_eq_mul, mul_comm])
    simpa using htarget
  have hddsum : HasSum
      (fun n : ℕ => powerSeriesSecondDerivativeCoefficients b n * w ^ n)
      ((scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients b)).sum w) := by
    have hraw := hdd.hasSum hw
    have htarget := hraw.congr_fun
      (g := fun n : ℕ => powerSeriesSecondDerivativeCoefficients b n * w ^ n)
      (fun n => by
        simp [scalarFormalPowerSeries, smul_eq_mul, mul_comm])
    simpa using htarget
  have hqa : Summable fun n : ℕ => ‖a n * w ^ n‖ := by
    have hwrad : w ∈ Metric.eball (0 : ℂ) (scalarFormalPowerSeries a).radius :=
      Metric.eball_subset_eball hq.r_le hw
    have hs := (scalarFormalPowerSeries a).summable_norm_apply hwrad
    refine hs.congr ?_
    intro n
    simp [scalarFormalPowerSeries, smul_eq_mul, mul_comm]
  have hyb : Summable fun n : ℕ => ‖b n * w ^ n‖ := by
    have hwrad : w ∈ Metric.eball (0 : ℂ) (scalarFormalPowerSeries b).radius :=
      Metric.eball_subset_eball hy.r_le hw
    have hs := (scalarFormalPowerSeries b).summable_norm_apply hwrad
    refine hs.congr ?_
    intro n
    simp [scalarFormalPowerSeries, smul_eq_mul, mul_comm]
  exact schwarzianFrobenius_tsum_ode_identity_of_recurrence
    hqsum hysum hddsum hqa hyb hrec

/--
Geometric majorants give a convergent Frobenius solution series for the
recursively constructed coefficients.

This is the convergence half of the Frobenius method: once the holomorphic
coefficient `q` has Taylor coefficients bounded by `C * T ^ n`, and the
initial data fit under the same geometric majorant `D * T ^ n`, the solution
coefficients define an honest analytic power series on every disc with
`T * r < 1`.
-/
theorem schwarzianFrobeniusCoefficientsWithInitial_hasFPowerSeriesOnBall_of_geometric_majorant
    {a : ℕ → ℂ} {C D T : ℝ} {b₀ b₁ : ℂ} {r : NNReal}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hCT : C ≤ 4 * T ^ 2)
    (ha : ∀ n, ‖a n‖ ≤ C * T ^ n)
    (hB₀ : ‖b₀‖ ≤ D)
    (hB₁ : ‖b₁‖ ≤ D * T)
    (hTr : T * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall
      (scalarFormalPowerSeries
        (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)).sum
      (scalarFormalPowerSeries
        (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)) 0
      (r : ENNReal) := by
  exact scalarFormalPowerSeries_hasFPowerSeriesOnBall_of_geometric_bound
    (b := schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)
    (D := D) (T := T) (r := r)
    hr hT
    (coefficientNormMajorizes_schwarzianFrobeniusCoefficientsWithInitial_geometric
      (a := a) (C := C) (D := D) (T := T) (b₀ := b₀) (b₁ := b₁)
      hC hD hT hCT ha hB₀ hB₁)
    hTr

/--
The first termwise derivative series of the recursively constructed Frobenius
solution converges under the same geometric majorant hypotheses.
-/
theorem schwarzianFrobeniusCoefficientsWithInitial_derivative_hasFPowerSeriesOnBall_of_geometric_majorant
    {a : ℕ → ℂ} {C D T : ℝ} {b₀ b₁ : ℂ} {r : NNReal}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hCT : C ≤ 4 * T ^ 2)
    (ha : ∀ n, ‖a n‖ ≤ C * T ^ n)
    (hB₀ : ‖b₀‖ ≤ D)
    (hB₁ : ‖b₁‖ ≤ D * T)
    (hTr : T * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall
      (scalarFormalPowerSeries
        (powerSeriesDerivativeCoefficients
          (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁))).sum
      (scalarFormalPowerSeries
        (powerSeriesDerivativeCoefficients
          (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁))) 0
      (r : ENNReal) := by
  exact scalarFormalPowerSeries_derivative_hasFPowerSeriesOnBall_of_geometric_bound
    (b := schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)
    (D := D) (T := T) (r := r)
    hr hT
    (coefficientNormMajorizes_schwarzianFrobeniusCoefficientsWithInitial_geometric
      (a := a) (C := C) (D := D) (T := T) (b₀ := b₀) (b₁ := b₁)
      hC hD hT hCT ha hB₀ hB₁)
    hTr

/--
The second termwise derivative series of the recursively constructed Frobenius
solution converges under the same geometric majorant hypotheses.
-/
theorem schwarzianFrobeniusCoefficientsWithInitial_second_derivative_hasFPowerSeriesOnBall_of_geometric_majorant
    {a : ℕ → ℂ} {C D T : ℝ} {b₀ b₁ : ℂ} {r : NNReal}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hCT : C ≤ 4 * T ^ 2)
    (ha : ∀ n, ‖a n‖ ≤ C * T ^ n)
    (hB₀ : ‖b₀‖ ≤ D)
    (hB₁ : ‖b₁‖ ≤ D * T)
    (hTr : T * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall
      (scalarFormalPowerSeries
        (powerSeriesSecondDerivativeCoefficients
          (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁))).sum
      (scalarFormalPowerSeries
        (powerSeriesSecondDerivativeCoefficients
          (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁))) 0
      (r : ENNReal) := by
  exact scalarFormalPowerSeries_second_derivative_hasFPowerSeriesOnBall_of_geometric_bound
    (b := schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)
    (D := D) (T := T) (r := r)
    hr hT
    (coefficientNormMajorizes_schwarzianFrobeniusCoefficientsWithInitial_geometric
      (a := a) (C := C) (D := D) (T := T) (b₀ := b₀) (b₁ := b₁)
      hC hD hT hCT ha hB₀ hB₁)
    hTr

/--
Convergence of the normalized numerator Frobenius series with initial
coefficients `(0, 1)`.
-/
theorem schwarzianFrobeniusNumerator_hasFPowerSeriesOnBall_of_geometric_majorant
    {a : ℕ → ℂ} {C D T : ℝ} {r : NNReal}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hCT : C ≤ 4 * T ^ 2)
    (ha : ∀ n, ‖a n‖ ≤ C * T ^ n)
    (hDT_one : 1 ≤ D * T)
    (hTr : T * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall
      (scalarFormalPowerSeries
        (schwarzianFrobeniusCoefficientsWithInitial a 0 1)).sum
      (scalarFormalPowerSeries
        (schwarzianFrobeniusCoefficientsWithInitial a 0 1)) 0
      (r : ENNReal) := by
  exact schwarzianFrobeniusCoefficientsWithInitial_hasFPowerSeriesOnBall_of_geometric_majorant
    (a := a) (C := C) (D := D) (T := T) (b₀ := 0) (b₁ := 1) (r := r)
    hr hC hD hT hCT ha (by simpa using hD) (by simpa using hDT_one) hTr

/--
Convergence of the normalized denominator Frobenius series with initial
coefficients `(1, 0)`.
-/
theorem schwarzianFrobeniusDenominator_hasFPowerSeriesOnBall_of_geometric_majorant
    {a : ℕ → ℂ} {C D T : ℝ} {r : NNReal}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hCT : C ≤ 4 * T ^ 2)
    (ha : ∀ n, ‖a n‖ ≤ C * T ^ n)
    (hD_one : 1 ≤ D)
    (hTr : T * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall
      (scalarFormalPowerSeries
        (schwarzianFrobeniusCoefficientsWithInitial a 1 0)).sum
      (scalarFormalPowerSeries
        (schwarzianFrobeniusCoefficientsWithInitial a 1 0)) 0
      (r : ENNReal) := by
  exact schwarzianFrobeniusCoefficientsWithInitial_hasFPowerSeriesOnBall_of_geometric_majorant
    (a := a) (C := C) (D := D) (T := T) (b₀ := 1) (b₁ := 0) (r := r)
    hr hC hD hT hCT ha (by simpa using hD_one)
    (by simpa using mul_nonneg hD hT) hTr

/-- The `z`-domain corresponding to a centered `w = z - z₀` power-series ball. -/
def centeredBallDomain (z₀ : ℂ) (r : ENNReal) : Set ℂ :=
  {z | z - z₀ ∈ Metric.eball (0 : ℂ) r}

/-- A centered power-series ball gives an open domain in the original coordinate. -/
theorem isOpen_centeredBallDomain (z₀ : ℂ) (r : ENNReal) :
    IsOpen (centeredBallDomain z₀ r) := by
  change IsOpen ((fun z : ℂ => z - z₀) ⁻¹' Metric.eball (0 : ℂ) r)
  exact IsOpen.preimage (continuous_id.sub continuous_const) Metric.isOpen_eball

/-- The center belongs to every centered ball of positive radius. -/
theorem mem_centeredBallDomain_center {z₀ : ℂ} {r : ENNReal} (hr : 0 < r) :
    z₀ ∈ centeredBallDomain z₀ r := by
  rw [centeredBallDomain]
  simp [Metric.mem_eball, hr]

/--
Analytic realization of one centered Frobenius series.

The fields deliberately record the analytic boundary: convergence as a
`HasFPowerSeriesOnBall`, the chosen symbolic first and second derivatives, and
the ODE identity on the ball.  Later work should prove these fields from
majorant estimates and termwise differentiation of the formal series.
-/
structure CenteredSchwarzianFrobeniusSolution
    (q : ℂ → ℂ) (z₀ : ℂ) (a : ℕ → ℂ) (b₀ b₁ : ℂ) (r : ENNReal) where
  /-- The formal Frobenius coefficients. -/
  series : SchwarzianFrobeniusSeriesWithInitial a b₀ b₁
  /-- The analytic sum in the centered variable `w = z - z₀`. -/
  solution : ℂ → ℂ
  /-- The chosen first derivative of the analytic sum. -/
  solutionDeriv : ℂ → ℂ
  /-- The chosen second derivative of the analytic sum. -/
  solutionSecondDeriv : ℂ → ℂ
  /-- The Frobenius series converges to `solution` on the centered ball. -/
  has_series : HasFPowerSeriesOnBall solution (scalarFormalPowerSeries series.coeff) 0 r
  /-- The termwise first derivative series converges to `solutionDeriv`. -/
  has_deriv_series :
    HasFPowerSeriesOnBall solutionDeriv
      (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients series.coeff)) 0 r
  /-- The termwise second derivative series converges to `solutionSecondDeriv`. -/
  has_second_deriv_series :
    HasFPowerSeriesOnBall solutionSecondDeriv
      (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients series.coeff)) 0 r
  /-- The value at the center is the prescribed constant coefficient. -/
  solution_zero : solution 0 = b₀
  /-- The derivative at the center is the prescribed linear coefficient. -/
  solutionDeriv_zero : solutionDeriv 0 = b₁
  /-- The analytic sum solves the centered linear Schwarzian ODE. -/
  solves_ode : ∀ w, w ∈ Metric.eball (0 : ℂ) r →
    solutionSecondDeriv w = -((1 / 2 : ℂ) * q (z₀ + w) * solution w)

/--
A centered Frobenius solution whose first and second derivative fields are
also supplied by the termwise differentiated power series.
-/
structure CenteredSchwarzianFrobeniusTermwiseSolution
    (q : ℂ → ℂ) (z₀ : ℂ) (a : ℕ → ℂ) (b₀ b₁ : ℂ) (r : ENNReal) where
  /-- The formal Frobenius coefficients. -/
  series : SchwarzianFrobeniusSeriesWithInitial a b₀ b₁
  /-- The analytic sum in the centered variable `w = z - z₀`. -/
  solution : ℂ → ℂ
  /-- The analytic sum of the termwise first derivative. -/
  solutionDeriv : ℂ → ℂ
  /-- The analytic sum of the termwise second derivative. -/
  solutionSecondDeriv : ℂ → ℂ
  /-- The Frobenius series converges to `solution` on the centered ball. -/
  has_series : HasFPowerSeriesOnBall solution (scalarFormalPowerSeries series.coeff) 0 r
  /-- The termwise first derivative series converges to `solutionDeriv`. -/
  has_deriv_series :
    HasFPowerSeriesOnBall solutionDeriv
      (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients series.coeff)) 0 r
  /-- The termwise second derivative series converges to `solutionSecondDeriv`. -/
  has_second_deriv_series :
    HasFPowerSeriesOnBall solutionSecondDeriv
      (scalarFormalPowerSeries (powerSeriesSecondDerivativeCoefficients series.coeff)) 0 r
  /-- The value at the center is the prescribed constant coefficient. -/
  solution_zero : solution 0 = b₀
  /-- The derivative at the center is the prescribed linear coefficient. -/
  solutionDeriv_zero : solutionDeriv 0 = b₁
  /-- The analytic sum solves the centered linear Schwarzian ODE. -/
  solves_ode : ∀ w, w ∈ Metric.eball (0 : ℂ) r →
    solutionSecondDeriv w = -((1 / 2 : ℂ) * q (z₀ + w) * solution w)

/--
Build the centered termwise Frobenius solution package from geometric
majorants, leaving only the analytic ODE identity for the sums as an input.

The convergence of `y`, the termwise `y'`, and the termwise `y''`, together
with the center initial values, is supplied by the majorant estimates.
-/
noncomputable def centeredSchwarzianFrobeniusTermwiseSolutionOfGeometricMajorant
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {C D T : ℝ}
    {b₀ b₁ : ℂ} {r : NNReal}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hCT : C ≤ 4 * T ^ 2)
    (ha : ∀ n, ‖a n‖ ≤ C * T ^ n)
    (hB₀ : ‖b₀‖ ≤ D)
    (hB₁ : ‖b₁‖ ≤ D * T)
    (hTr : T * (r : ℝ) < 1)
    (hsolves : ∀ w, w ∈ Metric.eball (0 : ℂ) (r : ENNReal) →
      (scalarFormalPowerSeries
        (powerSeriesSecondDerivativeCoefficients
          (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁))).sum w =
        -((1 / 2 : ℂ) * q (z₀ + w) *
          (scalarFormalPowerSeries
            (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)).sum w)) :
    CenteredSchwarzianFrobeniusTermwiseSolution q z₀ a b₀ b₁ (r : ENNReal) where
  series := schwarzianFrobeniusSeriesWithInitial a b₀ b₁
  solution :=
    (scalarFormalPowerSeries
      (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)).sum
  solutionDeriv :=
    (scalarFormalPowerSeries
      (powerSeriesDerivativeCoefficients
        (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁))).sum
  solutionSecondDeriv :=
    (scalarFormalPowerSeries
      (powerSeriesSecondDerivativeCoefficients
        (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁))).sum
  has_series := by
    simpa [schwarzianFrobeniusSeriesWithInitial] using
      schwarzianFrobeniusCoefficientsWithInitial_hasFPowerSeriesOnBall_of_geometric_majorant
        (a := a) (C := C) (D := D) (T := T) (b₀ := b₀) (b₁ := b₁) (r := r)
        hr hC hD hT hCT ha hB₀ hB₁ hTr
  has_deriv_series := by
    simpa [schwarzianFrobeniusSeriesWithInitial] using
      schwarzianFrobeniusCoefficientsWithInitial_derivative_hasFPowerSeriesOnBall_of_geometric_majorant
        (a := a) (C := C) (D := D) (T := T) (b₀ := b₀) (b₁ := b₁) (r := r)
        hr hC hD hT hCT ha hB₀ hB₁ hTr
  has_second_deriv_series := by
    simpa [schwarzianFrobeniusSeriesWithInitial] using
      schwarzianFrobeniusCoefficientsWithInitial_second_derivative_hasFPowerSeriesOnBall_of_geometric_majorant
        (a := a) (C := C) (D := D) (T := T) (b₀ := b₀) (b₁ := b₁) (r := r)
        hr hC hD hT hCT ha hB₀ hB₁ hTr
  solution_zero := by
    have hs :=
      schwarzianFrobeniusCoefficientsWithInitial_hasFPowerSeriesOnBall_of_geometric_majorant
        (a := a) (C := C) (D := D) (T := T) (b₀ := b₀) (b₁ := b₁) (r := r)
        hr hC hD hT hCT ha hB₀ hB₁ hTr
    simpa [schwarzianFrobeniusCoefficientsWithInitial_zero] using
      scalarFormalPowerSeries_sum_zero hs
  solutionDeriv_zero := by
    have hs :=
      schwarzianFrobeniusCoefficientsWithInitial_derivative_hasFPowerSeriesOnBall_of_geometric_majorant
        (a := a) (C := C) (D := D) (T := T) (b₀ := b₀) (b₁ := b₁) (r := r)
        hr hC hD hT hCT ha hB₀ hB₁ hTr
    simpa [schwarzianFrobeniusCoefficientsWithInitial_one] using
      scalarFormalPowerSeries_derivative_sum_zero hs
  solves_ode := hsolves

/--
Build the centered termwise Frobenius solution package from geometric
majorants and the Taylor expansion of the coefficient `q`.

Compared with `centeredSchwarzianFrobeniusTermwiseSolutionOfGeometricMajorant`,
this constructor also proves the ODE identity for the sums from the formal
coefficient recurrence and the Cauchy-product theorem.
-/
noncomputable def centeredSchwarzianFrobeniusTermwiseSolutionOfGeometricMajorantAndCoefficientSeries
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {C D T : ℝ}
    {b₀ b₁ : ℂ} {r : NNReal}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hCT : C ≤ 4 * T ^ 2)
    (ha : ∀ n, ‖a n‖ ≤ C * T ^ n)
    (hB₀ : ‖b₀‖ ≤ D)
    (hB₁ : ‖b₁‖ ≤ D * T)
    (hTr : T * (r : ℝ) < 1)
    (hq : HasFPowerSeriesOnBall
      (fun w : ℂ => q (z₀ + w)) (scalarFormalPowerSeries a) 0 (r : ENNReal)) :
    CenteredSchwarzianFrobeniusTermwiseSolution q z₀ a b₀ b₁ (r : ENNReal) :=
  centeredSchwarzianFrobeniusTermwiseSolutionOfGeometricMajorant
    (q := q) (z₀ := z₀) (a := a) (C := C) (D := D) (T := T)
    (b₀ := b₀) (b₁ := b₁) (r := r)
    hr hC hD hT hCT ha hB₀ hB₁ hTr
    (by
      have hy :
          HasFPowerSeriesOnBall
            (scalarFormalPowerSeries
              (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)).sum
            (scalarFormalPowerSeries
              (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)) 0
            (r : ENNReal) :=
        schwarzianFrobeniusCoefficientsWithInitial_hasFPowerSeriesOnBall_of_geometric_majorant
          (a := a) (C := C) (D := D) (T := T) (b₀ := b₀) (b₁ := b₁) (r := r)
          hr hC hD hT hCT ha hB₀ hB₁ hTr
      have hdd :
          HasFPowerSeriesOnBall
            (scalarFormalPowerSeries
              (powerSeriesSecondDerivativeCoefficients
                (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁))).sum
            (scalarFormalPowerSeries
              (powerSeriesSecondDerivativeCoefficients
                (schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁))) 0
            (r : ENNReal) :=
        schwarzianFrobeniusCoefficientsWithInitial_second_derivative_hasFPowerSeriesOnBall_of_geometric_majorant
          (a := a) (C := C) (D := D) (T := T) (b₀ := b₀) (b₁ := b₁) (r := r)
          hr hC hD hT hCT ha hB₀ hB₁ hTr
      exact schwarzianFrobenius_sum_ode_identityOnBall_of_recurrence
        (q := q) (z₀ := z₀) (a := a)
        (b := schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁)
        hq hy hdd
        (SchwarzianFrobeniusSeriesWithInitial.solves_recurrence
          (schwarzianFrobeniusSeriesWithInitial a b₀ b₁)))

namespace CenteredSchwarzianFrobeniusSolution

/-- Restrict a centered Frobenius solution to a smaller positive radius. -/
def restrict
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r r' : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r)
    (hr' : 0 < r') (hle : r' ≤ r) :
    CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r' where
  series := Y.series
  solution := Y.solution
  solutionDeriv := Y.solutionDeriv
  solutionSecondDeriv := Y.solutionSecondDeriv
  has_series := Y.has_series.mono hr' hle
  has_deriv_series := Y.has_deriv_series.mono hr' hle
  has_second_deriv_series := Y.has_second_deriv_series.mono hr' hle
  solution_zero := Y.solution_zero
  solutionDeriv_zero := Y.solutionDeriv_zero
  solves_ode := by
    intro w hw
    exact Y.solves_ode w (Metric.eball_subset_eball hle hw)

/-- A centered Frobenius solution is continuous at every point of its ball. -/
theorem solution_continuousAt
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r)
    {w : ℂ} (hw : w ∈ Metric.eball (0 : ℂ) r) :
    ContinuousAt Y.solution w :=
  Y.has_series.continuousOn.continuousAt (Metric.isOpen_eball.mem_nhds hw)

/-- The scalar termwise-derivative theorem gives the actual stored derivative. -/
theorem solution_hasDerivAt_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem)
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r)
    {w : ℂ} (hw : w ∈ Metric.eball (0 : ℂ) r) :
    HasDerivAt Y.solution (Y.solutionDeriv w) w := by
  have hderiv_series :
      HasFPowerSeriesOnBall (deriv Y.solution)
        (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients Y.series.coeff)) 0 r :=
    hScalarDeriv Y.has_series
  have hderiv_eq :
      deriv Y.solution w = Y.solutionDeriv w :=
    hderiv_series.unique Y.has_deriv_series hw
  have hactual : HasDerivAt Y.solution (deriv Y.solution w) w :=
    (Y.has_series.analyticAt_of_mem hw).hasStrictDerivAt.hasDerivAt
  simpa [hderiv_eq] using hactual

/--
The scalar termwise-derivative theorem applied to the stored first-derivative
series gives the stored second derivative.
-/
theorem solutionDeriv_hasDerivAt_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem)
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r)
    {w : ℂ} (hw : w ∈ Metric.eball (0 : ℂ) r) :
    HasDerivAt Y.solutionDeriv (Y.solutionSecondDeriv w) w := by
  have hderiv_series :
      HasFPowerSeriesOnBall (deriv Y.solutionDeriv)
        (scalarFormalPowerSeries
          (powerSeriesDerivativeCoefficients
            (powerSeriesDerivativeCoefficients Y.series.coeff))) 0 r :=
    hScalarDeriv Y.has_deriv_series
  rw [powerSeriesDerivativeCoefficients_derivative] at hderiv_series
  have hderiv_eq :
      deriv Y.solutionDeriv w = Y.solutionSecondDeriv w :=
    hderiv_series.unique Y.has_second_deriv_series hw
  have hactual : HasDerivAt Y.solutionDeriv (deriv Y.solutionDeriv w) w :=
    (Y.has_deriv_series.analyticAt_of_mem hw).hasStrictDerivAt.hasDerivAt
  simpa [hderiv_eq] using hactual

end CenteredSchwarzianFrobeniusSolution

/--
Analytic derivative boundary for one centered Frobenius solution.

This is the next small red piece below the quotient rule: the solution is a
convergent scalar power series and `solutionDeriv` is its termwise derivative
series, so this should eventually be proved from mathlib's power-series
differentiation API.
-/
def CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem : Prop :=
  ∀ {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r)
    ⦃w : ℂ⦄,
      w ∈ Metric.eball (0 : ℂ) r →
        HasDerivAt Y.solution (Y.solutionDeriv w) w

/--
Analytic second-derivative boundary for one centered Frobenius solution after
forgetting termwise data.

The termwise package proves this directly; this proposition is the form needed
after a normalized Frobenius pair has been harmlessly shrunk.
-/
def CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem : Prop :=
  ∀ {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r)
    ⦃w : ℂ⦄,
      w ∈ Metric.eball (0 : ℂ) r →
        HasDerivAt Y.solutionDeriv (Y.solutionSecondDeriv w) w

/--
The scalar termwise-derivative theorem proves the centered Frobenius solution
derivative theorem.
-/
theorem centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem) :
    CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem := by
  intro q z₀ a b₀ b₁ r Y w hw
  exact Y.solution_hasDerivAt_of_scalarFormalPowerSeriesDeriv hScalarDeriv hw

/-- Centered Frobenius solutions have the stored termwise derivative as their actual derivative. -/
theorem centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem :
    CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem :=
  centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem

/-- The scalar power-series derivative theorem proves the centered second derivative. -/
theorem centeredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem) :
    CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem := by
  intro q z₀ a b₀ b₁ r Y w hw
  exact Y.solutionDeriv_hasDerivAt_of_scalarFormalPowerSeriesDeriv hScalarDeriv hw

/-- Centered Frobenius first-derivative fields have the stored second derivative. -/
theorem centeredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem :
    CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem :=
  centeredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem

/--
A scalar complex power series on a ball is `C^3` when viewed as a real map.

Mathlib gives analyticity at every point of the convergence ball.  The final
step is restriction of scalars from complex to real differentiability; the
explicit application avoids a typeclass search corner for `ℂ` as both source
and target.
-/
theorem hasFPowerSeriesOnBall_contDiffOn_real_three
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ENNReal}
    (hf : HasFPowerSeriesOnBall f p 0 r) :
    ContDiffOn ℝ 3 f (Metric.eball (0 : ℂ) r) := by
  rw [Metric.isOpen_eball.contDiffOn_iff]
  intro z hz
  have hC : ContDiffAt ℂ 3 f z :=
    (hf.analyticAt_of_mem hz).contDiffAt
  exact
    @ContDiffAt.restrict_scalars ℝ inferInstance ℂ inferInstance
      inferInstance ℂ inferInstance inferInstance f z 3 ℂ inferInstance
      inferInstance inferInstance
      (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ) inferInstance
      (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ) hC

namespace CenteredSchwarzianFrobeniusSolution

/-- The analytic Frobenius sum is `C^3` on its centered convergence ball. -/
theorem solution_contDiffOn
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r) :
    ContDiffOn ℝ 3 Y.solution (Metric.eball (0 : ℂ) r) :=
  hasFPowerSeriesOnBall_contDiffOn_real_three Y.has_series

/-- The stored first-derivative Frobenius sum is `C^3` on the centered ball. -/
theorem solutionDeriv_contDiffOn
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r) :
    ContDiffOn ℝ 3 Y.solutionDeriv (Metric.eball (0 : ℂ) r) :=
  hasFPowerSeriesOnBall_contDiffOn_real_three Y.has_deriv_series

/-- The stored second-derivative Frobenius sum is `C^3` on the centered ball. -/
theorem solutionSecondDeriv_contDiffOn
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r) :
    ContDiffOn ℝ 3 Y.solutionSecondDeriv (Metric.eball (0 : ℂ) r) :=
  hasFPowerSeriesOnBall_contDiffOn_real_three Y.has_second_deriv_series

/-- The analytic Frobenius sum is `C^3` after recentering at `z₀`. -/
theorem solution_comp_sub_contDiffOn
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ Y.solution (z - z₀)) (centeredBallDomain z₀ r) := by
  have hsub : ContDiffOn ℝ 3 (fun z : ℂ ↦ z - z₀) (centeredBallDomain z₀ r) :=
    (contDiff_id.sub contDiff_const).contDiffOn
  have hmap :
      Set.MapsTo (fun z : ℂ ↦ z - z₀) (centeredBallDomain z₀ r)
        (Metric.eball (0 : ℂ) r) := by
    intro z hz
    exact hz
  simpa [Function.comp_def] using Y.solution_contDiffOn.comp hsub hmap

/-- The stored first derivative is `C^3` after recentering at `z₀`. -/
theorem solutionDeriv_comp_sub_contDiffOn
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ Y.solutionDeriv (z - z₀))
      (centeredBallDomain z₀ r) := by
  have hsub : ContDiffOn ℝ 3 (fun z : ℂ ↦ z - z₀) (centeredBallDomain z₀ r) :=
    (contDiff_id.sub contDiff_const).contDiffOn
  have hmap :
      Set.MapsTo (fun z : ℂ ↦ z - z₀) (centeredBallDomain z₀ r)
        (Metric.eball (0 : ℂ) r) := by
    intro z hz
    exact hz
  simpa [Function.comp_def] using Y.solutionDeriv_contDiffOn.comp hsub hmap

/-- The stored second derivative is `C^3` after recentering at `z₀`. -/
theorem solutionSecondDeriv_comp_sub_contDiffOn
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ Y.solutionSecondDeriv (z - z₀))
      (centeredBallDomain z₀ r) := by
  have hsub : ContDiffOn ℝ 3 (fun z : ℂ ↦ z - z₀) (centeredBallDomain z₀ r) :=
    (contDiff_id.sub contDiff_const).contDiffOn
  have hmap :
      Set.MapsTo (fun z : ℂ ↦ z - z₀) (centeredBallDomain z₀ r)
        (Metric.eball (0 : ℂ) r) := by
    intro z hz
    exact hz
  simpa [Function.comp_def] using Y.solutionSecondDeriv_contDiffOn.comp hsub hmap

end CenteredSchwarzianFrobeniusSolution

namespace CenteredSchwarzianFrobeniusTermwiseSolution

/-- Forget the termwise derivative series, retaining the centered Frobenius solution. -/
def toCenteredSchwarzianFrobeniusSolution
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusTermwiseSolution q z₀ a b₀ b₁ r) :
    CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r where
  series := Y.series
  solution := Y.solution
  solutionDeriv := Y.solutionDeriv
  solutionSecondDeriv := Y.solutionSecondDeriv
  has_series := Y.has_series
  has_deriv_series := Y.has_deriv_series
  has_second_deriv_series := Y.has_second_deriv_series
  solution_zero := Y.solution_zero
  solutionDeriv_zero := Y.solutionDeriv_zero
  solves_ode := Y.solves_ode

/-- The first derivative field is continuous at the center. -/
theorem solutionDeriv_continuousAt
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusTermwiseSolution q z₀ a b₀ b₁ r) :
    ContinuousAt Y.solutionDeriv 0 :=
  Y.has_deriv_series.hasFPowerSeriesAt.continuousAt

/--
The scalar termwise-derivative theorem applied to the first-derivative series
gives the stored second derivative.
-/
theorem solutionDeriv_hasDerivAt_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem)
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusTermwiseSolution q z₀ a b₀ b₁ r)
    {w : ℂ} (hw : w ∈ Metric.eball (0 : ℂ) r) :
    HasDerivAt Y.solutionDeriv (Y.solutionSecondDeriv w) w := by
  have hderiv_series :
      HasFPowerSeriesOnBall (deriv Y.solutionDeriv)
        (scalarFormalPowerSeries
          (powerSeriesDerivativeCoefficients
            (powerSeriesDerivativeCoefficients Y.series.coeff))) 0 r :=
    hScalarDeriv Y.has_deriv_series
  rw [powerSeriesDerivativeCoefficients_derivative] at hderiv_series
  have hderiv_eq :
      deriv Y.solutionDeriv w = Y.solutionSecondDeriv w :=
    hderiv_series.unique Y.has_second_deriv_series hw
  have hactual : HasDerivAt Y.solutionDeriv (deriv Y.solutionDeriv w) w :=
    (Y.has_deriv_series.analyticAt_of_mem hw).hasStrictDerivAt.hasDerivAt
  simpa [hderiv_eq] using hactual

end CenteredSchwarzianFrobeniusTermwiseSolution

/--
Analytic second-derivative boundary for one termwise centered Frobenius
solution.

This says the stored first-derivative sum has the stored second derivative on
the convergence ball.
-/
def CenteredSchwarzianFrobeniusTermwiseSolutionDerivHasDerivAtTheorem : Prop :=
  ∀ {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusTermwiseSolution q z₀ a b₀ b₁ r),
    ∀ {w : ℂ}, w ∈ Metric.eball (0 : ℂ) r →
      HasDerivAt Y.solutionDeriv (Y.solutionSecondDeriv w) w

/-- The scalar power-series derivative theorem proves the termwise second derivative. -/
theorem centeredSchwarzianFrobeniusTermwiseSolutionDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem) :
    CenteredSchwarzianFrobeniusTermwiseSolutionDerivHasDerivAtTheorem := by
  intro q z₀ a b₀ b₁ r Y w hw
  exact Y.solutionDeriv_hasDerivAt_of_scalarFormalPowerSeriesDeriv hScalarDeriv hw

/-- The termwise Frobenius first derivative has the stored second derivative. -/
theorem centeredSchwarzianFrobeniusTermwiseSolutionDerivHasDerivAtTheorem :
    CenteredSchwarzianFrobeniusTermwiseSolutionDerivHasDerivAtTheorem :=
  centeredSchwarzianFrobeniusTermwiseSolutionDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem

/--
A centered convergent Frobenius pair before the harmless shrinking needed to
make the denominator and Wronskian nonzero on the whole ball.
-/
structure CenteredNormalizedSchwarzianFrobeniusPrePair
    (q : ℂ → ℂ) (V : Set ℂ) (z₀ : ℂ) (a : ℕ → ℂ) where
  /-- Radius of the centered power-series ball. -/
  radius : ENNReal
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- The coefficient `q(z₀+w)` has the chosen Taylor/Frobenius coefficients. -/
  coefficient_has_series :
    HasFPowerSeriesOnBall (fun w ↦ q (z₀ + w)) (scalarFormalPowerSeries a) 0 radius
  /-- The numerator solution has initial data `(0,1)`. -/
  numerator : CenteredSchwarzianFrobeniusSolution q z₀ a 0 1 radius
  /-- The denominator solution has initial data `(1,0)`. -/
  denominator : CenteredSchwarzianFrobeniusSolution q z₀ a 1 0 radius
  /-- The centered ball stays inside the ambient coordinate domain. -/
  domain_subset : centeredBallDomain z₀ radius ⊆ V

/--
A centered Frobenius pre-pair whose two solutions come with termwise
differentiated power-series data.
-/
structure CenteredNormalizedSchwarzianFrobeniusTermwisePrePair
    (q : ℂ → ℂ) (V : Set ℂ) (z₀ : ℂ) (a : ℕ → ℂ) where
  /-- Radius of the centered power-series ball. -/
  radius : ENNReal
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- The coefficient `q(z₀+w)` has the chosen Taylor/Frobenius coefficients. -/
  coefficient_has_series :
    HasFPowerSeriesOnBall (fun w ↦ q (z₀ + w)) (scalarFormalPowerSeries a) 0 radius
  /-- The numerator solution has initial data `(0,1)`. -/
  numerator : CenteredSchwarzianFrobeniusTermwiseSolution q z₀ a 0 1 radius
  /-- The denominator solution has initial data `(1,0)`. -/
  denominator : CenteredSchwarzianFrobeniusTermwiseSolution q z₀ a 1 0 radius
  /-- The centered ball stays inside the ambient coordinate domain. -/
  domain_subset : centeredBallDomain z₀ radius ⊆ V

/--
Construct the normalized termwise Frobenius pre-pair from one geometric
majorant for the coefficient series and the two normalized initial conditions.

The local analytic choices at this constructor level are explicit: a radius
inside the coordinate domain, a Taylor series for `q(z₀ + w)` on that radius,
and geometric coefficient bounds on that Taylor series.  Later bridge theorems
derive this data from the holomorphicity stored in `LocalSchwarzianData`.
-/
noncomputable def centeredNormalizedSchwarzianFrobeniusTermwisePrePairOfGeometricMajorant
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {C D T : ℝ} {r : NNReal}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hCT : C ≤ 4 * T ^ 2)
    (ha : ∀ n, ‖a n‖ ≤ C * T ^ n)
    (hD_one : 1 ≤ D)
    (hDT_one : 1 ≤ D * T)
    (hTr : T * (r : ℝ) < 1)
    (hq : HasFPowerSeriesOnBall
      (fun w : ℂ => q (z₀ + w)) (scalarFormalPowerSeries a) 0 (r : ENNReal))
    (hDomain : centeredBallDomain z₀ (r : ENNReal) ⊆ V) :
    CenteredNormalizedSchwarzianFrobeniusTermwisePrePair q V z₀ a where
  radius := (r : ENNReal)
  radius_pos := by exact_mod_cast hr
  coefficient_has_series := hq
  numerator :=
    centeredSchwarzianFrobeniusTermwiseSolutionOfGeometricMajorantAndCoefficientSeries
      (q := q) (z₀ := z₀) (a := a) (C := C) (D := D) (T := T)
      (b₀ := 0) (b₁ := 1) (r := r)
      hr hC hD hT hCT ha (by simpa using hD) (by simpa using hDT_one) hTr hq
  denominator :=
    centeredSchwarzianFrobeniusTermwiseSolutionOfGeometricMajorantAndCoefficientSeries
      (q := q) (z₀ := z₀) (a := a) (C := C) (D := D) (T := T)
      (b₀ := 1) (b₁ := 0) (r := r)
      hr hC hD hT hCT ha (by simpa using hD_one) (by simpa using mul_nonneg hD hT)
      hTr hq
  domain_subset := hDomain

namespace CenteredNormalizedSchwarzianFrobeniusTermwisePrePair

/-- Forget termwise derivative data, retaining the centered Frobenius pre-pair. -/
def toPrePair
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusTermwisePrePair q V z₀ a) :
    CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a where
  radius := P.radius
  radius_pos := P.radius_pos
  coefficient_has_series := P.coefficient_has_series
  numerator := P.numerator.toCenteredSchwarzianFrobeniusSolution
  denominator := P.denominator.toCenteredSchwarzianFrobeniusSolution
  domain_subset := P.domain_subset

end CenteredNormalizedSchwarzianFrobeniusTermwisePrePair

namespace CenteredNormalizedSchwarzianFrobeniusPrePair

/-- The centered Wronskian of the two Frobenius solutions. -/
def wronskian
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) : ℂ → ℂ :=
  fun w ↦
    P.numerator.solutionDeriv w * P.denominator.solution w -
      P.numerator.solution w * P.denominator.solutionDeriv w

/-- The denominator has value `1` at the center. -/
theorem denominator_zero_eq_one
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.denominator.solution 0 = 1 :=
  P.denominator.solution_zero

/-- The numerator has value `0` at the center. -/
theorem numerator_zero_eq_zero
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.numerator.solution 0 = 0 :=
  P.numerator.solution_zero

/-- The denominator derivative has value `0` at the center. -/
theorem denominatorDeriv_zero_eq_zero
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.denominator.solutionDeriv 0 = 0 :=
  P.denominator.solutionDeriv_zero

/-- The numerator derivative has value `1` at the center. -/
theorem numeratorDeriv_zero_eq_one
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.numerator.solutionDeriv 0 = 1 :=
  P.numerator.solutionDeriv_zero

/-- The centered Wronskian has value `1` at the center. -/
theorem wronskian_zero_eq_one
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.wronskian 0 = 1 := by
  rw [wronskian, P.numeratorDeriv_zero_eq_one, P.denominator_zero_eq_one,
    P.numerator_zero_eq_zero, P.denominatorDeriv_zero_eq_zero]
  ring

/-- The denominator is nonzero at the center. -/
theorem denominator_ne_zero_at_zero
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.denominator.solution 0 ≠ 0 := by
  rw [P.denominator_zero_eq_one]
  norm_num

/-- The Wronskian is nonzero at the center. -/
theorem wronskian_ne_zero_at_zero
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.wronskian 0 ≠ 0 := by
  rw [P.wronskian_zero_eq_one]
  norm_num

/-- Restrict a centered Frobenius pre-pair to a smaller positive radius. -/
def restrict
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {r' : ENNReal}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a)
    (hr' : 0 < r') (hle : r' ≤ P.radius) :
    CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a where
  radius := r'
  radius_pos := hr'
  coefficient_has_series := P.coefficient_has_series.mono hr' hle
  numerator := P.numerator.restrict hr' hle
  denominator := P.denominator.restrict hr' hle
  domain_subset := by
    intro z hz
    exact P.domain_subset (Metric.eball_subset_eball hle hz)

end CenteredNormalizedSchwarzianFrobeniusPrePair

/--
Data witnessing the standard shrinking step: from a centered Frobenius pre-pair,
choose a smaller positive radius on which the denominator and Wronskian are
nonzero.
-/
structure CenteredFrobeniusNonvanishingShrink
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) where
  /-- The smaller radius. -/
  radius : ENNReal
  /-- The smaller radius is positive. -/
  radius_pos : 0 < radius
  /-- The smaller radius lies inside the original convergence radius. -/
  radius_le : radius ≤ P.radius
  /-- The denominator is nonzero on the smaller ball. -/
  denominator_ne_zero : ∀ w, w ∈ Metric.eball (0 : ℂ) radius →
    P.denominator.solution w ≠ 0
  /-- The Wronskian is nonzero on the smaller ball. -/
  wronskian_ne_zero : ∀ w, w ∈ Metric.eball (0 : ℂ) radius →
    P.wronskian w ≠ 0

/--
The remaining shrinking theorem target.  Analytically this follows from
continuity of the denominator and Wronskian and the center identities
`denominator(0)=1`, `Wronskian(0)=1`.
-/
def CenteredFrobeniusNonvanishingShrinkTheorem : Prop :=
  ∀ {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a),
      Nonempty (CenteredFrobeniusNonvanishingShrink P)

/--
Continuity data needed for the nonvanishing shrink.  The solution functions
themselves are continuous at the center because they are given by power
series; the first-derivative fields require the termwise-differentiation step.
-/
structure CenteredFrobeniusDerivativeContinuity
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) where
  /-- The numerator first-derivative field is continuous at the center. -/
  numeratorDeriv_continuousAt : ContinuousAt P.numerator.solutionDeriv 0
  /-- The denominator first-derivative field is continuous at the center. -/
  denominatorDeriv_continuousAt : ContinuousAt P.denominator.solutionDeriv 0

namespace CenteredNormalizedSchwarzianFrobeniusTermwisePrePair

/-- A termwise pre-pair supplies the derivative-continuity data needed for shrinking. -/
def derivativeContinuity
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusTermwisePrePair q V z₀ a) :
    CenteredFrobeniusDerivativeContinuity P.toPrePair where
  numeratorDeriv_continuousAt := P.numerator.solutionDeriv_continuousAt
  denominatorDeriv_continuousAt := P.denominator.solutionDeriv_continuousAt

end CenteredNormalizedSchwarzianFrobeniusTermwisePrePair

namespace CenteredFrobeniusDerivativeContinuity

/-- The denominator solution is continuous at the center. -/
theorem denominator_continuousAt
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    {P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a}
    (_C : CenteredFrobeniusDerivativeContinuity P) :
    ContinuousAt P.denominator.solution 0 :=
  P.denominator.has_series.hasFPowerSeriesAt.continuousAt

/-- The numerator solution is continuous at the center. -/
theorem numerator_continuousAt
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    {P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a}
    (_C : CenteredFrobeniusDerivativeContinuity P) :
    ContinuousAt P.numerator.solution 0 :=
  P.numerator.has_series.hasFPowerSeriesAt.continuousAt

/-- The centered Wronskian is continuous at the center. -/
theorem wronskian_continuousAt
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    {P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a}
    (C : CenteredFrobeniusDerivativeContinuity P) :
    ContinuousAt P.wronskian 0 := by
  change ContinuousAt
    (fun w ↦
      P.numerator.solutionDeriv w * P.denominator.solution w -
        P.numerator.solution w * P.denominator.solutionDeriv w) 0
  exact
    (C.numeratorDeriv_continuousAt.mul C.denominator_continuousAt).sub
      (C.numerator_continuousAt.mul C.denominatorDeriv_continuousAt)

end CenteredFrobeniusDerivativeContinuity

/--
Continuity at the center implies the nonvanishing shrinking step.

The proof uses `denominator(0)=1` and `Wronskian(0)=1`, then chooses a small
positive radius contained in the original convergence ball.
-/
theorem centeredFrobeniusNonvanishingShrink_of_derivativeContinuity
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a)
    (C : CenteredFrobeniusDerivativeContinuity P) :
    Nonempty (CenteredFrobeniusNonvanishingShrink P) := by
  have hden_eventually :
      ∀ᶠ w : ℂ in nhds 0, P.denominator.solution w ≠ 0 :=
    C.denominator_continuousAt.eventually_ne P.denominator_ne_zero_at_zero
  have hwronskian_eventually :
      ∀ᶠ w : ℂ in nhds 0, P.wronskian w ≠ 0 :=
    C.wronskian_continuousAt.eventually_ne P.wronskian_ne_zero_at_zero
  rcases Metric.eventually_nhds_iff.mp
      (hden_eventually.and hwronskian_eventually) with
    ⟨ε, hεpos, hε⟩
  let ρ : ENNReal := min (ENNReal.ofReal ε) P.radius
  have hρpos : 0 < ρ := by
    exact lt_min (ENNReal.ofReal_pos.mpr hεpos) P.radius_pos
  have hρle : ρ ≤ P.radius := by
    exact min_le_right _ _
  refine ⟨CenteredFrobeniusNonvanishingShrink.mk ρ hρpos hρle ?_ ?_⟩
  · intro w hw
    have hwed : edist w 0 < ENNReal.ofReal ε :=
      lt_of_lt_of_le hw (min_le_left _ _)
    have hdist : dist w 0 < ε := by
      rwa [edist_lt_ofReal] at hwed
    exact (hε hdist).1
  · intro w hw
    have hwed : edist w 0 < ENNReal.ofReal ε :=
      lt_of_lt_of_le hw (min_le_left _ _)
    have hdist : dist w 0 < ε := by
      rwa [edist_lt_ofReal] at hwed
    exact (hε hdist).2

/-- Derivative-continuity data for every pre-pair implies the shrinking theorem. -/
def centeredFrobeniusNonvanishingShrinkTheorem_of_derivativeContinuity
    (h :
      ∀ {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
        (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a),
          Nonempty (CenteredFrobeniusDerivativeContinuity P)) :
    CenteredFrobeniusNonvanishingShrinkTheorem := by
  intro q V z₀ a P
  rcases h P with ⟨C⟩
  exact centeredFrobeniusNonvanishingShrink_of_derivativeContinuity P C

namespace CenteredNormalizedSchwarzianFrobeniusPrePair

/--
Every centered Frobenius pre-pair has the derivative-continuity data needed
for the nonvanishing shrink, since the first-derivative fields are themselves
given by convergent power series.
-/
def derivativeContinuity
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    CenteredFrobeniusDerivativeContinuity P where
  numeratorDeriv_continuousAt :=
    P.numerator.has_deriv_series.hasFPowerSeriesAt.continuousAt
  denominatorDeriv_continuousAt :=
    P.denominator.has_deriv_series.hasFPowerSeriesAt.continuousAt

end CenteredNormalizedSchwarzianFrobeniusPrePair

/-- Every centered Frobenius pre-pair admits the standard nonvanishing shrink. -/
theorem centeredFrobeniusNonvanishingShrinkTheorem :
    CenteredFrobeniusNonvanishingShrinkTheorem :=
  centeredFrobeniusNonvanishingShrinkTheorem_of_derivativeContinuity
    (fun P => ⟨P.derivativeContinuity⟩)

/--
A centered convergent Frobenius pair with normalized numerator and denominator
initial data, already shrunk so the denominator and Wronskian are nonzero.
-/
structure CenteredNormalizedSchwarzianFrobeniusPair
    (q : ℂ → ℂ) (V : Set ℂ) (z₀ : ℂ) (a : ℕ → ℂ) where
  /-- Radius of the centered power-series ball. -/
  radius : ENNReal
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- The coefficient `q(z₀+w)` has the chosen Taylor/Frobenius coefficients. -/
  coefficient_has_series :
    HasFPowerSeriesOnBall (fun w ↦ q (z₀ + w)) (scalarFormalPowerSeries a) 0 radius
  /-- The numerator solution has initial data `(0,1)`. -/
  numerator : CenteredSchwarzianFrobeniusSolution q z₀ a 0 1 radius
  /-- The denominator solution has initial data `(1,0)`. -/
  denominator : CenteredSchwarzianFrobeniusSolution q z₀ a 1 0 radius
  /-- The centered ball stays inside the ambient coordinate domain. -/
  domain_subset : centeredBallDomain z₀ radius ⊆ V
  /-- The denominator is nonzero on the chosen centered ball. -/
  denominator_ne_zero : ∀ w, w ∈ Metric.eball (0 : ℂ) radius →
    denominator.solution w ≠ 0
  /-- The Wronskian is nonzero on the chosen centered ball. -/
  wronskian_ne_zero : ∀ w, w ∈ Metric.eball (0 : ℂ) radius →
    numerator.solutionDeriv w * denominator.solution w -
      numerator.solution w * denominator.solutionDeriv w ≠ 0

namespace CenteredNormalizedSchwarzianFrobeniusPair

/--
Shrink a centered Frobenius pre-pair using nonvanishing data for the
denominator and Wronskian.
-/
def ofPrePairShrink
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a)
    (N : CenteredFrobeniusNonvanishingShrink P) :
    CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a where
  radius := N.radius
  radius_pos := N.radius_pos
  coefficient_has_series := P.coefficient_has_series.mono N.radius_pos N.radius_le
  numerator := P.numerator.restrict N.radius_pos N.radius_le
  denominator := P.denominator.restrict N.radius_pos N.radius_le
  domain_subset := by
    intro z hz
    exact P.domain_subset (Metric.eball_subset_eball N.radius_le hz)
  denominator_ne_zero := N.denominator_ne_zero
  wronskian_ne_zero := by
    intro w hw
    exact N.wronskian_ne_zero w hw

/--
The affine ratio `y₁/y₀` associated to a centered Frobenius pair is continuous
at every point of its centered domain.
-/
theorem localMap_continuousAt
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a)
    {z : ℂ} (hz : z ∈ centeredBallDomain z₀ P.radius) :
    ContinuousAt
      (fun z ↦ P.numerator.solution (z - z₀) /
        P.denominator.solution (z - z₀)) z := by
  have hsub : ContinuousAt (fun z : ℂ => z - z₀) z :=
    continuousAt_id.sub continuousAt_const
  have hw : z - z₀ ∈ Metric.eball (0 : ℂ) P.radius := hz
  have hnum_comp :
      ContinuousAt (P.numerator.solution ∘ (fun z : ℂ => z - z₀)) z :=
    ContinuousAt.comp (x := z) (f := fun x : ℂ => x - z₀)
      (g := P.numerator.solution)
      (CenteredSchwarzianFrobeniusSolution.solution_continuousAt
        (Y := P.numerator) (w := z - z₀) hw)
      hsub
  have hnum :
      ContinuousAt (fun z ↦ P.numerator.solution (z - z₀)) z := by
    simpa [Function.comp_def] using hnum_comp
  have hden_comp :
      ContinuousAt (P.denominator.solution ∘ (fun z : ℂ => z - z₀)) z :=
    ContinuousAt.comp (x := z) (f := fun x : ℂ => x - z₀)
      (g := P.denominator.solution)
      (CenteredSchwarzianFrobeniusSolution.solution_continuousAt
        (Y := P.denominator) (w := z - z₀) hw)
      hsub
  have hden :
      ContinuousAt (fun z ↦ P.denominator.solution (z - z₀)) z := by
    simpa [Function.comp_def] using hden_comp
  exact hnum.div hden (P.denominator_ne_zero (z - z₀) hz)

/-- The numerator Frobenius solution, recentered on the coordinate domain, is `C^3`. -/
theorem numerator_comp_contDiffOn
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ P.numerator.solution (z - z₀))
      (centeredBallDomain z₀ P.radius) :=
  P.numerator.solution_comp_sub_contDiffOn

/-- The denominator Frobenius solution, recentered on the coordinate domain, is `C^3`. -/
theorem denominator_comp_contDiffOn
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ P.denominator.solution (z - z₀))
      (centeredBallDomain z₀ P.radius) :=
  P.denominator.solution_comp_sub_contDiffOn

/-- The numerator first-derivative Frobenius field, recentered, is `C^3`. -/
theorem numeratorDeriv_comp_contDiffOn
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ P.numerator.solutionDeriv (z - z₀))
      (centeredBallDomain z₀ P.radius) :=
  P.numerator.solutionDeriv_comp_sub_contDiffOn

/-- The denominator first-derivative Frobenius field, recentered, is `C^3`. -/
theorem denominatorDeriv_comp_contDiffOn
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ P.denominator.solutionDeriv (z - z₀))
      (centeredBallDomain z₀ P.radius) :=
  P.denominator.solutionDeriv_comp_sub_contDiffOn

/-- The Frobenius quotient map `y₁ / y₀` is `C^3` on its centered domain. -/
theorem localMap_contDiffOn
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦
        P.numerator.solution (z - z₀) / P.denominator.solution (z - z₀))
      (centeredBallDomain z₀ P.radius) := by
  simpa [div_eq_mul_inv] using
    P.numerator_comp_contDiffOn.mul
      (P.denominator_comp_contDiffOn.inv (by
        intro z hz
        exact P.denominator_ne_zero (z - z₀) hz))

/--
The canonical first derivative of the Frobenius quotient map is `C^3` on its
centered domain.
-/
theorem localMapDeriv_contDiffOn
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦
        ((P.numerator.solutionDeriv (z - z₀) *
              P.denominator.solution (z - z₀) -
            P.numerator.solution (z - z₀) *
              P.denominator.solutionDeriv (z - z₀)) /
          P.denominator.solution (z - z₀) ^ 2))
      (centeredBallDomain z₀ P.radius) := by
  have hW :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦
          P.numerator.solutionDeriv (z - z₀) *
              P.denominator.solution (z - z₀) -
            P.numerator.solution (z - z₀) *
              P.denominator.solutionDeriv (z - z₀))
        (centeredBallDomain z₀ P.radius) :=
    (P.numeratorDeriv_comp_contDiffOn.mul P.denominator_comp_contDiffOn).sub
      (P.numerator_comp_contDiffOn.mul P.denominatorDeriv_comp_contDiffOn)
  have hDenSq :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ P.denominator.solution (z - z₀) ^ 2)
        (centeredBallDomain z₀ P.radius) :=
    P.denominator_comp_contDiffOn.pow 2
  simpa [div_eq_mul_inv] using
    hW.mul
      (hDenSq.inv (by
        intro z hz
        exact pow_ne_zero 2 (P.denominator_ne_zero (z - z₀) hz)))

/--
If the two centered Frobenius solution functions have their stored actual
derivatives, then their quotient has the canonical Wronskian-over-square
derivative.
-/
theorem localMap_hasDerivAt_of_solutionHasDerivAt
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a)
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem)
    {z : ℂ} (hz : z ∈ centeredBallDomain z₀ P.radius) :
    HasDerivAt
      (fun z ↦ P.numerator.solution (z - z₀) /
        P.denominator.solution (z - z₀))
      ((P.numerator.solutionDeriv (z - z₀) *
            P.denominator.solution (z - z₀) -
          P.numerator.solution (z - z₀) *
            P.denominator.solutionDeriv (z - z₀)) /
        P.denominator.solution (z - z₀) ^ 2) z := by
  let w : ℂ := z - z₀
  have hw : w ∈ Metric.eball (0 : ℂ) P.radius := by
    change z - z₀ ∈ Metric.eball (0 : ℂ) P.radius
    exact hz
  have hsub : HasDerivAt (fun z : ℂ => z - z₀) 1 z :=
    (hasDerivAt_id' z).sub_const z₀
  have hnum_w :
      HasDerivAt P.numerator.solution (P.numerator.solutionDeriv w) w :=
    hSolDeriv P.numerator hw
  have hden_w :
      HasDerivAt P.denominator.solution (P.denominator.solutionDeriv w) w :=
    hSolDeriv P.denominator hw
  have hnum :
      HasDerivAt (fun z : ℂ => P.numerator.solution (z - z₀))
        (P.numerator.solutionDeriv w) z := by
    simpa [w, one_mul] using hnum_w.comp z hsub
  have hden :
      HasDerivAt (fun z : ℂ => P.denominator.solution (z - z₀))
        (P.denominator.solutionDeriv w) z := by
    simpa [w, one_mul] using hden_w.comp z hsub
  simpa [w] using
    hnum.fun_div hden (P.denominator_ne_zero w hw)

/--
A convergent centered normalized Frobenius pair gives the normalized local
solution pair required by the Schwarzian ODE construction.
-/
def toNormalizedSchwarzianLinearODESolutionPair
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    NormalizedSchwarzianLinearODESolutionPair q
      (centeredBallDomain z₀ P.radius) z₀ where
  numerator := fun z ↦ P.numerator.solution (z - z₀)
  denominator := fun z ↦ P.denominator.solution (z - z₀)
  numeratorDeriv := fun z ↦ P.numerator.solutionDeriv (z - z₀)
  denominatorDeriv := fun z ↦ P.denominator.solutionDeriv (z - z₀)
  numeratorSecondDeriv := fun z ↦ P.numerator.solutionSecondDeriv (z - z₀)
  denominatorSecondDeriv := fun z ↦ P.denominator.solutionSecondDeriv (z - z₀)
  denominator_ne_zero := by
    intro z hz
    exact P.denominator_ne_zero (z - z₀) hz
  wronskian_ne_zero := by
    intro z hz
    exact P.wronskian_ne_zero (z - z₀) hz
  numerator_solves_ode := by
    intro z hz
    have harg : z₀ + (z - z₀) = z := by ring
    simpa [harg] using P.numerator.solves_ode (z - z₀) hz
  denominator_solves_ode := by
    intro z hz
    have harg : z₀ + (z - z₀) = z := by ring
    simpa [harg] using P.denominator.solves_ode (z - z₀) hz
  base_mem := mem_centeredBallDomain_center P.radius_pos
  denominator_base := by
    simpa using P.denominator.solution_zero
  denominatorDeriv_base := by
    simpa using P.denominator.solutionDeriv_zero
  numerator_base := by
    simpa using P.numerator.solution_zero
  numeratorDeriv_base := by
    simpa using P.numerator.solutionDeriv_zero

/--
If the two centered Frobenius solution functions and their stored derivative
fields have their expected actual derivatives, then the canonical first
derivative of their quotient has the stored second derivative.
-/
theorem localMapDeriv_hasDerivAt_of_solutionHasDerivAt
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a)
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem)
    (hSolSecondDeriv : CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem)
    {z : ℂ} (hz : z ∈ centeredBallDomain z₀ P.radius) :
    HasDerivAt
      (fun z ↦
        ((P.numerator.solutionDeriv (z - z₀) *
              P.denominator.solution (z - z₀) -
            P.numerator.solution (z - z₀) *
              P.denominator.solutionDeriv (z - z₀)) /
          P.denominator.solution (z - z₀) ^ 2))
      (-2 *
        (P.numerator.solutionDeriv (z - z₀) *
            P.denominator.solution (z - z₀) -
          P.numerator.solution (z - z₀) *
            P.denominator.solutionDeriv (z - z₀)) *
        P.denominator.solutionDeriv (z - z₀) /
          P.denominator.solution (z - z₀) ^ 3) z := by
  let w : ℂ := z - z₀
  have hw : w ∈ Metric.eball (0 : ℂ) P.radius := by
    change z - z₀ ∈ Metric.eball (0 : ℂ) P.radius
    exact hz
  have hsub : HasDerivAt (fun z : ℂ => z - z₀) 1 z :=
    (hasDerivAt_id' z).sub_const z₀
  have hnum_w :
      HasDerivAt P.numerator.solution (P.numerator.solutionDeriv w) w :=
    hSolDeriv P.numerator hw
  have hden_w :
      HasDerivAt P.denominator.solution (P.denominator.solutionDeriv w) w :=
    hSolDeriv P.denominator hw
  have hnum'_w :
      HasDerivAt P.numerator.solutionDeriv (P.numerator.solutionSecondDeriv w) w :=
    hSolSecondDeriv P.numerator hw
  have hden'_w :
      HasDerivAt P.denominator.solutionDeriv (P.denominator.solutionSecondDeriv w) w :=
    hSolSecondDeriv P.denominator hw
  have hnum :
      HasDerivAt (fun z : ℂ => P.numerator.solution (z - z₀))
        (P.numerator.solutionDeriv w) z := by
    simpa [w, one_mul] using hnum_w.comp z hsub
  have hden :
      HasDerivAt (fun z : ℂ => P.denominator.solution (z - z₀))
        (P.denominator.solutionDeriv w) z := by
    simpa [w, one_mul] using hden_w.comp z hsub
  have hnum' :
      HasDerivAt (fun z : ℂ => P.numerator.solutionDeriv (z - z₀))
        (P.numerator.solutionSecondDeriv w) z := by
    simpa [w, one_mul] using hnum'_w.comp z hsub
  have hden' :
      HasDerivAt (fun z : ℂ => P.denominator.solutionDeriv (z - z₀))
        (P.denominator.solutionSecondDeriv w) z := by
    simpa [w, one_mul] using hden'_w.comp z hsub
  let Q := P.toNormalizedSchwarzianLinearODESolutionPair.toSchwarzianLinearODESolutionPair
  have hQ :
      HasDerivAt Q.localMapDeriv (Q.localMapSecondDeriv z) z :=
    Q.localMapDeriv_hasDerivAt hz hnum hden hnum' hden'
  simpa [Q, CenteredNormalizedSchwarzianFrobeniusPair.toNormalizedSchwarzianLinearODESolutionPair,
    SchwarzianLinearODESolutionPair.localMapDeriv,
    SchwarzianLinearODESolutionPair.localMapSecondDeriv,
    SchwarzianLinearODESolutionPair.wronskian, w] using hQ

/--
If the two centered Frobenius solution functions and their stored derivative
fields have their expected actual derivatives through the first derivative,
then the canonical second derivative of their quotient has the stored third
derivative.
-/
theorem localMapSecondDeriv_hasDerivAt_of_solutionHasDerivAt
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a)
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem)
    (hSolSecondDeriv : CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem)
    {z : ℂ} (hz : z ∈ centeredBallDomain z₀ P.radius) :
    HasDerivAt
      (fun z ↦
        -2 *
          (P.numerator.solutionDeriv (z - z₀) *
              P.denominator.solution (z - z₀) -
            P.numerator.solution (z - z₀) *
              P.denominator.solutionDeriv (z - z₀)) *
          P.denominator.solutionDeriv (z - z₀) /
            P.denominator.solution (z - z₀) ^ 3)
      (-2 *
          (P.numerator.solutionDeriv (z - z₀) *
              P.denominator.solution (z - z₀) -
            P.numerator.solution (z - z₀) *
              P.denominator.solutionDeriv (z - z₀)) *
          P.denominator.solutionSecondDeriv (z - z₀) /
            P.denominator.solution (z - z₀) ^ 3 +
        6 *
          (P.numerator.solutionDeriv (z - z₀) *
              P.denominator.solution (z - z₀) -
            P.numerator.solution (z - z₀) *
              P.denominator.solutionDeriv (z - z₀)) *
          P.denominator.solutionDeriv (z - z₀) ^ 2 /
            P.denominator.solution (z - z₀) ^ 4) z := by
  let w : ℂ := z - z₀
  have hw : w ∈ Metric.eball (0 : ℂ) P.radius := by
    change z - z₀ ∈ Metric.eball (0 : ℂ) P.radius
    exact hz
  have hsub : HasDerivAt (fun z : ℂ => z - z₀) 1 z :=
    (hasDerivAt_id' z).sub_const z₀
  have hnum_w :
      HasDerivAt P.numerator.solution (P.numerator.solutionDeriv w) w :=
    hSolDeriv P.numerator hw
  have hden_w :
      HasDerivAt P.denominator.solution (P.denominator.solutionDeriv w) w :=
    hSolDeriv P.denominator hw
  have hnum'_w :
      HasDerivAt P.numerator.solutionDeriv (P.numerator.solutionSecondDeriv w) w :=
    hSolSecondDeriv P.numerator hw
  have hden'_w :
      HasDerivAt P.denominator.solutionDeriv (P.denominator.solutionSecondDeriv w) w :=
    hSolSecondDeriv P.denominator hw
  have hnum :
      HasDerivAt (fun z : ℂ => P.numerator.solution (z - z₀))
        (P.numerator.solutionDeriv w) z := by
    simpa [w, one_mul] using hnum_w.comp z hsub
  have hden :
      HasDerivAt (fun z : ℂ => P.denominator.solution (z - z₀))
        (P.denominator.solutionDeriv w) z := by
    simpa [w, one_mul] using hden_w.comp z hsub
  have hnum' :
      HasDerivAt (fun z : ℂ => P.numerator.solutionDeriv (z - z₀))
        (P.numerator.solutionSecondDeriv w) z := by
    simpa [w, one_mul] using hnum'_w.comp z hsub
  have hden' :
      HasDerivAt (fun z : ℂ => P.denominator.solutionDeriv (z - z₀))
        (P.denominator.solutionSecondDeriv w) z := by
    simpa [w, one_mul] using hden'_w.comp z hsub
  let Q := P.toNormalizedSchwarzianLinearODESolutionPair.toSchwarzianLinearODESolutionPair
  have hQ :
      HasDerivAt Q.localMapSecondDeriv (Q.localMapThirdDeriv z) z :=
    Q.localMapSecondDeriv_hasDerivAt hz hnum hden hnum' hden'
  convert hQ using 1

end CenteredNormalizedSchwarzianFrobeniusPair

/--
Analytic Frobenius-pair existence target for a holomorphic Schwarzian
coefficient around a point.

This is the local ODE theorem in its power-series form: choose Taylor
coefficients for `q(z₀+w)`, prove the two Frobenius series converge on a
positive ball, prove they solve the ODE there, and shrink the ball so the
denominator and Wronskian are nonzero.  The coefficient and convergence side is
now derived downstream from local holomorphicity.
-/
def HolomorphicSchwarzianFrobeniusPairExistenceTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z₀ : ℂ⦄,
    z₀ ∈ u.coordinateDomain →
      ∃ a : ℕ → ℂ,
        Nonempty
          (CenteredNormalizedSchwarzianFrobeniusPair
            S.coefficient u.coordinateDomain z₀ a)

/--
Pre-shrinking Frobenius existence target: choose Taylor coefficients for
`q(z₀+w)` and build the two convergent normalized Frobenius sums on a positive
ball inside the coordinate domain.
-/
def HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z₀ : ℂ⦄,
    z₀ ∈ u.coordinateDomain →
      ∃ a : ℕ → ℂ,
        Nonempty
          (CenteredNormalizedSchwarzianFrobeniusPrePair
            S.coefficient u.coordinateDomain z₀ a)

/--
Pre-shrinking Frobenius existence with the derivative-continuity data needed
for the automatic nonvanishing shrink.
-/
def HolomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuityTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z₀ : ℂ⦄,
    z₀ ∈ u.coordinateDomain →
      ∃ a : ℕ → ℂ,
        ∃ P : CenteredNormalizedSchwarzianFrobeniusPrePair
            S.coefficient u.coordinateDomain z₀ a,
          Nonempty (CenteredFrobeniusDerivativeContinuity P)

/--
Termwise Frobenius existence target: construct the two normalized Frobenius
sums together with their termwise first and second derivative series.
-/
def HolomorphicSchwarzianFrobeniusTermwisePrePairExistenceTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z₀ : ℂ⦄,
    z₀ ∈ u.coordinateDomain →
      ∃ a : ℕ → ℂ,
        Nonempty
          (CenteredNormalizedSchwarzianFrobeniusTermwisePrePair
            S.coefficient u.coordinateDomain z₀ a)

/--
Coefficient-side analytic majorant target for the Frobenius construction.

This is the geometric-majorant input used by the Frobenius constructor: choose
Taylor coefficients for `S.coefficient (z₀ + w)` on a small coordinate ball,
together with a geometric bound strong enough for the Frobenius majorant
recurrence and the two normalized initial conditions.  It is now derived from
local holomorphicity through scalar Taylor coefficients and mathlib's
convergence-radius coefficient estimate.
-/
def HolomorphicSchwarzianCoefficientGeometricMajorantTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z₀ : ℂ⦄,
    z₀ ∈ u.coordinateDomain →
      ∃ (a : ℕ → ℂ) (C D T : ℝ) (r : NNReal),
        0 < r ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ T ∧ C ≤ 4 * T ^ 2 ∧
        (∀ n, ‖a n‖ ≤ C * T ^ n) ∧
        1 ≤ D ∧ 1 ≤ D * T ∧ T * (r : ℝ) < 1 ∧
        HasFPowerSeriesOnBall
          (fun w : ℂ => S.coefficient (z₀ + w))
          (scalarFormalPowerSeries a) 0 (r : ENNReal) ∧
        centeredBallDomain z₀ (r : ENNReal) ⊆ u.coordinateDomain

/--
Power-series Taylor-control target for the Schwarzian coefficient.

This is closer to mathlib's analytic API than the geometric-majorant target:
one supplies a scalar Taylor series on a coordinate ball, together with a
strictly smaller positive control radius.  Mathlib's convergence-radius
coefficient estimate then gives the geometric coefficient bounds needed by the
Frobenius construction.
-/
def HolomorphicSchwarzianCoefficientTaylorControlTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z₀ : ℂ⦄,
    z₀ ∈ u.coordinateDomain →
      ∃ (a : ℕ → ℂ) (R s : NNReal),
        0 < s ∧ (s : ENNReal) < (R : ENNReal) ∧
        HasFPowerSeriesOnBall
          (fun w : ℂ => S.coefficient (z₀ + w))
          (scalarFormalPowerSeries a) 0 (R : ENNReal) ∧
        centeredBallDomain z₀ (R : ENNReal) ⊆ u.coordinateDomain

/--
Pointwise scalar Taylor expansion target for the Schwarzian coefficient.

Compared with `HolomorphicSchwarzianCoefficientTaylorControlTheorem`, this
does not ask for nested control radii or for the Taylor ball to lie inside the
coordinate domain.  Those radius choices are topological and are derived below
from the openness of `u.coordinateDomain`.
-/
def HolomorphicSchwarzianCoefficientScalarTaylorTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z₀ : ℂ⦄,
    z₀ ∈ u.coordinateDomain →
      ∃ (a : ℕ → ℂ) (R : NNReal),
        0 < R ∧
        HasFPowerSeriesOnBall
          (fun w : ℂ => S.coefficient (z₀ + w))
          (scalarFormalPowerSeries a) 0 (R : ENNReal)

/--
In one complex variable, the scalar coefficients `p.coeff n` give an equivalent
scalar formal power series expansion.

This is a small bridge to mathlib's `HasFPowerSeriesAt` API: mathlib's general
one-variable analytic expansion already supplies the scalar coefficient
sequence via `FormalMultilinearSeries.coeff`.
-/
theorem hasFPowerSeriesAt_scalarFormalPowerSeries_coeff
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ}
    (h : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt f (scalarFormalPowerSeries p.coeff) z₀ := by
  rw [hasFPowerSeriesAt_iff] at h ⊢
  filter_upwards [h] with z hz
  simpa [scalarFormalPowerSeries] using hz

/--
The holomorphicity already stored in `LocalSchwarzianData` gives pointwise
scalar Taylor expansions.

This closes the coefficient-side boundary down to mathlib's ordinary
`AnalyticOnNhd` data plus the one-variable scalar-coefficient bridge above.
-/
theorem holomorphicSchwarzianCoefficientScalarTaylor_of_localAnalytic :
    HolomorphicSchwarzianCoefficientScalarTaylorTheorem := by
  intro u S z₀ hz₀
  rcases S.holomorphic_on_domain z₀ hz₀ with ⟨p, hp⟩
  have hp_centered :
      HasFPowerSeriesAt (fun w : ℂ => S.coefficient (z₀ + w)) p 0 := by
    simpa [sub_neg_eq_add, add_comm] using hp.comp_sub (-z₀)
  rcases hasFPowerSeriesAt_scalarFormalPowerSeries_coeff hp_centered with ⟨R, hR⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hR.r_pos with ⟨r, hr_pos, hr_lt⟩
  refine ⟨p.coeff, r, ?_, ?_⟩
  · exact_mod_cast hr_pos
  · exact hR.mono hr_pos hr_lt.le

/-- Every point of an open coordinate domain has a positive centered ball inside it. -/
theorem exists_centeredBallDomain_subset_of_isOpen
    {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ R : NNReal, 0 < R ∧ centeredBallDomain z₀ (R : ENNReal) ⊆ U := by
  rcases Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀) with ⟨ε, hε_pos, hε_subset⟩
  let R : NNReal := ⟨ε / 2, by positivity⟩
  refine ⟨R, ?_, ?_⟩
  · change 0 < ε / 2
    positivity
  · intro z hz
    apply hε_subset
    have hzdist : dist (z - z₀) 0 < ε / 2 := by
      simpa [centeredBallDomain, Metric.mem_eball, edist_lt_ofReal, dist_zero_right,
        R] using hz
    have hdist : dist z z₀ < ε := by
      have hdist_eq : dist (z - z₀) 0 = dist z z₀ := by
        rw [dist_eq_norm, dist_eq_norm]
        simp only [sub_zero]
      rw [hdist_eq] at hzdist
      linarith
    simpa using hdist

/--
Pointwise scalar Taylor expansions imply Taylor-control data.

The proof only chooses radii: one ball comes from the scalar Taylor expansion,
one from openness of the coordinate domain, and the control radius is half of
their minimum.
-/
theorem holomorphicSchwarzianCoefficientTaylorControl_of_scalarTaylor
    (hScalar : HolomorphicSchwarzianCoefficientScalarTaylorTheorem) :
    HolomorphicSchwarzianCoefficientTaylorControlTheorem := by
  intro u S z₀ hz₀
  rcases hScalar S hz₀ with ⟨a, Rseries, hRseries_pos, hq⟩
  rcases exists_centeredBallDomain_subset_of_isOpen
      u.isOpen_coordinateDomain hz₀ with
    ⟨Rdomain, hRdomain_pos, hDomain⟩
  let R : NNReal := min Rseries Rdomain
  let s : NNReal := R / 2
  have hR_pos : 0 < R := lt_min hRseries_pos hRdomain_pos
  have hs_pos : 0 < s := by
    change 0 < (R : NNReal) / 2
    positivity
  have hsR : (s : ENNReal) < (R : ENNReal) := by
    have hsR_nn : s < R := by
      change R / 2 < R
      exact half_lt_self hR_pos
    exact_mod_cast hsR_nn
  have hR_le_series : (R : ENNReal) ≤ (Rseries : ENNReal) := by
    exact_mod_cast (min_le_left Rseries Rdomain)
  have hR_le_domain : (R : ENNReal) ≤ (Rdomain : ENNReal) := by
    exact_mod_cast (min_le_right Rseries Rdomain)
  refine ⟨a, R, s, hs_pos, hsR, ?_, ?_⟩
  · exact hq.mono (by exact_mod_cast hR_pos) hR_le_series
  · intro z hz
    exact hDomain (Metric.eball_subset_eball hR_le_domain hz)

/--
Taylor-control data imply the geometric-majorant data needed by the Frobenius
construction.

The only analytic estimate used here is mathlib's
`FormalMultilinearSeries.norm_le_div_pow_of_pos_of_lt_radius`, applied to the
strictly smaller control radius `s`.  We then enlarge the geometric rate `T`
and shrink the final Frobenius radius so that `T * r < 1`.
-/
theorem holomorphicSchwarzianCoefficientGeometricMajorant_of_taylorControl
    (hTaylor : HolomorphicSchwarzianCoefficientTaylorControlTheorem) :
    HolomorphicSchwarzianCoefficientGeometricMajorantTheorem := by
  intro u S z₀ hz₀
  rcases hTaylor S hz₀ with ⟨a, R, s, hs_pos, hsR, hq, hDomain⟩
  let p : FormalMultilinearSeries ℂ ℂ ℂ := scalarFormalPowerSeries a
  have hs_radius : (s : ENNReal) < p.radius := by
    exact lt_of_lt_of_le hsR hq.r_le
  rcases p.norm_le_div_pow_of_pos_of_lt_radius hs_pos hs_radius with
    ⟨C, hC_pos, hC_bound⟩
  let T : ℝ := max 1 (max C ((s : ℝ)⁻¹))
  have hT_one : 1 ≤ T := by
    exact le_max_left _ _
  have hT_C : C ≤ T := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hT_inv : ((s : ℝ)⁻¹) ≤ T := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hT_nonneg : 0 ≤ T := le_trans (by norm_num) hT_one
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT_one
  let rT : NNReal := ⟨1 / (2 * T), by positivity⟩
  let r : NNReal := min R rT
  have hsR_nn : s < R := by
    exact_mod_cast hsR
  have hR_pos : 0 < R := lt_trans hs_pos hsR_nn
  have hrT_pos : 0 < rT := by
    change 0 < 1 / (2 * T)
    positivity
  have hr_pos : 0 < r := lt_min hR_pos hrT_pos
  have hr_le_R : (r : ENNReal) ≤ (R : ENNReal) := by
    exact_mod_cast (min_le_left R rT)
  have hq_r :
      HasFPowerSeriesOnBall
        (fun w : ℂ => S.coefficient (z₀ + w))
        (scalarFormalPowerSeries a) 0 (r : ENNReal) :=
    hq.mono (by exact_mod_cast hr_pos) hr_le_R
  have hDomain_r : centeredBallDomain z₀ (r : ENNReal) ⊆ u.coordinateDomain := by
    intro z hz
    exact hDomain (Metric.eball_subset_eball hr_le_R hz)
  have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
  have hCT : C ≤ 4 * T ^ 2 := by
    have hT_le_sq : T ≤ T ^ 2 := by nlinarith [hT_one, sq_nonneg T]
    nlinarith [hT_C, hT_le_sq, hT_nonneg]
  have ha : ∀ n, ‖a n‖ ≤ C * T ^ n := by
    intro n
    have hp_bound : ‖p n‖ ≤ C / (s : ℝ) ^ n := hC_bound n
    have ha_bound : ‖a n‖ ≤ C / (s : ℝ) ^ n := by
      simpa [p, scalarFormalPowerSeries] using hp_bound
    have hpow :
        ((s : ℝ)⁻¹) ^ n ≤ T ^ n :=
      pow_le_pow_left₀ (by positivity) hT_inv n
    calc
      ‖a n‖ ≤ C / (s : ℝ) ^ n := ha_bound
      _ = C * ((s : ℝ)⁻¹) ^ n := by
        rw [div_eq_mul_inv, inv_pow]
      _ ≤ C * T ^ n :=
        mul_le_mul_of_nonneg_left hpow hC_nonneg
  have hD_nonneg : 0 ≤ (1 : ℝ) := by norm_num
  have hTr : T * (r : ℝ) < 1 := by
    have hr_le_rT : (r : ℝ) ≤ (rT : ℝ) := by
      exact_mod_cast (min_le_right R rT)
    calc
      T * (r : ℝ) ≤ T * (rT : ℝ) :=
        mul_le_mul_of_nonneg_left hr_le_rT hT_nonneg
      _ = T * (1 / (2 * T)) := by rfl
      _ = 1 / 2 := by field_simp [hT_pos.ne']
      _ < 1 := by norm_num
  refine ⟨a, C, 1, T, r, hr_pos, hC_nonneg, hD_nonneg, hT_nonneg, hCT, ha,
    ?_, ?_, hTr, hq_r, hDomain_r⟩
  · norm_num
  · simpa using hT_one

/--
The coefficient majorant target implies the termwise Frobenius pre-pair
existence theorem.  All solution-side work is handled by the previously proved
Frobenius recurrence, convergence estimates, and Cauchy-product identity.
-/
theorem holomorphicSchwarzianFrobeniusTermwisePrePairExistence_of_coefficientGeometricMajorant
    (hCoeff : HolomorphicSchwarzianCoefficientGeometricMajorantTheorem) :
    HolomorphicSchwarzianFrobeniusTermwisePrePairExistenceTheorem := by
  intro u S z₀ hz₀
  rcases hCoeff S hz₀ with
    ⟨a, C, D, T, r, hr, hC, hD, hT, hCT, ha, hD_one, hDT_one, hTr, hq, hDomain⟩
  exact ⟨a, ⟨centeredNormalizedSchwarzianFrobeniusTermwisePrePairOfGeometricMajorant
    (q := S.coefficient) (V := u.coordinateDomain) (z₀ := z₀) (a := a)
    (C := C) (D := D) (T := T) (r := r)
    hr hC hD hT hCT ha hD_one hDT_one hTr hq hDomain⟩⟩

/-- Termwise Frobenius pre-pair existence forgets to ordinary pre-pair existence. -/
theorem holomorphicSchwarzianFrobeniusPrePairExistence_of_termwise
    (h : HolomorphicSchwarzianFrobeniusTermwisePrePairExistenceTheorem) :
    HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem := by
  intro u S z₀ hz₀
  rcases h S hz₀ with ⟨a, ⟨P⟩⟩
  exact ⟨a, ⟨P.toPrePair⟩⟩

/--
The coefficient majorant target gives ordinary pre-shrinking Frobenius
existence by forgetting the termwise derivative data.
-/
theorem holomorphicSchwarzianFrobeniusPrePairExistence_of_coefficientGeometricMajorant
    (hCoeff : HolomorphicSchwarzianCoefficientGeometricMajorantTheorem) :
    HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem :=
  holomorphicSchwarzianFrobeniusPrePairExistence_of_termwise
    (holomorphicSchwarzianFrobeniusTermwisePrePairExistence_of_coefficientGeometricMajorant
      hCoeff)

/--
Pre-shrinking Frobenius existence with derivative-continuity data forgets to
ordinary pre-shrinking Frobenius existence.
-/
theorem holomorphicSchwarzianFrobeniusPrePairExistence_of_prePairWithDerivativeContinuity
    (h : HolomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuityTheorem) :
    HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem := by
  intro u S z₀ hz₀
  rcases h S hz₀ with ⟨a, P, _hC⟩
  exact ⟨a, ⟨P⟩⟩

/--
Pre-shrinking Frobenius existence plus the nonvanishing shrinking theorem gives
the full Frobenius-pair existence target.
-/
theorem holomorphicSchwarzianFrobeniusPairExistence_of_prePair_and_shrink
    (hPre : HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem)
    (hShrink : CenteredFrobeniusNonvanishingShrinkTheorem) :
    HolomorphicSchwarzianFrobeniusPairExistenceTheorem := by
  intro u S z₀ hz₀
  rcases hPre S hz₀ with ⟨a, ⟨P⟩⟩
  rcases hShrink P with ⟨N⟩
  exact ⟨a, ⟨CenteredNormalizedSchwarzianFrobeniusPair.ofPrePairShrink P N⟩⟩

/--
Pre-shrinking Frobenius existence now gives the full Frobenius-pair existence
target, because the nonvanishing shrink is proved for every pre-pair.
-/
theorem holomorphicSchwarzianFrobeniusPairExistence_of_prePair
    (hPre : HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem) :
    HolomorphicSchwarzianFrobeniusPairExistenceTheorem :=
  holomorphicSchwarzianFrobeniusPairExistence_of_prePair_and_shrink
    hPre centeredFrobeniusNonvanishingShrinkTheorem

/-- Coefficient majorants now imply full normalized Frobenius-pair existence. -/
theorem holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
    (hCoeff : HolomorphicSchwarzianCoefficientGeometricMajorantTheorem) :
    HolomorphicSchwarzianFrobeniusPairExistenceTheorem :=
  holomorphicSchwarzianFrobeniusPairExistence_of_prePair
    (holomorphicSchwarzianFrobeniusPrePairExistence_of_coefficientGeometricMajorant hCoeff)

/--
%%handwave
name:
  Local Frobenius solution of the Schwarzian equation
statement:
  If $Q$ is holomorphic near $z_0$, then on a sufficiently small centered
  ball there are solutions $y_0,y_1$ of $y''+\tfrac12Qy=0$ with
  $y_0(z_0)=1$, $y_0'(z_0)=0$, $y_1(z_0)=0$, and $y_1'(z_0)=1$.
  The ball may be chosen so that $y_0$ and
  $W=y_1'y_0-y_1y_0'$ do not vanish there.
proof:
  Expand $Q(z_0+w)=\sum_{n\geq0}a_nw^n$. For
  $y(w)=\sum_{n\geq0}b_nw^n$, coefficient comparison gives
  $(n+2)(n+1)b_{n+2}=-\tfrac12\sum_{k=0}^na_kb_{n-k}$.
  Taylor coefficient bounds provide a geometric majorant, so the two series
  with the prescribed initial coefficients converge and solve the equation.
  At the center $y_0=1$ and $W=1$; continuity permits the final shrinking.
tags:
  milestone
-/
theorem holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic :
    HolomorphicSchwarzianFrobeniusPairExistenceTheorem :=
  holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
    (holomorphicSchwarzianCoefficientGeometricMajorant_of_taylorControl
      (holomorphicSchwarzianCoefficientTaylorControl_of_scalarTaylor
        holomorphicSchwarzianCoefficientScalarTaylor_of_localAnalytic))

/--
Pre-shrinking Frobenius existence with derivative-continuity data gives the full
Frobenius-pair existence target.
-/
theorem holomorphicSchwarzianFrobeniusPairExistence_of_prePairWithDerivativeContinuity
    (h : HolomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuityTheorem) :
    HolomorphicSchwarzianFrobeniusPairExistenceTheorem := by
  intro u S z₀ hz₀
  rcases h S hz₀ with ⟨a, P, ⟨C⟩⟩
  rcases centeredFrobeniusNonvanishingShrink_of_derivativeContinuity P C with ⟨N⟩
  exact ⟨a, ⟨CenteredNormalizedSchwarzianFrobeniusPair.ofPrePairShrink P N⟩⟩

/--
Ordinary pre-shrinking Frobenius existence already includes enough derivative
continuity for the automatic nonvanishing shrink, because each centered
solution stores its first-derivative power-series realization.
-/
theorem holomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuity_of_prePair
    (h : HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem) :
    HolomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuityTheorem := by
  intro u S z₀ hz₀
  rcases h S hz₀ with ⟨a, ⟨P⟩⟩
  exact ⟨a, P, ⟨P.derivativeContinuity⟩⟩

/--
Coefficient majorants give the pre-pair-with-continuity target directly, after
constructing the Frobenius pre-pair.
-/
theorem holomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuity_of_coefficientGeometricMajorant
    (hCoeff : HolomorphicSchwarzianCoefficientGeometricMajorantTheorem) :
    HolomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuityTheorem :=
  holomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuity_of_prePair
    (holomorphicSchwarzianFrobeniusPrePairExistence_of_coefficientGeometricMajorant hCoeff)

/--
Termwise Frobenius pre-pair existence implies the pre-pair-with-continuity
target.
-/
theorem holomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuity_of_termwise
    (h : HolomorphicSchwarzianFrobeniusTermwisePrePairExistenceTheorem) :
    HolomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuityTheorem := by
  intro u S z₀ hz₀
  rcases h S hz₀ with ⟨a, ⟨P⟩⟩
  exact ⟨a, P.toPrePair, ⟨P.derivativeContinuity⟩⟩

/-- Termwise Frobenius pre-pair existence gives the full Frobenius-pair target. -/
theorem holomorphicSchwarzianFrobeniusPairExistence_of_termwise
    (h : HolomorphicSchwarzianFrobeniusTermwisePrePairExistenceTheorem) :
    HolomorphicSchwarzianFrobeniusPairExistenceTheorem :=
  holomorphicSchwarzianFrobeniusPairExistence_of_prePairWithDerivativeContinuity
    (holomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuity_of_termwise h)

end

end JJMath
