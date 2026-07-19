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

/--
%%handwave
name:
  Schwarzian from the quotient identities and the denominator equation
statement:
  Let \(y_0\) and \(W\) be nonvanishing on \(V\), suppose
  \(y_0''=-\tfrac12Qy_0\), and let the prescribed derivatives of a function
  \(f\) satisfy
  \(f'=W/y_0^2\), \(f''=-2Wy_0'/y_0^3\), and
  \(f'''=-2Wy_0''/y_0^3+6W(y_0')^2/y_0^4\). Then their symbolic Schwarzian
  satisfies \(\{f,z\}=Q(z)\) throughout \(V\).
proof:
  Substitute \(f'=W/y_0^2\), \(f''=-2Wy_0'/y_0^3\), and
  \(f'''=-2Wy_0''/y_0^3+6W(y_0')^2/y_0^4\) into the Schwarzian expression.
  The quadratic terms cancel, and the differential equation gives
  \(-2y_0''/y_0=Q\).
-/
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

/--
%%handwave
name:
  Nonvanishing of the prescribed first quotient derivative
statement:
  If \(y_0\) and \(W\) are nonzero throughout \(V\) and the prescribed first
  derivative of \(f\) is \(f'=W/y_0^2\), then \(f'\) is nonzero throughout
  \(V\).
proof:
  The quotient \(W/y_0^2\) is a quotient of two nonzero complex numbers at
  every point of \(V\).
-/
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
  Symbolic Schwarzian of a ratio satisfying the linear ODE identities
statement:
  Let \(y_0,y_1\), together with prescribed first and second derivatives,
  satisfy the pointwise identities \(y_j''+\tfrac12Qy_j=0\) on \(V\).
  Wherever \(y_0\) and \(W=y_1'y_0-y_1y_0'\) are nonzero, the canonical
  quotient-derivative expressions for \(f=y_1/y_0\) have symbolic Schwarzian
  \(\{f,z\}=Q\).
proof:
  The canonical expressions are \(f'=W/y_0^2\),
  \(f''=-2Wy_0'/y_0^3\), and
  \(f'''=-2Wy_0''/y_0^3+6W(y_0')^2/y_0^4\). Substitution into
  \(\{f,z\}=f'''/f'-\tfrac32(f''/f')^2\) leaves
  \(-2y_0''/y_0=Q\).
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
%%handwave
name:
  Vanishing derivative of the Wronskian
statement:
  If \(y_0\) and \(y_1\) are twice complex differentiable at \(z\) and both satisfy
  \(y''+\tfrac12Qy=0\) there, then the derivative at \(z\) of
  \(W=y_1'y_0-y_1y_0'\) is zero.
proof:
  Differentiate the two products. The mixed terms cancel, leaving
  \(W'=y_1''y_0-y_1y_0''\), which vanishes after substituting the two copies of
  the differential equation.
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
%%handwave
name:
  Derivative of the first quotient expression
statement:
  At a point \(z\in V\) where the prescribed first and second derivatives of
  the two solutions are their actual complex derivatives, the derivative of
  \(W/y_0^2\) is
  \(-2Wy_0'/y_0^3\).
proof:
  The Wronskian has derivative zero. Apply the quotient rule to \(W/y_0^2\) and
  use \(y_0(z)\ne0\) to simplify the resulting expression.
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
%%handwave
name:
  Derivative of the second quotient expression
statement:
  At a point \(z\in V\) where the prescribed first and second derivatives of
  the two solutions are their actual complex derivatives, the derivative of
  \(-2Wy_0'/y_0^3\) is
  \(-2Wy_0''/y_0^3+6W(y_0')^2/y_0^4\).
proof:
  Differentiate the numerator and denominator, using \(W'=0\), and apply the
  quotient rule. Since \(y_0(z)\ne0\), collecting powers of \(y_0\) gives the
  stated formula.
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

/--
%%handwave
name:
  Wronskian of the normalized solution pair
statement:
  If \(y_0(z_0)=1\), \(y_0'(z_0)=0\), \(y_1(z_0)=0\), and \(y_1'(z_0)=1\), then
  \(W(z_0)=1\).
proof:
  Substitute the four initial values into
  \(W=y_1'y_0-y_1y_0'\).
-/
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
%%handwave
name:
  Dependence of a product coefficient on lower coefficients
statement:
  Let \(a,b,c:\mathbb N\to\mathbb C\). If \(b_m=c_m\) for every \(m\le n\), then
  \(\sum_{k=0}^n a_kb_{n-k}=\sum_{k=0}^n a_kc_{n-k}\).
proof:
  For each \(0\le k\le n\), the index \(n-k\) is at most \(n\), so the corresponding
  summands are equal. Sum these equalities.
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
%%handwave
name:
  Dependence of the next Frobenius coefficient
statement:
  If \(b_m=c_m\) for every \(m\le n\), then the next coefficients prescribed by
  the equation \(y''+\tfrac12Qy=0\) from \(a\) and either \(b\) or \(c\) are equal.
proof:
  The two formulas have the same denominator and their numerators are the
  equal product coefficients \(\sum_{k=0}^n a_kb_{n-k}\) and
  \(\sum_{k=0}^n a_kc_{n-k}\).
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

/--
%%handwave
name:
  Constant normalized Frobenius coefficient
statement:
  The recursively defined normalized solution of \(y''+\tfrac12Qy=0\) has
  constant coefficient \(b_0=1\).
proof:
  This is the constant initial condition in the recursive definition.
-/
theorem schwarzianFrobeniusCoefficients_zero (a : ℕ → ℂ) :
    schwarzianFrobeniusCoefficients a 0 = 1 := by
  simp [schwarzianFrobeniusCoefficients]

/--
%%handwave
name:
  Linear normalized Frobenius coefficient
statement:
  The recursively defined normalized solution of \(y''+\tfrac12Qy=0\) has
  linear coefficient \(b_1=0\).
proof:
  This is the linear initial condition in the recursive definition.
-/
theorem schwarzianFrobeniusCoefficients_one (a : ℕ → ℂ) :
    schwarzianFrobeniusCoefficients a 1 = 0 := by
  simp [schwarzianFrobeniusCoefficients]

/--
%%handwave
name:
  Recurrence for the normalized Frobenius coefficients
statement:
  For every \(n\ge0\), the normalized coefficients satisfy
  \(b_{n+2}=-\frac{1}{2(n+2)(n+1)}\sum_{k=0}^n a_kb_{n-k}\).
proof:
  By the recursive clause at \(n+2\), the truncated auxiliary sequence
  agrees with \(b\) through degree \(n\), which is all that the convolution for
  the next coefficient uses.
-/
theorem schwarzianFrobeniusCoefficients_succ_succ (a : ℕ → ℂ) (n : ℕ) :
    schwarzianFrobeniusCoefficients a (n + 2) =
      nextSchwarzianFrobeniusCoefficient a (schwarzianFrobeniusCoefficients a) n := by
  rw [schwarzianFrobeniusCoefficients]
  apply nextSchwarzianFrobeniusCoefficient_congr_of_eq_on_le
  intro m hm
  have hlt : m < n + 2 := by omega
  simp [hlt]

/--
%%handwave
name:
  Constant Frobenius coefficient with prescribed initial data
statement:
  The recursively defined solution with initial coefficients \(b_0,b_1\) has
  constant coefficient \(b_0\).
proof:
  This is the constant initial clause of the recursive definition.
-/
theorem schwarzianFrobeniusCoefficientsWithInitial_zero
    (a : ℕ → ℂ) (b₀ b₁ : ℂ) :
    schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁ 0 = b₀ := by
  simp [schwarzianFrobeniusCoefficientsWithInitial]

/--
%%handwave
name:
  Linear Frobenius coefficient with prescribed initial data
statement:
  The recursively defined solution with initial coefficients \(b_0,b_1\) has
  linear coefficient \(b_1\).
proof:
  This is the linear initial clause of the recursive definition.
-/
theorem schwarzianFrobeniusCoefficientsWithInitial_one
    (a : ℕ → ℂ) (b₀ b₁ : ℂ) :
    schwarzianFrobeniusCoefficientsWithInitial a b₀ b₁ 1 = b₁ := by
  simp [schwarzianFrobeniusCoefficientsWithInitial]

/--
%%handwave
name:
  Frobenius recurrence with prescribed initial data
statement:
  For every \(n\ge0\), the coefficients with arbitrary initial data satisfy
  \(b_{n+2}=-\frac{1}{2(n+2)(n+1)}\sum_{k=0}^n a_kb_{n-k}\).
proof:
  By the recursive clause at \(n+2\), the auxiliary truncated sequence
  agrees with the constructed sequence through degree \(n\), so the next
  coefficient is unchanged when the full sequence is substituted.
-/
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

/--
%%handwave
name:
  Agreement of the two normalized Frobenius constructions
statement:
  The normalized coefficient sequence equals the arbitrary-initial-data
  sequence specialized to \(b_0=1\) and \(b_1=0\).
proof:
  Use strong induction on the degree. The degrees zero and one are the same
  initial conditions; at degree \(n+2\), the recurrence depends only on the
  coefficients through degree \(n\), where the induction hypothesis applies.
-/
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
%%handwave
name:
  Vanishing of an ODE coefficient under the Frobenius recurrence
statement:
  If
  \(b_{n+2}=-\frac{1}{2(n+2)(n+1)}\sum_{k=0}^n a_kb_{n-k}\), then the coefficient
  of \(w^n\) in \(y''+\tfrac12Qy\) is zero.
proof:
  Substitute the recurrence into
  \((n+2)(n+1)b_{n+2}+\tfrac12\sum_{k=0}^n a_kb_{n-k}\). The positive integer
  factors in the denominator are nonzero, and the two terms cancel.
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
%%handwave
name:
  Norm bound for a product coefficient
statement:
  For complex sequences \(a,b\) and \(n\ge0\),
  \[
  \left\|\sum_{k=0}^n a_kb_{n-k}\right\|\le
  \sum_{k=0}^n\|a_k\|\,\|b_{n-k}\|.
  \]
proof:
  Apply the triangle inequality to the finite sum and multiplicativity of the
  complex norm to each summand.
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

/--
%%handwave
name:
  Norm of the Frobenius denominator
statement:
  For \(n\ge0\), the complex norm of \((n+2)(n+1)\) is the real number
  \((n+2)(n+1)\).
proof:
  The complex norm is multiplicative and sends each nonnegative integer to
  the corresponding real number.
-/
theorem norm_schwarzianFrobeniusDenominator (n : ℕ) :
    ‖(((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ))‖ =
      ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
  rw [norm_mul, norm_natCast, norm_natCast]

/--
%%handwave
name:
  Norm bound for the next Frobenius coefficient
statement:
  The coefficient prescribed at degree \(n+2\) by the recurrence satisfies
  \[
  \|b_{n+2}\|\le\frac{1}{2(n+2)(n+1)}
  \sum_{k=0}^n\|a_k\|\,\|b_{n-k}\|.
  \]
proof:
  Take norms in the recurrence, use the convolution norm bound for the
  numerator, and evaluate the norm of the positive-integer denominator.
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
%%handwave
name:
  Propagation of coefficient majorants
statement:
  Suppose \(A_k\ge0\), \(\|a_k\|\le A_k\), and \(\|b_k\|\le B_k\) for every
  \(k\le n\). Then the coefficient prescribed at degree \(n+2\) by the
  recurrence has norm at most
  \(\frac{1}{2(n+2)(n+1)}\sum_{k=0}^n A_kB_{n-k}\).
proof:
  Bound each term of the norm convolution by \(A_kB_{n-k}\) using
  nonnegativity, sum the inequalities, and divide by the nonnegative
  Frobenius denominator.
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

/--
%%handwave
name:
  Convolution of geometric sequences
statement:
  For real \(C,D,T\) and \(n\ge0\),
  \(\sum_{k=0}^n CT^k\,DT^{n-k}=(n+1)CDT^n\).
proof:
  Each summand equals \(CDT^n\) because \(k+(n-k)=n\). The sum contains exactly
  \(n+1\) identical terms.
-/
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
%%handwave
name:
  Geometric Frobenius majorant recurrence
statement:
  If \(D,T\ge0\) and \(C\le4T^2\), then \(A_n=CT^n\) and \(B_n=DT^n\) satisfy
  \(\frac{1}{2(n+2)(n+1)}\sum_{k=0}^n A_kB_{n-k}\le B_{n+2}\) for every \(n\).
proof:
  Evaluate the convolution as \((n+1)CDT^n\) and cancel the positive factor
  \(n+1\). Since \(D T^n\ge0\), it suffices to multiply
  \(C\le2(n+2)T^2\) by this factor; the required inequality follows from
  \(C\le4T^2\) and \(n+2\ge2\).
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
%%handwave
name:
  Frobenius coefficients are bounded by a recurrence majorant
statement:
  Let \(\|a_n\|\le A_n\) with \(A_n\ge0\). If
  \(\|b_0\|\le B_0\), \(\|b_1\|\le B_1\), and
  \(\frac{1}{2(n+2)(n+1)}\sum_{k=0}^n A_kB_{n-k}\le B_{n+2}\), then every
  recursively constructed Frobenius coefficient satisfies \(\|b_n\|\le B_n\).
proof:
  Use strong induction on \(n\). The first two cases are the assumed initial
  bounds. In degree \(n+2\), the induction hypotheses bound every coefficient
  in the convolution, and the next-coefficient estimate followed by the
  majorant recurrence gives the result.
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
%%handwave
name:
  Geometric bound for Frobenius coefficients
statement:
  Suppose \(C,D,T\ge0\), \(C\le4T^2\), \(\|a_n\|\le CT^n\),
  \(\|b_0\|\le D\), and \(\|b_1\|\le DT\). Then the Frobenius coefficients with
  these initial values satisfy \(\|b_n\|\le DT^n\) for every \(n\).
proof:
  The geometric sequences \(CT^n\) and \(DT^n\) satisfy the majorant recurrence.
  Apply the recurrence-majorant induction with the two assumed initial bounds.
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

/--
%%handwave
name:
  The normalized Frobenius coefficients satisfy the ODE recurrence
statement:
  If \(b_0=1\), \(b_1=0\), and \(b_{n+2}=-\frac{1}{2(n+2)(n+1)}\sum_{k=0}^n a_k b_{n-k}\), then \((n+2)(n+1)b_{n+2}+\tfrac12 \sum_{k=0}^n a_k b_{n-k}=0\) for every \(n\).
proof:
  Substitute the defining next-coefficient formula into the coefficient equation and clear the nonzero denominator.
-/
theorem solves_recurrence {a : ℕ → ℂ} (Y : SchwarzianFrobeniusSeries a) :
    SolvesSchwarzianFrobeniusRecurrence a Y.coeff := by
  intro n
  exact schwarzianLinearODECoeff_eq_zero_of_nextCoeff a Y.coeff n (Y.coeff_succ_succ n)

end SchwarzianFrobeniusSeries

namespace SchwarzianFrobeniusSeriesWithInitial

/--
%%handwave
name:
  Frobenius coefficients with arbitrary initial data satisfy the recurrence
statement:
  The recursively defined coefficients with prescribed \(b_0,b_1\) satisfy \((n+2)(n+1)b_{n+2}+\tfrac12 \sum_{k=0}^n a_k b_{n-k}=0\) for every \(n\).
proof:
  Apply the algebraic equivalence between the next-coefficient formula and the vanishing ODE coefficient.
-/
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
%%handwave
name:
  Existence of normalized formal Frobenius coefficients
statement:
  For every sequence \((a_n)\) there exists a sequence \((b_n)\) with \(b_0=1\), \(b_1=0\), and the Frobenius recurrence for \(y''+\tfrac12 qy=0\).
proof:
  Take the recursively constructed normalized sequence.
-/
theorem schwarzianFrobeniusRecurrenceExistence :
    SchwarzianFrobeniusRecurrenceExistenceTheorem := by
  intro a
  exact ⟨normalizedSchwarzianFrobeniusSeries a⟩

/--
%%handwave
name:
  Existence of formal Frobenius coefficients with prescribed initial data
statement:
  For every \((a_n)\) and every \(b_0,b_1 \in ℂ\), there is a coefficient sequence satisfying those initial values and the Frobenius recurrence.
proof:
  Take the recursively constructed sequence with the prescribed first two coefficients.
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

/--
%%handwave
name:
  Twice differentiating a coefficient sequence
statement:
  If \(b'_n=(n+1)b_{n+1}\), then \((b')'_n=(n+2)(n+1)b_{n+2}\).
proof:
  Expand both definitions and simplify the natural-number factors.
-/
theorem powerSeriesDerivativeCoefficients_derivative
    (b : ℕ → ℂ) :
    powerSeriesDerivativeCoefficients (powerSeriesDerivativeCoefficients b) =
      powerSeriesSecondDerivativeCoefficients b := by
  funext n
  simp [powerSeriesDerivativeCoefficients, powerSeriesSecondDerivativeCoefficients]
  ring

/--
%%handwave
name:
  Summability from a geometric coefficient bound
statement:
  If \(T \ge 0\), \(\lVert b_n\rVert \le DT^n\), and \(Tr<1\), then \(\sum_{n \ge 0}\lVert b_n\rVert r^n\) converges.
proof:
  Dominate termwise by the convergent geometric series \(D(Tr)^n\).
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
%%handwave
name:
  A radius bound from geometric coefficient growth
statement:
  If \(\lVert b_n\rVert \le DT^n\) with \(T \ge 0\) and \(Tr<1\), then the scalar power series \(\sum_{n \ge 0} b_n z^n\) has convergence radius at least \(r\).
proof:
  Use summability of the norm-weighted series at \(r\).
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
%%handwave
name:
  Convergence of a geometrically bounded scalar power series
statement:
  If \(r>0\), \(T \ge 0\), \(\lVert b_n\rVert \le DT^n\), and \(Tr<1\), then \(\sum_{n \ge 0} b_n z^n\) defines its canonical analytic sum on \(|z|<r\).
proof:
  The radius estimate gives positive convergence radius; restrict the canonical power-series expansion to the radius \(r\).
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
%%handwave
name:
  Summability of the first derivative series
statement:
  If \(\lVert b_n\rVert \le DT^n\), \(T \ge 0\), and \(Tr<1\), then \(\sum_{n \ge 0}(n+1)\lVert b_{n+1}\rVert r^n\) converges.
proof:
  Bound by \(DT \sum_{n \ge 0}(n+1)(Tr)^n\), which converges for \(Tr<1\).
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
%%handwave
name:
  Summability of the second derivative series
statement:
  If \(\lVert b_n\rVert \le DT^n\), \(T \ge 0\), and \(Tr<1\), then \(\sum_{n \ge 0}(n+2)(n+1)\lVert b_{n+2}\rVert r^n\) converges.
proof:
  Bound by \(DT^2 \sum_{n \ge 0}(n+2)(n+1)(Tr)^n\) and use convergence of a polynomially weighted geometric series.
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

/--
%%handwave
name:
  A radius bound for the first derivative series
statement:
  Under \(\lVert b_n\rVert \le DT^n\), \(T \ge 0\), and \(Tr<1\), the series \(\sum_{n \ge 0} (n+1)b_{n+1} z^n\) has radius at least \(r\).
proof:
  Apply the radius criterion to the summability estimate for the derivative coefficients.
-/
theorem scalarFormalPowerSeries_derivative_radius_ge_of_geometric_bound
    {b : ℕ → ℂ} {D T : ℝ} {r : NNReal}
    (hT : 0 ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ D * T ^ n)
    (hTr : T * (r : ℝ) < 1) :
    (r : ENNReal) ≤ (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b)).radius :=
  FormalMultilinearSeries.le_radius_of_summable_norm
    (scalarFormalPowerSeries (powerSeriesDerivativeCoefficients b))
    (scalarFormalPowerSeries_derivative_summable_norm_of_geometric_bound hT hb hTr)

/--
%%handwave
name:
  A radius bound for the second derivative series
statement:
  Under the same geometric bound, \(\sum_{n \ge 0} (n+2)(n+1)b_{n+2} z^n\) has radius at least \(r\) whenever \(Tr<1\).
proof:
  Apply the radius criterion to the second-derivative summability estimate.
-/
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

/--
%%handwave
name:
  Convergence of the first derivative power series
statement:
  If \(r>0\) and \(\lVert b_n\rVert \le DT^n\) with \(T \ge 0\) and \(Tr<1\), then \(\sum_{n \ge 0} (n+1)b_{n+1} z^n\) is the canonical analytic sum on \(|z|<r\).
proof:
  Use the radius lower bound and restrict the canonical expansion to \(r\).
-/
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
%%handwave
name:
  Formal differentiation gives the shifted scalar coefficients
statement:
  Evaluating the formal derivative of \(\sum_{n \ge 0} b_n z^n\) on the unit tangent vector gives the scalar series \(\sum_{n \ge 0} (n+1)b_{n+1} z^n\).
proof:
  Compare each homogeneous multilinear coefficient on arbitrary inputs and reduce it to its value on the diagonal.
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
%%handwave
name:
  Termwise differentiation of a scalar complex power series
statement:
  If \(f(z)=\sum_{n \ge 0} b_n z^n\) on \(|z|<r\), then \(f'(z)=\sum_{n \ge 0} (n+1)b_{n+1} z^n\) on the same ball.
proof:
  Differentiate the Fréchet power series, evaluate the resulting linear map on \(1\), and identify its coefficients.
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

/--
%%handwave
name:
  Universal termwise differentiation for scalar power series
statement:
  Every scalar complex power-series expansion differentiates termwise on its convergence ball.
proof:
  Apply the preceding termwise-differentiation theorem.
-/
theorem scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem :
    ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem := by
  intro f b r h
  exact scalarFormalPowerSeries_deriv_hasFPowerSeriesOnBall h

/--
%%handwave
name:
  Convergence of the second derivative power series
statement:
  If \(r>0\) and \(\lVert b_n\rVert \le DT^n\) with \(T \ge 0\) and \(Tr<1\), then \(\sum_{n \ge 0} (n+2)(n+1)b_{n+2} z^n\) is analytic on \(|z|<r\).
proof:
  Use the second-derivative radius estimate and restrict the canonical expansion.
-/
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

/--
%%handwave
name:
  Value of a scalar power series at its center
statement:
  If \(f(z)=\sum_{n \ge 0} b_n z^n\) on a ball centered at \(0\), then \(f(0)=b_0\).
proof:
  The constant homogeneous coefficient is the value at the center.
-/
theorem scalarFormalPowerSeries_sum_zero
    {b : ℕ → ℂ} {r : ENNReal}
    (h : HasFPowerSeriesOnBall
      (scalarFormalPowerSeries b).sum (scalarFormalPowerSeries b) 0 r) :
    (scalarFormalPowerSeries b).sum 0 = b 0 := by
  have hz := h.coeff_zero (fun _ : Fin 0 => (0 : ℂ))
  simpa [scalarFormalPowerSeries, FormalMultilinearSeries.ofScalars] using hz.symm

/--
%%handwave
name:
  Value of the derivative series at the center
statement:
  The sum of \(\sum_{n \ge 0} (n+1)b_{n+1} z^n\) at \(z=0\) is \(b_1\).
proof:
  Apply the center-value formula to the shifted derivative coefficients.
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
%%handwave
name:
  The Frobenius recurrence implies the summed ODE
statement:
  Suppose the series for \(q\), \(y\), and \(y''\) converge absolutely at \(w\) and their coefficients satisfy the Frobenius recurrence. Then \(y''(w)=-\tfrac12 q(w)y(w)\).
proof:
  Use the Cauchy product to identify the convolution with \(q(w)y(w)\), scale by \(-\tfrac12\), and use uniqueness of sums.
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
%%handwave
name:
  The analytic Frobenius sum solves the ODE on its ball
statement:
  If the power series for \(q(z_0+w)\), \(y(w)\), and \(y''(w)\) converge on a ball and the coefficients satisfy the recurrence, then \(y''(w)=-\tfrac12 q(z_0+w)y(w)\) throughout that ball.
proof:
  At each point, extract the three sums and their absolute summability, then apply the summed recurrence identity.
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
%%handwave
name:
  Convergence of geometrically majorized Frobenius coefficients
statement:
  Assume \(0 \le C,D,T\), \(C \le 4T^2\), \(\lVert a_n\rVert \le CT^n\), \(\lVert b_0\rVert \le D\), \(\lVert b_1\rVert \le DT\), and \(Tr<1\). Then the recursive Frobenius series \(\sum_{n \ge 0} b_n z^n\) converges on \(|z|<r\).
proof:
  The Frobenius majorant gives \(\lVert b_n\rVert \le DT^n\); apply scalar power-series convergence.
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
%%handwave
name:
  Convergence of the first derivative Frobenius series
statement:
  Under the same geometric majorant hypotheses, \(\sum_{n \ge 0} (n+1)b_{n+1} z^n\) converges on \(|z|<r\).
proof:
  Combine the Frobenius coefficient majorant with convergence of the termwise derivative series.
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
%%handwave
name:
  Convergence of the second derivative Frobenius series
statement:
  Under the same hypotheses, \(\sum_{n \ge 0} (n+2)(n+1)b_{n+2} z^n\) converges on \(|z|<r\).
proof:
  Combine the coefficient majorant with convergence of the second derivative series.
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
%%handwave
name:
  Convergence of the normalized numerator series
statement:
  If the coefficient majorant holds, \(1 \le DT\), and \(Tr<1\), then the Frobenius series with \((b_0,b_1)=(0,1)\) converges on \(|z|<r\).
proof:
  Specialize the general convergence theorem and verify the two initial coefficient bounds.
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
%%handwave
name:
  Convergence of the normalized denominator series
statement:
  If the coefficient majorant holds, \(1 \le D\), and \(Tr<1\), then the Frobenius series with \((b_0,b_1)=(1,0)\) converges on \(|z|<r\).
proof:
  Specialize the general convergence theorem and verify the normalized initial bounds.
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

/--
%%handwave
name:
  Openness of a recentered power-series ball
statement:
  For \(z_0 \in ℂ\) and radius \(r\), the set \({z:|z-z_0|<r}\) is open.
proof:
  It is the inverse image of an open ball under the continuous translation \(z \mapsto z-z_0\).
-/
theorem isOpen_centeredBallDomain (z₀ : ℂ) (r : ENNReal) :
    IsOpen (centeredBallDomain z₀ r) := by
  change IsOpen ((fun z : ℂ => z - z₀) ⁻¹' Metric.eball (0 : ℂ) r)
  exact IsOpen.preimage (continuous_id.sub continuous_const) Metric.isOpen_eball

/--
%%handwave
name:
  The center lies in every positive recentered ball
statement:
  If \(r>0\), then \(z_0 \in {z:|z-z_0|<r}\).
proof:
  At the center the translated coordinate is \(0\), whose distance from \(0\) is less than \(r\).
-/
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

/--
%%handwave
name:
  Continuity of a centered Frobenius sum
statement:
  A convergent centered Frobenius sum is continuous at every point of its convergence ball.
proof:
  A power-series expansion is analytic, hence continuous, throughout its ball.
-/
theorem solution_continuousAt
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r)
    {w : ℂ} (hw : w ∈ Metric.eball (0 : ℂ) r) :
    ContinuousAt Y.solution w :=
  Y.has_series.continuousOn.continuousAt (Metric.isOpen_eball.mem_nhds hw)

/--
%%handwave
name:
  The stored first derivative is the actual derivative
statement:
  If \(y=\sum_{n \ge 0} b_n w^n\) and the stored field is \(y_1=\sum_{n \ge 0} (n+1)b_{n+1} w^n\) on the same ball, then \(y'(w)=y_1(w)\).
proof:
  Termwise differentiation gives a power series for \(y'\); uniqueness of power-series sums identifies it with the stored field.
-/
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
%%handwave
name:
  The stored second derivative is the derivative of the first
statement:
  If \(y_1=\sum_{n \ge 0} (n+1)b_{n+1} w^n\) and \(y_2=\sum_{n \ge 0} (n+2)(n+1)b_{n+2} w^n\), then \(y_1'(w)=y_2(w)\).
proof:
  Differentiate the first-derivative series, identify the twice-shifted coefficients, and use uniqueness.
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
%%handwave
name:
  Termwise differentiation proves the centered derivative theorem
statement:
  If scalar complex power series differentiate termwise, then every centered Frobenius sum has its stored first-derivative field as its actual derivative on the convergence ball.
proof:
  Apply termwise differentiation and uniqueness to each centered solution.
-/
theorem centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem) :
    CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem := by
  intro q z₀ a b₀ b₁ r Y w hw
  exact Y.solution_hasDerivAt_of_scalarFormalPowerSeriesDeriv hScalarDeriv hw

/--
%%handwave
name:
  Centered Frobenius sums have their stored first derivative
statement:
  Every centered Frobenius sum satisfies \(y'(w)=y_1(w)\) on its convergence ball.
proof:
  Use universal termwise differentiation in the preceding implication.
-/
theorem centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem :
    CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem :=
  centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem

/--
%%handwave
name:
  Termwise differentiation proves the centered second-derivative theorem
statement:
  If scalar complex power series differentiate termwise, then every stored first-derivative Frobenius sum satisfies \(y_1'(w)=y_2(w)\).
proof:
  Apply termwise differentiation to the first derivative series and identify its coefficients with the second derivative series.
-/
theorem centeredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem) :
    CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem := by
  intro q z₀ a b₀ b₁ r Y w hw
  exact Y.solutionDeriv_hasDerivAt_of_scalarFormalPowerSeriesDeriv hScalarDeriv hw

/--
%%handwave
name:
  Centered first-derivative sums have their stored second derivative
statement:
  Every centered Frobenius solution satisfies \(y_1'(w)=y_2(w)\) on its convergence ball.
proof:
  Use universal scalar termwise differentiation in the preceding implication.
-/
theorem centeredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem :
    CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem :=
  centeredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem

/--
%%handwave
name:
  Real smoothness of a complex power-series sum
statement:
  A complex power-series sum on a ball is \(C^3\) there when regarded as a map between real planes.
proof:
  Complex analyticity gives complex \(C^3\) regularity, which restricts to real \(C^3\) regularity.
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

/--
%%handwave
name:
  Third-order regularity of a centered Frobenius sum
statement:
  The analytic Frobenius sum \(y\) is real \(C^3\) on its centered convergence ball.
proof:
  Apply real smoothness of complex power-series sums to the series for \(y\).
-/
theorem solution_contDiffOn
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r) :
    ContDiffOn ℝ 3 Y.solution (Metric.eball (0 : ℂ) r) :=
  hasFPowerSeriesOnBall_contDiffOn_real_three Y.has_series

/--
%%handwave
name:
  Third-order regularity of the first derivative sum
statement:
  The stored first-derivative sum \(y_1\) is real \(C^3\) on the centered ball.
proof:
  Apply the same smoothness theorem to its convergent power series.
-/
theorem solutionDeriv_contDiffOn
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r) :
    ContDiffOn ℝ 3 Y.solutionDeriv (Metric.eball (0 : ℂ) r) :=
  hasFPowerSeriesOnBall_contDiffOn_real_three Y.has_deriv_series

/--
%%handwave
name:
  Third-order regularity of the second derivative sum
statement:
  The stored second-derivative sum \(y_2\) is real \(C^3\) on the centered ball.
proof:
  Apply the same smoothness theorem to the second-derivative series.
-/
theorem solutionSecondDeriv_contDiffOn
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusSolution q z₀ a b₀ b₁ r) :
    ContDiffOn ℝ 3 Y.solutionSecondDeriv (Metric.eball (0 : ℂ) r) :=
  hasFPowerSeriesOnBall_contDiffOn_real_three Y.has_second_deriv_series

/--
%%handwave
name:
  Regularity after recentering the Frobenius sum
statement:
  The function \(z \mapsto y(z-z_0)\) is real \(C^3\) on \(|z-z_0|<r\).
proof:
  Compose the \(C^3\) sum with the affine translation \(z \mapsto z-z_0\).
-/
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

/--
%%handwave
name:
  Regularity after recentering the first derivative sum
statement:
  The function \(z \mapsto y_1(z-z_0)\) is real \(C^3\) on \(|z-z_0|<r\).
proof:
  Compose the \(C^3\) first-derivative sum with translation.
-/
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

/--
%%handwave
name:
  Regularity after recentering the second derivative sum
statement:
  The function \(z \mapsto y_2(z-z_0)\) is real \(C^3\) on \(|z-z_0|<r\).
proof:
  Compose the \(C^3\) second-derivative sum with translation.
-/
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

/--
%%handwave
name:
  Continuity of the termwise first derivative at the center
statement:
  For a termwise centered Frobenius solution, the sum \(y_1\) is continuous at \(0\).
proof:
  Its convergent power-series expansion is analytic at the center.
-/
theorem solutionDeriv_continuousAt
    {q : ℂ → ℂ} {z₀ : ℂ} {a : ℕ → ℂ} {b₀ b₁ : ℂ} {r : ENNReal}
    (Y : CenteredSchwarzianFrobeniusTermwiseSolution q z₀ a b₀ b₁ r) :
    ContinuousAt Y.solutionDeriv 0 :=
  Y.has_deriv_series.hasFPowerSeriesAt.continuousAt

/--
%%handwave
name:
  The termwise first derivative has the stored second derivative
statement:
  For a termwise centered solution, \(y_1'(w)=y_2(w)\) throughout the convergence ball.
proof:
  Differentiate the series for \(y_1\), identify its coefficients with those of \(y_2\), and use uniqueness.
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

/--
%%handwave
name:
  Termwise differentiation proves the termwise second-derivative theorem
statement:
  Universal scalar termwise differentiation implies \(y_1'=y_2\) for every termwise centered Frobenius solution.
proof:
  Apply the preceding derivative calculation to each solution.
-/
theorem centeredSchwarzianFrobeniusTermwiseSolutionDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem) :
    CenteredSchwarzianFrobeniusTermwiseSolutionDerivHasDerivAtTheorem := by
  intro q z₀ a b₀ b₁ r Y w hw
  exact Y.solutionDeriv_hasDerivAt_of_scalarFormalPowerSeriesDeriv hScalarDeriv hw

/--
%%handwave
name:
  The termwise first derivative has its stored derivative
statement:
  Every termwise centered Frobenius solution satisfies \(y_1'(w)=y_2(w)\) on its convergence ball.
proof:
  Use universal scalar termwise differentiation.
-/
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

/--
%%handwave
name:
  Normalized denominator value at the center
statement:
  For the normalized denominator solution \(y_0\), \(y_0(0)=1\).
proof:
  This is its prescribed constant coefficient.
-/
theorem denominator_zero_eq_one
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.denominator.solution 0 = 1 :=
  P.denominator.solution_zero

/--
%%handwave
name:
  Normalized numerator value at the center
statement:
  For the normalized numerator solution \(y_1\), \(y_1(0)=0\).
proof:
  This is its prescribed constant coefficient.
-/
theorem numerator_zero_eq_zero
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.numerator.solution 0 = 0 :=
  P.numerator.solution_zero

/--
%%handwave
name:
  Normalized denominator derivative at the center
statement:
  For the normalized denominator \(y_0\), \(y_0'(0)=0\).
proof:
  This is its prescribed linear coefficient.
-/
theorem denominatorDeriv_zero_eq_zero
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.denominator.solutionDeriv 0 = 0 :=
  P.denominator.solutionDeriv_zero

/--
%%handwave
name:
  Normalized numerator derivative at the center
statement:
  For the normalized numerator \(y_1\), \(y_1'(0)=1\).
proof:
  This is its prescribed linear coefficient.
-/
theorem numeratorDeriv_zero_eq_one
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.numerator.solutionDeriv 0 = 1 :=
  P.numerator.solutionDeriv_zero

/--
%%handwave
name:
  Normalized Wronskian at the center
statement:
  For \(W=y_1'y_0-y_1y_0'\), the normalized initial data give \(W(0)=1\).
proof:
  Substitute the four center values and simplify.
-/
theorem wronskian_zero_eq_one
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.wronskian 0 = 1 := by
  rw [wronskian, P.numeratorDeriv_zero_eq_one, P.denominator_zero_eq_one,
    P.numerator_zero_eq_zero, P.denominatorDeriv_zero_eq_zero]
  ring

/--
%%handwave
name:
  The normalized denominator is nonzero at the center
statement:
  The normalized denominator satisfies \(y_0(0) \ne 0\).
proof:
  Use \(y_0(0)=1\).
-/
theorem denominator_ne_zero_at_zero
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a) :
    P.denominator.solution 0 ≠ 0 := by
  rw [P.denominator_zero_eq_one]
  norm_num

/--
%%handwave
name:
  The normalized Wronskian is nonzero at the center
statement:
  The normalized Wronskian satisfies \(W(0) \ne 0\).
proof:
  Use \(W(0)=1\).
-/
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

/--
%%handwave
name:
  Continuity of the denominator at the center
statement:
  The denominator Frobenius sum \(y_0\) is continuous at \(0\).
proof:
  Its convergent power series is analytic at the center.
-/
theorem denominator_continuousAt
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    {P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a}
    (_C : CenteredFrobeniusDerivativeContinuity P) :
    ContinuousAt P.denominator.solution 0 :=
  P.denominator.has_series.hasFPowerSeriesAt.continuousAt

/--
%%handwave
name:
  Continuity of the numerator at the center
statement:
  The numerator Frobenius sum \(y_1\) is continuous at \(0\).
proof:
  Its convergent power series is analytic at the center.
-/
theorem numerator_continuousAt
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    {P : CenteredNormalizedSchwarzianFrobeniusPrePair q V z₀ a}
    (_C : CenteredFrobeniusDerivativeContinuity P) :
    ContinuousAt P.numerator.solution 0 :=
  P.numerator.has_series.hasFPowerSeriesAt.continuousAt

/--
%%handwave
name:
  Continuity of the Wronskian at the center
statement:
  If \(y_0,y_1,y_0',y_1'\) are continuous at \(0\), then \(W=y_1'y_0-y_1y_0'\) is continuous there.
proof:
  Use closure of continuity under products and subtraction.
-/
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
%%handwave
name:
  A positive ball with nonvanishing denominator and Wronskian
statement:
  If \(y_0\) and \(W\) are continuous at \(0\) with \(y_0(0)=W(0)=1\), then some \(0<ρ \le r\) has \(y_0(w) \ne 0\) and \(W(w) \ne 0\) for \(|w|<ρ\).
proof:
  Continuity makes both functions nonzero near \(0\); intersect that neighborhood with the original convergence ball.
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

/--
%%handwave
name:
  Every normalized pre-pair admits a nonvanishing shrink
statement:
  Every normalized centered Frobenius pre-pair can be restricted to a positive smaller ball on which its denominator and Wronskian never vanish.
proof:
  The convergent derivative series give the needed continuity, so apply the nonvanishing-neighborhood argument.
-/
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
%%handwave
name:
  Continuity of the Frobenius quotient
statement:
  If \(y_0(z-z_0) \ne 0\) on the centered ball, then \(f(z)=y_1(z-z_0)/y_0(z-z_0)\) is continuous at every point of that ball.
proof:
  Recenter the continuous numerator and denominator sums and use continuity of division by a nonzero value.
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

/--
%%handwave
name:
  Regularity of the recentered numerator
statement:
  The function \(z \mapsto y_1(z-z_0)\) is real \(C^3\) on the centered ball.
proof:
  Apply the recentered regularity theorem to the numerator solution.
-/
theorem numerator_comp_contDiffOn
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ P.numerator.solution (z - z₀))
      (centeredBallDomain z₀ P.radius) :=
  P.numerator.solution_comp_sub_contDiffOn

/--
%%handwave
name:
  Regularity of the recentered denominator
statement:
  The function \(z \mapsto y_0(z-z_0)\) is real \(C^3\) on the centered ball.
proof:
  Apply the recentered regularity theorem to the denominator solution.
-/
theorem denominator_comp_contDiffOn
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ P.denominator.solution (z - z₀))
      (centeredBallDomain z₀ P.radius) :=
  P.denominator.solution_comp_sub_contDiffOn

/--
%%handwave
name:
  Regularity of the recentered numerator derivative
statement:
  The function \(z \mapsto y_1'(z-z_0)\) is real \(C^3\) on the centered ball.
proof:
  Apply recentered regularity to the stored numerator derivative.
-/
theorem numeratorDeriv_comp_contDiffOn
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ P.numerator.solutionDeriv (z - z₀))
      (centeredBallDomain z₀ P.radius) :=
  P.numerator.solutionDeriv_comp_sub_contDiffOn

/--
%%handwave
name:
  Regularity of the recentered denominator derivative
statement:
  The function \(z \mapsto y_0'(z-z_0)\) is real \(C^3\) on the centered ball.
proof:
  Apply recentered regularity to the stored denominator derivative.
-/
theorem denominatorDeriv_comp_contDiffOn
    {q : ℂ → ℂ} {V : Set ℂ} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair q V z₀ a) :
    ContDiffOn ℝ 3 (fun z : ℂ ↦ P.denominator.solutionDeriv (z - z₀))
      (centeredBallDomain z₀ P.radius) :=
  P.denominator.solutionDeriv_comp_sub_contDiffOn

/--
%%handwave
name:
  Third-order regularity of the Frobenius quotient
statement:
  If \(y_0\) never vanishes on the centered ball, then \(f=y_1/y_0\) is real \(C^3\) there.
proof:
  Multiply the \(C^3\) numerator by the reciprocal of the nonvanishing \(C^3\) denominator.
-/
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
%%handwave
name:
  Regularity of the quotient derivative formula
statement:
  If \(y_0\) never vanishes, then \(W/y_0^2\) is real \(C^3\) on the centered ball.
proof:
  The Wronskian is built from \(C^3\) fields; divide it by the nonvanishing square of \(y_0\).
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
%%handwave
name:
  Derivative of the normalized Frobenius quotient
statement:
  If the centered solutions have actual derivatives \(y_0',y_1'\) and \(y_0 \ne 0\), then \((y_1/y_0)'=W/y_0^2\) with \(W=y_1'y_0-y_1y_0'\).
proof:
  Apply the chain rule for recentering and the quotient rule.
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
%%handwave
name:
  Second derivative of the normalized Frobenius quotient
statement:
  If \(y_j'=v_j\) and \(v_j'=y_j''\) for \(j=0,1\), both solve \(y_j''=-\tfrac12 qy_j\), and \(y_0 \ne 0\), then \((W/y_0^2)'=-2Wy_0'/y_0^3\).
proof:
  Use the previously proved quotient-derivative calculation for the two ODE solutions; their second-derivative terms cancel in \(W'\).
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
%%handwave
name:
  Third derivative of the normalized Frobenius quotient
statement:
  Under the same derivative and ODE hypotheses, \((-2Wy_0'/y_0^3)'=-2Wy_0''/y_0^3+6W(y_0')^2/y_0⁴\).
proof:
  Apply the established second-derivative quotient calculation and simplify the recentered formulas.
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
%%handwave
name:
  Scalarization of a one-variable power series
statement:
  If \(f\) has a complex power-series expansion with formal series \(p\) at \(z_0\), then it also has the scalar expansion \(\sum_{n \ge 0} p_n (z-z_0)^n\) using the diagonal coefficients \(p_n\).
proof:
  One-variable multilinear terms equal their scalar diagonal coefficients times powers, so the two series have the same sum near \(z_0\).
-/
theorem hasFPowerSeriesAt_scalarFormalPowerSeries_coeff
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ}
    (h : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt f (scalarFormalPowerSeries p.coeff) z₀ := by
  rw [hasFPowerSeriesAt_iff] at h ⊢
  filter_upwards [h] with z hz
  simpa [scalarFormalPowerSeries] using hz

/--
%%handwave
name:
  Local holomorphicity gives scalar Taylor coefficients
statement:
  If \(q\) is holomorphic near \(z_0\), then for some \(R>0\) there are coefficients \(a_n\) with \(q(z_0+w)=\sum_{n \ge 0} a_n w^n\) on \(|w|<R\).
proof:
  Take a local analytic power series, recenter it at \(0\), scalarize its coefficients, and choose a positive radius below its convergence radius.
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

/--
%%handwave
name:
  An open set contains a positive centered ball
statement:
  If \(U \subseteq ℂ\) is open and \(z_0 \in U\), then some \(R>0\) satisfies \({z:|z-z_0|<R} \subseteq U\).
proof:
  Choose a metric ball from the neighborhood characterization of openness and reduce its radius by half.
-/
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
%%handwave
name:
  Scalar Taylor data give nested control radii
statement:
  Given a scalar Taylor expansion of \(q(z_0+w)\) and an open coordinate domain containing \(z_0\), there are \(0<s<R\) such that the expansion holds on \(|w|<R\) and \(|z-z_0|<R\) lies in the domain.
proof:
  Intersect the Taylor radius with an interior-domain radius and take \(s=R/2\).
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
%%handwave
name:
  Taylor control gives a Frobenius geometric majorant
statement:
  From a Taylor expansion on radius \(R\) and \(0<s<R\), one can choose \(C,D,T \ge 0\) and \(r>0\) with \(C \le 4T^2\), \(\lVert a_n\rVert \le CT^n\), \(1 \le D\), \(1 \le DT\), \(Tr<1\), and the radius-\(r\) ball inside the domain.
proof:
  Use the coefficient estimate \(\lVert a_n\rVert \le C/s^n\), enlarge \(T\) to dominate \(1,C,s^{-1}\), set \(D=1\), and shrink \(r\) below both \(R\) and \(1/(2T)\).
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
%%handwave
name:
  Coefficient majorants produce termwise normalized Frobenius pre-pairs
statement:
  If the Taylor coefficients of a holomorphic Schwarzian coefficient satisfy the geometric majorant data, then the normalized numerator and denominator Frobenius series, with their first and second derivative series, exist on a positive ball inside the coordinate domain.
proof:
  Apply the geometric-majorant constructor to the two normalized initial conditions.
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

/--
%%handwave
name:
  Forgetting termwise data gives a Frobenius pre-pair
statement:
  Existence of normalized termwise Frobenius pre-pairs implies existence of normalized pre-pairs with the same coefficient series and domain.
proof:
  Discard only the extra termwise derivative-series structure.
-/
theorem holomorphicSchwarzianFrobeniusPrePairExistence_of_termwise
    (h : HolomorphicSchwarzianFrobeniusTermwisePrePairExistenceTheorem) :
    HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem := by
  intro u S z₀ hz₀
  rcases h S hz₀ with ⟨a, ⟨P⟩⟩
  exact ⟨a, ⟨P.toPrePair⟩⟩

/--
%%handwave
name:
  Coefficient majorants produce normalized Frobenius pre-pairs
statement:
  The geometric coefficient majorant implies existence of a normalized convergent Frobenius pre-pair on a positive coordinate ball.
proof:
  First construct a termwise pre-pair, then forget the extra derivative-series structure.
-/
theorem holomorphicSchwarzianFrobeniusPrePairExistence_of_coefficientGeometricMajorant
    (hCoeff : HolomorphicSchwarzianCoefficientGeometricMajorantTheorem) :
    HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem :=
  holomorphicSchwarzianFrobeniusPrePairExistence_of_termwise
    (holomorphicSchwarzianFrobeniusTermwisePrePairExistence_of_coefficientGeometricMajorant
      hCoeff)

/--
%%handwave
name:
  Shrinking a pre-pair gives a nonvanishing Frobenius pair
statement:
  If a normalized pre-pair exists and every pre-pair has a positive shrink on which \(y_0\) and \(W\) are nonzero, then a normalized Frobenius pair exists.
proof:
  Choose the pre-pair and its shrink, then restrict both solutions and their coefficient expansion.
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
%%handwave
name:
  Every pre-pair produces a full Frobenius pair
statement:
  Existence of a normalized pre-pair implies existence of a normalized pair with nonvanishing denominator and Wronskian.
proof:
  Apply the universal nonvanishing-shrink theorem to the chosen pre-pair.
-/
theorem holomorphicSchwarzianFrobeniusPairExistence_of_prePair
    (hPre : HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem) :
    HolomorphicSchwarzianFrobeniusPairExistenceTheorem :=
  holomorphicSchwarzianFrobeniusPairExistence_of_prePair_and_shrink
    hPre centeredFrobeniusNonvanishingShrinkTheorem

/--
%%handwave
name:
  Coefficient majorants produce full normalized Frobenius pairs
statement:
  A geometric majorant for the local Schwarzian Taylor coefficients yields two normalized solutions of \(y''+\tfrac12 qy=0\) on a positive ball where the denominator and Wronskian are nonzero.
proof:
  Construct a pre-pair from the majorant and apply the automatic nonvanishing shrink.
-/
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

end

end JJMath
