import JJMath.Hyperbolic.Schwarzian.Developing.MetricRecovery

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace LocalLiouvilleSchwarzianUniquenessData

/-- Build the uniqueness data from the normalized pullback candidate. -/
def ofCandidate
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (hu : u.SolvesLiouvilleEquation) (hPreconnected : IsPreconnected N.domain) :
    LocalLiouvilleSchwarzianUniquenessData N C where
  original_solvesLiouville := hu
  pullback_solvesLiouville := C.solvesLiouville
  domain_preconnected := hPreconnected
  pullback_domain_eq := C.coordinateDomain_eq
  same_schwarzian_coefficient := C.same_schwarzian_coefficient
  base_logDensity_eq := C.base_logDensity_eq
  base_uZ_eq := C.base_uZ_eq

end LocalLiouvilleSchwarzianUniquenessData

/--
Concrete calculus data for the Riccati reduction.

This is the part of the metric-recovery proof that is closest to the classical
calculation.  If `U_z,V_z` are the first Wirtinger derivatives of the original
and pullback log-densities, and `U_zz,V_zz` are their `z` derivatives, then
equality of the half-Schwarzian expressions

`V_zz - V_z^2 = U_zz - U_z^2`

implies that `α = V_z - U_z` satisfies

`α_z = α * (V_z + U_z)`.

The last field is deliberately still a boundary: once `α = 0`, one needs the
ordinary first-derivative uniqueness argument that identifies the two
log-density functions.
-/
structure LocalLiouvilleSchwarzianRiccatiReductionCalculusData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (_data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- First Wirtinger derivative of the original log-density. -/
  originalZ : ℂ → ℂ
  /-- First Wirtinger derivative of the pullback log-density. -/
  pullbackZ : ℂ → ℂ
  /-- Second `z` derivative of the original log-density. -/
  originalZZ : ℂ → ℂ
  /-- Second `z` derivative of the pullback log-density. -/
  pullbackZZ : ℂ → ℂ
  /-- The original first derivative has derivative `originalZZ`. -/
  originalZ_has_deriv_at :
    ∀ z, z ∈ N.domain → HasDerivAt originalZ (originalZZ z) z
  /-- The pullback first derivative has derivative `pullbackZZ`. -/
  pullbackZ_has_deriv_at :
    ∀ z, z ∈ N.domain → HasDerivAt pullbackZ (pullbackZZ z) z
  /-- Equality of the two half-Schwarzian expressions. -/
  same_half_schwarzian :
    ∀ z, z ∈ N.domain →
      pullbackZZ z - pullbackZ z ^ 2 = originalZZ z - originalZ z ^ 2
  /-- The normalized base data gives `V_z(z₀)=U_z(z₀)`. -/
  base_first_derivative_eq : pullbackZ z₀ = originalZ z₀
  /--
  If the first Wirtinger derivatives agree on the domain, then the log-density
  functions agree there.
  -/
  logDensity_eq_of_first_derivative_eq :
    (∀ z, z ∈ N.domain → pullbackZ z - originalZ z = 0) →
      ∀ z, z ∈ N.domain →
        u.logDensity z = C.conformalFactor.logDensity z

/--
Canonical version of the Riccati calculus data.

Here the symbolic first and second derivatives are fixed to be the actual
Frechet-Wirtinger fields carried by the two conformal factors:
`u.wirtingerZ`, `u.wirtingerZZ`, and their pullback analogues.  Thus the
remaining assumptions are no longer allowed to hide arbitrary choices of
derivative fields; they are exactly the analytic facts still needed for these
canonical functions.
-/
structure LocalLiouvilleSchwarzianCanonicalRiccatiCalculusData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- The original canonical first Wirtinger field has derivative `u_zz`. -/
  originalZ_has_deriv_at :
    ∀ z, z ∈ N.domain → HasDerivAt u.wirtingerZ (u.wirtingerZZ z) z
  /-- The pullback canonical first Wirtinger field has derivative `v_zz`. -/
  pullbackZ_has_deriv_at :
    ∀ z, z ∈ N.domain →
      HasDerivAt C.conformalFactor.wirtingerZ (C.conformalFactor.wirtingerZZ z) z
  /-- The two canonical half-Schwarzian expressions agree on the normalized domain. -/
  same_half_schwarzian :
    ∀ z, z ∈ N.domain →
      C.conformalFactor.halfSchwarzianCoefficient z = u.halfSchwarzianCoefficient z

/--
Canonical Riccati calculus data with the Schwarzian equality stated at the
usual metric-Schwarzian scale.

This is often the output of the projective-connection calculation: both sides
compute the same coefficient `2 * (u_zz - u_z^2)`.  The passage from this
metric-scaled equality to the half-Schwarzian equality needed by the Riccati
algebra is just cancellation of the nonzero scalar `2`.
-/
structure LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- The original canonical first Wirtinger field has derivative `u_zz`. -/
  originalZ_has_deriv_at :
    ∀ z, z ∈ N.domain → HasDerivAt u.wirtingerZ (u.wirtingerZZ z) z
  /-- The pullback canonical first Wirtinger field has derivative `v_zz`. -/
  pullbackZ_has_deriv_at :
    ∀ z, z ∈ N.domain →
      HasDerivAt C.conformalFactor.wirtingerZ (C.conformalFactor.wirtingerZZ z) z
  /-- The two usual metric Schwarzian coefficients agree on the normalized domain. -/
  same_metric_schwarzian :
    ∀ z, z ∈ N.domain →
      LocalSchwarzianData.metricSchwarzianCoefficient
        C.conformalFactor.halfSchwarzianCoefficient z =
      LocalSchwarzianData.metricSchwarzianCoefficient
        u.halfSchwarzianCoefficient z

namespace LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData

/--
%%handwave
name:
  Equality of half-Schwarzians from metric equality
statement:
  If \(2(V_{zz}-V_z²)=2(U_{zz}-U_z²)\) on \(Ω\), then \(V_{zz}-V_z²=U_{zz}-U_z²\) there.
proof:
  Cancel the nonzero complex factor \(2\).
-/
theorem same_half_schwarzian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (A : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData data) :
    ∀ z, z ∈ N.domain →
      C.conformalFactor.halfSchwarzianCoefficient z =
        u.halfSchwarzianCoefficient z := by
  intro z hz
  have h :
      (2 : ℂ) * C.conformalFactor.halfSchwarzianCoefficient z =
        (2 : ℂ) * u.halfSchwarzianCoefficient z := by
    simpa [LocalSchwarzianData.metricSchwarzianCoefficient] using
      A.same_metric_schwarzian z hz
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

/--
Metric-scaled canonical Riccati data specialize to the half-Schwarzian
canonical calculus package.
-/
def toCanonicalRiccatiCalculusData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (A : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData data) :
    LocalLiouvilleSchwarzianCanonicalRiccatiCalculusData data where
  originalZ_has_deriv_at := A.originalZ_has_deriv_at
  pullbackZ_has_deriv_at := A.pullbackZ_has_deriv_at
  same_half_schwarzian := A.same_half_schwarzian

end LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData

/--
Canonical metric Riccati data stated with the Frechet-Wirtinger `∂z`
operator.

Unlike `LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData`, this does
not ask the fields `u_z` and `v_z` to be complex-holomorphic.  It records the
honest local calculus available for arbitrary real conformal factors: the
`z`-Wirtinger derivative of `u_z` is `u_zz`, and similarly on the pullback
side.
-/
structure LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (_data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- The original canonical first Wirtinger field is real differentiable. -/
  originalZ_differentiableAt :
    ∀ z, z ∈ N.domain → DifferentiableAt ℝ u.wirtingerZ z
  /-- The pullback canonical first Wirtinger field is real differentiable. -/
  pullbackZ_differentiableAt :
    ∀ z, z ∈ N.domain → DifferentiableAt ℝ C.conformalFactor.wirtingerZ z
  /-- The two usual metric Schwarzian coefficients agree on the normalized domain. -/
  same_metric_schwarzian :
    ∀ z, z ∈ N.domain →
      LocalSchwarzianData.metricSchwarzianCoefficient
        C.conformalFactor.halfSchwarzianCoefficient z =
      LocalSchwarzianData.metricSchwarzianCoefficient
        u.halfSchwarzianCoefficient z

namespace LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData

/--
%%handwave
name:
  Equality of half-Schwarzians in Wirtinger form
statement:
  For real log-densities \(U,V\) on \(Ω\), equality of their metric Schwarzians implies \(V_{zz}-V_z²=U_{zz}-U_z²\) on \(Ω\).
proof:
  Expand the metric coefficients and cancel \(2\).
-/
theorem same_half_schwarzian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (A : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData data) :
    ∀ z, z ∈ N.domain →
      C.conformalFactor.halfSchwarzianCoefficient z =
        u.halfSchwarzianCoefficient z := by
  intro z hz
  have h :
      (2 : ℂ) * C.conformalFactor.halfSchwarzianCoefficient z =
        (2 : ℂ) * u.halfSchwarzianCoefficient z := by
    simpa [LocalSchwarzianData.metricSchwarzianCoefficient] using
      A.same_metric_schwarzian z hz
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

/--
%%handwave
name:
  The Wirtinger Riccati equation
statement:
  For \(α=V_z-U_z\) and \(β=V_z+U_z\), equality of half-Schwarzians gives \(∂_zα=αβ\) on \(Ω\).
proof:
  Identify \(∂_zα\) with \(V_{zz}-U_{zz}\), subtract the half-Schwarzian identities, and factor the difference of squares.
-/
theorem alpha_frechetDZValue_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (A : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData data) :
    ∀ z, z ∈ N.domain →
      frechetDZValue
          (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w) z =
        (C.conformalFactor.wirtingerZ z - u.wirtingerZ z) *
          (C.conformalFactor.wirtingerZ z + u.wirtingerZ z) := by
  intro z hz
  calc
    frechetDZValue
        (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w) z
        = C.conformalFactor.wirtingerZZ z - u.wirtingerZZ z := by
          rw [frechetDZValue_sub_of_differentiableAt
            (A.pullbackZ_differentiableAt z hz) (A.originalZ_differentiableAt z hz)]
          rfl
    _ = (C.conformalFactor.wirtingerZ z - u.wirtingerZ z) *
          (C.conformalFactor.wirtingerZ z + u.wirtingerZ z) := by
          have h := A.same_half_schwarzian z hz
          simp [LocalConformalFactor.halfSchwarzianCoefficient] at h
          linear_combination h

end LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData

/--
The genuine first-order system behind local Liouville-Schwarzian uniqueness.

For `φ = v - u` and `α = v_z - u_z`, the same-Schwarzian calculation gives
the `z`-equation

`∂z α = α * (v_z + u_z)`.

The two Liouville equations give the complementary equation

`∂bar α = (1 / 4) * (exp (2v) - exp (2u))`.

This is the honest two-real-dimensional system.  It replaces the false
temptation to treat `α` as holomorphic before metric recovery has been proved.
-/
structure LocalLiouvilleSchwarzianFirstOrderSystemData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- The `z`-Riccati equation for `α = v_z - u_z`. -/
  wirtinger :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData data
  /-- The equation `∂z φ = α` for `φ = v - u`. -/
  phi_frechetDZValue_eq :
    ∀ z, z ∈ N.domain →
      frechetDZValue
          (fun w : ℂ ↦
            ((C.conformalFactor.logDensity w - u.logDensity w : ℝ) : ℂ)) z =
        C.conformalFactor.wirtingerZ z - u.wirtingerZ z
  /-- The complementary Liouville equation for `∂bar α`. -/
  alpha_frechetDBarValue_eq :
    ∀ z, z ∈ N.domain →
      frechetDBarValue
          (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w) z =
        (1 / 4 : ℂ) *
          ((Real.exp (2 * C.conformalFactor.logDensity z) : ℂ) -
            (Real.exp (2 * u.logDensity z) : ℂ))
  /-- The normalized base data gives `φ z₀ = 0`. -/
  phi_base_eq_zero :
    C.conformalFactor.logDensity z₀ - u.logDensity z₀ = 0
  /-- The normalized base data gives `α z₀ = 0`. -/
  alpha_base_eq_zero :
    C.conformalFactor.wirtingerZ z₀ - u.wirtingerZ z₀ = 0

namespace LocalLiouvilleSchwarzianFirstOrderSystemData

/--
%%handwave
name:
  The Riccati equation carried by the first-order system
statement:
  The first-order Liouville–Schwarzian system satisfies \(∂_z(V_z-U_z)=(V_z-U_z)(V_z+U_z)\) on \(Ω\).
proof:
  Apply the Wirtinger Riccati equation included in the system.
-/
theorem alpha_frechetDZValue_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (F : LocalLiouvilleSchwarzianFirstOrderSystemData data) :
    ∀ z, z ∈ N.domain →
      frechetDZValue
          (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w) z =
        (C.conformalFactor.wirtingerZ z - u.wirtingerZ z) *
          (C.conformalFactor.wirtingerZ z + u.wirtingerZ z) :=
  F.wirtinger.alpha_frechetDZValue_eq

end LocalLiouvilleSchwarzianFirstOrderSystemData

/--
The divided difference of `x ↦ exp (2x)`, with the derivative value inserted
on the diagonal.
-/
def realExpTwoDividedDifference (u v : ℝ) : ℝ :=
  if v - u = 0 then
    2 * Real.exp (2 * u)
  else
    (Real.exp (2 * v) - Real.exp (2 * u)) / (v - u)

/-- The continuous extension of `sinh x / x` across `x = 0`. -/
def realSinhc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sinh x / x

/--
%%handwave
name:
  The hyperbolic sine quotient as a divided slope
statement:
  The function equal to \(1\) at \(0\) and \(sinh(x)/x\) otherwise is the divided slope of \(sinh\) from \(0\) to \(x\).
proof:
  At zero use \(sinh'(0)=1\); away from zero unfold the divided slope and use \(sinh(0)=0\).
-/
theorem realSinhc_eq_dslope :
    realSinhc = dslope Real.sinh 0 := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [realSinhc, dslope_same, Real.deriv_sinh]
  · rw [realSinhc, if_neg hx, dslope_of_ne (f := Real.sinh) hx]
    simp [slope, Real.sinh_zero, div_eq_inv_mul]

/--
%%handwave
name:
  Continuity of the hyperbolic sine quotient
statement:
  The completion \(sinhc(0)=1\) and \(sinhc(x)=sinh(x)/x\) for \(x≠0\) is continuous on \(ℝ\).
proof:
  Express it as the divided slope of the differentiable function \(sinh\).
-/
theorem realSinhc_continuous : Continuous realSinhc := by
  rw [realSinhc_eq_dslope]
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact continuousAt_dslope_same.mpr Real.differentiableAt_sinh
  · exact (continuousAt_dslope_of_ne (f := Real.sinh) (a := 0) (b := x) hx).2
      Real.continuous_sinh.continuousAt

/--
%%handwave
name:
  A symmetric exponential-difference formula
statement:
  For all \(u,v∈ℝ\), \(e^{2v}-e^{2u}=2e^{u+v}sinh(v-u)\).
proof:
  Expand the hyperbolic sine and simplify using the exponential laws.
-/
theorem real_exp_two_sub_eq_sinh (u v : ℝ) :
    Real.exp (2 * v) - Real.exp (2 * u) =
      2 * Real.exp (u + v) * Real.sinh (v - u) := by
  have h2v : 2 * v = v + v := by ring
  have h2u : 2 * u = u + u := by ring
  rw [Real.sinh_eq, h2v, h2u, Real.exp_add, Real.exp_add, Real.exp_sub,
    Real.exp_neg]
  rw [Real.exp_sub, Real.exp_add]
  field_simp [Real.exp_ne_zero]

/--
%%handwave
name:
  The exponential divided difference in hyperbolic-sine form
statement:
  The completed divided difference of \(x↦e^{2x}\) between \(u\) and \(v\) equals \(2e^{u+v}sinhc(v-u)\).
proof:
  Treat \(u=v\) directly; otherwise substitute the exponential-difference formula and divide by \(v-u\).
-/
theorem realExpTwoDividedDifference_eq_exp_sinhc (u v : ℝ) :
    realExpTwoDividedDifference u v =
      2 * Real.exp (u + v) * realSinhc (v - u) := by
  by_cases h : v - u = 0
  · have hv : v = u := sub_eq_zero.mp h
    subst v
    simp [realExpTwoDividedDifference, realSinhc]
    ring_nf
  · rw [realExpTwoDividedDifference, realSinhc, if_neg h, if_neg h]
    rw [real_exp_two_sub_eq_sinh u v]
    field_simp [h]

/--
Pure real continuity target for the divided difference of `x ↦ exp (2x)`.

This is the remaining scalar calculus fact behind continuity of the Liouville
linearized potential.
-/
def RealExpTwoDividedDifferenceContinuityTheorem : Prop :=
  Continuous fun p : ℝ × ℝ ↦ realExpTwoDividedDifference p.1 p.2

/--
%%handwave
name:
  Continuity of the exponential divided difference
statement:
  The function equal to \((e^{2v}-e^{2u})/(v-u)\) off the diagonal and \(2e^{2u}\) on it is continuous on \(ℝ²\).
proof:
  Rewrite it as \(2e^{u+v}sinhc(v-u)\).
-/
theorem realExpTwoDividedDifference_continuous :
    RealExpTwoDividedDifferenceContinuityTheorem := by
  have heq :
      (fun p : ℝ × ℝ ↦ realExpTwoDividedDifference p.1 p.2) =
        fun p : ℝ × ℝ ↦ 2 * Real.exp (p.1 + p.2) * realSinhc (p.2 - p.1) := by
    funext p
    exact realExpTwoDividedDifference_eq_exp_sinhc p.1 p.2
  rw [RealExpTwoDividedDifferenceContinuityTheorem, heq]
  exact
    (continuous_const.mul
      (Real.continuous_exp.comp (continuous_fst.add continuous_snd))).mul
      (realSinhc_continuous.comp (continuous_snd.sub continuous_fst))

/--
Scalar difference form of the local Liouville-Schwarzian uniqueness problem.

This keeps the same first-order data, but also exposes the second-order scalar
equation for `φ = v - u`:

`Δ φ = exp (2v) - exp (2u)`.

It is a useful elliptic formulation of the remaining local uniqueness boundary.
-/
structure LocalLiouvilleSchwarzianScalarDifferenceData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- The genuine first-order system. -/
  firstOrder :
    LocalLiouvilleSchwarzianFirstOrderSystemData data
  /-- The scalar difference of the two Liouville equations. -/
  phi_laplacian_eq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian
          (fun w : ℂ ↦ C.conformalFactor.logDensity w - u.logDensity w) z =
        Real.exp (2 * C.conformalFactor.logDensity z) -
          Real.exp (2 * u.logDensity z)

namespace LocalLiouvilleSchwarzianScalarDifferenceData

/--
The pointwise coefficient which linearizes the scalar Liouville difference.

For `φ = V - U`, the difference `exp (2V) - exp (2U)` can be written as
`a φ`.  At zeros of `φ` we choose the harmless limiting-looking value
`2 * exp (2U)`; away from zeros we use the exact quotient.
-/
def linearizedPotential
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (_E : LocalLiouvilleSchwarzianScalarDifferenceData data) (z : ℂ) : ℝ :=
  if C.conformalFactor.logDensity z - u.logDensity z = 0 then
    2 * Real.exp (2 * u.logDensity z)
  else
    (Real.exp (2 * C.conformalFactor.logDensity z) -
        Real.exp (2 * u.logDensity z)) /
      (C.conformalFactor.logDensity z - u.logDensity z)

/--
%%handwave
name:
  Exact linearization of the Liouville exponential
statement:
  For \(φ=V-U\) and the divided-difference potential \(a\), \(aφ=e^{2V}-e^{2U}\) pointwise.
proof:
  If \(φ=0\) both sides vanish; otherwise cancel \(φ\) in the quotient.
-/
theorem linearizedPotential_mul_phi_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianScalarDifferenceData data) :
    ∀ z,
      E.linearizedPotential z *
          (C.conformalFactor.logDensity z - u.logDensity z) =
        Real.exp (2 * C.conformalFactor.logDensity z) -
          Real.exp (2 * u.logDensity z) := by
  intro z
  by_cases hφ : C.conformalFactor.logDensity z - u.logDensity z = 0
  · have hlog : C.conformalFactor.logDensity z = u.logDensity z :=
      sub_eq_zero.mp hφ
    simp [linearizedPotential, hlog]
  · simp [linearizedPotential, hφ]

/--
%%handwave
name:
  The Liouville potential is an exponential divided difference
statement:
  At each \(z\), the linearized potential is the completed divided difference of \(x↦e^{2x}\) between \(U(z)\) and \(V(z)\).
proof:
  The two sides have identical piecewise definitions.
-/
theorem linearizedPotential_eq_realExpTwoDividedDifference
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianScalarDifferenceData data) (z : ℂ) :
    E.linearizedPotential z =
      realExpTwoDividedDifference
        (u.logDensity z) (C.conformalFactor.logDensity z) := by
  rfl

/--
%%handwave
name:
  Continuity of the linearized Liouville potential
statement:
  If the completed exponential divided difference is continuous on \(ℝ²\), then \(a(z)\) is continuous on \(Ω\).
proof:
  Compose it with the continuous map \(z↦(U(z),V(z))\).
-/
theorem linearizedPotential_continuousOn_of_realExpTwoDividedDifferenceContinuous
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianScalarDifferenceData data)
    (hdiv : RealExpTwoDividedDifferenceContinuityTheorem) :
    ContinuousOn E.linearizedPotential N.domain := by
  have hu :
      ContinuousOn u.logDensity N.domain :=
    u.logDensity_contDiffOn.continuousOn.mono
      (fun z hz ↦ D.domain_subset (N.normalized.domain_subset_original hz))
  have hC :
      ContinuousOn C.conformalFactor.logDensity N.domain := by
    have hC' :
        ContinuousOn C.conformalFactor.logDensity
          C.conformalFactor.coordinateDomain :=
      C.conformalFactor.logDensity_contDiffOn.continuousOn
    simpa [data.pullback_domain_eq] using hC'
  have hpair :
      ContinuousOn
        (fun z : ℂ ↦ (u.logDensity z, C.conformalFactor.logDensity z))
        N.domain :=
    hu.prodMk hC
  have hcomp :
      ContinuousOn
        (fun z : ℂ ↦
          realExpTwoDividedDifference
            (u.logDensity z) (C.conformalFactor.logDensity z))
        N.domain :=
    hdiv.continuousOn.comp' hpair (fun _ _ ↦ Set.mem_univ _)
  exact hcomp.congr fun z _hz ↦
    (E.linearizedPotential_eq_realExpTwoDividedDifference z).symm

/--
%%handwave
name:
  Vanishing of the density difference at the base point
statement:
  For \(φ=V-U\), the normalized data give \(φ(z₀)=0\).
proof:
  Use the base-value condition in the first-order system.
-/
theorem phi_base_eq_zero
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianScalarDifferenceData data) :
    C.conformalFactor.logDensity z₀ - u.logDensity z₀ = 0 :=
  E.firstOrder.phi_base_eq_zero

/--
%%handwave
name:
  Vanishing of the Wirtinger difference at the base point
statement:
  For \(α=V_z-U_z\), the normalized data give \(α(z₀)=0\).
proof:
  Use the base first-derivative condition in the first-order system.
-/
theorem phi_wirtingerZ_base_eq_zero
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianScalarDifferenceData data) :
    C.conformalFactor.wirtingerZ z₀ - u.wirtingerZ z₀ = 0 :=
  E.firstOrder.alpha_base_eq_zero

end LocalLiouvilleSchwarzianScalarDifferenceData

/--
Linearized scalar difference form of the local Liouville-Schwarzian uniqueness
problem.

This packages the scalar equation as

`Δ φ = a φ`, where `φ = V - U` and `a` is the pointwise linearized
Liouville coefficient.
-/
structure LocalLiouvilleSchwarzianLinearizedScalarDifferenceData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- The nonlinear scalar difference data. -/
  scalar :
    LocalLiouvilleSchwarzianScalarDifferenceData data
  /-- The real coefficient in the linearized equation. -/
  potential : ℂ → ℝ
  /-- The coefficient linearizes the nonlinear Liouville difference. -/
  potential_mul_phi_eq :
    ∀ z, z ∈ N.domain →
      potential z * (C.conformalFactor.logDensity z - u.logDensity z) =
        Real.exp (2 * C.conformalFactor.logDensity z) -
          Real.exp (2 * u.logDensity z)
  /-- The scalar difference equation in linear form. -/
  phi_laplacian_linear_eq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian
          (fun w : ℂ ↦ C.conformalFactor.logDensity w - u.logDensity w) z =
        potential z * (C.conformalFactor.logDensity z - u.logDensity z)

namespace LocalLiouvilleSchwarzianLinearizedScalarDifferenceData

/--
%%handwave
name:
  The linearized density difference vanishes initially
statement:
  The linearized scalar data satisfy \(V(z₀)-U(z₀)=0\).
proof:
  Project the base equality from the nonlinear scalar data.
-/
theorem phi_base_eq_zero
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data) :
    C.conformalFactor.logDensity z₀ - u.logDensity z₀ = 0 :=
  E.scalar.phi_base_eq_zero

/--
%%handwave
name:
  The linearized Wirtinger difference vanishes initially
statement:
  The linearized scalar data satisfy \(V_z(z₀)-U_z(z₀)=0\).
proof:
  Project the base first-derivative equality from the nonlinear scalar data.
-/
theorem phi_wirtingerZ_base_eq_zero
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data) :
    C.conformalFactor.wirtingerZ z₀ - u.wirtingerZ z₀ = 0 :=
  E.scalar.phi_wirtingerZ_base_eq_zero

/--
%%handwave
name:
  Zero real differential from zero Wirtinger derivative
statement:
  For real \(φ=V-U\), \(∂_zφ(z₀)=0\) implies \(Dφ(z₀)=0\).
proof:
  Wirtinger reconstruction determines the full real differential of a real function from \(∂_zφ\).
-/
theorem phi_fderiv_base_eq_zero
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data) :
    fderiv ℝ
        (fun w : ℂ ↦ C.conformalFactor.logDensity w - u.logDensity w) z₀ =
      0 := by
  have hCDiff : DifferentiableAt ℝ C.conformalFactor.logDensity z₀ :=
    (C.conformalFactor.logDensity_contDiffOn.contDiffAt
      (by
        have hzC : z₀ ∈ C.conformalFactor.coordinateDomain := by
          simpa [data.pullback_domain_eq] using N.base_mem
        exact C.conformalFactor.isOpen_coordinateDomain.mem_nhds hzC)).differentiableAt
      (by norm_num)
  have huDiff : DifferentiableAt ℝ u.logDensity z₀ :=
    (u.logDensity_contDiffOn.contDiffAt
      (u.isOpen_coordinateDomain.mem_nhds
        (D.domain_subset (N.normalized.domain_subset_original N.base_mem)))).differentiableAt
      (by norm_num)
  have hDiff :
      DifferentiableAt ℝ
        (fun w : ℂ ↦ C.conformalFactor.logDensity w - u.logDensity w) z₀ :=
    hCDiff.sub huDiff
  have hZ :
      frechetDZValue
          (fun w : ℂ ↦
            ((C.conformalFactor.logDensity w - u.logDensity w : ℝ) : ℂ)) z₀ =
        0 := by
    rw [E.scalar.firstOrder.phi_frechetDZValue_eq z₀ N.base_mem]
    exact E.scalar.firstOrder.alpha_base_eq_zero
  exact fderiv_real_eq_zero_of_frechetDZValue_complex_ofReal_eq_zero hDiff hZ

end LocalLiouvilleSchwarzianLinearizedScalarDifferenceData

/--
Linear elliptic Cauchy-data form of the local Liouville-Schwarzian uniqueness
problem.

The scalar equation is already linearized as `Δ φ = a φ`, and the normalized
two-jet data is now exposed as the standard Cauchy data
`φ z₀ = 0` and `dφ z₀ = 0`.
-/
structure LocalLiouvilleSchwarzianLinearEllipticCauchyData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- The linearized scalar difference data. -/
  linearized :
    LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data
  /-- The scalar difference vanishes at the base point. -/
  phi_base_eq_zero :
    C.conformalFactor.logDensity z₀ - u.logDensity z₀ = 0
  /-- The full real differential of the scalar difference vanishes at the base point. -/
  phi_fderiv_base_eq_zero :
    fderiv ℝ
        (fun w : ℂ ↦ C.conformalFactor.logDensity w - u.logDensity w) z₀ =
      0

namespace LocalLiouvilleSchwarzianLinearEllipticCauchyData

/--
%%handwave
name:
  The linear elliptic equation carried by the Cauchy data
statement:
  For \(φ=V-U\), \(Δφ(z)=a(z)φ(z)\) for every \(z∈Ω\).
proof:
  Project the linearized scalar equation.
-/
theorem phi_laplacian_linear_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianLinearEllipticCauchyData data) :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian
          (fun w : ℂ ↦ C.conformalFactor.logDensity w - u.logDensity w) z =
        E.linearized.potential z *
          (C.conformalFactor.logDensity z - u.logDensity z) :=
  E.linearized.phi_laplacian_linear_eq

end LocalLiouvilleSchwarzianLinearEllipticCauchyData

/--
Closed first-order linear system form of the local Liouville-Schwarzian
uniqueness problem.

After linearizing the scalar Liouville difference, the pair
`φ = V - U`, `α = V_z - U_z` satisfies a first-order linear system:

* `∂z φ = α`,
* `∂z α = α * β`,
* `∂bar α = γ * φ`.

Together with `φ z₀ = 0` and `α z₀ = 0`, this is the pathwise ODE uniqueness
form of the remaining local argument.
-/
structure LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- The linearized scalar difference data. -/
  linearized :
    LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data
  /-- The coefficient in `∂z α = α * β`. -/
  beta : ℂ → ℂ
  /-- The coefficient in `∂bar α = γ * φ`. -/
  gamma : ℂ → ℂ
  /-- `β = V_z + U_z` on the normalized domain. -/
  beta_eq :
    ∀ z, z ∈ N.domain →
      beta z = C.conformalFactor.wirtingerZ z + u.wirtingerZ z
  /-- `γ = a/4`, where `a` is the linearized scalar Liouville coefficient. -/
  gamma_eq :
    ∀ z, z ∈ N.domain →
      gamma z = (1 / 4 : ℂ) * (linearized.potential z : ℂ)
  /-- The equation `∂z φ = α`. -/
  phi_frechetDZValue_eq :
    ∀ z, z ∈ N.domain →
      frechetDZValue
          (fun w : ℂ ↦
            ((C.conformalFactor.logDensity w - u.logDensity w : ℝ) : ℂ)) z =
        C.conformalFactor.wirtingerZ z - u.wirtingerZ z
  /-- The equation `∂z α = α * β`. -/
  alpha_frechetDZValue_eq :
    ∀ z, z ∈ N.domain →
      frechetDZValue
          (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w) z =
        (C.conformalFactor.wirtingerZ z - u.wirtingerZ z) * beta z
  /-- The equation `∂bar α = γ * φ`. -/
  alpha_frechetDBarValue_eq :
    ∀ z, z ∈ N.domain →
      frechetDBarValue
          (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w) z =
        gamma z *
          ((C.conformalFactor.logDensity z - u.logDensity z : ℝ) : ℂ)
  /-- The normalized base data gives `φ z₀ = 0`. -/
  phi_base_eq_zero :
    C.conformalFactor.logDensity z₀ - u.logDensity z₀ = 0
  /-- The normalized base data gives `α z₀ = 0`. -/
  alpha_base_eq_zero :
    C.conformalFactor.wirtingerZ z₀ - u.wirtingerZ z₀ = 0

namespace LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData

/--
%%handwave
name:
  The scalar equation carried by the closed system
statement:
  The closed first-order system retains \(Δ(V-U)=a(V-U)\) throughout \(Ω\).
proof:
  Project the equation from its linearized scalar data.
-/
theorem phi_laplacian_linear_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian
          (fun w : ℂ ↦ C.conformalFactor.logDensity w - u.logDensity w) z =
        E.linearized.potential z *
          (C.conformalFactor.logDensity z - u.logDensity z) :=
  E.linearized.phi_laplacian_linear_eq

/--
%%handwave
name:
  Continuity of the Riccati coefficient
statement:
  If \(β=V_z+U_z\) on \(Ω\), then \(β\) is continuous there.
proof:
  Add the two continuous first Wirtinger fields.
-/
theorem beta_continuousOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) :
    ContinuousOn E.beta N.domain := by
  have hC :
      ContinuousOn C.conformalFactor.wirtingerZ N.domain := by
    rw [← data.pullback_domain_eq]
    exact C.conformalFactor.wirtingerZ_continuousOn
  have hu :
      ContinuousOn u.wirtingerZ N.domain :=
    u.wirtingerZ_continuousOn.mono
      (fun z hz ↦ D.domain_subset (N.normalized.domain_subset_original hz))
  exact (hC.add hu).congr fun z hz ↦ E.beta_eq z hz

/--
%%handwave
name:
  Continuity of the conjugate coefficient
statement:
  If \(a\) is continuous on \(Ω\) and \(γ=a/4\), then \(γ\) is continuous on \(Ω\).
proof:
  Complexification and multiplication by \(1/4\) preserve continuity.
-/
theorem gamma_continuousOn_of_potential_continuousOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data)
    (hpotential : ContinuousOn E.linearized.potential N.domain) :
    ContinuousOn E.gamma N.domain := by
  have hpotentialC :
      ContinuousOn (fun z ↦ (E.linearized.potential z : ℂ)) N.domain := by
    simpa using Complex.continuous_ofReal.comp_continuousOn' hpotential
  have hgamma :
      ContinuousOn (fun z ↦ (1 / 4 : ℂ) * (E.linearized.potential z : ℂ))
        N.domain :=
    continuousOn_const.mul hpotentialC
  exact hgamma.congr fun z hz ↦ E.gamma_eq z hz

/--
%%handwave
name:
  The conjugate Wirtinger derivative of the density difference
statement:
  For real \(φ=V-U\) with \(∂_zφ=α\), \(∂_{bar z}φ=overline α\) on \(Ω\).
proof:
  The Wirtinger derivatives of a real differentiable function are conjugates.
-/
theorem phi_frechetDBarValue_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) :
    ∀ z, z ∈ N.domain →
      frechetDBarValue
          (fun w : ℂ ↦
            ((C.conformalFactor.logDensity w - u.logDensity w : ℝ) : ℂ)) z =
        star (C.conformalFactor.wirtingerZ z - u.wirtingerZ z) := by
  intro z hz
  have hzC : z ∈ C.conformalFactor.coordinateDomain := by
    simpa [data.pullback_domain_eq] using hz
  have hC : DifferentiableAt ℝ C.conformalFactor.logDensity z :=
    (C.conformalFactor.logDensity_contDiffOn.contDiffAt
      (C.conformalFactor.isOpen_coordinateDomain.mem_nhds hzC)).differentiableAt
      (by norm_num)
  have hu : DifferentiableAt ℝ u.logDensity z :=
    (u.logDensity_contDiffOn.contDiffAt
      (u.isOpen_coordinateDomain.mem_nhds
        (D.domain_subset (N.normalized.domain_subset_original hz)))).differentiableAt
      (by norm_num)
  calc
    frechetDBarValue
          (fun w : ℂ ↦
            ((C.conformalFactor.logDensity w - u.logDensity w : ℝ) : ℂ)) z
        =
          star
            (frechetDZValue
              (fun w : ℂ ↦
                ((C.conformalFactor.logDensity w - u.logDensity w : ℝ) : ℂ)) z) :=
          frechetDBarValue_complex_ofReal_eq_star_frechetDZValue (hC.sub hu)
    _ = star (C.conformalFactor.wirtingerZ z - u.wirtingerZ z) := by
          rw [E.phi_frechetDZValue_eq z hz]

/--
%%handwave
name:
  Directional derivative of the density difference
statement:
  For \(α=V_z-U_z\) and \(ξ∈ℂ\), \(D(V-U)_z(ξ)=Re(ξ)(α+overline α)+Im(ξ)i(α-overline α)\).
proof:
  Reconstruct the real directional derivative from the two Wirtinger derivatives.
-/
theorem phi_fderiv_apply_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) :
    ∀ z, z ∈ N.domain → ∀ ξ : ℂ,
      fderiv ℝ
          (fun w : ℂ ↦
            ((C.conformalFactor.logDensity w - u.logDensity w : ℝ) : ℂ)) z ξ =
        (ξ.re : ℂ) *
            ((C.conformalFactor.wirtingerZ z - u.wirtingerZ z) +
              star (C.conformalFactor.wirtingerZ z - u.wirtingerZ z)) +
          (ξ.im : ℂ) * Complex.I *
            ((C.conformalFactor.wirtingerZ z - u.wirtingerZ z) -
              star (C.conformalFactor.wirtingerZ z - u.wirtingerZ z)) := by
  intro z hz ξ
  rw [fderiv_apply_eq_re_smul_frechetDZValue_add_dbar]
  rw [E.phi_frechetDZValue_eq z hz, E.phi_frechetDBarValue_eq z hz]

/--
%%handwave
name:
  Directional derivative of the derivative difference
statement:
  If \(∂_zα=αβ\) and \(∂_{bar z}α=γφ\), then \(Dα_z(ξ)=Re(ξ)(αβ+γφ)+Im(ξ)i(αβ-γφ)\).
proof:
  Apply Fréchet–Wirtinger reconstruction.
-/
theorem alpha_fderiv_apply_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) :
    ∀ z, z ∈ N.domain → ∀ ξ : ℂ,
      fderiv ℝ
          (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w) z ξ =
        (ξ.re : ℂ) *
            ((C.conformalFactor.wirtingerZ z - u.wirtingerZ z) * E.beta z +
              E.gamma z *
                ((C.conformalFactor.logDensity z - u.logDensity z : ℝ) : ℂ)) +
          (ξ.im : ℂ) * Complex.I *
            ((C.conformalFactor.wirtingerZ z - u.wirtingerZ z) * E.beta z -
              E.gamma z *
                ((C.conformalFactor.logDensity z - u.logDensity z : ℝ) : ℂ)) := by
  intro z hz ξ
  rw [fderiv_apply_eq_re_smul_frechetDZValue_add_dbar]
  rw [E.alpha_frechetDZValue_eq z hz, E.alpha_frechetDBarValue_eq z hz]

end LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData

/--
The real one-dimensional vector field obtained by restricting the closed
Liouville-Schwarzian first-order system to an affine path with velocity `ξ`.

The state is `(φ, α)`, where `φ = V - U` is complexified and
`α = V_z - U_z`.  The formula is exactly the Frechet-Wirtinger reconstruction
of the directional derivatives of `φ` and `α`.
-/
def closedFirstOrderPathVectorField (β γ : ℝ → ℂ) (ξ : ℂ) :
    ℝ → (ℂ × ℂ) → (ℂ × ℂ) :=
  fun t x ↦
    ((ξ.re : ℂ) * (x.2 + star x.2) +
        (ξ.im : ℂ) * Complex.I * (x.2 - star x.2),
      (ξ.re : ℂ) * (x.2 * β t + γ t * x.1) +
        (ξ.im : ℂ) * Complex.I * (x.2 * β t - γ t * x.1))

/--
%%handwave
name:
  The zero state is stationary
statement:
  For every \(t,β,γ,ξ\), the path vector field sends \(0∈ℂ²\) to \(0\).
proof:
  Substitute the zero components into the linear formula.
-/
@[simp]
theorem closedFirstOrderPathVectorField_zero
    (β γ : ℝ → ℂ) (ξ : ℂ) (t : ℝ) :
    closedFirstOrderPathVectorField β γ ξ t (0 : ℂ × ℂ) = 0 := by
  simp [closedFirstOrderPathVectorField]

/-- Left multiplication by a fixed complex number, as a real continuous linear map. -/
def complexLeftMulContinuousLinearMap (a : ℂ) : ℂ →L[ℝ] ℂ :=
  { toFun := fun z ↦ a * z
    map_add' := by
      intro z w
      ring
    map_smul' := by
      intro r z
      change a * ((r : ℂ) * z) = (r : ℂ) * (a * z)
      ring
    cont := continuous_const.mul continuous_id }

/--
The continuous linear map associated to the fixed-coefficient path-restricted
closed first-order system.
-/
def closedFirstOrderPathContinuousLinearMap (β γ ξ : ℂ) :
    (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  let fstMap : ℂ × ℂ →L[ℝ] ℂ := ContinuousLinearMap.fst ℝ ℂ ℂ
  let sndMap : ℂ × ℂ →L[ℝ] ℂ := ContinuousLinearMap.snd ℝ ℂ ℂ
  let conjSnd : ℂ × ℂ →L[ℝ] ℂ :=
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp sndMap
  let firstComponent : ℂ × ℂ →L[ℝ] ℂ :=
    (complexLeftMulContinuousLinearMap (ξ.re : ℂ)).comp (sndMap + conjSnd) +
      (complexLeftMulContinuousLinearMap ((ξ.im : ℂ) * Complex.I)).comp (sndMap - conjSnd)
  let secondComponent : ℂ × ℂ →L[ℝ] ℂ :=
    (complexLeftMulContinuousLinearMap (ξ.re : ℂ)).comp
        ((complexLeftMulContinuousLinearMap β).comp sndMap +
          (complexLeftMulContinuousLinearMap γ).comp fstMap) +
      (complexLeftMulContinuousLinearMap ((ξ.im : ℂ) * Complex.I)).comp
        ((complexLeftMulContinuousLinearMap β).comp sndMap -
          (complexLeftMulContinuousLinearMap γ).comp fstMap)
  firstComponent.prod secondComponent

/--
%%handwave
name:
  Action of the path-system operator
statement:
  For \(x=(φ,α)\), the operator has components \(Re(ξ)(α+overline α)+Im(ξ)i(α-overline α)\) and \(Re(ξ)(αβ+γφ)+Im(ξ)i(αβ-γφ)\).
proof:
  Expand the projections, conjugation, and scalar multiplications.
-/
@[simp]
theorem closedFirstOrderPathContinuousLinearMap_apply
    (β γ ξ : ℂ) (x : ℂ × ℂ) :
    closedFirstOrderPathContinuousLinearMap β γ ξ x =
      ((ξ.re : ℂ) * (x.2 + star x.2) +
          (ξ.im : ℂ) * Complex.I * (x.2 - star x.2),
        (ξ.re : ℂ) * (x.2 * β + γ * x.1) +
          (ξ.im : ℂ) * Complex.I * (x.2 * β - γ * x.1)) := by
  simp [closedFirstOrderPathContinuousLinearMap, complexLeftMulContinuousLinearMap,
    mul_add, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]

/--
%%handwave
name:
  The path operator realizes the vector field
statement:
  The fixed-coefficient operator at \(β(t),γ(t),ξ\) equals the path vector field at time \(t\) on every \(x∈ℂ²\).
proof:
  Compare their component formulas.
-/
@[simp]
theorem closedFirstOrderPathContinuousLinearMap_apply_path
    (β γ : ℝ → ℂ) (ξ : ℂ) (t : ℝ) (x : ℂ × ℂ) :
    closedFirstOrderPathContinuousLinearMap (β t) (γ t) ξ x =
      closedFirstOrderPathVectorField β γ ξ t x := by
  simp [closedFirstOrderPathVectorField, mul_assoc]

/--
%%handwave
name:
  An operator-norm estimate for the path system
statement:
  For \(β,γ,ξ∈ℂ\), \(‖L_{β,γ,ξ}‖≤4(‖ξ‖+1)(‖β‖+‖γ‖+1)\).
proof:
  Use triangle inequalities and bound coordinate norms by the product norm.
-/
theorem closedFirstOrderPathContinuousLinearMap_opNorm_le (β γ ξ : ℂ) :
    ‖closedFirstOrderPathContinuousLinearMap β γ ξ‖ ≤
      4 * (‖ξ‖ + 1) * (‖β‖ + ‖γ‖ + 1) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have hx₁ : ‖x.1‖ ≤ ‖x‖ := by
    simp [Prod.norm_def]
  have hx₂ : ‖x.2‖ ≤ ‖x‖ := by
    simp [Prod.norm_def]
  have hξre : ‖(ξ.re : ℂ)‖ ≤ ‖ξ‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using Complex.abs_re_le_norm ξ
  have hξimI : ‖(ξ.im : ℂ) * Complex.I‖ ≤ ‖ξ‖ := by
    simpa [Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs] using
      Complex.abs_im_le_norm ξ
  have hplus : ‖x.2 + star x.2‖ ≤ 2 * ‖x‖ := by
    calc
      ‖x.2 + star x.2‖ ≤ ‖x.2‖ + ‖star x.2‖ := norm_add_le _ _
      _ = 2 * ‖x.2‖ := by simp [two_mul]
      _ ≤ 2 * ‖x‖ := by nlinarith [hx₂]
  have hminus : ‖x.2 - star x.2‖ ≤ 2 * ‖x‖ := by
    calc
      ‖x.2 - star x.2‖ ≤ ‖x.2‖ + ‖star x.2‖ := norm_sub_le _ _
      _ = 2 * ‖x.2‖ := by simp [two_mul]
      _ ≤ 2 * ‖x‖ := by nlinarith [hx₂]
  have hfirstTerm₁ :
      ‖(ξ.re : ℂ) * (x.2 + star x.2)‖ ≤ ‖ξ‖ * (2 * ‖x‖) := by
    calc
      ‖(ξ.re : ℂ) * (x.2 + star x.2)‖ ≤
          ‖(ξ.re : ℂ)‖ * ‖x.2 + star x.2‖ := norm_mul_le _ _
      _ ≤ ‖ξ‖ * (2 * ‖x‖) := by gcongr
  have hfirstTerm₂ :
      ‖((ξ.im : ℂ) * Complex.I) * (x.2 - star x.2)‖ ≤ ‖ξ‖ * (2 * ‖x‖) := by
    calc
      ‖((ξ.im : ℂ) * Complex.I) * (x.2 - star x.2)‖ ≤
          ‖(ξ.im : ℂ) * Complex.I‖ * ‖x.2 - star x.2‖ := norm_mul_le _ _
      _ ≤ ‖ξ‖ * (2 * ‖x‖) := by gcongr
  have hfirst :
      ‖(ξ.re : ℂ) * (x.2 + star x.2) +
          (ξ.im : ℂ) * Complex.I * (x.2 - star x.2)‖ ≤
        (4 * (‖ξ‖ + 1) * (‖β‖ + ‖γ‖ + 1)) * ‖x‖ := by
    have hsum :=
      norm_add_le ((ξ.re : ℂ) * (x.2 + star x.2))
        ((ξ.im : ℂ) * Complex.I * (x.2 - star x.2))
    have hterm₂' :
        ‖(ξ.im : ℂ) * Complex.I * (x.2 - star x.2)‖ ≤ ‖ξ‖ * (2 * ‖x‖) := by
      simpa [mul_assoc] using hfirstTerm₂
    have hsmall :
        ‖(ξ.re : ℂ) * (x.2 + star x.2) +
            (ξ.im : ℂ) * Complex.I * (x.2 - star x.2)‖ ≤
          (4 * ‖ξ‖) * ‖x‖ := by
      nlinarith [hsum, hfirstTerm₁, hterm₂', norm_nonneg ξ, norm_nonneg x]
    calc
      ‖(ξ.re : ℂ) * (x.2 + star x.2) +
          (ξ.im : ℂ) * Complex.I * (x.2 - star x.2)‖ ≤
          (4 * ‖ξ‖) * ‖x‖ := hsmall
      _ ≤ (4 * (‖ξ‖ + 1) * (‖β‖ + ‖γ‖ + 1)) * ‖x‖ := by
          apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          nlinarith [norm_nonneg ξ, norm_nonneg β, norm_nonneg γ]
  have hcomboPlus :
      ‖x.2 * β + γ * x.1‖ ≤ (‖β‖ + ‖γ‖) * ‖x‖ := by
    have hmul₁ : ‖x.2 * β‖ ≤ ‖x.2‖ * ‖β‖ := norm_mul_le _ _
    have hmul₂ : ‖γ * x.1‖ ≤ ‖γ‖ * ‖x.1‖ := norm_mul_le _ _
    calc
      ‖x.2 * β + γ * x.1‖ ≤ ‖x.2 * β‖ + ‖γ * x.1‖ := norm_add_le _ _
      _ ≤ ‖x.2‖ * ‖β‖ + ‖γ‖ * ‖x.1‖ := by gcongr
      _ ≤ ‖x‖ * ‖β‖ + ‖γ‖ * ‖x‖ := by gcongr
      _ = (‖β‖ + ‖γ‖) * ‖x‖ := by ring
  have hcomboMinus :
      ‖x.2 * β - γ * x.1‖ ≤ (‖β‖ + ‖γ‖) * ‖x‖ := by
    have hmul₁ : ‖x.2 * β‖ ≤ ‖x.2‖ * ‖β‖ := norm_mul_le _ _
    have hmul₂ : ‖γ * x.1‖ ≤ ‖γ‖ * ‖x.1‖ := norm_mul_le _ _
    calc
      ‖x.2 * β - γ * x.1‖ ≤ ‖x.2 * β‖ + ‖γ * x.1‖ := norm_sub_le _ _
      _ ≤ ‖x.2‖ * ‖β‖ + ‖γ‖ * ‖x.1‖ := by gcongr
      _ ≤ ‖x‖ * ‖β‖ + ‖γ‖ * ‖x‖ := by gcongr
      _ = (‖β‖ + ‖γ‖) * ‖x‖ := by ring
  have hsecondTerm₁ :
      ‖(ξ.re : ℂ) * (x.2 * β + γ * x.1)‖ ≤
        ‖ξ‖ * ((‖β‖ + ‖γ‖) * ‖x‖) := by
    calc
      ‖(ξ.re : ℂ) * (x.2 * β + γ * x.1)‖ ≤
          ‖(ξ.re : ℂ)‖ * ‖x.2 * β + γ * x.1‖ := norm_mul_le _ _
      _ ≤ ‖ξ‖ * ((‖β‖ + ‖γ‖) * ‖x‖) := by gcongr
  have hsecondTerm₂ :
      ‖((ξ.im : ℂ) * Complex.I) * (x.2 * β - γ * x.1)‖ ≤
        ‖ξ‖ * ((‖β‖ + ‖γ‖) * ‖x‖) := by
    calc
      ‖((ξ.im : ℂ) * Complex.I) * (x.2 * β - γ * x.1)‖ ≤
          ‖(ξ.im : ℂ) * Complex.I‖ * ‖x.2 * β - γ * x.1‖ := norm_mul_le _ _
      _ ≤ ‖ξ‖ * ((‖β‖ + ‖γ‖) * ‖x‖) := by gcongr
  have hsecond :
      ‖(ξ.re : ℂ) * (x.2 * β + γ * x.1) +
          (ξ.im : ℂ) * Complex.I * (x.2 * β - γ * x.1)‖ ≤
        (4 * (‖ξ‖ + 1) * (‖β‖ + ‖γ‖ + 1)) * ‖x‖ := by
    have hsum :=
      norm_add_le ((ξ.re : ℂ) * (x.2 * β + γ * x.1))
        ((ξ.im : ℂ) * Complex.I * (x.2 * β - γ * x.1))
    have hterm₂' :
        ‖(ξ.im : ℂ) * Complex.I * (x.2 * β - γ * x.1)‖ ≤
          ‖ξ‖ * ((‖β‖ + ‖γ‖) * ‖x‖) := by
      simpa [mul_assoc] using hsecondTerm₂
    have hsmall :
        ‖(ξ.re : ℂ) * (x.2 * β + γ * x.1) +
            (ξ.im : ℂ) * Complex.I * (x.2 * β - γ * x.1)‖ ≤
          (2 * ‖ξ‖ * (‖β‖ + ‖γ‖)) * ‖x‖ := by
      nlinarith [hsum, hsecondTerm₁, hterm₂', norm_nonneg ξ, norm_nonneg β,
        norm_nonneg γ, norm_nonneg x]
    calc
      ‖(ξ.re : ℂ) * (x.2 * β + γ * x.1) +
          (ξ.im : ℂ) * Complex.I * (x.2 * β - γ * x.1)‖ ≤
          (2 * ‖ξ‖ * (‖β‖ + ‖γ‖)) * ‖x‖ := hsmall
      _ ≤ (4 * (‖ξ‖ + 1) * (‖β‖ + ‖γ‖ + 1)) * ‖x‖ := by
          apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          nlinarith [norm_nonneg ξ, norm_nonneg β, norm_nonneg γ]
  rw [closedFirstOrderPathContinuousLinearMap_apply, Prod.norm_def]
  exact max_le hfirst hsecond

/--
%%handwave
name:
  Coefficient bounds give an operator bound
statement:
  If \(‖β(t)‖≤B\) and \(‖γ(t)‖≤G\), then \(‖L_t‖≤4(‖ξ‖+1)(B+G+1)\) uniformly.
proof:
  Apply the pointwise operator estimate and monotonicity.
-/
theorem closedFirstOrderPathContinuousLinearMap_nnnorm_le_of_coeff_bound
    {β γ : ℝ → ℂ} {ξ : ℂ} {B G : NNReal}
    (hβ : ∀ t : ℝ, ‖β t‖ ≤ (B : ℝ))
    (hγ : ∀ t : ℝ, ‖γ t‖ ≤ (G : ℝ)) :
    ∀ t : ℝ,
      ‖closedFirstOrderPathContinuousLinearMap (β t) (γ t) ξ‖₊ ≤
        Real.toNNReal (4 * (‖ξ‖ + 1) * ((B : ℝ) + (G : ℝ) + 1)) := by
  intro t
  rw [← NNReal.coe_le_coe]
  change ‖closedFirstOrderPathContinuousLinearMap (β t) (γ t) ξ‖ ≤
    (Real.toNNReal (4 * (‖ξ‖ + 1) * ((B : ℝ) + (G : ℝ) + 1)) : ℝ)
  rw [Real.coe_toNNReal _ (by positivity)]
  calc
    ‖closedFirstOrderPathContinuousLinearMap (β t) (γ t) ξ‖ ≤
        4 * (‖ξ‖ + 1) * (‖β t‖ + ‖γ t‖ + 1) :=
      closedFirstOrderPathContinuousLinearMap_opNorm_le (β t) (γ t) ξ
    _ ≤ 4 * (‖ξ‖ + 1) * ((B : ℝ) + (G : ℝ) + 1) := by
      gcongr
      · exact hβ t
      · exact hγ t

/--
%%handwave
name:
  A clamped continuous path is globally bounded
statement:
  If \(f:ℝ→ℂ\) is continuous on \([0,1]\) and \(f(t)=f(proj_{[0,1]}t)\), then \(‖f(t)‖≤B\) globally for some \(B≥0\).
proof:
  Compactness bounds \(f\) on the interval; clamping reduces every argument to it.
-/
theorem exists_nnnorm_bound_of_continuousOn_Icc_of_eq_projIcc
    {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hproj :
      ∀ t : ℝ, f t = f (Set.projIcc (0 : ℝ) 1 zero_le_one t)) :
    ∃ B : NNReal, ∀ t : ℝ, ‖f t‖ ≤ (B : ℝ) := by
  rcases isCompact_Icc.exists_bound_of_continuousOn hf with ⟨C, hC⟩
  have hC_nonneg : 0 ≤ C := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    exact le_trans (norm_nonneg (f 0)) (hC 0 h0)
  refine ⟨Real.toNNReal C, ?_⟩
  intro t
  rw [Real.coe_toNNReal _ hC_nonneg]
  calc
    ‖f t‖ = ‖f (Set.projIcc (0 : ℝ) 1 zero_le_one t)‖ := by
      rw [hproj t]
    _ ≤ C :=
      hC (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)
        (Set.projIcc (0 : ℝ) 1 zero_le_one t).2

/--
%%handwave
name:
  An operator bound gives a Lipschitz vector field
statement:
  If \(‖L_t‖≤K\), then \(x↦L_tx\) is \(K\)-Lipschitz.
proof:
  Apply the operator-norm estimate to \(L_t(x-y)\).
-/
theorem closedFirstOrderPathVectorField_lipschitz_of_opNorm_bound
    {β γ : ℝ → ℂ} {ξ : ℂ} {K : NNReal}
    (hK :
      ∀ t : ℝ, ‖closedFirstOrderPathContinuousLinearMap (β t) (γ t) ξ‖₊ ≤ K) :
    ∀ t : ℝ, LipschitzWith K (closedFirstOrderPathVectorField β γ ξ t) := by
  intro t
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  calc
    dist (closedFirstOrderPathVectorField β γ ξ t x)
        (closedFirstOrderPathVectorField β γ ξ t y)
        = dist (closedFirstOrderPathContinuousLinearMap (β t) (γ t) ξ x)
            (closedFirstOrderPathContinuousLinearMap (β t) (γ t) ξ y) := by
          simp [closedFirstOrderPathVectorField, mul_assoc]
    _ ≤ (‖closedFirstOrderPathContinuousLinearMap (β t) (γ t) ξ‖₊ : ℝ) * dist x y :=
          (closedFirstOrderPathContinuousLinearMap (β t) (γ t) ξ).lipschitz.dist_le_mul x y
    _ ≤ (K : ℝ) * dist x y := by
          gcongr
          exact hK t

/--
%%handwave
name:
  Existence of a Lipschitz bound from operator boundedness
statement:
  A uniformly bounded family of path-system operators has a common Lipschitz constant.
proof:
  Choose the operator bound and apply the pointwise estimate.
-/
theorem closedFirstOrderPathVectorField_exists_lipschitz_of_opNorm_bound
    {β γ : ℝ → ℂ} {ξ : ℂ}
    (hK :
      ∃ K : NNReal,
        ∀ t : ℝ, ‖closedFirstOrderPathContinuousLinearMap (β t) (γ t) ξ‖₊ ≤ K) :
    ∃ K : NNReal,
      ∀ t : ℝ, LipschitzWith K (closedFirstOrderPathVectorField β γ ξ t) := by
  rcases hK with ⟨K, hK⟩
  exact ⟨K, closedFirstOrderPathVectorField_lipschitz_of_opNorm_bound hK⟩

/--
%%handwave
name:
  Zero initial data force the path state to vanish
statement:
  If \(X:[0,1]→ℂ²\) solves \(X'=F_t(X)\), the fields share a Lipschitz constant, \(F_t(0)=0\), and \(X(0)=0\), then \(X(1)=0\).
proof:
  The zero curve is a solution with the same initial value; ODE uniqueness identifies it with \(X\).
-/
theorem closedFirstOrderPath_state_eq_zero_of_ODE_unique
    {β γ : ℝ → ℂ} {ξ : ℂ} {state : ℝ → ℂ × ℂ}
    (hLip :
      ∃ K : NNReal,
        ∀ t : ℝ, LipschitzWith K (closedFirstOrderPathVectorField β γ ξ t))
    (hstate_cont : ContinuousOn state (Set.Icc (0 : ℝ) 1))
    (hstate_deriv :
      ∀ t, t ∈ Set.Ico (0 : ℝ) 1 →
        HasDerivWithinAt state
          (closedFirstOrderPathVectorField β γ ξ t (state t)) (Set.Ici t) t)
    (hbase : state 0 = 0) :
    state 1 = 0 := by
  rcases hLip with ⟨K, hK⟩
  have hzero_cont :
      ContinuousOn (fun _ : ℝ ↦ (0 : ℂ × ℂ)) (Set.Icc (0 : ℝ) 1) :=
    continuous_const.continuousOn
  have hzero_deriv :
      ∀ t, t ∈ Set.Ico (0 : ℝ) 1 →
        HasDerivWithinAt (fun _ : ℝ ↦ (0 : ℂ × ℂ))
          (closedFirstOrderPathVectorField β γ ξ t ((fun _ : ℝ ↦ (0 : ℂ × ℂ)) t))
          (Set.Ici t) t := by
    intro t _ht
    simpa using
      (hasDerivWithinAt_const (x := t) (s := Set.Ici t) (c := (0 : ℂ × ℂ)))
  have hEq :
      Set.EqOn state (fun _ : ℝ ↦ (0 : ℂ × ℂ)) (Set.Icc (0 : ℝ) 1) :=
    ODE_solution_unique (v := closedFirstOrderPathVectorField β γ ξ) (K := K)
      hK hstate_cont hstate_deriv hzero_cont hzero_deriv hbase
  simpa using hEq (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)

/--
Path-restriction data for the closed first-order Liouville-Schwarzian system.

This is the concrete certificate still needed to use the Grönwall uniqueness
bridge: it packages a real path from the base point to a target point, the
restricted coefficients, the restricted state `(φ, α)`, and the fact that this
state solves the restricted ODE.
-/
structure LocalLiouvilleSchwarzianClosedFirstOrderPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) (z : ℂ) where
  /-- The affine path velocity after reparametrization to `[0,1]`. -/
  velocity : ℂ
  /-- The `β` coefficient restricted to the path. -/
  betaPath : ℝ → ℂ
  /-- The `γ` coefficient restricted to the path. -/
  gammaPath : ℝ → ℂ
  /-- The path-restricted state `(φ, α)`. -/
  state : ℝ → ℂ × ℂ
  /-- The path starts with the zero normalized state. -/
  state_zero : state 0 = 0
  /-- The endpoint is the target value of `(φ, α)`. -/
  state_one :
    state 1 =
      (((C.conformalFactor.logDensity z - u.logDensity z : ℝ) : ℂ),
        C.conformalFactor.wirtingerZ z - u.wirtingerZ z)
  /-- The path-restricted vector field is uniformly Lipschitz in the state. -/
  lipschitz :
    ∃ K : NNReal,
      ∀ t : ℝ, LipschitzWith K
        (closedFirstOrderPathVectorField betaPath gammaPath velocity t)
  /-- The path-restricted state is continuous on the interval. -/
  state_continuousOn : ContinuousOn state (Set.Icc (0 : ℝ) 1)
  /-- The path-restricted state solves the path ODE. -/
  state_hasDerivWithinAt :
    ∀ t, t ∈ Set.Ico (0 : ℝ) 1 →
      HasDerivWithinAt state
        (closedFirstOrderPathVectorField betaPath gammaPath velocity t (state t))
        (Set.Ici t) t

namespace LocalLiouvilleSchwarzianClosedFirstOrderPathData

/--
%%handwave
name:
  Endpoint equality from a path solution
statement:
  If the normalized state \(X=(V-U,V_z-U_z)\) solves the Lipschitz path system from \(z₀\) to \(z\), then \(U(z)=V(z)\).
proof:
  ODE uniqueness gives \(X(1)=0\); read its first component.
-/
theorem logDensity_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderPathData E z) :
    u.logDensity z = C.conformalFactor.logDensity z := by
  have hstate_one_zero : P.state 1 = 0 :=
    closedFirstOrderPath_state_eq_zero_of_ODE_unique P.lipschitz
      P.state_continuousOn P.state_hasDerivWithinAt P.state_zero
  have hφ :
      ((C.conformalFactor.logDensity z - u.logDensity z : ℝ) : ℂ) = 0 := by
    have hfst := congrArg Prod.fst hstate_one_zero
    simpa [P.state_one] using hfst
  have hreal : C.conformalFactor.logDensity z - u.logDensity z = 0 := by
    exact Complex.ofReal_eq_zero.mp hφ
  linarith

/--
%%handwave
name:
  Endpoint derivative equality from a path solution
statement:
  Under the same hypotheses, \(V_z(z)-U_z(z)=0\).
proof:
  Read the second component of \(X(1)=0\).
-/
theorem alpha_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderPathData E z) :
    C.conformalFactor.wirtingerZ z - u.wirtingerZ z = 0 := by
  have hstate_one_zero : P.state 1 = 0 :=
    closedFirstOrderPath_state_eq_zero_of_ODE_unique P.lipschitz
      P.state_continuousOn P.state_hasDerivWithinAt P.state_zero
  have hα :
      C.conformalFactor.wirtingerZ z - u.wirtingerZ z = 0 := by
    have hsnd := congrArg Prod.snd hstate_one_zero
    simpa [P.state_one] using hsnd
  exact hα

end LocalLiouvilleSchwarzianClosedFirstOrderPathData

/--
Path-restriction data with the Lipschitz condition expressed as an operator
norm bound on the fixed-coefficient continuous linear maps.

This is closer to the usual finite-dimensional ODE verification: construct
the restricted state and prove a uniform bound for the associated linear
operators.
-/
structure LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) (z : ℂ) where
  /-- The affine path velocity after reparametrization to `[0,1]`. -/
  velocity : ℂ
  /-- The `β` coefficient restricted to the path. -/
  betaPath : ℝ → ℂ
  /-- The `γ` coefficient restricted to the path. -/
  gammaPath : ℝ → ℂ
  /-- The path-restricted state `(φ, α)`. -/
  state : ℝ → ℂ × ℂ
  /-- The path starts with the zero normalized state. -/
  state_zero : state 0 = 0
  /-- The endpoint is the target value of `(φ, α)`. -/
  state_one :
    state 1 =
      (((C.conformalFactor.logDensity z - u.logDensity z : ℝ) : ℂ),
        C.conformalFactor.wirtingerZ z - u.wirtingerZ z)
  /-- A uniform operator-norm bound for the restricted linear vector field. -/
  operatorBound : NNReal
  /-- The fixed-coefficient continuous linear maps are uniformly bounded. -/
  operator_norm_le :
    ∀ t : ℝ,
      ‖closedFirstOrderPathContinuousLinearMap (betaPath t) (gammaPath t) velocity‖₊ ≤
        operatorBound
  /-- The path-restricted state is continuous on the interval. -/
  state_continuousOn : ContinuousOn state (Set.Icc (0 : ℝ) 1)
  /-- The path-restricted state solves the path ODE. -/
  state_hasDerivWithinAt :
    ∀ t, t ∈ Set.Ico (0 : ℝ) 1 →
      HasDerivWithinAt state
        (closedFirstOrderPathVectorField betaPath gammaPath velocity t (state t))
        (Set.Ici t) t

namespace LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathData

/-- Forget an operator-bound path certificate to the older Lipschitz path certificate. -/
def toPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathData E z) :
    LocalLiouvilleSchwarzianClosedFirstOrderPathData E z where
  velocity := P.velocity
  betaPath := P.betaPath
  gammaPath := P.gammaPath
  state := P.state
  state_zero := P.state_zero
  state_one := P.state_one
  lipschitz :=
    closedFirstOrderPathVectorField_exists_lipschitz_of_opNorm_bound
      ⟨P.operatorBound, P.operator_norm_le⟩
  state_continuousOn := P.state_continuousOn
  state_hasDerivWithinAt := P.state_hasDerivWithinAt

/--
%%handwave
name:
  Log-density equality from operator-bounded paths
statement:
  If the normalized path state solves the system and its operators are uniformly bounded, then \(U(z)=V(z)\).
proof:
  The bound gives a Lipschitz path, so endpoint uniqueness applies.
-/
theorem logDensity_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathData E z) :
    u.logDensity z = C.conformalFactor.logDensity z :=
  P.toPathData.logDensity_eq

end LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathData

/--
Path-restriction data with bounded restricted coefficients.

This is the next more concrete certificate: the uniform operator bound is now
derived from ordinary norm bounds for the coefficient functions along the
path.
-/
structure LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) (z : ℂ) where
  /-- The affine path velocity after reparametrization to `[0,1]`. -/
  velocity : ℂ
  /-- The `β` coefficient restricted to the path. -/
  betaPath : ℝ → ℂ
  /-- The `γ` coefficient restricted to the path. -/
  gammaPath : ℝ → ℂ
  /-- The path-restricted state `(φ, α)`. -/
  state : ℝ → ℂ × ℂ
  /-- The path starts with the zero normalized state. -/
  state_zero : state 0 = 0
  /-- The endpoint is the target value of `(φ, α)`. -/
  state_one :
    state 1 =
      (((C.conformalFactor.logDensity z - u.logDensity z : ℝ) : ℂ),
        C.conformalFactor.wirtingerZ z - u.wirtingerZ z)
  /-- A uniform bound for the restricted `β` coefficient. -/
  betaBound : NNReal
  /-- A uniform bound for the restricted `γ` coefficient. -/
  gammaBound : NNReal
  /-- The restricted `β` coefficient is bounded. -/
  beta_norm_le : ∀ t : ℝ, ‖betaPath t‖ ≤ (betaBound : ℝ)
  /-- The restricted `γ` coefficient is bounded. -/
  gamma_norm_le : ∀ t : ℝ, ‖gammaPath t‖ ≤ (gammaBound : ℝ)
  /-- The path-restricted state is continuous on the interval. -/
  state_continuousOn : ContinuousOn state (Set.Icc (0 : ℝ) 1)
  /-- The path-restricted state solves the path ODE. -/
  state_hasDerivWithinAt :
    ∀ t, t ∈ Set.Ico (0 : ℝ) 1 →
      HasDerivWithinAt state
        (closedFirstOrderPathVectorField betaPath gammaPath velocity t (state t))
        (Set.Ici t) t

namespace LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathData

/-- Forget bounded-coefficient path data to operator-bound path data. -/
def toOperatorBoundPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathData E z) :
    LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathData E z where
  velocity := P.velocity
  betaPath := P.betaPath
  gammaPath := P.gammaPath
  state := P.state
  state_zero := P.state_zero
  state_one := P.state_one
  operatorBound :=
    Real.toNNReal (4 * (‖P.velocity‖ + 1) *
      ((P.betaBound : ℝ) + (P.gammaBound : ℝ) + 1))
  operator_norm_le :=
    closedFirstOrderPathContinuousLinearMap_nnnorm_le_of_coeff_bound
      P.beta_norm_le P.gamma_norm_le
  state_continuousOn := P.state_continuousOn
  state_hasDerivWithinAt := P.state_hasDerivWithinAt

/-- Forget bounded-coefficient path data all the way to the Lipschitz path data. -/
def toPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathData E z) :
    LocalLiouvilleSchwarzianClosedFirstOrderPathData E z :=
  P.toOperatorBoundPathData.toPathData

/--
%%handwave
name:
  Log-density equality from bounded coefficients
statement:
  If the normalized path state solves the system and \(β,γ\) are uniformly bounded, then \(U(z)=V(z)\).
proof:
  Coefficient bounds give an operator bound and hence path uniqueness.
-/
theorem logDensity_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathData E z) :
    u.logDensity z = C.conformalFactor.logDensity z :=
  P.toPathData.logDensity_eq

end LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathData

/--
The clamped affine path from the normalized base point `z₀` to a target point
`z`.

The clamp makes the coefficient paths global functions of real time, while the
ODE proof only uses the unclamped segment on `[0,1]`.
-/
def closedFirstOrderClampedAffinePath (z₀ z : ℂ) (t : ℝ) : ℂ :=
  AffineMap.lineMap z₀ z (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)

/--
%%handwave
name:
  Initial point of the clamped affine path
statement:
  For the clamped affine path \(c\) from \(z₀\) to \(z\), \(c(0)=z₀\).
proof:
  Projection fixes \(0\) and the affine line starts at \(z₀\).
-/
@[simp]
theorem closedFirstOrderClampedAffinePath_zero (z₀ z : ℂ) :
    closedFirstOrderClampedAffinePath z₀ z 0 = z₀ := by
  simp [closedFirstOrderClampedAffinePath]

/--
%%handwave
name:
  Endpoint of the clamped affine path
statement:
  For the clamped affine path \(c\) from \(z₀\) to \(z\), \(c(1)=z\).
proof:
  Projection fixes \(1\) and the affine line ends at \(z\).
-/
@[simp]
theorem closedFirstOrderClampedAffinePath_one (z₀ z : ℂ) :
    closedFirstOrderClampedAffinePath z₀ z 1 = z := by
  simp [closedFirstOrderClampedAffinePath]

/--
%%handwave
name:
  Clamping invariance of the affine path
statement:
  For every \(t∈ℝ\), \(c(t)=c(proj_{[0,1]}t)\).
proof:
  Projection onto \([0,1]\) is idempotent.
-/
theorem closedFirstOrderClampedAffinePath_eq_projIcc (z₀ z : ℂ) (t : ℝ) :
    closedFirstOrderClampedAffinePath z₀ z t =
      closedFirstOrderClampedAffinePath z₀ z
        (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) := by
  simp [closedFirstOrderClampedAffinePath]

/--
%%handwave
name:
  Continuity of the clamped affine path
statement:
  The affine path from \(z₀\) to \(z\), extended by clamping, is continuous on \(ℝ\).
proof:
  Compose the continuous affine line with interval projection.
-/
theorem continuous_closedFirstOrderClampedAffinePath (z₀ z : ℂ) :
    Continuous (closedFirstOrderClampedAffinePath z₀ z) := by
  simpa [closedFirstOrderClampedAffinePath] using
    (AffineMap.lineMap_continuous (p := z₀) (q := z)).comp
      (continuous_subtype_val.comp continuous_projIcc)

/--
%%handwave
name:
  Segments remain in the normalized ball
statement:
  If \(Ω\) is a Euclidean ball and \(z₀,z∈Ω\), then \((1-t)z₀+tz∈Ω\) for \(t∈[0,1]\).
proof:
  Euclidean balls are convex.
-/
theorem localHyperbolicTwoJet_segment_mem_of_ballDomain
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem)
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {z : ℂ} (hz : z ∈ N.domain) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      AffineMap.lineMap z₀ z t ∈ N.domain := by
  intro t ht
  rcases hBallDomain S N with ⟨c, r, hdomain⟩
  rw [hdomain] at hz ⊢
  have hbase : z₀ ∈ Metric.ball c r := by
    rw [← hdomain]
    exact N.base_mem
  have hseg : segment ℝ z₀ z ⊆ Metric.ball c r :=
    (convex_ball c r).segment_subset hbase hz
  exact hseg <| by
    refine ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, ?_⟩
    rw [AffineMap.lineMap_apply_module]

/--
The canonical state of the closed first-order Liouville-Schwarzian system
along the unclamped affine segment from `z₀` to `z`.
-/
def closedFirstOrderAffineState
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (C : LocalHyperbolicPullbackLiouvilleCandidate N) (z : ℂ) :
    ℝ → ℂ × ℂ :=
  fun t ↦
    let w := AffineMap.lineMap z₀ z t
    (((C.conformalFactor.logDensity w - u.logDensity w : ℝ) : ℂ),
      C.conformalFactor.wirtingerZ w - u.wirtingerZ w)

/--
%%handwave
name:
  Continuity of the canonical affine state
statement:
  If \(w(t)=(1-t)z₀+tz\) stays in \(Ω\), then \(X(t)=(V(w(t))-U(w(t)),V_z(w(t))-U_z(w(t)))\) is continuous.
proof:
  Compose the continuous fields with the segment, then pair their differences.
-/
theorem closedFirstOrderAffineState_continuousOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (C : LocalHyperbolicPullbackLiouvilleCandidate N) {z : ℂ}
    (hseg :
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        AffineMap.lineMap z₀ z t ∈ N.domain) :
    ContinuousOn (closedFirstOrderAffineState C z) (Set.Icc (0 : ℝ) 1) := by
  let path : ℝ → ℂ := fun t ↦ AffineMap.lineMap z₀ z t
  have hpath : ContinuousOn path (Set.Icc (0 : ℝ) 1) :=
    (AffineMap.lineMap_continuous (p := z₀) (q := z)).continuousOn
  have hmapsC : Set.MapsTo path (Set.Icc (0 : ℝ) 1) C.conformalFactor.coordinateDomain := by
    intro t ht
    simpa [path, C.coordinateDomain_eq] using hseg t ht
  have hmapsu : Set.MapsTo path (Set.Icc (0 : ℝ) 1) u.coordinateDomain := by
    intro t ht
    exact D.domain_subset (N.normalized.domain_subset_original (hseg t ht))
  have hClog :
      ContinuousOn (fun t ↦ C.conformalFactor.logDensity (path t)) (Set.Icc (0 : ℝ) 1) :=
    C.conformalFactor.logDensity_contDiffOn.continuousOn.comp' hpath hmapsC
  have hulog :
      ContinuousOn (fun t ↦ u.logDensity (path t)) (Set.Icc (0 : ℝ) 1) :=
    u.logDensity_contDiffOn.continuousOn.comp' hpath hmapsu
  have hphiReal :
      ContinuousOn
        (fun t ↦ C.conformalFactor.logDensity (path t) - u.logDensity (path t))
        (Set.Icc (0 : ℝ) 1) :=
    hClog.sub hulog
  have hphi :
      ContinuousOn
        (fun t ↦
          ((C.conformalFactor.logDensity (path t) - u.logDensity (path t) : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) 1) := by
    simpa using Complex.continuous_ofReal.comp_continuousOn' hphiReal
  have hCZ :
      ContinuousOn (fun t ↦ C.conformalFactor.wirtingerZ (path t)) (Set.Icc (0 : ℝ) 1) :=
    C.conformalFactor.wirtingerZ_continuousOn.comp' hpath hmapsC
  have huZ :
      ContinuousOn (fun t ↦ u.wirtingerZ (path t)) (Set.Icc (0 : ℝ) 1) :=
    u.wirtingerZ_continuousOn.comp' hpath hmapsu
  have halpha :
      ContinuousOn
        (fun t ↦ C.conformalFactor.wirtingerZ (path t) - u.wirtingerZ (path t))
        (Set.Icc (0 : ℝ) 1) :=
    hCZ.sub huZ
  show ContinuousOn
    (fun t ↦
      (((C.conformalFactor.logDensity (AffineMap.lineMap z₀ z t) -
          u.logDensity (AffineMap.lineMap z₀ z t) : ℝ) : ℂ),
        C.conformalFactor.wirtingerZ (AffineMap.lineMap z₀ z t) -
          u.wirtingerZ (AffineMap.lineMap z₀ z t)))
    (Set.Icc (0 : ℝ) 1)
  simpa [path, Complex.ofReal_sub] using hphi.prodMk halpha

/--
%%handwave
name:
  The affine state solves the restricted system
statement:
  Whenever \(w(t)∈Ω\), the canonical state along \(w(t)\) has derivative \(F_t(X(t))\) with velocity \(z-z₀\).
proof:
  Apply the chain rule to both components and substitute their directional equations.
-/
theorem closedFirstOrderAffineState_hasDerivWithinAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data)
    {z : ℂ} {t : ℝ}
    (hwt : AffineMap.lineMap z₀ z t ∈ N.domain) :
    HasDerivWithinAt (closedFirstOrderAffineState C z)
      (closedFirstOrderPathVectorField
        (fun τ : ℝ ↦ E.beta (AffineMap.lineMap z₀ z τ))
        (fun τ : ℝ ↦ E.gamma (AffineMap.lineMap z₀ z τ))
        (z - z₀) t (closedFirstOrderAffineState C z t))
      (Set.Ici t) t := by
  let path : ℝ → ℂ := fun τ ↦ AffineMap.lineMap z₀ z τ
  let phi : ℂ → ℂ := fun w ↦
    ((C.conformalFactor.logDensity w - u.logDensity w : ℝ) : ℂ)
  let alpha : ℂ → ℂ := fun w ↦
    C.conformalFactor.wirtingerZ w - u.wirtingerZ w
  have hpath : HasDerivWithinAt path (z - z₀) (Set.Ici t) t := by
    simpa [path] using
      (AffineMap.hasDerivWithinAt_lineMap
        (a := z₀) (b := z) (s := Set.Ici t) (x := t))
  have hCdom : path t ∈ C.conformalFactor.coordinateDomain := by
    simpa [path, data.pullback_domain_eq] using hwt
  have hudom : path t ∈ u.coordinateDomain := by
    exact D.domain_subset (N.normalized.domain_subset_original (by simpa [path] using hwt))
  have hCLogDiff : DifferentiableAt ℝ C.conformalFactor.logDensity (path t) :=
    (C.conformalFactor.logDensity_contDiffOn.contDiffAt
      (C.conformalFactor.isOpen_coordinateDomain.mem_nhds hCdom)).differentiableAt
      (by norm_num)
  have huLogDiff : DifferentiableAt ℝ u.logDensity (path t) :=
    (u.logDensity_contDiffOn.contDiffAt
      (u.isOpen_coordinateDomain.mem_nhds hudom)).differentiableAt
      (by norm_num)
  have hphiDiff : DifferentiableAt ℝ phi (path t) := by
    exact Complex.ofRealCLM.differentiableAt.comp (path t) (hCLogDiff.sub huLogDiff)
  have hphiDeriv₀ :
      HasDerivWithinAt (fun τ ↦ phi (path τ))
        (fderiv ℝ phi (path t) (z - z₀)) (Set.Ici t) t := by
    simpa [Function.comp_def] using hphiDiff.hasFDerivAt.comp_hasDerivWithinAt t hpath
  have hphiDeriv :
      HasDerivWithinAt (fun τ ↦
          ((C.conformalFactor.logDensity (AffineMap.lineMap z₀ z τ) -
              u.logDensity (AffineMap.lineMap z₀ z τ) : ℝ) : ℂ))
        ((closedFirstOrderPathVectorField
          (fun τ : ℝ ↦ E.beta (AffineMap.lineMap z₀ z τ))
          (fun τ : ℝ ↦ E.gamma (AffineMap.lineMap z₀ z τ))
          (z - z₀) t (closedFirstOrderAffineState C z t)).1)
        (Set.Ici t) t := by
    have hphiDeriv₁ :
        HasDerivWithinAt (fun τ ↦
            ((C.conformalFactor.logDensity (AffineMap.lineMap z₀ z τ) -
                u.logDensity (AffineMap.lineMap z₀ z τ) : ℝ) : ℂ))
          (fderiv ℝ phi (path t) (z - z₀)) (Set.Ici t) t := by
      simpa [phi, path] using hphiDeriv₀
    convert hphiDeriv₁ using 1
    rw [E.phi_fderiv_apply_eq (path t) (by simpa [path] using hwt) (z - z₀)]
    simp [closedFirstOrderPathVectorField, closedFirstOrderAffineState, path]
  have hCZDiff : DifferentiableAt ℝ C.conformalFactor.wirtingerZ (path t) :=
    C.conformalFactor.wirtingerZ_differentiableAt hCdom
  have huZDiff : DifferentiableAt ℝ u.wirtingerZ (path t) :=
    u.wirtingerZ_differentiableAt hudom
  have halphaDiff : DifferentiableAt ℝ alpha (path t) :=
    hCZDiff.sub huZDiff
  have halphaDeriv₀ :
      HasDerivWithinAt (fun τ ↦ alpha (path τ))
        (fderiv ℝ alpha (path t) (z - z₀)) (Set.Ici t) t := by
    simpa [Function.comp_def] using halphaDiff.hasFDerivAt.comp_hasDerivWithinAt t hpath
  have halphaDeriv :
      HasDerivWithinAt (fun τ ↦
          C.conformalFactor.wirtingerZ (AffineMap.lineMap z₀ z τ) -
            u.wirtingerZ (AffineMap.lineMap z₀ z τ))
        ((closedFirstOrderPathVectorField
          (fun τ : ℝ ↦ E.beta (AffineMap.lineMap z₀ z τ))
          (fun τ : ℝ ↦ E.gamma (AffineMap.lineMap z₀ z τ))
          (z - z₀) t (closedFirstOrderAffineState C z t)).2)
        (Set.Ici t) t := by
    have halphaDeriv₁ :
        HasDerivWithinAt (fun τ ↦
            C.conformalFactor.wirtingerZ (AffineMap.lineMap z₀ z τ) -
              u.wirtingerZ (AffineMap.lineMap z₀ z τ))
          (fderiv ℝ alpha (path t) (z - z₀)) (Set.Ici t) t := by
      simpa [alpha, path] using halphaDeriv₀
    convert halphaDeriv₁ using 1
    rw [E.alpha_fderiv_apply_eq (path t) (by simpa [path] using hwt) (z - z₀)]
    simp [closedFirstOrderPathVectorField, closedFirstOrderAffineState, path]
  show HasDerivWithinAt
    (fun τ ↦
      (((C.conformalFactor.logDensity (AffineMap.lineMap z₀ z τ) -
          u.logDensity (AffineMap.lineMap z₀ z τ) : ℝ) : ℂ),
        C.conformalFactor.wirtingerZ (AffineMap.lineMap z₀ z τ) -
          u.wirtingerZ (AffineMap.lineMap z₀ z τ)))
    (closedFirstOrderPathVectorField
      (fun τ : ℝ ↦ E.beta (AffineMap.lineMap z₀ z τ))
      (fun τ : ℝ ↦ E.gamma (AffineMap.lineMap z₀ z τ))
      (z - z₀) t (closedFirstOrderAffineState C z t))
    (Set.Ici t) t
  exact hphiDeriv.prodMk halphaDeriv

/--
Natural path data for the closed first-order system along the straight segment.

This package asks only for the remaining analytic chain-rule facts along the
segment: continuity of the coefficients on the normalized domain, continuity
of the canonical state along the interval, and the restricted integral-curve
equation.  The endpoint equations and all boundedness/Lipschitz consequences
are then derived below.
-/
structure LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) (z : ℂ) where
  /-- The straight segment from the base point to `z` stays in the normalized domain. -/
  segment_mem :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      AffineMap.lineMap z₀ z t ∈ N.domain
  /-- The `β` coefficient is continuous on the normalized domain. -/
  beta_continuousOn : ContinuousOn E.beta N.domain
  /-- The `γ` coefficient is continuous on the normalized domain. -/
  gamma_continuousOn : ContinuousOn E.gamma N.domain
  /-- The canonical restricted state is continuous on `[0,1]`. -/
  state_continuousOn :
    ContinuousOn (closedFirstOrderAffineState C z) (Set.Icc (0 : ℝ) 1)
  /-- The canonical restricted state solves the path ODE on `(0,1)`. -/
  state_hasDerivWithinAt :
    ∀ t, t ∈ Set.Ico (0 : ℝ) 1 →
      HasDerivWithinAt (closedFirstOrderAffineState C z)
        (closedFirstOrderPathVectorField
          (fun τ : ℝ ↦ E.beta (AffineMap.lineMap z₀ z τ))
          (fun τ : ℝ ↦ E.gamma (AffineMap.lineMap z₀ z τ))
          (z - z₀) t (closedFirstOrderAffineState C z t))
        (Set.Ici t) t

/--
The analytic core of straight-segment path data.

The domain-geometry field is omitted: for our normalized branches, ball-shaped
domains already imply that the affine segment from `z₀` to any target point in
the domain stays inside the domain.
-/
structure LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) (z : ℂ) where
  /-- The `β` coefficient is continuous on the normalized domain. -/
  beta_continuousOn : ContinuousOn E.beta N.domain
  /-- The `γ` coefficient is continuous on the normalized domain. -/
  gamma_continuousOn : ContinuousOn E.gamma N.domain
  /-- The canonical restricted state is continuous on `[0,1]`. -/
  state_continuousOn :
    ContinuousOn (closedFirstOrderAffineState C z) (Set.Icc (0 : ℝ) 1)
  /-- The canonical restricted state solves the path ODE on `(0,1)`. -/
  state_hasDerivWithinAt :
    ∀ t, t ∈ Set.Ico (0 : ℝ) 1 →
      HasDerivWithinAt (closedFirstOrderAffineState C z)
        (closedFirstOrderPathVectorField
          (fun τ : ℝ ↦ E.beta (AffineMap.lineMap z₀ z τ))
          (fun τ : ℝ ↦ E.gamma (AffineMap.lineMap z₀ z τ))
          (z - z₀) t (closedFirstOrderAffineState C z t))
        (Set.Ici t) t

namespace LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData

/--
Add the automatic ball-domain segment-membership field to the analytic
straight-segment path data.
-/
def toAffineSegmentPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData E z)
    (hz : z ∈ N.domain) :
    LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathData E z where
  segment_mem :=
    localHyperbolicTwoJet_segment_mem_of_ballDomain
      hyperbolicTwoJetNormalizationHasBallDomainTheorem N hz
  beta_continuousOn := P.beta_continuousOn
  gamma_continuousOn := P.gamma_continuousOn
  state_continuousOn := P.state_continuousOn
  state_hasDerivWithinAt := P.state_hasDerivWithinAt

end LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData

/--
Differential-core straight-segment path data.

Continuity of the canonical state is no longer part of this boundary: it is
derived from the regularity of the two local conformal factors and the fact
that the straight segment stays in the normalized domain.
-/
structure LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) (z : ℂ) where
  /-- The `β` coefficient is continuous on the normalized domain. -/
  beta_continuousOn : ContinuousOn E.beta N.domain
  /-- The `γ` coefficient is continuous on the normalized domain. -/
  gamma_continuousOn : ContinuousOn E.gamma N.domain
  /-- The canonical restricted state solves the path ODE on `(0,1)`. -/
  state_hasDerivWithinAt :
    ∀ t, t ∈ Set.Ico (0 : ℝ) 1 →
      HasDerivWithinAt (closedFirstOrderAffineState C z)
        (closedFirstOrderPathVectorField
          (fun τ : ℝ ↦ E.beta (AffineMap.lineMap z₀ z τ))
          (fun τ : ℝ ↦ E.gamma (AffineMap.lineMap z₀ z τ))
          (z - z₀) t (closedFirstOrderAffineState C z t))
        (Set.Ici t) t

namespace LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathData

/--
Add the automatic state-continuity field to differential straight-segment path
data.
-/
def toAffineSegmentAnalyticPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathData E z)
    (hz : z ∈ N.domain) :
    LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData E z where
  beta_continuousOn := P.beta_continuousOn
  gamma_continuousOn := P.gamma_continuousOn
  state_continuousOn :=
    closedFirstOrderAffineState_continuousOn C
      (localHyperbolicTwoJet_segment_mem_of_ballDomain
        hyperbolicTwoJetNormalizationHasBallDomainTheorem N hz)
  state_hasDerivWithinAt := P.state_hasDerivWithinAt

end LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathData

/--
Potential-core straight-segment path data.

The `β` coefficient is continuous automatically, and `γ` is continuous as soon
as the scalar linearized potential is continuous.  The canonical restricted
state solves the path ODE by the chain rule and the stored Frechet-Wirtinger
directional equations.  Thus this package retains only potential continuity.
-/
structure LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) (z : ℂ) where
  /-- The scalar linearized Liouville potential is continuous on the normalized domain. -/
  potential_continuousOn : ContinuousOn E.linearized.potential N.domain

namespace LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathData

/--
Add the automatic coefficient-continuity fields to potential-core
straight-segment path data.
-/
def toAffineSegmentDifferentialPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathData E z)
    (hz : z ∈ N.domain) :
    LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathData E z where
  beta_continuousOn := E.beta_continuousOn
  gamma_continuousOn := E.gamma_continuousOn_of_potential_continuousOn
    P.potential_continuousOn
  state_hasDerivWithinAt := by
    intro t ht
    exact closedFirstOrderAffineState_hasDerivWithinAt E
      (localHyperbolicTwoJet_segment_mem_of_ballDomain
        hyperbolicTwoJetNormalizationHasBallDomainTheorem N hz t
        ⟨ht.1, le_of_lt ht.2⟩)

end LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathData

/--
Path-restriction data with coefficient paths controlled by compactness.

The coefficients are required to be continuous on `[0,1]` and extended outside
that interval by the standard clamp `projIcc`.  Compactness of `[0,1]` then
supplies the global coefficient bounds needed by the ODE uniqueness theorem.
-/
structure LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data) (z : ℂ) where
  /-- The affine path velocity after reparametrization to `[0,1]`. -/
  velocity : ℂ
  /-- The `β` coefficient restricted to the path, clamped outside `[0,1]`. -/
  betaPath : ℝ → ℂ
  /-- The `γ` coefficient restricted to the path, clamped outside `[0,1]`. -/
  gammaPath : ℝ → ℂ
  /-- The path-restricted state `(φ, α)`. -/
  state : ℝ → ℂ × ℂ
  /-- The path starts with the zero normalized state. -/
  state_zero : state 0 = 0
  /-- The endpoint is the target value of `(φ, α)`. -/
  state_one :
    state 1 =
      (((C.conformalFactor.logDensity z - u.logDensity z : ℝ) : ℂ),
        C.conformalFactor.wirtingerZ z - u.wirtingerZ z)
  /-- The restricted `β` coefficient is continuous on the interval. -/
  beta_continuousOn : ContinuousOn betaPath (Set.Icc (0 : ℝ) 1)
  /-- The restricted `γ` coefficient is continuous on the interval. -/
  gamma_continuousOn : ContinuousOn gammaPath (Set.Icc (0 : ℝ) 1)
  /-- Outside `[0,1]`, `β` is defined by clamping to the interval. -/
  beta_eq_projIcc :
    ∀ t : ℝ, betaPath t = betaPath (Set.projIcc (0 : ℝ) 1 zero_le_one t)
  /-- Outside `[0,1]`, `γ` is defined by clamping to the interval. -/
  gamma_eq_projIcc :
    ∀ t : ℝ, gammaPath t = gammaPath (Set.projIcc (0 : ℝ) 1 zero_le_one t)
  /-- The path-restricted state is continuous on the interval. -/
  state_continuousOn : ContinuousOn state (Set.Icc (0 : ℝ) 1)
  /-- The path-restricted state solves the path ODE. -/
  state_hasDerivWithinAt :
    ∀ t, t ∈ Set.Ico (0 : ℝ) 1 →
      HasDerivWithinAt state
        (closedFirstOrderPathVectorField betaPath gammaPath velocity t (state t))
        (Set.Ici t) t

namespace LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathData

/-- Forget compact-continuous coefficient path data to bounded-coefficient path data. -/
def toCoefficientBoundPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathData E z) :
    LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathData E z where
  velocity := P.velocity
  betaPath := P.betaPath
  gammaPath := P.gammaPath
  state := P.state
  state_zero := P.state_zero
  state_one := P.state_one
  betaBound :=
    Classical.choose
      (exists_nnnorm_bound_of_continuousOn_Icc_of_eq_projIcc
        P.beta_continuousOn P.beta_eq_projIcc)
  gammaBound :=
    Classical.choose
      (exists_nnnorm_bound_of_continuousOn_Icc_of_eq_projIcc
        P.gamma_continuousOn P.gamma_eq_projIcc)
  beta_norm_le :=
    Classical.choose_spec
      (exists_nnnorm_bound_of_continuousOn_Icc_of_eq_projIcc
        P.beta_continuousOn P.beta_eq_projIcc)
  gamma_norm_le :=
    Classical.choose_spec
      (exists_nnnorm_bound_of_continuousOn_Icc_of_eq_projIcc
        P.gamma_continuousOn P.gamma_eq_projIcc)
  state_continuousOn := P.state_continuousOn
  state_hasDerivWithinAt := P.state_hasDerivWithinAt

/-- Forget compact-continuous coefficient path data to operator-bound path data. -/
def toOperatorBoundPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathData E z) :
    LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathData E z :=
  P.toCoefficientBoundPathData.toOperatorBoundPathData

/-- Forget compact-continuous coefficient path data all the way to Lipschitz path data. -/
def toPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathData E z) :
    LocalLiouvilleSchwarzianClosedFirstOrderPathData E z :=
  P.toCoefficientBoundPathData.toPathData

/--
%%handwave
name:
  Log-density equality from continuous clamped coefficients
statement:
  If clamped coefficients are continuous on \([0,1]\) and the state solves the path system, then \(U(z)=V(z)\).
proof:
  Compactness bounds the coefficients, and bounded-coefficient uniqueness applies.
-/
theorem logDensity_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathData E z) :
    u.logDensity z = C.conformalFactor.logDensity z :=
  P.toPathData.logDensity_eq

end LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathData

namespace LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathData

/--
Straight-segment path data gives the compact-continuous clamped coefficient
path certificate.
-/
def toContinuousCoefficientPathData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathData E z) :
    LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathData E z where
  velocity := z - z₀
  betaPath := fun t : ℝ ↦ E.beta (closedFirstOrderClampedAffinePath z₀ z t)
  gammaPath := fun t : ℝ ↦ E.gamma (closedFirstOrderClampedAffinePath z₀ z t)
  state := closedFirstOrderAffineState C z
  state_zero := by
    simp [closedFirstOrderAffineState, E.linearized.phi_base_eq_zero,
      E.alpha_base_eq_zero]
  state_one := by
    simp [closedFirstOrderAffineState]
  beta_continuousOn := by
    refine P.beta_continuousOn.comp
      (continuous_closedFirstOrderClampedAffinePath z₀ z).continuousOn ?_
    intro t _ht
    exact P.segment_mem
      (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)
      (Set.projIcc (0 : ℝ) 1 zero_le_one t).2
  gamma_continuousOn := by
    refine P.gamma_continuousOn.comp
      (continuous_closedFirstOrderClampedAffinePath z₀ z).continuousOn ?_
    intro t _ht
    exact P.segment_mem
      (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)
      (Set.projIcc (0 : ℝ) 1 zero_le_one t).2
  beta_eq_projIcc := by
    intro t
    simp [closedFirstOrderClampedAffinePath_eq_projIcc]
  gamma_eq_projIcc := by
    intro t
    simp [closedFirstOrderClampedAffinePath_eq_projIcc]
  state_continuousOn := P.state_continuousOn
  state_hasDerivWithinAt := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    have hproj : (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) = t := by
      rw [Set.projIcc_of_mem zero_le_one htIcc]
    simpa [closedFirstOrderPathVectorField, closedFirstOrderClampedAffinePath, hproj] using
      P.state_hasDerivWithinAt t ht

/--
%%handwave
name:
  Log-density equality along a straight segment
statement:
  If the segment state has continuous coefficients, is continuous, and solves the system, then \(U(z)=V(z)\).
proof:
  Clamp the segment and apply pathwise ODE uniqueness.
-/
theorem logDensity_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathData E z) :
    u.logDensity z = C.conformalFactor.logDensity z :=
  P.toContinuousCoefficientPathData.logDensity_eq

/--
%%handwave
name:
  Derivative equality along a straight segment
statement:
  Under the same segment hypotheses, \(V_z(z)-U_z(z)=0\).
proof:
  The clamped path state vanishes; read its second endpoint component.
-/
theorem alpha_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathData E z) :
    C.conformalFactor.wirtingerZ z - u.wirtingerZ z = 0 :=
  P.toContinuousCoefficientPathData.toPathData.alpha_eq

end LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathData

namespace LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData

/--
%%handwave
name:
  Log-density equality from analytic segment data
statement:
  If the coefficients and state are continuous along the segment to \(z∈Ω\) and solve the system, then \(U(z)=V(z)\).
proof:
  Convexity supplies segment membership, reducing to the preceding result.
-/
theorem logDensity_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData E z)
    (hz : z ∈ N.domain) :
    u.logDensity z = C.conformalFactor.logDensity z :=
  (P.toAffineSegmentPathData hz).logDensity_eq

/--
%%handwave
name:
  Derivative equality from analytic segment data
statement:
  Under the analytic segment hypotheses, \(V_z(z)-U_z(z)=0\).
proof:
  Add automatic segment membership and use endpoint uniqueness.
-/
theorem alpha_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data}
    {z : ℂ}
    (P : LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData E z)
    (hz : z ∈ N.domain) :
    C.conformalFactor.wirtingerZ z - u.wirtingerZ z = 0 :=
  (P.toAffineSegmentPathData hz).alpha_eq

end LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData

/--
Path-data formulation of the closed first-order uniqueness boundary.

For each target point, it asks for a path certificate whose restricted state
solves the ordinary real ODE.  The actual ODE uniqueness step is then supplied
by mathlib's Grönwall theorem.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderPathDataTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data),
      ∀ z, z ∈ N.domain →
        Nonempty (LocalLiouvilleSchwarzianClosedFirstOrderPathData E z)

/--
Operator-bound path-data formulation of the closed first-order uniqueness
boundary.

The raw Lipschitz condition has been replaced by a uniform operator-norm bound
for the associated continuous linear maps.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathDataTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data),
      ∀ z, z ∈ N.domain →
        Nonempty (LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathData E z)

/--
Bounded-coefficient path-data formulation of the closed first-order uniqueness
boundary.

The operator-norm condition has been replaced by ordinary norm bounds for the
coefficient paths.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathDataTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data),
      ∀ z, z ∈ N.domain →
        Nonempty (LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathData E z)

/--
Compact-continuous coefficient path-data formulation of the closed first-order
uniqueness boundary.

The coefficient bounds are now derived from continuity on `[0,1]` together
with the standard clamped extension outside the interval.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathDataTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data),
      ∀ z, z ∈ N.domain →
        Nonempty
          (LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathData E z)

/--
Straight-segment path-data formulation of the closed first-order uniqueness
boundary.

The path is now fixed to be the affine segment from the normalized base point
to the target.  Endpoint data, clamping, coefficient boundedness, and the
Lipschitz ODE input are all derived from this package.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathDataTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data),
      ∀ z, z ∈ N.domain →
        Nonempty (LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathData E z)

/--
Analytic-core straight-segment path-data formulation of the closed first-order
uniqueness boundary.

The ball-domain geometry is now automatic; this target retains only
coefficient continuity, state continuity, and the restricted integral-curve
calculation along the canonical segment.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathDataTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data),
      ∀ z, z ∈ N.domain →
        Nonempty
          (LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData E z)

/--
Differential-core straight-segment path-data formulation of the closed
first-order uniqueness boundary.

The straight-segment domain geometry and the canonical state's continuity are
now automatic.  This target retains coefficient continuity and the restricted
integral-curve calculation.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathDataTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data),
      ∀ z, z ∈ N.domain →
        Nonempty
          (LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathData E z)

/--
Potential-core straight-segment path-data formulation of the closed first-order
uniqueness boundary.

Continuity of `β`, continuity of `γ` from the scalar potential, canonical
state continuity, and straight-segment domain geometry are now automatic.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathDataTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data),
      ∀ z, z ∈ N.domain →
        Nonempty
          (LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathData E z)

/--
Domain-level scalar-potential continuity target for the closed first-order
system.

This is the remaining local analytic regularity input for the pathwise
Grönwall route after all segment, coefficient, state, and chain-rule
bookkeeping has been discharged.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderPotentialContinuityTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data),
      ContinuousOn E.linearized.potential N.domain

/--
%%handwave
name:
  Potential continuity supplies potential-core data
statement:
  If \(a\) is continuous on \(Ω\), then every \(z∈Ω\) has the corresponding potential-core straight-segment data.
proof:
  Use the assumed domainwise continuity as the sole required datum.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathDataTheorem_of_potentialContinuity
    (hPotential :
      LocalLiouvilleSchwarzianClosedFirstOrderPotentialContinuityTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathDataTheorem := by
  intro u S D z₀ N C data E z hz
  exact ⟨{ potential_continuousOn := hPotential S N C data E }⟩

/--
%%handwave
name:
  Potential-core data supply differential data
statement:
  Potential-core segment data for every \(z∈Ω\) yield differential segment data.
proof:
  Continuity of \(a\) gives continuity of \(γ=a/4\); \(β\) is continuous and the chain rule supplies the state equation.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathDataTheorem_of_potentialPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathDataTheorem := by
  intro u S D z₀ N C data E z hz
  rcases hPath S N C data E z hz with ⟨P⟩
  exact ⟨P.toAffineSegmentDifferentialPathData hz⟩

/--
%%handwave
name:
  Differential data supply analytic data
statement:
  Differential segment data for every \(z∈Ω\) yield analytic segment data.
proof:
  Regularity of the fields makes the canonical state continuous.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathDataTheorem_of_differentialPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathDataTheorem := by
  intro u S D z₀ N C data E z hz
  rcases hPath S N C data E z hz with ⟨P⟩
  exact ⟨P.toAffineSegmentAnalyticPathData hz⟩

/--
%%handwave
name:
  Analytic data supply full segment data
statement:
  Analytic segment data for every \(z∈Ω\) yield full segment data.
proof:
  Convexity of the normalized ball supplies segment membership.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathDataTheorem_of_analyticPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathDataTheorem := by
  intro u S D z₀ N C data E z hz
  rcases hPath S N C data E z hz with ⟨P⟩
  exact ⟨P.toAffineSegmentPathData hz⟩

/--
%%handwave
name:
  Segment data give continuous clamped paths
statement:
  Full segment data for all \(z∈Ω\) yield continuous-coefficient clamped paths.
proof:
  Clamp the affine path and coefficients outside \([0,1]\).
-/
theorem localLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathDataTheorem_of_affineSegmentPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathDataTheorem := by
  intro u S D z₀ N C data E z hz
  rcases hPath S N C data E z hz with ⟨P⟩
  exact ⟨P.toContinuousCoefficientPathData⟩

/--
%%handwave
name:
  Continuous clamped paths give bounded coefficients
statement:
  Continuous clamped coefficient paths yield bounded-coefficient paths.
proof:
  Compactness gives bounds on \([0,1]\) and clamping extends them globally.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathDataTheorem_of_continuousCoefficientPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathDataTheorem := by
  intro u S D z₀ N C data E z hz
  rcases hPath S N C data E z hz with ⟨P⟩
  exact ⟨P.toCoefficientBoundPathData⟩

/--
%%handwave
name:
  Bounded coefficients give operator-bounded paths
statement:
  Bounded-coefficient paths yield operator-bounded paths.
proof:
  Apply the operator-norm estimate with the coefficient bounds.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathDataTheorem_of_coefficientBoundPathData
    (hPath : LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathDataTheorem := by
  intro u S D z₀ N C data E z hz
  rcases hPath S N C data E z hz with ⟨P⟩
  exact ⟨P.toOperatorBoundPathData⟩

/--
%%handwave
name:
  Operator-bounded paths give Lipschitz paths
statement:
  Operator-bounded paths yield uniformly Lipschitz paths.
proof:
  A uniform operator norm is a uniform Lipschitz constant.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderPathDataTheorem_of_operatorBoundPathData
    (hPath : LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderPathDataTheorem := by
  intro u S D z₀ N C data E z hz
  rcases hPath S N C data E z hz with ⟨P⟩
  exact ⟨P.toPathData⟩

/--
The linearized scalar package gives the closed first-order linear system by
combining the Riccati equation with the linearized `∂bar α` equation.
-/
def localLiouvilleSchwarzianClosedFirstOrderLinearSystemData_of_linearizedScalarDifference
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data where
  linearized := E
  beta := fun z ↦ C.conformalFactor.wirtingerZ z + u.wirtingerZ z
  gamma := fun z ↦ (1 / 4 : ℂ) * (E.potential z : ℂ)
  beta_eq := by
    intro z hz
    rfl
  gamma_eq := by
    intro z hz
    rfl
  phi_frechetDZValue_eq := E.scalar.firstOrder.phi_frechetDZValue_eq
  alpha_frechetDZValue_eq := by
    intro z hz
    rw [E.scalar.firstOrder.alpha_frechetDZValue_eq z hz]
  alpha_frechetDBarValue_eq := by
    intro z hz
    have hα := E.scalar.firstOrder.alpha_frechetDBarValue_eq z hz
    have hpot := E.potential_mul_phi_eq z hz
    calc
      frechetDBarValue
          (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w) z
          = (1 / 4 : ℂ) *
              ((Real.exp (2 * C.conformalFactor.logDensity z) : ℂ) -
                (Real.exp (2 * u.logDensity z) : ℂ)) := hα
      _ = (1 / 4 : ℂ) *
              (((Real.exp (2 * C.conformalFactor.logDensity z) -
                Real.exp (2 * u.logDensity z) : ℝ)) : ℂ) := by
            norm_num
      _ = (1 / 4 : ℂ) *
              ((E.potential z *
                (C.conformalFactor.logDensity z - u.logDensity z) : ℝ) : ℂ) := by
            rw [← hpot]
      _ = ((1 / 4 : ℂ) * (E.potential z : ℂ)) *
              ((C.conformalFactor.logDensity z - u.logDensity z : ℝ) : ℂ) := by
            norm_num
            ring
  phi_base_eq_zero := E.scalar.firstOrder.phi_base_eq_zero
  alpha_base_eq_zero := E.scalar.firstOrder.alpha_base_eq_zero

/--
The linearized scalar package gives the standard linear elliptic Cauchy-data
package.
-/
def localLiouvilleSchwarzianLinearEllipticCauchyData_of_linearizedScalarDifference
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data) :
    LocalLiouvilleSchwarzianLinearEllipticCauchyData data where
  linearized := E
  phi_base_eq_zero := E.phi_base_eq_zero
  phi_fderiv_base_eq_zero := E.phi_fderiv_base_eq_zero

/--
The scalar Liouville-difference package gives the linearized scalar package by
choosing the explicit pointwise difference quotient as coefficient.
-/
def localLiouvilleSchwarzianLinearizedScalarDifferenceData_of_scalarDifference
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (E : LocalLiouvilleSchwarzianScalarDifferenceData data) :
    LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data where
  scalar := E
  potential := E.linearizedPotential
  potential_mul_phi_eq := by
    intro z _hz
    exact E.linearizedPotential_mul_phi_eq z
  phi_laplacian_linear_eq := by
    intro z hz
    rw [E.phi_laplacian_eq z hz]
    exact (E.linearizedPotential_mul_phi_eq z).symm

/--
The first-order system plus the two Liouville equations gives the scalar
difference equation for `φ = v - u`.
-/
def localLiouvilleSchwarzianScalarDifferenceData_of_firstOrderSystem
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (F : LocalLiouvilleSchwarzianFirstOrderSystemData data) :
    LocalLiouvilleSchwarzianScalarDifferenceData data where
  firstOrder := F
  phi_laplacian_eq := by
    intro z hz
    have hC2 : ContDiffAt ℝ 2 C.conformalFactor.logDensity z :=
      (C.conformalFactor.logDensity_contDiffOn.contDiffAt
        (by
          have hzC : z ∈ C.conformalFactor.coordinateDomain := by
            simpa [data.pullback_domain_eq] using hz
          exact C.conformalFactor.isOpen_coordinateDomain.mem_nhds hzC)).of_le
        (by norm_num)
    have hu2 : ContDiffAt ℝ 2 u.logDensity z :=
      (u.logDensity_contDiffOn.contDiffAt
        (u.isOpen_coordinateDomain.mem_nhds
          (D.domain_subset (N.normalized.domain_subset_original hz)))).of_le
        (by norm_num)
    have hLap :
        Laplacian.laplacian
            (C.conformalFactor.logDensity - u.logDensity) z =
          Laplacian.laplacian C.conformalFactor.logDensity z -
            Laplacian.laplacian u.logDensity z :=
      hC2.laplacian_sub hu2
    have hCL :
        Laplacian.laplacian C.conformalFactor.logDensity z =
          Real.exp (2 * C.conformalFactor.logDensity z) := by
      exact data.pullback_solvesLiouville z (by simpa [data.pullback_domain_eq] using hz)
    have huL :
        Laplacian.laplacian u.logDensity z =
          Real.exp (2 * u.logDensity z) := by
      exact data.original_solvesLiouville z
        (D.domain_subset (N.normalized.domain_subset_original hz))
    simpa only [Pi.sub_apply, hCL, huL] using hLap

/--
The corrected metric-Wirtinger Riccati data, together with the two Liouville
equations already carried by `LocalLiouvilleSchwarzianUniquenessData`, produce
the genuine first-order Liouville-Schwarzian system.
-/
def localLiouvilleSchwarzianFirstOrderSystemData_of_wirtingerRiccati
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (A : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData data) :
    LocalLiouvilleSchwarzianFirstOrderSystemData data where
  wirtinger := A
  phi_frechetDZValue_eq := by
    intro z hz
    have hCDiff : DifferentiableAt ℝ C.conformalFactor.complexLogDensity z :=
      (C.conformalFactor.complexLogDensity_contDiffAt
        (by simpa [data.pullback_domain_eq] using hz)).differentiableAt (by norm_num)
    have huDiff : DifferentiableAt ℝ u.complexLogDensity z :=
      (u.complexLogDensity_contDiffAt
        (D.domain_subset (N.normalized.domain_subset_original hz))).differentiableAt
        (by norm_num)
    calc
      frechetDZValue
          (fun w : ℂ ↦
            ((C.conformalFactor.logDensity w - u.logDensity w : ℝ) : ℂ)) z
          =
        frechetDZValue
          (fun w : ℂ ↦
            C.conformalFactor.complexLogDensity w - u.complexLogDensity w) z := by
            congr 1
            ext w
            simp [LocalConformalFactor.complexLogDensity]
      _ = C.conformalFactor.wirtingerZ z - u.wirtingerZ z := by
            rw [frechetDZValue_sub_of_differentiableAt hCDiff huDiff]
            rfl
  alpha_frechetDBarValue_eq := by
    intro z hz
    have hCzbar :
        C.conformalFactor.wirtingerZBar z =
          (1 / 4 : ℂ) *
            (Laplacian.laplacian C.conformalFactor.logDensity z : ℂ) :=
      C.conformalFactor.wirtingerZBar_eq_laplacian z
        (by simpa [data.pullback_domain_eq] using hz)
    have huzbar :
        u.wirtingerZBar z =
          (1 / 4 : ℂ) *
            (Laplacian.laplacian u.logDensity z : ℂ) :=
      u.wirtingerZBar_eq_laplacian z
        (D.domain_subset (N.normalized.domain_subset_original hz))
    have hCL :
        Laplacian.laplacian C.conformalFactor.logDensity z =
          Real.exp (2 * C.conformalFactor.logDensity z) := by
      exact data.pullback_solvesLiouville z (by simpa [data.pullback_domain_eq] using hz)
    have huL :
        Laplacian.laplacian u.logDensity z =
          Real.exp (2 * u.logDensity z) := by
      exact data.original_solvesLiouville z
        (D.domain_subset (N.normalized.domain_subset_original hz))
    calc
      frechetDBarValue
          (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w) z
          = C.conformalFactor.wirtingerZBar z - u.wirtingerZBar z := by
            rw [frechetDBarValue_sub_of_differentiableAt
              (A.pullbackZ_differentiableAt z hz) (A.originalZ_differentiableAt z hz)]
            rfl
      _ = (1 / 4 : ℂ) *
          ((Real.exp (2 * C.conformalFactor.logDensity z) : ℂ) -
            (Real.exp (2 * u.logDensity z) : ℂ)) := by
            rw [hCzbar, huzbar, hCL, huL]
            ring
  phi_base_eq_zero := sub_eq_zero.mpr data.base_logDensity_eq
  alpha_base_eq_zero := sub_eq_zero.mpr data.base_uZ_eq

namespace LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData

/--
The over-strong complex-derivative package forgets to the honest
Frechet-Wirtinger Riccati package.
-/
def toCanonicalMetricWirtingerRiccatiData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (A : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData data) :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData data where
  originalZ_differentiableAt := by
    intro z hz
    exact u.wirtingerZ_differentiableAt
      (D.domain_subset (N.normalized.domain_subset_original hz))
  pullbackZ_differentiableAt := by
    intro z hz
    exact C.conformalFactor.wirtingerZ_differentiableAt
      (by simpa [data.pullback_domain_eq] using hz)
  same_metric_schwarzian := A.same_metric_schwarzian

end LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData

/--
For a canonical Poincare pullback formula candidate, the pullback-side metric
Schwarzian compatibility is already formalized.  Therefore metric-scaled
canonical Riccati data reduce to the two domain derivative facts plus the
original-side identification of `S.coefficient` with the metric Schwarzian of
`u`.
-/
def localLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData_of_canonicalPullbackFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N)
    (data :
      LocalLiouvilleSchwarzianUniquenessData N
        (LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData P.toFormulaData))
    (hOriginal : LocalOriginalMetricSchwarzianIdentification S)
    (hOriginalZ :
      ∀ z, z ∈ N.domain → HasDerivAt u.wirtingerZ (u.wirtingerZZ z) z)
    (hPullbackZ :
      ∀ z, z ∈ N.domain →
        HasDerivAt
          (LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData
            P.toFormulaData).conformalFactor.wirtingerZ
          ((LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData
            P.toFormulaData).conformalFactor.wirtingerZZ z) z) :
    LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData data where
  originalZ_has_deriv_at := hOriginalZ
  pullbackZ_has_deriv_at := hPullbackZ
  same_metric_schwarzian := by
    intro z hz
    exact
      LocalHyperbolicPullbackLiouvilleCandidate.ofCanonicalFormulaData_same_metricSchwarzian_of_original P
        (fun w hw ↦
          hOriginal.coefficient_eq_metric w
            (D.domain_subset (N.normalized.domain_subset_original hw))) z hz

/--
For canonical pullback formula data, the honest Wirtinger-Riccati package only
needs the original metric-Schwarzian identification: differentiability of the
canonical first Wirtinger fields follows from the `C^3` regularity built into
`LocalConformalFactor`.
-/
def localLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData_of_canonicalPullbackFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N)
    (data :
      LocalLiouvilleSchwarzianUniquenessData N
        (LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData P.toFormulaData))
    (hOriginal : LocalOriginalMetricSchwarzianIdentification S) :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData data where
  originalZ_differentiableAt := by
    intro z hz
    exact u.wirtingerZ_differentiableAt
      (D.domain_subset (N.normalized.domain_subset_original hz))
  pullbackZ_differentiableAt := by
    intro z hz
    exact
      (LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData
        P.toFormulaData).conformalFactor.wirtingerZ_differentiableAt
        (by
          simpa [LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData,
            LocalHyperbolicPullbackLiouvilleFormulaData.conformalFactor])
  same_metric_schwarzian := by
    intro z hz
    exact
      LocalHyperbolicPullbackLiouvilleCandidate.ofCanonicalFormulaData_same_metricSchwarzian_of_original P
        (fun w hw ↦
          hOriginal.coefficient_eq_metric w
            (D.domain_subset (N.normalized.domain_subset_original hw))) z hz

namespace LocalLiouvilleSchwarzianCanonicalRiccatiCalculusData

/--
%%handwave
name:
  Equality from equality of first Wirtinger derivatives
statement:
  Let \(Ω\) be open and preconnected. If real \(U,V\) have equal \(∂_z\) derivatives on \(Ω\) and \(U(z₀)=V(z₀)\), then \(U=V\) on \(Ω\).
proof:
  Equality of \(∂_z\) gives equality of full real differentials, so \(U-V\) is constant and vanishes at \(z₀\).
-/
theorem logDensity_eq_of_first_derivative_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (hFirst :
      ∀ z, z ∈ N.domain →
        C.conformalFactor.wirtingerZ z - u.wirtingerZ z = 0) :
    ∀ z, z ∈ N.domain →
      u.logDensity z = C.conformalFactor.logDensity z := by
  have hOpen : IsOpen N.domain := by
    simpa [LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
      LocalUpperHalfPlaneProjectiveNormalization.domain] using
      N.normalized.projective.isOpen_domain
  have huDiff : DifferentiableOn ℝ u.logDensity N.domain :=
    (u.logDensity_contDiffOn.differentiableOn (by norm_num)).mono
      (fun z hz ↦ D.domain_subset (N.normalized.domain_subset_original hz))
  have hCDiff : DifferentiableOn ℝ C.conformalFactor.logDensity N.domain := by
    have hC :
        DifferentiableOn ℝ C.conformalFactor.logDensity
          C.conformalFactor.coordinateDomain :=
      C.conformalFactor.logDensity_contDiffOn.differentiableOn (by norm_num)
    simpa [data.pullback_domain_eq] using hC
  have hZ :
      ∀ z, z ∈ N.domain →
        frechetDZValue (fun w : ℂ ↦ (u.logDensity w : ℂ)) z =
          frechetDZValue (fun w : ℂ ↦ (C.conformalFactor.logDensity w : ℂ)) z := by
    intro z hz
    have hEq : C.conformalFactor.wirtingerZ z = u.wirtingerZ z :=
      sub_eq_zero.mp (hFirst z hz)
    simpa [LocalConformalFactor.wirtingerZ, LocalConformalFactor.complexLogDensity]
      using hEq.symm
  have hEqOn :
      N.domain.EqOn u.logDensity C.conformalFactor.logDensity :=
    eqOn_of_frechetDZValue_complex_ofReal_eq hOpen data.domain_preconnected
      huDiff hCDiff hZ N.base_mem data.base_logDensity_eq.symm
  intro z hz
  exact hEqOn hz

/--
Canonical Riccati calculus data specialize to the earlier concrete calculus
package by choosing the actual Frechet-Wirtinger fields.
-/
def toCalculusData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (A : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusData data) :
    LocalLiouvilleSchwarzianRiccatiReductionCalculusData data where
  originalZ := u.wirtingerZ
  pullbackZ := C.conformalFactor.wirtingerZ
  originalZZ := u.wirtingerZZ
  pullbackZZ := C.conformalFactor.wirtingerZZ
  originalZ_has_deriv_at := A.originalZ_has_deriv_at
  pullbackZ_has_deriv_at := A.pullbackZ_has_deriv_at
  same_half_schwarzian := by
    intro z hz
    simpa [LocalConformalFactor.halfSchwarzianCoefficient] using
      A.same_half_schwarzian z hz
  base_first_derivative_eq := data.base_uZ_eq
  logDensity_eq_of_first_derivative_eq :=
    logDensity_eq_of_first_derivative_eq data

end LocalLiouvilleSchwarzianCanonicalRiccatiCalculusData

/--
The Riccati difference package behind local Liouville-Schwarzian uniqueness.

If `u` and `v` have the same Schwarzian expression
`u_zz - u_z^2 = v_zz - v_z^2`, then
`α = v_z - u_z` satisfies
`α_z = α * (v_z + u_z)`.  With the normalized base data,
`α z₀ = 0`.  The final field records that once `α = 0`, the remaining
difference `v - u` is constant and the base log-density equality makes it zero.

The construction of `alpha` and `coefficient` is still upstream for the
pullback log-density: once its canonical Wirtinger derivative fields are
connected to the original metric Schwarzian data, the Riccati package itself
carries honest `HasDerivAt` and analyticity evidence for the resulting
coefficient.
-/
structure LocalLiouvilleSchwarzianRiccatiDifferenceData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (_data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- Symbolic difference `α = v_z - u_z`. -/
  alpha : ℂ → ℂ
  /-- Symbolic coefficient `v_z + u_z` in the Riccati equation. -/
  coefficient : ℂ → ℂ
  /-- The Riccati equation `α_z = α * coefficient` on the local domain. -/
  alpha_has_deriv_at_eq_on_domain :
    ∀ z, z ∈ N.domain → HasDerivAt alpha (alpha z * coefficient z) z
  /-- The Riccati coefficient is analytic on the normalized local domain. -/
  coefficient_analytic_on_domain : AnalyticOnNhd ℂ coefficient N.domain
  /-- The normalized base data gives `α z₀ = 0`. -/
  alpha_base_eq_zero : alpha z₀ = 0
  /-- If `α` vanishes on the domain, the logarithmic factors agree there. -/
  logDensity_eq_of_alpha_eq_zero :
    (∀ z, z ∈ N.domain → alpha z = 0) →
      ∀ z, z ∈ N.domain →
        u.logDensity z = C.conformalFactor.logDensity z

namespace LocalLiouvilleSchwarzianRiccatiReductionCalculusData

/--
%%handwave
name:
  Analyticity of the Riccati coefficient
statement:
  If complex fields \(p,q\) are complex differentiable throughout open \(Ω\), then \(p+q\) is analytic on \(Ω\).
proof:
  Their sum is differentiable on the open set, hence analytic.
-/
theorem coefficient_analytic_on_domain
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (A : LocalLiouvilleSchwarzianRiccatiReductionCalculusData data) :
    AnalyticOnNhd ℂ (fun z ↦ A.pullbackZ z + A.originalZ z) N.domain := by
  have hOpen : IsOpen N.domain := by
    simpa [LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
      LocalUpperHalfPlaneProjectiveNormalization.domain] using
      N.normalized.projective.isOpen_domain
  have hPullback : DifferentiableOn ℂ A.pullbackZ N.domain := by
    intro z hz
    exact (A.pullbackZ_has_deriv_at z hz).differentiableAt.differentiableWithinAt
  have hOriginal : DifferentiableOn ℂ A.originalZ N.domain := by
    intro z hz
    exact (A.originalZ_has_deriv_at z hz).differentiableAt.differentiableWithinAt
  exact (hPullback.add hOriginal).analyticOnNhd hOpen

/--
The concrete Riccati calculus data produce the Riccati difference package.

The only algebraic point is
`V_zz - U_zz = (V_z - U_z) * (V_z + U_z)`, which follows by subtracting the
two equal half-Schwarzian expressions.
-/
def toRiccatiDifferenceData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (A : LocalLiouvilleSchwarzianRiccatiReductionCalculusData data) :
    LocalLiouvilleSchwarzianRiccatiDifferenceData data where
  alpha := fun z ↦ A.pullbackZ z - A.originalZ z
  coefficient := fun z ↦ A.pullbackZ z + A.originalZ z
  alpha_has_deriv_at_eq_on_domain := by
    intro z hz
    have hderiv :
        HasDerivAt (fun w ↦ A.pullbackZ w - A.originalZ w)
          (A.pullbackZZ z - A.originalZZ z) z :=
      (A.pullbackZ_has_deriv_at z hz).sub (A.originalZ_has_deriv_at z hz)
    have hdiff :
        A.pullbackZZ z - A.originalZZ z =
          (A.pullbackZ z - A.originalZ z) * (A.pullbackZ z + A.originalZ z) := by
      have h := A.same_half_schwarzian z hz
      linear_combination h
    exact hderiv.congr_deriv hdiff
  coefficient_analytic_on_domain := A.coefficient_analytic_on_domain
  alpha_base_eq_zero := by
    simp [A.base_first_derivative_eq]
  logDensity_eq_of_alpha_eq_zero := A.logDensity_eq_of_first_derivative_eq

end LocalLiouvilleSchwarzianRiccatiReductionCalculusData

/--
Corrected canonical metric Riccati data plus the extra holomorphicity needed
to use the scalar integrating-factor uniqueness argument.

The bare Frechet-Wirtinger equation
`∂z α = α * β` with `α z₀ = 0` is not by itself a one-variable ODE uniqueness
principle.  This package records the additional Cauchy-Riemann/analytic data
which turns it back into the holomorphic Riccati problem already discharged
below.
-/
structure LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    (data : LocalLiouvilleSchwarzianUniquenessData N C) where
  /-- The honest Frechet-Wirtinger Riccati equation. -/
  wirtinger :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData data
  /-- The difference `α = v_z - u_z` satisfies the Cauchy-Riemann condition. -/
  alpha_hasDBarZeroOn :
    HasDBarZeroOn
      (fun z : ℂ ↦ C.conformalFactor.wirtingerZ z - u.wirtingerZ z) N.domain
  /-- The coefficient `β = v_z + u_z` is analytic on the normalized domain. -/
  coefficient_analytic_on_domain :
    AnalyticOnNhd ℂ
      (fun z : ℂ ↦ C.conformalFactor.wirtingerZ z + u.wirtingerZ z) N.domain

namespace LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiData

/--
The holomorphic strengthened Wirtinger-Riccati package specializes to the
scalar Riccati difference package used by the existing integrating-factor
proof.
-/
def toRiccatiDifferenceData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (A : LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiData data) :
    LocalLiouvilleSchwarzianRiccatiDifferenceData data where
  alpha := fun z ↦ C.conformalFactor.wirtingerZ z - u.wirtingerZ z
  coefficient := fun z ↦ C.conformalFactor.wirtingerZ z + u.wirtingerZ z
  alpha_has_deriv_at_eq_on_domain := by
    intro z hz
    have hderiv :
        HasDerivAt
          (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w)
          (frechetDZValue
            (fun w : ℂ ↦ C.conformalFactor.wirtingerZ w - u.wirtingerZ w) z) z :=
      hasDerivAt_frechetDZValue_of_hasDBarZeroAt (A.alpha_hasDBarZeroOn z hz)
    exact hderiv.congr_deriv (A.wirtinger.alpha_frechetDZValue_eq z hz)
  coefficient_analytic_on_domain := A.coefficient_analytic_on_domain
  alpha_base_eq_zero := by
    simp [data.base_uZ_eq]
  logDensity_eq_of_alpha_eq_zero := by
    intro hα
    exact
      LocalLiouvilleSchwarzianCanonicalRiccatiCalculusData.logDensity_eq_of_first_derivative_eq
        data hα

end LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiData

namespace LocalLiouvilleSchwarzianRiccatiDifferenceData

/--
An integrating factor for the Riccati difference equation.

For the equation `α_z = α * coefficient`, an integrating factor is a
nonvanishing function `μ` such that `α * μ` is constant on the local domain.
The usual construction is `μ = exp (-∫ coefficient)`, but that analytic
construction is kept separate from this algebraic consequence.
-/
structure IntegratingFactorData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (R : LocalLiouvilleSchwarzianRiccatiDifferenceData data) where
  /-- The integrating factor. -/
  integratingFactor : ℂ → ℂ
  /-- The integrating factor is nonzero on the local domain. -/
  integratingFactor_ne_zero_on_domain :
    ∀ z, z ∈ N.domain → integratingFactor z ≠ 0
  /-- The product `α * μ` is constant and equal to its base value. -/
  product_constant_on_domain :
    ∀ z, z ∈ N.domain →
      R.alpha z * integratingFactor z =
        R.alpha z₀ * integratingFactor z₀

/--
A primitive for the coefficient in the Riccati difference equation.

For `α_z = α * coefficient`, a primitive `A` of `coefficient` gives the
integrating factor `μ = exp (-A)`.
-/
structure PrimitiveData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (R : LocalLiouvilleSchwarzianRiccatiDifferenceData data) where
  /-- A local primitive of the Riccati coefficient. -/
  primitiveFun : ℂ → ℂ
  /-- The derivative of `primitive` is `R.coefficient` on the local domain. -/
  has_deriv_at_eq_coefficient_on_domain :
    ∀ z, z ∈ N.domain → HasDerivAt primitiveFun (R.coefficient z) z

namespace IntegratingFactorData

/--
%%handwave
name:
  An integrating factor annihilates the Riccati solution
statement:
  If \(α(z₀)=0\) and nowhere-zero \(μ\) makes \(αμ\) constant on \(Ω\), then \(α=0\) there.
proof:
  The product equals \(α(z₀)μ(z₀)=0\); cancel \(μ(z)≠0\).
-/
theorem alpha_eq_zero
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    (M : IntegratingFactorData R) :
    ∀ z, z ∈ N.domain → R.alpha z = 0 := by
  intro z hz
  have hprod :
      R.alpha z * M.integratingFactor z = 0 := by
    calc
      R.alpha z * M.integratingFactor z
          = R.alpha z₀ * M.integratingFactor z₀ :=
            M.product_constant_on_domain z hz
      _ = 0 := by
            rw [R.alpha_base_eq_zero, zero_mul]
  exact (mul_eq_zero.mp hprod).resolve_right
    (M.integratingFactor_ne_zero_on_domain z hz)

end IntegratingFactorData

namespace PrimitiveData

/-- The integrating factor `μ = exp (-A)` attached to a primitive `A`. -/
def integratingFactor
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    (P : PrimitiveData R) : ℂ → ℂ :=
  fun z ↦ Complex.exp (-(P.primitiveFun z))

/--
%%handwave
name:
  The exponential integrating factor never vanishes
statement:
  For every \(z∈ℂ\), \(μ(z)=e^{-A(z)}\) is nonzero.
proof:
  The complex exponential has no zeros.
-/
theorem integratingFactor_ne_zero
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    (P : PrimitiveData R) (z : ℂ) :
    P.integratingFactor z ≠ 0 :=
  Complex.exp_ne_zero _

/--
Turn a primitive into integrating-factor data once the product constancy
calculation has been proved.
-/
def toIntegratingFactorData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    (P : PrimitiveData R)
    (hConst :
      ∀ z, z ∈ N.domain →
        R.alpha z * P.integratingFactor z =
          R.alpha z₀ * P.integratingFactor z₀) :
    IntegratingFactorData R where
  integratingFactor := P.integratingFactor
  integratingFactor_ne_zero_on_domain := by
    intro z _hz
    exact P.integratingFactor_ne_zero z
  product_constant_on_domain := hConst

/--
The derivative-vanishing package for the primitive integrating factor.

This is the concrete calculus statement left after applying the product rule:
the product `α * exp(-A)` is differentiable on the normalized domain and has
zero derivative there.
-/
structure ProductDerivativeZeroData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    (P : PrimitiveData R) where
  /-- The integrating-factor product is differentiable on the local domain. -/
  product_differentiableOn :
    DifferentiableOn ℂ (fun z ↦ R.alpha z * P.integratingFactor z) N.domain
  /-- The derivative of the integrating-factor product is zero on the local domain. -/
  product_deriv_eq_zero_on_domain :
    Set.EqOn (deriv (fun z ↦ R.alpha z * P.integratingFactor z)) 0 N.domain

/--
%%handwave
name:
  Derivative of the primitive integrating factor
statement:
  If \(A'(z)=β(z)\), then \(μ=e^{-A}\) satisfies \(μ'=-βμ\).
proof:
  Apply the chain rule to \(e^{-A}\).
-/
theorem integratingFactor_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    (P : PrimitiveData R) {z : ℂ} (hz : z ∈ N.domain) :
    HasDerivAt P.integratingFactor (-(R.coefficient z) * P.integratingFactor z) z := by
  have hA : HasDerivAt (fun w ↦ -(P.primitiveFun w)) (-(R.coefficient z)) z :=
    (P.has_deriv_at_eq_coefficient_on_domain z hz).neg
  have hexp :
      HasDerivAt (fun w ↦ Complex.exp (-(P.primitiveFun w)))
        (Complex.exp (-(P.primitiveFun z)) * (-(R.coefficient z))) z :=
    hA.cexp
  simpa [integratingFactor, mul_comm] using hexp

/--
%%handwave
name:
  The integrating-factor product has zero derivative
statement:
  If \(α'=αβ\) and \(A'=β\), then \((αe^{-A})'=0\) on \(Ω\).
proof:
  Use the product rule and cancel the two terms.
-/
theorem product_hasDerivAt_zero
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    (P : PrimitiveData R) {z : ℂ} (hz : z ∈ N.domain) :
    HasDerivAt (fun w ↦ R.alpha w * P.integratingFactor w) 0 z := by
  have hα := R.alpha_has_deriv_at_eq_on_domain z hz
  have hμ := P.integratingFactor_hasDerivAt hz
  convert hα.mul hμ using 1
  ring

/--
The Riccati equation plus a primitive closes the product-derivative-zero
calculus package.
-/
def productDerivativeZeroData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    (P : PrimitiveData R) :
    ProductDerivativeZeroData P where
  product_differentiableOn := by
    intro z hz
    exact (P.product_hasDerivAt_zero hz).differentiableAt.differentiableWithinAt
  product_deriv_eq_zero_on_domain := by
    intro z hz
    exact (P.product_hasDerivAt_zero hz).deriv

/--
%%handwave
name:
  Zero derivative makes the product constant
statement:
  If \(Ω\) is open and preconnected and \((αe^{-A})'=0\), then \(α(z)e^{-A(z)}=α(z₀)e^{-A(z₀)}\) for \(z∈Ω\).
proof:
  A differentiable function with zero derivative on an open preconnected set is constant.
-/
theorem product_constant_on_domain_of_deriv_eq_zero
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    {P : PrimitiveData R}
    (Z : ProductDerivativeZeroData P) :
    ∀ z, z ∈ N.domain →
      R.alpha z * P.integratingFactor z =
        R.alpha z₀ * P.integratingFactor z₀ := by
  intro z hz
  exact N.normalized.projective.isOpen_domain.is_const_of_deriv_eq_zero
    data.domain_preconnected Z.product_differentiableOn
    Z.product_deriv_eq_zero_on_domain hz N.base_mem

end PrimitiveData

end LocalLiouvilleSchwarzianRiccatiDifferenceData

end

end JJMath
