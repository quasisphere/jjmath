import JJMath.Hyperbolic.Schwarzian.Developing.MetricRecovery

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace LocalLiouvilleSchwarzianUniquenessData

/--
%%handwave
name:
  Liouville--Schwarzian uniqueness data from a pullback candidate
statement:
  A normalized Poincaré pullback candidate, the original Liouville equation, and preconnectedness of the normalized domain supply two Liouville solutions with equal Schwarzian coefficient and equal density and first Wirtinger derivative at the base point.
-/
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

%%handwave
name:
  Divided difference of the doubled exponential
statement:
  For $u,v\in\mathbb R$, this is $(e^{2v}-e^{2u})/(v-u)$ when $v\ne u$ and the diagonal derivative $2e^{2u}$ when $v=u$.
-/
def realExpTwoDividedDifference (u v : ℝ) : ℝ :=
  if v - u = 0 then
    2 * Real.exp (2 * u)
  else
    (Real.exp (2 * v) - Real.exp (2 * u)) / (v - u)

/--
%%handwave
name:
  Continuous extension of the hyperbolic sine quotient
statement:
  For $x\in\mathbb R$, this is $\sinh(x)/x$ when $x\ne0$ and its continuous limiting value $1$ at $x=0$.
-/
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

%%handwave
name:
  Continuity assertion for the doubled-exponential divided difference
statement:
  The completed divided difference $(u,v)\mapsto(e^{2v}-e^{2u})/(v-u)$, with diagonal value $2e^{2u}$, is continuous on $\mathbb R^2$.
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

%%handwave
name:
  Linearized Liouville potential
statement:
  Given log-densities $U$ and $V$, the potential $a(z)$ is the completed divided difference of $x\mapsto e^{2x}$ at $U(z)$ and $V(z)$, so that $e^{2V(z)}-e^{2U(z)}=a(z)(V(z)-U(z))$.
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

end LocalLiouvilleSchwarzianLinearizedScalarDifferenceData



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

%%handwave
name:
  Path-restricted closed Liouville--Schwarzian vector field
statement:
  For coefficient paths $\beta,\gamma$, complex velocity $\xi$, and state $(\varphi,\alpha)\in\mathbb C^2$, this real vector field reconstructs the directional derivatives from $\varphi_z=\alpha$, $\varphi_{\bar z}=\overline\alpha$, $\alpha_z=\beta\alpha$, and $\alpha_{\bar z}=\gamma\varphi$.
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

/--
%%handwave
name:
  Real-linear complex multiplication operator
statement:
  For $a\in\mathbb C$, this is the continuous $\mathbb R$-linear operator $z\mapsto az$ on $\mathbb C$.
-/
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

%%handwave
name:
  Continuous linear operator of the path system
statement:
  For fixed $\beta,\gamma,\xi\in\mathbb C$, this is the continuous $\mathbb R$-linear endomorphism of $\mathbb C^2$ whose value at $(\varphi,\alpha)$ is the closed Liouville--Schwarzian path vector field with those coefficients.
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

/--
%%handwave
name:
  Lipschitz path data from a uniform operator bound
statement:
  A path solution whose time-dependent linear operators have a uniform norm bound determines path data with a uniform Lipschitz constant for the vector field.
-/
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

/--
%%handwave
name:
  Operator-bound path data from bounded coefficients
statement:
  Uniform bounds for the coefficient paths $\beta$ and $\gamma$ yield a uniform operator-norm bound for the associated linear path system, while preserving the state and its differential equation.
-/
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

/--
%%handwave
name:
  Lipschitz path data from bounded coefficients
statement:
  A path solution with uniformly bounded coefficient paths $\beta$ and $\gamma$ determines Lipschitz path data for the same closed first-order system.
-/
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

end LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathData

/--
The clamped affine path from the normalized base point `z₀` to a target point
`z`.

The clamp makes the coefficient paths global functions of real time, while the
ODE proof only uses the unclamped segment on `[0,1]`.

%%handwave
name:
  Clamped affine segment
statement:
  For $z_0,z\in\mathbb C$, the path is $c(t)=(1-s)z_0+sz$ with $s$ the projection of $t\in\mathbb R$ onto $[0,1]$.
-/
def closedFirstOrderClampedAffinePath (z₀ z : ℂ) (t : ℝ) : ℂ :=
  AffineMap.lineMap z₀ z (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)

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

%%handwave
name:
  Canonical Liouville--Schwarzian state along an affine segment
statement:
  Along $w(t)=(1-t)z_0+tz$, the state is $X(t)=(V(w(t))-U(w(t)),\,V_z(w(t))-U_z(w(t)))\in\mathbb C^2$.
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

%%handwave
name:
  Straight-segment path data from analytic path data
statement:
  For a target point in the normalized ball domain, analytic coefficient and state data along the straight segment determine full straight-segment path data because convexity keeps the segment inside the domain.
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

%%handwave
name:
  Analytic affine-segment data from differential data
statement:
  Differential path data along a segment in the normalized domain determine analytic path data, since the regularity of the two log-densities makes the canonical state continuous along the segment.
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

%%handwave
name:
  Differential affine-segment data from a continuous potential
statement:
  Continuity of the linearized scalar potential along the normalized domain makes both coefficients of the closed first-order system continuous and, with the chain rule, supplies differential path data along every admissible affine segment.
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

/--
%%handwave
name:
  Bounded-coefficient path data from clamped continuity
statement:
  Coefficient paths that are continuous on $[0,1]$ and constant under projection onto this interval are globally bounded, yielding bounded-coefficient data for the same path solution.
-/
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

/--
%%handwave
name:
  Lipschitz path data from clamped continuous coefficients
statement:
  A path solution with coefficient paths continuous on $[0,1]$ and clamped outside it determines Lipschitz path data for the closed first-order system.
-/
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

%%handwave
name:
  Clamped coefficient data from straight-segment data
statement:
  Straight-segment data from $z_0$ to $z$ determine global coefficient paths by composing with the clamped affine segment, together with the canonical state and its path differential equation.
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

end LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathData

/--
The linearized scalar package gives the closed first-order linear system by
combining the Riccati equation with the linearized `∂bar α` equation.

%%handwave
name:
  Closed first-order system from the linearized scalar equation
statement:
  If $\varphi=V-U$ satisfies the linearized Liouville equation with potential $a$, then $\alpha=V_z-U_z$ satisfies the closed system $\varphi_z=\alpha$, $\alpha_z=(V_z+U_z)\alpha$, and $\alpha_{\bar z}=\frac14a\varphi$.
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
The scalar Liouville-difference package gives the linearized scalar package by
choosing the explicit pointwise difference quotient as coefficient.

%%handwave
name:
  Linearized scalar equation from the Liouville difference
statement:
  The scalar equation $\Delta(V-U)=e^{2V}-e^{2U}$ becomes $\Delta\varphi=a\varphi$ by taking $a$ to be the completed divided difference of $x\mapsto e^{2x}$ at $U$ and $V$.
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

%%handwave
name:
  Scalar difference equation from two Liouville solutions
statement:
  If $U$ and $V$ solve $\Delta U=e^{2U}$ and $\Delta V=e^{2V}$, then $\varphi=V-U$ satisfies $\Delta\varphi=e^{2V}-e^{2U}$, together with the stored first-order identities.
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

%%handwave
name:
  First-order Liouville--Schwarzian system from Wirtinger Riccati data
statement:
  For two Liouville log-densities $U,V$ with the same metric Schwarzian, Wirtinger differentiation gives $\varphi_z=\alpha$, $\alpha_z=(V_z+U_z)\alpha$, and $\alpha_{\bar z}=\frac14(e^{2V}-e^{2U})$, with $\varphi=\alpha=0$ at the normalized base point.
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


/--
For canonical pullback formula data, the honest Wirtinger-Riccati package only
needs the original metric-Schwarzian identification: differentiability of the
canonical first Wirtinger fields follows from the `C^3` regularity built into
`LocalConformalFactor`.

%%handwave
name:
  Wirtinger Riccati data for the canonical hyperbolic pullback
statement:
  A canonical Poincaré pullback formula and identification of the original metric Schwarzian give differentiable first Wirtinger fields whose difference obeys the Riccati identity forced by equality of the two metric Schwarzians.
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







end

end JJMath
