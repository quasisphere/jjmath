# Condenser Capacity and Quasiconformal Pullback

Condenser capacity is the planned bridge from the Sobolev area and inverse
theorems to normalized compactness on the Riemann sphere.  The planar theory
uses continuous real-valued local $W^{1,2}$ representatives, which keeps the
plate conditions pointwise while allowing weak differentials in the energy.

## Planar capacity

For plates $E_0,E_1\subseteq\Omega$, a competitor equals $0$ on $E_0$ and
$1$ on $E_1$.  Its extended Dirichlet energy and the variational capacity are

$$
  \mathcal E_\Omega(u)=\int_\Omega\lVert Du(z)\rVert^2\,dz,
  \qquad
  \operatorname{cap}_\Omega(E_0,E_1)=\inf_u\mathcal E_\Omega(u).
$$

@include{lean:JJMath.Quasiconformal.PlanarCondenserCompetitor}

@include{lean:JJMath.Quasiconformal.planarCondenserCapacity}

## The pullback energy estimate

Let $F:\Omega\to\Omega'$ be $K$-quasiconformal.  For every target covector
field $a(y):\mathbb C\to\mathbb R$, submultiplicativity, the pointwise
distortion inequality, and the oriented Sobolev area formula give

$$
  \int_\Omega\lVert a(F(z))\circ DF(z)\rVert^2\,dz
    \leq K\int_{\Omega'}\lVert a(y)\rVert^2\,dy.
$$

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.lintegral_norm_comp_weakDifferential_sq_le}

This estimate is already strong enough for smooth competitors once the weak
chain rule is available.

## The smooth weak chain rule

Suppose $u$ is smooth and compactly supported and $T_n$ is a smooth graph
approximation to a local $W^{1,2}$ map $f$.  The chain-rule error splits as

$$
  (Du(T_n)-Du(f))[Df]
    +Du(T_n)[DT_n-Df].
$$

The differential field $Du$ is globally Lipschitz and bounded.  Each summand
therefore vanishes as an $L^2$ pairing, giving convergence of the weak test
integrals.

@include{lean:JJMath.Quasiconformal.PlanarWeakSobolevSmoothApproxGraphL2Data.smoothOuter_chain_integral_tendsto}

Passing the classical identities for $u\circ T_n$ to the limit proves

$$
  D(u\circ f)=(Du\circ f)\circ Df
$$

as a weak differential, with the required local $L^2$ bounds.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.postcomp_smoothCompactlySupported}

Consequently every smooth compactly supported target competitor pulls back to
an actual source competitor, and its energy is at most $K$ times the target
energy.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.exists_smoothPullbackCompetitor_energy_le}

## Bounded retraction of Sobolev approximants

On a compact target neighborhood, a continuous real-valued Sobolev function
has range in a compact interval.  There is a smooth compactly supported
scalar function $\vartheta$ which equals the identity, with identity
differential, throughout that interval.

@include{lean:JJMath.Quasiconformal.exists_smoothCompactlySupported_fix_continuousOn_compact_range}

Let $w_n\to w$ and $Dw_n\to Dw$ in the local Sobolev graph norm.  After
passing to a subsequence, $w_n\to w$ almost everywhere.  The retracted values
$\vartheta(w_n)$ are uniformly bounded and still converge almost everywhere
to $w$.  Their differentials satisfy

$$
  D\vartheta(w_n)\circ Dw_n-Dw
  =D\vartheta(w_n)(Dw_n-Dw)
   +(D\vartheta(w_n)-D\vartheta(w))Dw.
$$

The first term tends to zero by graph-norm convergence and boundedness of
$D\vartheta$.  The second tends to zero almost everywhere and is dominated
by a constant multiple of $\lVert Dw\rVert$, so dominated convergence gives
strong $L^2$ convergence.

@include{lean:JJMath.Quasiconformal.scalarWeakSobolevSmoothApproxGraphL2Data_exists_retracted_subsequence}

## Continuous Sobolev pullback

Let $u$ be continuous and locally $W^{1,2}$ on the target.  For the compact
support of a source test, choose a compact neighborhood of its image, use the
retracted approximation there, and multiply by a target cutoff equal to one
near that image.  The smooth pullback theorem applies to every approximant.
Lusin $N^{-1}$ and bounded dominated convergence pass the value pairing to
the limit.  The quasiconformal energy estimate sends the target $L^2$
differential error to zero on the source, so no unweighted $L^2$ composition
estimate is needed.  The resulting weak differential is

$$
  D(u\circ F)(z)=Du(F(z))\circ DF(z).
$$

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.postcomp_continuous_isLocalW12RealOn}

Consequently every continuous Sobolev competitor for the image condenser
pulls back to a source competitor with the expected energy control.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.exists_pullbackCompetitor_energy_le}

Taking the infimum over target competitors gives one capacity inequality.
Applying it to the quasiconformal inverse gives the other:

$$
  \operatorname{cap}_{\Omega'}(F(E_0),F(E_1))
    \leq K\operatorname{cap}_{\Omega}(E_0,E_1),
  \qquad
  \operatorname{cap}_{\Omega}(E_0,E_1)
    \leq K\operatorname{cap}_{\Omega'}(F(E_0),F(E_1)).
$$

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.planarCondenserCapacity_distortion}

## Model ring geometry

The geometric layer uses the whole-plane condenser whose zero plate is the
closed disk of radius $r$ and whose one plate is the exterior of the open disk
of radius $R$.

@include{lean:JJMath.Quasiconformal.planarRingCapacity}

Complex-affine maps preserve planar capacity exactly. In particular,
multiplication by a nonzero complex number rescales both ring radii without
changing the capacity, so for $r>0$ the model depends only on $R/r$:

$$
  \operatorname{cap}(r,R)=\operatorname{cap}(1,R/r).
$$

@include{lean:JJMath.Quasiconformal.planarCondenserCapacity_affineMap_image}

@include{lean:JJMath.Quasiconformal.planarRingCapacity_eq_one_div}

Both smooth and locally Lipschitz real functions now enter the local Sobolev
competitor class with their classical Fréchet differentials. The locally
Lipschitz bridge is the one needed for a piecewise logarithmic radial
competitor.

@include{lean:JJMath.Quasiconformal.isLocalW12RealOn_of_locallyLipschitzOn}

For $0<r<R$, the logarithmic cutoff

$$
  u_{r,R}(z)=\min\left\{1,
    \frac{\log(\max\{r,|z|\})-\log r}{\log R-\log r}\right\}
$$

is globally locally Lipschitz, equals $0$ on the closed inner disk, and equals
$1$ outside the open outer disk. It is therefore an admissible ring
competitor.

@include{lean:JJMath.Quasiconformal.planarLogRingCompetitor}

Away from the two boundary circles its differential vanishes off the annulus,
while on $r<|z|<R$ it has norm

$$
  \lVert Du_{r,R}(z)\rVert
    =\frac{1}{(\log R-\log r)|z|}.
$$

The boundary circles have area zero, so this gives the complete
almost-everywhere energy density.

@include{lean:JJMath.Quasiconformal.norm_fderiv_planarLogRingCutoff_sq_ae}

Polar integration then yields

$$
  \mathcal E(u_{r,R})
    =\frac{2\pi}{\log R-\log r},
$$

and the variational definition gives the same expression as an upper bound
for the concentric ring capacity.

@include{lean:JJMath.Quasiconformal.planarLogRingCompetitor_dirichletEnergy}

@include{lean:JJMath.Quasiconformal.planarRingCapacity_le_logarithmicEnergy}

For the lower bound, continuity is used before choosing any ACL
representative. Pulling the continuous strip theorem through two
stereographic polar charts proves directly that, for almost every direction
$\theta$ and all $0<a<b<1$,

$$
  |u(a\theta)-u(b\theta)|
    \leq \int_a^b |Du(t\theta)\theta|\,dt.
$$

@include{lean:JJMath.Uniformization.scalarWeakSobolev_unit_ball_radial_acl_all_segments_of_continuousOn}

Moreover, the weak differential may be replaced by a measurable member of
its almost-everywhere class without changing the weak-derivative identity or
the endpoint-preserving radial estimate.

@include{lean:JJMath.Uniformization.scalarWeakSobolev_unit_ball_exists_measurable_weakDifferential_radial_acl_all_segments_of_continuousOn}

Consequently, if $0<r<R<S$ and $u$ is an arbitrary ring competitor, dilation
to the unit ball preserves the actual plate values and gives

$$
  1\leq \int_{r/S}^{R/S}|S Du(St\theta)\theta|\,dt
$$

for almost every unit direction.


The required one-dimensional estimate is also available directly in
extended nonnegative values:

$$
  \int_a^b h(t)\,dt
    \leq
  \left(\int_a^b t h(t)^2\,dt\right)^{1/2}
  (\log b-\log a)^{1/2}.
$$

@include{lean:JJMath.Quasiconformal.lintegral_le_weighted_rpow_two_mul_log}

It uses the exact reciprocal integral
$\int_a^b t^{-1}\,dt=\log b-\log a$.

@include{lean:JJMath.Quasiconformal.lintegral_ennreal_reciprocal_Ioo}

Specializing the measurable differential field to the dilated competitor and
combining these two ingredients gives, for almost every direction,

$$
  1\leq
  \left(\int_{r/S}^{R/S}
    t\,|G(t\theta)\theta|^2\,dt\right)^{1/2}
  (\log R-\log r)^{1/2}.
$$

@include{lean:JJMath.Quasiconformal.PlanarCondenserCompetitor.exists_measurable_scaledWeakDifferential_one_le_weightedRadialEnergy_ae}

The polar normalization induced by planar Lebesgue measure has total angular
mass $2\pi$, and its radial measure is exactly $t\,dt$. Squaring the raywise
estimate, using $|G(t\theta)\theta|\leq\lVert G(t\theta)\rVert$, and integrating
therefore yields the sharp unit-disk lower bound

$$
  \frac{2\pi}{\log R-\log r}
    \leq \int_{|z|<1}\lVert G(z)\rVert^2\,dz.
$$

@include{lean:JJMath.Quasiconformal.complex_toSphere_apply_univ}

@include{lean:JJMath.Quasiconformal.two_pi_mul_inv_le_lintegral_ball_of_weightedRadialEnergy_ae}

Planar Dirichlet energy is invariant under dilation: the factor $S^2$ in
$\lVert S Du(Sz)\rVert^2$ cancels the Jacobian factor $S^{-2}$. Thus the
unit-disk estimate is exactly a lower bound for the original competitor's
energy, not merely for an auxiliary measurable field.

@include{lean:JJMath.Quasiconformal.lintegral_norm_const_smul_comp_sq_restrict_ball_one}

@include{lean:JJMath.Quasiconformal.PlanarCondenserCompetitor.two_pi_mul_inv_log_sub_log_le_dirichletEnergy}

Taking the infimum over all competitors gives the lower capacity bound. It
matches the energy of the logarithmic cutoff, so the model computation is now
complete:

$$
  \operatorname{cap}(r,R)=\frac{2\pi}{\log R-\log r}
  \qquad (0<r<R).
$$

@include{lean:JJMath.Quasiconformal.planarRingCapacity_eq_logarithmicEnergy}

For pullback through a merely Sobolev map, it is useful to smooth the two
corners of the logarithmic profile in its value variable. Let
$\vartheta:\mathbb R\to[0,1]$ be the standard smooth transition and put

$$
  \widetilde u_{r,R}(z)=\vartheta(u_{r,R}(z)),
  \qquad
  \widetilde u_{w;r,R}(y)=\widetilde u_{r,R}(y-w).
$$

Although the raw logarithmic cutoff is not smooth on the two boundary
circles, the transition is constant to infinite order outside $(0,1)$.
Hence $\widetilde u_{w;r,R}$ is globally smooth, vanishes on
$\overline B(w,r)$, and equals one outside $B(w,R)$.

@include{lean:JJMath.Quasiconformal.planarSmoothLogRingCutoff}

@include{lean:JJMath.Quasiconformal.planarSmoothLogRingCutoffAt}

The tail $\widetilde u_{w;r,R}-1$ is smooth and compactly supported.
Consequently, if $f$ is locally $W^{1,2}$, the composition
$\widetilde u_{w;r,R}\circ f$ is locally $W^{1,2}$ and

$$
  D(\widetilde u_{w;r,R}\circ f)(x)
    =D\widetilde u_{w;r,R}(f(x))\circ Df(x).
$$

@include{lean:JJMath.Quasiconformal.IsLocalW12On.postcomp_planarSmoothLogRingCutoffAt}

The derivative of $\vartheta$ has a fixed finite bound $C$. The smooth cutoff
therefore retains the logarithmic energy decay

$$
  \int_{\mathbb C}\|D\widetilde u_{w;r,R}(y)\|^2\,dy
    \leq
  C^2\frac{2\pi}{\log R-\log r}.
$$

@include{lean:JJMath.Quasiconformal.exists_smoothTransition_fderiv_norm_bound}

@include{lean:JJMath.Quasiconformal.lintegral_norm_fderiv_planarSmoothLogRingCutoffAt_sq_le}

## Normalized continuum separation

A sphere homeomorphism is normalized when it fixes $0$, $1$, and $\infty$.
Fixing infinity makes its finite-to-finite chart representation a genuine
homeomorphism of the whole complex plane, and normalization makes that planar
homeomorphism fix $0$ and $1$.

@include{lean:JJMath.Quasiconformal.IsNormalizedRiemannSphereHomeomorph}

@include{lean:JJMath.Quasiconformal.riemannSphereFiniteChartHomeomorph}

@include{lean:JJMath.Quasiconformal.IsNormalizedRiemannSphereHomeomorph.finiteChart_fixes_zero_one}

Use the positive real ray $[1,\infty)$ as the outer plate. It is closed and
connected, contains $1$, and is unbounded. A whole-plane homeomorphism
preserves unboundedness because the inverse image of every closed disk is
compact. Thus a normalized image of this ray has the same four properties.

@include{lean:JJMath.Quasiconformal.planarUnitRay_properties}

@include{lean:JJMath.Quasiconformal.Homeomorph.image_unbounded}

@include{lean:JJMath.Quasiconformal.IsNormalizedRiemannSphereHomeomorph.finiteChart_image_planarUnitRay_properties}

The geometric input is the planar Grötzsch--Loewner estimate.
For every $\delta>0$ there is $c(\delta)>0$ such that

$$
  c(\delta)\leq\operatorname{cap}_{\mathbb C}(E_0,E_1)
$$

whenever $E_0$ is compact and connected, contains $0$, and reaches modulus
$\delta$, while $E_1$ is closed and connected, contains $1$, and is
unbounded. This comparison for arbitrary continua is not a formal consequence
of the concentric-ring computation; it is proved directly by a circle-and-ray
length--area argument.

The topological part of that length--area proof is elementary but important:
the modulus maps a connected set to an interval. Thus a connected set with
points on both sides of the circle $|z|=r$ must meet that circle.

@include{lean:JJMath.Quasiconformal.IsConnected.exists_mem_norm_eq_of_norm_le}

In particular, the inner continuum meets every circle through radius
$\delta$, and the outer continuum meets every circle of radius at least one.
Set

$$
  d=\min\{\delta/2,1/4\}.
$$

Then $d>0$, $2d\leq\delta$, and $2d\leq1/2$.

@include{lean:JJMath.Quasiconformal.normalizedContinuumInnerRadius_bounds}

For an admissible competitor with total energy $E$, polar averaging on the
annuli $d<|z|<2d$ and $1<|z|<2$ selects circles of radii $a$ and $b$ whose
angular squared energies are at most $E/\log2$. On an ACL circle,
Cauchy--Schwarz bounds the diameter of the image by the square root of its
squared derivative energy times the square root of the parameter length.


The analytic coordinate swap needed to produce those angular ACL curves is
now formalized. The scalar weak differential first pulls through the
stereographic polar chart and then through the volume-preserving map which
reorders the real angular coordinate before the radius. Thus the pulled-back
function has its explicit weak differential on
$\{(t,r):0<r<1\}$.

@include{lean:JJMath.Quasiconformal.scalarWeakSobolev_stereographic_polar_angularCoordinates_pullback_weakDerivative}

On every compact sub-band of this cylinder, continuity and local
integrability also pull back.  The compact-strip ACL theorem therefore gives
absolute continuity, with the exact angular derivative, on every protected
angular segment for almost every radius.


The angular source coordinate may be translated without changing the radial
cylinder or losing the weak derivative.

@include{lean:JJMath.Quasiconformal.scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_acl_on_translated_compact}

Taking a countable intersection gives these ACL statements simultaneously on
the compact intervals $[n/2,n/2+3/4]$ for almost every radius in a protected
radial band.

@include{lean:JJMath.Quasiconformal.scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_acl_on_countable_cover}

These intervals cover the real stereographic line and consecutive intervals
overlap. The corresponding endpoint estimates can be specialized to the
half-integer partition. Finite induction joins its edges without overlapping
their derivative integrals, while the floor cells of the two endpoints add
the two remaining partial intervals. Consequently, for almost every protected
radius and all $s\leq t$,

$$
  |u(r\sigma_v(s))-u(r\sigma_v(t))|
    \leq\int_s^t
      |Du(r\sigma_v(x))(r\sigma_v'(x))|\,dx.
$$


@include{lean:JJMath.Quasiconformal.scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_global_endpoint_bound}

The stereographic metric factor is now explicit.  If $\sigma_v(t)$ is the
inverse-stereographic parametrization of the unit circle with pole $v$, then
$\|\sigma_v'(t)\|=4/(t^2+4)$.  At radius $r$, the angular vector of the full
polar chart is therefore $r\sigma_v'(t)$.

@include{lean:JJMath.Quasiconformal.norm_stereographicUnitCircleParamDerivative}

@include{lean:JJMath.Quasiconformal.stereographicPolarPatchMap_angular_fderiv}

In particular, the angular value of the pulled-back weak differential is
exactly $Du(r\sigma_v(t))(r\sigma_v'(t))$, and its norm is at most
$\|Du(r\sigma_v(t))\|4r/(t^2+4)$.

@include{lean:JJMath.Quasiconformal.stereographicPolarAngularWeakDifferential_apply}


The map $T_v(t+ir)=r\sigma_v(t)$ is injective for $0<r<1$, and its absolute
Jacobian is $4r/(t^2+4)$.  The classical area formula therefore gives the
weighted change of variables directly; no separate identification of the
omitted pole ray is needed for the energy upper bound.

@include{lean:JJMath.Quasiconformal.injOn_stereographicPolarAngularComplexMap_positiveUnitRadius}

@include{lean:JJMath.Quasiconformal.abs_weakJacobian_fderiv_stereographicPolarAngularComplexMap}

@include{lean:JJMath.Quasiconformal.lintegral_image_stereographicPolarAngularComplexMap}

After squaring the pointwise covector estimate and dividing by the positive
angular metric factor, the area formula bounds the complete weighted angular
energy by the $L^2$ energy of $Du$ on the unit disk.

@include{lean:JJMath.Quasiconformal.stereographicPolarAngularWeakDerivativeValue_weighted_sq_le}

@include{lean:JJMath.Quasiconformal.lintegral_stereographicPolarAngularWeakDerivativeValue_weighted_le}

The polar map also preserves null sets from the complex strip into the unit
disk. Thus the almost everywhere measurable representative supplied by
$Du\in L^2(B(0,1))$ pulls back legitimately. A volume-preserving swap to
radius-first coordinates and Tonelli now give the exact iterated estimate
$$
  \int_0^1\int_{\mathbb R}
    |Du(r\sigma_v(t))(r\sigma_v'(t))|^2
    \frac{t^2+4}{4r}\,dt\,dr
    \leq \int_{B(0,1)}\|Du(y)\|^2\,dy.
$$

@include{lean:JJMath.Quasiconformal.stereographicPolarAngularComplexMap_quasiMeasurePreserving}

@include{lean:JJMath.Quasiconformal.lintegral_radius_stereographicPolarAngularWeakDerivativeValue_weighted_le}

In particular, the weighted angular energy is finite on almost every radius.

@include{lean:JJMath.Quasiconformal.ae_lintegral_stereographicPolarAngularWeakDerivativeValue_weighted_lt_top}

The reciprocal stereographic metric factor has the exact total mass

$$
  \int_{\mathbb R}\frac{4r}{t^2+4}\,dt=2\pi r.
$$

@include{lean:JJMath.Quasiconformal.lintegral_stereographicAngularReciprocalWeight}

The extended-valued weighted Cauchy--Schwarz inequality needed to pair this
factor with the weighted angular energy is available for every almost
everywhere positive finite measurable weight.

@include{lean:JJMath.Quasiconformal.lintegral_le_weighted_rpow_two_mul_inv}

The norm of the angular weak derivative is measurable on almost every
radius. Weighted Cauchy--Schwarz therefore turns the global finite-parameter
endpoint estimate into

$$
  |u(r\sigma_v(s))-u(r\sigma_v(t))|
    \leq E_v(r)^{1/2}(2\pi r)^{1/2}.
$$

@include{lean:JJMath.Quasiconformal.ae_aemeasurable_stereographicPolarAngularWeakDerivativeNorm}

@include{lean:JJMath.Quasiconformal.lintegral_stereographicPolarAngularWeakDerivativeNorm_le_weightedEnergy}

@include{lean:JJMath.Quasiconformal.scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_global_endpoint_bound_weightedEnergy}

The inverse-stereographic curve converges to its omitted pole. Continuity of
$u$ extends the same estimate across that pole, and the stereographic line
together with its pole covers $S^1$. Thus for almost every protected radius
and all $\theta,\eta\in S^1$,

$$
  |u(r\theta)-u(r\eta)|
    \leq E_v(r)^{1/2}(2\pi r)^{1/2}.
$$

@include{lean:JJMath.Quasiconformal.tendsto_stereographicUnitCircleParam_atTop}

@include{lean:JJMath.Quasiconformal.angular_sphere_bound_of_continuousOn}

@include{lean:JJMath.Quasiconformal.scalarWeakSobolev_ae_stereographic_circle_oscillation_le_weightedEnergy}

The circle energy itself is almost everywhere measurable as a function of
the radius. A first-moment argument can therefore choose a radius in every
protected interval $(a,b)$ which retains the full-circle theorem and has
energy no larger than the annular average. In particular,

$$
  E_v(r)\leq\frac1{b-a}\int_{B(0,1)}\|Du(y)\|^2\,dy
$$

for some $r\in(a,b)$.

@include{lean:JJMath.Quasiconformal.aemeasurable_lintegral_stereographicPolarAngularWeakDerivativeValue_weighted}

@include{lean:JJMath.Quasiconformal.exists_good_radius_le_average}

@include{lean:JJMath.Quasiconformal.exists_stereographic_circle_energy_le_average}

Under a dilation $z\mapsto Sz$, the pulled-back covector field is
$D_S(z)=S Du(Sz)$. Its angular value at radius $q$ is the original angular
value at radius $Sq$, and the weighted circle energy obeys

$$
  E_v(D_S,q)=S E_v(D,Sq).
$$

The interval length scales by $S^{-1}$ while planar Dirichlet energy is
invariant. Thus the selector transports with no loss to a physical ball:
for $0<a<b<S$, some $r\in(a,b)$ satisfies

$$
  E_v(r)\leq\frac1{b-a}\int_{B(0,S)}\|Du(y)\|^2\,dy.
$$

@include{lean:JJMath.Quasiconformal.stereographicPolarAngularWeakDerivativeValue_const_smul_comp}

@include{lean:JJMath.Quasiconformal.lintegral_stereographicPolarAngularWeakDerivativeValue_const_smul_comp}

@include{lean:JJMath.Quasiconformal.exists_stereographic_circle_energy_le_average_on_ball}

For $0<d\leq1/4$, applying the physical selector on $(d,2d)$ and $(1,2)$
produces both circles needed by the separation argument. In either case the
interval-length denominator cancels the maximum circumference, giving the
common full-circle bound

$$
  |u(r\theta)-u(r\eta)|
    \leq
  \left(\int_{B(0,3)}\|Du\|^2\right)^{1/2}(4\pi)^{1/2}.
$$

@include{lean:JJMath.Quasiconformal.circle_oscillation_factor_le_of_radius_le_two_mul}

@include{lean:JJMath.Quasiconformal.exists_inner_outer_good_circles}

Because the two selected circles meet the corresponding plates, this bounds
$|u(a\theta)|$ and $|1-u(b\theta)|$ for every direction $\theta$. A second
polar averaging selects one radial ACL ray and proves

$$
  |u(a\theta)-u(b\theta)|
    \leq
  \left(\frac{E}{2\pi}\right)^{1/2}
  (\log b-\log a)^{1/2}.
$$

@include{lean:JJMath.Quasiconformal.exists_radial_segment_oscillation_le_average_energy}

Since $a>d$ and $b<2$, the logarithmic factor is at most
$\log 2-\log d$. The triangle inequality therefore gives
$1\leq C(\delta)E^{1/2}$ for an explicit positive finite $C(\delta)$, and
the square-root cancellation yields $C(\delta)^{-2}\leq E$.

@include{lean:JJMath.Quasiconformal.inv_sq_le_of_one_le_rpow_half_mul}

Taking the infimum over all competitors completes the continuum-separation
theorem.

@include{lean:JJMath.Quasiconformal.exists_pos_le_planarCondenserCapacity_of_normalized_continua}

In particular the normalized conclusion has a coordinate-free whole-plane
form. If $E_0$ is a compact nontrivial continuum and $E_1$ is a disjoint
closed connected unbounded set, choose distinct points of $E_0$ and one
point of $E_1$. A complex-affine change of coordinates sends the first
chosen point to $0$ and the point of $E_1$ to $1$; the second point of
$E_0$ supplies the positive normalization radius. Affine invariance then
returns the strictly positive capacity to the original plates.

@include{lean:JJMath.Quasiconformal.planarCondenserCapacity_pos_of_compact_nontrivial_continuum_of_unbounded_continuum}

All subsequent capacity bookkeeping is now formalized. The image of a closed
disk supplies the inner continuum. The source ray condenser has capacity at
most the round-ring capacity because $[1,\infty)$ lies outside the open unit
disk. Quasiconformal capacity distortion therefore bounds the normalized
image condenser from above by $K\operatorname{cap}(r,1)$.

@include{lean:JJMath.Quasiconformal.IsNormalizedRiemannSphereHomeomorph.finiteChart_image_closedBall_properties}

@include{lean:JJMath.Quasiconformal.planarCondenserCapacity_closedBall_planarUnitRay_le_planarRingCapacity}

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalRiemannSphere.finiteChart_image_closedBall_planarUnitRay_capacity_le}

Consequently, if the image of the closed $r$-disk reaches modulus $\delta$,
the same condenser is squeezed between

$$
  c(\delta)
  \leq \operatorname{cap}_{\mathbb C}
    \bigl(f(\overline B(0,r)),f([1,\infty))\bigr)
  \leq K\operatorname{cap}(r,1).
$$

@include{lean:JJMath.Quasiconformal.exists_pos_le_ofReal_mul_planarRingCapacity_of_finiteChart_image_closedBall_reaches}

At exponentially small radii the exact ring formula becomes

$$
  \operatorname{cap}(e^{-n},1)=\frac{2\pi}{n}\longrightarrow0.
$$

@include{lean:JJMath.Quasiconformal.tendsto_planarRingCapacity_exp_neg_nat}

Choosing $n$ so that $K\operatorname{cap}(e^{-n},1)<c(\delta)$ rules out an
image point of modulus at least $\delta$. This proves uniform finite-chart
equicontinuity at $0$ for the normalized $K$-quasiconformal family.

@include{lean:JJMath.Quasiconformal.exists_radius_finiteChart_norm_lt_of_norm_le}

## From the finite chart to spherical equicontinuity

The one-point compactification initially carries only its topology. Choose a
compatible metric by identifying it homeomorphically with the Euclidean unit
sphere $S^2\subset\mathbb R^3$ and pulling back Euclidean distance. The chosen
homeomorphism is then an isometry by construction.

@include{lean:JJMath.Quasiconformal.riemannSphereEquivUnitSphere}


Continuity and openness of the finite-point inclusion
$\mathbb C\hookrightarrow\widehat{\mathbb C}$ convert the uniform
finite-chart estimate into the intrinsic statement: every indexed family of
normalized $K$-quasiconformal sphere homeomorphisms is equicontinuous at the
spherical point $0$.

@include{lean:JJMath.Quasiconformal.equicontinuousAt_zero_normalizedKQuasiconformalRiemannSphere}

Inversion is already compatible with this chartwise definition. Reversing
the source and target standard charts turns the coordinate representation of
$F^{-1}$ into the inverse of the representation of $F$.

@include{lean:JJMath.Quasiconformal.riemannSphereChartRepresentation_symm}

The planar inverse theorem therefore lifts without loss of the distortion
constant, while the three marked points remain fixed.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalRiemannSphere.symm}

@include{lean:JJMath.Quasiconformal.IsNormalizedRiemannSphereHomeomorph.symm}

Applying the origin theorem to the inverse family gives the corresponding
two-sided control needed later to identify uniform limits as mutually inverse
homeomorphisms.

@include{lean:JJMath.Quasiconformal.equicontinuousAt_zero_symm_normalizedKQuasiconformalRiemannSphere}

## Exchanging zero and one

No new separation theorem is needed at the second finite normalization
point. For the finite-chart map $f$, conjugate by the affine involution
$T(z)=1-z$ and write $g=T\circ f\circ T$, so that
$g(w)=1-f(1-w)$. The map $g$ fixes $0$ and $1$, and
$$
  |w|=|z-1|,
  \qquad
  |g(w)|=|f(z)-1|
  \quad\text{when }w=1-z.
$$
This is exactly the origin estimate in changed coordinates. Formally, the
proof transports the capacity hypothesis needed by the generic origin
modulus: $T$ sends $\overline B(0,r)$ to $\overline B(1,r)$ and sends
$[1,\infty)$ to $(-\infty,0]$. Exact affine invariance identifies the
postcomposed image condenser, while quasiconformal capacity distortion for
$f$ and the transported round-ring comparison give the required upper bound
for $g$.




Applying the already proved origin modulus to $g$ and conjugating back gives
the finite-chart modulus at $1$ with no second continuum-separation argument.


The finite-point inclusion then upgrades the estimate to spherical
equicontinuity. Applying it to the already established quasiconformal inverse
family gives two-sided control at $1$.



## Reciprocal coordinates at infinity

The third normalization point requires no new continuum estimate either.
Reciprocal coordinates send $\infty$ to $0$ and leave $1$ fixed. Because a
normalized sphere homeomorphism also fixes the omitted spherical point $0$,
its reciprocal-to-reciprocal chart representation has source and target all
of $\mathbb C$ and is therefore a whole-plane homeomorphism.

@include{lean:JJMath.Quasiconformal.riemannSphereInfinityChartHomeomorph}

Normalization says that this whole-plane representative fixes $0$ and $1$.
The chartwise quasiconformal capacity inequality becomes the same normalized
condenser upper bound used at the original point $0$.

@include{lean:JJMath.Quasiconformal.IsNormalizedRiemannSphereHomeomorph.infinityChart_fixes_zero_one}

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalRiemannSphere.infinityChart_image_condenser_capacity_le}

Thus the generic origin modulus applies directly to the reciprocal-chart
representative: small reciprocal coordinate has uniformly small image
reciprocal coordinate.

@include{lean:JJMath.Quasiconformal.exists_radius_infinityChart_norm_lt_of_norm_le}

The inverse reciprocal chart sends a small Euclidean disk around $0$ to a
spherical neighborhood of $\infty$. Its continuity and openness upgrade the
coordinate estimate to spherical equicontinuity at $\infty$. Applying the
same theorem to the normalized quasiconformal inverse family gives the
two-sided statement.

@include{lean:JJMath.Quasiconformal.equicontinuousAt_infty_normalizedKQuasiconformalRiemannSphere}

@include{lean:JJMath.Quasiconformal.equicontinuousAt_infty_symm_normalizedKQuasiconformalRiemannSphere}

The inverse estimate already supplies the first ingredient for moving away
from the marked points. For a fixed $x\ne0$, reciprocal coordinates satisfy

$$
  g_{F^{-1}}\bigl(f_F(x)^{-1}\bigr)=x^{-1}.
$$

Hence $f_F(x)^{-1}$ cannot enter one fixed reciprocal disk about $0$, and the
finite coordinates $f_F(x)$ remain uniformly bounded throughout the
normalized family.

@include{lean:JJMath.Quasiconformal.exists_uniform_finiteChart_norm_bound_at}

## Recentering at arbitrary finite points

Fix a finite point $x\ne0$ and write

$$
  B_x(z)=x(1-z).
$$

This affine map sends the normalized pair $(0,1)$ to $(x,0)$. If $f$ is a
normalized finite-chart representative, then $f(x)\ne0$, and the doubly
recentered homeomorphism

$$
  G_{f,x}=B_{f(x)}^{-1}\circ f\circ B_x
$$

again fixes $0$ and $1$. The source disk and ray become a disk centered at
$x$ and the ray from $x$ through $0$; the target affine change normalizes
their images. Exact affine invariance on both sides therefore gives the same
round-ring capacity bound as at the original marked point.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalRiemannSphere.recenteredFiniteChart_image_capacity_le}

The origin modulus now applies to $G_{f,x}$. The uniform bound for $|f(x)|$
converts its normalized target estimate back into an absolute estimate for
$|f(z)-f(x)|$.

@include{lean:JJMath.Quasiconformal.exists_radius_finiteChart_norm_sub_lt_at}

The values $f(x)$ lie in one compact Euclidean disk. On a slightly larger
disk the finite-point inclusion into the sphere is uniformly continuous by
Heine--Cantor, so finite-coordinate control yields spherical equicontinuity
at every nonzero finite point.

@include{lean:JJMath.Quasiconformal.equicontinuousAt_finite_normalizedKQuasiconformalRiemannSphere}

Together with the already proved estimates at $0$ and $\infty$, this gives
equicontinuity everywhere. Compactness of the sphere upgrades it to uniform
equicontinuity. The same conclusions hold for the inverse family.

@include{lean:JJMath.Quasiconformal.equicontinuous_normalizedKQuasiconformalRiemannSphere}

@include{lean:JJMath.Quasiconformal.equicontinuous_symm_normalizedKQuasiconformalRiemannSphere}

@include{lean:JJMath.Quasiconformal.uniformEquicontinuous_normalizedKQuasiconformalRiemannSphere}

@include{lean:JJMath.Quasiconformal.uniformEquicontinuous_symm_normalizedKQuasiconformalRiemannSphere}

## Topological compactness

Arzelà--Ascoli first extracts a uniformly convergent subsequence of the maps
and then a further uniformly convergent subsequence of their inverses.
Passing the identities

$$
  F_n\circ F_n^{-1}=\operatorname{id},
  \qquad
  F_n^{-1}\circ F_n=\operatorname{id}
$$

to the limit shows that the two continuous limits are inverse
homeomorphisms. Their values at $0$, $1$, and $\infty$ remain fixed.

@include{lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_topological_compactness}

This is exactly the topological part of normalized quasiconformal
compactness. It does not yet say that the limiting homeomorphism is
$K$-quasiconformal. That remaining assertion is the analytic weak-closure
problem for the distortion inequality.

## Local energy bounds

The first analytic compactness input is already available without introducing
an intrinsic spherical Dirichlet energy. If $f:\Omega\to\Omega'$ is
$K$-quasiconformal with weak differential $Df$, then the distortion inequality
and the oriented area formula give, for every measurable $E\subseteq\Omega$,

$$
  \int_E \lVert Df(z)\rVert_{\mathrm{op}}^2\,dz
    \leq K\,|f(E)|.
$$

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.lintegral_norm_weakDifferential_sq_le_volume_image}

For a normalized sphere family, reciprocal control of the inverse maps gives
a common Euclidean bound for the finite-chart image of every fixed source
disk.

@include{lean:JJMath.Quasiconformal.exists_uniform_finiteChart_norm_bound_on_closedBall}

The image area in the preceding inequality is therefore bounded by the area
of one fixed target disk. Consequently, on every fixed finite-chart disk the
weak differentials of the whole normalized family have one finite uniform
$L^2$ bound.

@include{lean:JJMath.Quasiconformal.exists_uniform_finiteChart_weakDifferential_energy_bound}

On one fixed disk, evaluation at the coordinate vectors $1$ and $i$ is bounded
by the operator norm. Applying Hilbert-space weak compactness successively to
the fields $DF_n(1)$ and $DF_n(i)$ therefore produces a single subsequence on
which both fields converge weakly in $L^2$.

@include{lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_fixedDisk_weakDifferential_subsequence}

A single diagonal extraction now works simultaneously on all integer-radius
disks. The resulting coordinate limits agree under restriction from a larger
disk to a smaller one.

@include{lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_diskExhaustion_weakDifferential_subsequence}

Spherical uniform convergence and the uniform Euclidean image bound imply
strong local $L^2$ convergence of the finite-chart values.

@include{lean:JJMath.Quasiconformal.finiteChart_toLp_tendsto_of_tendstoUniformly}

Weak convergence of the two differential coordinates and strong convergence
of the values pass the distributional test-function identity to the limit.

@include{lean:JJMath.Quasiconformal.isWeakDerivativeOnEuclideanRegionWithValues_of_weak_tendsto_coordinates}

The compatible diskwise fields glue to one whole-plane weak differential.
Consequently the finite chart of the limiting normalized homeomorphism lies
in $W^{1,2}_{\mathrm{loc}}$.

@include{lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_localW12_compactness}

The stronger compactness interface retains the two weak coordinate limits on
every disk and identifies the limiting differential with their real-linear
reconstruction. This is the data needed to pass a differential equation
through the same diagonal subsequence.

@include{lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_localW12_compactness_with_diskwise_weakDifferential_of_isLocalW12On}

For prescribed coefficients, analytic closure is now complete even when the
coefficients vary. The two Wirtinger derivatives are bounded real-linear
combinations of the weakly convergent coordinate fields. If
$\mu_n\to\mu$ almost everywhere with one common essential bound, dominated
convergence makes multiplication by $\mu_n$ converge strongly on each fixed
$L^2$ test field. Duality therefore passes
$\partial_{\bar z}f_n=\mu_n\partial_zf_n$ to the reconstructed weak limit.

@include{lean:JJMath.Quasiconformal.weakBeltramiEquationOn_of_ae_tendsto_of_weak_tendsto_coordinateValues}

The integer-disk exhaustion packages this with uniform convergence of the
maps and inverses. The finite-chart limit lies locally in $W^{1,2}$ and
satisfies the limiting equation on all of $\mathbb C$.

@include{lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_compactness_of_isLocalW12On}

To control infinity, conjugate the subsequence by spherical inversion. The
coefficient becomes

$$
  \mu_\infty(z)=\mu(z^{-1})
    \frac{\overline{-z^{-2}}}{-z^{-2}}.
$$

Measurability, the essential bound, and almost-everywhere coefficient
convergence survive this pullback. Applying finite-chart compactness a second
time gives reciprocal-chart Sobolev data for the same spherical limit.

@include{lean:JJMath.Quasiconformal.AEStronglyMeasurable.inversionPullbackBeltrami}

@include{lean:JJMath.Quasiconformal.ae_tendsto_inversionPullbackBeltrami}

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalRiemannSphere.exists_invConjugate_finiteChart_weakDifferential_weakBeltrami}

@include{lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_twoChart_compactness_of_isLocalW12On}

Orientation preservation is closed under compact-local uniform convergence
of planar homeomorphisms. Thus the bounded Beltrami equation with
$|\mu|\leq k<1$ makes both diagonal standard charts
$((1+k)/(1-k))$-quasiconformal. The mixed charts are the punctured finite
chart preceded or followed by conformal inversion, so the same constant
holds there as well.

@include{lean:JJMath.Quasiconformal.preservesPlanarOrientation_of_compactly_tendstoUniformly}

@include{lean:JJMath.Quasiconformal.isKQuasiconformalRiemannSphere_of_finiteChart_and_invConjugate_finiteChart}

These finite- and reciprocal-chart results form the planar implementation
engine. The public compactness theorem packages them intrinsically:
almost-everywhere convergence of uniformly bounded spherical Beltrami
differentials gives a normalized quasiconformal sphere limit, with uniform
convergence of the maps and inverses and realization of the limiting
differential.

@include{lean:JJMath.Quasiconformal.normalizedRiemannSphere_beltramiDifferential_compactness}

General coefficient-free weak closure of the nonlinear finite-distortion
inequality remains useful, but it is not needed for the measurable Riemann
mapping construction.
