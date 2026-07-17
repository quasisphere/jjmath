# Subharmonic Functions

This note collects the harmonic and subharmonic background used by Perron's
method.  The main point is to keep the circle-mean machinery and the comparison
principle separate from the Perron envelope construction.

## Surface Harmonicity

Harmonicity is checked in complex coordinates, and the basic closure and
maximum-principle facts are proved at the surface level.

@include{lean:JJMath.Uniformization.IsHarmonicOnSurface}

@include{lean:JJMath.Uniformization.harmonicOnSurface_continuousOn}

@include{lean:JJMath.Uniformization.harmonicOnSurface_eqOn_of_isPreconnected_of_isMaxOn}

@include{lean:JJMath.Uniformization.harmonic_nonpositive_of_boundary_nonpositive_componentwise}

## Circle Means

On plane coordinate patches, subharmonicity can be phrased using circle means.
For upper semicontinuous traces, the circle average is expressed as
\(M-\fint(M-u)\), so the value is an extended real number and no ordinary
integrability of the trace is assumed in advance.

@include{lean:JJMath.Uniformization.upperCircleAverageERealWithBound}

@include{lean:JJMath.Uniformization.upperCircleAverageERealWithBound_eq_of_bounds}

@include{lean:JJMath.Uniformization.upperCircleAverageERealWithBound_eq_real_circleAverage}

@include{lean:JJMath.Uniformization.harmonicOnNhd_upperCircleAverageERealWithBound_eq}

@include{lean:JJMath.Uniformization.IsSubharmonicByExtendedCircleAverageOn}

@include{lean:JJMath.Uniformization.subharmonicByExtendedCircleAverageOn_add}

The compact-circle approximation starts from the fact that
[upper semicontinuous functions are infima of countably many continuous
majorants](lean:JJMath.Uniformization.upperSemicontinuousOn_compact_exists_countable_continuous_majorants).
Truncating finite infima gives that
[upper semicontinuous functions are decreasing limits of continuous
majorants](lean:JJMath.Uniformization.upperSemicontinuousOn_compact_exists_antitone_continuous_bounded_majorants).
This is the theorem cited from Bourbaki, *General Topology*, Chapter IX, §1,
and also in Ransford's *Potential Theory in the Complex Plane*, Theorem 2.1.3.
With the majorants bounded above by \(M\),
[their averages converge to the extended circle
average](lean:JJMath.Uniformization.tendsto_circleAverage_of_antitone_continuous_bounded_majorants).
This gives the continuous-majorant envelope formula for extended circle
averages.

@include{lean:JJMath.Uniformization.upperSemicontinuousOn_compact_exists_countable_continuous_majorants}

@include{lean:JJMath.Uniformization.upperSemicontinuousOn_compact_exists_antitone_continuous_bounded_majorants}

@include{lean:JJMath.Uniformization.upperCircleAverageERealWithBound_le_sInf_continuous_majorants}

@include{lean:JJMath.Uniformization.exists_continuous_majorant_circleAverage_lt_of_upperCircleAverage_lt}

@include{lean:JJMath.Uniformization.upperCircleAverageERealWithBound_eq_sInf_continuous_majorants}

## Comparison

The plane comparison principle and the extended circle-mean formulation are
equivalent on open plane domains.

@include{lean:JJMath.Uniformization.IsSubharmonicByPlaneComparisonOn}

@include{lean:JJMath.Uniformization.planeComparisonSubharmonic_le_upperCircleAverageERealWithBound}

@include{lean:JJMath.Uniformization.subharmonicByPlaneComparisonOn_iff_extendedCircleAverageOn}

@include{lean:JJMath.Uniformization.subharmonicByPlaneComparisonOn_add}

## Surface Subharmonicity

Surface subharmonicity is defined by upper semicontinuity plus harmonic
comparison on relatively compact test regions.  Superharmonicity is the dual
notion.

@include{lean:JJMath.Uniformization.IsSubharmonicOnSurface}

@include{lean:JJMath.Uniformization.subharmonicOnSurface_mono}

@include{lean:JJMath.Uniformization.harmonicOnSurface_openSubtype_univ_of_ambient}

@include{lean:JJMath.Uniformization.subharmonicOnSurface_openSubtype_univ_of_ambient}

@include{lean:JJMath.Uniformization.subharmonicOnSurface_add}

@include{lean:JJMath.Uniformization.subharmonicOnSurface_sup}

@include{lean:JJMath.Uniformization.subharmonicOnSurface_of_locally}

@include{lean:JJMath.Uniformization.IsSuperharmonicOnSurface}

@include{lean:JJMath.Uniformization.superharmonicOnSurface_inf}

@include{lean:JJMath.Uniformization.superharmonicOnSurface_of_locally}
