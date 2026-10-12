import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PositiveIntertwinerHarmonicIntegrals

/-!
# Probe: the island sees the AxiomMath library

Checks that the pinned dependency resolves and that the PGL2(ℂ) intertwiner positivity at ν = 1/3
(`positive_intertwiner_harmonic_integral`) is available. conjecture1_proved = False.
-/

open DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum in
#check @positive_intertwiner_harmonic_integral
