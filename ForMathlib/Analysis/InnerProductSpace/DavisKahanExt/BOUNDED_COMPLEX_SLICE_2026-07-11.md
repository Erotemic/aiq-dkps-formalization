# Bounded spectral slice — 2026-07-11

The completed theorem chain has been promoted out of `DavisKahanExt`.

## Scalar-generic core

1. `DavisKahan.norm_sylvester_le_of_coercive`;
2. `DavisKahan.sinTheta_directed_coercive`;
3. `Submodule.norm_starProjection_sub_eq_max`;
4. `DavisKahan.opNorm_starProjection_sub_le_of_coercive`;
5. `DavisKahan.opNorm_starProjection_sub_le_of_formBounds`.

These results work over arbitrary `RCLike` scalars.

## Complex spectral specialization

`SpectralOrder.Complex` converts spectra of actual restricted operators into
quadratic-form bounds.  The leaf theorem

`DavisKahan.Spectral.Complex.opNorm_starProjection_sub_le_of_restriction_spectra`

then applies the generic factor-one projector estimate.

## Real spectral target

The generic perturbation theorem already covers real Hilbert spaces once the
form bounds are supplied.  The missing conversion from real spectra is tracked
in `DavisKahan/Experimental/Foundation/RealSpectralBridge.lean`, with direct
Rayleigh-shift and complexification routes documented separately.
