# Davis--Kahan supported/experimental restructure — 2026-07-11

## Design decision

The mathematical core is organized by the weakest scalar assumptions actually
needed:

1. reducing-subspace, projection-block, Sylvester, and form-bound theory is
   generic over `RCLike`;
2. the sharp directed and two-sided projector estimates are generic over
   `RCLike`;
3. conversion from actual spectra to form bounds is a separate bridge;
4. the available continuous-functional-calculus bridge is implemented for
   complex Hilbert spaces;
5. the real spectral bridge remains an explicit foundational target rather
   than being hidden behind an artificial real-spectrum definition.

## Dependency direction

```text
ReducingSubspace / QuadraticFormBounds / ProjectionBlocks / ProjectionGap
                              |
                              v
                 supported RCLike DavisKahan
                              ^
                              |
                  complex spectral-order bridge
```

`DavisKahan.Experimental` may depend on every layer above.  No supported module
may import an experimental module.

## Compatibility

The former `DavisKahanExt/<Module>.lean` paths remain available:

- `DavisKahanExt.All` now means the supported bounded development;
- `DavisKahanExt.ExperimentalAll` builds all retained foundations and
  literature targets;
- individual old module paths forward to their new experimental locations;
- old theorem names are retained where practical.

This lets the finite theory and existing agent branches migrate incrementally.

## Real case

`Experimental/Foundation/RealSpectralBridge.lean` records the exact real
restriction-spectrum statements needed by the generic projector theorem.  Two
routes remain available:

1. a direct Rayleigh/shift argument, preferred because it is narrower;
2. a reusable complexification development, retained as a broader foundation.

The complex theorem is therefore a specialization, not the definition of the
main Davis--Kahan API.
