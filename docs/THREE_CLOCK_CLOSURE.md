# Three-clock formal closure

This milestone adds three non-duplicative interfaces on top of the current `entropic-physlib-linear-full` base:

1. `FiniteConditioningCertificate` records an exact Page--Wootters conditioning equality for a physical history state.
2. `modularFlow_ne_entropicFlow` proves that entropy-preserving modular flow and strict entropy-producing flow cannot coincide at positive clock reading.
3. `ThreeClockCalibration` composes Page--Wootters, modular, and entropic parameter equivalences and proves exact roundtrip, injectivity, and surjectivity.

## Boundaries

The conditioning equality remains a consumer-supplied theorem field: this module does not derive a tensor split or clock POVM from the abstract Hamiltonian constraint. The calibration equivalences are explicit assumptions; the module proves their composition properties and excludes collapse of distinct readings.
