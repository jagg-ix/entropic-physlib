# Four-clock dynamics and proper-time completion

This milestone completes three interfaces after the merged three-clock closure:

1. `ConditionedEvolutionCertificate.conditioned_evolves` transports a proved direct system-step law through exact Page--Wootters conditioning.
2. `FourClockCalibration` extends the Page--Wootters/modular/entropic chain to physical proper time and proves path commutation, roundtrip, injectivity, and surjectivity.
3. `OrderedFourClockCalibration.pwToProper_strictMono` proves that strictly monotone pairwise calibrations preserve temporal order across the full chain.

## Boundaries

The direct evolution law and exact conditioning equality remain explicit theorem fields. The pairwise calibration equivalences and their strict monotonicity are physical premises requiring independent construction or calibration. This module proves their consequences and prevents temporal collapse or order reversal once those premises are supplied.
