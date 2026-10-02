import Green41SingleExponential.DigitCover
import Green41SingleExponential.DigitRotation
import Green41SingleExponential.StepAFamily
import Green41SingleExponential.MinorArcDigit
import Green41SingleExponential.KL57Digit
import Green41SingleExponential.AssemblyDigit
import Green41SingleExponential.FinalSingle

/-!
# A single-exponential bound for Green's Problem 41

`Green41Proof.green_41_single_exponential_bound_solved`: `minCopies ε ≤ exp(ε^(-201))` for
`0 < ε ≤ 1/400000`. The double-exponential development `Green41DoubleExponentialFC` is reused
unchanged; Step A replaces the cyclic orbit of `ρ/ρ̄` by base-`p` digit rotations
`(1 + p^k i)/(1 - p^k i)`.
-/
