import Green41QuasiPolynomial.DiscreteGen
import Green41QuasiPolynomial.CellGen
import Green41QuasiPolynomial.DigitCast
import Green41QuasiPolynomial.MinorArcQuasi
import Green41QuasiPolynomial.AssemblyGen
import Green41QuasiPolynomial.KL57Quasi
import Green41QuasiPolynomial.FinalQuasi

/-!
# A quasi-polynomial bound for Green's Problem 41

`Green41Proof.green_41_quasi_polynomial_bound_solved`:
`minCopies ε ≤ exp((log ε⁻¹)^5)` for `0 < ε ≤ exp(-10^18)`, from the explicit
`minCopies ε ≤ exp(10^16 (log(1/ε) + 2)^4)` for `0 < ε < 1/10`.
-/
