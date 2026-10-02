import Green41QuasiPolynomial.MinorArcQuasi
import Green41QuasiPolynomial.AssemblyGen
import Green41SingleExponential.FinalSingle

/-!
# The minor-arc interface with digit rotations on both sides

With digit rotations in the discrete core, the cell generator carries the conjugate of the digit
denominator at level `ℓ`, of norm at most `p^{2p(ℓ²+1)}`, instead of `ρ̄^S` with
`S = (p - 1) p^(ℓ-1)`. The parameters become (with `c = clog_p K`, `L = 6c + 4`, `ℓ = 4L` as
before)

* `A = 2p(ℓ² + 1) + 2c + 3`, `n = 8(A + ℓ)`, `α = n - A`,

all of size `O(log² K)`. The interface `dataQ.KL` asks for `q` divisible by

* `D5Q ε  = digitDen 5 (n₅ + 4) Q · conj(digitDen 5 ℓ₅ Q)` and
* `D13Q ε = digitDen 13 (n₁₃ + 4) P · conj(digitDen 13 ℓ₁₃ P)`,

of norm `2^{O(n²)} = exp(O(log⁴ K))`, with tolerance `ηQ ε = 5^(-(A₅ + A₁₃))`.
-/

namespace Green41Proof

open Green41

open Complex ComplexConjugate Finset

/- ## Parameters -/

/-- `A = 2p(ℓ² + 1) + 2c + 3`. -/
def qA (p K : ℕ) : ℕ := 2 * p * (pℓ p K ^ 2 + 1) + 2 * pc p K + 3
/-- `n = 8(A + ℓ)`. -/
def qn (p K : ℕ) : ℕ := 8 * (qA p K + pℓ p K)
/-- `α = n - A`. -/
def qα (p K : ℕ) : ℕ := qn p K - qA p K

lemma qA_le_qn (p K : ℕ) : qA p K ≤ qn p K := by unfold qn; omega

/- ## The cell -/

lemma norm_cellGenD_sq {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (D : GaussianInt)
    (n α : ℕ) :
    ‖cellGenD π D n α‖ ^ 2 = (p : ℝ) ^ α * (D.norm : ℝ) / (p : ℝ) ^ n := by
  unfold cellGenD
  rw [norm_div, norm_mul, _root_.norm_pow, _root_.norm_pow, hπ.norm_toComplex_star_π,
    hπ.norm_toComplex_π, norm_toComplex, div_pow, mul_pow,
    sqrt_pow_sq (Nat.cast_nonneg p), sqrt_pow_sq (Nat.cast_nonneg p),
    Real.sq_sqrt (by exact_mod_cast GaussianInt.norm_nonneg D)]

/-- `‖g‖² = N(D) / p^A` when `α + A = n`. -/
lemma norm_cellGenD_sq' {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (D : GaussianInt)
    {n α A : ℕ} (hnA : α + A = n) :
    ‖cellGenD π D n α‖ ^ 2 = (D.norm : ℝ) / (p : ℝ) ^ A := by
  rw [norm_cellGenD_sq hπ, ← hnA, pow_add]
  have hp0 : (p : ℝ) ^ α ≠ 0 := pow_ne_zero _ (by exact_mod_cast hπ.prime.ne_zero)
  field_simp

lemma one_add_pow_le_pow {p j ℓ : ℕ} (hp : 2 ≤ p) (hj : j < ℓ) :
    1 + (p : ℤ) ^ (2 * j) ≤ (p : ℤ) ^ (2 * ℓ) := by
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have h1 : (1 : ℤ) ≤ (p : ℤ) ^ (2 * j) := one_le_pow₀ hp1
  have h2 : (p : ℤ) ^ (2 * j) * 2 ≤ (p : ℤ) ^ (2 * j) * p :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hp) (by positivity)
  have h3 : (p : ℤ) ^ (2 * j) * p = (p : ℤ) ^ (2 * j + 1) := by rw [pow_succ]
  have h4 : (p : ℤ) ^ (2 * j + 1) ≤ (p : ℤ) ^ (2 * ℓ) := pow_le_pow_right₀ hp1 (by omega)
  linarith

/-- The digit denominator at level `ℓ` has norm at most `p^{2p(ℓ²+1)}`. -/
lemma norm_digitDen_le_pow {p ℓ : ℕ} (hp : 2 ≤ p) {ρ : GaussianInt}
    (hρ : ρ.norm ≤ (p : ℤ) ^ 2) :
    (DigitPrime.digitDen p ℓ ρ).norm ≤ (p : ℤ) ^ (2 * p * (ℓ ^ 2 + 1)) := by
  rw [norm_digitDen]
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hρ0 : 0 ≤ ρ.norm := GaussianInt.norm_nonneg ρ
  have h1 : ρ.norm ^ (p - 2) ≤ (p : ℤ) ^ (2 * p) := by
    calc ρ.norm ^ (p - 2) ≤ ((p : ℤ) ^ 2) ^ (p - 2) := pow_le_pow_left₀ hρ0 hρ _
      _ = (p : ℤ) ^ (2 * (p - 2)) := by rw [← pow_mul]
      _ ≤ (p : ℤ) ^ (2 * p) := pow_le_pow_right₀ hp1 (by omega)
  have hfac : ∀ j ∈ Ico 1 ℓ, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) ≤ ((p : ℤ) ^ (2 * ℓ)) ^ p := by
    intro j hj
    have hb := one_add_pow_le_pow hp (mem_Ico.mp hj).2
    have hb0 : (0 : ℤ) ≤ 1 + (p : ℤ) ^ (2 * j) := by positivity
    calc (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) ≤ ((p : ℤ) ^ (2 * ℓ)) ^ (p - 1) :=
          pow_le_pow_left₀ hb0 hb _
      _ ≤ ((p : ℤ) ^ (2 * ℓ)) ^ p := pow_le_pow_right₀ (one_le_pow₀ hp1) (by omega)
  have hexp : 2 * ℓ * p * (ℓ - 1) ≤ 2 * p * ℓ ^ 2 := by
    calc 2 * ℓ * p * (ℓ - 1) ≤ 2 * ℓ * p * ℓ := Nat.mul_le_mul_left _ (Nat.sub_le ℓ 1)
      _ = 2 * p * ℓ ^ 2 := by ring
  have h2 : ∏ j ∈ Ico 1 ℓ, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) ≤ (p : ℤ) ^ (2 * p * ℓ ^ 2) := by
    calc ∏ j ∈ Ico 1 ℓ, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1)
        ≤ ∏ _j ∈ Ico 1 ℓ, ((p : ℤ) ^ (2 * ℓ)) ^ p :=
          prod_le_prod (fun j _ => by positivity) hfac
      _ = (((p : ℤ) ^ (2 * ℓ)) ^ p) ^ (ℓ - 1) := by rw [prod_const, Nat.card_Ico]
      _ = (p : ℤ) ^ (2 * ℓ * p * (ℓ - 1)) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ (p : ℤ) ^ (2 * p * ℓ ^ 2) := pow_le_pow_right₀ hp1 hexp
  have h3 : 0 ≤ ∏ j ∈ Ico 1 ℓ, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) :=
    prod_nonneg fun j _ => by positivity
  calc ρ.norm ^ (p - 2) * ∏ j ∈ Ico 1 ℓ, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1)
      ≤ (p : ℤ) ^ (2 * p) * (p : ℤ) ^ (2 * p * ℓ ^ 2) := mul_le_mul h1 h2 h3 (by positivity)
    _ = (p : ℤ) ^ (2 * p * (ℓ ^ 2 + 1)) := by rw [← pow_add]; ring_nf

/-- Upper bound on the cell: `‖g‖² ≤ ε²/125`. -/
lemma norm_cellGenD_sq_le {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp5 : 5 ≤ p)
    (hρn : ρ.norm ≤ (p : ℤ) ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ‖cellGenD π (star (DigitPrime.digitDen p (pℓ p ⌈1 / ε⌉₊) ρ)) (qn p ⌈1 / ε⌉₊)
        (qα p ⌈1 / ε⌉₊)‖ ^ 2 ≤ ε ^ 2 / 125 := by
  set K := ⌈1 / ε⌉₊ with hK
  rw [norm_cellGenD_sq' hπ _ (A := qA p K) (by unfold qα; have := qA_le_qn p K; omega),
    Zsqrtd.norm_conj]
  have hpr : (0 : ℝ) < p := by exact_mod_cast hπ.prime.pos
  have hpc : (K : ℝ) ≤ (p : ℝ) ^ pc p K := by exact_mod_cast le_pow_pc p K (by omega)
  have hKe : 1 / ε ≤ K := Nat.le_ceil _
  have hN : ((DigitPrime.digitDen p (pℓ p K) ρ).norm : ℝ) ≤
      (p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) := by
    exact_mod_cast norm_digitDen_le_pow (by omega) hρn
  have hA : (p : ℝ) ^ qA p K =
      (p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) * ((p : ℝ) ^ pc p K) ^ 2 * (p : ℝ) ^ 3 := by
    unfold qA; rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
  rw [hA, div_le_div_iff₀ (by positivity) (by norm_num)]
  have h2 : (125 : ℝ) ≤ (p : ℝ) ^ 3 := by
    have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    calc (125 : ℝ) = 5 ^ 3 := by norm_num
      _ ≤ (p : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
  have h3 : 1 ≤ ε ^ 2 * ((p : ℝ) ^ pc p K) ^ 2 := by
    have : 1 ≤ ε * (p : ℝ) ^ pc p K := by
      calc (1 : ℝ) = ε * (1 / ε) := by field_simp
        _ ≤ ε * K := by gcongr
        _ ≤ ε * (p : ℝ) ^ pc p K := by gcongr
    nlinarith
  have hq : (0 : ℝ) ≤ (p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) := by positivity
  calc ((DigitPrime.digitDen p (pℓ p K) ρ).norm : ℝ) * 125
      ≤ (p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) * 125 := by gcongr
    _ ≤ (p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) *
          ((p : ℝ) ^ 3 * (ε ^ 2 * ((p : ℝ) ^ pc p K) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hq; nlinarith
    _ = ε ^ 2 * ((p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) * ((p : ℝ) ^ pc p K) ^ 2 *
          (p : ℝ) ^ 3) := by
        ring

/-- Lower bound on the cell: `5^(-A) ≤ ‖g‖`. -/
lemma norm_cellGenD_ge {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp13 : p ≤ 13)
    {D : GaussianInt} (hD1 : 1 ≤ (D.norm : ℝ)) {n α A : ℕ} (hnA : α + A = n) :
    (1 / 5 : ℝ) ^ A ≤ ‖cellGenD π D n α‖ := by
  have hsq := norm_cellGenD_sq' hπ D hnA
  have hpr : (0 : ℝ) < p := by exact_mod_cast hπ.prime.pos
  have h1 : ((1 / 5 : ℝ) ^ A) ^ 2 ≤ ‖cellGenD π D n α‖ ^ 2 := by
    rw [hsq, ← pow_mul, le_div_iff₀ (by positivity)]
    have hp' : (p : ℝ) ≤ 25 := by
      have : (p : ℝ) ≤ 13 := by exact_mod_cast hp13
      linarith
    have h2 : (p : ℝ) ^ A ≤ 25 ^ A := pow_le_pow_left₀ hpr.le hp' A
    have h4 : (1 / 5 : ℝ) ^ (A * 2) * 25 ^ A = 1 := by
      rw [mul_comm A 2, pow_mul, ← mul_pow]; norm_num
    calc (1 / 5 : ℝ) ^ (A * 2) * (p : ℝ) ^ A ≤ (1 / 5 : ℝ) ^ (A * 2) * 25 ^ A := by gcongr
      _ = 1 := h4
      _ ≤ (D.norm : ℝ) := hD1
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h1

/- ## Divisibility facts -/

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

lemma not_dvd_digitDen {N : ℕ} {ρ : GaussianInt} (hρ2 : ¬ π ∣ star ρ) :
    ¬ π ∣ digitDen p N ρ := by
  intro h
  rw [digitDen] at h
  rcases hπ.prime_π.dvd_or_dvd h with h1 | h1
  · exact hρ2 (hπ.prime_π.dvd_of_dvd_pow h1)
  · rw [hπ.prime_π.dvd_finsetProd_iff] at h1
    obtain ⟨j, hj, hdvd⟩ := h1
    exact hπ.not_dvd_star_digitInt (mem_Ico.mp hj).1 (hπ.prime_π.dvd_of_dvd_pow hdvd)

lemma not_star_dvd_star_digitDen {N : ℕ} {ρ : GaussianInt} (hρ2 : ¬ π ∣ star ρ) :
    ¬ star π ∣ star (digitDen p N ρ) := by
  rintro ⟨c, hc⟩
  apply hπ.not_dvd_digitDen (N := N) hρ2
  exact ⟨star c, by rw [← star_star (digitDen p N ρ), hc, star_mul', star_star]⟩

lemma one_le_norm_star_digitDen {N : ℕ} {ρ : GaussianInt} (hρ1 : ¬ π ∣ ρ) :
    (1 : ℝ) ≤ ((star (digitDen p N ρ)).norm : ℝ) := by
  have hD0 : star (digitDen p N ρ) ≠ 0 := fun h0 =>
    (hπ.not_dvd_star_digitDen (N := N) hρ1) (by rw [h0]; exact dvd_zero π)
  have hpos : 0 < (star (digitDen p N ρ)).norm := by
    rcases (GaussianInt.norm_nonneg (star (digitDen p N ρ))).lt_or_eq with h | h
    · exact h
    · exact absurd (GaussianInt.norm_eq_zero.mp h.symm) hD0
  have : (1 : ℤ) ≤ (star (digitDen p N ρ)).norm := hpos
  exact_mod_cast this

end DigitPrime

/- ## The generic case -/

theorem case_core_quasi {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp5 : 5 ≤ p)
    (hp13 : p ≤ 13) (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ) (hρn : ρ.norm ≤ (p : ℤ) ^ 2)
    (hordA : ∀ k, 2 ≤ k → orderOf (hπ.mult (star ρ) k) = (p - 1) * p ^ (k - 1))
    (hordC : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
      orderOf (((hπ.mult (star ρ) n).val : ℕ) : ZMod (p ^ ℓ)) = (p - 1) * p ^ (ℓ - 1))
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) (hη : η ≤ (1 / 5 : ℝ) ^ qA p ⌈1 / ε⌉₊)
    (w : ℂ) (q : GaussianInt) {N₀ a₁ b₁ a₂ b₂ v : ℕ}
    (ha₁ : a₁ ≤ N₀) (hb₁ : b₁ ≤ N₀) (ha₂ : a₂ ≤ N₀) (hb₂ : b₂ ≤ N₀) {q₂ : GaussianInt}
    (hq₂ : ¬ star π ∣ q₂)
    (hqeq : q = star π ^ v * DigitPrime.digitDen p (qn p ⌈1 / ε⌉₊ + 4) ρ *
      star (DigitPrime.digitDen p (pℓ p ⌈1 / ε⌉₊) ρ) * q₂)
    (hclose : ‖(q : ℂ) - (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ ≤ η / 10) :
    ∃ a b : ℕ, a ≤ N₀ + v + (qA p ⌈1 / ε⌉₊ + 4) + qn p ⌈1 / ε⌉₊ ∧ b ≤ N₀ ∧
      ∃ μ ∈ digitRotFinset p (qn p ⌈1 / ε⌉₊ + 4) ρ,
      ∃ ν ∈ digitRotInvFinset p (pℓ p ⌈1 / ε⌉₊) ρ,
      ∃ k : ℤ, |(((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b * μ * ν * w).re - k| < ε := by
  set K := ⌈1 / ε⌉₊ with hK
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) (Nat.le_ceil (1 / ε))
    exact_mod_cast this
  have hℓ16 := pℓ_ge p K
  have hn2 : 2 ≤ qn p K := by unfold qn; omega
  -- the cell
  set g := cellGenD π (star (DigitPrime.digitDen p (pℓ p K) ρ)) (qn p K) (qα p K) with hg
  have hαA : qα p K + qA p K = qn p K := by unfold qα; have := qA_le_qn p K; omega
  have hglow : (1 / 5 : ℝ) ^ qA p K ≤ ‖g‖ :=
    norm_cellGenD_ge hπ hp13 (hπ.one_le_norm_star_digitDen hρ1) hαA
  have he' : ‖(((star π) ^ v * DigitPrime.digitDen p (qn p K + 4) ρ *
        star (DigitPrime.digitDen p (pℓ p K) ρ) * q₂ : GaussianInt) : ℂ) -
      (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ < 21 / 50 * ‖g‖ := by
    rw [← hqeq]
    have h5 : (0 : ℝ) < (1 / 5 : ℝ) ^ qA p K := by positivity
    linarith
  have hgε : Real.sqrt 2 * ‖g‖ ≤ ε / 2 :=
    sqrt_two_mul_le (norm_nonneg _) hε (norm_cellGenD_sq_le hπ hp5 hρn hε)
  have hH : 2 ≤ (pH K : ℝ) * ε ^ 2 := by
    have hKe : 1 / ε ≤ K := Nat.le_ceil _
    have h1 : 1 ≤ (K : ℝ) * ε := by
      calc (1 : ℝ) = (1 / ε) * ε := by field_simp
        _ ≤ K * ε := by gcongr
    unfold pH; push_cast; nlinarith
  have hHL : 25 * pH K ^ 3 < 4 * p ^ pL p K := pH_cube_lt p K hp5 hK1
  have hA4 := hordA (qn p K + 4) (by omega)
  rw [show qn p K + 4 - 1 = qn p K + 3 by omega] at hA4
  exact hπ.minor_arc_core_quasi hp5 hρ1 hρ2
    (n := qn p K) (α := qα p K) (A := qA p K) (L := pL p K) (ℓ := pℓ p K) (H := pH K)
    (pL_pos p K) rfl rfl (by omega) hA4 (hordC (qn p K) (pℓ p K) hn2 (by omega)) hε hH hHL hgε
    w ha₁ hb₁ ha₂ hb₂ hq₂ he'

/- ## The data attached to `ε` -/

/-- The divisor needed in the case of the digit prime `P` (multiplier `Q`). -/
noncomputable def D5Q (ε : ℝ) : GaussianInt :=
  DigitPrime.digitDen 5 (qn 5 ⌈1 / ε⌉₊ + 4) gQ * star (DigitPrime.digitDen 5 (pℓ 5 ⌈1 / ε⌉₊) gQ)

/-- The divisor needed in the case of the digit prime `Q` (multiplier `P`). -/
noncomputable def D13Q (ε : ℝ) : GaussianInt :=
  DigitPrime.digitDen 13 (qn 13 ⌈1 / ε⌉₊ + 4) gP *
    star (DigitPrime.digitDen 13 (pℓ 13 ⌈1 / ε⌉₊) gP)

/-- The modulus `N(D5Q) N(D13Q)` that the pigeonhole has to respect. -/
noncomputable def MdigQ (ε : ℝ) : ℕ := (D5Q ε).norm.natAbs * (D13Q ε).norm.natAbs

/-- The exponent budget: `O(log² (1/ε))`. -/
noncomputable def BdQ (ε : ℝ) : ℝ :=
  ((qA 5 ⌈1 / ε⌉₊ + 4 + qn 5 ⌈1 / ε⌉₊ + (qA 13 ⌈1 / ε⌉₊ + 4 + qn 13 ⌈1 / ε⌉₊) : ℕ) : ℝ)

/-- The tolerance `5^(-(A₅ + A₁₃))`. -/
noncomputable def ηQ (ε : ℝ) : ℝ := (1 / 5 : ℝ) ^ (qA 5 ⌈1 / ε⌉₊ + qA 13 ⌈1 / ε⌉₊)

/-- The products `μ ν` of a digit rotation at level `N` and an inverse digit rotation at
level `ℓ`. -/
noncomputable def rotPairs (p N ℓ : ℕ) (ρ : GaussianInt) : Finset ℂ :=
  (digitRotFinset p N ρ ×ˢ digitRotInvFinset p ℓ ρ).image fun x => x.1 * x.2

/-- The rotations used by the interface. -/
noncomputable def RotsQ (ε : ℝ) : Finset ℂ :=
  rotPairs 5 (qn 5 ⌈1 / ε⌉₊ + 4) (pℓ 5 ⌈1 / ε⌉₊) gQ ∪
    rotPairs 13 (qn 13 ⌈1 / ε⌉₊ + 4) (pℓ 13 ⌈1 / ε⌉₊) gP

lemma mem_rotPairs {p N ℓ : ℕ} {ρ : GaussianInt} {μ ν : ℂ} (hμ : μ ∈ digitRotFinset p N ρ)
    (hν : ν ∈ digitRotInvFinset p ℓ ρ) : μ * ν ∈ rotPairs p N ℓ ρ :=
  Finset.mem_image.mpr ⟨(μ, ν), Finset.mem_product.mpr ⟨hμ, hν⟩, rfl⟩

lemma norm_of_mem_rotPairs {p N ℓ : ℕ} {ρ : GaussianInt} (hρ : ρ ≠ 0) {x : ℂ}
    (hx : x ∈ rotPairs p N ℓ ρ) : ‖x‖ = 1 := by
  obtain ⟨⟨μ, ν⟩, hμν, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hμ, hν⟩ := Finset.mem_product.mp hμν
  rw [norm_mul, norm_of_mem_digitRotFinset hρ hμ, norm_of_mem_digitRotInvFinset hρ hν, one_mul]

lemma card_rotPairs_le (p N ℓ : ℕ) (ρ : GaussianInt) :
    (rotPairs p N ℓ ρ).card ≤ ((p - 1) * p ^ (N - 1)) * ((p - 1) * p ^ (ℓ - 1)) := by
  calc (rotPairs p N ℓ ρ).card ≤ (digitRotFinset p N ρ ×ˢ digitRotInvFinset p ℓ ρ).card :=
        Finset.card_image_le
    _ = (digitRotFinset p N ρ).card * (digitRotInvFinset p ℓ ρ).card := Finset.card_product _ _
    _ ≤ ((p - 1) * p ^ (N - 1)) * ((p - 1) * p ^ (ℓ - 1)) :=
        Nat.mul_le_mul (card_digitRotFinset_le _ _ _) (card_digitRotInvFinset_le _ _ _)

lemma one_mem_rotPairs {p N ℓ : ℕ} (hp : 2 ≤ p) (ρ : GaussianInt) : (1 : ℂ) ∈ rotPairs p N ℓ ρ := by
  have h := mem_rotPairs (one_mem_digitRotFinset (N := N) hp ρ)
    (one_mem_digitRotInvFinset (N := ℓ) hp ρ)
  rwa [one_mul] at h

lemma not_dvd_D5Q (ε : ℝ) : ¬ gPb ∣ D5Q ε := by
  intro h
  rcases prime_gPb.dvd_or_dvd h with h1 | h1
  · exact digitPrime_P.not_star_dvd_digitDen gP_not_dvd_gQ h1
  · exact digitPrime_P.not_star_dvd_star_digitDen gP_not_dvd_gQb h1

lemma not_dvd_D13Q (ε : ℝ) : ¬ gQb ∣ D13Q ε := by
  intro h
  rcases prime_gQb.dvd_or_dvd h with h1 | h1
  · exact digitPrime_Q.not_star_dvd_digitDen gQ_not_dvd_gP h1
  · exact digitPrime_Q.not_star_dvd_star_digitDen gQ_not_dvd_gPb h1

lemma D5Q_ne_zero (ε : ℝ) : D5Q ε ≠ 0 := fun h => not_dvd_D5Q ε (h ▸ dvd_zero _)

lemma D13Q_ne_zero (ε : ℝ) : D13Q ε ≠ 0 := fun h => not_dvd_D13Q ε (h ▸ dvd_zero _)

lemma MdigQ_pos (ε : ℝ) : 0 < MdigQ ε := by
  have h5 : 0 < (D5Q ε).norm.natAbs :=
    Int.natAbs_pos.mpr fun h => D5Q_ne_zero ε (GaussianInt.norm_eq_zero.mp h)
  have h13 : 0 < (D13Q ε).norm.natAbs :=
    Int.natAbs_pos.mpr fun h => D13Q_ne_zero ε (GaussianInt.norm_eq_zero.mp h)
  exact Nat.mul_pos h5 h13

lemma D5Q_dvd_of_MdigQ_dvd {ε : ℝ} {q : GaussianInt} (h : ((MdigQ ε : ℕ) : GaussianInt) ∣ q) :
    D5Q ε ∣ q := by
  refine (dvd_natAbs_norm _).trans (dvd_trans ?_ h)
  unfold MdigQ; push_cast
  exact dvd_mul_right _ _

lemma D13Q_dvd_of_MdigQ_dvd {ε : ℝ} {q : GaussianInt} (h : ((MdigQ ε : ℕ) : GaussianInt) ∣ q) :
    D13Q ε ∣ q := by
  refine (dvd_natAbs_norm _).trans (dvd_trans ?_ h)
  unfold MdigQ; push_cast
  exact dvd_mul_left _ _

lemma ηQ_pos (ε : ℝ) : 0 < ηQ ε := by unfold ηQ; positivity

lemma BdQ_nonneg (ε : ℝ) : 0 ≤ BdQ ε := by unfold BdQ; positivity

lemma norm_of_mem_RotsQ {ε : ℝ} {μ : ℂ} (hμ : μ ∈ RotsQ ε) : ‖μ‖ = 1 := by
  unfold RotsQ at hμ
  rcases Finset.mem_union.mp hμ with h | h
  · exact norm_of_mem_rotPairs gQ_ne_zero' h
  · exact norm_of_mem_rotPairs gP_ne_zero' h

lemma one_le_card_RotsQ (ε : ℝ) : 1 ≤ (RotsQ ε).card :=
  Finset.card_pos.mpr ⟨1, Finset.mem_union_left _ (one_mem_rotPairs (by norm_num) _)⟩

/-- The minor-arc data with digit rotations on both sides. -/
noncomputable def dataQ : ArcData where
  η := ηQ
  M := MdigQ
  Bd := BdQ
  Rots := RotsQ
  η_pos := ηQ_pos
  M_pos := MdigQ_pos
  Bd_nonneg := BdQ_nonneg
  norm_rots := fun _ _ hμ => norm_of_mem_RotsQ hμ
  card_rots := one_le_card_RotsQ

/- ## The interface -/

/-- **The minor-arc proposition with digit rotations on both sides.** -/
theorem dataQ_KL : dataQ.KL := by
  intro ε ϖ hε0 hε1 hϖ0 hϖ1 N₀ s₁ t₁ s₂ t₂ w q hs₁ ht₁ hs₂ ht₂ hM hlow hclose
  change ((MdigQ ε : ℕ) : GaussianInt) ∣ q at hM
  change ‖(q : ℂ) - (rot s₁ t₁ - rot s₂ t₂) * w‖ ≤ ηQ ε / 10 at hclose
  show ∃ s t : ℕ, (s : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + BdQ ε ∧
    (t : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + BdQ ε ∧ ∃ μ ∈ RotsQ ε, InStripe ε (rot s t * μ) w
  have h5n := size5_nonneg q
  have h13n := size13_nonneg q
  have hq : q ≠ 0 := by
    rintro rfl
    simp only [size5, size13, if_true] at hlow
    linarith
  have hlog0 : 0 ≤ Real.logb 5 ϖ⁻¹ :=
    Real.logb_nonneg (by norm_num) (by rw [le_inv_comm₀ one_pos hϖ0]; linarith)
  have hBd0 := BdQ_nonneg ε
  set K := ⌈1 / ε⌉₊ with hK
  have hBd5 : ((qA 5 K + 4 + qn 5 K : ℕ) : ℝ) ≤ BdQ ε := by
    unfold BdQ; rw [← hK]; exact_mod_cast Nat.le_add_right _ _
  have hBd13 : ((qA 13 K + 4 + qn 13 K : ℕ) : ℝ) ≤ BdQ ε := by
    unfold BdQ; rw [← hK]; exact_mod_cast Nat.le_add_left _ _
  by_cases h513 : size13 q ≤ size5 q
  · -- Case 1: digit prime `P`, multiplier `Q`.
    set v := multiplicity gPb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      rw [← size5_eq hq]; linarith
    have hcop : IsCoprime gPb (D5Q ε) :=
      prime_gPb.irreducible.coprime_iff_not_dvd.mpr (not_dvd_D5Q ε)
    obtain ⟨q₂, hq₂, hqeq⟩ := decomp_dvd prime_gPb hcop hq (D5Q_dvd_of_MdigQ_dvd hM)
    have hqeq' : q = star gP ^ v * DigitPrime.digitDen 5 (qn 5 ⌈1 / ε⌉₊ + 4) gQ *
        star (DigitPrime.digitDen 5 (pℓ 5 ⌈1 / ε⌉₊) gQ) * q₂ := by
      rw [hqeq, D5Q, ← hv]; simp only [star_gP]; ring
    have hordA : ∀ k, 2 ≤ k →
        orderOf (digitPrime_P.mult (star gQ) k) = (5 - 1) * 5 ^ (k - 1) := by
      intro k hk
      have : NeZero (5 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_P_Qb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordC : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_P.mult (star gQ) n).val : ℕ) : ZMod (5 ^ ℓ)) =
          (5 - 1) * 5 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_P_Qb hn hℓ
    have hη : ηQ ε ≤ (1 / 5 : ℝ) ^ qA 5 ⌈1 / ε⌉₊ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right _ _)
    obtain ⟨a, b, ha, hb, μ, hμ, ν, hν, k, hk⟩ := case_core_quasi digitPrime_P le_rfl
      (by norm_num) gP_not_dvd_gQ gP_not_dvd_gQb (by rw [norm_gQ]; norm_num) hordA hordC hε0 hε1
      hη w q hs₁ ht₁ hs₂ ht₂ hq₂ hqeq' hclose
    rw [← hK] at ha
    refine ⟨a, b, ?_, ?_, μ * ν, Finset.mem_union_left _ (mem_rotPairs hμ hν), k, ?_⟩
    · have h1 : (a : ℝ) ≤ N₀ + v + ((qA 5 K + 4 + qn 5 K : ℕ) : ℝ) := by
        have : a ≤ N₀ + v + (qA 5 K + 4 + qn 5 K) := by omega
        exact_mod_cast this
      linarith
    · have h1 : (b : ℝ) ≤ N₀ := by exact_mod_cast hb
      linarith
    · have hX : rot a b * (μ * ν) * w = ((gP : ℂ) / ((star gP : GaussianInt) : ℂ)) ^ a *
          ((gQ : ℂ) / ((star gQ : GaussianInt) : ℂ)) ^ b * μ * ν * w := by
        unfold rot θ5 θ13; rw [star_gP, star_gQ]; ring
      rw [hX]
      exact hk
  · -- Case 2: digit prime `Q`, multiplier `P`.
    push Not at h513
    set v := multiplicity gQb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      have h1 : ϖ ≤ size13 q := by linarith
      rw [size13_eq hq] at h1
      have h2 : (13 : ℝ) ^ (-(v : ℝ)) ≤ (5 : ℝ) ^ (-(v : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
        apply inv_anti₀ (by positivity)
        exact Real.rpow_le_rpow (by norm_num) (by norm_num) (Nat.cast_nonneg _)
      linarith
    have hcop : IsCoprime gQb (D13Q ε) :=
      prime_gQb.irreducible.coprime_iff_not_dvd.mpr (not_dvd_D13Q ε)
    obtain ⟨q₂, hq₂, hqeq⟩ := decomp_dvd prime_gQb hcop hq (D13Q_dvd_of_MdigQ_dvd hM)
    have hqeq' : q = star gQ ^ v * DigitPrime.digitDen 13 (qn 13 ⌈1 / ε⌉₊ + 4) gP *
        star (DigitPrime.digitDen 13 (pℓ 13 ⌈1 / ε⌉₊) gP) * q₂ := by
      rw [hqeq, D13Q, ← hv]; simp only [star_gQ]; ring
    have hordA : ∀ k, 2 ≤ k →
        orderOf (digitPrime_Q.mult (star gP) k) = (13 - 1) * 13 ^ (k - 1) := by
      intro k hk
      have : NeZero (13 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_Q_Pb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordC : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_Q.mult (star gP) n).val : ℕ) : ZMod (13 ^ ℓ)) =
          (13 - 1) * 13 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_Q_Pb hn hℓ
    have hη : ηQ ε ≤ (1 / 5 : ℝ) ^ qA 13 ⌈1 / ε⌉₊ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left _ _)
    have hrot : ∀ s t : ℕ, rot s t = ((gQ : ℂ) / ((star gQ : GaussianInt) : ℂ)) ^ t *
        ((gP : ℂ) / ((star gP : GaussianInt) : ℂ)) ^ s := by
      intro s t; unfold rot θ5 θ13; rw [star_gP, star_gQ]; ring
    rw [hrot s₁ t₁, hrot s₂ t₂] at hclose
    obtain ⟨a, b, ha, hb, μ, hμ, ν, hν, k, hk⟩ := case_core_quasi digitPrime_Q (by norm_num)
      le_rfl gQ_not_dvd_gP gQ_not_dvd_gPb (by rw [norm_gP]; norm_num) hordA hordC hε0 hε1
      hη w q ht₁ hs₁ ht₂ hs₂ hq₂ hqeq' hclose
    rw [← hK] at ha
    refine ⟨b, a, ?_, ?_, μ * ν, Finset.mem_union_right _ (mem_rotPairs hμ hν), k, ?_⟩
    · have h1 : (b : ℝ) ≤ N₀ := by exact_mod_cast hb
      linarith
    · have h1 : (a : ℝ) ≤ N₀ + v + ((qA 13 K + 4 + qn 13 K : ℕ) : ℝ) := by
        have : a ≤ N₀ + v + (qA 13 K + 4 + qn 13 K) := by omega
        exact_mod_cast this
      linarith
    · have hX : rot b a * (μ * ν) * w = ((gQ : ℂ) / ((star gQ : GaussianInt) : ℂ)) ^ a *
          ((gP : ℂ) / ((star gP : GaussianInt) : ℂ)) ^ b * μ * ν * w := by
        rw [hrot b a]; ring
      rw [hX]
      exact hk

end Green41Proof
