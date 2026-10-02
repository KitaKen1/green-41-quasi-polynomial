import Green41SingleExponential.MinorArcDigit

/-!
# The minor-arc interface with digit rotations

The double-exponential proof feeds the minor-arc proposition with a `q` whose `P̄`- and
`Q̄`-adic sizes are below `δ = 13^(-c η⁻⁵)`; this makes `q` divisible by `ρ̄^E` with `E`
exponential, which Step A needs. With digit rotations Step A only needs `q` to be divisible by
the explicit Gaussian integers

* `D5 ε  = digitDen 5 (n₅ + 4) Q · Q̄^(S₅)` (digit prime `P`, multiplier `Q`), and
* `D13 ε = digitDen 13 (n₁₃ + 4) P · P̄^(S₁₃)` (digit prime `Q`, multiplier `P`),

so the interface `KL57D` asks for `Mdig ε = N(D5 ε) N(D13 ε) ∣ q` instead of the condition on
`δ`. The rotation it produces is `rot s t * μ` with `μ` a digit rotation and `s, t` bounded by
the polynomial quantity `Bd ε`.
-/

namespace Green41Proof

open Green41

open Complex ComplexConjugate Finset

/- ## Decomposing `q` -/

/-- If `D ∣ q` and `D` is prime to the prime `a`, then `q = a^v D q₂` with `a ∤ q₂`. -/
lemma decomp_dvd {a D q : GaussianInt} (ha : Prime a) (hcop : IsCoprime a D) (hq : q ≠ 0)
    (hD : D ∣ q) : ∃ q₂, ¬ a ∣ q₂ ∧ q = a ^ multiplicity a q * D * q₂ := by
  have hf : FiniteMultiplicity a q := FiniteMultiplicity.of_not_isUnit ha.not_isUnit hq
  set v := multiplicity a q with hv
  obtain ⟨q₁, hq₁⟩ : a ^ v ∣ q := pow_multiplicity_dvd a q
  have hnd : ¬ a ∣ q₁ := by
    rintro ⟨c, hc⟩
    apply hf.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self v)
    exact ⟨c, by rw [hq₁, hc, pow_succ]; ring⟩
  have hb : D ∣ q₁ := by
    have h1 : D ∣ a ^ v * q₁ := hq₁ ▸ hD
    exact (hcop.symm.pow_right).dvd_of_dvd_mul_left h1
  obtain ⟨q₂, hq₂⟩ := hb
  refine ⟨q₂, fun h => hnd (by rw [hq₂]; exact dvd_mul_of_dvd_right h _), ?_⟩
  rw [hq₁, hq₂]; ring

/-- A Gaussian integer divides its norm. -/
lemma dvd_natAbs_norm (D : GaussianInt) : D ∣ ((D.norm.natAbs : ℕ) : GaussianInt) := by
  have h : ((D.norm.natAbs : ℕ) : ℤ) = D.norm := Int.natAbs_of_nonneg (GaussianInt.norm_nonneg D)
  have h2 : ((D.norm.natAbs : ℕ) : GaussianInt) = ((D.norm : ℤ) : GaussianInt) := by
    rw [← Int.cast_natCast, h]
  rw [h2, Zsqrtd.norm_eq_mul_conj]
  exact dvd_mul_right D _

/- ## The digit data attached to `ε` -/

/-- The divisor needed in the case of the digit prime `P` (multiplier `Q`). -/
noncomputable def D5 (ε : ℝ) : GaussianInt :=
  DigitPrime.digitDen 5 (pn 5 ⌈1 / ε⌉₊ + 4) gQ * star gQ ^ pS 5 ⌈1 / ε⌉₊

/-- The divisor needed in the case of the digit prime `Q` (multiplier `P`). -/
noncomputable def D13 (ε : ℝ) : GaussianInt :=
  DigitPrime.digitDen 13 (pn 13 ⌈1 / ε⌉₊ + 4) gP * star gP ^ pS 13 ⌈1 / ε⌉₊

/-- The modulus `N(D5) N(D13)` that the pigeonhole has to respect. -/
noncomputable def Mdig (ε : ℝ) : ℕ := (D5 ε).norm.natAbs * (D13 ε).norm.natAbs

/-- The exponent budget of the interface: polynomial in `1/ε`. -/
noncomputable def Bd (ε : ℝ) : ℝ :=
  ((pA 5 ⌈1 / ε⌉₊ + 4 + pn 5 ⌈1 / ε⌉₊ + (pA 13 ⌈1 / ε⌉₊ + 4 + pn 13 ⌈1 / ε⌉₊) : ℕ) : ℝ)

/-- The digit rotations used by the interface. -/
noncomputable def Rots (ε : ℝ) : Finset ℂ :=
  digitRotFinset 5 (pn 5 ⌈1 / ε⌉₊ + 4) gQ ∪ digitRotFinset 13 (pn 13 ⌈1 / ε⌉₊ + 4) gP

lemma not_dvd_D5 (ε : ℝ) : ¬ gPb ∣ D5 ε := by
  intro h
  rcases prime_gPb.dvd_or_dvd h with h1 | h1
  · exact digitPrime_P.not_star_dvd_digitDen gP_not_dvd_gQ h1
  · exact gPb_not_dvd_gQb (prime_gPb.dvd_of_dvd_pow h1)

lemma not_dvd_D13 (ε : ℝ) : ¬ gQb ∣ D13 ε := by
  intro h
  rcases prime_gQb.dvd_or_dvd h with h1 | h1
  · exact digitPrime_Q.not_star_dvd_digitDen gQ_not_dvd_gP h1
  · exact gQb_not_dvd_gPb (prime_gQb.dvd_of_dvd_pow h1)

lemma D5_ne_zero (ε : ℝ) : D5 ε ≠ 0 := fun h => not_dvd_D5 ε (h ▸ dvd_zero _)

lemma D13_ne_zero (ε : ℝ) : D13 ε ≠ 0 := fun h => not_dvd_D13 ε (h ▸ dvd_zero _)

lemma Mdig_pos (ε : ℝ) : 0 < Mdig ε := by
  have h5 : 0 < (D5 ε).norm.natAbs :=
    Int.natAbs_pos.mpr fun h => D5_ne_zero ε (GaussianInt.norm_eq_zero.mp h)
  have h13 : 0 < (D13 ε).norm.natAbs :=
    Int.natAbs_pos.mpr fun h => D13_ne_zero ε (GaussianInt.norm_eq_zero.mp h)
  exact Nat.mul_pos h5 h13

lemma D5_dvd_of_Mdig_dvd {ε : ℝ} {q : GaussianInt} (h : ((Mdig ε : ℕ) : GaussianInt) ∣ q) :
    D5 ε ∣ q := by
  refine (dvd_natAbs_norm _).trans (dvd_trans ?_ h)
  unfold Mdig; push_cast
  exact dvd_mul_right _ _

lemma D13_dvd_of_Mdig_dvd {ε : ℝ} {q : GaussianInt} (h : ((Mdig ε : ℕ) : GaussianInt) ∣ q) :
    D13 ε ∣ q := by
  refine (dvd_natAbs_norm _).trans (dvd_trans ?_ h)
  unfold Mdig; push_cast
  exact dvd_mul_left _ _

/- ## The generic case with digit rotations -/

theorem case_core_digit {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp5 : 5 ≤ p)
    (hp13 : p ≤ 13) (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ)
    (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0) (hρn : (ρ.norm : ℝ) ≤ (p : ℝ) ^ 2)
    (hρn1 : 1 ≤ (ρ.norm : ℝ))
    (hordA : ∀ k, 2 ≤ k → orderOf (hπ.mult (star ρ) k) = (p - 1) * p ^ (k - 1))
    (hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
      orderOf (((hπ.mult ρ n).val : ℕ) : ZMod (p ^ ℓ)) = (p - 1) * p ^ (ℓ - 1))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) (w : ℂ) (q : GaussianInt) {N₀ a₁ b₁ a₂ b₂ v : ℕ}
    (ha₁ : a₁ ≤ N₀) (hb₁ : b₁ ≤ N₀) (ha₂ : a₂ ≤ N₀) (hb₂ : b₂ ≤ N₀) {q₂ : GaussianInt}
    (hq₂ : ¬ star π ∣ q₂)
    (hqeq : q = star π ^ v * DigitPrime.digitDen p (pn p ⌈1 / ε⌉₊ + 4) ρ *
      star ρ ^ pS p ⌈1 / ε⌉₊ * q₂)
    (hclose : ‖(q : ℂ) - (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ ≤ ηKL 100 ε / 10) :
    ∃ a b : ℕ, a ≤ N₀ + v + (pA p ⌈1 / ε⌉₊ + 4) + pn p ⌈1 / ε⌉₊ ∧ b ≤ N₀ + pS p ⌈1 / ε⌉₊ ∧
      ∃ μ ∈ digitRotFinset p (pn p ⌈1 / ε⌉₊ + 4) ρ,
      ∃ k : ℤ, |(((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b * μ * w).re - k| < ε := by
  set K := ⌈1 / ε⌉₊ with hK
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) (Nat.le_ceil (1 / ε))
    exact_mod_cast this
  have hn2 : 2 ≤ pn p K := by unfold pn; have := pℓ_ge p K; omega
  have hℓ1 : 1 ≤ pℓ p K := by have := pℓ_ge p K; omega
  -- the cell
  set g := cellGen π ρ (pn p K) (pα p K) (pS p K) with hg
  have hαA : pα p K + pA p K = pn p K := by unfold pα; have := pA_le_pn p K; omega
  have hglow : (1 / 5 : ℝ) ^ pA p K ≤ ‖g‖ := norm_cellGen_ge hπ hp13 hρn1 hαA
  have hηA := ηKL_le_five_pow_neg hp5 hp13 hε hε1
  have he' : ‖(((star π) ^ v * DigitPrime.digitDen p (pn p K + 4) ρ * (star ρ) ^ pS p K * q₂ :
        GaussianInt) : ℂ) -
      (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ < 21 / 50 * ‖g‖ := by
    rw [← hqeq]
    have hη0 : 0 < ηKL 100 ε := ηKL_pos 100 ε
    linarith
  have hgε : Real.sqrt 2 * ‖g‖ ≤ ε / 2 :=
    sqrt_two_mul_le (norm_nonneg _) hε (norm_cellGen_sq_le hπ hp5 hρn hε)
  have hH : 2 ≤ (pH K : ℝ) * ε ^ 2 := by
    have hKe : 1 / ε ≤ K := Nat.le_ceil _
    have h1 : 1 ≤ (K : ℝ) * ε := by
      calc (1 : ℝ) = (1 / ε) * ε := by field_simp
        _ ≤ K * ε := by gcongr
    unfold pH; push_cast; nlinarith
  have hHL : 25 * pH K ^ 3 < 4 * p ^ pL p K := pH_cube_lt p K hp5 hK1
  have hA4 := hordA (pn p K + 4) (by omega)
  rw [show pn p K + 4 - 1 = pn p K + 3 by omega] at hA4
  exact hπ.minor_arc_core_digit hp5 hρ1 hρ2 hρ0
    (n := pn p K) (α := pα p K) (β := pS p K) (A := pA p K) (L := pL p K) (ℓ := pℓ p K)
    (S := pS p K) (H := pH K) (pL_pos p K) rfl rfl le_rfl rfl rfl hA4
    (hordB (pn p K) (pℓ p K) hn2 hℓ1) hε hH hHL hgε w ha₁ hb₁ ha₂ hb₂ hq₂ he'

/- ## The interface -/

/-- **The minor-arc proposition with digit rotations.** Compared with `KL57With c`, the
condition `size5 q + size13 q ≤ δ` is replaced by `Mdig ε ∣ q`, and the rotation found is
`rot s t * μ` with `μ ∈ Rots ε` and `s, t ≤ N₀ + log₅ ϖ⁻¹ + Bd ε`. -/
def KL57D : Prop :=
  ∀ ε ϖ : ℝ, 0 < ε → ε < 1 / 10 → 0 < ϖ → ϖ < 1 / 10 →
    ∀ (N₀ s₁ t₁ s₂ t₂ : ℕ) (w : ℂ) (q : GaussianInt),
      s₁ ≤ N₀ → t₁ ≤ N₀ → s₂ ≤ N₀ → t₂ ≤ N₀ →
      ((Mdig ε : ℕ) : GaussianInt) ∣ q →
      2 * ϖ ≤ size5 q + size13 q →
      ‖(q : ℂ) - (rot s₁ t₁ - rot s₂ t₂) * w‖ ≤ ηKL 100 ε / 10 →
      ∃ s t : ℕ, (s : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + Bd ε ∧
        (t : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + Bd ε ∧ ∃ μ ∈ Rots ε, InStripe ε (rot s t * μ) w

theorem kl57D : KL57D := by
  intro ε ϖ hε0 hε1 hϖ0 hϖ1 N₀ s₁ t₁ s₂ t₂ w q hs₁ ht₁ hs₂ ht₂ hM hlow hclose
  have h5n := size5_nonneg q
  have h13n := size13_nonneg q
  have hq : q ≠ 0 := by
    rintro rfl
    simp only [size5, size13, if_true] at hlow
    linarith
  have hlog0 : 0 ≤ Real.logb 5 ϖ⁻¹ :=
    Real.logb_nonneg (by norm_num) (by rw [le_inv_comm₀ one_pos hϖ0]; linarith)
  set K := ⌈1 / ε⌉₊ with hK
  have hBd5 : ((pA 5 K + 4 + pn 5 K : ℕ) : ℝ) ≤ Bd ε := by
    unfold Bd; rw [← hK]; exact_mod_cast Nat.le_add_right _ _
  have hBd13 : ((pA 13 K + 4 + pn 13 K : ℕ) : ℝ) ≤ Bd ε := by
    unfold Bd; rw [← hK]; exact_mod_cast Nat.le_add_left _ _
  by_cases h513 : size13 q ≤ size5 q
  · -- Case 1: digit prime `P`, multiplier `Q`.
    set v := multiplicity gPb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      rw [← size5_eq hq]; linarith
    have hcop : IsCoprime gPb (D5 ε) :=
      prime_gPb.irreducible.coprime_iff_not_dvd.mpr (not_dvd_D5 ε)
    obtain ⟨q₂, hq₂, hqeq⟩ := decomp_dvd prime_gPb hcop hq (D5_dvd_of_Mdig_dvd hM)
    have hqeq' : q = star gP ^ v * DigitPrime.digitDen 5 (pn 5 ⌈1 / ε⌉₊ + 4) gQ *
        star gQ ^ pS 5 ⌈1 / ε⌉₊ * q₂ := by
      rw [hqeq, D5, ← hv]; simp only [star_gP]; ring
    have hordA : ∀ k, 2 ≤ k →
        orderOf (digitPrime_P.mult (star gQ) k) = (5 - 1) * 5 ^ (k - 1) := by
      intro k hk
      have : NeZero (5 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_P_Qb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_P.mult gQ n).val : ℕ) : ZMod (5 ^ ℓ)) = (5 - 1) * 5 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_P_Q hn hℓ
    obtain ⟨a, b, ha, hb, μ, hμ, k, hk⟩ := case_core_digit digitPrime_P le_rfl (by norm_num)
      gP_not_dvd_gQ gP_not_dvd_gQb gQb_ne_zero (by rw [norm_gQ]; norm_num)
      (by rw [norm_gQ]; norm_num) hordA hordB hε0 hε1 w q hs₁ ht₁ hs₂ ht₂ hq₂ hqeq' hclose
    rw [← hK] at ha hb
    have hSA : pS 5 K ≤ pA 5 K + 4 + pn 5 K := by unfold pA; omega
    refine ⟨a, b, ?_, ?_, μ, Finset.mem_union_left _ hμ, k, hk⟩
    · have h1 : (a : ℝ) ≤ N₀ + v + ((pA 5 K + 4 + pn 5 K : ℕ) : ℝ) := by
        have : a ≤ N₀ + v + (pA 5 K + 4 + pn 5 K) := by omega
        exact_mod_cast this
      linarith
    · have h1 : (b : ℝ) ≤ N₀ + ((pA 5 K + 4 + pn 5 K : ℕ) : ℝ) := by
        have : b ≤ N₀ + (pA 5 K + 4 + pn 5 K) := by omega
        exact_mod_cast this
      linarith
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
    have hcop : IsCoprime gQb (D13 ε) :=
      prime_gQb.irreducible.coprime_iff_not_dvd.mpr (not_dvd_D13 ε)
    obtain ⟨q₂, hq₂, hqeq⟩ := decomp_dvd prime_gQb hcop hq (D13_dvd_of_Mdig_dvd hM)
    have hqeq' : q = star gQ ^ v * DigitPrime.digitDen 13 (pn 13 ⌈1 / ε⌉₊ + 4) gP *
        star gP ^ pS 13 ⌈1 / ε⌉₊ * q₂ := by
      rw [hqeq, D13, ← hv]; simp only [star_gQ]; ring
    have hordA : ∀ k, 2 ≤ k →
        orderOf (digitPrime_Q.mult (star gP) k) = (13 - 1) * 13 ^ (k - 1) := by
      intro k hk
      have : NeZero (13 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_Q_Pb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_Q.mult gP n).val : ℕ) : ZMod (13 ^ ℓ)) =
          (13 - 1) * 13 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_Q_P hn hℓ
    have hrot : ∀ s t : ℕ, rot s t = ((gQ : ℂ) / ((star gQ : GaussianInt) : ℂ)) ^ t *
        ((gP : ℂ) / ((star gP : GaussianInt) : ℂ)) ^ s := by
      intro s t; unfold rot θ5 θ13; rw [star_gP, star_gQ]; ring
    rw [hrot s₁ t₁, hrot s₂ t₂] at hclose
    obtain ⟨a, b, ha, hb, μ, hμ, k, hk⟩ := case_core_digit digitPrime_Q (by norm_num) le_rfl
      gQ_not_dvd_gP gQ_not_dvd_gPb gPb_ne_zero (by rw [norm_gP]; norm_num)
      (by rw [norm_gP]; norm_num) hordA hordB hε0 hε1 w q ht₁ hs₁ ht₂ hs₂ hq₂ hqeq' hclose
    rw [← hK] at ha hb
    have hSA : pS 13 K ≤ pA 13 K + 4 + pn 13 K := by unfold pA; omega
    refine ⟨b, a, ?_, ?_, μ, Finset.mem_union_right _ hμ, k, ?_⟩
    · have h1 : (b : ℝ) ≤ N₀ + ((pA 13 K + 4 + pn 13 K : ℕ) : ℝ) := by
        have : b ≤ N₀ + (pA 13 K + 4 + pn 13 K) := by omega
        exact_mod_cast this
      linarith
    · have h1 : (a : ℝ) ≤ N₀ + v + ((pA 13 K + 4 + pn 13 K : ℕ) : ℝ) := by
        have : a ≤ N₀ + v + (pA 13 K + 4 + pn 13 K) := by omega
        exact_mod_cast this
      linarith
    · rw [hrot b a]
      exact hk

end Green41Proof
