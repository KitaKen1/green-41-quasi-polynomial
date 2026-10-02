import Green41SingleExponential.DigitRotation

/-!
# Step A for a family of multipliers

`Green41Proof.DigitPrime.stepA` reaches every label with the powers `(ρ/ρ̄)^t`,
`t < (p - 1) p^(n+3)`, which forces `q` to be divisible by `ρ̄^E` with `E` exponential in `n`.
The proof only uses two facts about these multipliers:

1. their multipliers `ψ(Ā)/ψ(A)` reach every unit modulo `π̄^(n+4)`, and
2. their conjugates `Ā` all divide one common denominator `B`, which `q` absorbs.

`stepA_family` states Step A for any such family `𝒜` (the original is the case `𝒜 = {ρ^t}`,
`B = ρ̄^(E-β)`). `stepA_digit` instantiates it with the digit family of `DigitRotation`, whose
common denominator `ρ̄^(p-2) ∏_{1 ≤ j < n+4} (1 - p^j i)^(p-1)` has size `p^{O(n²)}`.
-/

namespace Green41Proof

open Complex Finset

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

/-- **Step A for a family.** If the multipliers of `𝒜` reach every unit modulo `π̄^(n+4)` and all
conjugates `Ā` divide `B`, then every residue `l` is the label of `σʲ (A/Ā) (q + e')` for some
`A ∈ 𝒜`, where `q = π̄^v B ρ̄^β q₂` and `j = v + (n - α + 4)`. -/
theorem stepA_family (hp5 : 5 ≤ p) {ρ : GaussianInt} (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0)
    {n α β : ℕ} (hα : α ≤ n) (𝒜 : Set GaussianInt) (B : GaussianInt)
    (hcover : ∀ c : ZMod (p ^ (n + 4)), IsUnit c → ∃ A ∈ 𝒜, hπ.mult (star A) (n + 4) = c)
    (hdvd : ∀ A ∈ 𝒜, star A ∣ B) (h𝒜 : ∀ A ∈ 𝒜, ¬ π ∣ A) (hB : ¬ star π ∣ B)
    {v : ℕ} {q₂ : GaussianInt} (hq₂ : ¬ star π ∣ q₂)
    {e' : ℂ} (he' : ‖e'‖ < 21 / 50 * ‖cellGen π ρ n α β‖) (l : ZMod (p ^ n)) :
    ∃ A ∈ 𝒜, hπ.label ρ n α β (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ (v + (n - α + 4)) *
        ((A : ℂ) / ((star A : GaussianInt) : ℂ)) *
        ((((star π) ^ v * B * (star ρ) ^ β * q₂ : GaussianInt) : ℂ) + e')) = l := by
  set D := n - α + 4 with hD
  set g := cellGen π ρ n α β with hg
  have hπ0 := hπ.toComplex_ne_zero
  have hπb0 := hπ.toComplex_star_ne_zero
  have hg0 : g ≠ 0 := by
    simp only [hg, cellGen]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hπb0) (pow_ne_zero _ hρ0)) (pow_ne_zero _ hπ0)
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg0
  have hk0 : 0 < n + 4 := by omega
  -- the target cell
  set m₀ : GaussianInt := ((l.val : ℕ) : GaussianInt) with hm₀
  set c₀ : ℂ := g * ((m₀ : ℂ) + (1 + I) / 2) with hc₀
  set h : ℂ := ((star π : GaussianInt) : ℂ) ^ D / ((star ρ : GaussianInt) : ℂ) ^ β with hh
  have hh0 : h ≠ 0 := div_ne_zero (pow_ne_zero _ hπb0) (pow_ne_zero _ hρ0)
  have hhg : ‖h‖ * ‖g‖ = (p : ℝ) ^ 2 := hπ.norm_shift_mul_norm_cellGen hρ0 (by omega)
  obtain ⟨W, hW, hWnear⟩ := hπ.exists_coprime_near (h * c₀)
  -- units modulo `π̄^(n+4)`
  set W₀ : GaussianInt := π ^ (v + D) * B * q₂ with hW₀
  have hW₀u : IsUnit (hπ.ψbar (n + 4) W₀) := by
    rw [hπ.isUnit_ψbar_iff hk0]
    intro hdvd'
    have hprime : Prime (star π) := hπ.prime_star_π
    rcases hprime.dvd_or_dvd hdvd' with h1 | h1
    · rcases hprime.dvd_or_dvd h1 with h2 | h2
      · exact hπ.not_star_dvd_self (hprime.dvd_of_dvd_pow h2)
      · exact hB h2
    · exact hq₂ h1
  have hWu : IsUnit (hπ.ψbar (n + 4) W) := (hπ.isUnit_ψbar_iff hk0 W).mpr hW
  set c := hπ.ψbar (n + 4) W * (hπ.ψbar (n + 4) W₀)⁻¹ with hc
  have hinv : hπ.ψbar (n + 4) W₀ * (hπ.ψbar (n + 4) W₀)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hW₀u
  have hcu : IsUnit c := hWu.mul (IsUnit.of_mul_eq_one_right _ hinv)
  obtain ⟨A, hA𝒜, hAeq⟩ := hcover c hcu
  refine ⟨A, hA𝒜, ?_⟩
  obtain ⟨C, hC⟩ := hdvd A hA𝒜
  have hAπ : ¬ π ∣ A := h𝒜 A hA𝒜
  have hA0' : A ≠ 0 := fun h0 => hAπ (h0 ▸ dvd_zero π)
  have hA0 : ((star A : GaussianInt) : ℂ) ≠ 0 :=
    toComplex_ne_zero_of_norm (by
      rw [Zsqrtd.norm_conj]
      exact fun h0 => hA0' (GaussianInt.norm_eq_zero.mp h0))
  -- the orbit point `W_A`
  set WA : GaussianInt := π ^ (v + D) * A * C * q₂ with hWA
  have hAu : IsUnit (hπ.ψ (n + 4) A) := (hπ.isUnit_ψ_iff hk0 A).mpr hAπ
  have hAinv : hπ.ψ (n + 4) A * (hπ.ψ (n + 4) A)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hAu
  have hψWA : hπ.ψbar (n + 4) WA = hπ.ψbar (n + 4) W₀ * hπ.mult (star A) (n + 4) := by
    rw [hWA, hW₀, hC]
    simp only [ψbar_apply, mult, star_star, map_mul, map_pow]
    linear_combination (-(hπ.ψ (n + 4) (star π) ^ (v + D) * hπ.ψ (n + 4) (star A) *
      hπ.ψ (n + 4) (star C) * hπ.ψ (n + 4) (star q₂))) * hAinv
  have hdiff : star π ^ (n + 4) ∣ WA - W := by
    rw [← hπ.ψbar_eq_zero_iff, map_sub, hψWA, hAeq, hc]
    rw [mul_comm (hπ.ψbar (n + 4) W), ← mul_assoc, hinv, one_mul, sub_self]
  obtain ⟨Δ, hΔ⟩ := hdiff
  -- complex bookkeeping
  set σA : ℂ := ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ (v + D) *
    ((A : ℂ) / ((star A : GaussianInt) : ℂ)) with hσA
  have hcx : σA * (((star π) ^ v * B * (star ρ) ^ β * q₂ : GaussianInt) : ℂ) = (WA : ℂ) / h := by
    rw [hC]
    simp only [hσA, hWA, hh, map_mul, map_pow, div_pow]
    field_simp
    ring
  have hWA' : (WA : ℂ) = (W : ℂ) + ((star π : GaussianInt) : ℂ) ^ (n + 4) * (Δ : ℂ) := by
    have hWW : WA = W + star π ^ (n + 4) * Δ := by rw [← hΔ]; ring
    rw [hWW, map_add, map_mul, map_pow]
  have hgπ : ((star π : GaussianInt) : ℂ) ^ (n + 4) / h = g * (π : ℂ) ^ n := by
    simp only [hh, hg, cellGen]
    have hn4 : n + 4 = α + D := by omega
    rw [hn4, pow_add]
    field_simp
  have hkey : σA * ((((star π) ^ v * B * (star ρ) ^ β * q₂ : GaussianInt) : ℂ) + e') =
      (W : ℂ) / h + g * (π : ℂ) ^ n * Δ + σA * e' := by
    rw [mul_add, hcx, hWA', ← hgπ]
    ring
  set u : ℂ := ((W : ℂ) / h - c₀ + σA * e') / g with hu
  have hy : (σA * ((((star π) ^ v * B * (star ρ) ^ β * q₂ : GaussianInt) : ℂ) + e')) / g =
      (((m₀ + π ^ n * Δ : GaussianInt) : ℂ)) + ((1 + I) / 2 + u) := by
    rw [hkey, hu, hc₀]
    simp only [map_add, map_mul, map_pow]
    field_simp
    ring
  have hunorm : ‖u‖ < 1 / 2 := by
    have hAn : ‖((star A : GaussianInt) : ℂ)‖ = ‖(A : ℂ)‖ := by
      rw [GaussianInt.toComplex_star, Complex.norm_conj]
    have hA0'' : ‖(A : ℂ)‖ ≠ 0 := by rw [← hAn]; exact norm_ne_zero_iff.mpr hA0
    have hτ : ‖σA * e'‖ = ‖e'‖ := by
      rw [hσA, norm_mul, norm_mul, _root_.norm_pow, hπ.norm_sigma, norm_div, hAn,
        div_self hA0'']
      simp
    have hW1 : ‖(W : ℂ) / h - c₀‖ = ‖h * c₀ - W‖ / ‖h‖ := by
      rw [norm_sub_rev (h * c₀), ← norm_div]; congr 1; field_simp
    have hhpos : 0 < ‖h‖ := norm_pos_iff.mpr hh0
    have hW2 : ‖(W : ℂ) / h - c₀‖ < 2 / 25 * ‖g‖ := by
      rw [hW1, div_lt_iff₀ hhpos]
      have hp2 : (25 : ℝ) ≤ (p : ℝ) ^ 2 := by
        have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
        nlinarith
      nlinarith [hhg]
    rw [hu, norm_div, div_lt_iff₀ hgpos]
    calc ‖(W : ℂ) / h - c₀ + σA * e'‖ ≤ ‖(W : ℂ) / h - c₀‖ + ‖σA * e'‖ := norm_add_le _ _
      _ < 1 / 2 * ‖g‖ := by rw [hτ]; linarith
  simp only [label]
  rw [← hg, hy, gaussFloor_add_intCast, gaussFloor_half_add hunorm, add_zero, map_add,
    map_mul, hπ.ψ_pow_self, zero_mul, add_zero, hm₀, hπ.ψ_natCast_val]

/-- The common denominator of the digit family: `ρ̄^(p-2) ∏_{1 ≤ j < N} (1 - p^j i)^(p-1)`. -/
def digitDen (p N : ℕ) (ρ : GaussianInt) : GaussianInt :=
  star ρ ^ (p - 2) * ∏ j ∈ Ico 1 N, star (digitInt p j) ^ (p - 1)

omit hπ in
lemma star_dvd_digitDen {N : ℕ} {ρ A : GaussianInt} (hA : A ∈ digitFamily p N ρ) :
    star A ∣ digitDen p N ρ := by
  obtain ⟨m, hm, d, hd, rfl⟩ := hA
  rw [star_mul', star_pow, digitDen]
  refine mul_dvd_mul (pow_dvd_pow _ (by omega)) ?_
  rw [star_prod]
  refine prod_dvd_prod_of_dvd _ _ fun j _ => ?_
  rw [star_pow]
  exact pow_dvd_pow _ (by have := hd j; omega)

lemma not_dvd_of_mem_digitFamily {N : ℕ} {ρ A : GaussianInt} (hρ1 : ¬ π ∣ ρ)
    (hA : A ∈ digitFamily p N ρ) : ¬ π ∣ A := by
  obtain ⟨m, -, d, -, rfl⟩ := hA
  intro h
  rcases hπ.prime_π.dvd_or_dvd h with h1 | h1
  · exact hρ1 (hπ.prime_π.dvd_of_dvd_pow h1)
  · rw [hπ.prime_π.dvd_finsetProd_iff] at h1
    obtain ⟨j, hj, hdvd⟩ := h1
    exact hπ.not_dvd_digitInt (mem_Ico.mp hj).1 (hπ.prime_π.dvd_of_dvd_pow hdvd)

lemma not_star_dvd_digitDen {N : ℕ} {ρ : GaussianInt} (hρ1 : ¬ π ∣ ρ) :
    ¬ star π ∣ digitDen p N ρ := by
  have hprime := hπ.prime_star_π
  -- `π̄ ∣ x̄ ↔ π ∣ x`
  have hconj : ∀ x : GaussianInt, star π ∣ star x → π ∣ x := fun x ⟨y, hy⟩ =>
    ⟨star y, by rw [← star_star x, hy, star_mul', star_star]⟩
  intro h
  rcases hprime.dvd_or_dvd h with h1 | h1
  · exact hρ1 (hconj ρ (hprime.dvd_of_dvd_pow h1))
  · rw [hprime.dvd_finsetProd_iff] at h1
    obtain ⟨j, hj, hdvd⟩ := h1
    exact hπ.not_dvd_digitInt (mem_Ico.mp hj).1 (hconj _ (hprime.dvd_of_dvd_pow hdvd))

/-- **Step A with digit rotations.** The single-exponential replacement of `stepA`: every
residue `l` is the label of `σʲ (A/Ā) (q + e')` for some `A` in the digit family, where now
`q = π̄^v · digitDen · ρ̄^β · q₂`. The denominator `digitDen p (n+4) ρ` replaces `ρ̄^(E-β)` with
`E ≥ (p - 1) p^(n+3)`. -/
theorem stepA_digit (hp5 : 5 ≤ p) {ρ : GaussianInt} (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ)
    (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0) {n α β : ℕ} (hα : α ≤ n)
    (hord : orderOf (hπ.mult (star ρ) (n + 4)) = (p - 1) * p ^ (n + 3))
    {v : ℕ} {q₂ : GaussianInt} (hq₂ : ¬ star π ∣ q₂)
    {e' : ℂ} (he' : ‖e'‖ < 21 / 50 * ‖cellGen π ρ n α β‖) (l : ZMod (p ^ n)) :
    ∃ A ∈ digitFamily p (n + 4) ρ,
      hπ.label ρ n α β (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ (v + (n - α + 4)) *
        ((A : ℂ) / ((star A : GaussianInt) : ℂ)) *
        ((((star π) ^ v * digitDen p (n + 4) ρ * (star ρ) ^ β * q₂ : GaussianInt) : ℂ) + e')) =
        l := by
  have hp2 : p ≠ 2 := by omega
  refine hπ.stepA_family hp5 hρ0 hα (digitFamily p (n + 4) ρ) (digitDen p (n + 4) ρ)
    (fun c hc => hπ.exists_digit_multiplier hp2 (by omega) hρ1 hρ2
      (by rw [hord]; congr 2) c hc)
    (fun A hA => star_dvd_digitDen hA) (fun A hA => hπ.not_dvd_of_mem_digitFamily hρ1 hA)
    (hπ.not_star_dvd_digitDen hρ1) hq₂ he' l

end DigitPrime

end Green41Proof
