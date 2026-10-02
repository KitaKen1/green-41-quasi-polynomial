import Green41SingleExponential.StepAFamily

/-!
# Cells with a general denominator

The cell generator of `Green41DoubleExponentialFC` is `g = π̄^α ρ̄^β / πⁿ`. The factor `ρ̄^β` is
there so that the rotations `(ρ/ρ̄)^w`, `w ≤ β`, used by the discrete core keep the cell
lattice. For other families of rotations `C/C̄` we only need `C̄` to divide the denominator.
This file redoes the cell machinery with `ρ̄^β` replaced by an arbitrary Gaussian integer `D`:

* `cellGenD π D n α = π̄^α D / πⁿ` and the labels `labelD`;
* the label count `pow_le_four_mul_card_sqD`;
* Step A for a multiplier family, `stepA_familyD`;
* the stripe value of a label after a rotation `C/C̄` with `C̄ ∣ D`, `re_label_formulaD`.
-/

namespace Green41Proof

open Green41

open Complex ComplexConjugate Finset

/-- The cell generator `g = π̄^α D / πⁿ`. -/
noncomputable def cellGenD (π D : GaussianInt) (n α : ℕ) : ℂ :=
  ((star π : GaussianInt) : ℂ) ^ α * (D : ℂ) / (π : ℂ) ^ n

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)

/-- The label `ψₙ(⌊x/g⌋)` of `x ∈ ℂ` for the cell `g = cellGenD π D n α`. -/
noncomputable def labelD (D : GaussianInt) (n α : ℕ) (x : ℂ) : ZMod (p ^ n) :=
  hπ.ψ n (gaussFloor (x / cellGenD π D n α))

include hπ in
/-- If every residue is the label of a difference of two points of `Z`, then
`pⁿ ≤ 4 · |labels(Z)|²`. -/
lemma pow_le_four_mul_card_sqD (D : GaussianInt) (n α : ℕ) (Z : Finset ℂ)
    (hall : ∀ l : ZMod (p ^ n), ∃ x ∈ Z, ∃ x' ∈ Z, hπ.labelD D n α (x - x') = l) :
    p ^ n ≤ 4 * ((Z.image (hπ.labelD D n α)).card) ^ 2 := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  set Y := Z.image (hπ.labelD D n α)
  set S := (Y ×ˢ Y) ×ˢ corrections
  let f : (ZMod (p ^ n) × ZMod (p ^ n)) × GaussianInt → ZMod (p ^ n) :=
    fun t => t.1.1 - t.1.2 - hπ.ψ n t.2
  have hsub : (Finset.univ : Finset (ZMod (p ^ n))) ⊆ S.image f := by
    intro l _
    obtain ⟨x, hx, x', hx', hl⟩ := hall l
    obtain ⟨d, hd, hfl⟩ := gaussFloor_sub (x / cellGenD π D n α) (x' / cellGenD π D n α)
    rw [Finset.mem_image]
    refine ⟨((hπ.labelD D n α x, hπ.labelD D n α x'), d), ?_, ?_⟩
    · simp only [S, Y, Finset.mem_product, Finset.mem_image]
      exact ⟨⟨⟨x, hx, rfl⟩, ⟨x', hx', rfl⟩⟩, hd⟩
    · rw [← hl]
      simp only [f, labelD, sub_div, hfl, map_sub]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at h1
  calc p ^ n ≤ (S.image f).card := h1
    _ ≤ S.card := Finset.card_image_le
    _ = 4 * Y.card ^ 2 := by
      simp only [S, Finset.card_product, card_corrections]; ring

include hπ

lemma cellGenD_ne_zero {D : GaussianInt} (hD0 : (D : ℂ) ≠ 0) (n α : ℕ) :
    cellGenD π D n α ≠ 0 := by
  unfold cellGenD
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hπ.toComplex_star_ne_zero) hD0)
    (pow_ne_zero _ hπ.toComplex_ne_zero)

/-- `‖π̄^E / D‖ · ‖g‖ = p²` when `E + α = n + 4`. -/
lemma norm_shift_mul_norm_cellGenD {D : GaussianInt} (hD0 : (D : ℂ) ≠ 0)
    {n α E : ℕ} (hE : E + α = n + 4) :
    ‖((star π : GaussianInt) : ℂ) ^ E / (D : ℂ)‖ * ‖cellGenD π D n α‖ = (p : ℝ) ^ 2 := by
  have hsp : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hπ.prime.pos)).ne'
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (by positivity)
  have h1 : ‖((star π : GaussianInt) : ℂ) ^ E‖ = Real.sqrt p ^ E := by
    rw [_root_.norm_pow, hπ.norm_toComplex_star_π]
  have h2 : ‖((star π : GaussianInt) : ℂ) ^ α‖ = Real.sqrt p ^ α := by
    rw [_root_.norm_pow, hπ.norm_toComplex_star_π]
  have h3 : ‖(π : ℂ) ^ n‖ = Real.sqrt p ^ n := by rw [_root_.norm_pow, hπ.norm_toComplex_π]
  set X := ‖(D : ℂ)‖ with hX
  have hX0 : X ≠ 0 := by rw [hX]; exact norm_ne_zero_iff.mpr hD0
  have hsn : Real.sqrt p ^ n ≠ 0 := pow_ne_zero _ hsp
  unfold cellGenD
  rw [norm_div, norm_div, norm_mul, h1, h2, h3, ← hX]
  calc Real.sqrt p ^ E / X * (Real.sqrt p ^ α * X / Real.sqrt p ^ n)
      = Real.sqrt p ^ (E + α) / Real.sqrt p ^ n := by rw [pow_add]; field_simp
    _ = (p : ℝ) ^ 2 := by
      rw [hE, pow_add, show Real.sqrt p ^ 4 = (Real.sqrt p ^ 2) ^ 2 by ring, hsq]
      field_simp

/-- **Step A for a family, general cell.** If the multipliers of `𝒜` reach every unit modulo
`π̄^(n+4)` and all conjugates `Ā` divide `B`, then every residue `l` is the label of
`σʲ (A/Ā) (q + e')` for some `A ∈ 𝒜`, where `q = π̄^v B D q₂` and `j = v + (n - α + 4)`. -/
theorem stepA_familyD (hp5 : 5 ≤ p) {D : GaussianInt} (hD0 : (D : ℂ) ≠ 0)
    {n α : ℕ} (hα : α ≤ n) (𝒜 : Set GaussianInt) (B : GaussianInt)
    (hcover : ∀ c : ZMod (p ^ (n + 4)), IsUnit c → ∃ A ∈ 𝒜, hπ.mult (star A) (n + 4) = c)
    (hdvd : ∀ A ∈ 𝒜, star A ∣ B) (h𝒜 : ∀ A ∈ 𝒜, ¬ π ∣ A) (hB : ¬ star π ∣ B)
    {v : ℕ} {q₂ : GaussianInt} (hq₂ : ¬ star π ∣ q₂)
    {e' : ℂ} (he' : ‖e'‖ < 21 / 50 * ‖cellGenD π D n α‖) (l : ZMod (p ^ n)) :
    ∃ A ∈ 𝒜, hπ.labelD D n α (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ (v + (n - α + 4)) *
        ((A : ℂ) / ((star A : GaussianInt) : ℂ)) *
        ((((star π) ^ v * B * D * q₂ : GaussianInt) : ℂ) + e')) = l := by
  set E := n - α + 4 with hE
  set g := cellGenD π D n α with hg
  have hπ0 := hπ.toComplex_ne_zero
  have hπb0 := hπ.toComplex_star_ne_zero
  have hg0 : g ≠ 0 := hπ.cellGenD_ne_zero hD0 n α
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg0
  have hk0 : 0 < n + 4 := by omega
  -- the target cell
  set m₀ : GaussianInt := ((l.val : ℕ) : GaussianInt) with hm₀
  set c₀ : ℂ := g * ((m₀ : ℂ) + (1 + I) / 2) with hc₀
  set h : ℂ := ((star π : GaussianInt) : ℂ) ^ E / (D : ℂ) with hh
  have hh0 : h ≠ 0 := div_ne_zero (pow_ne_zero _ hπb0) hD0
  have hhg : ‖h‖ * ‖g‖ = (p : ℝ) ^ 2 := hπ.norm_shift_mul_norm_cellGenD hD0 (by omega)
  obtain ⟨W, hW, hWnear⟩ := hπ.exists_coprime_near (h * c₀)
  -- units modulo `π̄^(n+4)`
  set W₀ : GaussianInt := π ^ (v + E) * B * q₂ with hW₀
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
  set WA : GaussianInt := π ^ (v + E) * A * C * q₂ with hWA
  have hAu : IsUnit (hπ.ψ (n + 4) A) := (hπ.isUnit_ψ_iff hk0 A).mpr hAπ
  have hAinv : hπ.ψ (n + 4) A * (hπ.ψ (n + 4) A)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hAu
  have hψWA : hπ.ψbar (n + 4) WA = hπ.ψbar (n + 4) W₀ * hπ.mult (star A) (n + 4) := by
    rw [hWA, hW₀, hC]
    simp only [ψbar_apply, mult, star_star, map_mul, map_pow]
    linear_combination (-(hπ.ψ (n + 4) (star π) ^ (v + E) * hπ.ψ (n + 4) (star A) *
      hπ.ψ (n + 4) (star C) * hπ.ψ (n + 4) (star q₂))) * hAinv
  have hdiff : star π ^ (n + 4) ∣ WA - W := by
    rw [← hπ.ψbar_eq_zero_iff, map_sub, hψWA, hAeq, hc]
    rw [mul_comm (hπ.ψbar (n + 4) W), ← mul_assoc, hinv, one_mul, sub_self]
  obtain ⟨Δ, hΔ⟩ := hdiff
  -- complex bookkeeping
  set σA : ℂ := ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ (v + E) *
    ((A : ℂ) / ((star A : GaussianInt) : ℂ)) with hσA
  have hcx : σA * (((star π) ^ v * B * D * q₂ : GaussianInt) : ℂ) = (WA : ℂ) / h := by
    rw [hC]
    simp only [hσA, hWA, hh, map_mul, map_pow, div_pow]
    field_simp
    ring
  have hWA' : (WA : ℂ) = (W : ℂ) + ((star π : GaussianInt) : ℂ) ^ (n + 4) * (Δ : ℂ) := by
    have hWW : WA = W + star π ^ (n + 4) * Δ := by rw [← hΔ]; ring
    rw [hWW, map_add, map_mul, map_pow]
  have hgπ : ((star π : GaussianInt) : ℂ) ^ (n + 4) / h = g * (π : ℂ) ^ n := by
    simp only [hh, hg, cellGenD]
    have hn4 : n + 4 = α + E := by omega
    rw [hn4, pow_add]
    field_simp
  have hkey : σA * ((((star π) ^ v * B * D * q₂ : GaussianInt) : ℂ) + e') =
      (W : ℂ) / h + g * (π : ℂ) ^ n * Δ + σA * e' := by
    rw [mul_add, hcx, hWA', ← hgπ]
    ring
  set u : ℂ := ((W : ℂ) / h - c₀ + σA * e') / g with hu
  have hy : (σA * ((((star π) ^ v * B * D * q₂ : GaussianInt) : ℂ) + e')) / g =
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
  simp only [labelD]
  rw [← hg, hy, gaussFloor_add_intCast, gaussFloor_half_add hunorm, add_zero, map_add,
    map_mul, hπ.ψ_pow_self, zero_mul, add_zero, hm₀, hπ.ψ_natCast_val]

/-- The unit factor `Xⱼ = Re(πⁿ) ψ(π̄)^(-j) ψ(π̄)^(α-j) ψ(D)` of the general label formula. -/
noncomputable def XfacD (D : GaussianInt) (n α j : ℕ) : ZMod (p ^ n) :=
  (((π ^ n).re : ℤ) : ZMod (p ^ n)) * ((hπ.ψ n (star π))⁻¹) ^ j * hπ.ψ n (star π) ^ (α - j) *
    hπ.ψ n D

lemma isUnit_XfacD {D : GaussianInt} (hD : ¬ π ∣ D) {n α j : ℕ} (hn : 0 < n) :
    IsUnit (hπ.XfacD D n α j) := by
  unfold XfacD
  have h1 := hπ.isUnit_re n
  have h2 : IsUnit (hπ.ψ n (star π)) := (hπ.isUnit_ψ_iff hn _).mpr hπ.not_dvd_star
  have h2' : IsUnit ((hπ.ψ n (star π))⁻¹) :=
    IsUnit.of_mul_eq_one_right _ (ZMod.mul_inv_of_unit _ h2)
  have h3 : IsUnit (hπ.ψ n D) := (hπ.isUnit_ψ_iff hn _).mpr hD
  exact ((h1.mul (h2'.pow j)).mul (h2.pow _)).mul h3

/-- **The stripe value of a label, general cell.** If `C̄ ∣ D`, then
`Re(σʲ (C/C̄) g m) ≡ val(Xⱼ mult(C) ψₙ(m)) / p^(n-j) (mod 1)`. -/
lemma re_label_formulaD {D C : GaussianInt} (hC : ¬ π ∣ star C) (hCD : star C ∣ D)
    {n α j : ℕ} (hn : 0 < n) (hj : j ≤ α) (hjn : j ≤ n) (m : GaussianInt) :
    ∃ k : ℤ, (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ j *
        ((C : ℂ) / ((star C : GaussianInt) : ℂ)) * (cellGenD π D n α * m)).re =
      (((hπ.XfacD D n α j * hπ.mult C n * hπ.ψ n m).val : ℕ) : ℝ) / (p : ℝ) ^ (n - j) + k := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  obtain ⟨F, hF⟩ := hCD
  have hC0' : star C ≠ 0 := fun h0 => hC (h0 ▸ dvd_zero π)
  have hC0 : ((star C : GaussianInt) : ℂ) ≠ 0 := by
    rw [Ne, GaussianInt.toComplex_eq_zero]; exact hC0'
  set z : GaussianInt := π ^ j * star π ^ (α - j) * C * F * m with hz
  have hπ0 := hπ.toComplex_ne_zero
  have hπb0 := hπ.toComplex_star_ne_zero
  have hcx : ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ j *
      ((C : ℂ) / ((star C : GaussianInt) : ℂ)) * (cellGenD π D n α * m) =
      (z : ℂ) / (π : ℂ) ^ n := by
    simp only [hz, cellGenD, hF, map_mul, map_pow, div_pow]
    obtain ⟨a, rfl⟩ : ∃ a, α = a + j := ⟨α - j, by omega⟩
    rw [Nat.add_sub_cancel]
    field_simp
    ring
  obtain ⟨k₁, hk₁⟩ := hπ.re_div_pow n z
  have hunit : hπ.ψ n (star π) * (hπ.ψ n (star π))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ ((hπ.isUnit_ψ_iff hn _).mpr hπ.not_dvd_star)
  have hψπ : hπ.ψ n π = (p : ZMod (p ^ n)) * (hπ.ψ n (star π))⁻¹ := by
    rw [← hπ.ψ_mul_star n, mul_assoc, hunit, mul_one]
  have hψC : hπ.ψ n C = hπ.mult C n * hπ.ψ n (star C) := (hπ.mult_mul hn hC).symm
  have hX : (((π ^ n).re : ℤ) : ZMod (p ^ n)) * hπ.ψ n z =
      (p : ZMod (p ^ n)) ^ j * (hπ.XfacD D n α j * hπ.mult C n * hπ.ψ n m) := by
    simp only [hz, XfacD, hF, map_mul, map_pow, hψπ, hψC]
    ring
  obtain ⟨k₂, hk₂⟩ := val_pow_mul_div hπ.prime.pos hjn
    (hπ.XfacD D n α j * hπ.mult C n * hπ.ψ n m)
  refine ⟨k₁ + k₂, ?_⟩
  rw [hcx, hk₁, hX, hk₂]
  push_cast; ring

end DigitPrime

end Green41Proof
