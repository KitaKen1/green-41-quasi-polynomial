import Green41QuasiPolynomial.DiscreteGen
import Green41QuasiPolynomial.CellGen
import Green41QuasiPolynomial.DigitCast

/-!
# Minor arcs with digit rotations on both sides

`minor_arc_core_digit` (single exponential) still runs the discrete core over the powers
`(ρ/ρ̄)^w`, `w < S = (p - 1) p^(ℓ-1)`, which forces the cell generator to carry `ρ̄^β` with
`β ≥ S`; since `S` is polynomial in `1/ε`, so are `A` and `n`, and the digit denominator of
Step A has size `exp(poly(1/ε))`.

Here the discrete core runs over the inverse digit rotations `Ā/A`, `A` in the digit family at
level `ℓ`: one for each unit modulo `p^ℓ` (`exists_digit_multiplier_cast`). Their numerators `Ā`
have conjugates `A` dividing `D = conj(digitDen p ℓ ρ)`, of size `p^{O(ℓ²)}`, and the cell
generator becomes `cellGenD π D n α`. Step A is `stepA_familyD` with the digit family at level
`n + 4`. The rotation found is `σᵃ τᵇ μ ν` with `μ` a digit rotation at level `n + 4`, `ν` an
inverse digit rotation at level `ℓ`, and `b ≤ N₀`.
-/

namespace Green41Proof

open Green41

open Complex ComplexConjugate Finset

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

/-- **Minor arcs with digit rotations on both sides.** -/
theorem minor_arc_core_quasi (hp5 : 5 ≤ p) {ρ : GaussianInt}
    (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ)
    {n α A L ℓ H : ℕ} (hL : 0 < L) (hℓ : ℓ = 4 * L) (hnA : n = 8 * (A + ℓ)) (hα : α = n - A)
    (hordA : orderOf (hπ.mult (star ρ) (n + 4)) = (p - 1) * p ^ (n + 3))
    (hordC : orderOf (((hπ.mult (star ρ) n).val : ℕ) : ZMod (p ^ ℓ)) = (p - 1) * p ^ (ℓ - 1))
    {ε : ℝ} (hε : 0 < ε) (hH : 2 ≤ (H : ℝ) * ε ^ 2) (hHL : 25 * H ^ 3 < 4 * p ^ L)
    (hg : Real.sqrt 2 * ‖cellGenD π (star (digitDen p ℓ ρ)) n α‖ ≤ ε / 2)
    (w : ℂ) {N₀ a₁ b₁ a₂ b₂ v : ℕ} (ha₁ : a₁ ≤ N₀) (hb₁ : b₁ ≤ N₀) (ha₂ : a₂ ≤ N₀)
    (hb₂ : b₂ ≤ N₀) {q₂ : GaussianInt} (hq₂ : ¬ star π ∣ q₂)
    (he' : ‖(((star π) ^ v * digitDen p (n + 4) ρ * star (digitDen p ℓ ρ) * q₂ : GaussianInt) :
          ℂ) -
        (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
            ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
          ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
            ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ <
        21 / 50 * ‖cellGenD π (star (digitDen p ℓ ρ)) n α‖) :
    ∃ a b : ℕ, a ≤ N₀ + v + (A + 4) + n ∧ b ≤ N₀ ∧ ∃ μ ∈ digitRotFinset p (n + 4) ρ,
      ∃ ν ∈ digitRotInvFinset p ℓ ρ, ∃ k : ℤ,
        |(((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b * μ * ν * w).re - k| < ε := by
  set σ : ℂ := (π : ℂ) / ((star π : GaussianInt) : ℂ) with hσ
  set τ : ℂ := (ρ : ℂ) / ((star ρ : GaussianInt) : ℂ) with hτ
  set Dc : GaussianInt := star (digitDen p ℓ ρ) with hDc
  set g := cellGenD π Dc n α with hg_def
  set j := v + (n - α + 4) with hj
  set q : ℂ := (((star π) ^ v * digitDen p (n + 4) ρ * Dc * q₂ : GaussianInt) : ℂ) with hq
  set r : ℂ := σ ^ a₁ * τ ^ b₁ - σ ^ a₂ * τ ^ b₂ with hr
  set e' : ℂ := r * w - q with he'_def
  have he'n : ‖e'‖ < 21 / 50 * ‖g‖ := by rw [he'_def, norm_sub_rev]; exact he'
  have hrw : r * w = q + e' := by rw [he'_def]; ring
  have hn0 : 0 < n := by omega
  have hαn : α ≤ n := by omega
  have hp0 : 0 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hDcπ : ¬ π ∣ Dc := hπ.not_dvd_star_digitDen hρ1
  have hDc0 : (Dc : ℂ) ≠ 0 := by
    rw [Ne, GaussianInt.toComplex_eq_zero]
    exact fun h0 => hDcπ (h0 ▸ dvd_zero π)
  -- Step A
  have hA : ∀ l : ZMod (p ^ n), ∃ Aμ ∈ digitFamily p (n + 4) ρ,
      hπ.labelD Dc n α (σ ^ j * ((Aμ : ℂ) / ((star Aμ : GaussianInt) : ℂ)) * (q + e')) = l :=
    fun l => hπ.stepA_familyD hp5 hDc0 hαn (digitFamily p (n + 4) ρ) (digitDen p (n + 4) ρ)
      (fun c hc => hπ.exists_digit_multiplier hp2 (by omega) hρ1 hρ2
        (by rw [hordA]; congr 2) c hc)
      (fun A hA => star_dvd_digitDen hA) (fun A hA => hπ.not_dvd_of_mem_digitFamily hρ1 hA)
      (hπ.not_star_dvd_digitDen hρ1) hq₂ he'n l
  -- the orbit
  set Mu : Finset ℂ := digitRotFinset p (n + 4) ρ with hMu
  set Z : Finset ℂ := (((range (N₀ + j + 1)) ×ˢ (range (N₀ + 1))) ×ˢ Mu).image
    (fun abμ => σ ^ abμ.1.1 * τ ^ abμ.1.2 * abμ.2 * w) with hZ
  have hmemZ : ∀ a b μ, a ≤ N₀ + j → b ≤ N₀ → μ ∈ Mu → σ ^ a * τ ^ b * μ * w ∈ Z := by
    intro a b μ ha hb hμ
    exact Finset.mem_image.mpr ⟨((a, b), μ), Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show a < N₀ + j + 1 by omega),
        Finset.mem_range.mpr (show b < N₀ + 1 by omega)⟩, hμ⟩, rfl⟩
  have hall : ∀ l : ZMod (p ^ n), ∃ x ∈ Z, ∃ x' ∈ Z, hπ.labelD Dc n α (x - x') = l := by
    intro l
    obtain ⟨Aμ, hAμ, hl⟩ := hA l
    have hμ : (Aμ : ℂ) / ((star Aμ : GaussianInt) : ℂ) ∈ Mu := mem_digitRotFinset_of_mem hAμ
    refine ⟨σ ^ (j + a₁) * τ ^ b₁ * ((Aμ : ℂ) / ((star Aμ : GaussianInt) : ℂ)) * w,
      hmemZ _ _ _ (by omega) (by omega) hμ,
      σ ^ (j + a₂) * τ ^ b₂ * ((Aμ : ℂ) / ((star Aμ : GaussianInt) : ℂ)) * w,
      hmemZ _ _ _ (by omega) (by omega) hμ, ?_⟩
    rw [← hl, ← hrw]
    congr 1
    rw [hr]; ring
  -- counting
  have hcount := hπ.pow_le_four_mul_card_sqD Dc n α Z hall
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  set Yl := Z.image (hπ.labelD Dc n α) with hYl
  set Yn : Finset ℕ := Yl.image ZMod.val with hYn
  have hYncard : Yn.card = Yl.card := Finset.card_image_of_injective _ (ZMod.val_injective (p ^ n))
  have hYnlt : ∀ y ∈ Yn, y < p ^ n := by
    intro y hy; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy; exact ZMod.val_lt x
  -- digit pigeonhole
  obtain ⟨s, hs1, hs2, lam, hfib⟩ := digit_pigeonhole hp5 hL (by rw [hnA, hℓ]) Yn hYnlt
    (by rw [hYncard]; exact hcount)
  rw [← hℓ] at hs1 hfib
  set F := digitFiber p s ℓ lam Yn with hF
  set j' := n - s with hj'
  set X := hπ.XfacD Dc n α j' with hXdef
  have hXu : IsUnit X := hπ.isUnit_XfacD hDcπ hn0
  have hXc : Nat.Coprime X.val p := hπ.coprime_val_of_isUnit hn0 hXu
  have hX0 : X.val ≠ 0 := by
    intro h0; rw [h0, Nat.coprime_zero_left] at hXc; omega
  have hd : p ^ (s - ℓ) ∣ p ^ s := pow_dvd_pow p (Nat.sub_le s ℓ)
  have hFmem : ∀ r ∈ F, ∃ y ∈ Yn, y % p ^ (s - ℓ) = lam ∧ r = y % p ^ s := by
    intro r hr
    simp only [hF, digitFiber, Finset.mem_image, Finset.mem_filter] at hr
    obtain ⟨y, ⟨hy, hyl⟩, rfl⟩ := hr
    exact ⟨y, hy, hyl, rfl⟩
  have hzlt : ∀ r ∈ F, r / p ^ (s - ℓ) < p ^ ℓ := by
    intro r hr
    obtain ⟨y, _, _, rfl⟩ := hFmem r hr
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' (by omega : ℓ ≤ s)]
    exact Nat.mod_lt _ (by positivity)
  have hrinj : Set.InjOn (fun r => r / p ^ (s - ℓ)) F := by
    intro r₁ h₁ r₂ h₂ h
    obtain ⟨y₁, _, hy₁, rfl⟩ := hFmem r₁ h₁
    obtain ⟨y₂, _, hy₂, rfl⟩ := hFmem r₂ h₂
    have e1 := Nat.mod_add_div (y₁ % p ^ s) (p ^ (s - ℓ))
    have e2 := Nat.mod_add_div (y₂ % p ^ s) (p ^ (s - ℓ))
    rw [Nat.mod_mod_of_dvd _ hd, hy₁] at e1
    rw [Nat.mod_mod_of_dvd _ hd, hy₂] at e2
    simp only at h
    rw [← e1, ← e2, h]
  set Yd : Finset ℕ := F.image (fun r => X.val * (r / p ^ (s - ℓ))) with hYd
  have hYdinj : Set.InjOn (fun r => X.val * (r / p ^ (s - ℓ))) F := by
    intro r₁ h₁ r₂ h₂ h
    apply hrinj h₁ h₂
    simp only at h ⊢
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hX0) h
  have hYdcard : Yd.card = F.card := Finset.card_image_of_injOn hYdinj
  have hYdmod : Set.InjOn (· % p ^ ℓ) Yd := by
    intro y₁ h₁ y₂ h₂ h
    obtain ⟨r₁, hr₁, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Finset.mem_image.mp h₂
    simp only at h ⊢
    rw [mul_mod_inj hXc (hzlt r₁ hr₁) (hzlt r₂ hr₂) h]
  -- the discrete-core family: one inverse digit rotation for each unit modulo `p^ℓ`
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓn : ℓ ≤ n := by omega
  have : NeZero (p ^ ℓ) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  have hex : ∀ u : (ZMod (p ^ ℓ))ˣ, ∃ A ∈ digitFamily p ℓ ρ,
      (((hπ.mult (star A) n).val : ℕ) : ZMod (p ^ ℓ)) = (u : ZMod (p ^ ℓ)) :=
    fun u => hπ.exists_digit_multiplier_cast hp2 hℓ1 hℓn hρ1 hρ2 hordC u u.isUnit
  choose Af hAf hAfeq using hex
  have hMinj : Set.InjOn (fun u => (((hπ.mult (star (Af u)) n).val : ℕ) : ZMod (p ^ ℓ)))
      ((Finset.univ : Finset (ZMod (p ^ ℓ))ˣ) : Set (ZMod (p ^ ℓ))ˣ) := by
    intro u₁ _ u₂ _ h
    simp only [hAfeq] at h
    exact Units.ext h
  have hIcard : 4 * p ^ ℓ ≤ 5 * (Finset.univ : Finset (ZMod (p ^ ℓ))ˣ).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_units_prime_pow hπ.prime hℓ1]
    have hpl : p ^ ℓ = p * p ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
    rw [hpl]
    have h4 : 4 * p ≤ 5 * (p - 1) := by omega
    calc 4 * (p * p ^ (ℓ - 1)) = (4 * p) * p ^ (ℓ - 1) := by ring
      _ ≤ (5 * (p - 1)) * p ^ (ℓ - 1) := Nat.mul_le_mul_right _ h4
      _ = 5 * ((p - 1) * p ^ (ℓ - 1)) := by ring
  have hYdbig : 25 * H ^ 3 < 4 * Yd.card := by rw [hYdcard]; omega
  set γ : ℝ := ((X.val * lam : ℕ) : ℝ) / (p : ℝ) ^ s with hγ
  obtain ⟨u', -, y', hy', hclose⟩ :=
    discrete_core_gen (N := p ^ ℓ) (by positivity) hε hH Finset.univ
      (fun u => (hπ.mult (star (Af u)) n).val) hMinj hIcard γ Yd hYdmod hYdbig
  -- unwind the chosen point
  obtain ⟨r₀, hr₀F, rfl⟩ := Finset.mem_image.mp hy'
  obtain ⟨yv, hyvYn, hyvl, rfl⟩ := hFmem r₀ hr₀F
  obtain ⟨yl, hylYl, rfl⟩ := Finset.mem_image.mp hyvYn
  obtain ⟨x, hxZ, rfl⟩ := Finset.mem_image.mp hylYl
  obtain ⟨⟨⟨a, b⟩, μ⟩, hab, rfl⟩ := Finset.mem_image.mp hxZ
  simp only [Finset.mem_product, Finset.mem_range] at hab
  obtain ⟨⟨ha', hb'⟩, hμ'⟩ := hab
  -- the stripe value of the label
  set m := gaussFloor ((σ ^ a * τ ^ b * μ * w) / g) with hm
  have hlabel : hπ.labelD Dc n α (σ ^ a * τ ^ b * μ * w) = hπ.ψ n m := rfl
  set C : GaussianInt := star (Af u') with hC
  have hCπ : ¬ π ∣ star C := by
    rw [hC, star_star]; exact hπ.not_dvd_of_mem_digitFamily hρ1 (hAf u')
  have hCD : star C ∣ Dc := by
    rw [hC, star_star]; exact dvd_star_digitDen (hAf u')
  obtain ⟨k₁, hk₁⟩ := hπ.re_label_formulaD hCπ hCD (n := n) (α := α) (j := j') hn0
    (by omega) (by omega) m
  have hnj : n - j' = s := by omega
  rw [hnj] at hk₁
  set B : ℕ := (hπ.mult (star (Af u')) n).val with hB
  have hval : (X * hπ.mult C n * hπ.ψ n m).val = X.val * B ^ 1 * (hπ.ψ n m).val % p ^ n := by
    rw [pow_one, ← ZMod.val_natCast]
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val, hB, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [hlabel] at hyvl
  obtain ⟨k₂, hk₂⟩ := frac_on_fiber hp0 (by omega : s ≤ n) (by omega : ℓ ≤ s) X.val B
    ((hπ.ψ n m).val) lam 1 hyvl
  -- the final exponents
  have hνmem : (C : ℂ) / ((star C : GaussianInt) : ℂ) ∈ digitRotInvFinset p ℓ ρ := by
    rw [hC, star_star]; exact mem_digitRotInvFinset_of_mem (hAf u')
  refine ⟨a + j', b, by omega, by omega, μ, hμ', (C : ℂ) / ((star C : GaussianInt) : ℂ),
    hνmem, ?_⟩
  set ν : ℂ := (C : ℂ) / ((star C : GaussianInt) : ℂ) with hν
  have hsplit : σ ^ (a + j') * τ ^ b * μ * ν * w =
      σ ^ j' * ν * (g * m) + σ ^ j' * ν * (σ ^ a * τ ^ b * μ * w - g * m) := by
    rw [pow_add]; ring
  have hg0 : g ≠ 0 := hπ.cellGenD_ne_zero hDc0 n α
  have hnear : ‖σ ^ a * τ ^ b * μ * w - g * m‖ < Real.sqrt 2 * ‖g‖ := by
    have : σ ^ a * τ ^ b * μ * w - g * m = g * ((σ ^ a * τ ^ b * μ * w) / g - m) := by
      field_simp
    rw [this, norm_mul, mul_comm]
    exact mul_lt_mul_of_pos_right (norm_sub_gaussFloor_lt _) (norm_pos_iff.mpr hg0)
  have hνn : ‖ν‖ = 1 := norm_of_mem_digitRotInvFinset
    (fun h0 : ρ = 0 => hρ1 (by rw [h0]; exact dvd_zero π)) hνmem
  have hunit : ‖σ ^ j' * ν‖ = 1 := by
    rw [norm_mul, _root_.norm_pow, hσ, hπ.norm_sigma, one_pow, one_mul, hνn]
  have hre2 : |(σ ^ j' * ν * (σ ^ a * τ ^ b * μ * w - g * m)).re| < ε / 2 := by
    calc |(σ ^ j' * ν * (σ ^ a * τ ^ b * μ * w - g * m)).re|
        ≤ ‖σ ^ j' * ν * (σ ^ a * τ ^ b * μ * w - g * m)‖ := Complex.abs_re_le_norm _
      _ = ‖σ ^ a * τ ^ b * μ * w - g * m‖ := by rw [norm_mul, hunit, one_mul]
      _ < Real.sqrt 2 * ‖g‖ := hnear
      _ ≤ ε / 2 := hg
  refine ⟨round ((B : ℝ) * (((X.val * ((hπ.ψ n m).val % p ^ s / p ^ (s - ℓ)) : ℕ) : ℝ) /
      ((p ^ ℓ : ℕ) : ℝ) + γ)) + k₁ + k₂, ?_⟩
  rw [← hγ] at hk₂
  have hc2 := hclose
  push_cast at hc2
  rw [hlabel] at hc2
  rw [hsplit, add_re, hk₁, hval, hk₂]
  push_cast
  rw [abs_lt] at hc2 hre2 ⊢
  constructor <;> linarith [hc2.1, hc2.2, hre2.1, hre2.2]

end DigitPrime

end Green41Proof
