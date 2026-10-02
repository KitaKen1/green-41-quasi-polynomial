import Green41SingleExponential.StepAFamily

/-!
# Minor arcs with digit rotations

`minor_arc_core_digit` is `Green41Proof.DigitPrime.minor_arc_core` with Step A replaced by
`stepA_digit`. The orbit used for counting labels becomes `σᵃ τᵇ μ w` with `μ` running over the
digit rotations `A/Ā`, `A ∈ digitFamily p (n + 4) ρ`, and `b ≤ N₀` instead of `b ≤ N₀ + T` with
`T = (p - 1) p^(n+3)`. Counting, the digit pigeonhole and the discrete core are unchanged.
-/

namespace Green41Proof

open Green41

open Complex ComplexConjugate Finset

/-- The digit family as a `Finset`: `ρ^m ∏_{i < N - 1} (1 + p^(1+i) i)^(d i)`. -/
def digitFamilyFinset (p N : ℕ) (ρ : GaussianInt) : Finset GaussianInt :=
  ((range (p - 1)) ×ˢ (Fintype.piFinset fun _ : Fin (N - 1) => range p)).image
    fun md => ρ ^ md.1 * ∏ i : Fin (N - 1), digitInt p (1 + (i : ℕ)) ^ md.2 i

lemma mem_digitFamilyFinset_of_mem {p N : ℕ} {ρ A : GaussianInt}
    (hA : A ∈ DigitPrime.digitFamily p N ρ) : A ∈ digitFamilyFinset p N ρ := by
  obtain ⟨m, hm, d, hd, rfl⟩ := hA
  refine Finset.mem_image.mpr ⟨(m, fun i => d (1 + (i : ℕ))), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hm,
      Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (hd _)⟩
  · simp only
    congr 1
    rw [Finset.prod_Ico_eq_prod_range]
    exact Fin.prod_univ_eq_prod_range (fun k => digitInt p (1 + k) ^ d (1 + k)) (N - 1)

/-- The digit rotations `A/Ā`. -/
noncomputable def digitRotFinset (p N : ℕ) (ρ : GaussianInt) : Finset ℂ :=
  (digitFamilyFinset p N ρ).image fun A : GaussianInt => (A : ℂ) / ((star A : GaussianInt) : ℂ)

lemma mem_digitRotFinset_of_mem {p N : ℕ} {ρ A : GaussianInt}
    (hA : A ∈ DigitPrime.digitFamily p N ρ) :
    (A : ℂ) / ((star A : GaussianInt) : ℂ) ∈ digitRotFinset p N ρ :=
  Finset.mem_image.mpr ⟨A, mem_digitFamilyFinset_of_mem hA, rfl⟩

lemma card_digitRotFinset_le (p N : ℕ) (ρ : GaussianInt) :
    (digitRotFinset p N ρ).card ≤ (p - 1) * p ^ (N - 1) := by
  calc (digitRotFinset p N ρ).card ≤ (digitFamilyFinset p N ρ).card := Finset.card_image_le
    _ ≤ ((range (p - 1)) ×ˢ (Fintype.piFinset fun _ : Fin (N - 1) => range p)).card :=
        Finset.card_image_le
    _ = (p - 1) * p ^ (N - 1) := by
        rw [Finset.card_product, Fintype.card_piFinset, Finset.card_range]
        simp

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

/-- **Minor arcs with digit rotations.** As `minor_arc_core`, but Step A uses the digit family,
so `q` only has to absorb `digitDen p (n + 4) ρ` instead of `ρ̄^E` with `E ≥ (p - 1) p^(n+3)`,
and the rotation found is `σᵃ τᵇ μ` with `μ` a digit rotation and `b ≤ N₀ + S`. -/
theorem minor_arc_core_digit (hp5 : 5 ≤ p) {ρ : GaussianInt}
    (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ)
    (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0)
    {n α β A L ℓ S H : ℕ} (hL : 0 < L) (hℓ : ℓ = 4 * L) (hS : S = (p - 1) * p ^ (ℓ - 1))
    (hSβ : S ≤ β) (hnA : n = 8 * (A + ℓ)) (hα : α = n - A)
    (hordA : orderOf (hπ.mult (star ρ) (n + 4)) = (p - 1) * p ^ (n + 3))
    (hordB : orderOf (((hπ.mult ρ n).val : ℕ) : ZMod (p ^ ℓ)) = S)
    {ε : ℝ} (hε : 0 < ε) (hH : 2 ≤ (H : ℝ) * ε ^ 2) (hHL : 25 * H ^ 3 < 4 * p ^ L)
    (hg : Real.sqrt 2 * ‖cellGen π ρ n α β‖ ≤ ε / 2)
    (w : ℂ) {N₀ a₁ b₁ a₂ b₂ v : ℕ} (ha₁ : a₁ ≤ N₀) (hb₁ : b₁ ≤ N₀) (ha₂ : a₂ ≤ N₀)
    (hb₂ : b₂ ≤ N₀) {q₂ : GaussianInt}
    (hq₂ : ¬ star π ∣ q₂)
    (he' : ‖(((star π) ^ v * digitDen p (n + 4) ρ * (star ρ) ^ β * q₂ : GaussianInt) : ℂ) -
        (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
            ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
          ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
            ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ <
        21 / 50 * ‖cellGen π ρ n α β‖) :
    ∃ a b : ℕ, a ≤ N₀ + v + (A + 4) + n ∧ b ≤ N₀ + S ∧ ∃ μ ∈ digitRotFinset p (n + 4) ρ,
      ∃ k : ℤ, |(((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b * μ * w).re - k| < ε := by
  set σ : ℂ := (π : ℂ) / ((star π : GaussianInt) : ℂ) with hσ
  set τ : ℂ := (ρ : ℂ) / ((star ρ : GaussianInt) : ℂ) with hτ
  set g := cellGen π ρ n α β with hg_def
  set j := v + (n - α + 4) with hj
  set q : ℂ := (((star π) ^ v * digitDen p (n + 4) ρ * (star ρ) ^ β * q₂ : GaussianInt) : ℂ)
    with hq
  set r : ℂ := σ ^ a₁ * τ ^ b₁ - σ ^ a₂ * τ ^ b₂ with hr
  set e' : ℂ := r * w - q with he'_def
  have he'n : ‖e'‖ < 21 / 50 * ‖g‖ := by rw [he'_def, norm_sub_rev]; exact he'
  have hrw : r * w = q + e' := by rw [he'_def]; ring
  have hn0 : 0 < n := by omega
  have hαn : α ≤ n := by omega
  have hp0 : 0 < p := by omega
  -- Step A
  have hA : ∀ l : ZMod (p ^ n), ∃ Aμ ∈ digitFamily p (n + 4) ρ,
      hπ.label ρ n α β (σ ^ j * ((Aμ : ℂ) / ((star Aμ : GaussianInt) : ℂ)) * (q + e')) = l :=
    fun l => hπ.stepA_digit hp5 hρ1 hρ2 hρ0 hαn hordA hq₂ he'n l
  -- the orbit
  set Mu : Finset ℂ := digitRotFinset p (n + 4) ρ with hMu
  set Z : Finset ℂ := (((range (N₀ + j + 1)) ×ˢ (range (N₀ + 1))) ×ˢ Mu).image
    (fun abμ => σ ^ abμ.1.1 * τ ^ abμ.1.2 * abμ.2 * w) with hZ
  have hmemZ : ∀ a b μ, a ≤ N₀ + j → b ≤ N₀ → μ ∈ Mu → σ ^ a * τ ^ b * μ * w ∈ Z := by
    intro a b μ ha hb hμ
    exact Finset.mem_image.mpr ⟨((a, b), μ), Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show a < N₀ + j + 1 by omega),
        Finset.mem_range.mpr (show b < N₀ + 1 by omega)⟩, hμ⟩, rfl⟩
  have hall : ∀ l : ZMod (p ^ n), ∃ x ∈ Z, ∃ x' ∈ Z, hπ.label ρ n α β (x - x') = l := by
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
  have hcount := hπ.pow_le_four_mul_card_sq ρ n α β Z hall
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  set Yl := Z.image (hπ.label ρ n α β) with hYl
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
  set X := hπ.Xfac ρ n α β j' with hXdef
  have hXu : IsUnit X := hπ.isUnit_Xfac hρ2 hn0
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
  -- discrete core
  set B := (hπ.mult ρ n).val with hB
  have hBinj : Set.InjOn (fun w : ℕ => ((B : ZMod (p ^ ℓ)) ^ w)) (Set.Iio S) := by
    rw [← hordB]; exact pow_injOn_Iio_orderOf
  have hYdbig : 25 * H ^ 3 < 4 * Yd.card := by rw [hYdcard]; omega
  set γ : ℝ := ((X.val * lam : ℕ) : ℝ) / (p : ℝ) ^ s with hγ
  obtain ⟨w', hw', y', hy', hclose⟩ :=
    discrete_core hp5 hS (by omega : 1 ≤ ℓ) hε hH hBinj γ Yd hYdmod hYdbig
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
  have hlabel : hπ.label ρ n α β (σ ^ a * τ ^ b * μ * w) = hπ.ψ n m := rfl
  obtain ⟨k₁, hk₁⟩ := hπ.re_label_formula hρ2 hρ0 (n := n) (α := α) (β := β) (j := j') (w := w')
    hn0 (by omega) (by omega) (by omega) m
  have hnj : n - j' = s := by omega
  rw [hnj] at hk₁
  have hval : (X * hπ.mult ρ n ^ w' * hπ.ψ n m).val =
      X.val * B ^ w' * (hπ.ψ n m).val % p ^ n := by
    rw [← ZMod.val_natCast]
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [hlabel] at hyvl
  obtain ⟨k₂, hk₂⟩ := frac_on_fiber hp0 (by omega : s ≤ n) (by omega : ℓ ≤ s) X.val B
    ((hπ.ψ n m).val) lam w' hyvl
  -- the final exponents
  refine ⟨a + j', b + w', by omega, by omega, μ, hμ', ?_⟩
  have hsplit : σ ^ (a + j') * τ ^ (b + w') * μ * w =
      σ ^ j' * τ ^ w' * (g * m) + σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * μ * w - g * m) := by
    rw [pow_add, pow_add]; ring
  have hg0 : g ≠ 0 := by
    simp only [hg_def, cellGen]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hπ.toComplex_star_ne_zero)
      (pow_ne_zero _ hρ0)) (pow_ne_zero _ hπ.toComplex_ne_zero)
  have hnear : ‖σ ^ a * τ ^ b * μ * w - g * m‖ < Real.sqrt 2 * ‖g‖ := by
    have : σ ^ a * τ ^ b * μ * w - g * m = g * ((σ ^ a * τ ^ b * μ * w) / g - m) := by
      field_simp
    rw [this, norm_mul, mul_comm]
    exact mul_lt_mul_of_pos_right (norm_sub_gaussFloor_lt _) (norm_pos_iff.mpr hg0)
  have hunit : ‖σ ^ j' * τ ^ w'‖ = 1 := by
    rw [norm_mul, _root_.norm_pow, _root_.norm_pow, hσ, hπ.norm_sigma, hτ, norm_rotOf hρ0,
      one_pow, one_pow, one_mul]
  have hre2 : |(σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * μ * w - g * m)).re| < ε / 2 := by
    calc |(σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * μ * w - g * m)).re|
        ≤ ‖σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * μ * w - g * m)‖ := Complex.abs_re_le_norm _
      _ = ‖σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * μ * w - g * m)‖ := rfl
      _ = ‖σ ^ a * τ ^ b * μ * w - g * m‖ := by rw [norm_mul, hunit, one_mul]
      _ < Real.sqrt 2 * ‖g‖ := hnear
      _ ≤ ε / 2 := hg
  refine ⟨round ((B : ℝ) ^ w' * (((X.val * ((hπ.ψ n m).val % p ^ s / p ^ (s - ℓ)) : ℕ) : ℝ) /
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
