import Green41SingleExponential.AssemblyDigit

/-!
# The single-exponential bound

`minCopies_le_Rots_G_pow` gives `minCopies ε ≤ |Rots ε| · G^88`. With `u = 1/ε` and
`W = (n₅ + 4) + (n₁₃ + 4) ≤ 5 u^100`:

* `|Rots ε| ≤ 16^(W+1)`,
* `Mdig ε ≤ 2^(144 W²)` (the digit denominators have norm `2^{O(n²)}`),
* `20/η = 20 · 5^(u^100)`, `Bd ε ≤ 2W`, `1/ε = u`,

so `G ≤ exp(4000 u^200 + 68)` and `minCopies ε ≤ exp(400000 u^200) ≤ exp(u^201)` once
`u ≥ 400000`.
-/

namespace Green41Proof

open Green41 Finset

/- ## Norms of the digit denominators -/

lemma norm_eq_normMonoidHom (x : GaussianInt) : x.norm = Zsqrtd.normMonoidHom x := rfl

lemma norm_star_pow (ρ : GaussianInt) (k : ℕ) : (star ρ ^ k).norm = ρ.norm ^ k := by
  rw [norm_eq_normMonoidHom, map_pow, ← norm_eq_normMonoidHom, Zsqrtd.norm_conj]

lemma norm_digitDen (p N : ℕ) (ρ : GaussianInt) :
    (DigitPrime.digitDen p N ρ).norm =
      ρ.norm ^ (p - 2) * ∏ j ∈ Ico 1 N, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) := by
  unfold DigitPrime.digitDen
  rw [Zsqrtd.norm_mul, norm_star_pow, norm_eq_normMonoidHom (∏ j ∈ Ico 1 N, _), map_prod]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  rw [← norm_eq_normMonoidHom, norm_star_pow, digitInt_norm]

lemma one_add_pow_le {p j N : ℕ} (hp : p ≤ 13) (hj : j < N) :
    1 + (p : ℤ) ^ (2 * j) ≤ 2 ^ (8 * N) := by
  have h1 : (p : ℤ) ^ (2 * j) ≤ 2 ^ (8 * j) := by
    rw [pow_mul, pow_mul]
    have hp' : (p : ℤ) ≤ 13 := by exact_mod_cast hp
    have hp0 : (0 : ℤ) ≤ p := by positivity
    have : (p : ℤ) ^ 2 ≤ 2 ^ 8 := by nlinarith
    exact pow_le_pow_left₀ (by positivity) this j
  have h2 : (1 : ℤ) ≤ 2 ^ (8 * j) := one_le_pow₀ (by norm_num)
  have h3 : (2 : ℤ) ^ (8 * j) * 2 ≤ 2 ^ (8 * N) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

lemma norm_digitDen_le {p N : ℕ} (hp : p ≤ 13) {ρ : GaussianInt} (hρ : ρ.norm ≤ 16) :
    (DigitPrime.digitDen p N ρ).norm ≤ 2 ^ (44 + 96 * N ^ 2) := by
  rw [norm_digitDen]
  have hρ0 : 0 ≤ ρ.norm := GaussianInt.norm_nonneg ρ
  have h1 : ρ.norm ^ (p - 2) ≤ 2 ^ 44 := by
    calc ρ.norm ^ (p - 2) ≤ 16 ^ (p - 2) := pow_le_pow_left₀ hρ0 hρ _
      _ ≤ 16 ^ 11 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 2 ^ 44 := by norm_num
  have hfac : ∀ j ∈ Ico 1 N, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) ≤ ((2 : ℤ) ^ (8 * N)) ^ 12 := by
    intro j hj
    have hb := one_add_pow_le hp (mem_Ico.mp hj).2
    have hb0 : (0 : ℤ) ≤ 1 + (p : ℤ) ^ (2 * j) := by positivity
    calc (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) ≤ ((2 : ℤ) ^ (8 * N)) ^ (p - 1) :=
          pow_le_pow_left₀ hb0 hb _
      _ ≤ ((2 : ℤ) ^ (8 * N)) ^ 12 := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
  have hexp : 8 * N * (12 * (N - 1)) ≤ 96 * N ^ 2 := by
    calc 8 * N * (12 * (N - 1)) ≤ 8 * N * (12 * N) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le N 1))
      _ = 96 * N ^ 2 := by ring
  have h2 : ∏ j ∈ Ico 1 N, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) ≤ 2 ^ (96 * N ^ 2) := by
    calc ∏ j ∈ Ico 1 N, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1)
        ≤ ∏ _j ∈ Ico 1 N, ((2 : ℤ) ^ (8 * N)) ^ 12 :=
          prod_le_prod (fun j _ => by positivity) hfac
      _ = (((2 : ℤ) ^ (8 * N)) ^ 12) ^ (N - 1) := by rw [prod_const, Nat.card_Ico]
      _ = 2 ^ (8 * N * (12 * (N - 1))) := by rw [← pow_mul, ← pow_mul]
      _ ≤ 2 ^ (96 * N ^ 2) := pow_le_pow_right₀ (by norm_num) hexp
  have h3 : 0 ≤ ∏ j ∈ Ico 1 N, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) :=
    prod_nonneg fun j _ => by positivity
  calc ρ.norm ^ (p - 2) * ∏ j ∈ Ico 1 N, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1)
      ≤ 2 ^ 44 * 2 ^ (96 * N ^ 2) := mul_le_mul h1 h2 h3 (by positivity)
    _ = 2 ^ (44 + 96 * N ^ 2) := by rw [pow_add]

lemma norm_digitDen_mul_le {p N β : ℕ} (hp : p ≤ 13) {ρ : GaussianInt} (hρ : ρ.norm ≤ 16)
    (hβ : β ≤ N) (hN : 1 ≤ N) :
    (DigitPrime.digitDen p N ρ * star ρ ^ β).norm ≤ 2 ^ (144 * N ^ 2) := by
  rw [Zsqrtd.norm_mul, norm_star_pow]
  have h1 := norm_digitDen_le (N := N) hp hρ
  have h2 : ρ.norm ^ β ≤ 2 ^ (4 * N) := by
    calc ρ.norm ^ β ≤ 16 ^ β := pow_le_pow_left₀ (GaussianInt.norm_nonneg ρ) hρ β
      _ ≤ 16 ^ N := pow_le_pow_right₀ (by norm_num) hβ
      _ = 2 ^ (4 * N) := by rw [pow_mul]; norm_num
  have h0 : 0 ≤ (DigitPrime.digitDen p N ρ).norm := GaussianInt.norm_nonneg _
  calc (DigitPrime.digitDen p N ρ).norm * ρ.norm ^ β
      ≤ 2 ^ (44 + 96 * N ^ 2) * 2 ^ (4 * N) :=
        mul_le_mul h1 h2 (pow_nonneg (GaussianInt.norm_nonneg ρ) _) (by positivity)
    _ = 2 ^ (44 + 96 * N ^ 2 + 4 * N) := by rw [← pow_add]
    _ ≤ 2 ^ (144 * N ^ 2) := pow_le_pow_right₀ (by norm_num) (by nlinarith)

lemma pS_le_pn_add_four (p K : ℕ) : pS p K ≤ pn p K + 4 := by
  have h := pA_le_pn p K
  unfold pA at h
  omega

lemma natAbs_norm_cast (D : GaussianInt) : ((D.norm.natAbs : ℕ) : ℝ) = ((D.norm : ℤ) : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast GaussianInt.norm_nonneg D)]

lemma Mdig_le (ε : ℝ) : (Mdig ε : ℝ) ≤
    2 ^ (144 * (pn 5 ⌈1 / ε⌉₊ + 4) ^ 2 + 144 * (pn 13 ⌈1 / ε⌉₊ + 4) ^ 2) := by
  have h5 : (D5 ε).norm ≤ 2 ^ (144 * (pn 5 ⌈1 / ε⌉₊ + 4) ^ 2) :=
    norm_digitDen_mul_le (by norm_num) (by rw [norm_gQ]; norm_num) (pS_le_pn_add_four 5 _)
      (by omega)
  have h13 : (D13 ε).norm ≤ 2 ^ (144 * (pn 13 ⌈1 / ε⌉₊ + 4) ^ 2) :=
    norm_digitDen_mul_le (by norm_num) (by rw [norm_gP]; norm_num) (pS_le_pn_add_four 13 _)
      (by omega)
  unfold Mdig
  push_cast
  rw [natAbs_norm_cast, natAbs_norm_cast, pow_add]
  have h5' : ((D5 ε).norm : ℝ) ≤ 2 ^ (144 * (pn 5 ⌈1 / ε⌉₊ + 4) ^ 2) := by exact_mod_cast h5
  have h13' : ((D13 ε).norm : ℝ) ≤ 2 ^ (144 * (pn 13 ⌈1 / ε⌉₊ + 4) ^ 2) := by exact_mod_cast h13
  exact mul_le_mul h5' h13' (by exact_mod_cast GaussianInt.norm_nonneg _) (by positivity)

lemma card_Rots_le (ε : ℝ) :
    (Rots ε).card ≤ 16 ^ (pn 5 ⌈1 / ε⌉₊ + 4 + (pn 13 ⌈1 / ε⌉₊ + 4) + 1) := by
  set N5 := pn 5 ⌈1 / ε⌉₊ + 4
  set N13 := pn 13 ⌈1 / ε⌉₊ + 4
  unfold Rots
  have h5 : (5 - 1) * 5 ^ (N5 - 1) ≤ 4 * 16 ^ (N5 + N13) := by
    have : 5 ^ (N5 - 1) ≤ 16 ^ (N5 + N13) :=
      (Nat.pow_le_pow_left (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have h13 : (13 - 1) * 13 ^ (N13 - 1) ≤ 12 * 16 ^ (N5 + N13) := by
    have : 13 ^ (N13 - 1) ≤ 16 ^ (N5 + N13) :=
      (Nat.pow_le_pow_left (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  calc (digitRotFinset 5 N5 gQ ∪ digitRotFinset 13 N13 gP).card
      ≤ (digitRotFinset 5 N5 gQ).card + (digitRotFinset 13 N13 gP).card := card_union_le _ _
    _ ≤ (5 - 1) * 5 ^ (N5 - 1) + (13 - 1) * 13 ^ (N13 - 1) :=
        add_le_add (card_digitRotFinset_le _ _ _) (card_digitRotFinset_le _ _ _)
    _ ≤ 16 ^ (N5 + N13 + 1) := by rw [pow_succ]; omega

lemma Bd_le_W (ε : ℝ) :
    Bd ε ≤ 2 * ((pn 5 ⌈1 / ε⌉₊ + 4 + (pn 13 ⌈1 / ε⌉₊ + 4) : ℕ) : ℝ) := by
  unfold Bd
  have h5 := pA_le_pn 5 ⌈1 / ε⌉₊
  have h13 := pA_le_pn 13 ⌈1 / ε⌉₊
  have : pA 5 ⌈1 / ε⌉₊ + 4 + pn 5 ⌈1 / ε⌉₊ + (pA 13 ⌈1 / ε⌉₊ + 4 + pn 13 ⌈1 / ε⌉₊) ≤
      2 * (pn 5 ⌈1 / ε⌉₊ + 4 + (pn 13 ⌈1 / ε⌉₊ + 4)) := by omega
  exact_mod_cast this

/- ## Real bounds -/

lemma two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]

lemma two_pow_le_exp (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp m := by
  calc (2 : ℝ) ^ m ≤ Real.exp 1 ^ m := pow_le_pow_left₀ (by norm_num) two_le_exp_one m
    _ = Real.exp m := by rw [← Real.exp_nat_mul, mul_one]

lemma le_exp_self' (x : ℝ) : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]

lemma log_five_le_three : Real.log 5 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (5 : ℝ) ≤ 2 ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) two_le_exp_one 3

lemma inv_η_le {ε : ℝ} (hε : 0 < ε) :
    20 / ηKL 100 ε ≤ Real.exp (20 + 3 * (1 / ε) ^ 100) := by
  rw [ηKL_hundred hε, Real.rpow_neg (by norm_num), div_inv_eq_mul,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5), Real.exp_add]
  have hu : (0 : ℝ) ≤ (1 / ε) ^ 100 := by positivity
  apply mul_le_mul (by linarith [Real.add_one_le_exp 20])
    (Real.exp_le_exp.mpr (by nlinarith [log_five_le_three])) (Real.exp_pos _).le
    (Real.exp_pos _).le

lemma rpow_neg_two_hundred_one {ε : ℝ} (hε : 0 < ε) :
    ε ^ (-(201 : ℝ)) = (1 / ε) ^ 201 := by
  rw [Real.rpow_neg hε.le, show (201 : ℝ) = ((201 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    one_div, inv_pow]

/-- **The single-exponential bound.** `minCopies ε ≤ exp(ε^(-201))` for `0 < ε ≤ 1/400000`. -/
theorem singleExponentialBound :
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, (minCopies ε : ℝ) ≤ Real.exp (ε ^ (-C)) := by
  refine ⟨201, 1 / 400000, by norm_num, ?_⟩
  rintro ε ⟨hε0, hεle⟩
  have hε1 : ε < 1 / 10 := by linarith
  set u : ℝ := 1 / ε with hu
  have hu4 : 400000 ≤ u := by
    rw [hu, le_div_iff₀ hε0]
    have : 400000 * ε ≤ 400000 * (1 / 400000) := by gcongr
    linarith
  have hu1 : 1 ≤ u := by linarith
  -- opaque names for `u^100` and `u^200`, so that arithmetic tactics do not expand them
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = u ^ 100 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u ^ 200 := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := by rw [hw]; exact one_le_pow₀ hu1
  have hwv : w ≤ v := by rw [hw, hv]; exact pow_le_pow_right₀ hu1 (by norm_num)
  have hvw : w * w = v := by rw [hw, hv, ← pow_add]
  have huv : u ≤ v := by
    rw [hv]
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ 200 := pow_le_pow_right₀ hu1 (by norm_num)
  have hv1 : 1 ≤ v := hw1.trans hwv
  -- the size of the digit expansions
  set N5 := pn 5 ⌈1 / ε⌉₊ + 4 with hN5
  set N13 := pn 13 ⌈1 / ε⌉₊ + 4 with hN13
  have hN5r : (N5 : ℝ) ≤ 5 / 2 * w := by
    have := pn_small (p := 5) (by norm_num) (by norm_num) hε0 hε1
    rw [← hu, ← hw] at this
    rw [hN5]; push_cast; linarith
  have hN13r : (N13 : ℝ) ≤ 5 / 2 * w := by
    have := pn_small (p := 13) (by norm_num) (by norm_num) hε0 hε1
    rw [← hu, ← hw] at this
    rw [hN13]; push_cast; linarith
  have hN5n : (0 : ℝ) ≤ N5 := by positivity
  have hN13n : (0 : ℝ) ≤ N13 := by positivity
  -- `X0 ≤ exp(4000 v)`
  have hX : X0D ε ≤ Real.exp (4000 * v) := by
    unfold X0D
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · have h := inv_η_le hε0
      rw [← hu, ← hw] at h
      calc 20 / ηKL 100 ε ≤ Real.exp (20 + 3 * w) := h
        _ ≤ Real.exp (4000 * v) := Real.exp_le_exp.mpr (by linarith)
    · have hM := Mdig_le ε
      rw [← hN5, ← hN13] at hM
      have h1 : (N5 : ℝ) * N5 ≤ (5 / 2 * w) * (5 / 2 * w) := mul_le_mul hN5r hN5r hN5n (by linarith)
      have h2 : (N13 : ℝ) * N13 ≤ (5 / 2 * w) * (5 / 2 * w) :=
        mul_le_mul hN13r hN13r hN13n (by linarith)
      have h3 : (5 / 2 * w) * (5 / 2 * w) = 25 / 4 * v := by rw [← hvw]; ring
      calc (Mdig ε : ℝ) ≤ 2 ^ (144 * N5 ^ 2 + 144 * N13 ^ 2) := hM
        _ ≤ Real.exp ((144 * N5 ^ 2 + 144 * N13 ^ 2 : ℕ) : ℝ) := two_pow_le_exp _
        _ ≤ Real.exp (4000 * v) := by
            apply Real.exp_le_exp.mpr
            push_cast
            rw [sq, sq]
            linarith
    · calc 1 / ε = u := rfl
        _ ≤ Real.exp u := le_exp_self' u
        _ ≤ Real.exp (4000 * v) := Real.exp_le_exp.mpr (by linarith)
    · have hB := Bd_le_W ε
      rw [← hN5, ← hN13] at hB
      push_cast at hB
      calc Bd ε ≤ 2 * ((N5 : ℝ) + N13) := hB
        _ ≤ Real.exp (2 * ((N5 : ℝ) + N13)) := le_exp_self' _
        _ ≤ Real.exp (4000 * v) := Real.exp_le_exp.mpr (by linarith)
  -- `G ≤ exp(4000 v + 68)`
  have hG : (GpD ε : ℝ) ≤ Real.exp (4000 * v + 68) := by
    have hX0 : 0 ≤ X0D ε := by
      have := (X0D_ge (ε := ε)).2.2.1
      have : 0 < 1 / ε := by positivity
      linarith
    have hceil : (⌈X0D ε⌉₊ : ℝ) < X0D ε + 1 := Nat.ceil_lt_add_one hX0
    set E := Real.exp (4000 * v) with hE
    have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
    set F := Real.exp 68 with hF
    have h68 : (68 : ℝ) ≤ F := by linarith [Real.add_one_le_exp 68]
    have hEF : 68 * E ≤ E * F := by
      have := mul_le_mul_of_nonneg_left h68 (by linarith : (0 : ℝ) ≤ E)
      linarith
    unfold GpD
    push_cast
    rw [Real.exp_add, ← hE, ← hF]
    linarith
  -- `|Rots| ≤ exp(24 v)`
  have hR : ((Rots ε).card : ℝ) ≤ Real.exp (24 * v) := by
    have h1 : ((Rots ε).card : ℝ) ≤ ((16 ^ (N5 + N13 + 1) : ℕ) : ℝ) := by
      exact_mod_cast card_Rots_le ε
    have h2 : ((16 ^ (N5 + N13 + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (4 * (N5 + N13 + 1)) := by
      push_cast; rw [pow_mul]; norm_num
    calc ((Rots ε).card : ℝ) ≤ (2 : ℝ) ^ (4 * (N5 + N13 + 1)) := h1.trans h2.le
      _ ≤ Real.exp ((4 * (N5 + N13 + 1) : ℕ) : ℝ) := two_pow_le_exp _
      _ ≤ Real.exp (24 * v) := by
          apply Real.exp_le_exp.mpr
          push_cast
          linarith
  -- conclusion
  have hmain := minCopies_le_Rots_G_pow hε0 hε1
  have hG0 : (0 : ℝ) ≤ GpD ε := by positivity
  have huv' : 400000 * v ≤ u * v := mul_le_mul_of_nonneg_right hu4 (by linarith)
  calc (minCopies ε : ℝ) ≤ (Rots ε).card * (GpD ε : ℝ) ^ 88 := hmain
    _ ≤ Real.exp (24 * v) * Real.exp (4000 * v + 68) ^ 88 :=
        mul_le_mul hR (pow_le_pow_left₀ hG0 hG 88) (pow_nonneg hG0 88) (Real.exp_pos _).le
    _ = Real.exp (24 * v + 88 * (4000 * v + 68)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
    _ ≤ Real.exp (u * v) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (ε ^ (-(201 : ℝ))) := by
        rw [rpow_neg_two_hundred_one hε0, ← hu, hv, ← pow_succ']

/-- The single-exponential target, in the form of a Formal Conjectures `answer(True)` statement. -/
theorem green_41_single_exponential_bound_solved : answer(True) ↔
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, (minCopies ε : ℝ) ≤ Real.exp (ε ^ (-C)) :=
  ⟨fun _ => singleExponentialBound, fun _ => trivial⟩

#print axioms green_41_single_exponential_bound_solved

end Green41Proof
