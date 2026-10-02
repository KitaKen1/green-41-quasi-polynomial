import Green41QuasiPolynomial.KL57Quasi

/-!
# The quasi-polynomial bound

`dataQ.minCopies_le_Rots_G_pow dataQ_KL` gives `minCopies ε ≤ |RotsQ ε| · G^88` with
`G = ⌈max(20/ηQ, MdigQ, 1/ε, BdQ)⌉ + 66`. Put `X = log(1/ε) + 2`. Then `c = clog_p K ≤ X`,
`ℓ ≤ 32X`, `A ≤ 26700 X²` and `N = n + 4 ≤ 214000 X²`, so

* `MdigQ ε ≤ 2^{O(N²)} = exp(O(X⁴))` (the digit denominators),
* `20/ηQ ε = 20 · 5^(A₅ + A₁₃) = exp(O(X²))`, `BdQ ε = O(X²)`, `1/ε ≤ exp X`,
* `|RotsQ ε| ≤ 16^(2(N₅ + N₁₃) + 1) = exp(O(X²))`.

Altogether `minCopies ε ≤ exp(10^16 (log(1/ε) + 2)^4)` for `0 < ε < 1/10`
(`quasiPolynomialBound_explicit`), hence `minCopies ε ≤ exp((log ε⁻¹)^5)` for
`0 < ε ≤ exp(-10^18)` (`quasiPolynomialBound`).
-/

namespace Green41Proof

open Green41 Finset

/- ## Sizes in terms of `log (1/ε)` -/

lemma pc_le_log {p : ℕ} (hp : 3 ≤ p) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (pc p ⌈1 / ε⌉₊ : ℝ) ≤ Real.log (1 / ε) + 2 := by
  set K := ⌈1 / ε⌉₊ with hK
  have hu1 : 1 < 1 / ε := by rw [lt_div_iff₀ hε]; linarith
  have hlog0 : 0 < Real.log (1 / ε) := Real.log_pos hu1
  have hK1 : (1 : ℝ) < K := lt_of_lt_of_le hu1 (Nat.le_ceil _)
  have hK2 : 1 < K := by exact_mod_cast hK1
  have hKu : (K : ℝ) ≤ 2 * (1 / ε) := by
    have := Nat.ceil_lt_add_one (le_of_lt (by positivity : (0 : ℝ) < 1 / ε))
    linarith
  rcases Nat.eq_zero_or_pos (pc p K) with h0 | hpos
  · rw [h0]; push_cast; linarith
  · have hlt : p ^ (pc p K - 1) < K := by
      have := Nat.pow_pred_clog_lt_self (by omega : 1 < p) hK2
      unfold pc
      simpa [Nat.pred_eq_sub_one] using this
    have hlt' : (p : ℝ) ^ (pc p K - 1) < K := by exact_mod_cast hlt
    have hlogp : 1 ≤ Real.log p := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have h1 : ((pc p K - 1 : ℕ) : ℝ) * Real.log p < Real.log K := by
      rw [← Real.log_pow]
      exact Real.log_lt_log (by positivity) hlt'
    have h2 : Real.log K ≤ Real.log 2 + Real.log (1 / ε) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) hKu
    have hlog2 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      linarith
    have hc1 : ((pc p K - 1 : ℕ) : ℝ) = (pc p K : ℝ) - 1 := by
      rw [Nat.cast_sub hpos]; simp
    have hc0 : (0 : ℝ) ≤ ((pc p K - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have : ((pc p K - 1 : ℕ) : ℝ) ≤ ((pc p K - 1 : ℕ) : ℝ) * Real.log p := by nlinarith
    linarith

lemma qA_qn_le {p K : ℕ} (hp : p ≤ 13) {X : ℝ} (hc : (pc p K : ℝ) ≤ X) (hX : 2 ≤ X) :
    (qA p K : ℝ) ≤ 26700 * X ^ 2 ∧ ((qn p K + 4 : ℕ) : ℝ) ≤ 214000 * X ^ 2 := by
  have hℓ : (pℓ p K : ℝ) = 24 * (pc p K : ℝ) + 16 := by unfold pℓ pL; push_cast; ring
  have hc0 : (0 : ℝ) ≤ pc p K := Nat.cast_nonneg _
  have hℓX : (pℓ p K : ℝ) ≤ 32 * X := by rw [hℓ]; linarith
  have hℓ0 : (0 : ℝ) ≤ pℓ p K := Nat.cast_nonneg _
  have hℓ2 : (pℓ p K : ℝ) ^ 2 ≤ 1024 * X ^ 2 := by nlinarith
  have hp' : (p : ℝ) ≤ 13 := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hqA : (qA p K : ℝ) = 2 * p * ((pℓ p K : ℝ) ^ 2 + 1) + 2 * pc p K + 3 := by
    unfold qA; push_cast; ring
  have h1 : 2 * (p : ℝ) * ((pℓ p K : ℝ) ^ 2 + 1) ≤ 2 * 13 * (1024 * X ^ 2 + 1) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have hA : (qA p K : ℝ) ≤ 26700 * X ^ 2 := by rw [hqA]; nlinarith
  refine ⟨hA, ?_⟩
  have hqn : ((qn p K + 4 : ℕ) : ℝ) = 8 * ((qA p K : ℝ) + pℓ p K) + 4 := by
    unfold qn; push_cast; ring
  rw [hqn]; nlinarith

/- ## The digit data -/

lemma pℓ_le_qn_add_four (p K : ℕ) : pℓ p K ≤ qn p K + 4 := by unfold qn; omega

lemma norm_DQ_le {p : ℕ} (hp : p ≤ 13) {ρ : GaussianInt} (hρ : ρ.norm ≤ 16) {N ℓ : ℕ}
    (hℓN : ℓ ≤ N) :
    (DigitPrime.digitDen p N ρ * star (DigitPrime.digitDen p ℓ ρ)).norm ≤
      2 ^ (88 + 192 * N ^ 2) := by
  rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj]
  have h1 := norm_digitDen_le (N := N) hp hρ
  have h2 := norm_digitDen_le (N := ℓ) hp hρ
  have h2' : (DigitPrime.digitDen p ℓ ρ).norm ≤ 2 ^ (44 + 96 * N ^ 2) :=
    h2.trans (pow_le_pow_right₀ (by norm_num) (by have := Nat.pow_le_pow_left hℓN 2; omega))
  calc (DigitPrime.digitDen p N ρ).norm * (DigitPrime.digitDen p ℓ ρ).norm
      ≤ 2 ^ (44 + 96 * N ^ 2) * 2 ^ (44 + 96 * N ^ 2) :=
        mul_le_mul h1 h2' (GaussianInt.norm_nonneg _) (by positivity)
    _ = 2 ^ (88 + 192 * N ^ 2) := by rw [← pow_add]; ring_nf

lemma MdigQ_le (ε : ℝ) : (MdigQ ε : ℝ) ≤
    2 ^ ((88 + 192 * (qn 5 ⌈1 / ε⌉₊ + 4) ^ 2) + (88 + 192 * (qn 13 ⌈1 / ε⌉₊ + 4) ^ 2)) := by
  have h5 : (D5Q ε).norm ≤ 2 ^ (88 + 192 * (qn 5 ⌈1 / ε⌉₊ + 4) ^ 2) :=
    norm_DQ_le (by norm_num) (by rw [norm_gQ]; norm_num) (pℓ_le_qn_add_four 5 _)
  have h13 : (D13Q ε).norm ≤ 2 ^ (88 + 192 * (qn 13 ⌈1 / ε⌉₊ + 4) ^ 2) :=
    norm_DQ_le (by norm_num) (by rw [norm_gP]; norm_num) (pℓ_le_qn_add_four 13 _)
  unfold MdigQ
  push_cast
  rw [natAbs_norm_cast, natAbs_norm_cast, pow_add]
  have h5' : ((D5Q ε).norm : ℝ) ≤ 2 ^ (88 + 192 * (qn 5 ⌈1 / ε⌉₊ + 4) ^ 2) := by
    exact_mod_cast h5
  have h13' : ((D13Q ε).norm : ℝ) ≤ 2 ^ (88 + 192 * (qn 13 ⌈1 / ε⌉₊ + 4) ^ 2) := by
    exact_mod_cast h13
  exact mul_le_mul h5' h13' (by exact_mod_cast GaussianInt.norm_nonneg _) (by positivity)

lemma sub_one_mul_pow_le {p N : ℕ} (hp16 : p ≤ 16) (hN : 1 ≤ N) :
    (p - 1) * p ^ (N - 1) ≤ 16 ^ N := by
  calc (p - 1) * p ^ (N - 1) ≤ p * p ^ (N - 1) := Nat.mul_le_mul_right _ (Nat.sub_le p 1)
    _ = p ^ N := by rw [← pow_succ']; congr 1; omega
    _ ≤ 16 ^ N := Nat.pow_le_pow_left hp16 N

lemma card_rotPairs_le' {p N ℓ : ℕ} (hp16 : p ≤ 16) (ρ : GaussianInt) (hℓ : 1 ≤ ℓ)
    (hℓN : ℓ ≤ N) : (rotPairs p N ℓ ρ).card ≤ 16 ^ (2 * N) := by
  calc (rotPairs p N ℓ ρ).card ≤ ((p - 1) * p ^ (N - 1)) * ((p - 1) * p ^ (ℓ - 1)) :=
        card_rotPairs_le p N ℓ ρ
    _ ≤ 16 ^ N * 16 ^ N :=
        Nat.mul_le_mul (sub_one_mul_pow_le hp16 (by omega))
          ((sub_one_mul_pow_le hp16 hℓ).trans (Nat.pow_le_pow_right (by norm_num) hℓN))
    _ = 16 ^ (2 * N) := by rw [← pow_add]; ring_nf

lemma card_RotsQ_le (ε : ℝ) :
    (RotsQ ε).card ≤ 16 ^ (2 * ((qn 5 ⌈1 / ε⌉₊ + 4) + (qn 13 ⌈1 / ε⌉₊ + 4)) + 1) := by
  set N5 := qn 5 ⌈1 / ε⌉₊ + 4
  set N13 := qn 13 ⌈1 / ε⌉₊ + 4
  have h5 : (rotPairs 5 N5 (pℓ 5 ⌈1 / ε⌉₊) gQ).card ≤ 16 ^ (2 * N5) :=
    card_rotPairs_le' (by norm_num) gQ (by have := pℓ_ge 5 ⌈1 / ε⌉₊; omega)
      (pℓ_le_qn_add_four 5 _)
  have h13 : (rotPairs 13 N13 (pℓ 13 ⌈1 / ε⌉₊) gP).card ≤ 16 ^ (2 * N13) :=
    card_rotPairs_le' (by norm_num) gP (by have := pℓ_ge 13 ⌈1 / ε⌉₊; omega)
      (pℓ_le_qn_add_four 13 _)
  have hle5 : 16 ^ (2 * N5) ≤ 16 ^ (2 * (N5 + N13)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle13 : 16 ^ (2 * N13) ≤ 16 ^ (2 * (N5 + N13)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold RotsQ
  calc (rotPairs 5 N5 (pℓ 5 ⌈1 / ε⌉₊) gQ ∪ rotPairs 13 N13 (pℓ 13 ⌈1 / ε⌉₊) gP).card
      ≤ (rotPairs 5 N5 (pℓ 5 ⌈1 / ε⌉₊) gQ).card + (rotPairs 13 N13 (pℓ 13 ⌈1 / ε⌉₊) gP).card :=
        card_union_le _ _
    _ ≤ 16 ^ (2 * (N5 + N13)) + 16 ^ (2 * (N5 + N13)) := add_le_add (h5.trans hle5)
        (h13.trans hle13)
    _ ≤ 16 ^ (2 * (N5 + N13) + 1) := by rw [pow_succ]; omega

lemma BdQ_le (ε : ℝ) :
    BdQ ε ≤ 2 * ((qn 5 ⌈1 / ε⌉₊ + 4 + (qn 13 ⌈1 / ε⌉₊ + 4) : ℕ) : ℝ) := by
  unfold BdQ
  have h5 := qA_le_qn 5 ⌈1 / ε⌉₊
  have h13 := qA_le_qn 13 ⌈1 / ε⌉₊
  have : qA 5 ⌈1 / ε⌉₊ + 4 + qn 5 ⌈1 / ε⌉₊ + (qA 13 ⌈1 / ε⌉₊ + 4 + qn 13 ⌈1 / ε⌉₊) ≤
      2 * (qn 5 ⌈1 / ε⌉₊ + 4 + (qn 13 ⌈1 / ε⌉₊ + 4)) := by omega
  exact_mod_cast this

lemma five_pow_le_exp (m : ℕ) : (5 : ℝ) ^ m ≤ Real.exp (3 * m) := by
  have h5 : (5 : ℝ) ≤ Real.exp 3 := by
    rw [← Real.log_le_iff_le_exp (by norm_num)]; exact log_five_le_three
  calc (5 : ℝ) ^ m ≤ Real.exp 3 ^ m := pow_le_pow_left₀ (by norm_num) h5 m
    _ = Real.exp (3 * m) := by rw [← Real.exp_nat_mul]; ring_nf

/- ## The bound -/

/-- `20/η ≤ exp(20 + 3(A₅ + A₁₃))`. -/
lemma inv_ηQ_le (ε : ℝ) :
    20 / ηQ ε ≤ Real.exp (20 + 3 * ((qA 5 ⌈1 / ε⌉₊ + qA 13 ⌈1 / ε⌉₊ : ℕ) : ℝ)) := by
  unfold ηQ
  rw [one_div, inv_pow, div_inv_eq_mul]
  have h1 := five_pow_le_exp (qA 5 ⌈1 / ε⌉₊ + qA 13 ⌈1 / ε⌉₊)
  have h20 : (20 : ℝ) ≤ Real.exp 20 := by linarith [Real.add_one_le_exp (20 : ℝ)]
  calc (20 : ℝ) * 5 ^ (qA 5 ⌈1 / ε⌉₊ + qA 13 ⌈1 / ε⌉₊)
      ≤ Real.exp 20 * Real.exp (3 * ((qA 5 ⌈1 / ε⌉₊ + qA 13 ⌈1 / ε⌉₊ : ℕ) : ℝ)) :=
        mul_le_mul h20 h1 (by positivity) (by positivity)
    _ = Real.exp (20 + 3 * ((qA 5 ⌈1 / ε⌉₊ + qA 13 ⌈1 / ε⌉₊ : ℕ) : ℝ)) := by
        rw [← Real.exp_add]

/-- `G ≤ exp(E + 68)` once `X0 ≤ exp E`. -/
lemma G_le_exp {d : ArcData} {ε E : ℝ} (hε : 0 < ε) (hE : 0 ≤ E) (hX0 : d.X0 ε ≤ Real.exp E) :
    (d.G ε : ℝ) ≤ Real.exp (E + 68) := by
  have hX00 : 0 ≤ d.X0 ε := by
    have := (ArcData.X0_ge (d := d) ε).2.2.1
    have : 0 < 1 / ε := by positivity
    linarith
  have hceil : (⌈d.X0 ε⌉₊ : ℝ) < d.X0 ε + 1 := Nat.ceil_lt_add_one hX00
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Real.exp E := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hR]; exact Real.one_le_exp hE
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = Real.exp 68 := ⟨_, rfl⟩
  have h68 : (68 : ℝ) ≤ F := by rw [hF]; linarith [Real.add_one_le_exp (68 : ℝ)]
  have hRF : 68 * R ≤ R * F := by
    have := mul_le_mul_of_nonneg_left h68 (by linarith : (0 : ℝ) ≤ R)
    linarith
  unfold ArcData.G
  push_cast
  rw [Real.exp_add, ← hR, ← hF]
  rw [← hR] at hX0
  linarith

/-- **The quasi-polynomial bound, explicit form.**
`minCopies ε ≤ exp(10^16 (log(1/ε) + 2)^4)` for `0 < ε < 1/10`. -/
theorem quasiPolynomialBound_explicit {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 10) :
    (minCopies ε : ℝ) ≤ Real.exp (10 ^ 16 * (Real.log (1 / ε) + 2) ^ 4) := by
  set K := ⌈1 / ε⌉₊ with hK
  have hu1 : 1 < 1 / ε := by rw [lt_div_iff₀ hε0]; linarith
  have hlog0 : 0 < Real.log (1 / ε) := Real.log_pos hu1
  have hc5 : (pc 5 K : ℝ) ≤ Real.log (1 / ε) + 2 := pc_le_log (by norm_num) hε0 (by linarith)
  have hc13 : (pc 13 K : ℝ) ≤ Real.log (1 / ε) + 2 := pc_le_log (by norm_num) hε0 (by linarith)
  -- opaque names for `X = log(1/ε) + 2`, `X²` and `X⁴`
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = Real.log (1 / ε) + 2 := ⟨_, rfl⟩
  rw [← hX] at hc5 hc13
  have hX2 : 2 ≤ X := by rw [hX]; linarith
  have hlogX : Real.log (1 / ε) ≤ X := by rw [hX]; linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = X ^ 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = X ^ 4 := ⟨_, rfl⟩
  have hfinal : Real.exp (10 ^ 16 * Z) = Real.exp (10 ^ 16 * (Real.log (1 / ε) + 2) ^ 4) := by
    rw [hZ, hX]
  have hY4 : 4 ≤ Y := by rw [hY]; nlinarith
  have hYZ : Y * Y = Z := by rw [hY, hZ, ← pow_add]
  have hXY : X ≤ Y := by rw [hY]; nlinarith
  obtain ⟨hA5, hN5⟩ := qA_qn_le (p := 5) (K := K) (by norm_num) hc5 hX2
  obtain ⟨hA13, hN13⟩ := qA_qn_le (p := 13) (K := K) (by norm_num) hc13 hX2
  rw [← hY] at hA5 hN5 hA13 hN13
  clear hY hZ hX
  have hYZ' : Y ≤ Z := by rw [← hYZ]; nlinarith
  have hZ16 : 16 ≤ Z := by rw [← hYZ]; nlinarith
  -- the digit sizes, opaque
  obtain ⟨N5, hN5def⟩ : ∃ N5 : ℕ, N5 = qn 5 K + 4 := ⟨_, rfl⟩
  obtain ⟨N13, hN13def⟩ : ∃ N13 : ℕ, N13 = qn 13 K + 4 := ⟨_, rfl⟩
  rw [← hN5def] at hN5
  rw [← hN13def] at hN13
  have hN5n : (0 : ℝ) ≤ (N5 : ℝ) := by positivity
  have hN13n : (0 : ℝ) ≤ (N13 : ℝ) := by positivity
  have hN5sq : (N5 : ℝ) * N5 ≤ 45796000000 * Z := by
    calc (N5 : ℝ) * N5 ≤ (214000 * Y) * (214000 * Y) :=
          mul_le_mul hN5 hN5 hN5n (by positivity)
      _ = 45796000000 * (Y * Y) := by ring
      _ = 45796000000 * Z := by rw [hYZ]
  have hN13sq : (N13 : ℝ) * N13 ≤ 45796000000 * Z := by
    calc (N13 : ℝ) * N13 ≤ (214000 * Y) * (214000 * Y) :=
          mul_le_mul hN13 hN13 hN13n (by positivity)
      _ = 45796000000 * (Y * Y) := by ring
      _ = 45796000000 * Z := by rw [hYZ]
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 20000000000000 * Z := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  -- `X0 ≤ exp E`
  have hX0 : dataQ.X0 ε ≤ Real.exp E := by
    unfold ArcData.X0
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · show 20 / ηQ ε ≤ Real.exp E
      refine (inv_ηQ_le ε).trans (Real.exp_le_exp.mpr ?_)
      rw [← hK]
      push_cast
      linarith
    · show (MdigQ ε : ℝ) ≤ Real.exp E
      have hM := MdigQ_le ε
      rw [← hK, ← hN5def, ← hN13def] at hM
      calc (MdigQ ε : ℝ) ≤ 2 ^ ((88 + 192 * N5 ^ 2) + (88 + 192 * N13 ^ 2)) := hM
        _ ≤ Real.exp (((88 + 192 * N5 ^ 2) + (88 + 192 * N13 ^ 2) : ℕ) : ℝ) := two_pow_le_exp _
        _ ≤ Real.exp E := by
            apply Real.exp_le_exp.mpr
            push_cast
            rw [sq, sq]
            linarith
    · calc 1 / ε = Real.exp (Real.log (1 / ε)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp E := Real.exp_le_exp.mpr (by linarith)
    · show BdQ ε ≤ Real.exp E
      have hB := BdQ_le ε
      rw [← hK, ← hN5def, ← hN13def] at hB
      push_cast at hB
      calc BdQ ε ≤ 2 * ((N5 : ℝ) + N13) := hB
        _ ≤ Real.exp (2 * ((N5 : ℝ) + N13)) := le_exp_self' _
        _ ≤ Real.exp E := Real.exp_le_exp.mpr (by linarith)
  have hG : (dataQ.G ε : ℝ) ≤ Real.exp (E + 68) := G_le_exp hε0 hE0 hX0
  -- `|RotsQ| ≤ exp E`
  have hRots : ((dataQ.Rots ε).card : ℝ) ≤ Real.exp E := by
    show ((RotsQ ε).card : ℝ) ≤ Real.exp E
    have hc := card_RotsQ_le ε
    rw [← hK, ← hN5def, ← hN13def] at hc
    have h1 : ((RotsQ ε).card : ℝ) ≤ ((16 ^ (2 * (N5 + N13) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hc
    have h2 : ((16 ^ (2 * (N5 + N13) + 1) : ℕ) : ℝ) =
        (2 : ℝ) ^ (4 * (2 * (N5 + N13) + 1)) := by
      push_cast; rw [pow_mul]; norm_num
    calc ((RotsQ ε).card : ℝ) ≤ (2 : ℝ) ^ (4 * (2 * (N5 + N13) + 1)) := h1.trans h2.le
      _ ≤ Real.exp ((4 * (2 * (N5 + N13) + 1) : ℕ) : ℝ) := two_pow_le_exp _
      _ ≤ Real.exp E := by
          apply Real.exp_le_exp.mpr
          push_cast
          linarith
  -- conclusion
  have hmain := dataQ.minCopies_le_Rots_G_pow dataQ_KL hε0 hε1
  have hG0 : (0 : ℝ) ≤ dataQ.G ε := by positivity
  calc (minCopies ε : ℝ) ≤ (dataQ.Rots ε).card * (dataQ.G ε : ℝ) ^ 88 := hmain
    _ ≤ Real.exp E * Real.exp (E + 68) ^ 88 :=
        mul_le_mul hRots (pow_le_pow_left₀ hG0 hG 88) (pow_nonneg hG0 88) (Real.exp_pos _).le
    _ = Real.exp (E + 88 * (E + 68)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
    _ ≤ Real.exp (10 ^ 16 * Z) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (10 ^ 16 * (Real.log (1 / ε) + 2) ^ 4) := hfinal

/-- **The quasi-polynomial bound.** `minCopies ε ≤ exp((log ε⁻¹)^5)` for
`0 < ε ≤ exp(-10^18)`. -/
theorem quasiPolynomialBound :
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀,
      (minCopies ε : ℝ) ≤ Real.exp (Real.log ε⁻¹ ^ C) := by
  refine ⟨5, Real.exp (-(10 ^ 18)), Real.exp_pos _, ?_⟩
  rintro ε ⟨hε0, hεle⟩
  have hbig : (10 : ℝ) < Real.exp (10 ^ 18) := by
    have := Real.add_one_le_exp ((10 : ℝ) ^ 18)
    have h : (10 : ℝ) < 10 ^ 18 + 1 := by norm_num
    linarith
  have h2 : (Real.exp (10 ^ 18))⁻¹ < 1 / 10 := by
    rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num), one_div, inv_inv]
    exact hbig
  have hε1 : ε < 1 / 10 := lt_of_le_of_lt hεle (by rw [Real.exp_neg]; exact h2)
  have ht : (10 : ℝ) ^ 18 ≤ Real.log (1 / ε) := by
    have h := Real.log_le_log hε0 hεle
    rw [Real.log_exp] at h
    rw [one_div, Real.log_inv]
    linarith
  have hmain := quasiPolynomialBound_explicit hε0 hε1
  refine hmain.trans (Real.exp_le_exp.mpr ?_)
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← one_div]
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.log (1 / ε) := ⟨_, rfl⟩
  rw [← htdef] at ht ⊢
  have h2t : t + 2 ≤ 2 * t := by linarith
  have ht0 : 0 ≤ t + 2 := by linarith
  have ht4 : 0 ≤ t ^ 4 := by positivity
  have h16 : (16 : ℝ) * 10 ^ 16 ≤ t := by linarith
  calc 10 ^ 16 * (t + 2) ^ 4 ≤ 10 ^ 16 * (2 * t) ^ 4 := by gcongr
    _ = (16 * 10 ^ 16) * t ^ 4 := by ring
    _ ≤ t * t ^ 4 := mul_le_mul_of_nonneg_right h16 ht4
    _ = t ^ 5 := by ring

/-- The quasi-polynomial target, in the form of a Formal Conjectures `answer(True)` statement. -/
theorem green_41_quasi_polynomial_bound_solved : answer(True) ↔
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀,
      (minCopies ε : ℝ) ≤ Real.exp (Real.log ε⁻¹ ^ C) :=
  ⟨fun _ => quasiPolynomialBound, fun _ => trivial⟩

#print axioms green_41_quasi_polynomial_bound_solved

end Green41Proof
