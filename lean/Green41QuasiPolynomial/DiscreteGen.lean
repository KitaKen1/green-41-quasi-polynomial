import Green41DoubleExponentialFC

/-!
# The discrete core for an arbitrary family of multipliers

`Green41Proof.discrete_core` uses the multipliers `Bʷ`, `w < (p - 1) p^(ℓ-1)`, but its proof only
needs two facts about them: they are pairwise distinct modulo `N = p^ℓ`, and there are at least
`4N/5` of them. `discrete_core_gen` states the discrete core for any finite family `M i`,
`i ∈ I`, with these two properties. The proof is the same Fejér-kernel argument.
-/

namespace Green41Proof

open Green41

open Complex Finset

/-- `sum_w_norm_sq_le` for a family `M i`, `i ∈ I`, that is injective modulo `N`. -/
lemma sum_fam_norm_sq_le {N : ℕ} (hN : 0 < N) {m : ℤ} (hm : m ≠ 0) (Y : Finset ℕ)
    (hinj : Set.InjOn (· % N) Y) {ι : Type*} (I : Finset ι) (M : ι → ℕ)
    (hM : Set.InjOn (fun i => (M i : ZMod N)) I) :
    ∑ i ∈ I, ‖∑ y ∈ Y, ex (m * (M i : ℝ) * y / N)‖ ^ 2 ≤ N * Y.card * m.natAbs := by
  have hres : ∀ i, ‖∑ y ∈ Y, ex (m * (M i : ℝ) * y / N)‖ =
      ‖∑ y ∈ Y, ex (m * ((M i % N : ℕ) : ℝ) * y / N)‖ := by
    intro i
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    have hdiv := Nat.mod_add_div (M i) N
    set q := M i / N with hq
    set r := M i % N with hr
    have h' : (M i : ℝ) = (r : ℝ) + N * (q : ℝ) := by
      exact_mod_cast hdiv.symm
    have : (m : ℝ) * (M i : ℝ) * y / N = m * (r : ℝ) * y / N + ((m * (q : ℤ) * y : ℤ) : ℝ) := by
      rw [h']; push_cast; field_simp
    rw [this, ex_add_intCast]
  simp_rw [hres]
  set f : ℕ → ℝ := fun u => ‖∑ y ∈ Y, ex (m * (u : ℝ) * y / N)‖ ^ 2 with hf
  have hinjU : Set.InjOn (fun i => M i % N) (I : Set ι) := by
    intro i₁ h₁ i₂ h₂ h
    apply hM h₁ h₂
    simp only at h ⊢
    rw [ZMod.natCast_eq_natCast_iff']
    exact h
  calc ∑ i ∈ I, f (M i % N)
      = ∑ u ∈ I.image (fun i => M i % N), f u := (Finset.sum_image hinjU).symm
    _ ≤ ∑ u ∈ range N, f u := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
          exact Finset.mem_range.mpr (Nat.mod_lt _ hN)
        · intro u _ _; positivity
    _ ≤ N * Y.card * m.natAbs := sum_norm_sq_char_le hN hm Y hinj

/-- Cauchy–Schwarz over the family: `‖Σᵢ σᵢ(m)‖ ≤ N √(|Y| |m|)`. -/
lemma norm_sum_fam_le {N : ℕ} (hN : 0 < N) {m : ℤ} (hm : m ≠ 0) (Y : Finset ℕ)
    (hinj : Set.InjOn (· % N) Y) {ι : Type*} (I : Finset ι) (M : ι → ℕ) (hIN : I.card ≤ N)
    (hM : Set.InjOn (fun i => (M i : ZMod N)) I) (γ : ℝ) :
    ‖∑ i ∈ I, ∑ y ∈ Y, ex (m * ((M i : ℝ) * ((y : ℝ) / N + γ)))‖ ≤
      N * Real.sqrt (Y.card * m.natAbs) := by
  have hfac : ∀ i, ‖∑ y ∈ Y, ex (m * ((M i : ℝ) * ((y : ℝ) / N + γ)))‖ =
      ‖∑ y ∈ Y, ex (m * (M i : ℝ) * y / N)‖ := by
    intro i
    have : ∑ y ∈ Y, ex (m * ((M i : ℝ) * ((y : ℝ) / N + γ))) =
        ex (m * (M i : ℝ) * γ) * ∑ y ∈ Y, ex (m * (M i : ℝ) * y / N) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [← ex_add]
      congr 1
      ring
    rw [this, norm_mul, norm_ex, one_mul]
  set a : ι → ℝ := fun i => ‖∑ y ∈ Y, ex (m * (M i : ℝ) * y / N)‖ with ha
  have hsum : ∑ i ∈ I, a i ≤ N * Real.sqrt (Y.card * m.natAbs) := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := I) (f := a)
    have hsq := sum_fam_norm_sq_le hN hm Y hinj I M hM
    have hbound : (∑ i ∈ I, a i) ^ 2 ≤ ((N : ℝ) * Real.sqrt (Y.card * m.natAbs)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      calc (∑ i ∈ I, a i) ^ 2 ≤ I.card * ∑ i ∈ I, a i ^ 2 := hcs
        _ ≤ N * (N * Y.card * m.natAbs) := by
            apply mul_le_mul (by exact_mod_cast hIN) hsq (by positivity) (by positivity)
        _ = (N : ℝ) ^ 2 * (Y.card * m.natAbs) := by ring
    exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun i _ => norm_nonneg _) (by positivity)
      two_ne_zero).mp hbound
  calc ‖∑ i ∈ I, ∑ y ∈ Y, ex (m * ((M i : ℝ) * ((y : ℝ) / N + γ)))‖
      ≤ ∑ i ∈ I, ‖∑ y ∈ Y, ex (m * ((M i : ℝ) * ((y : ℝ) / N + γ)))‖ := norm_sum_le _ _
    _ = ∑ i ∈ I, a i := by
        apply Finset.sum_congr rfl; intro i _; rw [hfac]
    _ ≤ N * Real.sqrt (Y.card * m.natAbs) := hsum

/-- A family that is injective modulo `N` has at most `N` members. -/
lemma card_le_of_injOn_mod {N : ℕ} (hN : 0 < N) {ι : Type*} (I : Finset ι) (M : ι → ℕ)
    (hM : Set.InjOn (fun i => (M i : ZMod N)) I) : I.card ≤ N := by
  have hinjU : Set.InjOn (fun i => M i % N) (I : Set ι) := by
    intro i₁ h₁ i₂ h₂ h
    apply hM h₁ h₂
    simp only at h ⊢
    rw [ZMod.natCast_eq_natCast_iff']
    exact h
  calc I.card = (I.image (fun i => M i % N)).card := (Finset.card_image_of_injOn hinjU).symm
    _ ≤ (range N).card := by
        apply Finset.card_le_card
        intro u hu
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_range.mpr (Nat.mod_lt _ hN)
    _ = N := card_range N

/-- **Discrete core for a family.** If `M i`, `i ∈ I`, are pairwise distinct modulo `N` and
`4N ≤ 5 |I|`, then some point `M i (y/N + γ)` (`i ∈ I`, `y ∈ Y`) is within `ε/2` of an
integer. -/
theorem discrete_core_gen {N H : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hH : 2 ≤ (H : ℝ) * ε ^ 2) {ι : Type*} (I : Finset ι) (M : ι → ℕ)
    (hM : Set.InjOn (fun i => (M i : ZMod N)) I) (hI : 4 * N ≤ 5 * I.card)
    (γ : ℝ) (Y : Finset ℕ) (hinj : Set.InjOn (· % N) Y) (hY : 25 * H ^ 3 < 4 * Y.card) :
    ∃ i ∈ I, ∃ y ∈ Y, |(M i : ℝ) * ((y : ℝ) / N + γ) -
      round ((M i : ℝ) * ((y : ℝ) / N + γ))| < ε / 2 := by
  by_contra hcon
  push Not at hcon
  set S := I.card with hSdef
  have hSN : S ≤ N := card_le_of_injOn_mod hN I M hM
  have h5S : 4 * N ≤ 5 * S := hI
  have hHpos : 0 < H := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · rw [h0] at hH; simp at hH; linarith
    · exact h0
  have hYpos : 0 < Y.card := by omega
  set t : ι → ℕ → ℝ := fun i y => (M i : ℝ) * ((y : ℝ) / N + γ) with ht
  -- upper bound on the kernel sum
  have hterm : ∀ i ∈ I, ∀ y ∈ Y, ‖∑ a ∈ range H, ex (a * t i y)‖ ^ 2 ≤ (1 / ε) ^ 2 := by
    intro i hi y hy
    have hfar := hcon i hi y hy
    have h := norm_geom_ex_le (x := t i y) (δ := ε / 2) (by positivity) hfar H
    rw [show 1 / (2 * (ε / 2)) = 1 / ε by field_simp] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hup : ∑ i ∈ I, ∑ y ∈ Y, ‖∑ a ∈ range H, ex (a * t i y)‖ ^ 2 ≤
      S * Y.card * (1 / ε) ^ 2 := by
    calc _ ≤ ∑ i ∈ I, ∑ y ∈ Y, (1 / ε) ^ 2 :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun y hy => hterm i hi y hy
      _ = S * Y.card * (1 / ε) ^ 2 := by simp [Finset.sum_const, hSdef]; ring
  -- expansion of the kernel
  have hexp : ∑ i ∈ I, ∑ y ∈ Y, ‖∑ a ∈ range H, ex (a * t i y)‖ ^ 2 =
      ∑ a ∈ range H, ∑ a' ∈ range H,
        (∑ i ∈ I, ∑ y ∈ Y, ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t i y)).re := by
    have h1 : ∀ i y, ‖∑ a ∈ range H, ex (a * t i y)‖ ^ 2 =
        ∑ a ∈ range H, ∑ a' ∈ range H, (ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t i y)).re := by
      intro i y
      rw [norm_sum_sq_eq, Complex.re_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl; intro a' _
      rw [ex_mul_conj]; congr 2; push_cast; ring
    simp_rw [h1]
    rw [sum_comm4]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro a' _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.re_sum]
  -- lower bound, term by term
  set c : ℝ := N * Real.sqrt (Y.card * H) with hc
  have hc0 : 0 ≤ c := by positivity
  have hlow : ∀ a ∈ range H, ∀ a' ∈ range H,
      (if a = a' then (S : ℝ) * Y.card else 0) - c ≤
        (∑ i ∈ I, ∑ y ∈ Y, ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t i y)).re := by
    intro a ha a' ha'
    by_cases haa : a = a'
    · subst haa
      have hX : (∑ i ∈ I, ∑ y ∈ Y, ex ((((a : ℤ) - (a : ℤ) : ℤ) : ℝ) * t i y)) =
          (S : ℂ) * Y.card := by
        simp only [sub_self, Int.cast_zero, zero_mul, ex_zero, Finset.sum_const,
          nsmul_eq_mul, mul_one, hSdef]
      rw [hX, if_pos rfl]
      have hre : ((S : ℂ) * (Y.card : ℂ)).re = (S : ℝ) * Y.card := by
        rw [← Nat.cast_mul, Complex.natCast_re, Nat.cast_mul]
      rw [hre]; linarith
    · simp only [haa, if_false, zero_sub]
      set m : ℤ := (a : ℤ) - (a' : ℤ) with hmdef
      have hm : m ≠ 0 := by intro h; apply haa; omega
      have hmH : m.natAbs ≤ H := by
        have h1 := Finset.mem_range.mp ha
        have h2 := Finset.mem_range.mp ha'
        omega
      have hnorm := norm_sum_fam_le hN hm Y hinj I M hSN hM γ
      have h2 : Real.sqrt (Y.card * m.natAbs) ≤ Real.sqrt (Y.card * H) := by
        apply Real.sqrt_le_sqrt
        have : (m.natAbs : ℝ) ≤ H := by exact_mod_cast hmH
        nlinarith [(Nat.cast_nonneg Y.card : (0 : ℝ) ≤ Y.card)]
      have h3 := neg_le_of_abs_le (Complex.abs_re_le_norm
        (∑ i ∈ I, ∑ y ∈ Y, ex ((m : ℝ) * t i y)))
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      calc -c ≤ -(N * Real.sqrt (Y.card * m.natAbs)) := by
            rw [hc]; nlinarith
        _ ≤ -‖∑ i ∈ I, ∑ y ∈ Y, ex ((m : ℝ) * t i y)‖ := by
            simp only [ht] at hnorm ⊢; linarith
        _ ≤ _ := h3
  have hinner : ∀ a ∈ range H, ∑ a' ∈ range H, ((if a = a' then (S : ℝ) * Y.card else 0) - c) =
      S * Y.card - H * c := by
    intro a ha
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos ha, Finset.sum_const, card_range,
      nsmul_eq_mul]
  have hsumlow : (H : ℝ) * (S * Y.card) - (H : ℝ) ^ 2 * c ≤
      ∑ a ∈ range H, ∑ a' ∈ range H,
        (∑ i ∈ I, ∑ y ∈ Y, ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t i y)).re := by
    calc (H : ℝ) * (S * Y.card) - (H : ℝ) ^ 2 * c =
          ∑ a ∈ range H, ((S : ℝ) * Y.card - H * c) := by
          rw [Finset.sum_const, card_range, nsmul_eq_mul]; ring
      _ = ∑ a ∈ range H, ∑ a' ∈ range H, ((if a = a' then (S : ℝ) * Y.card else 0) - c) := by
          apply Finset.sum_congr rfl; intro a ha; rw [hinner a ha]
      _ ≤ _ := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun a' ha' => hlow a ha a' ha'
  -- combine
  have hHε : (1 / ε) ^ 2 ≤ (H : ℝ) / 2 := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hYr : (0 : ℝ) < Y.card := by exact_mod_cast hYpos
  have hSr : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmain : (H : ℝ) * (S * Y.card) - (H : ℝ) ^ 2 * c ≤ S * Y.card * ((H : ℝ) / 2) := by
    calc (H : ℝ) * (S * Y.card) - (H : ℝ) ^ 2 * c ≤ S * Y.card * (1 / ε) ^ 2 := by
          rw [← hexp] at hsumlow; linarith
      _ ≤ S * Y.card * ((H : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_left hHε; positivity
  -- `S Y ≤ 2 H c`
  have h1 : (S : ℝ) * Y.card ≤ 2 * H * c := by nlinarith
  have hc2 : c ^ 2 = (N : ℝ) ^ 2 * (Y.card * H) := by
    rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
  have h2 : ((S : ℝ) * Y.card) ^ 2 ≤ (2 * H * c) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  simp only [mul_pow] at h2
  rw [hc2] at h2
  have h3 : (S : ℝ) ^ 2 * Y.card ≤ 4 * (H : ℝ) ^ 3 * N ^ 2 := by
    have : (S : ℝ) ^ 2 * Y.card * Y.card ≤ 4 * (H : ℝ) ^ 3 * N ^ 2 * Y.card := by nlinarith
    exact le_of_mul_le_mul_right this hYr
  have h5 : (4 : ℝ) * N ≤ 5 * S := by exact_mod_cast h5S
  have h5sq : (16 : ℝ) * N ^ 2 ≤ 25 * S ^ 2 := by
    have := mul_le_mul h5 h5 (by positivity) (by positivity)
    nlinarith
  have h6 : (16 : ℝ) * N ^ 2 * Y.card ≤ 25 * S ^ 2 * Y.card :=
    mul_le_mul_of_nonneg_right h5sq hYr.le
  have h7 : (16 : ℝ) * Y.card * N ^ 2 ≤ 100 * (H : ℝ) ^ 3 * N ^ 2 := by nlinarith
  have h8 : (16 : ℝ) * Y.card ≤ 100 * (H : ℝ) ^ 3 :=
    le_of_mul_le_mul_right h7 (by positivity)
  have h9 : (25 : ℝ) * (H : ℝ) ^ 3 < 4 * Y.card := by exact_mod_cast hY
  linarith

end Green41Proof
