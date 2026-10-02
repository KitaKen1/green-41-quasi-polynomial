import Mathlib

/-!
# Base-`p` digit covers of `ZMod (p ^ N)`

This is the "binary lifting" step behind the single-exponential bound. The double-exponential
proof reaches every unit modulo `p ^ N` with the powers `b ^ t`, `t < (p - 1) p ^ (N - 1)`, of a
single generator, so it needs a denominator of size exponential in `N`. Here a unit is instead
written as `b ^ m * ∏_{1 ≤ k < N} g k ^ d k` with `m < p - 1` and digits `d k < p`, where `g k` is
any element that is `1 + p ^ k c` (`c` a unit) to first order. Only `p - 2 + (p - 1) (N - 1)`
factors are used in total.

* `one_add_mul_pow_eq`: `(1 + P u) ^ d = 1 + d P u + P ^ 2 v`.
* `exists_digits`: every `x ≡ 1 (mod p ^ k)` is `∏_{k ≤ j < N} g j ^ d j` with `d j < p`.
* `exists_pow_sub_one_eq`: Fermat lifted to `ZMod (p ^ N)`: `x ^ (p - 1) ≡ 1 (mod p)`.
* `exists_mul_digits`: every unit is `b ^ m * ∏_{1 ≤ j < N} g j ^ d j` with `m < p - 1`.
-/

namespace Green41SingleExponential

open Finset

section Ring

variable {R : Type*} [CommRing R]

/-- `(1 + P u) ^ d = 1 + d P u + P ^ 2 v` for some `v`. -/
lemma one_add_mul_pow_eq (P u : R) (d : ℕ) :
    ∃ v : R, (1 + P * u) ^ d = 1 + d * P * u + P ^ 2 * v := by
  induction d with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨d * u ^ 2 + v * (1 + P * u), ?_⟩
    rw [pow_succ, hv]
    push_cast
    ring

end Ring

section Digits

variable {p N : ℕ}

/-- In `ZMod (p ^ N)`, `p ^ k = 0` as soon as `N ≤ k`. -/
lemma natCast_pow_eq_zero_of_le {k : ℕ} (h : N ≤ k) : (p : ZMod (p ^ N)) ^ k = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

/-- Elements `1 + p ^ k u` with `k ≥ 1` are units of `ZMod (p ^ N)`. -/
lemma isUnit_one_add_pow_mul {k : ℕ} (hk : 1 ≤ k) (u : ZMod (p ^ N)) :
    IsUnit (1 + (p : ZMod (p ^ N)) ^ k * u) := by
  apply IsNilpotent.isUnit_one_add
  refine ⟨N, ?_⟩
  rw [mul_pow, ← pow_mul, natCast_pow_eq_zero_of_le (by nlinarith), zero_mul]

/-- **Base-`p` digits.** If for `1 ≤ k < N` the element `g k` is `1 + p ^ k c + p ^ (k + 1) z`
with `c` a unit, then every `x ≡ 1 (mod p ^ k)` is a product `∏_{k ≤ j < N} g j ^ d j` with
digits `d j < p`. (Stated with `N = k + m` so that the induction runs on `m`.) -/
theorem exists_digits (hp : p.Prime) (g : ℕ → ZMod (p ^ N))
    (hg : ∀ k, 1 ≤ k → k < N → ∃ c z : ZMod (p ^ N), IsUnit c ∧
      g k = 1 + (p : ZMod (p ^ N)) ^ k * c + (p : ZMod (p ^ N)) ^ (k + 1) * z) :
    ∀ m k, N = k + m → 1 ≤ k → ∀ x : ZMod (p ^ N),
      (∃ y, x = 1 + (p : ZMod (p ^ N)) ^ k * y) →
      ∃ d : ℕ → ℕ, (∀ j, d j < p) ∧ x = ∏ j ∈ Ico k N, g j ^ d j := by
  have hN0 : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  intro m
  induction m with
  | zero =>
    intro k hk _ x hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨fun _ => 0, fun _ => hp.pos, ?_⟩
    rw [hy, natCast_pow_eq_zero_of_le (by omega), zero_mul, add_zero,
      Finset.Ico_eq_empty_of_le (by omega), Finset.prod_empty]
  | succ m ih =>
    intro k hk hk1 x hx
    obtain ⟨y, hy⟩ := hx
    have hkN : k < N := by omega
    obtain ⟨c, z, hc, hgk⟩ := hg k hk1 hkN
    set P : ZMod (p ^ N) := (p : ZMod (p ^ N)) with hP
    -- the digit `d₀ ≡ y / c (mod p)`
    set t : ZMod (p ^ N) := y * c⁻¹ with ht
    set d₀ : ℕ := t.val % p with hd₀
    have hd₀lt : d₀ < p := Nat.mod_lt _ hp.pos
    have hcinv : c * c⁻¹ = 1 := ZMod.mul_inv_of_unit c hc
    have hts : t = (d₀ : ZMod (p ^ N)) + P * ((t.val / p : ℕ) : ZMod (p ^ N)) := by
      have h := Nat.mod_add_div t.val p
      conv_lhs => rw [← ZMod.natCast_zmod_val t, ← h]
      push_cast
      ring
    have hyct : y = c * t := by
      rw [ht, ← mul_assoc, mul_comm c y, mul_assoc, hcinv, mul_one]
    -- expand `g k ^ d₀`
    obtain ⟨v, hv⟩ := one_add_mul_pow_eq (P ^ k) (c + P * z) d₀
    have hgk' : g k = 1 + P ^ k * (c + P * z) := by rw [hgk]; ring
    set G : ZMod (p ^ N) := g k ^ d₀ with hG
    have hGu : IsUnit G := by
      rw [hG, hgk']
      exact (isUnit_one_add_pow_mul hk1 _).pow _
    have hGinv : G * G⁻¹ = 1 := ZMod.mul_inv_of_unit G hGu
    -- `x = G + p ^ (k + 1) r`
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    set r : ZMod (p ^ N) :=
      c * ((t.val / p : ℕ) : ZMod (p ^ N)) - d₀ * z - P ^ k' * v with hr
    have hxG : x = G + P ^ (k' + 1 + 1) * r := by
      rw [hy, hG, hgk', hv, hyct, hts, hr]
      ring
    -- the remaining factor is `≡ 1 (mod p ^ (k + 1))`
    set x' : ZMod (p ^ N) := 1 + P ^ (k' + 1 + 1) * (r * G⁻¹) with hx'
    have hxx' : x = G * x' := by
      rw [hxG, hx']
      linear_combination (-(P ^ (k' + 1 + 1) * r)) * hGinv
    obtain ⟨d', hd'lt, hd'⟩ := ih (k' + 1 + 1) (by omega) (by omega) x' ⟨r * G⁻¹, rfl⟩
    refine ⟨fun j => if j = k' + 1 then d₀ else d' j, ?_, ?_⟩
    · intro j
      dsimp only
      split_ifs
      · exact hd₀lt
      · exact hd'lt j
    · beta_reduce
      rw [Finset.prod_eq_prod_Ico_succ_bot hkN, if_pos rfl, hxx', hd']
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [if_neg (by rw [Finset.mem_Ico] at hj; omega)]

/-- Fermat's little theorem lifted to `ZMod (p ^ N)`: for a unit `x`, `x ^ (p - 1) ≡ 1 (mod p)`. -/
lemma exists_pow_sub_one_eq (hp : p.Prime) (hN : 1 ≤ N) {x : ZMod (p ^ N)} (hx : IsUnit x) :
    ∃ y, x ^ (p - 1) = 1 + (p : ZMod (p ^ N)) * y := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hdvd : p ∣ p ^ N := dvd_pow_self p (by omega)
  set φ := ZMod.castHom hdvd (ZMod p) with hφ
  have hφx : φ x ≠ 0 := (hx.map φ).ne_zero
  have hferm : φ x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hφx
  have hz : φ (x ^ (p - 1) - 1) = 0 := by rw [map_sub, map_pow, hferm, map_one, sub_self]
  have hval : p ∣ (x ^ (p - 1) - 1).val := by
    rw [← ZMod.natCast_eq_zero_iff, ZMod.natCast_val, ← ZMod.castHom_apply (h := hdvd)]
    exact hz
  obtain ⟨s, hs⟩ := hval
  refine ⟨(s : ZMod (p ^ N)), ?_⟩
  have h1 : x ^ (p - 1) - 1 = (p : ZMod (p ^ N)) * s := by
    rw [← ZMod.natCast_zmod_val (x ^ (p - 1) - 1), hs]
    push_cast
    ring
  linear_combination h1

/-- **Digit cover of the units.** If `b` generates `(ZMod (p ^ N))ˣ`, every unit `u` is
`b ^ m * ∏_{1 ≤ j < N} g j ^ d j` with `m < p - 1` and digits `d j < p`. -/
theorem exists_mul_digits (hp : p.Prime) (hN : 1 ≤ N) {b : ZMod (p ^ N)} (hbu : IsUnit b)
    (hb : ∀ u : ZMod (p ^ N), IsUnit u → ∃ t, b ^ t = u)
    (g : ℕ → ZMod (p ^ N))
    (hg : ∀ k, 1 ≤ k → k < N → ∃ c z : ZMod (p ^ N), IsUnit c ∧
      g k = 1 + (p : ZMod (p ^ N)) ^ k * c + (p : ZMod (p ^ N)) ^ (k + 1) * z)
    (u : ZMod (p ^ N)) (hu : IsUnit u) :
    ∃ m < p - 1, ∃ d : ℕ → ℕ, (∀ j, d j < p) ∧ u = b ^ m * ∏ j ∈ Ico 1 N, g j ^ d j := by
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  obtain ⟨t, ht⟩ := hb u hu
  -- `t = m + (p - 1) s`, and `b ^ (p - 1) ≡ 1 (mod p)` by Fermat
  have htms : t = t % (p - 1) + (p - 1) * (t / (p - 1)) := (Nat.mod_add_div t (p - 1)).symm
  obtain ⟨y, hy⟩ := exists_pow_sub_one_eq hp hN hbu
  obtain ⟨v, hv⟩ := one_add_mul_pow_eq (p : ZMod (p ^ N)) y (t / (p - 1))
  have hx : ∃ y', (b ^ (p - 1)) ^ (t / (p - 1)) = 1 + (p : ZMod (p ^ N)) ^ 1 * y' :=
    ⟨(t / (p - 1) : ℕ) * y + p * v, by rw [hy, hv]; ring⟩
  obtain ⟨d, hdlt, hd⟩ := exists_digits hp g hg (N - 1) 1 (by omega) le_rfl _ hx
  refine ⟨t % (p - 1), Nat.mod_lt _ hp1, d, hdlt, ?_⟩
  rw [← ht, ← hd, ← pow_mul, ← pow_add, ← htms]

end Digits

end Green41SingleExponential
