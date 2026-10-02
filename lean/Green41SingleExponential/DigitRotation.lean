import Green41DoubleExponentialFC
import Green41SingleExponential.DigitCover

/-!
# Digit rotations `ω_k = (1 + p^k i) / (1 - p^k i)`

The rotation `ω_k` acts on `ℤ[i]/πᴺ` as multiplication by `1 - 2 p^k r` to first order, where
`r² = -1`; that is, it is a "digit" at level `k` in the sense of
`Green41SingleExponential.exists_mul_digits`. Its denominator `1 - p^k i` has absolute value about
`p^k`, so the `N - 1` digit rotations together have a common denominator of size `p^{O(N²)}`,
while the powers `θ^t` of a single rotation needed to reach every unit have size `p^{N}`
exponents. This file proves:

* `DigitPrime.mult_star_digitInt`: the first-order form of the multiplier of `ω_k`;
* `DigitPrime.mult_star_mul`, `mult_star_pow`, `mult_star_prod`: multipliers are multiplicative;
* `DigitPrime.exists_digit_multiplier`: every unit modulo `pᴺ` is the multiplier of
  `ρ^m ∏_{1 ≤ j < N} (1 + p^j i)^{d_j}` with `m < p - 1` and `d_j < p`.
-/

namespace Green41Proof

open Green41SingleExponential Finset

/-- The Gaussian integer `1 + p ^ k i`. -/
def digitInt (p k : ℕ) : GaussianInt := ⟨1, (p : ℤ) ^ k⟩

lemma digitInt_norm (p k : ℕ) : (digitInt p k).norm = 1 + (p : ℤ) ^ (2 * k) := by
  simp only [digitInt, Zsqrtd.norm_def]
  ring

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

lemma not_dvd_of_norm {z : GaussianInt} {k : ℕ} (hk : 1 ≤ k)
    (hz : z.norm = 1 + (p : ℤ) ^ (2 * k)) : ¬ π ∣ z := by
  intro h
  have h1 := norm_dvd_norm h
  rw [hπ.norm, hz] at h1
  have h2 : (p : ℤ) ∣ (p : ℤ) ^ (2 * k) := dvd_pow_self _ (by omega)
  have h3 : (p : ℤ) ∣ 1 := (dvd_add_left h2).mp h1
  have h4 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h3
  exact hπ.prime.one_lt.ne' (by exact_mod_cast h4)

lemma not_dvd_digitInt {k : ℕ} (hk : 1 ≤ k) : ¬ π ∣ digitInt p k :=
  hπ.not_dvd_of_norm hk (digitInt_norm p k)

lemma not_dvd_star_digitInt {k : ℕ} (hk : 1 ≤ k) : ¬ π ∣ star (digitInt p k) :=
  hπ.not_dvd_of_norm hk (by rw [Zsqrtd.norm_conj, digitInt_norm])

lemma ψ_digitInt (n k : ℕ) :
    hπ.ψ n (digitInt p k) = 1 + (p : ZMod (p ^ n)) ^ k * rootψ π p n := by
  rw [ψ_apply]
  simp [digitInt]

lemma ψ_star_digitInt (n k : ℕ) :
    hπ.ψ n (star (digitInt p k)) = 1 - (p : ZMod (p ^ n)) ^ k * rootψ π p n := by
  rw [ψ_apply]
  simp [digitInt]
  ring

/-- The multiplier of `ω_k` is `1 + p^k (-2 r) + p^(k+1) z`. -/
lemma mult_star_digitInt {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) :
    ∃ z : ZMod (p ^ n), hπ.mult (star (digitInt p k)) n =
      1 + (p : ZMod (p ^ n)) ^ k * (-2 * rootψ π p n) + (p : ZMod (p ^ n)) ^ (k + 1) * z := by
  have hmul := hπ.mult_mul hn (ρ := star (digitInt p k))
    (by rw [star_star]; exact hπ.not_dvd_digitInt hk)
  rw [star_star, hπ.ψ_digitInt, hπ.ψ_star_digitInt] at hmul
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨(p : ZMod (p ^ n)) ^ j * rootψ π p n ^ 2 * (1 + hπ.mult (star (digitInt p (j + 1))) n),
    ?_⟩
  linear_combination (1 - (p : ZMod (p ^ n)) ^ (j + 1) * rootψ π p n) * hmul

lemma isUnit_neg_two_mul_root (hp2 : p ≠ 2) (n : ℕ) : IsUnit (-2 * rootψ π p n) := by
  have hr : IsUnit (rootψ π p n) := by
    refine IsUnit.of_mul_eq_one (-rootψ π p n) ?_
    rw [mul_neg, hπ.rootψ_mul_self, neg_neg]
  have h2 : IsUnit (((2 : ℤ) : ZMod (p ^ n))) := by
    refine isUnit_intCast_of_not_dvd hπ.prime ?_ n
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hπ.prime Nat.prime_two).mp h')
  have h2' : IsUnit (2 : ZMod (p ^ n)) := by simpa using h2
  have : -2 * rootψ π p n = -(2 * rootψ π p n) := by ring
  rw [this]
  exact (h2'.mul hr).neg

/-- Multipliers are multiplicative. -/
lemma mult_star_mul {n : ℕ} (hn : 0 < n) {x y : GaussianInt} (hx : ¬ π ∣ x) (hy : ¬ π ∣ y) :
    hπ.mult (star (x * y)) n = hπ.mult (star x) n * hπ.mult (star y) n := by
  have hxy : ¬ π ∣ x * y := fun h => (hπ.prime_π.dvd_or_dvd h).elim hx hy
  have h1 := hπ.mult_mul hn (ρ := star (x * y)) (by rwa [star_star])
  have h2 := hπ.mult_mul hn (ρ := star x) (by rwa [star_star])
  have h3 := hπ.mult_mul hn (ρ := star y) (by rwa [star_star])
  rw [star_star] at h1 h2 h3
  have hu : IsUnit (hπ.ψ n (x * y)) := (hπ.isUnit_ψ_iff hn _).mpr hxy
  apply hu.mul_right_cancel
  rw [h1, map_mul, mul_mul_mul_comm, h2, h3, star_mul', map_mul]

lemma mult_star_one {n : ℕ} : hπ.mult (star (1 : GaussianInt)) n = 1 := by
  simp only [mult, star_one, map_one, one_mul]
  simp

lemma mult_star_pow {n : ℕ} (hn : 0 < n) {x : GaussianInt} (hx : ¬ π ∣ x) (k : ℕ) :
    hπ.mult (star (x ^ k)) n = hπ.mult (star x) n ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, hπ.mult_star_one]
  | succ k ih =>
    rw [pow_succ, hπ.mult_star_mul hn (fun h => hx (hπ.prime_π.dvd_of_dvd_pow h)) hx, ih,
      pow_succ]

lemma mult_star_prod {n : ℕ} (hn : 0 < n) (s : Finset ℕ) (f : ℕ → GaussianInt)
    (hf : ∀ j ∈ s, ¬ π ∣ f j) :
    hπ.mult (star (∏ j ∈ s, f j)) n = ∏ j ∈ s, hπ.mult (star (f j)) n := by
  induction s using Finset.induction_on with
  | empty => rw [prod_empty, prod_empty, hπ.mult_star_one]
  | insert a s ha ih =>
    have hs : ¬ π ∣ ∏ j ∈ s, f j := by
      rw [hπ.prime_π.dvd_finsetProd_iff]
      rintro ⟨j, hj, hdvd⟩
      exact hf j (mem_insert_of_mem hj) hdvd
    rw [prod_insert ha, prod_insert ha, hπ.mult_star_mul hn (hf a (mem_insert_self a s)) hs,
      ih (fun j hj => hf j (mem_insert_of_mem hj))]

/-- The digit family `ρ^m ∏_{1 ≤ j < N} (1 + p^j i)^{d_j}`. -/
def digitFamily (p N : ℕ) (ρ : GaussianInt) : Set GaussianInt :=
  {A | ∃ m < p - 1, ∃ d : ℕ → ℕ, (∀ j, d j < p) ∧
    A = ρ ^ m * ∏ j ∈ Ico 1 N, digitInt p j ^ d j}

/-- **Every unit is a digit multiplier.** If `θ = ρ/ρ̄` generates the units modulo `pᴺ`, every
unit is the multiplier of some `ρ^m ∏_{1 ≤ j < N} (1 + p^j i)^{d_j}`, `m < p - 1`, `d_j < p`. -/
theorem exists_digit_multiplier (hp2 : p ≠ 2) {N : ℕ} (hN : 1 ≤ N) {ρ : GaussianInt}
    (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ)
    (hord : orderOf (hπ.mult (star ρ) N) = (p - 1) * p ^ (N - 1))
    (u : ZMod (p ^ N)) (hu : IsUnit u) :
    ∃ A ∈ digitFamily p N ρ, hπ.mult (star A) N = u := by
  have hN0 : 0 < N := hN
  have : NeZero (p ^ N) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  have hbu : IsUnit (hπ.mult (star ρ) N) := hπ.isUnit_mult hN0 hρ2 (by rwa [star_star])
  have hcard : orderOf (hπ.mult (star ρ) N) = Nat.card (ZMod (p ^ N))ˣ := by
    rw [hord, card_units_prime_pow hπ.prime hN]
  have hb : ∀ u : ZMod (p ^ N), IsUnit u → ∃ t, hπ.mult (star ρ) N ^ t = u := by
    intro u hu
    obtain ⟨t, -, ht⟩ := exists_pow_eq_of_orderOf_eq_card _ hcard u hu
    exact ⟨t, ht⟩
  obtain ⟨m, hm, d, hd, hu'⟩ := exists_mul_digits hπ.prime hN hbu hb
    (fun j => hπ.mult (star (digitInt p j)) N)
    (fun k hk1 _ => by
      obtain ⟨z, hz⟩ := hπ.mult_star_digitInt (n := N) hN0 hk1
      exact ⟨-2 * rootψ π p N, z, hπ.isUnit_neg_two_mul_root hp2 N, hz⟩)
    u hu
  refine ⟨ρ ^ m * ∏ j ∈ Ico 1 N, digitInt p j ^ d j, ⟨m, hm, d, hd, rfl⟩, ?_⟩
  have hdig : ∀ j ∈ Ico 1 N, ¬ π ∣ digitInt p j ^ d j := fun j hj h =>
    hπ.not_dvd_digitInt (mem_Ico.mp hj).1 (hπ.prime_π.dvd_of_dvd_pow h)
  have hprod : ¬ π ∣ ∏ j ∈ Ico 1 N, digitInt p j ^ d j := by
    rw [hπ.prime_π.dvd_finsetProd_iff]
    rintro ⟨j, hj, h⟩
    exact hdig j hj h
  have hρm : ¬ π ∣ ρ ^ m := fun h => hρ1 (hπ.prime_π.dvd_of_dvd_pow h)
  rw [hπ.mult_star_mul hN0 hρm hprod, hπ.mult_star_pow hN0 hρ1, hπ.mult_star_prod hN0 _ _ hdig,
    hu']
  congr 1
  refine prod_congr rfl fun j hj => ?_
  exact hπ.mult_star_pow hN0 (hπ.not_dvd_digitInt (mem_Ico.mp hj).1) _

end DigitPrime

end Green41Proof
