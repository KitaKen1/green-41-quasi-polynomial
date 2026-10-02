import Green41SingleExponential.MinorArcDigit
import Green41SingleExponential.AssemblyDigit

/-!
# Digit multipliers read modulo a lower power

In the discrete core the multiplier of a rotation is computed in `ZMod (pⁿ)` (where the labels
live) and then only its residue modulo `p^ℓ`, `ℓ ≤ n`, matters. `exists_digit_multiplier_cast`
shows that the digit family at level `ℓ` reaches every unit modulo `p^ℓ` in this sense. The proof
reruns the digit cover in `ZMod (p^ℓ)` on the images of the level-`n` multipliers; the
first-order shape `1 + p^k (unit) + p^(k+1) (·)` of a digit survives the reduction.

The rotations used are the inverses `Ā/A` of the digit rotations, whose numerators `Ā` have
multiplier `mult (star A)`; `digitRotInvFinset` collects them.
-/

namespace Green41Proof

open Green41 Green41SingleExponential

open Complex Finset

/-- The residue modulo `p^ℓ` of an element of `ZMod (pⁿ)`, through its value. -/
lemma val_cast_eq_castHom' {p n ℓ : ℕ} [NeZero (p ^ n)] (h : ℓ ≤ n) (a : ZMod (p ^ n)) :
    ((a.val : ℕ) : ZMod (p ^ ℓ)) = ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ ℓ)) a := by
  rw [ZMod.natCast_val, ZMod.castHom_apply]

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

/-- **Every unit modulo `p^ℓ` is a reduced digit multiplier.** If the reduction of the level-`n`
multiplier of `ρ̄/ρ` generates the units modulo `p^ℓ`, then every unit modulo `p^ℓ` is the
reduction of the level-`n` multiplier `mult (star A) n` of some `A` in the digit family at
level `ℓ`. -/
theorem exists_digit_multiplier_cast (hp2 : p ≠ 2) {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    {ρ : GaussianInt} (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ)
    (hord : orderOf (((hπ.mult (star ρ) n).val : ℕ) : ZMod (p ^ ℓ)) = (p - 1) * p ^ (ℓ - 1))
    (u : ZMod (p ^ ℓ)) (hu : IsUnit u) :
    ∃ A ∈ digitFamily p ℓ ρ, (((hπ.mult (star A) n).val : ℕ) : ZMod (p ^ ℓ)) = u := by
  have hn0 : 0 < n := by omega
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  have : NeZero (p ^ ℓ) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  set φ := ZMod.castHom (pow_dvd_pow p hℓn) (ZMod (p ^ ℓ)) with hφ
  have hval : ∀ x : ZMod (p ^ n), ((x.val : ℕ) : ZMod (p ^ ℓ)) = φ x :=
    fun x => val_cast_eq_castHom' hℓn x
  set b := φ (hπ.mult (star ρ) n) with hb
  have hbu : IsUnit b := (hπ.isUnit_mult hn0 hρ2 (by rwa [star_star])).map φ
  have hcard : orderOf b = Nat.card (ZMod (p ^ ℓ))ˣ := by
    rw [hb, ← hval, hord, card_units_prime_pow hπ.prime hℓ]
  have hgen : ∀ u : ZMod (p ^ ℓ), IsUnit u → ∃ t, b ^ t = u := by
    intro u hu
    obtain ⟨t, -, ht⟩ := exists_pow_eq_of_orderOf_eq_card _ hcard u hu
    exact ⟨t, ht⟩
  obtain ⟨m, hm, d, hd, hu'⟩ := exists_mul_digits hπ.prime hℓ hbu hgen
    (fun j => φ (hπ.mult (star (digitInt p j)) n))
    (fun k hk1 _ => by
      obtain ⟨z, hz⟩ := hπ.mult_star_digitInt (n := n) hn0 hk1
      refine ⟨φ (-2 * rootψ π p n), φ z, (hπ.isUnit_neg_two_mul_root hp2 n).map φ, ?_⟩
      rw [hz]
      simp only [map_add, map_mul, map_pow, map_one, map_natCast])
    u hu
  refine ⟨ρ ^ m * ∏ j ∈ Ico 1 ℓ, digitInt p j ^ d j, ⟨m, hm, d, hd, rfl⟩, ?_⟩
  have hdig : ∀ j ∈ Ico 1 ℓ, ¬ π ∣ digitInt p j ^ d j := fun j hj h =>
    hπ.not_dvd_digitInt (mem_Ico.mp hj).1 (hπ.prime_π.dvd_of_dvd_pow h)
  have hprod : ¬ π ∣ ∏ j ∈ Ico 1 ℓ, digitInt p j ^ d j := by
    rw [hπ.prime_π.dvd_finsetProd_iff]
    rintro ⟨j, hj, h⟩
    exact hdig j hj h
  have hρm : ¬ π ∣ ρ ^ m := fun h => hρ1 (hπ.prime_π.dvd_of_dvd_pow h)
  rw [hval, hπ.mult_star_mul hn0 hρm hprod, hπ.mult_star_pow hn0 hρ1,
    hπ.mult_star_prod hn0 _ _ hdig, map_mul, map_pow, map_prod, hu']
  congr 1
  refine prod_congr rfl fun j hj => ?_
  rw [hπ.mult_star_pow hn0 (hπ.not_dvd_digitInt (mem_Ico.mp hj).1), map_pow]

omit hπ in
/-- Members of the digit family divide the conjugate of the digit denominator. -/
lemma dvd_star_digitDen {N : ℕ} {ρ A : GaussianInt} (hA : A ∈ digitFamily p N ρ) :
    A ∣ star (digitDen p N ρ) := by
  obtain ⟨c, hc⟩ := star_dvd_digitDen hA
  exact ⟨star c, by rw [hc, star_mul', star_star]⟩

lemma not_dvd_star_digitDen {N : ℕ} {ρ : GaussianInt} (hρ1 : ¬ π ∣ ρ) :
    ¬ π ∣ star (digitDen p N ρ) := by
  intro h
  apply hπ.not_star_dvd_digitDen (N := N) hρ1
  obtain ⟨c, hc⟩ := h
  exact ⟨star c, by rw [← star_star (digitDen p N ρ), hc, star_mul']⟩

end DigitPrime

/-- The inverse digit rotations `Ā/A`. -/
noncomputable def digitRotInvFinset (p N : ℕ) (ρ : GaussianInt) : Finset ℂ :=
  (digitFamilyFinset p N ρ).image fun A : GaussianInt => ((star A : GaussianInt) : ℂ) / (A : ℂ)

lemma mem_digitRotInvFinset_of_mem {p N : ℕ} {ρ A : GaussianInt}
    (hA : A ∈ DigitPrime.digitFamily p N ρ) :
    ((star A : GaussianInt) : ℂ) / (A : ℂ) ∈ digitRotInvFinset p N ρ :=
  Finset.mem_image.mpr ⟨A, mem_digitFamilyFinset_of_mem hA, rfl⟩

lemma card_digitRotInvFinset_le (p N : ℕ) (ρ : GaussianInt) :
    (digitRotInvFinset p N ρ).card ≤ (p - 1) * p ^ (N - 1) := by
  calc (digitRotInvFinset p N ρ).card ≤ (digitFamilyFinset p N ρ).card := Finset.card_image_le
    _ ≤ ((range (p - 1)) ×ˢ (Fintype.piFinset fun _ : Fin (N - 1) => range p)).card :=
        Finset.card_image_le
    _ = (p - 1) * p ^ (N - 1) := by
        rw [Finset.card_product, Fintype.card_piFinset, Finset.card_range]
        simp

lemma norm_of_mem_digitRotInvFinset {p N : ℕ} {ρ : GaussianInt} (hρ : ρ ≠ 0) {ν : ℂ}
    (hν : ν ∈ digitRotInvFinset p N ρ) : ‖ν‖ = 1 := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hν
  have hA0 := ne_zero_of_mem_digitFamilyFinset hρ hA
  have hA0' : (A : ℂ) ≠ 0 := by rw [Ne, GaussianInt.toComplex_eq_zero]; exact hA0
  rw [norm_div, GaussianInt.toComplex_star, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hA0')]

lemma one_mem_digitRotInvFinset {p N : ℕ} (hp : 2 ≤ p) (ρ : GaussianInt) :
    (1 : ℂ) ∈ digitRotInvFinset p N ρ := by
  refine Finset.mem_image.mpr ⟨1, Finset.mem_image.mpr ⟨(0, fun _ => 0), ?_, ?_⟩, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show 0 < p - 1 by omega),
      Fintype.mem_piFinset.mpr fun _ => Finset.mem_range.mpr (show 0 < p by omega)⟩
  · simp
  · simp

end Green41Proof
