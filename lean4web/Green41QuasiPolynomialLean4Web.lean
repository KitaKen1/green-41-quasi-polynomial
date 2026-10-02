import Mathlib

#eval Lean.versionString

/-!
# Green's Problem 41: standalone Lean4Web proof of the quasi-polynomial bound

This file reproduces the Formal Conjectures definitions `pyjamaSet`, `coveringCopies` and
`minCopies` (`FormalConjectures/GreensOpenProblems/41.lean`) and proves, for some `C` and
`ε₀ > 0` and all `0 < ε ≤ ε₀`,

* `minCopies ε ≤ exp (exp (ε ^ (-C)))` (`green_41.variants.double_exponential_bound`),
* `minCopies ε ≤ exp (ε ^ (-C))` (`green_41.variants.single_exponential_bound`),
* `minCopies ε ≤ exp ((log ε⁻¹) ^ C)` (`green_41.variants.quasi_polynomial_bound`).

The last one comes from the explicit bound `minCopies ε ≤ exp (10^16 (log (1/ε) + 2)^4)` for
`0 < ε < 1/10` (`quasiPolynomialBound_explicit`). It uses mathlib only.

The first part is the double-exponential development. The second part replaces the cyclic orbit
of `ρ/ρ̄` in its Step A by base-`p` digit rotations `(1 + p^k i)/(1 - p^k i)`, and the third part
does the same in its discrete core.
-/

/- ## Section: `Defs` -/

/-
# Green 41: the Formal Conjectures definitions

The three definitions below are copied from
`FormalConjectures/GreensOpenProblems/41.lean` at Formal Conjectures commit
`40a8592cb6f7e96cb9a8275d96bb3e013feeb1dc`,
with the same `open` declarations. Only the `module`/`public` wrappers are dropped.
-/

namespace Green41

open Complex Set Pointwise

/--
The pyjama set is the set of points in the complex plane whose real part is within $\varepsilon$ of
an integer.
-/
def pyjamaSet (ε : ℝ) : Set ℂ :=
  { z | ∃ k : ℤ, |z.re - (k : ℝ)| ≤ ε }

/-- The set of valid numbers of rotated copies of the pyjama set of width ε that cover the plane. -/
def coveringCopies (ε : ℝ) : Set ℕ :=
  { n : ℕ | ∃ (Θ : Finset ℝ), Θ.card = n ∧
    (⋃ θ ∈ Θ, exp (θ * I) • pyjamaSet ε) = univ }

/-- The minimal number of rotated copies of the pyjama set of width ε needed to cover the plane. -/
noncomputable def minCopies (ε : ℝ) : ℕ :=
  sInf (coveringCopies ε)

/-- The right-hand side of `Green41.green_41.variants.double_exponential_bound` in FC. -/
def DoubleExponentialBound : Prop :=
  ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, (minCopies ε : ℝ) ≤ Real.exp (Real.exp (ε ^ (-C)))

end Green41

/- ## Section: `Bridge` -/

/-
# From a finite covering by unit rotations to a bound on `minCopies`

`InStripe ε u z` says that `z` lies in the open pyjama stripe of width `ε`
rotated by the unit complex number `u`, i.e. the real part of `u * z` is within
`ε` of an integer. A finite set of unit rotations covering the plane in this
sense bounds the FC quantity `minCopies ε`.
-/

namespace Green41

open Complex Set Pointwise

/-- `z` lies in the open stripe of width `ε` rotated by `u`. -/
def InStripe (ε : ℝ) (u z : ℂ) : Prop :=
  ∃ k : ℤ, |(u * z).re - k| < ε

lemma exp_neg_arg_mul_self {u : ℂ} (hu : ‖u‖ = 1) :
    Complex.exp (((-Complex.arg u : ℝ) : ℂ) * I) * u = 1 := by
  have h := Complex.norm_mul_exp_arg_mul_I u
  rw [hu, Complex.ofReal_one, one_mul] at h
  have h0 : ((-Complex.arg u : ℝ) : ℂ) * I + Complex.arg u * I = 0 := by
    push_cast
    ring
  calc Complex.exp (((-Complex.arg u : ℝ) : ℂ) * I) * u
      = Complex.exp (((-Complex.arg u : ℝ) : ℂ) * I) * Complex.exp (Complex.arg u * I) := by
        rw [h]
    _ = 1 := by rw [← Complex.exp_add, h0, Complex.exp_zero]

/-- A finite family of unit rotations whose open stripes cover `ℂ` bounds `minCopies`. -/
theorem minCopies_le_of_cover {ε : ℝ} (Ω : Finset ℂ) (hunit : ∀ u ∈ Ω, ‖u‖ = 1)
    (hcov : ∀ z : ℂ, ∃ u ∈ Ω, InStripe ε u z) : minCopies ε ≤ Ω.card := by
  classical
  set Θ : Finset ℝ := Ω.image (fun u => -Complex.arg u) with hΘ
  have hmem : Θ.card ∈ coveringCopies ε := by
    refine ⟨Θ, rfl, ?_⟩
    ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨u, hu, k, hk⟩ := hcov z
    refine ⟨-Complex.arg u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, ?_⟩
    rw [Set.mem_smul_set]
    refine ⟨u * z, ⟨k, hk.le⟩, ?_⟩
    rw [smul_eq_mul, ← mul_assoc, exp_neg_arg_mul_self (hunit u hu), one_mul]
  calc minCopies ε ≤ Θ.card := Nat.sInf_le hmem
    _ ≤ Ω.card := Finset.card_image_le

end Green41

/- ## Section: `Endgame` -/

/-
# The end game: from lattice confinement to a covering of the whole plane

This is Lemma 7.1 of the round-2 draft. Suppose the points not covered by a
finite rotation set `Θ` lie within `H` of the lattice `(D / L) ℤ[i]`, and a finite
set `U` of rational rotations `a / b` covers the disc of radius `2 L H`.
If `|D| > 2 L H Q`, where `Q` bounds the denominators, then the rotations
`θ u ν`, `θ u ν̄` (`θ ∈ Θ`, `u ∈ U`) together with `U` cover the plane, where
`ν = 1/(2L) + i √(1 - 1/(4L²))` satisfies `ν + ν̄ = 1/L`.
No coprimality of `a` and `b` is used.
-/

namespace Green41

open Complex ComplexConjugate

/-- A Gaussian integer of absolute value less than one is zero. -/
lemma gaussianInt_eq_zero_of_norm_lt_one {x : GaussianInt} (hx : ‖(x : ℂ)‖ < 1) : x = 0 := by
  have h1 : Complex.normSq (x : ℂ) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have h0 : 0 ≤ ‖(x : ℂ)‖ := norm_nonneg _
    nlinarith
  rw [← GaussianInt.intCast_real_norm] at h1
  have h2 : x.norm < 1 := by exact_mod_cast h1
  have h3 : x.norm = 0 := le_antisymm (by omega) (GaussianInt.norm_nonneg x)
  exact GaussianInt.norm_eq_zero.mp h3

/-- The integer-centre step: two lattice representations of `w` and `(a / b) w` with
errors at most `H` force `b k' = a k` once the lattice step `|D| / L` is large. -/
lemma center_eq {D a b k k' : GaussianInt} {L : ℕ} (hL : 0 < L) {H Q : ℝ} {w : ℂ}
    (hb : (b : ℂ) ≠ 0) (hab : ‖(a : ℂ)‖ = ‖(b : ℂ)‖) (hbQ : ‖(b : ℂ)‖ ≤ Q)
    (hD : 2 * L * H * Q < ‖(D : ℂ)‖)
    (hk : ‖w - (D : ℂ) / L * k‖ ≤ H)
    (hk' : ‖((a : ℂ) / b) * w - (D : ℂ) / L * k'‖ ≤ H) :
    b * k' = a * k := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set X : GaussianInt := a * k - b * k' with hX
  have hXc : (X : ℂ) = (a : ℂ) * k - (b : ℂ) * k' := by
    rw [hX, GaussianInt.toComplex_sub, GaussianInt.toComplex_mul, GaussianInt.toComplex_mul]
  have hkey : (D : ℂ) / L * X
      = (b : ℂ) * (((a : ℂ) / b) * w - (D : ℂ) / L * k') - (a : ℂ) * (w - (D : ℂ) / L * k) := by
    rw [hXc]
    field_simp
    ring
  have hH : 0 ≤ H := le_trans (norm_nonneg _) hk
  have hbound : ‖(D : ℂ) / L * X‖ ≤ 2 * Q * H := by
    rw [hkey]
    calc ‖(b : ℂ) * (((a : ℂ) / b) * w - (D : ℂ) / L * k') - (a : ℂ) * (w - (D : ℂ) / L * k)‖
        ≤ ‖(b : ℂ) * (((a : ℂ) / b) * w - (D : ℂ) / L * k')‖ + ‖(a : ℂ) * (w - (D : ℂ) / L * k)‖ :=
          norm_sub_le _ _
      _ = ‖(b : ℂ)‖ * ‖((a : ℂ) / b) * w - (D : ℂ) / L * k'‖ + ‖(a : ℂ)‖ * ‖w - (D : ℂ) / L * k‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ Q * H + Q * H := by
          rw [hab]
          have hb0 : 0 ≤ ‖(b : ℂ)‖ := norm_nonneg _
          have hQ : 0 ≤ Q := le_trans hb0 hbQ
          gcongr
      _ = 2 * Q * H := by ring
  have hX0 : X = 0 := by
    by_contra hne
    have h1 : 1 ≤ ‖(X : ℂ)‖ := by
      by_contra hlt
      exact hne (gaussianInt_eq_zero_of_norm_lt_one (lt_of_not_ge hlt))
    have hnorm : ‖(D : ℂ) / L * X‖ = ‖(D : ℂ)‖ / L * ‖(X : ℂ)‖ := by
      rw [norm_mul, norm_div, Complex.norm_natCast]
    have hDpos : 0 ≤ ‖(D : ℂ)‖ / L := div_nonneg (norm_nonneg _) hLr.le
    have h2 : ‖(D : ℂ)‖ / L ≤ 2 * Q * H := by
      calc ‖(D : ℂ)‖ / L = ‖(D : ℂ)‖ / L * 1 := by ring
        _ ≤ ‖(D : ℂ)‖ / L * ‖(X : ℂ)‖ := by gcongr
        _ = ‖(D : ℂ) / L * X‖ := hnorm.symm
        _ ≤ 2 * Q * H := hbound
    have h3 : ‖(D : ℂ)‖ ≤ 2 * L * H * Q := by
      rw [div_le_iff₀ hLr] at h2
      linarith
    linarith
  have : a * k - b * k' = 0 := hX0
  exact (sub_eq_zero.mp this).symm

/-- The irrational rotation `ν = 1/(2L) + i √(1 - 1/(4L²))`. -/
noncomputable def nu (L : ℕ) : ℂ :=
  ((1 / (2 * (L : ℝ)) : ℝ) : ℂ) + ((Real.sqrt (1 - 1 / (4 * (L : ℝ) ^ 2)) : ℝ) : ℂ) * I

lemma nu_re (L : ℕ) : (nu L).re = 1 / (2 * (L : ℝ)) := by
  simp [nu]

lemma nu_add_conj {L : ℕ} (hL : 0 < L) : nu L + conj (nu L) = 1 / (L : ℂ) := by
  rw [Complex.add_conj, nu_re]
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp

lemma norm_nu {L : ℕ} (hL : 0 < L) : ‖nu L‖ = 1 := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hs : 0 ≤ 1 - 1 / (4 * (L : ℝ) ^ 2) := by
    have : 1 / (4 * (L : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  have hre : (nu L).re = 1 / (2 * (L : ℝ)) := by simp [nu]
  have him : (nu L).im = Real.sqrt (1 - 1 / (4 * (L : ℝ) ^ 2)) := by simp [nu]
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have hn : Complex.normSq (nu L) = 1 := by
    rw [Complex.normSq_apply, hre, him, Real.mul_self_sqrt hs]
    field_simp
    ring
  rw [Complex.norm_def, hn, Real.sqrt_one]

/-- The rotation set of the end game. -/
noncomputable def endgameSet (Θ : Finset ℂ) (U : Finset (GaussianInt × GaussianInt)) (L : ℕ) :
    Finset ℂ := by
  classical
  exact ((Θ ×ˢ U).image fun x => x.1 * ((x.2.1 : ℂ) / x.2.2) * nu L) ∪
    ((Θ ×ˢ U).image fun x => x.1 * ((x.2.1 : ℂ) / x.2.2) * conj (nu L)) ∪
    (U.image fun p => (p.1 : ℂ) / p.2)

lemma card_endgameSet_le (Θ : Finset ℂ) (U : Finset (GaussianInt × GaussianInt)) (L : ℕ) :
    (endgameSet Θ U L).card ≤ 2 * Θ.card * U.card + U.card := by
  classical
  unfold endgameSet
  calc _ ≤ ((Θ ×ˢ U).image fun x => x.1 * ((x.2.1 : ℂ) / x.2.2) * nu L).card +
          ((Θ ×ˢ U).image fun x => x.1 * ((x.2.1 : ℂ) / x.2.2) * conj (nu L)).card +
          (U.image fun p => (p.1 : ℂ) / p.2).card := by
        refine (Finset.card_union_le _ _).trans ?_
        gcongr
        exact Finset.card_union_le _ _
    _ ≤ (Θ ×ˢ U).card + (Θ ×ˢ U).card + U.card := by
        gcongr <;> exact Finset.card_image_le
    _ = 2 * Θ.card * U.card + U.card := by
        rw [Finset.card_product]
        ring

lemma norm_of_mem_endgameSet {Θ : Finset ℂ} {U : Finset (GaussianInt × GaussianInt)} {L : ℕ}
    (hL : 0 < L) (hΘ : ∀ θ ∈ Θ, ‖θ‖ = 1)
    (hU : ∀ p ∈ U, (p.2 : ℂ) ≠ 0 ∧ ‖(p.1 : ℂ)‖ = ‖(p.2 : ℂ)‖) :
    ∀ v ∈ endgameSet Θ U L, ‖v‖ = 1 := by
  classical
  have hq : ∀ p ∈ U, ‖(p.1 : ℂ) / p.2‖ = 1 := by
    intro p hp
    obtain ⟨hb, hab⟩ := hU p hp
    rw [norm_div, hab, div_self (norm_ne_zero_iff.mpr hb)]
  intro v hv
  unfold endgameSet at hv
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product] at hv
  rcases hv with (⟨x, ⟨hx1, hx2⟩, rfl⟩ | ⟨x, ⟨hx1, hx2⟩, rfl⟩) | ⟨p, hp, rfl⟩
  · rw [norm_mul, norm_mul, hΘ _ hx1, hq _ hx2, norm_nu hL]; ring
  · rw [norm_mul, norm_mul, hΘ _ hx1, hq _ hx2, Complex.norm_conj, norm_nu hL]; ring
  · exact hq p hp

/-- Lemma 7.1 of the round-2 draft. -/
theorem endgame_cover {ε H Q : ℝ} {L : ℕ} (hL : 0 < L) {D : GaussianInt}
    (Θ : Finset ℂ) (U : Finset (GaussianInt × GaussianInt))
    (hconf : ∀ w : ℂ, (∀ θ ∈ Θ, ¬ InStripe ε θ w) →
      ∃ k : GaussianInt, ‖w - (D : ℂ) / L * k‖ ≤ H)
    (hU : ∀ p ∈ U, (p.2 : ℂ) ≠ 0 ∧ ‖(p.1 : ℂ)‖ = ‖(p.2 : ℂ)‖ ∧ ‖(p.2 : ℂ)‖ ≤ Q)
    (h1 : ((1 : GaussianInt), (1 : GaussianInt)) ∈ U)
    (hcover : ∀ e : ℂ, ‖e‖ ≤ 2 * L * H → ∃ p ∈ U, InStripe ε ((p.1 : ℂ) / p.2) e)
    (hD : 2 * L * H * Q < ‖(D : ℂ)‖) :
    ∀ z : ℂ, ∃ v ∈ endgameSet Θ U L, InStripe ε v z := by
  classical
  intro z
  by_contra hz
  push Not at hz
  have memν : ∀ θ ∈ Θ, ∀ p ∈ U, θ * ((p.1 : ℂ) / p.2) * nu L ∈ endgameSet Θ U L := by
    intro θ hθ p hp
    unfold endgameSet
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(θ, p), Finset.mem_product.mpr ⟨hθ, hp⟩, rfl⟩))
  have memν' : ∀ θ ∈ Θ, ∀ p ∈ U, θ * ((p.1 : ℂ) / p.2) * conj (nu L) ∈ endgameSet Θ U L := by
    intro θ hθ p hp
    unfold endgameSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(θ, p), Finset.mem_product.mpr ⟨hθ, hp⟩, rfl⟩))
  have memU : ∀ p ∈ U, ((p.1 : ℂ) / p.2) ∈ endgameSet Θ U L := by
    intro p hp
    unfold endgameSet
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have tr : ∀ θ u v : ℂ, InStripe ε θ (u * v * z) ↔ InStripe ε (θ * u * v) z := by
    intro θ u v
    unfold InStripe
    rw [show θ * (u * v * z) = θ * u * v * z by ring]
  -- lattice representations of `u v z` for `v ∈ {ν, ν̄}` and `u ∈ U`
  have rep : ∀ v : ℂ, (v = nu L ∨ v = conj (nu L)) → ∀ p ∈ U, ∃ k : GaussianInt,
      ‖((p.1 : ℂ) / p.2) * v * z - (D : ℂ) / L * k‖ ≤ H := by
    intro v hv p hp
    apply hconf
    intro θ hθ hs
    rw [tr] at hs
    rcases hv with rfl | rfl
    · exact hz _ (memν θ hθ p hp) hs
    · exact hz _ (memν' θ hθ p hp) hs
  choose! kf hkf using rep
  have one_div_one : ((1 : GaussianInt) : ℂ) / ((1 : GaussianInt) : ℂ) = 1 := by
    rw [GaussianInt.toComplex_one, div_one]
  -- the base representations (u = 1)
  have base : ∀ v : ℂ, (v = nu L ∨ v = conj (nu L)) →
      ‖v * z - (D : ℂ) / L * kf v (1, 1)‖ ≤ H := by
    intro v hv
    have := hkf v hv (1, 1) h1
    simpa [one_div_one] using this
  -- integer centres: `u * k_v = k_{u v}` as complex numbers
  have centre : ∀ v : ℂ, (v = nu L ∨ v = conj (nu L)) → ∀ p ∈ U,
      ((kf v p : GaussianInt) : ℂ) = ((p.1 : ℂ) / p.2) * kf v (1, 1) := by
    intro v hv p hp
    obtain ⟨hb, hab, hbQ⟩ := hU p hp
    have h := center_eq (D := D) (a := p.1) (b := p.2) (k := kf v (1, 1)) (k' := kf v p)
      (w := v * z) hL hb hab hbQ hD (base v hv) (by rw [← mul_assoc]; exact hkf v hv p hp)
    have hc : (p.2 : ℂ) * (kf v p : ℂ) = (p.1 : ℂ) * (kf v (1, 1) : ℂ) := by
      rw [← GaussianInt.toComplex_mul, ← GaussianInt.toComplex_mul, h]
    field_simp
    linear_combination hc
  set kν := kf (nu L) (1, 1)
  set kν' := kf (conj (nu L)) (1, 1)
  set k₀ : GaussianInt := kν + kν'
  -- the decomposition `z = D k₀ + e` with `|e| ≤ 2 L H`
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set e : ℂ := z - (D : ℂ) * k₀ with he
  have he_eq : e = (L : ℂ) * ((nu L * z - (D : ℂ) / L * kν) +
      (conj (nu L) * z - (D : ℂ) / L * kν')) := by
    have h2 : (L : ℂ) * ((nu L * z - (D : ℂ) / L * kν) + (conj (nu L) * z - (D : ℂ) / L * kν'))
        = (L : ℂ) * (nu L + conj (nu L)) * z - (L : ℂ) * ((D : ℂ) / L) * ((kν : ℂ) + kν') := by
      ring
    have hL1 : (L : ℂ) * (1 / (L : ℂ)) = 1 := by field_simp
    have hLD : (L : ℂ) * ((D : ℂ) / L) = D := by field_simp
    rw [h2, nu_add_conj hL, hL1, hLD, he, GaussianInt.toComplex_add]
    ring
  have he_norm : ‖e‖ ≤ 2 * L * H := by
    rw [he_eq, norm_mul, Complex.norm_natCast]
    have h1' := base (nu L) (Or.inl rfl)
    have h2' := base (conj (nu L)) (Or.inr rfl)
    calc (L : ℝ) * ‖(nu L * z - (D : ℂ) / L * kν) + (conj (nu L) * z - (D : ℂ) / L * kν')‖
        ≤ (L : ℝ) * (H + H) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add h1' h2')
      _ = 2 * L * H := by ring
  obtain ⟨p, hp, m, hm⟩ := hcover e he_norm
  -- `u k₀` is a Gaussian integer
  set g : GaussianInt := kf (nu L) p + kf (conj (nu L)) p
  have hg : ((p.1 : ℂ) / p.2) * (k₀ : ℂ) = (g : ℂ) := by
    rw [GaussianInt.toComplex_add, GaussianInt.toComplex_add, centre _ (Or.inl rfl) p hp,
      centre _ (Or.inr rfl) p hp]
    ring
  apply hz _ (memU p hp)
  refine ⟨m + (D * g).re, ?_⟩
  have hz_eq : ((p.1 : ℂ) / p.2) * z = ((p.1 : ℂ) / p.2) * e + ((D * g : GaussianInt) : ℂ) := by
    rw [GaussianInt.toComplex_mul, ← hg, he]
    ring
  rw [hz_eq, Complex.add_re, ← GaussianInt.intCast_re]
  push_cast
  convert hm using 2
  ring

end Green41

/- ## Section: `Gaussian` -/

/-
# Gaussian-integer algebra for the orbit `θ₅^s θ₁₃^t`

With `P = 1 + 2i`, `Q = 2 + 3i`, `θ₅ = P / P̄`, `θ₁₃ = Q / Q̄`, the rotations
`rot s t = θ₅^s θ₁₃^t` (`s, t ≤ K`) satisfy `Δ · rot s t = v(s,t) ∈ ℤ[i]`
with `Δ = P̄^K Q̄^K`. Distinct labels give distinct `v`, so every nonzero orbit
difference `r` is `d / Δ` with `d ∈ ℤ[i] \ {0}`. The product `L` of the norms of all
these `d` is a common denominator: `L / r ∈ ℤ[i]`. We also record `|r| ≥ |Δ|⁻¹`.

This is the simple common denominator of the first draft; its size is still
polynomial in `K` after taking logarithms, which is all the final bound needs.
-/

namespace Green41

open Complex ComplexConjugate

/-- `P = 1 + 2i`. -/
def gP : GaussianInt := ⟨1, 2⟩
/-- `P̄ = 1 - 2i`. -/
def gPb : GaussianInt := ⟨1, -2⟩
/-- `Q = 2 + 3i`. -/
def gQ : GaussianInt := ⟨2, 3⟩
/-- `Q̄ = 2 - 3i`. -/
def gQb : GaussianInt := ⟨2, -3⟩

lemma norm_gP : gP.norm = 5 := by decide
lemma norm_gPb : gPb.norm = 5 := by decide
lemma norm_gQ : gQ.norm = 13 := by decide
lemma norm_gQb : gQb.norm = 13 := by decide

lemma norm_toComplex (x : GaussianInt) : ‖(x : ℂ)‖ = Real.sqrt (x.norm : ℝ) := by
  rw [Complex.norm_def, GaussianInt.intCast_real_norm]

lemma norm_dvd_norm {x y : GaussianInt} (h : x ∣ y) : x.norm ∣ y.norm := by
  obtain ⟨c, rfl⟩ := h
  rw [Zsqrtd.norm_mul]
  exact dvd_mul_right _ _

lemma irreducible_of_norm_prime {x : GaussianInt} (hx : (x.norm.natAbs).Prime) :
    Irreducible x := by
  constructor
  · intro hu
    rw [← Zsqrtd.norm_eq_one_iff] at hu
    rw [hu] at hx
    exact Nat.not_prime_one hx
  · intro a b hab
    have h := congrArg (fun z : GaussianInt => z.norm.natAbs) hab
    simp only [Zsqrtd.norm_mul, Int.natAbs_mul] at h
    rw [h] at hx
    rcases Nat.prime_mul_iff.mp hx with ⟨_, hb1⟩ | ⟨_, ha1⟩
    · exact Or.inr (Zsqrtd.norm_eq_one_iff.mp hb1)
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp ha1)

lemma prime_gP : Prime gP :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [norm_gP]; norm_num))

lemma prime_gQ : Prime gQ :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [norm_gQ]; norm_num))

lemma gP_not_dvd_gPb : ¬ gP ∣ gPb := by
  intro h
  have h2 : gP ∣ gP + gPb := dvd_add (dvd_refl _) h
  have hsum : gP + gPb = 2 := by decide
  rw [hsum] at h2
  have h3 := norm_dvd_norm h2
  have h4 : (2 : GaussianInt).norm = 4 := by decide
  rw [norm_gP, h4] at h3
  norm_num at h3

lemma gP_not_dvd_gQ : ¬ gP ∣ gQ := by
  intro h
  have h3 := norm_dvd_norm h
  rw [norm_gP, norm_gQ] at h3
  norm_num at h3

lemma gP_not_dvd_gQb : ¬ gP ∣ gQb := by
  intro h
  have h3 := norm_dvd_norm h
  rw [norm_gP, norm_gQb] at h3
  norm_num at h3

lemma gQ_not_dvd_gQb : ¬ gQ ∣ gQb := by
  intro h
  have h2 : gQ ∣ gQ + gQb := dvd_add (dvd_refl _) h
  have hsum : gQ + gQb = 4 := by decide
  rw [hsum] at h2
  have h3 := norm_dvd_norm h2
  have h4 : (4 : GaussianInt).norm = 16 := by decide
  rw [norm_gQ, h4] at h3
  norm_num at h3

lemma gQ_not_dvd_gP : ¬ gQ ∣ gP := by
  intro h
  have h3 := norm_dvd_norm h
  rw [norm_gQ, norm_gP] at h3
  norm_num at h3

lemma gQ_not_dvd_gPb : ¬ gQ ∣ gPb := by
  intro h
  have h3 := norm_dvd_norm h
  rw [norm_gQ, norm_gPb] at h3
  norm_num at h3

lemma toComplex_ne_zero_of_norm {x : GaussianInt} (hx : x.norm ≠ 0) : (x : ℂ) ≠ 0 := by
  intro h
  apply hx
  rw [GaussianInt.toComplex_eq_zero] at h
  rw [h]
  decide

lemma gPb_ne_zero : (gPb : ℂ) ≠ 0 := toComplex_ne_zero_of_norm (by rw [norm_gPb]; norm_num)
lemma gQb_ne_zero : (gQb : ℂ) ≠ 0 := toComplex_ne_zero_of_norm (by rw [norm_gQb]; norm_num)

lemma cnorm_gP : ‖(gP : ℂ)‖ = Real.sqrt 5 := by rw [norm_toComplex, norm_gP]; norm_num
lemma cnorm_gPb : ‖(gPb : ℂ)‖ = Real.sqrt 5 := by rw [norm_toComplex, norm_gPb]; norm_num
lemma cnorm_gQ : ‖(gQ : ℂ)‖ = Real.sqrt 13 := by rw [norm_toComplex, norm_gQ]; norm_num
lemma cnorm_gQb : ‖(gQb : ℂ)‖ = Real.sqrt 13 := by rw [norm_toComplex, norm_gQb]; norm_num

/-- `θ₅ = P / P̄`. -/
noncomputable def θ5 : ℂ := (gP : ℂ) / (gPb : ℂ)
/-- `θ₁₃ = Q / Q̄`. -/
noncomputable def θ13 : ℂ := (gQ : ℂ) / (gQb : ℂ)
/-- The orbit rotation `θ₅^s θ₁₃^t`. -/
noncomputable def rot (s t : ℕ) : ℂ := θ5 ^ s * θ13 ^ t

lemma norm_θ5 : ‖θ5‖ = 1 := by
  rw [θ5, norm_div, cnorm_gP, cnorm_gPb, div_self (by positivity)]

lemma norm_θ13 : ‖θ13‖ = 1 := by
  rw [θ13, norm_div, cnorm_gQ, cnorm_gQb, div_self (by positivity)]

lemma norm_rot (s t : ℕ) : ‖rot s t‖ = 1 := by
  rw [rot, norm_mul, norm_pow, norm_pow, norm_θ5, norm_θ13, one_pow, one_pow, one_mul]

/-- `v(s,t) = P^s P̄^(K-s) Q^t Q̄^(K-t)`. -/
def vv (K s t : ℕ) : GaussianInt := gP ^ s * gPb ^ (K - s) * gQ ^ t * gQb ^ (K - t)

/-- `Δ = P̄^K Q̄^K`. -/
def gΔ (K : ℕ) : GaussianInt := gPb ^ K * gQb ^ K

lemma vv_eq {K s t : ℕ} (hs : s ≤ K) (ht : t ≤ K) :
    (vv K s t : ℂ) = (gΔ K : ℂ) * rot s t := by
  have hPb := gPb_ne_zero
  have hQb := gQb_ne_zero
  simp only [vv, gΔ, rot, θ5, θ13, map_mul, map_pow]
  change (gP : ℂ) ^ s * (gPb : ℂ) ^ (K - s) * (gQ : ℂ) ^ t * (gQb : ℂ) ^ (K - t) =
    (gPb : ℂ) ^ K * (gQb : ℂ) ^ K * (((gP : ℂ) / gPb) ^ s * ((gQ : ℂ) / gQb) ^ t)
  rw [pow_sub₀ _ hPb hs, pow_sub₀ _ hQb ht, div_pow, div_pow]
  field_simp

lemma cnorm_gΔ (K : ℕ) : ‖(gΔ K : ℂ)‖ = Real.sqrt 65 ^ K := by
  have h : (gΔ K : ℂ) = (gPb : ℂ) ^ K * (gQb : ℂ) ^ K := by
    simp only [gΔ, map_mul, map_pow]
  rw [h, norm_mul, norm_pow, norm_pow, cnorm_gPb, cnorm_gQb, ← mul_pow,
    ← Real.sqrt_mul (by norm_num)]
  norm_num

lemma cnorm_vv {K s t : ℕ} (hs : s ≤ K) (ht : t ≤ K) : ‖(vv K s t : ℂ)‖ = Real.sqrt 65 ^ K := by
  rw [vv_eq hs ht, norm_mul, norm_rot, mul_one, cnorm_gΔ]

/-- If `p` is prime and divides neither `x` nor `y`, then `p^m x = p^m' y` forces `m = m'`. -/
lemma pow_exp_eq {p x y : GaussianInt} (hp : Prime p) {m m' : ℕ} (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : p ^ m * x = p ^ m' * y) : m = m' := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exfalso
    have h' : p ^ m * x = p ^ m * (p ^ (m' - m) * y) := by
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
    have hx' := mul_left_cancel₀ (pow_ne_zero m hp0) h'
    apply hx
    rw [hx']
    exact dvd_mul_of_dvd_left (dvd_pow_self p (Nat.sub_ne_zero_of_lt hlt)) y
  · exact heq
  · exfalso
    have h' : p ^ m' * y = p ^ m' * (p ^ (m - m') * x) := by
      rw [← h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hgt.le]
    have hy' := mul_left_cancel₀ (pow_ne_zero m' hp0) h'
    apply hy
    rw [hy']
    exact dvd_mul_of_dvd_left (dvd_pow_self p (Nat.sub_ne_zero_of_lt hgt)) x

lemma gP_not_dvd_rest (K s t : ℕ) : ¬ gP ∣ gPb ^ (K - s) * gQ ^ t * gQb ^ (K - t) := by
  intro h
  rcases prime_gP.dvd_or_dvd h with h1 | h1
  · rcases prime_gP.dvd_or_dvd h1 with h2 | h2
    · exact gP_not_dvd_gPb (prime_gP.dvd_of_dvd_pow h2)
    · exact gP_not_dvd_gQ (prime_gP.dvd_of_dvd_pow h2)
  · exact gP_not_dvd_gQb (prime_gP.dvd_of_dvd_pow h1)

lemma gQ_not_dvd_rest (K s t : ℕ) : ¬ gQ ∣ gP ^ s * gPb ^ (K - s) * gQb ^ (K - t) := by
  intro h
  rcases prime_gQ.dvd_or_dvd h with h1 | h1
  · rcases prime_gQ.dvd_or_dvd h1 with h2 | h2
    · exact gQ_not_dvd_gP (prime_gQ.dvd_of_dvd_pow h2)
    · exact gQ_not_dvd_gPb (prime_gQ.dvd_of_dvd_pow h2)
  · exact gQ_not_dvd_gQb (prime_gQ.dvd_of_dvd_pow h1)

lemma vv_inj {K s t s' t' : ℕ} (h : vv K s t = vv K s' t') : s = s' ∧ t = t' := by
  constructor
  · apply pow_exp_eq prime_gP (gP_not_dvd_rest K s t) (gP_not_dvd_rest K s' t')
    have e1 : vv K s t = gP ^ s * (gPb ^ (K - s) * gQ ^ t * gQb ^ (K - t)) := by
      simp only [vv]; ring
    have e2 : vv K s' t' = gP ^ s' * (gPb ^ (K - s') * gQ ^ t' * gQb ^ (K - t')) := by
      simp only [vv]; ring
    rw [← e1, ← e2, h]
  · apply pow_exp_eq prime_gQ (gQ_not_dvd_rest K s t) (gQ_not_dvd_rest K s' t')
    have e1 : vv K s t = gQ ^ t * (gP ^ s * gPb ^ (K - s) * gQb ^ (K - t)) := by
      simp only [vv]; ring
    have e2 : vv K s' t' = gQ ^ t' * (gP ^ s' * gPb ^ (K - s') * gQb ^ (K - t')) := by
      simp only [vv]; ring
    rw [← e1, ← e2, h]

/-- The labels `(s, t)` with `s, t ≤ K`. -/
def labels (K : ℕ) : Finset (ℕ × ℕ) := Finset.range (K + 1) ×ˢ Finset.range (K + 1)

lemma card_labels (K : ℕ) : (labels K).card = (K + 1) ^ 2 := by
  rw [labels, Finset.card_product, Finset.card_range, sq]

lemma mem_labels {K : ℕ} {x : ℕ × ℕ} : x ∈ labels K ↔ x.1 ≤ K ∧ x.2 ≤ K := by
  simp [labels]

/-- Ordered pairs of distinct labels. -/
def labelPairs (K : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (labels K ×ˢ labels K).filter (fun p => p.1 ≠ p.2)

/-- The numerator `v(λ) - v(μ)` of an orbit difference. -/
def dd (K : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : GaussianInt := vv K p.1.1 p.1.2 - vv K p.2.1 p.2.2

/-- The common denominator `L = ∏ N(v(λ) - v(μ))`. -/
def commonDen (K : ℕ) : ℕ := ∏ p ∈ labelPairs K, (dd K p).norm.natAbs

lemma dd_ne_zero {K : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ labelPairs K) : dd K p ≠ 0 := by
  simp only [labelPairs, Finset.mem_filter] at hp
  intro h
  apply hp.2
  have h' : vv K p.1.1 p.1.2 = vv K p.2.1 p.2.2 := sub_eq_zero.mp h
  obtain ⟨h1, h2⟩ := vv_inj h'
  exact Prod.ext h1 h2

lemma dd_eq {K : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ labelPairs K) :
    (dd K p : ℂ) = (gΔ K : ℂ) * (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) := by
  simp only [labelPairs, Finset.mem_filter, Finset.mem_product, mem_labels] at hp
  rw [dd, GaussianInt.toComplex_sub, vv_eq hp.1.1.1 hp.1.1.2, vv_eq hp.1.2.1 hp.1.2.2]
  ring

lemma commonDen_pos (K : ℕ) : 0 < commonDen K := by
  apply Finset.prod_pos
  intro p hp
  have h := dd_ne_zero hp
  rw [Int.natAbs_pos]
  exact (GaussianInt.norm_pos).mpr h |>.ne'

/-- `L / r` is a Gaussian integer for every nonzero orbit difference `r`. -/
lemma commonDen_div {K : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ labelPairs K) :
    ∃ c : GaussianInt, (c : ℂ) * (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) = (commonDen K : ℂ) := by
  set d := dd K p
  set n := d.norm.natAbs
  have hn : n ∣ commonDen K := Finset.dvd_prod_of_mem (fun q => (dd K q).norm.natAbs) hp
  refine ⟨((commonDen K / n : ℕ) : GaussianInt) * gΔ K * star d, ?_⟩
  have hd := dd_eq hp
  have hnorm : (d : ℂ) * conj (d : ℂ) = (n : ℂ) := by
    rw [Complex.mul_conj, ← GaussianInt.intCast_real_norm]
    have : (n : ℤ) = d.norm := GaussianInt.abs_natCast_norm d
    rw [← this]
    push_cast
    rfl
  calc _ = ((commonDen K / n : ℕ) : ℂ) * conj (d : ℂ) *
          ((gΔ K : ℂ) * (rot p.1.1 p.1.2 - rot p.2.1 p.2.2)) := by
        simp only [map_mul, map_natCast, GaussianInt.toComplex_star]
        ring
    _ = ((commonDen K / n : ℕ) : ℂ) * ((d : ℂ) * conj (d : ℂ)) := by rw [← hd]; ring
    _ = ((commonDen K / n : ℕ) : ℂ) * (n : ℂ) := by rw [hnorm]
    _ = (commonDen K : ℂ) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hn]

/-- `|r| ≥ 1 / |Δ|` for every nonzero orbit difference `r`. -/
lemma norm_rot_sub_ge {K : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ labelPairs K) :
    1 / Real.sqrt 65 ^ K ≤ ‖rot p.1.1 p.1.2 - rot p.2.1 p.2.2‖ := by
  have hd := dd_eq hp
  have hd1 : 1 ≤ ‖(dd K p : ℂ)‖ := by
    by_contra hlt
    exact dd_ne_zero hp (gaussianInt_eq_zero_of_norm_lt_one (lt_of_not_ge hlt))
  rw [hd, norm_mul, cnorm_gΔ] at hd1
  have hpos : 0 < Real.sqrt 65 ^ K := by positivity
  rw [div_le_iff₀ hpos]
  linarith [mul_comm (Real.sqrt 65 ^ K) ‖rot p.1.1 p.1.2 - rot p.2.1 p.2.2‖]

/-- `L ≤ (4 · 65^K)^((K+1)^4)`. -/
lemma commonDen_le (K : ℕ) : commonDen K ≤ (4 * 65 ^ K) ^ ((K + 1) ^ 4) := by
  have hfac : ∀ p ∈ labelPairs K, (dd K p).norm.natAbs ≤ 4 * 65 ^ K := by
    intro p hp
    have hp' := hp
    simp only [labelPairs, Finset.mem_filter, Finset.mem_product, mem_labels] at hp'
    have h1 := cnorm_vv (K := K) hp'.1.1.1 hp'.1.1.2
    have h2 := cnorm_vv (K := K) hp'.1.2.1 hp'.1.2.2
    have hle : ‖(dd K p : ℂ)‖ ≤ 2 * Real.sqrt 65 ^ K := by
      rw [dd, GaussianInt.toComplex_sub]
      calc _ ≤ ‖(vv K p.1.1 p.1.2 : ℂ)‖ + ‖(vv K p.2.1 p.2.2 : ℂ)‖ := norm_sub_le _ _
        _ = 2 * Real.sqrt 65 ^ K := by rw [h1, h2]; ring
    have hsq : ((dd K p).norm : ℝ) ≤ 4 * 65 ^ K := by
      rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq]
      have h0 : 0 ≤ ‖(dd K p : ℂ)‖ := norm_nonneg _
      calc ‖(dd K p : ℂ)‖ ^ 2 ≤ (2 * Real.sqrt 65 ^ K) ^ 2 := by gcongr
        _ = 4 * 65 ^ K := by
            rw [mul_pow, ← pow_mul, mul_comm K 2, pow_mul, Real.sq_sqrt (by norm_num)]
            norm_num
    have hnn : 0 ≤ (dd K p).norm := GaussianInt.norm_nonneg _
    have : ((dd K p).norm.natAbs : ℝ) ≤ 4 * 65 ^ K := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hnn)]
      exact hsq
    exact_mod_cast this
  calc commonDen K ≤ (4 * 65 ^ K) ^ (labelPairs K).card :=
        Finset.prod_le_pow_card _ _ _ hfac
    _ ≤ (4 * 65 ^ K) ^ ((K + 1) ^ 4) := by
        apply Nat.pow_le_pow_right (by positivity)
        calc (labelPairs K).card ≤ (labels K ×ˢ labels K).card := Finset.card_filter_le _ _
          _ = (K + 1) ^ 4 := by rw [Finset.card_product, card_labels]; ring

end Green41

/- ## Section: `Confinement` -/

/-
# Lattice confinement (Lemma 5.2 of the round-2 draft)

`KL57With c` is the consequence of Kravitz–Leng, Proposition 5.7, that the argument
uses, restricted to points `p = j_ℂ(w)` and Gaussian integers `q`:
the `p`-adic sizes of `q` are `5^(-v_{P̄}(q))` and `13^(-v_{Q̄}(q))`.
It is an interface: the final FC theorem must derive it, not assume it.

From it we prove the confinement lemma. If `w` is not covered by the orbit rotations
`rot s t` (`s, t ≤ T`), then `w` lies within `√65^K` of the lattice `(D_h / L) ℤ[i]`,
where `D_h = P̄^h Q̄^h` and `L = commonDen K`. The pigeonhole step rounds the orbit points
`rot s t · w` to the nearest Gaussian integer.
-/

namespace Green41

open Complex ComplexConjugate

/- ## `p`-adic sizes of Gaussian integers -/

/-- `|ι₅ q|₅ = 5^(-v_{P̄}(q))`, and `0` for `q = 0`. -/
noncomputable def size5 (q : GaussianInt) : ℝ :=
  if q = 0 then 0 else (5 : ℝ) ^ (-(multiplicity gPb q : ℝ))

/-- `|ι₁₃ q|₁₃ = 13^(-v_{Q̄}(q))`, and `0` for `q = 0`. -/
noncomputable def size13 (q : GaussianInt) : ℝ :=
  if q = 0 then 0 else (13 : ℝ) ^ (-(multiplicity gQb q : ℝ))

lemma size5_nonneg (q : GaussianInt) : 0 ≤ size5 q := by
  unfold size5; split_ifs <;> positivity

lemma size13_nonneg (q : GaussianInt) : 0 ≤ size13 q := by
  unfold size13; split_ifs <;> positivity

lemma gPb_not_isUnit : ¬ IsUnit gPb := by
  rw [← Zsqrtd.norm_eq_one_iff, norm_gPb]; decide

lemma gQb_not_isUnit : ¬ IsUnit gQb := by
  rw [← Zsqrtd.norm_eq_one_iff, norm_gQb]; decide

lemma size5_le_of_dvd {q : GaussianInt} {u : ℕ} (h : gPb ^ u ∣ q) :
    size5 q ≤ 1 / (5 : ℝ) ^ u := by
  unfold size5
  split_ifs with hq
  · positivity
  · have hf : FiniteMultiplicity gPb q := FiniteMultiplicity.of_not_isUnit gPb_not_isUnit hq
    have hu : u ≤ multiplicity gPb q := hf.le_multiplicity_of_pow_dvd h
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (u : ℝ) ≤ (multiplicity gPb q : ℝ) := by exact_mod_cast hu
    linarith

lemma size13_le_of_dvd {q : GaussianInt} {u : ℕ} (h : gQb ^ u ∣ q) :
    size13 q ≤ 1 / (13 : ℝ) ^ u := by
  unfold size13
  split_ifs with hq
  · positivity
  · have hf : FiniteMultiplicity gQb q := FiniteMultiplicity.of_not_isUnit gQb_not_isUnit hq
    have hu : u ≤ multiplicity gQb q := hf.le_multiplicity_of_pow_dvd h
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (u : ℝ) ≤ (multiplicity gQb q : ℝ) := by exact_mod_cast hu
    linarith

lemma dvd_of_size5_lt {q : GaussianInt} {h : ℕ} (hs : size5 q < 1 / (5 : ℝ) ^ h) :
    gPb ^ h ∣ q := by
  unfold size5 at hs
  split_ifs at hs with hq
  · rw [hq]; exact dvd_zero _
  · apply pow_dvd_of_le_multiplicity
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)] at hs
    have h2 := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 5)).mp hs
    have : (h : ℝ) < (multiplicity gPb q : ℝ) := by linarith
    exact_mod_cast this.le

lemma dvd_of_size13_lt {q : GaussianInt} {h : ℕ} (hs : size13 q < 1 / (13 : ℝ) ^ h) :
    gQb ^ h ∣ q := by
  unfold size13 at hs
  split_ifs at hs with hq
  · rw [hq]; exact dvd_zero _
  · apply pow_dvd_of_le_multiplicity
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)] at hs
    have h2 := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 13)).mp hs
    have : (h : ℝ) < (multiplicity gQb q : ℝ) := by linarith
    exact_mod_cast this.le

lemma five_eq : (5 : GaussianInt) = gP * gPb := by decide
lemma thirteen_eq : (13 : GaussianInt) = gQ * gQb := by decide

lemma isCoprime_gPb_gQb : IsCoprime gPb gQb := ⟨-5 * gP, 2 * gQ, by decide⟩

/-- `D_h = P̄^h Q̄^h`. -/
def gD (h : ℕ) : GaussianInt := gPb ^ h * gQb ^ h

lemma gD_dvd_of_size_lt {q : GaussianInt} {h : ℕ}
    (hs : size5 q + size13 q < 1 / (13 : ℝ) ^ h) : gD h ∣ q := by
  have h5 : size5 q < 1 / (5 : ℝ) ^ h := by
    have h13 : 1 / (13 : ℝ) ^ h ≤ 1 / (5 : ℝ) ^ h := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) h
    linarith [size13_nonneg q]
  have h13 : size13 q < 1 / (13 : ℝ) ^ h := by linarith [size5_nonneg q]
  exact (isCoprime_gPb_gQb.pow).mul_dvd (dvd_of_size5_lt h5) (dvd_of_size13_lt h13)

/- ## The Kravitz–Leng interface -/

/-- `η = 5^(-ε^(-c))`. -/
noncomputable def ηKL (c ε : ℝ) : ℝ := (5 : ℝ) ^ (-(ε ^ (-c)))

/-- `δ = 13^(-c η^(-5))`. -/
noncomputable def δKL (c ε : ℝ) : ℝ := (13 : ℝ) ^ (-(c * ηKL c ε ^ (-5 : ℝ)))

lemma ηKL_pos (c ε : ℝ) : 0 < ηKL c ε := by unfold ηKL; positivity
lemma δKL_pos (c ε : ℝ) : 0 < δKL c ε := by unfold δKL; positivity

/-- Kravitz–Leng, Proposition 5.7, for points `j_ℂ(w)` and Gaussian integers `q`,
with a fixed constant `c`. -/
def KL57With (c : ℝ) : Prop :=
  ∀ ε ϖ : ℝ, 0 < ε → ε < 1 / 10 → 0 < ϖ → ϖ < 1 / 10 →
    ∀ (N₀ s₁ t₁ s₂ t₂ : ℕ) (w : ℂ) (q : GaussianInt),
      s₁ ≤ N₀ → t₁ ≤ N₀ → s₂ ≤ N₀ → t₂ ≤ N₀ →
      2 * ϖ ≤ size5 q + size13 q → size5 q + size13 q ≤ δKL c ε →
      ‖(q : ℂ) - (rot s₁ t₁ - rot s₂ t₂) * w‖ ≤ ηKL c ε / 10 →
      ∃ s t : ℕ, (s : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + c * ηKL c ε ^ (-5 : ℝ) ∧
        (t : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + c * ηKL c ε ^ (-5 : ℝ) ∧ InStripe ε (rot s t) w

/-- The interface `KL57`: some positive constant works. -/
def KL57 : Prop := ∃ c : ℝ, 0 < c ∧ KL57With c

/- ## Rounding and the pigeonhole step -/

/-- The nearest Gaussian integer, rounding each coordinate. -/
noncomputable def gRound (x : ℂ) : GaussianInt := ⟨round x.re, round x.im⟩

lemma gRound_re (x : ℂ) : ((gRound x : ℂ)).re = (round x.re : ℝ) := by
  simp [gRound, GaussianInt.toComplex_def]

lemma gRound_im (x : ℂ) : ((gRound x : ℂ)).im = (round x.im : ℝ) := by
  simp [gRound, GaussianInt.toComplex_def]

lemma frac_mem (y : ℝ) : -(1 / 2) ≤ y - round y ∧ y - round y < 1 / 2 := by
  rw [round_eq]
  constructor
  · have := Int.floor_le (y + 1 / 2); linarith
  · have := Int.lt_floor_add_one (y + 1 / 2); linarith

/-- The cell of the offset `y - round y ∈ [-1/2, 1/2)` at resolution `1 / G`. -/
noncomputable def cell (G : ℕ) (y : ℝ) : ℤ := ⌊(y - round y + 1 / 2) * G⌋

lemma cell_mem {G : ℕ} (hG : 0 < G) (y : ℝ) : 0 ≤ cell G y ∧ cell G y < G := by
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  obtain ⟨h1, h2⟩ := frac_mem y
  constructor
  · apply Int.floor_nonneg.mpr
    have : 0 ≤ y - round y + 1 / 2 := by linarith
    positivity
  · rw [cell, Int.floor_lt]
    push_cast
    have : y - round y + 1 / 2 < 1 := by linarith
    nlinarith

lemma close_of_cell_eq {G : ℕ} (hG : 0 < G) {y₁ y₂ : ℝ} (h : cell G y₁ = cell G y₂) :
    |(y₁ - round y₁) - (y₂ - round y₂)| < 1 / G := by
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  unfold cell at h
  have a1 := Int.floor_le ((y₁ - round y₁ + 1 / 2) * G)
  have a2 := Int.lt_floor_add_one ((y₁ - round y₁ + 1 / 2) * G)
  have b1 := Int.floor_le ((y₂ - round y₂ + 1 / 2) * G)
  have b2 := Int.lt_floor_add_one ((y₂ - round y₂ + 1 / 2) * G)
  rw [h] at a1 a2
  have e : ((y₁ - round y₁) - (y₂ - round y₂)) * G =
      (y₁ - round y₁ + 1 / 2) * G - (y₂ - round y₂ + 1 / 2) * G := by ring
  have hAB : |((y₁ - round y₁) - (y₂ - round y₂)) * G| < 1 := by
    rw [e, abs_lt]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hG'] at hAB
  rw [lt_div_iff₀ hG']
  exact hAB

/-- The box of a point: residues of its rounding mod `M` and the cells of its offset. -/
noncomputable def box (M G : ℕ) (x : ℂ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((round x.re % (M : ℤ), round x.im % (M : ℤ)), (cell G x.re, cell G x.im))

lemma pigeonhole {K M G : ℕ} (hM : 0 < M) (hG : 0 < G) (hK : M ^ 2 * G ^ 2 < (K + 1) ^ 2)
    (w : ℂ) : ∃ p ∈ labelPairs K, box M G (rot p.1.1 p.1.2 * w) = box M G (rot p.2.1 p.2.2 * w) := by
  classical
  set t : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
    (Finset.Ico (0 : ℤ) M ×ˢ Finset.Ico (0 : ℤ) M) ×ˢ (Finset.Ico (0 : ℤ) G ×ˢ Finset.Ico (0 : ℤ) G)
  have ht : t.card = M ^ 2 * G ^ 2 := by
    simp only [t, Finset.card_product, Int.card_Ico, sub_zero, Int.toNat_natCast]
    ring
  have hc : t.card < (labels K).card := by rw [ht, card_labels]; exact hK
  have hmaps : ∀ x ∈ labels K, box M G (rot x.1 x.2 * w) ∈ t := by
    intro x _
    have hM' : (0 : ℤ) < M := by exact_mod_cast hM
    have c1 := cell_mem hG (rot x.1 x.2 * w).re
    have c2 := cell_mem hG (rot x.1 x.2 * w).im
    simp only [t, box, Finset.mem_product, Finset.mem_Ico]
    refine ⟨⟨⟨Int.emod_nonneg _ hM'.ne', Int.emod_lt_of_pos _ hM'⟩,
      ⟨Int.emod_nonneg _ hM'.ne', Int.emod_lt_of_pos _ hM'⟩⟩, ⟨c1, c2⟩⟩
  obtain ⟨x, hx, y, hy, hxy, hbox⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hmaps
  refine ⟨(x, y), ?_, hbox⟩
  simp only [labelPairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hx, hy⟩, hxy⟩

lemma box_eq_consequences {M G : ℕ} (hG : 0 < G) {x y : ℂ} (h : box M G x = box M G y) :
    (M : GaussianInt) ∣ gRound x - gRound y ∧
      ‖((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)‖ < 2 / G := by
  simp only [box, Prod.mk.injEq] at h
  obtain ⟨⟨hre, him⟩, ⟨cre, cim⟩⟩ := h
  constructor
  · have h1 : (M : ℤ) ∣ round x.re - round y.re := (Int.ModEq.dvd hre.symm)
    have h2 : (M : ℤ) ∣ round x.im - round y.im := (Int.ModEq.dvd him.symm)
    have : ((M : ℤ) : GaussianInt) ∣ gRound x - gRound y := by
      rw [Zsqrtd.intCast_dvd]
      exact ⟨h1, h2⟩
    simpa using this
  · have e1 := close_of_cell_eq hG cre
    have e2 := close_of_cell_eq hG cim
    have hre' : (((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)).re =
        -((x.re - round x.re) - (y.re - round y.re)) := by
      rw [Complex.sub_re, Complex.sub_re, GaussianInt.toComplex_sub, Complex.sub_re, gRound_re,
        gRound_re]
      ring
    have him' : (((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)).im =
        -((x.im - round x.im) - (y.im - round y.im)) := by
      rw [Complex.sub_im, Complex.sub_im, GaussianInt.toComplex_sub, Complex.sub_im, gRound_im,
        gRound_im]
      ring
    calc ‖((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)‖
        ≤ |(((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)).re| +
          |(((gRound x - gRound y : GaussianInt) : ℂ) - (x - y)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ < 1 / G + 1 / G := by
          rw [hre', him', abs_neg, abs_neg]
          exact add_lt_add e1 e2
      _ = 2 / G := by ring

/- ## The confinement lemma -/

/-- Lemma 5.2 of the round-2 draft, from `KL57With c`. -/
theorem confinement {c ε : ℝ} (hKL : KL57With c) (hε0 : 0 < ε) (hε1 : ε < 1 / 10)
    {K G u v h T : ℕ} (hGη : 20 / ηKL c ε ≤ G) (hGδ : 2 / δKL c ε ≤ G) (hG2 : 2 ≤ G)
    (hu : G ≤ 5 ^ u) (hv : G ≤ 13 ^ v)
    (hK : (5 ^ u * 13 ^ v) ^ 2 * G ^ 2 < (K + 1) ^ 2) (hh : 1 ≤ h)
    (hT : (K : ℝ) + Real.logb 5 (2 * 13 ^ h) + c * ηKL c ε ^ (-5 : ℝ) ≤ T) (w : ℂ)
    (hw : ∀ s t : ℕ, s ≤ T → t ≤ T → ¬ InStripe ε (rot s t) w) :
    ∃ k : GaussianInt, ‖w - (gD h : ℂ) / (commonDen K : ℂ) * k‖ ≤ Real.sqrt 65 ^ K := by
  have hG0 : 0 < G := by omega
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG0
  set M : ℕ := 5 ^ u * 13 ^ v with hMdef
  have hM : 0 < M := by positivity
  obtain ⟨p, hp, hbox⟩ := pigeonhole hM hG0 hK w
  obtain ⟨hMdvd, hclose⟩ := box_eq_consequences hG0 hbox
  set x := rot p.1.1 p.1.2 * w
  set y := rot p.2.1 p.2.2 * w
  set q : GaussianInt := gRound x - gRound y
  have hxy : x - y = (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w := by simp only [x, y]; ring
  have hq_close : ‖(q : ℂ) - (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w‖ < 2 / G := by
    rw [← hxy]; exact hclose
  -- sizes of `q`
  have h5u : gPb ^ u ∣ q := by
    have : (5 : GaussianInt) ^ u ∣ (M : GaussianInt) := by
      rw [hMdef]; push_cast; exact dvd_mul_right _ _
    have hPb5 : gPb ^ u ∣ (5 : GaussianInt) ^ u := pow_dvd_pow_of_dvd ⟨gP, by rw [five_eq]; ring⟩ u
    exact hPb5.trans (this.trans hMdvd)
  have h13v : gQb ^ v ∣ q := by
    have : (13 : GaussianInt) ^ v ∣ (M : GaussianInt) := by
      rw [hMdef]; push_cast; exact dvd_mul_left _ _
    have hQb13 : gQb ^ v ∣ (13 : GaussianInt) ^ v :=
      pow_dvd_pow_of_dvd ⟨gQ, by rw [thirteen_eq]; ring⟩ v
    exact hQb13.trans (this.trans hMdvd)
  have hs5 : size5 q ≤ 1 / G := by
    refine (size5_le_of_dvd h5u).trans ?_
    apply one_div_le_one_div_of_le hGr
    exact_mod_cast hu
  have hs13 : size13 q ≤ 1 / G := by
    refine (size13_le_of_dvd h13v).trans ?_
    apply one_div_le_one_div_of_le hGr
    exact_mod_cast hv
  have hη := ηKL_pos c ε
  have hδ := δKL_pos c ε
  by_cases hbig : 1 / (13 : ℝ) ^ h ≤ size5 q + size13 q
  · -- Kravitz–Leng applies and covers `w`: contradiction
    exfalso
    have hp' := hp
    simp only [labelPairs, Finset.mem_filter, Finset.mem_product, mem_labels] at hp'
    set ϖ : ℝ := 1 / (2 * 13 ^ h) with hϖ
    have hϖ0 : 0 < ϖ := by positivity
    have hϖ1 : ϖ < 1 / 10 := by
      rw [hϖ]
      have : (13 : ℝ) ≤ 13 ^ h := by
        calc (13 : ℝ) = 13 ^ 1 := by ring
          _ ≤ 13 ^ h := pow_le_pow_right₀ (by norm_num) hh
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2ϖ : 2 * ϖ ≤ size5 q + size13 q := by
      rw [hϖ]
      calc 2 * (1 / (2 * (13 : ℝ) ^ h)) = 1 / 13 ^ h := by field_simp
        _ ≤ _ := hbig
    have hsizeδ : size5 q + size13 q ≤ δKL c ε := by
      have : 2 / (G : ℝ) ≤ δKL c ε := by
        rw [div_le_iff₀ hGr]
        rw [div_le_iff₀ hδ] at hGδ
        linarith
      have h12 : (1 : ℝ) / G + 1 / G = 2 / G := by ring
      linarith
    have hcloseη : ‖(q : ℂ) - (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w‖ ≤ ηKL c ε / 10 := by
      have : 2 / (G : ℝ) ≤ ηKL c ε / 10 := by
        rw [div_le_iff₀ hGr]
        rw [div_le_iff₀ hη] at hGη
        linarith
      linarith
    obtain ⟨s, t, hs, ht, hst⟩ := hKL ε ϖ hε0 hε1 hϖ0 hϖ1 K p.1.1 p.1.2 p.2.1 p.2.2 w q
      hp'.1.1.1 hp'.1.1.2 hp'.1.2.1 hp'.1.2.2 h2ϖ hsizeδ hcloseη
    have hlog : Real.logb 5 ϖ⁻¹ = Real.logb 5 (2 * 13 ^ h) := by
      rw [hϖ, one_div, inv_inv]
    rw [hlog] at hs ht
    have hsT : s ≤ T := by exact_mod_cast hs.trans hT
    have htT : t ≤ T := by exact_mod_cast ht.trans hT
    exact hw s t hsT htT hst
  · -- `D_h ∣ q`, and the common denominator places `w` near the lattice
    push Not at hbig
    obtain ⟨k₁, hk₁⟩ := gD_dvd_of_size_lt hbig
    obtain ⟨cr, hcr⟩ := commonDen_div hp
    refine ⟨cr * k₁, ?_⟩
    have hr0 : rot p.1.1 p.1.2 - rot p.2.1 p.2.2 ≠ 0 := by
      intro h0
      have := norm_rot_sub_ge hp
      rw [h0, norm_zero] at this
      have : (0 : ℝ) < 1 / Real.sqrt 65 ^ K := by positivity
      linarith
    have hL0 : (commonDen K : ℂ) ≠ 0 := by exact_mod_cast (commonDen_pos K).ne'
    set rr := rot p.1.1 p.1.2 - rot p.2.1 p.2.2 with hrr
    have hkey : w - (gD h : ℂ) / (commonDen K : ℂ) * ((cr * k₁ : GaussianInt) : ℂ) =
        -(((q : ℂ) - rr * w) / rr) := by
      have hq' : (q : ℂ) = (gD h : ℂ) * (k₁ : ℂ) := by
        rw [hk₁, GaussianInt.toComplex_mul]
      have hcr0 : (cr : ℂ) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hcr
        exact hL0 hcr.symm
      rw [GaussianInt.toComplex_mul, hq', ← hcr]
      field_simp
      ring
    rw [hkey, norm_neg, norm_div]
    have hrr_ge := norm_rot_sub_ge hp
    have hrr_pos : 0 < ‖rr‖ := norm_pos_iff.mpr hr0
    rw [div_le_iff₀ hrr_pos]
    have hsq : 0 < Real.sqrt 65 ^ K := by positivity
    have h1 : 1 ≤ Real.sqrt 65 ^ K * ‖rr‖ := by
      rw [div_le_iff₀ hsq] at hrr_ge
      linarith
    have h2 : 2 / (G : ℝ) ≤ 1 := by
      rw [div_le_one hGr]; exact_mod_cast hG2
    calc ‖(q : ℂ) - rr * w‖ ≤ 2 / G := hq_close.le
      _ ≤ 1 := h2
      _ ≤ Real.sqrt 65 ^ K * ‖rr‖ := h1

end Green41

/- ## Section: `DiscCover` -/

/-
# A deterministic cover of a disc by `O(ε⁻¹ log R)` rational rotations

For `e ∈ ℂ` put `g(φ) = Re(e^{iφ} e)`. It has a zero `φ₀ ∈ [-π/2, π/2]`, where
`|g'(φ₀)| = |e|`.

* If `|e| ≤ 16`, some angle of the grid `-π/2 + m ε/16` is within `ε/32` of `φ₀`,
  so `|g| ≤ ε/2` there.
* If `2^k ≤ |e| < 2^(k+1)` with `k ≥ 4`, start from a base angle `β` within `π/32`
  of `φ₀` and step by `ε / 2^(k+1)`. Along the arc `|g'| ≥ |e|/2`, so `g` moves by at
  least `1` while each step moves it by less than `ε`. Hence some step lands within
  `ε/2` of an integer.

Each ideal angle `φ` is then replaced by the rational rotation `c / c̄`, where `c` is the
Gaussian integer nearest to `q e^{iφ/2}`; this moves `Re(u e)` by at most `ε/64`.
-/

namespace Green41

open Complex ComplexConjugate

/- ## The function `g(φ) = Re(e^{iφ} e)` -/

/-- `Re(e^{iφ} e)`. -/
noncomputable def gRe (e : ℂ) (φ : ℝ) : ℝ := e.re * Real.cos φ - e.im * Real.sin φ

/-- `Im(e^{iφ} e)`. -/
noncomputable def gIm (e : ℂ) (φ : ℝ) : ℝ := e.re * Real.sin φ + e.im * Real.cos φ

lemma exp_mul_I_mul (e : ℂ) (φ : ℝ) :
    Complex.exp (φ * I) * e = ⟨gRe e φ, gIm e φ⟩ := by
  apply Complex.ext
  · simp only [gRe, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  · simp only [gIm, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring

lemma gRe_eq (e : ℂ) (φ : ℝ) : gRe e φ = (Complex.exp (φ * I) * e).re := by
  rw [exp_mul_I_mul]

lemma continuous_gRe (e : ℂ) : Continuous (gRe e) := by
  unfold gRe; fun_prop

lemma hasDerivAt_gRe (e : ℂ) (φ : ℝ) : HasDerivAt (gRe e) (-gIm e φ) φ := by
  have h := ((Real.hasDerivAt_cos φ).const_mul e.re).sub ((Real.hasDerivAt_sin φ).const_mul e.im)
  have h' : -gIm e φ = e.re * -Real.sin φ - e.im * Real.cos φ := by unfold gIm; ring
  rw [h']
  exact h

lemma gRe_sq_add_gIm_sq (e : ℂ) (φ : ℝ) : gRe e φ ^ 2 + gIm e φ ^ 2 = ‖e‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hs := Real.sin_sq_add_cos_sq φ
  simp only [gRe, gIm]
  nlinarith [hs]

lemma norm_exp_sub_exp_le (a b : ℝ) :
    ‖Complex.exp (a * I) - Complex.exp (b * I)‖ ≤ |a - b| := by
  have h : Complex.exp (a * I) - Complex.exp (b * I) =
      Complex.exp (b * I) * (Complex.exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rwa [Real.norm_eq_abs] at this

lemma abs_gRe_sub_le (e : ℂ) (a b : ℝ) : |gRe e a - gRe e b| ≤ ‖e‖ * |a - b| := by
  rw [gRe_eq, gRe_eq, ← Complex.sub_re, ← sub_mul]
  calc |((Complex.exp (a * I) - Complex.exp (b * I)) * e).re|
      ≤ ‖(Complex.exp (a * I) - Complex.exp (b * I)) * e‖ := Complex.abs_re_le_norm _
    _ = ‖Complex.exp (a * I) - Complex.exp (b * I)‖ * ‖e‖ := norm_mul _ _
    _ ≤ |a - b| * ‖e‖ := by gcongr; exact norm_exp_sub_exp_le a b
    _ = ‖e‖ * |a - b| := by ring

lemma abs_gIm_sub_le (e : ℂ) (a b : ℝ) : |gIm e a - gIm e b| ≤ ‖e‖ * |a - b| := by
  have ha : gIm e a = (Complex.exp (a * I) * e).im := by rw [exp_mul_I_mul]
  have hb : gIm e b = (Complex.exp (b * I) * e).im := by rw [exp_mul_I_mul]
  rw [ha, hb, ← Complex.sub_im, ← sub_mul]
  calc |((Complex.exp (a * I) - Complex.exp (b * I)) * e).im|
      ≤ ‖(Complex.exp (a * I) - Complex.exp (b * I)) * e‖ := Complex.abs_im_le_norm _
    _ = ‖Complex.exp (a * I) - Complex.exp (b * I)‖ * ‖e‖ := norm_mul _ _
    _ ≤ |a - b| * ‖e‖ := by gcongr; exact norm_exp_sub_exp_le a b
    _ = ‖e‖ * |a - b| := by ring

lemma gRe_neg_pi_div_two (e : ℂ) : gRe e (-(Real.pi / 2)) = e.im := by
  simp [gRe]

lemma gRe_pi_div_two (e : ℂ) : gRe e (Real.pi / 2) = -e.im := by
  simp [gRe]

lemma exists_zero_gRe (e : ℂ) :
    ∃ φ₀ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2), gRe e φ₀ = 0 := by
  have hab : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hc : ContinuousOn (gRe e) (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    (continuous_gRe e).continuousOn
  rcases le_total 0 e.im with h | h
  · have hmem : (0 : ℝ) ∈ Set.Icc (gRe e (Real.pi / 2)) (gRe e (-(Real.pi / 2))) := by
      rw [gRe_pi_div_two, gRe_neg_pi_div_two]; constructor <;> linarith
    obtain ⟨φ, hφ, h0⟩ := intermediate_value_Icc' hab hc hmem
    exact ⟨φ, hφ, h0⟩
  · have hmem : (0 : ℝ) ∈ Set.Icc (gRe e (-(Real.pi / 2))) (gRe e (Real.pi / 2)) := by
      rw [gRe_pi_div_two, gRe_neg_pi_div_two]; constructor <;> linarith
    obtain ⟨φ, hφ, h0⟩ := intermediate_value_Icc hab hc hmem
    exact ⟨φ, hφ, h0⟩

lemma abs_gIm_of_gRe_eq_zero {e : ℂ} {φ : ℝ} (h : gRe e φ = 0) : |gIm e φ| = ‖e‖ := by
  have h2 := gRe_sq_add_gIm_sq e φ
  rw [h] at h2
  have h3 : gIm e φ ^ 2 = ‖e‖ ^ 2 := by linarith
  rw [← Real.sqrt_sq (norm_nonneg e), ← h3, Real.sqrt_sq_eq_abs]

/- ## A slowly moving finite sequence that travels far meets an integer -/

lemma exists_near_int_of_up {ε : ℝ} (y : ℕ → ℝ) (M : ℕ)
    (hstep : ∀ m < M, |y (m + 1) - y m| < ε) (hspan : y 0 + 1 ≤ y M) :
    ∃ m ≤ M, ∃ n : ℤ, |y m - n| < ε / 2 := by
  classical
  set n : ℤ := ⌈y 0⌉ with hn
  have hn1 : y 0 ≤ n := Int.le_ceil _
  have hn2 : (n : ℝ) < y 0 + 1 := Int.ceil_lt_add_one _
  have hex : ∃ m, (n : ℝ) ≤ y m ∧ m ≤ M := ⟨M, by linarith, le_refl _⟩
  obtain ⟨hm₀a, hm₀b⟩ := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · refine ⟨0, Nat.zero_le _, n, ?_⟩
    rw [h0] at hm₀a
    have hε : 0 < ε := by
      have := hstep 0 (by
        rcases Nat.eq_zero_or_pos M with hM | hM
        · rw [hM] at hspan; linarith
        · exact hM)
      linarith [abs_nonneg (y 1 - y 0)]
    rw [abs_lt]; constructor <;> linarith
  · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    rw [hm] at hm₀a hm₀b
    have hprev : ¬ ((n : ℝ) ≤ y m ∧ m ≤ M) := Nat.find_min hex (by omega)
    have hmM : m < M := by omega
    have hlt : y m < n := by
      by_contra hc
      exact hprev ⟨le_of_not_gt hc, hmM.le⟩
    have hs := hstep m hmM
    rw [abs_lt] at hs
    by_cases hcase : y (m + 1) - n < n - y m
    · refine ⟨m + 1, hm₀b, n, ?_⟩
      rw [abs_lt]; constructor <;> linarith
    · refine ⟨m, hmM.le, n, ?_⟩
      rw [abs_lt]; constructor <;> linarith

lemma exists_near_int_of_steps {ε : ℝ} (y : ℕ → ℝ) (M : ℕ)
    (hstep : ∀ m < M, |y (m + 1) - y m| < ε) (hspan : 1 ≤ |y M - y 0|) :
    ∃ m ≤ M, ∃ n : ℤ, |y m - n| < ε / 2 := by
  rcases le_or_gt 0 (y M - y 0) with h | h
  · rw [abs_of_nonneg h] at hspan
    exact exists_near_int_of_up y M hstep (by linarith)
  · rw [abs_of_neg h] at hspan
    have hstep' : ∀ m < M, |(-y (m + 1)) - (-y m)| < ε := by
      intro m hm
      rw [show (-y (m + 1)) - (-y m) = -(y (m + 1) - y m) by ring, abs_neg]
      exact hstep m hm
    obtain ⟨m, hm, n, hn⟩ := exists_near_int_of_up (fun m => -y m) M hstep' (by simp; linarith)
    refine ⟨m, hm, -n, ?_⟩
    rw [show y m - ((-n : ℤ) : ℝ) = -((-y m) - n) by push_cast; ring, abs_neg]
    exact hn

/- ## Rational rotations `c / c̄` -/

/-- The Gaussian integer nearest to `q e^{iφ/2}`. -/
noncomputable def cφ (q : ℕ) (φ : ℝ) : GaussianInt :=
  gRound ((q : ℂ) * Complex.exp (((φ / 2 : ℝ) : ℂ) * I))

lemma norm_gRound_sub_le (x : ℂ) : ‖(gRound x : ℂ) - x‖ ≤ 1 := by
  calc ‖(gRound x : ℂ) - x‖ ≤ |((gRound x : ℂ) - x).re| + |((gRound x : ℂ) - x).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / 2 + 1 / 2 := by
        rw [Complex.sub_re, Complex.sub_im, gRound_re, gRound_im]
        gcongr
        · rw [abs_sub_comm]; exact abs_sub_round _
        · rw [abs_sub_comm]; exact abs_sub_round _
    _ = 1 := by norm_num

lemma rat_rot_approx {q : ℕ} (hq : 2 ≤ q) (φ : ℝ) :
    (cφ q φ : ℂ) ≠ 0 ∧ ‖(cφ q φ : ℂ)‖ ≤ q + 1 ∧
      ‖(cφ q φ : ℂ) / conj (cφ q φ : ℂ) - Complex.exp (φ * I)‖ ≤ 2 / (q - 1) := by
  set w₀ : ℂ := Complex.exp (((φ / 2 : ℝ) : ℂ) * I) with hw₀
  have hw : ‖w₀‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  set c : ℂ := (cφ q φ : ℂ) with hc
  set d : ℂ := c - q * w₀ with hd
  have hd1 : ‖d‖ ≤ 1 := norm_gRound_sub_le _
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqw : ‖(q : ℂ) * w₀‖ = q := by rw [norm_mul, hw, mul_one, Complex.norm_natCast]
  have hcd : c = q * w₀ + d := by rw [hd]; ring
  have hc_lo : (q : ℝ) - 1 ≤ ‖c‖ := by
    have h1 : ‖(q : ℂ) * w₀‖ ≤ ‖c‖ + ‖d‖ := by
      calc ‖(q : ℂ) * w₀‖ = ‖c - d‖ := by rw [hcd]; ring_nf
        _ ≤ ‖c‖ + ‖d‖ := norm_sub_le _ _
    linarith
  have hc_hi : ‖c‖ ≤ q + 1 := by
    calc ‖c‖ = ‖(q : ℂ) * w₀ + d‖ := by rw [hcd]
      _ ≤ ‖(q : ℂ) * w₀‖ + ‖d‖ := norm_add_le _ _
      _ ≤ q + 1 := by rw [hqw]; linarith
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc_lo
    linarith
  refine ⟨hc0, hc_hi, ?_⟩
  have hcc0 : conj c ≠ 0 := (map_ne_zero _).mpr hc0
  have hw0 : w₀ ≠ 0 := by intro h0; rw [h0, norm_zero] at hw; norm_num at hw
  have hww : w₀ * conj w₀ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
  have hcw0 : conj w₀ ≠ 0 := (map_ne_zero _).mpr hw0
  have hsq : Complex.exp (φ * I) = w₀ ^ 2 := by
    rw [hw₀, sq, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  set z : ℂ := c * conj w₀ with hz
  have hzc : conj z = conj c * w₀ := by rw [hz, map_mul, Complex.conj_conj]
  have hident : c / conj c - Complex.exp (φ * I) = (z - conj z) / (conj c * conj w₀) := by
    rw [hsq, hzc, hz]
    field_simp
    linear_combination (-(conj c * w₀)) * hww
  have hzim : z.im = (d * conj w₀).im := by
    have : z = (q : ℂ) + d * conj w₀ := by
      rw [hz, hcd, add_mul, mul_assoc, hww, mul_one]
    rw [this, Complex.add_im, Complex.natCast_im, zero_add]
  have hden : ‖conj c * conj w₀‖ = ‖c‖ := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_conj, hw, mul_one]
  rw [hident, Complex.sub_conj, norm_div, hden]
  have hnum : ‖((2 * z.im : ℝ) : ℂ) * I‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2), hzim]
    have : |(d * conj w₀).im| ≤ 1 := by
      calc |(d * conj w₀).im| ≤ ‖d * conj w₀‖ := Complex.abs_im_le_norm _
        _ = ‖d‖ := by rw [norm_mul, Complex.norm_conj, hw, mul_one]
        _ ≤ 1 := hd1
    linarith
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  calc ‖((2 * z.im : ℝ) : ℂ) * I‖ / ‖c‖ ≤ 2 / ‖c‖ := by gcongr
    _ ≤ 2 / (q - 1) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hc_lo

/-- The rational rotation pair `(c, c̄)` for the angle `φ`. -/
noncomputable def rotPair (q : ℕ) (φ : ℝ) : GaussianInt × GaussianInt :=
  (cφ q φ, star (cφ q φ))

lemma rotPair_div (q : ℕ) (φ : ℝ) :
    ((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ) = (cφ q φ : ℂ) / conj (cφ q φ : ℂ) := by
  simp [rotPair, GaussianInt.toComplex_star]

/-- Replacing `e^{iφ}` by `c / c̄` changes `Re(u e)` by at most `2|e| / (q - 1)`. -/
lemma re_rotPair_close {q : ℕ} (hq : 2 ≤ q) (φ : ℝ) (e : ℂ) :
    |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re - gRe e φ| ≤ 2 / (q - 1) * ‖e‖ := by
  rw [rotPair_div, gRe_eq, ← Complex.sub_re, ← sub_mul]
  obtain ⟨_, _, h3⟩ := rat_rot_approx hq φ
  calc |(((cφ q φ : ℂ) / conj (cφ q φ : ℂ) - Complex.exp (φ * I)) * e).re|
      ≤ ‖((cφ q φ : ℂ) / conj (cφ q φ : ℂ) - Complex.exp (φ * I)) * e‖ :=
        Complex.abs_re_le_norm _
    _ = ‖(cφ q φ : ℂ) / conj (cφ q φ : ℂ) - Complex.exp (φ * I)‖ * ‖e‖ := norm_mul _ _
    _ ≤ 2 / (q - 1) * ‖e‖ := by gcongr

/- ## The two covering cases -/

/-- Rounding a nonnegative real to the nearest natural number. -/
lemma exists_nat_near {x : ℝ} (hx : 0 ≤ x) : ∃ m : ℕ, |(m : ℝ) - x| ≤ 1 / 2 ∧ (m : ℝ) ≤ x + 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋₊, ?_, Nat.floor_le (by linarith)⟩
  have h1 := Nat.floor_le (show 0 ≤ x + 1 / 2 by linarith)
  have h2 := Nat.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]; constructor <;> linarith

lemma small_disc {ε : ℝ} (hε : 0 < ε) {e : ℂ} (he : ‖e‖ ≤ 16) :
    ∃ m ∈ Finset.range (⌈16 * Real.pi / ε⌉₊ + 1),
      |gRe e (-(Real.pi / 2) + m * (ε / 16))| ≤ ε / 2 := by
  obtain ⟨φ₀, ⟨hφ1, hφ2⟩, hz⟩ := exists_zero_gRe e
  have hε16 : 0 < ε / 16 := by positivity
  set x : ℝ := (φ₀ + Real.pi / 2) / (ε / 16) with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hε16.le
  obtain ⟨m, hm1, hm2⟩ := exists_nat_near hx0
  refine ⟨m, ?_, ?_⟩
  · rw [Finset.mem_range]
    have hxle : x ≤ 16 * Real.pi / ε := by
      rw [hx, div_le_div_iff₀ hε16 hε]
      nlinarith [Real.pi_pos]
    have hc := Nat.le_ceil (16 * Real.pi / ε)
    have : (m : ℝ) < ⌈16 * Real.pi / ε⌉₊ + 1 := by linarith
    exact_mod_cast this
  · have hdist : |(-(Real.pi / 2) + m * (ε / 16)) - φ₀| ≤ ε / 32 := by
      have : (-(Real.pi / 2) + m * (ε / 16)) - φ₀ = ((m : ℝ) - x) * (ε / 16) := by
        rw [hx]; field_simp; ring
      rw [this, abs_mul, abs_of_pos hε16]
      nlinarith [hm1]
    calc |gRe e (-(Real.pi / 2) + m * (ε / 16))|
        = |gRe e (-(Real.pi / 2) + m * (ε / 16)) - gRe e φ₀| := by rw [hz, sub_zero]
      _ ≤ ‖e‖ * |(-(Real.pi / 2) + m * (ε / 16)) - φ₀| := abs_gRe_sub_le e _ _
      _ ≤ 16 * (ε / 32) := by gcongr
      _ = ε / 2 := by ring

lemma annulus {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) {k : ℕ} (hk : 4 ≤ k) {e : ℂ}
    (he1 : (2 : ℝ) ^ k ≤ ‖e‖) (he2 : ‖e‖ < 2 ^ (k + 1)) :
    ∃ i ∈ Finset.range 17, ∃ m ∈ Finset.range (⌈4 / ε⌉₊ + 1), ∃ n : ℤ,
      |gRe e (-(Real.pi / 2) + i * (Real.pi / 16) + m * (ε / 2 ^ (k + 1))) - n| < ε / 2 := by
  obtain ⟨φ₀, ⟨hφ1, hφ2⟩, hz⟩ := exists_zero_gRe e
  have hpi := Real.pi_pos
  have hpi4 : Real.pi < 3.2 := by linarith [Real.pi_lt_d2]
  have hpi16 : 0 < Real.pi / 16 := by positivity
  set x : ℝ := (φ₀ + Real.pi / 2) / (Real.pi / 16) with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hpi16.le
  obtain ⟨i, hi1, hi2⟩ := exists_nat_near hx0
  have hx16 : x ≤ 16 := by
    rw [hx, div_le_iff₀ hpi16]; linarith
  have hi16 : i < 17 := by
    have : (i : ℝ) < 17 := by linarith
    exact_mod_cast this
  set β : ℝ := -(Real.pi / 2) + i * (Real.pi / 16) with hβ
  have hβφ : |β - φ₀| ≤ Real.pi / 32 := by
    have : β - φ₀ = ((i : ℝ) - x) * (Real.pi / 16) := by
      rw [hβ, hx]; field_simp; ring
    rw [this, abs_mul, abs_of_pos hpi16]
    nlinarith [hi1]
  set M : ℕ := ⌈4 / ε⌉₊ with hM
  have h2k : (32 : ℝ) ≤ 2 ^ (k + 1) := by
    have : (2 : ℝ) ^ 5 ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this ⊢; linarith
  have h2kpos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  set dk : ℝ := ε / 2 ^ (k + 1) with hdk
  have hdk0 : 0 < dk := by positivity
  have hMge : 4 / ε ≤ M := Nat.le_ceil _
  have hMle : (M : ℝ) < 4 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMdk_lo : 2 / 2 ^ k ≤ M * dk := by
    have : 4 / ε * dk = 2 / 2 ^ k := by
      rw [hdk, pow_succ]; field_simp; ring
    rw [← this]; gcongr
  have hMdk_hi : M * dk ≤ 0.13 := by
    have h1 : M * dk ≤ (4 / ε + 1) * dk := by gcongr
    have h2 : (4 / ε + 1) * dk = (4 + ε) / 2 ^ (k + 1) := by
      rw [hdk]; field_simp
    rw [h2] at h1
    have h3 : (4 + ε) / 2 ^ (k + 1) ≤ (4 + ε) / 32 := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num) h2k
    linarith
  -- the sequence along the arc
  set y : ℕ → ℝ := fun m => gRe e (β + m * dk) with hy
  have hstep : ∀ m < M, |y (m + 1) - y m| < ε := by
    intro m _
    have h := abs_gRe_sub_le e (β + ((m + 1 : ℕ) : ℝ) * dk) (β + m * dk)
    have hd : |(β + ((m + 1 : ℕ) : ℝ) * dk) - (β + m * dk)| = dk := by
      push_cast; rw [show β + (m + 1) * dk - (β + m * dk) = dk by ring, abs_of_pos hdk0]
    rw [hd] at h
    have : ‖e‖ * dk < ε := by
      calc ‖e‖ * dk < 2 ^ (k + 1) * dk := by gcongr
        _ = ε := by rw [hdk]; field_simp
    exact lt_of_le_of_lt h this
  have hspan : 1 ≤ |y M - y 0| := by
    have hlt : β < β + M * dk := by
      have : 0 < (M : ℝ) * dk := by
        have : (0 : ℝ) < 2 / 2 ^ k := by positivity
        linarith
      linarith
    obtain ⟨ξ, ⟨hξ1, hξ2⟩, hξ⟩ := exists_hasDerivAt_eq_slope (gRe e) (fun x => -gIm e x) hlt
      (continuous_gRe e).continuousOn (fun x _ => hasDerivAt_gRe e x)
    have hMdkpos : 0 < (M : ℝ) * dk := by
      have : (0 : ℝ) < 2 / 2 ^ k := by positivity
      linarith
    have hyM : y M - y 0 = -gIm e ξ * (M * dk) := by
      have hden : β + M * dk - β = M * dk := by ring
      rw [hden] at hξ
      simp only [hy, Nat.cast_zero, zero_mul, add_zero]
      rw [hξ, div_mul_cancel₀ _ hMdkpos.ne']
    have hξφ : |ξ - φ₀| ≤ 0.23 := by
      have h1 : |ξ - β| ≤ M * dk := by
        rw [abs_le]; constructor <;> linarith
      calc |ξ - φ₀| = |(ξ - β) + (β - φ₀)| := by ring_nf
        _ ≤ |ξ - β| + |β - φ₀| := abs_add_le _ _
        _ ≤ 0.13 + Real.pi / 32 := by linarith
        _ ≤ 0.23 := by linarith
    have hgI : ‖e‖ / 2 ≤ |gIm e ξ| := by
      have h0 := abs_gIm_of_gRe_eq_zero hz
      have h1 := abs_gIm_sub_le e ξ φ₀
      have h2 : |gIm e φ₀| ≤ |gIm e ξ| + |gIm e ξ - gIm e φ₀| := by
        calc |gIm e φ₀| = |gIm e ξ - (gIm e ξ - gIm e φ₀)| := by ring_nf
          _ ≤ |gIm e ξ| + |gIm e ξ - gIm e φ₀| := abs_sub _ _
      have h3 : ‖e‖ * |ξ - φ₀| ≤ ‖e‖ * 0.23 := by gcongr
      nlinarith [norm_nonneg e]
    rw [hyM, abs_mul, abs_neg, abs_of_pos hMdkpos]
    calc (1 : ℝ) = (2 ^ k / 2) * (2 / 2 ^ k) := by field_simp
      _ ≤ (‖e‖ / 2) * (M * dk) := by
          gcongr
      _ ≤ |gIm e ξ| * (M * dk) := by
          have : 0 ≤ (M : ℝ) * dk := by positivity
          gcongr
  obtain ⟨m, hm, n, hn⟩ := exists_near_int_of_steps y M hstep hspan
  refine ⟨i, Finset.mem_range.mpr hi16, m, Finset.mem_range.mpr (by omega), n, ?_⟩
  simpa [hy, hβ, add_assoc] using hn

/- ## The deterministic disc cover -/

/-- The grid of angles for the small disc `|e| ≤ 16`. -/
noncomputable def smallAngles (ε : ℝ) : Finset ℝ :=
  (Finset.range (⌈16 * Real.pi / ε⌉₊ + 1)).image (fun m : ℕ => -(Real.pi / 2) + m * (ε / 16))

/-- The arcs of angles for the dyadic annuli `2^k ≤ |e| < 2^(k+1)`, `4 ≤ k ≤ log₂ R`. -/
noncomputable def annAngles (ε R : ℝ) : Finset ℝ :=
  ((Finset.Icc 4 (Nat.log 2 ⌊R⌋₊)) ×ˢ (Finset.range 17 ×ˢ Finset.range (⌈4 / ε⌉₊ + 1))).image
    (fun x : ℕ × ℕ × ℕ => -(Real.pi / 2) + x.2.1 * (Real.pi / 16) + x.2.2 * (ε / 2 ^ (x.1 + 1)))

/-- The parameter `q` of the rational rotations. -/
noncomputable def qPar (ε R : ℝ) : ℕ := ⌈128 * R / ε⌉₊ + 2

/-- The rotation pairs `(a, b)` (`u = a / b`) covering the disc of radius `R`. -/
noncomputable def discSet (ε R : ℝ) : Finset (GaussianInt × GaussianInt) := by
  classical
  exact insert (1, 1) ((smallAngles ε ∪ annAngles ε R).image (rotPair (qPar ε R)))

lemma mem_discSet_of_angle {ε R φ : ℝ} (h : φ ∈ smallAngles ε ∪ annAngles ε R) :
    rotPair (qPar ε R) φ ∈ discSet ε R := by
  classical
  unfold discSet
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨φ, h, rfl⟩)

theorem disc_cover {ε R : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) (hR : 16 ≤ R) :
    ((1 : GaussianInt), (1 : GaussianInt)) ∈ discSet ε R ∧
    (∀ p ∈ discSet ε R, (p.2 : ℂ) ≠ 0 ∧ ‖(p.1 : ℂ)‖ = ‖(p.2 : ℂ)‖ ∧
      ‖(p.2 : ℂ)‖ ≤ 128 * R / ε + 4) ∧
    (∀ e : ℂ, ‖e‖ ≤ R → ∃ p ∈ discSet ε R, InStripe ε ((p.1 : ℂ) / p.2) e) ∧
    ((discSet ε R).card : ℝ) ≤
      3 + 16 * Real.pi / ε + 17 * (4 / ε + 2) * ((Nat.log 2 ⌊R⌋₊ : ℝ) + 1) := by
  classical
  have hR0 : 0 < R := by linarith
  set q := qPar ε R with hqdef
  have hq2 : 2 ≤ q := by rw [hqdef, qPar]; omega
  have hqr : (q : ℝ) ≤ 128 * R / ε + 3 := by
    rw [hqdef, qPar]; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 128 * R / ε by positivity)
    linarith
  have hqr' : 128 * R / ε + 1 ≤ (q : ℝ) - 1 := by
    rw [hqdef, qPar]; push_cast
    have := Nat.le_ceil (128 * R / ε)
    linarith
  -- the rational replacement costs at most `ε / 64` inside the disc of radius `R`
  have happrox : ∀ φ : ℝ, ∀ e : ℂ, ‖e‖ ≤ R →
      |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re - gRe e φ| ≤ ε / 64 := by
    intro φ e he
    refine (re_rotPair_close hq2 φ e).trans ?_
    have hq1 : 0 < (q : ℝ) - 1 := by linarith [show (0:ℝ) < 128 * R / ε + 1 by positivity]
    calc 2 / ((q : ℝ) - 1) * ‖e‖ ≤ 2 / ((q : ℝ) - 1) * R := by gcongr
      _ ≤ 2 / (128 * R / ε) * R := by
          gcongr
          linarith
      _ = ε / 64 := by field_simp; ring
  refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
  · -- denominators
    intro p hp
    unfold discSet at hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · refine ⟨by simp [GaussianInt.toComplex_one], rfl, ?_⟩
      rw [GaussianInt.toComplex_one, norm_one]
      have : 0 ≤ 128 * R / ε := by positivity
      linarith
    · obtain ⟨φ, _, rfl⟩ := Finset.mem_image.mp hp'
      obtain ⟨h1, h2, _⟩ := rat_rot_approx hq2 φ
      simp only [rotPair, GaussianInt.toComplex_star]
      refine ⟨(map_ne_zero _).mpr h1, (Complex.norm_conj _).symm, ?_⟩
      rw [Complex.norm_conj]
      linarith
  · -- covering
    intro e he
    by_cases hsmall : ‖e‖ ≤ 16
    · obtain ⟨m, hm, hg⟩ := small_disc hε hsmall
      set φ := -(Real.pi / 2) + m * (ε / 16)
      have hφ : φ ∈ smallAngles ε ∪ annAngles ε R :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
      refine ⟨rotPair q φ, mem_discSet_of_angle hφ, 0, ?_⟩
      have h := happrox φ e he
      push_cast
      rw [sub_zero]
      calc |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re|
          ≤ |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re - gRe e φ| + |gRe e φ| := by
            have := abs_sub_abs_le_abs_sub
              ((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re (gRe e φ)
            linarith
        _ ≤ ε / 64 + ε / 2 := add_le_add h hg
        _ < ε := by linarith
    · push Not at hsmall
      set k := Nat.log 2 ⌊‖e‖⌋₊ with hk
      have hfl16 : 16 ≤ ⌊‖e‖⌋₊ := Nat.le_floor (by exact_mod_cast hsmall.le)
      have hk4 : 4 ≤ k := Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hfl16)
      have hflpos : ⌊‖e‖⌋₊ ≠ 0 := by omega
      have he1 : (2 : ℝ) ^ k ≤ ‖e‖ := by
        have h1 : 2 ^ k ≤ ⌊‖e‖⌋₊ := Nat.pow_log_le_self 2 hflpos
        have h2 : (⌊‖e‖⌋₊ : ℝ) ≤ ‖e‖ := Nat.floor_le (norm_nonneg _)
        calc (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ⌊‖e‖⌋₊ := by exact_mod_cast h1
          _ ≤ ‖e‖ := h2
      have he2 : ‖e‖ < 2 ^ (k + 1) := by
        have h1 : ⌊‖e‖⌋₊ < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
        have h2 : ‖e‖ < ⌊‖e‖⌋₊ + 1 := Nat.lt_floor_add_one _
        have h3 : ((⌊‖e‖⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h3
        linarith
      have hkR : k ≤ Nat.log 2 ⌊R⌋₊ := Nat.log_mono_right (Nat.floor_le_floor he)
      obtain ⟨i, hi, m, hm, n, hn⟩ := annulus hε hε1 hk4 he1 he2
      set φ := -(Real.pi / 2) + i * (Real.pi / 16) + m * (ε / 2 ^ (k + 1))
      have hφ : φ ∈ smallAngles ε ∪ annAngles ε R := by
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨(k, i, m), ?_, rfl⟩
        simp only [Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hk4, hkR⟩, hi, hm⟩
      refine ⟨rotPair q φ, mem_discSet_of_angle hφ, n, ?_⟩
      have h := happrox φ e he
      calc |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re - n|
          ≤ |((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re - gRe e φ| +
            |gRe e φ - n| := by
            have := abs_sub_le ((((rotPair q φ).1 : ℂ) / ((rotPair q φ).2 : ℂ)) * e).re
              (gRe e φ) n
            linarith
        _ < ε / 64 + ε / 2 := by linarith
        _ < ε := by linarith
  · -- the number of rotations
    have hc1 : ((smallAngles ε).card : ℝ) ≤ 16 * Real.pi / ε + 2 := by
      have h1 : (smallAngles ε).card ≤ ⌈16 * Real.pi / ε⌉₊ + 1 := by
        unfold smallAngles
        exact Finset.card_image_le.trans (by rw [Finset.card_range])
      have h2 := Nat.ceil_lt_add_one (show 0 ≤ 16 * Real.pi / ε by positivity)
      have h3 : ((smallAngles ε).card : ℝ) ≤ ⌈16 * Real.pi / ε⌉₊ + 1 := by exact_mod_cast h1
      linarith
    have hc2 : ((annAngles ε R).card : ℝ) ≤ 17 * (4 / ε + 2) * ((Nat.log 2 ⌊R⌋₊ : ℝ) + 1) := by
      have h1 : (annAngles ε R).card ≤
          (Nat.log 2 ⌊R⌋₊ + 1) * (17 * (⌈4 / ε⌉₊ + 1)) := by
        unfold annAngles
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range,
          Nat.card_Icc]
        gcongr
        omega
      have h2 := Nat.ceil_lt_add_one (show 0 ≤ 4 / ε by positivity)
      have h3 : ((annAngles ε R).card : ℝ) ≤
          ((Nat.log 2 ⌊R⌋₊ : ℝ) + 1) * (17 * (⌈4 / ε⌉₊ + 1)) := by exact_mod_cast h1
      have h4 : (17 : ℝ) * (⌈4 / ε⌉₊ + 1) ≤ 17 * (4 / ε + 2) := by linarith
      have h5 : 0 ≤ (Nat.log 2 ⌊R⌋₊ : ℝ) + 1 := by positivity
      nlinarith
    have hU : (discSet ε R).card ≤ 1 + ((smallAngles ε).card + (annAngles ε R).card) := by
      unfold discSet
      calc _ ≤ ((smallAngles ε ∪ annAngles ε R).image (rotPair q)).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ (smallAngles ε ∪ annAngles ε R).card + 1 := by gcongr; exact Finset.card_image_le
        _ ≤ ((smallAngles ε).card + (annAngles ε R).card) + 1 := by
            gcongr; exact Finset.card_union_le _ _
        _ = 1 + ((smallAngles ε).card + (annAngles ε R).card) := by ring
    have hU' : ((discSet ε R).card : ℝ) ≤ 1 + ((smallAngles ε).card + (annAngles ε R).card) := by
      exact_mod_cast hU
    linarith

end Green41

/- ## Section: `Assembly` -/

/-
# Assembling the covering (conditional on `KL57With c`)

For `0 < ε < 1/10` the parameters are chosen in this order:
`G ≥ max(20/η, 2/δ, 1/ε, c η⁻⁵) + 66`, `u = ⌈log₅ G⌉`, `v = ⌈log₁₃ G⌉`, `K = G⁴`,
`L = commonDen K`, `H = √65^K`, `R = 2LH + 16`, `Q = 128R/ε + 4`,
`h = 2 ⌈log₆₅(⌈2LHQ⌉ + 1)⌉`, `T = ⌈K + log₅(2·13^h) + c η⁻⁵⌉`.
The orbit `Θ = {rot s t : s, t ≤ T}` satisfies the confinement lemma, the disc cover
handles radius `R`, and the end game covers the plane with
`(2 (T+1)² + 1) |U|` rotations.
-/

namespace Green41

open Complex ComplexConjugate

section Params

variable (c ε : ℝ)

/-- `max(20/η, 2/δ, 1/ε, c η⁻⁵)`. -/
noncomputable def X0 : ℝ :=
  max (max (20 / ηKL c ε) (2 / δKL c ε)) (max (1 / ε) (c * ηKL c ε ^ (-5 : ℝ)))
/-- The pigeonhole resolution `G`. -/
noncomputable def Gp : ℕ := ⌈X0 c ε⌉₊ + 66
/-- `u = ⌈log₅ G⌉`. -/
noncomputable def up : ℕ := Nat.clog 5 (Gp c ε)
/-- `v = ⌈log₁₃ G⌉`. -/
noncomputable def vp : ℕ := Nat.clog 13 (Gp c ε)
/-- The short-orbit length `K = G⁴`. -/
noncomputable def Kp : ℕ := Gp c ε ^ 4
/-- The common denominator `L`. -/
noncomputable def Lp : ℕ := commonDen (Kp c ε)
/-- The confinement radius `H = √65^K`. -/
noncomputable def Hp : ℝ := Real.sqrt 65 ^ Kp c ε
/-- The disc radius `R = 2LH + 16`. -/
noncomputable def Rp : ℝ := 2 * Lp c ε * Hp c ε + 16
/-- The denominator bound `Q = 128R/ε + 4` of the disc cover. -/
noncomputable def Qp : ℝ := 128 * Rp c ε / ε + 4
/-- The lattice exponent `h`, with `|D_h| = √65^h > 2LHQ`. -/
noncomputable def hp : ℕ := 2 * Nat.clog 65 (⌈2 * (Lp c ε : ℝ) * Hp c ε * Qp c ε⌉₊ + 1)
/-- The orbit length `T`. -/
noncomputable def Tp : ℕ :=
  ⌈(Kp c ε : ℝ) + Real.logb 5 (2 * 13 ^ hp c ε) + c * ηKL c ε ^ (-5 : ℝ)⌉₊
/-- The orbit rotations `rot s t`, `s, t ≤ T`. -/
noncomputable def Θp : Finset ℂ := by
  classical
  exact (labels (Tp c ε)).image (fun p => rot p.1 p.2)
/-- The final rotation set. -/
noncomputable def Ωp : Finset ℂ := endgameSet (Θp c ε) (discSet ε (Rp c ε)) (Lp c ε)

end Params

lemma cnorm_gD (h : ℕ) : ‖(gD h : ℂ)‖ = Real.sqrt 65 ^ h := by
  have e : (gD h : ℂ) = (gPb : ℂ) ^ h * (gQb : ℂ) ^ h := by simp only [gD, map_mul, map_pow]
  rw [e, norm_mul, norm_pow, norm_pow, cnorm_gPb, cnorm_gQb, ← mul_pow,
    ← Real.sqrt_mul (by norm_num)]
  norm_num

section Bounds

variable {c ε : ℝ}

lemma X0_ge :
    20 / ηKL c ε ≤ X0 c ε ∧ 2 / δKL c ε ≤ X0 c ε ∧ 1 / ε ≤ X0 c ε ∧
      c * ηKL c ε ^ (-5 : ℝ) ≤ X0 c ε := by
  unfold X0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

lemma Gp_ge : X0 c ε ≤ Gp c ε ∧ 66 ≤ Gp c ε := by
  constructor
  · unfold Gp; push_cast
    have := Nat.le_ceil (X0 c ε)
    linarith
  · unfold Gp; omega

lemma up_bounds : Gp c ε ≤ 5 ^ up c ε ∧ 5 ^ up c ε < 5 * Gp c ε := by
  have hG := (Gp_ge (c := c) (ε := ε)).2
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have hpos : 0 < up c ε := Nat.clog_pos (by norm_num) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (b := 5) (by norm_num) (show 1 < Gp c ε by omega)
  unfold up at hpos ⊢
  obtain ⟨m, hm⟩ : ∃ m, Nat.clog 5 (Gp c ε) = m + 1 := ⟨Nat.clog 5 (Gp c ε) - 1, by omega⟩
  rw [hm] at hlt ⊢
  have hlt' : 5 ^ m < Gp c ε := by simpa using hlt
  rw [pow_succ]
  omega

lemma vp_bounds : Gp c ε ≤ 13 ^ vp c ε ∧ 13 ^ vp c ε < 13 * Gp c ε := by
  have hG := (Gp_ge (c := c) (ε := ε)).2
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have hpos : 0 < vp c ε := Nat.clog_pos (by norm_num) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (b := 13) (by norm_num) (show 1 < Gp c ε by omega)
  unfold vp at hpos ⊢
  obtain ⟨m, hm⟩ : ∃ m, Nat.clog 13 (Gp c ε) = m + 1 := ⟨Nat.clog 13 (Gp c ε) - 1, by omega⟩
  rw [hm] at hlt ⊢
  have hlt' : 13 ^ m < Gp c ε := by simpa using hlt
  rw [pow_succ]
  omega

lemma hK_param :
    (5 ^ up c ε * 13 ^ vp c ε) ^ 2 * Gp c ε ^ 2 < (Kp c ε + 1) ^ 2 := by
  have hG := (Gp_ge (c := c) (ε := ε)).2
  obtain ⟨_, hu⟩ := up_bounds (c := c) (ε := ε)
  obtain ⟨_, hv⟩ := vp_bounds (c := c) (ε := ε)
  set G := Gp c ε
  have hM : 5 ^ up c ε * 13 ^ vp c ε < 65 * G ^ 2 := by
    calc 5 ^ up c ε * 13 ^ vp c ε < (5 * G) * (13 * G) := Nat.mul_lt_mul'' hu hv
      _ = 65 * G ^ 2 := by ring
  have h1 : (5 ^ up c ε * 13 ^ vp c ε) ^ 2 * G ^ 2 < (65 * G ^ 2) ^ 2 * G ^ 2 := by
    have hG0 : 0 < G ^ 2 := by positivity
    have := Nat.pow_lt_pow_left hM (two_ne_zero)
    exact Nat.mul_lt_mul_of_pos_right this hG0
  have h2 : (65 * G ^ 2) ^ 2 * G ^ 2 ≤ G ^ 8 := by
    have : 65 * 65 ≤ G ^ 2 := by nlinarith
    calc (65 * G ^ 2) ^ 2 * G ^ 2 = (65 * 65) * G ^ 6 := by ring
      _ ≤ G ^ 2 * G ^ 6 := Nat.mul_le_mul_right _ this
      _ = G ^ 8 := by ring
  have h3 : G ^ 8 < (Kp c ε + 1) ^ 2 := by
    unfold Kp
    have : G ^ 8 = (G ^ 4) ^ 2 := by ring
    rw [this]
    exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) two_ne_zero
  omega

lemma Hp_ge_one : 1 ≤ Hp c ε := by
  unfold Hp
  exact one_le_pow₀ (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)

lemma Lp_pos : 0 < Lp c ε := commonDen_pos _

lemma Rp_ge : 16 ≤ Rp c ε ∧ 2 * (Lp c ε : ℝ) * Hp c ε ≤ Rp c ε := by
  unfold Rp
  have h1 : (0 : ℝ) ≤ 2 * Lp c ε * Hp c ε := by
    have := Hp_ge_one (c := c) (ε := ε)
    positivity
  constructor <;> linarith

lemma hp_spec (hε : 0 < ε) : 1 ≤ hp c ε ∧
    2 * (Lp c ε : ℝ) * Hp c ε * Qp c ε < ‖(gD (hp c ε) : ℂ)‖ := by
  set X := 2 * (Lp c ε : ℝ) * Hp c ε * Qp c ε with hX
  have hXpos : 0 < X := by
    have hL : (0 : ℝ) < Lp c ε := by exact_mod_cast Lp_pos
    have hH := Hp_ge_one (c := c) (ε := ε)
    have hQ : 0 < Qp c ε := by
      unfold Qp
      have := (Rp_ge (c := c) (ε := ε)).1
      positivity
    rw [hX]; positivity
  have hceil : 1 ≤ ⌈X⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
  set m := Nat.clog 65 (⌈X⌉₊ + 1) with hm
  have hm1 : 0 < m := Nat.clog_pos (by norm_num) (by omega)
  constructor
  · unfold hp; rw [← hm]; omega
  · rw [cnorm_gD]
    unfold hp
    rw [← hm, pow_mul, Real.sq_sqrt (by norm_num)]
    have h1 : ⌈X⌉₊ + 1 ≤ 65 ^ m := Nat.le_pow_clog (by norm_num) _
    have h2 : X < ⌈X⌉₊ + 1 := by
      have := Nat.le_ceil X; linarith
    have h3 : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ ((65 ^ m : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith

end Bounds

/-- The covering assembled from the confinement lemma, the disc cover and the end game. -/
theorem minCopies_le_param {c ε : ℝ} (hKL : KL57With c) (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    (minCopies ε : ℝ) ≤ (2 * ((Tp c ε : ℝ) + 1) ^ 2 + 1) * (discSet ε (Rp c ε)).card := by
  classical
  obtain ⟨hX20, hX2, _, hXc⟩ := X0_ge (c := c) (ε := ε)
  obtain ⟨hGX, hG66⟩ := Gp_ge (c := c) (ε := ε)
  obtain ⟨hu, _⟩ := up_bounds (c := c) (ε := ε)
  obtain ⟨hv, _⟩ := vp_bounds (c := c) (ε := ε)
  obtain ⟨hR16, hRLH⟩ := Rp_ge (c := c) (ε := ε)
  obtain ⟨hh1, hD⟩ := hp_spec (c := c) hε
  obtain ⟨hU1, hU2, hU3, _⟩ := disc_cover hε hε1 hR16
  have hGr : (66 : ℝ) ≤ Gp c ε := by exact_mod_cast hG66
  -- confinement for the orbit `Θ`
  have hconf : ∀ w : ℂ, (∀ θ ∈ Θp c ε, ¬ InStripe ε θ w) →
      ∃ k : GaussianInt, ‖w - (gD (hp c ε) : ℂ) / (Lp c ε : ℂ) * k‖ ≤ Hp c ε := by
    intro w hw
    have hw' : ∀ s t : ℕ, s ≤ Tp c ε → t ≤ Tp c ε → ¬ InStripe ε (rot s t) w := by
      intro s t hs ht
      apply hw
      unfold Θp
      exact Finset.mem_image.mpr ⟨(s, t), mem_labels.mpr ⟨hs, ht⟩, rfl⟩
    exact confinement hKL hε hε1 (by linarith) (by linarith) (by omega) hu hv
      (hK_param (c := c) (ε := ε)) hh1 (Nat.le_ceil _) w hw'
  -- the end game
  have hcov : ∀ z : ℂ, ∃ v ∈ Ωp c ε, InStripe ε v z := by
    intro z
    unfold Ωp
    refine endgame_cover (Q := Qp c ε) Lp_pos (Θp c ε) (discSet ε (Rp c ε)) hconf ?_ hU1 ?_ hD z
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hU2 p hp
      exact ⟨h1, h2, by unfold Qp; exact h3⟩
    · intro e he
      exact hU3 e (he.trans hRLH)
  have hunit : ∀ v ∈ Ωp c ε, ‖v‖ = 1 := by
    unfold Ωp
    refine norm_of_mem_endgameSet Lp_pos ?_ ?_
    · intro θ hθ
      unfold Θp at hθ
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hθ
      exact norm_rot _ _
    · intro p hp
      obtain ⟨h1, h2, _⟩ := hU2 p hp
      exact ⟨h1, h2⟩
  have hmin := minCopies_le_of_cover (Ωp c ε) hunit hcov
  have hcard := card_endgameSet_le (Θp c ε) (discSet ε (Rp c ε)) (Lp c ε)
  have hΘ : (Θp c ε).card ≤ (Tp c ε + 1) ^ 2 := by
    unfold Θp
    exact Finset.card_image_le.trans (by rw [card_labels])
  have h1 : (minCopies ε : ℝ) ≤ (Ωp c ε).card := by exact_mod_cast hmin
  have h2 : ((Ωp c ε).card : ℝ) ≤
      2 * (Θp c ε).card * (discSet ε (Rp c ε)).card + (discSet ε (Rp c ε)).card := by
    unfold Ωp; exact_mod_cast hcard
  have h3 : ((Θp c ε).card : ℝ) ≤ ((Tp c ε : ℝ) + 1) ^ 2 := by exact_mod_cast hΘ
  have hU0 : (0 : ℝ) ≤ (discSet ε (Rp c ε)).card := by positivity
  calc (minCopies ε : ℝ) ≤ (Ωp c ε).card := h1
    _ ≤ 2 * (Θp c ε).card * (discSet ε (Rp c ε)).card + (discSet ε (Rp c ε)).card := h2
    _ ≤ 2 * ((Tp c ε : ℝ) + 1) ^ 2 * (discSet ε (Rp c ε)).card + (discSet ε (Rp c ε)).card := by
        gcongr
    _ = (2 * ((Tp c ε : ℝ) + 1) ^ 2 + 1) * (discSet ε (Rp c ε)).card := by ring

end Green41

/- ## Section: `Estimates` -/

/-
# Polynomial bookkeeping: `minCopies ε ≤ G^88`

All auxiliary quantities are bounded crudely in terms of `B = (K+1)^5`, `K = G⁴`:
`L ≤ 65^B`, `H ≤ 65^B`, `R ≤ 65^(2B+1)`, `Q ≤ 65^(3B+3)`, `h ≤ 10B + 10`, `T ≤ 44B`,
`|U| ≤ 2300 B²`. Hence `minCopies ε ≤ 10^7 B⁴ ≤ G^88`.
-/

namespace Green41

open Complex ComplexConjugate

section

variable {c ε : ℝ}

/-- `B = (K+1)^5`. -/
noncomputable def Bp (c ε : ℝ) : ℕ := (Kp c ε + 1) ^ 5

lemma one_le_Bp : 1 ≤ Bp c ε := by unfold Bp; exact Nat.one_le_pow _ _ (by omega)

lemma Kp_le_Bp : Kp c ε ≤ Bp c ε := by
  unfold Bp
  calc Kp c ε ≤ Kp c ε + 1 := Nat.le_succ _
    _ = (Kp c ε + 1) ^ 1 := (pow_one _).symm
    _ ≤ (Kp c ε + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)

lemma Gp_le_Kp : Gp c ε ≤ Kp c ε := by
  unfold Kp
  have hG := (Gp_ge (c := c) (ε := ε)).2
  calc Gp c ε = Gp c ε ^ 1 := (pow_one _).symm
    _ ≤ Gp c ε ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)

lemma Gp_le_Bp : Gp c ε ≤ Bp c ε := Gp_le_Kp.trans Kp_le_Bp

lemma Bp_lt_pow : (Bp c ε : ℝ) < 65 ^ Bp c ε := by
  have h : Bp c ε < 65 ^ Bp c ε := Nat.lt_pow_self (by norm_num)
  exact_mod_cast h

lemma Lp_le : (Lp c ε : ℝ) ≤ 65 ^ Bp c ε := by
  have h1 := commonDen_le (Kp c ε)
  have h2 : 4 * 65 ^ Kp c ε ≤ 65 ^ (Kp c ε + 1) := by rw [pow_succ]; omega
  have h3 : (4 * 65 ^ Kp c ε) ^ ((Kp c ε + 1) ^ 4) ≤ 65 ^ Bp c ε := by
    calc (4 * 65 ^ Kp c ε) ^ ((Kp c ε + 1) ^ 4) ≤ (65 ^ (Kp c ε + 1)) ^ ((Kp c ε + 1) ^ 4) :=
          Nat.pow_le_pow_left h2 _
      _ = 65 ^ Bp c ε := by rw [← pow_mul, Bp]; ring_nf
  have h4 : Lp c ε ≤ 65 ^ Bp c ε := by unfold Lp; exact h1.trans h3
  exact_mod_cast h4

lemma Hp_le : Hp c ε ≤ 65 ^ Bp c ε := by
  unfold Hp
  have h1 : Real.sqrt 65 ≤ 65 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc Real.sqrt 65 ^ Kp c ε ≤ 65 ^ Kp c ε := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 _
    _ ≤ 65 ^ Bp c ε := pow_le_pow_right₀ (by norm_num) Kp_le_Bp

lemma Rp_le : Rp c ε ≤ 65 ^ (2 * Bp c ε + 1) := by
  unfold Rp
  have hL := Lp_le (c := c) (ε := ε)
  have hH := Hp_le (c := c) (ε := ε)
  have hH0 : 0 ≤ Hp c ε := le_trans zero_le_one Hp_ge_one
  have hpow : (65 : ℝ) ^ (2 * Bp c ε + 1) = 65 * (65 ^ Bp c ε * 65 ^ Bp c ε) := by
    rw [pow_succ, two_mul, pow_add]; ring
  have h1 : (1 : ℝ) ≤ 65 ^ Bp c ε := one_le_pow₀ (by norm_num)
  have h2 : 2 * (Lp c ε : ℝ) * Hp c ε ≤ 2 * (65 ^ Bp c ε * 65 ^ Bp c ε) := by
    have : (Lp c ε : ℝ) * Hp c ε ≤ 65 ^ Bp c ε * 65 ^ Bp c ε := by
      apply mul_le_mul hL hH hH0 (by positivity)
    nlinarith
  rw [hpow]
  nlinarith

lemma inv_ε_le : 1 / ε ≤ Bp c ε := by
  obtain ⟨_, _, h1, _⟩ := X0_ge (c := c) (ε := ε)
  have h2 := (Gp_ge (c := c) (ε := ε)).1
  have h3 : (Gp c ε : ℝ) ≤ Bp c ε := by exact_mod_cast Gp_le_Bp
  linarith

lemma cη_le : c * ηKL c ε ^ (-5 : ℝ) ≤ Bp c ε := by
  obtain ⟨_, _, _, h1⟩ := X0_ge (c := c) (ε := ε)
  have h2 := (Gp_ge (c := c) (ε := ε)).1
  have h3 : (Gp c ε : ℝ) ≤ Bp c ε := by exact_mod_cast Gp_le_Bp
  linarith

/- Abstract versions of the remaining estimates (to keep the definitions folded). -/

lemma Q_le_aux {B : ℕ} {R x : ℝ} (hR : R ≤ 65 ^ (2 * B + 1)) (hR0 : 0 ≤ R)
    (hx : x ≤ B) (hx0 : 0 ≤ x) : 128 * R * x + 4 ≤ (65 : ℝ) ^ (3 * B + 3) := by
  have hB : (B : ℝ) < 65 ^ B := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 65)
  have hpow : (65 : ℝ) ^ (3 * B + 3) = 65 ^ 2 * (65 ^ (2 * B + 1) * 65 ^ B) := by
    rw [show 3 * B + 3 = 2 + ((2 * B + 1) + B) by ring, pow_add, pow_add]
  have h1 : (1 : ℝ) ≤ 65 ^ (2 * B + 1) * 65 ^ B := by
    have h1a : (1 : ℝ) ≤ 65 ^ (2 * B + 1) := one_le_pow₀ (by norm_num)
    have h1b : (1 : ℝ) ≤ 65 ^ B := one_le_pow₀ (by norm_num)
    nlinarith
  have h3 : R * x ≤ 65 ^ (2 * B + 1) * 65 ^ B :=
    mul_le_mul hR (hx.trans hB.le) hx0 (by positivity)
  rw [hpow]
  nlinarith

lemma Qp_le (hε : 0 < ε) : Qp c ε ≤ 65 ^ (3 * Bp c ε + 3) := by
  have h := Q_le_aux (B := Bp c ε) (Rp_le (c := c) (ε := ε))
    (by linarith [(Rp_ge (c := c) (ε := ε)).1]) (inv_ε_le (c := c) (ε := ε)) (by positivity)
  unfold Qp
  calc 128 * Rp c ε / ε + 4 = 128 * Rp c ε * (1 / ε) + 4 := by ring
    _ ≤ _ := h

lemma X_le_aux {B : ℕ} {L H Q : ℝ} (hL : L ≤ 65 ^ B) (hH : H ≤ 65 ^ B)
    (hQ : Q ≤ 65 ^ (3 * B + 3)) (hL0 : 0 ≤ L) (hH0 : 0 ≤ H) (hQ0 : 0 ≤ Q) :
    2 * L * H * Q ≤ (65 : ℝ) ^ (5 * B + 4) := by
  have hpow : (65 : ℝ) ^ (5 * B + 4) = 65 * (65 ^ B * 65 ^ B * 65 ^ (3 * B + 3)) := by
    rw [show 5 * B + 4 = 1 + (B + B + (3 * B + 3)) by ring, pow_add, pow_add, pow_add, pow_one]
  have h1 : L * H * Q ≤ 65 ^ B * 65 ^ B * 65 ^ (3 * B + 3) :=
    mul_le_mul (mul_le_mul hL hH hH0 (by positivity)) hQ hQ0 (by positivity)
  rw [hpow]
  have h2 : 0 ≤ L * H * Q := by positivity
  nlinarith

lemma Qp_nonneg (hε : 0 < ε) : 0 ≤ Qp c ε := by
  unfold Qp; have := (Rp_ge (c := c) (ε := ε)).1; positivity

lemma X_le (hε : 0 < ε) :
    2 * (Lp c ε : ℝ) * Hp c ε * Qp c ε ≤ 65 ^ (5 * Bp c ε + 4) :=
  X_le_aux Lp_le Hp_le (Qp_le (c := c) hε) (by positivity) (le_trans zero_le_one Hp_ge_one)
    (Qp_nonneg (c := c) hε)

lemma clog_aux {B : ℕ} {X : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ (65 : ℝ) ^ (5 * B + 4)) :
    Nat.clog 65 (⌈X⌉₊ + 1) ≤ 5 * B + 5 := by
  apply Nat.clog_le_of_le_pow
  have hceil : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one hX0
  have h4 : (1 : ℝ) ≤ 65 ^ (5 * B + 4) := one_le_pow₀ (by norm_num)
  have h3 : (65 : ℝ) ^ (5 * B + 5) = 65 * 65 ^ (5 * B + 4) := by
    rw [show 5 * B + 5 = (5 * B + 4) + 1 by ring, pow_succ]; ring
  have h2 : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ ((65 ^ (5 * B + 5) : ℕ) : ℝ) := by
    push_cast
    rw [h3]; linarith
  exact_mod_cast h2

lemma hp_le (hε : 0 < ε) : hp c ε ≤ 10 * Bp c ε + 10 := by
  have hX0 : 0 ≤ 2 * (Lp c ε : ℝ) * Hp c ε * Qp c ε := by
    have hH0 : 0 ≤ Hp c ε := le_trans zero_le_one Hp_ge_one
    have hQ0 := Qp_nonneg (c := c) hε
    positivity
  have h := clog_aux hX0 (X_le (c := c) hε)
  unfold hp
  omega

lemma logb_bound (h : ℕ) : Real.logb 5 (2 * 13 ^ h) ≤ 1 + 2 * h := by
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]
  have h1 : Real.logb 5 2 ≤ 1 := by
    rw [← Real.logb_self_eq_one (b := 5) (by norm_num)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 5 13 ≤ 2 := by
    have : Real.logb 5 25 = 2 := by
      rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [← this]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
  have h3 : (0 : ℝ) ≤ h := by positivity
  nlinarith

lemma T_le_aux {B K h : ℕ} {t : ℝ} (hK : K ≤ B) (hh : h ≤ 10 * B + 10) (ht0 : 0 ≤ t)
    (ht : t ≤ B) (hB1 : 1 ≤ B) :
    (⌈(K : ℝ) + Real.logb 5 (2 * 13 ^ h) + t⌉₊ : ℝ) ≤ 44 * B := by
  have hKr : (K : ℝ) ≤ B := by exact_mod_cast hK
  have hhr : (h : ℝ) ≤ 10 * B + 10 := by exact_mod_cast hh
  have hB1r : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hlog := logb_bound h
  have hlog0 : 0 ≤ Real.logb 5 (2 * 13 ^ h) :=
    Real.logb_nonneg (by norm_num) (by
      have : (1 : ℝ) ≤ 13 ^ h := one_le_pow₀ (by norm_num)
      linarith)
  have hnn : 0 ≤ (K : ℝ) + Real.logb 5 (2 * 13 ^ h) + t := by positivity
  have hT := Nat.ceil_lt_add_one hnn
  linarith

lemma Tp_le (hc : 0 ≤ c) (hε : 0 < ε) : (Tp c ε : ℝ) ≤ 44 * Bp c ε := by
  unfold Tp
  exact T_le_aux Kp_le_Bp (hp_le (c := c) hε)
    (by have := ηKL_pos c ε; positivity) (cη_le (c := c) (ε := ε)) one_le_Bp

lemma U_le_aux {B : ℕ} {ε R : ℝ} (hB1 : 1 ≤ B) (hε : 0 < ε) (hiε : 1 / ε ≤ B)
    (hR16 : 16 ≤ R) (hR : R ≤ (65 : ℝ) ^ (2 * B + 1)) :
    3 + 16 * Real.pi / ε + 17 * (4 / ε + 2) * ((Nat.log 2 ⌊R⌋₊ : ℝ) + 1) ≤ 2200 * (B : ℝ) ^ 2 := by
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hfl0 : ⌊R⌋₊ ≠ 0 := by
    have : 16 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR16)
    omega
  have hlt : ⌊R⌋₊ < 2 ^ (7 * (2 * B + 1)) := by
    have h1 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le (by linarith)
    have h2 : (65 : ℝ) ^ (2 * B + 1) < 2 ^ (7 * (2 * B + 1)) := by
      rw [pow_mul]
      exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    have h3 : (⌊R⌋₊ : ℝ) < ((2 ^ (7 * (2 * B + 1)) : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  have hlog : Nat.log 2 ⌊R⌋₊ < 7 * (2 * B + 1) := Nat.log_lt_of_lt_pow hfl0 hlt
  have hlogr : (Nat.log 2 ⌊R⌋₊ : ℝ) + 1 ≤ 21 * B := by
    have : Nat.log 2 ⌊R⌋₊ + 1 ≤ 21 * B := by omega
    exact_mod_cast this
  have hpi : Real.pi ≤ 3.15 := by linarith [Real.pi_lt_d2]
  have h1 : 16 * Real.pi / ε ≤ 51 * B := by
    have : 16 * Real.pi / ε = 16 * Real.pi * (1 / ε) := by ring
    rw [this]
    have hpi0 := Real.pi_pos
    nlinarith
  have h2 : 4 / ε + 2 ≤ 6 * B := by
    have : 4 / ε = 4 * (1 / ε) := by ring
    rw [this]; linarith
  have h3 : 17 * (4 / ε + 2) * ((Nat.log 2 ⌊R⌋₊ : ℝ) + 1) ≤ 17 * (6 * B) * (21 * B) := by
    have h4 : 0 ≤ 4 / ε + 2 := by positivity
    have h5 : 0 ≤ (Nat.log 2 ⌊R⌋₊ : ℝ) + 1 := by positivity
    gcongr
  nlinarith

lemma card_discSet_le (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    ((discSet ε (Rp c ε)).card : ℝ) ≤ 2200 * (Bp c ε : ℝ) ^ 2 := by
  obtain ⟨_, _, _, hcard⟩ := disc_cover hε hε1 (Rp_ge (c := c) (ε := ε)).1
  exact hcard.trans (U_le_aux one_le_Bp hε inv_ε_le (Rp_ge (c := c) (ε := ε)).1 Rp_le)

lemma final_aux {B G : ℕ} {m T U : ℝ} (hG : 66 ≤ G) (hB : B ≤ 32 * G ^ 20) (hB1 : 1 ≤ B)
    (hm : m ≤ (2 * (T + 1) ^ 2 + 1) * U) (hT : T ≤ 44 * B) (hT0 : 0 ≤ T)
    (hU : U ≤ 2200 * (B : ℝ) ^ 2) (hU0 : 0 ≤ U) : m ≤ (G : ℝ) ^ 88 := by
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hGr : (66 : ℝ) ≤ G := by exact_mod_cast hG
  have hBG : (B : ℝ) ≤ 32 * (G : ℝ) ^ 20 := by exact_mod_cast hB
  have h1 : (2 * (T + 1) ^ 2 + 1) ≤ 4051 * (B : ℝ) ^ 2 := by
    have : T + 1 ≤ 45 * B := by linarith
    have h2 : (T + 1) ^ 2 ≤ (45 * (B : ℝ)) ^ 2 := by gcongr
    nlinarith
  have h2 : m ≤ 4051 * (B : ℝ) ^ 2 * (2200 * (B : ℝ) ^ 2) := by
    calc m ≤ (2 * (T + 1) ^ 2 + 1) * U := hm
      _ ≤ 4051 * (B : ℝ) ^ 2 * (2200 * (B : ℝ) ^ 2) := by
          apply mul_le_mul h1 hU hU0 (by positivity)
  have h3 : 4051 * (B : ℝ) ^ 2 * (2200 * (B : ℝ) ^ 2) ≤ 10 ^ 7 * (B : ℝ) ^ 4 := by nlinarith
  have h4 : (B : ℝ) ^ 4 ≤ (32 * (G : ℝ) ^ 20) ^ 4 := by gcongr
  have h5 : (10 : ℝ) ^ 7 * (32 * (G : ℝ) ^ 20) ^ 4 ≤ (G : ℝ) ^ 88 := by
    have hG8 : (10 : ℝ) ^ 7 * 32 ^ 4 ≤ (G : ℝ) ^ 8 := by
      calc (10 : ℝ) ^ 7 * 32 ^ 4 ≤ 66 ^ 8 := by norm_num
        _ ≤ (G : ℝ) ^ 8 := by gcongr
    have : (10 : ℝ) ^ 7 * (32 * (G : ℝ) ^ 20) ^ 4 = (10 ^ 7 * 32 ^ 4) * (G : ℝ) ^ 80 := by ring
    rw [this]
    calc (10 ^ 7 * 32 ^ 4) * (G : ℝ) ^ 80 ≤ (G : ℝ) ^ 8 * (G : ℝ) ^ 80 := by gcongr
      _ = (G : ℝ) ^ 88 := by ring
  calc m ≤ 4051 * (B : ℝ) ^ 2 * (2200 * (B : ℝ) ^ 2) := h2
    _ ≤ 10 ^ 7 * (B : ℝ) ^ 4 := h3
    _ ≤ 10 ^ 7 * (32 * (G : ℝ) ^ 20) ^ 4 := by gcongr
    _ ≤ (G : ℝ) ^ 88 := h5

lemma Bp_le_G (c ε : ℝ) : Bp c ε ≤ 32 * Gp c ε ^ 20 := by
  have hG := (Gp_ge (c := c) (ε := ε)).2
  unfold Bp Kp
  calc (Gp c ε ^ 4 + 1) ^ 5 ≤ (2 * Gp c ε ^ 4) ^ 5 := by
        apply Nat.pow_le_pow_left
        have : 1 ≤ Gp c ε ^ 4 := Nat.one_le_pow _ _ (by omega)
        omega
    _ = 32 * Gp c ε ^ 20 := by ring

/-- `minCopies ε ≤ G^88`, conditional on `KL57With c`. -/
theorem minCopies_le_G_pow (hKL : KL57With c) (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    (minCopies ε : ℝ) ≤ (Gp c ε : ℝ) ^ 88 :=
  final_aux (Gp_ge (c := c) (ε := ε)).2 (Bp_le_G c ε) one_le_Bp
    (minCopies_le_param hKL hε hε1) (Tp_le hc hε) (by positivity)
    (card_discSet_le hε hε1) (by positivity)

end

end Green41

/- ## Section: `Final` -/

/-
# The double-exponential bound, conditional on `KL57`

With `a = ε^(-c)`, `x = 1/ε` and `Y = η⁻⁵ = 5^(5a) ≤ e^(20a)`:
`G ≤ 91 exp(12(1+c)Y + x)`, so `G^88 ≤ exp(S)` with `S ≤ A e^(20a) x`, `A = 10⁴(1+c)`.
For `x ≥ 10 + log A` this is at most `exp(a x²) = exp(ε^(-(c+2)))`.
-/

namespace Green41

open Complex ComplexConjugate

lemma le_exp_self (x : ℝ) : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]

lemma log_le_self_sub_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1 :=
  Real.log_le_sub_one_of_pos hx

section

variable {c ε : ℝ}

lemma a_ge_one (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ ε ^ (-c) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)

lemma Y_eq (c ε : ℝ) : ηKL c ε ^ (-5 : ℝ) = (5 : ℝ) ^ (5 * ε ^ (-c)) := by
  unfold ηKL
  rw [← Real.rpow_mul (by norm_num)]
  ring_nf

lemma inv_η_le_Y (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 / ηKL c ε ≤ ηKL c ε ^ (-5 : ℝ) := by
  have ha := a_ge_one hc hε hε1
  rw [Y_eq]
  unfold ηKL
  rw [Real.rpow_neg (by norm_num), one_div, inv_inv]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma one_le_Y (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ ηKL c ε ^ (-5 : ℝ) := by
  rw [Y_eq]
  exact Real.one_le_rpow (by norm_num) (by have := a_ge_one hc hε hε1; linarith)

lemma Y_le_exp (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ηKL c ε ^ (-5 : ℝ) ≤ Real.exp (20 * ε ^ (-c)) := by
  have ha := a_ge_one hc hε hε1
  rw [Y_eq, Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have h5 : Real.log 5 ≤ 4 := by linarith [log_le_self_sub_one (show (0:ℝ) < 5 by norm_num)]
  have h0 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith

lemma two_div_δ (c ε : ℝ) : 2 / δKL c ε = 2 * (13 : ℝ) ^ (c * ηKL c ε ^ (-5 : ℝ)) := by
  unfold δKL
  rw [Real.rpow_neg (by norm_num)]
  field_simp

lemma thirteen_rpow_le {y : ℝ} (hy : 0 ≤ y) : (13 : ℝ) ^ y ≤ Real.exp (12 * y) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have h13 : Real.log 13 ≤ 12 := by linarith [log_le_self_sub_one (show (0:ℝ) < 13 by norm_num)]
  nlinarith

theorem Gp_le_exp (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Gp c ε : ℝ) ≤ 91 * Real.exp (12 * (1 + c) * ηKL c ε ^ (-5 : ℝ) + 1 / ε) := by
  set Y := ηKL c ε ^ (-5 : ℝ) with hY
  have hY1 : 1 ≤ Y := one_le_Y hc hε hε1
  have hη := ηKL_pos c ε
  set E := Real.exp (12 * (1 + c) * Y + 1 / ε) with hE
  have hx0 : 0 ≤ 1 / ε := by positivity
  have hcY : 0 ≤ c * Y := by positivity
  have hexp_mono : ∀ t : ℝ, t ≤ 12 * (1 + c) * Y + 1 / ε → Real.exp t ≤ E := fun t ht =>
    Real.exp_le_exp.mpr ht
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  -- the four terms of `X0`
  have t1 : 20 / ηKL c ε ≤ 20 * E := by
    have : 20 / ηKL c ε = 20 * (1 / ηKL c ε) := by ring
    rw [this]
    have h1 := inv_η_le_Y hc hε hε1
    have h2 : Y ≤ E := (le_exp_self Y).trans (hexp_mono Y (by nlinarith))
    rw [← hY] at h1
    nlinarith
  have t2 : 2 / δKL c ε ≤ 2 * E := by
    rw [two_div_δ, ← hY]
    have h1 := thirteen_rpow_le hcY
    have h2 : Real.exp (12 * (c * Y)) ≤ E := hexp_mono _ (by nlinarith)
    nlinarith
  have t3 : 1 / ε ≤ E := (le_exp_self _).trans (hexp_mono _ (by nlinarith))
  have t4 : c * Y ≤ E := (le_exp_self _).trans (hexp_mono _ (by nlinarith))
  have hX0 : X0 c ε ≤ 20 * E + 2 * E + E + E := by
    unfold X0
    have h20 : 0 ≤ 20 / ηKL c ε := by positivity
    have h2 : 0 ≤ 2 / δKL c ε := by have := δKL_pos c ε; positivity
    rw [← hY]
    apply max_le <;> apply max_le <;> linarith
  have hX00 : 0 ≤ X0 c ε := by
    unfold X0
    exact le_trans (by positivity) ((le_max_left _ _).trans (le_max_left _ _))
  have hG : (Gp c ε : ℝ) < X0 c ε + 67 := by
    unfold Gp
    push_cast
    have := Nat.ceil_lt_add_one hX00
    linarith
  nlinarith

theorem final_bound (hc : 0 ≤ c) (hε : 0 < ε)
    (hεA : ε ≤ 1 / (10 + Real.log (10000 * (1 + c)))) :
    (91 * Real.exp (12 * (1 + c) * ηKL c ε ^ (-5 : ℝ) + 1 / ε)) ^ 88 ≤
      Real.exp (Real.exp (ε ^ (-(c + 2)))) := by
  set A : ℝ := 10000 * (1 + c) with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  set Lg := Real.log A with hLg
  have hLg0 : 0 ≤ Lg := Real.log_nonneg hA1
  have hden : 0 < 10 + Lg := by linarith
  have hε1 : ε ≤ 1 := by
    have : 1 / (10 + Lg) ≤ 1 := by rw [div_le_one hden]; linarith
    linarith
  set x : ℝ := 1 / ε with hx
  have hxge : 10 + Lg ≤ x := by
    rw [hx]
    rw [le_div_iff₀ hε]
    rw [le_div_iff₀ hden] at hεA
    linarith
  have hx10 : 10 ≤ x := by linarith
  set a : ℝ := ε ^ (-c) with ha
  have ha1 : 1 ≤ a := a_ge_one hc hε hε1
  set Y := ηKL c ε ^ (-5 : ℝ) with hY
  have hY1 : 1 ≤ Y := one_le_Y hc hε hε1
  have hYe : Y ≤ Real.exp (20 * a) := Y_le_exp hc hε hε1
  -- the exponent `ε^(-(c+2)) = a x²`
  have hexp_eq : ε ^ (-(c + 2)) = a * x ^ 2 := by
    rw [ha, hx, show -(c + 2) = -c + (-2 : ℝ) by ring, Real.rpow_add hε, Real.rpow_neg hε.le c,
      Real.rpow_neg hε.le 2, Real.rpow_two]
    field_simp
  -- `(91 e^t)^88 = exp(88 log 91 + 88 t)`
  have hpow : (91 * Real.exp (12 * (1 + c) * Y + x)) ^ 88 =
      Real.exp (88 * Real.log 91 + 88 * (12 * (1 + c) * Y + x)) := by
    have h91 : Real.exp (88 * Real.log 91) = 91 ^ 88 := by
      rw [show (88 : ℝ) * Real.log 91 = Real.log (91 ^ 88) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    have h2 : Real.exp (88 * (12 * (1 + c) * Y + x)) = Real.exp (12 * (1 + c) * Y + x) ^ 88 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [show Real.exp (88 * Real.log 91 + 88 * (12 * (1 + c) * Y + x)) =
        Real.exp (88 * Real.log 91) * Real.exp (88 * (12 * (1 + c) * Y + x)) from Real.exp_add _ _,
      h91, h2, mul_pow]
  rw [hpow, hexp_eq]
  apply Real.exp_le_exp.mpr
  -- `S ≤ A e^(20a) x`
  have hlog91 : Real.log 91 ≤ 90 := by linarith [log_le_self_sub_one (show (0:ℝ) < 91 by norm_num)]
  have he20 : 1 ≤ Real.exp (20 * a) := Real.one_le_exp (by linarith)
  have hS : 88 * Real.log 91 + 88 * (12 * (1 + c) * Y + x) ≤ A * Real.exp (20 * a) * x := by
    have h1 : 88 * Real.log 91 ≤ 7920 * Real.exp (20 * a) * x := by
      have : (1 : ℝ) ≤ Real.exp (20 * a) * x := by nlinarith
      nlinarith
    have h2 : 88 * (12 * (1 + c) * Y) ≤ 1056 * (1 + c) * Real.exp (20 * a) * x := by
      have hc1 : 0 ≤ 1 + c := by linarith
      have : Y ≤ Real.exp (20 * a) * x := by nlinarith
      nlinarith
    have h3 : 88 * x ≤ 88 * Real.exp (20 * a) * x := by nlinarith
    rw [hA]
    nlinarith
  -- `A e^(20a) x ≤ e^(a x²)`
  have hlogx : Real.log x ≤ x := by linarith [log_le_self_sub_one (show (0:ℝ) < x by linarith)]
  have hkey : Lg + 20 * a + Real.log x ≤ a * x ^ 2 := by
    have h1 : x ^ 2 - 20 ≤ a * (x ^ 2 - 20) := by
      have : 0 ≤ x ^ 2 - 20 := by nlinarith
      nlinarith
    have h2 : Lg + x ≤ x ^ 2 - 20 := by nlinarith
    nlinarith
  have hAx : A * Real.exp (20 * a) * x = Real.exp (Lg + 20 * a + Real.log x) := by
    rw [Real.exp_add, Real.exp_add, hLg, Real.exp_log (by linarith), Real.exp_log (by linarith)]
  calc 88 * Real.log 91 + 88 * (12 * (1 + c) * Y + x) ≤ A * Real.exp (20 * a) * x := hS
    _ = Real.exp (Lg + 20 * a + Real.log x) := hAx
    _ ≤ Real.exp (a * x ^ 2) := Real.exp_le_exp.mpr hkey

end

/-- The FC right-hand side, conditional on the Kravitz–Leng interface `KL57`. -/
theorem doubleExponentialBound_of_KL57 (h : KL57) : DoubleExponentialBound := by
  obtain ⟨c, hc, hKL⟩ := h
  have hA1 : (1 : ℝ) < 10000 * (1 + c) := by nlinarith
  have hLg : 0 < Real.log (10000 * (1 + c)) := Real.log_pos hA1
  refine ⟨c + 2, 1 / (10 + Real.log (10000 * (1 + c))), by positivity, ?_⟩
  rintro ε ⟨hε0, hεle⟩
  have hε1 : ε < 1 / 10 := by
    have : 1 / (10 + Real.log (10000 * (1 + c))) < 1 / 10 := by
      apply one_div_lt_one_div_of_lt (by norm_num); linarith
    linarith
  have hG := Gp_le_exp (c := c) hc.le hε0 (by linarith)
  have hG0 : (0 : ℝ) ≤ Gp c ε := by positivity
  calc (minCopies ε : ℝ) ≤ (Gp c ε : ℝ) ^ 88 := minCopies_le_G_pow hKL hc.le hε0 hε1
    _ ≤ (91 * Real.exp (12 * (1 + c) * ηKL c ε ^ (-5 : ℝ) + 1 / ε)) ^ 88 := by gcongr
    _ ≤ Real.exp (Real.exp (ε ^ (-(c + 2)))) := final_bound hc.le hε0 hεle

end Green41

/- ## Section: `Residue` -/

/-
# Residues of Gaussian integers modulo `πⁿ`

For a Gaussian prime `π` of prime norm `p` with `π ∤ π̄`, we build a ring hom
`ψ hπ n : ℤ[i] →+* ZMod (p ^ n)` sending `i` to `Im(πⁿ) / Re(πⁿ)`. Its kernel is `πⁿ ℤ[i]`,
and it satisfies the stripe formula `Re(z · π̄ⁿ) ≡ Re(πⁿ) · ψ(z) (mod pⁿ)`
(blueprint §1, (R1)–(R4)).
-/

namespace Green41

open Complex ComplexConjugate

lemma gauss_add_star (z : GaussianInt) : z + star z = (((2 * z.re : ℤ)) : GaussianInt) := by
  ext <;> simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_star, Zsqrtd.im_star,
    Zsqrtd.re_intCast, Zsqrtd.im_intCast] <;> ring

lemma gauss_mul_star_re (z w : GaussianInt) : (z * star w).re = z.re * w.re + z.im * w.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]; ring

lemma gauss_mul_star_im (z w : GaussianInt) : (z * star w).im = z.im * w.re - z.re * w.im := by
  simp only [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]; ring

/-- Hypotheses on a digit prime `π`: its norm is the prime `p`, and `π ∤ π̄`. -/
structure DigitPrime (π : GaussianInt) (p : ℕ) : Prop where
  prime : p.Prime
  norm : π.norm = p
  not_dvd_star : ¬ π ∣ star π

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

lemma prime_π : Prime π :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [hπ.norm]; simpa using hπ.prime))

lemma norm_pow (n : ℕ) : (π ^ n).norm = (p : ℤ) ^ n := by
  rw [← hπ.norm]; exact map_pow Zsqrtd.normMonoidHom π n

lemma natCast_pow_eq (n : ℕ) : ((p ^ n : ℕ) : GaussianInt) = π ^ n * star (π ^ n) := by
  rw [← Zsqrtd.norm_eq_mul_conj, hπ.norm_pow]; push_cast; rfl


lemma not_dvd_re_pow (n : ℕ) : ¬ (p : ℤ) ∣ (π ^ n).re := by
  intro h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, Zsqrtd.re_one] at h
    exact hπ.prime.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
  have hπp : π ∣ ((p : ℤ) : GaussianInt) := by
    refine ⟨star π, ?_⟩
    have := hπ.natCast_pow_eq 1
    simp only [pow_one] at this
    rw [← this]; push_cast; rfl
  have h2 : π ∣ (((2 * (π ^ n).re : ℤ)) : GaussianInt) := by
    obtain ⟨k, hk⟩ := h
    refine dvd_trans hπp ⟨2 * k, ?_⟩
    rw [hk]; push_cast; ring
  rw [← gauss_add_star] at h2
  have h3 : π ∣ star (π ^ n) := (dvd_add_right (dvd_pow_self π hn.ne')).mp h2
  rw [star_pow] at h3
  exact hπ.not_dvd_star (hπ.prime_π.dvd_of_dvd_pow h3)

end DigitPrime

/-- An integer prime to `p` is a unit modulo `p ^ n`. -/
lemma isUnit_intCast_of_not_dvd {p : ℕ} (hp : p.Prime) {a : ℤ} (h : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    IsUnit ((a : ℤ) : ZMod (p ^ n)) := by
  have hc : IsCoprime ((p : ℤ) ^ n) a :=
    ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr h).pow_left
  obtain ⟨u, v, huv⟩ := hc
  refine IsUnit.of_mul_eq_one (v : ZMod (p ^ n)) ?_
  have h1 := congrArg (fun x : ℤ => (x : ZMod (p ^ n))) huv
  have hp0 : ((p : ZMod (p ^ n))) ^ n = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one, hp0,
    mul_zero, zero_add] at h1
  simpa [mul_comm] using h1

section Psi

variable {π : GaussianInt} {p : ℕ}

/-- `ψₙ(i) = Im(πⁿ) / Re(πⁿ)` in `ZMod (p ^ n)`. -/
def rootψ (π : GaussianInt) (p n : ℕ) : ZMod (p ^ n) :=
  ((π ^ n).im : ZMod (p ^ n)) * ((π ^ n).re : ZMod (p ^ n))⁻¹

namespace DigitPrime

variable (hπ : DigitPrime π p)
include hπ

lemma isUnit_re (n : ℕ) : IsUnit (((π ^ n).re : ℤ) : ZMod (p ^ n)) :=
  isUnit_intCast_of_not_dvd hπ.prime (hπ.not_dvd_re_pow n) n

lemma re_mul_inv (n : ℕ) :
    (((π ^ n).re : ℤ) : ZMod (p ^ n)) * (((π ^ n).re : ℤ) : ZMod (p ^ n))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (hπ.isUnit_re n)

lemma re_sq_add_im_sq (n : ℕ) :
    (((π ^ n).re : ℤ) : ZMod (p ^ n)) * ((π ^ n).re : ℤ) +
      (((π ^ n).im : ℤ) : ZMod (p ^ n)) * ((π ^ n).im : ℤ) = 0 := by
  have h := hπ.norm_pow n
  rw [Zsqrtd.norm_def] at h
  have h2 : ((π ^ n).re * (π ^ n).re + (π ^ n).im * (π ^ n).im : ℤ) = (p : ℤ) ^ n := by
    linarith
  have h3 := congrArg (fun x : ℤ => (x : ZMod (p ^ n))) h2
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast] at h3
  rw [h3, ← Nat.cast_pow, ZMod.natCast_self]

lemma rootψ_mul_self (n : ℕ) : rootψ π p n * rootψ π p n = -1 := by
  unfold rootψ
  set R : ZMod (p ^ n) := (((π ^ n).re : ℤ) : ZMod (p ^ n))
  set I : ZMod (p ^ n) := (((π ^ n).im : ℤ) : ZMod (p ^ n))
  have h1 : R * R⁻¹ = 1 := hπ.re_mul_inv n
  have h2 : R * R + I * I = 0 := hπ.re_sq_add_im_sq n
  have h3 : I * I = -(R * R) := by linear_combination h2
  calc I * R⁻¹ * (I * R⁻¹) = (I * I) * (R⁻¹ * R⁻¹) := by ring
    _ = -((R * R⁻¹) * (R * R⁻¹)) := by rw [h3]; ring
    _ = -1 := by rw [h1]; ring

/-- The residue map `ψₙ : ℤ[i] →+* ZMod (pⁿ)`, `x + yi ↦ x + y · Im(πⁿ)/Re(πⁿ)`. -/
def ψ (n : ℕ) : GaussianInt →+* ZMod (p ^ n) :=
  Zsqrtd.lift ⟨rootψ π p n, by rw [hπ.rootψ_mul_self]; simp⟩

lemma ψ_apply (n : ℕ) (z : GaussianInt) :
    hπ.ψ n z = (z.re : ZMod (p ^ n)) + (z.im : ZMod (p ^ n)) * rootψ π p n := rfl

lemma ψ_pow_self (n : ℕ) : hπ.ψ n (π ^ n) = 0 := by
  rw [ψ_apply]
  unfold rootψ
  set R : ZMod (p ^ n) := (((π ^ n).re : ℤ) : ZMod (p ^ n))
  set I : ZMod (p ^ n) := (((π ^ n).im : ℤ) : ZMod (p ^ n))
  have h1 : R * R⁻¹ = 1 := hπ.re_mul_inv n
  have h2 : R * R + I * I = 0 := hπ.re_sq_add_im_sq n
  calc R + I * (I * R⁻¹) = (R * R + I * I) * R⁻¹ + R * (1 - R * R⁻¹) := by ring
    _ = 0 := by rw [h1, h2]; ring

/-- (R1) The kernel of `ψₙ` is `πⁿ ℤ[i]`. -/
lemma ψ_eq_zero_iff (n : ℕ) (z : GaussianInt) : hπ.ψ n z = 0 ↔ π ^ n ∣ z := by
  constructor
  · intro hz
    rw [ψ_apply] at hz
    unfold rootψ at hz
    set R : ZMod (p ^ n) := (((π ^ n).re : ℤ) : ZMod (p ^ n)) with hR
    set I : ZMod (p ^ n) := (((π ^ n).im : ℤ) : ZMod (p ^ n)) with hI
    have h1 : R * R⁻¹ = 1 := hπ.re_mul_inv n
    have h2 : R * R + I * I = 0 := hπ.re_sq_add_im_sq n
    have ha : ((z.re * (π ^ n).re + z.im * (π ^ n).im : ℤ) : ZMod (p ^ n)) = 0 := by
      push_cast
      rw [← hR, ← hI]
      calc (z.re : ZMod (p ^ n)) * R + z.im * I
          = R * (z.re + z.im * (I * R⁻¹)) + z.im * I * (1 - R * R⁻¹) := by ring
        _ = 0 := by rw [hz, h1]; ring
    have hb : ((z.im * (π ^ n).re - z.re * (π ^ n).im : ℤ) : ZMod (p ^ n)) = 0 := by
      push_cast
      rw [← hR, ← hI]
      have hre : (z.re : ZMod (p ^ n)) = -(z.im * (I * R⁻¹)) := by linear_combination hz
      calc (z.im : ZMod (p ^ n)) * R - z.re * I
          = z.im * R - (-(z.im * (I * R⁻¹))) * I := by rw [hre]
        _ = z.im * R⁻¹ * (R * R + I * I) + z.im * R * (1 - R * R⁻¹) := by ring
        _ = 0 := by rw [h1, h2]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hb
    have hdiv : (((p ^ n : ℕ) : ℤ) : GaussianInt) ∣ z * star (π ^ n) := by
      rw [Zsqrtd.intCast_dvd]
      constructor
      · rw [gauss_mul_star_re]; simpa using ha
      · rw [gauss_mul_star_im]; simpa using hb
    have hcast : (((p ^ n : ℕ) : ℤ) : GaussianInt) = π ^ n * star (π ^ n) := by
      rw [Int.cast_natCast]; exact hπ.natCast_pow_eq n
    rw [hcast] at hdiv
    have hne : star (π ^ n) ≠ 0 := by
      rw [star_pow]
      exact pow_ne_zero _ (fun h0 => hπ.prime_π.ne_zero (by
        simpa using congrArg star h0))
    exact (mul_dvd_mul_iff_right hne).mp hdiv
  · rintro ⟨y, rfl⟩
    rw [map_mul, hπ.ψ_pow_self, zero_mul]

/-- (R2) The stripe formula: `Re(z · π̄ⁿ) ≡ Re(πⁿ) · ψₙ(z) (mod pⁿ)`. -/
lemma stripe_formula (n : ℕ) (z : GaussianInt) :
    (((z * star (π ^ n)).re : ℤ) : ZMod (p ^ n)) = ((π ^ n).re : ℤ) * hπ.ψ n z := by
  rw [gauss_mul_star_re, ψ_apply]
  unfold rootψ
  have h1 := hπ.re_mul_inv n
  push_cast
  linear_combination (-(z.im : ZMod (p ^ n)) * ((π ^ n).im : ZMod (p ^ n))) * h1

/-- (R3) `ψ(π) ψ(π̄) = p`. -/
lemma ψ_mul_star (n : ℕ) : hπ.ψ n π * hπ.ψ n (star π) = p := by
  rw [← map_mul]
  have := hπ.natCast_pow_eq 1
  simp only [pow_one] at this
  rw [← this, map_natCast]

/-- `ψₙ(z)` is a unit iff `π ∤ z` (for `n ≥ 1`). -/
lemma isUnit_ψ_iff {n : ℕ} (hn : 0 < n) (z : GaussianInt) : IsUnit (hπ.ψ n z) ↔ ¬ π ∣ z := by
  have hp := hπ.prime
  have : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow hn.ne' hp.one_lt⟩
  constructor
  · rintro hu ⟨y, rfl⟩
    rw [map_mul] at hu
    have hπu : IsUnit (hπ.ψ n π) := isUnit_of_mul_isUnit_left hu
    have h0 : hπ.ψ n π ^ n = 0 := by rw [← map_pow, hπ.ψ_pow_self]
    have := (hπu.pow n)
    rw [h0] at this
    exact not_isUnit_zero this
  · intro hz
    by_contra hu
    set x := hπ.ψ n z with hx
    have hxv : ((x.val : ℕ) : ZMod (p ^ n)) = x := ZMod.natCast_zmod_val x
    have hnd : p ∣ x.val := by
      by_contra hnd
      exact hu (hxv ▸ (ZMod.isUnit_natCast_iff_not_dvd_pow hp hn).mpr hnd)
    obtain ⟨k, hk⟩ := hnd
    have hxn : x ^ n = 0 := by
      rw [← hxv, hk, Nat.cast_mul, mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
    have : π ^ n ∣ z ^ n := by
      rw [← hπ.ψ_eq_zero_iff, map_pow, ← hx, hxn]
    exact hz (hπ.prime_π.dvd_of_dvd_pow (dvd_trans (dvd_pow_self π hn.ne') this))

/-- (R4) The conjugate residue map `ψ̄ₙ = ψₙ ∘ conj`, with kernel `π̄ⁿ ℤ[i]`. -/
def ψbar (n : ℕ) : GaussianInt →+* ZMod (p ^ n) := (hπ.ψ n).comp (starRingEnd GaussianInt)

lemma ψbar_apply (n : ℕ) (z : GaussianInt) : hπ.ψbar n z = hπ.ψ n (star z) := rfl

lemma ψbar_eq_zero_iff (n : ℕ) (z : GaussianInt) : hπ.ψbar n z = 0 ↔ star π ^ n ∣ z := by
  rw [ψbar_apply, ψ_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨star y, ?_⟩
    have := congrArg star hy
    rwa [star_star, star_mul, star_pow, mul_comm] at this
  · rintro ⟨y, rfl⟩
    exact ⟨star y, by rw [star_mul, star_pow, star_star, mul_comm]⟩

lemma isUnit_ψbar_iff {n : ℕ} (hn : 0 < n) (z : GaussianInt) :
    IsUnit (hπ.ψbar n z) ↔ ¬ star π ∣ z := by
  rw [ψbar_apply, hπ.isUnit_ψ_iff hn]
  constructor
  · rintro h ⟨y, rfl⟩
    exact h ⟨star y, by rw [star_mul, star_star, mul_comm]⟩
  · rintro h ⟨y, hy⟩
    exact h ⟨star y, by rw [← star_star z, hy, star_mul, mul_comm]⟩

end DigitPrime

end Psi

end Green41

/- ## Section: `Orders` -/

/-
# Orders of the multipliers (Kravitz–Leng Lemma 3.2 with `α = 1`)

If `B` has order `p - 1` modulo `p` and `B^(p-1) ≢ 1 (mod p²)`, then `B` has order
`(p - 1) p^(k-1)` modulo `p^k` for every `k ≥ 1` (lifting the exponent), so its powers run
through all units of `ZMod (p^k)` (blueprint §2).
-/

namespace Green41

lemma natCast_pow_eq_one_iff {B : ℕ} (hB : 0 < B) (M m : ℕ) :
    (B : ZMod M) ^ m = 1 ↔ M ∣ B ^ m - 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm,
    Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hB)]

section LTE

variable {p : ℕ}

/-- LTE: `p^k ∣ B^m - 1 ↔ (p - 1) p^(k-1) ∣ m`. -/
lemma pow_sub_one_dvd_iff (hpr : p.Prime) (hodd : Odd p) {B : ℕ} (hB : 2 ≤ B)
    (h1 : orderOf (B : ZMod p) = p - 1) (h2 : (B : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    p ^ k ∣ B ^ m - 1 ↔ (p - 1) * p ^ (k - 1) ∣ m := by
  have hp : Fact p.Prime := ⟨hpr⟩
  have hp2 : 2 ≤ p := hpr.two_le
  have hB0 : 0 < B := by omega
  set x := B ^ (p - 1) with hxdef
  have hx1 : 1 < x := Nat.one_lt_pow (by omega) (by omega)
  have hpx : p ∣ x - 1 := by
    have h := pow_orderOf_eq_one (B : ZMod p)
    rw [h1] at h
    exact (natCast_pow_eq_one_iff hB0 p (p - 1)).mp h
  have hnx : ¬ p ∣ x := by
    intro h
    have h3 : p ∣ x - (x - 1) := Nat.dvd_sub h hpx
    rw [Nat.sub_sub_self hx1.le] at h3
    exact hpr.one_lt.ne' (Nat.dvd_one.mp h3)
  have hv1 : padicValNat p (x - 1) = 1 := by
    have hne : x - 1 ≠ 0 := by omega
    have hge : 1 ≤ padicValNat p (x - 1) := (padicValNat_dvd_iff_le hne).mp (by simpa using hpx)
    have hlt : ¬ 2 ≤ padicValNat p (x - 1) := by
      intro h
      apply h2
      rw [natCast_pow_eq_one_iff hB0]
      exact (padicValNat_dvd_iff_le hne).mpr h
    omega
  have hlte : ∀ m' : ℕ, m' ≠ 0 → padicValNat p (x ^ m' - 1) = 1 + padicValNat p m' := by
    intro m' hm'
    have := padicValNat.pow_sub_pow hodd hx1 hpx hnx hm'
    rw [one_pow] at this
    rw [this, hv1]
  have hxm : ∀ m' : ℕ, m' ≠ 0 → x ^ m' - 1 ≠ 0 := by
    intro m' hm'
    have : 1 < x ^ m' := Nat.one_lt_pow hm' hx1
    omega
  constructor
  · intro hdvd
    have hpm : p ∣ B ^ m - 1 := dvd_trans (dvd_pow_self p (by omega)) hdvd
    have hord : p - 1 ∣ m := by
      rw [← h1]
      apply orderOf_dvd_of_pow_eq_one
      exact (natCast_pow_eq_one_iff hB0 p m).mpr hpm
    obtain ⟨m', rfl⟩ := hord
    rcases Nat.eq_zero_or_pos m' with rfl | hm'
    · simp
    rw [pow_mul] at hdvd
    have hle : k ≤ padicValNat p (x ^ m' - 1) := (padicValNat_dvd_iff_le (hxm m' hm'.ne')).mp hdvd
    rw [hlte m' hm'.ne'] at hle
    have : p ^ (k - 1) ∣ m' := (padicValNat_dvd_iff_le hm'.ne').mpr (by omega)
    exact mul_dvd_mul_left _ this
  · rintro ⟨c, rfl⟩
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    have hm' : p ^ (k - 1) * c ≠ 0 := by positivity
    rw [mul_assoc, pow_mul]
    apply (padicValNat_dvd_iff_le (hxm _ hm')).mpr
    rw [hlte _ hm', padicValNat.mul (by positivity) hc.ne', padicValNat.prime_pow]
    omega

/-- The order of `B` modulo `p^k` is `(p - 1) p^(k-1)`. -/
lemma orderOf_natCast_prime_pow (hpr : p.Prime) (hodd : Odd p) {B : ℕ} (hB : 2 ≤ B)
    (h1 : orderOf (B : ZMod p) = p - 1) (h2 : (B : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    orderOf (B : ZMod (p ^ k)) = (p - 1) * p ^ (k - 1) := by
  have hB0 : 0 < B := by omega
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [natCast_pow_eq_one_iff hB0, pow_sub_one_dvd_iff hpr hodd hB h1 h2 hk]
  · rw [← pow_sub_one_dvd_iff hpr hodd hB h1 h2 hk, ← natCast_pow_eq_one_iff hB0]
    exact pow_orderOf_eq_one _

end LTE

/-- If `orderOf x` equals the number of units, every unit is a power `x^t` with
`t < orderOf x`. -/
lemma exists_pow_eq_of_orderOf_eq_card {n : ℕ} [NeZero n] (x : ZMod n)
    (hx : orderOf x = Nat.card (ZMod n)ˣ) (u : ZMod n) (hu : IsUnit u) :
    ∃ t < orderOf x, x ^ t = u := by
  have hpos : 0 < orderOf x := by rw [hx, Nat.card_eq_fintype_card]; exact Fintype.card_pos
  have hxu : IsUnit x := IsUnit.of_pow_eq_one (pow_orderOf_eq_one x) hpos.ne'
  set X := hxu.unit with hX
  have hord : orderOf X = orderOf x := by rw [← orderOf_units, IsUnit.unit_spec]
  have himg : (Finset.range (orderOf X)).image (fun t => X ^ t) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn, Finset.card_range, hord, hx, Nat.card_eq_fintype_card]
    intro a ha b hb hab
    exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab
  have hmem : hu.unit ∈ (Finset.range (orderOf X)).image (fun t => X ^ t) := by
    rw [himg]; exact Finset.mem_univ _
  obtain ⟨t, ht, hteq⟩ := Finset.mem_image.mp hmem
  refine ⟨t, by rw [← hord]; simpa using ht, ?_⟩
  have := congrArg (fun y : (ZMod n)ˣ => (y : ZMod n)) hteq
  simpa [hX] using this

/-- Units of `ZMod (p^k)`: there are `(p - 1) p^(k-1)` of them. -/
lemma card_units_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (ZMod (p ^ k))ˣ = (p - 1) * p ^ (k - 1) := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by omega),
    mul_comm]

/-- In `ZMod (p^2)`, a nilpotent element squares to zero. -/
lemma sq_eq_zero_of_pow_eq_zero {p : ℕ} (hp : p.Prime) {y : ZMod (p ^ 2)} {n : ℕ}
    (hy : y ^ n = 0) : y * y = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hv : ((y.val : ℕ) : ZMod (p ^ 2)) = y := ZMod.natCast_zmod_val y
  have hdvd : p ∣ y.val := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      rw [pow_zero] at hy
      have h1 : (1 : ZMod (p ^ 2)) ≠ 0 := by
        have : Fact (1 < p ^ 2) := ⟨Nat.one_lt_pow (by norm_num) hp.one_lt⟩
        exact one_ne_zero
      exact h1 hy
    · rw [← hv, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff] at hy
      exact hp.dvd_of_dvd_pow (dvd_trans (dvd_pow_self p (by norm_num)) hy)
  obtain ⟨c, hc⟩ := hdvd
  rw [← hv, hc, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  exact ⟨c * c, by ring⟩

section Multiplier

variable {π : GaussianInt} {p : ℕ}

namespace DigitPrime

variable (hπ : DigitPrime π p)
include hπ

/-- The multiplier `ψₙ(ρ) / ψₙ(ρ̄)` of `ρ/ρ̄` on `ℤ[i]/πⁿ`. -/
def mult (ρ : GaussianInt) (n : ℕ) : ZMod (p ^ n) := hπ.ψ n ρ * (hπ.ψ n (star ρ))⁻¹

lemma mult_mul {ρ : GaussianInt} {n : ℕ} (hn : 0 < n) (hρ : ¬ π ∣ star ρ) :
    hπ.mult ρ n * hπ.ψ n (star ρ) = hπ.ψ n ρ := by
  unfold mult
  rw [mul_assoc, mul_comm _ (hπ.ψ n (star ρ)),
    ZMod.mul_inv_of_unit _ ((hπ.isUnit_ψ_iff hn _).mpr hρ), mul_one]

lemma isUnit_mult {ρ : GaussianInt} {n : ℕ} (hn : 0 < n) (hρ : ¬ π ∣ ρ) (hρ' : ¬ π ∣ star ρ) :
    IsUnit (hπ.mult ρ n) := by
  have h := hπ.mult_mul hn hρ'
  have hu : IsUnit (hπ.ψ n ρ) := (hπ.isUnit_ψ_iff hn _).mpr hρ
  rw [← h] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- The composite `ℤ[i] → ZMod (pⁿ) → ZMod (p²)` is determined by the image `x` of `i`. -/
lemma cast_ψ {n : ℕ} (hn : 2 ≤ n) (z : GaussianInt) :
    ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) (hπ.ψ n z) =
      (z.re : ZMod (p ^ 2)) + z.im * ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2))
        (rootψ π p n) := by
  rw [ψ_apply, map_add, map_mul, map_intCast, map_intCast]

lemma cast_root_mul_self {n : ℕ} (hn : 2 ≤ n) :
    ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) (rootψ π p n) *
      ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) (rootψ π p n) = -1 := by
  rw [← map_mul, hπ.rootψ_mul_self, map_neg, map_one]

lemma cast_ψ_π_sq {n : ℕ} (hn : 2 ≤ n) :
    ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) (hπ.ψ n π) *
      ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) (hπ.ψ n π) = 0 := by
  apply sq_eq_zero_of_pow_eq_zero hπ.prime (n := n)
  rw [← map_pow, ← map_pow, hπ.ψ_pow_self, map_zero]

end DigitPrime

end Multiplier

end Green41

/- ## Section: `Instances` -/

/-
# The two digit primes and their multipliers

Case 1 of the blueprint uses the digit prime `P = 1 + 2i` (norm 5) with multiplier `θ₁₃`;
case 2 uses `Q = 2 + 3i` (norm 13) with multiplier `θ₅`. The residues of the multipliers
modulo `p²` are forced by `rₙ² = -1` and `ψₙ(π)` nilpotent, and determine their orders.

| multiplier | mod `p²` | order mod `pᵏ` |
|---|---|---|
| `θ₁₃` on `ℤ[i]/Pⁿ` | 8 | `4·5^(k-1)` |
| `θ₁₃⁻¹` on `ℤ[i]/Pⁿ` | 22 | `4·5^(k-1)` |
| `θ₅` on `ℤ[i]/Qⁿ` | 11 | `12·13^(k-1)` |
| `θ₅⁻¹` on `ℤ[i]/Qⁿ` | 123 | `12·13^(k-1)` |
-/

namespace Green41

lemma star_gP : star gP = gPb := rfl
lemma star_gQ : star gQ = gQb := rfl
lemma star_gPb : star gPb = gP := rfl
lemma star_gQb : star gQb = gQ := rfl

lemma prime_gPb : Prime gPb :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [norm_gPb]; norm_num))

lemma prime_gQb : Prime gQb :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [norm_gQb]; norm_num))

lemma gQ_not_dvd_gQb' : ¬ gQ ∣ gQb := gQ_not_dvd_gQb

/-- `P = 1 + 2i` is a digit prime of norm 5. -/
lemma digitPrime_P : DigitPrime gP 5 where
  prime := by norm_num
  norm := by rw [norm_gP]; rfl
  not_dvd_star := by rw [star_gP]; exact gP_not_dvd_gPb

/-- `Q = 2 + 3i` is a digit prime of norm 13. -/
lemma digitPrime_Q : DigitPrime gQ 13 where
  prime := by norm_num
  norm := by rw [norm_gQ]; rfl
  not_dvd_star := by rw [star_gQ]; exact gQ_not_dvd_gQb

/-- The residue of a `ZMod (pⁿ)` element modulo `p²`, through its value. -/
lemma val_cast_eq_castHom {p n : ℕ} [NeZero (p ^ n)] (hn : 2 ≤ n) (a : ZMod (p ^ n)) :
    ((a.val : ℕ) : ZMod (p ^ 2)) = ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 2)) a := by
  rw [ZMod.natCast_val, ZMod.castHom_apply]

section NumericFacts

lemma zmod25_fact (x b : ZMod 25) (hx : x * x = -1) (hπ : (1 + 2 * x) * (1 + 2 * x) = 0)
    (hb : b * (2 + (-3) * x) = 2 + 3 * x) : b = 8 := by
  revert x b; decide

lemma zmod25_fact' (x b : ZMod 25) (hx : x * x = -1) (hπ : (1 + 2 * x) * (1 + 2 * x) = 0)
    (hb : b * (2 + 3 * x) = 2 + (-3) * x) : b = 22 := by
  revert x b; decide

set_option maxRecDepth 100000 in
lemma zmod169_root (x : ZMod 169) (hx : x * x = -1) (hπ : (2 + 3 * x) * (2 + 3 * x) = 0) :
    x = 99 := by
  revert x; decide

set_option maxRecDepth 100000 in
lemma zmod169_fact (b : ZMod 169) (hb : b * (1 + (-2) * 99) = 1 + 2 * 99) : b = 11 := by
  revert b; decide

set_option maxRecDepth 100000 in
lemma zmod169_fact' (b : ZMod 169) (hb : b * (1 + 2 * 99) = 1 + (-2) * 99) : b = 123 := by
  revert b; decide

end NumericFacts

/-- `θ₁₃ ≡ 8 (mod 25)` on `ℤ[i]/Pⁿ`. -/
lemma mult_P_Q_mod25 {n : ℕ} (hn : 2 ≤ n) :
    (((digitPrime_P.mult gQ n).val : ℕ) : ZMod (5 ^ 2)) = 8 := by
  have : NeZero (5 ^ n) := ⟨by positivity⟩
  have h := congrArg (ZMod.castHom (pow_dvd_pow 5 hn) (ZMod (5 ^ 2)))
    (digitPrime_P.mult_mul (by omega) (ρ := gQ) (by rw [star_gQ]; exact gP_not_dvd_gQb))
  rw [map_mul, digitPrime_P.cast_ψ hn, digitPrime_P.cast_ψ hn] at h
  have hx := digitPrime_P.cast_root_mul_self hn
  have hπ := digitPrime_P.cast_ψ_π_sq hn
  rw [digitPrime_P.cast_ψ hn] at hπ
  rw [val_cast_eq_castHom hn]
  exact zmod25_fact _ _ hx (by simpa [gP] using hπ) (by simpa [gQ, star_gQ, gQb] using h)

/-- `θ₁₃⁻¹ ≡ 22 (mod 25)` on `ℤ[i]/Pⁿ`. -/
lemma mult_P_Qb_mod25 {n : ℕ} (hn : 2 ≤ n) :
    (((digitPrime_P.mult (star gQ) n).val : ℕ) : ZMod (5 ^ 2)) = 22 := by
  have : NeZero (5 ^ n) := ⟨by positivity⟩
  have h := congrArg (ZMod.castHom (pow_dvd_pow 5 hn) (ZMod (5 ^ 2)))
    (digitPrime_P.mult_mul (by omega) (ρ := star gQ) (by rw [star_star]; exact gP_not_dvd_gQ))
  rw [map_mul, digitPrime_P.cast_ψ hn, digitPrime_P.cast_ψ hn] at h
  have hx := digitPrime_P.cast_root_mul_self hn
  have hπ := digitPrime_P.cast_ψ_π_sq hn
  rw [digitPrime_P.cast_ψ hn] at hπ
  rw [val_cast_eq_castHom hn]
  exact zmod25_fact' _ _ hx (by simpa [gP] using hπ) (by simpa [gQ, star_gQ, gQb] using h)

/-- `θ₅ ≡ 11 (mod 169)` on `ℤ[i]/Qⁿ`. -/
lemma mult_Q_P_mod169 {n : ℕ} (hn : 2 ≤ n) :
    (((digitPrime_Q.mult gP n).val : ℕ) : ZMod (13 ^ 2)) = 11 := by
  have : NeZero (13 ^ n) := ⟨by positivity⟩
  have h := congrArg (ZMod.castHom (pow_dvd_pow 13 hn) (ZMod (13 ^ 2)))
    (digitPrime_Q.mult_mul (by omega) (ρ := gP) (by rw [star_gP]; exact gQ_not_dvd_gPb))
  rw [map_mul, digitPrime_Q.cast_ψ hn, digitPrime_Q.cast_ψ hn] at h
  have hx := digitPrime_Q.cast_root_mul_self hn
  have hπ := digitPrime_Q.cast_ψ_π_sq hn
  rw [digitPrime_Q.cast_ψ hn] at hπ
  have hr := zmod169_root _ hx (by simpa [gQ] using hπ)
  rw [hr] at h
  rw [val_cast_eq_castHom hn]
  exact zmod169_fact _ (by simpa [gP, star_gP, gPb] using h)

/-- `θ₅⁻¹ ≡ 123 (mod 169)` on `ℤ[i]/Qⁿ`. -/
lemma mult_Q_Pb_mod169 {n : ℕ} (hn : 2 ≤ n) :
    (((digitPrime_Q.mult (star gP) n).val : ℕ) : ZMod (13 ^ 2)) = 123 := by
  have : NeZero (13 ^ n) := ⟨by positivity⟩
  have h := congrArg (ZMod.castHom (pow_dvd_pow 13 hn) (ZMod (13 ^ 2)))
    (digitPrime_Q.mult_mul (by omega) (ρ := star gP) (by rw [star_star]; exact gQ_not_dvd_gP))
  rw [map_mul, digitPrime_Q.cast_ψ hn, digitPrime_Q.cast_ψ hn] at h
  have hx := digitPrime_Q.cast_root_mul_self hn
  have hπ := digitPrime_Q.cast_ψ_π_sq hn
  rw [digitPrime_Q.cast_ψ hn] at hπ
  have hr := zmod169_root _ hx (by simpa [gQ] using hπ)
  rw [hr] at h
  rw [val_cast_eq_castHom hn]
  exact zmod169_fact' _ (by simpa [gP, star_gP, gPb] using h)

/-- From the residue modulo `p²` to the order modulo `pᵏ`. -/
lemma orderOf_of_mod_sq {p : ℕ} (hpr : p.Prime) (hodd : Odd p) {B r : ℕ}
    (hBr : (B : ZMod (p ^ 2)) = (r : ZMod (p ^ 2))) (hr : 2 ≤ r) (hrp : r < p ^ 2)
    (h1 : orderOf ((r % p : ℕ) : ZMod p) = p - 1) (h2 : (r : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    orderOf (B : ZMod (p ^ k)) = (p - 1) * p ^ (k - 1) := by
  have hmod : B % p ^ 2 = r := by
    rw [ZMod.natCast_eq_natCast_iff'] at hBr
    rw [hBr, Nat.mod_eq_of_lt hrp]
  have hB : 2 ≤ B := by
    have := Nat.mod_le B (p ^ 2); omega
  apply orderOf_natCast_prime_pow hpr hodd hB _ (by rwa [hBr]) hk
  have : (B : ZMod p) = ((r % p : ℕ) : ZMod p) := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod]
    rw [← hmod, Nat.mod_mod_of_dvd _ (dvd_pow_self p (by norm_num))]
  rw [this, h1]

lemma orderOf_three_zmod5 : orderOf ((8 % 5 : ℕ) : ZMod 5) = 5 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

lemma orderOf_two_zmod5 : orderOf ((22 % 5 : ℕ) : ZMod 5) = 5 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

lemma orderOf_eleven_zmod13 : orderOf ((11 % 13 : ℕ) : ZMod 13) = 13 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

lemma orderOf_six_zmod13 : orderOf ((123 % 13 : ℕ) : ZMod 13) = 13 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- The order of `θ₁₃` on `ℤ[i]/Pⁿ`, read modulo `5ᵏ`. -/
lemma orderOf_mult_P_Q {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    orderOf (((digitPrime_P.mult gQ n).val : ℕ) : ZMod (5 ^ k)) = 4 * 5 ^ (k - 1) :=
  orderOf_of_mod_sq (r := 8) (by norm_num) (by decide) (by rw [mult_P_Q_mod25 hn]; rfl)
    (by norm_num) (by norm_num) orderOf_three_zmod5 (by decide) hk

/-- The order of `θ₁₃⁻¹` on `ℤ[i]/Pⁿ`, read modulo `5ᵏ`. -/
lemma orderOf_mult_P_Qb {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    orderOf (((digitPrime_P.mult (star gQ) n).val : ℕ) : ZMod (5 ^ k)) = 4 * 5 ^ (k - 1) :=
  orderOf_of_mod_sq (r := 22) (by norm_num) (by decide) (by rw [mult_P_Qb_mod25 hn]; rfl)
    (by norm_num) (by norm_num) orderOf_two_zmod5 (by decide) hk

/-- The order of `θ₅` on `ℤ[i]/Qⁿ`, read modulo `13ᵏ`. -/
lemma orderOf_mult_Q_P {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    orderOf (((digitPrime_Q.mult gP n).val : ℕ) : ZMod (13 ^ k)) = 12 * 13 ^ (k - 1) :=
  orderOf_of_mod_sq (r := 11) (by norm_num) (by decide) (by rw [mult_Q_P_mod169 hn]; rfl)
    (by norm_num) (by norm_num) orderOf_eleven_zmod13 (by decide) hk

/-- The order of `θ₅⁻¹` on `ℤ[i]/Qⁿ`, read modulo `13ᵏ`. -/
lemma orderOf_mult_Q_Pb {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    orderOf (((digitPrime_Q.mult (star gP) n).val : ℕ) : ZMod (13 ^ k)) = 12 * 13 ^ (k - 1) :=
  orderOf_of_mod_sq (r := 123) (by norm_num) (by decide) (by rw [mult_Q_Pb_mod169 hn]; rfl)
    (by norm_num) (by norm_num) orderOf_six_zmod13 (by decide) hk

end Green41

/- ## Section: `Labels` -/

/-
# Cells, labels and the stripe value of a label (blueprint §3, §5)

For the cell generator `g = π̄^α ρ̄^β / πⁿ`, the label of `x ∈ ℂ` is `ψₙ(⌊x/g⌋)`.
* (L1) `x` lies within `√2 |g|` of `g ⌊x/g⌋`.
* (L3) `⌊(x - x')/g⌋ = ⌊x/g⌋ - ⌊x'/g⌋ - d` with `d ∈ {0, 1, i, 1+i}`.
  Hence, if the labels of differences of a finite set `Z` cover `ZMod (pⁿ)`, then
  `pⁿ ≤ 4 |labels(Z)|²`.
* (L4) The stripe value `Re(σʲ τʷ g m)` is `val(Xⱼ bʷ ψₙ(m)) / p^(n-j)` modulo `1`.
-/

namespace Green41

open Complex ComplexConjugate

/- ## Gaussian floor -/

/-- `⌊z⌋ = ⌊Re z⌋ + ⌊Im z⌋ i`. -/
noncomputable def gaussFloor (z : ℂ) : GaussianInt := ⟨⌊z.re⌋, ⌊z.im⌋⟩

lemma gaussFloor_re (z : ℂ) : ((gaussFloor z : ℂ)).re = (⌊z.re⌋ : ℝ) := by
  simp [gaussFloor, GaussianInt.toComplex_def]

lemma gaussFloor_im (z : ℂ) : ((gaussFloor z : ℂ)).im = (⌊z.im⌋ : ℝ) := by
  simp [gaussFloor, GaussianInt.toComplex_def]

/-- (L1) `‖z - ⌊z⌋‖ < √2`. -/
lemma norm_sub_gaussFloor_lt (z : ℂ) : ‖z - gaussFloor z‖ < Real.sqrt 2 := by
  have h1 := Int.fract_nonneg z.re
  have h2 := Int.fract_lt_one z.re
  have h3 := Int.fract_nonneg z.im
  have h4 := Int.fract_lt_one z.im
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [sub_re, sub_im, gaussFloor_re, gaussFloor_im]
  have e1 : z.re - ⌊z.re⌋ = Int.fract z.re := rfl
  have e2 : z.im - ⌊z.im⌋ = Int.fract z.im := rfl
  rw [e1, e2]
  apply Real.sqrt_lt_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  nlinarith

lemma floor_sub_cases (a b : ℝ) : ⌊a - b⌋ = ⌊a⌋ - ⌊b⌋ ∨ ⌊a - b⌋ = ⌊a⌋ - ⌊b⌋ - 1 := by
  have h : a - b = ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) + (Int.fract a - Int.fract b) := by
    rw [Int.fract, Int.fract]; push_cast; ring
  have ha0 := Int.fract_nonneg a
  have ha1 := Int.fract_lt_one a
  have hb0 := Int.fract_nonneg b
  have hb1 := Int.fract_lt_one b
  rw [h, Int.floor_intCast_add]
  rcases le_or_gt 0 (Int.fract a - Int.fract b) with h0 | h0
  · left
    have : ⌊Int.fract a - Int.fract b⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, by linarith⟩
    rw [this, add_zero]
  · right
    have : ⌊Int.fract a - Int.fract b⌋ = -1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; ring

/-- The four corrections `{0, 1, i, 1 + i}`. -/
def corrections : Finset GaussianInt := {0, 1, ⟨0, 1⟩, ⟨1, 1⟩}

lemma card_corrections : corrections.card = 4 := by decide

/-- (L3) `⌊u - v⌋ = ⌊u⌋ - ⌊v⌋ - d` with `d ∈ {0, 1, i, 1 + i}`. -/
lemma gaussFloor_sub (u v : ℂ) :
    ∃ d ∈ corrections, gaussFloor (u - v) = gaussFloor u - gaussFloor v - d := by
  have hre := floor_sub_cases u.re v.re
  have him := floor_sub_cases u.im v.im
  have hr : (u - v).re = u.re - v.re := sub_re u v
  have hi : (u - v).im = u.im - v.im := sub_im u v
  rcases hre with hre | hre <;> rcases him with him | him
  · refine ⟨0, by simp [corrections], ?_⟩
    ext <;> simp [gaussFloor, hr, hi, hre, him]
  · refine ⟨⟨0, 1⟩, by simp [corrections], ?_⟩
    ext <;> simp [gaussFloor, hr, hi, hre, him]
  · refine ⟨1, by simp [corrections], ?_⟩
    ext <;> simp [gaussFloor, hr, hi, hre, him]
  · refine ⟨⟨1, 1⟩, by simp [corrections], ?_⟩
    ext <;> simp [gaussFloor, hr, hi, hre, him]

/- ## Labels and counting -/

/-- The cell generator `g = π̄^α ρ̄^β / πⁿ`. -/
noncomputable def cellGen (π ρ : GaussianInt) (n α β : ℕ) : ℂ :=
  ((star π : GaussianInt) : ℂ) ^ α * ((star ρ : GaussianInt) : ℂ) ^ β / (π : ℂ) ^ n

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)

/-- The label `ψₙ(⌊x/g⌋)` of `x ∈ ℂ`. -/
noncomputable def label (ρ : GaussianInt) (n α β : ℕ) (x : ℂ) : ZMod (p ^ n) :=
  hπ.ψ n (gaussFloor (x / cellGen π ρ n α β))

include hπ in
/-- (§5) If every residue is the label of a difference of two points of `Z`, then
`pⁿ ≤ 4 · |labels(Z)|²`. -/
lemma pow_le_four_mul_card_sq (ρ : GaussianInt) (n α β : ℕ) (Z : Finset ℂ)
    (hall : ∀ l : ZMod (p ^ n), ∃ x ∈ Z, ∃ x' ∈ Z, hπ.label ρ n α β (x - x') = l) :
    p ^ n ≤ 4 * ((Z.image (hπ.label ρ n α β)).card) ^ 2 := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  set Y := Z.image (hπ.label ρ n α β)
  set S := (Y ×ˢ Y) ×ˢ corrections
  let f : (ZMod (p ^ n) × ZMod (p ^ n)) × GaussianInt → ZMod (p ^ n) :=
    fun t => t.1.1 - t.1.2 - hπ.ψ n t.2
  have hsub : (Finset.univ : Finset (ZMod (p ^ n))) ⊆ S.image f := by
    intro l _
    obtain ⟨x, hx, x', hx', hl⟩ := hall l
    obtain ⟨d, hd, hfl⟩ := gaussFloor_sub (x / cellGen π ρ n α β) (x' / cellGen π ρ n α β)
    rw [Finset.mem_image]
    refine ⟨((hπ.label ρ n α β x, hπ.label ρ n α β x'), d), ?_, ?_⟩
    · simp only [S, Y, Finset.mem_product, Finset.mem_image]
      exact ⟨⟨⟨x, hx, rfl⟩, ⟨x', hx', rfl⟩⟩, hd⟩
    · rw [← hl]
      simp only [f, label, sub_div, hfl, map_sub]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at h1
  calc p ^ n ≤ (S.image f).card := h1
    _ ≤ S.card := Finset.card_image_le
    _ = 4 * Y.card ^ 2 := by
      simp only [S, Finset.card_product, card_corrections]; ring

end DigitPrime

/- ## The stripe value of a label (L4) -/

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

lemma toComplex_ne_zero : (π : ℂ) ≠ 0 := by
  rw [Ne, GaussianInt.toComplex_eq_zero]; exact hπ.prime_π.ne_zero

lemma toComplex_star_ne_zero : ((star π : GaussianInt) : ℂ) ≠ 0 := by
  rw [GaussianInt.toComplex_star]; exact (map_ne_zero _).mpr hπ.toComplex_ne_zero

lemma pow_mul_conj_pow (n : ℕ) : (π : ℂ) ^ n * ((star π : GaussianInt) : ℂ) ^ n = (p : ℂ) ^ n := by
  have h := congrArg (fun z : GaussianInt => (z : ℂ)) (hπ.natCast_pow_eq n)
  simp only [map_natCast, map_mul, map_pow, star_pow, Nat.cast_pow] at h
  exact h.symm

/-- `Re(z / πⁿ) ≡ val(Re(πⁿ) ψₙ(z)) / pⁿ (mod 1)`. -/
lemma re_div_pow (n : ℕ) (z : GaussianInt) : ∃ k : ℤ,
    ((z : ℂ) / (π : ℂ) ^ n).re =
      ((((((π ^ n).re : ℤ) : ZMod (p ^ n)) * hπ.ψ n z).val : ℕ) : ℝ) / (p : ℝ) ^ n + k := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  have hπ0 := hπ.toComplex_ne_zero
  have hpc : ((p : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hπ.prime.ne_zero)
  have hπb0 := hπ.toComplex_star_ne_zero
  have hdiv : (z : ℂ) / (π : ℂ) ^ n =
      ((z * star (π ^ n) : GaussianInt) : ℂ) / (((p : ℝ) ^ n : ℝ) : ℂ) := by
    rw [map_mul, star_pow, map_pow]
    push_cast
    rw [← hπ.pow_mul_conj_pow n]
    field_simp
  set A := (z * star (π ^ n)).re with hA
  set X := (((π ^ n).re : ℤ) : ZMod (p ^ n)) * hπ.ψ n z with hX
  have hsf : ((A : ℤ) : ZMod (p ^ n)) = X := hπ.stripe_formula n z
  have hv : (((X.val : ℕ) : ℤ) : ZMod (p ^ n)) = X := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcong : ((p ^ n : ℕ) : ℤ) ∣ A - (X.val : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]; rw [hv, hsf]
  obtain ⟨k, hk⟩ := hcong
  refine ⟨k, ?_⟩
  rw [hdiv, Complex.div_ofReal_re, ← GaussianInt.intCast_re, ← hA]
  have hA' : (A : ℝ) = (X.val : ℝ) + ((p : ℝ) ^ n) * k := by
    have : A = (X.val : ℤ) + ((p ^ n : ℕ) : ℤ) * k := by linarith
    rw [this]; push_cast; ring
  rw [hA']
  have hpr : ((p : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hπ.prime.ne_zero)
  field_simp

omit hπ in
/-- `val(pʲ Y) / pⁿ ≡ val(Y) / p^(n-j) (mod 1)`. -/
lemma val_pow_mul_div {p n j : ℕ} (hp : 0 < p) (hj : j ≤ n) (Y : ZMod (p ^ n)) : ∃ k : ℤ,
    ((((p : ZMod (p ^ n)) ^ j * Y).val : ℕ) : ℝ) / (p : ℝ) ^ n =
      ((Y.val : ℕ) : ℝ) / (p : ℝ) ^ (n - j) + k := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne'⟩
  have hcast : (p : ZMod (p ^ n)) ^ j * Y = ((p ^ j * Y.val : ℕ) : ZMod (p ^ n)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [hcast, ZMod.val_natCast]
  obtain ⟨q, hq⟩ : ∃ q, p ^ j * Y.val = p ^ j * Y.val % p ^ n + p ^ n * q :=
    ⟨_, (Nat.mod_add_div _ _).symm⟩
  refine ⟨-(q : ℤ), ?_⟩
  have hR : ((p ^ j * Y.val % p ^ n : ℕ) : ℝ) = (p : ℝ) ^ j * Y.val - (p : ℝ) ^ n * q := by
    have h1 := congrArg (fun x : ℕ => (x : ℝ)) hq
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at h1
    linarith
  rw [hR]
  have hpn : (p : ℝ) ^ n = (p : ℝ) ^ j * (p : ℝ) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  have hpj : (p : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
  have hpnj : (p : ℝ) ^ (n - j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
  rw [hpn]
  field_simp
  push_cast
  ring

/-- The unit factor `Xⱼ = Re(πⁿ) ψ(π̄)^(-j) ψ(π̄)^(α-j) ψ(ρ̄)^β` of (L4). -/
noncomputable def Xfac (ρ : GaussianInt) (n α β j : ℕ) : ZMod (p ^ n) :=
  (((π ^ n).re : ℤ) : ZMod (p ^ n)) * ((hπ.ψ n (star π))⁻¹) ^ j * hπ.ψ n (star π) ^ (α - j) *
    hπ.ψ n (star ρ) ^ β

/-- (L4) `Re(σʲ τʷ g m) ≡ val(Xⱼ bʷ ψₙ(m)) / p^(n-j) (mod 1)`. -/
lemma re_label_formula {ρ : GaussianInt} (hρ' : ¬ π ∣ star ρ) (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0)
    {n α β j w : ℕ} (hn : 0 < n) (hj : j ≤ α) (hw : w ≤ β) (hjn : j ≤ n) (m : GaussianInt) :
    ∃ k : ℤ, (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ j * ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ w *
        (cellGen π ρ n α β * m)).re =
      (((hπ.Xfac ρ n α β j * hπ.mult ρ n ^ w * hπ.ψ n m).val : ℕ) : ℝ) / (p : ℝ) ^ (n - j) +
        k := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  set z : GaussianInt := π ^ j * star π ^ (α - j) * ρ ^ w * star ρ ^ (β - w) * m with hz
  have hπ0 := hπ.toComplex_ne_zero
  have hπb0 := hπ.toComplex_star_ne_zero
  have hcx : ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ j * ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ w *
      (cellGen π ρ n α β * m) = (z : ℂ) / (π : ℂ) ^ n := by
    simp only [hz, cellGen, map_mul, map_pow, div_pow]
    obtain ⟨a, rfl⟩ : ∃ a, α = a + j := ⟨α - j, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, β = b + w := ⟨β - w, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
    field_simp
    ring
  obtain ⟨k₁, hk₁⟩ := hπ.re_div_pow n z
  have hunit : hπ.ψ n (star π) * (hπ.ψ n (star π))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ ((hπ.isUnit_ψ_iff hn _).mpr hπ.not_dvd_star)
  have hψπ : hπ.ψ n π = (p : ZMod (p ^ n)) * (hπ.ψ n (star π))⁻¹ := by
    rw [← hπ.ψ_mul_star n, mul_assoc, hunit, mul_one]
  have hψρ : hπ.ψ n ρ = hπ.mult ρ n * hπ.ψ n (star ρ) := (hπ.mult_mul hn hρ').symm
  have hX : (((π ^ n).re : ℤ) : ZMod (p ^ n)) * hπ.ψ n z =
      (p : ZMod (p ^ n)) ^ j * (hπ.Xfac ρ n α β j * hπ.mult ρ n ^ w * hπ.ψ n m) := by
    simp only [hz, map_mul, map_pow, hψπ, hψρ, Xfac]
    obtain ⟨b, rfl⟩ : ∃ b, β = b + w := ⟨β - w, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  obtain ⟨k₂, hk₂⟩ := val_pow_mul_div hπ.prime.pos hjn
    (hπ.Xfac ρ n α β j * hπ.mult ρ n ^ w * hπ.ψ n m)
  refine ⟨k₁ + k₂, ?_⟩
  rw [hcx, hk₁, hX, hk₂]
  push_cast; ring

end DigitPrime

end Green41

/- ## Section: `StepA` -/

/-
# Step A: the orbit meets every label (blueprint §4)

This replaces Kravitz–Leng Theorem 5.1. Write `q = π̄^v ρ̄^E q₂` with `π̄ ∤ q₂`, and let
`j = v + D` with `D = n - α + 4`. For `t < (p - 1) p^(n+3)`,
`σʲ τᵗ q = ρ̄^β W_t / π̄^D` with `W_t = πʲ ρᵗ ρ̄^(E-β-t) q₂`.
The residues `W_t mod π̄^(n+4)` run over all units, so every cell `g(m₀ + [0,1)²)` modulo
`M = π̄^α ρ̄^β ℤ[i]` receives a point `σʲ τᵗ (q + e')`, provided `|e'| < 0.42 |g|`.
-/

namespace Green41

open Complex ComplexConjugate

/- ## Helpers on floors, rounding and norms -/

lemma gaussFloor_add_intCast (m : GaussianInt) (z : ℂ) :
    gaussFloor ((m : ℂ) + z) = m + gaussFloor z := by
  have hre : ((m : ℂ) + z).re = ((m.re : ℤ) : ℝ) + z.re := by
    rw [add_re, ← GaussianInt.intCast_re]
  have him : ((m : ℂ) + z).im = ((m.im : ℤ) : ℝ) + z.im := by
    rw [add_im, ← GaussianInt.intCast_im]
  ext
  · simp only [gaussFloor, Zsqrtd.re_add]; rw [hre, Int.floor_intCast_add]
  · simp only [gaussFloor, Zsqrtd.im_add]; rw [him, Int.floor_intCast_add]

lemma gaussFloor_half_add {u : ℂ} (hu : ‖u‖ < 1 / 2) : gaussFloor ((1 + I) / 2 + u) = 0 := by
  have h1 : |u.re| < 1 / 2 := lt_of_le_of_lt (Complex.abs_re_le_norm u) hu
  have h2 : |u.im| < 1 / 2 := lt_of_le_of_lt (Complex.abs_im_le_norm u) hu
  rw [abs_lt] at h1 h2
  ext
  · simp only [gaussFloor, Zsqrtd.re_zero]
    rw [Int.floor_eq_zero_iff]
    simp only [add_re, div_re, one_re, I_re, normSq_ofNat, Set.mem_Ico]
    norm_num; constructor <;> linarith
  · simp only [gaussFloor, Zsqrtd.im_zero]
    rw [Int.floor_eq_zero_iff]
    simp only [add_im, div_im, one_im, I_im, normSq_ofNat, Set.mem_Ico]
    norm_num; constructor <;> linarith

lemma norm_sub_gRound_lt_one (x : ℂ) : ‖x - gRound x‖ < 1 := by
  have h1 := frac_mem x.re
  have h2 := frac_mem x.im
  rw [Complex.norm_def, Complex.normSq_apply]
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  simp only [sub_re, sub_im, gRound_re, gRound_im]
  apply Real.sqrt_lt_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  nlinarith

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

/-- A Gaussian integer prime to `π̄` within distance `2` of any point. -/
lemma exists_coprime_near (c : ℂ) : ∃ W : GaussianInt, ¬ star π ∣ W ∧ ‖c - W‖ < 2 := by
  have h1 := norm_sub_gRound_lt_one c
  by_cases hdvd : star π ∣ gRound c
  · refine ⟨gRound c + 1, ?_, ?_⟩
    · intro h
      have h1' : star π ∣ (1 : GaussianInt) := (dvd_add_right hdvd).mp h
      have hu : IsUnit (star π) := isUnit_of_dvd_one h1'
      have : IsUnit π := by simpa using hu.star
      exact hπ.prime_π.not_isUnit this
    · calc ‖c - ((gRound c + 1 : GaussianInt) : ℂ)‖ = ‖(c - gRound c) - 1‖ := by
            rw [map_add, map_one]; ring_nf
        _ ≤ ‖c - gRound c‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ < 2 := by rw [norm_one]; linarith
  · exact ⟨gRound c, hdvd, by linarith⟩

lemma norm_toComplex_π : ‖(π : ℂ)‖ = Real.sqrt p := by
  rw [norm_toComplex, hπ.norm]; norm_cast

lemma norm_toComplex_star_π : ‖((star π : GaussianInt) : ℂ)‖ = Real.sqrt p := by
  rw [GaussianInt.toComplex_star, Complex.norm_conj, hπ.norm_toComplex_π]

lemma norm_sigma : ‖(π : ℂ) / ((star π : GaussianInt) : ℂ)‖ = 1 := by
  rw [norm_div, hπ.norm_toComplex_π, hπ.norm_toComplex_star_π,
    div_self (Real.sqrt_pos.mpr (by exact_mod_cast hπ.prime.pos)).ne']

/-- `‖π̄^D / ρ̄^β‖ · ‖g‖ = p²` when `D + α = n + 4`. -/
lemma norm_shift_mul_norm_cellGen {ρ : GaussianInt} (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0)
    {n α β D : ℕ} (hD : D + α = n + 4) :
    ‖((star π : GaussianInt) : ℂ) ^ D / ((star ρ : GaussianInt) : ℂ) ^ β‖ *
      ‖cellGen π ρ n α β‖ = (p : ℝ) ^ 2 := by
  have hsp : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hπ.prime.pos)).ne'
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (by positivity)
  have h1 : ‖((star π : GaussianInt) : ℂ) ^ D‖ = Real.sqrt p ^ D := by
    rw [_root_.norm_pow, hπ.norm_toComplex_star_π]
  have h2 : ‖((star π : GaussianInt) : ℂ) ^ α‖ = Real.sqrt p ^ α := by
    rw [_root_.norm_pow, hπ.norm_toComplex_star_π]
  have h3 : ‖(π : ℂ) ^ n‖ = Real.sqrt p ^ n := by rw [_root_.norm_pow, hπ.norm_toComplex_π]
  set X := ‖((star ρ : GaussianInt) : ℂ) ^ β‖ with hX
  have hX0 : X ≠ 0 := by rw [hX, _root_.norm_pow]; exact pow_ne_zero _ (norm_ne_zero_iff.mpr hρ0)
  have hsn : Real.sqrt p ^ n ≠ 0 := pow_ne_zero _ hsp
  unfold cellGen
  rw [norm_div, norm_div, norm_mul, h1, h2, h3, ← hX]
  calc Real.sqrt p ^ D / X * (Real.sqrt p ^ α * X / Real.sqrt p ^ n)
      = Real.sqrt p ^ (D + α) / Real.sqrt p ^ n := by rw [pow_add]; field_simp
    _ = (p : ℝ) ^ 2 := by
      rw [hD, pow_add, show Real.sqrt p ^ 4 = (Real.sqrt p ^ 2) ^ 2 by ring, hsq]
      field_simp

/-- A Gaussian integer is `≡` its value modulo `πⁿ`: the natural-number representative of a
residue has that residue. -/
lemma ψ_natCast_val (n : ℕ) (l : ZMod (p ^ n)) : hπ.ψ n ((l.val : ℕ) : GaussianInt) = l := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

lemma not_star_dvd_self : ¬ star π ∣ π := by
  rintro ⟨y, hy⟩
  apply hπ.not_dvd_star
  refine ⟨star y, ?_⟩
  have h := congrArg star hy
  rw [star_mul, star_star] at h
  rw [h, mul_comm]

lemma prime_star_π : Prime (star π) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_norm_prime (by rw [Zsqrtd.norm_conj, hπ.norm]; simpa using hπ.prime))

/-- **Step A.** Every residue `l` is the label of `σʲ τᵗ (q + e')` for some
`t < (p - 1) p^(n+3)`, where `q = π̄^v ρ̄^E q₂` and `j = v + (n - α + 4)`. -/
theorem stepA (hp5 : 5 ≤ p) {ρ : GaussianInt} (hρ1 : ¬ π ∣ ρ)
    (hρ4 : ¬ star π ∣ star ρ) (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0)
    {n α β : ℕ} (hα : α ≤ n)
    (hord : orderOf (hπ.mult (star ρ) (n + 4)) = (p - 1) * p ^ (n + 3))
    {v E : ℕ} (hE : (p - 1) * p ^ (n + 3) + β ≤ E) {q₂ : GaussianInt} (hq₂ : ¬ star π ∣ q₂)
    {e' : ℂ} (he' : ‖e'‖ < 21 / 50 * ‖cellGen π ρ n α β‖) (l : ZMod (p ^ n)) :
    ∃ t < (p - 1) * p ^ (n + 3),
      hπ.label ρ n α β (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ (v + (n - α + 4)) *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ t *
        ((((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) + e')) = l := by
  set D := n - α + 4 with hD
  set T := (p - 1) * p ^ (n + 3) with hT
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
  set W₀ : GaussianInt := π ^ (v + D) * star ρ ^ (E - β) * q₂ with hW₀
  have hW₀u : IsUnit (hπ.ψbar (n + 4) W₀) := by
    rw [hπ.isUnit_ψbar_iff hk0]
    intro hdvd
    have hprime : Prime (star π) := hπ.prime_star_π
    rcases hprime.dvd_or_dvd hdvd with h1 | h1
    · rcases hprime.dvd_or_dvd h1 with h2 | h2
      · exact hπ.not_star_dvd_self (hprime.dvd_of_dvd_pow h2)
      · exact hρ4 (hprime.dvd_of_dvd_pow h2)
    · exact hq₂ h1
  have hWu : IsUnit (hπ.ψbar (n + 4) W) := (hπ.isUnit_ψbar_iff hk0 W).mpr hW
  set c := hπ.ψbar (n + 4) W * (hπ.ψbar (n + 4) W₀)⁻¹ with hc
  have hinv : hπ.ψbar (n + 4) W₀ * (hπ.ψbar (n + 4) W₀)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hW₀u
  have hcu : IsUnit c := hWu.mul (IsUnit.of_mul_eq_one_right _ hinv)
  have : NeZero (p ^ (n + 4)) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  have hcard : orderOf (hπ.mult (star ρ) (n + 4)) = Nat.card (ZMod (p ^ (n + 4)))ˣ := by
    rw [hord, card_units_prime_pow hπ.prime hk0, hT, show n + 4 - 1 = n + 3 by omega]
  obtain ⟨t, htlt, hteq⟩ := exists_pow_eq_of_orderOf_eq_card _ hcard c hcu
  rw [hord] at htlt
  refine ⟨t, htlt, ?_⟩
  -- the orbit point `W_t`
  set Wt : GaussianInt := π ^ (v + D) * ρ ^ t * star ρ ^ (E - β - t) * q₂ with hWt
  have hρu : IsUnit (hπ.ψ (n + 4) ρ) := (hπ.isUnit_ψ_iff hk0 ρ).mpr hρ1
  have hρinv : hπ.ψ (n + 4) ρ * (hπ.ψ (n + 4) ρ)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hρu
  have hψWt : hπ.ψbar (n + 4) Wt = hπ.ψbar (n + 4) W₀ * hπ.mult (star ρ) (n + 4) ^ t := by
    obtain ⟨e, he⟩ : ∃ e, E - β = e + t := ⟨E - β - t, by omega⟩
    have he2 : E - β - t = e := by omega
    rw [hWt, hW₀, he2, he]
    simp only [ψbar_apply, mult, star_star, map_mul, map_pow]
    rw [pow_add (hπ.ψ (n + 4) ρ) e t, mul_pow (hπ.ψ (n + 4) (star ρ))]
    have hone : hπ.ψ (n + 4) ρ ^ t * ((hπ.ψ (n + 4) ρ)⁻¹) ^ t = 1 := by
      rw [← mul_pow, hρinv, one_pow]
    linear_combination (-(hπ.ψ (n + 4) (star π) ^ (v + D) * hπ.ψ (n + 4) ρ ^ e *
      hπ.ψ (n + 4) (star q₂) * hπ.ψ (n + 4) (star ρ) ^ t)) * hone
  have hdiff : star π ^ (n + 4) ∣ Wt - W := by
    rw [← hπ.ψbar_eq_zero_iff, map_sub, hψWt, hteq, hc]
    rw [mul_comm (hπ.ψbar (n + 4) W), ← mul_assoc, hinv, one_mul, sub_self]
  obtain ⟨Δ, hΔ⟩ := hdiff
  -- complex bookkeeping
  set σt : ℂ := ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ (v + D) *
    ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ t with hσt
  have hcx : σt * (((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) = (Wt : ℂ) / h := by
    have hEsplit : ((star ρ : GaussianInt) : ℂ) ^ E = ((star ρ : GaussianInt) : ℂ) ^ (E - β - t) *
        ((star ρ : GaussianInt) : ℂ) ^ β * ((star ρ : GaussianInt) : ℂ) ^ t := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    simp only [hσt, hWt, hh, map_mul, map_pow, div_pow]
    rw [hEsplit, pow_add, pow_add]
    field_simp
    ring
  have hWt' : (Wt : ℂ) = (W : ℂ) + ((star π : GaussianInt) : ℂ) ^ (n + 4) * (Δ : ℂ) := by
    have hWW : Wt = W + star π ^ (n + 4) * Δ := by rw [← hΔ]; ring
    rw [hWW, map_add, map_mul, map_pow]
  have hgπ : ((star π : GaussianInt) : ℂ) ^ (n + 4) / h = g * (π : ℂ) ^ n := by
    simp only [hh, hg, cellGen]
    have hn4 : n + 4 = α + D := by omega
    rw [hn4, pow_add]
    field_simp
  have hkey : σt * ((((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) + e') =
      (W : ℂ) / h + g * (π : ℂ) ^ n * Δ + σt * e' := by
    rw [mul_add, hcx, hWt', ← hgπ]
    ring
  set u : ℂ := ((W : ℂ) / h - c₀ + σt * e') / g with hu
  have hy : (σt * ((((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) + e')) / g =
      (((m₀ + π ^ n * Δ : GaussianInt) : ℂ)) + ((1 + I) / 2 + u) := by
    rw [hkey, hu, hc₀]
    simp only [map_add, map_mul, map_pow]
    field_simp
    ring
  have hunorm : ‖u‖ < 1 / 2 := by
    have hρn : ‖((star ρ : GaussianInt) : ℂ)‖ = ‖(ρ : ℂ)‖ := by
      rw [GaussianInt.toComplex_star, Complex.norm_conj]
    have hρ0' : ‖(ρ : ℂ)‖ ≠ 0 := by rw [← hρn]; exact norm_ne_zero_iff.mpr hρ0
    have hτ : ‖σt * e'‖ = ‖e'‖ := by
      rw [hσt, norm_mul, norm_mul, _root_.norm_pow, _root_.norm_pow, hπ.norm_sigma, norm_div, hρn,
        div_self hρ0']
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
    calc ‖(W : ℂ) / h - c₀ + σt * e'‖ ≤ ‖(W : ℂ) / h - c₀‖ + ‖σt * e'‖ := norm_add_le _ _
      _ < 1 / 2 * ‖g‖ := by rw [hτ]; linarith
  simp only [label]
  rw [← hg, hy, gaussFloor_add_intCast, gaussFloor_half_add hunorm, add_zero, map_add,
    map_mul, hπ.ψ_pow_self, zero_mul, add_zero, hm₀, hπ.ψ_natCast_val]

end DigitPrime

end Green41

/- ## Section: `DigitPigeonhole` -/

/-
# Digit pigeonhole (Gayfulin–Moshchevitin Lemma 4, abstract form; blueprint §6)

Let `Y` be a set of naturals `< pⁿ` with `pⁿ ≤ 4 |Y|²`. Take `ℓ = 4L` and `n = 8(A + ℓ)`.
Then there are a level `s` with `A + ℓ ≤ s ≤ n` and a residue `λ` mod `p^(s-ℓ)` over which
`Y` has at least `p^L` distinct residues mod `p^s`.

Proof: with levels `s_i = n - iℓ` (`i ≤ J`, `s_J ∈ [A, A + ℓ)`), the number of residues of
`Y` at level `s_i` is at most `p^L` times the number at level `s_{i+1}` unless some fiber is
large. Telescoping gives `|Y| ≤ p^(s_J) p^(LJ)`, which is too small.
-/

namespace Green41

/-- The residues mod `p^s` of the elements of `Y` lying over `λ` mod `p^(s-ℓ)`. -/
def digitFiber (p s ℓ lam : ℕ) (Y : Finset ℕ) : Finset ℕ :=
  (Y.filter (fun y => y % p ^ (s - ℓ) = lam)).image (· % p ^ s)

lemma card_image_mod_le_card_image_mul {p : ℕ} {s ℓ L : ℕ}
    (Y : Finset ℕ) (hfib : ∀ lam, (digitFiber p s ℓ lam Y).card ≤ p ^ L) :
    (Y.image (· % p ^ s)).card ≤ p ^ L * (Y.image (· % p ^ (s - ℓ))).card := by
  have hdvd : p ^ (s - ℓ) ∣ p ^ s := pow_dvd_pow p (Nat.sub_le s ℓ)
  have himg : (Y.image (· % p ^ s)).image (· % p ^ (s - ℓ)) = Y.image (· % p ^ (s - ℓ)) := by
    rw [Finset.image_image]
    congr 1
    funext y
    exact Nat.mod_mod_of_dvd y hdvd
  rw [← himg]
  apply Finset.card_le_mul_card_image
  intro lam _
  calc ((Y.image (· % p ^ s)).filter (fun x => x % p ^ (s - ℓ) = lam)).card
      = (digitFiber p s ℓ lam Y).card := by
        congr 1
        ext x
        simp only [digitFiber, Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨y, hy, rfl⟩, hx⟩
          exact ⟨y, ⟨hy, by rwa [Nat.mod_mod_of_dvd y hdvd] at hx⟩, rfl⟩
        · rintro ⟨y, ⟨hy, hyl⟩, rfl⟩
          exact ⟨⟨y, hy, rfl⟩, by rwa [Nat.mod_mod_of_dvd y hdvd]⟩
    _ ≤ p ^ L := hfib lam

/-- **Digit pigeonhole.** -/
theorem digit_pigeonhole {p : ℕ} (hp : 5 ≤ p) {n A L : ℕ} (hL : 0 < L)
    (hn : n = 8 * (A + 4 * L)) (Y : Finset ℕ) (hY : ∀ y ∈ Y, y < p ^ n)
    (hcard : p ^ n ≤ 4 * Y.card ^ 2) :
    ∃ s, A + 4 * L ≤ s ∧ s ≤ n ∧ ∃ lam : ℕ, p ^ L ≤ (digitFiber p s (4 * L) lam Y).card := by
  by_contra hcon
  push Not at hcon
  have hp0 : 0 < p := by omega
  set ℓ := 4 * L with hℓ
  have hℓpos : 0 < ℓ := by omega
  set J := (n - A) / ℓ with hJ
  have hJℓ : J * ℓ ≤ n - A := Nat.div_mul_le_self (n - A) ℓ
  have hJℓ' : n - A < J * ℓ + ℓ := by
    have := Nat.lt_div_mul_add (a := n - A) hℓpos; rw [hJ]; linarith
  have hAn : A ≤ n := by omega
  -- telescoping over the levels `n - i ℓ`
  have htel : ∀ i, i ≤ J → Y.card ≤ (Y.image (· % p ^ (n - i * ℓ))).card * (p ^ L) ^ i := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [zero_mul, Nat.sub_zero, pow_zero, mul_one]
      apply le_of_eq
      rw [Finset.card_image_of_injOn]
      intro a ha b hb hab
      simp only at hab
      rwa [Nat.mod_eq_of_lt (hY a ha), Nat.mod_eq_of_lt (hY b hb)] at hab
    | succ i ih =>
      intro hi
      have hi' : i ≤ J := by omega
      have hs1 : A + ℓ ≤ n - i * ℓ := by
        have : (i + 1) * ℓ ≤ J * ℓ := Nat.mul_le_mul_right ℓ hi
        rw [add_mul, one_mul] at this
        omega
      have hstep := card_image_mod_le_card_image_mul (p := p) (s := n - i * ℓ) (ℓ := ℓ) (L := L)
        Y (fun lam => (hcon _ hs1 (by omega) lam).le)
      have heq : n - i * ℓ - ℓ = n - (i + 1) * ℓ := by rw [add_mul, one_mul]; omega
      rw [heq] at hstep
      calc Y.card ≤ (Y.image (· % p ^ (n - i * ℓ))).card * (p ^ L) ^ i := ih hi'
        _ ≤ (p ^ L * (Y.image (· % p ^ (n - (i + 1) * ℓ))).card) * (p ^ L) ^ i :=
            Nat.mul_le_mul_right _ hstep
        _ = (Y.image (· % p ^ (n - (i + 1) * ℓ))).card * (p ^ L) ^ (i + 1) := by ring
  have hlast := htel J le_rfl
  set sJ := n - J * ℓ with hsJ
  have hsJlt : sJ < A + ℓ := by omega
  have hcardJ : (Y.image (· % p ^ sJ)).card ≤ p ^ sJ := by
    calc (Y.image (· % p ^ sJ)).card ≤ (Finset.range (p ^ sJ)).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
      _ = p ^ sJ := Finset.card_range _
  have hY2 : Y.card ≤ p ^ (sJ + L * J) := by
    calc Y.card ≤ (Y.image (· % p ^ sJ)).card * (p ^ L) ^ J := hlast
      _ ≤ p ^ sJ * (p ^ L) ^ J := Nat.mul_le_mul_right _ hcardJ
      _ = p ^ (sJ + L * J) := by rw [← pow_mul, ← pow_add]
  have hexp : 2 * (sJ + L * J) + 1 ≤ n := by
    have h4 : 4 * (L * J) = n - sJ := by
      have : J * ℓ = n - sJ := by omega
      rw [← this, hℓ]; ring
    omega
  have hlt : 4 * Y.card ^ 2 < p ^ n := by
    calc 4 * Y.card ^ 2 ≤ 4 * (p ^ (sJ + L * J)) ^ 2 := by
          apply Nat.mul_le_mul_left; exact Nat.pow_le_pow_left hY2 2
      _ = 4 * p ^ (2 * (sJ + L * J)) := by rw [← pow_mul, mul_comm (sJ + L * J) 2]
      _ < p * p ^ (2 * (sJ + L * J)) := by
          apply Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = p ^ (2 * (sJ + L * J) + 1) := by rw [pow_succ]; ring
      _ ≤ p ^ n := Nat.pow_le_pow_right hp0 hexp
  omega

end Green41

/- ## Section: `DiscreteCore` -/

/-
# The discrete core (Gayfulin–Moshchevitin Lemmas 5–8, simplified; blueprint §7)

Let `N = p^ℓ` with `p ≥ 5`, let `B` have `w ↦ Bʷ mod N` injective on `[0, S)`, where
`S = (p - 1) p^(ℓ-1)`, let `γ ∈ ℝ`, and let `𝔜` be a finite set of naturals with distinct
residues mod `N`, with `25 H³ < 4 |𝔜|` and `H ε² ≥ 2`. Then some point `Bʷ (y/N + γ)` lies
within `ε/2` of an integer.

Proof: sum the Fejér-type kernel `|Σ_{a<H} e(a t)|²` over all points. Each term is at most
`1/ε²` if the point is `ε/2`-far from the integers. The diagonal of the expanded sum is
`H S |𝔜|`. An off-diagonal frequency `m` contributes at most `N √(|𝔜| |m|)`, by
Cauchy–Schwarz, injectivity of `w ↦ Bʷ`, orthogonality of additive characters mod `N`, and a
bucket count of `{y' : N ∣ m (y - y')}`.
-/

namespace Green41

open Complex Finset

/-- `e(x) = exp(2πix)`. -/
noncomputable def ex (x : ℝ) : ℂ := Complex.exp (I * ((2 * Real.pi * x : ℝ) : ℂ))

lemma norm_ex (x : ℝ) : ‖ex x‖ = 1 := by
  unfold ex; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _

lemma ex_add (x y : ℝ) : ex (x + y) = ex x * ex y := by
  unfold ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ex_intCast (k : ℤ) : ex k = 1 := by
  unfold ex
  rw [Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

lemma ex_add_intCast (x : ℝ) (k : ℤ) : ex (x + k) = ex x := by
  rw [ex_add, ex_intCast, mul_one]

lemma ex_zero : ex 0 = 1 := by simpa using ex_intCast 0

lemma ex_nat_mul (a : ℕ) (x : ℝ) : ex (a * x) = ex x ^ a := by
  unfold ex; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma ex_neg (x : ℝ) : ex (-x) = (starRingEnd ℂ) (ex x) := by
  unfold ex
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

lemma ex_eq_one_iff (x : ℝ) : ex x = 1 ↔ ∃ k : ℤ, x = k := by
  unfold ex
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h2 : (((2 * Real.pi * x : ℝ)) : ℂ) = ((2 * Real.pi * k : ℝ) : ℂ) := by
      have hI : I ≠ 0 := I_ne_zero
      apply mul_left_cancel₀ hI
      rw [hk]; push_cast; ring
    have h3 : 2 * Real.pi * x = 2 * Real.pi * k := by exact_mod_cast h2
    have hpi : 2 * Real.pi ≠ 0 := by positivity
    exact mul_left_cancel₀ hpi h3
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

/-- `‖e(x) - 1‖ ≥ 4 |x - k|` for the nearest integer `k = round x`. -/
lemma norm_ex_sub_one_ge (x : ℝ) : 4 * |x - round x| ≤ ‖ex x - 1‖ := by
  set y := x - round x with hy
  have hxy : ex x = ex y := by
    rw [hy, sub_eq_add_neg, ← Int.cast_neg, ex_add_intCast]
  rw [hxy]
  have hy1 : |y| ≤ 1 / 2 := by
    rw [hy]; exact abs_sub_round x
  unfold ex
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  have hs : 2 * |y| ≤ |Real.sin (2 * Real.pi * y / 2)| := by
    rw [show 2 * Real.pi * y / 2 = Real.pi * y by ring]
    rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0]
      have h1 : Real.pi * y ≤ Real.pi / 2 := by
        have := abs_of_nonneg h0 ▸ hy1; nlinarith [Real.pi_pos]
      have := Real.mul_le_sin (by positivity) h1
      have hnn : 0 ≤ 2 / Real.pi * (Real.pi * y) := by positivity
      rw [abs_of_nonneg (by linarith)]
      calc 2 * y = 2 / Real.pi * (Real.pi * y) := by field_simp
        _ ≤ Real.sin (Real.pi * y) := this
    · rw [abs_of_neg h0]
      have h1 : Real.pi * (-y) ≤ Real.pi / 2 := by
        have := abs_of_neg h0 ▸ hy1; nlinarith [Real.pi_pos]
      have := Real.mul_le_sin (by nlinarith [Real.pi_pos]) h1
      have hsin : Real.sin (Real.pi * y) = -Real.sin (Real.pi * (-y)) := by
        rw [mul_neg, Real.sin_neg, neg_neg]
      have hnn : 0 ≤ 2 / Real.pi * (Real.pi * -y) := by
        have : 0 ≤ -y := by linarith
        positivity
      rw [hsin, abs_neg, abs_of_nonneg (by linarith)]
      calc 2 * -y = 2 / Real.pi * (Real.pi * -y) := by field_simp
        _ ≤ Real.sin (Real.pi * -y) := this
  linarith

/-- Fejér bound: if `x` is `δ`-far from the integers, `‖Σ_{a<H} e(a x)‖ ≤ 1/(2δ)`. -/
lemma norm_geom_ex_le {x δ : ℝ} (hδ : 0 < δ) (hfar : δ ≤ |x - round x|) (H : ℕ) :
    ‖∑ a ∈ range H, ex (a * x)‖ ≤ 1 / (2 * δ) := by
  have hge := norm_ex_sub_one_ge x
  have hne : ex x ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hge
    linarith
  have hpos : 0 < ‖ex x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  simp_rw [ex_nat_mul]
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖ex x ^ H - 1‖ ≤ 2 := by
    calc ‖ex x ^ H - 1‖ ≤ ‖ex x ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_ex, one_pow, norm_one]; norm_num
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith

/-- Orthogonality: `Σ_{u<N} e(u x / N) = N` if `N ∣ x` and `0` otherwise. -/
lemma sum_ex_div (N : ℕ) (hN : 0 < N) (x : ℤ) :
    ∑ u ∈ range N, ex (u * x / N) = if (N : ℤ) ∣ x then (N : ℂ) else 0 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hterm : ∀ u : ℕ, ex (u * x / N) = ex ((x : ℝ) / N) ^ u := by
    intro u; rw [← ex_nat_mul]; congr 1; ring
  simp_rw [hterm]
  split_ifs with hdvd
  · obtain ⟨k, hk⟩ := hdvd
    have : ex ((x : ℝ) / N) = 1 := by
      rw [ex_eq_one_iff]; exact ⟨k, by rw [hk]; push_cast; field_simp⟩
    simp [this]
  · have hne : ex ((x : ℝ) / N) ≠ 1 := by
      rw [Ne, ex_eq_one_iff]
      rintro ⟨k, hk⟩
      apply hdvd
      refine ⟨k, ?_⟩
      have : (x : ℝ) = N * k := by rw [← hk]; field_simp
      exact_mod_cast this
    rw [geom_sum_eq hne]
    have hpow : ex ((x : ℝ) / N) ^ N = 1 := by
      rw [← ex_nat_mul, show (N : ℝ) * ((x : ℝ) / N) = ((x : ℤ) : ℝ) by field_simp, ex_intCast]
    rw [hpow, sub_self, zero_div]

/-- `‖Σ zᵢ‖² = Re Σᵢ Σⱼ zᵢ z̄ⱼ`. -/
lemma norm_sum_sq_eq {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 = (∑ i ∈ s, ∑ j ∈ s, z i * (starRingEnd ℂ) (z j)).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj,
    map_sum, Finset.sum_mul_sum]

lemma ex_mul_conj (a b : ℝ) : ex a * (starRingEnd ℂ) (ex b) = ex (a - b) := by
  rw [← ex_neg, ← ex_add, sub_eq_add_neg]

/-- Bucket count: among residues that are pairwise `N ∣ m (y - y')`, there are at most `|m|`. -/
lemma card_filter_dvd_le {N : ℕ} (hN : 0 < N) {m : ℤ} (hm : m ≠ 0) (Y : Finset ℕ)
    (hinj : Set.InjOn (· % N) Y) (y : ℕ) :
    (Y.filter (fun y' : ℕ => (N : ℤ) ∣ m * ((y : ℤ) - (y' : ℤ)))).card ≤ m.natAbs := by
  set S := Y.filter (fun y' : ℕ => (N : ℤ) ∣ m * ((y : ℤ) - (y' : ℤ)))
  set M := m.natAbs with hM
  have hMpos : 0 < M := Int.natAbs_pos.mpr hm
  have hMz : (M : ℤ) = |m| := Int.natCast_natAbs m
  calc S.card ≤ (range M).card := by
        apply Finset.card_le_card_of_injOn (fun y' => (y' % N) * M / N)
        · intro y' _
          simp only [coe_range, Set.mem_Iio]
          rw [Nat.div_lt_iff_lt_mul hN]
          calc y' % N * M < N * M := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hN) hMpos
            _ = M * N := mul_comm _ _
        · intro y₁ hy₁ y₂ hy₂ hb
          replace hy₁ := Finset.mem_filter.mp (Finset.mem_coe.mp hy₁)
          replace hy₂ := Finset.mem_filter.mp (Finset.mem_coe.mp hy₂)
          by_contra hne
          set r₁ := y₁ % N with hr₁
          set r₂ := y₂ % N with hr₂
          have hr : r₁ ≠ r₂ := fun h => hne (hinj hy₁.1 hy₂.1 h)
          have e1 : (y₁ : ℤ) = (r₁ : ℤ) + (N : ℤ) * ((y₁ / N : ℕ) : ℤ) := by
            have h := Nat.mod_add_div y₁ N
            rw [← hr₁] at h
            exact_mod_cast h.symm
          have e2 : (y₂ : ℤ) = (r₂ : ℤ) + (N : ℤ) * ((y₂ / N : ℕ) : ℤ) := by
            have h := Nat.mod_add_div y₂ N
            rw [← hr₂] at h
            exact_mod_cast h.symm
          -- `N ∣ m (r₁ - r₂)`
          have hd : (N : ℤ) ∣ m * ((r₁ : ℤ) - (r₂ : ℤ)) := by
            have h1 := dvd_sub hy₂.2 hy₁.2
            have hid : m * ((r₁ : ℤ) - (r₂ : ℤ)) = (m * ((y : ℤ) - y₂) - m * ((y : ℤ) - y₁)) -
                (N : ℤ) * (m * (((y₁ / N : ℕ) : ℤ) - ((y₂ / N : ℕ) : ℤ))) := by
              rw [e1, e2]; ring
            rw [hid]
            exact dvd_sub h1 (dvd_mul_right _ _)
          have hne0 : m * ((r₁ : ℤ) - (r₂ : ℤ)) ≠ 0 := by
            apply mul_ne_zero hm
            intro h0; apply hr; exact_mod_cast sub_eq_zero.mp h0
          have hle := Int.le_of_dvd (abs_pos.mpr hne0) ((dvd_abs _ _).mpr hd)
          -- same bucket: `|r₁ M - r₂ M| < N`
          have hq := Nat.div_add_mod (r₁ * M) N
          have hq2 := Nat.div_add_mod (r₂ * M) N
          simp only at hb
          rw [hb] at hq
          have hm1 := Nat.mod_lt (r₁ * M) hN
          have hm2 := Nat.mod_lt (r₂ * M) hN
          have hq' : (N : ℤ) * ((r₂ * M / N : ℕ) : ℤ) + ((r₁ * M % N : ℕ) : ℤ) = (r₁ : ℤ) * M := by
            exact_mod_cast hq
          have hq2' : (N : ℤ) * ((r₂ * M / N : ℕ) : ℤ) + ((r₂ * M % N : ℕ) : ℤ) = (r₂ : ℤ) * M := by
            exact_mod_cast hq2
          have hm1' : ((r₁ * M % N : ℕ) : ℤ) < N := by exact_mod_cast hm1
          have hm2' : ((r₂ * M % N : ℕ) : ℤ) < N := by exact_mod_cast hm2
          have hm1'' : (0 : ℤ) ≤ ((r₁ * M % N : ℕ) : ℤ) := Int.natCast_nonneg _
          have hm2'' : (0 : ℤ) ≤ ((r₂ * M % N : ℕ) : ℤ) := Int.natCast_nonneg _
          have habs : |(r₁ : ℤ) * M - (r₂ : ℤ) * M| < N := by
            rw [abs_lt]; constructor <;> linarith
          have hEq : |m * ((r₁ : ℤ) - (r₂ : ℤ))| = |(r₁ : ℤ) * M - (r₂ : ℤ) * M| := by
            rw [show (r₁ : ℤ) * M - (r₂ : ℤ) * M = (M : ℤ) * ((r₁ : ℤ) - (r₂ : ℤ)) by ring,
              abs_mul, abs_mul, hMz, abs_abs]
          linarith
    _ = M := card_range _

/-- `Σ_{u<N} ‖Σ_y e(m u y / N)‖² ≤ N |Y| |m|`. -/
lemma sum_norm_sq_char_le {N : ℕ} (hN : 0 < N) {m : ℤ} (hm : m ≠ 0) (Y : Finset ℕ)
    (hinj : Set.InjOn (· % N) Y) :
    ∑ u ∈ range N, ‖∑ y ∈ Y, ex (m * u * y / N)‖ ^ 2 ≤ N * Y.card * m.natAbs := by
  have hexpand : ∀ u : ℕ, ‖∑ y ∈ Y, ex (m * u * y / N)‖ ^ 2 =
      (∑ y ∈ Y, ∑ y' ∈ Y, ex (u * (m * ((y : ℤ) - (y' : ℤ)) : ℤ) / N)).re := by
    intro u
    rw [norm_sum_sq_eq]
    congr 1
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro y' _
    rw [ex_mul_conj]; congr 1; push_cast; ring
  simp_rw [hexpand]
  rw [← Complex.re_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := range N)]
  simp_rw [sum_ex_div N hN]
  have hcount : ∀ y ∈ Y, (∑ y' ∈ Y, (if (N : ℤ) ∣ m * ((y : ℤ) - (y' : ℤ)) then (N : ℂ) else 0)).re ≤
      N * m.natAbs := by
    intro y _
    rw [← Finset.sum_filter, Complex.re_sum]
    simp only [Complex.natCast_re, Finset.sum_const, nsmul_eq_mul]
    have := card_filter_dvd_le hN hm Y hinj y
    have h2 : ((Y.filter (fun y' : ℕ => (N : ℤ) ∣ m * ((y : ℤ) - (y' : ℤ)))).card : ℝ) ≤ m.natAbs := by
      exact_mod_cast this
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  rw [Complex.re_sum]
  calc ∑ y ∈ Y, (∑ y' ∈ Y, (if (N : ℤ) ∣ m * ((y : ℤ) - (y' : ℤ)) then (N : ℂ) else 0)).re
      ≤ ∑ y ∈ Y, ((N : ℝ) * m.natAbs) := Finset.sum_le_sum hcount
    _ = N * Y.card * m.natAbs := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Replacing `Bʷ` by its residue and reindexing by the injective map `w ↦ Bʷ mod N`. -/
lemma sum_w_norm_sq_le {N S B : ℕ} (hN : 0 < N) {m : ℤ} (hm : m ≠ 0) (Y : Finset ℕ)
    (hinj : Set.InjOn (· % N) Y)
    (hB : Set.InjOn (fun w : ℕ => ((B : ZMod N) ^ w)) (Set.Iio S)) :
    ∑ w ∈ range S, ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w) * y / N)‖ ^ 2 ≤ N * Y.card * m.natAbs := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hres : ∀ w : ℕ, ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w) * y / N)‖ =
      ‖∑ y ∈ Y, ex (m * ((B ^ w % N : ℕ) : ℝ) * y / N)‖ := by
    intro w
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    have hdiv := Nat.mod_add_div (B ^ w) N
    set q := B ^ w / N with hq
    set r := B ^ w % N with hr
    have h' : ((B : ℝ) ^ w) = (r : ℝ) + N * (q : ℝ) := by
      exact_mod_cast hdiv.symm
    have : (m : ℝ) * ((B : ℝ) ^ w) * y / N = m * (r : ℝ) * y / N + ((m * (q : ℤ) * y : ℤ) : ℝ) := by
      rw [h']; push_cast; field_simp
    rw [this, ex_add_intCast]
  simp_rw [hres]
  set f : ℕ → ℝ := fun u => ‖∑ y ∈ Y, ex (m * (u : ℝ) * y / N)‖ ^ 2 with hf
  have hinjU : Set.InjOn (fun w => B ^ w % N) (range S : Set ℕ) := by
    intro w₁ hw₁ w₂ hw₂ h
    apply hB (by simpa using hw₁) (by simpa using hw₂)
    simp only at h ⊢
    rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff']
    exact h
  calc ∑ w ∈ range S, f (B ^ w % N)
      = ∑ u ∈ (range S).image (fun w => B ^ w % N), f u := (Finset.sum_image hinjU).symm
    _ ≤ ∑ u ∈ range N, f u := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hu
          exact Finset.mem_range.mpr (Nat.mod_lt _ hN)
        · intro u _ _; positivity
    _ ≤ N * Y.card * m.natAbs := sum_norm_sq_char_le hN hm Y hinj

/-- Cauchy–Schwarz over `w`: `‖Σ_w σ_w(m)‖ ≤ N √(|Y| |m|)`. -/
lemma norm_sum_w_le {N S B : ℕ} (hN : 0 < N) (hSN : S ≤ N) {m : ℤ} (hm : m ≠ 0) (Y : Finset ℕ)
    (hinj : Set.InjOn (· % N) Y)
    (hB : Set.InjOn (fun w : ℕ => ((B : ZMod N) ^ w)) (Set.Iio S)) (γ : ℝ) :
    ‖∑ w ∈ range S, ∑ y ∈ Y, ex (m * ((B : ℝ) ^ w * ((y : ℝ) / N + γ)))‖ ≤
      N * Real.sqrt (Y.card * m.natAbs) := by
  have hfac : ∀ w, ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w * ((y : ℝ) / N + γ)))‖ =
      ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w) * y / N)‖ := by
    intro w
    have : ∑ y ∈ Y, ex (m * ((B : ℝ) ^ w * ((y : ℝ) / N + γ))) =
        ex (m * (B : ℝ) ^ w * γ) * ∑ y ∈ Y, ex (m * ((B : ℝ) ^ w) * y / N) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [← ex_add]
      congr 1
      ring
    rw [this, norm_mul, norm_ex, one_mul]
  set a : ℕ → ℝ := fun w => ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w) * y / N)‖ with ha
  have hsum : ∑ w ∈ range S, a w ≤ N * Real.sqrt (Y.card * m.natAbs) := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := range S) (f := a)
    rw [card_range] at hcs
    have hsq := sum_w_norm_sq_le hN hm Y hinj hB
    have hbound : (∑ w ∈ range S, a w) ^ 2 ≤ ((N : ℝ) * Real.sqrt (Y.card * m.natAbs)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      calc (∑ w ∈ range S, a w) ^ 2 ≤ S * ∑ w ∈ range S, a w ^ 2 := hcs
        _ ≤ N * (N * Y.card * m.natAbs) := by
            apply mul_le_mul (by exact_mod_cast hSN) hsq (by positivity) (by positivity)
        _ = (N : ℝ) ^ 2 * (Y.card * m.natAbs) := by ring
    exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun w _ => norm_nonneg _) (by positivity)
      two_ne_zero).mp hbound
  calc ‖∑ w ∈ range S, ∑ y ∈ Y, ex (m * ((B : ℝ) ^ w * ((y : ℝ) / N + γ)))‖
      ≤ ∑ w ∈ range S, ‖∑ y ∈ Y, ex (m * ((B : ℝ) ^ w * ((y : ℝ) / N + γ)))‖ := norm_sum_le _ _
    _ = ∑ w ∈ range S, a w := by
        apply Finset.sum_congr rfl; intro w _; rw [hfac]
    _ ≤ N * Real.sqrt (Y.card * m.natAbs) := hsum

lemma sum_comm4 {α β γ δ M : Type*} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (C : Finset γ) (D : Finset δ) (f : α → β → γ → δ → M) :
    ∑ w ∈ A, ∑ y ∈ B, ∑ a ∈ C, ∑ a' ∈ D, f w y a a' =
      ∑ a ∈ C, ∑ a' ∈ D, ∑ w ∈ A, ∑ y ∈ B, f w y a a' := by
  simp_rw [← Finset.sum_product' (s := C) (t := D)]
  rw [Finset.sum_congr rfl (fun w _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

/-- **Discrete core.** Some point `Bʷ (y/N + γ)` (`w < S`, `y ∈ Y`) is within `ε/2` of an
integer. -/
theorem discrete_core {p ℓ S H B : ℕ} (hp : 5 ≤ p) (hS : S = (p - 1) * p ^ (ℓ - 1)) (hℓ : 1 ≤ ℓ)
    {ε : ℝ} (hε : 0 < ε) (hH : 2 ≤ (H : ℝ) * ε ^ 2)
    (hB : Set.InjOn (fun w : ℕ => ((B : ZMod (p ^ ℓ)) ^ w)) (Set.Iio S))
    (γ : ℝ) (Y : Finset ℕ) (hinj : Set.InjOn (· % p ^ ℓ) Y) (hY : 25 * H ^ 3 < 4 * Y.card) :
    ∃ w < S, ∃ y ∈ Y, |(B : ℝ) ^ w * ((y : ℝ) / ((p ^ ℓ : ℕ) : ℝ) + γ) -
      round ((B : ℝ) ^ w * ((y : ℝ) / ((p ^ ℓ : ℕ) : ℝ) + γ))| < ε / 2 := by
  by_contra hcon
  push Not at hcon
  set N := p ^ ℓ with hNdef
  have hN : 0 < N := by positivity
  have hpl : p ^ ℓ = p * p ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
  have hSN : S ≤ N := by
    rw [hS, hNdef, hpl]; exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
  have h5S : 4 * N ≤ 5 * S := by
    rw [hS, hNdef, hpl]
    have h4 : 4 * p ≤ 5 * (p - 1) := by omega
    calc 4 * (p * p ^ (ℓ - 1)) = (4 * p) * p ^ (ℓ - 1) := by ring
      _ ≤ (5 * (p - 1)) * p ^ (ℓ - 1) := Nat.mul_le_mul_right _ h4
      _ = 5 * ((p - 1) * p ^ (ℓ - 1)) := by ring
  have hHpos : 0 < H := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · rw [h0] at hH; simp at hH; linarith
    · exact h0
  have hYpos : 0 < Y.card := by omega
  set t : ℕ → ℕ → ℝ := fun w y => (B : ℝ) ^ w * ((y : ℝ) / N + γ) with ht
  -- upper bound on the kernel sum
  have hterm : ∀ w ∈ range S, ∀ y ∈ Y, ‖∑ a ∈ range H, ex (a * t w y)‖ ^ 2 ≤ (1 / ε) ^ 2 := by
    intro w hw y hy
    have hfar := hcon w (Finset.mem_range.mp hw) y hy
    have h := norm_geom_ex_le (x := t w y) (δ := ε / 2) (by positivity) hfar H
    rw [show 1 / (2 * (ε / 2)) = 1 / ε by field_simp] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hup : ∑ w ∈ range S, ∑ y ∈ Y, ‖∑ a ∈ range H, ex (a * t w y)‖ ^ 2 ≤
      S * Y.card * (1 / ε) ^ 2 := by
    calc _ ≤ ∑ w ∈ range S, ∑ y ∈ Y, (1 / ε) ^ 2 :=
          Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun y hy => hterm w hw y hy
      _ = S * Y.card * (1 / ε) ^ 2 := by simp [Finset.sum_const, card_range]; ring
  -- expansion of the kernel
  have hexp : ∑ w ∈ range S, ∑ y ∈ Y, ‖∑ a ∈ range H, ex (a * t w y)‖ ^ 2 =
      ∑ a ∈ range H, ∑ a' ∈ range H,
        (∑ w ∈ range S, ∑ y ∈ Y, ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t w y)).re := by
    have h1 : ∀ w y, ‖∑ a ∈ range H, ex (a * t w y)‖ ^ 2 =
        ∑ a ∈ range H, ∑ a' ∈ range H, (ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t w y)).re := by
      intro w y
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
    apply Finset.sum_congr rfl; intro w _
    rw [Complex.re_sum]
  -- lower bound, term by term
  set c : ℝ := N * Real.sqrt (Y.card * H) with hc
  have hc0 : 0 ≤ c := by positivity
  have hlow : ∀ a ∈ range H, ∀ a' ∈ range H,
      (if a = a' then (S : ℝ) * Y.card else 0) - c ≤
        (∑ w ∈ range S, ∑ y ∈ Y, ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t w y)).re := by
    intro a ha a' ha'
    by_cases haa : a = a'
    · subst haa
      have hX : (∑ w ∈ range S, ∑ y ∈ Y, ex ((((a : ℤ) - (a : ℤ) : ℤ) : ℝ) * t w y)) =
          (S : ℂ) * Y.card := by
        simp only [sub_self, Int.cast_zero, zero_mul, ex_zero, Finset.sum_const, card_range,
          nsmul_eq_mul, mul_one]
      rw [hX, ite_eq_left rfl]
      have hre : ((S : ℂ) * (Y.card : ℂ)).re = (S : ℝ) * Y.card := by
        rw [← Nat.cast_mul, Complex.natCast_re, Nat.cast_mul]
      rw [hre]; linarith
    · simp only [haa, ite_false, zero_sub]
      set m : ℤ := (a : ℤ) - (a' : ℤ) with hmdef
      have hm : m ≠ 0 := by intro h; apply haa; omega
      have hmH : m.natAbs ≤ H := by
        have h1 := Finset.mem_range.mp ha
        have h2 := Finset.mem_range.mp ha'
        omega
      have hnorm := norm_sum_w_le hN hSN hm Y hinj hB γ
      have h2 : Real.sqrt (Y.card * m.natAbs) ≤ Real.sqrt (Y.card * H) := by
        apply Real.sqrt_le_sqrt
        have : (m.natAbs : ℝ) ≤ H := by exact_mod_cast hmH
        nlinarith [(Nat.cast_nonneg Y.card : (0 : ℝ) ≤ Y.card)]
      have h3 := neg_le_of_abs_le (Complex.abs_re_le_norm
        (∑ w ∈ range S, ∑ y ∈ Y, ex ((m : ℝ) * t w y)))
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      calc -c ≤ -(N * Real.sqrt (Y.card * m.natAbs)) := by
            rw [hc]; nlinarith
        _ ≤ -‖∑ w ∈ range S, ∑ y ∈ Y, ex ((m : ℝ) * t w y)‖ := by
            simp only [ht] at hnorm ⊢; linarith
        _ ≤ _ := h3
  have hinner : ∀ a ∈ range H, ∑ a' ∈ range H, ((if a = a' then (S : ℝ) * Y.card else 0) - c) =
      S * Y.card - H * c := by
    intro a ha
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, ite_eq_left ha, Finset.sum_const, card_range,
      nsmul_eq_mul]
  have hsumlow : (H : ℝ) * (S * Y.card) - (H : ℝ) ^ 2 * c ≤
      ∑ a ∈ range H, ∑ a' ∈ range H,
        (∑ w ∈ range S, ∑ y ∈ Y, ex ((((a : ℤ) - (a' : ℤ) : ℤ) : ℝ) * t w y)).re := by
    calc (H : ℝ) * (S * Y.card) - (H : ℝ) ^ 2 * c = ∑ a ∈ range H, ((S : ℝ) * Y.card - H * c) := by
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

end Green41

/- ## Section: `MinorArc` -/

/-
# The minor-arc proposition (blueprint §8)

Chain Step A (§4), the counting of labels (§5), the digit pigeonhole (§6) and the
discrete core (§7) to hit the stripe. This file proves the generic statement for a digit
prime `π` with multiplier prime `ρ`. `KL57.lean` instantiates it with `(P, Q)` and `(Q, P)`
and fixes the parameters.
-/

namespace Green41

open Complex ComplexConjugate Finset

/- ## Arithmetic of the fiber -/

/-- The value `val(X bʷ y) / p^s` modulo `1`, read on a fiber over `λ` mod `p^(s-ℓ)`. -/
lemma frac_on_fiber {p n s ℓ : ℕ} (hp : 0 < p) (hsn : s ≤ n) (hℓs : ℓ ≤ s) (X B yv lam w : ℕ)
    (hlam : yv % p ^ (s - ℓ) = lam) :
    ∃ k : ℤ, ((X * B ^ w * yv % p ^ n : ℕ) : ℝ) / (p : ℝ) ^ s =
      (B : ℝ) ^ w * (((X * (yv % p ^ s / p ^ (s - ℓ)) : ℕ) : ℝ) / ((p ^ ℓ : ℕ) : ℝ) +
        ((X * lam : ℕ) : ℝ) / (p : ℝ) ^ s) + k := by
  set r := yv % p ^ s with hr
  set z := r / p ^ (s - ℓ) with hz
  set Q := yv / p ^ s with hQ
  set M := X * B ^ w * yv with hM
  have hdvd : p ^ (s - ℓ) ∣ p ^ s := pow_dvd_pow p (Nat.sub_le s ℓ)
  have hrl : r % p ^ (s - ℓ) = lam := by rw [hr, Nat.mod_mod_of_dvd _ hdvd, hlam]
  have hr1 : r = lam + p ^ (s - ℓ) * z := by
    have := Nat.mod_add_div r (p ^ (s - ℓ)); rw [hrl] at this; exact this.symm
  have hy1 : yv = r + p ^ s * Q := by
    have := Nat.mod_add_div yv (p ^ s); exact this.symm
  have hM1 : M % p ^ n + p ^ n * (M / p ^ n) = M := Nat.mod_add_div M (p ^ n)
  set qM := M / p ^ n with hqM
  refine ⟨(X * B ^ w * Q : ℕ) - (p ^ (n - s) * qM : ℕ), ?_⟩
  have hpr : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hps : (p : ℝ) ^ s = (p : ℝ) ^ (s - ℓ) * (p : ℝ) ^ ℓ := by
    rw [← pow_add, Nat.sub_add_cancel hℓs]
  have hpn : (p : ℝ) ^ n = (p : ℝ) ^ s * (p : ℝ) ^ (n - s) := by
    rw [← pow_add, Nat.add_sub_cancel' hsn]
  have eM : ((M % p ^ n : ℕ) : ℝ) = (M : ℝ) - (p : ℝ) ^ n * (qM : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hM1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at this
    linarith
  have eMv : (M : ℝ) = X * (B : ℝ) ^ w * ((lam : ℝ) + (p : ℝ) ^ (s - ℓ) * z + (p : ℝ) ^ s * Q) := by
    rw [hM, hy1, hr1]; push_cast; ring
  rw [eM, eMv]
  push_cast
  rw [hpn, hps]
  field_simp
  ring

/-- Multiplication by a unit is injective on residues `< p^ℓ`. -/
lemma mul_mod_inj {p ℓ X z₁ z₂ : ℕ} (hX : Nat.Coprime X p) (h1 : z₁ < p ^ ℓ) (h2 : z₂ < p ^ ℓ)
    (h : X * z₁ % p ^ ℓ = X * z₂ % p ^ ℓ) : z₁ = z₂ := by
  have hc : Nat.gcd (p ^ ℓ) X = 1 := by
    rw [Nat.gcd_comm]; exact (Nat.Coprime.pow_right ℓ hX)
  have hmod : z₁ ≡ z₂ [MOD p ^ ℓ] := Nat.ModEq.cancel_left_of_coprime hc h
  unfold Nat.ModEq at hmod
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod

/- ## The generic minor-arc theorem -/

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

lemma isUnit_Xfac {ρ : GaussianInt} (hρ2 : ¬ π ∣ star ρ) {n α β j : ℕ} (hn : 0 < n) :
    IsUnit (hπ.Xfac ρ n α β j) := by
  unfold Xfac
  have h1 := hπ.isUnit_re n
  have h2 : IsUnit (hπ.ψ n (star π)) := (hπ.isUnit_ψ_iff hn _).mpr hπ.not_dvd_star
  have h2' : IsUnit ((hπ.ψ n (star π))⁻¹) :=
    IsUnit.of_mul_eq_one_right _ (ZMod.mul_inv_of_unit _ h2)
  have h3 : IsUnit (hπ.ψ n (star ρ)) := (hπ.isUnit_ψ_iff hn _).mpr hρ2
  exact ((h1.mul (h2'.pow j)).mul (h2.pow _)).mul (h3.pow _)

lemma coprime_val_of_isUnit {n : ℕ} (hn : 0 < n) {X : ZMod (p ^ n)} (hX : IsUnit X) :
    Nat.Coprime X.val p := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hπ.prime.ne_zero⟩
  rw [← ZMod.natCast_zmod_val X, ZMod.isUnit_iff_coprime] at hX
  exact Nat.Coprime.coprime_dvd_right (dvd_pow_self p hn.ne') hX

omit hπ in
lemma norm_rotOf {ρ : GaussianInt} (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0) :
    ‖(ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)‖ = 1 := by
  have h : ‖((star ρ : GaussianInt) : ℂ)‖ = ‖(ρ : ℂ)‖ := by
    rw [GaussianInt.toComplex_star, Complex.norm_conj]
  rw [norm_div, h, div_self]
  rw [← h]; exact norm_ne_zero_iff.mpr hρ0

/-- **Minor arcs, generic form.** -/
theorem minor_arc_core (hp5 : 5 ≤ p) {ρ : GaussianInt}
    (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ) (hρ4 : ¬ star π ∣ star ρ)
    (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0)
    {n α β A L ℓ S H : ℕ} (hL : 0 < L) (hℓ : ℓ = 4 * L) (hS : S = (p - 1) * p ^ (ℓ - 1))
    (hSβ : S ≤ β) (hnA : n = 8 * (A + ℓ)) (hα : α = n - A)
    (hordA : orderOf (hπ.mult (star ρ) (n + 4)) = (p - 1) * p ^ (n + 3))
    (hordB : orderOf (((hπ.mult ρ n).val : ℕ) : ZMod (p ^ ℓ)) = S)
    {ε : ℝ} (hε : 0 < ε) (hH : 2 ≤ (H : ℝ) * ε ^ 2) (hHL : 25 * H ^ 3 < 4 * p ^ L)
    (hg : Real.sqrt 2 * ‖cellGen π ρ n α β‖ ≤ ε / 2)
    (w : ℂ) {N₀ a₁ b₁ a₂ b₂ v E : ℕ} (ha₁ : a₁ ≤ N₀) (hb₁ : b₁ ≤ N₀) (ha₂ : a₂ ≤ N₀)
    (hb₂ : b₂ ≤ N₀) (hE : (p - 1) * p ^ (n + 3) + β ≤ E) {q₂ : GaussianInt}
    (hq₂ : ¬ star π ∣ q₂)
    (he' : ‖(((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) -
        (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
            ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
          ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
            ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ <
        21 / 50 * ‖cellGen π ρ n α β‖) :
    ∃ a b : ℕ, a ≤ N₀ + v + (A + 4) + n ∧ b ≤ N₀ + (p - 1) * p ^ (n + 3) + S ∧
      ∃ k : ℤ, |(((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b * w).re - k| < ε := by
  set σ : ℂ := (π : ℂ) / ((star π : GaussianInt) : ℂ) with hσ
  set τ : ℂ := (ρ : ℂ) / ((star ρ : GaussianInt) : ℂ) with hτ
  set g := cellGen π ρ n α β with hg_def
  set T := (p - 1) * p ^ (n + 3) with hT
  set j := v + (n - α + 4) with hj
  set q : ℂ := (((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) with hq
  set r : ℂ := σ ^ a₁ * τ ^ b₁ - σ ^ a₂ * τ ^ b₂ with hr
  set e' : ℂ := r * w - q with he'_def
  have he'n : ‖e'‖ < 21 / 50 * ‖g‖ := by rw [he'_def, norm_sub_rev]; exact he'
  have hrw : r * w = q + e' := by rw [he'_def]; ring
  have hn0 : 0 < n := by omega
  have hαn : α ≤ n := by omega
  have hp0 : 0 < p := by omega
  -- Step A
  have hA : ∀ l : ZMod (p ^ n), ∃ t < T, hπ.label ρ n α β (σ ^ j * τ ^ t * (q + e')) = l :=
    fun l => hπ.stepA hp5 hρ1 hρ4 hρ0 hαn hordA hE hq₂ he'n l
  -- the orbit
  set Z : Finset ℂ := ((range (N₀ + j + 1)) ×ˢ (range (N₀ + T + 1))).image
    (fun ab => σ ^ ab.1 * τ ^ ab.2 * w) with hZ
  have hmemZ : ∀ a b, a ≤ N₀ + j → b ≤ N₀ + T → σ ^ a * τ ^ b * w ∈ Z := by
    intro a b ha hb
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, rfl⟩
  have hall : ∀ l : ZMod (p ^ n), ∃ x ∈ Z, ∃ x' ∈ Z, hπ.label ρ n α β (x - x') = l := by
    intro l
    obtain ⟨t, ht, hl⟩ := hA l
    refine ⟨σ ^ (j + a₁) * τ ^ (t + b₁) * w, hmemZ _ _ (by omega) (by omega),
      σ ^ (j + a₂) * τ ^ (t + b₂) * w, hmemZ _ _ (by omega) (by omega), ?_⟩
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
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hxZ
  simp only [Finset.mem_product, Finset.mem_range] at hab
  -- the stripe value of the label
  set m := gaussFloor ((σ ^ a * τ ^ b * w) / g) with hm
  have hlabel : hπ.label ρ n α β (σ ^ a * τ ^ b * w) = hπ.ψ n m := rfl
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
  refine ⟨a + j', b + w', by omega, by omega, ?_⟩
  have hsplit : σ ^ (a + j') * τ ^ (b + w') * w =
      σ ^ j' * τ ^ w' * (g * m) + σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * w - g * m) := by
    rw [pow_add, pow_add]; ring
  have hg0 : g ≠ 0 := by
    simp only [hg_def, cellGen]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hπ.toComplex_star_ne_zero)
      (pow_ne_zero _ hρ0)) (pow_ne_zero _ hπ.toComplex_ne_zero)
  have hnear : ‖σ ^ a * τ ^ b * w - g * m‖ < Real.sqrt 2 * ‖g‖ := by
    have : σ ^ a * τ ^ b * w - g * m = g * ((σ ^ a * τ ^ b * w) / g - m) := by
      field_simp
    rw [this, norm_mul, mul_comm]
    exact mul_lt_mul_of_pos_right (norm_sub_gaussFloor_lt _) (norm_pos_iff.mpr hg0)
  have hunit : ‖σ ^ j' * τ ^ w'‖ = 1 := by
    rw [norm_mul, _root_.norm_pow, _root_.norm_pow, hσ, hπ.norm_sigma, hτ, norm_rotOf hρ0,
      one_pow, one_pow, one_mul]
  have hre2 : |(σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * w - g * m)).re| < ε / 2 := by
    calc |(σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * w - g * m)).re|
        ≤ ‖σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * w - g * m)‖ := Complex.abs_re_le_norm _
      _ = ‖σ ^ j' * τ ^ w' * (σ ^ a * τ ^ b * w - g * m)‖ := rfl
      _ = ‖σ ^ a * τ ^ b * w - g * m‖ := by rw [norm_mul, hunit, one_mul]
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

end Green41

/- ## Section: `Params` -/

/-
# Parameters for the minor-arc proposition (blueprint §8)

All parameters are functions of the prime `p` and of `K = ⌈1/ε⌉₊`:
`c = clog_p K`, `L = 6c + 4`, `ℓ = 4L`, `S = (p-1) p^(ℓ-1)`, `A = 2S + 2c + 3`,
`n = 8(A + ℓ)`, `α = n - A`, `H = 2K²`.
The key size bound is `n + 4 ≤ 25 · 13^40 · K^24` for `5 ≤ p ≤ 13`.
-/

namespace Green41

/-- `c = clog_p K`. -/
def pc (p K : ℕ) : ℕ := Nat.clog p K
/-- `L = 6c + 4`. -/
def pL (p K : ℕ) : ℕ := 6 * pc p K + 4
/-- `ℓ = 4L`. -/
def pℓ (p K : ℕ) : ℕ := 4 * pL p K
/-- `S = (p - 1) p^(ℓ-1)`. -/
def pS (p K : ℕ) : ℕ := (p - 1) * p ^ (pℓ p K - 1)
/-- `A = 2S + 2c + 3`. -/
def pA (p K : ℕ) : ℕ := 2 * pS p K + 2 * pc p K + 3
/-- `n = 8(A + ℓ)`. -/
def pn (p K : ℕ) : ℕ := 8 * (pA p K + pℓ p K)
/-- `α = n - A`. -/
def pα (p K : ℕ) : ℕ := pn p K - pA p K
/-- `H = 2K²`. -/
def pH (K : ℕ) : ℕ := 2 * K ^ 2

lemma pL_pos (p K : ℕ) : 0 < pL p K := by unfold pL; omega

lemma pℓ_ge (p K : ℕ) : 16 ≤ pℓ p K := by unfold pℓ pL; omega

lemma pn_eq (p K : ℕ) : pn p K = 8 * (pA p K + pℓ p K) := rfl

lemma pα_eq (p K : ℕ) : pα p K = pn p K - pA p K := rfl

lemma pA_le_pn (p K : ℕ) : pA p K ≤ pn p K := by unfold pn; omega

lemma pS_le (p K : ℕ) : pS p K ≤ p ^ pℓ p K := by
  unfold pS
  have hℓ := pℓ_ge p K
  have : p ^ pℓ p K = p * p ^ (pℓ p K - 1) := by
    rw [← pow_succ']; congr 1
  rw [this]
  exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)

lemma pow_pc_le (p K : ℕ) (hp : 2 ≤ p) (hK : 2 ≤ K) : p ^ pc p K ≤ p * K := by
  unfold pc
  rcases Nat.eq_zero_or_pos (Nat.clog p K) with h0 | h0
  · rw [h0, pow_zero]; nlinarith
  · have h1 := Nat.pow_pred_clog_lt_self (by omega : 1 < p) (by omega : 1 < K)
    have : p ^ Nat.clog p K = p * p ^ (Nat.clog p K).pred := by
      rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos h0).symm
    rw [this]
    exact Nat.mul_le_mul_left _ h1.le

lemma le_pow_pc (p K : ℕ) (hp : 2 ≤ p) : K ≤ p ^ pc p K := Nat.le_pow_clog (by omega) K

lemma pow_pL_eq (p K : ℕ) : p ^ pL p K = p ^ 4 * (p ^ pc p K) ^ 6 := by
  unfold pL; rw [← pow_mul, ← pow_add]; ring_nf

lemma pow_pℓ_eq (p K : ℕ) : p ^ pℓ p K = (p ^ pL p K) ^ 4 := by
  unfold pℓ; rw [← pow_mul]; ring_nf

/-- `625 K⁶ ≤ p^L`. -/
lemma pow_pL_ge (p K : ℕ) (hp : 5 ≤ p) : 625 * K ^ 6 ≤ p ^ pL p K := by
  rw [pow_pL_eq]
  have h1 : 625 ≤ p ^ 4 := by
    calc 625 = 5 ^ 4 := by norm_num
      _ ≤ p ^ 4 := Nat.pow_le_pow_left hp 4
  have h2 : K ^ 6 ≤ (p ^ pc p K) ^ 6 := Nat.pow_le_pow_left (le_pow_pc p K (by omega)) 6
  exact Nat.mul_le_mul h1 h2

/-- `25 H³ < 4 p^L`. -/
lemma pH_cube_lt (p K : ℕ) (hp : 5 ≤ p) (hK : 1 ≤ K) : 25 * pH K ^ 3 < 4 * p ^ pL p K := by
  have h := pow_pL_ge p K hp
  unfold pH
  have hK6 : 1 ≤ K ^ 6 := Nat.one_le_pow _ _ hK
  have : 25 * (2 * K ^ 2) ^ 3 = 200 * K ^ 6 := by ring
  rw [this]
  omega

/-- `p^ℓ ≤ p^40 K^24`. -/
lemma pow_pℓ_le (p K : ℕ) (hp : 2 ≤ p) (hK : 2 ≤ K) : p ^ pℓ p K ≤ p ^ 40 * K ^ 24 := by
  rw [pow_pℓ_eq, pow_pL_eq]
  have h := pow_pc_le p K hp hK
  calc (p ^ 4 * (p ^ pc p K) ^ 6) ^ 4 ≤ (p ^ 4 * (p * K) ^ 6) ^ 4 := by
        apply Nat.pow_le_pow_left
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 6)
    _ = p ^ 40 * K ^ 24 := by ring

/-- `n + 4 ≤ 25 p^40 K^24`. -/
lemma pn_add_four_le (p K : ℕ) (hp : 5 ≤ p) (hK : 2 ≤ K) :
    pn p K + 4 ≤ 25 * (p ^ 40 * K ^ 24) := by
  have hS := pS_le p K
  have hℓ := pℓ_ge p K
  have hℓp : 3 * pℓ p K + 3 ≤ p ^ pℓ p K := by
    have h2 : pℓ p K + 1 ≤ 2 ^ pℓ p K := Nat.lt_two_pow_self
    have h4 : 2 ^ pℓ p K * 2 ^ pℓ p K ≤ p ^ pℓ p K := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
    nlinarith
  have hc : pc p K ≤ pℓ p K := by unfold pℓ pL; omega
  have hpl := pow_pℓ_le p K (by omega) hK
  have hA : pA p K + pℓ p K ≤ 3 * p ^ pℓ p K := by unfold pA; omega
  unfold pn
  have : 1 ≤ p ^ pℓ p K := Nat.one_le_pow _ _ (by omega)
  omega

end Green41

/- ## Section: `KL57Proof` -/

/-
# Proof of the Kravitz–Leng interface `KL57With 100`

For `ε < 1/10` put `K = ⌈1/ε⌉₊` and take the parameters of `Params.lean`. Case 1
(`size5 q ≥ size13 q`) uses the digit prime `P` with multiplier `Q`; case 2 uses `Q` with `P`.
Both go through the generic `DigitPrime.minor_arc_core`.
-/

namespace Green41

open Complex ComplexConjugate

/- ## Real bounds -/

lemma rpow_neg_hundred {ε : ℝ} (hε : 0 < ε) : ε ^ (-(100 : ℝ)) = (1 / ε) ^ 100 := by
  rw [Real.rpow_neg hε.le, show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    one_div, inv_pow]

lemma ηKL_hundred {ε : ℝ} (hε : 0 < ε) : ηKL 100 ε = (5 : ℝ) ^ (-((1 / ε) ^ 100)) := by
  unfold ηKL; rw [rpow_neg_hundred hε]

lemma ηKL_rpow_neg_five {ε : ℝ} (hε : 0 < ε) :
    ηKL 100 ε ^ (-5 : ℝ) = (5 : ℝ) ^ (5 * (1 / ε) ^ 100) := by
  rw [ηKL_hundred hε, ← Real.rpow_mul (by norm_num)]
  congr 1; ring

/-- The key size bound: `n + 4 ≤ (5/2) (1/ε)^100`. -/
lemma pn_small {p : ℕ} (hp5 : 5 ≤ p) (hp13 : p ≤ 13) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    ((pn p ⌈1 / ε⌉₊ : ℕ) : ℝ) + 4 ≤ 5 / 2 * (1 / ε) ^ 100 := by
  set u := 1 / ε with hu
  have hu10 : 10 < u := by rw [hu, lt_div_iff₀ hε]; linarith
  set K := ⌈u⌉₊ with hK
  have hK1 : (1 : ℝ) < K := lt_of_lt_of_le (by linarith) (Nat.le_ceil u)
  have hK2 : 2 ≤ K := by
    have : 1 < K := by exact_mod_cast hK1
    omega
  have hKu : (K : ℝ) ≤ 2 * u := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ u)
    linarith
  have hnat := pn_add_four_le p K hp5 hK2
  have h1 : ((pn p K + 4 : ℕ) : ℝ) ≤ ((25 * (p ^ 40 * K ^ 24) : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at h1
  have hp' : (p : ℝ) ≤ 13 := by exact_mod_cast hp13
  have h2 : (p : ℝ) ^ 40 ≤ 13 ^ 40 := pow_le_pow_left₀ (by positivity) hp' 40
  have h3 : (K : ℝ) ^ 24 ≤ (2 * u) ^ 24 := pow_le_pow_left₀ (by positivity) hKu 24
  have hu76 : (10 : ℝ) ^ 76 ≤ u ^ 76 := pow_le_pow_left₀ (by norm_num) hu10.le 76
  have hnum : (25 : ℝ) * 13 ^ 40 * 2 ^ 24 ≤ 5 / 2 * 10 ^ 76 := by norm_num
  have hu24 : (0 : ℝ) ≤ u ^ 24 := by positivity
  calc ((pn p K : ℕ) : ℝ) + 4 ≤ 25 * ((p : ℝ) ^ 40 * (K : ℝ) ^ 24) := h1
    _ ≤ 25 * ((13 : ℝ) ^ 40 * (2 * u) ^ 24) := by gcongr
    _ = 25 * 13 ^ 40 * 2 ^ 24 * u ^ 24 := by ring
    _ ≤ 5 / 2 * 10 ^ 76 * u ^ 24 := by gcongr
    _ ≤ 5 / 2 * u ^ 76 * u ^ 24 := by gcongr
    _ = 5 / 2 * u ^ 100 := by ring

/-- `√2 g ≤ ε/2` from `g² ≤ ε²/125`. -/
lemma sqrt_two_mul_le {g ε : ℝ} (hg0 : 0 ≤ g) (hε : 0 < ε) (h : g ^ 2 ≤ ε ^ 2 / 125) :
    Real.sqrt 2 * g ≤ ε / 2 := by
  have h2 : (Real.sqrt 2 * g) ^ 2 ≤ (ε / 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2

/- ## The cell generator -/

lemma sqrt_pow_sq {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : (Real.sqrt x ^ k) ^ 2 = x ^ k := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx]

lemma norm_cellGen_sq {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (n α β : ℕ) :
    ‖cellGen π ρ n α β‖ ^ 2 = (p : ℝ) ^ α * (ρ.norm : ℝ) ^ β / (p : ℝ) ^ n := by
  have hρn : ‖((star ρ : GaussianInt) : ℂ)‖ = Real.sqrt (ρ.norm : ℝ) := by
    rw [norm_toComplex, Zsqrtd.norm_conj]
  unfold cellGen
  rw [norm_div, norm_mul, _root_.norm_pow, _root_.norm_pow, _root_.norm_pow,
    hπ.norm_toComplex_star_π, hπ.norm_toComplex_π, hρn, div_pow, mul_pow,
    sqrt_pow_sq (Nat.cast_nonneg p), sqrt_pow_sq (Nat.cast_nonneg p),
    sqrt_pow_sq (by exact_mod_cast GaussianInt.norm_nonneg ρ)]

/-- `‖g‖² = N(ρ)^β / p^A` when `α + A = n`. -/
lemma norm_cellGen_sq' {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) {n α β A : ℕ}
    (hnA : α + A = n) :
    ‖cellGen π ρ n α β‖ ^ 2 = (ρ.norm : ℝ) ^ β / (p : ℝ) ^ A := by
  rw [norm_cellGen_sq hπ, ← hnA, pow_add]
  have hp0 : (p : ℝ) ^ α ≠ 0 := pow_ne_zero _ (by exact_mod_cast hπ.prime.ne_zero)
  field_simp

/-- Upper bound on the cell: `‖g‖² ≤ ε²/125`. -/
lemma norm_cellGen_sq_le {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp5 : 5 ≤ p)
    (hρn : (ρ.norm : ℝ) ≤ (p : ℝ) ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ‖cellGen π ρ (pn p ⌈1 / ε⌉₊) (pα p ⌈1 / ε⌉₊) (pS p ⌈1 / ε⌉₊)‖ ^ 2 ≤ ε ^ 2 / 125 := by
  set K := ⌈1 / ε⌉₊ with hK
  rw [norm_cellGen_sq' hπ (A := pA p K) (by unfold pα; have := pA_le_pn p K; omega)]
  have hpr : (0 : ℝ) < p := by exact_mod_cast hπ.prime.pos
  have hpc : (K : ℝ) ≤ (p : ℝ) ^ pc p K := by exact_mod_cast le_pow_pc p K (by omega)
  have hKe : 1 / ε ≤ K := Nat.le_ceil _
  have hA : (p : ℝ) ^ pA p K = ((p : ℝ) ^ 2) ^ pS p K * ((p : ℝ) ^ pc p K) ^ 2 * (p : ℝ) ^ 3 := by
    unfold pA; rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; ring_nf
  rw [hA, div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : (ρ.norm : ℝ) ^ pS p K ≤ ((p : ℝ) ^ 2) ^ pS p K :=
    pow_le_pow_left₀ (by exact_mod_cast GaussianInt.norm_nonneg ρ) hρn _
  have h2 : (125 : ℝ) ≤ (p : ℝ) ^ 3 := by
    have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    nlinarith
  have h3 : 1 ≤ ε ^ 2 * ((p : ℝ) ^ pc p K) ^ 2 := by
    have : 1 ≤ ε * (p : ℝ) ^ pc p K := by
      calc (1 : ℝ) = ε * (1 / ε) := by field_simp
        _ ≤ ε * K := by gcongr
        _ ≤ ε * (p : ℝ) ^ pc p K := by gcongr
    nlinarith
  have hq : (0 : ℝ) ≤ ((p : ℝ) ^ 2) ^ pS p K := by positivity
  calc (ρ.norm : ℝ) ^ pS p K * 125 ≤ ((p : ℝ) ^ 2) ^ pS p K * 125 := by gcongr
    _ ≤ ((p : ℝ) ^ 2) ^ pS p K * ((p : ℝ) ^ 3 * (ε ^ 2 * ((p : ℝ) ^ pc p K) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hq; nlinarith
    _ = ε ^ 2 * (((p : ℝ) ^ 2) ^ pS p K * ((p : ℝ) ^ pc p K) ^ 2 * (p : ℝ) ^ 3) := by ring

/-- Lower bound on the cell: `5^(-A) ≤ ‖g‖`. -/
lemma norm_cellGen_ge {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp13 : p ≤ 13)
    (hρ1 : 1 ≤ (ρ.norm : ℝ)) {n α β A : ℕ} (hnA : α + A = n) :
    (1 / 5 : ℝ) ^ A ≤ ‖cellGen π ρ n α β‖ := by
  have hsq := norm_cellGen_sq' hπ (ρ := ρ) (β := β) hnA
  have hpr : (0 : ℝ) < p := by exact_mod_cast hπ.prime.pos
  have h1 : ((1 / 5 : ℝ) ^ A) ^ 2 ≤ ‖cellGen π ρ n α β‖ ^ 2 := by
    rw [hsq, ← pow_mul, le_div_iff₀ (by positivity)]
    have hp' : (p : ℝ) ≤ 25 := by have : (p : ℝ) ≤ 13 := by exact_mod_cast hp13
                                  linarith
    have h2 : (p : ℝ) ^ A ≤ 25 ^ A := pow_le_pow_left₀ hpr.le hp' A
    have h3 : (1 : ℝ) ≤ (ρ.norm : ℝ) ^ β := one_le_pow₀ hρ1
    have h4 : (1 / 5 : ℝ) ^ (A * 2) * 25 ^ A = 1 := by
      rw [mul_comm A 2, pow_mul, ← mul_pow]; norm_num
    calc (1 / 5 : ℝ) ^ (A * 2) * (p : ℝ) ^ A ≤ (1 / 5 : ℝ) ^ (A * 2) * 25 ^ A := by gcongr
      _ = 1 := h4
      _ ≤ (ρ.norm : ℝ) ^ β := h3
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h1

/- ## Budget bounds -/

/-- `p^(n+4) < 100 η^(-5)`. -/
lemma pow_n4_lt {p : ℕ} (hp5 : 5 ≤ p) (hp13 : p ≤ 13) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    ((p ^ (pn p ⌈1 / ε⌉₊ + 4) : ℕ) : ℝ) < 100 * ηKL 100 ε ^ (-5 : ℝ) := by
  set n := pn p ⌈1 / ε⌉₊
  have hsmall := pn_small hp5 hp13 hε hε1
  rw [ηKL_rpow_neg_five hε]
  have hp' : (p : ℝ) ≤ 25 := by
    have : (p : ℝ) ≤ 13 := by exact_mod_cast hp13
    linarith
  have h1 : ((p ^ (n + 4) : ℕ) : ℝ) ≤ (25 : ℝ) ^ (n + 4) := by
    push_cast; exact pow_le_pow_left₀ (by positivity) hp' _
  have h2 : (25 : ℝ) ^ (n + 4) = (5 : ℝ) ^ ((2 * (n + 4) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, pow_mul]; norm_num
  have h3 : (5 : ℝ) ^ ((2 * (n + 4) : ℕ) : ℝ) ≤ (5 : ℝ) ^ (5 * (1 / ε) ^ 100) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast; linarith
  have h4 : (0 : ℝ) < (5 : ℝ) ^ (5 * (1 / ε) ^ 100) := by positivity
  linarith

lemma budget_A {p K : ℕ} (hp5 : 5 ≤ p) : pA p K + 4 + pn p K ≤ p ^ (pn p K + 4) := by
  have hA := pA_le_pn p K
  have h1 : pn p K + 4 < 2 ^ (pn p K + 4) := Nat.lt_two_pow_self
  have h2 : 2 ^ (pn p K + 4) * 2 ≤ p ^ (pn p K + 4) := by
    calc 2 ^ (pn p K + 4) * 2 ≤ 2 ^ (pn p K + 4) * 2 ^ (pn p K + 4) := by
          apply Nat.mul_le_mul_left; exact Nat.le_self_pow (by omega) 2
      _ = 4 ^ (pn p K + 4) := by rw [← mul_pow]; norm_num
      _ ≤ p ^ (pn p K + 4) := Nat.pow_le_pow_left (by omega) _
  omega

lemma budget_T {p K : ℕ} (hp5 : 5 ≤ p) :
    (p - 1) * p ^ (pn p K + 3) + pS p K ≤ p ^ (pn p K + 4) := by
  have hS := pS_le p K
  have hℓ : pℓ p K ≤ pn p K + 3 := by unfold pn; omega
  have h1 : p ^ pℓ p K ≤ p ^ (pn p K + 3) := Nat.pow_le_pow_right (by omega) hℓ
  have h2 : p ^ (pn p K + 4) = (p - 1) * p ^ (pn p K + 3) + p ^ (pn p K + 3) := by
    set X := p ^ (pn p K + 3) with hX
    have h3 : p ^ (pn p K + 4) = p * X := by rw [hX, ← pow_succ']
    have h4 : (p - 1) * X + X = ((p - 1) + 1) * X := by ring
    rw [h3, h4, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  omega

/-- `η ≤ 5^(-A)`. -/
lemma ηKL_le_five_pow_neg {p : ℕ} (hp5 : 5 ≤ p) (hp13 : p ≤ 13) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1 / 10) : ηKL 100 ε ≤ (1 / 5 : ℝ) ^ pA p ⌈1 / ε⌉₊ := by
  have hsmall := pn_small hp5 hp13 hε hε1
  have hA : (pA p ⌈1 / ε⌉₊ : ℝ) * 8 ≤ pn p ⌈1 / ε⌉₊ := by
    have : pA p ⌈1 / ε⌉₊ * 8 ≤ pn p ⌈1 / ε⌉₊ := by unfold pn; omega
    exact_mod_cast this
  have h5 : (1 / 5 : ℝ) ^ pA p ⌈1 / ε⌉₊ = (5 : ℝ) ^ (-(pA p ⌈1 / ε⌉₊ : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  rw [ηKL_hundred hε, h5]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hu : (0 : ℝ) ≤ (1 / ε) ^ 100 := by positivity
  linarith

/- ## The generic case -/

theorem case_core {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp5 : 5 ≤ p) (hp13 : p ≤ 13)
    (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ) (hρ4 : ¬ star π ∣ star ρ)
    (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0) (hρn : (ρ.norm : ℝ) ≤ (p : ℝ) ^ 2)
    (hρn1 : 1 ≤ (ρ.norm : ℝ))
    (hordA : ∀ k, 2 ≤ k → orderOf (hπ.mult (star ρ) k) = (p - 1) * p ^ (k - 1))
    (hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
      orderOf (((hπ.mult ρ n).val : ℕ) : ZMod (p ^ ℓ)) = (p - 1) * p ^ (ℓ - 1))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) (w : ℂ) (q : GaussianInt) {N₀ a₁ b₁ a₂ b₂ v : ℕ}
    (ha₁ : a₁ ≤ N₀) (hb₁ : b₁ ≤ N₀) (ha₂ : a₂ ≤ N₀) (hb₂ : b₂ ≤ N₀)
    (hdiv : ∀ E : ℕ, (E : ℝ) < 100 * ηKL 100 ε ^ (-5 : ℝ) →
      ∃ q₂ : GaussianInt, ¬ star π ∣ q₂ ∧ q = star π ^ v * star ρ ^ E * q₂)
    (hclose : ‖(q : ℂ) - (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ ≤ ηKL 100 ε / 10) :
    ∃ a b : ℕ, (a : ℝ) ≤ N₀ + v + 100 * ηKL 100 ε ^ (-5 : ℝ) ∧
      (b : ℝ) ≤ N₀ + 100 * ηKL 100 ε ^ (-5 : ℝ) ∧
      ∃ k : ℤ, |(((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b * w).re - k| < ε := by
  set K := ⌈1 / ε⌉₊ with hK
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) (Nat.le_ceil (1 / ε))
    exact_mod_cast this
  have hn2 : 2 ≤ pn p K := by unfold pn; have := pℓ_ge p K; omega
  have hℓ1 : 1 ≤ pℓ p K := by have := pℓ_ge p K; omega
  set E := (p - 1) * p ^ (pn p K + 3) + pS p K with hE
  have hM := pow_n4_lt hp5 hp13 hε hε1
  have hEM : E ≤ p ^ (pn p K + 4) := budget_T hp5
  have hAM : pA p K + 4 + pn p K ≤ p ^ (pn p K + 4) := budget_A hp5
  have hEreal : (E : ℝ) < 100 * ηKL 100 ε ^ (-5 : ℝ) := by
    have : (E : ℝ) ≤ ((p ^ (pn p K + 4) : ℕ) : ℝ) := by exact_mod_cast hEM
    linarith
  obtain ⟨q₂, hq₂, hqeq⟩ := hdiv E hEreal
  -- the cell
  set g := cellGen π ρ (pn p K) (pα p K) (pS p K) with hg
  have hαA : pα p K + pA p K = pn p K := by unfold pα; have := pA_le_pn p K; omega
  have hglow : (1 / 5 : ℝ) ^ pA p K ≤ ‖g‖ := norm_cellGen_ge hπ hp13 hρn1 hαA
  have hηA := ηKL_le_five_pow_neg hp5 hp13 hε hε1
  have hgpos : 0 < ‖g‖ := lt_of_lt_of_le (by positivity) hglow
  have he' : ‖(((star π) ^ v * (star ρ) ^ E * q₂ : GaussianInt) : ℂ) -
      (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ < 21 / 50 * ‖g‖ := by
    rw [← hqeq]
    have hη0 : 0 < ηKL 100 ε := ηKL_pos 100 ε
    linarith
  have hgε : Real.sqrt 2 * ‖g‖ ≤ ε / 2 :=
    sqrt_two_mul_le (norm_nonneg _) hε (norm_cellGen_sq_le hπ hp5 hρn hε)
  have hH : 2 ≤ (pH K : ℝ) * ε ^ 2 := by
    have hKe : 1 / ε ≤ K := Nat.le_ceil _
    have h1 : 1 ≤ (K : ℝ) * ε := by
      calc (1 : ℝ) = (1 / ε) * ε := by field_simp
        _ ≤ K * ε := by gcongr
    unfold pH; push_cast; nlinarith
  have hHL : 25 * pH K ^ 3 < 4 * p ^ pL p K := pH_cube_lt p K hp5 hK1
  have hA4 := hordA (pn p K + 4) (by omega)
  rw [show pn p K + 4 - 1 = pn p K + 3 by omega] at hA4
  obtain ⟨a, b, ha, hb, k, hk⟩ := hπ.minor_arc_core hp5 hρ1 hρ2 hρ4 hρ0
    (n := pn p K) (α := pα p K) (β := pS p K) (A := pA p K) (L := pL p K) (ℓ := pℓ p K)
    (S := pS p K) (H := pH K) (pL_pos p K) rfl rfl le_rfl rfl rfl hA4
    (hordB (pn p K) (pℓ p K) hn2 hℓ1) hε hH hHL hgε w ha₁ hb₁ ha₂ hb₂ le_rfl hq₂ he'
  refine ⟨a, b, ?_, ?_, k, hk⟩
  · have h1 : (a : ℝ) ≤ N₀ + v + ((pA p K + 4 + pn p K : ℕ) : ℝ) := by
      have : a ≤ N₀ + v + (pA p K + 4 + pn p K) := by omega
      exact_mod_cast this
    have h2 : ((pA p K + 4 + pn p K : ℕ) : ℝ) ≤ ((p ^ (pn p K + 4) : ℕ) : ℝ) := by
      exact_mod_cast hAM
    linarith
  · have h1 : (b : ℝ) ≤ N₀ + (E : ℝ) := by
      have : b ≤ N₀ + E := by omega
      exact_mod_cast this
    have h2 : (E : ℝ) ≤ ((p ^ (pn p K + 4) : ℕ) : ℝ) := by exact_mod_cast hEM
    linarith

/- ## Decomposing `q` -/

lemma decomp_pow {a b q : GaussianInt} (ha : Prime a) (hcop : IsCoprime a b) (hq : q ≠ 0)
    {E : ℕ} (hE : b ^ E ∣ q) : ∃ q₂, ¬ a ∣ q₂ ∧ q = a ^ multiplicity a q * b ^ E * q₂ := by
  have hf : FiniteMultiplicity a q := FiniteMultiplicity.of_not_isUnit ha.not_isUnit hq
  set v := multiplicity a q with hv
  have hdvd : a ^ v ∣ q := pow_multiplicity_dvd a q
  obtain ⟨q₁, hq₁⟩ := hdvd
  have hnd : ¬ a ∣ q₁ := by
    rintro ⟨c, hc⟩
    apply hf.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self v)
    exact ⟨c, by rw [hq₁, hc, pow_succ]; ring⟩
  have hb : b ^ E ∣ q₁ := by
    have h1 : b ^ E ∣ a ^ v * q₁ := hq₁ ▸ hE
    exact (hcop.symm.pow).dvd_of_dvd_mul_left h1
  obtain ⟨q₂, hq₂⟩ := hb
  refine ⟨q₂, fun h => hnd (by rw [hq₂]; exact dvd_mul_of_dvd_right h _), ?_⟩
  rw [hq₁, hq₂]; ring

lemma size5_eq {q : GaussianInt} (hq : q ≠ 0) :
    size5 q = (5 : ℝ) ^ (-(multiplicity gPb q : ℝ)) := by
  unfold size5; rw [ite_eq_right hq]

lemma size13_eq {q : GaussianInt} (hq : q ≠ 0) :
    size13 q = (13 : ℝ) ^ (-(multiplicity gQb q : ℝ)) := by
  unfold size13; rw [ite_eq_right hq]

lemma le_logb_of_rpow_neg {b ϖ : ℝ} (hb : 1 < b) (hϖ : 0 < ϖ) {v : ℕ}
    (h : ϖ ≤ b ^ (-(v : ℝ))) : (v : ℝ) ≤ Real.logb b ϖ⁻¹ := by
  rw [Real.le_logb_iff_rpow_le hb (inv_pos.mpr hϖ)]
  rw [Real.rpow_neg (by linarith)] at h
  have hpos : 0 < b ^ (v : ℝ) := by positivity
  rw [le_inv_comm₀ hϖ hpos] at h
  exact h

lemma gPb_not_dvd_gQb : ¬ gPb ∣ gQb := by
  rintro ⟨c, hc⟩
  apply gP_not_dvd_gQ
  refine ⟨star c, ?_⟩
  have := congrArg star hc
  rwa [star_gQb, star_mul, star_gPb, mul_comm] at this

lemma gQb_not_dvd_gPb : ¬ gQb ∣ gPb := by
  rintro ⟨c, hc⟩
  apply gQ_not_dvd_gP
  refine ⟨star c, ?_⟩
  have := congrArg star hc
  rwa [star_gPb, star_mul, star_gQb, mul_comm] at this

lemma natCast_val_eq {m : ℕ} [NeZero m] (a : ZMod m) : ((a.val : ℕ) : ZMod m) = a :=
  ZMod.natCast_zmod_val a

/- ## The interface -/

/-- **Kravitz–Leng, Proposition 5.7, for points of `ℂ`**, with the constant `c = 100`. -/
theorem kl57With_100 : KL57With 100 := by
  intro ε ϖ hε0 hε1 hϖ0 hϖ1 N₀ s₁ t₁ s₂ t₂ w q hs₁ ht₁ hs₂ ht₂ hlow hup hclose
  have h5n := size5_nonneg q
  have h13n := size13_nonneg q
  have hq : q ≠ 0 := by
    rintro rfl
    simp only [size5, size13, ite_true] at hlow
    linarith
  have hlog0 : 0 ≤ Real.logb 5 ϖ⁻¹ :=
    Real.logb_nonneg (by norm_num) (by rw [le_inv_comm₀ one_pos hϖ0]; linarith)
  set X := 100 * ηKL 100 ε ^ (-5 : ℝ) with hX
  have hX0 : 0 ≤ X := mul_nonneg (by norm_num) (Real.rpow_nonneg (ηKL_pos 100 ε).le _)
  have hδ : δKL 100 ε = (13 : ℝ) ^ (-X) := rfl
  by_cases h513 : size13 q ≤ size5 q
  · -- Case 1: digit prime `P`, multiplier `Q`.
    set v := multiplicity gPb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      rw [← size5_eq hq]; linarith
    have hdiv : ∀ E : ℕ, (E : ℝ) < X →
        ∃ q₂ : GaussianInt, ¬ star gP ∣ q₂ ∧ q = star gP ^ v * star gQ ^ E * q₂ := by
      intro E hE
      have hlt : size13 q < 1 / (13 : ℝ) ^ E := by
        have h1 : (13 : ℝ) ^ (-X) < (13 : ℝ) ^ (-(E : ℝ)) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
        have hE' : (13 : ℝ) ^ (-(E : ℝ)) = 1 / (13 : ℝ) ^ E := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
        rw [hE', ← hδ] at h1
        linarith
      exact decomp_pow prime_gPb isCoprime_gPb_gQb hq (dvd_of_size13_lt hlt)
    have hordA : ∀ k, 2 ≤ k → orderOf (digitPrime_P.mult (star gQ) k) = (5 - 1) * 5 ^ (k - 1) := by
      intro k hk
      have : NeZero (5 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_P_Qb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_P.mult gQ n).val : ℕ) : ZMod (5 ^ ℓ)) = (5 - 1) * 5 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_P_Q hn hℓ
    obtain ⟨a, b, ha, hb, k, hk⟩ := case_core digitPrime_P le_rfl (by norm_num) gP_not_dvd_gQ
      gP_not_dvd_gQb gPb_not_dvd_gQb gQb_ne_zero (by rw [norm_gQ]; norm_num)
      (by rw [norm_gQ]; norm_num) hordA hordB hε0 hε1 w q hs₁ ht₁ hs₂ ht₂ hdiv hclose
    exact ⟨a, b, by linarith, by linarith, k, hk⟩
  · -- Case 2: digit prime `Q`, multiplier `P`.
    push Not at h513
    set v := multiplicity gQb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      have h1 : ϖ ≤ size13 q := by linarith
      rw [size13_eq hq] at h1
      have h2 : (13 : ℝ) ^ (-(v : ℝ)) ≤ (5 : ℝ) ^ (-(v : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
        apply inv_anti₀ (by positivity)
        exact Real.rpow_le_rpow (by norm_num) (by norm_num) (Nat.cast_nonneg _)
      linarith
    have hdiv : ∀ E : ℕ, (E : ℝ) < X →
        ∃ q₂ : GaussianInt, ¬ star gQ ∣ q₂ ∧ q = star gQ ^ v * star gP ^ E * q₂ := by
      intro E hE
      have hlt : size5 q < 1 / (5 : ℝ) ^ E := by
        have h1 : (13 : ℝ) ^ (-X) ≤ (5 : ℝ) ^ (-X) := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
          apply inv_anti₀ (by positivity)
          exact Real.rpow_le_rpow (by norm_num) (by norm_num) hX0
        have h2 : (5 : ℝ) ^ (-X) < (5 : ℝ) ^ (-(E : ℝ)) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
        have hE' : (5 : ℝ) ^ (-(E : ℝ)) = 1 / (5 : ℝ) ^ E := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
        rw [hE'] at h2
        rw [← hδ] at h1
        linarith
      exact decomp_pow prime_gQb isCoprime_gPb_gQb.symm hq (dvd_of_size5_lt hlt)
    have hordA : ∀ k, 2 ≤ k →
        orderOf (digitPrime_Q.mult (star gP) k) = (13 - 1) * 13 ^ (k - 1) := by
      intro k hk
      have : NeZero (13 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_Q_Pb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_Q.mult gP n).val : ℕ) : ZMod (13 ^ ℓ)) =
          (13 - 1) * 13 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_Q_P hn hℓ
    have hrot : ∀ s t : ℕ, rot s t = ((gQ : ℂ) / ((star gQ : GaussianInt) : ℂ)) ^ t *
        ((gP : ℂ) / ((star gP : GaussianInt) : ℂ)) ^ s := by
      intro s t; unfold rot θ5 θ13; rw [star_gP, star_gQ]; ring
    rw [hrot s₁ t₁, hrot s₂ t₂] at hclose
    obtain ⟨a, b, ha, hb, k, hk⟩ := case_core digitPrime_Q (by norm_num) le_rfl gQ_not_dvd_gP
      gQ_not_dvd_gPb gQb_not_dvd_gPb gPb_ne_zero (by rw [norm_gP]; norm_num)
      (by rw [norm_gP]; norm_num) hordA hordB hε0 hε1 w q ht₁ hs₁ ht₂ hs₂ hdiv hclose
    refine ⟨b, a, by linarith, by linarith, k, ?_⟩
    rw [hrot b a]
    exact hk

/-- The interface `KL57` holds. -/
theorem kl57 : KL57 := ⟨100, by norm_num, kl57With_100⟩

end Green41

/- ## The target -/

namespace Green41

open Complex Set Pointwise

/-- The double-exponential bound, with no hypotheses. -/
theorem doubleExponentialBound : DoubleExponentialBound :=
  doubleExponentialBound_of_KL57 kl57

/-- The Formal Conjectures statement with the answer `True`. -/
theorem green_41.variants.double_exponential_bound : True ↔
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, (minCopies ε : ℝ) ≤ Real.exp (Real.exp (ε ^ (-C))) :=
  ⟨fun _ => doubleExponentialBound, fun _ => trivial⟩

#print axioms green_41.variants.double_exponential_bound

end Green41

/- ## Section: `DigitCover` -/

/-
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
      rw [Finset.prod_eq_prod_Ico_succ_bot hkN, ite_eq_left rfl, hxx', hd']
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [ite_eq_right (by rw [Finset.mem_Ico] at hj; omega)]

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

/- ## Section: `DigitRotation` -/

/-
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

namespace Green41

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

end Green41

/- ## Section: `StepAFamily` -/

/-
# Step A for a family of multipliers

`Green41.DigitPrime.stepA` reaches every label with the powers `(ρ/ρ̄)^t`,
`t < (p - 1) p^(n+3)`, which forces `q` to be divisible by `ρ̄^E` with `E` exponential in `n`.
The proof only uses two facts about these multipliers:

1. their multipliers `ψ(Ā)/ψ(A)` reach every unit modulo `π̄^(n+4)`, and
2. their conjugates `Ā` all divide one common denominator `B`, which `q` absorbs.

`stepA_family` states Step A for any such family `𝒜` (the original is the case `𝒜 = {ρ^t}`,
`B = ρ̄^(E-β)`). `stepA_digit` instantiates it with the digit family of `DigitRotation`, whose
common denominator `ρ̄^(p-2) ∏_{1 ≤ j < n+4} (1 - p^j i)^(p-1)` has size `p^{O(n²)}`.
-/

namespace Green41

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

end Green41

/- ## Section: `MinorArcDigit` -/

/-
# Minor arcs with digit rotations

`minor_arc_core_digit` is `Green41.DigitPrime.minor_arc_core` with Step A replaced by
`stepA_digit`. The orbit used for counting labels becomes `σᵃ τᵇ μ w` with `μ` running over the
digit rotations `A/Ā`, `A ∈ digitFamily p (n + 4) ρ`, and `b ≤ N₀` instead of `b ≤ N₀ + T` with
`T = (p - 1) p^(n+3)`. Counting, the digit pigeonhole and the discrete core are unchanged.
-/

namespace Green41


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

end Green41

/- ## Section: `KL57Digit` -/

/-
# The minor-arc interface with digit rotations

The double-exponential proof feeds the minor-arc proposition with a `q` whose `P̄`- and
`Q̄`-adic sizes are below `δ = 13^(-c η⁻⁵)`; this makes `q` divisible by `ρ̄^E` with `E`
exponential, which Step A needs. With digit rotations Step A only needs `q` to be divisible by
the explicit Gaussian integers

* `D5 ε  = digitDen 5 (n₅ + 4) Q · Q̄^(S₅)` (digit prime `P`, multiplier `Q`), and
* `D13 ε = digitDen 13 (n₁₃ + 4) P · P̄^(S₁₃)` (digit prime `Q`, multiplier `P`),

so the interface `KL57D` asks for `Mdig ε = N(D5 ε) N(D13 ε) ∣ q` instead of the condition on
`δ`. The rotation it produces is `rot s t * μ` with `μ` a digit rotation and `s, t` bounded by
the polynomial quantity `Bd ε`.
-/

namespace Green41


open Complex ComplexConjugate Finset

/- ## Decomposing `q` -/

/-- If `D ∣ q` and `D` is prime to the prime `a`, then `q = a^v D q₂` with `a ∤ q₂`. -/
lemma decomp_dvd {a D q : GaussianInt} (ha : Prime a) (hcop : IsCoprime a D) (hq : q ≠ 0)
    (hD : D ∣ q) : ∃ q₂, ¬ a ∣ q₂ ∧ q = a ^ multiplicity a q * D * q₂ := by
  have hf : FiniteMultiplicity a q := FiniteMultiplicity.of_not_isUnit ha.not_isUnit hq
  set v := multiplicity a q with hv
  obtain ⟨q₁, hq₁⟩ : a ^ v ∣ q := pow_multiplicity_dvd a q
  have hnd : ¬ a ∣ q₁ := by
    rintro ⟨c, hc⟩
    apply hf.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self v)
    exact ⟨c, by rw [hq₁, hc, pow_succ]; ring⟩
  have hb : D ∣ q₁ := by
    have h1 : D ∣ a ^ v * q₁ := hq₁ ▸ hD
    exact (hcop.symm.pow_right).dvd_of_dvd_mul_left h1
  obtain ⟨q₂, hq₂⟩ := hb
  refine ⟨q₂, fun h => hnd (by rw [hq₂]; exact dvd_mul_of_dvd_right h _), ?_⟩
  rw [hq₁, hq₂]; ring

/-- A Gaussian integer divides its norm. -/
lemma dvd_natAbs_norm (D : GaussianInt) : D ∣ ((D.norm.natAbs : ℕ) : GaussianInt) := by
  have h : ((D.norm.natAbs : ℕ) : ℤ) = D.norm := Int.natAbs_of_nonneg (GaussianInt.norm_nonneg D)
  have h2 : ((D.norm.natAbs : ℕ) : GaussianInt) = ((D.norm : ℤ) : GaussianInt) := by
    rw [← Int.cast_natCast, h]
  rw [h2, Zsqrtd.norm_eq_mul_conj]
  exact dvd_mul_right D _

/- ## The digit data attached to `ε` -/

/-- The divisor needed in the case of the digit prime `P` (multiplier `Q`). -/
noncomputable def D5 (ε : ℝ) : GaussianInt :=
  DigitPrime.digitDen 5 (pn 5 ⌈1 / ε⌉₊ + 4) gQ * star gQ ^ pS 5 ⌈1 / ε⌉₊

/-- The divisor needed in the case of the digit prime `Q` (multiplier `P`). -/
noncomputable def D13 (ε : ℝ) : GaussianInt :=
  DigitPrime.digitDen 13 (pn 13 ⌈1 / ε⌉₊ + 4) gP * star gP ^ pS 13 ⌈1 / ε⌉₊

/-- The modulus `N(D5) N(D13)` that the pigeonhole has to respect. -/
noncomputable def Mdig (ε : ℝ) : ℕ := (D5 ε).norm.natAbs * (D13 ε).norm.natAbs

/-- The exponent budget of the interface: polynomial in `1/ε`. -/
noncomputable def Bd (ε : ℝ) : ℝ :=
  ((pA 5 ⌈1 / ε⌉₊ + 4 + pn 5 ⌈1 / ε⌉₊ + (pA 13 ⌈1 / ε⌉₊ + 4 + pn 13 ⌈1 / ε⌉₊) : ℕ) : ℝ)

/-- The digit rotations used by the interface. -/
noncomputable def Rots (ε : ℝ) : Finset ℂ :=
  digitRotFinset 5 (pn 5 ⌈1 / ε⌉₊ + 4) gQ ∪ digitRotFinset 13 (pn 13 ⌈1 / ε⌉₊ + 4) gP

lemma not_dvd_D5 (ε : ℝ) : ¬ gPb ∣ D5 ε := by
  intro h
  rcases prime_gPb.dvd_or_dvd h with h1 | h1
  · exact digitPrime_P.not_star_dvd_digitDen gP_not_dvd_gQ h1
  · exact gPb_not_dvd_gQb (prime_gPb.dvd_of_dvd_pow h1)

lemma not_dvd_D13 (ε : ℝ) : ¬ gQb ∣ D13 ε := by
  intro h
  rcases prime_gQb.dvd_or_dvd h with h1 | h1
  · exact digitPrime_Q.not_star_dvd_digitDen gQ_not_dvd_gP h1
  · exact gQb_not_dvd_gPb (prime_gQb.dvd_of_dvd_pow h1)

lemma D5_ne_zero (ε : ℝ) : D5 ε ≠ 0 := fun h => not_dvd_D5 ε (h ▸ dvd_zero _)

lemma D13_ne_zero (ε : ℝ) : D13 ε ≠ 0 := fun h => not_dvd_D13 ε (h ▸ dvd_zero _)

lemma Mdig_pos (ε : ℝ) : 0 < Mdig ε := by
  have h5 : 0 < (D5 ε).norm.natAbs :=
    Int.natAbs_pos.mpr fun h => D5_ne_zero ε (GaussianInt.norm_eq_zero.mp h)
  have h13 : 0 < (D13 ε).norm.natAbs :=
    Int.natAbs_pos.mpr fun h => D13_ne_zero ε (GaussianInt.norm_eq_zero.mp h)
  exact Nat.mul_pos h5 h13

lemma D5_dvd_of_Mdig_dvd {ε : ℝ} {q : GaussianInt} (h : ((Mdig ε : ℕ) : GaussianInt) ∣ q) :
    D5 ε ∣ q := by
  refine (dvd_natAbs_norm _).trans (dvd_trans ?_ h)
  unfold Mdig; push_cast
  exact dvd_mul_right _ _

lemma D13_dvd_of_Mdig_dvd {ε : ℝ} {q : GaussianInt} (h : ((Mdig ε : ℕ) : GaussianInt) ∣ q) :
    D13 ε ∣ q := by
  refine (dvd_natAbs_norm _).trans (dvd_trans ?_ h)
  unfold Mdig; push_cast
  exact dvd_mul_left _ _

/- ## The generic case with digit rotations -/

theorem case_core_digit {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp5 : 5 ≤ p)
    (hp13 : p ≤ 13) (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ)
    (hρ0 : ((star ρ : GaussianInt) : ℂ) ≠ 0) (hρn : (ρ.norm : ℝ) ≤ (p : ℝ) ^ 2)
    (hρn1 : 1 ≤ (ρ.norm : ℝ))
    (hordA : ∀ k, 2 ≤ k → orderOf (hπ.mult (star ρ) k) = (p - 1) * p ^ (k - 1))
    (hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
      orderOf (((hπ.mult ρ n).val : ℕ) : ZMod (p ^ ℓ)) = (p - 1) * p ^ (ℓ - 1))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) (w : ℂ) (q : GaussianInt) {N₀ a₁ b₁ a₂ b₂ v : ℕ}
    (ha₁ : a₁ ≤ N₀) (hb₁ : b₁ ≤ N₀) (ha₂ : a₂ ≤ N₀) (hb₂ : b₂ ≤ N₀) {q₂ : GaussianInt}
    (hq₂ : ¬ star π ∣ q₂)
    (hqeq : q = star π ^ v * DigitPrime.digitDen p (pn p ⌈1 / ε⌉₊ + 4) ρ *
      star ρ ^ pS p ⌈1 / ε⌉₊ * q₂)
    (hclose : ‖(q : ℂ) - (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ ≤ ηKL 100 ε / 10) :
    ∃ a b : ℕ, a ≤ N₀ + v + (pA p ⌈1 / ε⌉₊ + 4) + pn p ⌈1 / ε⌉₊ ∧ b ≤ N₀ + pS p ⌈1 / ε⌉₊ ∧
      ∃ μ ∈ digitRotFinset p (pn p ⌈1 / ε⌉₊ + 4) ρ,
      ∃ k : ℤ, |(((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b * μ * w).re - k| < ε := by
  set K := ⌈1 / ε⌉₊ with hK
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) (Nat.le_ceil (1 / ε))
    exact_mod_cast this
  have hn2 : 2 ≤ pn p K := by unfold pn; have := pℓ_ge p K; omega
  have hℓ1 : 1 ≤ pℓ p K := by have := pℓ_ge p K; omega
  -- the cell
  set g := cellGen π ρ (pn p K) (pα p K) (pS p K) with hg
  have hαA : pα p K + pA p K = pn p K := by unfold pα; have := pA_le_pn p K; omega
  have hglow : (1 / 5 : ℝ) ^ pA p K ≤ ‖g‖ := norm_cellGen_ge hπ hp13 hρn1 hαA
  have hηA := ηKL_le_five_pow_neg hp5 hp13 hε hε1
  have he' : ‖(((star π) ^ v * DigitPrime.digitDen p (pn p K + 4) ρ * (star ρ) ^ pS p K * q₂ :
        GaussianInt) : ℂ) -
      (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ < 21 / 50 * ‖g‖ := by
    rw [← hqeq]
    have hη0 : 0 < ηKL 100 ε := ηKL_pos 100 ε
    linarith
  have hgε : Real.sqrt 2 * ‖g‖ ≤ ε / 2 :=
    sqrt_two_mul_le (norm_nonneg _) hε (norm_cellGen_sq_le hπ hp5 hρn hε)
  have hH : 2 ≤ (pH K : ℝ) * ε ^ 2 := by
    have hKe : 1 / ε ≤ K := Nat.le_ceil _
    have h1 : 1 ≤ (K : ℝ) * ε := by
      calc (1 : ℝ) = (1 / ε) * ε := by field_simp
        _ ≤ K * ε := by gcongr
    unfold pH; push_cast; nlinarith
  have hHL : 25 * pH K ^ 3 < 4 * p ^ pL p K := pH_cube_lt p K hp5 hK1
  have hA4 := hordA (pn p K + 4) (by omega)
  rw [show pn p K + 4 - 1 = pn p K + 3 by omega] at hA4
  exact hπ.minor_arc_core_digit hp5 hρ1 hρ2 hρ0
    (n := pn p K) (α := pα p K) (β := pS p K) (A := pA p K) (L := pL p K) (ℓ := pℓ p K)
    (S := pS p K) (H := pH K) (pL_pos p K) rfl rfl le_rfl rfl rfl hA4
    (hordB (pn p K) (pℓ p K) hn2 hℓ1) hε hH hHL hgε w ha₁ hb₁ ha₂ hb₂ hq₂ he'

/- ## The interface -/

/-- **The minor-arc proposition with digit rotations.** Compared with `KL57With c`, the
condition `size5 q + size13 q ≤ δ` is replaced by `Mdig ε ∣ q`, and the rotation found is
`rot s t * μ` with `μ ∈ Rots ε` and `s, t ≤ N₀ + log₅ ϖ⁻¹ + Bd ε`. -/
def KL57D : Prop :=
  ∀ ε ϖ : ℝ, 0 < ε → ε < 1 / 10 → 0 < ϖ → ϖ < 1 / 10 →
    ∀ (N₀ s₁ t₁ s₂ t₂ : ℕ) (w : ℂ) (q : GaussianInt),
      s₁ ≤ N₀ → t₁ ≤ N₀ → s₂ ≤ N₀ → t₂ ≤ N₀ →
      ((Mdig ε : ℕ) : GaussianInt) ∣ q →
      2 * ϖ ≤ size5 q + size13 q →
      ‖(q : ℂ) - (rot s₁ t₁ - rot s₂ t₂) * w‖ ≤ ηKL 100 ε / 10 →
      ∃ s t : ℕ, (s : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + Bd ε ∧
        (t : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + Bd ε ∧ ∃ μ ∈ Rots ε, InStripe ε (rot s t * μ) w

theorem kl57D : KL57D := by
  intro ε ϖ hε0 hε1 hϖ0 hϖ1 N₀ s₁ t₁ s₂ t₂ w q hs₁ ht₁ hs₂ ht₂ hM hlow hclose
  have h5n := size5_nonneg q
  have h13n := size13_nonneg q
  have hq : q ≠ 0 := by
    rintro rfl
    simp only [size5, size13, ite_true] at hlow
    linarith
  have hlog0 : 0 ≤ Real.logb 5 ϖ⁻¹ :=
    Real.logb_nonneg (by norm_num) (by rw [le_inv_comm₀ one_pos hϖ0]; linarith)
  set K := ⌈1 / ε⌉₊ with hK
  have hBd5 : ((pA 5 K + 4 + pn 5 K : ℕ) : ℝ) ≤ Bd ε := by
    unfold Bd; rw [← hK]; exact_mod_cast Nat.le_add_right _ _
  have hBd13 : ((pA 13 K + 4 + pn 13 K : ℕ) : ℝ) ≤ Bd ε := by
    unfold Bd; rw [← hK]; exact_mod_cast Nat.le_add_left _ _
  by_cases h513 : size13 q ≤ size5 q
  · -- Case 1: digit prime `P`, multiplier `Q`.
    set v := multiplicity gPb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      rw [← size5_eq hq]; linarith
    have hcop : IsCoprime gPb (D5 ε) :=
      prime_gPb.irreducible.coprime_iff_not_dvd.mpr (not_dvd_D5 ε)
    obtain ⟨q₂, hq₂, hqeq⟩ := decomp_dvd prime_gPb hcop hq (D5_dvd_of_Mdig_dvd hM)
    have hqeq' : q = star gP ^ v * DigitPrime.digitDen 5 (pn 5 ⌈1 / ε⌉₊ + 4) gQ *
        star gQ ^ pS 5 ⌈1 / ε⌉₊ * q₂ := by
      rw [hqeq, D5, ← hv]; simp only [star_gP]; ring
    have hordA : ∀ k, 2 ≤ k →
        orderOf (digitPrime_P.mult (star gQ) k) = (5 - 1) * 5 ^ (k - 1) := by
      intro k hk
      have : NeZero (5 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_P_Qb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_P.mult gQ n).val : ℕ) : ZMod (5 ^ ℓ)) = (5 - 1) * 5 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_P_Q hn hℓ
    obtain ⟨a, b, ha, hb, μ, hμ, k, hk⟩ := case_core_digit digitPrime_P le_rfl (by norm_num)
      gP_not_dvd_gQ gP_not_dvd_gQb gQb_ne_zero (by rw [norm_gQ]; norm_num)
      (by rw [norm_gQ]; norm_num) hordA hordB hε0 hε1 w q hs₁ ht₁ hs₂ ht₂ hq₂ hqeq' hclose
    rw [← hK] at ha hb
    have hSA : pS 5 K ≤ pA 5 K + 4 + pn 5 K := by unfold pA; omega
    refine ⟨a, b, ?_, ?_, μ, Finset.mem_union_left _ hμ, k, hk⟩
    · have h1 : (a : ℝ) ≤ N₀ + v + ((pA 5 K + 4 + pn 5 K : ℕ) : ℝ) := by
        have : a ≤ N₀ + v + (pA 5 K + 4 + pn 5 K) := by omega
        exact_mod_cast this
      linarith
    · have h1 : (b : ℝ) ≤ N₀ + ((pA 5 K + 4 + pn 5 K : ℕ) : ℝ) := by
        have : b ≤ N₀ + (pA 5 K + 4 + pn 5 K) := by omega
        exact_mod_cast this
      linarith
  · -- Case 2: digit prime `Q`, multiplier `P`.
    push Not at h513
    set v := multiplicity gQb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      have h1 : ϖ ≤ size13 q := by linarith
      rw [size13_eq hq] at h1
      have h2 : (13 : ℝ) ^ (-(v : ℝ)) ≤ (5 : ℝ) ^ (-(v : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
        apply inv_anti₀ (by positivity)
        exact Real.rpow_le_rpow (by norm_num) (by norm_num) (Nat.cast_nonneg _)
      linarith
    have hcop : IsCoprime gQb (D13 ε) :=
      prime_gQb.irreducible.coprime_iff_not_dvd.mpr (not_dvd_D13 ε)
    obtain ⟨q₂, hq₂, hqeq⟩ := decomp_dvd prime_gQb hcop hq (D13_dvd_of_Mdig_dvd hM)
    have hqeq' : q = star gQ ^ v * DigitPrime.digitDen 13 (pn 13 ⌈1 / ε⌉₊ + 4) gP *
        star gP ^ pS 13 ⌈1 / ε⌉₊ * q₂ := by
      rw [hqeq, D13, ← hv]; simp only [star_gQ]; ring
    have hordA : ∀ k, 2 ≤ k →
        orderOf (digitPrime_Q.mult (star gP) k) = (13 - 1) * 13 ^ (k - 1) := by
      intro k hk
      have : NeZero (13 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_Q_Pb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordB : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_Q.mult gP n).val : ℕ) : ZMod (13 ^ ℓ)) =
          (13 - 1) * 13 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_Q_P hn hℓ
    have hrot : ∀ s t : ℕ, rot s t = ((gQ : ℂ) / ((star gQ : GaussianInt) : ℂ)) ^ t *
        ((gP : ℂ) / ((star gP : GaussianInt) : ℂ)) ^ s := by
      intro s t; unfold rot θ5 θ13; rw [star_gP, star_gQ]; ring
    rw [hrot s₁ t₁, hrot s₂ t₂] at hclose
    obtain ⟨a, b, ha, hb, μ, hμ, k, hk⟩ := case_core_digit digitPrime_Q (by norm_num) le_rfl
      gQ_not_dvd_gP gQ_not_dvd_gPb gPb_ne_zero (by rw [norm_gP]; norm_num)
      (by rw [norm_gP]; norm_num) hordA hordB hε0 hε1 w q ht₁ hs₁ ht₂ hs₂ hq₂ hqeq' hclose
    rw [← hK] at ha hb
    have hSA : pS 13 K ≤ pA 13 K + 4 + pn 13 K := by unfold pA; omega
    refine ⟨b, a, ?_, ?_, μ, Finset.mem_union_right _ hμ, k, ?_⟩
    · have h1 : (b : ℝ) ≤ N₀ + ((pA 13 K + 4 + pn 13 K : ℕ) : ℝ) := by
        have : b ≤ N₀ + (pA 13 K + 4 + pn 13 K) := by omega
        exact_mod_cast this
      linarith
    · have h1 : (a : ℝ) ≤ N₀ + v + ((pA 13 K + 4 + pn 13 K : ℕ) : ℝ) := by
        have : a ≤ N₀ + v + (pA 13 K + 4 + pn 13 K) := by omega
        exact_mod_cast this
      linarith
    · rw [hrot b a]
      exact hk

end Green41

/- ## Section: `AssemblyDigit` -/

/-
# Assembling the covering with digit rotations

The structure is that of `Assembly` and `Estimates` in the double-exponential part, with three
changes.

* The pigeonhole modulus is `Mdig ε` instead of `5^u 13^v`; the condition on `δ` is gone.
* `G ≥ max(20/η, Mdig ε, 1/ε, Bd ε) + 66`, so that `Mdig ε ≤ G` and `K = G⁴` still works.
* The orbit is `Θ = {rot s t * μ : s, t ≤ T, μ ∈ Rots ε}`, so the count gains a factor
  `|Rots ε|`: `minCopies ε ≤ |Rots ε| · G^88`.
-/

namespace Green41


open Complex ComplexConjugate

/- ## Digit rotations have norm one -/

lemma digitInt_ne_zero (p k : ℕ) : digitInt p k ≠ 0 := by
  intro h
  have := congrArg Zsqrtd.re h
  simp [digitInt] at this

lemma ne_zero_of_mem_digitFamilyFinset {p N : ℕ} {ρ A : GaussianInt} (hρ : ρ ≠ 0)
    (hA : A ∈ digitFamilyFinset p N ρ) : A ≠ 0 := by
  obtain ⟨md, -, rfl⟩ := Finset.mem_image.mp hA
  exact mul_ne_zero (pow_ne_zero _ hρ)
    (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (digitInt_ne_zero _ _))

lemma norm_of_mem_digitRotFinset {p N : ℕ} {ρ : GaussianInt} (hρ : ρ ≠ 0) {μ : ℂ}
    (hμ : μ ∈ digitRotFinset p N ρ) : ‖μ‖ = 1 := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hμ
  have hA0 := ne_zero_of_mem_digitFamilyFinset hρ hA
  apply DigitPrime.norm_rotOf
  exact toComplex_ne_zero_of_norm (by
    rw [Zsqrtd.norm_conj]; exact fun h => hA0 (GaussianInt.norm_eq_zero.mp h))

lemma gP_ne_zero' : gP ≠ 0 := by decide

lemma gQ_ne_zero' : gQ ≠ 0 := by decide

lemma norm_of_mem_Rots {ε : ℝ} {μ : ℂ} (hμ : μ ∈ Rots ε) : ‖μ‖ = 1 := by
  unfold Rots at hμ
  rcases Finset.mem_union.mp hμ with h | h
  · exact norm_of_mem_digitRotFinset gQ_ne_zero' h
  · exact norm_of_mem_digitRotFinset gP_ne_zero' h

lemma one_mem_digitRotFinset {p N : ℕ} (hp : 2 ≤ p) (ρ : GaussianInt) :
    (1 : ℂ) ∈ digitRotFinset p N ρ := by
  refine Finset.mem_image.mpr ⟨1, Finset.mem_image.mpr ⟨(0, fun _ => 0), ?_, ?_⟩, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show 0 < p - 1 by omega),
      Fintype.mem_piFinset.mpr fun _ => Finset.mem_range.mpr (show 0 < p by omega)⟩
  · simp
  · simp

lemma one_le_card_Rots (ε : ℝ) : 1 ≤ (Rots ε).card :=
  Finset.card_pos.mpr ⟨1, Finset.mem_union_left _ (one_mem_digitRotFinset (by norm_num) _)⟩

/- ## Confinement -/

/-- The confinement lemma, from `KL57D`. -/
theorem confinement_digit (hKL : KL57D) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 10)
    {K G h T : ℕ} (hGη : 20 / ηKL 100 ε ≤ G) (hG2 : 2 ≤ G)
    (hK : Mdig ε ^ 2 * G ^ 2 < (K + 1) ^ 2) (hh : 1 ≤ h)
    (hT : (K : ℝ) + Real.logb 5 (2 * 13 ^ h) + Bd ε ≤ T) (w : ℂ)
    (hw : ∀ s t : ℕ, s ≤ T → t ≤ T → ∀ μ ∈ Rots ε, ¬ InStripe ε (rot s t * μ) w) :
    ∃ k : GaussianInt, ‖w - (gD h : ℂ) / (commonDen K : ℂ) * k‖ ≤ Real.sqrt 65 ^ K := by
  have hG0 : 0 < G := by omega
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG0
  obtain ⟨p, hp, hbox⟩ := pigeonhole (Mdig_pos ε) hG0 hK w
  obtain ⟨hMdvd, hclose⟩ := box_eq_consequences hG0 hbox
  set x := rot p.1.1 p.1.2 * w
  set y := rot p.2.1 p.2.2 * w
  set q : GaussianInt := gRound x - gRound y
  have hxy : x - y = (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w := by simp only [x, y]; ring
  have hq_close : ‖(q : ℂ) - (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w‖ < 2 / G := by
    rw [← hxy]; exact hclose
  have hη := ηKL_pos 100 ε
  by_cases hbig : 1 / (13 : ℝ) ^ h ≤ size5 q + size13 q
  · -- the minor-arc proposition applies and covers `w`: contradiction
    exfalso
    have hp' := hp
    simp only [labelPairs, Finset.mem_filter, Finset.mem_product, mem_labels] at hp'
    set ϖ : ℝ := 1 / (2 * 13 ^ h) with hϖ
    have hϖ0 : 0 < ϖ := by positivity
    have hϖ1 : ϖ < 1 / 10 := by
      rw [hϖ]
      have : (13 : ℝ) ≤ 13 ^ h := by
        calc (13 : ℝ) = 13 ^ 1 := by ring
          _ ≤ 13 ^ h := pow_le_pow_right₀ (by norm_num) hh
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2ϖ : 2 * ϖ ≤ size5 q + size13 q := by
      rw [hϖ]
      calc 2 * (1 / (2 * (13 : ℝ) ^ h)) = 1 / 13 ^ h := by field_simp
        _ ≤ _ := hbig
    have hcloseη : ‖(q : ℂ) - (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w‖ ≤ ηKL 100 ε / 10 := by
      have : 2 / (G : ℝ) ≤ ηKL 100 ε / 10 := by
        rw [div_le_iff₀ hGr]
        rw [div_le_iff₀ hη] at hGη
        linarith
      linarith
    obtain ⟨s, t, hs, ht, μ, hμ, hst⟩ := hKL ε ϖ hε0 hε1 hϖ0 hϖ1 K p.1.1 p.1.2 p.2.1 p.2.2 w q
      hp'.1.1.1 hp'.1.1.2 hp'.1.2.1 hp'.1.2.2 hMdvd h2ϖ hcloseη
    have hlog : Real.logb 5 ϖ⁻¹ = Real.logb 5 (2 * 13 ^ h) := by
      rw [hϖ, one_div, inv_inv]
    rw [hlog] at hs ht
    have hsT : s ≤ T := by exact_mod_cast hs.trans hT
    have htT : t ≤ T := by exact_mod_cast ht.trans hT
    exact hw s t hsT htT μ hμ hst
  · -- `D_h ∣ q`, and the common denominator places `w` near the lattice
    push Not at hbig
    obtain ⟨k₁, hk₁⟩ := gD_dvd_of_size_lt hbig
    obtain ⟨cr, hcr⟩ := commonDen_div hp
    refine ⟨cr * k₁, ?_⟩
    have hr0 : rot p.1.1 p.1.2 - rot p.2.1 p.2.2 ≠ 0 := by
      intro h0
      have := norm_rot_sub_ge hp
      rw [h0, norm_zero] at this
      have : (0 : ℝ) < 1 / Real.sqrt 65 ^ K := by positivity
      linarith
    have hL0 : (commonDen K : ℂ) ≠ 0 := by exact_mod_cast (commonDen_pos K).ne'
    set rr := rot p.1.1 p.1.2 - rot p.2.1 p.2.2 with hrr
    have hkey : w - (gD h : ℂ) / (commonDen K : ℂ) * ((cr * k₁ : GaussianInt) : ℂ) =
        -(((q : ℂ) - rr * w) / rr) := by
      have hq' : (q : ℂ) = (gD h : ℂ) * (k₁ : ℂ) := by
        rw [hk₁, GaussianInt.toComplex_mul]
      have hcr0 : (cr : ℂ) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hcr
        exact hL0 hcr.symm
      rw [GaussianInt.toComplex_mul, hq', ← hcr]
      field_simp
      ring
    rw [hkey, norm_neg, norm_div]
    have hrr_ge := norm_rot_sub_ge hp
    have hrr_pos : 0 < ‖rr‖ := norm_pos_iff.mpr hr0
    rw [div_le_iff₀ hrr_pos]
    have hsq : 0 < Real.sqrt 65 ^ K := by positivity
    have h1 : 1 ≤ Real.sqrt 65 ^ K * ‖rr‖ := by
      rw [div_le_iff₀ hsq] at hrr_ge
      linarith
    have h2 : 2 / (G : ℝ) ≤ 1 := by
      rw [div_le_one hGr]; exact_mod_cast hG2
    calc ‖(q : ℂ) - rr * w‖ ≤ 2 / G := hq_close.le
      _ ≤ 1 := h2
      _ ≤ Real.sqrt 65 ^ K * ‖rr‖ := h1

/- ## Parameters -/

section ParamsD

variable (ε : ℝ)

/-- `max(20/η, Mdig, 1/ε, Bd)`. -/
noncomputable def X0D : ℝ := max (max (20 / ηKL 100 ε) (Mdig ε : ℝ)) (max (1 / ε) (Bd ε))
/-- The pigeonhole resolution `G`. -/
noncomputable def GpD : ℕ := ⌈X0D ε⌉₊ + 66
/-- `K = G⁴`. -/
noncomputable def KpD : ℕ := GpD ε ^ 4
/-- The common denominator `L`. -/
noncomputable def LpD : ℕ := commonDen (KpD ε)
/-- `H = √65^K`. -/
noncomputable def HpD : ℝ := Real.sqrt 65 ^ KpD ε
/-- `R = 2LH + 16`. -/
noncomputable def RpD : ℝ := 2 * LpD ε * HpD ε + 16
/-- `Q = 128R/ε + 4`. -/
noncomputable def QpD : ℝ := 128 * RpD ε / ε + 4
/-- `h` with `|D_h| > 2LHQ`. -/
noncomputable def hpD : ℕ := 2 * Nat.clog 65 (⌈2 * (LpD ε : ℝ) * HpD ε * QpD ε⌉₊ + 1)
/-- `T = ⌈K + log₅(2·13^h) + Bd⌉`. -/
noncomputable def TpD : ℕ := ⌈(KpD ε : ℝ) + Real.logb 5 (2 * 13 ^ hpD ε) + Bd ε⌉₊
/-- The orbit rotations `rot s t * μ`, `s, t ≤ T`, `μ ∈ Rots ε`. -/
noncomputable def ΘpD : Finset ℂ := by
  classical
  exact ((labels (TpD ε)) ×ˢ (Rots ε)).image (fun x => rot x.1.1 x.1.2 * x.2)
/-- The final rotation set. -/
noncomputable def ΩpD : Finset ℂ := endgameSet (ΘpD ε) (discSet ε (RpD ε)) (LpD ε)

end ParamsD

section BoundsD

variable {ε : ℝ}

lemma X0D_ge :
    20 / ηKL 100 ε ≤ X0D ε ∧ (Mdig ε : ℝ) ≤ X0D ε ∧ 1 / ε ≤ X0D ε ∧ Bd ε ≤ X0D ε := by
  unfold X0D
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

lemma GpD_ge : X0D ε ≤ GpD ε ∧ 66 ≤ GpD ε := by
  constructor
  · unfold GpD; push_cast
    have := Nat.le_ceil (X0D ε)
    linarith
  · unfold GpD; omega

lemma Mdig_le_GpD : Mdig ε ≤ GpD ε := by
  have h1 := (X0D_ge (ε := ε)).2.1
  have h2 := (GpD_ge (ε := ε)).1
  exact_mod_cast h1.trans h2

lemma hK_paramD : Mdig ε ^ 2 * GpD ε ^ 2 < (KpD ε + 1) ^ 2 := by
  have hM := Mdig_le_GpD (ε := ε)
  have hG := (GpD_ge (ε := ε)).2
  unfold KpD
  set G := GpD ε
  have h1 : Mdig ε ^ 2 * G ^ 2 ≤ G ^ 2 * G ^ 2 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM 2)
  have h4 : 1 ≤ G ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : G ^ 2 * G ^ 2 < (G ^ 4 + 1) ^ 2 := by
    have : G ^ 2 * G ^ 2 = G ^ 4 := by ring
    rw [this]
    nlinarith
  omega

lemma HpD_ge_one : 1 ≤ HpD ε := by
  unfold HpD
  exact one_le_pow₀ (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)

lemma LpD_pos : 0 < LpD ε := commonDen_pos _

lemma RpD_ge : 16 ≤ RpD ε ∧ 2 * (LpD ε : ℝ) * HpD ε ≤ RpD ε := by
  unfold RpD
  have h1 : (0 : ℝ) ≤ 2 * LpD ε * HpD ε := by
    have := HpD_ge_one (ε := ε)
    positivity
  constructor <;> linarith

lemma hpD_spec (hε : 0 < ε) : 1 ≤ hpD ε ∧
    2 * (LpD ε : ℝ) * HpD ε * QpD ε < ‖(gD (hpD ε) : ℂ)‖ := by
  set X := 2 * (LpD ε : ℝ) * HpD ε * QpD ε with hX
  have hXpos : 0 < X := by
    have hL : (0 : ℝ) < LpD ε := by exact_mod_cast LpD_pos
    have hH := HpD_ge_one (ε := ε)
    have hQ : 0 < QpD ε := by
      unfold QpD
      have := (RpD_ge (ε := ε)).1
      positivity
    rw [hX]; positivity
  have hceil : 1 ≤ ⌈X⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
  set m := Nat.clog 65 (⌈X⌉₊ + 1) with hm
  have hm1 : 0 < m := Nat.clog_pos (by norm_num) (by omega)
  constructor
  · unfold hpD; rw [← hm]; omega
  · rw [cnorm_gD]
    unfold hpD
    rw [← hm, pow_mul, Real.sq_sqrt (by norm_num)]
    have h1 : ⌈X⌉₊ + 1 ≤ 65 ^ m := Nat.le_pow_clog (by norm_num) _
    have h2 : X < ⌈X⌉₊ + 1 := by
      have := Nat.le_ceil X; linarith
    have h3 : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ ((65 ^ m : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith

end BoundsD

/-- The covering assembled from the confinement lemma, the disc cover and the end game. -/
theorem minCopies_le_paramD {ε : ℝ} (hKL : KL57D) (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    (minCopies ε : ℝ) ≤
      (2 * ((TpD ε : ℝ) + 1) ^ 2 * (Rots ε).card + 1) * (discSet ε (RpD ε)).card := by
  classical
  obtain ⟨hX20, _, _, _⟩ := X0D_ge (ε := ε)
  obtain ⟨hGX, hG66⟩ := GpD_ge (ε := ε)
  obtain ⟨hR16, hRLH⟩ := RpD_ge (ε := ε)
  obtain ⟨hh1, hD⟩ := hpD_spec hε
  obtain ⟨hU1, hU2, hU3, _⟩ := disc_cover hε hε1 hR16
  have hGr : (66 : ℝ) ≤ GpD ε := by exact_mod_cast hG66
  -- confinement for the orbit `Θ`
  have hconf : ∀ w : ℂ, (∀ θ ∈ ΘpD ε, ¬ InStripe ε θ w) →
      ∃ k : GaussianInt, ‖w - (gD (hpD ε) : ℂ) / (LpD ε : ℂ) * k‖ ≤ HpD ε := by
    intro w hw
    have hw' : ∀ s t : ℕ, s ≤ TpD ε → t ≤ TpD ε → ∀ μ ∈ Rots ε,
        ¬ InStripe ε (rot s t * μ) w := by
      intro s t hs ht μ hμ
      apply hw
      unfold ΘpD
      exact Finset.mem_image.mpr ⟨((s, t), μ),
        Finset.mem_product.mpr ⟨mem_labels.mpr ⟨hs, ht⟩, hμ⟩, rfl⟩
    exact confinement_digit hKL hε hε1 (by linarith) (by omega) hK_paramD hh1 (Nat.le_ceil _) w
      hw'
  -- the end game
  have hcov : ∀ z : ℂ, ∃ v ∈ ΩpD ε, InStripe ε v z := by
    intro z
    unfold ΩpD
    refine endgame_cover (Q := QpD ε) LpD_pos (ΘpD ε) (discSet ε (RpD ε)) hconf ?_ hU1 ?_ hD z
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hU2 p hp
      exact ⟨h1, h2, by unfold QpD; exact h3⟩
    · intro e he
      exact hU3 e (he.trans hRLH)
  have hunit : ∀ v ∈ ΩpD ε, ‖v‖ = 1 := by
    unfold ΩpD
    refine norm_of_mem_endgameSet LpD_pos ?_ ?_
    · intro θ hθ
      unfold ΘpD at hθ
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hθ
      rw [norm_mul, norm_rot, one_mul]
      exact norm_of_mem_Rots (Finset.mem_product.mp hx).2
    · intro p hp
      obtain ⟨h1, h2, _⟩ := hU2 p hp
      exact ⟨h1, h2⟩
  have hmin := minCopies_le_of_cover (ΩpD ε) hunit hcov
  have hcard := card_endgameSet_le (ΘpD ε) (discSet ε (RpD ε)) (LpD ε)
  have hΘ : (ΘpD ε).card ≤ (TpD ε + 1) ^ 2 * (Rots ε).card := by
    unfold ΘpD
    exact Finset.card_image_le.trans (by rw [Finset.card_product, card_labels])
  have h1 : (minCopies ε : ℝ) ≤ (ΩpD ε).card := by exact_mod_cast hmin
  have h2 : ((ΩpD ε).card : ℝ) ≤
      2 * (ΘpD ε).card * (discSet ε (RpD ε)).card + (discSet ε (RpD ε)).card := by
    unfold ΩpD; exact_mod_cast hcard
  have h3 : ((ΘpD ε).card : ℝ) ≤ ((TpD ε : ℝ) + 1) ^ 2 * (Rots ε).card := by
    exact_mod_cast hΘ
  have hU0 : (0 : ℝ) ≤ (discSet ε (RpD ε)).card := by positivity
  calc (minCopies ε : ℝ) ≤ (ΩpD ε).card := h1
    _ ≤ 2 * (ΘpD ε).card * (discSet ε (RpD ε)).card + (discSet ε (RpD ε)).card := h2
    _ ≤ 2 * (((TpD ε : ℝ) + 1) ^ 2 * (Rots ε).card) * (discSet ε (RpD ε)).card +
          (discSet ε (RpD ε)).card := by gcongr
    _ = (2 * ((TpD ε : ℝ) + 1) ^ 2 * (Rots ε).card + 1) * (discSet ε (RpD ε)).card := by ring

/- ## Estimates -/

section EstimatesD

variable {ε : ℝ}

/-- `B = (K+1)^5`. -/
noncomputable def BpD (ε : ℝ) : ℕ := (KpD ε + 1) ^ 5

lemma one_le_BpD : 1 ≤ BpD ε := by unfold BpD; exact Nat.one_le_pow _ _ (by omega)

lemma KpD_le_BpD : KpD ε ≤ BpD ε := by
  unfold BpD
  calc KpD ε ≤ KpD ε + 1 := Nat.le_succ _
    _ = (KpD ε + 1) ^ 1 := (pow_one _).symm
    _ ≤ (KpD ε + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)

lemma GpD_le_KpD : GpD ε ≤ KpD ε := by
  unfold KpD
  have hG := (GpD_ge (ε := ε)).2
  calc GpD ε = GpD ε ^ 1 := (pow_one _).symm
    _ ≤ GpD ε ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)

lemma GpD_le_BpD : GpD ε ≤ BpD ε := GpD_le_KpD.trans KpD_le_BpD

lemma LpD_le : (LpD ε : ℝ) ≤ 65 ^ BpD ε := by
  have h1 := commonDen_le (KpD ε)
  have h2 : 4 * 65 ^ KpD ε ≤ 65 ^ (KpD ε + 1) := by rw [pow_succ]; omega
  have h3 : (4 * 65 ^ KpD ε) ^ ((KpD ε + 1) ^ 4) ≤ 65 ^ BpD ε := by
    calc (4 * 65 ^ KpD ε) ^ ((KpD ε + 1) ^ 4) ≤ (65 ^ (KpD ε + 1)) ^ ((KpD ε + 1) ^ 4) :=
          Nat.pow_le_pow_left h2 _
      _ = 65 ^ BpD ε := by rw [← pow_mul, BpD]; ring_nf
  have h4 : LpD ε ≤ 65 ^ BpD ε := by unfold LpD; exact h1.trans h3
  exact_mod_cast h4

lemma HpD_le : HpD ε ≤ 65 ^ BpD ε := by
  unfold HpD
  have h1 : Real.sqrt 65 ≤ 65 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc Real.sqrt 65 ^ KpD ε ≤ 65 ^ KpD ε := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 _
    _ ≤ 65 ^ BpD ε := pow_le_pow_right₀ (by norm_num) KpD_le_BpD

lemma RpD_le : RpD ε ≤ 65 ^ (2 * BpD ε + 1) := by
  unfold RpD
  have hL := LpD_le (ε := ε)
  have hH := HpD_le (ε := ε)
  have hH0 : 0 ≤ HpD ε := le_trans zero_le_one HpD_ge_one
  have hpow : (65 : ℝ) ^ (2 * BpD ε + 1) = 65 * (65 ^ BpD ε * 65 ^ BpD ε) := by
    rw [pow_succ, two_mul, pow_add]; ring
  have h1 : (1 : ℝ) ≤ 65 ^ BpD ε := one_le_pow₀ (by norm_num)
  have h2 : 2 * (LpD ε : ℝ) * HpD ε ≤ 2 * (65 ^ BpD ε * 65 ^ BpD ε) := by
    have : (LpD ε : ℝ) * HpD ε ≤ 65 ^ BpD ε * 65 ^ BpD ε := by
      apply mul_le_mul hL hH hH0 (by positivity)
    nlinarith
  rw [hpow]
  nlinarith

lemma inv_ε_leD : 1 / ε ≤ BpD ε := by
  obtain ⟨_, _, h1, _⟩ := X0D_ge (ε := ε)
  have h2 := (GpD_ge (ε := ε)).1
  have h3 : (GpD ε : ℝ) ≤ BpD ε := by exact_mod_cast GpD_le_BpD
  linarith

lemma Bd_leD : Bd ε ≤ BpD ε := by
  obtain ⟨_, _, _, h1⟩ := X0D_ge (ε := ε)
  have h2 := (GpD_ge (ε := ε)).1
  have h3 : (GpD ε : ℝ) ≤ BpD ε := by exact_mod_cast GpD_le_BpD
  linarith

lemma Bd_nonneg : 0 ≤ Bd ε := by unfold Bd; positivity

lemma QpD_le (hε : 0 < ε) : QpD ε ≤ 65 ^ (3 * BpD ε + 3) := by
  have h := Q_le_aux (B := BpD ε) (RpD_le (ε := ε))
    (by linarith [(RpD_ge (ε := ε)).1]) (inv_ε_leD (ε := ε)) (by positivity)
  unfold QpD
  calc 128 * RpD ε / ε + 4 = 128 * RpD ε * (1 / ε) + 4 := by ring
    _ ≤ _ := h

lemma QpD_nonneg (hε : 0 < ε) : 0 ≤ QpD ε := by
  unfold QpD; have := (RpD_ge (ε := ε)).1; positivity

lemma XD_le (hε : 0 < ε) :
    2 * (LpD ε : ℝ) * HpD ε * QpD ε ≤ 65 ^ (5 * BpD ε + 4) :=
  X_le_aux LpD_le HpD_le (QpD_le hε) (by positivity) (le_trans zero_le_one HpD_ge_one)
    (QpD_nonneg hε)

lemma hpD_le (hε : 0 < ε) : hpD ε ≤ 10 * BpD ε + 10 := by
  have hX0 : 0 ≤ 2 * (LpD ε : ℝ) * HpD ε * QpD ε := by
    have hH0 : 0 ≤ HpD ε := le_trans zero_le_one HpD_ge_one
    have hQ0 := QpD_nonneg hε
    positivity
  have h := clog_aux hX0 (XD_le hε)
  unfold hpD
  omega

lemma TpD_le (hε : 0 < ε) : (TpD ε : ℝ) ≤ 44 * BpD ε := by
  unfold TpD
  exact T_le_aux KpD_le_BpD (hpD_le hε) Bd_nonneg Bd_leD one_le_BpD

lemma card_discSet_leD (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    ((discSet ε (RpD ε)).card : ℝ) ≤ 2200 * (BpD ε : ℝ) ^ 2 := by
  obtain ⟨_, _, _, hcard⟩ := disc_cover hε hε1 (RpD_ge (ε := ε)).1
  exact hcard.trans (U_le_aux one_le_BpD hε inv_ε_leD (RpD_ge (ε := ε)).1 RpD_le)

lemma BpD_le_G (ε : ℝ) : BpD ε ≤ 32 * GpD ε ^ 20 := by
  have hG := (GpD_ge (ε := ε)).2
  unfold BpD KpD
  calc (GpD ε ^ 4 + 1) ^ 5 ≤ (2 * GpD ε ^ 4) ^ 5 := by
        apply Nat.pow_le_pow_left
        have : 1 ≤ GpD ε ^ 4 := Nat.one_le_pow _ _ (by omega)
        omega
    _ = 32 * GpD ε ^ 20 := by ring

/-- `minCopies ε ≤ |Rots ε| · G^88`. -/
theorem minCopies_le_Rots_G_pow (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    (minCopies ε : ℝ) ≤ (Rots ε).card * (GpD ε : ℝ) ^ 88 := by
  set U : ℝ := ((discSet ε (RpD ε)).card : ℝ) with hU
  set T : ℝ := (TpD ε : ℝ) with hT
  set R : ℝ := ((Rots ε).card : ℝ) with hR
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; exact_mod_cast one_le_card_Rots ε
  have hU0 : 0 ≤ U := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hm := minCopies_le_paramD kl57D hε hε1
  have hkey : (2 * (T + 1) ^ 2 + 1) * U ≤ (GpD ε : ℝ) ^ 88 :=
    final_aux (GpD_ge (ε := ε)).2 (BpD_le_G ε) one_le_BpD le_rfl (TpD_le hε) hT0
      (card_discSet_leD hε hε1) hU0
  calc (minCopies ε : ℝ) ≤ (2 * (T + 1) ^ 2 * R + 1) * U := hm
    _ ≤ R * ((2 * (T + 1) ^ 2 + 1) * U) := by nlinarith [sq_nonneg (T + 1)]
    _ ≤ R * (GpD ε : ℝ) ^ 88 := by gcongr

end EstimatesD

end Green41

/- ## Section: `FinalSingle` -/

/-
# The single-exponential bound

`minCopies_le_Rots_G_pow` gives `minCopies ε ≤ |Rots ε| · G^88`. With `u = 1/ε` and
`W = (n₅ + 4) + (n₁₃ + 4) ≤ 5 u^100`:

* `|Rots ε| ≤ 16^(W+1)`,
* `Mdig ε ≤ 2^(144 W²)` (the digit denominators have norm `2^{O(n²)}`),
* `20/η = 20 · 5^(u^100)`, `Bd ε ≤ 2W`, `1/ε = u`,

so `G ≤ exp(4000 u^200 + 68)` and `minCopies ε ≤ exp(400000 u^200) ≤ exp(u^201)` once
`u ≥ 400000`.
-/

namespace Green41

open Finset

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
          prod_le_prod₀ (fun j _ => by positivity) hfac
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

/-- The Formal Conjectures-style statement with the answer `True`. -/
theorem green_41.variants.single_exponential_bound : True ↔
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, (minCopies ε : ℝ) ≤ Real.exp (ε ^ (-C)) :=
  ⟨fun _ => singleExponentialBound, fun _ => trivial⟩

#print axioms green_41.variants.single_exponential_bound

end Green41

/- ## Section: `DiscreteGen` -/

/-
# The discrete core for an arbitrary family of multipliers

`Green41.discrete_core` uses the multipliers `Bʷ`, `w < (p - 1) p^(ℓ-1)`, but its proof only
needs two facts about them: they are pairwise distinct modulo `N = p^ℓ`, and there are at least
`4N/5` of them. `discrete_core_gen` states the discrete core for any finite family `M i`,
`i ∈ I`, with these two properties. The proof is the same Fejér-kernel argument.
-/

namespace Green41


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
      rw [hX, ite_eq_left rfl]
      have hre : ((S : ℂ) * (Y.card : ℂ)).re = (S : ℝ) * Y.card := by
        rw [← Nat.cast_mul, Complex.natCast_re, Nat.cast_mul]
      rw [hre]; linarith
    · simp only [haa, ite_false, zero_sub]
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
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, ite_eq_left ha, Finset.sum_const, card_range,
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

end Green41

/- ## Section: `CellGen` -/

/-
# Cells with a general denominator

The cell generator of the double-exponential part is `g = π̄^α ρ̄^β / πⁿ`. The factor `ρ̄^β` is
there so that the rotations `(ρ/ρ̄)^w`, `w ≤ β`, used by the discrete core keep the cell
lattice. For other families of rotations `C/C̄` we only need `C̄` to divide the denominator.
This file redoes the cell machinery with `ρ̄^β` replaced by an arbitrary Gaussian integer `D`:

* `cellGenD π D n α = π̄^α D / πⁿ` and the labels `labelD`;
* the label count `pow_le_four_mul_card_sqD`;
* Step A for a multiplier family, `stepA_familyD`;
* the stripe value of a label after a rotation `C/C̄` with `C̄ ∣ D`, `re_label_formulaD`.
-/

namespace Green41


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

end Green41

/- ## Section: `DigitCast` -/

/-
# Digit multipliers read modulo a lower power

In the discrete core the multiplier of a rotation is computed in `ZMod (pⁿ)` (where the labels
live) and then only its residue modulo `p^ℓ`, `ℓ ≤ n`, matters. `exists_digit_multiplier_cast`
shows that the digit family at level `ℓ` reaches every unit modulo `p^ℓ` in this sense. The proof
reruns the digit cover in `ZMod (p^ℓ)` on the images of the level-`n` multipliers; the
first-order shape `1 + p^k (unit) + p^(k+1) (·)` of a digit survives the reduction.

The rotations used are the inverses `Ā/A` of the digit rotations, whose numerators `Ā` have
multiplier `mult (star A)`; `digitRotInvFinset` collects them.
-/

namespace Green41

open Green41SingleExponential

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

end Green41

/- ## Section: `MinorArcQuasi` -/

/-
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

namespace Green41


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

end Green41

/- ## Section: `AssemblyGen` -/

/-
# The assembly for an arbitrary minor-arc interface

`AssemblyDigit` turns the interface `KL57D` into `minCopies ε ≤ |Rots ε| · G^88`. The argument
uses only a few properties of the data in the interface: the tolerance `η ε > 0`, the modulus
`M ε > 0` that `q` must be divisible by, the exponent budget `Bd ε ≥ 0`, and the extra
rotations `Rots ε` (of norm one, at least one of them). `ArcData` bundles these, `ArcData.KL`
is the interface, and `ArcData.minCopies_le_Rots_G_pow` is the assembled bound with
`G = ⌈max(20/η, M, 1/ε, Bd)⌉ + 66`.
-/

namespace Green41


open Complex ComplexConjugate

/-- The data that a minor-arc proposition hands to the assembly. -/
structure ArcData where
  /-- The closeness tolerance. -/
  η : ℝ → ℝ
  /-- The modulus that `q` must be divisible by. -/
  M : ℝ → ℕ
  /-- The exponent budget. -/
  Bd : ℝ → ℝ
  /-- The extra rotations. -/
  Rots : ℝ → Finset ℂ
  η_pos : ∀ ε, 0 < η ε
  M_pos : ∀ ε, 0 < M ε
  Bd_nonneg : ∀ ε, 0 ≤ Bd ε
  norm_rots : ∀ ε, ∀ μ ∈ Rots ε, ‖μ‖ = 1
  card_rots : ∀ ε, 1 ≤ (Rots ε).card

namespace ArcData

variable (d : ArcData)

/-- The minor-arc interface for the data `d`: if `q` is divisible by `M ε`, has
`P̄`- or `Q̄`-adic size at least `ϖ`, and is `η ε / 10`-close to `(rot s₁ t₁ - rot s₂ t₂) w`,
then some rotation `rot s t * μ`, `μ ∈ Rots ε`, `s, t ≤ N₀ + log₅ ϖ⁻¹ + Bd ε`, puts `w` in
the stripe. -/
def KL : Prop :=
  ∀ ε ϖ : ℝ, 0 < ε → ε < 1 / 10 → 0 < ϖ → ϖ < 1 / 10 →
    ∀ (N₀ s₁ t₁ s₂ t₂ : ℕ) (w : ℂ) (q : GaussianInt),
      s₁ ≤ N₀ → t₁ ≤ N₀ → s₂ ≤ N₀ → t₂ ≤ N₀ →
      ((d.M ε : ℕ) : GaussianInt) ∣ q →
      2 * ϖ ≤ size5 q + size13 q →
      ‖(q : ℂ) - (rot s₁ t₁ - rot s₂ t₂) * w‖ ≤ d.η ε / 10 →
      ∃ s t : ℕ, (s : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + d.Bd ε ∧
        (t : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + d.Bd ε ∧ ∃ μ ∈ d.Rots ε, InStripe ε (rot s t * μ) w

/- ## Confinement -/

/-- The confinement lemma for the data `d`. -/
theorem confinement (hKL : d.KL) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 10)
    {K G h T : ℕ} (hGη : 20 / d.η ε ≤ G) (hG2 : 2 ≤ G)
    (hK : d.M ε ^ 2 * G ^ 2 < (K + 1) ^ 2) (hh : 1 ≤ h)
    (hT : (K : ℝ) + Real.logb 5 (2 * 13 ^ h) + d.Bd ε ≤ T) (w : ℂ)
    (hw : ∀ s t : ℕ, s ≤ T → t ≤ T → ∀ μ ∈ d.Rots ε, ¬ InStripe ε (rot s t * μ) w) :
    ∃ k : GaussianInt, ‖w - (gD h : ℂ) / (commonDen K : ℂ) * k‖ ≤ Real.sqrt 65 ^ K := by
  have hG0 : 0 < G := by omega
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG0
  obtain ⟨p, hp, hbox⟩ := pigeonhole (d.M_pos ε) hG0 hK w
  obtain ⟨hMdvd, hclose⟩ := box_eq_consequences hG0 hbox
  set x := rot p.1.1 p.1.2 * w
  set y := rot p.2.1 p.2.2 * w
  set q : GaussianInt := gRound x - gRound y
  have hxy : x - y = (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w := by simp only [x, y]; ring
  have hq_close : ‖(q : ℂ) - (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w‖ < 2 / G := by
    rw [← hxy]; exact hclose
  have hη := d.η_pos ε
  by_cases hbig : 1 / (13 : ℝ) ^ h ≤ size5 q + size13 q
  · -- the minor-arc proposition applies and covers `w`: contradiction
    exfalso
    have hp' := hp
    simp only [labelPairs, Finset.mem_filter, Finset.mem_product, mem_labels] at hp'
    set ϖ : ℝ := 1 / (2 * 13 ^ h) with hϖ
    have hϖ0 : 0 < ϖ := by positivity
    have hϖ1 : ϖ < 1 / 10 := by
      rw [hϖ]
      have : (13 : ℝ) ≤ 13 ^ h := by
        calc (13 : ℝ) = 13 ^ 1 := by ring
          _ ≤ 13 ^ h := pow_le_pow_right₀ (by norm_num) hh
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2ϖ : 2 * ϖ ≤ size5 q + size13 q := by
      rw [hϖ]
      calc 2 * (1 / (2 * (13 : ℝ) ^ h)) = 1 / 13 ^ h := by field_simp
        _ ≤ _ := hbig
    have hcloseη : ‖(q : ℂ) - (rot p.1.1 p.1.2 - rot p.2.1 p.2.2) * w‖ ≤ d.η ε / 10 := by
      have : 2 / (G : ℝ) ≤ d.η ε / 10 := by
        rw [div_le_iff₀ hGr]
        rw [div_le_iff₀ hη] at hGη
        linarith
      linarith
    obtain ⟨s, t, hs, ht, μ, hμ, hst⟩ := hKL ε ϖ hε0 hε1 hϖ0 hϖ1 K p.1.1 p.1.2 p.2.1 p.2.2 w q
      hp'.1.1.1 hp'.1.1.2 hp'.1.2.1 hp'.1.2.2 hMdvd h2ϖ hcloseη
    have hlog : Real.logb 5 ϖ⁻¹ = Real.logb 5 (2 * 13 ^ h) := by
      rw [hϖ, one_div, inv_inv]
    rw [hlog] at hs ht
    have hsT : s ≤ T := by exact_mod_cast hs.trans hT
    have htT : t ≤ T := by exact_mod_cast ht.trans hT
    exact hw s t hsT htT μ hμ hst
  · -- `D_h ∣ q`, and the common denominator places `w` near the lattice
    push Not at hbig
    obtain ⟨k₁, hk₁⟩ := gD_dvd_of_size_lt hbig
    obtain ⟨cr, hcr⟩ := commonDen_div hp
    refine ⟨cr * k₁, ?_⟩
    have hr0 : rot p.1.1 p.1.2 - rot p.2.1 p.2.2 ≠ 0 := by
      intro h0
      have := norm_rot_sub_ge hp
      rw [h0, norm_zero] at this
      have : (0 : ℝ) < 1 / Real.sqrt 65 ^ K := by positivity
      linarith
    have hL0 : (commonDen K : ℂ) ≠ 0 := by exact_mod_cast (commonDen_pos K).ne'
    set rr := rot p.1.1 p.1.2 - rot p.2.1 p.2.2 with hrr
    have hkey : w - (gD h : ℂ) / (commonDen K : ℂ) * ((cr * k₁ : GaussianInt) : ℂ) =
        -(((q : ℂ) - rr * w) / rr) := by
      have hq' : (q : ℂ) = (gD h : ℂ) * (k₁ : ℂ) := by
        rw [hk₁, GaussianInt.toComplex_mul]
      have hcr0 : (cr : ℂ) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hcr
        exact hL0 hcr.symm
      rw [GaussianInt.toComplex_mul, hq', ← hcr]
      field_simp
      ring
    rw [hkey, norm_neg, norm_div]
    have hrr_ge := norm_rot_sub_ge hp
    have hrr_pos : 0 < ‖rr‖ := norm_pos_iff.mpr hr0
    rw [div_le_iff₀ hrr_pos]
    have hsq : 0 < Real.sqrt 65 ^ K := by positivity
    have h1 : 1 ≤ Real.sqrt 65 ^ K * ‖rr‖ := by
      rw [div_le_iff₀ hsq] at hrr_ge
      linarith
    have h2 : 2 / (G : ℝ) ≤ 1 := by
      rw [div_le_one hGr]; exact_mod_cast hG2
    calc ‖(q : ℂ) - rr * w‖ ≤ 2 / G := hq_close.le
      _ ≤ 1 := h2
      _ ≤ Real.sqrt 65 ^ K * ‖rr‖ := h1

/- ## Parameters -/

/-- `max(20/η, M, 1/ε, Bd)`. -/
noncomputable def X0 (ε : ℝ) : ℝ := max (max (20 / d.η ε) (d.M ε : ℝ)) (max (1 / ε) (d.Bd ε))
/-- The pigeonhole resolution `G`. -/
noncomputable def G (ε : ℝ) : ℕ := ⌈d.X0 ε⌉₊ + 66
/-- `K = G⁴`. -/
noncomputable def Kp (ε : ℝ) : ℕ := d.G ε ^ 4
/-- The common denominator `L`. -/
noncomputable def Lp (ε : ℝ) : ℕ := commonDen (d.Kp ε)
/-- `H = √65^K`. -/
noncomputable def Hp (ε : ℝ) : ℝ := Real.sqrt 65 ^ d.Kp ε
/-- `R = 2LH + 16`. -/
noncomputable def Rp (ε : ℝ) : ℝ := 2 * d.Lp ε * d.Hp ε + 16
/-- `Q = 128R/ε + 4`. -/
noncomputable def Qp (ε : ℝ) : ℝ := 128 * d.Rp ε / ε + 4
/-- `h` with `|D_h| > 2LHQ`. -/
noncomputable def hp (ε : ℝ) : ℕ := 2 * Nat.clog 65 (⌈2 * (d.Lp ε : ℝ) * d.Hp ε * d.Qp ε⌉₊ + 1)
/-- `T = ⌈K + log₅(2·13^h) + Bd⌉`. -/
noncomputable def Tp (ε : ℝ) : ℕ := ⌈(d.Kp ε : ℝ) + Real.logb 5 (2 * 13 ^ d.hp ε) + d.Bd ε⌉₊
/-- The orbit rotations `rot s t * μ`, `s, t ≤ T`, `μ ∈ Rots ε`. -/
noncomputable def Θp (ε : ℝ) : Finset ℂ := by
  classical
  exact ((labels (d.Tp ε)) ×ˢ (d.Rots ε)).image (fun x => rot x.1.1 x.1.2 * x.2)
/-- The final rotation set. -/
noncomputable def Ωp (ε : ℝ) : Finset ℂ := endgameSet (d.Θp ε) (discSet ε (d.Rp ε)) (d.Lp ε)

variable {d}

lemma X0_ge (ε : ℝ) :
    20 / d.η ε ≤ d.X0 ε ∧ (d.M ε : ℝ) ≤ d.X0 ε ∧ 1 / ε ≤ d.X0 ε ∧ d.Bd ε ≤ d.X0 ε := by
  unfold X0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

lemma G_ge (ε : ℝ) : d.X0 ε ≤ d.G ε ∧ 66 ≤ d.G ε := by
  constructor
  · unfold G; push_cast
    have := Nat.le_ceil (d.X0 ε)
    linarith
  · unfold G; omega

lemma M_le_G (ε : ℝ) : d.M ε ≤ d.G ε := by
  have h1 := (X0_ge (d := d) ε).2.1
  have h2 := (G_ge (d := d) ε).1
  exact_mod_cast h1.trans h2

lemma hK_param (ε : ℝ) : d.M ε ^ 2 * d.G ε ^ 2 < (d.Kp ε + 1) ^ 2 := by
  have hM := M_le_G (d := d) ε
  have hG := (G_ge (d := d) ε).2
  unfold Kp
  set G := d.G ε
  have h1 : d.M ε ^ 2 * G ^ 2 ≤ G ^ 2 * G ^ 2 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM 2)
  have h4 : 1 ≤ G ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : G ^ 2 * G ^ 2 < (G ^ 4 + 1) ^ 2 := by
    have : G ^ 2 * G ^ 2 = G ^ 4 := by ring
    rw [this]
    nlinarith
  omega

lemma Hp_ge_one (ε : ℝ) : 1 ≤ d.Hp ε := by
  unfold Hp
  exact one_le_pow₀ (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)

lemma Lp_pos (ε : ℝ) : 0 < d.Lp ε := commonDen_pos _

lemma Rp_ge (ε : ℝ) : 16 ≤ d.Rp ε ∧ 2 * (d.Lp ε : ℝ) * d.Hp ε ≤ d.Rp ε := by
  unfold Rp
  have h1 : (0 : ℝ) ≤ 2 * d.Lp ε * d.Hp ε := by
    have := Hp_ge_one (d := d) ε
    positivity
  constructor <;> linarith

lemma hp_spec {ε : ℝ} (hε : 0 < ε) : 1 ≤ d.hp ε ∧
    2 * (d.Lp ε : ℝ) * d.Hp ε * d.Qp ε < ‖(gD (d.hp ε) : ℂ)‖ := by
  set X := 2 * (d.Lp ε : ℝ) * d.Hp ε * d.Qp ε with hX
  have hXpos : 0 < X := by
    have hL : (0 : ℝ) < d.Lp ε := by exact_mod_cast Lp_pos (d := d) ε
    have hH := Hp_ge_one (d := d) ε
    have hQ : 0 < d.Qp ε := by
      unfold Qp
      have := (Rp_ge (d := d) ε).1
      positivity
    rw [hX]; positivity
  have hceil : 1 ≤ ⌈X⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
  set m := Nat.clog 65 (⌈X⌉₊ + 1) with hm
  have hm1 : 0 < m := Nat.clog_pos (by norm_num) (by omega)
  constructor
  · unfold hp; rw [← hm]; omega
  · rw [cnorm_gD]
    unfold hp
    rw [← hm, pow_mul, Real.sq_sqrt (by norm_num)]
    have h1 : ⌈X⌉₊ + 1 ≤ 65 ^ m := Nat.le_pow_clog (by norm_num) _
    have h2 : X < ⌈X⌉₊ + 1 := by
      have := Nat.le_ceil X; linarith
    have h3 : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ ((65 ^ m : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith

variable (d)

/-- The covering assembled from the confinement lemma, the disc cover and the end game. -/
theorem minCopies_le_param {ε : ℝ} (hKL : d.KL) (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    (minCopies ε : ℝ) ≤
      (2 * ((d.Tp ε : ℝ) + 1) ^ 2 * (d.Rots ε).card + 1) * (discSet ε (d.Rp ε)).card := by
  classical
  obtain ⟨hX20, _, _, _⟩ := X0_ge (d := d) ε
  obtain ⟨hGX, hG66⟩ := G_ge (d := d) ε
  obtain ⟨hR16, hRLH⟩ := Rp_ge (d := d) ε
  obtain ⟨hh1, hD⟩ := hp_spec (d := d) hε
  obtain ⟨hU1, hU2, hU3, _⟩ := disc_cover hε hε1 hR16
  have hGr : (66 : ℝ) ≤ d.G ε := by exact_mod_cast hG66
  -- confinement for the orbit `Θ`
  have hconf : ∀ w : ℂ, (∀ θ ∈ d.Θp ε, ¬ InStripe ε θ w) →
      ∃ k : GaussianInt, ‖w - (gD (d.hp ε) : ℂ) / (d.Lp ε : ℂ) * k‖ ≤ d.Hp ε := by
    intro w hw
    have hw' : ∀ s t : ℕ, s ≤ d.Tp ε → t ≤ d.Tp ε → ∀ μ ∈ d.Rots ε,
        ¬ InStripe ε (rot s t * μ) w := by
      intro s t hs ht μ hμ
      apply hw
      unfold Θp
      exact Finset.mem_image.mpr ⟨((s, t), μ),
        Finset.mem_product.mpr ⟨mem_labels.mpr ⟨hs, ht⟩, hμ⟩, rfl⟩
    exact d.confinement hKL hε hε1 (by linarith) (by omega) (hK_param (d := d) ε) hh1
      (Nat.le_ceil _) w hw'
  -- the end game
  have hcov : ∀ z : ℂ, ∃ v ∈ d.Ωp ε, InStripe ε v z := by
    intro z
    unfold Ωp
    refine endgame_cover (Q := d.Qp ε) (Lp_pos (d := d) ε) (d.Θp ε) (discSet ε (d.Rp ε)) hconf
      ?_ hU1 ?_ hD z
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hU2 p hp
      exact ⟨h1, h2, by unfold Qp; exact h3⟩
    · intro e he
      exact hU3 e (he.trans hRLH)
  have hunit : ∀ v ∈ d.Ωp ε, ‖v‖ = 1 := by
    unfold Ωp
    refine norm_of_mem_endgameSet (Lp_pos (d := d) ε) ?_ ?_
    · intro θ hθ
      unfold Θp at hθ
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hθ
      rw [norm_mul, norm_rot, one_mul]
      exact d.norm_rots ε _ (Finset.mem_product.mp hx).2
    · intro p hp
      obtain ⟨h1, h2, _⟩ := hU2 p hp
      exact ⟨h1, h2⟩
  have hmin := minCopies_le_of_cover (d.Ωp ε) hunit hcov
  have hcard := card_endgameSet_le (d.Θp ε) (discSet ε (d.Rp ε)) (d.Lp ε)
  have hΘ : (d.Θp ε).card ≤ (d.Tp ε + 1) ^ 2 * (d.Rots ε).card := by
    unfold Θp
    exact Finset.card_image_le.trans (by rw [Finset.card_product, card_labels])
  have h1 : (minCopies ε : ℝ) ≤ (d.Ωp ε).card := by exact_mod_cast hmin
  have h2 : ((d.Ωp ε).card : ℝ) ≤
      2 * (d.Θp ε).card * (discSet ε (d.Rp ε)).card + (discSet ε (d.Rp ε)).card := by
    unfold Ωp; exact_mod_cast hcard
  have h3 : ((d.Θp ε).card : ℝ) ≤ ((d.Tp ε : ℝ) + 1) ^ 2 * (d.Rots ε).card := by
    exact_mod_cast hΘ
  have hU0 : (0 : ℝ) ≤ (discSet ε (d.Rp ε)).card := by positivity
  calc (minCopies ε : ℝ) ≤ (d.Ωp ε).card := h1
    _ ≤ 2 * (d.Θp ε).card * (discSet ε (d.Rp ε)).card + (discSet ε (d.Rp ε)).card := h2
    _ ≤ 2 * (((d.Tp ε : ℝ) + 1) ^ 2 * (d.Rots ε).card) * (discSet ε (d.Rp ε)).card +
          (discSet ε (d.Rp ε)).card := by gcongr
    _ = (2 * ((d.Tp ε : ℝ) + 1) ^ 2 * (d.Rots ε).card + 1) * (discSet ε (d.Rp ε)).card := by
        ring

/- ## Estimates -/

/-- `B = (K+1)^5`. -/
noncomputable def Bp (ε : ℝ) : ℕ := (d.Kp ε + 1) ^ 5

variable {d}

lemma one_le_Bp (ε : ℝ) : 1 ≤ d.Bp ε := by unfold Bp; exact Nat.one_le_pow _ _ (by omega)

lemma Kp_le_Bp (ε : ℝ) : d.Kp ε ≤ d.Bp ε := by
  unfold Bp
  calc d.Kp ε ≤ d.Kp ε + 1 := Nat.le_succ _
    _ = (d.Kp ε + 1) ^ 1 := (pow_one _).symm
    _ ≤ (d.Kp ε + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)

lemma G_le_Kp (ε : ℝ) : d.G ε ≤ d.Kp ε := by
  unfold Kp
  have hG := (G_ge (d := d) ε).2
  calc d.G ε = d.G ε ^ 1 := (pow_one _).symm
    _ ≤ d.G ε ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)

lemma G_le_Bp (ε : ℝ) : d.G ε ≤ d.Bp ε := (G_le_Kp ε).trans (Kp_le_Bp ε)

lemma Lp_le (ε : ℝ) : (d.Lp ε : ℝ) ≤ 65 ^ d.Bp ε := by
  have h1 := commonDen_le (d.Kp ε)
  have h2 : 4 * 65 ^ d.Kp ε ≤ 65 ^ (d.Kp ε + 1) := by rw [pow_succ]; omega
  have h3 : (4 * 65 ^ d.Kp ε) ^ ((d.Kp ε + 1) ^ 4) ≤ 65 ^ d.Bp ε := by
    calc (4 * 65 ^ d.Kp ε) ^ ((d.Kp ε + 1) ^ 4) ≤ (65 ^ (d.Kp ε + 1)) ^ ((d.Kp ε + 1) ^ 4) :=
          Nat.pow_le_pow_left h2 _
      _ = 65 ^ d.Bp ε := by rw [← pow_mul, Bp]; ring_nf
  have h4 : d.Lp ε ≤ 65 ^ d.Bp ε := by unfold Lp; exact h1.trans h3
  exact_mod_cast h4

lemma Hp_le (ε : ℝ) : d.Hp ε ≤ 65 ^ d.Bp ε := by
  unfold Hp
  have h1 : Real.sqrt 65 ≤ 65 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc Real.sqrt 65 ^ d.Kp ε ≤ 65 ^ d.Kp ε := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 _
    _ ≤ 65 ^ d.Bp ε := pow_le_pow_right₀ (by norm_num) (Kp_le_Bp ε)

lemma Rp_le (ε : ℝ) : d.Rp ε ≤ 65 ^ (2 * d.Bp ε + 1) := by
  unfold Rp
  have hL := Lp_le (d := d) ε
  have hH := Hp_le (d := d) ε
  have hH0 : 0 ≤ d.Hp ε := le_trans zero_le_one (Hp_ge_one ε)
  have hpow : (65 : ℝ) ^ (2 * d.Bp ε + 1) = 65 * (65 ^ d.Bp ε * 65 ^ d.Bp ε) := by
    rw [pow_succ, two_mul, pow_add]; ring
  have h1 : (1 : ℝ) ≤ 65 ^ d.Bp ε := one_le_pow₀ (by norm_num)
  have h2 : 2 * (d.Lp ε : ℝ) * d.Hp ε ≤ 2 * (65 ^ d.Bp ε * 65 ^ d.Bp ε) := by
    have : (d.Lp ε : ℝ) * d.Hp ε ≤ 65 ^ d.Bp ε * 65 ^ d.Bp ε := by
      apply mul_le_mul hL hH hH0 (by positivity)
    nlinarith
  rw [hpow]
  nlinarith

lemma inv_ε_le (ε : ℝ) : 1 / ε ≤ d.Bp ε := by
  obtain ⟨_, _, h1, _⟩ := X0_ge (d := d) ε
  have h2 := (G_ge (d := d) ε).1
  have h3 : (d.G ε : ℝ) ≤ d.Bp ε := by exact_mod_cast G_le_Bp ε
  linarith

lemma Bd_le (ε : ℝ) : d.Bd ε ≤ d.Bp ε := by
  obtain ⟨_, _, _, h1⟩ := X0_ge (d := d) ε
  have h2 := (G_ge (d := d) ε).1
  have h3 : (d.G ε : ℝ) ≤ d.Bp ε := by exact_mod_cast G_le_Bp ε
  linarith

lemma Qp_le {ε : ℝ} (hε : 0 < ε) : d.Qp ε ≤ 65 ^ (3 * d.Bp ε + 3) := by
  have h := Q_le_aux (B := d.Bp ε) (Rp_le (d := d) ε)
    (by linarith [(Rp_ge (d := d) ε).1]) (inv_ε_le (d := d) ε) (by positivity)
  unfold Qp
  calc 128 * d.Rp ε / ε + 4 = 128 * d.Rp ε * (1 / ε) + 4 := by ring
    _ ≤ _ := h

lemma Qp_nonneg {ε : ℝ} (hε : 0 < ε) : 0 ≤ d.Qp ε := by
  unfold Qp; have := (Rp_ge (d := d) ε).1; positivity

lemma X_le {ε : ℝ} (hε : 0 < ε) :
    2 * (d.Lp ε : ℝ) * d.Hp ε * d.Qp ε ≤ 65 ^ (5 * d.Bp ε + 4) :=
  X_le_aux (Lp_le ε) (Hp_le ε) (Qp_le hε) (by positivity) (le_trans zero_le_one (Hp_ge_one ε))
    (Qp_nonneg hε)

lemma hp_le {ε : ℝ} (hε : 0 < ε) : d.hp ε ≤ 10 * d.Bp ε + 10 := by
  have hX0 : 0 ≤ 2 * (d.Lp ε : ℝ) * d.Hp ε * d.Qp ε := by
    have hH0 : 0 ≤ d.Hp ε := le_trans zero_le_one (Hp_ge_one ε)
    have hQ0 := Qp_nonneg (d := d) hε
    positivity
  have h := clog_aux hX0 (X_le hε)
  unfold hp
  omega

lemma Tp_le {ε : ℝ} (hε : 0 < ε) : (d.Tp ε : ℝ) ≤ 44 * d.Bp ε := by
  unfold Tp
  exact T_le_aux (Kp_le_Bp ε) (hp_le hε) (d.Bd_nonneg ε) (Bd_le ε) (one_le_Bp ε)

lemma card_discSet_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    ((discSet ε (d.Rp ε)).card : ℝ) ≤ 2200 * (d.Bp ε : ℝ) ^ 2 := by
  obtain ⟨_, _, _, hcard⟩ := disc_cover hε hε1 (Rp_ge (d := d) ε).1
  exact hcard.trans (U_le_aux (one_le_Bp ε) hε (inv_ε_le ε) (Rp_ge (d := d) ε).1 (Rp_le ε))

lemma Bp_le_G (ε : ℝ) : d.Bp ε ≤ 32 * d.G ε ^ 20 := by
  have hG := (G_ge (d := d) ε).2
  unfold Bp Kp
  calc (d.G ε ^ 4 + 1) ^ 5 ≤ (2 * d.G ε ^ 4) ^ 5 := by
        apply Nat.pow_le_pow_left
        have : 1 ≤ d.G ε ^ 4 := Nat.one_le_pow _ _ (by omega)
        omega
    _ = 32 * d.G ε ^ 20 := by ring

variable (d)

/-- **The assembled bound** `minCopies ε ≤ |Rots ε| · G^88`. -/
theorem minCopies_le_Rots_G_pow (hKL : d.KL) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) :
    (minCopies ε : ℝ) ≤ (d.Rots ε).card * (d.G ε : ℝ) ^ 88 := by
  set U : ℝ := ((discSet ε (d.Rp ε)).card : ℝ) with hU
  set T : ℝ := (d.Tp ε : ℝ) with hT
  set R : ℝ := ((d.Rots ε).card : ℝ) with hR
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; exact_mod_cast d.card_rots ε
  have hU0 : 0 ≤ U := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hm := d.minCopies_le_param hKL hε hε1
  have hkey : (2 * (T + 1) ^ 2 + 1) * U ≤ (d.G ε : ℝ) ^ 88 :=
    final_aux (G_ge (d := d) ε).2 (Bp_le_G ε) (one_le_Bp ε) le_rfl (Tp_le hε) hT0
      (card_discSet_le hε hε1) hU0
  calc (minCopies ε : ℝ) ≤ (2 * (T + 1) ^ 2 * R + 1) * U := hm
    _ ≤ R * ((2 * (T + 1) ^ 2 + 1) * U) := by nlinarith [sq_nonneg (T + 1)]
    _ ≤ R * (d.G ε : ℝ) ^ 88 := by gcongr

end ArcData

end Green41

/- ## Section: `KL57Quasi` -/

/-
# The minor-arc interface with digit rotations on both sides

With digit rotations in the discrete core, the cell generator carries the conjugate of the digit
denominator at level `ℓ`, of norm at most `p^{2p(ℓ²+1)}`, instead of `ρ̄^S` with
`S = (p - 1) p^(ℓ-1)`. The parameters become (with `c = clog_p K`, `L = 6c + 4`, `ℓ = 4L` as
before)

* `A = 2p(ℓ² + 1) + 2c + 3`, `n = 8(A + ℓ)`, `α = n - A`,

all of size `O(log² K)`. The interface `dataQ.KL` asks for `q` divisible by

* `D5Q ε  = digitDen 5 (n₅ + 4) Q · conj(digitDen 5 ℓ₅ Q)` and
* `D13Q ε = digitDen 13 (n₁₃ + 4) P · conj(digitDen 13 ℓ₁₃ P)`,

of norm `2^{O(n²)} = exp(O(log⁴ K))`, with tolerance `ηQ ε = 5^(-(A₅ + A₁₃))`.
-/

namespace Green41


open Complex ComplexConjugate Finset

/- ## Parameters -/

/-- `A = 2p(ℓ² + 1) + 2c + 3`. -/
def qA (p K : ℕ) : ℕ := 2 * p * (pℓ p K ^ 2 + 1) + 2 * pc p K + 3
/-- `n = 8(A + ℓ)`. -/
def qn (p K : ℕ) : ℕ := 8 * (qA p K + pℓ p K)
/-- `α = n - A`. -/
def qα (p K : ℕ) : ℕ := qn p K - qA p K

lemma qA_le_qn (p K : ℕ) : qA p K ≤ qn p K := by unfold qn; omega

/- ## The cell -/

lemma norm_cellGenD_sq {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (D : GaussianInt)
    (n α : ℕ) :
    ‖cellGenD π D n α‖ ^ 2 = (p : ℝ) ^ α * (D.norm : ℝ) / (p : ℝ) ^ n := by
  unfold cellGenD
  rw [norm_div, norm_mul, _root_.norm_pow, _root_.norm_pow, hπ.norm_toComplex_star_π,
    hπ.norm_toComplex_π, norm_toComplex, div_pow, mul_pow,
    sqrt_pow_sq (Nat.cast_nonneg p), sqrt_pow_sq (Nat.cast_nonneg p),
    Real.sq_sqrt (by exact_mod_cast GaussianInt.norm_nonneg D)]

/-- `‖g‖² = N(D) / p^A` when `α + A = n`. -/
lemma norm_cellGenD_sq' {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (D : GaussianInt)
    {n α A : ℕ} (hnA : α + A = n) :
    ‖cellGenD π D n α‖ ^ 2 = (D.norm : ℝ) / (p : ℝ) ^ A := by
  rw [norm_cellGenD_sq hπ, ← hnA, pow_add]
  have hp0 : (p : ℝ) ^ α ≠ 0 := pow_ne_zero _ (by exact_mod_cast hπ.prime.ne_zero)
  field_simp

lemma one_add_pow_le_pow {p j ℓ : ℕ} (hp : 2 ≤ p) (hj : j < ℓ) :
    1 + (p : ℤ) ^ (2 * j) ≤ (p : ℤ) ^ (2 * ℓ) := by
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have h1 : (1 : ℤ) ≤ (p : ℤ) ^ (2 * j) := one_le_pow₀ hp1
  have h2 : (p : ℤ) ^ (2 * j) * 2 ≤ (p : ℤ) ^ (2 * j) * p :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hp) (by positivity)
  have h3 : (p : ℤ) ^ (2 * j) * p = (p : ℤ) ^ (2 * j + 1) := by rw [pow_succ]
  have h4 : (p : ℤ) ^ (2 * j + 1) ≤ (p : ℤ) ^ (2 * ℓ) := pow_le_pow_right₀ hp1 (by omega)
  linarith

/-- The digit denominator at level `ℓ` has norm at most `p^{2p(ℓ²+1)}`. -/
lemma norm_digitDen_le_pow {p ℓ : ℕ} (hp : 2 ≤ p) {ρ : GaussianInt}
    (hρ : ρ.norm ≤ (p : ℤ) ^ 2) :
    (DigitPrime.digitDen p ℓ ρ).norm ≤ (p : ℤ) ^ (2 * p * (ℓ ^ 2 + 1)) := by
  rw [norm_digitDen]
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hρ0 : 0 ≤ ρ.norm := GaussianInt.norm_nonneg ρ
  have h1 : ρ.norm ^ (p - 2) ≤ (p : ℤ) ^ (2 * p) := by
    calc ρ.norm ^ (p - 2) ≤ ((p : ℤ) ^ 2) ^ (p - 2) := pow_le_pow_left₀ hρ0 hρ _
      _ = (p : ℤ) ^ (2 * (p - 2)) := by rw [← pow_mul]
      _ ≤ (p : ℤ) ^ (2 * p) := pow_le_pow_right₀ hp1 (by omega)
  have hfac : ∀ j ∈ Ico 1 ℓ, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) ≤ ((p : ℤ) ^ (2 * ℓ)) ^ p := by
    intro j hj
    have hb := one_add_pow_le_pow hp (mem_Ico.mp hj).2
    have hb0 : (0 : ℤ) ≤ 1 + (p : ℤ) ^ (2 * j) := by positivity
    calc (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) ≤ ((p : ℤ) ^ (2 * ℓ)) ^ (p - 1) :=
          pow_le_pow_left₀ hb0 hb _
      _ ≤ ((p : ℤ) ^ (2 * ℓ)) ^ p := pow_le_pow_right₀ (one_le_pow₀ hp1) (by omega)
  have hexp : 2 * ℓ * p * (ℓ - 1) ≤ 2 * p * ℓ ^ 2 := by
    calc 2 * ℓ * p * (ℓ - 1) ≤ 2 * ℓ * p * ℓ := Nat.mul_le_mul_left _ (Nat.sub_le ℓ 1)
      _ = 2 * p * ℓ ^ 2 := by ring
  have h2 : ∏ j ∈ Ico 1 ℓ, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) ≤ (p : ℤ) ^ (2 * p * ℓ ^ 2) := by
    calc ∏ j ∈ Ico 1 ℓ, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1)
        ≤ ∏ _j ∈ Ico 1 ℓ, ((p : ℤ) ^ (2 * ℓ)) ^ p :=
          prod_le_prod₀ (fun j _ => by positivity) hfac
      _ = (((p : ℤ) ^ (2 * ℓ)) ^ p) ^ (ℓ - 1) := by rw [prod_const, Nat.card_Ico]
      _ = (p : ℤ) ^ (2 * ℓ * p * (ℓ - 1)) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ (p : ℤ) ^ (2 * p * ℓ ^ 2) := pow_le_pow_right₀ hp1 hexp
  have h3 : 0 ≤ ∏ j ∈ Ico 1 ℓ, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1) :=
    prod_nonneg fun j _ => by positivity
  calc ρ.norm ^ (p - 2) * ∏ j ∈ Ico 1 ℓ, (1 + (p : ℤ) ^ (2 * j)) ^ (p - 1)
      ≤ (p : ℤ) ^ (2 * p) * (p : ℤ) ^ (2 * p * ℓ ^ 2) := mul_le_mul h1 h2 h3 (by positivity)
    _ = (p : ℤ) ^ (2 * p * (ℓ ^ 2 + 1)) := by rw [← pow_add]; ring_nf

/-- Upper bound on the cell: `‖g‖² ≤ ε²/125`. -/
lemma norm_cellGenD_sq_le {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp5 : 5 ≤ p)
    (hρn : ρ.norm ≤ (p : ℤ) ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ‖cellGenD π (star (DigitPrime.digitDen p (pℓ p ⌈1 / ε⌉₊) ρ)) (qn p ⌈1 / ε⌉₊)
        (qα p ⌈1 / ε⌉₊)‖ ^ 2 ≤ ε ^ 2 / 125 := by
  set K := ⌈1 / ε⌉₊ with hK
  rw [norm_cellGenD_sq' hπ _ (A := qA p K) (by unfold qα; have := qA_le_qn p K; omega),
    Zsqrtd.norm_conj]
  have hpr : (0 : ℝ) < p := by exact_mod_cast hπ.prime.pos
  have hpc : (K : ℝ) ≤ (p : ℝ) ^ pc p K := by exact_mod_cast le_pow_pc p K (by omega)
  have hKe : 1 / ε ≤ K := Nat.le_ceil _
  have hN : ((DigitPrime.digitDen p (pℓ p K) ρ).norm : ℝ) ≤
      (p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) := by
    exact_mod_cast norm_digitDen_le_pow (by omega) hρn
  have hA : (p : ℝ) ^ qA p K =
      (p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) * ((p : ℝ) ^ pc p K) ^ 2 * (p : ℝ) ^ 3 := by
    unfold qA; rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
  rw [hA, div_le_div_iff₀ (by positivity) (by norm_num)]
  have h2 : (125 : ℝ) ≤ (p : ℝ) ^ 3 := by
    have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    calc (125 : ℝ) = 5 ^ 3 := by norm_num
      _ ≤ (p : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
  have h3 : 1 ≤ ε ^ 2 * ((p : ℝ) ^ pc p K) ^ 2 := by
    have : 1 ≤ ε * (p : ℝ) ^ pc p K := by
      calc (1 : ℝ) = ε * (1 / ε) := by field_simp
        _ ≤ ε * K := by gcongr
        _ ≤ ε * (p : ℝ) ^ pc p K := by gcongr
    nlinarith
  have hq : (0 : ℝ) ≤ (p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) := by positivity
  calc ((DigitPrime.digitDen p (pℓ p K) ρ).norm : ℝ) * 125
      ≤ (p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) * 125 := by gcongr
    _ ≤ (p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) *
          ((p : ℝ) ^ 3 * (ε ^ 2 * ((p : ℝ) ^ pc p K) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hq; nlinarith
    _ = ε ^ 2 * ((p : ℝ) ^ (2 * p * (pℓ p K ^ 2 + 1)) * ((p : ℝ) ^ pc p K) ^ 2 *
          (p : ℝ) ^ 3) := by
        ring

/-- Lower bound on the cell: `5^(-A) ≤ ‖g‖`. -/
lemma norm_cellGenD_ge {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp13 : p ≤ 13)
    {D : GaussianInt} (hD1 : 1 ≤ (D.norm : ℝ)) {n α A : ℕ} (hnA : α + A = n) :
    (1 / 5 : ℝ) ^ A ≤ ‖cellGenD π D n α‖ := by
  have hsq := norm_cellGenD_sq' hπ D hnA
  have hpr : (0 : ℝ) < p := by exact_mod_cast hπ.prime.pos
  have h1 : ((1 / 5 : ℝ) ^ A) ^ 2 ≤ ‖cellGenD π D n α‖ ^ 2 := by
    rw [hsq, ← pow_mul, le_div_iff₀ (by positivity)]
    have hp' : (p : ℝ) ≤ 25 := by
      have : (p : ℝ) ≤ 13 := by exact_mod_cast hp13
      linarith
    have h2 : (p : ℝ) ^ A ≤ 25 ^ A := pow_le_pow_left₀ hpr.le hp' A
    have h4 : (1 / 5 : ℝ) ^ (A * 2) * 25 ^ A = 1 := by
      rw [mul_comm A 2, pow_mul, ← mul_pow]; norm_num
    calc (1 / 5 : ℝ) ^ (A * 2) * (p : ℝ) ^ A ≤ (1 / 5 : ℝ) ^ (A * 2) * 25 ^ A := by gcongr
      _ = 1 := h4
      _ ≤ (D.norm : ℝ) := hD1
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h1

/- ## Divisibility facts -/

namespace DigitPrime

variable {π : GaussianInt} {p : ℕ} (hπ : DigitPrime π p)
include hπ

lemma not_dvd_digitDen {N : ℕ} {ρ : GaussianInt} (hρ2 : ¬ π ∣ star ρ) :
    ¬ π ∣ digitDen p N ρ := by
  intro h
  rw [digitDen] at h
  rcases hπ.prime_π.dvd_or_dvd h with h1 | h1
  · exact hρ2 (hπ.prime_π.dvd_of_dvd_pow h1)
  · rw [hπ.prime_π.dvd_finsetProd_iff] at h1
    obtain ⟨j, hj, hdvd⟩ := h1
    exact hπ.not_dvd_star_digitInt (mem_Ico.mp hj).1 (hπ.prime_π.dvd_of_dvd_pow hdvd)

lemma not_star_dvd_star_digitDen {N : ℕ} {ρ : GaussianInt} (hρ2 : ¬ π ∣ star ρ) :
    ¬ star π ∣ star (digitDen p N ρ) := by
  rintro ⟨c, hc⟩
  apply hπ.not_dvd_digitDen (N := N) hρ2
  exact ⟨star c, by rw [← star_star (digitDen p N ρ), hc, star_mul', star_star]⟩

lemma one_le_norm_star_digitDen {N : ℕ} {ρ : GaussianInt} (hρ1 : ¬ π ∣ ρ) :
    (1 : ℝ) ≤ ((star (digitDen p N ρ)).norm : ℝ) := by
  have hD0 : star (digitDen p N ρ) ≠ 0 := fun h0 =>
    (hπ.not_dvd_star_digitDen (N := N) hρ1) (by rw [h0]; exact dvd_zero π)
  have hpos : 0 < (star (digitDen p N ρ)).norm := by
    rcases (GaussianInt.norm_nonneg (star (digitDen p N ρ))).lt_or_eq with h | h
    · exact h
    · exact absurd (GaussianInt.norm_eq_zero.mp h.symm) hD0
  have : (1 : ℤ) ≤ (star (digitDen p N ρ)).norm := hpos
  exact_mod_cast this

end DigitPrime

/- ## The generic case -/

theorem case_core_quasi {π ρ : GaussianInt} {p : ℕ} (hπ : DigitPrime π p) (hp5 : 5 ≤ p)
    (hp13 : p ≤ 13) (hρ1 : ¬ π ∣ ρ) (hρ2 : ¬ π ∣ star ρ) (hρn : ρ.norm ≤ (p : ℤ) ^ 2)
    (hordA : ∀ k, 2 ≤ k → orderOf (hπ.mult (star ρ) k) = (p - 1) * p ^ (k - 1))
    (hordC : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
      orderOf (((hπ.mult (star ρ) n).val : ℕ) : ZMod (p ^ ℓ)) = (p - 1) * p ^ (ℓ - 1))
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 10) (hη : η ≤ (1 / 5 : ℝ) ^ qA p ⌈1 / ε⌉₊)
    (w : ℂ) (q : GaussianInt) {N₀ a₁ b₁ a₂ b₂ v : ℕ}
    (ha₁ : a₁ ≤ N₀) (hb₁ : b₁ ≤ N₀) (ha₂ : a₂ ≤ N₀) (hb₂ : b₂ ≤ N₀) {q₂ : GaussianInt}
    (hq₂ : ¬ star π ∣ q₂)
    (hqeq : q = star π ^ v * DigitPrime.digitDen p (qn p ⌈1 / ε⌉₊ + 4) ρ *
      star (DigitPrime.digitDen p (pℓ p ⌈1 / ε⌉₊) ρ) * q₂)
    (hclose : ‖(q : ℂ) - (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ ≤ η / 10) :
    ∃ a b : ℕ, a ≤ N₀ + v + (qA p ⌈1 / ε⌉₊ + 4) + qn p ⌈1 / ε⌉₊ ∧ b ≤ N₀ ∧
      ∃ μ ∈ digitRotFinset p (qn p ⌈1 / ε⌉₊ + 4) ρ,
      ∃ ν ∈ digitRotInvFinset p (pℓ p ⌈1 / ε⌉₊) ρ,
      ∃ k : ℤ, |(((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a *
        ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b * μ * ν * w).re - k| < ε := by
  set K := ⌈1 / ε⌉₊ with hK
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) (Nat.le_ceil (1 / ε))
    exact_mod_cast this
  have hℓ16 := pℓ_ge p K
  have hn2 : 2 ≤ qn p K := by unfold qn; omega
  -- the cell
  set g := cellGenD π (star (DigitPrime.digitDen p (pℓ p K) ρ)) (qn p K) (qα p K) with hg
  have hαA : qα p K + qA p K = qn p K := by unfold qα; have := qA_le_qn p K; omega
  have hglow : (1 / 5 : ℝ) ^ qA p K ≤ ‖g‖ :=
    norm_cellGenD_ge hπ hp13 (hπ.one_le_norm_star_digitDen hρ1) hαA
  have he' : ‖(((star π) ^ v * DigitPrime.digitDen p (qn p K + 4) ρ *
        star (DigitPrime.digitDen p (pℓ p K) ρ) * q₂ : GaussianInt) : ℂ) -
      (((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₁ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₁ -
        ((π : ℂ) / ((star π : GaussianInt) : ℂ)) ^ a₂ *
          ((ρ : ℂ) / ((star ρ : GaussianInt) : ℂ)) ^ b₂) * w‖ < 21 / 50 * ‖g‖ := by
    rw [← hqeq]
    have h5 : (0 : ℝ) < (1 / 5 : ℝ) ^ qA p K := by positivity
    linarith
  have hgε : Real.sqrt 2 * ‖g‖ ≤ ε / 2 :=
    sqrt_two_mul_le (norm_nonneg _) hε (norm_cellGenD_sq_le hπ hp5 hρn hε)
  have hH : 2 ≤ (pH K : ℝ) * ε ^ 2 := by
    have hKe : 1 / ε ≤ K := Nat.le_ceil _
    have h1 : 1 ≤ (K : ℝ) * ε := by
      calc (1 : ℝ) = (1 / ε) * ε := by field_simp
        _ ≤ K * ε := by gcongr
    unfold pH; push_cast; nlinarith
  have hHL : 25 * pH K ^ 3 < 4 * p ^ pL p K := pH_cube_lt p K hp5 hK1
  have hA4 := hordA (qn p K + 4) (by omega)
  rw [show qn p K + 4 - 1 = qn p K + 3 by omega] at hA4
  exact hπ.minor_arc_core_quasi hp5 hρ1 hρ2
    (n := qn p K) (α := qα p K) (A := qA p K) (L := pL p K) (ℓ := pℓ p K) (H := pH K)
    (pL_pos p K) rfl rfl (by omega) hA4 (hordC (qn p K) (pℓ p K) hn2 (by omega)) hε hH hHL hgε
    w ha₁ hb₁ ha₂ hb₂ hq₂ he'

/- ## The data attached to `ε` -/

/-- The divisor needed in the case of the digit prime `P` (multiplier `Q`). -/
noncomputable def D5Q (ε : ℝ) : GaussianInt :=
  DigitPrime.digitDen 5 (qn 5 ⌈1 / ε⌉₊ + 4) gQ * star (DigitPrime.digitDen 5 (pℓ 5 ⌈1 / ε⌉₊) gQ)

/-- The divisor needed in the case of the digit prime `Q` (multiplier `P`). -/
noncomputable def D13Q (ε : ℝ) : GaussianInt :=
  DigitPrime.digitDen 13 (qn 13 ⌈1 / ε⌉₊ + 4) gP *
    star (DigitPrime.digitDen 13 (pℓ 13 ⌈1 / ε⌉₊) gP)

/-- The modulus `N(D5Q) N(D13Q)` that the pigeonhole has to respect. -/
noncomputable def MdigQ (ε : ℝ) : ℕ := (D5Q ε).norm.natAbs * (D13Q ε).norm.natAbs

/-- The exponent budget: `O(log² (1/ε))`. -/
noncomputable def BdQ (ε : ℝ) : ℝ :=
  ((qA 5 ⌈1 / ε⌉₊ + 4 + qn 5 ⌈1 / ε⌉₊ + (qA 13 ⌈1 / ε⌉₊ + 4 + qn 13 ⌈1 / ε⌉₊) : ℕ) : ℝ)

/-- The tolerance `5^(-(A₅ + A₁₃))`. -/
noncomputable def ηQ (ε : ℝ) : ℝ := (1 / 5 : ℝ) ^ (qA 5 ⌈1 / ε⌉₊ + qA 13 ⌈1 / ε⌉₊)

/-- The products `μ ν` of a digit rotation at level `N` and an inverse digit rotation at
level `ℓ`. -/
noncomputable def rotPairs (p N ℓ : ℕ) (ρ : GaussianInt) : Finset ℂ :=
  (digitRotFinset p N ρ ×ˢ digitRotInvFinset p ℓ ρ).image fun x => x.1 * x.2

/-- The rotations used by the interface. -/
noncomputable def RotsQ (ε : ℝ) : Finset ℂ :=
  rotPairs 5 (qn 5 ⌈1 / ε⌉₊ + 4) (pℓ 5 ⌈1 / ε⌉₊) gQ ∪
    rotPairs 13 (qn 13 ⌈1 / ε⌉₊ + 4) (pℓ 13 ⌈1 / ε⌉₊) gP

lemma mem_rotPairs {p N ℓ : ℕ} {ρ : GaussianInt} {μ ν : ℂ} (hμ : μ ∈ digitRotFinset p N ρ)
    (hν : ν ∈ digitRotInvFinset p ℓ ρ) : μ * ν ∈ rotPairs p N ℓ ρ :=
  Finset.mem_image.mpr ⟨(μ, ν), Finset.mem_product.mpr ⟨hμ, hν⟩, rfl⟩

lemma norm_of_mem_rotPairs {p N ℓ : ℕ} {ρ : GaussianInt} (hρ : ρ ≠ 0) {x : ℂ}
    (hx : x ∈ rotPairs p N ℓ ρ) : ‖x‖ = 1 := by
  obtain ⟨⟨μ, ν⟩, hμν, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hμ, hν⟩ := Finset.mem_product.mp hμν
  rw [norm_mul, norm_of_mem_digitRotFinset hρ hμ, norm_of_mem_digitRotInvFinset hρ hν, one_mul]

lemma card_rotPairs_le (p N ℓ : ℕ) (ρ : GaussianInt) :
    (rotPairs p N ℓ ρ).card ≤ ((p - 1) * p ^ (N - 1)) * ((p - 1) * p ^ (ℓ - 1)) := by
  calc (rotPairs p N ℓ ρ).card ≤ (digitRotFinset p N ρ ×ˢ digitRotInvFinset p ℓ ρ).card :=
        Finset.card_image_le
    _ = (digitRotFinset p N ρ).card * (digitRotInvFinset p ℓ ρ).card := Finset.card_product _ _
    _ ≤ ((p - 1) * p ^ (N - 1)) * ((p - 1) * p ^ (ℓ - 1)) :=
        Nat.mul_le_mul (card_digitRotFinset_le _ _ _) (card_digitRotInvFinset_le _ _ _)

lemma one_mem_rotPairs {p N ℓ : ℕ} (hp : 2 ≤ p) (ρ : GaussianInt) : (1 : ℂ) ∈ rotPairs p N ℓ ρ := by
  have h := mem_rotPairs (one_mem_digitRotFinset (N := N) hp ρ)
    (one_mem_digitRotInvFinset (N := ℓ) hp ρ)
  rwa [one_mul] at h

lemma not_dvd_D5Q (ε : ℝ) : ¬ gPb ∣ D5Q ε := by
  intro h
  rcases prime_gPb.dvd_or_dvd h with h1 | h1
  · exact digitPrime_P.not_star_dvd_digitDen gP_not_dvd_gQ h1
  · exact digitPrime_P.not_star_dvd_star_digitDen gP_not_dvd_gQb h1

lemma not_dvd_D13Q (ε : ℝ) : ¬ gQb ∣ D13Q ε := by
  intro h
  rcases prime_gQb.dvd_or_dvd h with h1 | h1
  · exact digitPrime_Q.not_star_dvd_digitDen gQ_not_dvd_gP h1
  · exact digitPrime_Q.not_star_dvd_star_digitDen gQ_not_dvd_gPb h1

lemma D5Q_ne_zero (ε : ℝ) : D5Q ε ≠ 0 := fun h => not_dvd_D5Q ε (h ▸ dvd_zero _)

lemma D13Q_ne_zero (ε : ℝ) : D13Q ε ≠ 0 := fun h => not_dvd_D13Q ε (h ▸ dvd_zero _)

lemma MdigQ_pos (ε : ℝ) : 0 < MdigQ ε := by
  have h5 : 0 < (D5Q ε).norm.natAbs :=
    Int.natAbs_pos.mpr fun h => D5Q_ne_zero ε (GaussianInt.norm_eq_zero.mp h)
  have h13 : 0 < (D13Q ε).norm.natAbs :=
    Int.natAbs_pos.mpr fun h => D13Q_ne_zero ε (GaussianInt.norm_eq_zero.mp h)
  exact Nat.mul_pos h5 h13

lemma D5Q_dvd_of_MdigQ_dvd {ε : ℝ} {q : GaussianInt} (h : ((MdigQ ε : ℕ) : GaussianInt) ∣ q) :
    D5Q ε ∣ q := by
  refine (dvd_natAbs_norm _).trans (dvd_trans ?_ h)
  unfold MdigQ; push_cast
  exact dvd_mul_right _ _

lemma D13Q_dvd_of_MdigQ_dvd {ε : ℝ} {q : GaussianInt} (h : ((MdigQ ε : ℕ) : GaussianInt) ∣ q) :
    D13Q ε ∣ q := by
  refine (dvd_natAbs_norm _).trans (dvd_trans ?_ h)
  unfold MdigQ; push_cast
  exact dvd_mul_left _ _

lemma ηQ_pos (ε : ℝ) : 0 < ηQ ε := by unfold ηQ; positivity

lemma BdQ_nonneg (ε : ℝ) : 0 ≤ BdQ ε := by unfold BdQ; positivity

lemma norm_of_mem_RotsQ {ε : ℝ} {μ : ℂ} (hμ : μ ∈ RotsQ ε) : ‖μ‖ = 1 := by
  unfold RotsQ at hμ
  rcases Finset.mem_union.mp hμ with h | h
  · exact norm_of_mem_rotPairs gQ_ne_zero' h
  · exact norm_of_mem_rotPairs gP_ne_zero' h

lemma one_le_card_RotsQ (ε : ℝ) : 1 ≤ (RotsQ ε).card :=
  Finset.card_pos.mpr ⟨1, Finset.mem_union_left _ (one_mem_rotPairs (by norm_num) _)⟩

/-- The minor-arc data with digit rotations on both sides. -/
noncomputable def dataQ : ArcData where
  η := ηQ
  M := MdigQ
  Bd := BdQ
  Rots := RotsQ
  η_pos := ηQ_pos
  M_pos := MdigQ_pos
  Bd_nonneg := BdQ_nonneg
  norm_rots := fun _ _ hμ => norm_of_mem_RotsQ hμ
  card_rots := one_le_card_RotsQ

/- ## The interface -/

/-- **The minor-arc proposition with digit rotations on both sides.** -/
theorem dataQ_KL : dataQ.KL := by
  intro ε ϖ hε0 hε1 hϖ0 hϖ1 N₀ s₁ t₁ s₂ t₂ w q hs₁ ht₁ hs₂ ht₂ hM hlow hclose
  change ((MdigQ ε : ℕ) : GaussianInt) ∣ q at hM
  change ‖(q : ℂ) - (rot s₁ t₁ - rot s₂ t₂) * w‖ ≤ ηQ ε / 10 at hclose
  show ∃ s t : ℕ, (s : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + BdQ ε ∧
    (t : ℝ) ≤ N₀ + Real.logb 5 ϖ⁻¹ + BdQ ε ∧ ∃ μ ∈ RotsQ ε, InStripe ε (rot s t * μ) w
  have h5n := size5_nonneg q
  have h13n := size13_nonneg q
  have hq : q ≠ 0 := by
    rintro rfl
    simp only [size5, size13, ite_true] at hlow
    linarith
  have hlog0 : 0 ≤ Real.logb 5 ϖ⁻¹ :=
    Real.logb_nonneg (by norm_num) (by rw [le_inv_comm₀ one_pos hϖ0]; linarith)
  have hBd0 := BdQ_nonneg ε
  set K := ⌈1 / ε⌉₊ with hK
  have hBd5 : ((qA 5 K + 4 + qn 5 K : ℕ) : ℝ) ≤ BdQ ε := by
    unfold BdQ; rw [← hK]; exact_mod_cast Nat.le_add_right _ _
  have hBd13 : ((qA 13 K + 4 + qn 13 K : ℕ) : ℝ) ≤ BdQ ε := by
    unfold BdQ; rw [← hK]; exact_mod_cast Nat.le_add_left _ _
  by_cases h513 : size13 q ≤ size5 q
  · -- Case 1: digit prime `P`, multiplier `Q`.
    set v := multiplicity gPb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      rw [← size5_eq hq]; linarith
    have hcop : IsCoprime gPb (D5Q ε) :=
      prime_gPb.irreducible.coprime_iff_not_dvd.mpr (not_dvd_D5Q ε)
    obtain ⟨q₂, hq₂, hqeq⟩ := decomp_dvd prime_gPb hcop hq (D5Q_dvd_of_MdigQ_dvd hM)
    have hqeq' : q = star gP ^ v * DigitPrime.digitDen 5 (qn 5 ⌈1 / ε⌉₊ + 4) gQ *
        star (DigitPrime.digitDen 5 (pℓ 5 ⌈1 / ε⌉₊) gQ) * q₂ := by
      rw [hqeq, D5Q, ← hv]; simp only [star_gP]; ring
    have hordA : ∀ k, 2 ≤ k →
        orderOf (digitPrime_P.mult (star gQ) k) = (5 - 1) * 5 ^ (k - 1) := by
      intro k hk
      have : NeZero (5 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_P_Qb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordC : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_P.mult (star gQ) n).val : ℕ) : ZMod (5 ^ ℓ)) =
          (5 - 1) * 5 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_P_Qb hn hℓ
    have hη : ηQ ε ≤ (1 / 5 : ℝ) ^ qA 5 ⌈1 / ε⌉₊ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right _ _)
    obtain ⟨a, b, ha, hb, μ, hμ, ν, hν, k, hk⟩ := case_core_quasi digitPrime_P le_rfl
      (by norm_num) gP_not_dvd_gQ gP_not_dvd_gQb (by rw [norm_gQ]; norm_num) hordA hordC hε0 hε1
      hη w q hs₁ ht₁ hs₂ ht₂ hq₂ hqeq' hclose
    rw [← hK] at ha
    refine ⟨a, b, ?_, ?_, μ * ν, Finset.mem_union_left _ (mem_rotPairs hμ hν), k, ?_⟩
    · have h1 : (a : ℝ) ≤ N₀ + v + ((qA 5 K + 4 + qn 5 K : ℕ) : ℝ) := by
        have : a ≤ N₀ + v + (qA 5 K + 4 + qn 5 K) := by omega
        exact_mod_cast this
      linarith
    · have h1 : (b : ℝ) ≤ N₀ := by exact_mod_cast hb
      linarith
    · have hX : rot a b * (μ * ν) * w = ((gP : ℂ) / ((star gP : GaussianInt) : ℂ)) ^ a *
          ((gQ : ℂ) / ((star gQ : GaussianInt) : ℂ)) ^ b * μ * ν * w := by
        unfold rot θ5 θ13; rw [star_gP, star_gQ]; ring
      rw [hX]
      exact hk
  · -- Case 2: digit prime `Q`, multiplier `P`.
    push Not at h513
    set v := multiplicity gQb q with hv
    have hvϖ : (v : ℝ) ≤ Real.logb 5 ϖ⁻¹ := by
      apply le_logb_of_rpow_neg (by norm_num) hϖ0
      have h1 : ϖ ≤ size13 q := by linarith
      rw [size13_eq hq] at h1
      have h2 : (13 : ℝ) ^ (-(v : ℝ)) ≤ (5 : ℝ) ^ (-(v : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
        apply inv_anti₀ (by positivity)
        exact Real.rpow_le_rpow (by norm_num) (by norm_num) (Nat.cast_nonneg _)
      linarith
    have hcop : IsCoprime gQb (D13Q ε) :=
      prime_gQb.irreducible.coprime_iff_not_dvd.mpr (not_dvd_D13Q ε)
    obtain ⟨q₂, hq₂, hqeq⟩ := decomp_dvd prime_gQb hcop hq (D13Q_dvd_of_MdigQ_dvd hM)
    have hqeq' : q = star gQ ^ v * DigitPrime.digitDen 13 (qn 13 ⌈1 / ε⌉₊ + 4) gP *
        star (DigitPrime.digitDen 13 (pℓ 13 ⌈1 / ε⌉₊) gP) * q₂ := by
      rw [hqeq, D13Q, ← hv]; simp only [star_gQ]; ring
    have hordA : ∀ k, 2 ≤ k →
        orderOf (digitPrime_Q.mult (star gP) k) = (13 - 1) * 13 ^ (k - 1) := by
      intro k hk
      have : NeZero (13 ^ k) := ⟨by positivity⟩
      have := orderOf_mult_Q_Pb (n := k) (k := k) hk (by omega)
      rwa [natCast_val_eq] at this
    have hordC : ∀ n ℓ, 2 ≤ n → 1 ≤ ℓ →
        orderOf (((digitPrime_Q.mult (star gP) n).val : ℕ) : ZMod (13 ^ ℓ)) =
          (13 - 1) * 13 ^ (ℓ - 1) :=
      fun n ℓ hn hℓ => orderOf_mult_Q_Pb hn hℓ
    have hη : ηQ ε ≤ (1 / 5 : ℝ) ^ qA 13 ⌈1 / ε⌉₊ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left _ _)
    have hrot : ∀ s t : ℕ, rot s t = ((gQ : ℂ) / ((star gQ : GaussianInt) : ℂ)) ^ t *
        ((gP : ℂ) / ((star gP : GaussianInt) : ℂ)) ^ s := by
      intro s t; unfold rot θ5 θ13; rw [star_gP, star_gQ]; ring
    rw [hrot s₁ t₁, hrot s₂ t₂] at hclose
    obtain ⟨a, b, ha, hb, μ, hμ, ν, hν, k, hk⟩ := case_core_quasi digitPrime_Q (by norm_num)
      le_rfl gQ_not_dvd_gP gQ_not_dvd_gPb (by rw [norm_gP]; norm_num) hordA hordC hε0 hε1
      hη w q ht₁ hs₁ ht₂ hs₂ hq₂ hqeq' hclose
    rw [← hK] at ha
    refine ⟨b, a, ?_, ?_, μ * ν, Finset.mem_union_right _ (mem_rotPairs hμ hν), k, ?_⟩
    · have h1 : (b : ℝ) ≤ N₀ := by exact_mod_cast hb
      linarith
    · have h1 : (a : ℝ) ≤ N₀ + v + ((qA 13 K + 4 + qn 13 K : ℕ) : ℝ) := by
        have : a ≤ N₀ + v + (qA 13 K + 4 + qn 13 K) := by omega
        exact_mod_cast this
      linarith
    · have hX : rot b a * (μ * ν) * w = ((gQ : ℂ) / ((star gQ : GaussianInt) : ℂ)) ^ a *
          ((gP : ℂ) / ((star gP : GaussianInt) : ℂ)) ^ b * μ * ν * w := by
        rw [hrot b a]; ring
      rw [hX]
      exact hk

end Green41

/- ## Section: `FinalQuasi` -/

/-
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

namespace Green41

open Finset

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

/-- The Formal Conjectures-style statement with the answer `True`. -/
theorem green_41.variants.quasi_polynomial_bound : True ↔
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀,
      (minCopies ε : ℝ) ≤ Real.exp (Real.log ε⁻¹ ^ C) :=
  ⟨fun _ => quasiPolynomialBound, fun _ => trivial⟩

#print axioms green_41.variants.quasi_polynomial_bound

end Green41
