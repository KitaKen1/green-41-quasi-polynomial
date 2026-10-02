import Green41SingleExponential.KL57Digit

/-!
# Assembling the covering with digit rotations

The structure is that of `Assembly` and `Estimates` in `Green41DoubleExponentialFC`, with three
changes.

* The pigeonhole modulus is `Mdig ε` instead of `5^u 13^v`; the condition on `δ` is gone.
* `G ≥ max(20/η, Mdig ε, 1/ε, Bd ε) + 66`, so that `Mdig ε ≤ G` and `K = G⁴` still works.
* The orbit is `Θ = {rot s t * μ : s, t ≤ T, μ ∈ Rots ε}`, so the count gains a factor
  `|Rots ε|`: `minCopies ε ≤ |Rots ε| · G^88`.
-/

namespace Green41Proof

open Green41

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

end Green41Proof
