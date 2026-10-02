import Green41SingleExponential.AssemblyDigit

/-!
# The assembly for an arbitrary minor-arc interface

`AssemblyDigit` turns the interface `KL57D` into `minCopies ε ≤ |Rots ε| · G^88`. The argument
uses only a few properties of the data in the interface: the tolerance `η ε > 0`, the modulus
`M ε > 0` that `q` must be divisible by, the exponent budget `Bd ε ≥ 0`, and the extra
rotations `Rots ε` (of norm one, at least one of them). `ArcData` bundles these, `ArcData.KL`
is the interface, and `ArcData.minCopies_le_Rots_G_pow` is the assembled bound with
`G = ⌈max(20/η, M, 1/ε, Bd)⌉ + 66`.
-/

namespace Green41Proof

open Green41

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

end Green41Proof
