import RHPrimeError.Sharp.Landau

/-!
# Local structure of the zeros of the Riemann zeta function

We apply Landau's lemma (`RHPrimeError.exists_isZeroFactorization`) to the entire function
`riemannZeta₁ s = (s - 1) * ζ s` on the discs of centre `3 / 2 + τ * I` and radii
`27 / 20 < 69 / 50 < 71 / 50 < 29 / 20`. The inner disc contains the box
`[1 / 4, 3 / 4] × [τ - 1 / 2, τ + 1 / 2]`.

## Main results

* `RHPrimeError.norm_riemannZeta₁_le`: `‖(s - 1) ζ(s)‖ ≤ (‖s‖ + 1) / 2 + ‖s‖ ‖s - 1‖ / re s`
  for `0 < re s`.
* `RHPrimeError.exists_isZeroFactorization_riemannZeta₁`: for every real `τ` the function
  `riemannZeta₁` factors on the disc around `3 / 2 + τ * I` as a polynomial with at most
  `A * log (|τ| + 3)` roots times a zero-free function `g` with `‖g' / g‖ ≤ A * log (|τ| + 3)`.
* `RHPrimeError.IsZeroFactorization.deriv_riemannZeta_div_eq`: the resulting formula for
  `ζ' / ζ`.
-/

open Metric Set Complex

namespace RHPrimeError

/-- For `s ≠ 1`, `riemannZeta₁ s = (s - 1) * ζ s`. -/
theorem riemannZeta₁_eq_sub_one_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  have h0 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [riemannZeta_eq_inv_sub_mul hs]
  field_simp

/-- For `s ≠ 1`, `ζ s = 0` if and only if `riemannZeta₁ s = 0`. -/
theorem riemannZeta_eq_zero_iff {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = 0 ↔ riemannZeta₁ s = 0 := by
  rw [riemannZeta₁_eq_sub_one_mul hs, mul_eq_zero, or_iff_right (sub_ne_zero.2 hs)]

/-- The logarithmic derivative of `ζ` in terms of that of `riemannZeta₁`. -/
theorem deriv_riemannZeta_div_eq {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      deriv riemannZeta₁ s / riemannZeta₁ s - (s - 1)⁻¹ := by
  have h0 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  have h1 : HasDerivAt (fun w : ℂ ↦ (w - 1)⁻¹) (-((s - 1) ^ 2)⁻¹) s := by
    refine HasDerivAt.congr_deriv (((hasDerivAt_id s).sub_const 1).inv h0) ?_
    simp [neg_div]
  have h2 : HasDerivAt riemannZeta₁ (deriv riemannZeta₁ s) s :=
    differentiable_riemannZeta₁.differentiableAt.hasDerivAt
  have h3 : HasDerivAt riemannZeta
      (-((s - 1) ^ 2)⁻¹ * riemannZeta₁ s + (s - 1)⁻¹ * deriv riemannZeta₁ s) s := by
    refine (h1.mul h2).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    exact riemannZeta_eq_inv_sub_mul hw
  rw [h3.deriv, riemannZeta_eq_inv_sub_mul hs]
  field_simp
  ring

/-- A polynomial bound for `(s - 1) * ζ s` in the half-plane `0 < re s`. -/
theorem norm_riemannZeta₁_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₁ s‖ ≤ (‖s‖ + 1) / 2 + ‖s‖ * ‖s - 1‖ / s.re := by
  by_cases hs1 : s = 1
  · subst hs1
    simp
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have h0 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  obtain ⟨J, hJ⟩ : ∃ J : ℂ,
      J = ∫ x in Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := ⟨_, rfl⟩
  have hJle : ‖J‖ ≤ 1 / s.re := by
    have h := ZetaBnd_aux1b 1 le_rfl (σ := s.re) (t := s.im) hs
    rw [re_add_im, ← hJ] at h
    simpa using h
  have hz : riemannZeta s = 1 + 1 / (s - 1) - 1 / 2 + s * J := by
    rw [← Zeta0EqZeta one_pos hs hs1, riemannZeta0, ← hJ]
    have h1 : (1 - s) ≠ 0 := fun h ↦ h0 (by linear_combination -h)
    simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
      Nat.cast_one, zero_cpow hs0, one_cpow, div_zero, zero_add]
    field_simp
    ring
  have hform : riemannZeta₁ s = (s + 1) / 2 + s * (s - 1) * J := by
    rw [riemannZeta₁_eq_sub_one_mul hs1, hz]
    field_simp
    ring
  rw [hform]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, Complex.norm_ofNat]
    gcongr
    exact (norm_add_le s 1).trans_eq (by rw [norm_one])
  · rw [norm_mul, norm_mul]
    calc ‖s‖ * ‖s - 1‖ * ‖J‖ ≤ ‖s‖ * ‖s - 1‖ * (1 / s.re) := by gcongr
      _ = ‖s‖ * ‖s - 1‖ / s.re := by ring

/-- The box `|re s - 3 / 2| ≤ 5 / 4`, `|im s - τ| ≤ 1 / 2` lies in the closed disc of centre
`3 / 2 + τ * I` and radius `27 / 20`. -/
theorem mem_closedBall_of_abs_le {s : ℂ} {τ : ℝ} (hre : |s.re - 3 / 2| ≤ 5 / 4)
    (him : |s.im - τ| ≤ 1 / 2) : s ∈ closedBall (3 / 2 + τ * I : ℂ) (27 / 20) := by
  rw [mem_closedBall, dist_eq_norm]
  have h1 : ‖s - (3 / 2 + τ * I)‖ ^ 2 = (s.re - 3 / 2) ^ 2 + (s.im - τ) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    simp
    ring
  have h2 : (s.re - 3 / 2) ^ 2 ≤ (5 / 4) ^ 2 := sq_le_sq' (abs_le.1 hre).1 (abs_le.1 hre).2
  have h3 : (s.im - τ) ^ 2 ≤ (1 / 2) ^ 2 := sq_le_sq' (abs_le.1 him).1 (abs_le.1 him).2
  refine (abs_le_of_sq_le_sq' ?_ (by norm_num)).2
  rw [h1]
  norm_num at h2 h3 ⊢
  linarith

/-- Points of the closed disc of centre `3 / 2 + τ * I` and radius `71 / 50` have real part at
least `2 / 25` and norm at most `|τ| + 3`. -/
theorem re_ge_and_norm_le_of_mem_closedBall {s : ℂ} {τ : ℝ}
    (hs : s ∈ closedBall (3 / 2 + τ * I : ℂ) (71 / 50)) :
    2 / 25 ≤ s.re ∧ ‖s‖ ≤ |τ| + 3 := by
  rw [mem_closedBall, dist_eq_norm] at hs
  constructor
  · have h1 := (abs_re_le_norm (s - (3 / 2 + τ * I))).trans hs
    have h2 : (s - (3 / 2 + τ * I)).re = s.re - 3 / 2 := by simp
    rw [h2, abs_le] at h1
    linarith [h1.1]
  · have h1 : ‖(3 / 2 + τ * I : ℂ)‖ ≤ 3 / 2 + |τ| := by
      refine (norm_add_le _ _).trans ?_
      simp
    have h2 := norm_add_le (s - (3 / 2 + τ * I)) (3 / 2 + τ * I)
    rw [sub_add_cancel] at h2
    linarith

/-- **Local structure of the zeros of `ζ`.** There is a constant `A` such that for every real
`τ` the function `riemannZeta₁ s = (s - 1) ζ(s)` factors on the disc of centre `3 / 2 + τ * I`
and radius `71 / 50` as `∏ ρ ∈ Z, (s - ρ) * g s`, where `Z` consists of at most
`A * log (|τ| + 3)` points of the closed disc of radius `69 / 50`, `g` has no zeros there, and
`‖g' / g‖ ≤ A * log (|τ| + 3)` on the closed disc of radius `27 / 20`. -/
theorem exists_isZeroFactorization_riemannZeta₁ :
    ∃ A : ℝ, 0 < A ∧ ∀ τ : ℝ, ∃ (Z : Multiset ℂ) (g : ℂ → ℂ),
      IsZeroFactorization riemannZeta₁ (3 / 2 + τ * I) (69 / 50) (71 / 50) Z g ∧
      (Z.card : ℝ) ≤ A * Real.log (|τ| + 3) ∧
      ∀ z ∈ closedBall (3 / 2 + τ * I : ℂ) (27 / 20),
        ‖deriv g z / g z‖ ≤ A * Real.log (|τ| + 3) := by
  obtain ⟨K, hK, hLandau⟩ := exists_isZeroFactorization (r₁ := 27 / 20) (r₂ := 69 / 50)
    (r := 71 / 50) (R := 29 / 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Real.log (71 / 50 / (69 / 50)) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := hlam ▸ Real.log_pos (by norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ‖riemannZeta 3 / riemannZeta (3 / 2)‖ := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    rw [hm, norm_pos_iff]
    exact div_ne_zero (riemannZeta_ne_zero_of_one_le_re (by norm_num))
      (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = |Real.log (26 / m)| + 4 := ⟨_, rfl⟩
  have hE₀pos : 0 < E₀ := by
    rw [hE₀]
    positivity
  refine ⟨E₀ / lam + K * E₀ + 1, by positivity, fun τ ↦ ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = 3 / 2 + τ * I := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (|τ| + 3) := ⟨_, rfl⟩
  have hτ0 : 0 ≤ |τ| := abs_nonneg τ
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  -- the upper bound on the disc
  have hB : ∀ z ∈ closedBall c (71 / 50), ‖riemannZeta₁ z‖ ≤ 13 * (|τ| + 4) ^ 2 := by
    intro z hz
    obtain ⟨hre, hnorm⟩ := re_ge_and_norm_le_of_mem_closedBall (hc ▸ hz)
    have hre0 : 0 < z.re := by linarith
    have h1 : ‖z - 1‖ ≤ |τ| + 4 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      linarith
    have h2 : ‖z‖ * ‖z - 1‖ / z.re ≤ (|τ| + 3) * (|τ| + 4) / (2 / 25) := by gcongr
    refine (norm_riemannZeta₁_le hre0).trans ?_
    have h3 : (‖z‖ + 1) / 2 ≤ (|τ| + 4) / 2 := by linarith
    nlinarith
  -- the lower bound at the centre
  have hc1 : c ≠ 1 := by
    rw [hc]
    intro h
    have := congrArg Complex.re h
    simp at this
    norm_num at this
  have hcent : m / 2 ≤ ‖riemannZeta₁ c‖ := by
    rw [riemannZeta₁_eq_sub_one_mul hc1, norm_mul]
    have h1 : 1 / 2 ≤ ‖c - 1‖ := by
      have := abs_re_le_norm (c - 1)
      have e : (c - 1).re = 1 / 2 := by
        rw [hc]
        simp
        norm_num
      rw [e, abs_of_pos (by norm_num)] at this
      exact this
    have h2 : m ≤ ‖riemannZeta c‖ := by
      have := ZetaFixedLowerBound τ
      rw [ge_iff_le, ← NNReal.coe_le_coe] at this
      rw [hm, hc, mul_comm (τ : ℂ) I]
      simpa using this
    nlinarith [norm_nonneg (riemannZeta c), norm_nonneg (c - 1)]
  have hcpos : 0 < ‖riemannZeta₁ c‖ := lt_of_lt_of_le (by positivity) hcent
  obtain ⟨Z, g, hfact, hcard, hbound⟩ := hLandau riemannZeta₁ c (13 * (|τ| + 4) ^ 2)
    differentiable_riemannZeta₁.differentiableOn hB (norm_pos_iff.1 hcpos)
  -- the bound for `log (B / ‖f c‖)`
  have hE : Real.log (13 * (|τ| + 4) ^ 2 / ‖riemannZeta₁ c‖) ≤ E₀ * L := by
    have h1 : 13 * (|τ| + 4) ^ 2 / ‖riemannZeta₁ c‖ ≤ 26 / m * (|τ| + 4) ^ 2 := by
      rw [div_le_iff₀ hcpos]
      have h2 : 26 / m * (|τ| + 4) ^ 2 * (m / 2) = 13 * (|τ| + 4) ^ 2 := by
        field_simp
        ring
      have h3 : 0 ≤ 26 / m * (|τ| + 4) ^ 2 := by positivity
      nlinarith
    have h4 : Real.log (|τ| + 4) ≤ 2 * L := by
      have : Real.log ((|τ| + 3) ^ 2) = 2 * L := by
        rw [Real.log_pow, hL]
        norm_num
      rw [← this]
      exact Real.log_le_log (by positivity) (by nlinarith)
    calc Real.log (13 * (|τ| + 4) ^ 2 / ‖riemannZeta₁ c‖)
        ≤ Real.log (26 / m * (|τ| + 4) ^ 2) := Real.log_le_log (by positivity) h1
      _ = Real.log (26 / m) + 2 * Real.log (|τ| + 4) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        norm_num
      _ ≤ |Real.log (26 / m)| * L + 2 * (2 * L) := by
        have := le_abs_self (Real.log (26 / m))
        have := abs_nonneg (Real.log (26 / m))
        gcongr
        nlinarith
      _ = E₀ * L := by
        rw [hE₀]
        ring
  rw [← hc]
  refine ⟨Z, g, hfact, ?_, fun z hz ↦ ?_⟩
  · have h1 : (Z.card : ℝ) * lam ≤ E₀ * L := (hlam ▸ hcard).trans hE
    have h2 : (Z.card : ℝ) ≤ E₀ * L / lam := by rwa [le_div_iff₀ hlam0]
    have h3 : E₀ * L / lam = E₀ / lam * L := by ring
    have h4 : 0 ≤ (K * E₀ + 1) * L := by positivity
    rw [← hL]
    linarith
  · have h1 := (hbound z hz).trans (mul_le_mul_of_nonneg_left hE hK)
    have h2 : 0 ≤ (E₀ / lam + 1) * L := by positivity
    rw [← hL]
    linarith

/-- The formula `ζ' / ζ = ∑ ρ ∈ Z, 1 / (s - ρ) + g' / g - 1 / (s - 1)` attached to a
factorisation of `riemannZeta₁` in a disc. -/
theorem IsZeroFactorization.deriv_riemannZeta_div_eq {g : ℂ → ℂ} {c : ℂ} {r₂ r : ℝ}
    {Z : Multiset ℂ} (h : IsZeroFactorization riemannZeta₁ c r₂ r Z g) (h2r : r₂ < r) {s : ℂ}
    (hs : s ∈ closedBall c r₂) (hsZ : s ∉ Z) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 ∧ deriv riemannZeta s / riemannZeta s =
      (Z.map fun ρ ↦ (s - ρ)⁻¹).sum + deriv g s / g s - (s - 1)⁻¹ := by
  have h0 := h.ne_zero_of_notMem h2r hs hsZ
  refine ⟨fun hζ ↦ h0 ((riemannZeta_eq_zero_iff hs1).1 hζ), ?_⟩
  rw [RHPrimeError.deriv_riemannZeta_div_eq hs1 h0, h.deriv_div_eq h2r hs hsZ]

/-- A member of a factorisation multiset of `riemannZeta₁` is a zero of `ζ`. -/
theorem IsZeroFactorization.riemannZeta_eq_zero {g : ℂ → ℂ} {c : ℂ} {r₂ r : ℝ}
    {Z : Multiset ℂ} (h : IsZeroFactorization riemannZeta₁ c r₂ r Z g) (h2r : r₂ < r) {ρ : ℂ}
    (hρ : ρ ∈ Z) : ρ ≠ 1 ∧ riemannZeta ρ = 0 := by
  have h0 := h.eq_zero_of_mem h2r hρ
  have h1 : ρ ≠ 1 := by
    rintro rfl
    simp at h0
  exact ⟨h1, (riemannZeta_eq_zero_iff h1).2 h0⟩

/-- A bound for the norm of a sum over a multiset. -/
theorem norm_multiset_sum_map_le {Z : Multiset ℂ} {F : ℂ → ℂ} {M : ℝ}
    (h : ∀ ρ ∈ Z, ‖F ρ‖ ≤ M) : ‖(Z.map F).sum‖ ≤ Z.card * M := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons ρ Z ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have h1 := h ρ (Multiset.mem_cons_self ρ Z)
    have h2 := ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)
    push_cast
    linarith [norm_add_le (F ρ) (Z.map F).sum]

end RHPrimeError
