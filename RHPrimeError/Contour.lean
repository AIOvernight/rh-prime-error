import RHPrimeError.LogDeriv
import RHPrimeError.Mellin

/-!
# Contour estimates under the Riemann Hypothesis

We bound the pieces of the shifted contour appearing in `SmoothedChebyshevPull1` of the
PrimeNumberTheoremAnd project, when the contour is moved to the line `re s = σ₁` with
`1 / 2 < σ₁ < 1`. Under the Riemann Hypothesis:

* `holomorphicOn_logDeriv_riemannZeta`: `ζ' / ζ` is holomorphic on the relevant rectangle
  (minus the pole at `1`);
* `exists_norm_I₂_le`, `exists_norm_I₈_le`: the horizontal segments are `O(X / (ε T))`;
* `exists_norm_I₃₇_le`: the vertical segment is `O(X ^ σ₁ * (log T) ^ 2)`.
-/

open Complex Set MeasureTheory

namespace RHPrimeError

/-- Under RH, `ζ' / ζ` is holomorphic on `[σ₁, 2] × [-T, T]` minus the point `1`, for every
`σ₁ > 1 / 2` and every `T`. -/
theorem holomorphicOn_logDeriv_riemannZeta (hRH : RiemannHypothesis) {σ₁ : ℝ}
    (hσ₁ : 1 / 2 < σ₁) (T : ℝ) :
    HolomorphicOn (deriv riemannZeta / riemannZeta) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}) := by
  refine LogDerivZetaHoloOn (by simp) fun s hs ↦ ?_
  have hre : s.re ∈ Icc σ₁ 2 := hs.1.1
  exact riemannZeta_ne_zero_of_half_lt_re hRH (lt_of_lt_of_le hσ₁ hre.1) hs.2

/-- The norm of the integrand defining the smoothed Chebyshev function. -/
theorem norm_smoothedChebyshevIntegrand_eq {F : ℝ → ℝ} {ε X : ℝ} (hX : 0 < X) (s : ℂ) :
    ‖SmoothedChebyshevIntegrand F ε X s‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ *
        ‖mellin (fun x ↦ (Smooth1 F ε x : ℂ)) s‖ * X ^ s.re := by
  unfold SmoothedChebyshevIntegrand
  rw [norm_mul, norm_mul, neg_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hX]

/-- `X ^ (1 + 1 / log X) = e * X`. -/
theorem rpow_one_add_inv_log {X : ℝ} (hX : 1 < X) :
    X ^ (1 + (Real.log X)⁻¹) = Real.exp 1 * X := by
  have hpos : 0 < X := by linarith
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  rw [Real.rpow_def_of_pos hpos, mul_add, mul_one, mul_inv_cancel₀ hlog, Real.exp_add,
    Real.exp_log hpos, mul_comm]

/-- The normalizing factor `1 / (2 π i)` has norm at most one. -/
theorem norm_one_div_two_pi_I_le_one : ‖1 / (2 * (Real.pi : ℂ) * I)‖ ≤ 1 := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  rw [norm_div, norm_one, norm_mul, norm_mul, norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_ofNat]
  exact (div_le_one (by linarith)).mpr hpi

/-- Under RH, the lower horizontal segment `I₂` of the shifted contour is `O(X / (ε T))`. -/
theorem exists_norm_I₂_le (hRH : RiemannHypothesis) {F : ℝ → ℝ} (diffF : ContDiff ℝ 1 F)
    (suppF : F.support ⊆ Icc (1 / 2) 2) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁) (hσ₁' : σ₁ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 < X → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ T : ℝ, 3 ≤ T →
      ‖I₂ F ε T X σ₁‖ ≤ C * X / (ε * T) := by
  obtain ⟨C₁, C₁pos, hC₁⟩ := MellinOfSmooth1b diffF suppF
  obtain ⟨C₂, C₂pos, hC₂⟩ := exists_norm_deriv_riemannZeta_div_le_log hRH hσ₁
  refine ⟨2 * (C₂ * C₁ * Real.exp 1), by positivity, fun X hX ε hε hε1 T hT ↦ ?_⟩
  have hXpos : 0 < X := by linarith
  have hTpos : 0 < T := by linarith
  have hlog : 1 < Real.log X := logt_gt_one hX.le
  have hσ₀ : 1 + (Real.log X)⁻¹ ≤ 2 := (one_add_inv_log hX.le).le
  have hσ₀' : 1 ≤ 1 + (Real.log X)⁻¹ := by
    have := inv_pos.mpr (lt_trans one_pos hlog)
    linarith
  have hle : σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
  have key : ∀ σ ∈ Set.uIoc σ₁ (1 + (Real.log X)⁻¹),
      ‖SmoothedChebyshevIntegrand F ε X (σ - T * I)‖ ≤
        C₂ * C₁ * Real.exp 1 * X / (ε * T) := by
    intro σ hσ
    rw [uIoc_of_le hle] at hσ
    have hre : ((σ : ℂ) - T * I).re = σ := by simp
    have him : ((σ : ℂ) - T * I).im = -T := by simp
    have hnorm : T ≤ ‖(σ : ℂ) - T * I‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) - T * I)
      rwa [him, abs_neg, abs_of_pos hTpos] at this
    rw [norm_smoothedChebyshevIntegrand_eq hXpos, hre]
    have h1 : ‖deriv riemannZeta (σ - T * I) / riemannZeta (σ - T * I)‖ ≤ C₂ * T := by
      refine (hC₂ _ (by rw [hre]; exact hσ.1.le) (by rw [hre]; linarith [hσ.2])
        (by rw [him, abs_neg, abs_of_pos hTpos]; exact hT)).trans ?_
      rw [him, abs_neg, abs_of_pos hTpos]
      gcongr
      exact (Real.log_le_sub_one_of_pos hTpos).trans (by linarith)
    have h2 : ‖mellin (fun x ↦ (Smooth1 F ε x : ℂ)) (σ - T * I)‖ ≤ C₁ * (ε * T ^ 2)⁻¹ := by
      refine (hC₁ σ₁ (by linarith) _ (by rw [hre]; exact hσ.1.le)
        (by rw [hre]; linarith [hσ.2]) ε hε hε1).trans ?_
      gcongr
    have h3 : X ^ σ ≤ Real.exp 1 * X := by
      rw [← rpow_one_add_inv_log (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.2
    calc _ ≤ C₂ * T * (C₁ * (ε * T ^ 2)⁻¹) * (Real.exp 1 * X) := by gcongr
      _ = _ := by field_simp
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const key
  have hK : 0 ≤ C₂ * C₁ * Real.exp 1 * X / (ε * T) := by positivity
  have habs : |1 + (Real.log X)⁻¹ - σ₁| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  unfold I₂
  rw [norm_mul]
  calc _ ≤ 1 * (C₂ * C₁ * Real.exp 1 * X / (ε * T) * 2) :=
        mul_le_mul norm_one_div_two_pi_I_le_one
          (hint.trans (mul_le_mul_of_nonneg_left habs hK)) (norm_nonneg _) zero_le_one
    _ = _ := by ring

/-- Under RH, the upper horizontal segment `I₈` of the shifted contour is `O(X / (ε T))`. -/
theorem exists_norm_I₈_le (hRH : RiemannHypothesis) {F : ℝ → ℝ} (diffF : ContDiff ℝ 1 F)
    (suppF : F.support ⊆ Icc (1 / 2) 2) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁) (hσ₁' : σ₁ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 < X → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ T : ℝ, 3 ≤ T →
      ‖I₈ F ε T X σ₁‖ ≤ C * X / (ε * T) := by
  obtain ⟨C, Cpos, hC⟩ := exists_norm_I₂_le hRH diffF suppF hσ₁ hσ₁'
  refine ⟨C, Cpos, fun X hX ε hε hε1 T hT ↦ ?_⟩
  rw [I8I2 hX, norm_neg, Complex.norm_conj]
  exact hC X hX ε hε hε1 T hT

/-- The integral of `1 / (1 + |t|)` over `[-T, T]`. -/
theorem integral_inv_one_add_abs {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (-T)..T, (1 + |t|)⁻¹ = 2 * Real.log (1 + T) := by
  have hcont : Continuous fun t : ℝ ↦ (1 + |t|)⁻¹ :=
    (continuous_const.add continuous_abs).inv₀ fun t ↦ (by positivity : (0 : ℝ) < 1 + |t|).ne'
  have hpos : ∫ t in (0 : ℝ)..T, (1 + |t|)⁻¹ = Real.log (1 + T) := by
    have hcongr : ∫ t in (0 : ℝ)..T, (1 + |t|)⁻¹ = ∫ t in (0 : ℝ)..T, (1 + t)⁻¹ := by
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le hT] at ht
      simp only [abs_of_nonneg ht.1]
    rw [hcongr, intervalIntegral.integral_comp_add_left (fun x ↦ x⁻¹) 1,
      integral_inv_of_pos (by norm_num) (by linarith)]
    simp
  have hneg : ∫ t in (-T)..0, (1 + |t|)⁻¹ = Real.log (1 + T) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := T) fun t : ℝ ↦ (1 + |t|)⁻¹
    simp only [abs_neg, neg_zero] at this
    rw [← this, hpos]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _), hneg, hpos]
  ring

/-- Under RH, the vertical segment `I₃₇` of the shifted contour, on the line `re s = σ₁` with
`1 / 2 < σ₁ < 1`, is `O(X ^ σ₁ * (log T) ^ 2)`, uniformly in `ε ∈ (0, 1)`. -/
theorem exists_norm_I₃₇_le (hRH : RiemannHypothesis) {F : ℝ → ℝ} (diffF : ContDiff ℝ 1 F)
    (suppF : F.support ⊆ Icc (1 / 2) 2) (Fnonneg : ∀ x > 0, 0 ≤ F x)
    (mass_one : ∫ x in Ioi 0, F x / x = 1) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁) (hσ₁' : σ₁ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 < X → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ T : ℝ, 3 ≤ T →
      ‖I₃₇ F ε T X σ₁‖ ≤ C * X ^ σ₁ * Real.log T ^ 2 := by
  obtain ⟨C₂, C₂pos, hC₂⟩ := exists_norm_deriv_riemannZeta_div_le_log hRH hσ₁
  obtain ⟨C₃, C₃pos, hC₃⟩ := exists_norm_deriv_riemannZeta_div_le_of_abs_im_le hRH hσ₁ hσ₁'
  obtain ⟨C₄, C₄pos, hC₄⟩ := exists_norm_mellin_smooth1_le_div_norm diffF suppF Fnonneg mass_one
  refine ⟨4 * (8 * C₃ * C₄ + 2 * C₂ * C₄), by positivity, fun X hX ε hε hε1 T hT ↦ ?_⟩
  have hTpos : 0 < T := by linarith
  have hlogT : 1 < Real.log T := logt_gt_one hT
  have hXσ : 0 < X ^ σ₁ := Real.rpow_pos_of_pos hX _
  have key : ∀ t ∈ Ioc (-T) T, ‖SmoothedChebyshevIntegrand F ε X (σ₁ + t * I)‖ ≤
      (8 * C₃ * C₄ + 2 * C₂ * C₄) * X ^ σ₁ * Real.log T * (1 + |t|)⁻¹ := by
    intro t ht
    have htT : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hre : ((σ₁ : ℂ) + t * I).re = σ₁ := by simp
    have him : ((σ₁ : ℂ) + t * I).im = t := by simp
    rw [norm_smoothedChebyshevIntegrand_eq hX, hre]
    have hM := hC₄ ε hε hε1 (σ₁ + t * I) (by rw [hre]; linarith) (by rw [hre]; linarith)
    have hinv : 0 < (1 + |t|)⁻¹ := by positivity
    rcases le_total |t| 3 with h3 | h3
    · have hz := hC₃ t h3
      have hs : (1 / 2 : ℝ) ≤ ‖(σ₁ : ℂ) + t * I‖ := by
        have := Complex.abs_re_le_norm ((σ₁ : ℂ) + t * I)
        rw [hre, abs_of_pos (by linarith)] at this
        linarith
      have hM' : ‖mellin (fun x ↦ (Smooth1 F ε x : ℂ)) (σ₁ + t * I)‖ ≤ 2 * C₄ :=
        hM.trans (by rw [div_le_iff₀ (by linarith)]; nlinarith)
      have h4 : 1 ≤ 4 * (1 + |t|)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        linarith
      have h5 : 1 ≤ Real.log T * (4 * (1 + |t|)⁻¹) := by nlinarith
      have h6 : 0 ≤ 2 * C₂ * C₄ * X ^ σ₁ * Real.log T * (1 + |t|)⁻¹ := by positivity
      calc _ ≤ C₃ * (2 * C₄) * X ^ σ₁ := by gcongr
        _ ≤ C₃ * (2 * C₄) * X ^ σ₁ * (Real.log T * (4 * (1 + |t|)⁻¹)) :=
          le_mul_of_one_le_right (by positivity) h5
        _ ≤ _ := by linarith
    · have htpos : 0 < |t| := by linarith
      have hz := hC₂ (σ₁ + t * I) (by rw [hre]) (by rw [hre]; linarith) (by rw [him]; exact h3)
      rw [him] at hz
      have hz' : ‖deriv riemannZeta (σ₁ + t * I) / riemannZeta (σ₁ + t * I)‖ ≤
          C₂ * Real.log T := hz.trans (by gcongr)
      have hs : |t| ≤ ‖(σ₁ : ℂ) + t * I‖ := by
        have := Complex.abs_im_le_norm ((σ₁ : ℂ) + t * I)
        rwa [him] at this
      have h7 : |t|⁻¹ ≤ 2 * (1 + |t|)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ htpos]
        linarith
      have hM' : ‖mellin (fun x ↦ (Smooth1 F ε x : ℂ)) (σ₁ + t * I)‖ ≤
          C₄ * (2 * (1 + |t|)⁻¹) :=
        calc _ ≤ C₄ / ‖(σ₁ : ℂ) + t * I‖ := hM
          _ ≤ C₄ / |t| := by gcongr
          _ = C₄ * |t|⁻¹ := div_eq_mul_inv _ _
          _ ≤ _ := by gcongr
      have h6 : 0 ≤ 8 * C₃ * C₄ * X ^ σ₁ * Real.log T * (1 + |t|)⁻¹ := by positivity
      calc _ ≤ C₂ * Real.log T * (C₄ * (2 * (1 + |t|)⁻¹)) * X ^ σ₁ := by gcongr
        _ ≤ _ := by linarith
  have hcont : Continuous fun t : ℝ ↦
      (8 * C₃ * C₄ + 2 * C₂ * C₄) * X ^ σ₁ * Real.log T * (1 + |t|)⁻¹ :=
    continuous_const.mul ((continuous_const.add continuous_abs).inv₀
      fun t ↦ (by positivity : (0 : ℝ) < 1 + |t|).ne')
  have hint := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun t : ℝ ↦ SmoothedChebyshevIntegrand F ε X (σ₁ + t * I)) (by linarith : -T ≤ T)
    (Filter.Eventually.of_forall key) (hcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_abs hTpos.le] at hint
  have hlog2 : Real.log (1 + T) ≤ 2 * Real.log T := by
    have hpow : Real.log (T ^ 2) = 2 * Real.log T := by
      rw [Real.log_pow]
      norm_num
    rw [← hpow]
    exact Real.log_le_log (by linarith) (by nlinarith)
  unfold I₃₇
  rw [norm_mul, norm_mul, norm_I, one_mul]
  calc _ ≤ 1 * ((8 * C₃ * C₄ + 2 * C₂ * C₄) * X ^ σ₁ * Real.log T *
        (2 * (2 * Real.log T))) :=
        mul_le_mul norm_one_div_two_pi_I_le_one (hint.trans (by gcongr)) (norm_nonneg _)
          zero_le_one
    _ = _ := by ring

end RHPrimeError
