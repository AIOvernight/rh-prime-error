import RHPrimeError.Sharp.Residues

/-!
# The vertical segment `re s = 3 / 4` under RH, with the sharp bound

Under the Riemann Hypothesis we bound the integral `I₃₇` of the smoothed Chebyshev integrand
over the segment `re s = 3 / 4`, `|im s| ≤ T` by `O(√X * (log T) ^ 2)`, for suitable heights
`T`. The segment is moved to the line `re s = 1 / 4` across the critical line:

* the residues at the zeros of `ζ` are controlled by `RHPrimeError.exists_sum_inv_norm_le`;
* the integral over `re s = 1 / 4` by
  `RHPrimeError.exists_norm_deriv_riemannZeta_div_le_of_re_eq_quarter`;
* the horizontal segments by `RHPrimeError.exists_good_height`.

## Main result

* `RHPrimeError.exists_norm_I₃₇_le_sqrt`: every interval `[T₀, T₀ + 1]` contains a height `T`
  with `‖I₃₇ ν ε T X (3 / 4)‖ ≤ C * X ^ (1 / 2) * log (T₀ + 4) ^ 2` for `1 ≤ X ≤ T₀`.
-/

open Complex Set MeasureTheory

namespace RHPrimeError

/-- The norm of a sum over a multiset is at most the sum of bounds for the norms. -/
theorem norm_multiset_sum_map_le_sum_map {W : Multiset ℂ} {f : ℂ → ℂ} {b : ℂ → ℝ}
    (h : ∀ ρ ∈ W, ‖f ρ‖ ≤ b ρ) : ‖(W.map f).sum‖ ≤ (W.map b).sum := by
  induction W using Multiset.induction_on with
  | empty => simp
  | cons ρ W ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    have h1 := h ρ (Multiset.mem_cons_self ρ W)
    have h2 := ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)
    linarith [norm_add_le (f ρ) (W.map f).sum]

/-- Under RH, the integral of the smoothed Chebyshev integrand over the segment `re s = 1 / 4`,
`|im s| ≤ T` is `O(X ^ (1 / 4) * log (T + 3) * log (1 + T))`. -/
theorem exists_norm_vIntegral_quarter_le (hRH : RiemannHypothesis) {F : ℝ → ℝ}
    (diffF : ContDiff ℝ 1 F) (suppF : F.support ⊆ Icc (1 / 2) 2) (Fnonneg : ∀ x > 0, 0 ≤ F x)
    (mass_one : ∫ x in Ioi 0, F x / x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 < X → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ T : ℝ, 0 ≤ T →
      ‖VIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (-T) T‖ ≤
        C * X ^ (1 / 4 : ℝ) * Real.log (T + 3) * Real.log (1 + T) := by
  obtain ⟨C₃, C₃pos, hC₃⟩ := exists_norm_deriv_riemannZeta_div_le_of_re_eq_quarter hRH
  obtain ⟨C₄, C₄pos, hC₄⟩ := exists_norm_mellin_smooth1_le_div_norm diffF suppF Fnonneg mass_one
  refine ⟨10 * C₃ * C₄, by positivity, fun X hX ε hε hε1 T hT ↦ ?_⟩
  have hlogT : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have key : ∀ t ∈ Ioc (-T) T,
      ‖SmoothedChebyshevIntegrand F ε X (((1 / 4 : ℝ) : ℂ) + t * I)‖ ≤
        5 * C₃ * C₄ * X ^ (1 / 4 : ℝ) * Real.log (T + 3) * (1 + |t|)⁻¹ := by
    intro t ht
    have htT : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hre : (((1 / 4 : ℝ) : ℂ) + t * I).re = 1 / 4 := by simp
    have him : (((1 / 4 : ℝ) : ℂ) + t * I).im = t := by simp
    obtain ⟨-, hz⟩ := hC₃ _ hre
    rw [him] at hz
    have hz' : ‖deriv riemannZeta (((1 / 4 : ℝ) : ℂ) + t * I) /
        riemannZeta (((1 / 4 : ℝ) : ℂ) + t * I)‖ ≤ C₃ * Real.log (T + 3) :=
      hz.trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity) (by linarith)) C₃pos.le)
    have hM := hC₄ ε hε hε1 (((1 / 4 : ℝ) : ℂ) + t * I) (by rw [hre]; norm_num)
      (by rw [hre]; norm_num)
    have hs : (1 + |t|) / 5 ≤ ‖((1 / 4 : ℝ) : ℂ) + t * I‖ := by
      have h1 := abs_re_le_norm (((1 / 4 : ℝ) : ℂ) + t * I)
      have h2 := abs_im_le_norm (((1 / 4 : ℝ) : ℂ) + t * I)
      rw [hre, abs_of_pos (by norm_num)] at h1
      rw [him] at h2
      linarith
    have hpos : 0 < (1 + |t|) / 5 := by positivity
    have hM' : ‖mellin (fun x ↦ (Smooth1 F ε x : ℂ)) (((1 / 4 : ℝ) : ℂ) + t * I)‖ ≤
        C₄ * (5 * (1 + |t|)⁻¹) :=
      calc _ ≤ C₄ / ‖((1 / 4 : ℝ) : ℂ) + t * I‖ := hM
        _ ≤ C₄ / ((1 + |t|) / 5) := div_le_div_of_nonneg_left C₄pos.le hpos hs
        _ = C₄ * (5 * (1 + |t|)⁻¹) := by
          field_simp
    rw [norm_smoothedChebyshevIntegrand_eq hX, hre]
    have h12 := mul_le_mul hz' hM' (norm_nonneg _) (mul_nonneg C₃pos.le hlogT)
    refine (mul_le_mul_of_nonneg_right h12 (Real.rpow_nonneg hX.le _)).trans (le_of_eq ?_)
    ring
  have hcont : Continuous fun t : ℝ ↦
      5 * C₃ * C₄ * X ^ (1 / 4 : ℝ) * Real.log (T + 3) * (1 + |t|)⁻¹ :=
    continuous_const.mul ((continuous_const.add continuous_abs).inv₀
      fun t ↦ (by positivity : (0 : ℝ) < 1 + |t|).ne')
  have hint := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun t : ℝ ↦ SmoothedChebyshevIntegrand F ε X (((1 / 4 : ℝ) : ℂ) + t * I))
    (by linarith : -T ≤ T) (Filter.Eventually.of_forall key) (hcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_abs hT] at hint
  rw [VIntegral, norm_smul, norm_I, one_mul]
  refine hint.trans (le_of_eq ?_)
  ring

/-- The integral of the smoothed Chebyshev integrand over a horizontal segment
`1 / 4 ≤ re s ≤ 3 / 4`, `im s = y` on which `‖ζ' / ζ‖ ≤ D` is `O(D * X ^ (3 / 4) / |y|)`. -/
theorem exists_norm_hIntegral_le {F : ℝ → ℝ} (diffF : ContDiff ℝ 1 F)
    (suppF : F.support ⊆ Icc (1 / 2) 2) (Fnonneg : ∀ x > 0, 0 ≤ F x)
    (mass_one : ∫ x in Ioi 0, F x / x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ T : ℝ, 0 < T →
      ∀ y D : ℝ, |y| = T → 0 ≤ D →
      (∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → |s.im| = T →
        ‖deriv riemannZeta s / riemannZeta s‖ ≤ D) →
      ‖HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) y‖ ≤
        C * D * X ^ (3 / 4 : ℝ) / T := by
  obtain ⟨C₄, C₄pos, hC₄⟩ := exists_norm_mellin_smooth1_le_div_norm diffF suppF Fnonneg mass_one
  refine ⟨C₄, C₄pos, fun X hX ε hε hε1 T hT y D hy hD0 hD ↦ ?_⟩
  have hXpos : 0 < X := by linarith
  have key : ∀ x ∈ Set.uIoc (1 / 4 : ℝ) (3 / 4),
      ‖SmoothedChebyshevIntegrand F ε X ((x : ℂ) + y * I)‖ ≤ D * (C₄ / T) * X ^ (3 / 4 : ℝ) := by
    intro x hx
    rw [uIoc_of_le (by norm_num)] at hx
    have hre : ((x : ℂ) + y * I).re = x := by simp
    have him : ((x : ℂ) + y * I).im = y := by simp
    have hz := hD ((x : ℂ) + y * I) (by rw [hre]; exact hx.1.le) (by rw [hre]; exact hx.2)
      (by rw [him]; exact hy)
    have hM := hC₄ ε hε hε1 ((x : ℂ) + y * I) (by rw [hre]; linarith [hx.1])
      (by rw [hre]; linarith [hx.2])
    have hs : T ≤ ‖(x : ℂ) + y * I‖ := by
      have := abs_im_le_norm ((x : ℂ) + y * I)
      rwa [him, hy] at this
    have hM' : ‖mellin (fun x ↦ (Smooth1 F ε x : ℂ)) ((x : ℂ) + y * I)‖ ≤ C₄ / T :=
      hM.trans (div_le_div_of_nonneg_left C₄pos.le hT hs)
    have hXx : X ^ x ≤ X ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hx.2
    rw [norm_smoothedChebyshevIntegrand_eq hXpos, hre]
    have h12 := mul_le_mul hz hM' (norm_nonneg _) hD0
    exact mul_le_mul h12 hXx (Real.rpow_nonneg hXpos.le _)
      (mul_nonneg hD0 (div_nonneg C₄pos.le hT.le))
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const key
  have habs : |(3 / 4 : ℝ) - 1 / 4| ≤ 1 := by norm_num [abs_le]
  have hK : 0 ≤ D * (C₄ / T) * X ^ (3 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg hD0 (div_nonneg C₄pos.le hT.le)) (Real.rpow_nonneg hXpos.le _)
  rw [HIntegral]
  refine (hint.trans (mul_le_of_le_one_right hK habs)).trans (le_of_eq ?_)
  ring

/-- **The segment `re s = 3 / 4` under RH.** There is a constant `C` such that every interval
`[T₀, T₀ + 1]` with `1 ≤ T₀` contains a height `T` with
`‖I₃₇ ν ε T X (3 / 4)‖ ≤ C * X ^ (1 / 2) * log (T₀ + 4) ^ 2` for all `1 ≤ X ≤ T₀` and
`ε ∈ (0, 1)`. -/
theorem exists_norm_I₃₇_le_sqrt (hRH : RiemannHypothesis) {F : ℝ → ℝ}
    (diffF : ContDiff ℝ 1 F) (suppF : F.support ⊆ Icc (1 / 2) 2) (Fnonneg : ∀ x > 0, 0 ≤ F x)
    (mass_one : ∫ x in Ioi 0, F x / x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, 1 ≤ T₀ → ∃ T ∈ Icc T₀ (T₀ + 1), ∀ X : ℝ, 1 ≤ X → X ≤ T₀ →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖I₃₇ F ε T X (3 / 4)‖ ≤ C * X ^ (1 / 2 : ℝ) * Real.log (T₀ + 4) ^ 2 := by
  obtain ⟨Cg, Cgpos, hCg⟩ := exists_good_height
  obtain ⟨Cs, Cspos, hCs⟩ := exists_sum_inv_norm_le
  obtain ⟨Cv, Cvpos, hCv⟩ := exists_norm_vIntegral_quarter_le hRH diffF suppF Fnonneg mass_one
  obtain ⟨Ch, Chpos, hCh⟩ := exists_norm_hIntegral_le diffF suppF Fnonneg mass_one
  obtain ⟨C₄, C₄pos, hC₄⟩ := exists_norm_mellin_smooth1_le_div_norm diffF suppF Fnonneg mass_one
  refine ⟨4 * C₄ * Cs + 4 * Cv + 2 * (Ch * Cg), by positivity, fun T₀ hT₀ ↦ ?_⟩
  obtain ⟨T, hT, hgood⟩ := hCg T₀ hT₀
  refine ⟨T, hT, fun X hX hXT ε hε hε1 ↦ ?_⟩
  have hXpos : 0 < X := by linarith
  have hT1 : 1 ≤ T := hT₀.trans hT.1
  have hTpos : 0 < T := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (T₀ + 4) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hlog4 : Real.log (T + 4) ≤ 2 * L := by
    have : Real.log ((T₀ + 4) ^ 2) = 2 * L := by
      rw [Real.log_pow, hL]
      norm_num
    rw [← this]
    exact Real.log_le_log (by positivity) (by nlinarith [hT.2])
  have hlog3 : Real.log (T + 3) ≤ 2 * L :=
    (Real.log_le_log (by positivity) (by linarith)).trans hlog4
  have hlog1 : Real.log (1 + T) ≤ 2 * L :=
    (Real.log_le_log (by positivity) (by linarith)).trans hlog4
  have hlog3' : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hlog1' : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
  have hlog4' : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = X ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := hr ▸ Real.one_le_rpow hX (by norm_num)
  have hX4 : X ^ (1 / 4 : ℝ) ≤ r := hr ▸ Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hX4' : 0 ≤ X ^ (1 / 4 : ℝ) := Real.rpow_nonneg hXpos.le _
  have hX34 : X ^ (3 / 4 : ℝ) / T ≤ r := by
    rw [div_le_iff₀ hTpos]
    have h1 : X ^ (3 / 4 : ℝ) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    rw [Real.rpow_one] at h1
    nlinarith [hT.1]
  rw [← hL, ← hr]
  -- the residue identity
  have hT0 : ∀ s : ℂ, s.re = 1 / 2 → |s.im| = T → riemannZeta s ≠ 0 := fun s h1 h2 ↦
    (hgood s (by rw [h1]; norm_num) (by rw [h1]; norm_num) h2).1
  obtain ⟨W, hW, hord, hid⟩ := exists_rectangleIntegral_smoothedChebyshevIntegrand_eq hRH diffF
    suppF Fnonneg mass_one hε hε1 hXpos hTpos hT0
  -- the sum over zeros
  have hS : ‖(W.map fun ρ ↦ mellin (fun x ↦ (Smooth1 F ε x : ℂ)) ρ * (X : ℂ) ^ ρ).sum‖ ≤
      4 * C₄ * Cs * r * L ^ 2 := by
    have h1 : ∀ ρ ∈ W, ‖mellin (fun x ↦ (Smooth1 F ε x : ℂ)) ρ * (X : ℂ) ^ ρ‖ ≤
        C₄ * r * ‖ρ‖⁻¹ := by
      intro ρ hρ
      have hre := (hW ρ hρ).1
      have hM := hC₄ ε hε hε1 ρ (by rw [hre]; norm_num) (by rw [hre]; norm_num)
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hXpos, hre, ← hr]
      calc _ ≤ C₄ / ‖ρ‖ * r := by gcongr
        _ = C₄ * r * ‖ρ‖⁻¹ := by ring
    have h2 := norm_multiset_sum_map_le_sum_map h1
    rw [Multiset.sum_map_mul_left] at h2
    have h3 := hCs T hT1 W hW hord
    have h4 : Real.log (T + 4) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hlog4' hlog4 2
    calc _ ≤ C₄ * r * (W.map fun ρ ↦ ‖ρ‖⁻¹).sum := h2
      _ ≤ C₄ * r * (Cs * (2 * L) ^ 2) := by
        gcongr
        exact h3.trans (mul_le_mul_of_nonneg_left h4 Cspos.le)
      _ = 4 * C₄ * Cs * r * L ^ 2 := by ring
  -- the left vertical segment
  have hV : ‖VIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (-T) T‖ ≤
      4 * Cv * r * L ^ 2 := by
    refine (hCv X hXpos ε hε hε1 T hTpos.le).trans ?_
    calc Cv * X ^ (1 / 4 : ℝ) * Real.log (T + 3) * Real.log (1 + T)
        ≤ Cv * r * (2 * L) * (2 * L) := by gcongr
      _ = 4 * Cv * r * L ^ 2 := by ring
  -- the horizontal segments
  have hD0 : 0 ≤ Cg * L ^ 2 := by positivity
  have hD : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → |s.im| = T →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ Cg * L ^ 2 := fun s h1 h2 h3 ↦ by
    rw [hL]
    exact (hgood s h1 h2 h3).2
  have hH : ∀ y : ℝ, |y| = T →
      ‖HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) y‖ ≤
        Ch * Cg * r * L ^ 2 := by
    intro y hy
    refine (hCh X hX ε hε hε1 T hTpos y (Cg * L ^ 2) hy hD0 hD).trans ?_
    calc Ch * (Cg * L ^ 2) * X ^ (3 / 4 : ℝ) / T
        = Ch * (Cg * L ^ 2) * (X ^ (3 / 4 : ℝ) / T) := by ring
      _ ≤ Ch * (Cg * L ^ 2) * r := by gcongr
      _ = Ch * Cg * r * L ^ 2 := by ring
  have hHb := hH (-T) (by rw [abs_neg, abs_of_pos hTpos])
  have hHt := hH T (abs_of_pos hTpos)
  -- assembly
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hI : I₃₇ F ε T X (3 / 4) =
      -(W.map fun ρ ↦ mellin (fun x ↦ (Smooth1 F ε x : ℂ)) ρ * (X : ℂ) ^ ρ).sum +
      1 / (2 * Real.pi * I) * (VIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (-T) T -
        HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) (-T) +
        HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) T) := by
    have hVr : VIntegral (SmoothedChebyshevIntegrand F ε X) (3 / 4) (-T) T =
        -(2 * Real.pi * I *
          (W.map fun ρ ↦ mellin (fun x ↦ (Smooth1 F ε x : ℂ)) ρ * (X : ℂ) ^ ρ).sum) +
        (VIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (-T) T -
        HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) (-T) +
        HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) T) := by
      linear_combination hid
    have hdef : I₃₇ F ε T X (3 / 4) =
        1 / (2 * Real.pi * I) * VIntegral (SmoothedChebyshevIntegrand F ε X) (3 / 4) (-T) T := by
      rw [I₃₇, VIntegral, smul_eq_mul]
    rw [hdef, hVr]
    field_simp
  rw [hI]
  have hn1 := norm_add_le
    (-(W.map fun ρ ↦ mellin (fun x ↦ (Smooth1 F ε x : ℂ)) ρ * (X : ℂ) ^ ρ).sum)
    (1 / (2 * Real.pi * I) * (VIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (-T) T -
        HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) (-T) +
        HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) T))
  rw [norm_neg, norm_mul] at hn1
  have hn2 := norm_add_le
    (VIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (-T) T -
        HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) (-T))
    (HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) T)
  have hn3 := norm_sub_le
    (VIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (-T) T)
    (HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) (-T))
  have hn4 := mul_le_of_le_one_left (norm_nonneg
    (VIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (-T) T -
        HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) (-T) +
        HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) T))
    norm_one_div_two_pi_I_le_one
  linarith

end RHPrimeError
