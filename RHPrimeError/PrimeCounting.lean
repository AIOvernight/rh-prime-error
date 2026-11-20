import RHPrimeError.Main

/-!
# The prime-counting function under the Riemann Hypothesis

From the Chebyshev-`ψ` form of the error term under the Riemann Hypothesis
(`chebyshev_psi_sub_isBigO_of_riemannHypothesis`) we deduce the corresponding statements for the
Chebyshev function `θ` and for the prime-counting function `π`.

* `ψ - θ = O(√x)` (Mathlib's `Chebyshev.isBigO_psi_sub_theta_sqrt`) gives
  `θ(x) - x = O(x ^ (1 / 2 + ε))`.
* Abel summation (`Chebyshev.primeCounting_eq_theta_div_log_add_integral`) and an integration by
  parts for `∫ 1 / log t` give, for `x ≥ 2`,
  `π(x) - ∫ t in 2..x, 1 / log t
    = (θ(x) - x) / log x + 2 / log 2 + ∫ t in 2..x, (θ(t) - t) / (t * log t ^ 2)`,
  and each term is `O(x ^ (1 / 2 + ε))`.

The transfer from `θ` to `π` does not use the Riemann Hypothesis: it is stated for an arbitrary
exponent `a > 0` in `RHPrimeError.primeCounting_sub_integral_isBigO_of_theta`.

## Main results

* `chebyshev_theta_sub_isBigO_of_riemannHypothesis`: under RH, `θ(x) - x = O(x ^ (1 / 2 + ε))`.
* `primeCounting_sub_integral_isBigO_of_riemannHypothesis`: under RH,
  `π(x) - ∫ t in 2..x, 1 / log t = O(x ^ (1 / 2 + ε))`.
-/

open Filter Asymptotics MeasureTheory Real

namespace RHPrimeError

/-- `√x = O(x ^ a)` at infinity for every `a ≥ 1 / 2`. -/
theorem sqrt_isBigO_rpow {a : ℝ} (ha : 1 / 2 ≤ a) :
    Real.sqrt =O[atTop] fun x : ℝ => x ^ a := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hpow : x ^ (1 / 2 : ℝ) ≤ x ^ a := Real.rpow_le_rpow_of_exponent_le hx ha
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg x),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) a), one_mul, Real.sqrt_eq_rpow]
  exact hpow

/-- An asymptotic bound `θ(t) - t = O(t ^ a)` with `a ≥ 0` upgrades to a uniform bound on
`[2, ∞)`, because `θ` is bounded on bounded sets. -/
theorem exists_abs_theta_sub_le {a : ℝ} (ha : 0 ≤ a)
    (hθ : (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] fun x : ℝ => x ^ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ K * t ^ a := by
  obtain ⟨C, hC⟩ := hθ.bound
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp hC
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hTnonneg : 0 ≤ (Real.log 4 + 1) * max t₀ 2 :=
    mul_nonneg (by linarith) (le_trans (by norm_num) (le_max_right t₀ 2))
  refine ⟨|C| + (Real.log 4 + 1) * max t₀ 2, add_nonneg (abs_nonneg C) hTnonneg, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := by linarith
  have hpow_nonneg : 0 ≤ t ^ a := Real.rpow_nonneg ht0 a
  have hpow_one : 1 ≤ t ^ a := Real.one_le_rpow (by linarith) ha
  rcases le_or_gt t₀ t with h | h
  · have hb := ht₀ t h
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hpow_nonneg] at hb
    calc |Chebyshev.theta t - t| ≤ C * t ^ a := hb
      _ ≤ |C| * t ^ a := mul_le_mul_of_nonneg_right (le_abs_self C) hpow_nonneg
      _ ≤ (|C| + (Real.log 4 + 1) * max t₀ 2) * t ^ a :=
        mul_le_mul_of_nonneg_right (by linarith) hpow_nonneg
  · have hθnonneg := Chebyshev.theta_nonneg t
    have hθle := Chebyshev.theta_le_log4_mul_x ht0
    have habs : |Chebyshev.theta t - t| ≤ (Real.log 4 + 1) * t := by
      rw [abs_le]
      constructor <;> nlinarith
    have htmax : t ≤ max t₀ 2 := le_trans h.le (le_max_left t₀ 2)
    calc |Chebyshev.theta t - t| ≤ (Real.log 4 + 1) * t := habs
      _ ≤ (Real.log 4 + 1) * max t₀ 2 := mul_le_mul_of_nonneg_left htmax (by linarith)
      _ ≤ (Real.log 4 + 1) * max t₀ 2 * t ^ a := le_mul_of_one_le_right hTnonneg hpow_one
      _ ≤ (|C| + (Real.log 4 + 1) * max t₀ 2) * t ^ a :=
        mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C]) hpow_nonneg

/-- `1 / log t` is interval integrable on `[2, x]` for `x ≥ 2`. -/
theorem intervalIntegrable_one_div_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  fun_prop (disch := assumption)

/-- Integration by parts for the offset logarithmic integral:
`∫ t in 2..x, 1 / log t = x / log x - 2 / log 2 + ∫ t in 2..x, 1 / log t ^ 2`. -/
theorem integral_one_div_log_eq {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / Real.log t =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hint1 := intervalIntegrable_one_div_log hx
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hFTC : ∫ t in (2 : ℝ)..x, (1 / Real.log t - 1 / Real.log t ^ 2) =
      x / Real.log x - 2 / Real.log 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => t / Real.log t)
      (fun t ht => ?_) (hint1.sub hint2)
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hderiv := (hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hlog
    convert hderiv using 1
    · rfl
    · simp only [id]
      field_simp
  rw [intervalIntegral.integral_sub hint1 hint2] at hFTC
  linarith

/-- The exact formula for the error term of the prime-counting function in terms of the error
term of `θ`: for `x ≥ 2`,
`π(x) - ∫ t in 2..x, 1 / log t
  = (θ(x) - x) / log x + 2 / log 2 + ∫ t in 2..x, (θ(t) - t) / (t * log t ^ 2)`. -/
theorem primeCounting_sub_integral_eq {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t =
      (Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
  have hint1 : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2))
      volume 2 x := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx, ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hsplit : ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) =
      (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
        ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    rw [← intervalIntegral.integral_sub hint1 hint2]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    field_simp
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx, integral_one_div_log_eq hx,
    hsplit]
  ring

/-- Bound for the integral term in `primeCounting_sub_integral_eq`, given a uniform bound
`|θ(t) - t| ≤ K * t ^ a` on `[2, ∞)`. -/
theorem abs_integral_theta_sub_div_le {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ K * t ^ a) {x : ℝ} (hx : 2 ≤ x) :
    |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      K / (a * Real.log 2 ^ 2) * x ^ a := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgint : IntervalIntegrable (fun t : ℝ => K / Real.log 2 ^ 2 * t ^ (a - 1)) volume 2 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hx
    (f := fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
    (g := fun t : ℝ => K / Real.log 2 ^ 2 * t ^ (a - 1))
    (Eventually.of_forall fun t ht => ?_) hgint
  · rw [Real.norm_eq_abs] at hle
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    have h2pow : 0 ≤ (2 : ℝ) ^ (a - 1 + 1) := Real.rpow_nonneg (by norm_num) _
    have hxpow : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith) _
    have hcoef : 0 ≤ K / Real.log 2 ^ 2 := by positivity
    have hstep : (x ^ (a - 1 + 1) - (2 : ℝ) ^ (a - 1 + 1)) / (a - 1 + 1) ≤ x ^ a / a := by
      rw [sub_add_cancel]
      rw [sub_add_cancel] at h2pow
      exact div_le_div_of_nonneg_right (by linarith) ha.le
    calc K / Real.log 2 ^ 2 * ((x ^ (a - 1 + 1) - (2 : ℝ) ^ (a - 1 + 1)) / (a - 1 + 1))
        ≤ K / Real.log 2 ^ 2 * (x ^ a / a) := mul_le_mul_of_nonneg_left hstep hcoef
      _ = K / (a * Real.log 2 ^ 2) * x ^ a := by field_simp
  · have ht2 : 2 < t := ht.1
    have ht0 : 0 < t := by linarith
    have hlogle : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2.le
    have hsq : Real.log 2 ^ 2 ≤ Real.log t ^ 2 := pow_le_pow_left₀ hlog2.le hlogle 2
    have hden : 0 < t * Real.log 2 ^ 2 := by positivity
    have hlogt : 0 < Real.log t := lt_of_lt_of_le hlog2 hlogle
    have hnum : 0 ≤ K * t ^ a := mul_nonneg hK (Real.rpow_nonneg ht0.le a)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < t * Real.log t ^ 2)]
    calc |Chebyshev.theta t - t| / (t * Real.log t ^ 2)
        ≤ K * t ^ a / (t * Real.log t ^ 2) :=
          div_le_div_of_nonneg_right (hbound t ht2.le) (by positivity)
      _ ≤ K * t ^ a / (t * Real.log 2 ^ 2) :=
          div_le_div_of_nonneg_left hnum hden (mul_le_mul_of_nonneg_left hsq ht0.le)
      _ = K / Real.log 2 ^ 2 * t ^ (a - 1) := by
          rw [Real.rpow_sub_one ht0.ne']
          field_simp

/-- Transfer of an error term from `θ` to `π` by partial summation (no hypothesis on `ζ`):
if `θ(x) - x = O(x ^ a)` with `a > 0`, then `π(x) - ∫ t in 2..x, 1 / log t = O(x ^ a)`. -/
theorem primeCounting_sub_integral_isBigO_of_theta {a : ℝ} (ha : 0 < a)
    (hθ : (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] fun x : ℝ => x ^ a) :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t)
      =O[atTop] fun x : ℝ => x ^ a := by
  obtain ⟨K, hK, hbound⟩ := exists_abs_theta_sub_le ha.le hθ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine IsBigO.of_bound (K + 2 / Real.log 2 + K / (a * Real.log 2 ^ 2)) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_ge_atTop 2] with x hxe hx
  have hx0 : 0 < x := by linarith
  have hpow_nonneg : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le a
  have hpow_one : 1 ≤ x ^ a := Real.one_le_rpow (by linarith) ha.le
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact hxe
  have hterm1 : |(Chebyshev.theta x - x) / Real.log x| ≤ K * x ^ a := by
    rw [abs_div, abs_of_pos (by linarith : 0 < Real.log x)]
    calc |Chebyshev.theta x - x| / Real.log x ≤ |Chebyshev.theta x - x| :=
          div_le_self (abs_nonneg _) hlogx
      _ ≤ K * x ^ a := hbound x hx
  have hterm2 : |2 / Real.log 2| ≤ 2 / Real.log 2 * x ^ a := by
    rw [abs_of_pos (by positivity)]
    exact le_mul_of_one_le_right (by positivity) hpow_one
  have hterm3 := abs_integral_theta_sub_div_le ha hK hbound hx
  rw [primeCounting_sub_integral_eq hx, Real.norm_eq_abs, Real.norm_of_nonneg hpow_nonneg]
  calc |(Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)|
      ≤ |(Chebyshev.theta x - x) / Real.log x| + |2 / Real.log 2| +
        |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| := abs_add_three _ _ _
    _ ≤ K * x ^ a + 2 / Real.log 2 * x ^ a + K / (a * Real.log 2 ^ 2) * x ^ a := by
        linarith
    _ = (K + 2 / Real.log 2 + K / (a * Real.log 2 ^ 2)) * x ^ a := by ring

end RHPrimeError

/-- **The Riemann Hypothesis implies `θ(x) - x = O(x ^ (1 / 2 + ε))`** for every `ε > 0`, where
`θ` is the Chebyshev function `θ(x) = ∑ p ≤ x, log p`. -/
theorem chebyshev_theta_sub_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => Chebyshev.theta x - x) =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε) := by
  intro ε hε
  have hψ := chebyshev_psi_sub_isBigO_of_riemannHypothesis hRH ε hε
  have hdiff : (fun x : ℝ => Chebyshev.psi x - Chebyshev.theta x)
      =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε) :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans (RHPrimeError.sqrt_isBigO_rpow (by linarith))
  refine (hψ.sub hdiff).congr_left fun x => ?_
  ring

/-- **The Riemann Hypothesis implies `π(x) - ∫ t in 2..x, 1 / log t = O(x ^ (1 / 2 + ε))`** for
every `ε > 0`, where `π` is the prime-counting function and the integral is the offset
logarithmic integral `Li(x)`. -/
theorem primeCounting_sub_integral_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t)
        =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε) := by
  intro ε hε
  exact RHPrimeError.primeCounting_sub_integral_isBigO_of_theta (by linarith)
    (chebyshev_theta_sub_isBigO_of_riemannHypothesis hRH ε hε)
