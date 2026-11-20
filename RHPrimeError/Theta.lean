import Mathlib.NumberTheory.Chebyshev

/-!
# From the Chebyshev function `θ` to `π` and to primes in intervals

Two facts about the Chebyshev function `θ(x) = ∑ p ≤ x, log p` that do not depend on the Riemann
Hypothesis and are used to transfer bounds for `θ(x) - x` to the prime-counting function and
to primes in short intervals.

## Main results

* `RHPrimeError.primeCounting_sub_integral_eq`: for `x ≥ 2`,
  `π(x) - ∫ t in 2..x, 1 / log t
    = (θ(x) - x) / log x + 2 / log 2 + ∫ t in 2..x, (θ(t) - t) / (t * log t ^ 2)`,
  by Abel summation (`Chebyshev.primeCounting_eq_theta_div_log_add_integral`) and an integration
  by parts for `∫ 1 / log t`.
* `RHPrimeError.exists_prime_mem_Ioc_of_theta_lt`: if `θ x < θ y` then there is a prime in
  `(x, y]`.
-/

open MeasureTheory

namespace RHPrimeError

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

/-- If the Chebyshev function `θ` takes a strictly larger value at `y` than at `x`, then there
is a prime in the interval `(x, y]`. -/
theorem exists_prime_mem_Ioc_of_theta_lt {x y : ℝ} (hx : 0 ≤ x)
    (h : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  by_contra hcon
  push Not at hcon
  have hxy : x ≤ y := by
    by_contra hlt
    exact absurd (Chebyshev.theta_mono (le_of_not_ge hlt)) (not_le.mpr h)
  have hy : 0 ≤ y := hx.trans hxy
  refine h.ne ?_
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  refine (Finset.sum_congr ?_ fun _ _ => rfl).symm
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, zero_le, true_and]
  constructor
  · rintro ⟨hp, hprime⟩
    refine ⟨?_, hprime⟩
    by_contra hnot
    have hxp : x < p := by
      by_contra hle
      exact hnot ((Nat.le_floor_iff hx).mpr (not_lt.mp hle))
    exact absurd ((Nat.le_floor_iff hy).mp hp) (not_le.mpr (hcon p hprime hxp))
  · rintro ⟨hp, hprime⟩
    exact ⟨(Nat.le_floor_iff hy).mpr (((Nat.le_floor_iff hx).mp hp).trans hxy), hprime⟩

end RHPrimeError
