import RHPrimeError.Sharp.Main
import RHPrimeError.Theta

/-!
# Sharp error terms for `θ` and `π` under the Riemann Hypothesis

From von Koch's bound `ψ(x) - x = O(√x (log x)²)` under the Riemann Hypothesis
(`chebyshev_psi_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis`) we deduce the corresponding
sharp statements for the Chebyshev function `θ`, for the prime-counting function `π`, and a
corollary on primes in short intervals.

* `ψ - θ = O(√x)` gives `θ(x) - x = O(√x (log x)²)`.
* The exact formula `RHPrimeError.primeCounting_sub_integral_eq` gives
  `π(x) - ∫ t in 2..x, 1 / log t = O(√x log x)`: the factor `(log t)²` in the bound for
  `θ(t) - t` cancels against the kernel `1 / (t (log t)²)`.
* Comparing `θ` at `x` and at `x + C √x (log x)²` gives a prime in between.

The transfer from `θ` to `π` and to short intervals does not use the Riemann Hypothesis.

## Main results

* `chebyshev_theta_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis`
* `primeCounting_sub_integral_isBigO_sqrt_mul_log_of_riemannHypothesis`
* `exists_prime_mem_Ioc_sqrt_mul_log_sq_of_riemannHypothesis`
-/

open Filter Asymptotics MeasureTheory Real

namespace RHPrimeError

/-- `√x = O(√x * (log x) ^ 2)` at infinity. -/
theorem sqrt_isBigO_sqrt_mul_log_sq :
    Real.sqrt =O[atTop] fun x : ℝ => Real.sqrt x * Real.log x ^ 2 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlogx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hsq : 1 ≤ Real.log x ^ 2 := one_le_pow₀ hlogx
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg x),
    Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)), one_mul]
  exact le_mul_of_one_le_right (Real.sqrt_nonneg x) hsq

/-- An asymptotic bound `θ(t) - t = O(√t * (log t) ^ 2)` upgrades to a uniform bound on
`[2, ∞)` with a positive constant, because `θ` is bounded on bounded sets. -/
theorem exists_abs_theta_sub_le_sqrt_mul_log_sq
    (hθ : (fun x : ℝ => Chebyshev.theta x - x) =O[atTop]
      fun x : ℝ => Real.sqrt x * Real.log x ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.theta t - t| ≤ K * (Real.sqrt t * Real.log t ^ 2) := by
  obtain ⟨C, hC⟩ := hθ.bound
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hM : 0 ≤ (Real.log 4 + 1) * max t₀ 2 :=
    mul_nonneg (by linarith) (le_trans (by norm_num) (le_max_right t₀ 2))
  have hM' : 0 ≤ (Real.log 4 + 1) * max t₀ 2 / Real.log 2 ^ 2 := by positivity
  refine ⟨|C| + 1 + (Real.log 4 + 1) * max t₀ 2 / Real.log 2 ^ 2,
    by linarith [abs_nonneg C], ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := by linarith
  have hlogle : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hsq : Real.log 2 ^ 2 ≤ Real.log t ^ 2 := pow_le_pow_left₀ hlog2.le hlogle 2
  have hsqrt : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr (by linarith)
  have hw : Real.log 2 ^ 2 ≤ Real.sqrt t * Real.log t ^ 2 := by
    calc Real.log 2 ^ 2 = 1 * Real.log 2 ^ 2 := (one_mul _).symm
      _ ≤ Real.sqrt t * Real.log t ^ 2 :=
        mul_le_mul hsqrt hsq (by positivity) (Real.sqrt_nonneg t)
  have hw0 : 0 ≤ Real.sqrt t * Real.log t ^ 2 := le_trans (by positivity) hw
  rcases le_or_gt t₀ t with h | h
  · have hb := ht₀ t h
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hw0] at hb
    calc |Chebyshev.theta t - t| ≤ C * (Real.sqrt t * Real.log t ^ 2) := hb
      _ ≤ |C| * (Real.sqrt t * Real.log t ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hw0
      _ ≤ (|C| + 1 + (Real.log 4 + 1) * max t₀ 2 / Real.log 2 ^ 2) *
          (Real.sqrt t * Real.log t ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hw0
  · have hθnonneg := Chebyshev.theta_nonneg t
    have hθle := Chebyshev.theta_le_log4_mul_x ht0
    have habs : |Chebyshev.theta t - t| ≤ (Real.log 4 + 1) * t := by
      rw [abs_le]
      constructor <;> nlinarith
    have htmax : t ≤ max t₀ 2 := le_trans h.le (le_max_left t₀ 2)
    calc |Chebyshev.theta t - t| ≤ (Real.log 4 + 1) * t := habs
      _ ≤ (Real.log 4 + 1) * max t₀ 2 := mul_le_mul_of_nonneg_left htmax (by linarith)
      _ = (Real.log 4 + 1) * max t₀ 2 / Real.log 2 ^ 2 * Real.log 2 ^ 2 := by
        field_simp
      _ ≤ (Real.log 4 + 1) * max t₀ 2 / Real.log 2 ^ 2 * (Real.sqrt t * Real.log t ^ 2) :=
        mul_le_mul_of_nonneg_left hw hM'
      _ ≤ (|C| + 1 + (Real.log 4 + 1) * max t₀ 2 / Real.log 2 ^ 2) *
          (Real.sqrt t * Real.log t ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C]) hw0

/-- Bound for the integral term in `primeCounting_sub_integral_eq`, given a uniform bound
`|θ(t) - t| ≤ K * (√t * (log t) ^ 2)` on `[2, ∞)`: the integral is at most `2 * K * √x`. -/
theorem abs_integral_theta_sub_div_le_sqrt {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.theta t - t| ≤ K * (Real.sqrt t * Real.log t ^ 2)) {x : ℝ} (hx : 2 ≤ x) :
    |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      2 * K * Real.sqrt x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgint : IntervalIntegrable (fun t : ℝ => K * t ^ (-(1 / 2) : ℝ)) volume 2 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hx
    (f := fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
    (g := fun t : ℝ => K * t ^ (-(1 / 2) : ℝ))
    (Eventually.of_forall fun t ht => ?_) hgint
  · rw [Real.norm_eq_abs] at hle
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    have hexp : (-(1 / 2) + 1 : ℝ) = 1 / 2 := by norm_num
    rw [hexp, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have hstep : (Real.sqrt x - Real.sqrt 2) / (1 / 2) ≤ 2 * Real.sqrt x := by
      rw [div_le_iff₀ (by norm_num)]
      linarith [Real.sqrt_nonneg 2]
    calc K * ((Real.sqrt x - Real.sqrt 2) / (1 / 2)) ≤ K * (2 * Real.sqrt x) :=
          mul_le_mul_of_nonneg_left hstep hK
      _ = 2 * K * Real.sqrt x := by ring
  · have ht2 : 2 < t := ht.1
    have ht0 : 0 < t := by linarith
    have hlogt : 0 < Real.log t :=
      lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) ht2.le)
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hden : 0 < t * Real.log t ^ 2 := by positivity
    have hrp : t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹ := by
      rw [Real.rpow_neg ht0.le, Real.sqrt_eq_rpow]
    have hinv : (Real.sqrt t)⁻¹ * t = Real.sqrt t := by
      rw [inv_mul_eq_div, div_eq_iff hsqrt.ne']
      exact (Real.mul_self_sqrt ht0.le).symm
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    calc |Chebyshev.theta t - t| ≤ K * (Real.sqrt t * Real.log t ^ 2) := hbound t ht2.le
      _ = K * ((Real.sqrt t)⁻¹ * t * Real.log t ^ 2) := by rw [hinv]
      _ = K * t ^ (-(1 / 2) : ℝ) * (t * Real.log t ^ 2) := by
        rw [hrp]
        ring

/-- Transfer of the sharp error term from `θ` to `π` by partial summation (no hypothesis on
`ζ`): if `θ(x) - x = O(√x * (log x) ^ 2)` then
`π(x) - ∫ t in 2..x, 1 / log t = O(√x * log x)`. -/
theorem primeCounting_sub_integral_isBigO_sqrt_mul_log_of_theta
    (hθ : (fun x : ℝ => Chebyshev.theta x - x) =O[atTop]
      fun x : ℝ => Real.sqrt x * Real.log x ^ 2) :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t)
      =O[atTop] fun x : ℝ => Real.sqrt x * Real.log x := by
  obtain ⟨K, hKpos, hbound⟩ := exists_abs_theta_sub_le_sqrt_mul_log_sq hθ
  have hK : 0 ≤ K := hKpos.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine IsBigO.of_bound (K + 2 / Real.log 2 + 2 * K) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_ge_atTop 2] with x hxe hx
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hlogpos : 0 < Real.log x := by linarith
  have hsqrt : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hmain : 1 ≤ Real.sqrt x * Real.log x := one_le_mul_of_one_le_of_one_le hsqrt hlogx
  have hterm1 : |(Chebyshev.theta x - x) / Real.log x| ≤ K * (Real.sqrt x * Real.log x) := by
    rw [abs_div, abs_of_pos hlogpos, div_le_iff₀ hlogpos]
    calc |Chebyshev.theta x - x| ≤ K * (Real.sqrt x * Real.log x ^ 2) := hbound x hx
      _ = K * (Real.sqrt x * Real.log x) * Real.log x := by ring
  have hterm2 : |2 / Real.log 2| ≤ 2 / Real.log 2 * (Real.sqrt x * Real.log x) := by
    rw [abs_of_pos (by positivity)]
    exact le_mul_of_one_le_right (by positivity) hmain
  have hterm3 : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      2 * K * (Real.sqrt x * Real.log x) := by
    refine (abs_integral_theta_sub_div_le_sqrt hK hbound hx).trans ?_
    have : Real.sqrt x ≤ Real.sqrt x * Real.log x := le_mul_of_one_le_right hsqrt0 hlogx
    exact mul_le_mul_of_nonneg_left this (by positivity)
  rw [primeCounting_sub_integral_eq hx, Real.norm_eq_abs,
    Real.norm_of_nonneg (mul_nonneg hsqrt0 hlogpos.le)]
  calc |(Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)|
      ≤ |(Chebyshev.theta x - x) / Real.log x| + |2 / Real.log 2| +
        |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| := abs_add_three _ _ _
    _ ≤ K * (Real.sqrt x * Real.log x) + 2 / Real.log 2 * (Real.sqrt x * Real.log x) +
        2 * K * (Real.sqrt x * Real.log x) := by linarith
    _ = (K + 2 / Real.log 2 + 2 * K) * (Real.sqrt x * Real.log x) := by ring

/-- For every `C > 0`, eventually `C * √x * (log x) ^ 2 ≤ x`. -/
theorem eventually_mul_sqrt_mul_log_sq_le {C : ℝ} (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, C * Real.sqrt x * Real.log x ^ 2 ≤ x := by
  have hlittle := ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
    Real.tendsto_sqrt_atTop).bound (by positivity : 0 < 1 / (4 * C))
  filter_upwards [hlittle, eventually_ge_atTop 0] with x hb hx0
  simp only [Function.comp_apply, id, Real.norm_eq_abs] at hb
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (Real.sqrt_nonneg x), Real.log_sqrt hx0]
    at hb
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h1 : C * Real.log x ^ 2 ≤ Real.sqrt x := by
    have h2 : C * Real.log x ^ 2 = 4 * C * (Real.log x / 2) ^ 2 := by ring
    rw [h2]
    calc 4 * C * (Real.log x / 2) ^ 2 ≤ 4 * C * (1 / (4 * C) * Real.sqrt x) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = Real.sqrt x := by field_simp
  calc C * Real.sqrt x * Real.log x ^ 2 = Real.sqrt x * (C * Real.log x ^ 2) := by ring
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left h1 hs
    _ = x := Real.mul_self_sqrt hx0

/-- Primes in short intervals from a bound on `θ` (no hypothesis on `ζ`): if
`|θ(t) - t| ≤ K * (√t * (log t) ^ 2)` for `t ≥ 2` with `K > 0`, then for all large `x` there is
a prime in `(x, x + 4 * K * √x * (log x) ^ 2]`. -/
theorem exists_prime_mem_Ioc_of_abs_theta_sub_le {K : ℝ} (hK : 0 < K)
    (hbound : ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.theta t - t| ≤ K * (Real.sqrt t * Real.log t ^ 2)) :
    ∀ᶠ x : ℝ in atTop,
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 4 * K * Real.sqrt x * Real.log x ^ 2 := by
  filter_upwards [eventually_mul_sqrt_mul_log_sq_le (by positivity : 0 < 4 * K),
    eventually_ge_atTop 1024] with x hsmall hx
  have hx0 : 0 < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  have hlogx : 10 * Real.log 2 ≤ Real.log x := by
    rw [← hlog1024]
    exact Real.log_le_log (by norm_num) hx
  have hlogpos : 0 < Real.log x := by linarith
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  set S : ℝ := Real.sqrt x * Real.log x ^ 2 with hS
  have hSpos : 0 < S := by positivity
  set y : ℝ := x + 4 * K * Real.sqrt x * Real.log x ^ 2 with hy
  have hyx : y - x = 4 * K * S := by rw [hy, hS]; ring
  have hxy : x ≤ y := by nlinarith
  have hy2 : y ≤ 2 * x := by rw [hy]; linarith
  have hy0 : 0 < y := by linarith
  have hsqrty : Real.sqrt y ≤ 3 / 2 * Real.sqrt x := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hx0.le]
    linarith
  have hlogy : Real.log y ≤ 11 / 10 * Real.log x := by
    calc Real.log y ≤ Real.log (2 * x) := Real.log_le_log hy0 hy2
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ 11 / 10 * Real.log x := by linarith
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogysq : Real.log y ^ 2 ≤ (11 / 10 * Real.log x) ^ 2 :=
    pow_le_pow_left₀ hlogy0 hlogy 2
  have hyS : Real.sqrt y * Real.log y ^ 2 ≤ 2 * S := by
    calc Real.sqrt y * Real.log y ^ 2
        ≤ 3 / 2 * Real.sqrt x * (11 / 10 * Real.log x) ^ 2 :=
          mul_le_mul hsqrty hlogysq (sq_nonneg _) (by positivity)
      _ = 363 / 200 * S := by rw [hS]; ring
      _ ≤ 2 * S := by linarith
  have hbx := (abs_le.mp (hbound x (by linarith))).2
  have hby := (abs_le.mp (hbound y (by linarith))).1
  have hKy : K * (Real.sqrt y * Real.log y ^ 2) ≤ K * (2 * S) :=
    mul_le_mul_of_nonneg_left hyS hK.le
  have hKS : 0 < K * S := mul_pos hK hSpos
  refine exists_prime_mem_Ioc_of_theta_lt hx0.le ?_
  linarith

end RHPrimeError

/-- **The Riemann Hypothesis implies `θ(x) - x = O(√x * (log x) ^ 2)`**, where `θ` is the
Chebyshev function `θ(x) = ∑ p ≤ x, log p`. -/
theorem chebyshev_theta_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis (hRH : RiemannHypothesis) :
    (fun x : ℝ => Chebyshev.theta x - x) =O[Filter.atTop]
      fun x : ℝ => Real.sqrt x * Real.log x ^ 2 := by
  have hψ := chebyshev_psi_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis hRH
  have hdiff : (fun x : ℝ => Chebyshev.psi x - Chebyshev.theta x)
      =O[atTop] fun x : ℝ => Real.sqrt x * Real.log x ^ 2 :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans RHPrimeError.sqrt_isBigO_sqrt_mul_log_sq
  refine (hψ.sub hdiff).congr_left fun x => ?_
  ring

/-- **The Riemann Hypothesis implies `π(x) - ∫ t in 2..x, 1 / log t = O(√x * log x)`**, where
`π` is the prime-counting function and the integral is the offset logarithmic integral
`Li(x)`. -/
theorem primeCounting_sub_integral_isBigO_sqrt_mul_log_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t)
      =O[Filter.atTop] fun x : ℝ => Real.sqrt x * Real.log x :=
  RHPrimeError.primeCounting_sub_integral_isBigO_sqrt_mul_log_of_theta
    (chebyshev_theta_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis hRH)

/-- **Primes in short intervals under RH, sharp form.** Assuming the Riemann Hypothesis, there
is a constant `C > 0` such that for all sufficiently large real `x` there is a prime `p` with
`x < p ≤ x + C * √x * (log x) ^ 2`. -/
theorem exists_prime_mem_Ioc_sqrt_mul_log_sq_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + C * Real.sqrt x * Real.log x ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := RHPrimeError.exists_abs_theta_sub_le_sqrt_mul_log_sq
    (chebyshev_theta_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis hRH)
  exact ⟨4 * K, by positivity, RHPrimeError.exists_prime_mem_Ioc_of_abs_theta_sub_le hK hbound⟩
