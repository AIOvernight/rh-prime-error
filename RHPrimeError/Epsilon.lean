import RHPrimeError.Sharp.PrimeCounting

/-!
# The `x ^ (1 / 2 + ε)` error terms under the Riemann Hypothesis

The classical "`ε` forms" of the consequences of the Riemann Hypothesis for the distribution of
primes. All four statements are corollaries of the sharp bounds of
`RHPrimeError/Sharp/Main.lean` and `RHPrimeError/Sharp/PrimeCounting.lean`, because
`√x * (log x) ^ n = o(x ^ (1 / 2 + ε))` for every `ε > 0`
(`RHPrimeError.sqrt_mul_log_pow_isLittleO_rpow`).

## Main results

* `chebyshev_psi_sub_isBigO_of_riemannHypothesis`: `ψ(x) - x = O(x ^ (1 / 2 + ε))`.
* `chebyshev_theta_sub_isBigO_of_riemannHypothesis`: `θ(x) - x = O(x ^ (1 / 2 + ε))`.
* `primeCounting_sub_integral_isBigO_of_riemannHypothesis`:
  `π(x) - ∫ t in 2..x, 1 / log t = O(x ^ (1 / 2 + ε))`.
* `exists_prime_mem_Ioc_of_riemannHypothesis`: for all large `x` there is a prime `p` with
  `x < p ≤ x + x ^ (1 / 2 + ε)`.
-/

open Filter Asymptotics

namespace RHPrimeError

/-- `√x * (log x) ^ n = o(x ^ (1 / 2 + ε))` at infinity, for every `ε > 0`. -/
theorem sqrt_mul_log_pow_isLittleO_rpow (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (fun x : ℝ => Real.sqrt x * Real.log x ^ n) =o[atTop] fun x : ℝ => x ^ (1 / 2 + ε) := by
  have hlog : (fun x : ℝ => Real.log x ^ n) =o[atTop] fun x : ℝ => x ^ ε :=
    (isLittleO_log_rpow_rpow_atTop (n : ℝ) hε).congr_left fun x => Real.rpow_natCast _ n
  refine ((isBigO_refl Real.sqrt atTop).mul_isLittleO hlog).congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]

end RHPrimeError

open RHPrimeError

/-- **The Riemann Hypothesis implies `ψ(x) - x = O(x ^ (1 / 2 + ε))`** for every `ε > 0`, where
`ψ` is the Chebyshev function. -/
theorem chebyshev_psi_sub_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε) :=
  fun _ hε => (chebyshev_psi_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis hRH).trans
    (sqrt_mul_log_pow_isLittleO_rpow 2 hε).isBigO

/-- **The Riemann Hypothesis implies `θ(x) - x = O(x ^ (1 / 2 + ε))`** for every `ε > 0`, where
`θ` is the Chebyshev function `θ(x) = ∑ p ≤ x, log p`. -/
theorem chebyshev_theta_sub_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => Chebyshev.theta x - x) =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε) :=
  fun _ hε => (chebyshev_theta_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis hRH).trans
    (sqrt_mul_log_pow_isLittleO_rpow 2 hε).isBigO

/-- **The Riemann Hypothesis implies `π(x) - ∫ t in 2..x, 1 / log t = O(x ^ (1 / 2 + ε))`** for
every `ε > 0`, where `π` is the prime-counting function and the integral is the offset
logarithmic integral `Li(x)`. -/
theorem primeCounting_sub_integral_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t)
        =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε) := by
  intro ε hε
  refine (primeCounting_sub_integral_isBigO_sqrt_mul_log_of_riemannHypothesis hRH).trans ?_
  simpa only [pow_one] using (sqrt_mul_log_pow_isLittleO_rpow 1 hε).isBigO

/-- **Primes in short intervals under RH.** Assuming the Riemann Hypothesis, for every `ε > 0`
and all sufficiently large real `x` there is a prime `p` with `x < p ≤ x + x ^ (1 / 2 + ε)`. -/
theorem exists_prime_mem_Ioc_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (1 / 2 + ε) := by
  intro ε hε
  obtain ⟨C, hC, hprime⟩ := exists_prime_mem_Ioc_sqrt_mul_log_sq_of_riemannHypothesis hRH
  filter_upwards [hprime, (sqrt_mul_log_pow_isLittleO_rpow 2 hε).bound (inv_pos.mpr hC),
    eventually_ge_atTop 0] with x ⟨p, hp, hxp, hpx⟩ hb hx
  refine ⟨p, hp, hxp, hpx.trans ?_⟩
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.rpow_nonneg hx _),
    ← div_eq_inv_mul, le_div_iff₀' hC] at hb
  linarith
