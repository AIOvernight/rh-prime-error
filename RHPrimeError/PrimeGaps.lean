import RHPrimeError.PrimeCounting

/-!
# Primes in short intervals under the Riemann Hypothesis

Under the Riemann Hypothesis, `θ(x) - x = O(x ^ (1 / 2 + ε))` for every `ε > 0`
(`chebyshev_theta_sub_isBigO_of_riemannHypothesis`). Comparing `θ` at `x` and at
`x + x ^ (1 / 2 + ε)` shows that `θ` strictly increases on this interval once `x` is large,
so the interval contains a prime.

## Main results

* `RHPrimeError.exists_prime_mem_Ioc_of_theta_lt`: if `θ x < θ y` then there is a prime in
  `(x, y]`.
* `exists_prime_mem_Ioc_of_riemannHypothesis`: under RH, for every `ε > 0` and all large `x`
  there is a prime `p` with `x < p ≤ x + x ^ (1 / 2 + ε)`.
-/

open Filter Asymptotics Real

namespace RHPrimeError

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

/-- Under RH, for `0 < ε ≤ 1 / 2` and all large `x` there is a prime in
`(x, x + x ^ (1 / 2 + ε)]`. -/
theorem exists_prime_mem_Ioc_of_le_half (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε ≤ 1 / 2) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (1 / 2 + ε) := by
  obtain ⟨C, hCpos, hC⟩ :=
    (chebyshev_theta_sub_isBigO_of_riemannHypothesis hRH (ε / 2) (by positivity)).exists_pos
  rw [isBigOWith_iff] at hC
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp hC
  have hlarge : ∀ᶠ x : ℝ in atTop, 3 * C < x ^ (ε / 2) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 2)).eventually_gt_atTop (3 * C)
  filter_upwards [hlarge, eventually_ge_atTop t₀, eventually_ge_atTop 1] with x hx3 hxt hx1
  have hx0 : 0 < x := by linarith
  set a : ℝ := 1 / 2 + ε / 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  set y : ℝ := x + x ^ (1 / 2 + ε) with hy
  have hpow_pos : 0 < x ^ (1 / 2 + ε) := Real.rpow_pos_of_pos hx0 _
  have hpow_le : x ^ (1 / 2 + ε) ≤ x := by
    calc x ^ (1 / 2 + ε) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have hxy : x ≤ y := by rw [hy]; linarith
  have hy2 : y ≤ 2 * x := by rw [hy]; linarith
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 _
  have hya : y ^ a ≤ 2 * x ^ a := by
    calc y ^ a ≤ (2 * x) ^ a := Real.rpow_le_rpow (by linarith) hy2 ha0
      _ = (2 : ℝ) ^ a * x ^ a := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ (2 : ℝ) ^ (1 : ℝ) * x ^ a := by
        gcongr
        · norm_num
      _ = 2 * x ^ a := by rw [Real.rpow_one]
  have hsplit : x ^ (1 / 2 + ε) = x ^ (ε / 2) * x ^ a := by
    rw [← Real.rpow_add hx0]
    congr 1
    rw [ha]
    ring
  have hbx := ht₀ x hxt
  have hby := ht₀ y (hxt.trans hxy)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxa] at hbx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)] at hby
  have h1 := (abs_le.mp hbx).2
  have h2 := (abs_le.mp hby).1
  have h3 : C * y ^ a ≤ C * (2 * x ^ a) := mul_le_mul_of_nonneg_left hya hCpos.le
  have h4 : 3 * C * x ^ a < x ^ (ε / 2) * x ^ a := mul_lt_mul_of_pos_right hx3 hxa
  refine exists_prime_mem_Ioc_of_theta_lt hx0.le ?_
  have hyx : y - x = x ^ (ε / 2) * x ^ a := by rw [hy, ← hsplit]; ring
  nlinarith

end RHPrimeError

/-- **Primes in short intervals under RH.** Assuming the Riemann Hypothesis, for every `ε > 0`
and all sufficiently large real `x` there is a prime `p` with `x < p ≤ x + x ^ (1 / 2 + ε)`. -/
theorem exists_prime_mem_Ioc_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (1 / 2 + ε) := by
  intro ε hε
  have hδ : 0 < min ε (1 / 2) := lt_min hε (by norm_num)
  filter_upwards [RHPrimeError.exists_prime_mem_Ioc_of_le_half hRH hδ (min_le_right _ _),
    eventually_ge_atTop 1] with x hx hx1
  obtain ⟨p, hp, hxp, hpy⟩ := hx
  refine ⟨p, hp, hxp, hpy.trans ?_⟩
  have := Real.rpow_le_rpow_of_exponent_le hx1
    (by linarith [min_le_left ε (1 / 2)] : 1 / 2 + min ε (1 / 2) ≤ 1 / 2 + ε)
  linarith
