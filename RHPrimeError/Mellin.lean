import PrimeNumberTheoremAnd.MediumPNT

/-!
# A uniform bound for the Mellin transform of the smoothed cutoff
-/

open Complex

namespace RHPrimeError

/-- The Mellin transform of `Smooth1 ν ε` is `O(1 / ‖s‖)` on `0 < re s ≤ 2`, uniformly in
`ε ∈ (0, 1)`. -/
theorem exists_norm_mellin_smooth1_le_div_norm {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ s : ℂ, 0 < s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C / ‖s‖ := by
  refine ⟨4, by norm_num, fun ε εpos εlt s hs hs2 ↦ ?_⟩
  rw [MellinOfSmooth1a diffν suppν εpos hs]
  have hint : MeasureTheory.Integrable (fun x ↦ ν x / x)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    MeasureTheory.integrable_of_integral_eq_one mass_one
  have hre : (ε * s).re = ε * s.re := by simp
  have hre0 : 0 ≤ ε * s.re := by positivity
  have hre2 : ε * s.re ≤ 2 := by nlinarith
  have key : ‖mellin (fun x ↦ (ν x : ℂ)) (ε * s)‖ ≤ 4 := by
    have h := MeasureTheory.norm_integral_le_of_norm_le
      (f := fun t : ℝ ↦ (t : ℂ) ^ ((ε : ℂ) * s - 1) • (ν t : ℂ)) (hint.const_mul 4)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0 : ℝ) < t := ht
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (νnonneg t ht0)]
        by_cases hν : ν t = 0
        · simp [hν]
        have htm : t ∈ Set.Icc (1 / 2 : ℝ) 2 := suppν hν
        have h1 : t ^ (ε * s.re) ≤ 4 := by
          calc t ^ (ε * s.re) ≤ (2 : ℝ) ^ (ε * s.re) :=
                Real.rpow_le_rpow ht0.le htm.2 hre0
            _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hre2
            _ = 4 := by norm_num
        have h2 : t ^ (((ε : ℂ) * s - 1).re) = t ^ (ε * s.re) / t := by
          rw [Complex.sub_re, hre, Complex.one_re, Real.rpow_sub_one ht0.ne']
        rw [h2]
        have h3 : 0 ≤ ν t / t := div_nonneg (νnonneg t ht0) ht0.le
        calc t ^ (ε * s.re) / t * ν t = t ^ (ε * s.re) * (ν t / t) := by ring
          _ ≤ 4 * (ν t / t) := by gcongr)
    rw [MeasureTheory.integral_const_mul, mass_one] at h
    simpa [mellin] using h
  rw [norm_mul, norm_inv, div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right key (inv_nonneg.mpr (norm_nonneg s))
end RHPrimeError
