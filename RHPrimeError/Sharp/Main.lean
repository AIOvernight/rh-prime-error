import RHPrimeError.Main
import RHPrimeError.Sharp.Bounds

/-!
# von Koch's theorem: `ψ(x) - x = O(√x (log x)²)` under the Riemann Hypothesis

We prove the sharp form of the error term in the prime number theorem under RH, due to
von Koch: `ψ(x) - x = O(x ^ (1 / 2) * (log x) ^ 2)`, where `ψ` is the Chebyshev function.

As in `RHPrimeError/Main.lean`, the smoothed Chebyshev function with smoothing parameter
`ε = X ^ (-1 / 2)` is compared with `ψ X`, and its contour is pulled to the line `re s = 3 / 4`
truncated at a height `T ∈ [X ^ 2, X ^ 2 + 1]` (`SmoothedChebyshevPull1` of the
PrimeNumberTheoremAnd project). The new ingredient is the bound
`RHPrimeError.exists_norm_I₃₇_le_sqrt` for the vertical segment, obtained by moving it across
the critical line and summing over the zeros of `ζ`; this requires a suitable choice of `T`.

## Main results

* `RHPrimeError.exists_abs_psi_sub_le_sqrt_mul_log_sq`:
  `|ψ X - X| ≤ C * X ^ (1 / 2) * (log X) ^ 2` for large `X`.
* `chebyshev_psi_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis`:
  `ψ(x) - x = O(√x * (log x) ^ 2)`.
-/

open Complex Set MeasureTheory Filter

namespace RHPrimeError

/-- Under RH, `|ψ X - X| ≤ C * X ^ (1 / 2) * (log X) ^ 2` for all sufficiently large `X`. -/
theorem exists_abs_psi_sub_le_sqrt_mul_log_sq (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      |Chebyshev.psi X - X| ≤ C * X ^ (1 / 2 : ℝ) * Real.log X ^ 2 := by
  obtain ⟨F, hFsmooth, hFnonneg, hFsupp, hFmass⟩ := SmoothExistence
  have diffF : ContDiff ℝ 1 F := hFsmooth.of_le (by simp)
  have Fnonneg : ∀ x > 0, 0 ≤ F x := fun x _ ↦ hFnonneg x
  have mass_one : ∫ x in Ioi 0, F x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨c₀, c₀pos, h₀⟩ := SmoothedChebyshevClose diffF hFsupp Fnonneg mass_one
  obtain ⟨ε₀, cm, ε₀pos, cmpos, hm⟩ := MellinOfSmooth1cExplicit diffF hFsupp mass_one
  obtain ⟨c₁, c₁pos, h₁⟩ := I1Bound hFsupp diffF Fnonneg mass_one
  obtain ⟨c₉, c₉pos, h₉⟩ := I9Bound hFsupp diffF Fnonneg mass_one
  obtain ⟨c₂, c₂pos, h₂⟩ := exists_norm_I₂_le hRH diffF hFsupp (σ₁ := 3 / 4) (by norm_num)
    (by norm_num)
  obtain ⟨c₈, c₈pos, h₈⟩ := exists_norm_I₈_le hRH diffF hFsupp (σ₁ := 3 / 4) (by norm_num)
    (by norm_num)
  obtain ⟨c₃, c₃pos, h₃⟩ := exists_norm_I₃₇_le_sqrt hRH diffF hFsupp Fnonneg mass_one
  refine ⟨c₀ + cm + c₁ + c₉ + c₂ + c₈ + 9 * c₃, by positivity, ?_⟩
  have hsmall : ∀ᶠ X : ℝ in atTop, X ^ (-(1 / 2 : ℝ)) < ε₀ :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually (gt_mem_nhds ε₀pos)
  filter_upwards [hsmall, eventually_gt_atTop 4] with X hXε hX4
  have hX3 : 3 < X := by linarith
  have hXpos : 0 < X := by linarith
  -- The parameters: `r = X ^ (1 / 2)`, `ε = 1 / r`, `T ∈ [X ^ 2, X ^ 2 + 1]`.
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = X ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hrpos : 0 < r := hr ▸ Real.rpow_pos_of_pos hXpos _
  have hrr : r * r = X := by
    rw [hr, ← Real.rpow_add hXpos]
    norm_num
  have hr2 : 2 < r := by nlinarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = X ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hεr : ε = r⁻¹ := by rw [hε, hr, Real.rpow_neg hXpos.le]
  have hεpos : 0 < ε := hε ▸ Real.rpow_pos_of_pos hXpos _
  have hε1 : ε < 1 := by
    rw [hεr]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hεX : ε * X = r := by
    rw [hεr, ← hrr]
    field_simp
  have hXε2 : 2 < X * ε := by rwa [mul_comm, hεX]
  have hXsq : X ≤ X ^ 2 := by nlinarith
  obtain ⟨T, hT, hI₃₇⟩ := h₃ (X ^ 2) (by nlinarith)
  have hTX : X ^ 2 ≤ T := hT.1
  have hT3 : 3 < T := by nlinarith
  have hXT : X / (ε * T) ≤ r := by
    have hmul : r * (ε * T) = T := by
      rw [hεr]
      field_simp
    rw [div_le_iff₀ (by positivity), hmul]
    linarith
  have hL : 1 < Real.log X := logt_gt_one hX3.le
  have hlog : Real.log (X ^ 2 + 4) ≤ 3 * Real.log X := by
    have : Real.log (X ^ 3) = 3 * Real.log X := by
      rw [Real.log_pow]
      norm_num
    rw [← this]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlog0 : 0 ≤ Real.log (X ^ 2 + 4) := Real.log_nonneg (by nlinarith)
  -- The two basic comparisons with the final bound.
  have hL2 : Real.log X ≤ Real.log X ^ 2 := by nlinarith
  have hrB : r ≤ r * Real.log X ^ 2 := le_mul_of_one_le_right hrpos.le (by linarith)
  have hrLB : r * Real.log X ≤ r * Real.log X ^ 2 := by gcongr
  -- The contour shift and the individual bounds.
  have pull := SmoothedChebyshevPull1 hεpos hε1 X hX3 (T := T) (by linarith)
    (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
    (holomorphicOn_logDeriv_riemannZeta hRH (by norm_num) T) hFsupp Fnonneg mass_one diffF
  have b₀ := h₀ X hX3 ε hεpos hε1 hXε2
  have bm := hm ε ⟨hεpos, hε ▸ hXε⟩
  have b₁ := h₁ ε hεpos hε1 X hX3 hT3
  have b₉ := h₉ hεpos hε1 X hX3 hT3
  have b₂ := h₂ X hX3 ε hεpos hε1 T hT3.le
  have b₈ := h₈ X hX3 ε hεpos hε1 T hT3.le
  have b₃ := hI₃₇ X (by linarith) hXsq ε hεpos hε1
  rw [← hr] at b₃ ⊢
  have b₀' : ‖SmoothedChebyshev F ε X - (Chebyshev.psi X : ℂ)‖ ≤
      c₀ * (r * Real.log X ^ 2) := by
    refine b₀.trans ?_
    calc c₀ * ε * X * Real.log X = c₀ * (ε * X * Real.log X) := by ring
      _ ≤ _ := by rw [hεX]; gcongr
  have bm' : ‖(mellin (fun x ↦ (Smooth1 F ε x : ℂ)) 1 - 1) * (X : ℂ)‖ ≤
      cm * (r * Real.log X ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hXpos.le]
    calc _ ≤ cm * ε * X := by gcongr
      _ = cm * (ε * X) := by ring
      _ ≤ _ := by rw [hεX]; gcongr
  have b₁' : ‖I₁ F ε X T‖ ≤ c₁ * (r * Real.log X ^ 2) := by
    refine b₁.trans ?_
    calc c₁ * X * Real.log X / (ε * T) = c₁ * (X / (ε * T) * Real.log X) := by ring
      _ ≤ c₁ * (r * Real.log X) := by gcongr
      _ ≤ _ := by gcongr
  have b₉' : ‖I₉ F ε X T‖ ≤ c₉ * (r * Real.log X ^ 2) := by
    refine b₉.trans ?_
    calc c₉ * X * Real.log X / (ε * T) = c₉ * (X / (ε * T) * Real.log X) := by ring
      _ ≤ c₉ * (r * Real.log X) := by gcongr
      _ ≤ _ := by gcongr
  have b₂' : ‖I₂ F ε T X (3 / 4)‖ ≤ c₂ * (r * Real.log X ^ 2) := by
    refine b₂.trans ?_
    calc c₂ * X / (ε * T) = c₂ * (X / (ε * T)) := by ring
      _ ≤ _ := by gcongr; exact hXT.trans hrB
  have b₈' : ‖I₈ F ε T X (3 / 4)‖ ≤ c₈ * (r * Real.log X ^ 2) := by
    refine b₈.trans ?_
    calc c₈ * X / (ε * T) = c₈ * (X / (ε * T)) := by ring
      _ ≤ _ := by gcongr; exact hXT.trans hrB
  have b₃' : ‖I₃₇ F ε T X (3 / 4)‖ ≤ 9 * c₃ * (r * Real.log X ^ 2) := by
    refine b₃.trans ?_
    calc c₃ * r * Real.log (X ^ 2 + 4) ^ 2 ≤ c₃ * r * (3 * Real.log X) ^ 2 := by gcongr
      _ = 9 * c₃ * (r * Real.log X ^ 2) := by ring
  have hdecomp : ((Chebyshev.psi X - X : ℝ) : ℂ) =
      -(SmoothedChebyshev F ε X - (Chebyshev.psi X : ℂ)) + I₁ F ε X T - I₂ F ε T X (3 / 4) +
        I₃₇ F ε T X (3 / 4) + I₈ F ε T X (3 / 4) + I₉ F ε X T +
        (mellin (fun x ↦ (Smooth1 F ε x : ℂ)) 1 - 1) * (X : ℂ) := by
    rw [pull]
    push_cast
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdecomp]
  refine (norm_neg_add_sub_add_le _ _ _ _ _ _ _).trans ?_
  linarith

end RHPrimeError

open RHPrimeError in
/-- **von Koch's theorem: the Riemann Hypothesis implies `ψ(x) - x = O(√x * (log x) ^ 2)`**,
where `ψ` is the Chebyshev function. -/
theorem chebyshev_psi_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop]
      fun x : ℝ => Real.sqrt x * Real.log x ^ 2 := by
  obtain ⟨C, -, hC⟩ := exists_abs_psi_sub_le_sqrt_mul_log_sq hRH
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hC, eventually_ge_atTop 0] with X h1 hX0
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg X) (sq_nonneg _)),
    Real.sqrt_eq_rpow, ← mul_assoc]
  exact h1
