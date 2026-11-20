import RHPrimeError.Contour

/-!
# The prime-counting error term under the Riemann Hypothesis

We prove the classical consequence of the Riemann Hypothesis
`ψ(x) - x = O(x ^ (1 / 2 + ε))` for every `ε > 0`, where `ψ` is the Chebyshev function.

The proof follows the contour-shifting argument of the PrimeNumberTheoremAnd project
(`MediumPNT.lean`): the smoothed Chebyshev function with smoothing parameter
`ε_X = X ^ (-1 / 2)` is compared with `ψ X` (`SmoothedChebyshevClose`), and its defining contour
is pulled (`SmoothedChebyshevPull1`) to the line `re s = σ₁`, `1 / 2 < σ₁ < 1`, truncated at
height `T_X = X ^ 2`. Under RH the only singularity crossed is the pole at `s = 1`, and the
pieces of the new contour are bounded in `RHPrimeError/Contour.lean`.

## Main results

* `RHPrimeError.exists_abs_psi_sub_le`: `|ψ X - X| ≤ C * X ^ σ₁ * (log X) ^ 2` for large `X`.
* `chebyshev_psi_sub_isBigO_of_riemannHypothesis`: `ψ x - x = O(x ^ (1 / 2 + ε))`.
-/

open Complex Set MeasureTheory Filter

namespace RHPrimeError

/-- A seven-term triangle inequality, in the shape produced by `SmoothedChebyshevPull1`. -/
theorem norm_neg_add_sub_add_le (a b c d e f g : ℂ) :
    ‖-a + b - c + d + e + f + g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  have h1 := norm_add_le (-a + b - c + d + e + f) g
  have h2 := norm_add_le (-a + b - c + d + e) f
  have h3 := norm_add_le (-a + b - c + d) e
  have h4 := norm_add_le (-a + b - c) d
  have h5 := norm_sub_le (-a + b) c
  have h6 := norm_add_le (-a) b
  rw [norm_neg] at h6
  linarith

/-- Under RH, for every `σ₁ ∈ (1 / 2, 1)` we have `|ψ X - X| ≤ C * X ^ σ₁ * (log X) ^ 2` for
all sufficiently large `X`. -/
theorem exists_abs_psi_sub_le (hRH : RiemannHypothesis) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁)
    (hσ₁' : σ₁ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      |Chebyshev.psi X - X| ≤ C * X ^ σ₁ * Real.log X ^ 2 := by
  obtain ⟨F, hFsmooth, hFnonneg, hFsupp, hFmass⟩ := SmoothExistence
  have diffF : ContDiff ℝ 1 F := hFsmooth.of_le (by simp)
  have Fnonneg : ∀ x > 0, 0 ≤ F x := fun x _ ↦ hFnonneg x
  have mass_one : ∫ x in Ioi 0, F x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨c₀, c₀pos, h₀⟩ := SmoothedChebyshevClose diffF hFsupp Fnonneg mass_one
  obtain ⟨ε₀, cm, ε₀pos, cmpos, hm⟩ := MellinOfSmooth1cExplicit diffF hFsupp mass_one
  obtain ⟨c₁, c₁pos, h₁⟩ := I1Bound hFsupp diffF Fnonneg mass_one
  obtain ⟨c₉, c₉pos, h₉⟩ := I9Bound hFsupp diffF Fnonneg mass_one
  obtain ⟨c₂, c₂pos, h₂⟩ := exists_norm_I₂_le hRH diffF hFsupp hσ₁ hσ₁'
  obtain ⟨c₈, c₈pos, h₈⟩ := exists_norm_I₈_le hRH diffF hFsupp hσ₁ hσ₁'
  obtain ⟨c₃, c₃pos, h₃⟩ := exists_norm_I₃₇_le hRH diffF hFsupp Fnonneg mass_one hσ₁ hσ₁'
  refine ⟨c₀ + cm + c₁ + c₉ + c₂ + c₈ + 4 * c₃, by positivity, ?_⟩
  have hsmall : ∀ᶠ X : ℝ in atTop, X ^ (-(1 / 2 : ℝ)) < ε₀ :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually (gt_mem_nhds ε₀pos)
  filter_upwards [hsmall, eventually_gt_atTop 4] with X hXε hX4
  have hX3 : 3 < X := by linarith
  have hXpos : 0 < X := by linarith
  -- The parameters: `r = X ^ (1 / 2)`, `ε = 1 / r`, `T = X ^ 2`.
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
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = X ^ 2 := ⟨_, rfl⟩
  have hT3 : 3 < T := by nlinarith
  have hlogT : Real.log T = 2 * Real.log X := by
    rw [hT, Real.log_pow]
    norm_num
  have hXT : X / (ε * T) ≤ r := by
    have hmul : r * (ε * T) = X ^ 2 := by
      rw [hεr, hT]
      field_simp
    rw [div_le_iff₀ (by positivity), hmul]
    nlinarith
  have hrσ : r ≤ X ^ σ₁ := hr ▸ Real.rpow_le_rpow_of_exponent_le (by linarith) hσ₁.le
  have hL : 1 < Real.log X := logt_gt_one hX3.le
  have hXσ : 0 < X ^ σ₁ := Real.rpow_pos_of_pos hXpos _
  -- The two basic comparisons with the final bound.
  have hL2 : Real.log X ≤ Real.log X ^ 2 := by nlinarith
  have hrB : r ≤ X ^ σ₁ * Real.log X ^ 2 :=
    hrσ.trans (le_mul_of_one_le_right hXσ.le (by linarith))
  have hrLB : r * Real.log X ≤ X ^ σ₁ * Real.log X ^ 2 := by
    calc r * Real.log X ≤ X ^ σ₁ * Real.log X := by gcongr
      _ ≤ _ := by gcongr
  -- The contour shift and the individual bounds.
  have pull := SmoothedChebyshevPull1 hεpos hε1 X hX3 (T := T) (by linarith)
    (by linarith : 0 < σ₁) hσ₁' (holomorphicOn_logDeriv_riemannZeta hRH hσ₁ T) hFsupp Fnonneg
    mass_one diffF
  have b₀ := h₀ X hX3 ε hεpos hε1 hXε2
  have bm := hm ε ⟨hεpos, hε ▸ hXε⟩
  have b₁ := h₁ ε hεpos hε1 X hX3 hT3
  have b₉ := h₉ hεpos hε1 X hX3 hT3
  have b₂ := h₂ X hX3 ε hεpos hε1 T hT3.le
  have b₈ := h₈ X hX3 ε hεpos hε1 T hT3.le
  have b₃ := h₃ X hXpos ε hεpos hε1 T hT3.le
  rw [hlogT] at b₃
  have b₀' : ‖SmoothedChebyshev F ε X - (Chebyshev.psi X : ℂ)‖ ≤
      c₀ * (X ^ σ₁ * Real.log X ^ 2) := by
    refine b₀.trans ?_
    calc c₀ * ε * X * Real.log X = c₀ * (ε * X * Real.log X) := by ring
      _ ≤ _ := by rw [hεX]; gcongr
  have bm' : ‖(mellin (fun x ↦ (Smooth1 F ε x : ℂ)) 1 - 1) * (X : ℂ)‖ ≤
      cm * (X ^ σ₁ * Real.log X ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hXpos.le]
    calc _ ≤ cm * ε * X := by gcongr
      _ = cm * (ε * X) := by ring
      _ ≤ _ := by rw [hεX]; gcongr
  have b₁' : ‖I₁ F ε X T‖ ≤ c₁ * (X ^ σ₁ * Real.log X ^ 2) := by
    refine b₁.trans ?_
    calc c₁ * X * Real.log X / (ε * T) = c₁ * (X / (ε * T) * Real.log X) := by ring
      _ ≤ c₁ * (r * Real.log X) := by gcongr
      _ ≤ _ := by gcongr
  have b₉' : ‖I₉ F ε X T‖ ≤ c₉ * (X ^ σ₁ * Real.log X ^ 2) := by
    refine b₉.trans ?_
    calc c₉ * X * Real.log X / (ε * T) = c₉ * (X / (ε * T) * Real.log X) := by ring
      _ ≤ c₉ * (r * Real.log X) := by gcongr
      _ ≤ _ := by gcongr
  have b₂' : ‖I₂ F ε T X σ₁‖ ≤ c₂ * (X ^ σ₁ * Real.log X ^ 2) := by
    refine b₂.trans ?_
    calc c₂ * X / (ε * T) = c₂ * (X / (ε * T)) := by ring
      _ ≤ _ := by gcongr; exact hXT.trans hrB
  have b₈' : ‖I₈ F ε T X σ₁‖ ≤ c₈ * (X ^ σ₁ * Real.log X ^ 2) := by
    refine b₈.trans ?_
    calc c₈ * X / (ε * T) = c₈ * (X / (ε * T)) := by ring
      _ ≤ _ := by gcongr; exact hXT.trans hrB
  have b₃' : ‖I₃₇ F ε T X σ₁‖ ≤ 4 * c₃ * (X ^ σ₁ * Real.log X ^ 2) := by
    refine b₃.trans (le_of_eq ?_)
    ring
  have hdecomp : ((Chebyshev.psi X - X : ℝ) : ℂ) =
      -(SmoothedChebyshev F ε X - (Chebyshev.psi X : ℂ)) + I₁ F ε X T - I₂ F ε T X σ₁ +
        I₃₇ F ε T X σ₁ + I₈ F ε T X σ₁ + I₉ F ε X T +
        (mellin (fun x ↦ (Smooth1 F ε x : ℂ)) 1 - 1) * (X : ℂ) := by
    rw [pull]
    push_cast
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdecomp]
  refine (norm_neg_add_sub_add_le _ _ _ _ _ _ _).trans ?_
  linarith

end RHPrimeError

open RHPrimeError in
/-- **The Riemann Hypothesis implies `ψ(x) - x = O(x ^ (1 / 2 + ε))`** for every `ε > 0`, where
`ψ` is the Chebyshev function. -/
theorem chebyshev_psi_sub_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε) := by
  intro ε hε
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (ε / 2) (1 / 4) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (by linarith) (by norm_num)
  have hδε : δ ≤ ε / 2 := hδ ▸ min_le_left _ _
  have hδ4 : δ ≤ 1 / 4 := hδ ▸ min_le_right _ _
  obtain ⟨C, Cpos, hC⟩ := exists_abs_psi_sub_le hRH (σ₁ := 1 / 2 + δ) (by linarith)
    (by linarith)
  have hlog := (isLittleO_log_rpow_rpow_atTop 2 hδpos).bound one_pos
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hC, hlog, eventually_ge_atTop 1] with X h1 h2 hX1
  have hXpos : 0 < X := by linarith
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hXpos.le _)]
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hXpos.le _), Real.rpow_two,
    Real.norm_of_nonneg (sq_nonneg _)] at h2
  calc |Chebyshev.psi X - X| ≤ C * X ^ (1 / 2 + δ) * Real.log X ^ 2 := h1
    _ ≤ C * X ^ (1 / 2 + δ) * X ^ δ := by gcongr
    _ = C * X ^ (1 / 2 + δ + δ) := by rw [mul_assoc, ← Real.rpow_add hXpos]
    _ ≤ C * X ^ (1 / 2 + ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) Cpos.le
