import RHPrimeError.Sharp.ZetaLocal

/-!
# Consequences of the local structure of the zeros of `ζ`

From `RHPrimeError.exists_isZeroFactorization_riemannZeta₁` we deduce the three estimates
needed to move a contour across the critical line.

## Main results

* `RHPrimeError.exists_norm_deriv_riemannZeta_div_le_of_re_eq_quarter`: under RH,
  `‖ζ' / ζ (s)‖ ≤ C * log (|im s| + 3)` on the line `re s = 1 / 4`.
* `RHPrimeError.exists_good_height`: every interval `[T₀, T₀ + 1]` contains a height `T` such
  that `ζ` has no zeros on the segments `1 / 4 ≤ re s ≤ 3 / 4`, `|im s| = T`, and
  `‖ζ' / ζ‖ ≤ C * log (T₀ + 4) ^ 2` there (no hypothesis on the zeros is needed).
* `RHPrimeError.exists_sum_inv_norm_le`: if `W` is a multiset of points with `re ρ = 1 / 2`,
  `|im ρ| ≤ T`, each occurring at most as often as its order as a zero of `(s - 1) ζ(s)`, then
  `∑ ρ ∈ W, 1 / ‖ρ‖ ≤ C * log (T + 4) ^ 2`.
-/

open Metric Set Complex

namespace RHPrimeError

/-- Under RH, a zero of `ζ` with positive real part, different from `1`, lies on the critical
line. -/
theorem re_eq_half_of_riemannZeta_eq_zero (hRH : RiemannHypothesis) {ρ : ℂ} (hre : 0 < ρ.re)
    (h1 : ρ ≠ 1) (h0 : riemannZeta ρ = 0) : ρ.re = 1 / 2 := by
  refine hRH ρ h0 ?_ h1
  rintro ⟨n, hn⟩
  have := congrArg Complex.re hn
  simp at this
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Points of the closed disc of centre `3 / 2 + τ * I` and radius `69 / 50` have positive real
part. -/
theorem re_pos_of_mem_closedBall {s : ℂ} {τ : ℝ}
    (hs : s ∈ closedBall (3 / 2 + τ * I : ℂ) (69 / 50)) : 0 < s.re := by
  rw [mem_closedBall, dist_eq_norm] at hs
  have h1 := (abs_re_le_norm (s - (3 / 2 + τ * I))).trans hs
  have h2 : (s - (3 / 2 + τ * I)).re = s.re - 3 / 2 := by simp
  rw [h2, abs_le] at h1
  linarith [h1.1]

/-- A bound for `ζ' / ζ` at a point of a disc, in terms of its distance to the zeros of the
disc. -/
theorem IsZeroFactorization.norm_deriv_riemannZeta_div_le {g : ℂ → ℂ} {c : ℂ} {r₂ r : ℝ}
    {Z : Multiset ℂ} (h : IsZeroFactorization riemannZeta₁ c r₂ r Z g) (h2r : r₂ < r) {s : ℂ}
    (hs : s ∈ closedBall c r₂) (hs1 : s ≠ 1) {δ M : ℝ} (hδ : 0 < δ)
    (hdist : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) (hM : ‖deriv g s / g s‖ ≤ M) :
    riemannZeta s ≠ 0 ∧
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ Z.card * δ⁻¹ + M + ‖s - 1‖⁻¹ := by
  have hsZ : s ∉ Z := by
    intro hmem
    have := hdist s hmem
    rw [sub_self, norm_zero] at this
    linarith
  obtain ⟨h0, heq⟩ := h.deriv_riemannZeta_div_eq h2r hs hsZ hs1
  refine ⟨h0, ?_⟩
  rw [heq]
  have h1 : ‖(Z.map fun ρ ↦ (s - ρ)⁻¹).sum‖ ≤ Z.card * δ⁻¹ :=
    norm_multiset_sum_map_le fun ρ hρ ↦ by
      rw [norm_inv]
      exact inv_anti₀ hδ (hdist ρ hρ)
  have h2 := norm_sub_le ((Z.map fun ρ ↦ (s - ρ)⁻¹).sum + deriv g s / g s) (s - 1)⁻¹
  have h3 := norm_add_le (Z.map fun ρ ↦ (s - ρ)⁻¹).sum (deriv g s / g s)
  rw [norm_inv] at h2
  linarith

/-- **`ζ' / ζ` on the line `re s = 1 / 4` under RH.** -/
theorem exists_norm_deriv_riemannZeta_div_le_of_re_eq_quarter (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = 1 / 4 →
      riemannZeta s ≠ 0 ∧
        ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log (|s.im| + 3) := by
  obtain ⟨A, hA, hloc⟩ := exists_isZeroFactorization_riemannZeta₁
  refine ⟨5 * A + 2, by positivity, fun s hs ↦ ?_⟩
  obtain ⟨Z, g, hfact, hcard, hbound⟩ := hloc s.im
  have h2r : (69 / 50 : ℝ) < 71 / 50 := by norm_num
  have hL1 : 1 ≤ Real.log (|s.im| + 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_d9.le.trans (by linarith [abs_nonneg s.im])
  have hs₁ : s ∈ closedBall (3 / 2 + s.im * I : ℂ) (27 / 20) :=
    mem_closedBall_of_abs_le (by rw [hs]; norm_num [abs_le]) (by simp)
  have hs₂ : s ∈ closedBall (3 / 2 + s.im * I : ℂ) (69 / 50) :=
    closedBall_subset_closedBall (by norm_num) hs₁
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at hs
  have hdist : ∀ ρ ∈ Z, (1 / 4 : ℝ) ≤ ‖s - ρ‖ := by
    intro ρ hρ
    obtain ⟨hρ1, hρ0⟩ := hfact.riemannZeta_eq_zero h2r hρ
    have hρre := re_eq_half_of_riemannZeta_eq_zero hRH
      (re_pos_of_mem_closedBall (hfact.mem_closedBall ρ hρ)) hρ1 hρ0
    have := abs_re_le_norm (s - ρ)
    rw [sub_re, hs, hρre] at this
    norm_num at this
    linarith
  obtain ⟨h0, hle⟩ := hfact.norm_deriv_riemannZeta_div_le h2r hs₂ hs1 (by norm_num) hdist
    (hbound s hs₁)
  refine ⟨h0, hle.trans ?_⟩
  have h1 : ‖s - 1‖⁻¹ ≤ 2 := by
    have := abs_re_le_norm (s - 1)
    rw [sub_re, hs] at this
    norm_num at this
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h2 : (Z.card : ℝ) * (1 / 4 : ℝ)⁻¹ ≤ 4 * (A * Real.log (|s.im| + 3)) := by
    norm_num
    linarith
  nlinarith

/-- A pigeonhole principle: every interval of length one contains a point at distance at least
`1 / (2 * (card Y + 1))` from all the points of a finite multiset `Y`. -/
theorem exists_mem_Icc_forall_le_abs_sub (Y : Multiset ℝ) (a : ℝ) :
    ∃ t ∈ Icc a (a + 1), ∀ y ∈ Y, 1 / (2 * ((Y.card : ℝ) + 1)) ≤ |t - y| := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = Y.card := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (2 * ((N : ℝ) + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδdef]
    positivity
  have hδN : 2 * ((N : ℝ) + 1) * δ = 1 := by
    rw [hδdef]
    field_simp
  rw [← hN, ← hδdef]
  by_contra hcon
  push Not at hcon
  have ht : ∀ j ∈ Finset.range (N + 1), a + (2 * (j : ℝ) + 1) * δ ∈ Icc a (a + 1) := by
    intro j hj
    have hjN : (j : ℝ) ≤ N := by
      exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    constructor
    · nlinarith
    · nlinarith
  have hex : ∀ j : ℕ, j ∈ Finset.range (N + 1) →
      ∃ y, y ∈ Y ∧ |a + (2 * (j : ℝ) + 1) * δ - y| < δ := fun j hj ↦ hcon _ (ht j hj)
  choose! φ hφY hφd using hex
  have hinj : Set.InjOn φ (Finset.range (N + 1) : Set ℕ) := by
    intro i hi j hj hij
    have hi' := hφd i hi
    have hj' := hφd j hj
    rw [hij, abs_lt] at hi'
    rw [abs_lt] at hj'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      nlinarith
    · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      nlinarith
  have hcard := Finset.card_le_card_of_injOn φ
    (fun j hj ↦ Multiset.mem_toFinset.2 (hφY j hj)) hinj
  have := Multiset.toFinset_card_le Y
  rw [Finset.card_range] at hcard
  omega

/-- **Good heights.** There is a constant `C` such that every interval `[T₀, T₀ + 1]` with
`1 ≤ T₀` contains a `T` for which `ζ` does not vanish on the horizontal segments
`1 / 4 ≤ re s ≤ 3 / 4`, `|im s| = T`, and `‖ζ' / ζ‖ ≤ C * log (T₀ + 4) ^ 2` on these
segments. -/
theorem exists_good_height :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, 1 ≤ T₀ → ∃ T ∈ Icc T₀ (T₀ + 1), ∀ s : ℂ,
      1 / 4 ≤ s.re → s.re ≤ 3 / 4 → |s.im| = T →
      riemannZeta s ≠ 0 ∧
        ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log (T₀ + 4) ^ 2 := by
  obtain ⟨A, hA, hloc⟩ := exists_isZeroFactorization_riemannZeta₁
  refine ⟨4 * A * (2 * A + 1) + A + 1, by positivity, fun T₀ hT₀ ↦ ?_⟩
  have h2r : (69 / 50 : ℝ) < 71 / 50 := by norm_num
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = T₀ + 1 / 2 := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (T₀ + 4) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hLτ : Real.log (|τ| + 3) ≤ L := by
    rw [hL, abs_of_pos hτ0]
    exact Real.log_le_log (by positivity) (by linarith)
  have hLτ' : Real.log (|-τ| + 3) ≤ L := by rwa [abs_neg]
  obtain ⟨Zp, gp, hfp, hcp, hbp⟩ := hloc τ
  obtain ⟨Zm, gm, hfm, hcm, hbm⟩ := hloc (-τ)
  obtain ⟨Y, hY⟩ : ∃ Y : Multiset ℝ,
      Y = Zp.map (fun ρ ↦ ρ.im) + Zm.map (fun ρ ↦ -ρ.im) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (Y.card : ℝ) := ⟨_, rfl⟩
  have hncard : n = Zp.card + Zm.card := by
    rw [hn, hY, Multiset.card_add, Multiset.card_map, Multiset.card_map]
    push_cast
    ring
  have hn0 : 0 ≤ n := hn ▸ Nat.cast_nonneg _
  have hZp0 : (0 : ℝ) ≤ Zp.card := Nat.cast_nonneg _
  have hZm0 : (0 : ℝ) ≤ Zm.card := Nat.cast_nonneg _
  have hnL : n ≤ 2 * A * L := by
    rw [hncard]
    nlinarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (2 * (n + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδdef]
    positivity
  have hδinv : δ⁻¹ = 2 * (n + 1) := by rw [hδdef, one_div, inv_inv]
  obtain ⟨T, hT, hfar⟩ := exists_mem_Icc_forall_le_abs_sub Y T₀
  rw [← hn, ← hδdef] at hfar
  have hfarp : ∀ ρ ∈ Zp, δ ≤ |T - ρ.im| := fun ρ hρ ↦
    hfar _ (hY ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_map_of_mem _ hρ)))
  have hfarm : ∀ ρ ∈ Zm, δ ≤ |T - -ρ.im| := fun ρ hρ ↦
    hfar _ (hY ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_map_of_mem _ hρ)))
  rw [← hL]
  refine ⟨T, hT, fun s hre1 hre2 him ↦ ?_⟩
  have hT1 : 1 ≤ T := hT₀.trans hT.1
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at him
    linarith
  have hinv : ‖s - 1‖⁻¹ ≤ 1 := by
    have h1 := abs_im_le_norm (s - 1)
    rw [sub_im, one_im, sub_zero, him] at h1
    exact inv_le_one_of_one_le₀ (hT1.trans h1)
  have hre : |s.re - 3 / 2| ≤ 5 / 4 := by
    rw [abs_le]
    constructor <;> linarith
  -- the final numerical inequality
  have hfinal : ∀ k : ℝ, 0 ≤ k → k ≤ n →
      k * δ⁻¹ + A * L + 1 ≤ (4 * A * (2 * A + 1) + A + 1) * L ^ 2 := by
    intro k hk0 hkn
    rw [hδinv]
    have h1 : n + 1 ≤ (2 * A + 1) * L := by nlinarith
    have h2 : k * (2 * (n + 1)) ≤ 2 * A * L * (2 * ((2 * A + 1) * L)) := by
      have : k ≤ 2 * A * L := hkn.trans hnL
      gcongr
    have h3 : L ≤ L ^ 2 := by nlinarith
    have h4 : (1 : ℝ) ≤ L ^ 2 := by nlinarith
    nlinarith
  rcases (abs_eq (by linarith : (0 : ℝ) ≤ T)).1 him with him' | him'
  · have hs₁ : s ∈ closedBall (3 / 2 + τ * I : ℂ) (27 / 20) :=
      mem_closedBall_of_abs_le hre (by
        rw [him', hτ, abs_le]
        constructor <;> linarith [hT.1, hT.2])
    have hdist : ∀ ρ ∈ Zp, δ ≤ ‖s - ρ‖ := fun ρ hρ ↦ by
      have := abs_im_le_norm (s - ρ)
      rw [sub_im, him'] at this
      exact (hfarp ρ hρ).trans this
    obtain ⟨h0, hle⟩ := hfp.norm_deriv_riemannZeta_div_le h2r
      (closedBall_subset_closedBall (by norm_num) hs₁) hs1 hδ hdist (hbp s hs₁)
    refine ⟨h0, hle.trans ?_⟩
    have := hfinal Zp.card hZp0 (by rw [hncard]; linarith)
    have hA' : A * Real.log (|τ| + 3) ≤ A * L := by gcongr
    linarith
  · have hs₁ : s ∈ closedBall (3 / 2 + (-τ : ℝ) * I : ℂ) (27 / 20) :=
      mem_closedBall_of_abs_le hre (by
        rw [him', hτ, abs_le]
        constructor <;> linarith [hT.1, hT.2])
    have hdist : ∀ ρ ∈ Zm, δ ≤ ‖s - ρ‖ := fun ρ hρ ↦ by
      have := abs_im_le_norm (s - ρ)
      rw [sub_im, him'] at this
      have h1 := hfarm ρ hρ
      have h2 : |T - -ρ.im| = |-T - ρ.im| := by
        rw [← abs_neg]
        congr 1
        ring
      rw [h2] at h1
      exact h1.trans this
    obtain ⟨h0, hle⟩ := hfm.norm_deriv_riemannZeta_div_le h2r
      (closedBall_subset_closedBall (by norm_num) hs₁) hs1 hδ hdist (hbm s hs₁)
    refine ⟨h0, hle.trans ?_⟩
    have := hfinal Zm.card hZm0 (by rw [hncard]; linarith)
    have hA' : A * Real.log (|-τ| + 3) ≤ A * L := by gcongr
    linarith

/-- **Sum over zeros.** There is a constant `C` such that, if `W` is a multiset of points with
`re ρ = 1 / 2` and `|im ρ| ≤ T`, each of them occurring at most as often as its order as a zero
of `riemannZeta₁ s = (s - 1) ζ(s)`, then `∑ ρ ∈ W, 1 / ‖ρ‖ ≤ C * log (T + 4) ^ 2`. -/
theorem exists_sum_inv_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ W : Multiset ℂ,
      (∀ ρ ∈ W, ρ.re = 1 / 2 ∧ |ρ.im| ≤ T) →
      (∀ ρ, (W.count ρ : ℕ∞) ≤ analyticOrderAt riemannZeta₁ ρ) →
      (W.map fun ρ ↦ ‖ρ‖⁻¹).sum ≤ C * Real.log (T + 4) ^ 2 := by
  classical
  obtain ⟨A, hA, hloc⟩ := exists_isZeroFactorization_riemannZeta₁
  choose Zf gf hfact hcard _ using hloc
  refine ⟨8 * A, by positivity, fun T hT W hW hord ↦ ?_⟩
  have h2r : (69 / 50 : ℝ) < 71 / 50 := by norm_num
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (T + 4) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊T⌋₊ := ⟨_, rfl⟩
  have hNT : (N : ℝ) ≤ T := hN ▸ Nat.floor_le (by linarith)
  obtain ⟨V, hV⟩ : ∃ V : ℕ → Multiset ℂ,
      V = fun k : ℕ ↦ Zf ((k : ℝ) + 1 / 2) + Zf (-((k : ℝ) + 1 / 2)) := ⟨_, rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℂ → ℕ, κ = fun ρ ↦ ⌊|ρ.im|⌋₊ := ⟨_, rfl⟩
  have hκ : ∀ ρ ∈ W.toFinset, κ ρ ∈ Finset.range (N + 1) := by
    intro ρ hρ
    rw [Finset.mem_range, Nat.lt_succ_iff, hκdef, hN]
    exact Nat.floor_le_floor (hW ρ (Multiset.mem_toFinset.1 hρ)).2
  have hκle : ∀ ρ : ℂ, (κ ρ : ℝ) ≤ |ρ.im| ∧ |ρ.im| < κ ρ + 1 := fun ρ ↦ by
    rw [hκdef]
    exact ⟨Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
  have hcount : ∀ ρ ∈ W, W.count ρ ≤ (V (κ ρ)).count ρ := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hκle ρ
    have hre : |ρ.re - 3 / 2| ≤ 5 / 4 := by
      rw [(hW ρ hρ).1]
      norm_num [abs_le]
    have key : ∀ τ : ℝ, |ρ.im - τ| ≤ 1 / 2 → W.count ρ ≤ (Zf τ).count ρ := by
      intro τ hτ
      have hmem : ρ ∈ closedBall (3 / 2 + τ * I : ℂ) (69 / 50) :=
        closedBall_subset_closedBall (by norm_num) (mem_closedBall_of_abs_le hre hτ)
      have := (hfact τ).count_eq_analyticOrderAt h2r hmem
      have h3 := hord ρ
      rw [← this] at h3
      exact_mod_cast h3
    rw [hV, Multiset.count_add]
    rcases le_total 0 ρ.im with h0 | h0
    · rw [abs_of_nonneg h0] at h1 h2
      have := key ((κ ρ : ℝ) + 1 / 2) (by
        rw [abs_le]
        constructor <;> linarith)
      omega
    · rw [abs_of_nonpos h0] at h1 h2
      have := key (-((κ ρ : ℝ) + 1 / 2)) (by
        rw [abs_le]
        constructor <;> linarith)
      omega
  have hnorm : ∀ ρ ∈ W, ‖ρ‖⁻¹ ≤ 2 / ((κ ρ : ℝ) + 1) := by
    intro ρ hρ
    obtain ⟨h1, -⟩ := hκle ρ
    have h3 := abs_re_le_norm ρ
    rw [(hW ρ hρ).1, abs_of_pos (by norm_num)] at h3
    have h4 := abs_im_le_norm ρ
    have h5 : ((κ ρ : ℝ) + 1) / 2 ≤ ‖ρ‖ := by
      rcases Nat.eq_zero_or_pos (κ ρ) with h0 | h0
      · rw [h0]
        norm_num
        linarith
      · have : (1 : ℝ) ≤ κ ρ := by exact_mod_cast h0
        linarith
    calc ‖ρ‖⁻¹ ≤ (((κ ρ : ℝ) + 1) / 2)⁻¹ := inv_anti₀ (by positivity) h5
      _ = 2 / ((κ ρ : ℝ) + 1) := inv_div _ _
  have hVcard : ∀ k ∈ Finset.range (N + 1), ((V k).card : ℝ) ≤ 2 * A * L := by
    intro k hk
    have hkN : (k : ℝ) ≤ N := by
      exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 := hcard ((k : ℝ) + 1 / 2)
    have h2 := hcard (-((k : ℝ) + 1 / 2))
    rw [abs_neg] at h2
    have h3 : Real.log (|(k : ℝ) + 1 / 2| + 3) ≤ L := by
      rw [hL, abs_of_pos (by positivity)]
      exact Real.log_le_log (by positivity) (by linarith)
    rw [hV, Multiset.card_add]
    push_cast
    nlinarith
  have hfiber : ∀ k ∈ Finset.range (N + 1),
      ∑ ρ ∈ W.toFinset with κ ρ = k, W.count ρ • ‖ρ‖⁻¹ ≤ 4 * A * L * (1 / ((k : ℝ) + 1)) := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hsub : (W.toFinset.filter fun ρ ↦ κ ρ = k) ⊆ (V k).toFinset := by
      intro ρ hρ
      obtain ⟨hρW, hρk⟩ := Finset.mem_filter.1 hρ
      rw [Multiset.mem_toFinset] at hρW ⊢
      have h1 := hcount ρ hρW
      rw [hρk] at h1
      exact Multiset.count_pos.1 (lt_of_lt_of_le (Multiset.count_pos.2 hρW) h1)
    calc ∑ ρ ∈ W.toFinset with κ ρ = k, W.count ρ • ‖ρ‖⁻¹
        ≤ ∑ ρ ∈ W.toFinset with κ ρ = k, ((V k).count ρ : ℝ) * (2 / ((k : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun ρ hρ ↦ ?_
          obtain ⟨hρW, hρk⟩ := Finset.mem_filter.1 hρ
          rw [Multiset.mem_toFinset] at hρW
          have h1 : (W.count ρ : ℝ) ≤ (V k).count ρ := by
            exact_mod_cast hρk ▸ hcount ρ hρW
          have h2 := hnorm ρ hρW
          rw [hρk] at h2
          rw [nsmul_eq_mul]
          gcongr
      _ ≤ ∑ ρ ∈ (V k).toFinset, ((V k).count ρ : ℝ) * (2 / ((k : ℝ) + 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun ρ _ _ ↦ by positivity
      _ = ((V k).card : ℝ) * (2 / ((k : ℝ) + 1)) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Multiset.toFinset_sum_count_eq (V k)
      _ ≤ 2 * A * L * (2 / ((k : ℝ) + 1)) := by
          gcongr
          exact hVcard k hk
      _ = 4 * A * L * (1 / ((k : ℝ) + 1)) := by ring
  have hharm : ∑ k ∈ Finset.range (N + 1), 1 / ((k : ℝ) + 1) ≤ 2 * L := by
    have h1 : ∑ k ∈ Finset.range (N + 1), 1 / ((k : ℝ) + 1) = (harmonic (N + 1) : ℝ) := by
      simp [harmonic]
    have h2 := harmonic_le_one_add_log (N + 1)
    have h3 : Real.log ((N + 1 : ℕ) : ℝ) ≤ L := by
      rw [hL]
      refine Real.log_le_log (by positivity) ?_
      push_cast
      linarith
    rw [h1]
    linarith
  rw [← hL, Finset.sum_multiset_map_count, ← Finset.sum_fiberwise_of_maps_to hκ]
  calc ∑ k ∈ Finset.range (N + 1), ∑ ρ ∈ W.toFinset with κ ρ = k, W.count ρ • ‖ρ‖⁻¹
      ≤ ∑ k ∈ Finset.range (N + 1), 4 * A * L * (1 / ((k : ℝ) + 1)) :=
        Finset.sum_le_sum hfiber
    _ = 4 * A * L * ∑ k ∈ Finset.range (N + 1), 1 / ((k : ℝ) + 1) := by rw [Finset.mul_sum]
    _ ≤ 4 * A * L * (2 * L) := by gcongr
    _ = 8 * A * L ^ 2 := by ring

end RHPrimeError
