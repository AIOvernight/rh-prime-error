import PrimeNumberTheoremAnd.MediumPNT
import PrimeNumberTheoremAnd.StrongPNT

/-!
# Bounds for `ζ' / ζ` to the right of the critical line, under RH
-/

open Complex

namespace RHPrimeError

open Metric Set in
/-- The Borel–Carathéodory theorem on a disc centred at `c`, for a function vanishing at `c`. -/
lemma borelCaratheodory_closedBall {f : ℂ → ℂ} {c : ℂ} {M R r : ℝ} (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball c R)) (hfc : f c = 0)
    (hre : ∀ z ∈ ball c R, (f z).re ≤ M)
    (hr : 0 ≤ r) (hrR : r < R) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖f z‖ ≤ 2 * M * r / (R - r) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hmaps : Set.MapsTo (fun w : ℂ ↦ w + c) (ball 0 R) (ball c R) := by
    intro w hw
    simpa [dist_eq_norm] using hw
  have hF : DifferentiableOn ℂ (fun w : ℂ ↦ f (w + c)) (ball 0 R) :=
    hf.comp (by fun_prop) hmaps
  have hx : ‖z - c‖ ≤ r := by simpa [dist_eq_norm] using hz
  have hzc : z - c ∈ ball (0 : ℂ) R := by
    simpa using hx.trans_lt hrR
  have key := Complex.borelCaratheodory (f := fun w : ℂ ↦ f (w + c)) hM hF
    (fun w hw ↦ hre _ (hmaps hw)) hR hzc
  simp only [sub_add_cancel, zero_add, hfc, norm_zero, zero_mul, zero_div, add_zero] at key
  refine key.trans ?_
  have hd : 0 < R - r := by linarith
  have hx0 : 0 ≤ ‖z - c‖ := norm_nonneg _
  gcongr

open Metric Set in
/-- If `f` is holomorphic and zero-free on `ball c r₂` and bounded by `B` there, then on the
smaller closed disc `closedBall c r₁` its logarithmic derivative is bounded by
`8 * r₂ / (r₂ - r₁) ^ 2 * log (B / ‖f c‖)`. -/
theorem norm_deriv_div_le_of_forall_mem_ball_ne_zero {f : ℂ → ℂ} {c : ℂ} {r₁ r₂ B : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hf : DifferentiableOn ℂ f (ball c r₂))
    (hne : ∀ z ∈ ball c r₂, f z ≠ 0) (hB : ∀ z ∈ ball c r₂, ‖f z‖ ≤ B) {z : ℂ}
    (hz : z ∈ closedBall c r₁) :
    ‖deriv f z / f z‖ ≤ 8 * r₂ / (r₂ - r₁) ^ 2 * Real.log (B / ‖f c‖) := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hcB : c ∈ ball c r₂ := mem_ball_self hr₂
  have hfc : 0 < ‖f c‖ := norm_pos_iff.2 (hne c hcB)
  have hBpos : 0 < B := hfc.trans_le (hB c hcB)
  have hE : 0 ≤ Real.log (B / ‖f c‖) :=
    Real.log_nonneg ((one_le_div hfc).2 (hB c hcB))
  set d : ℝ := (r₂ - r₁) / 2 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hfd : DifferentiableOn ℂ (fun s ↦ deriv f s / f s) (ball c r₂) :=
    (hf.deriv isOpen_ball).div hf hne
  obtain ⟨g, hgc, hgd⟩ := hfd.isExactOn_ball.with_val_at c (Complex.log (f c))
  -- `f * exp (-g)` is constant
  have hFd : ∀ s ∈ ball c r₂, HasDerivAt (fun s ↦ f s * Complex.exp (-g s)) 0 s := by
    intro s hs
    have h1 := (hf.differentiableAt (isOpen_ball.mem_nhds hs)).hasDerivAt
    have h2 : HasDerivAt (fun x ↦ Complex.exp (-g x))
        (Complex.exp (-g s) * -(deriv f s / f s)) s := (hgd s hs).neg.cexp
    have h3 := h1.mul h2
    have h0 := hne s hs
    refine h3.congr_deriv ?_
    have e : f s * (Complex.exp (-g s) * -(deriv f s / f s))
        = -(deriv f s * Complex.exp (-g s)) := by
      field_simp
    rw [e]; ring
  have hexp : ∀ s ∈ ball c r₂, Complex.exp (g s) = f s := by
    intro s hs
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r₂).isPreconnected
      (fun x hx ↦ (hFd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (hFd x hx).deriv) hs hcB
    have hc1 : f c * Complex.exp (-g c) = 1 := by
      rw [hgc, Complex.exp_neg, Complex.exp_log (hne c hcB), mul_inv_cancel₀ (hne c hcB)]
    rw [hc1] at hconst
    have : f s * Complex.exp (-g s) * Complex.exp (g s) = Complex.exp (g s) := by
      rw [hconst, one_mul]
    rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hgre : ∀ s ∈ ball c r₂, (g s).re = Real.log ‖f s‖ := by
    intro s hs
    rw [← hexp s hs, Complex.norm_exp, Real.log_exp]
  have hgdiff : DifferentiableOn ℂ g (ball c r₂) := fun s hs ↦
    (hgd s hs).differentiableAt.differentiableWithinAt
  set h : ℂ → ℂ := fun s ↦ g s - g c with hh
  have hhdiff : DifferentiableOn ℂ h (ball c r₂) := hgdiff.sub_const _
  have hhc : h c = 0 := by simp [hh]
  have hzc : dist z c ≤ r₁ := mem_closedBall.1 hz
  have hzB : z ∈ ball c r₂ := mem_ball.2 (hzc.trans_lt h12)
  have hderiv : deriv h z = deriv f z / f z := ((hgd z hzB).sub_const (g c)).deriv
  have hsub : closedBall z d ⊆ closedBall c (r₁ + d) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    linarith [dist_triangle w z c]
  have hsub' : closedBall c (r₁ + d) ⊆ ball c r₂ := closedBall_subset_ball (by rw [hd]; linarith)
  -- bound for every `M` larger than `log (B / ‖f c‖)`
  have key : ∀ M : ℝ, Real.log (B / ‖f c‖) < M →
      ‖deriv f z / f z‖ ≤ 8 * r₂ / (r₂ - r₁) ^ 2 * M := by
    intro M hM
    have hMpos : 0 < M := hE.trans_lt hM
    have hre : ∀ s ∈ ball c r₂, (h s).re ≤ M := by
      intro s hs
      have hfs : 0 < ‖f s‖ := norm_pos_iff.2 (hne s hs)
      simp only [hh, sub_re]
      rw [hgre s hs, hgre c hcB, ← Real.log_div hfs.ne' hfc.ne']
      refine (Real.log_le_log (div_pos hfs hfc) ?_).trans hM.le
      gcongr
      exact hB s hs
    have hbc : ∀ w ∈ closedBall c (r₁ + d), ‖h w‖ ≤ 2 * M * (r₁ + d) / d := by
      intro w hw
      have := borelCaratheodory_closedBall hMpos hhdiff hhc hre
        (by positivity : (0 : ℝ) ≤ r₁ + d) (by rw [hd]; linarith) hw
      have e : r₂ - (r₁ + d) = d := by rw [hd]; ring
      rwa [e] at this
    have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hd0
      (hhdiff.diffContOnCl_ball (hsub.trans hsub'))
      (fun w hw ↦ hbc w (hsub (sphere_subset_closedBall hw)))
    rw [hderiv] at hcauchy
    refine hcauchy.trans ?_
    have e : 2 * M * (r₁ + d) / d / d = 8 * (r₁ + d) / (r₂ - r₁) ^ 2 * M := by
      rw [hd]; field_simp; ring
    rw [e]
    have : 0 < (r₂ - r₁) ^ 2 := by nlinarith
    gcongr
    rw [hd]; linarith
  have hK : 0 < 8 * r₂ / (r₂ - r₁) ^ 2 := by
    have : 0 < (r₂ - r₁) ^ 2 := by nlinarith
    positivity
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have := key (Real.log (B / ‖f c‖) + ε / (8 * r₂ / (r₂ - r₁) ^ 2))
    (lt_add_of_pos_right _ (div_pos hε hK))
  rwa [mul_add, mul_div_cancel₀ _ hK.ne'] at this

/-- Under RH, `ζ` has no zeros with real part greater than `1 / 2`. -/
theorem riemannZeta_ne_zero_of_half_lt_re (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro h0
  have h := hRH s h0 (by
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith) hs1
  linarith

/-- Under RH, `‖ζ' / ζ‖ ≤ C * log |t|` on `σ₁ ≤ re s ≤ 2`, `3 ≤ |im s|`, for any `σ₁ > 1 / 2`. -/
theorem exists_norm_deriv_riemannZeta_div_le_log (hRH : RiemannHypothesis) {σ₁ : ℝ}
    (hσ₁ : 1 / 2 < σ₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 2 → 3 ≤ |s.im| →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log |s.im| := by
  set σ' : ℝ := min σ₁ 1 with hσ'
  have hσ'1 : σ' ≤ 1 := min_le_right _ _
  have hσ'2 : 1 / 2 < σ' := lt_min hσ₁ (by norm_num)
  set r₁ : ℝ := 3 / 2 - σ' with hr₁
  have hr₁0 : 0 < r₁ := by rw [hr₁]; linarith
  have hr₁1 : r₁ < 1 := by rw [hr₁]; linarith
  set K : ℝ := 8 * 1 / (1 - r₁) ^ 2 with hK
  have hK0 : 0 < K := by
    have : 0 < (1 - r₁) ^ 2 := by nlinarith
    positivity
  set m : ℝ := ‖riemannZeta 3 / riemannZeta (3 / 2)‖ with hm
  have hm0 : 0 < m := by
    rw [hm, norm_pos_iff]
    exact div_ne_zero (riemannZeta_ne_zero_of_one_le_re (by norm_num))
      (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_d9.trans (by norm_num)
  refine ⟨K * (3 + |Real.log m|), by positivity, fun s hs1 hs2 hs3 ↦ ?_⟩
  set t : ℝ := s.im with ht
  set c : ℂ := 3 / 2 + I * t with hc
  have ht0 : 0 < |t| := by linarith
  have hlogt : 1 < Real.log |t| :=
    hlog3.trans_le (Real.log_le_log (by norm_num) hs3)
  have him : ∀ z ∈ Metric.ball c 1, 2 < |z.im| := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := (abs_im_le_norm (z - c)).trans_lt hz
    have h2 : (z - c).im = z.im - t := by simp [hc]
    rw [h2] at h1
    have h3 : |t| ≤ |z.im| + |z.im - t| := by
      have h4 := abs_add_le (z.im) (-(z.im - t))
      rw [abs_neg] at h4
      have h5 : z.im + -(z.im - t) = t := by ring
      rw [h5] at h4
      exact h4
    linarith
  have hre : ∀ z ∈ Metric.ball c 1, 1 / 2 < z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := (abs_re_le_norm (z - c)).trans_lt hz
    have h2 : (z - c).re = z.re - 3 / 2 := by simp [hc]
    rw [h2, abs_lt] at h1
    linarith [h1.1]
  have hne1 : ∀ z ∈ Metric.ball c 1, z ≠ 1 := by
    rintro z hz rfl
    have := him 1 hz
    simp at this
    linarith
  have hdiff : DifferentiableOn ℂ riemannZeta (Metric.ball c 1) := fun z hz ↦
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hne : ∀ z ∈ Metric.ball c 1, riemannZeta z ≠ 0 := fun z hz ↦
    riemannZeta_ne_zero_of_half_lt_re hRH (hre z hz) (hne1 z hz)
  have hB : ∀ z ∈ Metric.ball c 1, ‖riemannZeta z‖ ≤ 7 + 2 * |t| := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := GlobalBound (s := z - c) hz.le (t := t) (by linarith)
    have e : z - c + 3 / 2 + I * t = z := by rw [hc]; ring
    rwa [e] at this
  have hsc : s ∈ Metric.closedBall c r₁ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have e : s - c = ((s.re - 3 / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc, ht]
    rw [e, norm_real, Real.norm_eq_abs, abs_le, hr₁]
    have : σ' ≤ σ₁ := min_le_left _ _
    constructor <;> linarith
  have main := norm_deriv_div_le_of_forall_mem_ball_ne_zero hr₁0 hr₁1 hdiff hne hB hsc
  rw [← hK] at main
  refine main.trans ?_
  have hc0 : 0 < ‖riemannZeta c‖ := norm_pos_iff.2 (hne c (Metric.mem_ball_self one_pos))
  have hmc : m ≤ ‖riemannZeta c‖ := by
    have := ZetaFixedLowerBound t
    rw [ge_iff_le, ← NNReal.coe_le_coe] at this
    simpa [hm, hc] using this
  have hBpos : 0 < 7 + 2 * |t| := by positivity
  have h1 : Real.log ((7 + 2 * |t|) / ‖riemannZeta c‖) ≤ Real.log ((7 + 2 * |t|) / m) :=
    Real.log_le_log (div_pos hBpos hc0) (div_le_div_of_nonneg_left hBpos.le hm0 hmc)
  have h2 : Real.log (7 + 2 * |t|) ≤ 3 * Real.log |t| := by
    have : Real.log (|t| ^ 3) = 3 * Real.log |t| := by
      rw [Real.log_pow]; norm_num
    rw [← this]
    refine Real.log_le_log hBpos ?_
    nlinarith [mul_pos ht0 ht0]
  rw [Real.log_div hBpos.ne' hm0.ne'] at h1
  have h3 : -Real.log m ≤ |Real.log m| * Real.log |t| := by
    have := neg_le_abs (Real.log m)
    nlinarith [abs_nonneg (Real.log m)]
  calc K * Real.log ((7 + 2 * |t|) / ‖riemannZeta c‖)
      ≤ K * (3 * Real.log |t| + |Real.log m| * Real.log |t|) := by
        gcongr
        linarith
    _ = K * (3 + |Real.log m|) * Real.log |t| := by ring

end RHPrimeError
