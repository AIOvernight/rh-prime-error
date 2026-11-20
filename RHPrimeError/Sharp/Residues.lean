import RHPrimeError.Sharp.ZetaZeros
import RHPrimeError.Contour

/-!
# The residue identity for the smoothed Chebyshev integrand across the critical line

We compute the integral of `SmoothedChebyshevIntegrand ν ε X` (that is, of
`-(ζ' / ζ)(s) * 𝓜(Smooth1 ν ε)(s) * X ^ s`) over the boundary of the rectangle
`[1 / 4, 3 / 4] × [-T, T]` under the Riemann Hypothesis: it is `-2πi` times the sum of
`𝓜(Smooth1 ν ε)(ρ) * X ^ ρ` over the zeros `ρ` of `ζ` in the rectangle, with multiplicity.

## Main results

* `RHPrimeError.rectangleIntegral_multiset_sum_inv_sub_add_mul`: the residue theorem on a
  rectangle for a function of the form `(∑ ρ ∈ Z, 1 / (s - ρ) + φ s) * h s` with `φ`, `h`
  holomorphic.
* `RHPrimeError.exists_rectangleIntegral_smoothedChebyshevIntegrand_eq`: the residue identity
  for the smoothed Chebyshev integrand.

The global decomposition `ζ' / ζ = ∑ ρ ∈ Z, 1 / (s - ρ) + φ` near the rectangle is obtained from
Landau's lemma on a large disc containing it.
-/

open Complex Set Metric

open scoped Interval

namespace RHPrimeError

/-- `s ↦ ∑ ρ ∈ Z, 1 / (s - ρ)` is continuous on any set disjoint from `Z`. -/
theorem continuousOn_multiset_sum_inv_sub (Z : Multiset ℂ) {S : Set ℂ} (hZ : ∀ ρ ∈ Z, ρ ∉ S) :
    ContinuousOn (fun s : ℂ ↦ (Z.map fun ρ ↦ (s - ρ)⁻¹).sum) S := by
  induction Z using Multiset.induction_on with
  | empty => simpa using continuousOn_const
  | cons ρ Z ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    refine ContinuousOn.add ?_ (ih fun x hx ↦ hZ x (Multiset.mem_cons_of_mem hx))
    refine (continuousOn_id.sub continuousOn_const).inv₀ fun s hs ↦ sub_ne_zero.2 ?_
    rintro rfl
    exact hZ _ (Multiset.mem_cons_self _ Z) hs

/-- A point of a rectangle which is not on its border is an interior point. -/
theorem rectangle_mem_nhds_of_notMem_border {z w ρ : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hρ : ρ ∈ Rectangle z w) (hρb : ρ ∉ RectangleBorder z w) :
    Rectangle z w ∈ nhds ρ := by
  rw [rectangle_mem_nhds_iff, mem_reProdIm, uIoo_of_le hre, uIoo_of_le him]
  rw [Rectangle, mem_reProdIm, uIcc_of_le hre, uIcc_of_le him] at hρ
  have hre' : ρ.re ∈ [[z.re, w.re]] := by rw [uIcc_of_le hre]; exact hρ.1
  have him' : ρ.im ∈ [[z.im, w.im]] := by rw [uIcc_of_le him]; exact hρ.2
  refine ⟨⟨lt_of_le_of_ne hρ.1.1 fun h ↦ hρb ?_, lt_of_le_of_ne hρ.1.2 fun h ↦ hρb ?_⟩,
    ⟨lt_of_le_of_ne hρ.2.1 fun h ↦ hρb ?_, lt_of_le_of_ne hρ.2.2 fun h ↦ hρb ?_⟩⟩
  · exact Or.inl (Or.inl (Or.inr ⟨h.symm, him'⟩))
  · exact Or.inr ⟨h, him'⟩
  · exact Or.inl (Or.inl (Or.inl ⟨hre', h.symm⟩))
  · exact Or.inl (Or.inr ⟨hre', h⟩)

open Classical in
/-- The integral of `h s / (s - ρ)` over the boundary of a rectangle, for `h` holomorphic on
the rectangle and `ρ` not on its border. -/
theorem rectangleIntegral_inv_sub_mul {z w ρ : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {h : ℂ → ℂ} (hh : HolomorphicOn h (Rectangle z w)) (hρ : ρ ∉ RectangleBorder z w) :
    RectangleIntegral (fun s ↦ (s - ρ)⁻¹ * h s) z w =
      if ρ ∈ Rectangle z w then 2 * Real.pi * I * h ρ else 0 := by
  split_ifs with hmem
  · have hnhds := rectangle_mem_nhds_of_notMem_border hre him hmem hρ
    have key := ResidueTheoremOnRectangleWithSimplePole (f := fun s ↦ (s - ρ)⁻¹ * h s)
      (g := dslope h ρ) (A := h ρ) hre him hnhds ((differentiableOn_dslope hnhds).2 hh) (by
        intro s hs
        have hsρ : s ≠ ρ := hs.2
        have h0 : s - ρ ≠ 0 := sub_ne_zero.2 hsρ
        simp only [Pi.sub_apply]
        rw [dslope_of_ne _ hsρ, slope_def_field]
        field_simp)
    rw [RectangleIntegral', smul_eq_mul] at key
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    rw [← key]
    field_simp
  · refine HolomorphicOn.vanishesOnRectangle (U := Rectangle z w) ?_ subset_rfl
    refine DifferentiableOn.mul ?_ hh
    refine (differentiableOn_id.sub (differentiableOn_const _)).inv fun s hs ↦ sub_ne_zero.2 ?_
    rintro rfl
    exact hmem hs

open Classical in
/-- **Residue theorem on a rectangle** for a function `(∑ ρ ∈ Z, 1 / (s - ρ) + φ s) * h s`,
where `φ` and `h` are holomorphic on the rectangle and no point of `Z` lies on its border. -/
theorem rectangleIntegral_multiset_sum_inv_sub_add_mul {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) {φ h : ℂ → ℂ} (hφ : HolomorphicOn φ (Rectangle z w))
    (hh : HolomorphicOn h (Rectangle z w)) (Z : Multiset ℂ)
    (hZ : ∀ ρ ∈ Z, ρ ∉ RectangleBorder z w) :
    RectangleIntegral (fun s ↦ ((Z.map fun ρ ↦ (s - ρ)⁻¹).sum + φ s) * h s) z w =
      2 * Real.pi * I * ((Z.filter (· ∈ Rectangle z w)).map h).sum := by
  have hsub := rectangleBorder_subset_rectangle z w
  induction Z using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero, zero_add, Multiset.filter_zero, mul_zero]
    exact HolomorphicOn.vanishesOnRectangle (U := Rectangle z w) (hφ.mul hh) subset_rfl
  | cons ρ Z ih =>
    have hZ' : ∀ x ∈ Z, x ∉ RectangleBorder z w := fun x hx ↦ hZ x (Multiset.mem_cons_of_mem hx)
    have hρ : ρ ∉ RectangleBorder z w := hZ ρ (Multiset.mem_cons_self ρ Z)
    have hfun : (fun s ↦ (((ρ ::ₘ Z).map fun ρ ↦ (s - ρ)⁻¹).sum + φ s) * h s) =
        (fun s ↦ (s - ρ)⁻¹ * h s) + fun s ↦ ((Z.map fun ρ ↦ (s - ρ)⁻¹).sum + φ s) * h s := by
      funext s
      simp only [Multiset.map_cons, Multiset.sum_cons, Pi.add_apply]
      ring
    have hint₁ : RectangleBorderIntegrable (fun s ↦ (s - ρ)⁻¹ * h s) z w := by
      refine ContinuousOn.rectangleBorder_integrable
        (ContinuousOn.mul ?_ (hh.continuousOn.mono hsub))
      refine (continuousOn_id.sub continuousOn_const).inv₀ fun s hs ↦ sub_ne_zero.2 ?_
      rintro rfl
      exact hρ hs
    have hint₂ : RectangleBorderIntegrable
        (fun s ↦ ((Z.map fun ρ ↦ (s - ρ)⁻¹).sum + φ s) * h s) z w :=
      ContinuousOn.rectangleBorder_integrable
        (((continuousOn_multiset_sum_inv_sub Z hZ').add (hφ.continuousOn.mono hsub)).mul
          (hh.continuousOn.mono hsub))
    rw [hfun, RectangleBorderIntegrable.add hint₁ hint₂, ih hZ',
      rectangleIntegral_inv_sub_mul hre him hh hρ]
    split_ifs with hmem
    · rw [Multiset.filter_cons_of_pos _ hmem, Multiset.map_cons, Multiset.sum_cons]
      ring
    · rw [Multiset.filter_cons_of_neg _ hmem, zero_add]

open Classical in
/-- **Residue identity across the critical line.** Assume RH and let `T > 0` be such that `ζ`
has no zero `ρ` with `re ρ = 1 / 2` and `|im ρ| = T`. Then the integral of the smoothed
Chebyshev integrand over the boundary of `[1 / 4, 3 / 4] × [-T, T]` equals `-2πi` times the sum
of `𝓜(Smooth1 ν ε)(ρ) * X ^ ρ` over a multiset `W` of points with `re ρ = 1 / 2`, `|im ρ| ≤ T`
in which each point occurs at most as often as its order as a zero of `(s - 1) ζ(s)`. -/
theorem exists_rectangleIntegral_smoothedChebyshevIntegrand_eq (hRH : RiemannHypothesis)
    {F : ℝ → ℝ} (diffF : ContDiff ℝ 1 F) (suppF : F.support ⊆ Icc (1 / 2) 2)
    (Fnonneg : ∀ x > 0, 0 ≤ F x) (mass_one : ∫ x in Ioi 0, F x / x = 1) {ε X T : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X) (hT : 0 < T)
    (hT0 : ∀ s : ℂ, s.re = 1 / 2 → |s.im| = T → riemannZeta s ≠ 0) :
    ∃ W : Multiset ℂ, (∀ ρ ∈ W, ρ.re = 1 / 2 ∧ |ρ.im| ≤ T) ∧
      (∀ ρ, (W.count ρ : ℕ∞) ≤ analyticOrderAt riemannZeta₁ ρ) ∧
      HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) (-T) -
        HIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (3 / 4) T +
        VIntegral (SmoothedChebyshevIntegrand F ε X) (3 / 4) (-T) T -
        VIntegral (SmoothedChebyshevIntegrand F ε X) (1 / 4) (-T) T =
      -(2 * Real.pi * I *
        (W.map fun ρ ↦ mellin (fun x ↦ (Smooth1 F ε x : ℂ)) ρ * (X : ℂ) ^ ρ).sum) := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ⟨1 / 4, -T⟩ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ⟨3 / 4, T⟩ := ⟨_, rfl⟩
  have hzre : z.re = 1 / 4 := by rw [hz]
  have hzim : z.im = -T := by rw [hz]
  have hwre : w.re = 3 / 4 := by rw [hw]
  have hwim : w.im = T := by rw [hw]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; norm_num
  have him : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  have hR : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (1 / 4 ≤ s.re ∧ s.re ≤ 3 / 4) ∧ (-T ≤ s.im ∧ s.im ≤ T) := by
    intro s
    rw [Rectangle, mem_reProdIm, uIcc_of_le hre, uIcc_of_le him, hzre, hzim, hwre, hwim]
    rfl
  -- Landau's lemma on a big disc
  obtain ⟨K, -, hLandau⟩ := exists_isZeroFactorization (r₁ := T + 2) (r₂ := T + 3)
    (r := T + 4) (R := T + 5) (by linarith) (by linarith) (by linarith) (by linarith)
  have h2r : T + 3 < T + 4 := by linarith
  obtain ⟨B, hB⟩ := (isCompact_closedBall (2 : ℂ) (T + 4)).exists_bound_of_continuousOn
    differentiable_riemannZeta₁.continuous.continuousOn
  have hcentre : riemannZeta₁ 2 ≠ 0 := by
    rw [riemannZeta₁_eq_sub_one_mul (by norm_num)]
    exact mul_ne_zero (by norm_num) (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  obtain ⟨Z, g, hfact, -, -⟩ := hLandau riemannZeta₁ 2 B
    differentiable_riemannZeta₁.differentiableOn hB hcentre
  have hRball : ∀ s ∈ Rectangle z w, s ∈ closedBall (2 : ℂ) (T + 3) := by
    intro s hs
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (hR s).1 hs
    rw [mem_closedBall, dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : |(s - 2).re| ≤ 7 / 4 := by
      rw [sub_re, re_ofNat, abs_le]
      constructor <;> linarith
    have e2 : |(s - 2).im| ≤ T := by
      rw [sub_im, im_ofNat, sub_zero, abs_le]
      exact ⟨h3, h4⟩
    linarith
  have hRball' : ∀ s ∈ Rectangle z w, s ∈ ball (2 : ℂ) (T + 4) := fun s hs ↦
    closedBall_subset_ball h2r (hRball s hs)
  have hRne1 : ∀ s ∈ Rectangle z w, s ≠ 1 := by
    rintro s hs rfl
    have := ((hR 1).1 hs).1.2
    norm_num at this
  have hRre : ∀ s ∈ Rectangle z w, 0 < s.re := fun s hs ↦ by linarith [((hR s).1 hs).1.1]
  -- the zeros in the rectangle
  have hZre : ∀ ρ ∈ Z, ρ ∈ Rectangle z w → ρ.re = 1 / 2 := by
    intro ρ hρ hρR
    obtain ⟨hρ1, hρ0⟩ := hfact.riemannZeta_eq_zero h2r hρ
    exact re_eq_half_of_riemannZeta_eq_zero hRH (hRre ρ hρR) hρ1 hρ0
  have hZborder : ∀ ρ ∈ Z, ρ ∉ RectangleBorder z w := by
    intro ρ hρ hb
    have hρR := rectangleBorder_subset_rectangle z w hb
    have hρre := hZre ρ hρ hρR
    obtain ⟨-, hρ0⟩ := hfact.riemannZeta_eq_zero h2r hρ
    rcases hb with ((hb | hb) | hb) | hb
    · have : ρ.im = z.im := hb.2
      exact hT0 ρ hρre (by rw [this, hzim, abs_neg, abs_of_pos hT]) hρ0
    · have : ρ.re = z.re := hb.1
      rw [hρre, hzre] at this
      norm_num at this
    · have : ρ.im = w.im := hb.2
      exact hT0 ρ hρre (by rw [this, hwim, abs_of_pos hT]) hρ0
    · have : ρ.re = w.re := hb.1
      rw [hρre, hwre] at this
      norm_num at this
  -- the holomorphic parts
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℂ → ℂ, φ = fun s ↦ deriv g s / g s - (s - 1)⁻¹ := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℂ → ℂ, M = mellin (fun x ↦ (Smooth1 F ε x : ℂ)) := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h : ℂ → ℂ, h = fun s ↦ -(M s * (X : ℂ) ^ s) := ⟨_, rfl⟩
  have hφ : HolomorphicOn φ (Rectangle z w) := by
    rw [hφdef]
    refine DifferentiableOn.sub (DifferentiableOn.div ?_ ?_ ?_) ?_
    · exact ((hfact.differentiableOn.deriv isOpen_ball).mono hRball')
    · exact hfact.differentiableOn.mono hRball'
    · exact fun s hs ↦ hfact.ne_zero s (hRball s hs)
    · exact (differentiableOn_id.sub (differentiableOn_const _)).inv fun s hs ↦
        sub_ne_zero.2 (hRne1 s hs)
  have hh : HolomorphicOn h (Rectangle z w) := by
    rw [hhdef]
    intro s hs
    have h1 : DifferentiableAt ℂ M s := by
      rw [hMdef]
      exact Smooth1MellinDifferentiable diffF suppF ⟨hε, hε1⟩ Fnonneg mass_one (hRre s hs)
    have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ (X : ℂ) ^ s) s :=
      differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 hX.ne'))
    exact (h1.mul h2).neg.differentiableWithinAt
  -- the integrand on the border
  have hEq : EqOn (SmoothedChebyshevIntegrand F ε X)
      (fun s ↦ ((Z.map fun ρ ↦ (s - ρ)⁻¹).sum + φ s) * h s) (RectangleBorder z w) := by
    intro s hs
    have hsR := rectangleBorder_subset_rectangle z w hs
    have hsZ : s ∉ Z := fun hmem ↦ hZborder s hmem hs
    obtain ⟨-, heq⟩ := hfact.deriv_riemannZeta_div_eq h2r (hRball s hsR) hsZ (hRne1 s hsR)
    simp only [SmoothedChebyshevIntegrand]
    rw [neg_div, heq, hφdef, hhdef, hMdef]
    ring
  have key := rectangleIntegral_multiset_sum_inv_sub_add_mul hre him hφ hh Z hZborder
  rw [← RectangleIntegral_congr hEq] at key
  refine ⟨Z.filter (· ∈ Rectangle z w), ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨hρZ, hρR⟩ := Multiset.mem_filter.1 hρ
    refine ⟨hZre ρ hρZ hρR, ?_⟩
    rw [abs_le]
    exact ((hR ρ).1 hρR).2
  · intro ρ
    by_cases hρ : ρ ∈ Z.filter (· ∈ Rectangle z w)
    · have hρR := (Multiset.mem_filter.1 hρ).2
      rw [← hfact.count_eq_analyticOrderAt h2r (hRball ρ hρR)]
      exact_mod_cast Multiset.count_le_of_le ρ (Multiset.filter_le _ Z)
    · rw [Multiset.count_eq_zero_of_notMem hρ]
      simp
  · have hneg : ((Z.filter (· ∈ Rectangle z w)).map h).sum =
        -((Z.filter (· ∈ Rectangle z w)).map fun ρ ↦ M ρ * (X : ℂ) ^ ρ).sum := by
      rw [hhdef, Multiset.sum_map_neg]
    rw [hneg, hMdef] at key
    rw [RectangleIntegral, hzre, hzim, hwre, hwim] at key
    rw [key]
    ring

end RHPrimeError
