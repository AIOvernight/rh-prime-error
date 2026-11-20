# von Koch's bound `ψ(x) - x = O(√x log² x)` under RH: paper proof

Status: fully formalised (no `sorry`) in `Landau.lean`, `ZetaLocal.lean` (B1–B3),
`ZetaZeros.lean` (B4–B6), `Residues.lean`, `Bounds.lean`, `Main.lean` of this directory.

Notation: `ζ₁(s) = (s - 1) ζ(s)` (entire, `ζ₁(1) = 1`; Mathlib's `riemannZeta₁`),
`L(τ) = log(|τ| + 3) ≥ 1`. `ν` is a fixed admissible smoothing function, `M_ε = 𝓜(Smooth1 ν ε)`,
`h(s) = M_ε(s) X^s` (holomorphic on `Re s > 0`), `G = -(ζ'/ζ) h` (the integrand
`SmoothedChebyshevIntegrand ν ε X` of PrimeNumberTheoremAnd, "PNT+" below).

## A. Landau's lemma (factorised form)  — `Landau.lean`

**Lemma A.** Let `0 < r₁ < r₂ < r < R`, `λ = log(r / r₂)`,
`K = 8 r₂ / (r₂ - r₁)² + r₂ / (r (r - r₂) λ)`. Let `f` be holomorphic on `ball c R`, `‖f‖ ≤ B` on
`closedBall c r`, `f c ≠ 0`, `E = log(B / ‖f c‖) ≥ 0`. Then there are a finite multiset `Z` of
points of `closedBall c r₂` and `g` holomorphic on `ball c r` such that
1. `f z = ∏_{ρ ∈ Z} (z - ρ) · g z` on `ball c r`;
2. `g ≠ 0` on `closedBall c r₂`;
3. `card Z · λ ≤ E`;
4. `‖g'/g‖ ≤ K E` on `closedBall c r₁`.

*Proof.* Induction on `n` with `E < n λ`. If `f` has no zero in `closedBall c r₂`, take `Z = ∅`,
`g = f`; 4 is Borel–Carathéodory applied to a logarithm of `f` on `ball c r₂` plus a Cauchy
estimate (`norm_deriv_div_le_of_forall_mem_ball_ne_zero`, constant `8 r₂ / (r₂ - r₁)²`).
Otherwise pick a zero `ρ ∈ closedBall c r₂` (so `ρ ≠ c`), let
`D(w) = r² - conj(ρ - c)(w - c)` and `f₁ = dslope f ρ · D / r`, so `f D = r (w - ρ) f₁`.
On the circle `|w - c| = r`, `|D(w)| = r |w - ρ|`, so `|f₁| = |f| ≤ B` there and, by the maximum
principle, on `closedBall c r`. At the centre `|f₁(c)| = |f(c)| r / |c - ρ| ≥ |f(c)| r / r₂`,
so `E₁ := log(B / |f₁(c)|) ≤ E - λ < (n-1) λ` (in particular `n ≥ 1` is consistent with `E₁ ≥ 0`).
By induction `f₁ = P₁ g₁`. On `closedBall c r`, `|D| ≥ r² - r₂ r > 0`. Put `Z = ρ :: Z₁`,
`g = g₁ r / D`. Then 1–3 are clear and `g'/g = g₁'/g₁ + conj(ρ - c)/D`, with
`|conj(ρ - c)/D| ≤ r₂ / (r (r - r₂)) =: K₁` on `closedBall c r₂`, hence
`‖g'/g‖ ≤ K E₁ + K₁ ≤ K (E - λ) + K₁ ≤ K E` because `K₁ ≤ K λ`. ∎

**Corollaries** (for `z ∈ ball c r`):
* `f z = 0 ∧ z ∈ closedBall c r₂ ⟹ z ∈ Z`; conversely every `ρ ∈ Z` is a zero of `f`;
* for `ρ ∈ closedBall c r₂`: `count ρ Z = analyticOrderAt f ρ`
  (write `f = (z - ρ)^{count} · (∏_{ρ' ≠ ρ} (z - ρ') · g)`, the second factor is analytic and
  nonzero at `ρ`);
* if `z ∉ Z` and `g z ≠ 0`: `f'/f(z) = Σ_{ρ ∈ Z} 1/(z - ρ) + g'/g(z)`.

## B. Zeros of zeta  — `ZetaLocal.lean` (B1–B3), `ZetaZeros.lean` (B4–B6)

**B1 (growth).** For `Re s > 0`: `‖ζ₁(s)‖ ≤ (‖s‖ + 1)/2 + ‖s‖ ‖s - 1‖ / Re s`.
From PNT+ `Zeta0EqZeta` with `N = 1`:
`ζ(s) = 1 + 1/(s-1) - 1/2 + s J(s)`, `J(s) = ∫_1^∞ (⌊x⌋ + 1/2 - x) x^{-s-1} dx`,
`|J(s)| ≤ 1/Re s` (`ZetaBnd_aux1b`). So `ζ₁(s) = (s + 1)/2 + s (s - 1) J(s)` for `s ≠ 1`; at
`s = 1` the bound is trivial.

**B2 (centre).** `|ζ(3/2 + iτ)| ≥ m := |ζ(3)/ζ(3/2)| > 0` (PNT+ `ZetaFixedLowerBound`), hence
`|ζ₁(3/2 + iτ)| ≥ m/2`.

**B3 (local structure).** Radii `r₁ = 27/20 < r₂ = 69/50 < r = 71/50 < R = 29/20`, centre
`c_τ = 3/2 + iτ`. On `closedBall c_τ r`: `Re s ≥ 2/25`, `‖s‖ ≤ |τ| + 3`, so
`‖ζ₁‖ ≤ (|τ| + 4)/2 + (|τ| + 3)(|τ| + 4)·(25/2) ≤ 13 (|τ| + 4)² =: B_τ`.
`E_τ ≤ log(26 (|τ| + 4)² / m) ≤ (|log(26/m)| + 4) L(τ)` since `|τ| + 4 ≤ (|τ| + 3)²`.
Lemma A gives a constant `A` and, for every real `τ`, `Z_τ`, `g_τ` with
`card Z_τ ≤ A L(τ)`, `‖g_τ'/g_τ‖ ≤ A L(τ)` on `closedBall c_τ r₁`, `count ρ Z_τ = ord_ρ ζ₁` for
`ρ ∈ closedBall c_τ r₂`.

Geometry used below: the box `[1/4, 3/4] × [τ - 1/2, τ + 1/2]` lies in `closedBall c_τ r₁`
(`(5/4)² + (1/2)² = 1.8125 ≤ 1.8225 = r₁²`).

For `s ≠ 1`, `ζ(s) ≠ 0`: `ζ'/ζ(s) = ζ₁'/ζ₁(s) - 1/(s - 1)`.

**B4 (line `Re s = 1/4`, RH).** For real `t`, `s = 1/4 + it ∈ closedBall c_t r₁`. Each `ρ ∈ Z_t`
is a zero of `ζ` with `Re ρ ≥ 3/2 - r₂ > 0`, so `Re ρ = 1/2` by RH, `|s - ρ| ≥ 1/4`. Hence
`ζ(s) ≠ 0` and `|ζ'/ζ(s)| ≤ 4 A L(t) + A L(t) + 1/|s - 1| ≤ (5A + 2) L(t)`.

**B5 (good heights, no RH).** Let `T₀ ≥ 1`, `τ = T₀ + 1/2`, `Z₊ = Z_τ`, `Z₋ = Z_{-τ}`,
`N = card Z₊ + card Z₋ ≤ 2 A L(τ)`, `δ = 1/(2(N + 1))`. The `N + 1` points
`t_j = T₀ + (2j + 1) δ ∈ [T₀, T₀ + 1]` (`0 ≤ j ≤ N`) are `2δ`-separated, so each of the `N`
numbers `Im ρ` (`ρ ∈ Z₊`), `-Im ρ` (`ρ ∈ Z₋`) is at distance `< δ` from at most one `t_j`; by
pigeonhole some `T = t_j` has `|T - Im ρ| ≥ δ` for `ρ ∈ Z₊` and `|T + Im ρ| ≥ δ` for `ρ ∈ Z₋`.
For `1/4 ≤ σ ≤ 3/4`, `s = σ ± iT ∈ closedBall c_{±τ} r₁`, so `ζ(s) ≠ 0` and
`|ζ'/ζ(s)| ≤ N/δ + A L + 1 = 2N(N+1) + A L + 1 ≤ (4A(2A+1) + A + 1) L²` with
`L = log(T₀ + 4) ≥ L(τ)`, using `N ≤ 2 A L`, `N + 1 ≤ (2A + 1) L`, `|s - 1| ≥ T ≥ 1`.

**B6 (sum over zeros, no RH).** Let `T ≥ 1` and `W` a finite multiset with `Re ρ = 1/2`,
`|Im ρ| ≤ T` and `count ρ W ≤ ord_ρ ζ₁` for all `ρ`. Then
`Σ_{ρ ∈ W} 1/‖ρ‖ ≤ 8 A log(T + 4)²`.
Proof: put `k(ρ) = ⌊|Im ρ|⌋ ∈ {0, …, ⌊T⌋}`. A `ρ` with `k(ρ) = k` lies in
`closedBall c_{k + 1/2} r₂` or `closedBall c_{-(k + 1/2)} r₂` (`1 + 1/4 ≤ r₂²`), so
`count ρ W ≤ count ρ (Z_{k+1/2} + Z_{-(k+1/2)})`, and `‖ρ‖ ≥ max(1/2, k) ≥ (k + 1)/2`. Hence the
part of the sum with `k(ρ) = k` is `≤ 2/(k+1) · 2 A L(k + 1/2) ≤ 4 A log(T + 4)/(k + 1)` and
`Σ_{k ≤ ⌊T⌋} 1/(k+1) ≤ 1 + log(⌊T⌋ + 1) ≤ 2 log(T + 4)`.

## C. Residue identity  — `Residues.lean`

**C1 (general).** Rectangle with corners `z, w` (`z.re ≤ w.re`, `z.im ≤ w.im`), `φ, h`
holomorphic on the closed rectangle, `Z` a finite multiset with no point on the border. Then
`∮ (Σ_{ρ ∈ Z} 1/(s - ρ) + φ(s)) h(s) ds = 2πi Σ_{ρ ∈ Z, ρ ∈ rectangle} h(ρ)`.
Induction on `Z`: `h(s)/(s - ρ)` is holomorphic on the rectangle if `ρ` is outside, and equals
`h(ρ)/(s - ρ) + dslope h ρ s` if `ρ` is inside (PNT+ `ResidueTheoremOnRectangleWithSimplePole`).
Here `∮ = RectangleIntegral = bottom - top + right - left` (PNT+ convention).

**C2 (zeta, RH).** Let `T > 0` with `ζ(1/2 ± iT) ≠ 0`, `0 < ε < 1`, `X > 0`. Apply Lemma A to
`ζ₁` on the big disc of centre `2` and radii `T + 2 < T + 3 < T + 4 < T + 5` (`ζ₁(2) = ζ(2) ≠ 0`,
`B` any bound on the compact disc): `ζ₁ = P_Z g`. The rectangle
`R_T = [1/4, 3/4] × [-T, T]` lies in `closedBall 2 (T + 2)`. A point `ρ ∈ Z ∩ R_T` is a zero of
`ζ` with `0 < Re ρ`, `ρ ≠ 1`, so `Re ρ = 1/2`; it is not on the border since
`ζ(1/2 ± iT) ≠ 0`. On the border `ζ ≠ 0` (vertical sides: RH; horizontal sides: RH and the choice
of `T`), and `-ζ'/ζ = -(Σ_Z 1/(s - ρ) + g'/g - 1/(s-1))`. By C1 with `φ = g'/g - 1/(s - 1)`,
`∮_{∂R_T} G = -2πi Σ_{ρ ∈ W} h(ρ)`, `W = Z ∩ R_T`, and `count ρ W ≤ count ρ Z = ord_ρ ζ₁`.

## D. Estimates and assembly  — `Bounds.lean`, `Main.lean`

Let `C₄` with `‖M_ε(s)‖ ≤ C₄/‖s‖` for `0 < Re s ≤ 2` (`Mellin.lean`), `X ≥ 1`, `T ≥ 1` a good
height (B5) for `T₀`, i.e. `T ∈ [T₀, T₀ + 1]`. Write
`∮_{∂R_T} G = H(-T) - H(T) + V(3/4) - V(1/4)` and `I₃₇ = V(3/4)/(2πi)`. Hence
`I₃₇ = -Σ_W h(ρ) + (V(1/4) - H(-T) + H(T))/(2πi)` and
* `‖Σ_W h(ρ)‖ ≤ √X C₄ Σ_W 1/‖ρ‖ ≤ 8 A C₄ √X log(T + 4)²` (B6, `|X^ρ| = √X`);
* `‖V(1/4)‖ ≤ ∫_{-T}^{T} (5A+2) L(t) · C₄/‖1/4 + it‖ · X^{1/4} dt
   ≤ (5A+2) C₄ X^{1/4} log(T + 3) · 5 · 2 log(1 + T)` (`‖1/4 + it‖ ≥ (1 + |t|)/5`);
* `‖H(±T)‖ ≤ (1/2) · C_h L(T₀ + 1/2)² · C₄/T · X^{3/4}`.

Assembly as in `RHPrimeError/Main.lean` with `ε = X^{-1/2}`, `T₀ = X²`, `T ∈ [X², X² + 1]` good,
`σ₁ = 3/4` in `SmoothedChebyshevPull1`:
`ψ(X) - X = -(ψ_ε(X) - ψ(X)) + I₁ - I₂ + I₃₇ + I₈ + I₉ + (M_ε(1) - 1) X`, where
`|ψ_ε - ψ| ≤ c₀ ε X log X = c₀ √X log X`, `|(M_ε(1) - 1) X| ≤ c ε X = c √X`,
`|I₁|, |I₉| ≤ c X log X/(ε T) ≤ c √X log X` (as `T ≥ X²`), `|I₂|, |I₈| ≤ c X/(ε T) ≤ c √X`, and
by the above, using `log(T + 4) ≤ 3 log X` for `X ≥ 4`,
`|I₃₇| ≤ C √X log² X + C X^{1/4} log² X + C X^{3/4} log² X / X² ≤ C' √X log² X`.
Hence `ψ(X) - X = O(√X log² X)`. ∎

## Design choices

* Discs are centred at `3/2 + iτ` because PrimeNumberTheoremAnd already has the uniform lower
  bound `ZetaFixedLowerBound` on `Re s = 3/2`.
* Lemma A is stated as a factorisation `f = ∏ (z - ρ) · g` rather than through `f'/f`; the
  logarithmic-derivative identity, the zero count, and "count = analytic order" are corollaries.
* Residue identity: the global holomorphic part is obtained by applying Lemma A on one big disc
  containing `R_T` (no quantitative information is used there), which avoids a separate
  finiteness/removable-singularity argument. Multiplicities of the big-disc multiset and of the
  local multisets are compared through `analyticOrderAt`.
* Good heights need no RH and no conjugation symmetry (both `Z_τ` and `Z_{-τ}` are avoided).
* Horizontal sides use only `‖M_ε(s)‖ ≤ C₄/‖s‖` (enough since `T ≥ X²`).
* Constants: `K` in Lemma A and the constants of B1–B6 are as in the Lean code; the numeric
  constants of section D are indicative only.
