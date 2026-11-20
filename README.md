# RH and the error term in the prime number theorem, in Lean 4

[![CI](https://github.com/AIOvernight/rh-prime-error/actions/workflows/ci.yml/badge.svg)](https://github.com/AIOvernight/rh-prime-error/actions/workflows/ci.yml)

A Lean 4 formalization of the classical equivalence between the Riemann Hypothesis and a square-root error term in the prime number theorem, with its consequences for `θ`, `π` and primes in short intervals. The direction "RH ⇒ error term" is built on top of the [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project.

## Statements

```lean
theorem riemannHypothesis_iff_chebyshev_psi_sub_isBigO :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε)

theorem chebyshev_psi_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis (hRH : RiemannHypothesis) :
    (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop]
      fun x : ℝ => Real.sqrt x * Real.log x ^ 2

theorem chebyshev_theta_sub_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => Chebyshev.theta x - x) =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε)

theorem primeCounting_sub_integral_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t)
        =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε)

theorem exists_prime_mem_Ioc_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (1 / 2 + ε)
```

That is: RH holds if and only if `ψ(x) = x + O(x^(1/2+ε))` for every `ε > 0`; under RH one has von Koch's sharp form `ψ(x) = x + O(√x · log² x)`; and under RH, `θ(x) = x + O(x^(1/2+ε))`, `π(x) = ∫₂ˣ dt / log t + O(x^(1/2+ε))`, and every interval `(x, x + x^(1/2+ε)]` with `x` large contains a prime. The two directions of the equivalence are also available separately, as `chebyshev_psi_sub_isBigO_of_riemannHypothesis` and `riemannHypothesis_of_chebyshev_psi_sub_isBigO`.

`RiemannHypothesis`, `Chebyshev.psi`, `Chebyshev.theta` and `Nat.primeCounting` are Mathlib's own definitions. The statements use nothing defined in this repository or in PrimeNumberTheoremAnd; the logarithmic integral is written out as an integral so that no auxiliary definition is involved.

## What this is, and what it is not

- **Nothing here proves RH.** The first theorem is an equivalence between RH and a statement about primes that is just as open; the others say "if RH, then …".
- **The mathematics is classical**, usually attributed to von Koch (1901). The contribution here is the machine-checked proof.
- **Most of the machinery for "RH ⇒ error term" is not ours.** The smoothed Chebyshev function, its closeness to `ψ`, the Mellin calculus and the contour shift with its residue are theorems of the PrimeNumberTheoremAnd project (Kontorovich, Tao and collaborators), which uses them for its "medium" prime number theorem. What is added here is the input that RH provides (holomorphy and a logarithmic bound for `ζ'/ζ` to the right of the critical line), the estimates of the shifted contour at `Re s = 1/2 + δ`, the choice of parameters, and the passage from `ψ` to `θ` and `π`. The converse direction does not use PrimeNumberTheoremAnd at all: it imports only Mathlib.
- **The sharp form is proved for `ψ` only.** `ψ(x) = x + O(√x · log² x)` under RH is von Koch's bound. The statements for `θ`, `π` and short intervals are still the `ε` versions, where an arbitrarily small power of `x` is lost; the sharp `π(x) = li(x) + O(√x · log x)` is not included. Explicit constants are not tracked. The statement on primes in short intervals is far from Legendre's or Cramér's conjectures, which do not follow from RH.
- **The equivalence is stated for `ψ` only.** For `θ` and `π` only the direction from RH is proved.
- **Novelty.** At the pinned commit, PrimeNumberTheoremAnd uses `RiemannHypothesis` as a hypothesis only in statements about prime gaps, and we found no Lean proof of this implication there, in Mathlib, or through GitHub code search. That is a bounded search, not a guarantee; we have not asked on the Lean Zulip.

## Verification status

- `lake build` succeeds with Lean `v4.35.0` and PrimeNumberTheoremAnd at commit `a4fb6989b07e9c76b511807ae93e33e25b820e9b` (which pins Mathlib). CI rebuilds on every push, scans the sources for `sorry` and escape hatches, and fails if a main theorem uses a non-standard axiom.
- `#print axioms` on the seven theorems reports only `propext`, `Classical.choice`, `Quot.sound`.
- **About `sorry` in the dependency.** PrimeNumberTheoremAnd contains unfinished parts (`sorry`) elsewhere. None of them is used: a `sorry` anywhere in the dependency chain of a theorem shows up as the axiom `sorryAx`, and it does not appear above.
- No `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `@[extern]`, `opaque` or `set_option` in the sources of this repository.
- Replayed through the kernel with `leanchecker`, one module at a time: all fourteen modules pass.
- Not yet reviewed by a human expert.

## How to check it yourself

```bash
lake exe cache get      # prebuilt Mathlib
lake build              # also compiles the needed part of PrimeNumberTheoremAnd
lake env lean Check.lean
```

The last command prints, for each of the seven theorems, `depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Proof outline

Let `ψ_ε` be the smoothed Chebyshev function of PrimeNumberTheoremAnd, a vertical integral of `(−ζ'/ζ)(s) · 𝓜(smooth cutoff)(s) · X^s` over `Re s = 1 + 1/log X`.

1. `|ψ_ε(X) − ψ(X)| ≤ C · ε · X · log X` (PrimeNumberTheoremAnd).
2. Under RH, `ζ'/ζ` is holomorphic on every rectangle `[σ₁, 2] × [−T, T]` minus `{1}` with `σ₁ > 1/2`, so the contour can be moved to `Re s = σ₁`, picking up the residue `≈ X` at `s = 1` (PrimeNumberTheoremAnd's contour-pull theorem, applied with RH).
3. Under RH, `|ζ'/ζ(s)| ≤ C log |t|` for `σ₁ ≤ Re s ≤ 2`, `|t| ≥ 3`: a zero-free disc, a polynomial bound for ζ, and Borel–Carathéodory.
4. The Mellin transform of the smooth cutoff is `O(1/|s|)` uniformly in `ε`, so the integral over the new vertical segment is `O(X^σ₁ · log² T)`; the horizontal segments and the tails are negligible.
5. Take `σ₁ = 1/2 + δ`, `ε = X^(−1/2)` and `T = X²`: `ψ(X) − X = O(X^(1/2+δ) · log² X)`.
6. `ψ − θ = O(√x)` and partial summation give the statements for `θ` and `π` (Mathlib); comparing `θ(x + h)` with `θ(x)` gives primes in short intervals.

**Sharp form.** Keeping the contour to the right of the critical line and bounding `ζ'/ζ` in absolute value cannot give `log²`. Instead the contour is moved from `Re s = 3/4` across the critical line to `Re s = 1/4`, picking up a residue at every zero. The inputs are a form of Landau's lemma (a holomorphic function bounded on a disc factors as a product over its zeros times a zero-free function with controlled logarithmic derivative, with a bound on the number of zeros), applied to `(s − 1)ζ(s)`: at most `C log t` zeros at height `t`, `ζ'/ζ = O(log t)` on `Re s = 1/4` under RH, and heights `T` that stay away from all zeros. Under RH each residue has size `√X / |ρ|`, and `Σ 1/|ρ| ≪ log² T`. A paper proof is in `RHPrimeError/Sharp/NOTES.md`.

**Converse.** If `ψ(x) − x = O(x^(1/2+ε))` for every `ε`, then by Abel summation `−ζ'/ζ(s) = s/(s−1) + s·H(s)` for `Re s > 1`, where `H(s) = ∫₁^∞ (ψ(x) − x) x^(−s−1) dx` is holomorphic on `Re s > 1/2`. By the identity theorem `ζ' + ζ·K = 0` on `Re s > 1/2`, `s ≠ 1`, with `K` holomorphic; comparing orders of vanishing, ζ cannot have a zero there. The functional equation then shows that the only zeros with `Re s < 1/2` are the trivial ones, which is Mathlib's `RiemannHypothesis`.

| File | Content |
|---|---|
| `RHPrimeError/LogDeriv.lean` | Under RH: ζ has no zeros with `Re s > 1/2`; `‖ζ'/ζ‖ ≤ C log |t|` to the right of the critical line |
| `RHPrimeError/Mellin.lean` | `‖𝓜(Smooth1 ν ε)(s)‖ ≤ 4 / ‖s‖`, uniformly in `ε` |
| `RHPrimeError/Contour.lean` | Holomorphy of `ζ'/ζ` under RH; bounds for the shifted contour |
| `RHPrimeError/Main.lean` | RH implies the error term for `ψ` |
| `RHPrimeError/PrimeCounting.lean` | The theorems for `θ` and `π` |
| `RHPrimeError/PrimeGaps.lean` | Primes in short intervals |
| `RHPrimeError/Converse.lean` | The error term implies RH; also `riemannHypothesis_of_forall_riemannZeta_ne_zero`: no zeros with `Re s > 1/2` implies RH |
| `RHPrimeError/Equivalence.lean` | The equivalence |
| `RHPrimeError/Sharp/Landau.lean` | Landau's lemma: factorisation over the zeros in a disc, zero count, formula for `f'/f` |
| `RHPrimeError/Sharp/ZetaLocal.lean` | The factorisation for `(s − 1)ζ(s)` on discs at height `τ`, with bounds `O(log τ)` |
| `RHPrimeError/Sharp/ZetaZeros.lean` | `ζ'/ζ` on `Re s = 1/4` under RH; heights avoiding the zeros; `Σ 1/‖ρ‖ ≪ log² T` |
| `RHPrimeError/Sharp/Residues.lean` | Residue theorem on a rectangle for finitely many simple poles; the contour identity across the critical line |
| `RHPrimeError/Sharp/Bounds.lean` | Bounds for the left side, the horizontal sides and the sum over zeros |
| `RHPrimeError/Sharp/Main.lean` | The sharp bound for `ψ` |

## How it was produced

Everything in this repository was written by Claude (Anthropic) in a Claude Code session directed by the repository owner. Claude chose the proof strategy and split the work; Claude subagents, several of them in parallel, wrote the Lean proofs. The sharp bound was done by a single subagent from a proof plan, which it adjusted in several places (listed in `Sharp/NOTES.md`). All of it was checked by the Lean kernel. **No part of the Lean code has been written or reviewed line by line by a human.**

## Context

This was written on 2026-11-20, the day Levent Alpöge announced a Lean formalization of a proof of RH. That announcement is the motivation: **assuming his proof is correct, the conclusions of these theorems follow**, since his main theorem and our hypothesis are the same Mathlib statement, `RiemannHypothesis`.

Two things should be kept apart:

- **What is proved here** is only the implications. They do not import his code and they remain true whether or not his proof is correct.
- **What we assume, and have not checked,** is the correctness of his proof. We have not built or audited his formalization. Note also that this repository uses a newer Lean and Mathlib than his, so combining the two would require porting one of them. Until his proof is independently confirmed, the conclusions remain conditional.

A companion repository, [rh-implies-lindelof](https://github.com/AIOvernight/rh-implies-lindelof), contains the Lindelöf bounds.
