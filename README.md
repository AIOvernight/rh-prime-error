# RH and the error term in the prime number theorem, in Lean 4

[![CI](https://github.com/AIOvernight/rh-prime-error/actions/workflows/ci.yml/badge.svg)](https://github.com/AIOvernight/rh-prime-error/actions/workflows/ci.yml)

A Lean 4 formalization of the classical equivalence between the Riemann Hypothesis and a square-root error term in the prime number theorem, and of von Koch's sharp bounds for `ψ`, `θ` and `π` under RH. The direction "RH ⇒ error term" is built on top of the [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project.

## Statements

The equivalence:

```lean
theorem riemannHypothesis_iff_chebyshev_psi_sub_isBigO :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε)
```

The sharp bounds under RH:

```lean
theorem chebyshev_psi_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis (hRH : RiemannHypothesis) :
    (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop]
      fun x : ℝ => Real.sqrt x * Real.log x ^ 2

theorem chebyshev_theta_sub_isBigO_sqrt_mul_log_sq_of_riemannHypothesis (hRH : RiemannHypothesis) :
    (fun x : ℝ => Chebyshev.theta x - x) =O[Filter.atTop]
      fun x : ℝ => Real.sqrt x * Real.log x ^ 2

theorem primeCounting_sub_integral_isBigO_sqrt_mul_log_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t)
      =O[Filter.atTop] fun x : ℝ => Real.sqrt x * Real.log x

theorem exists_prime_mem_Ioc_sqrt_mul_log_sq_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + C * Real.sqrt x * Real.log x ^ 2
```

That is:

- RH holds if and only if `ψ(x) = x + O(x^(1/2+ε))` for every `ε > 0`.
- Under RH, `ψ(x) = x + O(√x · log² x)` and `θ(x) = x + O(√x · log² x)` (von Koch's bounds).
- Under RH, `π(x) = ∫₂ˣ dt / log t + O(√x · log x)`.
- Under RH, for large `x` there is a prime in `(x, x + C · √x · log² x]`.

The two directions of the equivalence are available separately (`chebyshev_psi_sub_isBigO_of_riemannHypothesis`, `riemannHypothesis_of_chebyshev_psi_sub_isBigO`), as are the weaker `x^(1/2+ε)` versions of the statements for `θ`, `π` and short intervals, which are corollaries of the sharp ones.

`RiemannHypothesis`, `Chebyshev.psi`, `Chebyshev.theta`, `Nat.primeCounting` and `Real.sqrt` are Mathlib's own definitions. The statements use nothing defined in this repository or in PrimeNumberTheoremAnd; the logarithmic integral is written out as an integral so that no auxiliary definition is involved.

## What this is, and what it is not

- **Nothing here proves RH.** The first theorem is an equivalence between RH and a statement about primes that is just as open; the others say "if RH, then …".
- **The mathematics is classical**, usually attributed to von Koch (1901).
- **What is ours and what is not.** For "RH ⇒ error term", the starting point is not ours: the smoothed Chebyshev function, its closeness to `ψ`, the Mellin calculus and the first contour shift (with the residue at `s = 1`) are theorems of the PrimeNumberTheoremAnd project (Kontorovich, Tao and collaborators), which uses them for its "medium" prime number theorem; a few of its bounds for ζ are used as well. Added here: the inputs that RH provides for `ζ'/ζ`; for the sharp form, Landau's lemma, the local count of zeros of ζ, a residue theorem on rectangles for several simple poles and the contour shift across the critical line; the choice of parameters; and the passage from `ψ` to `θ`, `π` and short intervals. The converse direction does not use PrimeNumberTheoremAnd at all: it imports only Mathlib.
- **No explicit constants.** All bounds are `O(·)` statements with unspecified constants. The short-interval statement is weaker than Cramér's conditional bound `O(√x · log x)` for prime gaps, and far from Legendre's or Cramér's conjectures, which do not follow from RH.
- **The equivalence is stated for `ψ` only.** For `θ` and `π` only the direction from RH is proved.
- **Prior work: the main bounds were already formalized.** Jonathan Hanke's [analytic-number-theory-lean](https://github.com/jonhanke/analytic-number-theory-lean), which formalizes Apostol's and Davenport's books on top of Mathlib alone, already contains von Koch's bound (`NTKB.Davenport.psi_sub_self_le_of_riemannHypothesis`), the bound for `π(x)` under RH (`NTKB.Davenport.primeCounting_sub_logIntegral_le_of_riemannHypothesis`) and the analogue in arithmetic progressions under GRH. Its statements are stronger than ours (an explicit inequality for all `x ≥ 2`, and a general version for zeros with real part at most `Θ`). We found it only after writing this repository; the search we did beforehand covered PrimeNumberTheoremAnd alone. So the sharp bounds here are **not new**: they are an independent proof by a different route (smoothed Chebyshev function and contour shifts from PrimeNumberTheoremAnd, instead of Davenport's explicit formula).
- **What we did not find elsewhere.** The converse for `ψ` and the resulting equivalence with Mathlib's `RiemannHypothesis`: not in the library above (searched at commit `35fe0c9`), not in Mathlib, not in PrimeNumberTheoremAnd, not in [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (searched at commit `911e17d6`; it relates `RiemannHypothesis` to the zeros of the completed zeta function, which is a different statement), and not through GitHub code search. A closely related converse, for a smoothed sum instead of `ψ` and with a one-sided hypothesis, is part of Levent Alpöge's formalization (`riemann_hypothesis_of_power_bound`), which we have not built. PrimeNumberTheoremAnd states, without proof, sharper explicit results on primes in short intervals under RH than the one here. All of this is a bounded search, not a guarantee; we have not asked on the Lean Zulip.

## Verification status

- `lake build` succeeds with Lean `v4.35.0` and PrimeNumberTheoremAnd at commit `a4fb6989b07e9c76b511807ae93e33e25b820e9b` (which pins Mathlib). CI rebuilds on every push, scans the sources for `sorry` and escape hatches, and fails if a main theorem uses a non-standard axiom.
- `#print axioms` on the ten theorems reports only `propext`, `Classical.choice`, `Quot.sound`.
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

The last command prints, for each of the ten theorems, `depends on axioms: [propext, Classical.choice, Quot.sound]` (for long names Lean wraps the list over three lines).

## Proof outline

**RH ⇒ `ψ(x) = x + O(√x · log² x)`.** Let `ψ_ε` be the smoothed Chebyshev function of PrimeNumberTheoremAnd, a vertical integral of `G(s) = (−ζ'/ζ)(s) · 𝓜(smooth cutoff)(s) · X^s` over `Re s = 1 + 1/log X`. Take `ε = X^(−1/2)` and a height `T` between `X²` and `X² + 1`.

1. `|ψ_ε(X) − ψ(X)| ≤ C · ε · X · log X` (PrimeNumberTheoremAnd).
2. Under RH, `ζ'/ζ` is holomorphic on `[3/4, 2] × [−T, T]` minus `{1}`, so the contour can be moved to `Re s = 3/4`, picking up the residue `≈ X` at `s = 1` (PrimeNumberTheoremAnd's contour-pull theorem, applied with RH). The tails and the horizontal sides are negligible; for the latter one uses `|ζ'/ζ(s)| ≤ C log |t|` to the right of the critical line, from a zero-free disc and Borel–Carathéodory.
3. The remaining segment is moved from `Re s = 3/4` across the critical line to `Re s = 1/4`, picking up a residue at every zero. Keeping the contour to the right of the line and bounding `ζ'/ζ` in absolute value cannot give `log²`.
4. The inputs for step 3 come from a form of Landau's lemma (a holomorphic function bounded on a disc factors as a product over its zeros times a zero-free function with controlled logarithmic derivative, with a bound on the number of zeros), applied to `(s − 1)ζ(s)`: at most `C log t` zeros at height `t`, `ζ'/ζ = O(log t)` on `Re s = 1/4` under RH, and heights `T` that stay away from all zeros.
5. The Mellin transform of the smooth cutoff is `O(1/|s|)` uniformly in `ε`. Under RH each residue has size `√X / |ρ|`, and `Σ 1/|ρ| ≪ log² T`; the segment at `Re s = 1/4` contributes `O(X^(1/4) · log² T)`.

A paper proof with the constants is in `RHPrimeError/Sharp/NOTES.md`.

**`θ`, `π`, short intervals.** `ψ − θ = O(√x)` and partial summation (Mathlib) give the bounds for `θ` and `π`; comparing `θ(x + h)` with `θ(x)` gives primes in short intervals. The `x^(1/2+ε)` versions follow since `√x · logⁿ x = o(x^(1/2+ε))`.

**Converse.** If `ψ(x) − x = O(x^(1/2+ε))` for every `ε`, then by Abel summation `−ζ'/ζ(s) = s/(s−1) + s·H(s)` for `Re s > 1`, where `H(s) = ∫₁^∞ (ψ(x) − x) x^(−s−1) dx` is holomorphic on `Re s > 1/2`. By the identity theorem `ζ' + ζ·K = 0` on `Re s > 1/2`, `s ≠ 1`, with `K` holomorphic; comparing orders of vanishing, ζ cannot have a zero there. The functional equation then shows that the only zeros with `Re s < 1/2` are the trivial ones, which is Mathlib's `RiemannHypothesis`.

| File | Content |
|---|---|
| `RHPrimeError/LogDeriv.lean` | Under RH: ζ has no zeros with `Re s > 1/2`; `‖ζ'/ζ‖ ≤ C log |t|` to the right of the critical line |
| `RHPrimeError/Mellin.lean` | `‖𝓜(Smooth1 ν ε)(s)‖ ≤ 4 / ‖s‖`, uniformly in `ε` |
| `RHPrimeError/Contour.lean` | Holomorphy of `ζ'/ζ` under RH; bounds for the horizontal sides of the first contour shift |
| `RHPrimeError/Theta.lean` | Without RH, Mathlib only: the exact formula for `π(x) − ∫₂ˣ dt/log t` in terms of `θ`; `θ(x) < θ(y)` gives a prime in `(x, y]` |
| `RHPrimeError/Sharp/Landau.lean` | Landau's lemma: factorisation over the zeros in a disc, zero count, formula for `f'/f` |
| `RHPrimeError/Sharp/ZetaLocal.lean` | The factorisation for `(s − 1)ζ(s)` on discs at height `τ`, with bounds `O(log τ)` |
| `RHPrimeError/Sharp/ZetaZeros.lean` | `ζ'/ζ` on `Re s = 1/4` under RH; heights avoiding the zeros; `Σ 1/‖ρ‖ ≪ log² T` |
| `RHPrimeError/Sharp/Residues.lean` | Residue theorem on a rectangle for finitely many simple poles; the contour identity across the critical line |
| `RHPrimeError/Sharp/Bounds.lean` | Bounds for the left side, the horizontal sides and the sum over zeros |
| `RHPrimeError/Sharp/Main.lean` | The sharp bound for `ψ` |
| `RHPrimeError/Sharp/PrimeCounting.lean` | The sharp bounds for `θ` and `π`, and primes in short intervals |
| `RHPrimeError/Epsilon.lean` | The `x^(1/2+ε)` versions, as corollaries of the sharp bounds |
| `RHPrimeError/Converse.lean` | The error term implies RH; also `riemannHypothesis_of_forall_riemannZeta_ne_zero`: no zeros with `Re s > 1/2` implies RH |
| `RHPrimeError/Equivalence.lean` | The equivalence |

## How it was produced

Everything in this repository was written by Claude (Anthropic) in a Claude Code session directed by the repository owner. Claude chose the proof strategy and split the work; Claude subagents, several of them in parallel, wrote the Lean proofs. The sharp bound was done by a single subagent; a paper version of its proof, with the design choices, is in `RHPrimeError/Sharp/NOTES.md`. All of it was checked by the Lean kernel. **No part of the Lean code has been written or reviewed line by line by a human.**

## Context

This was written on 2026-11-20, the day Levent Alpöge announced a Lean formalization of a proof of RH. That announcement is the motivation: **assuming his proof is correct, the conclusions of these theorems follow**, since his main theorem and our hypothesis are the same Mathlib statement, `RiemannHypothesis`.

Two things should be kept apart:

- **What is proved here** is the equivalence, which has no hypothesis at all, and the implications from RH. None of them imports his code, and all of them remain true whether or not his proof is correct.
- **What we assume, and have not checked,** is the correctness of his proof. We have not built or audited his formalization. Note also that this repository uses a newer Lean and Mathlib than his, so combining the two would require porting one of them. Until his proof is independently confirmed, the conclusions remain conditional.
