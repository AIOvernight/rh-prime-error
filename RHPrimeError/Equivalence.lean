import RHPrimeError.Epsilon
import RHPrimeError.Converse

/-!
# The Riemann Hypothesis is equivalent to a square-root error term for `ψ`

We combine `chebyshev_psi_sub_isBigO_of_riemannHypothesis` (the Riemann Hypothesis implies
`ψ(x) - x = O(x ^ (1 / 2 + ε))` for every `ε > 0`) with its converse
`riemannHypothesis_of_chebyshev_psi_sub_isBigO` into a single equivalence.

## Main results

* `riemannHypothesis_iff_chebyshev_psi_sub_isBigO`: the Riemann Hypothesis holds if and only if
  `ψ(x) - x = O(x ^ (1 / 2 + ε))` for every `ε > 0`.
-/

/-- **The Riemann Hypothesis is equivalent to the square-root error term in the prime number
theorem**: `RiemannHypothesis` holds if and only if `ψ(x) - x = O(x ^ (1 / 2 + ε))` for every
`ε > 0`, where `ψ` is the Chebyshev function. -/
theorem riemannHypothesis_iff_chebyshev_psi_sub_isBigO :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε) :=
  ⟨chebyshev_psi_sub_isBigO_of_riemannHypothesis, riemannHypothesis_of_chebyshev_psi_sub_isBigO⟩
