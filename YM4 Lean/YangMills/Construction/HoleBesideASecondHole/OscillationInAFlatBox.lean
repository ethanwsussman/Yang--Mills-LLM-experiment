import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormula
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.FlatBoxes
open LatticeFractionalIntegration
def boxBetween (lo hi : LatticeFractionalIntegration.Lattice4) : Finset LatticeFractionalIntegration.Lattice4 :=
  Fintype.piFinset fun j => Finset.Icc (lo j) (hi j)
def flatBoxOscillationStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin 4) (n : ℕ) (lo hi : LatticeFractionalIntegration.Lattice4)
    (f : LatticeFractionalIntegration.Lattice4 → ℍ[ℝ]) (w : LatticeFractionalIntegration.Lattice4 → ℝ) (E : ℝ),
    2 ≤ n → lo i = hi i → (∀ j, j ≠ i → (n : ℤ) ≤ hi j - lo j + 1 ∧ hi j - lo j + 1 ≤ 8 * n) →
    0 ≤ E → (∀ x, 0 ≤ w x) →
    (∀ x ∈ boxBetween lo hi, ∀ j, x + basisVector j ∈ boxBetween lo hi → ‖f (x + basisVector j) - f x‖ ≤ w x) →
    ∑ x ∈ boxBetween lo hi, w x ^ 4 ≤ E ^ 4 →
    ∀ x ∈ boxBetween lo hi, ∀ y ∈ boxBetween lo hi, ‖f x - f y‖ ^ 4 ≤ C * n * E ^ 4
end YangMills.Construction.FlatBoxes
end
