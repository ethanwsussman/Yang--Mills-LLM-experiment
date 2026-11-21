import YangMills.Construction.Continuum.SystemsModesAndScaledNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FrequencySum
def FrequencySumBound : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Q : ConfigSpace.PointSystem n) (C : ℝ) (f : Q.freqLattice → ℝ),
    (∀ ξ : Q.freqLattice,
      ‖f ξ‖ ≤ C * (1 + Q.scale * ConfigSpace.coordSupNorm (ξ : ConfigSpace.Config n)) ^
        (-(4 * (n : ℤ)) - 1)) →
    Summable (fun ξ : Q.freqLattice => ‖f ξ‖) ∧ ∑' ξ : Q.freqLattice, ‖f ξ‖ ≤ C * (1 + 8 * (n : ℝ))
end YangMills.Construction.FrequencySum
