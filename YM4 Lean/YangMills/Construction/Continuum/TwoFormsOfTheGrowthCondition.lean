import YangMills.Construction.Continuum.ConjLinearSeminormInnerForm
import YangMills.Construction.Continuum.GrowthConditionOfSequencesOnFlatFunctions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
namespace YangMills.Construction.GrowthForms
def GeomBound (S : GrowthSequences.FlatSeq) (k : ℕ) (c C κ : ℝ) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (φ : ConfigurationSpace.flatSchwartzSet n),
    ENNReal.ofReal ‖S.posTerm n hn φ‖ ≤
      ENNReal.ofReal (c * C ^ n * (n.factorial : ℝ) ^ κ) *
        ConfigurationSpace.sobolevWeightNorm (k * n) φ.1
def GrowthFormsEquiv : Prop :=
  (∀ C : ℝ, 0 ≤ C → ∀ n : ℕ, 1 ≤ n →
    C ^ n ≤ max 1 C * (n.factorial : ℝ) ^ Continuum.binaryLog (max 1 C)) ∧
  ∀ S : GrowthSequences.FlatSeq, GrowthSequences.IsDistribSeq S →
    (∀ (k : ℕ) (c C κ : ℝ), 0 < k → 0 ≤ c → 0 ≤ C → 0 ≤ κ → GeomBound S k c C κ →
      GrowthSequences.GrowthWith S k (c * max 1 C) (κ + Continuum.binaryLog (max 1 C))) ∧
    (∀ (s : ℕ) (α β : ℝ), GrowthSequences.GrowthWith S s α β → GeomBound S s α 1 β)
end YangMills.Construction.GrowthForms
