import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace BlockAverages
def minimalChainExistenceStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell), 0 ≤ a →
    (∀ (j : ℕ) (A : F.GaugeField j) (A' : F.GaugeField (j + 1)) e, 0 ≤ blockFit A A' e) ∧
    (∀ (j : ℕ) (A : F.GaugeField j), 0 ≤ minimalAction a S j A) ∧
    (∀ (j : ℕ) (V : F.GaugeField (j + 1)), ∃ W : F.GaugeField j,
      blockEnergy a S j W V = minimalAction a S (j + 1) V ∧ ∀ W', blockEnergy a S j W V ≤ blockEnergy a S j W' V) ∧
    ∀ V : F.GaugeField F.top, ∃ A : F.FieldChain, IsMinimalChain a S V A ∧
      chainAction a S A = minimalAction a S F.top V
end BlockAverages
end YangMills.Construction
end
