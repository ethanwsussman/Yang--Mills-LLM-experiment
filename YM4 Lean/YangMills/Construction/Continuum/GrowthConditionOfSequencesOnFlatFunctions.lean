import YangMills.Construction.Continuum.TestFunctionsOfConfigurationSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
namespace YangMills.Construction.GrowthSequences
open ConfigurationSpace
structure FlatSeq where
  zeroTerm : ℂ → ℂ
  posTerm : (n : ℕ) → 1 ≤ n → flatSchwartzSet n → ℂ
def IsDistribSeq (S : FlatSeq) : Prop :=
  S.zeroTerm = id ∧ ∀ (n : ℕ) (hn : 1 ≤ n), S.posTerm n hn ∈ flatSchwartzDualSet n
def GrowthWith (S : FlatSeq) (s : ℕ) (α β : ℝ) : Prop :=
  IsDistribSeq S ∧ 0 < s ∧ 0 ≤ α ∧ 0 ≤ β ∧
    ∃ c : ℕ → ℝ, (∀ n, 1 ≤ n → 0 ≤ c n) ∧
      (∀ (n : ℕ) (hn : 1 ≤ n) (φ : flatSchwartzSet n),
        ENNReal.ofReal ‖S.posTerm n hn φ‖ ≤ ENNReal.ofReal (c n) * sobolevWeightNorm (n * s) φ.1) ∧
      ∀ n, 1 ≤ n → c n ≤ α * (n.factorial : ℝ) ^ β
end YangMills.Construction.GrowthSequences
