import YangMills.Construction.Continuum.NormsOfASchwartzFunction
import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def TensorAcrossZeroTime : Prop :=
  ∀ p p' : ℕ, 1 ≤ p → 1 ≤ p' →
    ∀ (k : ℕ) (f : SchwartzFn p) (g : SchwartzFn p'),
      (∃ hfg : IsSchwartz (tensorFn f.1 g.1),
        bracketNorm k ⟨tensorFn f.1 g.1, hfg⟩ ≤ bracketNorm k f * bracketNorm k g) ∧
      (f.1 ∈ schwartzFlatOffNegTime p → g.1 ∈ schwartzFlatOffPosTime p' →
        tensorFn f.1 g.1 ∈ schwartzFlatOffDiagonal (p + p')) ∧
      (f.1 ∈ schwartzFlatOffPosTime p → g.1 ∈ schwartzFlatOffPosTime p' →
        tensorFn (flipConj f.1) g.1 ∈ schwartzFlatOffDiagonal (p + p'))
end YangMills.Construction.ConfigSpace
end
