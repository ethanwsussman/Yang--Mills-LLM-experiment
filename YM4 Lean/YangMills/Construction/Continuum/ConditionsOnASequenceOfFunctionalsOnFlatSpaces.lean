import YangMills.Construction.Continuum.SchwingerFunctionsOfAFunctionalOnSeparatedTuples
import Mathlib
set_option autoImplicit false
open ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace
def IsLinearFunctionalSeq (S : FlatSequence) : Prop :=
  (∀ c : flatOffDiagonalAt 0, S 0 c = c.1) ∧
    ∀ k : ℕ, IsComplexLinearOnFlat (S.atSucc k)
def IsContinuousSeq (S : FlatSequence) : Prop :=
  ∀ k : ℕ, IsContLinearOnFlat (S.atSucc k)
def IsReflectionReal (S : FlatSequence) : Prop :=
  ∀ (k : ℕ) (φ : schwartzFlatOffDiagonal (k + 1))
    (hφ : flipConj φ.1 ∈ schwartzFlatOffDiagonal (k + 1)),
    S.atSucc k ⟨_, hφ⟩ = conj (S.atSucc k φ)
end ConfigSpace
end YangMills.Construction
end
