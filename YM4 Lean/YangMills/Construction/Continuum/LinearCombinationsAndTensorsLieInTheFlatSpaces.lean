import YangMills.Construction.Continuum.SchwingerFunctionsOfAFunctionalOnSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace
def FlatSpaceClosure : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ (c c' : ℂ) (φ ψ : schwartzFlatOffDiagonal n),
      ∃ χ : schwartzFlatOffDiagonal n, χ.1 = c • φ.1 + c' • ψ.1) ∧
    ∀ X : SepFamilyOfLength n, AllSmoothCompact X.1 →
      tensorRealFamily X.1 ∈ schwartzFlatOffDiagonal n
end ConfigSpace
end YangMills.Construction
end
