import YangMills.Construction.LatticeFields.CompressedGreenDecayProof
import YangMills.Construction.LatticeFields.SubsetWeightConjRules
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
namespace TorusConj
variable {d N : ℕ} {κ : LatticeShape d}
theorem fieldInner_weightMul [NeZero N] (g : LatticeSite N κ → ℝ) (s : LatticeScale) {I : Type}
    (F G : LatticeField (s.invSpacing N) κ I) :
    fieldInner (weightMul g s F) G = fieldInner F (weightMul g s G) := by apply _root_.YangMills.Construction.LatticeFields.SubsetWeightConjugation.fieldInner_weightMul <;> assumption
end TorusConj
end YangMills.Construction.LatticeFields
