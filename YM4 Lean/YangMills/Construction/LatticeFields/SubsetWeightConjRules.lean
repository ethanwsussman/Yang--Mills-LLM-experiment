import YangMills.Construction.LatticeFields.BlockMomentInverseProof
import YangMills.Construction.LatticeFields.WeightConjRules
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
namespace SubsetWeightConjugation
variable {d N : ℕ} {κ : LatticeShape d}
theorem weightMul_exp_weightMul_exp_neg [NeZero N] (θ : LatticeSite N κ → ℝ) (s : LatticeScale)
    {I : Type} (F : LatticeField (s.invSpacing N) κ I) :
    weightMul (fun x => Real.exp (θ x)) s (weightMul (fun x => Real.exp (-θ x)) s F) = F := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.weightMul_exp_exp_neg <;> assumption
theorem fieldInner_weightMul [NeZero N] (g : LatticeSite N κ → ℝ) (s : LatticeScale) {I : Type}
    (F G : LatticeField (s.invSpacing N) κ I) :
    fieldInner (weightMul g s F) G = fieldInner F (weightMul g s G) := by
  unfold fieldInner
  congr 1
  funext p
  cases s <;> simp only [weightMul, mulBase] <;> ring
end SubsetWeightConjugation
end YangMills.Construction.LatticeFields
