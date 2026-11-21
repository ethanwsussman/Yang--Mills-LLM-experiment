import YangMills.Construction.LatticeFields.SubsetWeightConjRules
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.WeightConjRules
variable {d : ℕ} {κ : LatticeShape d}
section Multiplication
variable {M : ℕ} {I : Type}
theorem latticeSpacing_nonneg (M : ℕ) : 0 ≤ latticeSpacing M := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.latticeSpacing_nonneg <;> assumption
theorem fieldInner_mulBase (f : LatticeSite M κ → ℝ) (F G : LatticeField M κ I) :
    fieldInner (mulBase f F) G = fieldInner F (mulBase f G) := by
  unfold fieldInner
  refine tsum_congr fun p => ?_
  simp only [mulBase]
  ring
end Multiplication
section Weight
variable {N : ℕ} [NeZero N] {I J : Type}
def atScale (f : LatticeSite N κ → ℝ) :
    (s : LatticeScale) → LatticeSite (s.invSpacing N) κ → ℝ
  | .fine => f
  | .unit => restrictUnitSites f
theorem weightMul_eq_mulBase (f : LatticeSite N κ → ℝ) (s : LatticeScale)
    (F : LatticeField (s.invSpacing N) κ I) : weightMul f s F = mulBase (atScale f s) F := by
  cases s <;> rfl
theorem fieldInner_weightMul (f : LatticeSite N κ → ℝ) (s : LatticeScale)
    (F G : LatticeField (s.invSpacing N) κ I) :
    fieldInner (weightMul f s F) G = fieldInner F (weightMul f s G) := by
  simp only [weightMul_eq_mulBase]
  exact fieldInner_mulBase _ F G
end Weight
section Distance
variable {M : ℕ}
end Distance
end YangMills.Construction.LatticeFields.WeightConjRules
