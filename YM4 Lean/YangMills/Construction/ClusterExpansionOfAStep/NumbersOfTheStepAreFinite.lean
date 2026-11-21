import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
def PotentialSumsFinite : Prop :=
  ∀ rt n₁ : ℝ, 0 < rt → 0 < n₁ →
    Summable (fun cc : LatticeBond × LatticeBond => potentialNorm cc.1 * potentialNorm cc.2 *
      Real.exp (-(rt / 2 ^ 6 * bondPairDiam cc.1 cc.2))) ∧
    Summable (fun cc : LatticeBond × LatticeBond => potentialNorm cc.1 * potentialNorm cc.2 /
      expansionWeight rt n₁ (bondPairDiam cc.1 cc.2)) ∧
    BddAbove (Set.range fun m : ℕ => expansionWeight rt n₁ m * Real.exp (-(2 * (rt / 2 ^ 10) * m))) ∧
    (∀ m : ℕ, expansionWeight rt n₁ m * Real.exp (-(2 * (rt / 2 ^ 10) * m)) ≤ weightGrowthSup rt n₁) ∧
    0 ≤ potentialDecaySum rt ∧ 0 ≤ potentialWeightSum rt n₁ ∧ 1 ≤ weightGrowthSup rt n₁
end YangMills.Construction.TorusLumps
end
