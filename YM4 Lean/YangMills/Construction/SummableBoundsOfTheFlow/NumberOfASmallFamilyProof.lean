import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStepAreFinite
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderAtAbelianFields
import YangMills.Construction.SummableBoundsOfTheFlow.NumberOfASmallFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilyNorms
open YangMills.Construction.TorusLumps
theorem smallFamilyValue_holds (hA : SecondOrderAtAbelianFields)
    (hN : PotentialSumsFinite) : smallFamilyValueStatement := by
  intro ℓ C g hf hC H
  obtain ⟨a1, a2, -, -, -⟩ := hA ℓ hf C g H
  obtain ⟨-, sG, -, -, -, sG0, -⟩ := hN ℓ.rt ℓ.n₁ hf.rt_pos hf.n₁_pos
  have hlim : HasLimitSecondDeriv g := fun c c' X X' => ⟨_, a1 c c' X X'⟩
  have b : ∀ cc, ‖limitFormTerm g unitPlaneCurvature unitPlaneCurvature cc‖ ≤ C * (potentialNorm cc.1 * potentialNorm cc.2 /
      expansionWeight ℓ.rt ℓ.n₁ (bondPairDiam cc.1 cc.2)) := by
    rintro ⟨c, c'⟩
    have := a2 c c' (linearPotential unitPlaneCurvature c) (linearPotential unitPlaneCurvature c')
    rw [Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    show _ * (C / ℓ.weight _) = _
    simp only [potentialNorm]
    have e : ℓ.weight (offsetTriangleDiameter c.1 c'.1) = expansionWeight ℓ.rt ℓ.n₁ (bondPairDiam c c') := rfl
    rw [e]
    ring
  have s := sG.hasSum.mul_left C
  have S : Summable (limitFormTerm g unitPlaneCurvature unitPlaneCurvature) := Summable.of_norm_bounded s.summable b
  have n := tsum_of_norm_bounded s b
  refine ⟨_, ⟨hlim, S.hasSum⟩, ?_⟩
  refine n.trans ?_
  set T := ∑' cc : LatticeBond × LatticeBond, potentialNorm cc.1 * potentialNorm cc.2 /
    expansionWeight ℓ.rt ℓ.n₁ (bondPairDiam cc.1 cc.2) with hT
  have hG : potentialWeightSum ℓ.rt ℓ.n₁ = 2 * T := rfl
  rw [hG]
  have : 0 ≤ T := by
    have := sG0
    rw [hG] at this
    linarith
  nlinarith [mul_nonneg hC this]
end YangMills.Construction.FamilyNorms
end
