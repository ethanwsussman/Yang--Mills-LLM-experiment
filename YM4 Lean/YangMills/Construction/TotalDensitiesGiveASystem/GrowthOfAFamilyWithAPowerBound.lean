import YangMills.Construction.Continuum.GrowthConditionFromAPowerBoundOnSeparatedTuples
import YangMills.Construction.LimitTheorem.ConditionsAtGivenConstants
import YangMills.Construction.SystemsWithFiveBounds.TheoremOverASystemWithFiveBounds
import YangMills.Construction.TotalDensitiesGiveASystem.WhatALimitAlongToriHas
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensities
def GrowthOfPowerBoundedFamily : Prop :=
  ∀ (C : ℝ) (S : LimitTheorem.CumulantFamily), 0 ≤ C → LimitProperties S →
    SeparatedPowerBound.PowerSepBound 1 5 C 6 S →
    (∃ T, LimitTheorem.HasSchwingerSequence (LimitTheorem.centredOf S) T ∧
      LimitTheorem.SatisfiesGrowth T 15 (2 * SeparatedBound.extFactorAbs) (SeparatedPowerBound.powerBase 1 5 C) 26) ∧
    SystemsWithFiveBounds.DistributionalExtension S
end YangMills.Construction.TotalDensities
end
