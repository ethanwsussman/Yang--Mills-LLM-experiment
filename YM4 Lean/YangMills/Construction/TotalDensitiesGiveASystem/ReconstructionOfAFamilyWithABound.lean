import YangMills.Construction.LimitTheorem.ConditionsAtGivenConstants
import YangMills.Construction.TotalDensitiesGiveASystem.WhatALimitAlongToriHas
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def HasBallSupportBound (c : ℕ → ℝ → ℝ → ℝ) (S : LimitTheorem.CumulantFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (R d : ℝ), 0 < R → 0 < d → ∀ X : TestSpaces.SepTupleOfCard n,
    (∀ i, ∃ x, tsupport (X.1 i) ⊆ TestFunctions.closedBallR4 x R) →
    (∀ i l, i ≠ l → ENNReal.ofReal d ≤ TestFunctions.setDistR4 (tsupport (X.1 i)) (tsupport (X.1 l))) →
      |S n hn X| ≤ c n d R * ∏ i, TestFunctions.sharpNormR4 1 (X.1 i)
def reconstructionOfBoundedFamily : Prop :=
  ∀ (c : ℕ → ℝ → ℝ → ℝ) (S : LimitTheorem.CumulantFamily),
    (∀ n, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ c n d R) →
    LimitProperties S → HasBallSupportBound c S →
    (LimitTheorem.centredOf S).IsEntrywiseLinear ∧ (LimitTheorem.centredOf S).IsAdmissiblyContinuous ∧
      LimitTheorem.ReconstructionProperties (LimitTheorem.centredOf S)
end YangMills.Construction.TotalDensities
end
