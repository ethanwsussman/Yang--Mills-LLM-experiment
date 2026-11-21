import YangMills.Construction.ParameterData.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
structure IsFirstPassage {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y) (g β : ℝ) (K : ℕ) : Prop where
  isFirstPassageIndex : SequencePassage.IsFirstPassageIndex D.shift g (D.coupling β) K
  hasExpansion : ∀ k ≤ K, TorusLumps.HasExpansion (T.stepParameters y) k (D.coupling β k)
    (TorusLumps.couplingFlow (T.stepParameters y) β k).2
  coupling_gt : ∀ k ≤ K, g ^ (-2 : ℤ) < D.coupling β k
  lower_bound : (β - g ^ (-2 : ℤ)) / D.shift - 1 ≤ K
  upper_bound : (K : ℝ) ≤ 1 + (β - g ^ (-2 : ℤ) - D.shift + D.c₅) / D.lam
  lengthScale_ge : SequencePassage.lowerWindowCoupling D.shift g ≤ lengthScale (D.coupling β K)
  lengthScale_lt : lengthScale (D.coupling β K) < g
def FirstPassageExistsAt {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y) : Prop :=
  ∀ g : ℝ, 0 < g → D.floorStar ≤ g ^ (-2 : ℤ) →
    ∀ β : ℝ, D.threshold g ≤ β → ∃ K : ℕ, IsFirstPassage D g β K
def firstPassageExistsStatement : Prop :=
  ∀ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (D : TrajectoryParameters T y), D.Admissible → FirstPassageExistsAt D
end YangMills.Construction.TrajectoryData
end
