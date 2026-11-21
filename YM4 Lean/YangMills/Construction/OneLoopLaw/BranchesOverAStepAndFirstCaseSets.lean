import YangMills.Construction.OneLoopLaw.AveragedBackgroundOfTheAxialCriticalBranch
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.OneLoopLaw
namespace AxialBranchSetting
abbrev atHeight (s : Conventions.StandingParameters) (n : ℕ) (h₁ : 1 ≤ n)
    (h₂ : n ≤ (s.K : ℕ)) : AxialBranchSetting :=
  ⟨s, n, h₁, h₂⟩
end AxialBranchSetting
structure StepBranch (s : Conventions.StandingParameters) (i : ℕ) where
  height : ℕ
  succ_le_height : i + 1 ≤ height
  height_le : height ≤ (s.K : ℕ)
  data : (AxialBranchSetting.atHeight s height (by omega) height_le).AxialLiftSystem
  isAxial : data.IsAxialLiftSystem
namespace StepBranch
variable {s : Conventions.StandingParameters} {i : ℕ} (B : StepBranch s i)
abbrev setting : AxialBranchSetting :=
  AxialBranchSetting.atHeight s B.height (by have := B.succ_le_height; omega) B.height_le
def nhd : Set (B.setting.Edge (i + 1) → Matrices.ComplexMatrix2) := B.data.nhdAt (i + 1)
def lift : (B.setting.Edge (i + 1) → Matrices.ComplexMatrix2) →
    B.setting.Edge i → Matrices.ComplexMatrix2 := B.data.lift i
def comp : (B.setting.Edge (i + 1) → Matrices.ComplexMatrix2) →
    B.setting.Edge 0 → Matrices.ComplexMatrix2 :=
  B.data.comp (i + 1)
structure IsFirstCaseSet (ε : ℝ) (N : Set (B.setting.Edge (i + 1) → Matrices.ComplexMatrix2)) :
    Prop where
  subset_nhd : N ⊆ B.nhd
  unitField_mem : B.setting.unitField (i + 1) ∈ N
  properties : ∀ W ∈ N, B.setting.FibreMinimumProperties i ε W (B.lift W) (B.comp W)
end StepBranch
end YangMills.Construction.OneLoopLaw
end
