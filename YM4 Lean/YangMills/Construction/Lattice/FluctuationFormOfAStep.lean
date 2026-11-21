import YangMills.Construction.OneLoopLaw.AveragedBackgroundOfTheAxialCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace CubesOfStep
open Set YangMills.Construction.ParameterChoice
variable (c : ChoiceUpToDegreeConstants) (m K k : ℕ)
def HasAxialBranchSetting : Prop :=
  Conventions.IsAdmissibleBlockingFactor c.L ∧ 0 < K ∧ 0 < m ∧ k < K
variable {c m K k}
def axialBranchSetting (h : HasAxialBranchSetting c m K k) : OneLoopLaw.AxialBranchSetting where
  params := ⟨c.L, h.1, ⟨K, h.2.1⟩, ⟨m, h.2.2.1⟩⟩
  level := k + 1
  one_le_level := Nat.succ_le_succ (Nat.zero_le k)
  level_le_cutoff := h.2.2.2
variable (c m K k)
def branchMap :
    (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) →
      BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  open Classical in
  if h : HasAxialBranchSetting c m K k then (axialBranchSetting h).branchLift k
  else fun _ _ => 1
def backgroundNhd : Set (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) :=
  open Classical in
  if h : HasAxialBranchSetting c m K k then
    (axialBranchSetting h).backgroundNhd k c.εv
  else ∅
variable {m K k} (D : StepData c.L m K k)
def basePoint : BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  backgroundPoint c D (backgroundNhd c m K k) (branchMap c m K k)
def IsHessianStep : Prop :=
  k < K ∧ HasBackgroundPoint c D (backgroundNhd c m K k) ∧
    HasUniqueCriticalOrbit (Averaging.smoothingRadius c.L) c.εv K k D.domains
      (activeBondSet K k D.domains) (fieldDatum c D (basePoint c D))
def stepNormalizer : ℝ :=
  gaussianNormalizer c D (basePoint c D)
end CubesOfStep
end YangMills.Construction.PeriodicLattice
