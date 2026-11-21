import YangMills.Construction.ParameterData.FirstExitPathDefs
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import YangMills.Construction.Thresholds.DegreeFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
structure BlockExponents where
  blockExp : ℕ
  logPower : ℕ
  two_le_logPower : 2 ≤ logPower
variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryData.TrajectoryParameters T y) (S : BlockExponents)
def blockCubeSize (T : RenormalizationStepParameters.ParameterAssignment) (S : BlockExponents) : ℕ := T.side ^ S.blockExp
def blockSizeAtThreshold (g : ℝ) : ℕ := Thresholds.blockSize T.side S.logPower (D.threshold g)
def referenceTorusExponent (g : ℝ) : ℕ :=
  11 + S.blockExp + Nat.log T.side (blockSizeAtThreshold D S g)
def referenceTorusSide (g : ℝ) : ℝ := PeriodicLattice.torusSide T.side (referenceTorusExponent D S g)
def admissibleSides (g : ℝ) : Set ℝ :=
  {ℓ | ℓ ∈ PeriodicLattice.torusSides T.side ∧ referenceTorusSide D S g ≤ ℓ}
def oneLoopDeviation (T : RenormalizationStepParameters.ParameterAssignment) : ℝ :=
  ⨆ k : ℕ, |∑ l ∈ Finset.range k, FamilyNorms.ParameterAssignment.oneLoop T l -
    (k : ℝ) * CouplingFlow.slopeConst T.side|
def inverseCouplingFloor : ℝ :=
  max D.floorStar (max (2 * D.shift + 2) (max (y + 2 * oneLoopDeviation T + 1) (2 * D.cH + 9)))
def ForAllTrajectoryParameters
    (P : ∀ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ), TrajectoryData.TrajectoryParameters T y → Prop) : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun T y =>
    ∀ D : TrajectoryData.TrajectoryParameters T y, D.Admissible → P T y D
def ForAllTrajectoryCouplings
    (P : ∀ (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ), TrajectoryData.TrajectoryParameters T y → ℝ → Prop) : Prop :=
  ForAllTrajectoryParameters fun T y D =>
    ∀ g : ℝ, 0 < g → inverseCouplingFloor D ≤ g ^ (-2 : ℤ) → P T y D g
end YangMills.Construction.SystemOfAdmissibleConstants
end
