import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import YangMills.Construction.Towers.TheFieldsAndTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields
namespace RunningCouplingSlope
open Tower Tower.CriticalBranchResponse
def sinePhase {s : ℕ} (t : ℝ) (x : TorusFields.TorusSite s) : ℝ :=
  Real.sin (t * (centredCoords x 0 : ℝ))
def IsPlaneWavePair (L n k : ℕ) [NeZero (2 * L ^ n)] (t : ℝ)
    (C S : Tower.edgeFormSpace L n k k) : Prop :=
  (C : Tower.Edge L n k k → Matrices.ComplexMatrix2) = planeWaveValues L n k (cosinePhase t) ∧
    (S : Tower.Edge L n k k → Matrices.ComplexMatrix2) = planeWaveValues L n k (sinePhase t)
def normaliserHessianAtResponse (L n k : ℕ) (B : Tower.edgeFormSpace L n k k) : ℝ :=
  Tower.fieldFunctionalSecondDeriv L n k (meshScaledResponse L n k B, 0, 0)
    (meshScaledResponse L n k B, 0, 0)
def freeEnergyHessianAtResponse {L n k : ℕ} (a : ℝ) (B : Tower.edgeFormSpace L n k k) : ℝ :=
  hessianOfFreeEnergy a (backgroundOnlyTriple (meshScaledResponse L n k B))
    (backgroundOnlyTriple (meshScaledResponse L n k B))
end RunningCouplingSlope
end YangMills.Construction
end
