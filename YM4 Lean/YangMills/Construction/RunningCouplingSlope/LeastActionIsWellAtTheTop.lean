import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.RunningCouplingSlope.ActionsNearTheFlatField
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames
def MinimizerNearTrivialInChart (a : ℝ) (F : BlockFrame) [Fintype (F.Site F.top)] : Prop :=
  ∃ x : (F.Site F.top → Fin 4 → ℍ[ℝ]) → StepVariable (finiteCells F),
    AnalyticAt ℝ x (quaternionsOfField (trivialBlockField F F.top)) ∧
    x (quaternionsOfField (trivialBlockField F F.top)) = 0 ∧
    ∀ᶠ Y in 𝓝 (quaternionsOfField (trivialBlockField F F.top)),
      (∀ W', blockEnergy a (finiteCells F) F.depth
          (chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y)) (fieldOfQuaternions Y) ≤
        blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y)) ∧
      (∀ W', (∀ W'', blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y) ≤
          blockEnergy a (finiteCells F) F.depth W'' (fieldOfQuaternions Y)) →
        ∃ γ : F.Site F.depth → UnitQuaternion, (∀ z, γ (cellCentre F.depth z) = 1) ∧
          W' = gaugeTransform γ (chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y))) ∧
      AnalyticAt ℝ (fun η : StepVariable (finiteCells F) =>
        chartedEnergy a (stepCoordinates η) (fieldOfQuaternions Y)) (x Y) ∧
      ∀ v : StepVariable (finiteCells F), v ≠ 0 →
        0 < fderiv ℝ (fderiv ℝ fun η : StepVariable (finiteCells F) =>
          chartedEnergy a (stepCoordinates η) (fieldOfQuaternions Y)) (x Y) v v
def minimalActionNondegeneratePropagatesStatement : Prop :=
  ∀ (F : BlockFrame) [Fintype (F.Site F.depth)] [Fintype (F.Site F.top)] (a : ℝ), 0 < a →
    Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
    IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth) →
    IsNondegenerateAtTrivial (F := F) (k := F.top) (minimalAction a (finiteCells F) F.top) ∧
      MinimizerNearTrivialInChart a F
end YangMills.Construction.RunningCouplingSlope
end
