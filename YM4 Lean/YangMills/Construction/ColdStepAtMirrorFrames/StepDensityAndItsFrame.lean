import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def stepDensityFamily (T : StepParameters) (x : ℝ) (f : LocalFamily) : TopLevelFamily :=
  fun _ Y V => expansionDensity false T.a T.chainParams.ρA T.ballRadius x (frameRadius x) T.p f Y V
def expansionAtFrameFamily (T : StepParameters) (star : Bool) (x : ℝ) (f : LocalFamily) : TopLevelFamily :=
  fun _ Y V => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y 0 V
def HasBoundedFlatLimitForm (L t : ℕ) (g : TopLevelFamily) (e : ℝ) : Prop :=
  ∃ q : BondBilinearForm,
    (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform g L t n b b' X X') Filter.atTop
      (𝓝 (q b b' X X'))) ∧
    ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
      ‖X‖ = 1 → μ < ν →
      IsLinearPotential (constantPlaneCurvature X μ ν) B →
      ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        q e.1 e.2 (B e.1) (B e.2)) v ∧ |v| ≤ e
end YangMills.Construction.ColdStepAtMirrorFrames
end
