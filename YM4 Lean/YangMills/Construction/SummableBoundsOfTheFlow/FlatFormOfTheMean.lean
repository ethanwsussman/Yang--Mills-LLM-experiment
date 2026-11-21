import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.MeanInTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SummableBounds
open BlockAverages ColdStepAtMirrorFrames
def MeanHessianAtUniform (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (φ h : LocalFamily) (ε : ℝ) (mirror : Bool), T.coupling ≤ x → 0 < ε →
    FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E (T.E / T.η₃) φ →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h →
    ∃ q : BondBilinearForm,
      (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform
        (Estimates.conditionalExpansionMean mirror T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h)
        T.L t n b b' X X') Filter.atTop (nhds (q b b' X X'))) ∧
      ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
        ‖X‖ = 1 → μ < ν → IsLinearPotential (constantPlaneCurvature X μ ν) B →
        ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
          q e.1 e.2 (B e.1) (B e.2)) v ∧ |v| ≤ T.CE * ε * x ^ (-(1 / 2 : ℝ))
def meanHessianAtUniformStatement : Prop := EventuallyInParameters MeanHessianAtUniform
end YangMills.Construction.SummableBounds
end
