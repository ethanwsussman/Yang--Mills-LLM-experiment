import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import YangMills.Construction.TotalDensitiesGiveASystem.ConditionsOfTheMainStatement
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TopAux
def referenceFlow (a ρ lam : ℝ) (L : ℕ) (β : ℝ) : ℕ → ℝ :=
  CouplingFlow.flow (ReferenceDensity.oneLoopCoefficient a ρ lam L)
    (ScaledVariables.secondStepCoefficient a ρ lam L) β
def ReferenceFlowBound (ℓ : TorusLumps.StepParameters) (Bs a ρ lam Cr g : ℝ) : Prop :=
  ∀ (K : ℕ) (β : ℝ), TotalDensitySystem.IsFirstPassageDatum ℓ Bs g K β →
    (∀ k ≤ K, 0 < referenceFlow a ρ lam ℓ.side β k) ∧
    (∀ k ≤ K, |TotalDensityFlow.coupling ℓ β k - referenceFlow a ρ lam ℓ.side β k| ≤
      2 * Cr * TotalDensityFlow.coupling ℓ β k ^ (-(1 / 4) : ℝ)) ∧
    |TotalDensityFlow.coupling ℓ β K - referenceFlow a ρ lam ℓ.side β K| ≤ 2 * Cr * g ^ (1 / 2 : ℝ)
namespace TopWithFlowBound
def Statement : Prop :=
  ∃ J Lstar : ℕ, 1 ≤ J ∧ ∀ L : ℕ, Odd L → Lstar ≤ L →
    ∃ (ℓ : TorusLumps.StepParameters) (Bs c₅ γ : ℝ) (Nw : ℕ) (CT : ℝ)
      (T : RenormalizationStepParameters.ParameterAssignment) (y c M Cr : ℝ),
    ℓ.side = L ∧ ℓ.baseDepth = J ∧ TotalDensitySystem.IsUnitMeshStepParameters ℓ ∧ 2 ≤ Bs ∧ 0 ≤ c₅ ∧
      γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < CT ∧ 1 ≤ Nw ∧
      T.Admissible ∧ T.stepParameters y = ℓ ∧ 0 ≤ Cr ∧
      CouplingFlow.HasAverageSlope (ReferenceDensity.oneLoopCoefficient T.coupling T.ρA T.lam T.side)
        (CouplingFlow.slopeConst L) c ∧
      (∀ t, |ScaledVariables.secondStepCoefficient T.coupling T.ρA T.lam T.side t| ≤ M) ∧
      ∀ g ∈ Ioc 0 γ,
        TotalDensitySystem.CouplingConditions ℓ Bs c₅ (3 / 4 * TotalDensitySystem.oneLoopShift L) Nw CT g ∧
          ReferenceFlowBound ℓ Bs T.coupling T.ρA T.lam Cr g
end TopWithFlowBound
end YangMills.Construction.TopAux
end
