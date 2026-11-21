import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfSpins
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames StepCosts StepGas StepSettings RenormalizationStepParameters TorusFields TorusLumps
def GroundCasesAreFamilies : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      (∀ Γ, G.IsPairwiseFarApart Γ → G.familyBadBonds Γ ⊆ markedBonds R G.cut) ∧
      (∀ Γ Γ', G.IsPairwiseFarApart Γ → G.IsPairwiseFarApart Γ' → G.familyBadBonds Γ = G.familyBadBonds Γ' →
        G.familySites Γ = G.familySites Γ' → Γ = Γ') ∧
      (∀ Γ A, G.IsPairwiseFarApart Γ →
        (G.CaseAvoids A (G.familyBadBonds Γ) (G.familySites Γ) ↔ ∀ i ∈ Γ, ¬ i.1.Touches A)) ∧
      ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
        (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω),
        bad ⊆ markedBonds R G.cut →
        IsHullState R.params R.range (G.state.fieldWithStoredLinks W) Yt →
        coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state →
        ∃ Γ, G.IsPairwiseFarApart Γ ∧ bad = G.familyBadBonds Γ ∧ Yt = G.familySites Γ
end YangMills.Construction.ClusterExpansionOfAStep
end
