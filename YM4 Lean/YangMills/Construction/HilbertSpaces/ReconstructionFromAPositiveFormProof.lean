import YangMills.Construction.HilbertSpaces.EnergyDominatesMomentumOnTheCompletion
import YangMills.Construction.HilbertSpaces.EnergyMomentumMeasureOfACommutingRepresentation
import YangMills.Construction.HilbertSpaces.FormAndItsCompletion
import YangMills.Construction.HilbertSpaces.GeneratorOfASemigroupOfPositiveContractions
import YangMills.Construction.HilbertSpaces.KernelOfTheHamiltonianUnderClustering
import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveForm
import YangMills.Construction.HilbertSpaces.RotationInvarianceOfTheEnergyMomentumSupport
import YangMills.Construction.HilbertSpaces.SemigroupOnTheCompletion
import YangMills.Construction.HilbertSpaces.UnitaryOperatorsOnTheCompletion
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PositiveFormReconstruction
theorem reconstructionStatement_of_parts (h₁ : QuotientCompletion.Statement)
    (h₂ : SemigroupOnCompletion.TransferSemigroupSpec)
    (h₃ : UnitaryOpsOnCompletion.UnitaryActionSpec)
    (h₄ : PositiveContractionGenerator.Statement)
    (h₅ : CommutingJointSpectrum.Statement)
    (h₆ : RotationInvariantSupport.Statement)
    (h₇ : CompletionEnergyBound.Statement)
    (h₈ : ClusteringVacuumKernel.Statement) : ReconstructionStatement := by
  intro V _ _ S hS
  obtain ⟨ha, hb, hc, hd⟩ := h₁ V S hS
  refine ⟨ha, hb, hc, fun H _ _ _ j hj => ?_⟩
  obtain ⟨s₁, s₂, s₃, s₄⟩ := h₂ V S hS H j hj
  obtain ⟨u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉, u₁₀⟩ := h₃ V S hS H j hj
  obtain ⟨g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩ := h₄ H _ s₂ s₃
  obtain ⟨e₀, p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉⟩ := h₅ H _ _ _ s₂ g₃ g₄ u₂ u₄
  have hrot := fun w => h₆ H _ _ _ (rotationOp S hS.hermitian.toIsSesquilinear j w) w s₂ g₃ g₄
    u₂ u₄ (u₈ w) (u₉ w)
  refine ⟨hd H j hj, ?_, ?_, ?_, h₇ V S hS H j hj, h₈ V S hS H j hj⟩
  · exact ⟨s₁, s₂, s₃, s₄, g₁, g₂, g₃, g₄, g₅ _ (s₄ 1), g₆, g₇⟩
  · exact ⟨u₁, u₂, u₃, u₄, e₀, p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉⟩
  · exact ⟨u₅, u₆, u₇, u₈, fun w => (hrot w).1, u₁₀, fun w => (hrot w).2⟩
end YangMills.Construction.PositiveFormReconstruction
