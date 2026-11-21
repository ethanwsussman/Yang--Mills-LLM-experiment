import YangMills.Construction.Towers.PeriodicExtensionOfAConfigurationIsAConfiguration
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels
theorem liftGaugeField_isGaugeField (hProj : Tower.EdgeProjectionProperties) : LiftIsGaugeField := by
  intro L n k j hL hn hj U
  have key : ∀ 𝒢 : Set Matrices.ComplexMatrix2, PeriodicLattice.IsGaugeField 𝒢 univ U →
      Tower.FullSpace.IsFieldIn 𝒢 (liftGaugeField L n k j U) := by
    intro 𝒢 hU
    refine ⟨fun b => hU.1 _ (mem_univ _), fun b => ?_⟩
    have hopp := ((hProj L n k j hL hn hj).1 b).2.2.2
    show U (Tower.FullSpace.projEdge L n k j b.opposite) =
      (U (Tower.FullSpace.projEdge L n k j b))⁻¹
    rw [← hopp]
    exact hU.2 _ (mem_univ _)
  exact ⟨key _, key _⟩
end YangMills.Construction.LocalKernels
end
