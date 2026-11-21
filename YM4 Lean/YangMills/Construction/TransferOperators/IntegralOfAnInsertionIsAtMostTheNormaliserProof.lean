import YangMills.Construction.TransferOperators.FactsOfTheOperatorsOfACubicTorus
import YangMills.Construction.TransferOperators.InsertedOperatorsOfABlockAreContractions
import YangMills.Construction.TransferOperators.IntegralOfAnInsertionIsAtMostTheNormaliser
import YangMills.Construction.TransferOperators.IntegralOfAnInsertionOfContractionsIsATrace
import YangMills.Construction.TransferOperators.NormaliserOfACubicTorusIsATrace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators.ExpShiftIntegral
theorem bound_holds (trace : ExpShiftIntegralTraceStatement)
    (partition : CubicPartitionFunctionTraceStatement)
    (contractions : LevelProductOps.ContractionStatement)
    (inequality : ContractionTraceBound.Statement)
    (facts : CubicTorusOperators.Statement) : BoundStatement := by
  intro β hβ μ B Ξ hΞ hreal hgauge hpos i Q' hQ' hdisjoint Γ hΓ
  refine ⟨?_, rfl⟩
  obtain ⟨-, hI⟩ := trace β hβ μ B Ξ hΞ hreal hgauge hpos i Q' hQ' hdisjoint Γ hΓ
  obtain ⟨-, hZ⟩ := partition β hβ μ Γ
  obtain ⟨-, -, -, hL⟩ := (facts β hβ).1 Γ μ
  obtain ⟨ρ, hρ⟩ := exists_ne μ
  have : Nonempty (Γ.LinkOrbits μ) := ⟨Γ.linkClass (SliceLink.ofAxis 0 ρ hρ)⟩
  obtain ⟨-, -, -, -, hle, -⟩ := (inequality Γ.side Γ.one_le_side).2 (Γ.LinkOrbits μ)
    (Γ.transfer μ β) (Γ.levelProductOps B Ξ i Q') hL.transfer_nonneg
    hL.entry_summable fun k => (contractions μ B Ξ hΞ i Q' hdisjoint Γ hΓ _).2
  rw [← hI, ← hZ, Complex.norm_real, Complex.ofReal_re] at hle
  exact (le_abs_self _).trans hle
end YangMills.Construction.TransferOperators.ExpShiftIntegral
end
