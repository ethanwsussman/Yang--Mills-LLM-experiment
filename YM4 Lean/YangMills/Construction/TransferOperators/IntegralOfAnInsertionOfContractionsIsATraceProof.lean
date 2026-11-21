import YangMills.Construction.TransferOperators.CycleOfKernelsIsATraceProof
import YangMills.Construction.TransferOperators.CycleOfKernelsIsATrace
import YangMills.Construction.TransferOperators.InsertedOperatorsOfABlockAreContractions
import YangMills.Construction.TransferOperators.IntegralOfAnInsertionOfContractionsIsATrace
import YangMills.Construction.TransferOperators.IntegrandOfAnInsertionIsAProductOfKernels
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.TransferOperators.ExpShiftIntegral
theorem levelClass_succ_bijective (Γ : CubicPeriodSublattice) :
    Function.Bijective fun k : Fin Γ.side => Γ.levelClass ((k : ℕ) + 1) := by apply _root_.YangMills.Construction.TransferOperators.CubicPeriodSublattice.indexLevel_bijective <;> assumption
theorem expShiftIntegralTrace_holds (hCycle : KernelCycleTrace.Statement)
    (hContr : LevelProductOps.ContractionStatement)
    (hIntegrand : ExpShiftIntegrand.ProdStatement) : ExpShiftIntegralTraceStatement := by
  intro β hβ μ B A hA hReal hComm hPos i H hIndex hDisj Γ hΓ
  have hNorm : ∀ k, ‖Γ.levelProductOps B A i H k‖ ≤ 1 := fun k =>
    (hContr μ B A hA i H hDisj Γ hΓ _).2
  obtain ⟨hTrace, -, hIntegral⟩ := hCycle β hβ Γ μ (Γ.levelProductOps B A i H) hNorm
  refine ⟨hTrace, ?_⟩
  rw [← hIntegral, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  have hU := hIntegrand β hβ μ B A hA hReal hComm hPos i H hIndex hDisj Γ hΓ U
  refine hU.trans ?_
  exact ((levelClass_succ_bijective Γ).prod_comp fun j =>
    Complex.exp (-Γ.sliceEnergy β (Γ.sliceField (μ := μ) U j)) *
      sqrtKernelSandwich β (Γ.levelProductOp B A i H j)
        (Γ.sliceField (μ := μ) U j)
        (Γ.orbitGaugeAct (Γ.temporalSliceField (μ := μ) U j)
          (Γ.sliceField (μ := μ) U (j + 1)))).symm
end YangMills.Construction.TransferOperators.ExpShiftIntegral
end
