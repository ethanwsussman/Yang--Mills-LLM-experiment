import YangMills.Construction.TransferOperators.IntegralOfAnInsertionOfContractionsIsATraceProof
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsLinearAndReal
import YangMills.Construction.TransferOperators.NormaliserOfACubicTorusIsATrace
import YangMills.Construction.TransferOperators.TorusWeightIsAProductOverLayers
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TransferOperators.CubicPartitionTrace
theorem levelClass_add_one_bijective (Γ : CubicPeriodSublattice) :
    Function.Bijective fun k : Fin Γ.side => Γ.levelClass ((k : ℕ) + 1) := by apply _root_.YangMills.Construction.TransferOperators.ExpShiftIntegral.levelClass_succ_bijective <;> assumption
theorem interleavedProd_const_one {M : Type*} [Monoid M] (s : ℕ) (A : M) :
    interleavedProd (fun _ : Fin s => (1 : M)) A = A ^ s := by
  simp [interleavedProd, List.ofFn_const]
theorem cubicPartitionFunction_eq_trace (hcycle : KernelCycleTrace.Statement)
    (hprod : BoltzmannWeight.ProdSlicesStatement)
    (hlin : SandwichKernelLinearStatement) : CubicPartitionFunctionTraceStatement := by
  intro β hβ μ Γ
  obtain ⟨htr, -, hval⟩ := hcycle β hβ Γ μ (fun _ => 1) fun _ => ContinuousLinearMap.norm_id_le
  rw [interleavedProd_const_one] at htr hval
  refine ⟨htr, ?_⟩
  rw [← hval, InfiniteLattice.PeriodSublattice.partitionFunction, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  change ((Γ.lattice.boltzmannWeight β U : ℝ) : ℂ) = Γ.kernelCycle μ β (fun _ => 1) U
  rw [hprod β hβ μ Γ U, CubicPeriodSublattice.kernelCycle]
  refine (Function.Bijective.prod_comp (levelClass_add_one_bijective Γ) _).symm.trans ?_
  refine Finset.prod_congr rfl fun k _ => ?_
  obtain ⟨ν, hν⟩ := exists_ne μ
  have : Nonempty (Γ.LinkOrbits μ) := ⟨Γ.linkClass (SliceLink.ofAxis 0 ν hν)⟩
  rw [(hlin β hβ _).2.1]
end YangMills.Construction.TransferOperators.CubicPartitionTrace
end
