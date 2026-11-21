import YangMills.Construction.LawInAState.MeanOnATorusByThePeriodGroup
import YangMills.Construction.LawInAState.TheArrayOfTwoCellsOnTheLeastTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.LawInAState
theorem twoCellPeriodicMean_of_torusMean (hM : LawInAState.TorusMeanViaPeriods.Statement) :
    LawInAState.twoCellPeriodicMeanStatement := by
  intro D g hq H hH hC
  obtain ⟨hZ, hF⟩ := hM D g hq 0
  have hZc : ((ReflectedCopies.torusPartition g (ReflectedCopies.minimalCounts D) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hZ.ne'
  rw [div_eq_iff hZc]
  exact (hF H ⟨hH, hC⟩).symm
end YangMills.Construction.LawInAState
end
