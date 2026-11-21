import YangMills.Construction.InfiniteLattice.PeriodicMeasuresHaveCubicPeriodsAtEverySpacing
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.InfiniteLattice
theorem periodicMeasuresCubicInvarianceAllSpacings_holds :
    PeriodicMeasuresCubicInvarianceAllSpacings := by
  intro a β ha _
  have lagrange : ∀ Q : AddSubgroup (LatticePoint a), Q.FiniteIndex →
      ∀ v : LatticePoint a, Q.index • v ∈ Q :=
    fun Q _ v => Q.nsmul_index_mem v
  refine ⟨lagrange, fun ν hν => ?_⟩
  simp only [periodicGibbsClass, Set.mem_iUnion] at hν
  obtain ⟨Q, hQ, hν⟩ := hν
  exact ⟨Q.index, Nat.one_le_iff_ne_zero.mpr hQ.index_ne_zero,
    fun v => hν.2 _ (lagrange Q hQ v)⟩
end YangMills.Construction.InfiniteLattice
