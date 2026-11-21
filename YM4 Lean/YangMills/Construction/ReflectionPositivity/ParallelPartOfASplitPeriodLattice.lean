import YangMills.Construction.ReflectionPositivity.PeriodLatticesSplitForANormal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodSublattice
def transversePart (Γ : PeriodSublattice 1) (n : AmbientSpace) (z : ℤ) : AddSubgroup AmbientSpace :=
  Classical.epsilon (Γ.IsTransverseComplement n z)
theorem isTransverseComplement_transversePart {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ}
    (h : Γ.SplitsAlongWithHalfPeriod n z) :
    Γ.IsTransverseComplement n z (Γ.transversePart n z) :=
  Classical.epsilon_spec h.2.2
end YangMills.Construction.InfiniteLattice.PeriodSublattice
end
