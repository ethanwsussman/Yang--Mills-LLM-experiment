import YangMills.Construction.InfiniteLattice.KernelsOfFiniteSetsOfBonds
import YangMills.Construction.InfiniteLattice.PeriodGroupsAndCumulantsInAState
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.GibbsAtFixedSpacing
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def gibbsKernelUnit (β : ℝ) (W : Finset (Link (1 : ℝ)))
    (hW : HasNoOppositePairs (W : Set (Link (1 : ℝ))))
    (F : GaugeField (1 : ℝ) → ℂ) (U : GaugeField (1 : ℝ)) : ℂ :=
  wilsonLinkKernel β W hW F U
def periodicGibbsAtMesh (a β : ℝ) : Set (Measure (GaugeField a)) :=
  {ν | IsGibbs β ν ∧ IsPeriodicMeasure ν}
def periodicGibbsUnit (β : ℝ) : Set (Measure (GaugeField (1 : ℝ))) :=
  periodicGibbsAtMesh 1 β
theorem mem_periodicGibbsUnit_iff (β : ℝ) (ν : Measure (GaugeField (1 : ℝ))) :
    ν ∈ periodicGibbsUnit β ↔
      IsGibbs β ν ∧ ∃ P : AddSubgroup (LatticePoint (1 : ℝ)), IsPeriodSubgroup ν P :=
  Iff.rfl
end YangMills.Construction.InfiniteLattice
