import YangMills.Construction.InfiniteLattice.CoveringOfTheLatticeOfACutoff
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.CutoffLinks
namespace CutoffData
variable (d : CutoffData)
def restrictToPositiveLinks (U : d.PeriodicFields) : GroupFamily d.positiveLinkSet :=
  fun l => U.linkValue l.1
def faceAction (P : d.PeriodicPlaquette) (U : d.PeriodicFields) : ℝ :=
  PeriodicLattice.plaquetteCost U.1 P
abbrev periodicPartitionFunction : ℝ :=
  PeriodicLattice.partitionFunction d.L (d.m : ℕ) (d.K : ℕ) d.coupling
end CutoffData
def PeriodicFieldsAtPositiveLinks : Prop :=
  ∀ d : CutoffData,
    (Finite d.PeriodicSite ∧ Finite d.PeriodicBond ∧ Finite d.PeriodicPlaquette ∧
      (∀ l : d.PeriodicBond, Xor (l ∈ d.positiveLinkSet) (∃ l' ∈ d.positiveLinkSet, l = l'.opposite)) ∧
      Function.Bijective d.restrictToPositiveLinks) ∧
    ((∀ P : d.PeriodicPlaquette,
        Continuous (d.faceAction P) ∧
        (∀ U : d.PeriodicFields, d.faceAction P U ∈ Icc (0 : ℝ) 2) ∧
        ∀ U U' : d.PeriodicFields,
          (∀ l : d.PeriodicBond, CutoffData.FaceContains P l → U.linkValue l = U'.linkValue l) →
            d.faceAction P U = d.faceAction P U') ∧
      0 < d.periodicPartitionFunction ∧ d.periodicPartitionFunction ≤ 1)
end YangMills.Construction.CutoffLinks
