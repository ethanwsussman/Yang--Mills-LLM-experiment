import YangMills.Construction.DirichletOperator.ScaledCoordinatesOfTheBareLattice
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.BareDilation
def AveragedFormReadsCentered : Prop :=
  ∀ (L j N : ℕ) (𝒯 : NestedRegions) (S : YangMills.Construction.PeriodicLattice.Scales 4 L j N)
    (r : ℝ) (R : DilationData 𝒯 S r), TwoLayered 𝒯 j → ∀ A : 𝒯.FineBond → ℝ,
      bondInner A (avgOp A) =
        centeredAvgPart S R.coarseTrace r ((L : ℝ) * r) 1 (R.pullBond A)
end YangMills.Construction.BareDilation
