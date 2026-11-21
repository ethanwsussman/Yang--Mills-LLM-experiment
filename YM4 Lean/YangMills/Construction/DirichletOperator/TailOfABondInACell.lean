import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.SourceInCell
def Statement : Prop :=
  ∀ (S : RegionSequence.NestedRegions) (K m M R₁ : ℕ), S.IsLevelUnitChain K m M R₁ →
    ∀ b ∈ S.bonds, ∀ y ∈ S.allCentres, AnchoredIn (S.cellOf y) b →
      (b.source : S.Point) ∈ doubledSiteCube S.L S.ξ S.Ω y
end YangMills.Construction.PartitionCubes.SourceInCell
