import YangMills.Construction.MirrorGridsOfEverySide.SimilarityOfTheLatticesAndItsProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
def ScalingMapTheorem : Prop :=
  ∀ (D : GridSetup) (S : ScalingMap D),
    (0 < ((D.K : ℕ) : ℤ) - (S.power : ℤ) ∧ S.scale * PeriodicLattice.torusSide D.L D.m ∈ D.sideSet ∧
      ((S.image.K : ℕ) : ℤ) = ((D.K : ℕ) : ℤ) - (S.power : ℤ) ∧
      PeriodicLattice.torusSide S.image.L S.image.m = S.scale * PeriodicLattice.torusSide D.L D.m) ∧
    S.PreservesGridPoints ∧ S.PreservesTorus ∧ S.PreservesMeasures ∧
    S.PreservesReflectionGrids
end YangMills.Construction.MirrorGridsAllSides
end
