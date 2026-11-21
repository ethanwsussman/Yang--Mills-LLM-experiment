import YangMills.Construction.DirichletOperator.SourcesOfTheAdjointDefectOfACube
import YangMills.Construction.DirichletOperator.TermsOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RegionSequence RegionSequence.NestedRegions PartitionCubes RemainderEstimates
open CubeAdjointDefect (cellWeightedSum)
open CubeOperators (cutoffSize cubeDivOne)
namespace CubeGreenSources
variable {R : NestedRegions} {M : ℕ}
def greenOfSources (Q : LevelCube R M) (w : Q.system.setting.Tensor 1)
    (f : Q.system.setting.FineBond → ℝ) : R.FineBond → ℝ :=
  Q.system.pushBonds Q.partitionFn (Q.system.inv (cubeDivOne Q w + f))
variable (R M) in
def SupBound (L : ℕ) (B : ℝ) : Prop :=
  ∀ y : R.allCentres, ∀ Q ∈ active R M, (Q.supp ∩ doubledCube (y : R.Point)).Nonempty →
    ∀ w : Q.system.setting.Tensor 1, ∀ f ∈ Q.system.forms,
      supBond (cellCutBond (y : R.Point) (greenOfSources Q w f)) ≤ B * cellWeightedSum L Q y w f
def minBlock (L : ℕ) : ℝ :=
  max ((L : ℝ) ^ 5) ((L : ℝ) * (CubeTorus.chosenConstants L).minBlock)
end CubeGreenSources
end YangMills.Construction
