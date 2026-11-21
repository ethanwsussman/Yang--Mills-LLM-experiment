import YangMills.Construction.DirichletOperator.BoundsOnTheToriOfTheCubes
import YangMills.Construction.DirichletOperator.CellsOfACube
import YangMills.Construction.RegionSequence.BlockOperatorNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RegionSequence RegionSequence.NestedRegions PartitionCubes
open CubeTorus (torusSetting levelSpacing chosenConstants)
namespace CubeCommutator
variable {𝒮 : NestedRegions} {M : ℕ}
def longCommutator (Q : LevelCube 𝒮 M) (v : (torusSetting Q).FineBond → ℝ) :
    (torusSetting Q).FineBond → ℝ :=
  Q.torusLongOp (Q.system.mulTransfer Q.partitionFn v) -
    Q.system.mulTransfer Q.partitionFn (Q.torusLongOp v)
def CellRestrictedNormLE (Q : LevelCube 𝒮 M) (p : NormExponent) (w w' : (torusSetting Q).Point)
    (a : ℝ) : Prop :=
  ∀ v ∈ Q.system.forms,
    (formCutSpace (torusSetting Q)).pNorm p
        (Q.restrictBondsToCell w (longCommutator Q (Q.restrictBondsToCell w' v))) ≤
      a * (formCutSpace (torusSetting Q)).pNorm p v
def CommutatorBound (L : ℕ) (C : ℝ) (Q : LevelCube 𝒮 M) : Prop :=
  ∀ w ∈ Q.cellPoints, ∀ w' ∈ Q.cellPoints, ∀ p : NormExponent,
    CellRestrictedNormLE Q p w w'
      (C * (M : ℝ)⁻¹ * (levelSpacing Q ^ 2)⁻¹ * (1 + Q.torusDist w w') *
        (chosenConstants L).expDecay Q w w')
def CommutatorClaim : Prop :=
  ∀ L : ℕ, Odd L → 13 ≤ L → ∃ C : ℝ,
    ∀ (K m M R₁ : ℕ) (𝒮 : NestedRegions), 𝒮.L = L → 𝒮.IsLevelUnitChain K m M R₁ →
      max ((L : ℝ) ^ 5) ((L : ℝ) * (chosenConstants L).minBlock) ≤ (M : ℝ) →
      ∀ Q : LevelCube 𝒮 M, Q.IsFirstType → CommutatorBound L C Q
end CubeCommutator
end YangMills.Construction
