import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.AdjointTermsAsOperatorsOnFormsProof
import YangMills.Construction.DirichletOperator.BlockNormCalculus
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.CubeTorusComparison YangMills.Construction.BlockCalculus
open YangMills.Construction.RegionSequence.CellStructure (IsSelfAdjointOn)
noncomputable section
namespace YangMills.Construction.PartitionCubes.LongChange
section Exponents
variable {ι ι' : Type} [Finite ι] [Finite ι']
variable {D : Set ι} {D' : Set ι'}
end Exponents
section Pairings
theorem bondInner_comm {𝒯 : NestedRegions} (f g : 𝒯.FineBond → ℝ) :
    bondInner f g = bondInner g f := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
variable {𝒯 : NestedRegions} [Finite 𝒯.FineBond]
theorem bondInner_add_left (f g k : 𝒯.FineBond → ℝ) :
    bondInner (f + g) k = bondInner f k + bondInner g k := by apply _root_.YangMills.Construction.RegionSequence.Positivity.bondInner_add_left <;> assumption
theorem bondInner_sub_left (f g k : 𝒯.FineBond → ℝ) :
    bondInner (f - g) k = bondInner f k - bondInner g k := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.bondInner_sub_left <;> assumption
theorem eq_zero_of_bondInner_self (d : 𝒯.FineBond → ℝ) (h : bondInner d d = 0) : d = 0 := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.eq_zero_of_bondInner_self <;> assumption
end Pairings
section Transfers
variable {𝒮 : NestedRegions} {M : ℕ}
structure FirstTypeData (Q : LevelCube 𝒮 M) : Prop where
  transfers : Q.TransfersToTorus
  partitionTransfers : Q.PartitionTransfers
  abs_partitionFn_le : ∀ x, |Q.partitionFn x| ≤ 1
  abs_smallCutoff_le : ∀ x, |Q.smallCutoff x| ≤ 1
  supp_subset : Q.supp ⊆ Q.thicken (1 / 3)
  mem_of_smallCutoff_ne : ∀ x, Q.smallCutoff x ≠ 0 → x ∈ Q.thicken (1 / 3)
  thicken_third_subset : Q.thicken (1 / 3) ⊆ Q.thicken (5 / 6)
  thicken_subset_strictPts : Q.thicken (5 / 6) ⊆ Q.strictPts
variable {Q : LevelCube 𝒮 M}
end Transfers
section Bounds
variable {𝒮 : NestedRegions} {M : ℕ} {Q : LevelCube 𝒮 M}
theorem abs_le_supBond {𝒯 : NestedRegions} [Finite 𝒯.FineBond] (f : 𝒯.FineBond → ℝ)
    (b : 𝒯.FineBond) : |f b| ≤ supBond f :=
  le_ciSup (f := fun b => ‖f b‖) (Set.finite_range _).bddAbove b
theorem supBond_nonneg {𝒯 : NestedRegions} (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem supBond_le {𝒯 : NestedRegions} {f : 𝒯.FineBond → ℝ} {a : ℝ} (h : ∀ b, |f b| ≤ a)
    (ha : 0 ≤ a) : supBond f ≤ a :=
  Real.iSup_le h ha
end Bounds
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
end YangMills.Construction.PartitionCubes.LongChange
