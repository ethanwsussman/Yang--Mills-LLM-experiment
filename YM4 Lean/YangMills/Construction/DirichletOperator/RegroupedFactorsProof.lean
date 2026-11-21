import YangMills.Construction.DirichletOperator.ChainOfRemaindersProof
import YangMills.Construction.Dirichlet.CommutatorBoundsProof
import YangMills.Construction.Dirichlet.CommutatorIdentity
import YangMills.Construction.Dirichlet.GreenBoundsOnRegionsProof
import YangMills.Construction.DirichletOperator.RegroupedFactors
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Dirichlet.RegroupedFactors
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
open YangMills.Construction.Dirichlet.WalkExpansion
section Lengths
variable {d : ℕ} {S : ℝ}
theorem supNorm_sub_comm (p q : PeriodicTorus d S) : supNorm (p - q) = supNorm (q - p) := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_sub_comm <;> assumption
theorem supNorm_sub_le (p q r : PeriodicTorus d S) :
    supNorm (p - r) ≤ supNorm (p - q) + supNorm (q - r) := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_sub_le_add <;> assumption
theorem supNorm_sub_le_of_isNeighbor {ξ : ℝ} (hξ : 0 < ξ) {x x' : LatticeSite d S ξ}
    (h : IsNeighbor x x') : supNorm ((x' : PeriodicTorus d S) - (x : PeriodicTorus d S)) ≤ ξ := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_sub_le_of_isNeighbor <;> assumption
end Lengths
section Functions
variable {d : ℕ} {S ξ : ℝ}
theorem restrictTo_of_mem {X : Set (PeriodicTorus d S)} (f : LatticeSite d S ξ → ℝ)
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∈ X) : restrictTo X f x = f x :=
  Set.indicator_of_mem (s := {x : LatticeSite d S ξ | (x : PeriodicTorus d S) ∈ X}) hx f
theorem restrictTo_of_not_mem {X : Set (PeriodicTorus d S)} (f : LatticeSite d S ξ → ℝ)
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∉ X) : restrictTo X f x = 0 := by apply _root_.YangMills.Construction.Dirichlet.RemainderChains.restrictTo_of_not_mem <;> assumption
theorem supNormAll_nonneg (f : LatticeSite d S ξ → ℝ) : 0 ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.zero_le_supNormAll <;> assumption
theorem abs_le_supNormAll [Finite (LatticeSite d S ξ)] (f : LatticeSite d S ξ → ℝ)
    (x : LatticeSite d S ξ) : |f x| ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.abs_le_supNormAll <;> assumption
theorem fieldSupNorm_nonneg (F : BondField d S ξ) : 0 ≤ fieldSupNorm F :=
  Real.iSup_nonneg fun _ => supNormAll_nonneg _
end Functions
variable {d L : ℕ} {S aMinus aPlus : ℝ}
structure SettingFacts (B : BlockSetting d L aMinus aPlus S) : Prop where
  params : Parameters d L aMinus aPlus
  cells : CentreCellFacts B
  consequences : ThresholdConsequences.Conclusions B
  placement : PartitionOfUnity.CubePlacement B
  bumps : PartitionOfUnity.BumpProperties B
  diffBounds : PartitionOfUnity.CutoffDiffBounds B (PartitionOfUnity.partitionConst d)
  nearCube : PartitionOfUnity.CentresNearCube B
  calculus : ∀ (f h ψ : LatticeSite d S B.ξ → ℝ) (F : BondField d S B.ξ)
    (x : LatticeSite d S B.ξ), LatticeCalculus.BlockIdentities f h ψ F x
  lengths : LengthAxioms d S
  formula : Commutator.CommutatorFormula B
  divForm : ∀ Q ∈ B.coverCubes, CommutatorDivForm B (B.latticeCutoff Q)
  greenLinear : ∀ (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S B.ξ)), B.IsCellUnion W →
    IsBoundaryRule (B.Ω 0) W E → GreenLinearity.BlockGreenFacts B W E
section Geometry
variable {B : BlockSetting d L aMinus aPlus S}
theorem SettingFacts.ξ_pos (_ : SettingFacts B) : 0 < B.ξ := B.isSeparatedChain.scale_pos
theorem SettingFacts.one_le_blockFactor (D : SettingFacts B) : (1 : ℝ) ≤ (L : ℝ) := by
  have := D.params.three_le_blockFactor
  exact_mod_cast (by omega : 1 ≤ L)
theorem SettingFacts.one_le_M (D : SettingFacts B) : (1 : ℝ) ≤ (B.M : ℝ) := by
  have h := D.consequences.blockSize_floor
  have hL := D.params.three_le_blockFactor
  have : 1 ≤ B.M := by nlinarith
  exact_mod_cast this
theorem SettingFacts.partitionConst_nonneg (D : SettingFacts B) :
    0 ≤ PartitionOfUnity.partitionConst d :=
  D.consequences.partitionConst_nonneg
theorem centreOf_spec (D : SettingFacts B) {x : LatticeSite d S B.ξ}
    (hx : (x : PeriodicTorus d S) ∈ B.Ω 0) :
    B.centreOf x ∈ B.centres ∧ (x : PeriodicTorus d S) ∈ B.cell (B.centreOf x) := by
  obtain ⟨y, hy, -⟩ := D.cells.existsUnique_cell x hx
  exact Classical.epsilon_spec
    (p := fun y => y ∈ B.centres ∧ (x : PeriodicTorus d S) ∈ B.cell y) ⟨y, hy⟩
theorem centreOf_eq (D : SettingFacts B) {y : PeriodicTorus d S} (hy : y ∈ B.centres)
    {x : LatticeSite d S B.ξ} (hx : (x : PeriodicTorus d S) ∈ B.cell y) : B.centreOf x = y := by
  have hx0 := D.cells.cell_subset y hy hx
  exact (D.cells.existsUnique_cell x hx0).unique (centreOf_spec D hx0) ⟨hy, hx⟩
theorem supNorm_sub_le_of_mem_cell {y : PeriodicTorus d S} {p : PeriodicTorus d S}
    (hp : p ∈ B.cell y) : supNorm (p - y) ≤ B.centreSpacing y / 2 := hp
theorem supSetDist_singleton_le {p q : PeriodicTorus d S} {X : Set (PeriodicTorus d S)}
    (hq : q ∈ X) {r : ℝ} (h : supNorm (p - q) ≤ r) : supSetDist {p} X ≤ ENNReal.ofReal r :=
  calc supSetDist {p} X ≤ ENNReal.ofReal (supNorm (p - q)) :=
        iInf₂_le_of_le p rfl (iInf₂_le_of_le q hq le_rfl)
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal h
theorem supNorm_sub_self (D : SettingFacts B) (p : PeriodicTorus d S) : supNorm (p - p) = 0 := by
  rw [sub_self]
  exact D.lengths.supNorm_zero
theorem mem_baseNbhd (D : SettingFacts B) {p : PeriodicTorus d S} (hp : p ∈ B.Ω 0) :
    p ∈ B.baseNbhd :=
  supSetDist_singleton_le hp (by rw [supNorm_sub_self D]; linarith [D.ξ_pos])
def cutoffSlope (B : BlockSetting d L aMinus aPlus S) (y : PeriodicTorus d S) : ℝ :=
  PartitionOfUnity.partitionConst d * (L : ℝ) ^ 2 / ((B.M : ℝ) * B.centreSpacing y)
theorem cutoffSlope_nonneg (D : SettingFacts B) (y : PeriodicTorus d S) : 0 ≤ cutoffSlope B y := by
  have := D.partitionConst_nonneg
  have := D.cells.centreSpacing_pos y
  have := D.one_le_M
  unfold cutoffSlope
  positivity
end Geometry
section Regroup
variable {B : BlockSetting d L aMinus aPlus S}
end Regroup
section Factors
variable {B : BlockSetting d L aMinus aPlus S}
theorem abs_finsum_mem_le_ncard_mul {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ)
    (bound : ℝ) (h : ∀ x ∈ s, |f x| ≤ bound) : |∑ᶠ x ∈ s, f x| ≤ (s.ncard : ℝ) * bound := by apply _root_.YangMills.Construction.Dirichlet.Commutator.abs_finsum_mem_le_ncard_mul <;> assumption
def remainderBound (B : BlockSetting d L aMinus aPlus S) (y : PeriodicTorus d S)
    (ψ : LatticeSite d S B.ξ → ℝ) : ℝ :=
  (PartitionOfUnity.partitionConst d * (L : ℝ) ^ 4 / ((B.M : ℝ) * B.centreSpacing y) ^ 2 +
    aPlus * (d : ℝ) * PartitionOfUnity.partitionConst d * (L : ℝ) ^ 2 /
      ((B.M : ℝ) * B.centreSpacing y ^ 2)) * supNormAll ψ
theorem upper_pos (D : SettingFacts B) : 0 < aPlus :=
  lt_of_lt_of_le D.params.lower_pos D.params.lower_le_upper
def finalConst (d L : ℕ) : ℝ :=
  (d : ℝ) * PartitionOfUnity.partitionConst d * (L : ℝ) ^ 4 + 1
end Factors
end YangMills.Construction.Dirichlet.RegroupedFactors
