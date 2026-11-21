import YangMills.Construction.DirichletOperator.ChainOfRemaindersProof
import YangMills.Construction.DirichletOperator.NormOfTheRemainderProof
import YangMills.Construction.DirichletOperator.RegroupedFactors
import YangMills.Construction.DirichletOperator.RemainderOnABlockProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet YangMills.Construction.WeightedGreen YangMills.Construction.Dirichlet.WalkExpansion
noncomputable section
namespace YangMills.Construction.Dirichlet.DivergenceWalkBounds
section Lists
variable {α ι : Type*}
variable (D : Finset α) (Y : Finset ι) (near : α → ι → Prop)
open Classical in
def pairSum (e : ι → ℝ) (b : List α → ι → ℝ) (Q Q₁ : α) (ω : List α) : ℝ :=
  ∑ y₁ ∈ Y, if near Q y₁ ∧ near Q₁ y₁ then e y₁ * b (Q₁ :: ω) y₁ else 0
end Lists
section Functions
variable {d : ℕ} {S ξ : ℝ}
theorem pointwiseMul_add (h f g : LatticeSite d S ξ → ℝ) :
    pointwiseMul h (f + g) = pointwiseMul h f + pointwiseMul h g := by apply _root_.YangMills.Construction.Dirichlet.RemainderNeumann.pointwiseMul_add <;> assumption
theorem supNormAll_nonneg (f : LatticeSite d S ξ → ℝ) : 0 ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.zero_le_supNormAll <;> assumption
theorem fieldSupNorm_nonneg (F : BondField d S ξ) : 0 ≤ fieldSupNorm F :=
  Real.iSup_nonneg fun _ => supNormAll_nonneg _
theorem scaledHolderSeminorm_nonneg (α : ℝ) {s : ℝ} (hs : 0 < s) (f : LatticeSite d S ξ → ℝ) :
    0 ≤ scaledHolderSeminorm α s f := by apply _root_.YangMills.Construction.Dirichlet.GreenPointwise.scaledHolderSeminorm_nonneg <;> assumption
end Functions
variable {d L : ℕ} {S aMinus aPlus : ℝ}
section Operators
variable (B : BlockSetting d L aMinus aPlus S)
theorem commutatorOp_zero (h : LatticeSite d S B.ξ → ℝ) :
    B.commutatorOp h 0 = 0 := by apply _root_.YangMills.Construction.Dirichlet.LocalRemainderBound.commutatorOp_zero <;> assumption
abbrev halfDecay (y y' : PeriodicTorus d S) : ℝ :=
  WeightedDistance.expDecay B (expDecayRate d L aMinus aPlus / 2) y y'
variable (E : CentredCube d S → Set (LatticeBond d S B.ξ)) (F : BondField d S B.ξ)
def chainSolution (Q : CentredCube d S) (ω : List (CentredCube d S)) : LatticeSite d S B.ξ → ℝ :=
  B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) (remainderChain B E ω (divSource B F)))
def cellPiece (Q : CentredCube d S) (ω : List (CentredCube d S)) (y : PeriodicTorus d S) :
    LatticeSite d S B.ξ → ℝ :=
  restrictTo (B.cell y) (chainSolution B E F Q ω)
end Operators
section Terms
variable {B : BlockSetting d L aMinus aPlus S} {E : CentredCube d S → Set (LatticeBond d S B.ξ)}
  {C : ℝ} {Cα : ℝ → ℝ}
end Terms
section Sums
variable {B : BlockSetting d L aMinus aPlus S} {E : CentredCube d S → Set (LatticeBond d S B.ξ)}
  {C : ℝ} {Cα : ℝ → ℝ}
abbrev stepRatio (B : BlockSetting d L aMinus aPlus S) : ℝ :=
  (cubeOverlap d : ℝ) * (crossConstC d L aMinus aPlus * (B.M : ℝ)⁻¹) *
    sumBound d L aMinus aPlus
end Sums
end YangMills.Construction.Dirichlet.DivergenceWalkBounds
