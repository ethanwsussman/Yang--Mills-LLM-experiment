import YangMills.Construction.Dirichlet.HolderProductBound
import YangMills.Construction.DirichletOperator.BoundsAtOneCubeProof
import YangMills.Construction.DirichletOperator.ChainOfRemaindersProof
import YangMills.Construction.DirichletOperator.WalkBoundsOnFunctions
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
open YangMills.Construction.Dirichlet.WalkExpansion
noncomputable section
namespace YangMills.Construction.Dirichlet.FunctionWalkBounds
variable {d L : ℕ} {S aMinus aPlus : ℝ}
theorem supNormOn_nonneg {ξ : ℝ} (X : Set (PeriodicTorus d S)) (f : LatticeSite d S ξ → ℝ) :
    0 ≤ supNormOn X f :=
  Real.sSup_nonneg (by rintro r ⟨x, -, rfl⟩; exact abs_nonneg _)
theorem abs_le_supNormOn {ξ : ℝ} [Finite (LatticeSite d S ξ)] {X : Set (PeriodicTorus d S)}
    (f : LatticeSite d S ξ → ℝ) {x : LatticeSite d S ξ}
    (hx : (x : PeriodicTorus d S) ∈ X) : |f x| ≤ supNormOn X f := by apply _root_.YangMills.Construction.Dirichlet.RemainderChains.le_supNormOn <;> assumption
theorem fieldSupNorm_zero {ξ : ℝ} : fieldSupNorm (0 : BondField d S ξ) = 0 := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.fieldSupNorm_zero_eq <;> assumption
structure Hypotheses (𝒮 : BlockSetting d L aMinus aPlus S)
    (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ)) : Prop where
  facts : CentreCellFacts 𝒮
  placement : PartitionOfUnity.CubePlacement 𝒮
  bumps : PartitionOfUnity.BumpProperties 𝒮
  nearCell : PartitionOfUnity.CentresNearCube 𝒮
  support : ∀ Q ∈ 𝒮.coverCubes, Commutator.CubeSupport 𝒮 Q
  rules : 𝒮.IsRuleFamily E
  linear : ∀ Q ∈ 𝒮.coverCubes, GreenLinearity.BlockGreenFacts 𝒮 (𝒮.innerRegion Q) (E Q)
variable {𝒮 : BlockSetting d L aMinus aPlus S} {E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ)}
def cellPiece (𝒮 : BlockSetting d L aMinus aPlus S) (Q : CentredCube d S) (y₀ : PeriodicTorus d S)
    (μ : LatticeSite d S 𝒮.ξ → ℝ) : LatticeSite d S 𝒮.ξ → ℝ :=
  pointwiseMul (𝒮.latticeCutoff Q) (restrictTo (𝒮.cell y₀) μ)
def cellPart (𝒮 : BlockSetting d L aMinus aPlus S)
    (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ)) (Q : CentredCube d S)
    (y₀ : PeriodicTorus d S) (μ : LatticeSite d S 𝒮.ξ → ℝ) :
    LatticeSite d S 𝒮.ξ → ℝ :=
  CubeEstimates.cutoffSolution 𝒮 Q (E Q) (cellPiece 𝒮 Q y₀ μ) 0
end YangMills.Construction.Dirichlet.FunctionWalkBounds
