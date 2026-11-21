import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.GreenOperatorOfACubeOnADivergenceOfACellProof
import YangMills.Construction.DirichletOperator.NormBoundsOfACubeTermOfADivergence
import YangMills.Construction.DirichletOperator.FactsOfTheCellsOfACube
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.ApproxInverseScales
open YangMills.Construction.EnlargedCubeBounds (EnlargedKernelBounds)
open YangMills.Construction.CubeOperators (chosenConstants cubeDivOne cubeDivTwo)
open YangMills.Construction.CubeTorus (levelSpacing TensorAnchorSupported)
noncomputable section
namespace YangMills.Construction.CubeTermDivergence.Estimates
theorem finite_fineBond (hl : YangMills.Construction.Torus.TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
section InnerProduct
variable {𝒯 : NestedRegions}
theorem bondInner_comm (A B : 𝒯.FineBond → ℝ) : bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem bondInner_add [Finite 𝒯.FineBond] (A B g : 𝒯.FineBond → ℝ) :
    bondInner (A + B) g = bondInner A g + bondInner B g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.bondInner_add_left <;> assumption
theorem fwdDiff_add (ν : Fin 4) (A B : 𝒯.FineBond → ℝ) :
    fwdDiff ν (A + B) = fwdDiff ν A + fwdDiff ν B := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.fwdDiff_add <;> assumption
theorem fwdDiff_smul (ν : Fin 4) (c : ℝ) (A : 𝒯.FineBond → ℝ) :
    fwdDiff ν (c • A) = c • fwdDiff ν A := by apply _root_.YangMills.Construction.CubeTermBounds.fwdDiff_smul_fun <;> assumption
end InnerProduct
section Norms
variable {𝒯 : NestedRegions}
theorem supSite_nonneg (f : 𝒯.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem ltwoTensor_nonneg {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ ltwoTensor J := by apply _root_.YangMills.Construction.CornerGreen.ltwoTensor_nonneg' <;> assumption
theorem ltwoBond_zero : ltwoBond (0 : 𝒯.FineBond → ℝ) = 0 := by
  simp [ltwoBond, bondL2, bondInner]
theorem ltwoTensor_zero {r : ℕ} : ltwoTensor (0 : 𝒯.Tensor r) = 0 := by
  simp [ltwoTensor, tensorL2, tensorInner, bondInner]
theorem nablaOne_add_smul (A B : 𝒯.FineBond → ℝ) (c : ℝ) :
    nablaOne (A + c • B) = nablaOne A + c • nablaOne B := by apply _root_.YangMills.Construction.CubeGreenDivergence.nablaOne_add_smul <;> assumption
theorem cubeHalfSide_mono (o : 𝒯.Point) {a b : ℝ} (h : a ≤ b) :
    cubeHalfSide o a ⊆ cubeHalfSide o b := by apply _root_.YangMills.Construction.CubeTermBounds.cubeHalfSide_mono <;> assumption
theorem anchoredIn_mono {X Y : Set 𝒯.Point} (h : X ⊆ Y) {b : 𝒯.FineBond} (hb : AnchoredIn X b) :
    AnchoredIn Y b := h hb
theorem tensorAnchorSupported_mono {X Y : Set 𝒯.Point} (h : X ⊆ Y) {J : 𝒯.Tensor 1}
    (hJ : TensorAnchorSupported X J) : TensorAnchorSupported Y J :=
  fun ν b hb => hJ ν b fun h' => hb (anchoredIn_mono h h')
end Norms
theorem scale_pos (𝒯 : NestedRegions) (n : ℕ) : 0 < 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem levelScale_pos (𝒯 : NestedRegions) (y : 𝒯.Point) : 0 < 𝒯.levelScale y := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.levelScale_pos <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
end YangMills.Construction.CubeTermDivergence.Estimates
