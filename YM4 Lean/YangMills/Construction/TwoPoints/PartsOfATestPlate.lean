import YangMills.Construction.TwoPoints.FourShapesAndTheShapeConstant
import YangMills.Construction.TwoPoints.TestPlatesAtAWidthAndTheNumbersOfTheGrowthBound
import Mathlib
open Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints.TestPlates
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
open YangMills.Construction.TwoPoints.Shapes (shapeConst)
structure PlateHypotheses (φ : (Fin 2 → ℝ) → ℂ) (r w k : ℝ) : Prop where
  profile_mem : φ ∈ transProfiles
  exists_ne_zero : ∃ ζ, φ ζ ≠ 0
  radius_pos : 0 < r
  tsupport_subset : tsupport φ ⊆ {ζ | euclidNorm ζ ≤ r}
  width_pos : 0 < w
  width_le_radius : w ≤ r
  dilation_mem : k ∈ Icc (1 : ℝ) 2
def stripRect (w r : ℝ) : Set (Fin 2 → ℝ) :=
  {y | y 0 ∈ Icc (2 * w) (3 * w) ∧ y 1 ∈ Icc (-r) r}
def CellsCoverProfile (φ : (Fin 2 → ℝ) → ℂ) (r w : ℝ) : Prop :=
  (∀ ζ, HasSum (fun i : Fin 2 → ℤ => cellBump w i ζ) 1) ∧
  (∀ (i : Fin 2 → ℤ) (ζ), 0 ≤ cellBump w i ζ ∧ cellBump w i ζ ≤ cellPlateauAt w i ζ) ∧
  (supportCells w φ).Finite ∧
  ((supportCells w φ).ncard : ℝ) ≤ cellCountBound w r ∧
  cellCountBound w r ≤ 25 * r ^ 2 / w ^ 2
def PedestalEstimate (φ : (Fin 2 → ℝ) → ℂ) (w : ℝ) : Prop :=
  0 < plateWidthNorm w φ ∧
  ∀ i ∈ supportCells w φ, ∀ ζ, (upperCellProfile w φ i ζ).im = 0 ∧
    plateWidthNorm w φ * cellPlateauAt w i ζ ≤ (upperCellProfile w φ i ζ).re ∧
    (upperCellProfile w φ i ζ).re ≤ 3 * plateWidthNorm w φ * cellPlateauAt w i ζ
def PlaneBumpProperties (w k : ℝ) : Prop :=
  (∀ y, 0 ≤ planeBumpAt w k y) ∧
  YangMills.Construction.TwoPoints.Shapes.ofRealFun (planeBumpAt w k) ∈
    realCc1In (univ : Set (Fin 2 → ℝ)) ∧
  IsGreatest (range (planeBumpAt w k)) 1 ∧
  tsupport (planeBumpAt w k) ⊆ stripRect w (1 / 4 * k * w) ∧
  stripRect w (1 / 4 * k * w) ⊆ stripRect w (1 / 2 * w)
def IsPlatePiece (w : ℝ) (h : AmbientSpace → ℂ) : Prop :=
  (∀ x, IsRealNonneg (h x)) ∧ h ∈ compactC1Real ∧ tsupport h ⊆ {x | 2 * w ≤ x 3 ∧ x 3 ≤ 3 * w}
def PlateSplitting (φ : (Fin 2 → ℝ) → ℂ) (w k : ℝ) : Prop :=
  widthPlate w k φ ∈ realCc1In {x : AmbientSpace | 0 < x 3} ∧
  widthPlate w k φ =
    ∑ᶠ i ∈ supportCells w φ, (upperCellPlate w k φ i - lowerCellPlate w k φ i) ∧
  ∀ i ∈ supportCells w φ,
    IsPlatePiece w (upperCellPlate w k φ i) ∧ IsPlatePiece w (lowerCellPlate w k φ i) ∧
    TestFunctions.uniformNorm (lowerCellPlate w k φ i) = 2 * plateWidthNorm w φ ∧
    plateWidthNorm w φ ≤ TestFunctions.uniformNorm (upperCellPlate w k φ i) ∧
    TestFunctions.uniformNorm (upperCellPlate w k φ i) ≤ 3 * plateWidthNorm w φ
def ReflectedPairAdmissible (w : ℝ) (h : AmbientSpace → ℂ) : Prop :=
  (∃ p ∈ TestFunctions.separatedPairsR4 (5 / 2 * w) shapeConst,
    YangMills.Construction.TwoPoints.ofRealFun p.1 = reflectFun (coordVec 3) h ∧
    YangMills.Construction.TwoPoints.ofRealFun p.2 = h) ∧
  reflectFun (coordVec 3) h ∈ compactC1Real ∧ h ∈ compactC1Real ∧
  TestFunctions.uniformNorm (reflectFun (coordVec 3) h) = TestFunctions.uniformNorm h
def TestPlatePieces.Statement : Prop :=
  ∀ (φ : (Fin 2 → ℝ) → ℂ) (r w k : ℝ), PlateHypotheses φ r w k →
    CellsCoverProfile φ r w ∧
    PedestalEstimate φ w ∧
    PlaneBumpProperties w k ∧
    PlateSplitting φ w k ∧
    ∀ i ∈ supportCells w φ,
      ReflectedPairAdmissible w (upperCellPlate w k φ i) ∧
      ReflectedPairAdmissible w (lowerCellPlate w k φ i)
end YangMills.Construction.TwoPoints.TestPlates
