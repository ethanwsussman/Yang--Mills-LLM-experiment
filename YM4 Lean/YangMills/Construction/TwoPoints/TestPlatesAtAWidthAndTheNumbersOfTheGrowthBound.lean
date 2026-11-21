import YangMills.Construction.TwoPoints.SmoothedIndicatorsAndTheThreeShapes
import Mathlib
open MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints.TestPlates
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Splines (cubicSpline cubicSplineIntegral)
open YangMills.Construction.TwoPoints.Shapes (timeBump planePartitionOfUnity planePlateau)
def plateWidthNorm (w : ℝ) (φ : (Fin 2 → ℝ) → ℂ) : ℝ :=
  YangMills.Construction.TestFunctions.uniformNorm φ + w * YangMills.Construction.TwoPoints.gradPlaneSup φ
def planeBumpAt (w κ : ℝ) (y : Fin 2 → ℝ) : ℝ :=
  timeBump (y 0 / w) * cubicSpline (4 * y 1 / (κ * w))
def widthPlate (w κ : ℝ) (φ : (Fin 2 → ℝ) → ℂ) : AmbientSpace → ℂ :=
  YangMills.Construction.TwoPoints.tensorPlate (Shapes.ofRealFun (planeBumpAt w κ)) φ
def timeLaplace (w E : ℝ) : ℝ := ∫ t : ℝ, timeBump (t / w) * Real.exp (-(t * E))
def scaledSplineFourier (w κ q : ℝ) : ℂ :=
  ∫ s : ℝ, (cubicSpline (4 * s / (κ * w)) : ℂ) * Complex.exp (Complex.I * (s : ℂ) * (q : ℂ))
def scaledFrequency (w κ q : ℝ) : ℝ := κ * w * q / 16
def cellBump (w : ℝ) (j : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) : ℝ :=
  planePartitionOfUnity fun i => ζ i / w - (j i : ℝ)
def cellPlateauAt (w : ℝ) (j : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) : ℝ :=
  planePlateau fun i => ζ i / w - (j i : ℝ)
def localizedProfile (w : ℝ) (φ : (Fin 2 → ℝ) → ℂ) (j : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) : ℂ :=
  (cellBump w j ζ : ℂ) * φ ζ
def supportCells (w : ℝ) (φ : (Fin 2 → ℝ) → ℂ) : Set (Fin 2 → ℤ) :=
  {j | ∃ ζ, localizedProfile w φ j ζ ≠ 0}
def cellCountBound (w r : ℝ) : ℝ := (2 * r / w + 3) ^ 2
def basePedestal (w : ℝ) (φ : (Fin 2 → ℝ) → ℂ) (j : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) : ℂ :=
  ((2 * plateWidthNorm w φ * cellPlateauAt w j ζ : ℝ) : ℂ)
def lowerCellProfile (w : ℝ) (φ : (Fin 2 → ℝ) → ℂ) (j : Fin 2 → ℤ) : (Fin 2 → ℝ) → ℂ :=
  basePedestal w φ j
def upperCellProfile (w : ℝ) (φ : (Fin 2 → ℝ) → ℂ) (j : Fin 2 → ℤ) : (Fin 2 → ℝ) → ℂ :=
  fun ζ => basePedestal w φ j ζ + localizedProfile w φ j ζ
def lowerCellPlate (w κ : ℝ) (φ : (Fin 2 → ℝ) → ℂ) (j : Fin 2 → ℤ) : AmbientSpace → ℂ :=
  YangMills.Construction.TwoPoints.tensorPlate (Shapes.ofRealFun (planeBumpAt w κ)) (lowerCellProfile w φ j)
def upperCellPlate (w κ : ℝ) (φ : (Fin 2 → ℝ) → ℂ) (j : Fin 2 → ℤ) : AmbientSpace → ℂ :=
  YangMills.Construction.TwoPoints.tensorPlate (Shapes.ofRealFun (planeBumpAt w κ)) (upperCellProfile w φ j)
def spacingConst : ℝ := 8
def sineWindowConst : ℝ := 1 / 10
def sineLossConst : ℝ :=
  2 * sineWindowConst * (16 / spacingConst + 1 / Real.pi +
    32 * sineWindowConst / (Real.pi * spacingConst))
def sineLowerConst : ℝ := (1 - sineLossConst) * Real.sin sineWindowConst ^ 8
def averageLowerConst : ℝ :=
  1 / 16 * cubicSplineIntegral ^ 2 * min (Real.sin 1 ^ 8) (8 ^ 8 * sineLowerConst)
def weightSupConst : ℝ := sSup ((fun x : ℝ => Real.exp (-x) * (1 + x ^ 2) ^ 4) '' Ici 0)
def plateConst : ℝ := 4 * weightSupConst / averageLowerConst
def growthConst : ℝ := 36 * 625 * plateConst
def decayGrowthConst : ℝ := 7 ^ 8 * growthConst
end YangMills.Construction.TwoPoints.TestPlates
