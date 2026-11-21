import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import YangMills.Construction.FreeKernel.KernelsAndAbbreviationsInFourDimensions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.HeatKernelGreen
open MeasureTheory YangMills.Construction.FourDimKernel YangMills.Construction.Constants.HeatKernel
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
open YangMills.Construction.PeriodicLattice.VectorClasses
open scoped ComplexOrder
abbrev castVec (x : Fin 4 → ℤ) : Fin 4 → ℝ := fun i => (x i : ℝ)
def PeriodicSummation (L : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s →
    (∀ x : Fin 4 → ℤ, 0 < latticeHeatKernel4 s x) ∧
    HasSum (latticeHeatKernel4 s) 1 ∧
    (∀ p : Fin 4 → ℝ,
      HasSum
        (fun x : Fin 4 → ℤ =>
          latticeHeatKernel4 s x * Complex.exp (-(Complex.I * (wavePairing p x : ℝ))))
        ((Real.exp (-s * laplacianSymbol p) : ℝ) : ℂ)) ∧
    ∀ x : Fin 4 → ℤ,
      HasSum (fun w : Fin 4 → ℤ => latticeHeatKernel4 s (x + (L : ℤ) • w)) (torusHeatKernel L s x)
def TorusTimeIntegrals (L : ℕ) (μ μ' : Fin 4) : Prop :=
  ∀ x : Fin 4 → ℤ,
    (IntegrableOn (fun s : ℝ => torusHeatKernel L s x - (L : ℂ) ^ (-4 : ℤ)) (Set.Ioi 0) ∧
      greenOnVectors L x = ∫ s in Set.Ioi (0 : ℝ), (torusHeatKernel L s x - (L : ℂ) ^ (-4 : ℤ))) ∧
    (IntegrableOn (fun s : ℝ => mixedSecondDiff μ μ' (torusHeatKernel L s) x) (Set.Ioi 0) ∧
      mixedSecondDiff μ μ' (greenOnVectors L) x =
        ∫ s in Set.Ioi (0 : ℝ), mixedSecondDiff μ μ' (torusHeatKernel L s) x)
def ContinuumTimeIntegrals (μ μ' : Fin 4) : Prop :=
  ∀ y : Fin 4 → ℝ, y ≠ 0 →
    (IntegrableOn (fun s : ℝ => gaussianHeatKernel4 s y) (Set.Ioi 0) ∧
      ∫ s in Set.Ioi (0 : ℝ), gaussianHeatKernel4 s y = continuumGreenFunction y) ∧
    (IntegrableOn (fun s : ℝ => mixedSecondPartial μ μ' (gaussianHeatKernel4 s) y) (Set.Ioi 0) ∧
      ∫ s in Set.Ioi (0 : ℝ), mixedSecondPartial μ μ' (gaussianHeatKernel4 s) y =
        mixedSecondPartial μ μ' continuumGreenFunction y)
def ShortTimeBounds (d : ℕ) (μ μ' : Fin 4) : Prop :=
  ∀ (x : Fin 4 → ℤ) (s : ℝ), 0 < s → s ≤ 1 →
    ‖mixedSecondDiff μ μ' (latticeHeatKernel4 s) x‖ ≤
        (gaussianComparison d).toReal * bracketOnePlus (intVecNorm x) ^ (-(d : ℤ)) ∧
      (x ≠ 0 →
        |mixedSecondPartial μ μ' (gaussianHeatKernel4 s) (castVec x)| ≤
          (gaussianComparison d).toReal * bracketOnePlus (intVecNorm x) ^ (-(d : ℤ)))
def LongTimeBounds (d : ℕ) (μ μ' : Fin 4) : Prop :=
  ∀ (x : Fin 4 → ℤ) (s : ℝ), 1 ≤ s →
    ‖mixedSecondDiff μ μ' (latticeHeatKernel4 s) x‖ ≤
        (gaussianComparison d).toReal * s ^ (-3 : ℤ) *
          ∏ i, bracketOnePlus (|(x i : ℝ)| / Real.sqrt s) ^ (-(d : ℤ)) ∧
      (gaussianComparison d).toReal * s ^ (-3 : ℤ) *
          ∏ i, bracketOnePlus (|(x i : ℝ)| / Real.sqrt s) ^ (-(d : ℤ)) ≤
        (gaussianComparison d).toReal * s ^ (-3 : ℤ) *
          bracketOnePlus (intVecNorm x / (2 * Real.sqrt s)) ^ (-(d : ℤ)) ∧
      ‖mixedSecondDiff μ μ' (latticeHeatKernel4 s) x -
          ((mixedSecondPartial μ μ' (gaussianHeatKernel4 s) (castVec x) : ℝ) : ℂ)‖ ≤
        (gaussianComparison d).toReal * s ^ (-(7 / 2) : ℝ) *
          bracketOnePlus (intVecNorm x / (2 * Real.sqrt s)) ^ (-(d : ℤ))
def NearDiagonalBound (μ μ' : Fin 4) : Prop :=
  ∀ (s : ℝ) (y : Fin 4 → ℝ), 0 < s → realVecNorm y ^ 2 ≤ s →
    |mixedSecondPartial μ μ' (gaussianHeatKernel4 s) y| ≤ lowerDiagonalConstant * s ^ (-3 : ℤ)
def HeatKernelGreenProperties : Prop :=
  ∀ L : ℕ, 2 ≤ L → ∀ μ μ' : Fin 4,
    PeriodicSummation L ∧ TorusTimeIntegrals L μ μ' ∧ ContinuumTimeIntegrals μ μ' ∧
      (∀ d : ℕ, ShortTimeBounds d μ μ' ∧ LongTimeBounds d μ μ') ∧ NearDiagonalBound μ μ'
end YangMills.Construction.FreeKernel.HeatKernelGreen
end
