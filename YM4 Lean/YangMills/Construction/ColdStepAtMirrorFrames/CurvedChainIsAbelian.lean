import YangMills.Construction.ColdStepAtMirrorFrames.ChainOfConstantCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def linearFluxAngle (g : ℝ) (μ ν : Fin 4) (φ : (Fin 4 → ℤ) → ℝ) (z : Fin 4 → ℤ) (i : Fin 4) : ℝ :=
  φ (z + Pi.single i 1) - φ z + if i = ν then g * (z μ : ℝ) else 0
def IsAbelianLinearAlong {j : ℕ} (X : imaginaryQuaternions) (g : ℝ) (μ ν : Fin 4) (U : F.GaugeField j) : Prop :=
  ∃ φ : (Fin 4 → ℤ) → ℝ, ∀ z i, U (siteOfCoords j z) i = expUnit (linearFluxAngle g μ ν φ z i • X)
def IsAbelianLinearPair {j : ℕ} (X : imaginaryQuaternions) (g : ℝ) (μ ν : Fin 4) (U : F.GaugeField j)
    (V : F.GaugeField (j + 1)) : Prop :=
  ∃ φ : (Fin 4 → ℤ) → ℝ, (∀ z i, U (siteOfCoords j z) i = expUnit (linearFluxAngle g μ ν φ z i • X)) ∧
    ∀ z i, V (siteOfCoords (j + 1) z) i =
      expUnit (linearFluxAngle ((F.blockSide : ℝ) ^ 2 * g) μ ν (fun z => φ fun k => (F.blockSide : ℤ) * z k) z i • X)
def levelFlux (F : BlockFrame) (μ : Fin 4) (l j : ℕ) : ℝ := 2 * Real.pi * l / (F.period j μ : ℝ) ^ 2
def ConstantCurvatureChainAbelian : Prop :=
  ∀ (F : BlockFrame) (X : imaginaryQuaternions) (μ ν : Fin 4) (n l : ℕ), Odd F.blockSide → (∀ i, F.extent i = n) →
    0 < n → ‖X‖ = 1 → μ < ν →
    2 * Real.pi * l / (n : ℝ) ^ 2 ≤ 1 → ∀ j, j ≤ F.top →
      IsAbelianLinearAlong X (levelFlux F μ l j) μ ν (constantCurvatureChain F X μ ν l j) ∧
      (j < F.top → (∀ c, blockFit (constantCurvatureChain F X μ ν l j) (constantCurvatureChain F X μ ν l (j + 1)) c = 0) ∧
        IsAbelianLinearPair X (levelFlux F μ l j) μ ν (constantCurvatureChain F X μ ν l j)
          (constantCurvatureChain F X μ ν l (j + 1)) ∧
        ∀ c : F.Site (j + 1) × Fin 4, ∃ ρ : ℝ, 0 < ρ ∧ contourAverage (constantCurvatureChain F X μ ν l j) c =
          ρ • ((constantCurvatureChain F X μ ν l (j + 1) c.1 c.2 : UnitQuaternion) : Quaternion ℝ))
end YangMills.Construction.ColdStepAtMirrorFrames
end
