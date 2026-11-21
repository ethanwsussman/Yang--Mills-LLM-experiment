import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def cutoffCovariance (ρ : ℝ) (p : ℝ → ℝ) (Ψ H H' : StepVariable (finiteCells F) → ℝ) : ℝ :=
  cutoffMean ρ p Ψ (fun η => H η * H' η) - cutoffMean ρ p Ψ H * cutoffMean ρ p Ψ H'
def MeansLocalize (dual : Bool) (a ρA ρ lam x κ Cs CE : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily)
    {F' : BlockFrame} (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell)
    (r : ℕ) : Prop :=
  ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
    |cutoffMean ρ p (fun η => v * stepExponent dual a ρA x m f 0 V η + (1 - v) * totalQuadratic lam x η)
        (fun η => cellExponent dual a ρA x m Y V η - cellQuadratic lam x Y η) -
      cutoffMean ρ p (fun η => v * stepExponent dual a ρA x m f 0 V' η + (1 - v) * totalQuadratic lam x η)
        (fun η => cellExponent dual a ρA x m Y' V' η - cellQuadratic lam x Y' η)| ≤
      Cs * Real.exp (-(κ * r / 2 ^ 7)) ∧
    |cutoffMean ρ p (stepExponent dual a ρA x m f v V) (fun η => cellCentredExpansion dual a ρA m f Y η V) -
      cutoffMean ρ p (stepExponent dual a ρA x m f v V')
        (fun η => cellCentredExpansion dual a ρA m f Y' η V')| ≤ CE * Real.exp (-(κ * r / 2 ^ 7))
def ThirdDerivCovarianceLocal (dual : Bool) (a ρA ρ x κ E E₃ Cs : ℝ) (m : ℕ) (p : ℝ → ℝ)
    (f : LocalFamily) (V : F.GaugeField F.top) : Prop :=
  ∀ (ν : ℝ) (y : F.Site F.depth) (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions),
    0 ≤ ν → ν ≤ 1 → AreUnitVectors X →
    ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
      |cutoffCovariance ρ p (stepExponent dual a ρA x m f ν V) (fun η => centredExpansion dual a ρA m f y η V)
        (fun η => bondDeriv (centredExpansion dual a ρA m f y' η) V c X)| ≤
      Cs * E * E₃ * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ / 2 ^ 5 * bondSpan (enclosingCell y) c))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
