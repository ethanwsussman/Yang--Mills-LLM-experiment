import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.WeightedResponses
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
def flatCoefficient (a ρ : ℝ) (X : imaginaryQuaternions) (b : F.Site F.depth × Fin 4) (c : F.Cell × Fin 4) : ℝ :=
  -(((bondDeriv (torusCoordinate a ρ b) (flatTopField (F := F)) ![c] ![X] : imaginaryQuaternions) : ℍ[ℝ]) *
    (X : ℍ[ℝ])).re
def flatLinearPart (a ρ : ℝ) (X : imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (D : F.Cell → Fin 4 → imaginaryQuaternions) : imaginaryQuaternions :=
  ∑ z ∈ finiteCells F, ∑ i : Fin 4, flatCoefficient a ρ X b (z, i) • D z i
def smallFormCoordinateStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), Odd L → c.Admissible a L → ∃ K s₁ : ℝ, 0 ≤ K ∧ 0 < s₁ ∧
    ∀ (F : BlockFrame) (b : F.Site F.depth × Fin 4) (D : F.Cell → Fin 4 → imaginaryQuaternions)
      (X : imaginaryQuaternions) (s : ℝ), IsBlockTorus L F →
      b ∈ chordBonds (finiteCells F) → ‖X‖ = 1 → 0 ≤ s → s ≤ s₁ → (∀ z i, ‖D z i‖ ≤ s) →
      ‖((torusCoordinate a c.ρA b (leftTranslate D (flatTopField (F := F))) - flatLinearPart a c.ρA X b D :
        imaginaryQuaternions) : ℍ[ℝ])‖ ≤ K * s ^ 2
end YangMills.Construction.WeightedResponses
end
