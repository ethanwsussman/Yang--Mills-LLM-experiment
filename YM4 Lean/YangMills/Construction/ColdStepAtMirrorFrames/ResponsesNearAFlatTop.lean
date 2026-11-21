import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
open BlockOffsets
variable {F : BlockFrame}
def IsNearUniformAbout (s : ℝ) (R : ℕ) (V : F.GaugeField F.top) (Y : F.Cell) : Prop :=
  ∀ (r : ℕ) (b : (Fin 4 → ℤ) × Fin 4), r ≤ R → BondWithinRadius r b →
    distFromOne (V (Y + siteOfCoords F.top b.1) b.2) ≤ 3 * r * s
def DerivsNearUniformTop : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → c.Admissible a L → ∀ ε : ℝ, 0 < ε →
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ σ₀ : ℝ, 0 < σ₀ ∧
      ∀ (σ : ℝ) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell), 0 < σ → σ ≤ σ₀ →
        IsBlockTorus L F → (∀ i, 2 * R + 2 < F.extent i) → IsSmallCurvature (5 / 4 * σ) V →
        IsNearUniformAbout (5 / 4 * σ) R V Y →
        ∀ (b : F.Site F.depth × Fin 4) (e : F.Site F.top × Fin 4) (X : imaginaryQuaternions),
          b ∈ chordBonds (finiteCells F) → 4 * cellSupDist Y (enclosingCell b.1) ≤ R →
          4 * cellSupDist Y e.1 ≤ R → ‖X‖ = 1 →
          ‖bondDeriv (torusCoordinate a c.ρA b) V ![e] ![X] -
            bondDeriv (torusCoordinate a c.ρA b) (uniformField F F.top) ![e] ![X]‖ ≤ ε
end ColdStepAtMirrorFrames
end YangMills.Construction
end
