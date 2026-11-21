import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.FunctionAlongAMove
import YangMills.Construction.ColdStepAtMirrorFrames.MoveOfAChartField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def slotDecayWeight {k : ℕ} (r : ℝ) (b : F.Site F.depth × Fin 4) (c : Fin k → F.Site F.top × Fin 4)
    (i : Fin k) : ℝ :=
  Real.exp (-(r * cellSupDist (enclosingCell b.1) (c i).1))
abbrev slotBasisVector {k : ℕ} (i : Fin k) : Fin k → ℝ := Pi.single i 1
structure StepFrameBounds (star : Bool) (a ρA δ₂ Cw σ : ℝ) (m : ℕ) (V : F.GaugeField F.top) : Prop where
  norm_le : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame star a ρA m b V‖ ≤ Cw * σ
  analytic : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame star a ρA m b) V
  decay : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
    ‖bondDeriv (stepFrame star a ρA m b) V c X‖ ≤
      Cw * Real.exp (-(δ₂ / 4 * bondListDistance (enclosingCell b.1) c))
structure MoveDerivDecay {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (K r : ℝ)
    {B : Finset (F.Site F.depth × Fin 4)} (A : (Fin k → ℝ) → ↥B → imaginaryQuaternions) : Prop where
  first : ∀ (i : Fin k) (b : ↥B), firstDerivNorm A (slotBasisVector i) b ≤ K * slotDecayWeight r b.1 c i
  second : ∀ (i j x : Fin k) (b : ↥B), i ≠ j → (x = i ∨ x = j) →
    secondDerivNorm A (slotBasisVector i) (slotBasisVector j) b ≤ K * slotDecayWeight r b.1 c x
  third : ∀ (i j l x : Fin k) (b : ↥B), i ≠ j → i ≠ l → j ≠ l → (x = i ∨ x = j ∨ x = l) →
    thirdDerivNorm A (slotBasisVector i) (slotBasisVector j) (slotBasisVector l) b ≤
      K * slotDecayWeight r b.1 c x
structure IsFieldAboveFrameMove (star : Bool) (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (K r : ℝ) (B : Finset (F.Site F.depth × Fin 4))
    (A : (Fin k → ℝ) → ↥B → imaginaryQuaternions) : Prop where
  smooth : ContDiffAt ℝ 3 A 0
  map_zero : A 0 = 0
  eventually_eq : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), fieldAboveFrame star a ρA m (movedField c X V τ) η =
    leftTranslate (extendByZero (A τ)) (fieldAboveFrame star a ρA m V η)
  tree_bond : ∀ (b : ↥B) (τ : Fin k → ℝ), IsAxialTreeBond b.1 → A τ b = 0
  decays : MoveDerivDecay c K r A
  first_deriv_near : ∀ (i : Fin k) (b : ↥B), ¬ IsAxialTreeBond b.1 →
    ‖iteratedFDeriv ℝ 1 (fun τ => A τ b) 0 ![slotBasisVector i] -
      (bondDeriv (stepFrame star a ρA m b.1) V ![c i] ![X i] + crossingMoveMap c X b.1 (slotBasisVector i))‖ ≤
      K * ‖coordsAboveFrame star a ρA m V η b.1.1 b.1.2‖
def fieldAboveFrameMoveStatement : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (F : BlockFrame) (star : Bool) (a ρA δ₂ Cw σ ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (B : Finset (F.Site F.depth × Fin 4)),
    (∀ b, b ∈ B) → (∀ b : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond b → b ∈ chordBonds (finiteCells F)) →
    AreUnitVectors X → 0 ≤ Cw → 0 ≤ δ₂ → 0 ≤ ρ → StepFrameBounds star a ρA δ₂ Cw σ m V → Cw * σ + ρ ≤ 1 →
    (∀ b, ‖η b‖ ≤ ρ) →
    ∃ A : (Fin k → ℝ) → ↥B → imaginaryQuaternions,
      IsFieldAboveFrameMove star a ρA m V η c X (C₀ * (Cw + 2) ^ 3) (δ₂ / 4) B A
end ColdStepAtMirrorFrames
end YangMills.Construction
end
