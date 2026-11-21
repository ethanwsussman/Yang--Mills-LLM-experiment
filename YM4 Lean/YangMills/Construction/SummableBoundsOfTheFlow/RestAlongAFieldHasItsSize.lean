import YangMills.Construction.ColdStepAtMirrorFrames.MomentOfASquareBound
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativeAlongAMovingField
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Interpolation YangMills.Construction.IteratedDerivative
namespace YangMills.Construction.IteratedDerivative
def MovingFieldRemainderHasSize : Prop :=
  ∀ (F : BlockFrame) (ρ x lam κ W C Cb Cf Ek : ℝ)
    (d : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ)
    (Φ : StepVariable (finiteCells F) → ℝ) (p : ℝ → ℝ) (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (Z : ↥(chordBonds (finiteCells F)) → F.GaugeField F.top → BondVector → BondVector) (V : F.GaugeField F.top)
    (Y : F.Cell) (c₀ : F.Site F.top × Fin 4) (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions),
    0 < ρ → 1 ≤ x → 0 < lam → 0 < κ → 0 ≤ W → 0 ≤ Cb → 0 ≤ Cf → 0 ≤ Ek → IsCutoff ρ p → IsPseudoMetricOnBonds d →
    HasUniformlyConvexLaw ρ lam x κ C d Φ → (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
    ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ W →
    AreUnitVectors X →
    (∀ (η : StepVariable (finiteCells F)) (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
      (X' : Fin k → imaginaryQuaternions),
      (∀ b, ‖η b‖ < ρ) → AreUnitVectors X' → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (rotatedEval G V c' X') (η, 0)) →
    (∀ (η : StepVariable (finiteCells F)) (l k : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
      (e : Fin l → BondVector) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions),
      (∀ b, ‖η b‖ < ρ) → 1 ≤ l → l + k ≤ 3 → (∀ i, ‖e i‖ = 1) → AreUnitVectors X' →
      |jointMixedDeriv G η V b e c' X'| ≤
        Cb * Ek * Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert Y (chordBondCells b ∪ topBondCells c'))))) →
    (∀ (b : ↥(chordBonds (finiteCells F))) (v : BondVector) (l : Fin 2), ‖v‖ < ρ →
      ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (vectorFieldDerivSingle (Z b) V c X l) v ∧
      ‖vectorFieldDerivSingle (Z b) V c X l v‖ ≤
        Cf * Real.exp (-(2 ^ 8 * κ * cellSetDiameter {enclosingCell b.1.1, c₀.1, (c l).1})) ∧
      ‖fderiv ℝ (vectorFieldDerivSingle (Z b) V c X l) v‖ ≤
        Cf * Real.exp (-(2 ^ 8 * κ * cellSetDiameter {enclosingCell b.1.1, c₀.1, (c l).1}))) →
    (∀ (b : ↥(chordBonds (finiteCells F))) (v : BondVector), ‖v‖ < ρ →
      ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (vectorFieldDerivPair (Z b) V c X) v ∧
      ‖vectorFieldDerivPair (Z b) V c X v‖ ≤
        Cf * Real.exp (-(2 ^ 8 * κ * cellSetDiameter {enclosingCell b.1.1, c₀.1, (c 0).1, (c 1).1})) ∧
      ‖fderiv ℝ (vectorFieldDerivPair (Z b) V c X) v‖ ≤
        Cf * Real.exp (-(2 ^ 8 * κ * cellSetDiameter {enclosingCell b.1.1, c₀.1, (c 0).1, (c 1).1}))) →
    ContDiffOn ℝ 1 (movingFieldRemainder G Z V c X) {η | ∀ b, ‖η b‖ < ρ} ∧
    HasLocalSize ρ (cutoffFactor ρ p) Φ (lpMomentConstant lam W W) x κ
      ((W + 1) * (6 * (Cb * Ek * Cf) * W *
        Real.exp (-(2 ^ 4 * κ * cellSetDiameter {Y, c₀.1, (c 0).1, (c 1).1}))) * x ^ (-(1 / 2 : ℝ)))
      (fun b : ↥(chordBonds (finiteCells F)) => (cellSupDist (enclosingCell b.1.1) Y : ℝ))
      (movingFieldRemainder G Z V c X)
end YangMills.Construction.IteratedDerivative
end
