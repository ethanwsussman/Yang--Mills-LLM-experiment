import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def InBallProduct (ρ : ℝ) (η : StepVariable (finiteCells F)) : Prop := ∀ b, ‖η b‖ < ρ
structure ExpansionTransportBounds (star : Bool) (a ρA ρ δ E E₃ : ℝ) (L nss m : ℕ) (f : LocalFamily)
    (V : F.GaugeField F.top) : Prop where
  smooth : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), InBallProduct ρ η →
    ContDiffThreeAlongBonds (cellCentredExpansion star a ρA m f Y η) V
  lowDeriv : ∀ (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    1 ≤ k → k ≤ 2 → AreUnitVectors X →
    |bondDeriv (cellCentredExpansion star a ρA m f Y 0) V c X| ≤
      2⁻¹ ^ 6 * E / torusDecayFactor L δ (bondSpan Y c)
  thirdDeriv : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (c : Fin 3 → F.Site F.top × Fin 4)
    (X : Fin 3 → imaginaryQuaternions), InBallProduct ρ η → AreUnitVectors X →
    |bondDeriv (cellCentredExpansion star a ρA m f Y η) V c X| ≤
      2⁻¹ ^ 6 * E₃ / torusDecayFactor L δ (bondSpan Y c)
  abs_le : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), InBallProduct ρ η →
    |cellCentredExpansion star a ρA m f Y η V| ≤ 2⁻¹ ^ 8 * E / torusDecayFactor L δ nss
def ExpansionLocalAboveFrame (star : Bool) (a ρA δ E : ℝ) (L m : ℕ) (f : LocalFamily) {F' : BlockFrame}
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop :=
  ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
    (∀ l, BondWithinRadius r (h l)) → AreUnitVectors X →
    |bondDeriv (cellCentredExpansion star a ρA m f Y 0) V (bondsAt Y h) X -
      bondDeriv (cellCentredExpansion star a ρA m f Y' 0) V' (bondsAt Y' h) X| ≤
      2⁻¹ ^ 5 * E / torusDecayFactor L δ r
def expansionTransportAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ star,
      ExpansionTransportBounds star T.a T.chainParams.ρA T.ballRadius T.decayRate T.E T.energyRatio T.L
        T.blockIndex (frameRadius x) f V ∧
      ∀ (F' : BlockFrame) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
        IsCubicTopTorus T.L t T.n₀ F' → IsSmallCurvature (5 / 4 * T.σ) V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
        ExpansionLocalAboveFrame star T.a T.chainParams.ρA T.decayRate T.E T.L (frameRadius x) f V V' Y Y' r
def expansionTransportStatement : Prop := EventuallyInParameters expansionTransportAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
