import YangMills.Construction.ResponseInTheExpansion.LawOfTheColdHalf
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdOrderWithTwoFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
variable {F : BlockFrame}
structure HasDecayingKernels (ρ B r : ℝ) (Y : F.Cell) (G : AboveFrames F) (V : F.GaugeField F.top) : Prop where
  smooth : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)),
    (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η)
  deriv_one : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (u : BondVector),
    k ≤ 3 → (∀ b, ‖η b‖ ≤ ρ) → ‖u‖ = 1 → AreUnitVectors X →
    |jointMixedDeriv G η V ![b] ![u] c X| ≤
      B * Real.exp (-(r * cellSetDiameter ({Y} ∪ chordBondCells ![b] ∪ topBondCells c)))
  deriv_two : ∀ (η : StepVariable (finiteCells F)) (b b' : ↥(chordBonds (finiteCells F))) (u u' : BondVector),
    (∀ b, ‖η b‖ ≤ ρ) → ‖u‖ = 1 → ‖u'‖ = 1 →
    |jointMixedDeriv G η V ![b, b'] ![u, u'] ![] ![]| ≤
      B * Real.exp (-(r * cellSetDiameter ({Y} ∪ chordBondCells ![b, b'])))
structure LawDataAtField (Q : ColdHalfLaw) (m : ℕ → ℝ) (V : F.GaugeField F.top) : Prop where
  ballRadius_pos : 0 < Q.ballRadius
  isCutoff : IsCutoff Q.ballRadius Q.cutoff
  one_le_coupling : 1 ≤ Q.coupling
  continuous_exponent : ∃ Ψ : StepVariable (finiteCells F) → ℝ, Continuous Ψ ∧
    ballDensity Q.radialWeight (Q.exponent V) = ballDensity Q.radialWeight Ψ
  moments : ∀ (q : ℕ) (b : ↥(chordBonds (finiteCells F))),
    ballExpectation Q.radialWeight (Q.exponent V) (fun η => ‖η b‖ ^ (2 * q)) ≤ m q * (Q.coupling ^ q)⁻¹
def TopVariationBounded (Q : ColdHalfLaw) (Z : ℝ) (V : F.GaugeField F.top) : Prop :=
  ∀ (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions),
    (∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th w X)) →
    ∀ (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (b : ↥(chordBonds (finiteCells F))) (v : BondVector),
      ‖X‖ = 1 → ‖v‖ < Q.ballRadius →
      ContDiffAt ℝ 1 (fun v' : BondVector => imaginaryCoords
        (topVariationField Th 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v') V)) v ∧
      ‖imaginaryCoords (topVariationField Th 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v) V)‖ ≤
        Z * Real.exp (-(2 ^ 8 * Q.rate * bondDistToTopBond b c)) ∧
      ‖fderiv ℝ (fun v' : BondVector => imaginaryCoords
        (topVariationField Th 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v') V)) v‖ ≤
        Z * Real.exp (-(2 ^ 8 * Q.rate * bondDistToTopBond b c))
end YangMills.Construction.WeightedResponses
end
