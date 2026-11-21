import YangMills.Construction.ResponseInTheExpansion.KernelsAboveTheFrames
import YangMills.Construction.ResponseInTheExpansion.SlotsOfTheColdLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison
def KernelIncrementIsSlot : Prop :=
  ∀ (F : BlockFrame) (Q : ColdHalfLaw) (m : ℕ → ℝ) (V : F.GaugeField F.top) (Y : F.Cell) (G : AboveFrames F) (B r Wt Z C : ℝ),
    LawDataAtField Q m V → (∀ q, 0 ≤ m q) → HasDecayingKernels Q.ballRadius B r Y G V → TopVariationBounded Q Z V → 0 ≤ B → 0 ≤ Z →
    0 < Q.rate → 2 ^ 6 * Q.rate ≤ r → 1 ≤ Wt →
    (∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(r / 2 * bondDistToCell Y' b)) ≤ Wt) →
    4 * B * Wt * (1 + Z) ≤ C →
    IsSlot Q (fun q => 1 + m q) (C * Q.coupling ^ (-(1 / 2) : ℝ)) Y (fun η V' => G η V' - G 0 V') V ∧
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |Q.expectation V (fun η => bondDeriv (fun V' => G η V' - G 0 V') V c X)| ≤
        (1 + m 1) * (C * Q.coupling ^ (-(1 / 2) : ℝ)) * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))
def ColdHalfLaw.blockExponent (Q : ColdHalfLaw) {F : BlockFrame} (Y : F.Cell) : AboveFrames F :=
  fun η V => interpolatedBlockExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V η
def BlockExponentAddKernelIsSlot : Prop :=
  ∀ (F : BlockFrame) (Q : ColdHalfLaw) (m Cz : ℕ → ℝ) (V : F.GaugeField F.top) (Y : F.Cell) (R : AboveFrames F)
    (B r Wt W Z Cs C : ℝ),
    LawDataAtField Q m V → (∀ q, 0 ≤ m q) → (∀ q, 0 ≤ Cz q) → HasDecayingKernels Q.ballRadius B r Y R V →
    TopVariationBounded Q Z V →
    0 < B → 0 ≤ Z → 0 < Q.rate → 2 ^ 6 * Q.rate ≤ r → 1 ≤ Wt → 0 ≤ W → 0 < Cs →
    (∀ u v : F.Cell, cellSupDist u v = cellSupDist v u) →
    (∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(r / 2 * bondDistToCell Y' b)) ≤ Wt) →
    (∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * Q.rate * bondDistToCell Y' b)) ≤ W) →
    InterpolatedExponentBounds 1 Q.a Q.chartRadius Q.ballRadius Q.coupling Q.rate Cs Q.mirrorRadius V →
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (η : StepVariable (finiteCells F)),
      (∀ b, ‖η b‖ ≤ Q.ballRadius) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        Q.blockExponent Y q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η)) →
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 → AreUnitVectors X →
      Q.HasSize Cz V (Cs * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))) Y fun η => bondDeriv (Q.blockExponent Y η) V c X) →
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |bondDeriv (R 0) V c X| ≤ B * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))) →
    Cs * (3 + W) * (1 + Z) + 4 * B * Wt * (1 + Z) + B ≤ C →
    IsSlot Q (fun q => 1 + m q + Cz q) C Y (fun η V' => Q.blockExponent Y η V' + R η V') V ∧
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |Q.expectation V (fun η => bondDeriv (fun V' => Q.blockExponent Y η V' + R η V') V c X)| ≤
        (1 + m 1) * C * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))
def slotsFromKernelsStatement : Prop := KernelIncrementIsSlot ∧ BlockExponentAddKernelIsSlot
end YangMills.Construction.WeightedResponses
end
