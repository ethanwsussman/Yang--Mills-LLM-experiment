import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTop
import YangMills.Construction.SummableBoundsOfTheFlow.PartsBetweenAreSmoothInTheParameters
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Interpolation YangMills.Construction.Estimates
namespace YangMills.Construction.Interpolation
def chordBondDist {F : BlockFrame} (b b' : ↥(chordBonds (finiteCells F))) : ℝ :=
  (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ)
def slopeConstant (C W : ℝ) : ℝ := 2 * C * (W + 1) + 1
def FamilyLawExponentSlopeBounds : Prop :=
  ∀ (F : BlockFrame) (s a ρA ρ x κ C Cb Ef W : ℝ) (m : ℕ) (V : F.GaugeField F.top) (φ : LocalFamily),
    0 < ρ → 1 ≤ x → 0 < κ → 0 ≤ C → 0 ≤ Cb → 0 ≤ Ef → 0 ≤ W →
    InterpolatedExponentBounds s a ρA ρ x κ C m V → InterpolatedPartsSmooth s a ρA ρ x m V →
    (∀ y : F.Site F.depth, JointlyContDiffOnBalls ρ V (fun ζ V' => interpolatedExpansion s a ρA m φ y ζ V')) →
    (∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (l : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
      (u : Fin l → BondVector), (∀ b, ‖η b‖ < ρ) → (∀ i, ‖u i‖ = 1) → 1 ≤ l → l ≤ 2 →
      |jointMixedDeriv (fun ζ V' => interpolatedExpansion s a ρA m φ y ζ V') η V b u
        (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)| ≤
        Cb * Ef * Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert (enclosingCell y) (chordBondCells b ∪
          topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)))))) →
    (∀ z : F.Cell, ∑ Y ∈ finiteCells F, Real.exp (-(2 ^ 5 * κ * (cellSupDist Y z : ℝ))) ≤ W) →
    (∀ z : F.Cell, ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell y) z : ℝ))) ≤ W) →
    (∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W) →
    Cb * Ef * W ≤ Real.sqrt x →
    ∀ b : ↥(chordBonds (finiteCells F)), ∃ w : ↥(chordBonds (finiteCells F)) → ℝ, (∀ b', 0 ≤ w b') ∧
      ∑ b', w b' ≤ W ^ 2 ∧
      (∀ (η : StepVariable (finiteCells F)) (e : BondVector), (∀ b, ‖η b‖ < ρ) →
        |bondPartialDeriv (familyLawExponent s a ρA x m φ V) b η e| ≤
          slopeConstant C W * Real.sqrt x * (x * ∑ b', w b' * ‖η b'‖ ^ 2 + 1) * ‖e‖) ∧
      ∀ (η : StepVariable (finiteCells F)) (b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
        (∀ b, ‖η b‖ < ρ) →
        |secondDerivAlong (familyLawExponent s a ρA x m φ V) η (bondVariation b e) (bondVariation b' e')| ≤
          slopeConstant C W * x * Real.exp (-(2 * κ * chordBondDist b' b)) * ‖e‖ * ‖e'‖
end YangMills.Construction.Interpolation
end
