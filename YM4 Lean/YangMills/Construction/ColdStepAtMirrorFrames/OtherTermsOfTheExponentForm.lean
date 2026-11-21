import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.PullbackThroughTheChartForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
structure IsChartBasePoint (T : StepParameters) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) : Prop where
  room : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ + T.ballRadius ≤ T.chainParams.ρA
  small : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ + T.ballRadius ≤ 1 / (64 * (T.L : ℝ))
  curvature_small : IsSmallCurvature (41 / 64 * T.σ) (chartedField w V)
  contour_near_one : ∀ (c : F.Site F.top × Fin 4) (h : Fin 4 → ℤ) (g : Equiv.Perm (Fin 4)), h ∈ centredCube T.L →
    ‖contourHolonomyDefect (chartedField w V) V c h g - 1‖ + 5 * (T.L : ℝ) * T.ballRadius ≤ 1 / 2
def exponentMinusEnergy (a x : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (f : LocalFamily)
    (ν : ℝ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) : ℝ :=
  exponentInChart a x w f ν V η - x * chartedEnergyAt a w V η
def RemainderExponentBoundsAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (ν : ℝ), T.coupling ≤ x →
    HasDecayingDerivs T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsChartBasePoint T w V → 0 ≤ ν → ν ≤ 1 →
    ∃ K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ,
      (∀ b b', 0 ≤ K b b') ∧ (∀ b b', K b b' = K b' b) ∧
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
        ContDiffAt ℝ 3 (exponentMinusEnergy T.a x w f ν V) η) ∧
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
          |secondDerivAlong (exponentMinusEnergy T.a x w f ν V) η (bondVariation b e) (bondVariation b' e')| ≤
            K b b' * ‖e‖ * ‖e'‖) ∧
      (∀ b, ∑ b', K b b' * Real.exp (2 * T.κ * chordBondDist F b b') ≤ x * T.chainParams.lam / 16) ∧
      ∀ (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.ballRadius) →
        ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
          |bondPartialDeriv (exponentMinusEnergy T.a x w f ν V) b η e| ≤
            (Real.sqrt (x * T.chainParams.lam / 4) - 1) * ‖e‖
def RemainderExponentBounds : Prop := EventuallyInParameters RemainderExponentBoundsAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
