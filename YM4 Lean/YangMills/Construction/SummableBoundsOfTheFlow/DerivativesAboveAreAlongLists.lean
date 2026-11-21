import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.GradientAlongTheRay
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace IteratedDerivative
variable {F : BlockFrame}
def rotatedEval {k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (p : StepVariable (finiteCells F) × (Fin k → ℝ)) : ℝ :=
  G p.1 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X p.2) V)
def parameterBasis (k : ℕ) : List (Fin k → ℝ) := List.ofFn fun i => Pi.single i 1
open Classical in
def pointDirections {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) :
    List (StepVariable (finiteCells F) × (Fin k → ℝ)) :=
  List.ofFn fun i => variableDirection (Fin k → ℝ) (Pi.single (b i) (u i))
def JointMixedDerivEqDerivAlong : Prop :=
  ∀ (F : BlockFrame) (V : F.GaugeField F.top) (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    (Nonempty ↥(chordBonds (finiteCells F)) →
      (∀ (l : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3)),
        2 ≤ l → (∀ i, ‖u i‖ = 1) → ContDiffAt ℝ ((l + k : ℕ) : WithTop ℕ∞) (jointDisplacement G η V b u c X) 0) →
      ∀ n : ℕ, ContDiffAt ℝ (n : WithTop ℕ∞) (rotatedEval G V c X) (η, 0)) ∧
    ∀ (l : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3)),
      ContDiffAt ℝ ((l + k : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0) →
      jointMixedDeriv G η V b u c X = derivAlong (rotatedEval G V c X)
        (pointDirections b u ++ parameterDirections _ _ (parameterBasis k)) (η, 0)
end IteratedDerivative
end YangMills.Construction
end
