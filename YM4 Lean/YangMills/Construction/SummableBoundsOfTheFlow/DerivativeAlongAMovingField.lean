import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveAreAlongLists
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.IteratedDerivative
open scoped Topology
open BlockAverages ColdStepAtMirrorFrames BondIntegration
variable {F : BlockFrame}
def translateAlongPair (V : F.GaugeField F.top) (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (r : Fin 2 → ℝ) : F.GaugeField F.top :=
  leftTranslate (ColdStepAtMirrorFrames.bondSpread c X r) V
def vectorFieldDerivSingle (Z : F.GaugeField F.top → BondVector → BondVector) (V : F.GaugeField F.top)
    (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions) (l : Fin 2) (v : BondVector) : BondVector :=
  bondDeriv (fun V' => Z V' v) V (fun _ : Fin 1 => c l) (fun _ => X l)
def vectorFieldDerivPair (Z : F.GaugeField F.top → BondVector → BondVector) (V : F.GaugeField F.top)
    (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions) (v : BondVector) : BondVector :=
  bondDeriv (fun V' => Z V' v) V c X
def movingFieldRemainder (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (Z : ↥(chordBonds (finiteCells F)) → F.GaugeField F.top → BondVector → BondVector) (V : F.GaugeField F.top)
    (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions) (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ b, (fieldDerivative b (vectorFieldDerivSingle (Z b) V c X 0)
      (fun ζ => bondDeriv (G ζ) V (fun _ : Fin 1 => c 1) (fun _ => X 1)) η +
    fieldDerivative b (vectorFieldDerivSingle (Z b) V c X 1)
      (fun ζ => bondDeriv (G ζ) V (fun _ : Fin 1 => c 0) (fun _ => X 0)) η +
    fieldDerivative b (vectorFieldDerivPair (Z b) V c X) (fun ζ => G ζ V) η)
def MovingFieldSecondDeriv : Prop :=
  ∀ (F : BlockFrame) (V : F.GaugeField F.top) (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (Z : ↥(chordBonds (finiteCells F)) → F.GaugeField F.top → BondVector → BondVector) (D : F.GaugeField F.top → ℝ)
    (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions) (η : StepVariable (finiteCells F)),
    (∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (ζ, 0)) →
    (∀ b, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun r => Z b (translateAlongPair V c X r) (η b)) 0) →
    (∀ᶠ r in 𝓝 (0 : Fin 2 → ℝ), D (translateAlongPair V c X r) =
      ∑ b, bondPartialDeriv (fun ζ => G ζ (translateAlongPair V c X r)) b η (Z b (translateAlongPair V c X r) (η b))) →
    bondDeriv D V c X =
      (∑ b, fieldDerivative b (Z b V) (fun ζ => bondDeriv (G ζ) V c X) η) + movingFieldRemainder G Z V c X η
end YangMills.Construction.IteratedDerivative
end
