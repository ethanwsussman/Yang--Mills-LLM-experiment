import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASide
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
namespace YangMills.Construction.ColdStepAtMirrorFrames
def readOnMultiples (L t : ℕ) (f : LocalFamily) : LocalDensity :=
  fun n y W => f (torusFrame L t (n / L)) (siteOfCoords _ fun k => ((y k).cast : ℤ))
    (readAtLevel (torusFrame L t (n / L)) (torusFrame L t (n / L)).depth W)
def LocalFamilyOnTori : Prop :=
  ∀ (ℓ : StepParameters) (t : ℕ) (δ E E₃ : ℝ) (f : LocalFamily), ℓ.Admissible →
    ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ) → δ = ℓ.weightRate →
    0 < E → E ≤ E₃ → IsRegularFamily ℓ.side t ℓ.n₀ ℓ.threshold δ E E₃ f →
    IsCurvatureFamilyOnMultiples ℓ ℓ.side E₃ (readOnMultiples ℓ.side t f) ∧
    (∀ (m : ℕ) (b b' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions), 0 < m →
      flatSecondDeriv (readOnMultiples ℓ.side t f) (ℓ.side * m) b b' X X' =
        hessianAtTrivial f ℓ.side t m b b' X X') ∧
    ∀ (n : ℕ) (y : (torusFrame ℓ.side t n).Site (torusFrame ℓ.side t n).depth)
      (W : (torusFrame ℓ.side t n).GaugeField (torusFrame ℓ.side t n).depth),
      0 < n → centered (readOnMultiples ℓ.side t f) (n * ℓ.side) (toTorusSite _ y) (restrictToTorus _ W) =
        subtractTrivial f (torusFrame ℓ.side t n) y W
end YangMills.Construction.ColdStepAtMirrorFrames
end
