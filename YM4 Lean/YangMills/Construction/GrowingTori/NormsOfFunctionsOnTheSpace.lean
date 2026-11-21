import YangMills.Construction.GrowingTori.DefinitionsForSequencesOfGrowingTori
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.GrowingTori.Ambient
variable {L : ℕ} {V : Type*} [NormedAddCommGroup V]
def lipConst : (E : Ambient L) → (E.Point → V) → ℝ
  | euclidean => fun (g : (Fin 4 → ℝ) → V) => TestFunctions.lipConstR4 g
  | torus ℓ _ => fun (g : TorusMetric.Torus4 ℓ → V) => TestFunctions.lipConstTorus g
def liftR4 : (E : Ambient L) → (E.Point → ℝ) → (Fin 4 → ℝ) → ℝ
  | euclidean => fun (g : (Fin 4 → ℝ) → ℝ) => g
  | torus ℓ _ => fun (g : TorusMetric.Torus4 ℓ → ℝ) => g ∘ TorusMetric.torusProj ℓ
def grad (E : Ambient L) (g : E.Point → ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => TestFunctions.partialDerivR4 μ (E.liftR4 g) x
def gradNorm (E : Ambient L) (g : E.Point → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  Real.sqrt (∑ μ, |E.grad g x μ| ^ 2)
def gradSupENNReal (E : Ambient L) (g : E.Point → ℝ) : ℝ≥0∞ :=
  ⨆ x : Fin 4 → ℝ, ENNReal.ofReal (E.gradNorm g x)
def gradSup (E : Ambient L) (g : E.Point → ℝ) : ℝ := (E.gradSupENNReal g).toReal
end YangMills.Construction.GrowingTori.Ambient
end
