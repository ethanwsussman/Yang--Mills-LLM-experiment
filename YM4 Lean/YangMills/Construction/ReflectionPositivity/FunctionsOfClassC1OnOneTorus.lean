import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOnOneTorusIsometriesAndSymmetricFunctions
import Mathlib
set_option autoImplicit false
open scoped ENNReal Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TorusC1
variable {s : Conventions.StandingParameters}
def GradBoundedUnifCont (f : s.Torus → ℝ) : Prop :=
  TorusCutoffs.gradSupNorm f < ∞ ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x x' : s.Torus, TorusCutoffs.torusDist x x' ≤ δ →
      TorusMetric.euclidNormVec (TorusCutoffs.grad f x - TorusCutoffs.grad f x') ≤ ε
def LipschitzByGradSup (f : s.Torus → ℝ) : Prop :=
  (∀ x x' : s.Torus,
      |f x - f x'| ≤ (TorusCutoffs.gradSupNorm f).toReal * TorusCutoffs.torusDist x x') ∧
    TorusTuples.IsLipschitzReal f ∧
    TestFunctions.lipConstTorus f ≤ (TorusCutoffs.gradSupNorm f).toReal
def GradEquivariant (f : s.Torus → ℝ) : Prop :=
  (∀ r : s.Torus ≃ s.Torus, TorusTuples.IsTorusIsometry s r →
    ∀ (R : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ), R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      (∀ y, r.symm (TorusCutoffs.proj s y) = TorusCutoffs.proj s (R *ᵥ y + w)) →
        TorusCutoffs.IsC1 (TorusTuples.transport r f) ∧
          ∀ x, TorusCutoffs.grad (TorusTuples.transport r f) x =
            Rᵀ *ᵥ TorusCutoffs.grad f (r.symm x)) ∧
  ∀ v x : s.Torus, TorusCutoffs.grad (TorusTuples.transport (TorusTuples.shiftBy v) f) x =
    TorusCutoffs.grad f (x - v)
def SubC1 (f : s.Torus → ℝ) : Prop :=
  ∀ f' : s.Torus → ℝ, TorusCutoffs.IsC1 f' →
    TorusCutoffs.IsC1 (f - f') ∧ TorusCutoffs.grad (f - f') = TorusCutoffs.grad f - TorusCutoffs.grad f'
def C1Properties : Prop :=
  ∀ (s : Conventions.StandingParameters) (f : s.Torus → ℝ), TorusCutoffs.IsC1 f →
    GradBoundedUnifCont f ∧ LipschitzByGradSup f ∧ GradEquivariant f ∧ SubC1 f
end YangMills.Construction.ReflectionPositivity.TorusC1
end
