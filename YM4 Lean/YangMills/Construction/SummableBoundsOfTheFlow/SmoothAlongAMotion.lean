import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Estimates
open BlockAverages ColdStepAtMirrorFrames
def SmoothAlongMotion : Prop :=
  ∀ (F : BlockFrame) (j N p : ℕ) (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (α : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions), (∀ i, F.period j i ≠ 0) →
    (∀ (q : ℕ) (c : Fin q → F.Site j × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ N (fun τ : Fin q → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) →
    (∀ x b, ContDiffAt ℝ N (fun τ => α τ x b) 0) → (∀ x b, α 0 x b = 0) →
    ContDiffAt ℝ N (fun τ => G (leftTranslate (α τ) W)) 0
end YangMills.Construction.Estimates
end
