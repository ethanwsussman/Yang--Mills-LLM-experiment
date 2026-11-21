import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace IteratedDerivative
variable {F : BlockFrame}
def ContDiffAlongBonds (k : ℕ) {l : ℕ} (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin l → F.Site F.top × Fin 4) (X : Fin l → imaginaryQuaternions) : Prop :=
  ContDiffAt ℝ (k : WithTop ℕ∞) (fun σ : Fin l → ℝ => G (ColdStepAtMirrorFrames.leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ) V)) 0
def restrictToList {α : Type} {k : ℕ} (c : Fin k → α) (A : List (Fin k)) : Fin A.length → α :=
  fun l => c (A.get l)
def BondDerivSumProductRules : Prop :=
  ∀ (F : BlockFrame) (V : F.GaugeField F.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions),
    (∀ (ι : Type) (s : Finset ι) (G : ι → F.GaugeField F.top → ℝ),
      (∀ i ∈ s, ContDiffAlongBonds k (G i) V c X) →
      bondDeriv (fun V' => ∑ i ∈ s, G i V') V c X = ∑ i ∈ s, bondDeriv (G i) V c X) ∧
    (∀ (r : ℝ) (G : F.GaugeField F.top → ℝ), ContDiffAlongBonds k G V c X →
      bondDeriv (fun V' => r * G V') V c X = r * bondDeriv G V c X) ∧
    ∀ (G H : F.GaugeField F.top → ℝ) (M : ℝ), ContDiffAlongBonds k G V c X → ContDiffAlongBonds k H V c X →
      (∀ A B : List (Fin k), A.length + B.length = k → (∀ l, l ∈ A ∨ l ∈ B) →
        |bondDeriv G V (restrictToList c A) (restrictToList X A)| *
          |bondDeriv H V (restrictToList c B) (restrictToList X B)| ≤ M) →
      |bondDeriv (fun V' => G V' * H V') V c X| ≤ 2 ^ k * M
end IteratedDerivative
end YangMills.Construction
end
