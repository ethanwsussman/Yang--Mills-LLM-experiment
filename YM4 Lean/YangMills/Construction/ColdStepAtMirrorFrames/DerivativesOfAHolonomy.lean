import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def pathPositiveBonds {j : ℕ} : F.Site j → List PathStep → List (F.Site j × Fin 4)
  | _, [] => []
  | x, st :: r => (if st.2 then (x, st.1) else (x - unitStep j st.1, st.1)) ::
      pathPositiveBonds (x + stepDisplacement j st) r
def perturbedHolonomy {j k : ℕ} (W : F.GaugeField j) (x : F.Site j) (l : List PathStep)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) : ℍ[ℝ] :=
  ((pathHolonomy (leftTranslate (bondSpread c X τ) W) x l : UnitQuaternion) : ℍ[ℝ])
def HolonomyDerivativeBounds : Prop :=
  ∃ B : ℕ → ℕ → ℕ → ℝ, (∀ k n j, 0 ≤ B k n j) ∧
    ∀ (F : BlockFrame) (lev : ℕ) (W : F.GaugeField lev) (x : F.Site lev) (l : List PathStep) (k : ℕ)
      (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (perturbedHolonomy W x l c X) ∧
      ((∀ i, ‖X i‖ ≤ 1) → ∀ j, ‖iteratedFDeriv ℝ j (perturbedHolonomy W x l c X) 0‖ ≤ B k l.length j) ∧
      ∀ i, c i ∉ pathPositiveBonds x l → ∀ (τ : Fin k → ℝ) (s : ℝ),
        perturbedHolonomy W x l c X (Function.update τ i s) = perturbedHolonomy W x l c X τ
end YangMills.Construction.ColdStepAtMirrorFrames
end
