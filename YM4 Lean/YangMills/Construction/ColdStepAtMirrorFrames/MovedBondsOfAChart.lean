import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame} {k : ℕ}
def shiftedCoords (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions) (σ : Fin k → ℝ) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => w x i + ∑ l, σ l • ξ l x i
def translatedTop (V : F.GaugeField F.top) (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions)
    (σ : Fin k → ℝ) : F.GaugeField F.top :=
  leftTranslate (fun y i => ∑ l, σ l • μ l y i) V
def translatedChart (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (σ : Fin k → ℝ) : F.GaugeField F.depth :=
  chartedField (shiftedCoords w ξ σ) (translatedTop V μ σ)
def ParameterMovesBond (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (l : Fin k)
    (b : F.Site F.depth × Fin 4) : Prop :=
  ξ l b.1 b.2 ≠ 0 ∨ (IsCrossingBond b ∧ μ l (enclosingCell b.1) b.2 ≠ 0)
def TranslatedChartAnalytic : Prop :=
  ∃ D : ℕ → ℕ → ℝ, (∀ k j, 0 ≤ D k j) ∧
    ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (k : ℕ)
      (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
      (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions),
      (∀ (y : F.Site F.top) (i : Fin 4),
        ContDiff ℝ ω (fun σ : Fin k → ℝ => ((translatedTop V μ σ y i : UnitQuaternion) : ℍ[ℝ])) ∧
        ((∀ l, ‖μ l y i‖ ≤ 1) → ∀ j,
          ‖iteratedFDeriv ℝ j (fun σ : Fin k → ℝ => ((translatedTop V μ σ y i : UnitQuaternion) : ℍ[ℝ])) 0‖
            ≤ D k j)) ∧
      ∀ (x : F.Site F.depth) (i : Fin 4),
        ContDiff ℝ ω (fun σ : Fin k → ℝ => ((translatedChart w V ξ μ σ x i : UnitQuaternion) : ℍ[ℝ])) ∧
        (‖w x i‖ ≤ 1 ∨ IsAxialTreeBond (x, i) → (∀ l, ‖ξ l x i‖ ≤ 1) →
          (∀ l, ‖μ l (enclosingCell x) i‖ ≤ 1) →
          ∀ j, ‖iteratedFDeriv ℝ j
            (fun σ : Fin k → ℝ => ((translatedChart w V ξ μ σ x i : UnitQuaternion) : ℍ[ℝ])) 0‖ ≤ D k j) ∧
        ∀ σ σ' : Fin k → ℝ, (∀ l, ParameterMovesBond ξ μ l (x, i) → σ l = σ' l) →
          translatedChart w V ξ μ σ x i = translatedChart w V ξ μ σ' x i
end ColdStepAtMirrorFrames
end YangMills.Construction
end
