import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAField
import YangMills.Construction.ColdStepAtMirrorFrames.MoveAlongABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def movedField {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) (τ : Fin k → ℝ) : F.GaugeField F.top :=
  leftTranslate (bondSpread c X τ) V
open Classical in
def crossingMoveMap {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (b : F.Site F.depth × Fin 4) : (Fin k → ℝ) →L[ℝ] imaginaryQuaternions :=
  if IsCrossingBond b then
    ∑ l, if c l = (enclosingCell b.1, b.2) then
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight (X l) else 0
  else 0
def ChartedFieldUnderMove : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : BlockFrame) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (w : F.GaugeField F.top → F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (B : Finset (F.Site F.depth × Fin 4)),
    (∀ b, b ∈ B) →
    (∀ b : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond b →
      ContDiffAt ℝ 3 (fun τ => w (movedField c X V τ) b.1 b.2) 0) →
    (∀ b : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond b → ‖w V b.1 b.2‖ ≤ 1) →
    ∃ A : (Fin k → ℝ) → ↥B → imaginaryQuaternions, ContDiffAt ℝ 3 A 0 ∧ A 0 = 0 ∧
      (∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), chartedField (w (movedField c X V τ)) (movedField c X V τ) =
        leftTranslate (extendByZero (A τ)) (chartedField (w V) V)) ∧
      ∀ b : ↥B, (IsAxialTreeBond b.1 → ∀ τ, A τ b = 0) ∧
        (¬ IsAxialTreeBond b.1 →
          IsExpProductLog C (fun τ => w (movedField c X V τ) b.1.1 b.1.2) (crossingMoveMap c X b.1)
            fun τ => A τ b)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
