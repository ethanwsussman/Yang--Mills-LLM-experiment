import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotionProof
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothAlongAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open scoped Quaternion
namespace YangMills.Construction.Estimates
namespace SmoothAlongMotionChart
section torus
def imagBasis (r : Fin 3) : imaginaryQuaternions :=
  ![⟨(⟨0, 1, 0, 0⟩ : ℍ[ℝ]), rfl⟩, ⟨(⟨0, 0, 1, 0⟩ : ℍ[ℝ]), rfl⟩, ⟨(⟨0, 0, 0, 1⟩ : ℍ[ℝ]), rfl⟩] r
def imagCoord (r : Fin 3) (w : imaginaryQuaternions) : ℝ :=
  ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK] r
variable {F : BlockFrame} {j : ℕ} [∀ i, NeZero (F.period j i)]
def fieldOfBonds (A : F.Site j × Fin 4 → imaginaryQuaternions) :
    F.Site j → Fin 4 → imaginaryQuaternions := fun x b => A (x, b)
def chartComp (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (A : F.Site j × Fin 4 → imaginaryQuaternions) : ℝ :=
  G (leftTranslate (fieldOfBonds A) W)
def bondCoordinates {q : ℕ} (e : (F.Site j × Fin 4) × Fin 3 ≃ Fin q) :
    (F.Site j × Fin 4 → imaginaryQuaternions) →L[ℝ] (Fin q → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A l => imagCoord (e.symm l).2 (A (e.symm l).1)
      map_add' := fun A A' => by
        funext l
        have h : ∀ r (w w' : imaginaryQuaternions),
            imagCoord r (w + w') = imagCoord r w + imagCoord r w' := by
          intro r w w'
          fin_cases r <;> simp [imagCoord]
        simp [h]
      map_smul' := fun u A => by
        funext l
        have h : ∀ r (w : imaginaryQuaternions), imagCoord r (u • w) = u * imagCoord r w := by
          intro r w
          fin_cases r <;> simp [imagCoord]
        simp [h] }
theorem contDiffAt_chartComp {p : ℕ} {G : F.GaugeField j → ℝ} {W : F.GaugeField j}
    (hG : ∀ (q : ℕ) (c : Fin q → F.Site j × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ p (fun τ : Fin q → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W)) 0) :
    ContDiffAt ℝ p (chartComp G W) 0 := by apply _root_.YangMills.Construction.Estimates.contDiffAt_chartPullback <;> assumption
end torus
end SmoothAlongMotionChart
open SmoothAlongMotionChart in
theorem smoothAlongMotion_holds : SmoothAlongMotion := by
  intro F j N p G W α hper hG hα h0
  have : ∀ i, NeZero (F.period j i) := fun i => ⟨hper i⟩
  have hc := contDiffAt_chartComp hG
  let β : (Fin p → ℝ) → F.Site j × Fin 4 → imaginaryQuaternions := fun τ d => α τ d.1 d.2
  have hβ : ContDiffAt ℝ N β 0 := contDiffAt_pi.2 fun d => hα d.1 d.2
  have hβ0 : β 0 = 0 := by
    funext d
    exact h0 d.1 d.2
  have hfun : (fun τ => G (leftTranslate (α τ) W)) = chartComp G W ∘ β := rfl
  rw [hfun]
  exact ContDiffAt.comp (0 : Fin p → ℝ) (hβ0 ▸ hc) hβ
end YangMills.Construction.Estimates
end
