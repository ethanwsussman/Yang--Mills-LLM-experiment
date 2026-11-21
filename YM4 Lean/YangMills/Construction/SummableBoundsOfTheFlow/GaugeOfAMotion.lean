import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Estimates
namespace YangMills.Construction.GaugeAlongMotion
variable {F : BlockFrame}
def gaugeExponential {j p : ℕ} (ψ : Fin p → F.Site j → imaginaryQuaternions) (τ : Fin p → ℝ) :
    F.Site j → UnitQuaternion :=
  fun z => expUnit (∑ l, τ l • ψ l z)
def gaugeAlongMotionStatement : Prop :=
  ∀ (n : ℕ) (A : ℕ → ℝ) (B : ℝ), (∀ q, 0 ≤ A q) → 0 ≤ B → ∃ M : ℕ → ℝ, (∀ q, 0 ≤ M q) ∧
    ∀ (F : BlockFrame) (j p : ℕ) (W : F.GaugeField j) (α : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions)
      (ψ : Fin p → F.Site j → imaginaryQuaternions) (ω : F.Site j → Fin 4 → Fin p → ℝ), (∀ i, F.period j i ≠ 0) →
      (∀ x i, α 0 x i = 0) → (∀ x i, ContDiffAt ℝ n (fun τ => α τ x i) 0) →
      (∀ x i l, 0 ≤ ω x i l) → (∀ x i l, ω x i l ≤ 1) →
      (∀ (q : ℕ) (e : Fin q → Fin p) (x : F.Site j) (i : Fin 4) (l : Fin q), q ≤ n →
        ‖motionComponent α e x i‖ ≤ A q * ω x i (e l)) →
      (∀ x i l, ‖ψ l x‖ ≤ B * ω x i l ∧ ‖ψ l (x + unitStep j i)‖ ≤ B * ω x i l) →
      ∃ α' : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions, (∀ x i, α' 0 x i = 0) ∧
        (∀ x i, ContDiffAt ℝ n (fun τ => α' τ x i) 0) ∧
        (∀ᶠ τ in 𝓝 0, gaugeTransform (gaugeExponential ψ τ) (leftTranslate (α τ) W) = leftTranslate (α' τ) W) ∧
        (1 ≤ n → ∀ (l : Fin p) (x : F.Site j) (i : Fin 4), motionComponent α' (fun _ : Fin 1 => l) x i =
          motionComponent α (fun _ : Fin 1 => l) x i + ψ l x - adjointAction (W x i) (ψ l (x + unitStep j i))) ∧
        ∀ (q : ℕ) (e : Fin q → Fin p) (x : F.Site j) (i : Fin 4) (l : Fin q), q ≤ n →
          ‖motionComponent α' e x i‖ ≤ M q * ω x i (e l)
end YangMills.Construction.GaugeAlongMotion
end
