import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Estimates
variable {F : BlockFrame}
def mixedDerivAlong {j i : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (A : Fin i → F.Site j → Fin 4 → imaginaryQuaternions) : ℝ :=
  iteratedFDeriv ℝ i (fun τ : Fin i → ℝ => G (leftTranslate (fun x b => ∑ l, τ l • A l x b) W)) 0
    fun l => Pi.single l 1
def motionComponent {j p r : ℕ} (α : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions) (e : Fin r → Fin p) :
    F.Site j → Fin 4 → imaginaryQuaternions :=
  fun x b => iteratedFDeriv ℝ r (fun τ => α τ x b) 0 fun l => Pi.single (e l) 1
def FaaDiBrunoAlongMotion : Prop :=
  ∀ (F : BlockFrame) (j p : ℕ) (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (α : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions), (∀ i, F.period j i ≠ 0) →
    (∀ (q : ℕ) (c : Fin q → F.Site j × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ p (fun τ : Fin q → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) →
    (∀ x b, ContDiffAt ℝ p (fun τ => α τ x b) 0) → (∀ x b, α 0 x b = 0) →
    ContDiffAt ℝ p (fun τ => G (leftTranslate (α τ) W)) 0 ∧
      iteratedFDeriv ℝ p (fun τ => G (leftTranslate (α τ) W)) 0 (fun l => Pi.single l 1) =
        ∑ c : OrderedFinpartition p, mixedDerivAlong G W fun m => motionComponent α (c.emb m)
def MixedDerivBound : Prop :=
  ∀ (F : BlockFrame) (j i : ℕ) (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (A : Fin i → F.Site j → Fin 4 → imaginaryQuaternions)
    (T : Finset (F.Site j × Fin 4)) (B : (Fin i → F.Site j × Fin 4) → ℝ), (∀ l, F.period j l ≠ 0) →
    (∀ b, b ∈ T) →
    (∀ (q : ℕ) (c : Fin q → F.Site j × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ i (fun τ : Fin q → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) →
    (∀ (b : Fin i → F.Site j × Fin 4) (X : Fin i → imaginaryQuaternions), AreUnitVectors X →
      |bondDeriv G W b X| ≤ B b) →
    |mixedDerivAlong G W A| ≤
      ∑ b ∈ Fintype.piFinset fun _ : Fin i => T, B b * ∏ l, ‖A l (b l).1 (b l).2‖
def expansionAlongMotionStatement : Prop := FaaDiBrunoAlongMotion ∧ MixedDerivBound
end Estimates
end YangMills.Construction
end
