import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
open Classical in
def extendByZero {j : ℕ} {B : Finset (F.Site j × Fin 4)} (A : ↥B → imaginaryQuaternions) :
    F.Site j → Fin 4 → imaginaryQuaternions :=
  fun y i => if h : (y, i) ∈ B then A ⟨(y, i), h⟩ else 0
def formComposition {E : Type} {j : ℕ} (B : Finset (F.Site j × Fin 4)) (G : F.GaugeField j → E)
    (W : F.GaugeField j) (A : ↥B → imaginaryQuaternions) : E :=
  G (leftTranslate (extendByZero A) W)
open Classical in
def singleBondForm {j : ℕ} {B : Finset (F.Site j × Fin 4)} (b : ↥B) (X : imaginaryQuaternions) :
    ↥B → imaginaryQuaternions := Pi.single b X
def FormCompositionJet : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : BlockFrame) (j : ℕ)
    (B : Finset (F.Site j × Fin 4)) (G : F.GaugeField j → E) (W : F.GaugeField j),
    ContDiffThreeAlongBonds G W →
    ContDiffAt ℝ 3 (formComposition B G W) 0 ∧
    (∀ (k : ℕ) (c : Fin k → ↥B) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      iteratedFDeriv ℝ k (formComposition B G W) 0 (fun l => singleBondForm (c l) (X l)) =
        bondDeriv G W (fun l => (c l).1) X) ∧
    ∀ (k : ℕ) (e : (Fin k → ↥B) → ℝ), k ≤ 3 → (∀ c, 0 ≤ e c) →
      (∀ (c : Fin k → ↥B) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
        ‖bondDeriv G W (fun l => (c l).1) X‖ ≤ e c) →
      ∀ Z : Fin k → ↥B → imaginaryQuaternions,
        ‖iteratedFDeriv ℝ k (formComposition B G W) 0 Z‖ ≤ ∑ c : Fin k → ↥B, e c * ∏ l, ‖Z l (c l)‖
end YangMills.Construction.ColdStepAtMirrorFrames
end
