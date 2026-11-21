import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
def topVariationCoords (Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions)
    (s a ρA : ℝ) (m : ℕ) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions)
    (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) (v : BondVector) : BondVector :=
  imaginaryCoords (topVariationField (fun w X' => Th w X') s a ρA m c X b (toImaginary v) V)
def variationFieldConstant (M CT : ℝ) (K : ℕ → ℝ) : ℝ :=
  2 * M * (K 1 + K 2 + K 3) + CT * (1 + K 1 + K 1 ^ 2 + K 2)
def TopVariationCoordsSmooth : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ (F : BlockFrame) (s a ρA r CT : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions)
    (K : ℕ → ℝ) (b : F.Site F.depth × Fin 4) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (v : BondVector),
    (∀ i, F.period F.top i ≠ 0) → 0 ≤ r → (∀ k, 0 ≤ K k) → 0 ≤ CT →
    (∀ w : imaginaryQuaternions, ‖w‖ < Real.pi → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Th w) →
    (∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 3 → ‖iteratedFDeriv ℝ j Th w‖ ≤ CT) →
    IsBondAnalyticAt (interpolatedFrame s a ρA m b) V →
    (∀ (i : ℕ) (cs : Fin i → F.Site F.top × Fin 4) (Xs : Fin i → imaginaryQuaternions), 1 ≤ i → AreUnitVectors Xs →
      ‖bondDeriv (interpolatedFrame s a ρA m b) V cs Xs‖ ≤
        K i * Real.exp (-(r * bondListDistance (enclosingCell b.1) cs))) →
    ‖interpolatedFrame s a ρA m b V‖ + ‖v‖ < 1 → ‖X‖ = 1 →
    (∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions), k ≤ 2 → AreUnitVectors X' →
      ContDiffAt ℝ (k : WithTop ℕ∞)
        (fun τ : Fin k → ℝ => topVariationCoords Th s a ρA m c X b (leftTranslate (ColdStepAtMirrorFrames.bondSpread c' X' τ) V) v) 0 ∧
      ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
        (fun v' => bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v') V c' X') v ∧
      ‖bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v) V c' X'‖ ≤ variationFieldConstant M CT K *
        Real.exp (-(r * bondListDistance (enclosingCell b.1) (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4))) ∧
      ‖fderiv ℝ (fun v' => bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v') V c' X') v‖ ≤
        variationFieldConstant M CT K *
          Real.exp (-(r * bondListDistance (enclosingCell b.1) (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4)))) ∧
    ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (topVariationCoords Th s a ρA m c X b V) v ∧
    ∀ e e' : BondVector, ‖fderiv ℝ (fun v' => fderiv ℝ (topVariationCoords Th s a ρA m c X b V) v' e') v e‖ ≤
      CT * Real.exp (-(r * cellSupDist (enclosingCell b.1) c.1)) * ‖e‖ * ‖e'‖
end YangMills.Construction.Interpolation
end
