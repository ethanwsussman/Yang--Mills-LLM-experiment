import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def topVariationFieldDecayStatement : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ (F : BlockFrame) (s a ρA r CT : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions)
    (K : ℕ → ℝ) (b : F.Site F.depth × Fin 4) (c : F.Site F.top × Fin 4) (X u : imaginaryQuaternions) (k : ℕ)
    (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions),
    (∀ i, F.period F.top i ≠ 0) → 0 ≤ r → (∀ k, 0 ≤ K k) → 0 ≤ CT →
    (∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th w) →
    (∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 2 → ‖iteratedFDeriv ℝ j Th w‖ ≤ CT) →
    IsBondAnalyticAt (interpolatedFrame s a ρA m b) V →
    (∀ (i : ℕ) (cs : Fin i → F.Site F.top × Fin 4) (Xs : Fin i → imaginaryQuaternions), 1 ≤ i → AreUnitVectors Xs →
      ‖bondDeriv (interpolatedFrame s a ρA m b) V cs Xs‖ ≤ K i * Real.exp (-(r * bondListDistance (enclosingCell b.1) cs))) →
    ‖interpolatedFrame s a ρA m b V + u‖ ≤ 1 → ‖X‖ = 1 → k ≤ 2 → AreUnitVectors X' →
    ‖bondDeriv (topVariationField (fun w X => Th w X) s a ρA m c X b u) V c' X'‖ ≤
      (M * (K 1 + K 2 + K 3) + CT * (1 + K 1 + K 1 ^ 2 + K 2)) *
        Real.exp (-(r * bondListDistance (enclosingCell b.1) (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4)))
end Interpolation
end YangMills.Construction
end
