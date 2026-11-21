import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def mixedPartial {r : ℕ} (p : (Fin 2 → ℝ) → imaginaryQuaternions) (e : Fin r → Fin 2) : imaginaryQuaternions :=
  iteratedFDeriv ℝ r p 0 fun i => Pi.single (e i) 1
def ConjugatedCurveDerivStability : Prop :=
  ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∀ (a a' u u' v : (Fin 2 → ℝ) → imaginaryQuaternions) (ε : ℝ), 0 ≤ ε →
    a 0 = 0 → a' 0 = 0 → v 0 = 0 → ContDiffAt ℝ 3 a 0 → ContDiffAt ℝ 3 a' 0 → ContDiffAt ℝ 3 u 0 →
    ContDiffAt ℝ 3 u' 0 → ContDiffAt ℝ 3 v 0 →
    (∀ᶠ t in 𝓝 (0 : Fin 2 → ℝ), expUnit (a t) = expUnit (u t) * expUnit (v t) * (expUnit (u 0))⁻¹) →
    (∀ᶠ t in 𝓝 (0 : Fin 2 → ℝ), expUnit (a' t) = expUnit (u' t) * expUnit (v t) * (expUnit (u' 0))⁻¹) →
    ‖u 0‖ ≤ 1 → ‖u' 0‖ ≤ 1 →
    (∀ i, ‖mixedPartial u ![i]‖ ≤ K) → (∀ i, ‖mixedPartial u' ![i]‖ ≤ K) → (∀ i, ‖mixedPartial v ![i]‖ ≤ K) →
    ‖mixedPartial u ![0, 1]‖ ≤ K → ‖mixedPartial u' ![0, 1]‖ ≤ K → ‖mixedPartial v ![0, 1]‖ ≤ K →
    ‖u 0 - u' 0‖ ≤ ε → (∀ i, ‖mixedPartial u ![i] - mixedPartial u' ![i]‖ ≤ ε) →
    ‖mixedPartial u ![0, 1] - mixedPartial u' ![0, 1]‖ ≤ ε →
    (∀ i, ‖mixedPartial a ![i] - mixedPartial a' ![i]‖ ≤ C * ε) ∧
      ‖mixedPartial a ![0, 1] - mixedPartial a' ![0, 1]‖ ≤ C * ε
end YangMills.Construction.ColdStepAtMirrorFrames
end
