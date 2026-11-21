import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongAFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def plaquetteBondList {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) : Fin 4 → F.Site j × Fin 4 :=
  ![(p.1, p.2.1), (p.1 + unitStep j p.2.1, p.2.2), (p.1 + unitStep j p.2.2, p.2.1), (p.1, p.2.2)]
def CutoffFlowSmallCurvature : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (X : F.GaugeField j) (A : F.Site j → Fin 4 → imaginaryQuaternions)
    (ch : F.Site j → Fin 4 → ℝ) (σ : ℝ),
    0 < σ → (∀ y i, 0 ≤ ch y i ∧ ch y i ≤ 1) →
    (∀ p : F.Site j × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      (∀ l, ch (plaquetteBondList p l).1 (plaquetteBondList p l).2 = 0) ∨
      ((∀ l, X (plaquetteBondList p l).1 (plaquetteBondList p l).2 =
          expUnit (A (plaquetteBondList p l).1 (plaquetteBondList p l).2)) ∧
        ∑ l, ‖A (plaquetteBondList p l).1 (plaquetteBondList p l).2‖ ≤ 1 ∧
        plaquetteDefect X p + (∑ l, |ch (plaquetteBondList p l).1 (plaquetteBondList p l).2 - ch p.1 p.2.1| *
            ‖A (plaquetteBondList p l).1 (plaquetteBondList p l).2‖) +
          4 * (∑ l, ‖A (plaquetteBondList p l).1 (plaquetteBondList p l).2‖) ^ 2 < σ)) →
    ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      IsSmallCurvature σ (expFlow (fun y i => ch y i • A y i) (uniformField F j) u)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
