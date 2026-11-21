import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ThirdDerivative
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
def ThirdDerivEqMeanOverOrders : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 3 → F.Site j × Fin 4)
    (X : Fin 3 → imaginaryQuaternions),
    (∀ i, F.period j i ≠ 0) →
    (∀ (q : ℕ) (c' : Fin q → F.Site j × Fin 4) (X' : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ 3 (fun τ : Fin q → ℝ => G (leftTranslate (bondSpread c' X' τ) W)) 0) →
    bondDeriv G W c X = (1 / 6) * ∑ π : Equiv.Perm (Fin 3),
      bondDeriv (fun W' => bondDeriv G W' (fun _ : Fin 1 => c (π 0)) (fun _ => X (π 0))) W
        ![c (π 1), c (π 2)] ![X (π 1), X (π 2)]
end YangMills.Construction.ThirdDerivative
end
