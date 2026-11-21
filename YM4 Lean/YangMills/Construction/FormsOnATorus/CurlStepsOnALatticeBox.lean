import YangMills.Construction.FormsOnATorus.LatticeFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
def curlDiffBoundStatement : Prop :=
  ∀ cK c C : ℝ, 0 < cK → 0 < c → 0 ≤ C → ∀ j : ℕ, ∃ κ : ℝ, 0 < κ ∧
    ∀ Q : IntBond → IntBond → ℝ, IsGradientBlindKernel cK c C Q →
    ∀ (v : IntBond → ℝ) (ρ r t q : ℕ) (W ε : ℝ), 1 ≤ t → q + t + (j + 4) * (2 * t + 2) ≤ r → 0 ≤ W → 0 ≤ ε →
      (∀ b, b ∉ bondCube ρ → v b = 0) → (∀ b, |v b| ≤ W) → (∀ b ∈ bondCube r, |kernelResidual Q v b| ≤ ε) →
      ∀ (l : List (Fin 4)), l.length = j → ∀ y ∈ siteCube q, ∀ i k : Fin 4, i < k →
        |plaquetteForwardDiffs l (intCurl v) (y, i, k)| ≤
          κ * (((t : ℝ) ^ (j + 2))⁻¹ * Real.sqrt (∑ p ∈ plaquetteCube r, intCurl v p ^ 2) +
            (t : ℝ) ^ 2 * Real.sqrt (energyStepError c C ρ r (j + 4) t W ε / (2 * cK)))
end YangMills.Construction.LimitForms
end
