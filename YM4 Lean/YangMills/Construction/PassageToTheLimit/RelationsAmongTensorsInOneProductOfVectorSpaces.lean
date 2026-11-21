import YangMills.Construction.PassageToTheLimit.SeparatedTuplesMultilinearFunctionalsCentredFunctionalTensors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitSpaces
def TensorRelationsTransfer : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (q : ℕ), 1 ≤ q →
    ∀ (V : Fin q → Submodule ℝ (E.Carrier s → ℝ)) (Φ : MultilinearMap ℝ (fun k => V k) ℝ)
      (ι : Type) [Fintype ι] (a : ι → ℝ) (g : (i : ι) → (k : Fin q) → V k),
      (∀ x : Fin q → E.Carrier s,
        ∑ i, a i * E.tensorProd s (fun k => (g i k : E.Carrier s → ℝ)) x = 0) →
      ∑ i, a i * Φ (g i) = 0
end YangMills.Construction.LimitSpaces
end
