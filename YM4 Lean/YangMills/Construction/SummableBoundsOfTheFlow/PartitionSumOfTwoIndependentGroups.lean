import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Cumulants
def CumulantOfIndependentGroupsZero : Prop :=
  ∀ (p : ℕ) (S : Finset (Fin p)) (f g : Finset (Fin p) → ℝ),
    S.Nonempty → Sᶜ.Nonempty → f ∅ = 1 → g ∅ = 1 →
    ∑ π : Finpartition (Finset.univ : Finset (Fin p)),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
        ∏ B ∈ π.parts, (f (B ∩ S) * g (B \ S)) = 0
end YangMills.Construction.Cumulants
