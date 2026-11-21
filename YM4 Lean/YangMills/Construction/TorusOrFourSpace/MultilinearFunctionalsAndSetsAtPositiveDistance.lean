import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (P : PeriodicSpace.Params) (Y : PeriodicSpace.Kind)
def IsMultilinearOn {n : ℕ} (K : Set (FnTuple P Y n)) (Ψ : K → ℝ) : Prop :=
  ∀ (i : Fin n) (h h' : K), (∀ l, l ≠ i → h.1 l = h'.1 l) →
    (∀ hAdd : Function.update h.1 i (h.1 i + h'.1 i) ∈ K, Ψ ⟨_, hAdd⟩ = Ψ h + Ψ h') ∧
      ∀ (c : ℝ) (hSmul : Function.update h.1 i (c • h.1 i) ∈ K),
        Ψ ⟨_, hSmul⟩ = c * Ψ h
def PairwisePositiveSetDist {n : ℕ} (A : Fin n → Set (Y.Pt P)) : Prop :=
  ∀ l l', l ≠ l' → 0 < setInfDist P Y (A l) (A l')
end YangMills.Construction.PeriodicSpace.Kind
