import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
def supportRadius (P : Params) (K : Kind) {n : ℕ} (f : FnTuple P K n) : ℝ≥0∞ :=
  max 1 (⨆ i, setDiam P K (supportQ P K (f i)))
def CompactSupportDiameters.FiniteDiameters : Prop :=
  ∀ (P : Params) (K : Kind),
    (∀ S : Set (K.Pt P), IsCompactQ P K S → setDiam P K S < ∞) ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ f ∈ sepC1Tuples P K n,
      supportRadius P K f ∈ Set.Ico (1 : ℝ≥0∞) ∞ ∧
      ∀ i, ∃ B : Set (K.Pt P),
        IsClosedBallWithRadius P K B (supportRadius P K f).toReal ∧ supportQ P K (f i) ⊆ B
end YangMills.Construction.PeriodicSpace
