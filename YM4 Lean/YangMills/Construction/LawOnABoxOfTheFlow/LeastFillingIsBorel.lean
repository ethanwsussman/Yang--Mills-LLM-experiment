import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BoxLaws
def LexLeastSectionMeasurable : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : ℕ)
    (K : Set (X × (Fin m → ℝ))), IsCompact K →
    ∃ s : X → Fin m → ℝ,
      (∀ x ∈ Prod.fst '' K, (x, s x) ∈ K ∧ ∀ y, (x, y) ∈ K → toLex (s x) ≤ toLex y) ∧
      Measurable fun x : (Prod.fst '' K : Set X) => s x
end YangMills.Construction.BoxLaws
end
