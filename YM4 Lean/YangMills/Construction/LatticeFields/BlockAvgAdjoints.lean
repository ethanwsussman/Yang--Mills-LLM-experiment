import YangMills.Construction.LatticeFields.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def BlockAvgAdjointFacts : Prop :=
  ∀ (d N : ℕ) [NeZero N] (κ : LatticeShape d),
    (∀ ω : ScalarField 1 κ, FieldSquareSummable ω →
      FieldSquareSummable (siteBlockAvgAdj (N := N) ω)) ∧
    (∀ B : LatticeOneForm 1 κ, FieldSquareSummable B →
      FieldSquareSummable (bondBlockAvgAdj (N := N) B)) ∧
    (∀ (f : ScalarField N κ) (ω : ScalarField 1 κ), FieldSquareSummable f →
      FieldSquareSummable ω →
      fieldInner (siteBlockAvg f) ω = fieldInner f (siteBlockAvgAdj ω)) ∧
    (∀ (A : LatticeOneForm N κ) (B : LatticeOneForm 1 κ), FieldSquareSummable A →
      FieldSquareSummable B →
      fieldInner (bondBlockAvg A) B = fieldInner A (bondBlockAvgAdj B))
end YangMills.Construction.LatticeFields
