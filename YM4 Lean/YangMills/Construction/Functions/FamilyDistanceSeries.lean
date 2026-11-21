import YangMills.Construction.Functions.FamilyTopology
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilySeries
open FamilyTopology
def seriesTerm {X ι : Type} (f : ι → X → ℝ) (σ : ℕ+ → ι) (x x' : X) (s : ℕ+) : ℝ :=
  (2 : ℝ) ^ (-((s : ℕ) : ℤ)) * min 1 |f (σ s) x - f (σ s) x'|
def FamilySeriesTerms : Prop :=
  ∀ (X ι : Type) (f : ι → X → ℝ) (σ : ℕ+ → ι) (hσ : Function.Surjective σ) (x x' : X),
    (∀ s : ℕ+, seriesTerm f σ x x' s ∈ Set.Icc (0 : ℝ) ((2 : ℝ) ^ (-((s : ℕ) : ℤ)))) ∧
    HasSum (seriesTerm f σ x x') (familyDistance f σ hσ x x')
end YangMills.Construction.FamilySeries
