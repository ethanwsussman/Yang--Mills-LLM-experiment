import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings RenormalizationStepParameters
variable {n : ℕ}
structure FourCornerStates {Ω : Type} (P P' : Finset (TorusSite n)) (W : Fin 2 → Fin 2 → TorusField n)
    (Y : Fin 2 → Fin 2 → Finset (TorusSite n)) (ω : ∀ i j, Y i j → Ω) : Prop where
  field_rest : ∀ i j i' j' (b : TorusBond n), b.1 ∉ P ∪ P' → b.1 + unitStep n b.2 ∉ P ∪ P' →
    W i j b.1 b.2 = W i' j' b.1 b.2
  field_first : ∀ i j j' (b : TorusBond n), (b.1 ∈ P ∨ b.1 + unitStep n b.2 ∈ P) →
    W i j b.1 b.2 = W i j' b.1 b.2
  field_second : ∀ i i' j (b : TorusBond n), (b.1 ∈ P' ∨ b.1 + unitStep n b.2 ∈ P') →
    W i j b.1 b.2 = W i' j b.1 b.2
  set_rest : ∀ i j i' j' z, z ∉ P ∪ P' → (z ∈ Y i j ↔ z ∈ Y i' j')
  set_first : ∀ i j j' z, z ∈ P → (z ∈ Y i j ↔ z ∈ Y i j')
  set_second : ∀ i i' j z, z ∈ P' → (z ∈ Y i j ↔ z ∈ Y i' j)
  label_rest : ∀ i j i' j' z (hz : z ∈ Y i j) (hz' : z ∈ Y i' j'), z ∉ P ∪ P' →
    ω i j ⟨z, hz⟩ = ω i' j' ⟨z, hz'⟩
  label_first : ∀ i j j' z (hz : z ∈ Y i j) (hz' : z ∈ Y i j'), z ∈ P → ω i j ⟨z, hz⟩ = ω i j' ⟨z, hz'⟩
  label_second : ∀ i i' j z (hz : z ∈ Y i j) (hz' : z ∈ Y i' j), z ∈ P' → ω i j ⟨z, hz⟩ = ω i' j ⟨z, hz'⟩
def FourCornerBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup,
    R.params = T.stepParameters y → y ≤ R.coupling → R.HasExpansions →
      ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (P P' : Finset (TorusSite n))
          (W : Fin 2 → Fin 2 → TorusField n) (Y : Fin 2 → Fin 2 → Finset (TorusSite n))
          (ω : ∀ i j, Y i j → R.labels.Ω) (d : ℕ),
          FourCornerStates P P' W Y ω → (∀ i j, IsHullState R.params R.range (W i j) (Y i j)) →
          (∀ z ∈ P, ∀ z' ∈ P', d ≤ supDist z z') → (R.range : ℝ) / 16 ≤ d →
          (∀ i j, ∀ X ∈ chainComponents R.range (Y i j),
            ¬ ((X ∩ thickening R.range P).Nonempty ∧ (X ∩ thickening R.range P').Nonempty)) →
          let prodΦ := fun i j => ∏ X ∈ chainComponents R.range (Y i j), R.clusterFactor n (W i j) (Y i j) (ω i j) X
          let Dij := fun i j => R.labelWeight n (W i j) (Y i j) (ω i j)
          prodΦ 1 1 * prodΦ 0 0 = prodΦ 1 0 * prodΦ 0 1 ∧
          (0 < Dij 1 1 * Dij 0 0 ↔ 0 < Dij 1 0 * Dij 0 1) ∧
          (0 < Dij 1 1 * Dij 0 0 →
            |Real.log (Dij 1 1 * Dij 0 0 / (Dij 1 0 * Dij 0 1))| ≤
              C * R.coupling * min (P.card : ℝ) P'.card * Real.exp (-(R.params.decayRate * d / 3)))
end YangMills.Construction.ClusterExpansionOfAStep
end
