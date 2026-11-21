import YangMills.Construction.SpectralTheory.MatrixMeasuresAndCommutation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.SpectralProduct
open BorelSpectral
variable {n₁ n₂ : ℕ}
def leftCoords (y : (univ : Set (Fin (n₁ + n₂) → ℝ))) : (univ : Set (Fin n₁ → ℝ)) :=
  ⟨fun i => y.1 (Fin.castAdd n₂ i), mem_univ _⟩
def rightCoords (y : (univ : Set (Fin (n₁ + n₂) → ℝ))) : (univ : Set (Fin n₂ → ℝ)) :=
  ⟨fun j => y.1 (Fin.natAdd n₁ j), mem_univ _⟩
theorem measurable_leftCoords : Measurable (leftCoords (n₁ := n₁) (n₂ := n₂)) := by
  refine Measurable.subtype_mk (measurable_pi_iff.mpr fun i => ?_)
  exact (measurable_pi_apply (Fin.castAdd n₂ i)).comp measurable_subtype_coe
theorem measurable_rightCoords : Measurable (rightCoords (n₁ := n₁) (n₂ := n₂)) := by
  refine Measurable.subtype_mk (measurable_pi_iff.mpr fun j => ?_)
  exact (measurable_pi_apply (Fin.natAdd n₁ j)).comp measurable_subtype_coe
def boxSet (A : BorelSubsets (univ : Set (Fin n₁ → ℝ)))
    (B : BorelSubsets (univ : Set (Fin n₂ → ℝ))) :
    BorelSubsets (univ : Set (Fin (n₁ + n₂) → ℝ)) :=
  ⟨leftCoords ⁻¹' A.1 ∩ rightCoords ⁻¹' B.1,
    (measurable_leftCoords A.2).inter (measurable_rightCoords B.2)⟩
def IsProductMeasure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : SpectralMeasure (univ : Set (Fin (n₁ + n₂) → ℝ)) H)
    (E₁ : SpectralMeasure (univ : Set (Fin n₁ → ℝ)) H)
    (E₂ : SpectralMeasure (univ : Set (Fin n₂ → ℝ)) H) : Prop :=
  ∀ A B, E (boxSet A B) = E₁ A * E₂ B
def ProductTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n₁ n₂ : ℕ)
    (E₁ : SpectralMeasure (univ : Set (Fin n₁ → ℝ)) H)
    (E₂ : SpectralMeasure (univ : Set (Fin n₂ → ℝ)) H),
    E₁.Commutes E₂ →
      (∃! E : SpectralMeasure (univ : Set (Fin (n₁ + n₂) → ℝ)) H, IsProductMeasure E E₁ E₂) ∧
      ∀ E : SpectralMeasure (univ : Set (Fin (n₁ + n₂) → ℝ)) H, IsProductMeasure E E₁ E₂ →
        ∀ T : H →L[ℂ] H, SpectralMeasure.OpCommutes T E₁ →
          SpectralMeasure.OpCommutes T E₂ →
            SpectralMeasure.OpCommutes T E
end YangMills.Construction.SpectralProduct
