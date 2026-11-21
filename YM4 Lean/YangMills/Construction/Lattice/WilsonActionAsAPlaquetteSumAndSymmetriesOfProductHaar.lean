import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def wilsonPlaquetteFunction (V : Matrices.ComplexMatrix2) : ℝ :=
  1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace V).re
def WilsonActionPlaquetteSumAndHaarSymmetry : Prop :=
  ∀ (L m : ℕ) (j : ℤ), 1 < L → 0 < m → 0 ≤ j →
    (∀ g ∈ Matrices.ComplexMatrix2.specialUnitary,
      wilsonPlaquetteFunction g⁻¹ = wilsonPlaquetteFunction g ∧
      ∀ h ∈ Matrices.ComplexMatrix2.specialUnitary,
        wilsonPlaquetteFunction (h * g * h⁻¹) = wilsonPlaquetteFunction g) ∧
    Finite (Plaquette L m j) ∧
    (∀ U : Bond L m j → Matrices.ComplexMatrix2,
      wilsonAction U = ∑ᶠ p : Plaquette L m j, wilsonPlaquetteFunction (plaquetteHolonomy U p)) ∧
    ∀ τ : Bond L m j ≃ Bond L m j, (∀ b, τ b.opposite = (τ b).opposite) →
      (productHaarMeasure L m j).map (fun U => U ∘ τ) = productHaarMeasure L m j
end PeriodicLattice
end YangMills.Construction
