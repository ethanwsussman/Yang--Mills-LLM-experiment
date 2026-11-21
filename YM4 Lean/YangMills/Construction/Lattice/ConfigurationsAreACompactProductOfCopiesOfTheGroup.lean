import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def IsOrientationChoice (S : Set (Bond L m j)) : Prop :=
  (∀ b ∈ S, b.IsPositivelyOriented) ∧ ∀ b : Bond L m j, Xor (b ∈ S) (b.opposite ∈ S)
def GaugeFieldsCompactProduct.Statement : Prop :=
  ∀ (L m : ℕ) (j : ℤ), 0 < L → -(m : ℤ) ≤ j →
    Finite (Bond L m j) ∧
    IsCompact (compactGaugeFields L m j) ∧
    TopologicalSpace.MetrizableSpace (compactGaugeFields L m j) ∧
    BorelSpace (compactGaugeFields L m j) ∧
    ∃ S : Set (Bond L m j), IsOrientationChoice S ∧
      ∃ e : compactGaugeFields L m j ≃ₜ (S → Matrices.ComplexMatrix2.specialUnitary),
        (∀ (U : compactGaugeFields L m j) (b : S),
          (e U b : Matrices.ComplexMatrix2) = U.1 b) ∧
        Measurable e ∧ Measurable e.symm
end YangMills.Construction.PeriodicLattice
