import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def SiteAndPlaquetteCounts : Prop :=
  ∀ (L m : ℕ) (j : ℤ), 0 < L → -(m : ℤ) ≤ j →
    torusSide L m / meshSize L j = ((2 * L ^ ((m : ℤ) + j).toNat : ℕ) : ℝ) ∧
    Nat.card {t : AddCircle (torusSide L m) //
        ∃ n : ℤ, t = (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))} =
      2 * L ^ ((m : ℤ) + j).toNat ∧
    Nat.card (Site L m j) = (2 * L ^ ((m : ℤ) + j).toNat) ^ 4 ∧
    Nat.card (Plaquette L m j) = 6 * (2 * L ^ ((m : ℤ) + j).toNat) ^ 4 ∧
    (Odd L → (fun x => x + centerDiagonalPoint L m) '' dualLatticePoints L m j = sublattice L m j) ∧
    (1 < L → 0 < (m : ℤ) + j →
      Finite (PositivelyOrientedBond L m j) ∧
      Topology.IsEmbedding
        (gaugeFieldOfPositive :
          (PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) → _) ∧
      range (gaugeFieldOfPositive :
          (PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) → _) =
        compactGaugeFields L m j ∧
      IsCompact (compactGaugeFields L m j) ∧
      TopologicalSpace.MetrizableSpace (compactGaugeFields L m j))
end PeriodicLattice
end YangMills.Construction
