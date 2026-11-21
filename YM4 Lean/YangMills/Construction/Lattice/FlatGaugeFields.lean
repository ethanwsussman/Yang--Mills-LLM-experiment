import YangMills.Construction.Lattice.BondsWithinSiteSets
import Mathlib
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def IsFlatOver (U : Bond L m j → Matrices.ComplexMatrix2) (Y : Set (Site L m j)) : Prop :=
  ∀ p : Plaquette L m j, p.LiesIn Y → plaquetteHolonomy U p = 1
theorem isFlatOver_congr {U U' : Bond L m j → Matrices.ComplexMatrix2} {Y : Set (Site L m j)}
    (h : ∀ b : Bond L m j, b.LiesIn Y → U b = U' b) : IsFlatOver U Y ↔ IsFlatOver U' Y := by
  have key : ∀ p : Plaquette L m j, p.LiesIn Y →
      plaquetteHolonomy U p = plaquetteHolonomy U' p := by
    intro p hp
    have hb : p.boundaryBonds.map U = p.boundaryBonds.map U' :=
      List.map_congr_left fun b hb => h b (Plaquette.LiesIn.boundaryBonds_liesIn hp b hb)
    simp only [plaquetteHolonomy, pathHolonomy, hb]
  exact forall₂_congr fun p hp => by rw [key p hp]
end YangMills.Construction.PeriodicLattice
