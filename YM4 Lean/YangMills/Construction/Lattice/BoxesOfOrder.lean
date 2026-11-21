import YangMills.Construction.Lattice.SiteBoxes
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
noncomputable section
namespace PeriodicLattice
variable {L m : ℕ}
def coordCount {j : ℤ} (μ : Fin 4) (P : Set (Site L m j)) : ℕ∞ :=
  ((fun x : Site L m j => (x : FourTorus L m) μ) '' P).encard
def IsOrderBox (K j : ℕ) (P : Set (SiteAtLevel L m K j)) : Prop :=
  j ≤ K ∧ IsSiteBox (levelDepth K j) P ∧ ∀ μ, coordCount μ P ≤ 3
end PeriodicLattice
end
end YangMills.Construction
