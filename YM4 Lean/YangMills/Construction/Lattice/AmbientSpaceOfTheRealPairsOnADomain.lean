import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m : ℕ}
section Finite
variable [NeZero L]
instance instFiniteSite (j : ℤ) : Finite (Site L m j) :=
  SeparatedSequences.BaseParameters.site_finite (Nat.pos_of_ne_zero (NeZero.ne L)) m j
instance instFiniteBond (j : ℤ) : Finite (Bond L m j) :=
  Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun _ _ h =>
    Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
end Finite
end YangMills.Construction.PeriodicLattice
end
