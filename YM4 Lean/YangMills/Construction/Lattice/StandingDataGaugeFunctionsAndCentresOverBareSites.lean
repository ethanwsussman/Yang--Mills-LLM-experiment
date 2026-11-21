import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
theorem coe_toSublattice_of_coe_eq {j j' : ℤ} {y : Site L m j} {z : Site L m j'}
    (h : (z : FourTorus L m) = y) : ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : Site L m j' => (x : FourTorus L m) = y) ⟨z, h⟩
end YangMills.Construction.PeriodicLattice
end
