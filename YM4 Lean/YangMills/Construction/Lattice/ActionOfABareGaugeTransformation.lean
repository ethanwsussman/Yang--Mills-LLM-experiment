import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ}
theorem coe_toSublattice_finest (hL : 0 < L) {i : ℕ} (x : SiteAtLevel L m K i) :
    ((x.toSublattice (levelDepth K 0) : SiteAtLevel L m K 0) : FourTorus L m) = x := by
  have hle : levelDepth K i ≤ levelDepth K 0 := by simp [levelDepth]
  exact Classical.epsilon_spec
    (p := fun y : Site L m (levelDepth K 0) => (y : FourTorus L m) = x)
    ⟨⟨x, sublattice_mono hL m hle x.2⟩, rfl⟩
end PeriodicLattice
end YangMills.Construction
