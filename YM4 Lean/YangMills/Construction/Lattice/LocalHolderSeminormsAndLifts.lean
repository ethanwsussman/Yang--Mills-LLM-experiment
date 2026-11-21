import YangMills.Construction.Lattice.InfiniteLatticeCalculus
import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {d N : ℕ}
def quotientMap (v : Fin d → ℝ) : Torus d N := fun μ => (v μ : AddCircle (N : ℝ))
def IsLiftOf (v : Fin d → ℝ) (u : Torus d N) : Prop := quotientMap v = u
theorem quotientMap_mem_sublattice (s : Mesh N) (x : InfiniteLattice.GridSite d s.h) :
    (quotientMap (x : Fin d → ℝ) : Torus d N) ∈ gridSubgroup d s := by
  have hx : ∃ n : Fin d → ℤ, ∀ μ, (x : Fin d → ℝ) μ = (n μ : ℝ) * s.h := x.2
  obtain ⟨n, hn⟩ := hx
  intro μ _
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n μ, ?_⟩
  simp only [quotientMap, hn μ]
  rw [← zsmul_eq_mul, AddCircle.coe_zsmul]
def quotientSite (s : Mesh N) (x : InfiniteLattice.GridSite d s.h) : GridPoint d s :=
  ⟨quotientMap (x : Fin d → ℝ), quotientMap_mem_sublattice s x⟩
def pullbackToGrid {s : Mesh N} (f : SiteFun d s) : InfiniteLattice.GridSite d s.h → ℝ :=
  fun x => f (quotientSite s x)
end YangMills.Construction.PeriodicLattice
