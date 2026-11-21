import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def bondCochains (L m : ℕ) (j : ℤ) : Submodule ℝ (Bond L m j → ℝ) where
  carrier := {α | ∀ b, α b.opposite = -α b}
  add_mem' := by
    intro α β hα hβ b
    simp only [Pi.add_apply, hα b, hβ b]
    ring
  zero_mem' := by
    intro b
    simp
  smul_mem' := by
    intro r α hα b
    simp only [Pi.smul_apply, hα b, smul_eq_mul]
    ring
abbrev PlaquetteCochain (L m : ℕ) (j : ℤ) : Type := Plaquette L m j → ℝ
def bondCochainInner (α β : Bond L m j → ℝ) : ℝ :=
  ∑ᶠ b : {b : Bond L m j // b.IsPositivelyOriented}, α b * β b
def plaquetteInner (ω ω' : PlaquetteCochain L m j) : ℝ := ∑ᶠ p, ω p * ω' p
def pathCochainSum (α : Bond L m j → ℝ) (Γ : List (Bond L m j)) : ℝ := (Γ.map α).sum
def bondDifferential : bondCochains L m j →ₗ[ℝ] PlaquetteCochain L m j where
  toFun α p := pathCochainSum α p.boundaryBonds
  map_add' α β := by
    funext p
    simp only [pathCochainSum, Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' r α := by
    funext p
    simp only [pathCochainSum, Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def closedBondCochains (L m : ℕ) (j : ℤ) : Submodule ℝ (bondCochains L m j) :=
  LinearMap.ker bondDifferential
def closedBondCochainsOrth (L m : ℕ) (j : ℤ) : Set (bondCochains L m j) :=
  {α | ∀ h ∈ closedBondCochains L m j, bondCochainInner α.1 h.1 = 0}
def exactPlaquetteCochains (L m : ℕ) (j : ℤ) : Submodule ℝ (PlaquetteCochain L m j) :=
  LinearMap.range bondDifferential
end YangMills.Construction.PeriodicLattice
