import YangMills.Construction.Lattice.CurvatureKernelGradient
import YangMills.Construction.LinearAlgebra.BivectorsReflectionsAngles
import Mathlib
set_option autoImplicit false
open Matrix YangMills.Construction.Exterior
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace AxisPlane
def IsDisjoint (P Q : AxisPlane) : Prop :=
  P.lower ≠ Q.lower ∧ P.lower ≠ Q.upper ∧ P.upper ≠ Q.lower ∧ P.upper ≠ Q.upper
instance (P Q : AxisPlane) : Decidable (IsDisjoint P Q) := by
  unfold IsDisjoint
  infer_instance
theorem existsUnique_isDisjoint (Q : AxisPlane) : ∃! P, IsDisjoint Q P := by
  have key : ∀ Q : AxisPlane, ∃ P, IsDisjoint Q P ∧
      ∀ R, IsDisjoint Q R → R.lower = P.lower ∧ R.upper = P.upper := by
    decide +kernel
  obtain ⟨P, hP, huniq⟩ := key Q
  exact ⟨P, hP, fun R hR => AxisPlane.ext (huniq R hR).1 (huniq R hR).2⟩
def opposite (Q : AxisPlane) : AxisPlane :=
  (existsUnique_isDisjoint Q).choose
theorem eq_opposite_of_isDisjoint {P Q : AxisPlane} (hPQ : IsDisjoint Q P) :
    P = opposite Q :=
  (existsUnique_isDisjoint Q).choose_spec.2 P hPQ
end AxisPlane
def bivectorComponent (ω : Bivector) (P : AxisPlane) : ℝ := ω.1 P.lower P.upper
def endEntry (S : Bivector →ₗ[ℝ] Bivector) (μ ν ρ σ : Fin 4) : ℝ :=
  inner ℝ (wedgeProd (Pi.single μ 1) (Pi.single ν 1)) (S (wedgeProd (Pi.single ρ 1) (Pi.single σ 1)))
def permSign4 (μ ν ρ σ : Fin 4) : ℤ :=
  if hinj : Function.Injective ![μ, ν, ρ, σ] then
    ((Equiv.Perm.sign (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)) : ℤˣ) : ℤ)
  else 0
def axisPlaneSign (P Q : AxisPlane) : ℤ := permSign4 P.lower P.upper Q.lower Q.upper
theorem axisPlaneSign_eq_zero_of_not_isDisjoint {P Q : AxisPlane} (hPQ : ¬P.IsDisjoint Q) :
    axisPlaneSign P Q = 0 := by
  revert P Q
  decide +kernel
def orthogonalBivectors (u : Fin 4 → ℝ) : Submodule ℝ Bivector :=
  Submodule.span ℝ {ω | ∃ v w : Fin 4 → ℝ, u ⬝ᵥ v = 0 ∧ u ⬝ᵥ w = 0 ∧ ω = wedgeProd v w}
end YangMills.Construction.PeriodicLattice
end
