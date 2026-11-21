import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.HessianOfTheMainTerm
variable {L m : ℕ} {j : ℤ}
def supLengthInMesh (u : Site L m j) : ℝ := TorusMetric.torusSupNorm (u : FourTorus L m) / meshSize L j
def sitesPerSide (L m : ℕ) (j : ℤ) : ℕ := 2 * L ^ ((m : ℤ) + j).toNat
def SiteLengthFacts : Prop :=
  ∀ (L m : ℕ) (j : ℤ), 1 < L → 0 ≤ (m : ℤ) + j →
    Finite (Site L m j) ∧
    (∀ x y : FourTorus L m, TorusMetric.torusSupNorm (x + y) ≤
      TorusMetric.torusSupNorm x + TorusMetric.torusSupNorm y) ∧
    (∀ x : FourTorus L m, TorusMetric.torusSupNorm (-x) = TorusMetric.torusSupNorm x) ∧
    (∀ x : FourTorus L m, 0 ≤ TorusMetric.torusSupNorm x) ∧
    (∀ (x : FourTorus L m) (κ : Fin 4), ‖x κ‖ ≤ TorusMetric.torusSupNorm x) ∧
    supLengthInMesh (0 : Site L m j) = 0 ∧
    (∀ u : Site L m j, 0 ≤ supLengthInMesh u) ∧ (∀ u : Site L m j, supLengthInMesh (-u) = supLengthInMesh u) ∧
    (∀ u v : Site L m j, supLengthInMesh (u + v) ≤ supLengthInMesh u + supLengthInMesh v) ∧
    (∀ u : Site L m j, ∃ n : Fin 4 → ℤ,
      (∀ μ, (u : FourTorus L m) μ = (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))) ∧
      supLengthInMesh u = Finset.univ.sup' Finset.univ_nonempty fun μ => |(n μ : ℝ)|)
end YangMills.Construction.HessianOfTheMainTerm
