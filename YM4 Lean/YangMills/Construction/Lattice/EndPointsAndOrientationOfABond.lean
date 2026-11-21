import YangMills.Construction.Lattice.ConsistencyOfLiftsAndAveragesSetting
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Conventions.StandingParameters
def signedLatticeStep (s : StandingParameters) (k : ℕ) (σ : ℝ) (μ : Fin 4) : Fin 4 → ℝ :=
  (σ * PeriodicLattice.meshSize s.L (PeriodicLattice.levelDepth s.K k)) •
    PeriodicLattice.coordVec μ
def HasSignAndAxis (s : StandingParameters) {k : ℕ} (c : s.BondAt k) (σ : ℝ) (μ : Fin 4) :
    Prop :=
  (σ = 1 ∨ σ = -1) ∧
    (c.target : s.Torus) - (c.source : s.Torus) = s.pointClass (s.signedLatticeStep k σ μ)
end Conventions.StandingParameters
namespace PeriodicLattice
open Conventions
def BondEndpointsOrientation.Statement : Prop :=
  ∀ (s : StandingParameters) (k : ℕ), k ≤ (s.K : ℕ) →
    (torusSide s.L s.m = sideInLevelUnits s.L s.m s.K k * meshSize s.L (levelDepth s.K k) ∧
      2 * (s.L : ℝ) ≤ sideInLevelUnits s.L s.m s.K k ∧ (6 : ℝ) ≤ 2 * (s.L : ℝ) ∧
      2 < sideInLevelUnits s.L s.m s.K k) ∧
    (∀ (σ : ℝ) (μ : Fin 4), (σ = 1 ∨ σ = -1) →
      s.pointClass (s.signedLatticeStep k σ μ) ≠ s.pointClass 0) ∧
    (∀ (σ σ' : ℝ) (μ μ' : Fin 4), (σ = 1 ∨ σ = -1) → (σ' = 1 ∨ σ' = -1) →
      s.pointClass (s.signedLatticeStep k σ μ) = s.pointClass (s.signedLatticeStep k σ' μ') →
        σ = σ' ∧ μ = μ') ∧
    ∀ c : s.BondAt k,
      (∃! p : ℝ × Fin 4, s.HasSignAndAxis c p.1 p.2) ∧
      c.source ≠ c.target ∧ c.opposite ≠ c ∧ c.opposite.opposite = c ∧
      (∀ (σ : ℝ) (μ : Fin 4), s.HasSignAndAxis c σ μ →
        (∀ (σ' : ℝ) (μ' : Fin 4), s.HasSignAndAxis c.opposite σ' μ' ↔ σ' = -σ ∧ μ' = μ) ∧
        (c.IsPositivelyOriented ↔ σ = 1) ∧ (c.opposite.IsPositivelyOriented ↔ σ = -1)) ∧
      Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented
end PeriodicLattice
end YangMills.Construction
end
