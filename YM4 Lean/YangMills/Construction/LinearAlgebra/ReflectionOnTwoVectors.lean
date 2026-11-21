import YangMills.Construction.Lattice.AxisBivectorBasis
import YangMills.Construction.LinearAlgebra.SignsOfCoordinatePlanesAndEntriesOfTwoVectors
import Mathlib
set_option autoImplicit false
open Matrix YangMills.Construction.TorusMetric YangMills.Construction.Exterior
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def kroneckerReal (μ ν : Fin 4) : ℝ := if μ = ν then 1 else 0
def householderMinorBracket (u : Fin 4 → ℝ) (μ ν ρ σ : Fin 4) : ℝ :=
  kroneckerReal μ ρ * u ν * u σ + kroneckerReal ν σ * u μ * u ρ -
    kroneckerReal μ σ * u ν * u ρ - kroneckerReal ν ρ * u μ * u σ
def HouseholderOnBivectorsFacts : Prop :=
  ∀ u : Fin 4 → ℝ, euclidNormVec u = 1 →
    ((householder u)ᵀ = householder u ∧
      householder u * householder u = 1 ∧
      householder u ∈ Matrix.orthogonalGroup (Fin 4) ℝ ∧
      householder u *ᵥ u = -u ∧
      (∀ v : Fin 4 → ℝ, u ⬝ᵥ v = 0 → householder u *ᵥ v = v) ∧
      ((householder u).charpoly.map (algebraMap ℝ ℂ)).roots = {-1, 1, 1, 1} ∧
      (householder u).det = -1 ∧
      householder (-u) = householder u) ∧
    (Module.finrank ℝ (wedgeRange u) = 3 ∧
      IsCompl (wedgeRange u) (orthogonalBivectors u) ∧
      (wedgeRange u).IsOrtho (orthogonalBivectors u)) ∧
    (exteriorSq (householder u) = LinearMap.id - (2 : ℝ) • wedgeRangeProj u ∧
      wedgeRangeProj u + hodge ∘ₗ wedgeRangeProj u ∘ₗ hodge = LinearMap.id ∧
      hodge ∘ₗ exteriorSq (householder u) ∘ₗ hodge =
        -exteriorSq (householder u)) ∧
    (IsSelfAdjointMap (exteriorSq (householder u)) ∧
      LinearMap.adjoint (exteriorSq (householder u)) ∘ₗ exteriorSq (householder u) =
        LinearMap.id ∧
      exteriorSq (householder u) ∘ₗ exteriorSq (householder u) = LinearMap.id ∧
      bivectorTrace (exteriorSq (householder u)) = 0) ∧
    ((∀ μ ρ : Fin 4, householder u μ ρ = kroneckerReal μ ρ - 2 * u μ * u ρ) ∧
      (∀ μ ν ρ σ : Fin 4,
        endEntry (exteriorSq (householder u)) μ ν ρ σ =
          householder u μ ρ * householder u ν σ - householder u μ σ * householder u ν ρ) ∧
      (∀ μ ν ρ σ : Fin 4,
        householder u μ ρ * householder u ν σ - householder u μ σ * householder u ν ρ =
          kroneckerReal μ ρ * kroneckerReal ν σ - kroneckerReal μ σ * kroneckerReal ν ρ -
            2 * householderMinorBracket u μ ν ρ σ) ∧
      (∀ μ ν ρ σ : Fin 4,
        endEntry (wedgeRangeProj u) μ ν ρ σ = householderMinorBracket u μ ν ρ σ) ∧
      (∀ ρ σ : Fin 4,
        wedgeRangeProj u (wedgeProd (Pi.single ρ 1) (Pi.single σ 1)) =
          wedgeProd u (u ρ • Pi.single σ 1 - u σ • Pi.single ρ 1)) ∧
      (∀ P Q : AxisPlane,
        |bivectorMatrixEntry (exteriorSq (householder u)) P Q| ≤ 1 ∧
          |bivectorMatrixEntry (wedgeRangeProj u) P Q| ≤ 1) ∧
      (∀ P Q : AxisPlane, P.IsDisjoint Q →
        bivectorMatrixEntry (exteriorSq (householder u)) P Q = 0 ∧
          bivectorMatrixEntry (wedgeRangeProj u) P Q = 0))
end YangMills.Construction.PeriodicLattice
end
