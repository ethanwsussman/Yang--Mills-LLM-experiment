import YangMills.Construction.Lattice.InfiniteLatticeHolderSeminorms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace LatticePoisson
open InfiniteLattice
variable {d : ℕ} {ξ : ℝ}
def poissonSize (x₀ : GridSite d ξ) (r : ℝ) (u g : GridSite d ξ → ℝ) (F : GridField d ξ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (r ^ (-(d : ℝ) / 2)) * restrictedL2Norm (gridCube x₀ r) u +
    ENNReal.ofReal (r ^ 2) * supOver (gridCube x₀ r) g + ENNReal.ofReal r * fieldSupNorm F
def holderFactor (r α : ℝ) (x x' : GridSite d ξ) : ℝ :=
  (l1Length ((x - x' : GridSite d ξ) : Fin d → ℝ) / r) ^ α
def HasInteriorEstimates (d : ℕ) (C : ℝ) (COfExponent : ℝ → ℝ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∀ r : ℝ, 16 * ξ ≤ r → ∀ x₀ : GridSite d ξ,
    ∀ (u g : GridSite d ξ → ℝ) (F : GridField d ξ),
      (∀ x ∈ gridCube x₀ (r - ξ), laplacian u x = g x + gradientAdjoint F x) →
      ∀ x ∈ gridCube x₀ (r / 4), ∀ x' ∈ gridCube x₀ (r / 4), ∀ ν : Fin d,
        (ENNReal.ofReal |u x| ≤ ENNReal.ofReal C * poissonSize x₀ r u g F ∧
          ∀ α : ℝ, 0 < α → α < 1 →
            ENNReal.ofReal |u x - u x'| ≤
              ENNReal.ofReal (COfExponent α * holderFactor r α x x') *
                poissonSize x₀ r u g F) ∧
        (F = 0 →
          ENNReal.ofReal (r * |forwardDiff ν u x|) ≤
              ENNReal.ofReal C * poissonSize x₀ r u g F ∧
          ∀ α : ℝ, 0 < α → α < 1 →
            ENNReal.ofReal (r * |forwardDiff ν u x - forwardDiff ν u x'|) ≤
              ENNReal.ofReal (COfExponent α * holderFactor r α x x') *
                poissonSize x₀ r u g F)
def chosenInteriorConsts (d : ℕ) : ℝ × (ℝ → ℝ) :=
  Classical.epsilon fun p : ℝ × (ℝ → ℝ) => HasInteriorEstimates d p.1 p.2
def interiorConst (d : ℕ) : ℝ := (chosenInteriorConsts d).1
def interiorConstOfExponent (d : ℕ) (α : ℝ) : ℝ := (chosenInteriorConsts d).2 α
end LatticePoisson
namespace FreeKernel
open LatticePoisson
end FreeKernel
end YangMills.Construction
