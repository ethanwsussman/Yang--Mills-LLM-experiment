import YangMills.Construction.Lattice.OneScaleOperatorBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {d N : ℕ}
def poissonDataSize {s : Mesh N} (Y : Set (GridPoint d s)) (u g : SiteFun d s) (F : OneForm d s) : ℝ :=
  ‖SiteFun.restrictTo Y u‖ + SiteFun.maxNorm (SiteFun.restrictTo Y g) +
    MultiField.maxNorm (MultiField.restrictTo Y F)
def IsPoissonSolutionOn {s : Mesh N} (Y : Set (GridPoint d s)) (u g : SiteFun d s)
    (F : OneForm d s) : Prop :=
  ∀ z ∈ Y, discreteLaplacian s u z = g z + LinearMap.adjoint (discreteGrad s) F z
structure PoissonTwoSiteBounds {s : Mesh N} (c : ℝ) (cα : ℝ → ℝ) (cβε : ℝ → ℝ → ℝ)
    (Y : Set (GridPoint d s)) (x x' : GridPoint d s) (u g : SiteFun d s) (F : OneForm d s) : Prop where
  abs_le : |u x| ≤ c * poissonDataSize Y u g F
  abs_sub_le : ∀ α : ℝ, 0 < α → α < 1 →
    |u x - u x'| ≤ cα α * taxicabDist (x : Torus d N) x' ^ α * poissonDataSize Y u g F
  abs_deriv_le_of_zero : F = 0 → ∀ ν : Fin d,
    |forwardDiff s ν u x| ≤ c * poissonDataSize Y u g F
  abs_deriv_sub_le_of_zero : F = 0 → ∀ ν : Fin d, ∀ α : ℝ, 0 < α → α < 1 →
    |forwardDiff s ν u x - forwardDiff s ν u x'| ≤
      cα α * taxicabDist (x : Torus d N) x' ^ α * poissonDataSize Y u g F
  abs_deriv_le : ∀ β ε : ℝ, 0 ≤ β → 0 < ε → β + ε < 1 → ∀ ν : Fin d,
    |forwardDiff s ν u x| ≤
      cβε β ε * (poissonDataSize Y u g F + MultiField.holderSemi (β + ε) F)
  abs_deriv_sub_le : ∀ β ε : ℝ, 0 ≤ β → 0 < ε → β + ε < 1 → ∀ ν : Fin d,
    |forwardDiff s ν u x - forwardDiff s ν u x'| ≤
      cβε β ε * taxicabDist (x : Torus d N) x' ^ β *
        (poissonDataSize Y u g F + MultiField.holderSemi (β + ε) F)
end YangMills.Construction.PeriodicLattice
