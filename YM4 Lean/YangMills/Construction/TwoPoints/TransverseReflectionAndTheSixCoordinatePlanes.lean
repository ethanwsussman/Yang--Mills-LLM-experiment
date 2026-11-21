import YangMills.Construction.TwoPoints.KernelOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
def flipTransverse (x : AmbientSpace) : AmbientSpace := assemble (planeCoords x) (-transCoords x)
def IsAxisPermutation (w : Equiv.Perm AmbientSpace) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), ∀ i : Fin 4, w (coordVec i) = coordVec (σ i)
def KernelAxisSymmetries.Statement : Prop :=
  ∀ (τ : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ),
    IsDisjointForm S → IsAdmissibleForm τ S →
    ((∃ w ∈ hyperoctahedralPerms, ⇑w = flipTransverse) ∧
      ∀ y ζ : Fin 2 → ℝ, (y, ζ) ≠ 0 →
        ofCoords (formKernel S) y (-ζ) = ofCoords (formKernel S) y ζ) ∧
    (∀ μ ν : Fin 4, μ < ν → ∃ w ∈ hyperoctahedralPerms, IsAxisPermutation w ∧
        w '' coordPlane =
          (Submodule.span ℝ {coordVec μ, coordVec ν} : Submodule ℝ AmbientSpace)) ∧
    Set.ncard {p : Fin 4 × Fin 4 | p.1 < p.2} = 6
end YangMills.Construction.TwoPoints
end
