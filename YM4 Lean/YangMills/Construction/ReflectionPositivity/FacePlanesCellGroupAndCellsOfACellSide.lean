import YangMills.Construction.InfiniteLattice.RefinedLattices
import YangMills.Construction.Lattice.GridCellsAndFaceReflections
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.FaceReflections
open YangMills.Construction.InfiniteLattice (AmbientSpace)
variable (L K : ℕ) (a : ℝ)
def faceHyperplane (μ : Fin 4) (j : ℤ) : Set AmbientSpace :=
  {x | x μ = j * a - 1 / 2 * InfiniteLattice.refinedSpacing L K}
def reflect (μ : Fin 4) (j : ℤ) (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (x μ - j * a + 1 / 2 * InfiniteLattice.refinedSpacing L K)) •
    BoxTorus.basisVector μ
def reflectEquiv (μ : Fin 4) (j : ℤ) : AmbientSpace ≃ᵃ[ℝ] AmbientSpace :=
  AffineEquiv.mk' (reflect L K a μ j) (CellGrid.axisFlip μ) 0 fun x => by
    funext i
    by_cases h : i = μ
    · subst h
      simp [reflect, CellGrid.axisFlip_apply, CellGrid.flipDiag, BoxTorus.basisVector]
      ring
    · simp [reflect, CellGrid.axisFlip_apply, CellGrid.flipDiag,
        BoxTorus.basisVector, Function.update_of_ne h, Pi.single_eq_of_ne h]
def reflectionGroup : Subgroup (AmbientSpace ≃ᵃ[ℝ] AmbientSpace) :=
  Subgroup.closure (range fun p : Fin 4 × ℤ => reflectEquiv L K a p.1 p.2)
variable {L K a}
variable (L K a)
variable {L K}
end YangMills.Construction.FaceReflections
end
