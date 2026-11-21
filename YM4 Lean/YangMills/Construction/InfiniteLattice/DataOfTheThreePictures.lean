import YangMills.Construction.InfiniteLattice.LatticeMirrorsGivenWithANormal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
structure ReflectionPictureData (ι : Type) where
  plane : NormalHyperplane
  normalStep : Point
  midPlane : NormalHyperplane
  tangentStep : ι → Point
def NormalHyperplane.diagonal (μ κ : Direction) (hne : μ ≠ κ) (c : ℝ) :
    NormalHyperplane :=
  ⟨basisVector μ + basisVector κ, c, Or.inr ⟨μ, κ, hne, Or.inl rfl⟩⟩
def linkPicture (a : Spacing) (μ : Direction) : ReflectionPictureData {l : Direction // l ≠ μ} where
  plane := NormalHyperplane.axial μ (-((a : ℝ) / 2))
  normalStep := (a : ℝ) • basisVector μ
  midPlane := NormalHyperplane.axial μ 0
  tangentStep l := (a : ℝ) • basisVector l.1
def sitePicture (a : Spacing) (μ : Direction) : ReflectionPictureData {l : Direction // l ≠ μ} where
  plane := NormalHyperplane.axial μ 0
  normalStep := (a : ℝ) • basisVector μ
  midPlane := NormalHyperplane.axial μ ((a : ℝ) / 2)
  tangentStep l := (a : ℝ) • basisVector l.1
def diagonalPicture (a : Spacing) (μ κ : Direction) (hne : μ ≠ κ) (c : ℝ)
    (_hc : ∃ q : ℤ, c = (q : ℝ) * (a : ℝ)) : ReflectionPictureData Unit where
  plane := NormalHyperplane.diagonal μ κ hne c
  normalStep := (a : ℝ) • (basisVector μ + basisVector κ)
  midPlane := NormalHyperplane.diagonal μ κ hne (c + (a : ℝ))
  tangentStep _ := (a : ℝ) • (basisVector μ - basisVector κ)
theorem timeAxis_ne_toDirection (j : SpatialDirection) : timeAxis ≠ j.toDirection := by
  fin_cases j <;> decide
end LatticeConventions
end YangMills.Construction
end
