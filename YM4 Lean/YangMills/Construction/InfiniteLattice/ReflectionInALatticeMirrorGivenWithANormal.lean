import YangMills.Construction.InfiniteLattice.LatticeMirrorsGivenWithANormal
import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
theorem euclidNorm_sq_eq_dotProduct (x : Point) : euclidNorm x ^ 2 = x ⬝ᵥ x := by
  have hx : 0 ≤ euclidDot x x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  rw [euclidNorm, ← Real.sqrt_eq_rpow, Real.sq_sqrt hx]
  rfl
namespace NormalHyperplane
open YangMills.Construction.InfiniteLattice (LatticeSymmetry hyperplaneReflect)
variable {a : ℝ} (H : NormalHyperplane)
theorem reflect_eq_hyperplaneReflect : H.reflect = hyperplaneReflect H.normal H.level := by
  funext x
  simp only [reflect, hyperplaneReflect, euclidNorm_sq_eq_dotProduct]
  rfl
def toMirrorPair {H : NormalHyperplane} (hH : H.IsLatticeMirror a) :
    ReflectionPositivity.MirrorHyperplanes.MirrorPair a where
  normal := H.normal
  height := H.level
  admissible := by
    rcases H.normal_valid with h | h
    · exact Or.inl ⟨h, hH.1 h⟩
    · exact Or.inr ⟨h, hH.2 h⟩
def reflectSymmetry {H : NormalHyperplane} (hH : H.IsLatticeMirror a) :
    LatticeSymmetry a where
  toFun := H.reflect
  preservesDist := by
    rw [reflect_eq_hyperplaneReflect]
    exact (toMirrorPair hH).reflect.preservesDist
  image_eq := by
    rw [reflect_eq_hyperplaneReflect]
    exact (toMirrorPair hH).reflect.image_eq
end NormalHyperplane
end LatticeConventions
end YangMills.Construction
end
