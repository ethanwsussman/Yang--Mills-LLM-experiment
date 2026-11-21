import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.Rotation.ProductFunctionsOnFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RealPlane
variable {n : ℕ}
def injectivePointTuples (n : ℕ) : Set (Fin n → RealPlane) :=
  TestFunctions.injectiveTuples RealPlane n
def mapPoints (a : RealPlane → RealPlane) (y : Fin n → RealPlane) :
    Fin n → RealPlane :=
  fun i => a (y i)
def permuteTuple {α : Type*} (σ : Equiv.Perm (Fin n)) (t : Fin n → α) : Fin n → α :=
  fun i => t (σ i)
def successiveDifferences (y : Fin n → RealPlane) : Fin (n - 1) → RealPlane :=
  fun i => y ⟨i + 1, by omega⟩ - y ⟨i, by omega⟩
@[ext]
structure LabelledPoints (n : ℕ) where
  points : Fin n → RealPlane
  labels : Fin n → RealPlane → ℝ
  labels_mem : ∀ i, labels i ∈ realLabels
end YangMills.Construction.RealPlane
end
