import YangMills.Construction.ForwardTube.RotatedDirectionsAndSeparatedSets
import YangMills.Construction.Rotation.LabelledPointConfigurations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RealPlane
variable {n : ℕ}
def openingAngles : Set ℝ := Set.Ioo 0 (Real.pi / 4)
def coneSector (α : openingAngles) : Set RealPlane :=
  {v | v ≠ 0 ∧ |Complex.arg (ForwardTube.lightConePlus (ForwardTube.embedPlane v))| < α}
def pencilSet (α : openingAngles) (n : ℕ) : Set (Fin n → RealPlane) :=
  {x | ∀ i, successiveDifferences x i ∈ coneSector α}
def minGapLength (hn : 2 ≤ n) (x : Fin n → RealPlane) : ℝ :=
  Finset.univ.inf' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun i => ‖successiveDifferences x i‖
end YangMills.Construction.RealPlane
end
