import YangMills.Construction.Rotation.FourthFirstCoordinatePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RealPlane
open MeasureTheory
def complexProfiles : Set (RealPlane → ℂ) := {α | ContDiff ℝ 1 α ∧ HasCompactSupport α}
def realLabels : Set (RealPlane → ℝ) := {φ | ContDiff ℝ 1 φ ∧ HasCompactSupport φ}
def productFunction (α : RealPlane → ℂ) (φ : RealPlane → ℝ) (x : Fin 4 → ℝ) : ℂ :=
  α (planeComponent x) * (φ (orthogonalComponent x) : ℂ)
def IsProductFunction (f : (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ α ∈ complexProfiles, ∃ φ ∈ realLabels, f = productFunction α φ
def translateProfile (u : RealPlane) (α : RealPlane → ℂ) : RealPlane → ℂ :=
  fun y => α (y - u)
def profileL1Norm (α : RealPlane → ℂ) : ℝ := ∫ y, ‖α y‖
theorem integrable_of_mem_complexProfiles {α : RealPlane → ℂ} (hα : α ∈ complexProfiles) :
    Integrable α :=
  hα.1.continuous.integrable_of_hasCompactSupport hα.2
end YangMills.Construction.RealPlane
end
