import YangMills.Construction.ReflectionPositivity.ReflectionsMirrorsAndSlabsAtOneCutoff
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.TorusMirrors
open YangMills.Construction.Conventions
open YangMills.Construction.ReflectionPositivity.CutoffMirrors
variable (s : StandingParameters)
def unitCouplingData (μ : Fin 4) : MirrorData :=
  { s with
    coupling := 1
    coupling_pos := one_pos
    dir := μ }
def reflectVec (μ : Fin 4) (c : ℝ) : (Fin 4 → ℝ) → Fin 4 → ℝ :=
  (unitCouplingData s μ).reflectVec c
def reflect (μ : Fin 4) (c : ℝ) : s.Torus → s.Torus := (unitCouplingData s μ).reflect c
def openSlab (μ : Fin 4) (c : ℝ) (σ : SlabSide) : Set s.Torus :=
  (unitCouplingData s μ).openSlab c σ
structure AxisLevel where
  axis : Fin 4
  level : ℝ
namespace AxisLevel
variable (M : AxisLevel)
def reflect : s.Torus → s.Torus := TorusMirrors.reflect s M.axis M.level
def openSlab (σ : SlabSide) : Set s.Torus := TorusMirrors.openSlab s M.axis M.level σ
end AxisLevel
end ReflectionPositivity.TorusMirrors
end YangMills.Construction
end
