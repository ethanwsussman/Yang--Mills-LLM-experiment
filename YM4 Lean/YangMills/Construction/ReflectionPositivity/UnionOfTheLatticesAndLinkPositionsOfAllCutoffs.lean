import YangMills.Construction.ReflectionPositivity.ReflectionsMirrorsAndSlabsAtOneCutoff
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.EveryCutoff
variable (s : Conventions.StandingParameters)
def mirrorDataAt (k : ℕ+) : CutoffMirrors.MirrorData where
  toStandingParameters := { s with K := k }
  coupling := 1
  coupling_pos := one_pos
  dir := 0
def meshAt (k : ℕ+) : ℝ := (mirrorDataAt s k).spacing
theorem meshAt_eq (k : ℕ+) : meshAt s k = (s.L : ℝ) ^ (-((k : ℕ) : ℤ)) := rfl
def sublatticeAt (k : ℕ+) : AddSubgroup s.Torus := (mirrorDataAt s k).latticeSubgroup
def unionOfSublattices : Set s.Torus := ⋃ k : ℕ+, (sublatticeAt s k : Set s.Torus)
def linkLevelsAt (k : ℕ+) : Set ℝ := {c | ∃ n : ℤ, c = meshAt s k * ((n : ℝ) + 1 / 2)}
def allLinkLevels : Set ℝ := ⋃ k : ℕ+, linkLevelsAt s k
end YangMills.Construction.ReflectionPositivity.EveryCutoff
end
