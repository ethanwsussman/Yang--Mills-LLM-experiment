import YangMills.Construction.ReflectionPositivity.PositionsAndKindsOfMirrors
import YangMills.Construction.ReflectionPositivity.ReflectionsHyperplanesMirrorsAndOpenSides
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.MirrorLevelKinds
def HalfSideOverMesh (D : MirrorData) : Prop :=
  D.side / (2 * D.mesh) = (D.halfSideCount : ℝ)
def HalfShiftPreservesLevels (D : MirrorData) : Prop :=
  ∀ c : ℝ,
    (c ∈ siteLevels D.mesh ↔ c + D.side / 2 ∈ siteLevels D.mesh) ∧
      (c ∈ linkLevels D.mesh ↔ c + D.side / 2 ∈ linkLevels D.mesh)
def MirrorIsTwoLevelSets (D : MirrorData) (μ : Fin 4) (c : ℝ) : Prop :=
  Ambient.levelSet D μ c .torus = D.projection '' coordSet μ (fun t => t = c) ∧
    Ambient.levelSet D μ (c + D.side / 2) .torus =
      D.projection '' coordSet μ (fun t => t = c + D.side / 2) ∧
    CoordMirror.carrier D ⟨μ, c⟩ .torus =
      Ambient.levelSet D μ c .torus ∪ Ambient.levelSet D μ (c + D.side / 2) .torus
def SameKindLevels (D : MirrorData) (c : ℝ) : Prop :=
  (c ∈ siteLevels D.mesh ∧ c + D.side / 2 ∈ siteLevels D.mesh) ∨
    (c ∈ linkLevels D.mesh ∧ c + D.side / 2 ∈ linkLevels D.mesh)
def Statement : Prop :=
  ∀ D : MirrorData,
    HalfSideOverMesh D ∧ HalfShiftPreservesLevels D ∧
      ∀ (μ : Fin 4) (c : ℝ), c ∈ halfLevels D.mesh →
        MirrorIsTwoLevelSets D μ c ∧ SameKindLevels D c
end YangMills.Construction.ReflectionPositivity.AxisMirror.MirrorLevelKinds
