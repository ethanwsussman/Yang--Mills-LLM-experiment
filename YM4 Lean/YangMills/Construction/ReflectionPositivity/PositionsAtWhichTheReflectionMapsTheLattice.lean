import YangMills.Construction.Lattice.EuclideanIsometries
import YangMills.Construction.ReflectionPositivity.PositionsAndKindsOfMirrors
import YangMills.Construction.ReflectionPositivity.ReflectionsHyperplanesMirrorsAndOpenSides
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.ReflectionLevels
def PreservesTorusLattice (D : MirrorData) (μ : Fin 4) (c : ℝ) : Prop :=
  (Ambient.reflectAt D μ c Ambient.torus : D.Torus → D.Torus) '' (D.torusSublattice : Set D.Torus) =
    (D.torusSublattice : Set D.Torus)
def PreservesFlatLattice (D : MirrorData) (μ : Fin 4) (c : ℝ) : Prop :=
  euclidReflect μ c '' (D.flatLattice : Set (Fin 4 → ℝ)) =
    (D.flatLattice : Set (Fin 4 → ℝ))
def IsTorusSymmetry (D : MirrorData) (μ : Fin 4) (c : ℝ) : Prop :=
  ∃ s : PeriodicLattice.TorusLatticeSymmetry D.L D.m D.K,
    s.toFun = (Ambient.reflectAt D μ c Ambient.torus : D.Torus → D.Torus)
def IsFlatSymmetry (D : MirrorData) (μ : Fin 4) (c : ℝ) : Prop :=
  ∃ s : InfiniteLattice.LatticeSymmetry D.mesh, s.toFun = euclidReflect μ c
def Characterization : Prop :=
  (∀ (D : MirrorData) (μ : Fin 4) (c : ℝ),
    (PreservesTorusLattice D μ c ↔ 2 * c ∈ siteLevels D.mesh) ∧
      (PreservesFlatLattice D μ c ↔ 2 * c ∈ siteLevels D.mesh) ∧
      (IsTorusSymmetry D μ c ↔ c ∈ halfLevels D.mesh) ∧
      (IsFlatSymmetry D μ c ↔ c ∈ halfLevels D.mesh)) ∧
    ∀ D : MirrorData, halfLevels D.mesh = siteLevels D.mesh ∪ linkLevels D.mesh ∧
      Disjoint (siteLevels D.mesh) (linkLevels D.mesh)
end YangMills.Construction.ReflectionPositivity.AxisMirror.ReflectionLevels
