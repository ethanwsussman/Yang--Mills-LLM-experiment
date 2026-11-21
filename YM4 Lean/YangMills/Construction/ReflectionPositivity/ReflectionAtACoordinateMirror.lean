import YangMills.Construction.Lattice.EuclideanIsometries
import YangMills.Construction.ReflectionPositivity.ReflectionsHyperplanesMirrorsAndOpenSides
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace MirrorData
variable (D : MirrorData)
def residueClass (y : Fin 4 → ℝ) : Set (Fin 4 → ℝ) := {y' | y' - y ∈ intLattice D.side}
def IsInvolutiveIsometry (μ : Fin 4) (c : ℝ) : Prop :=
  InfiniteLattice.IsSpaceIsometry (euclidReflect μ c) ∧
    euclidReflect μ c ∘ euclidReflect μ c = id ∧
    (∀ y, ∃ y', euclidReflect μ c '' D.residueClass y = D.residueClass y') ∧
    PeriodicLattice.IsTorusIsometry (L := D.L) (m := D.m) (Ambient.reflectAt D μ c .torus) ∧
    Ambient.reflectAt D μ c .torus ∘ Ambient.reflectAt D μ c .torus = id ∧
    (Function.LeftInverse (euclidReflect μ c) (euclidReflect μ c) ∧
      Function.RightInverse (euclidReflect μ c) (euclidReflect μ c)) ∧
    Function.LeftInverse (Ambient.reflectAt D μ c .torus) (Ambient.reflectAt D μ c .torus) ∧
    Function.RightInverse (Ambient.reflectAt D μ c .torus) (Ambient.reflectAt D μ c .torus)
def FixedSetOfReflect (μ : Fin 4) (c : ℝ) : Prop :=
  {y | euclidReflect μ c y = y} = CoordMirror.carrier D ⟨μ, c⟩ .euclidean ∧
    CoordMirror.carrier D ⟨μ, c⟩ .euclidean = Ambient.levelSet D μ c .euclidean ∧
    {x | Ambient.reflectAt D μ c .torus x = x} = CoordMirror.carrier D ⟨μ, c⟩ .torus ∧
    CoordMirror.carrier D ⟨μ, c⟩ .torus =
      Ambient.levelSet D μ c .torus ∪ Ambient.levelSet D μ (c + D.side / 2) .torus ∧
    Disjoint (Ambient.levelSet D μ c .torus) (Ambient.levelSet D μ (c + D.side / 2) .torus)
def ReflectSwapsSides (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ E : Ambient,
    Ambient.reflectAt D μ c E '' CoordMirror.upperSide D ⟨μ, c⟩ E =
        CoordMirror.lowerSide D ⟨μ, c⟩ E ∧
      Ambient.reflectAt D μ c E '' CoordMirror.lowerSide D ⟨μ, c⟩ E =
        CoordMirror.upperSide D ⟨μ, c⟩ E
end MirrorData
def ReflectionProperties : Prop :=
  ∀ (D : MirrorData) (μ : Fin 4) (c : ℝ), D.IsInvolutiveIsometry μ c ∧
    D.FixedSetOfReflect μ c ∧ D.ReflectSwapsSides μ c
end YangMills.Construction.ReflectionPositivity.AxisMirror
