import YangMills.Construction.ReflectionPositivity.FactsOfTheCoveringMap
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
def axisSignFlip (μ : Fin 4) : PeriodicLattice.SignedFrame := (1, fun ν => if ν = μ then -1 else 1)
def euclidReflect (μ : Fin 4) (c : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  y - (2 * (y μ - c)) • PeriodicLattice.coordVec μ
theorem euclidReflect_eq_frameAffine (μ : Fin 4) (c : ℝ) :
    euclidReflect μ c =
      frameAffine (axisSignFlip μ) ((2 * c) • PeriodicLattice.coordVec μ) := by
  funext y ν
  by_cases hν : ν = μ
  · subst hν
    simp [euclidReflect, frameAffine, axisSignFlip, PeriodicLattice.SignedFrame.actOnVector,
      PeriodicLattice.coordVec]
    ring
  · simp [euclidReflect, frameAffine, axisSignFlip, PeriodicLattice.SignedFrame.actOnVector,
      PeriodicLattice.coordVec, hν]
structure CoordMirror where
  axis : Fin 4
  height : ℝ
namespace Ambient
variable (D : MirrorData)
def reflectAt (μ : Fin 4) (c : ℝ) : (E : Ambient) → E.Point D → E.Point D
  | .torus => D.descended (euclidReflect μ c)
  | .euclidean => euclidReflect μ c
def levelSet (μ : Fin 4) (c : ℝ) : (E : Ambient) → Set (E.Point D)
  | .torus => D.projection '' coordSet μ fun t => t = c
  | .euclidean => coordSet μ fun t => t = c
end Ambient
namespace CoordMirror
variable (D : MirrorData) (S : CoordMirror)
def carrier : (E : Ambient) → Set (E.Point D)
  | .torus => D.projection ''
      (coordSet S.axis (fun t => t = S.height) ∪
        coordSet S.axis fun t => t = S.height + D.side / 2)
  | .euclidean => coordSet S.axis fun t => t = S.height
def upperSide : (E : Ambient) → Set (E.Point D)
  | .torus => D.projection ''
      coordSet S.axis fun t => 0 < t - S.height ∧ t - S.height < D.side / 2
  | .euclidean => coordSet S.axis fun t => t > S.height
def lowerSide : (E : Ambient) → Set (E.Point D)
  | .torus => D.projection ''
      coordSet S.axis fun t => 0 < -(t - S.height) ∧ -(t - S.height) < D.side / 2
  | .euclidean => coordSet S.axis fun t => t < S.height
def reflect (E : Ambient) : E.Point D → E.Point D := Ambient.reflectAt D S.axis S.height E
def pullback {α : Type*} (E : Ambient) (f : E.Point D → α) : E.Point D → α :=
  f ∘ S.reflect D E
end CoordMirror
end YangMills.Construction.ReflectionPositivity.AxisMirror
end
