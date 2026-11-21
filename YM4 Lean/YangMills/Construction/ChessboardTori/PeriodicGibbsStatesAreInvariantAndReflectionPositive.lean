import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (IsSymmetricUnder IsReflectionPositiveAt LatticeMirror ReflectionClass
  LatticePoint AmbientSpace hypercubicGroup latticeMotions latticeMotionSymmetry)
def hypercubicAsMotion {a : ℝ} (w : hypercubicGroup) : latticeMotions a :=
  ⟨fun x => w.1 x, w.1, w.2, 0, zero_mem _, fun x => by simp⟩
def axialMirror {a : ℝ} (μ : Fin 4) (c : ℝ) (hc : ∃ q : ℤ, c = (q : ℝ) * (a / 2)) :
    LatticeMirror a :=
  ⟨ReflectionClass.axial μ, c, hc⟩
namespace PeriodicStateSymmetries
def Statement : Prop :=
  ∀ D : ChessboardSetup, ∀ ν ∈ D.periodicStates,
    (∀ v : LatticePoint D.mesh, IsSymmetricUnder ν (InfiniteLattice.shift v)) ∧
    (∀ (μ : Fin 4) (c : ℝ) (hc : ∃ q : ℤ, c = (q : ℝ) * (D.mesh / 2)),
      IsSymmetricUnder ν (axialMirror μ c hc).symmetry ∧
        IsReflectionPositiveAt ν (axialMirror μ c hc)) ∧
    (∀ (μ μ' : Fin 4) (c : ℝ), μ ≠ μ' → (∃ q : ℤ, c = (q : ℝ) * D.mesh) →
      ∀ P : LatticeMirror D.mesh,
        (P.plane = {x : AmbientSpace | x μ + x μ' = c} ∨
          P.plane = {x : AmbientSpace | x μ - x μ' = c}) →
        IsSymmetricUnder ν P.symmetry ∧ IsReflectionPositiveAt ν P) ∧
    ∀ w : hypercubicGroup,
      IsSymmetricUnder ν (latticeMotionSymmetry (hypercubicAsMotion w))
end PeriodicStateSymmetries
end YangMills.Construction.ChessboardTori
end
