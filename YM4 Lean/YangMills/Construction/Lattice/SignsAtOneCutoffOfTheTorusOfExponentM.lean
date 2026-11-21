import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import YangMills.Construction.ReflectionPositivity.ReflectionsMirrorsAndSlabsAtOneCutoff
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.CutoffNotation
variable (S : Conventions.StandingParameters)
@[reducible] def withCoupling (β : ℝ) (hβ : 0 < β) (μ : Fin 4) :
    ReflectionPositivity.CutoffMirrors.MirrorData :=
  { S with coupling := β, coupling_pos := hβ, dir := μ }
@[reducible] def defaultMirrorData : ReflectionPositivity.CutoffMirrors.MirrorData :=
  withCoupling S 1 one_pos 0
abbrev CutoffLink : Type := PeriodicLattice.Bond S.L S.m ((S.K : ℕ) : ℤ)
abbrev LinkField : Type := CutoffLink S → Matrices.ComplexMatrix2
def smearedObs {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : S.Torus → E) :
    LinkField S → E :=
  PeriodicLattice.observableExpanded f
section Numbers
variable {E : Type*} [NormedAddCommGroup E]
def lipConst (f : S.Torus → E) : ℝ≥0∞ := PeriodicLattice.torusLipConst f
def HasFiniteLip (f : S.Torus → E) : Prop := lipConst S f ≠ ∞
end Numbers
def reImPart (h : S.Torus → ℂ) (a : Fin 2) : S.Torus → ℝ :=
  fun x => if a = 0 then (h x).re else (h x).im
def markSum {B : Type*} [Fintype B] (ε : B → Fin 2) : ℕ := ∑ l, (ε l : ℕ)
end YangMills.Construction.CutoffNotation
end
