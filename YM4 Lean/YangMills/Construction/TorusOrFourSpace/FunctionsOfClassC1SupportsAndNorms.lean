import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.TorusOrFourSpace.SpaceQuotientMapAndDistance
import Mathlib
set_option autoImplicit false
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction
namespace PeriodicSpace
namespace Kind
variable (D : Params) (E : Kind)
def IsC1Fn (u : E.Pt D → ℝ) : Prop := TestFunctions.IsC1R4 (u ∘ E.quotMap D)
def IsSmoothFn (u : E.Pt D → ℝ) : Prop := ContDiff ℝ ∞ (u ∘ E.quotMap D)
def c1Set : Set (E.Pt D → ℝ) := {u | IsC1Fn D E u}
def smoothSet : Set (E.Pt D → ℝ) := {u | IsSmoothFn D E u}
def smoothUnitIntervalSet : Set (E.Pt D → ℝ) :=
  {u | u ∈ smoothSet D E ∧ ∀ y, u y ∈ Set.Icc (0 : ℝ) 1}
def partialDeriv (μ : Fin 4) (u : E.Pt D → ℝ) : E.Pt D → ℝ :=
  Classical.epsilon fun v =>
    v ∘ E.quotMap D = TestFunctions.partialDerivR4 μ (u ∘ E.quotMap D)
def gradVec (u : E.Pt D → ℝ) (y : E.Pt D) : Fin 4 → ℝ :=
  fun μ => partialDeriv D E μ u y
def gradNorm (u : E.Pt D → ℝ) (y : E.Pt D) : ℝ :=
  TorusMetric.euclidNormVec (gradVec D E u y)
def supportQ {Z : Type*} [Zero Z] (u : E.Pt D → Z) : Set (E.Pt D) :=
  closureQ D E {y | u y ≠ 0}
def supNormQ (v : E.Pt D → ℝ) : ℝ≥0∞ := ⨆ y, ENNReal.ofReal |v y|
def vecSupNormQ (v : E.Pt D → Fin 4 → ℝ) : ℝ≥0∞ :=
  ⨆ y, ENNReal.ofReal (TorusMetric.euclidNormVec (v y))
def IsLipschitzQ (u : E.Pt D → ℝ) : Prop := TestFunctions.IsLipschitzFor (quotDist D E) u
def lipConstQ (u : E.Pt D → ℝ) : ℝ :=
  TestFunctions.bestLipschitzConstant (quotDist D E) u
def sharpNormQ (u : E.Pt D → ℝ) : ℝ≥0∞ :=
  max (supNormQ D E u) (ENNReal.ofReal (40 * D.M * lipConstQ D E u))
def euclidC1Norm (u : E.Pt D → ℝ) : ℝ≥0∞ :=
  max (supNormQ D E u) (vecSupNormQ D E (gradVec D E u))
def c1NormQ (u : E.Pt D → ℝ) : ℝ≥0∞ :=
  max (supNormQ D E u) (⨆ μ : Fin 4, supNormQ D E (partialDeriv D E μ u))
end Kind
end PeriodicSpace
end YangMills.Construction
