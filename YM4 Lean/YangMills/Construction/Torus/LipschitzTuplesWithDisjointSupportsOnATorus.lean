import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOnOneTorusIsometriesAndSymmetricFunctions
import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace TorusLipschitzTuples
open ReflectionPositivity.AxisMirror (Ambient)
variable (P : Conventions.StandingParameters)
abbrev FnFamily (n : ℕ) : Type := Fin n → AmbientPoints.Pt P .torus → ℝ
def componentList {n : ℕ} (u : FnFamily P n) : ReflectionPositivity.TorusTuples.FnTuple P ℝ :=
  List.ofFn u
abbrev lipTuples (n : ℕ) : Set (FnFamily P n) :=
  AmbientPoints.sepLipTuples P .torus n
abbrev axisMirrorData (β : ℝ) (hβ : 0 < β) : ReflectionPositivity.AxisMirror.MirrorData :=
  { toStandingParameters := P, β := β, β_pos := hβ }
def SupportGapPos : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ u ∈ lipTuples P n, 0 < AmbientPoints.supportGap u
def LipTuplesEqUnion : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    lipTuples P n = ⋃ (r : ℝ) (_ : 0 < r),
      {u | u ∈ lipTuples P n ∧ ENNReal.ofReal r ≤ AmbientPoints.supportGap u}
def SeparatedSupportsIffGap : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ u ∈ lipTuples P n, ∀ r : ℝ, 0 < r →
    (TestFunctions.HasSeparatedSupportsTorus (ℓ := PeriodicLattice.torusSide P.L P.m) (E := ℝ) u r ↔
      ENNReal.ofReal r ≤ AmbientPoints.supportGap u)
def C1TuplesSubsetLipTuples : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ReflectionPositivity.TorusTuples.disjointC1Tuples P n ⊆ componentList P '' lipTuples P n
def LipTuplesEqDisjointTuples : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ReflectionPositivity.TorusTuples.disjointTuples P n = componentList P '' lipTuples P n
def SupportGapEqGap : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ u ∈ lipTuples P n,
    AmbientPoints.supportGap u = ReflectionPositivity.TorusTuples.gap (componentList P u)
def C1TuplesAgree : Prop :=
  ∀ q : ℕ, 1 ≤ q →
    ReflectionPositivity.TorusTuples.disjointC1Tuples P q =
        componentList P '' AmbientPoints.sepTuples P .torus q ∧
    ReflectionPositivity.TorusTuples.disjointC1Tuples P q =
        componentList P '' AmbientPoints.separatedTuples P .torus q ∧
    ∀ (β : ℝ) (hβ : 0 < β),
      ReflectionPositivity.TorusTuples.disjointC1Tuples P q =
        Ambient.separatedN (axisMirrorData P β hβ) .torus q
def RestrictionIsMultilinearForm : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ Φ : ReflectionPositivity.TorusTuples.disjointTuples P n → ℝ,
    ReflectionPositivity.TorusTuples.IsMultilinear Φ →
    ∀ Ψ : AmbientPoints.TupleForm (AmbientPoints.sepTuples P .torus n),
      (∀ u (h : componentList P u.1 ∈ ReflectionPositivity.TorusTuples.disjointTuples P n),
          Ψ u = (Φ ⟨_, h⟩ : ℂ)) →
        AmbientPoints.TupleForm.IsReal Ψ ∧ AmbientPoints.TupleForm.IsMultilinear Ψ
def FormIsMultilinearFunctional : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ Ψ : AmbientPoints.TupleForm (AmbientPoints.sepTuples P .torus q),
    AmbientPoints.TupleForm.IsReal Ψ → AmbientPoints.TupleForm.IsMultilinear Ψ →
    (∀ Ψ' : AmbientPoints.separatedTuples P .torus q → ℝ,
      (∀ u (h : u.1 ∈ AmbientPoints.sepTuples P .torus q), Ψ ⟨u.1, h⟩ = (Ψ' u : ℂ)) →
        AmbientPoints.IsTupleMultilinear Ψ') ∧
    ∀ (β : ℝ) (hβ : 0 < β)
      (Ψ' : Ambient.separatedN (axisMirrorData P β hβ) .torus q → ℝ),
      (∀ (u : AmbientPoints.sepTuples P .torus q)
        (h : componentList P u.1 ∈ Ambient.separatedN (axisMirrorData P β hβ) .torus q),
        Ψ u = (Ψ' ⟨_, h⟩ : ℂ)) →
        Ambient.IsSeparatedMultilinear (axisMirrorData P β hβ) .torus Ψ'
def TorusLipschitzTupleFacts : Prop :=
  ∀ P : Conventions.StandingParameters,
    SupportGapPos P ∧ LipTuplesEqUnion P ∧
    SeparatedSupportsIffGap P ∧ C1TuplesSubsetLipTuples P ∧
    LipTuplesEqDisjointTuples P ∧ SupportGapEqGap P ∧ C1TuplesAgree P ∧
    RestrictionIsMultilinearForm P ∧ FormIsMultilinearFunctional P
end TorusLipschitzTuples
end YangMills.Construction
end
