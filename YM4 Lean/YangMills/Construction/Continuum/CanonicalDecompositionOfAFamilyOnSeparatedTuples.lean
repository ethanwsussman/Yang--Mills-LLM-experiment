import YangMills.Construction.Continuum.IteratedFarTranslationLimits
import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import YangMills.Construction.Measures.SupportOfProbabilityMeasure
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.CanonicalDecomposition
open YangMills.Construction.TestSpaces YangMills.Construction.TupleLists
open YangMills.Construction.SeparatedTuples (atInfinity iterLimitDomain iterLimitValue shiftedJuxt)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
abbrev TupleFamily : Type := (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ
section Shifts
variable (X : SepTuple) (Ys : List SepTuple)
def IsAdmissibleShifts (k : ℕ) (vs : List AmbientSpace) : Prop :=
  vs ∈ iterLimitDomain (toList X) (Ys.map toList) Set.univ k
def shiftedGlue (k : ℕ) (vs : List AmbientSpace) : SepTuple :=
  ofList (shiftedJuxt (toList X) (((Ys.map toList).drop k).zip vs))
variable (σ : SepTuple → ℝ)
def partialLimit (k : ℕ) (vs : List AmbientSpace) : ℝ :=
  iterLimitValue (fun W => σ (ofList W)) (toList X) (Ys.map toList) Set.univ k vs
def IteratedLimitsExist : Prop :=
  ∀ k < Ys.length, ∀ vs, IsAdmissibleShifts X Ys (k + 1) vs →
    (∃ s : ℝ, ∀ v : AmbientSpace, s ≤ euclidNormVec v → IsAdmissibleShifts X Ys k (v :: vs)) ∧
      ∃ c : ℝ, Tendsto (fun v => partialLimit X Ys σ k (v :: vs)) atInfinity (𝓝 c)
def iterLimit : ℝ := partialLimit X Ys σ Ys.length []
theorem partialLimit_zero (vs : List AmbientSpace) :
    partialLimit X Ys σ 0 vs = σ (shiftedGlue X Ys 0 vs) := by
  simp [partialLimit, shiftedGlue, iterLimitValue]
theorem isAdmissibleShifts_length_iff (vs : List AmbientSpace) :
    IsAdmissibleShifts X Ys Ys.length vs ↔ vs = [] := by
  have h := YangMills.Construction.SeparatedTuples.iterLimitDomain_length (toList X)
    (Ys.map toList) Set.univ
  rw [List.length_map] at h
  simp [IsAdmissibleShifts, h]
theorem shiftedGlue_length : shiftedGlue X Ys Ys.length [] = X := by
  simp [shiftedGlue, shiftedJuxt, ofList_toList]
end Shifts
structure DecompositionTriple where
  space : Type
  [instTop : TopologicalSpace space]
  [instMeas : MeasurableSpace space]
  [instBorel : BorelSpace space]
  law : Measure space
  comp : space → SepTuple → ℝ
attribute [instance] DecompositionTriple.instTop DecompositionTriple.instMeas
  DecompositionTriple.instBorel
namespace DecompositionTriple
structure IsCanonical (A : DecompositionTriple) (S : TupleFamily) : Prop where
  compact : CompactSpace A.space
  metrizable : TopologicalSpace.MetrizableSpace A.space
  isProbability : IsProbabilityMeasure A.law
  support_eq_univ : YangMills.Construction.Measures.probabilitySupport A.law = Set.univ
  comp_isSepFunctional : ∀ ξ, IsSepFunctional (A.comp ξ)
  comp_invariant : ∀ ξ, YangMills.Construction.WightmanReconstruction.IsPermutationInvariant (A.comp ξ)
  continuous_comp : ∀ X : SepTuple, Continuous fun ξ => A.comp ξ X
  injective_comp : Function.Injective A.comp
  limitsExist : ∀ (X : SepTuple) (Ys : List SepTuple),
    IteratedLimitsExist X Ys (centredOfCumulants S)
  integral_prod_eq : ∀ (X : SepTuple) (Ys : List SepTuple),
    ∫ ξ, A.comp ξ X * (Ys.map fun Z => A.comp ξ Z).prod ∂A.law =
      iterLimit X Ys (centredOfCumulants S)
def Isomorphic (A B : DecompositionTriple) : Prop :=
  ∃ h : A.space ≃ₜ B.space, A.law.map h = B.law ∧
    ∀ ξ, B.comp (h ξ) = A.comp ξ
end DecompositionTriple
end YangMills.Construction.CanonicalDecomposition
