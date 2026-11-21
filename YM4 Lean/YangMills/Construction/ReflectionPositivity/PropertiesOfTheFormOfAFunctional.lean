import YangMills.Construction.ReflectionPositivity.FormOfAFunctionalOnSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.FormProperties
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.HilbertSpaceBasics
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open Classical in
def shiftedSpan (v : AmbientSpace) (F : PositiveSpan) : PositiveSpan :=
  if h : pushSpan (translate v) F.1 ∈ spanIn TimeAxis.upperHalfSpace then
    ⟨pushSpan (translate v) F.1, h⟩
  else 0
def unitSpan : PositiveSpan :=
  spanBasisIn TimeAxis.upperHalfSpace ⟨SepTuple.nil, nil_mem_supportedIn _⟩
variable (σ : TupleFunctional)
def HermitianOfPositive : Prop :=
  σ.IsReflectionPositive (Mirrors.axialHyperplane TimeAxis.timeIdx 0) →
    IsPosSemidef (reflectionForm σ) ∧ IsHermitianForm (reflectionForm σ)
def ReflectedValuesAgree : Prop :=
  σ.IsReflectionPositive (Mirrors.axialHyperplane TimeAxis.timeIdx 0) →
    (∀ X : supportedIn TimeAxis.upperHalfSpace,
      (σ (push TimeAxis.timeReflection X.1) : ℂ) =
          reflectionForm σ (spanBasisIn TimeAxis.upperHalfSpace X) unitSpan ∧
        reflectionForm σ (spanBasisIn TimeAxis.upperHalfSpace X) unitSpan =
          conj (reflectionForm σ unitSpan (spanBasisIn TimeAxis.upperHalfSpace X)) ∧
        conj (reflectionForm σ unitSpan (spanBasisIn TimeAxis.upperHalfSpace X)) = (σ X.1 : ℂ)) ∧
    reflectionForm σ unitSpan unitSpan = 1
def ShiftsCommuteWithForm (F F' : PositiveSpan) : Prop :=
  σ.IsTranslateInvariant →
    (∀ t : ℝ, 0 ≤ t →
      reflectionForm σ F (shiftedSpan (t • PeriodicLattice.coordVec TimeAxis.timeIdx) F') =
          reflectionForm σ (shiftedSpan (t • PeriodicLattice.coordVec TimeAxis.timeIdx) F) F' ∧
        reflectedCorrelation σ F ((2 * t) • PeriodicLattice.coordVec TimeAxis.timeIdx) =
          reflectionForm σ (shiftedSpan (t • PeriodicLattice.coordVec TimeAxis.timeIdx) F)
            (shiftedSpan (t • PeriodicLattice.coordVec TimeAxis.timeIdx) F)) ∧
    ∀ v : AmbientSpace, TimeAxis.IsPurelySpatial v →
      reflectionForm σ (shiftedSpan v F) (shiftedSpan v F') = reflectionForm σ F F'
def CorrelationNonnegConj (F : PositiveSpan) : Prop :=
  σ.IsTranslateInvariant →
    σ.IsReflectionPositive (Mirrors.axialHyperplane TimeAxis.timeIdx 0) →
    ∀ t : ℝ, 0 ≤ t → ∀ v : AmbientSpace, TimeAxis.IsPurelySpatial v →
      0 ≤ reflectedCorrelation σ F (t • PeriodicLattice.coordVec TimeAxis.timeIdx) ∧
      reflectedCorrelation σ F (t • PeriodicLattice.coordVec TimeAxis.timeIdx - v) =
        conj (reflectedCorrelation σ F (t • PeriodicLattice.coordVec TimeAxis.timeIdx + v)) ∧
      0 ≤ reflectedCorrelation σ F ((2 * t) • PeriodicLattice.coordVec TimeAxis.timeIdx) ∧
      0 ≤ reflectionForm σ F F ∧
      (reflectedCorrelation σ F 0 -
          4 * reflectedCorrelation σ F (t • PeriodicLattice.coordVec TimeAxis.timeIdx) +
          reflectedCorrelation σ F ((2 * t) • PeriodicLattice.coordVec TimeAxis.timeIdx) +
          reflectedCorrelation σ F (t • PeriodicLattice.coordVec TimeAxis.timeIdx + v) +
          reflectedCorrelation σ F (t • PeriodicLattice.coordVec TimeAxis.timeIdx - v)).im = 0
def ContinuousInShift (F F' : PositiveSpan) : Prop :=
  σ.IsAdmissiblyContinuous →
    ContinuousOn (fun v : AmbientSpace => reflectionForm σ F (shiftedSpan v F'))
      {v | 0 ≤ TimeAxis.timeComponent v}
def Assertion : Prop :=
  ∀ (σ : TupleFunctional) (F F' : PositiveSpan),
    HermitianOfPositive σ ∧ ReflectedValuesAgree σ ∧ ShiftsCommuteWithForm σ F F' ∧
      CorrelationNonnegConj σ F ∧ ContinuousInShift σ F F'
end YangMills.Construction.ReflectionPositivity.FormProperties
