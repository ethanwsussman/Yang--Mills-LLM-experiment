import YangMills.Construction.Continuum.DistributionsOnOpenSetsOfPointsAndRegularFunctionals
import YangMills.Construction.Continuum.TestSpacesAndNormsOfTheAxiomsOnSchwartzFunctions
import YangMills.Construction.Continuum.TranslationsAsMotionsAndSmoothSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.OffDiagonal
variable {n : ℕ}
def restrictToCompactSupp (h : (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)) ⊆
      flatSchwartzSet n) (T : flatSchwartzSet n → ℂ) :
    TestFnOn (distinctLocus n) → ℂ :=
  fun φ => T ⟨φ.1, h φ.2⟩
def DistribDeterminedByTensors (n : ℕ) : Prop :=
  ∀ u₁ u₂ : TestFnOn (distinctLocus n) → ℂ,
    IsDistribOn u₁ → IsDistribOn u₂ →
    (∀ X : SepTupleOfCard n, HasSmoothComponents Set.univ X.1 →
      ∀ h : tensorProdComplex X.1 ∈
          (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)),
        u₁ ⟨_, h⟩ = u₂ ⟨_, h⟩) →
    u₁ = u₂
def BoundedFunctionalRestrictsToDistrib (n : ℕ) : Prop :=
  ∀ (T : flatSchwartzSet n → ℂ) (k : ℕ) (c : ℝ), IsCLinearOnFlat T → 0 < k → 0 ≤ c →
    (∀ φ : flatSchwartzSet n,
      ENNReal.ofReal ‖T φ‖ ≤ ENNReal.ofReal c * weightedSeminorm k φ.1) →
    ∃ h : (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)) ⊆
        flatSchwartzSet n,
      IsDistribOn (restrictToCompactSupp h T)
def SchwingerFamilyImpliesRegular (n : ℕ) : Prop :=
  ∀ (σ : SepTuple → ℝ) (T : (m : ℕ) → flatSchwartzSet m → ℂ),
    IsSepFunctional σ → IsSchwingerFamily σ T →
    IsRegular σ ∧
      ∃ h : (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)) ⊆
          flatSchwartzSet n,
        IsDistribOn (restrictToCompactSupp h (T n)) ∧
          AgreesOnTensors σ (restrictToCompactSupp h (T n)) ∧
          ∀ u : TestFnOn (distinctLocus n) → ℂ,
            IsDistribOn u → AgreesOnTensors σ u → u = restrictToCompactSupp h (T n)
def SpatialShiftPreservesPositiveTime (n : ℕ) : Prop :=
  ∀ v : Fin 4 → ℝ, YangMills.Construction.TimeAxis.IsPurelySpatial v →
    ∀ ψ ∈ YangMills.Construction.SchwartzAxioms.positiveTimeSchwartz n,
      YangMills.Construction.SmoothSeparatedTuples.translateFun v ψ ∈
        YangMills.Construction.SchwartzAxioms.positiveTimeSchwartz n
def ReflectConjTensorFlat : Prop :=
  ∀ q q' : ℕ, 0 < q → 0 < q' → ∀ φ ∈ YangMills.Construction.SchwartzAxioms.positiveTimeSchwartz q,
    ∀ ψ ∈ YangMills.Construction.SchwartzAxioms.positiveTimeSchwartz q',
      YangMills.Construction.Motions.reflectConj φ ∈
          YangMills.Construction.SchwartzAxioms.negativeTimeSchwartz q ∧
        tensorFun (YangMills.Construction.Motions.reflectConj φ) ψ ∈ flatSchwartzSet (q + q')
def OffDiagonalFacts : Prop :=
  ∀ n : ℕ, 0 < n →
    DistribDeterminedByTensors n ∧ BoundedFunctionalRestrictsToDistrib n ∧
      SchwingerFamilyImpliesRegular n ∧ SpatialShiftPreservesPositiveTime n ∧ ReflectConjTensorFlat
end YangMills.Construction.TestSpaces.OffDiagonal
end
