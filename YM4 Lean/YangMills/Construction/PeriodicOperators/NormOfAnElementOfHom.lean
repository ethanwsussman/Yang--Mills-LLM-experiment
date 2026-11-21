import YangMills.Construction.Conventions.RealPowerAndLogarithm
import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
namespace HomNorm
def NormContinuousInEntries (I I' : PeriodicData) : Prop :=
  ∃ φ : (I'.UnitQuot → I.UnitQuot → ℂ) → ℝ, Continuous φ ∧
    ∀ A : QuotHom I I', (quotHomNorm A).toReal = φ (linearMapEntry A)
def NormContinuousAlong (I I' : PeriodicData) : Prop :=
  ∀ (U : Set (Coordinates.ComplexCoordinates 4)) (A : Coordinates.ComplexCoordinates 4 → QuotHom I I'),
    QuotHomFamilyContinuousOn U A → ContinuousOn (fun z => (quotHomNorm (A z)).toReal) U
def EntryLeNorm (I I' : PeriodicData) : Prop :=
  ∀ (A : QuotHom I I') (b : I'.UnitQuot) (a : I.UnitQuot),
    ‖linearMapEntry A b a‖ ≤ (quotHomNorm A).toReal *
      RealPower.sqrtOf (I.quotWeight 1 a / I'.quotWeight 1 b)
def NormBoundedIffEntriesBounded (I I' : PeriodicData) : Prop :=
  ∀ (X : Type) (U : Set X) (A : X → QuotHom I I'),
    (∃ C : ℝ, ∀ x ∈ U, |(quotHomNorm (A x)).toReal| ≤ C) ↔ QuotHomFamilyBoundedOn U A
def ComplexModuleStructure (I I' : PeriodicData) : Prop :=
  ∃ (G : AddCommGroup (QuotHom I I')) (Mo : @Module ℂ (QuotHom I I') _ G.toAddCommMonoid),
    (∀ (A B : QuotHom I I') (u : I.UnitQuot → ℂ), (G.add A B) u = A u + B u) ∧
      ∀ (z : ℂ) (A : QuotHom I I') (u : I.UnitQuot → ℂ), (Mo.smul z A) u = z • A u
def AddSMulNorm (I I' : PeriodicData) : Prop :=
  (∀ (A B : QuotHom I I') (u : I.UnitQuot → ℂ), (A + B) u = A u + B u) ∧
    (∀ (z : ℂ) (A : QuotHom I I') (u : I.UnitQuot → ℂ), (z • A) u = z • A u) ∧
    ComplexModuleStructure I I' ∧
    (∀ A B : QuotHom I I', quotHomNorm (A + B) ≤ quotHomNorm A + quotHomNorm B) ∧
    ∀ (z : ℂ) (A : QuotHom I I'), quotHomNorm (z • A) = quotHomNorm A * ENNReal.ofReal ‖z‖
def NormApplyComp (I I' I'' : PeriodicData) : Prop :=
  (∀ (A : QuotHom I I') (u : I.UnitQuot → ℂ),
    wNorm (I'.quotWeight 1) (A u) ≤
      (quotHomNorm A).toReal * wNorm (I.quotWeight 1) u) ∧
    ∀ (A : QuotHom I I') (B : QuotHom I'' I),
      quotHomNorm (A.comp B) ≤ quotHomNorm A * quotHomNorm B
def QuotOneIsIdNormLeOne (I : PeriodicData) : Prop :=
  linearMapOfEntries (quotOne I) = (LinearMap.id : QuotHom I I) ∧
    quotHomNorm (LinearMap.id : QuotHom I I) ≤ 1
def SubAndEntriesOfLinComb (I I' : PeriodicData) : Prop :=
  ∀ (A B : QuotHom I I') (z : ℂ),
    A - B = A + (-1 : ℂ) • B ∧
    (∀ (b : I'.UnitQuot) (a : I.UnitQuot),
      linearMapEntry (A + B) b a = linearMapEntry A b a + linearMapEntry B b a ∧
        linearMapEntry (z • A) b a = z * linearMapEntry A b a ∧
        linearMapEntry (A - B) b a = linearMapEntry A b a - linearMapEntry B b a) ∧
    A + B = linearMapOfEntries (kernelLinComb 1 1 (linearMapEntry A) (linearMapEntry B)) ∧
    z • A = linearMapOfEntries (fun b a => z * linearMapEntry A b a) ∧
    A - B = linearMapOfEntries (kernelLinComb 1 (-1) (linearMapEntry A) (linearMapEntry B))
def Claim : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    Quotients.LinearMapNormFinite I I' 1 1 ∧
    NormContinuousInEntries I I' ∧
    NormContinuousAlong I I' ∧
    EntryLeNorm I I' ∧
    NormBoundedIffEntriesBounded I I' ∧
    AddSMulNorm I I' ∧
    (∀ I'' : PeriodicData, IsPeriodic I'' → NormApplyComp I I' I'') ∧
    QuotOneIsIdNormLeOne I ∧
    SubAndEntriesOfLinComb I I'
end HomNorm
end PeriodicOperators
end YangMills.Construction
end
