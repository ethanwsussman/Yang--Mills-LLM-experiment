import YangMills.Construction.Lattice.OneStepObjects
import YangMills.Construction.Lattice.SchemesOfTheOneStepToolbox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open YangMills.Construction.Matrices
variable {L m K n : ℕ}
def StepData (c : BondAtLevel L m K (n + 1)) (W₀ : BondAtLevel L m K n → ComplexMatrix2) : Prop :=
  n < K ∧ c.IsPositivelyOriented ∧
    IsGaugeField complexGaugeGroup (doubleBlockSymmetricSet c).bonds W₀
abbrev stepTwistedField (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W₀ : BondAtLevel L m K n → ComplexMatrix2) :
    BondAtLevel L m K n → ComplexMatrix2 :=
  twistedConfig c a W₀
abbrev stepLogAt (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n) : ComplexMatrix2 :=
  stepLog s c a W₀ y x
abbrev stepGaugeAt (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : ComplexMatrix2 :=
  stepGauge s c a W₀ y
abbrev stepVariableAt (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W₀ : BondAtLevel L m K n → ComplexMatrix2) :
    ComplexMatrix2 :=
  stepVariable s c a W₀
def StepVariableFormed (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W₀ : BondAtLevel L m K n → ComplexMatrix2) :
    Prop :=
  StepData c W₀ ∧ StepVariableDefined s c a W₀ ∧
    IsOneStepAverageFormed s (stepTwistedField c a W₀) c ∧
    IsOneStepAverageFormed s W₀ c
end PeriodicLattice
end YangMills.Construction
