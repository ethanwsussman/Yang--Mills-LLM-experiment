import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.Towers.PeriodicExtensionsLocalKernelsAndKernelsThatDescend
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower (IsColourTrivialOnClasses)
open YangMills.Construction.PeriodicOperators.Quotients (conjKernel)
open YangMills.Construction.LocalKernels (CellType Cell)
variable {P P' P'' : PeriodicData}
def conjQuotHom (A : QuotHom P P') : QuotHom P P' :=
  linearMapOfEntries (conjKernel (linearMapEntry A))
def negConjPoint (z : Fin 4 → ℂ) : Fin 4 → ℂ := fun μ => -conj (z μ)
def phaseConj (n : Fin 4 → ℤ) (A : QuotHom P P') : QuotHom P P' :=
  (quotHomInverse (phaseMul P' n : QuotHom P' P')).comp
    (A.comp (phaseMul P n : QuotHom P P))
def IsSymmetricSet (U : Set (Fin 4 → ℂ)) : Prop :=
  ∀ z ∈ U, negConjPoint z ∈ U ∧ ∀ n : Fin 4 → ℤ, addTwoPiInt z n ∈ U
def IsSymmetricFamilyOn (U : Set (Fin 4 → ℂ)) (A : (Fin 4 → ℂ) → QuotHom P P') : Prop :=
  ∀ z ∈ U, conjQuotHom (A z) = A (negConjPoint z) ∧
    ∀ n : Fin 4 → ℤ, A (addTwoPiInt z n) = phaseConj n (A z)
def unitPoints (U : Set (Fin 4 → ℂ)) (A : (Fin 4 → ℂ) → QuotHom P P) : Set (Fin 4 → ℂ) :=
  {z | z ∈ U ∧ IsInvertibleQuotHom (A z)}
def colourCells (L k j : ℕ) : CellType → PeriodicData
  | .vertex => colourVertices L k j
  | .edge => colourEdges L k j
  | .face => colourFaces L k j
def colourCellQuot (L k j : ℕ) :
    ∀ t : CellType, Fin 3 × Cell L k j t → (colourCells L k j t).UnitQuot
  | .vertex, x => (colourVertices L k j).mkQuot 1 x
  | .edge, x => (colourEdges L k j).mkQuot 1 x
  | .face, x => (colourFaces L k j).mkQuot 1 x
def IsColourTrivial {L k j j' : ℕ} {t t' : CellType}
    (A : QuotHom (colourCells L k j t) (colourCells L k j' t')) : Prop :=
  IsColourTrivialOnClasses (colourCellQuot L k j t) (colourCellQuot L k j' t')
    (linearMapEntry A)
namespace CompInv
def ConjCompInv (P P' P'' : PeriodicData) : Prop :=
  (∀ (A : QuotHom P P') (B : QuotHom P'' P),
    conjQuotHom (A.comp B) = (conjQuotHom A).comp (conjQuotHom B)) ∧
  ∀ A : QuotHom P P, IsInvertibleQuotHom A →
    IsInvertibleQuotHom (conjQuotHom A) ∧
      quotHomInverse (conjQuotHom A) = conjQuotHom (quotHomInverse A)
def PhaseCompInv (P P' P'' : PeriodicData) : Prop :=
  ∀ n : Fin 4 → ℤ,
    IsInvertibleQuotHom (phaseMul P n : QuotHom P P) ∧
    IsInvertibleQuotHom (phaseMul P' n : QuotHom P' P') ∧
    IsInvertibleQuotHom (phaseMul P'' n : QuotHom P'' P'') ∧
    (∀ (A : QuotHom P P') (B : QuotHom P'' P),
      (phaseConj n A).comp (phaseConj n B) = phaseConj n (A.comp B)) ∧
    ∀ A : QuotHom P P, IsInvertibleQuotHom A →
      IsInvertibleQuotHom (phaseConj n A) ∧
        quotHomInverse (phaseConj n A) = phaseConj n (quotHomInverse A)
def ColourCompInv (L k j j' j'' : ℕ) (t t' t'' : CellType) : Prop :=
  (∀ (A : QuotHom (colourCells L k j t) (colourCells L k j' t'))
      (B : QuotHom (colourCells L k j'' t'') (colourCells L k j t)),
    IsColourTrivial A → IsColourTrivial B →
      IsColourTrivial (A.comp B)) ∧
  ∀ A : QuotHom (colourCells L k j t) (colourCells L k j t),
    IsInvertibleQuotHom A → IsColourTrivial A →
      IsColourTrivial (quotHomInverse A)
def FamilyInv (P : PeriodicData) : Prop :=
  ∀ (U : Set (Fin 4 → ℂ)) (A : (Fin 4 → ℂ) → QuotHom P P),
    IsSymmetricSet U → IsSymmetricFamilyOn U A →
      IsSymmetricSet (unitPoints U A) ∧
      ∀ z ∈ unitPoints U A,
        conjQuotHom (quotHomInverse (A z)) = quotHomInverse (A (negConjPoint z)) ∧
        ∀ n : Fin 4 → ℤ,
          quotHomInverse (A (addTwoPiInt z n)) = phaseConj n (quotHomInverse (A z))
def FamilyComp (P P' P'' : PeriodicData) : Prop :=
  ∀ (U : Set (Fin 4 → ℂ)) (A : (Fin 4 → ℂ) → QuotHom P P') (B : (Fin 4 → ℂ) → QuotHom P'' P),
    IsSymmetricSet U → IsSymmetricFamilyOn U A → IsSymmetricFamilyOn U B →
      ∀ z ∈ U,
        conjQuotHom ((A z).comp (B z)) =
          (A (negConjPoint z)).comp (B (negConjPoint z)) ∧
        ∀ n : Fin 4 → ℤ,
          (A (addTwoPiInt z n)).comp (B (addTwoPiInt z n)) =
            phaseConj n ((A z).comp (B z))
def ColourFamilies (L k j j' j'' : ℕ) (t t' t'' : CellType) : Prop :=
  (∀ (U : Set (Fin 4 → ℂ)) (A : (Fin 4 → ℂ) → QuotHom (colourCells L k j t) (colourCells L k j t)),
    IsSymmetricSet U → IsSymmetricFamilyOn U A →
      (∀ z ∈ unitPoints U A, IsColourTrivial (A z)) →
        ∀ z ∈ unitPoints U A, IsColourTrivial (quotHomInverse (A z))) ∧
  ∀ (U : Set (Fin 4 → ℂ))
    (A : (Fin 4 → ℂ) → QuotHom (colourCells L k j t) (colourCells L k j' t'))
    (B : (Fin 4 → ℂ) → QuotHom (colourCells L k j'' t'') (colourCells L k j t)),
    IsSymmetricSet U → IsSymmetricFamilyOn U A → IsSymmetricFamilyOn U B →
      (∀ z ∈ U, IsColourTrivial (A z)) → (∀ z ∈ U, IsColourTrivial (B z)) →
        ∀ z ∈ U, IsColourTrivial ((A z).comp (B z))
def Claim : Prop :=
  (∀ P P' P'' : PeriodicData, IsPeriodic P → IsPeriodic P' → IsPeriodic P'' →
    ConjCompInv P P' P'' ∧ PhaseCompInv P P' P'' ∧
      FamilyInv P ∧ FamilyComp P P' P'') ∧
  (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ j j' j'' : ℕ, j ≤ k → j' ≤ k →
    j'' ≤ k → ∀ t t' t'' : CellType,
      ColourCompInv L k j j' j'' t t' t'' ∧
        ColourFamilies L k j j' j'' t t' t'') ∧
  ∀ (z : Fin 4 → ℂ) (n : Fin 4 → ℤ) (S : Set (Fin 4 → ℂ)), IsImStrip S → z ∈ S →
    negConjPoint z ∈ S ∧ addTwoPiInt z n ∈ S
end CompInv
end YangMills.Construction.PeriodicOperators
end
