import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LocalOpFunTaylor
open TorusMetric (euclidNormVec)
section Families
variable (F I I' : PeriodicData)
def IsLinearCoeffFamily (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (R : ℝ)
    (i' : I'.Carrier) (i : I.Carrier) (t : nearIndices F (I'.pos i') R → ℂ) : Prop :=
  ∀ z : F.Carrier → ℂ, coeffOne F I I' T z i' i = ∑ᶠ k, t k * z k
def IsQuadraticCoeffFamily (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (R : ℝ)
    (i' : I'.Carrier) (i : I.Carrier)
    (t : nearIndices F (I'.pos i') R → nearIndices F (I'.pos i') R → ℂ) : Prop :=
  (∀ k k', t k k' = t k' k) ∧
    ∀ z z' : F.Carrier → ℂ,
      coeffTwo F I I' T z z' i' i = ∑ᶠ (k) (k'), t k k' * z k * z' k'
def linearCoeffFamily (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (R : ℝ)
    (i' : I'.Carrier) (i : I.Carrier) : nearIndices F (I'.pos i') R → ℂ :=
  Classical.epsilon (IsLinearCoeffFamily F I I' T R i' i)
def quadraticCoeffFamily (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (R : ℝ)
    (i' : I'.Carrier) (i : I.Carrier) :
    nearIndices F (I'.pos i') R → nearIndices F (I'.pos i') R → ℂ :=
  Classical.epsilon (IsQuadraticCoeffFamily F I I' T R i' i)
def CoeffsGivenByFamilies (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (R : ℝ)
    (i' : I'.Carrier) (i : I.Carrier) : Prop :=
  (nearIndices F (I'.pos i') R).Finite ∧
    (∃! t, IsLinearCoeffFamily F I I' T R i' i t) ∧
      IsLinearCoeffFamily F I I' T R i' i (linearCoeffFamily F I I' T R i' i) ∧
    (∃! t, IsQuadraticCoeffFamily F I I' T R i' i t) ∧
      IsQuadraticCoeffFamily F I I' T R i' i (quadraticCoeffFamily F I I' T R i' i)
def VanishOutsideRange (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (R : ℝ)
    (z z' : F.Carrier → ℂ) (i' : I'.Carrier) (i : I.Carrier) : Prop :=
  (R < euclidNormVec (I.pos i - I'.pos i') →
    coeffZero F I I' T i' i = 0 ∧
      (∀ k, linearCoeffFamily F I I' T R i' i k = 0) ∧
      ∀ k k', quadraticCoeffFamily F I I' T R i' i k k' = 0) ∧
    (¬ euclidNormVec (I.pos i - I'.pos i') ≤ R →
      coeffZero F I I' T i' i = 0 ∧
        coeffOne F I I' T z i' i = 0 ∧
        coeffTwo F I I' T z z' i' i = 0)
def ShiftCovariant (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (R : ℝ)
    (z z' : F.Carrier → ℂ) (i' : I'.Carrier) (i : I.Carrier) (n : Fin 4 → ℤ) : Prop :=
  coeffZero F I I' T (I'.translate n i') (I.translate n i) = coeffZero F I I' T i' i ∧
    (∀ k : nearIndices F (I'.pos i') R,
      ∃ h : F.translate n k ∈ nearIndices F (I'.pos (I'.translate n i')) R,
        linearCoeffFamily F I I' T R (I'.translate n i') (I.translate n i) ⟨F.translate n k, h⟩ =
          linearCoeffFamily F I I' T R i' i k) ∧
    (∀ k k' : nearIndices F (I'.pos i') R,
      ∃ (h : F.translate n k ∈ nearIndices F (I'.pos (I'.translate n i')) R)
        (h' : F.translate n k' ∈ nearIndices F (I'.pos (I'.translate n i')) R),
        quadraticCoeffFamily F I I' T R (I'.translate n i') (I.translate n i) ⟨F.translate n k, h⟩
            ⟨F.translate n k', h'⟩ =
          quadraticCoeffFamily F I I' T R i' i k k') ∧
    coeffOne F I I' T (shiftField F n z) (I'.translate n i') (I.translate n i) =
      coeffOne F I I' T z i' i ∧
    coeffTwo F I I' T (shiftField F n z) (shiftField F n z')
        (I'.translate n i') (I.translate n i) =
      coeffTwo F I I' T z z' i' i
def PeriodSumsFinite (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (z z' : F.Carrier → ℂ)
    (i' : I'.Carrier) (i : I.Carrier) : Prop :=
  ∀ s : ℕ, 0 < s → ∀ Y : I'.Carrier → I.Carrier → ℂ,
    (Y = coeffZero F I I' T ∨ Y = coeffOne F I I' T z ∨
      Y = coeffTwo F I I' T z z') →
    PeriodSumFinite I I' Y s i' i
end Families
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ρ R : ℝ),
      IsLocalWith F I I' T ρ R →
      ∀ (z z' : F.Carrier → ℂ) (i' : I'.Carrier) (i : I.Carrier) (n : Fin 4 → ℤ),
        CoeffsGivenByFamilies F I I' T R i' i ∧
          VanishOutsideRange F I I' T R z z' i' i ∧
          ShiftCovariant F I I' T R z z' i' i n ∧
          PeriodSumsFinite F I I' T z z' i' i
end YangMills.Construction.PeriodicOperators.LocalOpFunTaylor
end
