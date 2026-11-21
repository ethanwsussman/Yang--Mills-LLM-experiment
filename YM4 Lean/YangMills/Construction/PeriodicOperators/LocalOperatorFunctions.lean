import YangMills.Construction.Coordinates.QuadraticTaylorExpansion
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
section Fields
variable (F : PeriodicData)
def IsSupBelow (ζ : F.Carrier → ℂ) (ρ : ℝ) : Prop :=
  ∃ r : ℝ, r < ρ ∧ ∀ κ, ‖ζ κ‖ ≤ r
def liftQuotField (s : ℕ) (ζ : F.QuotMod s → ℂ) : F.Carrier → ℂ :=
  fun κ => ζ (F.mkQuot s κ)
def shiftField (n : Fin 4 → ℤ) (ζ : F.Carrier → ℂ) : F.Carrier → ℂ :=
  fun κ => ζ (F.translate (-n) κ)
def nearIndices (y : YangMills.Construction.InfiniteLattice.AmbientSpace) (R : ℝ) :
    Set F.Carrier :=
  {κ | euclidNormVec (F.pos κ - y) ≤ R}
variable {F}
def fieldValues {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) (ζ : F.Carrier → ℂ) :
    YangMills.Construction.Coordinates.ComplexCoordinates l :=
  fun j => ζ (e j)
def fieldExtend {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S)
    (z : YangMills.Construction.Coordinates.ComplexCoordinates l) :
    F.Carrier → ℂ :=
  Function.extend (fun j => ((e j : S) : F.Carrier)) z 0
end Fields
section Local
variable (F I I' : PeriodicData)
structure IsLocalWith (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ρ R : ℝ) : Prop where
  radius_pos : 0 < ρ
  vanish_far : ∀ ζ, IsSupBelow F ζ ρ → ∀ ι' ι,
    ¬ euclidNormVec (I.pos ι - I'.pos ι') ≤ R → T ζ ι' ι = 0
  holo_entry : ∀ ι' ι, ∃ (l : ℕ) (e : Fin l ≃ nearIndices F (I'.pos ι') R)
    (h : YangMills.Construction.Coordinates.ComplexCoordinates l → ℂ),
    YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
      (YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk 0 ρ)
      (fun z _ => h z) ∧
    ∀ ζ, IsSupBelow F ζ ρ → T ζ ι' ι = h (fieldValues e ζ)
  shift_covariant : ∀ ζ, IsSupBelow F ζ ρ → ∀ (n : Fin 4 → ℤ) ι' ι,
    T (shiftField F n ζ) (I'.translate n ι') (I.translate n ι) = T ζ ι' ι
def IsLocalOpFun (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) : Prop :=
  ∃ ρ R : ℝ, IsLocalWith F I I' T ρ R
def InLocalDomain (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ζ : F.Carrier → ℂ) : Prop :=
  ∃ ρ R : ℝ, IsLocalWith F I I' T ρ R ∧ IsSupBelow F ζ ρ
variable {F I I'}
def entryFun (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ι' : I'.Carrier) (ι : I.Carrier)
    {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) :
    YangMills.Construction.Coordinates.ComplexCoordinates l → ℂ :=
  fun z => T (fieldExtend e z) ι' ι
variable (F I I')
def IsLinearCoeff (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ζ : F.Carrier → ℂ)
    (ι' : I'.Carrier) (ι : I.Carrier) (t : ℂ) : Prop :=
  ∀ ρ R : ℝ, IsLocalWith F I I' T ρ R →
    ∀ (l : ℕ) (e : Fin l ≃ nearIndices F (I'.pos ι') R)
      (φ : YangMills.Construction.Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ)
      (β : YangMills.Construction.Coordinates.ComplexCoordinates l →ₗ[ℂ]
        YangMills.Construction.Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ),
      IsSecondOrderExpansion (entryFun T ι' ι e) φ β → φ (fieldValues e ζ) = t
def IsBilinearCoeff (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ζ ζ' : F.Carrier → ℂ)
    (ι' : I'.Carrier) (ι : I.Carrier) (t : ℂ) : Prop :=
  ∀ ρ R : ℝ, IsLocalWith F I I' T ρ R →
    ∀ (l : ℕ) (e : Fin l ≃ nearIndices F (I'.pos ι') R)
      (φ : YangMills.Construction.Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ)
      (β : YangMills.Construction.Coordinates.ComplexCoordinates l →ₗ[ℂ]
        YangMills.Construction.Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ),
      IsSecondOrderExpansion (entryFun T ι' ι e) φ β →
        β (fieldValues e ζ) (fieldValues e ζ') = t
def coeffZero (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) : I'.Carrier → I.Carrier → ℂ :=
  T 0
def coeffOne (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ζ : F.Carrier → ℂ) :
    I'.Carrier → I.Carrier → ℂ :=
  fun ι' ι => Classical.epsilon (IsLinearCoeff F I I' T ζ ι' ι)
def coeffTwo (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (ζ ζ' : F.Carrier → ℂ) :
    I'.Carrier → I.Carrier → ℂ :=
  fun ι' ι => Classical.epsilon (IsBilinearCoeff F I I' T ζ ζ' ι' ι)
def PeriodSumFinite (Y : I'.Carrier → I.Carrier → ℂ) (s : ℕ) (ι' : I'.Carrier) (ι : I.Carrier) :
    Prop :=
  {n : Fin 4 → ℤ | Y ι' (I.translate (s • n) ι) ≠ 0}.Finite
def periodicValue (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (s : ℕ)
    (ζ : F.QuotMod s → ℂ) : I'.Carrier → I.Carrier → ℂ :=
  periodization I I' (T (liftQuotField F s ζ)) s
def periodicCoeffZero (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (s : ℕ) :
    I'.Carrier → I.Carrier → ℂ :=
  periodization I I' (coeffZero F I I' T) s
def periodicCoeffOne (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (s : ℕ)
    (ζ : F.QuotMod s → ℂ) : I'.Carrier → I.Carrier → ℂ :=
  periodization I I' (coeffOne F I I' T (liftQuotField F s ζ)) s
def periodicCoeffTwo (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (s : ℕ)
    (ζ ζ' : F.QuotMod s → ℂ) : I'.Carrier → I.Carrier → ℂ :=
  periodization I I' (coeffTwo F I I' T (liftQuotField F s ζ) (liftQuotField F s ζ')) s
end Local
section Operations
variable {F I I' I'' : PeriodicData}
def opFunAdd (T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) :
    (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ :=
  fun ζ => T ζ + T' ζ
def opFunComp (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ)
    (S : (F.Carrier → ℂ) → I.Carrier → I''.Carrier → ℂ) :
    (F.Carrier → ℂ) → I'.Carrier → I''.Carrier → ℂ :=
  fun ζ => compKernel (T ζ) (S ζ)
def opFunTranspose (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) :
    (F.Carrier → ℂ) → I.Carrier → I'.Carrier → ℂ :=
  fun ζ => wTranspose I.weightOf I'.weightOf (T ζ)
end Operations
end PeriodicOperators
end YangMills.Construction
end
