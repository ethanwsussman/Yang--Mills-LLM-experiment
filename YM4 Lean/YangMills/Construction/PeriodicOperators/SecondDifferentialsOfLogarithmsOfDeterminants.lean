import YangMills.Construction.Matrices.SecondDifferentialOfTheLogarithmOfADeterminant
import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
open Coordinates.ComplexCoordinates.LogDetSecondDeriv
  (seriesLog scalarSecondDeriv IsHolomorphicScalarIn)
open JetQuad (IsInvertibleJet logNumber)
variable (F I : PeriodicData)
def quotOperator (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (s : ℕ) (ζ : F.QuotMod s → ℂ) :
    Module.End ℂ (I.QuotMod s → ℂ) :=
  linearMapOfEntries (descendMatrix I I s (periodicValue F I I T s ζ))
def normalizedDet (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (s : ℕ)
    (ζ : F.QuotMod s → ℂ) : ℂ :=
  LinearMap.det (Ring.inverse (quotOperator F I T s 0) * quotOperator F I T s ζ)
def logNormalizedDet (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (s : ℕ)
    (ζ : F.QuotMod s → ℂ) : ℂ :=
  seriesLog (normalizedDet F I T s ζ)
def realLogAbsDetDiff (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (s : ℕ)
    (u : F.QuotMod s → ℝ) : ℝ :=
  Real.log ‖LinearMap.det (quotOperator F I T s fun c => (u c : ℂ))‖ -
    Real.log ‖LinearMap.det (quotOperator F I T s 0)‖
variable {F}
def ofCoords {s N : ℕ} (e : Fin N ≃ F.QuotMod s) (z : Coordinates.ComplexCoordinates N) :
    F.QuotMod s → ℂ :=
  fun c => z (e.symm c)
def toCoords {s N : ℕ} (e : Fin N ≃ F.QuotMod s) (ζ : F.QuotMod s → ℂ) :
    Coordinates.ComplexCoordinates N :=
  fun j => ζ (e j)
def ofRealCoords {s N : ℕ} (e : Fin N ≃ F.QuotMod s) (v : Fin N → ℝ) :
    F.QuotMod s → ℝ :=
  fun c => v (e.symm c)
variable (F)
def descendField (s : ℕ) (f : F.Carrier → ℂ) : F.QuotMod s → ℂ :=
  fun c => Classical.epsilon fun z => ∀ κ, F.mkQuot s κ = c → f κ = z
variable {F}
variable (F) in
def logDetInCoords (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) {s N : ℕ}
    (e : Fin N ≃ F.QuotMod s) : Coordinates.ComplexCoordinates N → ℂ :=
  fun z => logNormalizedDet F I T s (ofCoords e z)
variable (F) in
def logDetSecondDeriv (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) {s N : ℕ}
    (e : Fin N ≃ F.QuotMod s) (ζ ζ' : F.QuotMod s → ℂ) : ℂ :=
  scalarSecondDeriv (logDetInCoords F I T e) 0 (toCoords e ζ) (toCoords e ζ')
variable (F) in
def realLogAbsDetDiffInCoords (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) {s N : ℕ}
    (e : Fin N ≃ F.QuotMod s) : (Fin N → ℝ) → ℝ :=
  fun v => realLogAbsDetDiff F I T s (ofRealCoords e v)
def HasSecondFDerivAtZero {N : ℕ} (g : (Fin N → ℝ) → ℝ) : Prop :=
  (∀ᶠ v in 𝓝 (0 : Fin N → ℝ), DifferentiableAt ℝ g v) ∧
    DifferentiableAt ℝ (fderiv ℝ g) (0 : Fin N → ℝ)
def complexifiedSecondDeriv {N : ℕ} (g : (Fin N → ℝ) → ℝ)
    (z z' : Coordinates.ComplexCoordinates N) : ℂ :=
  ((fderiv ℝ (fderiv ℝ g) 0 (fun j => (z j).re) (fun j => (z' j).re) -
      fderiv ℝ (fderiv ℝ g) 0 (fun j => (z j).im) (fun j => (z' j).im) : ℝ) : ℂ) +
    Complex.I * ((fderiv ℝ (fderiv ℝ g) 0 (fun j => (z j).re) (fun j => (z' j).im) +
      fderiv ℝ (fderiv ℝ g) 0 (fun j => (z j).im) (fun j => (z' j).re) : ℝ) : ℂ)
variable (F) in
def realLogAbsDetSecondDeriv (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) {s N : ℕ}
    (e : Fin N ≃ F.QuotMod s) (ζ ζ' : F.QuotMod s → ℂ) : ℂ :=
  complexifiedSecondDeriv (realLogAbsDetDiffInCoords F I T e) (toCoords e ζ) (toCoords e ζ')
variable (F)
def VanishesOffAntipodal (s : ℕ)
    (D : (F.QuotMod s → ℂ) → (F.QuotMod s → ℂ) → ℂ) : Prop :=
  ∀ p ∈ dualLattice s, ∀ p' ∈ dualLattice s, ∀ εPlus εMinus : F.UnitQuot → ℂ,
    p + p' ∉ InfiniteLattice.latticeSubgroup (2 * Real.pi) →
      D (descendField F s (blochWave F (toComplexVec p) εPlus))
        (descendField F s (blochWave F (toComplexVec p') εMinus)) = 0
def IsCloseToLogNumber (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (s : ℕ)
    (D : (F.QuotMod s → ℂ) → (F.QuotMod s → ℂ) → ℂ) (C c : ℝ) : Prop :=
  ∀ p ∈ dualLattice s, ∀ εPlus εMinus : F.UnitQuot → ℂ,
    ‖((s : ℂ) ^ 4)⁻¹ * D (descendField F s (blochWave F (toComplexVec p) εPlus))
          (descendField F s (blochWave F (-toComplexVec p) εMinus)) -
        logNumber (toComplexVec p)
          (jetAlong F I I T (toComplexVec p) εPlus εMinus)‖ ≤
      C * Real.exp (-c * s) * wNorm (F.quotWeight 1) εPlus *
        wNorm (F.quotWeight 1) εMinus
def IsRealOnRealFields (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ ζ : F.Carrier → ℂ, (∀ κ, (ζ κ).im = 0) → InLocalDomain F I I T ζ →
    ∀ ι' ι, (T ζ ι' ι).im = 0
def Claim : Prop :=
  ∀ (F I : PeriodicData), IsPeriodic F → IsPeriodic I →
    ∀ T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I T →
      (∀ κ : InfiniteLattice.AmbientSpace,
        IsUnit (symbolHom I I (coeffZero F I I T) (toComplexVec κ) :
          Module.End ℂ (I.UnitQuot → ℂ))) →
      ∃ δ : ℝ, 0 < δ ∧
        (∀ p ∈ imStrip δ, ∀ εPlus εMinus : F.UnitQuot → ℂ,
          IsInvertibleJet δ p (jetAlong F I I T p εPlus εMinus)) ∧
        (∃ (s₀ : ℕ) (C c : ℝ), 0 < C ∧ 0 < c ∧ ∀ s : ℕ, s₀ ≤ s →
          IsUnit (quotOperator F I T s 0) ∧
          ∀ (N : ℕ) (e : Fin N ≃ F.QuotMod s),
            (∃ W : Set (Coordinates.ComplexCoordinates N), IsOpen W ∧ 0 ∈ W ∧
              (∀ z ∈ W, ‖normalizedDet F I T s (ofCoords e z) - 1‖ < 1) ∧
              IsHolomorphicScalarIn W (logDetInCoords F I T e)) ∧
            VanishesOffAntipodal F s (logDetSecondDeriv F I T e) ∧
            IsCloseToLogNumber F I T s (logDetSecondDeriv F I T e) C c) ∧
        (∃ O : Set (Fin 4 → ℂ), IsOpen O ∧ imStrip δ ⊆ O ∧
          ∃ a : F.UnitQuot → F.UnitQuot → (Fin 4 → ℂ) → ℂ,
            (∀ c c', IsHolomorphicScalarIn O (a c c')) ∧
            ∀ p ∈ imStrip δ, ∀ εPlus εMinus : F.UnitQuot → ℂ,
              logNumber p (jetAlong F I I T p εPlus εMinus) =
                ∑' c, ∑' c', a c c' p * εPlus c * εMinus c') ∧
        (IsRealOnRealFields F I T →
          ∃ (s₀ : ℕ) (C c : ℝ), 0 < C ∧ 0 < c ∧ ∀ s : ℕ, s₀ ≤ s →
            ∀ (N : ℕ) (e : Fin N ≃ F.QuotMod s),
              (∀ᶠ v in 𝓝 (0 : Fin N → ℝ),
                LinearMap.det (quotOperator F I T s fun c =>
                  (ofRealCoords e v c : ℂ)) ≠ 0) ∧
              HasSecondFDerivAtZero (realLogAbsDetDiffInCoords F I T e) ∧
              VanishesOffAntipodal F s (realLogAbsDetSecondDeriv F I T e) ∧
              IsCloseToLogNumber F I T s
                (realLogAbsDetSecondDeriv F I T e) C c)
end YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
end
