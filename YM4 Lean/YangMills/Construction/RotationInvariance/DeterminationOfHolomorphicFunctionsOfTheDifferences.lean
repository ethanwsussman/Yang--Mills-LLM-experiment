import YangMills.Construction.RotationInvariance.ApertureTimeGapsAndComplexAnalysisInThePlane
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ForwardTube
open RealPlane
def realTuplesTimeAbove (p : ℕ) (η : ℝ) : Set (Fin p → RealPlane) :=
  {v | ∀ i, η < v i 0}
def complexifyRealTuple {p : ℕ} (v : Fin p → RealPlane) : Fin p → ℂ × ℂ :=
  fun i => embedPlane (v i)
def complexifyProfiles {n : ℕ} (b : Fin n → RealPlane → ℝ) :
    Fin n → RealPlane → ℂ :=
  fun i y => (b i y : ℂ)
def SmoothTimeSeparated {n : ℕ} (η : ℝ) (b : Fin n → RealPlane → ℝ) : Prop :=
  (∀ i, ContDiff ℝ ∞ (b i)) ∧ TimeSeparated η (complexifyProfiles b)
def differencesIntegral {n : ℕ} (b : Fin n → RealPlane → ℝ)
    (f : (Fin (n - 1) → ℂ × ℂ) → ℂ) : ℂ :=
  profileIntegral (complexifyProfiles b)
    fun y => f (complexifyRealTuple (successiveDifferences y))
namespace HolomorphicDifferences
def determinedByProductIntegrals : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ η : ℝ, 0 ≤ η →
    (∀ b : Fin n → RealPlane → ℂ, TimeSeparated η b →
      ∀ y : Fin n → RealPlane, (∀ i, y i ∈ tsupport (b i)) →
        successiveDifferences y ∈ realTuplesTimeAbove (n - 1) η) ∧
    ∀ (D : Set (Fin (n - 1) → ℂ × ℂ)) (f : (Fin (n - 1) → ℂ × ℂ) → ℂ),
      IsOpen D → IsConnected D →
      (∀ v ∈ realTuplesTimeAbove (n - 1) η, complexifyRealTuple v ∈ D) →
      HolomorphicOnTuples D f →
      ((∀ b : Fin n → RealPlane → ℝ, SmoothTimeSeparated η b →
          differencesIntegral b f = 0) → ∀ z ∈ D, f z = 0) ∧
      ((∀ b : Fin n → RealPlane → ℝ, SmoothTimeSeparated η b →
          (differencesIntegral b f).im = 0) →
        ∀ v ∈ realTuplesTimeAbove (n - 1) η, (f (complexifyRealTuple v)).im = 0)
end HolomorphicDifferences
end YangMills.Construction.ForwardTube
end
