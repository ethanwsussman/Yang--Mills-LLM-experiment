import YangMills.Construction.EuclideanFunctionals.StandingDataOfTheStudyFromOneInsertionToPlates
import YangMills.Construction.EuclideanFunctionals.TransportOfAReconstructionAndThePlateBoundInACoordinatePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open RealPlane
namespace TimeShiftAndFractions
variable {m : SharpScale} {S : ConnFamily}
def ShiftUpContracts (σ : EuclidFunctionalWithRecon m S) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ A ∈ finCombIn upperHalf,
    (EuclidMotion.transl (t • timeVec)).actFree A ∈ finCombIn upperHalf ∧
      ‖reconClass σ ((EuclidMotion.transl (t • timeVec)).actFree A)‖ ≤ ‖reconClass σ A‖
def InsertionTimeShift (σ : EuclidFunctionalWithRecon m S) : Prop :=
  ∀ c t : ℝ, 0 < c → |t| < c →
    ∀ F ∈ finCombIn {x | c < x 3}, ∀ G ∈ finCombIn {x | c < x 3},
      ∀ f ∈ C1c ℂ, supp f ⊆ {x | |x 3 - t| < c - |t|} →
        supp f ⊆ {x | |x 3| < c} ∧
        supp ((EuclidMotion.transl ((-t) • timeVec)).actFn f) ⊆ {x | |x 3| < c - |t|} ∧
        (EuclidMotion.transl (t • timeVec)).actFree F ∈ finCombIn {x | c - |t| < x 3} ∧
        (EuclidMotion.transl ((-t) • timeVec)).actFree G ∈ finCombIn {x | c - |t| < x 3} ∧
        insertion S F f G =
          insertion S ((EuclidMotion.transl (t • timeVec)).actFree F)
            ((EuclidMotion.transl ((-t) • timeVec)).actFn f)
            ((EuclidMotion.transl ((-t) • timeVec)).actFree G) ∧
        heightNorm σ (c - |t|) ((EuclidMotion.transl (t • timeVec)).actFree F) ≤
          heightNorm σ c F ∧
        heightNorm σ (c - |t|) ((EuclidMotion.transl ((-t) • timeVec)).actFree G) ≤
          heightNorm σ c G
def fractionConstants (p c : ℝ) (C : (RealPlane → ℝ) → ℝ) (φ : RealPlane → ℝ) : ℝ :=
  (2 / (1 - 4 * c)) ^ p * C φ
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S),
    ShiftUpContracts σ ∧ InsertionTimeShift σ ∧
    (∀ α ∈ complexProfiles, profileL1Norm α = l1Norm α) ∧
    ∀ (p : ℝ) (C : (RealPlane → ℝ) → ℝ) (cS : ℝ) (h : ProductBoundHolds σ p C cS),
      (∀ c ∈ productBoundFractions, ProductBoundHolds σ p (fractionConstants p c C) c) ∧
      ∀ (c : ℝ) (hc : c ∈ productBoundFractions),
        ProductBoundWithExponent σ h.pos_exponent hc ∧
          ImagePlaneProductBound σ 1 h.pos_exponent hc
end TimeShiftAndFractions
end YangMills.Construction.EuclideanFunctionals
