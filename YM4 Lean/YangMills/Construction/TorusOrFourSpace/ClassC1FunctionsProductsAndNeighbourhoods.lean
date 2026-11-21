import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.NeighbourhoodsOfACompactSet
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
def C1CompactSupportLipschitz (P : Params) (Y : Kind) : Prop :=
  (∀ g ∈ c1Set P Y, IsCompactQ P Y (supportQ P Y g) →
    (∀ x y, ENNReal.ofReal |g x - g y| ≤
      vecSupNormQ P Y (gradVec P Y g) * ENNReal.ofReal (quotDist P Y x y)) ∧
    IsLipschitzQ P Y g ∧
    ENNReal.ofReal (lipConstQ P Y g) ≤ vecSupNormQ P Y (gradVec P Y g) ∧
    vecSupNormQ P Y (gradVec P Y g) < ∞ ∧
    sharpNormQ P Y g ≤ ENNReal.ofReal (40 * P.M) * euclidC1Norm P Y g) ∧
  (∀ A : Set (Y.Pt P), c1SupportedIn P Y A ⊆ lipschitzSupportedIn P Y A) ∧
  (∀ n : ℕ, 1 ≤ n → sepC1Tuples P Y n ⊆ sepLipTuples P Y n)
def LipschitzCutoffProductMem (P : Params) (Y : Kind) : Prop :=
  ∀ χ : Y.Pt P → ℝ, (∀ y, χ y ∈ Set.Icc (0 : ℝ) 1) → IsLipschitzQ P Y χ →
    ∀ (A : Set (Y.Pt P)), ∀ h ∈ lipschitzSupportedIn P Y A,
      χ * h ∈ lipschitzSupportedIn P Y (A ∩ supportQ P Y χ) ∧
      sharpNormQ P Y (χ * h) ≤
        ENNReal.ofReal (1 + 40 * P.M * lipConstQ P Y χ) * sharpNormQ P Y h ∧
      (IsC1Fn P Y χ → h ∈ c1SupportedIn P Y A →
        χ * h ∈ c1SupportedIn P Y (A ∩ supportQ P Y χ))
def ThickeningsOpenCompactSeparated (P : Params) (Y : Kind) : Prop :=
  (∃ h₀ : IsCompactQ P Y ∅, ∀ (η : ℝ) (hη : 0 < η),
    openThickening P Y ∅ h₀ η hη = ∅ ∧ closedThickening P Y ∅ h₀ η hη = ∅) ∧
  (∀ (K : Set (Y.Pt P)) (hK : IsCompactQ P Y K) (η : ℝ) (hη : 0 < η),
    IsOpenQ P Y (openThickening P Y K hK η hη) ∧
    IsCompactQ P Y (closedThickening P Y K hK η hη) ∧
    K ⊆ openThickening P Y K hK η hη ∧
    openThickening P Y K hK η hη ⊆ closedThickening P Y K hK η hη) ∧
  (∀ (K K' : Set (Y.Pt P)) (hK : IsCompactQ P Y K) (hK' : IsCompactQ P Y K') (d : ℝ),
    0 < d → ENNReal.ofReal d ≤ setInfDist P Y K K' →
    ∀ (η η' : ℝ) (hη : 0 < η) (hη' : 0 < η'),
      ENNReal.ofReal (d - η - η') ≤
        setInfDist P Y (closedThickening P Y K hK η hη)
          (closedThickening P Y K' hK' η' hη')) ∧
  (∀ (K : Set (Y.Pt P)) (hK : IsCompactQ P Y K) (η : ℝ) (hη : 0 < η) (ρ : ℝ≥0∞),
    0 < ρ → ρ < ∞ → K ⊆ centredBall P Y ρ →
    closedThickening P Y K hK η hη ⊆ closedBallAbout P Y (origin P Y) (ρ.toReal + η))
def CompactSubsetClosedBallOfDiam (P : Params) (Y : Kind) : Prop :=
  ∀ K : Set (Y.Pt P), IsCompactQ P Y K → ∀ R : ℝ, 0 < R →
    setDiam P Y K ≤ ENNReal.ofReal R →
    ∃ B, IsClosedBallWithRadius P Y B R ∧ K ⊆ B
def C1ProductsAndThickenings.Statement : Prop :=
  ∀ (P : Params) (Y : Kind),
    C1CompactSupportLipschitz P Y ∧
    LipschitzCutoffProductMem P Y ∧
    ThickeningsOpenCompactSeparated P Y ∧
    CompactSubsetClosedBallOfDiam P Y
end YangMills.Construction.PeriodicSpace
