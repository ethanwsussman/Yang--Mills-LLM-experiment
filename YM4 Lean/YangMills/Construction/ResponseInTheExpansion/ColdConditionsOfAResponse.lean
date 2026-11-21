import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.SharesAreACurvatureFamily
import YangMills.Construction.ResponseInTheExpansion.ExpansionOfTheResponse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WeightedResponses
open TorusFields TorusLumps StepCosts ShareFamilies BlockAverages
def responseAtOne {L t : ℕ} (P : ColdResponse L t) : LocalDensity := fun n y W =>
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    P n y W (constOneWeight _)
def responseSubShare (a : ℝ) {L t : ℕ} (P : ColdResponse L t) (c : ℝ) : LocalDensity := fun n y W =>
  responseAtOne P n y W - c * levelShareFamily a L t n y W
structure HalfDensityBounds (ℓ : StepParameters) (E η₃ : ℝ) (F : LocalDensity) : Prop where
  admissible : IsAdmissibleDensity ℓ F
  decay : DerivDecay ℓ F fun k m => 1 / 2 * (if k = 3 then E / η₃ else E) / ℓ.weight m
  compare : LocalComparison ℓ (centeredFamily F) fun m => 1 / 2 * E / ℓ.weight m
structure IsTotalRemainder (ℓ : StepParameters) {t : ℕ} (P : ColdResponse ℓ.side t) (c : ℝ)
    (F : LocalDensity) : Prop where
  sum_eq : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ W : TorusField n, IsCold ℓ.threshold W →
    ∑ y, centeredResponse P n y W (constOneWeight _) =
      c * actionAtLevel ℓ.coupling ℓ.side t Finset.univ W + ∑ y, centered F n y W
structure RemainderBounds (ℓ : StepParameters) (K : ResponseParameters) (t : ℕ)
    (P : ColdResponse ℓ.side t) : Prop where
  smooth : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ∀ h : PlaquetteWeight (fineSide ℓ.side t n), ContDiffThreeAt (responseRemainder P n y h) W
  decay : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ∀ (h : PlaquetteWeight (fineSide ℓ.side t n)) (k : ℕ) (c : Fin k → TorusBond n)
      (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
      AreUnitVectors X →
      |mixedDeriv (responseRemainder P n y h) W c X| ≤
        (if k = 3 then K.Kc / K.η₃ else K.Kc) * weightLipschitz ℓ.side t h / ℓ.weight (supportDiam y c)
  compare : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W W' : TorusField n) (m : ℕ), 2 * m + 2 < n →
    IsCold ℓ.threshold W → IsCold ℓ.threshold W' → FieldsAgreeNear W W' y y m →
    ∀ (h : PlaquetteWeight (fineSide ℓ.side t n)) (k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4)
      (X : Fin k → imaginaryQuaternions), k ≤ 2 →
      (∀ l, TorusFields.BondOffsetInBox m (b l)) → AreUnitVectors X →
      |mixedDeriv (centeredRemainder P n y h) W (fun l => bondFrom y (b l)) X -
          mixedDeriv (centeredRemainder P n y h) W' (fun l => bondFrom y (b l)) X| ≤
        K.Kc * weightLipschitz ℓ.side t h / ℓ.weight m
structure ColdResponseBounds (ℓ : StepParameters) (K : ResponseParameters) (t : ℕ) (x c : ℝ)
    (P : ColdResponse ℓ.side t) (Ra Rb : LocalDensity) : Prop where
  share_site : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    centeredResponse P n y W (constOneWeight _) =
      c * levelShare ℓ.coupling ℓ.side t Finset.univ y W + centered Ra n y W
  share_total : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ W : TorusField n, IsCold ℓ.threshold W →
    ∑ y, centeredResponse P n y W (constOneWeight _) =
      c * actionAtLevel ℓ.coupling ℓ.side t Finset.univ W + ∑ y, centered Rb n y W
  site_family : ColdDensityBounds ℓ (K.Ka * x ^ (-(1 / 2) : ℝ)) (K.Ka * x ^ (-(1 / 2) : ℝ) / K.η₃) Ra
  total_family : ColdDensityBounds ℓ (K.Kb * x⁻¹) (K.Kb * x⁻¹ / K.η₃) Rb
  remainder : RemainderBounds ℓ K t P
end WeightedResponses
end YangMills.Construction
end
