import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings StepGas ClusterExpansionOfAStep BlockAverages
structure ResponseShapeBounds (ℓ : StepParameters) (t : ℕ) (x : ℝ) (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (P : ColdResponse ℓ.side t) (Q : HullResponse ℓ.side t Λ.Ω) : Prop where
  cold_linear : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (U : TorusField n), IsCold ℓ.threshold U →
    ∀ (c : ℝ) (f f' : PlaquetteWeight (fineSide ℓ.side t n)), P n y U (c • f + f') = c * P n y U f + P n y U f'
  hull_linear : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (U : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → Λ.Ω), IsLiveState ℓ x Dq U Y ω → ∀ (c : ℝ) (f f' : PlaquetteWeight (fineSide ℓ.side t n)),
    Q n y U Y ω (c • f + f') = c * Q n y U Y ω f + Q n y U Y ω f'
  cold_reads : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (U : TorusField n), IsCold ℓ.threshold U →
    ∀ f f' : PlaquetteWeight (fineSide ℓ.side t n), (∀ p, IsPlaquetteAt ℓ.side t y p → f p = f' p) →
      P n y U f = P n y U f'
  hull_reads : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (U : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → Λ.Ω), IsLiveState ℓ x Dq U Y ω → ∀ f f' : PlaquetteWeight (fineSide ℓ.side t n),
    (∀ p, IsPlaquetteAt ℓ.side t y p → f p = f' p) → Q n y U Y ω f = Q n y U Y ω f'
  cold_borel : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (f : PlaquetteWeight (fineSide ℓ.side t n)),
    (open Classical in Measurable fun U : TorusField n => if IsCold ℓ.threshold U then P n y U f else 0)
  hull_borel : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (Y : Finset (TorusSite n))
    (f : PlaquetteWeight (fineSide ℓ.side t n)),
    (open Classical in Measurable fun p : TorusField n × (Y → Λ.Ω) =>
      if IsLiveState ℓ x Dq p.1 Y p.2 then Q n y p.1 Y p.2 f else 0)
  cold_gauge : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion) (U : TorusField n),
    IsCold ℓ.threshold U → ∀ f : PlaquetteWeight (fineSide ℓ.side t n), P n y (gaugeTransform g U) f = P n y U f
  hull_gauge : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion)
    (U : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω), IsLiveState ℓ x Dq U Y ω →
    ∀ f : PlaquetteWeight (fineSide ℓ.side t n), Q n y (gaugeTransform g U) Y (Λ.act Y g ω) f = Q n y U Y ω f
  cold_translation : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (v : Fin 4 → ℤ) (U : TorusField n),
    IsCold ℓ.threshold U → ∀ f : PlaquetteWeight (fineSide ℓ.side t n),
    P n y (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) U)
        (translateWeight (fineTranslate ℓ.side t n fun i => (ℓ.side : ℤ) * v i) f) =
      P n (y + siteOfInt fun i => (ℓ.side : ℤ) * v i) U f
  hull_translation : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (v : Fin 4 → ℤ) (U : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω), IsLiveState ℓ x Dq U Y ω →
    ∀ f : PlaquetteWeight (fineSide ℓ.side t n),
    Q n y (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) U)
        (translateSet (siteOfInt fun i => (ℓ.side : ℤ) * v i) Y)
        (translateLabel (siteOfInt fun i => (ℓ.side : ℤ) * v i) Y ω)
        (translateWeight (fineTranslate ℓ.side t n fun i => (ℓ.side : ℤ) * v i) f) =
      Q n (y + siteOfInt fun i => (ℓ.side : ℤ) * v i) U Y ω f
  empty : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (U : TorusField n)
    (ω : (∅ : Finset (TorusSite n)) → Λ.Ω), IsLiveState ℓ x Dq U ∅ ω →
    ∀ f : PlaquetteWeight (fineSide ℓ.side t n), Q n y U ∅ ω f = P n y U f
structure ResponseDecayBounds (ℓ : StepParameters) (t : ℕ) (x : ℝ) (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ) (s : Λ.Ω → ℝ)
    (P : ColdResponse ℓ.side t) (Q : HullResponse ℓ.side t Λ.Ω) : Prop where
  forget : ∀ n n' [NeZero n] [NeZero n'], IsBlockTorusSide ℓ n → IsBlockTorusSide ℓ n' →
    ∀ (U : TorusField n) (U' : TorusField n') (Y : Finset (TorusSite n)) (Y' : Finset (TorusSite n')) (ω : Y → Λ.Ω)
      (ω' : Y' → Λ.Ω) (y : TorusSite n) (y' : TorusSite n') (m : ℕ) (f : PlaquetteWeight (fineSide ℓ.side t n))
      (f' : PlaquetteWeight (fineSide ℓ.side t n')),
      IsLiveState ℓ x Dq U Y ω → IsLiveState ℓ x Dq U' Y' ω' →
      (clusterRange x : ℝ) / 64 ≤ m → StatesAgreeNear ℓ U U' Y Y' ω ω' y y' m → WeightsAgreeAt ℓ.side t y y' f f' →
      |centeredHullResponse P Q n y U Y ω f - centeredHullResponse P Q n' y' U' Y' ω' f'| ≤
        (1 + siteScore s Y ω y) * Real.exp (-ℓ.decayRate * m) * weightNorm ℓ.side t f
  forget_cold : ∀ n n' [NeZero n] [NeZero n'], IsBlockTorusSide ℓ n → ℓ.n₀ ≤ n' →
    ∀ (U : TorusField n) (U' : TorusField n') (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω)
      (ω' : (∅ : Finset (TorusSite n')) → Λ.Ω)
      (y : TorusSite n) (y' : TorusSite n') (m : ℕ) (f : PlaquetteWeight (fineSide ℓ.side t n))
      (f' : PlaquetteWeight (fineSide ℓ.side t n')),
      IsLiveState ℓ x Dq U Y ω → IsCold ℓ.threshold U' →
      (clusterRange x : ℝ) / 64 ≤ m → StatesAgreeNear ℓ U U' Y ∅ ω ω' y y' m → WeightsAgreeAt ℓ.side t y y' f f' →
      |centeredHullResponse P Q n y U Y ω f - centeredResponse P n' y' U' f'| ≤
        (1 + siteScore s Y ω y) * Real.exp (-ℓ.decayRate * m) * weightNorm ℓ.side t f
  forget_both_cold : ∀ n n' [NeZero n] [NeZero n'], ℓ.n₀ ≤ n → ℓ.n₀ ≤ n' →
    ∀ (U : TorusField n) (U' : TorusField n') (y : TorusSite n) (y' : TorusSite n') (m : ℕ)
      (f : PlaquetteWeight (fineSide ℓ.side t n)) (f' : PlaquetteWeight (fineSide ℓ.side t n')),
      IsCold ℓ.threshold U → IsCold ℓ.threshold U' → (clusterRange x : ℝ) / 64 ≤ m → 2 * m + 2 < n →
      2 * m + 2 < n' → FieldsAgreeNear U U' y y' m → WeightsAgreeAt ℓ.side t y y' f f' →
      |centeredResponse P n y U f - centeredResponse P n' y' U' f'| ≤
        Real.exp (-ℓ.decayRate * m) * weightNorm ℓ.side t f
structure ResponseSizeBounds (ℓ : StepParameters) (K : ResponseParameters) (t : ℕ) (x : ℝ) (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ) (s : Λ.Ω → ℝ)
    (P : ColdResponse ℓ.side t) (Q : HullResponse ℓ.side t Λ.Ω) : Prop where
  size_cold : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (U : TorusField n), IsCold ℓ.threshold U →
    ∀ f : PlaquetteWeight (fineSide ℓ.side t n), |centeredResponse P n y U f| ≤ K.C₀ * weightNorm ℓ.side t f
  size_hull : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (U : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω), IsLiveState ℓ x Dq U Y ω →
    ∀ f : PlaquetteWeight (fineSide ℓ.side t n),
    |centeredHullResponse P Q n y U Y ω f| ≤ (K.C₀ + siteScore s Y ω y) * weightNorm ℓ.side t f
def coldStepSizeBound {R : StepSetup} (A : ResponseSetup R) : Prop :=
  ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (Y : TorusSite n) (V : TorusField n), IsCold R.params.threshold V →
    ∀ f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
      |centeredResponse A.coldStep n Y V f| ≤
        (A.responseParams.C₀ - 1) * weightNorm R.params.side (R.depth + 1) f
abbrev StepShapeBounds {R : StepSetup} (A : ResponseSetup R) (hL : CoarseLabelFacts R) : Prop :=
  ResponseShapeBounds R.params (R.depth + 1) R.nextCoupling (coarseLabelSpace R hL) (coarseWeightExpansion R)
    A.coldStep A.hullStep
abbrev StepDecayBounds {R : StepSetup} (A : ResponseSetup R) (hL : CoarseLabelFacts R) : Prop :=
  ResponseDecayBounds R.params (R.depth + 1) R.nextCoupling (coarseLabelSpace R hL) (coarseWeightExpansion R)
    (coarseLabelScore A.responseParams.s₁ A.score) A.coldStep A.hullStep
abbrev StepSizeBounds {R : StepSetup} (A : ResponseSetup R) (hL : CoarseLabelFacts R) : Prop :=
  ResponseSizeBounds R.params A.responseParams (R.depth + 1) R.nextCoupling (coarseLabelSpace R hL)
    (coarseWeightExpansion R) (coarseLabelScore A.responseParams.s₁ A.score) A.coldStep A.hullStep
end YangMills.Construction.WeightedResponses
end
