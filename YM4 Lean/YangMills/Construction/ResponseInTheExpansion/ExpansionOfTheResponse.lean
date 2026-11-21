import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.BlockAverages YangMills.Construction.StepCosts
variable {n : ℕ}
def siteScore {Ω : Type} (s : Ω → ℝ) (Y : Finset (TorusSite n)) (ω : Y → Ω) (y : TorusSite n) : ℝ :=
  open Classical in if hy : y ∈ Y then s (ω ⟨y, hy⟩) else 0
structure PriceBoundsScore (ℓ : StepParameters) (x : ℝ) (Λ : LabelSpace)
    (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (s : Λ.Ω → ℝ) : Prop where
  nonneg : ∀ w, 0 ≤ s w
  borel : Measurable s
  gauge : ∀ (n : ℕ) [NeZero n] (Y : Finset (TorusSite n)) (g : TorusSite n → UnitQuaternion) (ω : Y → Λ.Ω) (y : Y),
    s (Λ.act Y g ω y) = s (ω y)
  price : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω)
    (P : Finset (Finset (TorusSite n))), IsHullState ℓ (clusterRange x) W Y →
    P ⊆ chainComponents (clusterRange x) Y →
    (∀ X ∈ chainComponents (clusterRange x) Y \ P, Φ n W Y ω X ≠ 0) →
    (open Classical in
      ∫⁻ ν, (if ∃ X ∈ P, Φ n W Y (glueLabel Y (P.biUnion id) ω ν) X = 0 then 0 else
        ENNReal.ofReal ((∏ X ∈ P, Φ n W Y (glueLabel Y (P.biUnion id) ω ν) X) *
          Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
            φ n y W Y (glueLabel Y (P.biUnion id) ω ν)) *
          Real.exp (∑ y : (P.biUnion id : Finset (TorusSite n)), s (ν y))))
        ∂(Measure.pi fun _ : (P.biUnion id : Finset (TorusSite n)) => Λ.μ)) ≤
      ENNReal.ofReal (Real.exp (-(x * ℓ.κ * ℓ.threshold ^ 2 *
          ((open Classical in (torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).card : ℝ)) -
        ℓ.κ₁ * x * ℓ.threshold ^ 2 * (excessLength ℓ (clusterRange x) (P.biUnion id) W : ℝ)))
structure ResponseParameters where
  η₃ : ℝ
  N₀ : ℝ
  nr : ℕ
  Kc : ℝ
  C₀ : ℝ
  s₁ : ℝ
  Ka : ℝ
  Kb : ℝ
  Cstar : ℝ
structure ResponseParameters.Admissible (K : ResponseParameters) (ℓ : StepParameters) : Prop where
  η₃_pos : 0 < K.η₃
  η₃_le : K.η₃ ≤ 1
  E₃_eq : ℓ.E₃ = ℓ.E / K.η₃
  N₀_nonneg : 0 ≤ K.N₀
  Kc_ge : 1 ≤ K.Kc
  C₀_eq : K.C₀ = 12 + 40 * ℓ.coupling + 8 * K.N₀ + 2 * K.Kc
  s₁_eq : K.s₁ = 2 * (ℓ.side : ℝ) ^ 4 * (K.C₀ + 2) + 40 * ℓ.coupling
  Ka_nonneg : 0 ≤ K.Ka
  Kb_nonneg : 0 ≤ K.Kb
  Cstar_nonneg : 0 ≤ K.Cstar
structure ColdDensityBounds (ℓ : StepParameters) (E E₃ : ℝ) (f : LocalDensity) : Prop where
  smooth : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ContDiffThreeAt (f n y) W
  gauge : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion) (W : TorusField n),
    IsCold ℓ.threshold W → f n y (gaugeTransform g W) = f n y W
  translation : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y u : TorusSite n) (W : TorusField n),
    IsCold ℓ.threshold W → f n y (TorusFields.translate u W) = f n (y + u) W
  decay : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (f n y) W c X| ≤ (if k = 3 then E₃ else E) / ℓ.weight (supportDiam y c)
  local_density : ∀ n n' [NeZero n] [NeZero n'], ℓ.n₀ ≤ n → ℓ.n₀ ≤ n' →
    ∀ (y : TorusSite n) (y' : TorusSite n') (W : TorusField n) (W' : TorusField n') (m : ℕ),
      2 * m + 2 < n → 2 * m + 2 < n' →
      IsCold ℓ.threshold W → IsCold ℓ.threshold W' → FieldsAgreeNear W W' y y' m →
      ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
        (∀ l, BondOffsetInBox m (h l)) → AreUnitVectors X →
        |mixedDeriv (centered f n y) W (fun l => bondFrom y (h l)) X -
            mixedDeriv (centered f n' y') W' (fun l => bondFrom y' (h l)) X| ≤ E / ℓ.weight m
  no_curvature_term : ∀ A A' : Fin 4 → Fin 4 → imaginaryQuaternions,
    (∀ μ ν, A μ ν = - A ν μ) → (∀ μ ν, A' μ ν = - A' ν μ) →
    ∑' cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4),
      secondDerivLimit f cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2) = 0
abbrev ColdResponse (L t : ℕ) : Type :=
  (n : ℕ) → [NeZero n] → TorusSite n → TorusField n → PlaquetteWeight (fineSide L t n) → ℝ
abbrev HullResponse (L t : ℕ) (Ω : Type) : Type :=
  (n : ℕ) → [NeZero n] → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Ω) →
    PlaquetteWeight (fineSide L t n) → ℝ
def centeredResponse {L t : ℕ} (P : ColdResponse L t) (n : ℕ) [NeZero n] (y : TorusSite n) (W : TorusField n)
    (h : PlaquetteWeight (fineSide L t n)) : ℝ :=
  P n y W h - P n y (trivialField n) h
def centeredHullResponse {L t : ℕ} {Ω : Type} (P : ColdResponse L t) (Q : HullResponse L t Ω) (n : ℕ) [NeZero n]
    (y : TorusSite n) (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Ω)
    (h : PlaquetteWeight (fineSide L t n)) : ℝ :=
  Q n y W Y ω h - P n y (trivialField n) h
def responseRemainder {L t : ℕ} [NeZero L] (P : ColdResponse L t) (n : ℕ) [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight (fineSide L t n)) (W : TorusField n) : ℝ :=
  P n y W h - blockMean L t n y h * P n y W (constOneWeight _)
def centeredRemainder {L t : ℕ} [NeZero L] (P : ColdResponse L t) (n : ℕ) [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight (fineSide L t n)) (W : TorusField n) : ℝ :=
  responseRemainder P n y h W - responseRemainder P n y h (trivialField n)
def responseMass (ℓ : StepParameters) (t : ℕ) (x : ℝ) (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Q : HullResponse ℓ.side t Λ.Ω) (n : ℕ) [NeZero n] (y : TorusSite n) (W : TorusField n) : ℝ :=
  open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange x) W),
    ∫ ω, Q n y W Y ω (constOneWeight _) * Dq n W Y ω ∂(Measure.pi fun _ : Y => Λ.μ)
def IsLiveState (ℓ : StepParameters) (x : ℝ) {Ω : Type}
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Ω) → ℝ) {n : ℕ} [NeZero n]
    (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Ω) : Prop :=
  IsHullState ℓ (clusterRange x) W Y ∧ 0 < Dq n W Y ω
structure ResponseBounds (ℓ : StepParameters) (K : ResponseParameters) (t : ℕ) (x al : ℝ) (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ) (s : Λ.Ω → ℝ)
    (P : ColdResponse ℓ.side t) (Q : HullResponse ℓ.side t Λ.Ω) (Ra Rb : LocalDensity) : Prop where
  cold_linear : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ∀ (c : ℝ) (h h' : PlaquetteWeight (fineSide ℓ.side t n)), P n y W (c • h + h') = c * P n y W h + P n y W h'
  hull_linear : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (W : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω), IsLiveState ℓ x Dq W Y ω →
    ∀ (c : ℝ) (h h' : PlaquetteWeight (fineSide ℓ.side t n)),
    Q n y W Y ω (c • h + h') = c * Q n y W Y ω h + Q n y W Y ω h'
  cold_reads : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ∀ h h' : PlaquetteWeight (fineSide ℓ.side t n), (∀ p, IsPlaquetteAt ℓ.side t y p → h p = h' p) →
      P n y W h = P n y W h'
  hull_reads : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (W : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω), IsLiveState ℓ x Dq W Y ω →
    ∀ h h' : PlaquetteWeight (fineSide ℓ.side t n),
    (∀ p, IsPlaquetteAt ℓ.side t y p → h p = h' p) → Q n y W Y ω h = Q n y W Y ω h'
  cold_borel : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side t n)),
    (open Classical in Measurable fun W : TorusField n => if IsCold ℓ.threshold W then P n y W h else 0)
  hull_borel : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (Y : Finset (TorusSite n))
    (h : PlaquetteWeight (fineSide ℓ.side t n)),
    (open Classical in Measurable fun p : TorusField n × (Y → Λ.Ω) =>
      if IsLiveState ℓ x Dq p.1 Y p.2 then Q n y p.1 Y p.2 h else 0)
  cold_gauge : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion)
    (W : TorusField n), IsCold ℓ.threshold W → ∀ h : PlaquetteWeight (fineSide ℓ.side t n),
    P n y (gaugeTransform g W) h = P n y W h
  hull_gauge : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion)
    (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω), IsLiveState ℓ x Dq W Y ω →
    ∀ h : PlaquetteWeight (fineSide ℓ.side t n), Q n y (gaugeTransform g W) Y (Λ.act Y g ω) h = Q n y W Y ω h
  cold_translation : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (v : Fin 4 → ℤ) (W : TorusField n),
    IsCold ℓ.threshold W → ∀ h : PlaquetteWeight (fineSide ℓ.side t n),
    P n y (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W)
        (translateWeight (fineTranslate ℓ.side t n fun i => (ℓ.side : ℤ) * v i) h) =
      P n (y + siteOfInt fun i => (ℓ.side : ℤ) * v i) W h
  hull_translation : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (v : Fin 4 → ℤ)
    (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω), IsLiveState ℓ x Dq W Y ω →
    ∀ h : PlaquetteWeight (fineSide ℓ.side t n),
    Q n y (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W)
        (translateSet (siteOfInt fun i => (ℓ.side : ℤ) * v i) Y)
        (translateLabel (siteOfInt fun i => (ℓ.side : ℤ) * v i) Y ω)
        (translateWeight (fineTranslate ℓ.side t n fun i => (ℓ.side : ℤ) * v i) h) =
      Q n (y + siteOfInt fun i => (ℓ.side : ℤ) * v i) W Y ω h
  empty : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (W : TorusField n)
    (ω : (∅ : Finset (TorusSite n)) → Λ.Ω), IsLiveState ℓ x Dq W ∅ ω →
    ∀ h : PlaquetteWeight (fineSide ℓ.side t n), Q n y W ∅ ω h = P n y W h
  mass_integrable : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (W : TorusField n)
    (Y : Finset (TorusSite n)), IsHullState ℓ (clusterRange x) W Y →
    Integrable (fun ω : Y → Λ.Ω => Q n y W Y ω (constOneWeight _) * Dq n W Y ω) (Measure.pi fun _ : Y => Λ.μ)
  mass_carried : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (g : TorusIsometry) (y : TorusSite n)
    (W W' : TorusField n), g.Transports W W' →
    responseMass ℓ t x Λ Dq Q n (g.mapSite y) W' = responseMass ℓ t x Λ Dq Q n y W
  cold_carried : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (g : TorusIsometry) (y : TorusSite n) (W W' : TorusField n),
    IsCold ℓ.threshold W → g.Transports W W' →
    P n (g.mapSite y) W' (constOneWeight _) = P n y W (constOneWeight _)
  share_site : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    centeredResponse P n y W (constOneWeight _) =
      al * levelShare ℓ.coupling ℓ.side t Finset.univ y W + centered Ra n y W
  share_total : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ W : TorusField n, IsCold ℓ.threshold W →
    ∑ y, centeredResponse P n y W (constOneWeight _) =
      al * actionAtLevel ℓ.coupling ℓ.side t Finset.univ W + ∑ y, centered Rb n y W
  site_family : ColdDensityBounds ℓ (K.Ka * x ^ (-(1 / 2) : ℝ)) (K.Ka * x ^ (-(1 / 2) : ℝ) / K.η₃) Ra
  total_family : ColdDensityBounds ℓ (K.Kb * x⁻¹) (K.Kb * x⁻¹ / K.η₃) Rb
  remainder_smooth : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ∀ h : PlaquetteWeight (fineSide ℓ.side t n), ContDiffThreeAt (responseRemainder P n y h) W
  remainder_decay : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ∀ (h : PlaquetteWeight (fineSide ℓ.side t n)) (k : ℕ) (c : Fin k → TorusBond n)
      (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (responseRemainder P n y h) W c X| ≤
        (if k = 3 then K.Kc / K.η₃ else K.Kc) * weightLipschitz ℓ.side t h / ℓ.weight (supportDiam y c)
  remainder_local : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W W' : TorusField n) (m : ℕ),
    2 * m + 2 < n → IsCold ℓ.threshold W → IsCold ℓ.threshold W' → FieldsAgreeNear W W' y y m →
    ∀ (h : PlaquetteWeight (fineSide ℓ.side t n)) (k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4)
      (X : Fin k → imaginaryQuaternions), k ≤ 2 → (∀ l, BondOffsetInBox m (b l)) → AreUnitVectors X →
      |mixedDeriv (centeredRemainder P n y h) W (fun l => bondFrom y (b l)) X -
          mixedDeriv (centeredRemainder P n y h) W' (fun l => bondFrom y (b l)) X| ≤
        K.Kc * weightLipschitz ℓ.side t h / ℓ.weight m
  forget : ∀ n n' [NeZero n] [NeZero n'], IsBlockTorusSide ℓ n → IsBlockTorusSide ℓ n' →
    ∀ (W : TorusField n) (W' : TorusField n') (Y : Finset (TorusSite n)) (Y' : Finset (TorusSite n'))
      (ω : Y → Λ.Ω) (ω' : Y' → Λ.Ω) (y : TorusSite n) (y' : TorusSite n') (m : ℕ)
      (h : PlaquetteWeight (fineSide ℓ.side t n)) (h' : PlaquetteWeight (fineSide ℓ.side t n')),
      IsLiveState ℓ x Dq W Y ω → IsLiveState ℓ x Dq W' Y' ω' →
      (clusterRange x : ℝ) / 64 ≤ m → StatesAgreeNear ℓ W W' Y Y' ω ω' y y' m →
      WeightsAgreeAt ℓ.side t y y' h h' →
      |centeredHullResponse P Q n y W Y ω h - centeredHullResponse P Q n' y' W' Y' ω' h'| ≤
        (1 + siteScore s Y ω y) * Real.exp (-ℓ.decayRate * m) * weightNorm ℓ.side t h
  forget_cold : ∀ n n' [NeZero n] [NeZero n'], IsBlockTorusSide ℓ n → ℓ.n₀ ≤ n' →
    ∀ (W : TorusField n) (W' : TorusField n') (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω)
      (ω' : (∅ : Finset (TorusSite n')) → Λ.Ω) (y : TorusSite n) (y' : TorusSite n') (m : ℕ)
      (h : PlaquetteWeight (fineSide ℓ.side t n)) (h' : PlaquetteWeight (fineSide ℓ.side t n')),
      IsLiveState ℓ x Dq W Y ω → IsCold ℓ.threshold W' →
      (clusterRange x : ℝ) / 64 ≤ m → StatesAgreeNear ℓ W W' Y ∅ ω ω' y y' m →
      WeightsAgreeAt ℓ.side t y y' h h' →
      |centeredHullResponse P Q n y W Y ω h - centeredResponse P n' y' W' h'| ≤
        (1 + siteScore s Y ω y) * Real.exp (-ℓ.decayRate * m) * weightNorm ℓ.side t h
  forget_both_cold : ∀ n n' [NeZero n] [NeZero n'], ℓ.n₀ ≤ n → ℓ.n₀ ≤ n' →
    ∀ (W : TorusField n) (W' : TorusField n') (y : TorusSite n) (y' : TorusSite n') (m : ℕ)
      (h : PlaquetteWeight (fineSide ℓ.side t n)) (h' : PlaquetteWeight (fineSide ℓ.side t n')),
      IsCold ℓ.threshold W → IsCold ℓ.threshold W' → (clusterRange x : ℝ) / 64 ≤ m →
      2 * m + 2 < n → 2 * m + 2 < n' →
      FieldsAgreeNear W W' y y' m → WeightsAgreeAt ℓ.side t y y' h h' →
      |centeredResponse P n y W h - centeredResponse P n' y' W' h'| ≤
        Real.exp (-ℓ.decayRate * m) * weightNorm ℓ.side t h
  size_cold : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
    ∀ h : PlaquetteWeight (fineSide ℓ.side t n), |centeredResponse P n y W h| ≤ K.C₀ * weightNorm ℓ.side t h
  size_hull : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (y : TorusSite n) (W : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω), IsLiveState ℓ x Dq W Y ω →
    ∀ h : PlaquetteWeight (fineSide ℓ.side t n),
    |centeredHullResponse P Q n y W Y ω h| ≤ (K.C₀ + siteScore s Y ω y) * weightNorm ℓ.side t h
def HasResponseBoundsWith (ℓ : StepParameters) (K : ResponseParameters) (t : ℕ) (x al : ℝ) (D : TorusFunctional)
    (Λ : LabelSpace) (s : Λ.Ω → ℝ) (P : ColdResponse ℓ.side t) (Q : HullResponse ℓ.side t Λ.Ω)
    (Ra Rb : LocalDensity) : Prop :=
  HasExpansion ℓ t x D ∧ ∃ f : LocalDensity, ColdExpansion ℓ t x D f ∧
    ∃ (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
      (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
      (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ),
      HullExpansion ℓ t x D f Λ Dq Φ φ ∧ PriceBoundsScore ℓ x Λ Φ φ s ∧
        ResponseBounds ℓ K t x al Λ Dq s P Q Ra Rb
end YangMills.Construction.WeightedResponses
end
