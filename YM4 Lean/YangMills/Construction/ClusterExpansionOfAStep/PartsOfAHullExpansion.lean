import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
structure HullExpansionStates (ℓ : StepParameters) (x : ℝ) (D : TorusFunctional) (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ) : Prop where
  nonneg : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω),
    IsHullState ℓ (clusterRange x) W Y → 0 ≤ Dq n W Y ω
  sum : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ W : TorusField n,
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange x) W),
      ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ)) = ENNReal.ofReal (D n W)
  gauge : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω)
    (g : TorusSite n → UnitQuaternion), IsHullState ℓ (clusterRange x) W Y →
    Dq n (gaugeTransform g W) Y (Λ.act Y g ω) = Dq n W Y ω
  translation : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω)
    (u : TorusSite n), IsBlockTranslation ℓ u → IsHullState ℓ (clusterRange x) W Y →
    Dq n (TorusFields.translate u W) (translateSet u Y) (translateLabel u Y ω) = Dq n W Y ω
  factor_nonneg : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → Λ.Ω) (X : Finset (TorusSite n)), 0 ≤ Φ n W Y ω X
  one_rule : ∀ n n' [NeZero n] [NeZero n'], IsBlockTorusSide ℓ n → IsBlockTorusSide ℓ n' →
    ∀ (W : TorusField n) (W' : TorusField n') (Y : Finset (TorusSite n)) (Y' : Finset (TorusSite n')) (ω : Y → Λ.Ω)
      (ω' : Y' → Λ.Ω) (X : Finset (TorusSite n)) (X' : Finset (TorusSite n')) (y : TorusSite n) (y' : TorusSite n')
      (m : ℕ),
      2 * m + 2 < n → 2 * m + 2 < n' → X ⊆ Y → X' ⊆ Y' → SameBlockPosition ℓ y y' →
      CongruentInBoxes X X' y y' m → FieldsAgreeOnSet W W' y y' m X → LabelsAgreeNear Y Y' ω ω' y y' m X →
      Φ n W Y ω X = Φ n' W' Y' ω' X'
  reads_class : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (W W' : TorusField n) (Y Y' : Finset (TorusSite n))
      (ω : Y → Λ.Ω) (ω' : Y' → Λ.Ω) (X : Finset (TorusSite n)), X ⊆ Y → X ⊆ Y' →
      (∀ b : TorusBond n, b.1 ∈ X → b.1 + TorusFields.unitStep n b.2 ∈ X → W b.1 b.2 = W' b.1 b.2) →
      (∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), z ∈ X → ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) →
      Φ n W Y ω X = Φ n W' Y' ω' X
structure HullExpansionDisplay (ℓ : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) (f : LocalDensity)
    (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ) : Prop where
  form : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω),
    IsHullState ℓ (clusterRange x) W Y →
    Dq n W Y ω = D n (trivialField n) *
      Real.exp (-x * actionAtLevel ℓ.coupling ℓ.side t
          (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W +
        ∑ y, φ n y W Y ω) * ∏ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X
  empty : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (ω : (∅ : Finset (TorusSite n)) → Λ.Ω)
    (y : TorusSite n), IsHullState ℓ (clusterRange x) W ∅ → φ n y W ∅ ω = centered f n y W
  forget : ∀ n n' [NeZero n] [NeZero n'], IsBlockTorusSide ℓ n → IsBlockTorusSide ℓ n' →
    ∀ (W : TorusField n) (W' : TorusField n') (Y : Finset (TorusSite n)) (Y' : Finset (TorusSite n'))
      (ω : Y → Λ.Ω) (ω' : Y' → Λ.Ω) (y : TorusSite n) (y' : TorusSite n') (m : ℕ),
      IsHullState ℓ (clusterRange x) W Y → IsHullState ℓ (clusterRange x) W' Y' →
      (∀ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X ≠ 0) →
      (∀ X ∈ chainComponents (clusterRange x) Y', Φ n' W' Y' ω' X ≠ 0) →
      (clusterRange x : ℝ) / 64 ≤ m → StatesAgreeNear ℓ W W' Y Y' ω ω' y y' m →
      |φ n y W Y ω - φ n' y' W' Y' ω'| ≤ Real.exp (-ℓ.decayRate * m)
  forget_cold : ∀ n n' [NeZero n] [NeZero n'], IsBlockTorusSide ℓ n → ℓ.n₀ ≤ n' →
    ∀ (W : TorusField n) (W' : TorusField n') (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω)
      (ω' : (∅ : Finset (TorusSite n')) → Λ.Ω) (y : TorusSite n) (y' : TorusSite n') (m : ℕ),
      IsHullState ℓ (clusterRange x) W Y → IsCold ℓ.threshold W' →
      (∀ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X ≠ 0) →
      (clusterRange x : ℝ) / 64 ≤ m → StatesAgreeNear ℓ W W' Y ∅ ω ω' y y' m →
      |φ n y W Y ω - centered f n' y' W'| ≤ Real.exp (-ℓ.decayRate * m)
structure HullExpansionRegularity (ℓ : StepParameters) (x : ℝ) (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ) : Prop where
  borel : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ Y : Finset (TorusSite n),
    (open Classical in
      Measurable fun p : TorusField n × (Y → Λ.Ω) =>
        if IsHullState ℓ (clusterRange x) p.1 Y then Dq n p.1 Y p.2 else 0) ∧
    (∀ X : Finset (TorusSite n), Measurable fun p : TorusField n × (Y → Λ.Ω) => Φ n p.1 Y p.2 X) ∧
    (∀ y : TorusSite n, open Classical in
      Measurable fun p : TorusField n × (Y → Λ.Ω) =>
        if IsHullState ℓ (clusterRange x) p.1 Y ∧ ∀ X ∈ chainComponents (clusterRange x) Y, Φ n p.1 Y p.2 X ≠ 0
        then φ n y p.1 Y p.2 else 0)
  smooth : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω),
    IsHullState ℓ (clusterRange x) W Y → 0 < Dq n W Y ω →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      (∀ l, ∀ z ∈ Y, clusterRange x ≤ supDist (c l).1 z) →
      ContDiffAt ℝ 3 (fun s : Fin k → ℝ => Dq n (perturb c X s W) Y ω) 0 ∧
      (1 ≤ k → k ≤ 3 → AreUnitVectors X →
        |mixedDeriv (fun W' => Real.log (Dq n W' Y ω)) W c X| ≤ (ℓ.derivBound * x) ^ k)
structure HullExpansionPrice (ℓ : StepParameters) (x : ℝ) (Λ : LabelSpace)
    (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ) : Prop where
  price : ∀ n [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω)
    (P : Finset (Finset (TorusSite n))), IsHullState ℓ (clusterRange x) W Y →
    P ⊆ chainComponents (clusterRange x) Y →
    (∀ X ∈ chainComponents (clusterRange x) Y \ P, Φ n W Y ω X ≠ 0) →
    (open Classical in
      ∫⁻ ν, (if ∃ X ∈ P, Φ n W Y (glueLabel Y (P.biUnion id) ω ν) X = 0 then 0 else
        ENNReal.ofReal ((∏ X ∈ P, Φ n W Y (glueLabel Y (P.biUnion id) ω ν) X) *
          Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
            φ n y W Y (glueLabel Y (P.biUnion id) ω ν))))
        ∂(Measure.pi fun _ : (P.biUnion id : Finset (TorusSite n)) => Λ.μ)) ≤
      ENNReal.ofReal (Real.exp (-(x * ℓ.κ * ℓ.threshold ^ 2 *
          ((open Classical in (torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).card : ℝ)) -
        ℓ.κ₁ * x * ℓ.threshold ^ 2 * (excessLength ℓ (clusterRange x) (P.biUnion id) W : ℝ)))
theorem hullExpansion_of_parts {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity}
    {Λ : LabelSpace}
    {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
    {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
    {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
    (hS : HullExpansionStates ℓ x D Λ Dq Φ) (hD : HullExpansionDisplay ℓ t x D f Λ Dq Φ φ)
    (hR : HullExpansionRegularity ℓ x Λ Dq Φ φ) (hP : HullExpansionPrice ℓ x Λ Φ φ) :
    HullExpansion ℓ t x D f Λ Dq Φ φ :=
  ⟨hS.nonneg, hR.borel, hS.sum, hS.gauge, hS.translation, hD.form, hS.factor_nonneg, hS.one_rule, hS.reads_class,
    hD.empty, hD.forget, hD.forget_cold, hR.smooth, hP.price⟩
end YangMills.Construction.TorusLumps
end
