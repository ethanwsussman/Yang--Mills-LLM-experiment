import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusFields
variable {n : ℕ}
def StepParameters.weightRate (p : StepParameters) : ℝ := p.rt / 2 ^ 10
def StepParameters.decayRate (p : StepParameters) : ℝ := p.rt / 2 ^ 12
def StepParameters.weight (p : StepParameters) (m : ℕ) : ℝ :=
  max 1 (((m : ℝ) / p.n₁) ^ 16000) * Real.exp (p.weightRate * m)
def clusterRange (x : ℝ) : ℕ := ⌈x ^ ((1 : ℝ) / 100)⌉₊
abbrev LocalDensity : Type := (n : ℕ) → TorusSite n → TorusField n → ℝ
def centered (f : LocalDensity) (n : ℕ) (y : TorusSite n) (U : TorusField n) : ℝ :=
  f n y U - f n y (trivialField n)
def bondFrom (y : TorusSite n) (b : (Fin 4 → ℤ) × Fin 4) : TorusBond n := (y + siteOfInt b.1, b.2)
def FieldsAgreeNear {n' : ℕ} (U : TorusField n) (U' : TorusField n') (y : TorusSite n) (y' : TorusSite n')
    (m : ℕ) : Prop :=
  ∀ b : (Fin 4 → ℤ) × Fin 4, BondOffsetInBox m b →
    U (bondFrom y b).1 (bondFrom y b).2 = U' (bondFrom y' b).1 (bondFrom y' b).2
def secondDerivLimit (f : LocalDensity) (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions) : ℝ :=
  Filter.limUnder Filter.atTop fun n : ℕ =>
    mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X']
def linearPotential (A : Fin 4 → Fin 4 → imaginaryQuaternions) (b : (Fin 4 → ℤ) × Fin 4) :
    imaginaryQuaternions :=
  (1 / 2 : ℝ) • ∑ ν, ((b.1 ν : ℤ) : ℝ) • A ν b.2
structure ColdExpansion (p : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) (f : LocalDensity) :
    Prop where
  positive : ∀ n [NeZero n], p.n₀ ≤ n → ∀ U : TorusField n, IsCold p.threshold U → 0 < D n U
  smooth : ∀ n [NeZero n], p.n₀ ≤ n → ∀ (y : TorusSite n) (U : TorusField n), IsCold p.threshold U →
    ContDiffThreeAt (f n y) U
  gauge : ∀ n [NeZero n], p.n₀ ≤ n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion) (U : TorusField n),
    IsCold p.threshold U → f n y (gaugeTransform g U) = f n y U
  translation : ∀ n [NeZero n], p.n₀ ≤ n → ∀ (y u : TorusSite n) (U : TorusField n),
    IsCold p.threshold U → f n y (TorusFields.translate u U) = f n (y + u) U
  form : ∀ n [NeZero n], p.n₀ ≤ n → ∀ U : TorusField n, IsCold p.threshold U →
    Real.log (D n U) - Real.log (D n (trivialField n)) =
      -x * actionAtLevel p.coupling p.side t Finset.univ U + ∑ y, centered f n y U
  decay : ∀ n [NeZero n], p.n₀ ≤ n → ∀ (y : TorusSite n) (U : TorusField n), IsCold p.threshold U →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (f n y) U c X| ≤ (if k = 3 then p.E₃ else p.E) / p.weight (supportDiam y c)
  local_density : ∀ n n' [NeZero n] [NeZero n'], p.n₀ ≤ n → p.n₀ ≤ n' →
    ∀ (y : TorusSite n) (y' : TorusSite n') (U : TorusField n) (U' : TorusField n') (m : ℕ),
      2 * m + 2 < n → 2 * m + 2 < n' →
      IsCold p.threshold U → IsCold p.threshold U' → FieldsAgreeNear U U' y y' m →
      ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
        (∀ l, BondOffsetInBox m (h l)) → AreUnitVectors X →
        |mixedDeriv (centered f n y) U (fun l => bondFrom y (h l)) X -
            mixedDeriv (centered f n' y') U' (fun l => bondFrom y' (h l)) X| ≤ p.E / p.weight m
  no_curvature_term : ∀ A A' : Fin 4 → Fin 4 → imaginaryQuaternions, (∀ μ ν, A μ ν = - A ν μ) →
    (∀ μ ν, A' μ ν = - A' ν μ) →
    HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
      secondDerivLimit f cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2)) 0
structure LabelSpace where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  [sbΩ : StandardBorelSpace Ω]
  μ : Measure Ω
  [sfμ : SigmaFinite μ]
  act : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)), (TorusSite n → UnitQuaternion) → (Y → Ω) → (Y → Ω)
  act_borel : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)),
    Measurable fun q : (TorusSite n → UnitQuaternion) × (Y → Ω) => act Y q.1 q.2
  act_one : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)) (ω : Y → Ω), act Y (fun _ => 1) ω = ω
  act_mul : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)) (g g' : TorusSite n → UnitQuaternion) (ω : Y → Ω),
    act Y (g * g') ω = act Y g (act Y g' ω)
  act_keeps : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)) (g : TorusSite n → UnitQuaternion),
    MeasurePreserving (act Y g) (Measure.pi fun _ : Y => μ) (Measure.pi fun _ : Y => μ)
  act_local : ∀ {n : ℕ} [NeZero n] (Y Y' : Finset (TorusSite n)) (g g' : TorusSite n → UnitQuaternion)
    (ω : Y → Ω) (ω' : Y' → Ω) (y : TorusSite n) (hy : y ∈ Y) (hy' : y ∈ Y'),
    (∀ z, supDist z y ≤ 1 → g z = g' z) → (∀ z, supDist z y ≤ 1 → (z ∈ Y ↔ z ∈ Y')) →
    (∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), supDist z y ≤ 1 → ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) →
    act Y g ω ⟨y, hy⟩ = act Y' g' ω' ⟨y, hy'⟩
  act_free : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)) (g : TorusSite n → UnitQuaternion) (ω : Y → Ω)
    (y : Y), (∀ z, supDist z (y : TorusSite n) ≤ 1 → g z = 1) → act Y g ω y = ω y
attribute [instance] LabelSpace.mΩ LabelSpace.sbΩ LabelSpace.sfμ
def thickening (m : ℕ) (X : Finset (TorusSite n)) [NeZero n] : Finset (TorusSite n) :=
  open Classical in Finset.univ.filter fun z => ∃ w ∈ X, supDist z w ≤ m
def ChainConnected (r : ℕ) (Y : Finset (TorusSite n)) : TorusSite n → TorusSite n → Prop :=
  Relation.ReflTransGen fun u v => u ∈ Y ∧ v ∈ Y ∧ supDist u v ≤ r
open Classical in
def chainComponents [NeZero n] (r : ℕ) (Y : Finset (TorusSite n)) : Finset (Finset (TorusSite n)) :=
  Y.image fun y => Y.filter (ChainConnected r Y y)
def IsHullState [NeZero n] (p : StepParameters) (r : ℕ) (U : TorusField n) (Y : Finset (TorusSite n)) : Prop :=
  thickening (2 * r) (torusHotSites p U) ⊆ Y ∧
    ∀ X ∈ chainComponents r Y, ∃ l ∈ torusHotLumps p U, (l ∩ X).Nonempty
def ballCoverNumber [NeZero n] (m : ℕ) (X : Finset (TorusSite n)) : ℕ :=
  sInf {k | ∃ C : Finset (TorusSite n), C.card = k ∧ X ⊆ thickening m C}
open Classical in
def excessLength [NeZero n] (p : StepParameters) (r : ℕ) (X : Finset (TorusSite n)) (U : TorusField n) : ℕ :=
  ballCoverNumber (4 * r)
    (X \ thickening (4 * r) (((torusHotLumps p U).filter (· ⊆ X)).image lumpCenter))
def IsBlockTorusSide (p : StepParameters) (n : ℕ) : Prop := p.side ∣ n ∧ p.side * p.n₀ ≤ n
def translateSet [NeZero n] (u : TorusSite n) (Y : Finset (TorusSite n)) : Finset (TorusSite n) :=
  open Classical in Finset.univ.filter fun z => z + u ∈ Y
def translateLabel [NeZero n] {Ω : Type} (u : TorusSite n) (Y : Finset (TorusSite n)) (ω : Y → Ω) :
    translateSet u Y → Ω :=
  fun z => ω ⟨z.1 + u, (by classical exact (Finset.mem_filter.mp z.2).2)⟩
def IsBlockTranslation (p : StepParameters) (u : TorusSite n) : Prop :=
  ∃ v : Fin 4 → ℤ, u = siteOfInt fun i => (p.side : ℤ) * v i
def SameBlockPosition (p : StepParameters) {n' : ℕ} (y : TorusSite n) (y' : TorusSite n') : Prop :=
  ∀ i, (((y i).cast : ℤ) - ((y' i).cast : ℤ)) % (p.side : ℤ) = 0
def CongruentInBoxes {n' : ℕ} (X : Finset (TorusSite n)) (X' : Finset (TorusSite n')) (y : TorusSite n)
    (y' : TorusSite n') (m : ℕ) : Prop :=
  (∀ z ∈ X, ∃ h, OffsetInBox m h ∧ z = y + siteOfInt h) ∧
    (∀ z ∈ X', ∃ h, OffsetInBox m h ∧ z = y' + siteOfInt h) ∧
    ∀ h, OffsetInBox m h → (y + siteOfInt h ∈ X ↔ y' + siteOfInt h ∈ X')
def LabelsAgreeNear {Ω : Type} {n' : ℕ} (Y : Finset (TorusSite n)) (Y' : Finset (TorusSite n')) (ω : Y → Ω)
    (ω' : Y' → Ω) (y : TorusSite n) (y' : TorusSite n') (m : ℕ) (X : Finset (TorusSite n)) : Prop :=
  ∀ h, OffsetInBox m h → ∀ (hz : y + siteOfInt h ∈ Y) (hz' : y' + siteOfInt h ∈ Y'), y + siteOfInt h ∈ X →
    ω ⟨_, hz⟩ = ω' ⟨_, hz'⟩
def FieldsAgreeOnSet {n' : ℕ} (U : TorusField n) (U' : TorusField n') (y : TorusSite n) (y' : TorusSite n')
    (m : ℕ) (X : Finset (TorusSite n)) : Prop :=
  ∀ b : (Fin 4 → ℤ) × Fin 4, BondOffsetInBox m b → (bondFrom y b).1 ∈ X →
    (bondFrom y b).1 + TorusFields.unitStep n b.2 ∈ X →
    U (bondFrom y b).1 (bondFrom y b).2 = U' (bondFrom y' b).1 (bondFrom y' b).2
def StatesAgreeNear (p : StepParameters) {Ω : Type} [NeZero n] {n' : ℕ} (U : TorusField n) (U' : TorusField n')
    (Y : Finset (TorusSite n)) (Y' : Finset (TorusSite n')) (ω : Y → Ω) (ω' : Y' → Ω) (y : TorusSite n)
    (y' : TorusSite n') (m : ℕ) : Prop :=
  2 * m + 2 < n ∧ 2 * m + 2 < n' ∧ FieldsAgreeNear U U' y y' m ∧
    (∀ h, OffsetInBox m h → (y + siteOfInt h ∈ Y ↔ y' + siteOfInt h ∈ Y')) ∧
    LabelsAgreeNear Y Y' ω ω' y y' m Finset.univ ∧
    ((∃ h, OffsetInBox m h ∧ y + siteOfInt h ∈ Y) → SameBlockPosition p y y')
open Classical in
def glueLabel {Ω : Type} [NeZero n] (Y P : Finset (TorusSite n)) (ω : Y → Ω) (ν : P → Ω) : Y → Ω :=
  fun z => if h : (z : TorusSite n) ∈ P then ν ⟨z, h⟩ else ω z
structure HullExpansion (p : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) (f : LocalDensity)
    (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ) : Prop where
  nonneg : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ (U : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω),
    IsHullState p (clusterRange x) U Y → 0 ≤ Dq n U Y ω
  borel : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ Y : Finset (TorusSite n),
    (open Classical in
      Measurable fun q : TorusField n × (Y → Λ.Ω) =>
        if IsHullState p (clusterRange x) q.1 Y then Dq n q.1 Y q.2 else 0) ∧
    (∀ X : Finset (TorusSite n), Measurable fun q : TorusField n × (Y → Λ.Ω) => Φ n q.1 Y q.2 X) ∧
    (∀ y : TorusSite n, open Classical in
      Measurable fun q : TorusField n × (Y → Λ.Ω) =>
        if IsHullState p (clusterRange x) q.1 Y ∧ ∀ X ∈ chainComponents (clusterRange x) Y, Φ n q.1 Y q.2 X ≠ 0
        then φ n y q.1 Y q.2 else 0)
  sum : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ U : TorusField n,
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState p (clusterRange x) U),
      ∫⁻ ω, ENNReal.ofReal (Dq n U Y ω) ∂(Measure.pi fun _ : Y => Λ.μ)) = ENNReal.ofReal (D n U)
  gauge : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ (U : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω)
    (g : TorusSite n → UnitQuaternion), IsHullState p (clusterRange x) U Y →
    Dq n (gaugeTransform g U) Y (Λ.act Y g ω) = Dq n U Y ω
  translation : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ (U : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → Λ.Ω) (u : TorusSite n), IsBlockTranslation p u → IsHullState p (clusterRange x) U Y →
    Dq n (TorusFields.translate u U) (translateSet u Y) (translateLabel u Y ω) = Dq n U Y ω
  form : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ (U : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω),
    IsHullState p (clusterRange x) U Y →
    Dq n U Y ω = D n (trivialField n) *
      Real.exp (-x * actionAtLevel p.coupling p.side t
          (Finset.univ \ thickening lumpRange (torusHotSites p U)) U +
        ∑ y, φ n y U Y ω) * ∏ X ∈ chainComponents (clusterRange x) Y, Φ n U Y ω X
  factor_nonneg : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ (U : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → Λ.Ω) (X : Finset (TorusSite n)), 0 ≤ Φ n U Y ω X
  one_rule : ∀ n n' [NeZero n] [NeZero n'], IsBlockTorusSide p n → IsBlockTorusSide p n' →
    ∀ (U : TorusField n) (U' : TorusField n') (Y : Finset (TorusSite n)) (Y' : Finset (TorusSite n'))
      (ω : Y → Λ.Ω) (ω' : Y' → Λ.Ω) (X : Finset (TorusSite n)) (X' : Finset (TorusSite n')) (y : TorusSite n)
      (y' : TorusSite n') (m : ℕ),
      2 * m + 2 < n → 2 * m + 2 < n' → X ⊆ Y → X' ⊆ Y' → SameBlockPosition p y y' →
      CongruentInBoxes X X' y y' m → FieldsAgreeOnSet U U' y y' m X → LabelsAgreeNear Y Y' ω ω' y y' m X →
      Φ n U Y ω X = Φ n' U' Y' ω' X'
  reads_class : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ (U U' : TorusField n) (Y Y' : Finset (TorusSite n))
      (ω : Y → Λ.Ω) (ω' : Y' → Λ.Ω) (X : Finset (TorusSite n)), X ⊆ Y → X ⊆ Y' →
      (∀ b : TorusBond n, b.1 ∈ X → b.1 + TorusFields.unitStep n b.2 ∈ X → U b.1 b.2 = U' b.1 b.2) →
      (∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), z ∈ X → ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) →
      Φ n U Y ω X = Φ n U' Y' ω' X
  empty : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ (U : TorusField n) (ω : (∅ : Finset (TorusSite n)) → Λ.Ω)
    (y : TorusSite n), IsHullState p (clusterRange x) U ∅ → φ n y U ∅ ω = centered f n y U
  forget : ∀ n n' [NeZero n] [NeZero n'], IsBlockTorusSide p n → IsBlockTorusSide p n' →
    ∀ (U : TorusField n) (U' : TorusField n') (Y : Finset (TorusSite n)) (Y' : Finset (TorusSite n'))
      (ω : Y → Λ.Ω) (ω' : Y' → Λ.Ω) (y : TorusSite n) (y' : TorusSite n') (m : ℕ),
      IsHullState p (clusterRange x) U Y → IsHullState p (clusterRange x) U' Y' →
      (∀ X ∈ chainComponents (clusterRange x) Y, Φ n U Y ω X ≠ 0) →
      (∀ X ∈ chainComponents (clusterRange x) Y', Φ n' U' Y' ω' X ≠ 0) →
      (clusterRange x : ℝ) / 64 ≤ m → StatesAgreeNear p U U' Y Y' ω ω' y y' m →
      |φ n y U Y ω - φ n' y' U' Y' ω'| ≤ Real.exp (-p.decayRate * m)
  forget_cold : ∀ n n' [NeZero n] [NeZero n'], IsBlockTorusSide p n → p.n₀ ≤ n' →
    ∀ (U : TorusField n) (U' : TorusField n') (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω)
      (ω' : (∅ : Finset (TorusSite n')) → Λ.Ω) (y : TorusSite n) (y' : TorusSite n') (m : ℕ),
      IsHullState p (clusterRange x) U Y → IsCold p.threshold U' →
      (∀ X ∈ chainComponents (clusterRange x) Y, Φ n U Y ω X ≠ 0) →
      (clusterRange x : ℝ) / 64 ≤ m → StatesAgreeNear p U U' Y ∅ ω ω' y y' m →
      |φ n y U Y ω - centered f n' y' U'| ≤ Real.exp (-p.decayRate * m)
  smooth : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ (U : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω),
    IsHullState p (clusterRange x) U Y → 0 < Dq n U Y ω →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      (∀ l, ∀ z ∈ Y, clusterRange x ≤ supDist (c l).1 z) →
      ContDiffAt ℝ 3 (fun s : Fin k → ℝ => Dq n (perturb c X s U) Y ω) 0 ∧
      (1 ≤ k → k ≤ 3 → AreUnitVectors X →
        |mixedDeriv (fun U' => Real.log (Dq n U' Y ω)) U c X| ≤ (p.derivBound * x) ^ k)
  price : ∀ n [NeZero n], IsBlockTorusSide p n → ∀ (U : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω)
    (P : Finset (Finset (TorusSite n))), IsHullState p (clusterRange x) U Y →
    P ⊆ chainComponents (clusterRange x) Y →
    (∀ X ∈ chainComponents (clusterRange x) Y \ P, Φ n U Y ω X ≠ 0) →
    (open Classical in
      ∫⁻ ν, (if ∃ X ∈ P, Φ n U Y (glueLabel Y (P.biUnion id) ω ν) X = 0 then 0 else
        ENNReal.ofReal ((∏ X ∈ P, Φ n U Y (glueLabel Y (P.biUnion id) ω ν) X) *
          Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
            φ n y U Y (glueLabel Y (P.biUnion id) ω ν))))
        ∂(Measure.pi fun _ : (P.biUnion id : Finset (TorusSite n)) => Λ.μ)) ≤
      ENNReal.ofReal (Real.exp (-(x * p.κ * p.threshold ^ 2 *
          ((open Classical in (torusHotLumps p U).filter (· ⊆ P.biUnion id)).card : ℝ)) -
        p.κ₁ * x * p.threshold ^ 2 * (excessLength p (clusterRange x) (P.biUnion id) U : ℝ)))
structure StepParameters.Admissible (p : StepParameters) : Prop where
  a_ge : 1 ≤ p.coupling
  L_odd : Odd p.side
  L_ge : 2 ^ 16 ≤ p.side
  σ_pos : 0 < p.threshold
  κ_pos : 0 < p.κ
  κ_le : p.κ ≤ 1 / 8
  κ₁_pos : 0 < p.κ₁
  rt_pos : 0 < p.rt
  n₁_pos : 0 < p.n₁
  E_pos : 0 < p.E
  E_ge : 1 ≤ p.E
  depth_lt : 11 * 2 ^ 12 * p.baseDepth < p.side
  E₃_pos : 0 < p.E₃
  B_pos : 0 < p.B
  Cder_ge : 1 ≤ p.derivBound
  n₀_ge : 4096 ≤ p.n₀
  y₁_ge : 1 ≤ p.y₁
  range_ge : 2 ^ 16 ≤ clusterRange p.y₁
def HasExpansion (p : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) : Prop :=
  (∀ n [NeZero n], p.n₀ ≤ n → Measurable (D n) ∧ (∀ U, 0 ≤ D n U) ∧
    (∀ (g : TorusSite n → UnitQuaternion) (U : TorusField n), D n (gaugeTransform g U) = D n U) ∧
    ∀ (g : TorusIsometry) (U U' : TorusField n), g.Transports U U' → D n U' = D n U) ∧
  ∃ f : LocalDensity, ColdExpansion p t x D f ∧
    ∃ (Λ : LabelSpace) (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
      (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
      (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ),
      HullExpansion p t x D f Λ Dq Φ φ
end YangMills.Construction.TorusLumps
end
