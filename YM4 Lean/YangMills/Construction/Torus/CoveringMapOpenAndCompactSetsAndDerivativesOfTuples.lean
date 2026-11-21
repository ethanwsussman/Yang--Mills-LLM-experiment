import YangMills.Construction.Torus.FunctionsOfSeveralPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.Conventions (StandingParameters)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
def IsOpenWrt {X : Type} (d : X → X → ℝ) (U : Set X) : Prop :=
  ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∀ x', d x x' < r → x' ∈ U
def IsBoundedWrt {X : Type} (d : X → X → ℝ) (U : Set X) : Prop :=
  ∃ C : ℝ, ∀ x ∈ U, ∀ x' ∈ U, d x x' ≤ C
def liftSupDist {p : ℕ} (x x' : Fin (4 * p) → ℝ) : ℝ :=
  supNorm ((flattenCoords p).symm (x - x'))
def liftEuclidDist {p : ℕ} (x x' : Fin (4 * p) → ℝ) : ℝ :=
  Real.sqrt (∑ j, (x j - x' j) ^ 2)
variable {s : StandingParameters} {E : Ambient}
def blockOf {q : ℕ} (P : Fin q → ℕ) (y : Tuple s E (∑ a, P a)) (a : Fin q) : Tuple s E (P a) :=
  fun i => y (finSigmaFinEquiv ⟨a, i⟩)
def blockProduct {q : ℕ} (P : Fin q → ℕ) (A : (a : Fin q) → Set (Tuple s E (P a))) :
    Set (Tuple s E (∑ a, P a)) :=
  {y | ∀ a, blockOf P y a ∈ A a}
def TupleCoveringProps (s : StandingParameters) (E : Ambient) (p : ℕ) : Prop :=
  Function.Surjective (tupleProj s E p) ∧
  (∀ x x', tupleProj s E p x = tupleProj s E p x' ↔ IsTuplePeriod s E p (x - x')) ∧
  (∀ x x', supDist (tupleProj s E p x) (tupleProj s E p x') ≤
    liftSupDist x x') ∧
  ∀ (x : Fin (4 * p) → ℝ) (y : Tuple s E p), ∃ x', IsLiftOfTuple s E y x' ∧
    liftSupDist x x' = supDist (tupleProj s E p x) y
def TupleOpenSetProps (s : StandingParameters) (E : Ambient) (p : ℕ) : Prop :=
  (∀ U : Set (Fin (4 * p) → ℝ),
    IsOpenWrt liftSupDist U ↔ IsOpenWrt liftEuclidDist U) ∧
  (∀ U : Set (Fin (4 * p) → ℝ),
    IsBoundedWrt liftSupDist U ↔ IsBoundedWrt liftEuclidDist U) ∧
  (∀ U : Set (Fin (4 * p) → ℝ), IsOpen U ↔ IsOpenWrt liftEuclidDist U) ∧
  (∀ U : Set (Fin (4 * p) → ℝ),
    Bornology.IsBounded U ↔ IsBoundedWrt liftEuclidDist U) ∧
  (∀ A : Set (Tuple s E p), IsOpen A ↔ IsOpen (tupleProj s E p ⁻¹' A)) ∧
  ∀ (X : Type) [MetricSpace X] (h : Tuple s E p → X),
    Continuous h ↔ Continuous (h ∘ tupleProj s E p)
def BlockProductProps (s : StandingParameters) (E : Ambient) : Prop :=
  ∀ (q : ℕ) (P : Fin q → ℕ), 1 ≤ q → (∀ a, 1 ≤ P a) →
    ∀ A : (a : Fin q) → Set (Tuple s E (P a)),
      ((∀ a, IsOpen (A a)) → IsOpen (blockProduct P A)) ∧
      ((∀ a, IsClosed (A a)) → IsClosed (blockProduct P A)) ∧
      ((∀ a, IsCompact (A a)) → IsCompact (blockProduct P A))
def TupleFactorProps (s : StandingParameters) (E : Ambient) (p : ℕ) : Prop :=
  (∀ A : Fin p → Set (Pt s E),
    ((∀ i, IsOpen (A i)) → IsOpen (Set.pi univ A)) ∧
    ((∀ i, IsClosed (A i)) → IsClosed (Set.pi univ A)) ∧
    ((∀ i, IsCompact (A i)) → IsCompact (Set.pi univ A))) ∧
  (∀ i : Fin p, Continuous (fun y : Tuple s E p => y i) ∧
    ∀ K : Set (Tuple s E p), IsCompact K → IsCompact ((fun y : Tuple s E p => y i) '' K)) ∧
  IsOpen {y : Tuple s E p | ∀ i i', i ≠ i' → y i ≠ y i'}
def TupleBallProps (s : StandingParameters) (E : Ambient) (p : ℕ) : Prop :=
  (∀ A : Set (Tuple s E p), IsClosed A → Bornology.IsBounded A → IsCompact A) ∧
  ∀ (y : Tuple s E p) (r : ℝ), 0 < r →
    {y' : Tuple s E p | supDist y' y ≤ r} = Set.pi univ (fun i => closedBall s E (y i) r) ∧
    IsCompact {y' : Tuple s E p | supDist y' y ≤ r} ∧
    {y' : Tuple s E p | supDist y' y < r} = Set.pi univ (fun i => openBall s E (y i) r) ∧
    IsOpen {y' : Tuple s E p | supDist y' y < r}
def TupleDerivProps (s : StandingParameters) (E : Ambient) (p : ℕ) : Prop :=
  ∀ (ν : ℕ∞) (F : Tuple s E p → ℂ), IsCn ν F →
    (∀ α : YangMills.Construction.PowerSeries.MultiIndex (4 * p), (α.order : ℕ∞) ≤ ν →
      (∃! H : Tuple s E p → ℂ,
        H ∘ tupleProj s E p = iteratedPartial α (F ∘ tupleProj s E p)) ∧
      Continuous (multiDeriv α F) ∧
      closedSupport (multiDeriv α F) ⊆ closedSupport F ∧
      (ν = ⊤ → IsSmoothFn (multiDeriv α F) ∧
        ∀ β : YangMills.Construction.PowerSeries.MultiIndex (4 * p),
          multiDeriv β (multiDeriv α F) = multiDeriv (α + β) F)) ∧
    ∀ n : ℕ, ν = n → IsCompact (closedSupport F) → cnNorm n F < ⊤
def TupleTopology.Holds : Prop :=
  ∀ (s : StandingParameters) (E : Ambient),
    (∀ p : ℕ, 1 ≤ p →
      TupleCoveringProps s E p ∧ TupleOpenSetProps s E p ∧ TupleFactorProps s E p ∧
        TupleBallProps s E p ∧ TupleDerivProps s E p) ∧
    BlockProductProps s E ∧
    ∀ K K' : Set (Pt s E), IsCompact K → IsCompact K' → Disjoint K K' →
      0 < setDist s E K K'
end YangMills.Construction.AmbientPoints
