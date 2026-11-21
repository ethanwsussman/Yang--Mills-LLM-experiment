import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import YangMills.Construction.Continuum.TensorProductsAndIntegrationOverArguments
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.Elementary
variable {n : ℕ}
def linComb (a : ℂ) (φ : PointTuple n → ℂ) (b : ℂ) (ψ : PointTuple n → ℂ) : PointTuple n → ℂ :=
  fun x => a * φ x + b * ψ x
def conjPointwise (φ : PointTuple n → ℂ) : PointTuple n → ℂ := fun x => starRingEnd ℂ (φ x)
def rePart (φ : PointTuple n → ℂ) : PointTuple n → ℂ := fun x => ((φ x).re : ℂ)
def imPart (φ : PointTuple n → ℂ) : PointTuple n → ℂ := fun x => ((φ x).im : ℂ)
def setPower (O : Set (Fin 4 → ℝ)) : Set (PointTuple n) := Set.pi Set.univ fun _ => O
def subtuple (J : Finset (Fin n)) (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    Fin J.card → (Fin 4 → ℝ) → ℝ :=
  fun t => f (J.orderEmbOfFin rfl t)
def tensorProdComplex (f : Fin n → (Fin 4 → ℝ) → ℝ) : PointTuple n → ℂ :=
  fun x => ((tensorProd f x : ℝ) : ℂ)
def SchwartzClosedUnderOps (n : ℕ) : Prop :=
  (∀ φ ∈ schwartzSet n, ∀ ψ ∈ schwartzSet n, ∀ a b : ℂ,
    (linComb a φ b ψ ∈ schwartzSet n ∧ conjPointwise φ ∈ schwartzSet n ∧
      rePart φ ∈ schwartzSet n ∧ imPart φ ∈ schwartzSet n) ∧
    (∀ k m : ℕ, 0 < k → k ≤ m →
      weightedSeminorm k φ ≤ weightedSeminorm m φ ∧
      weightedSeminorm k (linComb a φ b ψ) ≤
        ENNReal.ofReal ‖a‖ * weightedSeminorm k φ + ENNReal.ofReal ‖b‖ * weightedSeminorm k ψ ∧
      weightedSeminorm k (conjPointwise φ) = weightedSeminorm k φ ∧
      weightedSeminorm k (rePart φ) ≤ weightedSeminorm k φ ∧
      weightedSeminorm k (imPart φ) ≤ weightedSeminorm k φ) ∧
    (∀ U : Set (PointTuple n), IsOpen U → VanishesToInfiniteOrderOff φ U →
      VanishesToInfiniteOrderOff ψ U →
      VanishesToInfiniteOrderOff (linComb a φ b ψ) U ∧ VanishesToInfiniteOrderOff (conjPointwise φ) U ∧
      VanishesToInfiniteOrderOff (rePart φ) U ∧ VanishesToInfiniteOrderOff (imPart φ) U)) ∧
  ∀ U : Set (PointTuple n), IsOpen U → ∃ S : Submodule ℂ (PointTuple n → ℂ),
    (S : Set (PointTuple n → ℂ)) = {φ | φ ∈ schwartzSet n ∧ VanishesToInfiniteOrderOff φ U}
def OpenLociFacts (n : ℕ) : Prop :=
  IsOpen (distinctLocus n) ∧ IsOpen (positiveTimeLocus n) ∧ IsOpen (negativeTimeLocus n) ∧
  negativeTimeLocus n = timeReflectSet (positiveTimeLocus n) ∧
  distinctLocus n = setPower Set.univ ∩ TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∧
  positiveTimeLocus n = setPower upperHalfSpace ∩ TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∧
  flatSchwartzSet n =
    {φ | φ ∈ schwartzSet n ∧ VanishesToInfiniteOrderOff φ (distinctLocus n)} ∧
  ∀ φ ∈ schwartzSet n,
    VanishesToInfiniteOrderOff φ (positiveTimeLocus n) ∨
      VanishesToInfiniteOrderOff φ (negativeTimeLocus n) →
      φ ∈ flatSchwartzSet n
def CompactSupportFacts (n : ℕ) : Prop :=
  ∀ U : Set (PointTuple n), IsOpen U → ∀ φ ∈ (smoothCompactSupp U : Set (PointTuple n → ℂ)),
    φ ∈ schwartzSet n ∧ VanishesToInfiniteOrderOff φ U ∧ (∀ p : ℕ, derivSupNorm p φ < ⊤) ∧
    ∀ R : ℝ, 0 ≤ R → (∀ x, x ∉ {x : PointTuple n | tupleNorm x ≤ R} → φ x = 0) →
      ∀ k : ℕ, 0 < k →
        weightedSeminorm k φ ≤ ENNReal.ofReal ((1 + R ^ 2) ^ ((k : ℝ) / 2)) * derivSupNorm k φ
def SubtupleTensorFacts (n : ℕ) : Prop :=
  ∀ O : Set (Fin 4 → ℝ), IsOpen O → ∀ f ∈ disjointSupportTuples O n,
    (∀ J : Finset (Fin n), subtuple J f ∈ disjointSupportTuples O J.card ∧
      (HasSmoothComponents O f → HasSmoothComponents O (subtuple J f))) ∧
    (HasSmoothComponents O f →
      tensorProd f ∈ (smoothCompactSupp
        (setPower O ∩ TestFunctions.injectiveTuples (Fin 4 → ℝ) n) : Set (PointTuple n → ℝ)) ∧
      tensorProdComplex f ∈ flatSchwartzSet n ∧
      (O = upperHalfSpace → VanishesToInfiniteOrderOff (tensorProdComplex f) (positiveTimeLocus n)))
def WeightIntegralBounds : Prop :=
  ∀ k : ℕ, 4 < k →
    0 < weightIntegral k ∧ weightIntegral k < ⊤ ∧ weightIntegral k ≤ weightIntegral 5
def BasicProperties : Prop :=
  ∀ n : ℕ, 0 < n →
    SchwartzClosedUnderOps n ∧ OpenLociFacts n ∧ CompactSupportFacts n ∧
      SubtupleTensorFacts n ∧ WeightIntegralBounds
end YangMills.Construction.TestSpaces.Elementary
end
