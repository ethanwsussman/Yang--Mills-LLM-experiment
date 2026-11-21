import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open ReflectionPositivity.AxisMirror (MirrorData Ambient)
open ReflectionPositivity.AxisMirror.Ambient (compactC1 separatedN compactC1SuppIn evalOrZero
  IsSeparatedMultilinear ConnectedFamily)
open TestFunctions (setDistR4 HasSeparatedSupportsR4)
namespace SchwingerFunctions.RealConnected
variable {n : ℕ}
def PosDistOfCompactDisjoint : Prop :=
  (∀ K K' : Set (Fin 4 → ℝ), IsCompact K → IsCompact K' → Disjoint K K' →
      0 < setDistR4 K K') ∧
    ∀ A B : Set (Fin 4 → ℝ), 0 < setDistR4 A B → Disjoint A B
def SeparatedSupportsIffMem : Prop :=
  ∀ (D : MirrorData) (n : ℕ), 1 ≤ n → ∀ φ : Fin n → (Fin 4 → ℝ) → ℝ,
    ((∀ i, φ i ∈ compactC1 D ℝ Ambient.euclidean) ∧
        ∃ d : ℝ, HasSeparatedSupportsR4 φ d) ↔
      List.ofFn φ ∈ separatedN D Ambient.euclidean n
def IsCompactPairwisePosDist (K : Fin n → Set (Fin 4 → ℝ)) : Prop :=
  (∀ i, IsCompact (K i)) ∧ Pairwise fun i j => 0 < setDistR4 (K i) (K j)
def CompactProductsMem : Prop :=
  ∀ (D : MirrorData) (n : ℕ), 1 ≤ n → ∀ K : Fin n → Set (Fin 4 → ℝ), IsCompactPairwisePosDist K →
    ∀ φ : Fin n → (Fin 4 → ℝ) → ℝ, (∀ i, φ i ∈ compactC1SuppIn D Ambient.euclidean (K i)) →
      List.ofFn φ ∈ separatedN D Ambient.euclidean n
def IsLinearOnCompactProducts (D : MirrorData)
    (T : separatedN D Ambient.euclidean n → ℝ) : Prop :=
  ∀ K : Fin n → Set (Fin 4 → ℝ), IsCompactPairwisePosDist K →
    ∀ φ : Fin n → (Fin 4 → ℝ) → ℝ, (∀ i, φ i ∈ compactC1SuppIn D Ambient.euclidean (K i)) →
      ∀ (i : Fin n) (ψ : (Fin 4 → ℝ) → ℝ), ψ ∈ compactC1SuppIn D Ambient.euclidean (K i) → ∀ s t : ℝ,
        evalOrZero T (List.ofFn (Function.update φ i (s • φ i + t • ψ))) =
          s * evalOrZero T (List.ofFn φ) + t * evalOrZero T (List.ofFn (Function.update φ i ψ))
def MultilinearIffLinearOnCompactProducts : Prop :=
  ∀ (D : MirrorData) (n : ℕ), 1 ≤ n → ∀ T : separatedN D Ambient.euclidean n → ℝ,
    IsSeparatedMultilinear D Ambient.euclidean T ↔ IsLinearOnCompactProducts D T
def IsAdmissibleTuple (φ : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  (∀ i, IsC1c (φ i)) ∧ ∃ d : ℝ, HasSeparatedSupportsR4 φ d
def IsRealValued (S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ) : Prop :=
  ∀ n, 2 ≤ n → ∀ φ : Fin n → (Fin 4 → ℝ) → ℝ, IsAdmissibleTuple φ → (S n φ).im = 0
def MatchesConnected {D : MirrorData} (S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ)
    (F : ConnectedFamily D Ambient.euclidean) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (φ : Fin n → (Fin 4 → ℝ) → ℝ), IsAdmissibleTuple φ →
    S n φ = (evalOrZero (F.fn n hn) (List.ofFn φ) : ℝ)
def ConnectedFamiliesCorrespond : Prop :=
  ∀ D : MirrorData,
    (∀ F : ConnectedFamily D Ambient.euclidean,
      (∃ S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ, MatchesConnected S F) ∧
        ∀ S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ, MatchesConnected S F →
          IsContinuumSchwingerFamily S ∧ IsRealValued S) ∧
      ∀ S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ, IsContinuumSchwingerFamily S → IsRealValued S →
        ∃! F : ConnectedFamily D Ambient.euclidean, MatchesConnected S F
def ConnectedRealFamilies : Prop :=
  PosDistOfCompactDisjoint ∧ SeparatedSupportsIffMem ∧
    CompactProductsMem ∧ MultilinearIffLinearOnCompactProducts ∧
    ConnectedFamiliesCorrespond
end SchwingerFunctions.RealConnected
end YangMills.Construction
end
