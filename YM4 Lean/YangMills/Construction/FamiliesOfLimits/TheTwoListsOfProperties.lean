import YangMills.Construction.FamiliesOfLimits.FamiliesOfLimitsAlongGrowingTori
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfMaps
import YangMills.Construction.Torus.DistributionsOffTheDiagonalsAndRegularMaps
import YangMills.Construction.Torus.MirrorsAtRealPositionsAndReflectionPositivityOfAMapOnTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open AmbientPoints
open ReflectionPositivity.AxisMirror (Ambient)
open TorusSymmetries
namespace FamiliesOfLimits
variable {s : Conventions.StandingParameters} {E : Ambient}
def AgreesOnTensorProducts {n : ℕ} (u : testFns (pairwiseDistinctTuples s E n) → ℂ)
    (φ : separatedTuples s E n → ℝ) : Prop :=
  ∀ (f : Fin n → Pt s E → ℝ) (hf : f ∈ separatedTuples s E n),
    (∀ i, IsSmoothReal (f i)) →
      ∃ hF : realTensor f ∈ testFns (pairwiseDistinctTuples s E n),
        u ⟨_, hF⟩ = ((φ ⟨f, hf⟩ : ℝ) : ℂ)
def HasUniqueDistribOfOrder {n : ℕ} (P : Set (Pt s E) → Prop)
    (φ : separatedTuples s E n → ℝ) : Prop :=
  ∃ u : testFns (pairwiseDistinctTuples s E n) → ℂ, IsDistrib u ∧ AgreesOnTensorProducts u φ ∧
    (∀ v : testFns (pairwiseDistinctTuples s E n) → ℂ,
      IsDistrib v → AgreesOnTensorProducts v φ → v = u) ∧
    ∀ O : Fin n → Set (Pt s E), (∀ i, IsOpen (O i)) → (∀ i, P (O i)) →
      (Pairwise fun i j => PositivelySeparated s E (O i) (O j)) →
      ∀ h : Set.univ.pi O ⊆ pairwiseDistinctTuples s E n, HasOrderLEOn (5 * n + 1) h u
def IsTranslationHypercubicInvariant (S : TupleMapFamily s E) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n),
    (∀ v : Pt s E, IsInvariantOnLength (translateOn s E v) (S n hn)) ∧
      IsInvariantOnLengthGroup (groupOn s E) (S n hn)
def TorusReflectionPositive (S : TupleMapFamily s .torus) : Prop :=
  ∀ M : AmbientMirror .torus, AmbientMirror.IsReflectionPositive s .torus M (centredOfMaps S)
def R4ReflectionPositive (S : TupleMapFamily s .euclidean) : Prop :=
  ∀ M : AmbientMirror .euclidean, AmbientMirror.IsAxial .euclidean M →
    AmbientMirror.IsReflectionPositive s .euclidean M (centredOfMaps S)
def complexOfMaps (S : TupleMapFamily s .euclidean) : SeparatedTupleFunctions s :=
  fun n hn X => ((S n hn X : ℝ) : ℂ)
end FamiliesOfLimits
end YangMills.Construction
end
