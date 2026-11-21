import YangMills.Construction.TorusOrFourSpace.EquicontinuityInequalities
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndProductsOfClasses
import YangMills.Construction.TorusOrFourSpace.SequencesOfC1Forms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
section Parts
variable (D : Params) (E : Kind)
def InBallsAndSeparated {n : ℕ} (A : Fin n → Set (E.Pt D)) (d R : ℝ) : Prop :=
  (∀ l, ∃ S, IsClosedBallWithRadius D E S R ∧ A l ⊆ S) ∧
    DiagonalLimits.PairwiseSetDistGe D E A d
def MultilinearOnClasses {n : ℕ} (K : Set (FnTuple D E n)) (Ψ : K → ℝ)
    (W : Fin n → Set (E.Pt D → ℝ)) : Prop :=
  ∃ V : Fin n → Submodule ℝ (E.Pt D → ℝ), (∀ l, (V l : Set (E.Pt D → ℝ)) = W l) ∧
    ∃ hIn : ∀ h : (∀ l, V l), (fun l => (h l : E.Pt D → ℝ)) ∈ K,
      IsMultilinearProd fun h : (∀ l, V l) => Ψ ⟨fun l => (h l : E.Pt D → ℝ), hIn h⟩
def BoundedEquicontOnClasses {n : ℕ} (K : Set (FnTuple D E n)) (Ψ : K → ℝ)
    (W : Fin n → Set (E.Pt D → ℝ)) (c : ℝ) : Prop :=
  productSet D E W ⊆ K ∧
    (∀ h : K, h.1 ∈ productSet D E W →
      ENNReal.ofReal |Ψ h| ≤ ENNReal.ofReal c * ∏ l, sharpNormQ D E (h.1 l)) ∧
    ∀ f g : K, f.1 ∈ productSet D E W → g.1 ∈ productSet D E W →
      EquicontinuityBounds D E c (Ψ f) (Ψ g) f.1 g.1
end Parts
def UniformC1Bounds : Prop :=
  ∀ (D : Params) (E : Kind) (θ : RadiusRatio) (P : TorusPartitionChoice D θ)
    (C : BoundFamily),
    (∀ (J₀ : Sequences.PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞)
      (Ψ : BoundedC1FormSeq D E J₀ ρ C) (n : ℕ) (hn : 2 ≤ n) (d R : ℝ), 0 < d →
      ∀ (hR : 0 < R) (A : Fin n → Set (E.Pt D)),
        InBallsAndSeparated D E A d R →
        ∀ j : J₀.carrier, Ψ.thresholdAtRadius θ n hn R hR ≤ (((j.1 : ℕ+) : ℕ) : ℤ) →
          (∀ l, A l ⊆ centredBall D E (ρ j)) →
          MultilinearOnClasses D E (sepC1TuplesInBall D E n (ρ j))
            (Ψ.func j n hn) (fun l => c1SupportedIn D E (A l)) ∧
          BoundedEquicontOnClasses D E (sepC1TuplesInBall D E n (ρ j))
            (Ψ.func j n hn) (fun l => c1SupportedIn D E (A l))
            (effConstAt P E C n d R)) ∧
    ∀ Φ ∈ boundedHierarchies D E C, ∀ (n : ℕ) (hn : 2 ≤ n) (d R : ℝ), 0 < d → 0 < R →
      ∀ A : Fin n → Set (E.Pt D), InBallsAndSeparated D E A d R →
        BoundedEquicontOnClasses D E (sepC1Tuples D E n)
          (Φ.func n hn) (fun l => c1SupportedIn D E (A l))
          (effConstAt P E C n d R)
end YangMills.Construction.PeriodicSpace.Kind
