import YangMills.Construction.TorusOrFourSpace.AdmissibleFamiliesOfOpenSets
import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.QuarterSideOpenBallsDistinctPointsAndBoundedFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
def AdmissibleProductFacts : Prop :=
  ∀ (D : Params) (E : Kind) (n : ℕ+),
    Tuple.IsOpenT D E (pairwiseDistinct D E n) ∧
    (∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
      Tuple.IsOpenT D E (Tuple.boxSet D E G) ∧
        Tuple.boxSet D E G ⊆ pairwiseDistinct D E n) ∧
    (∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ y : E.Tuple D n,
      (∀ i i', i ≠ i' → δ ≤ quotDist D E (y i) (y i')) →
        AdmissibleWith D E η (δ / 3) fun i => openBallAt D E (y i) η) ∧
    (∀ y ∈ pairwiseDistinct D E n, ∃ G : Fin (n : ℕ) → Set (E.Pt D),
      Admissible D E G ∧ y ∈ Tuple.boxSet D E G) ∧
    ∀ (R d : ℝ) (G G' : Fin (n : ℕ) → Set (E.Pt D)), AdmissibleWith D E R d G →
      Admissible D E G' →
        AdmissibleWith D E R d (memberInter D E G G') ∧
          Tuple.boxSet D E (memberInter D E G G') =
            Tuple.boxSet D E G ∩ Tuple.boxSet D E G'
end YangMills.Construction.PeriodicSpace.Kind
