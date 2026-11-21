import YangMills.Construction.Lattice.TriplesAndTheOperatorsOfASequenceInAnAmbientRegion
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences
open YangMills.Construction.SeparatedRegions YangMills.Construction.Matrices
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
structure WeightedSeminorms (L m : ℕ) (S : ScaleData) where
  onSites : ℝ → (SiteAtLevel L m S.levels 0 → ComplexMatrix2) → ℝ≥0∞
  onBonds : ℝ → (FineBond L m S → ComplexMatrix2) → ℝ≥0∞
  onTops : ℝ → (FourTorus L m → ComplexMatrix2) → ℝ≥0∞
  onExpansions : ℝ → (LeveledBond L m S → ComplexMatrix2) → ℝ≥0∞
def localSeminorms (y : FourTorus L m) : WeightedSeminorms L m S where
  onSites s f := scaledLocalMax S Ω (siteIndexSet S (Ω 0)) (siteLocation S Ω) s f y
  onBonds s f := scaledLocalMax S Ω (bondIndexSet S (Ω 0)) (bondLocation S Ω) s f y
  onTops s f := scaledLocalMax S Ω (layerPoints S Ω) id s f y
  onExpansions s f := scaledLocalMax S Ω (leveledIndexSet S Ω) (leveledLocation S Ω) s f y
def gradientSeminorm (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (A : FineBond L m S → ComplexMatrix2) : ℝ≥0∞ :=
  scaledLocalMax S Ω (bondAxisIndexSet S (Ω 0)) (bondAxisLocation S Ω) (-2)
    (formCovariantGradient S (Ω 0) W A) y
abbrev SourceTuple (L m : ℕ) (S : ScaleData) : Type :=
  FullTuple L m S × (FineBond L m S → ComplexMatrix2)
abbrev ReducedSourceTuple (L m : ℕ) (S : ScaleData) : Type :=
  ReducedTuple L m S × (FineBond L m S → ComplexMatrix2)
def sourceTupleSpace : Set (SourceTuple L m S) :=
  fullTupleSpace S Ω ×ˢ regionBondFormSpace S (Ω 0)
def reducedSourceTupleSpace : Set (ReducedSourceTuple L m S) :=
  reducedTupleSpace S Ω ×ˢ regionBondFormSpace S (Ω 0)
abbrev siteSourceTripleSpace : Set (SiteTriple L m S) := siteTripleSpace S Ω
abbrev firstBlockSourceSpace : Set (SiteAtLevel L m S.levels 0 → ComplexMatrix2) :=
  firstBlockSpace S Ω
def sourceEmbedding (W : FineBond L m S → ComplexMatrix2) : SourceTuple L m S → FullTuple L m S
  | ((g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈), X) =>
    (g₁, g₂, g₃, g₄, g₅ + covDivAt S Ω W X, g₆, g₇, g₈)
def reducedSourceEmbedding (W : FineBond L m S → ComplexMatrix2) :
    ReducedSourceTuple L m S → ReducedTuple L m S
  | ((g₁, g₂, g₃, g₄, g₅, g₆, g₇), X) =>
    (g₁, g₂, g₃, g₄, g₅ + covDivAt S Ω W X, g₆, g₇)
def siteSourceEmbedding : SiteTriple L m S → SiteTriple L m S := id
def firstBlockSourceEmbedding :
    (SiteAtLevel L m S.levels 0 → ComplexMatrix2) → SiteAtLevel L m S.levels 0 → ComplexMatrix2 := id
def solutionMax (N : WeightedSeminorms L m S) (W : FineBond L m S → ComplexMatrix2)
    (e : (FineBond L m S → ComplexMatrix2) → ℝ≥0∞) : FullTuple L m S → ℝ≥0∞
  | (A, v, w, σ, p, q, r, ω) =>
    N.onBonds (-1) A ⊔ e A ⊔ N.onSites 0 v ⊔ N.onBonds (-1) (covGradAt S Ω W v) ⊔
      N.onSites (-2) w ⊔ N.onBonds (-3) (covGradAt S Ω W w) ⊔ N.onTops (-4) σ ⊔
      N.onSites (-2) p ⊔ N.onSites 0 q ⊔ N.onBonds (-1) (covGradAt S Ω W q) ⊔
      N.onTops (-4) r ⊔ N.onExpansions (-3) ω
def reducedSolutionMax (N : WeightedSeminorms L m S) (W : FineBond L m S → ComplexMatrix2)
    (e : (FineBond L m S → ComplexMatrix2) → ℝ≥0∞) : ReducedTuple L m S → ℝ≥0∞
  | (A, v, w, σ, p, q, r) =>
    N.onBonds (-1) A ⊔ e A ⊔ N.onSites 0 v ⊔ N.onBonds (-1) (covGradAt S Ω W v) ⊔
      N.onSites (-2) w ⊔ N.onBonds (-3) (covGradAt S Ω W w) ⊔ N.onTops (-4) σ ⊔
      N.onSites (-2) p ⊔ N.onSites 0 q ⊔ N.onBonds (-1) (covGradAt S Ω W q) ⊔
      N.onTops (-4) r
def siteSolutionMax (N : WeightedSeminorms L m S) (W : FineBond L m S → ComplexMatrix2) :
    SiteTriple L m S → ℝ≥0∞
  | (v, w, σ) =>
    N.onSites 0 v ⊔ N.onBonds (-1) (covGradAt S Ω W v) ⊔ N.onSites (-2) w ⊔
      N.onBonds (-3) (covGradAt S Ω W w) ⊔ N.onTops (-4) σ
def firstBlockSolutionMax (N : WeightedSeminorms L m S) (W : FineBond L m S → ComplexMatrix2)
    (w : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : ℝ≥0∞ :=
  N.onSites (-2) w ⊔ N.onBonds (-3) (covGradAt S Ω W w)
def sourceMax (N : WeightedSeminorms L m S) : SourceTuple L m S → ℝ≥0∞
  | ((g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈), X) =>
    N.onBonds (-3) g₁ ⊔ N.onSites (-2) g₂ ⊔ N.onSites (-4) g₃ ⊔ N.onTops 0 g₄ ⊔
      N.onSites (-4) g₅ ⊔ N.onBonds (-3) X ⊔ N.onSites (-2) g₆ ⊔ N.onTops 0 g₇ ⊔
      N.onExpansions (-1) g₈
def reducedSourceMax (N : WeightedSeminorms L m S) : ReducedSourceTuple L m S → ℝ≥0∞
  | ((g₁, g₂, g₃, g₄, g₅, g₆, g₇), X) =>
    N.onBonds (-3) g₁ ⊔ N.onSites (-2) g₂ ⊔ N.onSites (-4) g₃ ⊔ N.onTops 0 g₄ ⊔
      N.onSites (-4) g₅ ⊔ N.onBonds (-3) X ⊔ N.onSites (-2) g₆ ⊔ N.onTops 0 g₇
def siteSourceMax (N : WeightedSeminorms L m S) : SiteTriple L m S → ℝ≥0∞
  | (g₂, g₃, g₄) => N.onSites (-2) g₂ ⊔ N.onSites (-4) g₃ ⊔ N.onTops 0 g₄
def firstBlockSourceMax (N : WeightedSeminorms L m S)
    (g : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : ℝ≥0∞ :=
  N.onSites (-4) g
def solutionSeminormAt (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (Ψ : FullTuple L m S) : ℝ≥0∞ :=
  solutionMax S Ω (localSeminorms S Ω y) W (gradientSeminorm S Ω W y) Ψ
def reducedSolutionSeminormAt (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (Ψ : ReducedTuple L m S) : ℝ≥0∞ :=
  reducedSolutionMax S Ω (localSeminorms S Ω y) W (gradientSeminorm S Ω W y) Ψ
def siteSolutionSeminormAt (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (Ψ : SiteTriple L m S) : ℝ≥0∞ :=
  siteSolutionMax S Ω (localSeminorms S Ω y) W Ψ
def firstBlockSolutionSeminormAt (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (w : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : ℝ≥0∞ :=
  firstBlockSolutionMax S Ω (localSeminorms S Ω y) W w
def sourceSeminormAt (y : FourTorus L m) (g : SourceTuple L m S) : ℝ≥0∞ :=
  sourceMax S (localSeminorms S Ω y) g
def reducedSourceSeminormAt (y : FourTorus L m) (g : ReducedSourceTuple L m S) : ℝ≥0∞ :=
  reducedSourceMax S (localSeminorms S Ω y) g
def siteSourceSeminormAt (y : FourTorus L m) (g : SiteTriple L m S) : ℝ≥0∞ :=
  siteSourceMax S (localSeminorms S Ω y) g
def firstBlockSourceSeminormAt (y : FourTorus L m)
    (g : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : ℝ≥0∞ :=
  firstBlockSourceMax S (localSeminorms S Ω y) g
end YangMills.Construction.SequenceTriples
end
