import YangMills.Construction.Lattice.SolutionsAndSourcesOfTheSystemOfATriple
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice SeparatedSequences SeparatedRegions
namespace SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def siteSmul (θ : FourTorus L m → ℝ) (f : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2 :=
  fun x => θ (x : FourTorus L m) • f x
def bondSmul (θ : FourTorus L m → ℝ) (f : FineBond L m S → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  fun b => θ b.centre • f b
def topSmul (θ : FourTorus L m → ℝ) (f : FourTorus L m → Matrices.ComplexMatrix2) :
    FourTorus L m → Matrices.ComplexMatrix2 :=
  fun y => θ y • f y
def expansionSmul (θ : FourTorus L m → ℝ) (f : LeveledBond L m S → Matrices.ComplexMatrix2) :
    LeveledBond L m S → Matrices.ComplexMatrix2 :=
  fun q => θ (leveledAnchor S q) • f q
def fullTupleSmul (θ : FourTorus L m → ℝ) : FullTuple L m S → FullTuple L m S
  | (A, v, w, σ, p, q, r, ω) =>
    (bondSmul S θ A, siteSmul S θ v, siteSmul S θ w, topSmul θ σ, siteSmul S θ p,
      siteSmul S θ q, topSmul θ r, expansionSmul S θ ω)
def reducedTupleSmul (θ : FourTorus L m → ℝ) : ReducedTuple L m S → ReducedTuple L m S
  | (A, v, w, σ, p, q, r) =>
    (bondSmul S θ A, siteSmul S θ v, siteSmul S θ w, topSmul θ σ, siteSmul S θ p,
      siteSmul S θ q, topSmul θ r)
def siteTripleSmul (θ : FourTorus L m → ℝ) : SiteTriple L m S → SiteTriple L m S
  | (v, w, σ) => (siteSmul S θ v, siteSmul S θ w, topSmul θ σ)
def covDivCommutator (W : FineBond L m S → Matrices.ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (X : FineBond L m S → Matrices.ComplexMatrix2) : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2 :=
  covDivAt S Ω W (bondSmul S θ X) -
    siteSmul S θ (covDivAt S Ω W X)
def sourceTwistedSmul (W : FineBond L m S → Matrices.ComplexMatrix2) (θ : FourTorus L m → ℝ) :
    SourceTuple L m S → SourceTuple L m S
  | ((f₁, f₂, f₃, f₄, f₅, f₆, f₇, f₈), X₅) =>
    ((bondSmul S θ f₁, siteSmul S θ f₂, siteSmul S θ f₃, topSmul θ f₄,
        siteSmul S θ f₅ - covDivCommutator S Ω W θ X₅, siteSmul S θ f₆,
        topSmul θ f₇, expansionSmul S θ f₈),
      bondSmul S θ X₅)
def reducedSourceTwistedSmul (W : FineBond L m S → Matrices.ComplexMatrix2) (θ : FourTorus L m → ℝ) :
    ReducedSourceTuple L m S → ReducedSourceTuple L m S
  | ((f₁, f₂, f₃, f₄, f₅, f₆, f₇), X₅) =>
    ((bondSmul S θ f₁, siteSmul S θ f₂, siteSmul S θ f₃, topSmul θ f₄,
        siteSmul S θ f₅ - covDivCommutator S Ω W θ X₅, siteSmul S θ f₆,
        topSmul θ f₇),
      bondSmul S θ X₅)
def siteSourceTwistedSmul (θ : FourTorus L m → ℝ) : SiteTriple L m S → SiteTriple L m S
  | (f₂, f₃, f₄) => (siteSmul S θ f₂, siteSmul S θ f₃, topSmul θ f₄)
def firstSourceTwistedSmul (θ : FourTorus L m → ℝ) (f₃ : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2 :=
  siteSmul S θ f₃
end SequenceTriples
end YangMills.Construction
end
