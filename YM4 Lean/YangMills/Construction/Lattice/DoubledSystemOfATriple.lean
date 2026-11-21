import YangMills.Construction.Lattice.SolutionsAndSourcesOfTheSystemOfATriple
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences YangMills.Construction.SeparatedRegions YangMills.Construction.Matrices
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def couplingTerm (W : FineBond L m S → ComplexMatrix2) : ReducedTuple L m S → ReducedTuple L m S
  | (A', _, w', _, _, _, _) =>
    reducedInjOne S (covGradAt S Ω W (covDivAt S Ω W A' - w'))
def reducedWeakSeminormAt (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (Ψ : ReducedTuple L m S) : ℝ≥0∞ :=
  reducedSolutionMax S Ω (localSeminorms S Ω y) W (fun _ => 0) Ψ
def axisFieldOfSite (W : FineBond L m S → ComplexMatrix2)
    (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : FineBond L m S × Fin 4 → ComplexMatrix2 :=
  (bondAxisIndexSet S (Ω 0)).indicator fun i =>
    if i.2 = i.1.axis then
      -ComplexMatrix2.conjugateBy (W (Bond.forwardFrom i.1.source i.1.axis))
        (f (i.1.source + unitStep L m (levelDepth S.levels 0) i.1.axis))
    else 0
def siteBoundaryForm (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  bondFormOfPositive ((bondIndexSet S (Ω 0)).indicator fun b =>
    open Classical in
    if Bond.forwardFrom (b.source - unitStep L m (levelDepth S.levels 0) b.axis) b.axis ∉
        (bondsInside (Ω 0) : Set (FineBond L m S)) then
      -((((S.finestMesh L)⁻¹ : ℝ) : ℂ) • f b.source)
    else 0)
def dirichletCorrection (l : SiteAtLevel L m S.levels 0 → ComplexMatrix2)
    (x : SiteAtLevel L m S.levels 0) : ComplexMatrix2 :=
  ((((S.finestMesh L)⁻¹ ^ 2 * (8 - (Bare.degreeInside (Ω 0) x : ℝ)) : ℝ)) : ℂ) • l x
end YangMills.Construction.SequenceTriples
end
