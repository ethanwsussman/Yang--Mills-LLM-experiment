import YangMills.Construction.Lattice.DoubledSystemOfATriple
import YangMills.Construction.Lattice.FurtherSeminormsOfSolutionsAndSources
import YangMills.Construction.Lattice.SettingsOfTheCommutatorsWithAFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Matrices PeriodicLattice SeparatedSequences SeparatedRegions CommutatorSettings
namespace SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def lowerHalfDifference (θ : FourTorus L m → ℝ) (b : FineBond L m S) : ℝ :=
  (S.finestMesh L)⁻¹ * (θ b.centre - θ (b.source : FourTorus L m))
def upperHalfDifference (θ : FourTorus L m → ℝ) (b : FineBond L m S) : ℝ :=
  (S.finestMesh L)⁻¹ * (θ (b.target : FourTorus L m) - θ b.centre)
def sourceField (W : FineBond L m S → ComplexMatrix2) :
    ReducedTuple L m S → SiteAtLevel L m S.levels 0 → ComplexMatrix2
  | (A', _, w', _, _, _, _) => covDivAt S Ω W A' - w'
def sourceFieldEmbedding (W : FineBond L m S → ComplexMatrix2) (Ψ' : ReducedTuple L m S) :
    ReducedAugmentedSourceTuple L m S :=
  (reducedSourceInjOne S (siteBoundaryForm S Ω (sourceField S Ω W Ψ')),
    axisFieldOfSite S Ω W (sourceField S Ω W Ψ'))
def divCommutatorOfTuple (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) :
    ReducedTuple L m S → SiteAtLevel L m S.levels 0 → ComplexMatrix2
  | (A', _, _, _, _, _, _) => covDivCommutator S Ω W θ A'
def insideBondComponent (A' : FineBond L m S → ComplexMatrix2) (ν : Fin 4)
    (x : SiteAtLevel L m S.levels 0) : ComplexMatrix2 :=
  (bondsInside (Ω 0) : Set (FineBond L m S)).indicator A' (Bond.forwardFrom x ν)
def splitBondFlux (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (A' : FineBond L m S → ComplexMatrix2) : FineBond L m S × Fin 4 → ComplexMatrix2 :=
  (bondAxisIndexSet S (Ω 0)).indicator fun i =>
    lowerHalfDifference S θ i.1 • insideBondComponent S Ω A' i.2 i.1.source +
      upperHalfDifference S θ i.1 • ComplexMatrix2.conjugateBy (W (Bond.forwardFrom i.1.source i.1.axis))
        (insideBondComponent S Ω A' i.2 (i.1.source + unitStep L m (levelDepth S.levels 0) i.1.axis))
def splitBondRemainder (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (A' : FineBond L m S → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  covGradCommutator S Ω W θ (covDivAt S Ω W A') -
    formCovariantDivergence S (Ω 0) W (splitBondFlux S Ω W θ A')
def sourceCommutator (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (Ψ' : ReducedTuple L m S) : ReducedSourceTuple L m S :=
  reducedSourceInjOne S (covGradCommutator S Ω W θ (sourceField S Ω W Ψ') +
    covGradAt S Ω W (divCommutatorOfTuple S Ω W θ Ψ'))
def weakSourceCommutator (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (Ψ' : ReducedTuple L m S) : ReducedAugmentedSourceTuple L m S :=
  (reducedSourceInjOne S (splitBondRemainder S Ω W θ Ψ'.1 -
        covGradCommutator S Ω W θ Ψ'.2.2.1 +
        siteBoundaryForm S Ω (divCommutatorOfTuple S Ω W θ Ψ')),
    splitBondFlux S Ω W θ Ψ'.1 +
      axisFieldOfSite S Ω W (divCommutatorOfTuple S Ω W θ Ψ'))
end SequenceTriples
end YangMills.Construction
end
