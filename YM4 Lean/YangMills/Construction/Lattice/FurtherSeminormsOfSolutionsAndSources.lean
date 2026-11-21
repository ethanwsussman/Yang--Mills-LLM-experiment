import YangMills.Construction.Lattice.CommutatorsWithAFunctionAndTheirMap
import YangMills.Construction.Lattice.PointsAndOperatorsOfTheSystem
import YangMills.Construction.Lattice.SeminormsOfFunctionsOnIndexSets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SequenceTriples
open YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences YangMills.Construction.SeparatedRegions YangMills.Construction.Matrices
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
abbrev AugmentedSourceTuple (L m : ℕ) (S : ScaleData) : Type :=
  SourceTuple L m S × (FineBond L m S × Fin 4 → ComplexMatrix2)
abbrev ReducedAugmentedSourceTuple (L m : ℕ) (S : ScaleData) : Type :=
  ReducedSourceTuple L m S × (FineBond L m S × Fin 4 → ComplexMatrix2)
def augmentedSourceTupleSpace : Set (AugmentedSourceTuple L m S) :=
  sourceTupleSpace S Ω ×ˢ bondAxisFunctionSpace S (Ω 0)
def reducedAugmentedSourceTupleSpace : Set (ReducedAugmentedSourceTuple L m S) :=
  reducedSourceTupleSpace S Ω ×ˢ bondAxisFunctionSpace S (Ω 0)
def augmentedSourceEmbedding (W : FineBond L m S → ComplexMatrix2) :
    AugmentedSourceTuple L m S → FullTuple L m S
  | (g, X) => sourceEmbedding S Ω W g + fullInjOne S (formCovariantDivergence S (Ω 0) W X)
def reducedAugmentedSourceEmbedding (W : FineBond L m S → ComplexMatrix2) :
    ReducedAugmentedSourceTuple L m S → ReducedTuple L m S
  | (g, X) =>
    reducedSourceEmbedding S Ω W g + reducedInjOne S (formCovariantDivergence S (Ω 0) W X)
def divergenceSmulCommutator (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (X : FineBond L m S × Fin 4 → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  formCovariantDivergence S (Ω 0) W (bondAxisSmul S θ X) -
    bondSmul S θ (formCovariantDivergence S (Ω 0) W X)
def augmentedSourceTwistedSmul (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) :
    AugmentedSourceTuple L m S → AugmentedSourceTuple L m S
  | (g, X) =>
    match sourceTwistedSmul S Ω W θ g with
    | ((h₁, f), h₅) =>
      (((h₁ - divergenceSmulCommutator S Ω W θ X, f), h₅),
        bondAxisSmul S θ X)
def reducedAugmentedSourceTwistedSmul (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) :
    ReducedAugmentedSourceTuple L m S → ReducedAugmentedSourceTuple L m S
  | (g, X) =>
    match reducedSourceTwistedSmul S Ω W θ g with
    | ((h₁, f), h₅) =>
      (((h₁ - divergenceSmulCommutator S Ω W θ X, f), h₅),
        bondAxisSmul S θ X)
def augmentedSourceSeminormAt (y : FourTorus L m) : AugmentedSourceTuple L m S → ℝ≥0∞
  | (g, X) => sourceSeminormAt S Ω y g ⊔ supLocalNorm S Ω .bondAxes (-2) X y
def reducedAugmentedSourceSeminormAt (y : FourTorus L m) :
    ReducedAugmentedSourceTuple L m S → ℝ≥0∞
  | (g, X) => reducedSourceSeminormAt S Ω y g ⊔ supLocalNorm S Ω .bondAxes (-2) X y
def augmentedSourceHoelderSeminormAt (ε : ℝ) (W : FineBond L m S → ComplexMatrix2)
    (y : FourTorus L m) : AugmentedSourceTuple L m S → ℝ≥0∞
  | (g, X) => sourceSeminormAt S Ω y g ⊔ bondAxisScaledLocalHoelder S Ω ε (-2) W X y
def reducedAugmentedSourceHoelderSeminormAt (ε : ℝ) (W : FineBond L m S → ComplexMatrix2)
    (y : FourTorus L m) : ReducedAugmentedSourceTuple L m S → ℝ≥0∞
  | (g, X) => reducedSourceSeminormAt S Ω y g ⊔ bondAxisScaledLocalHoelder S Ω ε (-2) W X y
def solutionWeakHoelderSeminormAt (β : ℝ) (W : FineBond L m S → ComplexMatrix2)
    (y : FourTorus L m) (Ψ : FullTuple L m S) : ℝ≥0∞ :=
  solutionMax S Ω (localSeminorms S Ω y) W (fun A => bondScaledLocalHoelder S Ω β (-1) W A y) Ψ
def reducedSolutionWeakHoelderSeminormAt (β : ℝ) (W : FineBond L m S → ComplexMatrix2)
    (y : FourTorus L m) (Ψ : ReducedTuple L m S) : ℝ≥0∞ :=
  reducedSolutionMax S Ω (localSeminorms S Ω y) W
    (fun A => bondScaledLocalHoelder S Ω β (-1) W A y) Ψ
def gradientHoelderTerm (β : ℝ) (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (A : FineBond L m S → ComplexMatrix2) : ℝ≥0∞ :=
  bondAxisScaledLocalHoelder S Ω β (-2) W (formCovariantGradient S (Ω 0) W A) y
def solutionStrongHoelderSeminormAt (β : ℝ) (W : FineBond L m S → ComplexMatrix2)
    (y : FourTorus L m) (Ψ : FullTuple L m S) : ℝ≥0∞ :=
  solutionSeminormAt S Ω W y Ψ ⊔ gradientHoelderTerm S Ω β W y Ψ.1
def reducedSolutionStrongHoelderSeminormAt (β : ℝ) (W : FineBond L m S → ComplexMatrix2)
    (y : FourTorus L m) (Ψ : ReducedTuple L m S) : ℝ≥0∞ :=
  reducedSolutionSeminormAt S Ω W y Ψ ⊔ gradientHoelderTerm S Ω β W y Ψ.1
def l2Seminorms (y : FourTorus L m) : WeightedSeminorms L m S where
  onSites s f := localNorm S Ω .sites s f y
  onBonds s f := localNorm S Ω .bonds s f y
  onTops s f := localNorm S Ω .tops s f y
  onExpansions s f := localNorm S Ω .leveled s f y
def gradientL2Term (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (A : FineBond L m S → ComplexMatrix2) : ℝ≥0∞ :=
  localNorm S Ω .bondAxes (-2) (formCovariantGradient S (Ω 0) W A) y
def hessianL2Term (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (A : FineBond L m S → ComplexMatrix2) : ℝ≥0∞ :=
  l2LocalNorm S Ω {i : (FineBond L m S × Fin 4) × Fin 4 | i.1 ∈ bondAxisIndexSet S (Ω 0)}
    (fun i => bondAxisLocation S Ω i.1) (-3)
    (fun i => formCovariantHessian S (Ω 0) W (formCovariantGradient S (Ω 0) W A) i.1 i.2) y
def solutionL2SeminormAt (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (Ψ : FullTuple L m S) : ℝ≥0∞ :=
  solutionMax S Ω (l2Seminorms S Ω y) W (gradientL2Term S Ω W y) Ψ
def reducedSolutionL2SeminormAt (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (Ψ : ReducedTuple L m S) : ℝ≥0∞ :=
  reducedSolutionMax S Ω (l2Seminorms S Ω y) W (gradientL2Term S Ω W y) Ψ
def sourceL2SeminormAt (y : FourTorus L m) (g : SourceTuple L m S) : ℝ≥0∞ :=
  sourceMax S (l2Seminorms S Ω y) g
def reducedSourceL2SeminormAt (y : FourTorus L m) (g : ReducedSourceTuple L m S) : ℝ≥0∞ :=
  reducedSourceMax S (l2Seminorms S Ω y) g
def augmentedSourceL2SeminormAt (y : FourTorus L m) : AugmentedSourceTuple L m S → ℝ≥0∞
  | (g, X) => sourceL2SeminormAt S Ω y g ⊔ localNorm S Ω .bondAxes (-2) X y
def reducedAugmentedSourceL2SeminormAt (y : FourTorus L m) :
    ReducedAugmentedSourceTuple L m S → ℝ≥0∞
  | (g, X) => reducedSourceL2SeminormAt S Ω y g ⊔ localNorm S Ω .bondAxes (-2) X y
def solutionStrongL2SeminormAt (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (Ψ : FullTuple L m S) : ℝ≥0∞ :=
  solutionL2SeminormAt S Ω W y Ψ ⊔ hessianL2Term S Ω W y Ψ.1
def reducedSolutionStrongL2SeminormAt (W : FineBond L m S → ComplexMatrix2) (y : FourTorus L m)
    (Ψ : ReducedTuple L m S) : ℝ≥0∞ :=
  reducedSolutionL2SeminormAt S Ω W y Ψ ⊔ hessianL2Term S Ω W y Ψ.1
end YangMills.Construction.SequenceTriples
end
