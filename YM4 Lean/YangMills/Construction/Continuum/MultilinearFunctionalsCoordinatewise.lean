import YangMills.Construction.Continuum.OneClassOfTuplesAndOneNotionOfMultilinearity
import YangMills.Construction.Continuum.SeparatedTuplesThatDifferOnlyInOneEntry
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open AmbientPoints
open TestSpaces.UnifiedSeparatedTuples
namespace EntrywiseMultilinearity
variable {s : Conventions.StandingParameters} {n : ℕ}
def pairSupports (i : Fin n) (h h' : Fin n → Pt s .euclidean → ℝ) :
    Fin n → Set (Pt s .euclidean) :=
  Function.update (fun l => tsupport (h l)) i (tsupport (h i) ∪ tsupport (h' i))
def updateLinComb (i : Fin n) (c c' : ℝ) (h h' : Fin n → Pt s .euclidean → ℝ) :
    Fin n → Pt s .euclidean → ℝ :=
  Function.update h i (c • h i + c' • h' i)
def c1Product (Y : Fin n → Set (Pt s .euclidean)) : Set (Fin n → Pt s .euclidean → ℝ) :=
  Set.pi Set.univ fun l => c1CompactlySupportedIn (Y l)
def MemCommonProduct (s : Conventions.StandingParameters) (n : ℕ) : Prop :=
  ∀ (i : Fin n) (h h' : Fin n → Pt s .euclidean → ℝ) (c c' : ℝ), AgreeOffComponent s i h h' →
    (Pairwise fun l l' => PositivelySeparated s .euclidean
      (pairSupports i h h' l) (pairSupports i h h' l')) ∧
    h ∈ c1Product (pairSupports i h h') ∧
    h' ∈ c1Product (pairSupports i h h') ∧
    updateLinComb i c c' h h' ∈ c1Product (pairSupports i h h') ∧
    c1Product (pairSupports i h h') ⊆ separatedTuples s .euclidean n
def IsLinearInEachComponent (Ψ : separatedTuples s .euclidean n → ℝ) : Prop :=
  ∀ (i : Fin n) (c c' : ℝ) (h h' h'' : separatedTuples s .euclidean n),
    AgreeOffComponent s i h.1 h'.1 → h''.1 = updateLinComb i c c' h.1 h'.1 →
      Ψ h'' = c * Ψ h + c' * Ψ h'
def MultilinearIffLinearInEachCoordinate (s : Conventions.StandingParameters) (n : ℕ) : Prop :=
  ∀ Ψ : separatedTuples s .euclidean n → ℝ, IsTupleMultilinear Ψ ↔ IsLinearInEachComponent Ψ
def TuplesAgreeOnEuclidean (s : Conventions.StandingParameters) : Prop :=
  (∀ u : ℕ, (separatedTuples s .euclidean u : Set (Fin u → (Fin 4 → ℝ) → ℝ)) =
    TestSpaces.disjointSupportTuples Set.univ u) ∧
  SameTuple ⟨nilTuple s .euclidean, nilTuple_mem_allSeparatedTuples⟩ TestSpaces.sepTupleNil ∧
  allSeparatedTuples s .euclidean =
    Set.range (fun Y : TestSpaces.SepTuple =>
      (⟨Y.1, Y.2.1⟩ : FunctionTuple s .euclidean)) ∧
  ∀ (u : ℕ) (f : separatedTuples s .euclidean u) (X : TestSpaces.SepTupleOfCard u),
    (f.1 : Fin u → (Fin 4 → ℝ) → ℝ) = X.1 → ∀ J : Finset (Fin u),
      SameTuple (toAllSeparated (restrictSeparated f J))
        ⟨J.card, TestSpaces.sepRestrict X J⟩
def MultilinearAgreesOnEuclidean (s : Conventions.StandingParameters) (n : ℕ) : Prop :=
  ∀ (Ψ : separatedTuples s .euclidean n → ℝ) (Φ : TestSpaces.SepTupleOfCard n → ℝ),
    AgreeOnComponents Ψ Φ → (IsTupleMultilinear Ψ ↔ TestSpaces.IsMultilinearOnSep Φ)
def PartitionsAgree : Prop :=
  (∀ n : ℕ, 1 ≤ n → ClusterExpansion.SymGraph.partitions (Fin n) =
    (Finset.univ : Finset (SetPartition.PartitionsFin n)).image fun π => π.parts) ∧
  ∀ u : ℕ, TestSpaces.partitionsNoSingletons (Fin u) =
    (SetPartition.singletonFree u).image fun π => π.parts
def CentredAgree (s : Conventions.StandingParameters) : Prop :=
  ∀ (F : ConnectedFamily s .euclidean)
    (G : (n : ℕ) → 2 ≤ n → TestSpaces.SepTupleOfCard n → ℝ),
    (∀ (n : ℕ) (hn : 2 ≤ n), AgreeOnComponents (F.fn n hn) (G n hn)) →
      AgreeOnSameTuples F.centred (TestSpaces.centredOfCumulants G)
def Statement : Prop :=
  ∀ s : Conventions.StandingParameters,
    (∀ n : ℕ, 1 ≤ n → MemCommonProduct s n ∧ MultilinearIffLinearInEachCoordinate s n ∧
      MultilinearAgreesOnEuclidean s n) ∧
    TuplesAgreeOnEuclidean s ∧ FunctionalsCoincide s ∧ PartitionsAgree ∧
      CentredAgree s
end EntrywiseMultilinearity
end YangMills.Construction
end
