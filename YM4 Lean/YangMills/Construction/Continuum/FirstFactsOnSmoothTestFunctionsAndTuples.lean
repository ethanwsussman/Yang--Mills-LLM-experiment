import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndSetsAtPositiveDistance
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace.TupleFacts
open SmoothMaps TestFunctions PeriodicSpace
variable {n : ℕ}
def minSupportSep (f : FnTuple n) : ℝ≥0∞ :=
  ⨅ i, ⨅ j, ⨅ _ : i ≠ j, setDistR4 (tsupport (f i)) (tsupport (f j))
def toComplexTuple (P : Params) (g : Kind.FnTuple P .euclidean n) : FnTuple n :=
  fun i y => ((g i y : ℝ) : ℂ)
def RestrictsFrom (P : Params) (Ψ : Kind.sepC1Tuples P .euclidean n → ℝ)
    (T : smoothRealTupleSet n → ℝ) : Prop :=
  ∀ (f : smoothRealTupleSet n) (g : Kind.sepC1Tuples P .euclidean n),
    toComplexTuple P g.1 = f.1 → T f = Ψ g
def RealAmongComplex (n : ℕ) : Prop :=
  smoothRealTupleSet n = {f | f ∈ smoothComplexTupleSet n ∧ ∀ i, IsRealValued (f i)}
def TensorIsTestFn (f : FnTuple n) : Prop :=
  tensorProd f ∈ testFnOffDiag n ∧
    tsupport (tensorProd f) ⊆ cylinderSet fun i => tsupport (f i)
def TensorSpaceFacts (n : ℕ) : Prop :=
  (∀ f ∈ smoothComplexTupleSet n, TensorIsTestFn f) ∧
    (∀ f ∈ smoothRealTupleSet n, TensorIsTestFn f) ∧
    ∃ W : Submodule ℂ (Config n → ℂ),
      (W : Set (Config n → ℂ)) = testFnOffDiag n ∧
        (W : Set (Config n → ℂ)) ⊆ flatSchwartzSet n
def SeminormMonotone (n : ℕ) : Prop :=
  ∀ φ ∈ schwartzSet n, ∀ a b a' b' : ℕ, a ≤ a' → b ≤ b' →
    decaySeminorm a b φ ≤ decaySeminorm a' b' φ
def ClosedUnderComponentOps (n : ℕ) : Prop :=
  ∀ (i : Fin n) (h h' : FnTuple n), h ∈ smoothComplexTupleSet n → h' ∈ smoothComplexTupleSet n →
    AgreeExcept i h h' → ∀ c : ℂ,
      Function.update h i (h i + h' i) ∈ smoothComplexTupleSet n ∧
      Function.update h i (c • h i) ∈ smoothComplexTupleSet n ∧
      (h ∈ smoothRealTupleSet n → h' ∈ smoothRealTupleSet n → c.im = 0 →
        Function.update h i (h i + h' i) ∈ smoothRealTupleSet n ∧
        Function.update h i (c • h i) ∈ smoothRealTupleSet n)
def MultilinearZeroCoordinate (n : ℕ) : Prop :=
  (∀ T : smoothRealTupleSet n → ℝ, IsRealMultilinearSmooth T →
    ∀ f : smoothRealTupleSet n, (∃ i, f.1 i = 0) → T f = 0) ∧
  ∀ T : smoothComplexTupleSet n → ℂ, IsComplexMultilinearSmooth T →
    ∀ f : smoothComplexTupleSet n, (∃ i, f.1 i = 0) → T f = 0
def MinSupportSepPos (n : ℕ) : Prop :=
  ∀ f ∈ smoothComplexTupleSet n,
    0 < minSupportSep f ∧ ((∀ i, f i ≠ 0) → minSupportSep f < ⊤)
def EuclideanCompat (n : ℕ) : Prop :=
  ∀ P : Params,
    smoothRealTupleSet n = toComplexTuple P ''
      {g | g ∈ Kind.sepC1Tuples P .euclidean n ∧ ∀ i, Kind.IsSmoothFn P .euclidean (g i)} ∧
    ∀ (Ψ : Kind.sepC1Tuples P .euclidean n → ℝ) (T : smoothRealTupleSet n → ℝ),
      Kind.IsMultilinearOn P .euclidean (Kind.sepC1Tuples P .euclidean n) Ψ →
        RestrictsFrom P Ψ T → IsRealMultilinearSmooth T
def RealMultilinearRestrict (n : ℕ) : Prop :=
  ∀ Φ : realTupleSet n univ → ℝ, IsRealMultilinear Φ →
    IsRealMultilinearSmooth fun f : smoothRealTupleSet n => Φ ⟨f.1, f.2.1⟩
def BasicFacts : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    RealAmongComplex n ∧ TensorSpaceFacts n ∧ SeminormMonotone n ∧
      ClosedUnderComponentOps n ∧ MultilinearZeroCoordinate n ∧
      MinSupportSepPos n ∧ EuclideanCompat n ∧
      RealMultilinearRestrict n
end YangMills.Construction.ConfigSpace.TupleFacts
end
