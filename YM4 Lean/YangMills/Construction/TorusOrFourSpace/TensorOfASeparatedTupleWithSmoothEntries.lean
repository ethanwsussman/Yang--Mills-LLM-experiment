import YangMills.Construction.Continuum.FunctionsNormsBallsAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.PointsPairsAndMultiIndicesOfFourSpace
import YangMills.Construction.TorusOrFourSpace.TensorsOfSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Euclid
open Kind.Tuple
def SmoothSepTensorFacts : Prop :=
  ∀ (D : Params) (n : ℕ+) (O : Set (Kind.euclidean.Pt D)),
    Kind.IsOpenQ D Kind.euclidean O →
    ∀ f ∈ Kind.sepC1Tuples D Kind.euclidean (n : ℕ),
      (∀ i, Kind.IsSmoothFn D Kind.euclidean (f i)) →
      (∀ i, TorusTransport.HasCompactSupportIn (f i) O) →
      let F : Kind.euclidean.Tuple D n → ℂ :=
        Kind.tensorFn D Kind.euclidean fun i y => ((f i y : ℝ) : ℂ)
      let C : Set (Kind.euclidean.Tuple D n) :=
        boxSet D Kind.euclidean fun i => Kind.supportQ D Kind.euclidean (f i)
      IsSmoothT D Kind.euclidean F ∧ supportT D Kind.euclidean F = C ∧
        IsCompactT D Kind.euclidean C ∧ C ⊆ injTuplesIn O (n : ℕ)
end YangMills.Construction.PeriodicSpace.Euclid
end
