import YangMills.Construction.Continuum.FunctionsNormsBallsAndNeighbourhoods
import YangMills.Construction.Continuum.TensorProductOfTwoFunctionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.PointsPairsAndMultiIndicesOfFourSpace
import YangMills.Construction.TorusOrFourSpace.QuarterSideOpenBallsDistinctPointsAndBoundedFamilies
import YangMills.Construction.TorusOrFourSpace.TensorsOfSeparatedTuples
import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.DenseTensorSpan
open YangMills.Construction.PeriodicSpace.Kind.Tuple
open YangMills.Construction.TorusTransport.TestFunctionOrders (tensorMulti)
def smoothSepTensorSpan (P : Params) (n : ℕ+) (O : Set (Kind.euclidean.Pt P)) :
    Submodule ℂ (Kind.euclidean.Tuple P n → ℂ) :=
  Submodule.span ℂ
    {F | ∃ f ∈ Kind.sepC1Tuples P Kind.euclidean (n : ℕ),
      (∀ i, Kind.IsSmoothFn P Kind.euclidean (f i)) ∧
      (∀ i, TorusTransport.HasCompactSupportIn (E := ℝ) (f i) O) ∧
      F = Kind.tensorFn P Kind.euclidean fun i y => ((f i y : ℝ) : ℂ)}
def DensityStatement : Prop :=
  ∀ (P : Params) (n : ℕ+) (O : Set (Kind.euclidean.Pt P)),
    Kind.IsOpenQ P Kind.euclidean O →
    (∀ F ∈ smoothSepTensorSpan P n O,
      F ∈ Kind.sepTensorSpan P Kind.euclidean (n : ℕ) ∧
        F ∈ testFns P Kind.euclidean (Euclid.injTuplesIn O (n : ℕ))) ∧
    (∀ F : testFns P Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)),
      ∃ Fs : ℕ+ → testFns P Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)),
        (∀ t, (Fs t).1 ∈ smoothSepTensorSpan P n O) ∧ TendstoInTestFns Fs F) ∧
    (∀ T : testFns P Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) → ℂ,
      IsDistrib T → (∀ F, F.1 ∈ smoothSepTensorSpan P n O → T F = 0) → ∀ F, T F = 0) ∧
    ∀ (m : ℕ+) (O' : Set (Kind.euclidean.Pt P)), Kind.IsOpenQ P Kind.euclidean O' →
      O ∩ O' = ∅ →
      ∀ (Fs : ℕ+ → testFns P Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)))
        (F : testFns P Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)))
        (Hs : ℕ+ → testFns P Kind.euclidean (Euclid.injTuplesIn O' (m : ℕ)))
        (H : testFns P Kind.euclidean (Euclid.injTuplesIn O' (m : ℕ))),
        TendstoInTestFns Fs F → TendstoInTestFns Hs H →
        ∃ (hs : ∀ t, tensorMulti n.pos m.pos (Fs t).1 (Hs t).1 ∈
              testFns P Kind.euclidean (Kind.pairwiseDistinct P Kind.euclidean (n + m)))
          (h : tensorMulti n.pos m.pos F.1 H.1 ∈
              testFns P Kind.euclidean (Kind.pairwiseDistinct P Kind.euclidean (n + m))),
          TendstoInTestFns (fun t => ⟨_, hs t⟩) ⟨_, h⟩
end YangMills.Construction.PeriodicSpace.DenseTensorSpan
