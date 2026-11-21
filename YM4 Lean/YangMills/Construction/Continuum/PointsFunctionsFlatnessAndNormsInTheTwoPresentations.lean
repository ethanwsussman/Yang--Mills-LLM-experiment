import YangMills.Construction.Continuum.NormsOfASchwartzFunction
import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Continuum.TwoPresentations
open YangMills.Construction.TestSpaces (PointTuple MultiIdx4)
def PresentationsAgree : Prop :=
  ∀ n : ℕ,
    ConfigSpace.Config n = PointTuple n ∧
    ConfigSpace.MultiIndex n = MultiIdx4 n ∧
    (∀ (x : PointTuple n) (i : Fin n), ConfigSpace.argTime x i = TestSpaces.timeCoord x i) ∧
    (∀ x : PointTuple n, ConfigSpace.euclidNorm x = TestSpaces.tupleNorm x) ∧
    (∀ β : MultiIdx4 n, ConfigSpace.MultiIndex.order β = TestSpaces.idxOrder β) ∧
    (∀ (β : MultiIdx4 n) (u : PointTuple n → ℂ),
      ConfigSpace.iteratedPartial β u = TestSpaces.multiDeriv β u) ∧
    (∀ ψ : PointTuple n → ℂ,
      ConfigSpace.IsSchwartz ψ ↔ ψ ∈ TestSpaces.schwartzSet n) ∧
    ConfigSpace.schwartzSpace n = TestSpaces.schwartzSet n ∧
    (∀ (ψ : PointTuple n → ℂ) (x : PointTuple n),
      ConfigSpace.FlatAt ψ x ↔ TestSpaces.VanishesToInfiniteOrderAt ψ x) ∧
    (∀ (ψ : PointTuple n → ℂ) (U : Set (PointTuple n)),
      ConfigSpace.FlatOff ψ U ↔ TestSpaces.VanishesToInfiniteOrderOff ψ U) ∧
    ConfigSpace.distinctArgs n = TestSpaces.distinctLocus n ∧
    ConfigSpace.posTimeSet n = TestSpaces.positiveTimeLocus n ∧
    ConfigSpace.negTimeSet n = TestSpaces.negativeTimeLocus n ∧
    (∀ (k : ℕ) (ψ : PointTuple n → ℂ),
      ConfigSpace.schwartzSeminorm k ψ = TestSpaces.weightedSeminorm k ψ) ∧
    (∀ (k : ℕ) (ψ : ConfigSpace.SchwartzFn n),
      ENNReal.ofReal (ConfigSpace.bracketNorm k ψ) =
        TestSpaces.weightedSeminorm k ψ.1)
end YangMills.Construction.Continuum.TwoPresentations
end
