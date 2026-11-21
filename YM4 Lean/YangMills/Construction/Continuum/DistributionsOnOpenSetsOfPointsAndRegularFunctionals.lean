import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces
variable {n : ℕ}
abbrev TestFnOn (V : Set (PointTuple n)) : Type :=
  (smoothCompactSupp V : Set (PointTuple n → ℂ))
def IsTestFnLinear {V : Set (PointTuple n)} (u : TestFnOn V → ℂ) : Prop :=
  ∀ (a b : ℂ) (f g h : TestFnOn V), h.1 = a • f.1 + b • g.1 →
    u h = a * u f + b * u g
def IsDistribOn {V : Set (PointTuple n)} (u : TestFnOn V → ℂ) : Prop :=
  IsTestFnLinear u ∧
    ∀ K : Set (PointTuple n), IsCompact K → K ⊆ V → ∃ (p : ℕ) (c : ℝ), 0 ≤ c ∧
      ∀ f : TestFnOn V, tsupport f.1 ⊆ K →
        ENNReal.ofReal ‖u f‖ ≤ ENNReal.ofReal c * derivSupNorm p f.1
def AgreesOnTensors (σ : SepTuple → ℝ) (u : TestFnOn (distinctLocus n) → ℂ) :
    Prop :=
  ∀ X : SepTupleOfCard n, HasSmoothComponents Set.univ X.1 →
    ∃ hX : tensorProdComplex X.1 ∈
        (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)),
      u ⟨_, hX⟩ = σ ⟨n, X⟩
def IsRegular (σ : SepTuple → ℝ) : Prop :=
  IsSepFunctional σ ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ u : TestFnOn (distinctLocus n) → ℂ, IsDistribOn u ∧ AgreesOnTensors σ u
end YangMills.Construction.TestSpaces
end
