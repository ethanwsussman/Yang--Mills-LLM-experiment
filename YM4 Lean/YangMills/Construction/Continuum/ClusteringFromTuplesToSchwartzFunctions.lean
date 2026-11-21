import YangMills.Construction.Continuum.TestSpacesAndNormsOfTheAxiomsOnSchwartzFunctions
import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.WightmanReconstruction
def flatSequenceAsMaps (S : ConfigSpace.FlatSequence) :
    (n : ℕ) → TestSpaces.flatSchwartzSet n → ℂ
  | 0, f => S 0 ⟨f.1 fun i => i.elim0, Set.mem_univ _⟩
  | m + 1, f => S (m + 1) ⟨f.1, (SchwartzAxioms.flatSchwartzSet_eq (n := m + 1)).subset f.2⟩
def IsTranslationInvariant (σ : TestSpaces.SepTuple → ℝ) : Prop :=
  ∀ y : Fin 4 → ℝ, IsMotionInvariant σ (UpperHalfTensors.translateMotion y)
def IsReflectionPositiveOnSpan (σ : TestSpaces.SepTuple → ℝ) : Prop :=
  ∀ F ∈ SeparatedTuples.spanIn TestSpaces.upperHalfSpace,
    (linearExtension σ
        (SeparatedTuples.formalMul
          (SeparatedTuples.pushSpan TimeAxis.timeReflection (SeparatedTuples.conjugation F)) F)).im = 0 ∧
      0 ≤ (linearExtension σ
        (SeparatedTuples.formalMul
          (SeparatedTuples.pushSpan TimeAxis.timeReflection (SeparatedTuples.conjugation F)) F)).re
def TupleClusteringAlong (σ : TestSpaces.SepTuple → ℝ) (v : Fin 4 → ℝ) : Prop :=
  ∀ A ∈ smoothSupportedIn TestSpaces.upperHalfSpace,
    ∀ B ∈ smoothSupportedIn TestSpaces.upperHalfSpace,
      Tendsto
        (fun t : ℝ => σ (TupleLists.ofList
          (SeparatedTuples.SepTuple.juxt (SeparatedTuples.push TimeAxis.timeReflection A)
            (SeparatedTuples.push (SeparatedTuples.translate (t • v)) B))))
        atTop
        (𝓝 (σ (TupleLists.ofList (SeparatedTuples.push TimeAxis.timeReflection A)) *
          σ (TupleLists.ofList B)))
def SchwingerClusteringAlong (S : ConfigSpace.FlatSequence) (v : Fin 4 → ℝ) : Prop :=
  ∀ f g : ConfigSpace.PosTimeSeq,
    ConfigSpace.PosTimeSeq.IsFinitelySupported f → ConfigSpace.PosTimeSeq.IsFinitelySupported g →
      Tendsto
        (fun t : ℝ =>
          S.reflectionPairing (fun q => (f q).1) fun q =>
            ConfigSpace.shiftActAt (t • v) (g q).1)
        atTop
        (𝓝 ((∑ᶠ q : ℕ, S.evalAt (ConfigSpace.flipConjAt (f q).1)) *
          ∑ᶠ q : ℕ, S.evalAt (g q).1))
theorem hasClusterProperty_iff (S : ConfigSpace.FlatSequence) :
    ConfigSpace.HasClusterProperty S ↔
      ∀ v ∈ ConfigSpace.zeroTimeHyperplane, v ≠ 0 → SchwingerClusteringAlong S v :=
  ⟨fun h v hv hv0 f g hf hg => h f g hf hg v hv hv0, fun h f g hf hg v hv hv0 => h v hv hv0 f g hf hg⟩
def ClusteringTransfer.Statement : Prop :=
  ∀ (σ : TestSpaces.SepTuple → ℝ) (S : ConfigSpace.FlatSequence) (v : Fin 4 → ℝ),
    TestSpaces.IsSepFunctional σ → IsTranslationInvariant σ →
    IsReflectionPositiveOnSpan σ →
    (∀ c : ConfigSpace.flatOffDiagonalAt 0, S 0 c = c.1) →
    TestSpaces.IsSchwingerFamily σ (flatSequenceAsMaps S) →
    v ∈ ConfigSpace.zeroTimeHyperplane → TupleClusteringAlong σ v →
    SchwingerClusteringAlong S v
end YangMills.Construction.WightmanReconstruction
end
