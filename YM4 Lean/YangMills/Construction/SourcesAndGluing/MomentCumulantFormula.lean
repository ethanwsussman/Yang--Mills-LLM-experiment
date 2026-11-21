import YangMills.Construction.SourcesAndGluing.LogarithmDerivativesPartitionsCumulantsAndConnectedFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.MomentCumulant
def Claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ (U : Set (Coordinates.ComplexCoordinates n)) (h : Coordinates.ComplexCoordinates n → ℂ),
      IsOpen U → (0 : Coordinates.ComplexCoordinates n) ∈ U → HolomorphicOnSet U h → h 0 = 1 →
        setPartial (firstIndices n) (fun z => principalLog (h z)) 0 =
          ∑ π : IndexPartition n,
            (-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
              ∏ J ∈ π.parts, setPartial J h 0) ∧
    (∑ π : IndexPartition n,
        (blockCount π - 1).factorial * ∏ J ∈ π.parts, J.card.factorial) =
      (n - 1).factorial * (2 ^ n - 1) ∧
    Fintype.card (IndexPartition n) ≤ n.factorial
end YangMills.Construction.SourcesAndGluing.MomentCumulant
end
