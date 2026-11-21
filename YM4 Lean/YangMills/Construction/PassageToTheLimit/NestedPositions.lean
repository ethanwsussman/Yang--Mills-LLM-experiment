import YangMills.Construction.PassageToTheLimit.SpaceTestFunctionsTranslationsReflectionsPositions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LimitSpaces.RefinedCutoffs
def Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (K' : ℕ+), s.K ≤ K' →
    multiplesOf (latticeScale s (s.K : ℕ)) ⊆ multiplesOf (latticeScale s (K' : ℕ)) ∧
    halfShiftedMultiplesOf (latticeScale s (s.K : ℕ)) ⊆
      halfShiftedMultiplesOf (latticeScale s (K' : ℕ)) ∧
    vertexCoords s s.K ⊆ vertexCoords s K' ∧
    edgeMidCoords s s.K ⊆ edgeMidCoords s K' ∧
    (∀ (E : Ambient) (i i' : ℕ+), i ≤ i' → ∀ P : Set (E.Carrier s),
      IsVertexMirror s E i P → IsVertexMirror s E i' P) ∧
    (∀ (E : Ambient) (i i' : ℕ+), i ≤ i' → ∀ P : Set (E.Carrier s),
      IsEdgeMirror s E i P → IsEdgeMirror s E i' P) ∧
    (∀ i : ℕ+, (0 : ℝ) ∈ vertexCoords s i) ∧
    (∀ c : ℝ,
      realInfDist c (multiplesOf (latticeScale s (s.K : ℕ))) ≤
          ENNReal.ofReal (1 / 2 * latticeScale s (s.K : ℕ)) ∧
        realInfDist c (halfShiftedMultiplesOf (latticeScale s (s.K : ℕ))) ≤
          ENNReal.ofReal (1 / 2 * latticeScale s (s.K : ℕ))) ∧
    Dense (⋃ i : ℕ+, multiplesOf (latticeScale s (i : ℕ))) ∧
    Dense (edgeMidCoordsAll s)
end YangMills.Construction.LimitSpaces.RefinedCutoffs
