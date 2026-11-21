import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps RenormalizationStepParameters WeightedResponses BlockAverages
def separatedHotPlaquettesRareStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∃ c t₀ yP : ℝ, 0 < t₀ ∧
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (j n : ℕ) [NeZero n], IsTowerAtParameters Tb y T β j →
      T.MarksMeasurable → yP ≤ (couplingFlow (Tb.stepParameters y) β j).1 →
      IsBlockTorusSide (Tb.stepParameters y) n →
      ∀ (ι : Type) [Fintype ι] (P : ι → TorusPlaquette n), (∀ i, P i ∈ plaquettesIn (Finset.univ : Finset (TorusSite n))) →
        (∀ i i', i ≠ i' → ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
          ∀ z' ∈ plaquetteVertices (P i').1 (P i').2.1 (P i').2.2, 2 ^ 17 ≤ supDist z z') →
        ∀ t : ℝ, 0 < t → t ≤ t₀ →
          (markedSampleLaw T β j n).real
              {u | ∀ i, t < plaquetteEnergy (topField (Tb.stepParameters y) j n u) (P i).1 (P i).2.1 (P i).2.2} ≤
            Real.exp (c * (Real.log (couplingFlow (Tb.stepParameters y) β j).1 + 1) * (n : ℝ) ^ 4 -
              2 * Tb.coercivity * (couplingFlow (Tb.stepParameters y) β j).1 * t * (Fintype.card ι : ℝ))
end YangMills.Construction.ResponseInTheExpansion
end
