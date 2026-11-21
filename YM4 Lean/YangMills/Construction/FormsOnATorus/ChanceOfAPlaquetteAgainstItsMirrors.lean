import YangMills.Construction.FormsOnATorus.MirrorsOfCells
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps RenormalizationStepParameters WeightedResponses BlockAverages
def plaquetteChessboardStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y =>
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (j M : ℕ) [NeZero (Tb.side * M)], IsTowerAtParameters Tb y T β j →
      T.MarksMeasurable → Even M → (Tb.stepParameters y).n₀ ≤ M →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (Tb.side * M))), ∀ t : ℝ,
        ((markedSampleLaw T β j (Tb.side * M)).real
            {u | t < plaquetteEnergy (topField (Tb.stepParameters y) j (Tb.side * M) u) p.1 p.2.1 p.2.2}) ^ (M ^ 4) ≤
          (markedSampleLaw T β j (Tb.side * M)).real {u | ∀ k : Fin 4 → Fin M,
            t < plaquetteEnergy (topField (Tb.stepParameters y) j (Tb.side * M) u) (plaquetteCellImage Tb.side M p k).1
              (plaquetteCellImage Tb.side M p k).2.1 (plaquetteCellImage Tb.side M p k).2.2}
end YangMills.Construction.ResponseInTheExpansion
end
