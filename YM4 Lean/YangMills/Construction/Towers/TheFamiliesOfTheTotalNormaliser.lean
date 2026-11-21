import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.CompositionWithAStepOfTheCriticalBranch
import YangMills.Construction.Towers.NormaliserOfAStepOnTheTowerOfASide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators.Tempered
theorem cast_eq_edgeEquivOfVertexEquiv {L n : ℕ} {d d' : ℤ} (hd : d = d')
    (hl : PeriodicLattice.sublattice L n d = PeriodicLattice.sublattice L n d')
    (hs : ∀ μ, AddEquiv.addSubgroupCongr hl (PeriodicLattice.unitStep L n d μ) =
      PeriodicLattice.unitStep L n d' μ) :
    Equiv.cast (congrArg (PeriodicLattice.Bond L n) hd) =
      edgeEquivOfVertexEquiv (AddEquiv.addSubgroupCongr hl) hs := by
  subst hd
  refine Equiv.ext fun b => PeriodicLattice.Bond.ext ?_ ?_ <;> rfl
theorem topEdgeEquiv_eq_topEdgeEquivUnit (L n k : ℕ) :
    PeriodicOperators.Tempered.topEdgeEquiv L n k = topEdgeEquivUnit L n k :=
  cast_eq_edgeEquivOfVertexEquiv (by simp [PeriodicLattice.levelDepth]) _ _
def logNormaliserOfSide (L n k : ℕ) : (Edge L n k k → Matrices.ComplexMatrix2) → ℝ :=
  logTotalNormaliserRatio L n k
def logNormaliserFamily (L k : ℕ) : FieldFamily L :=
  fun n U => logNormaliserOfSide L n k (U ∘ topEdgeEquivUnit L n k)
theorem logNormaliserFamily_transportTotal (L n k : ℕ) (W : Edge L n k k → Matrices.ComplexMatrix2) :
    logNormaliserFamily L k n (transportTotal (topEdgeEquivUnit L n k) W) =
      logTotalNormaliserRatio L n k W := by
  simp [logNormaliserFamily, logNormaliserOfSide, transportTotal, Function.comp_def]
theorem logNormaliserFamily_zero (L n : ℕ) (U : UnitEdge L n → Matrices.ComplexMatrix2) :
    logNormaliserFamily L 0 n U = 0 := by
  simp [logNormaliserFamily, logNormaliserOfSide, logTotalNormaliserRatio]
end YangMills.Construction.Tower
end
