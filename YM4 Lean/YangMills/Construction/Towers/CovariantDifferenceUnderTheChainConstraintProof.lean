import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSites
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfiguration
import YangMills.Construction.Towers.CovariantDifferenceUnderTheChainConstraint
import YangMills.Construction.Towers.ExpansionOfTheIterateInTheLeftChart
import YangMills.Construction.Towers.RealAndCovariantDifferentialsOfTheChain
import YangMills.Construction.Towers.TheChainOfABlockField
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
namespace CovDiffConstraintLemmas
variable {L n k : ℕ}
private theorem isPositivelyOriented_or_opposite {m : ℕ} {j : ℤ} (e : PeriodicLattice.Bond L m j) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
private theorem covDiff_congr_positive {V V' : Edge L n k k → Matrices.ComplexMatrix2}
    (h : ∀ e : Edge L n k k, e.IsPositivelyOriented → V e = V' e)
    (l : Vertex L n k k → Matrices.ComplexMatrix2) :
    covDiff V l = covDiff V' l := by
  funext e
  simp only [covDiff, extendOddly]
  split_ifs with he
  · rw [h e he]
  · rw [h e.opposite ((isPositivelyOriented_or_opposite e).resolve_left he)]
end CovDiffConstraintLemmas
open CovDiffConstraintLemmas in
theorem covDiffUnderTopConstraint_holds
    (hR : RealDerivEqComplexAtChainBottom)
    (hC : TrivialFieldAverages.AtTrivialField)
    (hChain : BlockFieldChainProperties)
    (hComp : ProlongCompositesAndVertexLayers.Statement)
    (hExp : IterLeftChartExpansion) :
    CovDiffUnderTopConstraint := by
  intro L n k hL hn hk
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨hTop, -, -⟩ := hComp.1 L n k hL hn hk
  have hchain := (hChain L n k hL hn hk hL0).1
  have h₁ : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k,
      _ := (hTop.tendsto 0 (Nat.zero_le k)).eventually (hExp L n k hL hn hk)
  have h₂ : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k,
      chosenProlongIter L n k (Nat.zero_le k) W = chosenProlongComp L n k k W :=
    hTop.comp_zero_eq
  have e₁ : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, _ := hchain
  have e₂ : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, _ :=
    hR L n k hL hn hk
  show ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, _
  filter_upwards [h₁, h₂, e₁, e₂] with W hexp hcomp hW hreal l B hB
  rw [hcomp, ← chainBottom_eq] at hexp
  have hmember : smoothingIter L n k k (chainBottom W) = W := by
    have h := (hW.1 k le_rfl).2
    rw [descendingChain_top] at h
    exact h.symm
  have hgauge := ((hC L hL).1 n k hn hk).2.2.2 k le_rfl (chainBottom W) hexp.1.1 l
    (fun z _ => (l.2 z (mem_univ z)).2)
  have hreal' := hreal k le_rfl B
  show (smoothingIterDifferential L n k k (chainBottom W) B : Edge L n k k → Matrices.ComplexMatrix2) = _
  rw [hreal', hB, hgauge]
  refine covDiff_congr_positive (fun e he => ?_) _
  have h := hexp.1.2.1 ⟨e, he⟩
  rw [hmember] at h
  exact h
end YangMills.Construction.Tower
end
