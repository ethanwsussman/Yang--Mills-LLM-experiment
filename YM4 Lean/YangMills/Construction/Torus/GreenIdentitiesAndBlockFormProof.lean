import YangMills.Construction.Torus.GreenIdentitiesAndBlockForm
import YangMills.Construction.Torus.QuadraticFormsAndMatricesOfTheAveragesProof
import YangMills.Construction.Torus.WeightedDistanceAndCellsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric
noncomputable section
namespace GeneralTorus.GreenBlock
section Bonds
variable {D : ScaleData}
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
end Bonds
section Gradients
variable {W : GaugeSetting}
theorem set_antitone (B : SeparatedChain W.data) {i j : ℕ} (h : i ≤ j) :
    B.set j ⊆ B.set i := by
  induction j, h using Nat.le_induction with
  | base => exact Subset.rfl
  | succ j _ ih =>
    by_cases hj : j < W.data.lastLevel
    · exact (B.mono j hj).trans ih
    · rw [B.eq_empty_of_gt (j + 1) (by omega)]
      exact empty_subset _
theorem mem_shellSites_iff (hc : SeparatedChainStructure) {n : ℕ}
    (hn : n ≤ W.data.lastLevel) (y : W.data.Space) :
    y ∈ W.chain.shellSites n ↔ y ∈ (W.data.levelSublattice n : Set W.data.Space) ∧
      y ∈ W.chain.set n ∧ y ∉ W.chain.set (n + 1) := by
  rw [((hc W.data W.chain).2.1 n hn).2.2.1]
  rfl
theorem shellIndex_eq (hc : SeparatedChainStructure) {n : ℕ}
    (hn : n ≤ W.data.lastLevel) {y : W.data.Space} (hy : y ∈ W.chain.shellSites n) :
    W.chain.shellIndex y = n := by
  have hb := (mem_shellSites_iff hc hn y).1 hy
  have hs : {i | y ∈ W.chain.shellSites i} = {n} := by
    ext i
    simp only [mem_ofPred_eq, mem_singleton_iff]
    refine ⟨fun hi => ?_, fun hi => hi ▸ hy⟩
    by_cases hit : i ≤ W.data.lastLevel
    · have ha := (mem_shellSites_iff hc hit y).1 hi
      rcases lt_trichotomy i n with h | h | h
      · exact absurd (set_antitone W.chain h hb.2.1) ha.2.2
      · exact h
      · exact absurd (set_antitone W.chain h ha.2.1) hb.2.2
    · have hl : W.chain.shell i = ∅ := by
        unfold SeparatedChain.shell
        rw [if_neg (by omega), if_neg (by omega)]
      unfold SeparatedChain.shellSites at hi
      rw [hl, inter_empty] at hi
      exact absurd hi (notMem_empty _)
  unfold SeparatedChain.shellIndex
  rw [hs]
  simp
end Gradients
structure LaplacianInputs (W : GaugeSetting) : Prop where
  finiteCoarse : Finite W.CoarseBond
  site : IsInnerProductForm W.data.siteInner
  bond : IsInnerProductForm W.data.bondInner
  coarse : IsInnerProductForm W.coarseInner
  dirichlet : IsInnerProductForm W.chain.dirichletInner
  form : IsInnerProductForm W.formInner
  gradAdj : IsAdjointFor W.data.siteInner W.data.bondInner W.data.grad W.data.gradAdjoint
  meanAdj : IsAdjointFor W.formInner W.coarseInner W.meanOp W.meanOpAdjoint
  siteProjSpec : IsOrthProjFor W.data.siteInner W.chain.dirichletSites W.chain.siteProj
  formProjSpec : IsOrthProjFor W.data.bondInner W.formSubspace W.formProj
  imageProjSpec : IsOrthProjFor W.chain.dirichletInner
    (W.chain.siteMeansKer.map W.chain.dirichletLap)
    (orthProjFor W.chain.dirichletInner (W.chain.siteMeansKer.map W.chain.dirichletLap))
  unit : IsUnit W.gaugeLap
  posDef : W.IsFormPosDef W.gaugeLap
  greenSymm : W.IsFormSymmetric W.greenOp
  greenPosDef : W.IsFormPosDef W.greenOp
  selfAdj : IsSelfAdjointFor W.formInner W.gaugeLap
  energy : ∀ A : ↥W.formSubspace,
    W.formInner A (W.gaugeLap A) =
      W.data.plaquetteL2Norm (W.data.plaquetteCurl A) ^ 2 +
        W.data.siteL2Norm (W.chain.lapImageProj
          (W.chain.siteProj (W.data.gradAdjoint A)) : W.data.SiteField) ^ 2 +
        W.coarseInner (W.meanOp A) (W.massMul (W.meanOp A))
  onto : ∃ E : W.CoarseField →ₗ[ℝ] ↥W.formSubspace, W.meanOp ∘ₗ E = LinearMap.id
  gradMem : ∀ l ∈ W.chain.siteMeansKer,
    W.data.grad (l : W.data.SiteField) ∈ W.formSubspace
  meanGrad : ∀ l ∈ W.chain.siteMeansKer,
    ∀ h : W.data.grad (l : W.data.SiteField) ∈ W.formSubspace,
      W.meanOp ⟨W.data.grad (l : W.data.SiteField), h⟩ = 0
section Algebra
variable {W : GaugeSetting}
variable (F : LaplacianInputs W)
include F
end Algebra
end GeneralTorus.GreenBlock
end
end YangMills.Construction
