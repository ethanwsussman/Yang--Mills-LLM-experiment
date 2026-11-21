import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.BaseLawIsAProduct
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TorusLumps TorusFields StepSettings StepCosts
section
variable {F : BlockFrame}
theorem isBaseChoice_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth) :
    IsBaseChoice J₀ h b ↔ ∀ y, b y ∈ baseSitesAt J₀ h y := by apply _root_.YangMills.Construction.InBoxTransfer.isBaseChoice_iff <;> assumption
end
theorem uniform_piFinset_eq_prod {ι α : Type} [Fintype ι] (s : ι → Finset α) (B : Finset (ι → α))
    (hB : ∀ c, c ∈ B ↔ ∀ y, c y ∈ s y) (b : ι → α) [Decidable (b ∈ B)] [∀ y, Decidable (b y ∈ s y)] :
    (if b ∈ B then 1 / (B.card : ℝ) else 0) = ∏ y, if b y ∈ s y then 1 / ((s y).card : ℝ) else 0 := by
  classical
  have hBe : B = Fintype.piFinset s := by
    ext c
    rw [hB, Fintype.mem_piFinset]
  by_cases hall : b ∈ B
  · rw [if_pos hall]
    have hy := (hB b).mp hall
    rw [Finset.prod_congr rfl fun y _ => if_pos (hy y), Finset.prod_div_distrib, hBe, Fintype.card_piFinset]
    push_cast
    simp
  · rw [if_neg hall]
    obtain ⟨y, hy⟩ : ∃ y, b y ∉ s y := by
      by_contra hc
      push Not at hc
      exact hall ((hB b).mpr hc)
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ y) (if_neg hy)
theorem baseLawIsProduct_holds : BaseLawIsProduct := by
  classical
  intro R n _ W b
  have hB : ∀ c, c ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) ↔
      ∀ y, c y ∈ baseSitesAt (F := stepBlockFrame R.params.side n) R.params.baseDepth
        (stepHotLumps R.params W) y := by
    intro c
    refine Iff.trans ?_ (isBaseChoice_iff _ _ c)
    exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  unfold baseLaw blockBaseWeight
  exact @uniform_piFinset_eq_prod _ _ _ _ _ hB b _ _
end YangMills.Construction.ClusterExpansionOfAStep
end
