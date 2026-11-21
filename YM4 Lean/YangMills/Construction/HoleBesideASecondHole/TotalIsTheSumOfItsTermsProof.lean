import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.TotalIsTheSumOfItsTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours CellTerms
namespace ChainTerms
open LumpContours.BlockLevels
theorem chainActionEqSumTerms : chainActionEqSumTermsStatement := by
  intro F a S ha hL X k
  classical
  refine ⟨fun z => ?_, ?_⟩
  · unfold cellTerms
    refine add_nonneg (Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg _ p) (mul_nonneg ha ?_)
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => gaugedBlockFit_nonneg _ _ _ c
  · have hplaq : ∀ p ∈ innerPlaquettes S 0, enclosingCell p.1 ∈ S := fun p hp => by
      simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp
      exact enclosingCell_mem_of_mem_sitesOfCells (Nat.zero_le _) hL hp.1
    have hbond : ∀ j, j < F.top → ∀ c ∈ innerBonds S (j + 1), enclosingCell c.1 ∈ S := fun j hj c hc => by
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc
      exact enclosingCell_mem_of_mem_sitesOfCells hj hL hc.1
    unfold gaugedChainAction cellTerms
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    · unfold wilsonAction
      rw [← Finset.sum_fiberwise_of_maps_to (s := innerPlaquettes S 0) (t := S) (g := fun p => enclosingCell p.1) hplaq]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr ?_ fun _ _ => rfl
      ext p
      simp [plaquettesOver]
    · congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← Finset.sum_fiberwise_of_maps_to (s := innerBonds S (j + 1)) (t := S) (g := fun c => enclosingCell c.1)
        (hbond j (Finset.mem_range.1 hj))]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr ?_ fun _ _ => rfl
      ext c
      simp [bondsOver]
end ChainTerms
end YangMills.Construction
end
