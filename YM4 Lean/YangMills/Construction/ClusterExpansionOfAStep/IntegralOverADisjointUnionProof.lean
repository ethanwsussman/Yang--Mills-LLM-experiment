import YangMills.Construction.ClusterExpansionOfAStep.IntegralOverADisjointUnion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.DisjointUnionIntegrals
open YangMills.Construction.ColdStepAtMirrorFrames
theorem integralSplitsOverDisjointUnion_holds : IntegralSplitsOverDisjointUnion := by
  intro α _ S C T G hS hd hG
  subst hS
  have e := volume_preserving_piFinsetUnion (fun _ : α => BondVector) hd
  have hfun : ∀ p : (C → BondVector) × (T → BondVector),
      (MeasurableEquiv.piFinsetUnion (fun _ : α => BondVector) hd) p =
        fun b : ↥(C ∪ T) => joinFields C T p.1 p.2 b := by
    rintro ⟨a, ξ⟩
    funext b
    obtain ⟨b, hb⟩ := b
    by_cases hC : b ∈ C
    · have h1 := Equiv.piFinsetUnion_left (fun _ : α => BondVector) hd (f := a) (g := ξ) hC hb
      simp only [joinFields, dif_pos hC]
      exact h1
    · have hT : b ∈ T := by
        rcases Finset.mem_union.mp hb with h | h
        · exact absurd h hC
        · exact h
      have h1 := Equiv.piFinsetUnion_right (fun _ : α => BondVector) hd (f := a) (g := ξ) hT hb
      simp only [joinFields, dif_neg hC, dif_pos hT]
      exact h1
  have hcomp : (fun p : (C → BondVector) × (T → BondVector) => G fun b => joinFields C T p.1 p.2 b) =
      G ∘ (MeasurableEquiv.piFinsetUnion (fun _ : α => BondVector) hd) := by
    funext p
    simp only [Function.comp, hfun]
  rw [hcomp]
  refine ⟨(e.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hG, ?_⟩
  exact (e.integral_comp' G).symm
end YangMills.Construction.DisjointUnionIntegrals
end
