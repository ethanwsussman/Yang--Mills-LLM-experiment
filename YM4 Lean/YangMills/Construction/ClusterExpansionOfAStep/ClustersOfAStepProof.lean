import YangMills.Construction.ClusterExpansionOfAStep.BallsAndBlocksOfATorusForm
import YangMills.Construction.ClusterExpansionOfAStep.ClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.HullsOfHotLumps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusFields
variable {n : ℕ}
theorem supDist_parentBlock_le [NeZero n] (L : ℕ) [NeZero L] (x x' : TorusSite (n * L)) :
    supDist (parentBlock L x) (parentBlock L x') ≤ supDist x x' / L + 1 := by apply _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one <;> assumption
theorem coarseHullIsHullState_holds : CoarseHullIsHullState := by
  classical
  intro ℓ hadm r r' hrr hr' n _ hLn V bad Yt
  set C := thickening (2 * r') (torusHotSites ℓ V) with hC
  set Z := storedBlocks ℓ.side r bad Yt C with hZ
  set Y' := coarseHull ℓ.side r r' bad Yt C with hY'
  have hLbig : 2 ^ 16 ≤ ℓ.side := hadm.L_ge
  have hZY : Z ⊆ Y' := fun z hz =>
    (mem_thickening _ _ _).mpr ⟨z, hz, by rw [supDist_self]; omega⟩
  have hCZ : C ⊆ Z := Finset.subset_union_left
  have hsmall : ∀ d, d ≤ 10 * r → d / ℓ.side + 1 ≤ r' := by
    intro d hd
    have h1 : d / ℓ.side ≤ d / 16 := Nat.div_le_div_left (by omega) (by norm_num)
    omega
  have hsub : thickening (2 * r') (torusHotSites ℓ V) ⊆ Y' := hCZ.trans hZY
  refine ⟨hsub, fun X hX => ?_⟩
  have hfromC : ∀ z ∈ X, z ∈ C → ∃ l ∈ torusHotLumps ℓ V, (l ∩ X).Nonempty := by
    intro z hzX hzC
    obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hzC
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx
    have hj := chainConnected_of_supDist_le_two_mul hsub hx hzx
    have hxY : x ∈ Y' := hsub ((mem_thickening _ _ _).mpr ⟨x, hx, by rw [supDist_self]; omega⟩)
    exact ⟨l, hl, x, Finset.mem_inter.mpr
      ⟨hxl, mem_of_chainConnected_of_mem_chainComponents hX hzX hxY (chainConnected_symm hj)⟩⟩
  have hne : ∃ y₀, y₀ ∈ X := by
    obtain ⟨y₀, hy₀, rfl⟩ := mem_chainComponents.mp hX
    exact ⟨y₀, Finset.mem_filter.mpr ⟨hy₀, Relation.ReflTransGen.refl⟩⟩
  obtain ⟨y₀, hy₀X⟩ := hne
  obtain ⟨z, hzZ, hyz⟩ := (mem_thickening _ _ _).mp (subset_of_mem_chainComponents hX hy₀X)
  have hzX : z ∈ X := mem_of_chainConnected_of_mem_chainComponents hX hy₀X (hZY hzZ)
    (chainConnected_of_supDist_le (subset_of_mem_chainComponents hX hy₀X) (hZY hzZ) (by omega))
  rcases Finset.mem_union.mp hzZ with hzC | hzcore
  · exact hfromC z hzX hzC
  · obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hzcore).2
    obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
    have hbu : parentBlock ℓ.side u = z := by
      simpa [sitesInBlocks] using hu1
    obtain ⟨a, ha, hua⟩ := (mem_thickening _ _ _).mp hu2
    obtain ⟨A, hA, haA⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨hAcl, hAC⟩ := Finset.mem_filter.mp hA
    obtain ⟨c, hc⟩ := hAC
    obtain ⟨hcA, hcC⟩ := Finset.mem_inter.mp hc
    have hblock : ∀ v ∈ A, parentBlock ℓ.side v ∈ Z := by
      intro v hv
      refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, ?_⟩)
      refine Finset.mem_inter.mpr
        ⟨?_, (mem_thickening _ _ _).mpr ⟨v, Finset.mem_biUnion.mpr ⟨A, hA, hv⟩, ?_⟩⟩
      · simp [sitesInBlocks]
      · rw [supDist_self]
        omega
    have hchain : ∀ b, ChainConnected (10 * r) (bad.image Prod.fst ∪ Yt ∪ sitesInBlocks ℓ.side C) a b →
        b ∈ A → ChainConnected r' Y' (parentBlock ℓ.side a) (parentBlock ℓ.side b) := by
      intro b hab
      induction hab with
      | refl => exact fun _ => Relation.ReflTransGen.refl
      | tail hab' hs ih =>
        intro hb
        have hu' : _ ∈ A := mem_of_chainConnected_of_mem_chainComponents hAcl haA hs.1 hab'
        refine (ih hu').trans
          (chainConnected_of_supDist_le (hZY (hblock _ hu')) (hZY (hblock _ hb)) ?_)
        exact (supDist_parentBlock_le ℓ.side _ _).trans (hsmall _ hs.2.2)
    have hac := hchain c (chainConnected_of_mem_chainComponents hAcl haA hcA) hcA
    have hzA : ChainConnected r' Y' z (parentBlock ℓ.side a) := by
      refine chainConnected_of_supDist_le (hZY hzZ) (hZY (hblock a haA)) ?_
      rw [← hbu]
      exact (supDist_parentBlock_le ℓ.side _ _).trans (hsmall _ (by omega))
    have hcX : parentBlock ℓ.side c ∈ X :=
      mem_of_chainConnected_of_mem_chainComponents hX hzX (hZY (hblock c hcA)) (hzA.trans hac)
    have hcC' : parentBlock ℓ.side c ∈ C := by
      simpa [sitesInBlocks] using hcC
    exact hfromC _ hcX hcC'
end YangMills.Construction.TorusLumps
end
