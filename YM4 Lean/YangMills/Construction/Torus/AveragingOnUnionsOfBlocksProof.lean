import YangMills.Construction.Torus.AveragingOnUnionsOfBlocks
import YangMills.Construction.Weighted.GivenChainGeneral
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
open GivenChainGeneral in
theorem blockUnionAveraging_holds
    (hGiven : GivenChainGeneralFacts) :
    BlockUnionAveragingStatement := by
  intro D B W hW
  obtain ⟨Y, ⟨y₀, hy₀⟩, hYs, hWeq⟩ := hW
  have hmono : ∀ n, n ≤ D.top → B.stage n ⊆ B.stage 0 := by
    intro n
    induction n with
    | zero => exact fun _ => Subset.rfl
    | succ n ih =>
      intro hn
      exact (B.decreasing n hn).trans (ih (Nat.le_of_succ_le hn))
  have hfirst : (B.stage 0).Nonempty := by
    have hy := hYs hy₀
    simp only [SeparatedChain.allSites, mem_iUnion, Finset.mem_range] at hy
    obtain ⟨n, hn, hyn⟩ := hy
    have hn' : n ≤ D.top := Nat.lt_succ_iff.1 hn
    have hlayer : (B.layer n).Nonempty := ⟨y₀, hyn.2⟩
    unfold SeparatedChain.layer at hlayer
    split_ifs at hlayer with h1 h2
    · obtain ⟨z, hz⟩ := closure_nonempty_iff.1 hlayer
      exact ⟨z, hmono n hn' hz.1⟩
    · obtain ⟨z, hz⟩ := hlayer
      exact ⟨z, hmono n hn' hz⟩
    · exact absurd hlayer not_nonempty_empty
  have hb : BlockPartition B := (hGiven ⟨D, B, hfirst⟩).2.2.2.2.1
  have hY : Y = B.sitesIn W := by
    rw [hWeq]
    exact hb.sitesIn_iUnion Y hYs
  have hW0 : D.bareSites W = ⋃ y ∈ Y, B.block y := by
    rw [hWeq]
    exact hb.bareSites_iUnion Y hYs
  have hcenter : ∀ x ∈ D.bareSites (B.stage 0),
      B.blockCenter x ∈ B.allSites ∧ x ∈ B.block (B.blockCenter x) := by
    intro x hx
    rw [← hb.iUnion_block] at hx
    simp only [mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact Classical.epsilon_spec (p := fun y => y ∈ B.allSites ∧ x ∈ B.block y) ⟨y, hy, hxy⟩
  have heval : ∀ (w : B.LayerFn) (y : D.Space) (h : y ∈ B.allSites),
      B.layerEval w y = w ⟨y, h⟩ := by
    intro w y h
    simp [SeparatedChain.layerEval, h]
  have hT : ∀ w ∈ B.layerSpaceOn W, ∀ x, x ∉ D.bareSites W →
      (B.avgOpAdjoint w : D.BareSite → ℝ) x = 0 := by
    intro w hw x hxW
    by_cases hx : x ∈ D.bareSites (B.stage 0)
    · obtain ⟨hc, hxc⟩ := hcenter x hx
      have hnot : B.blockCenter x ∉ B.sitesIn W := by
        intro hin
        rw [← hY] at hin
        apply hxW
        rw [hW0]
        exact mem_biUnion hin hxc
      have hv : w ⟨B.blockCenter x, hc⟩ = 0 := hw ⟨B.blockCenter x, hc⟩ hnot
      change (D.bareSites (B.stage 0)).indicator
        (fun x => B.layerEval w (B.blockCenter x)) x = 0
      rw [indicator_of_mem hx, heval w _ hc, hv]
    · exact (B.avgOpAdjoint w).2 x hx
  have hQ : ∀ f : ↥(B.bareSpaceOn W),
      B.avgOp (B.bareSpaceOnIncl W f) ∈ B.layerSpaceOn W := by
    intro f y hy
    have hzero : ∀ x ∈ B.block y, (f : D.BareSite → ℝ) x = 0 := by
      intro x hxy
      refine (Submodule.mem_inf.1 f.2).2 x ?_
      intro hxW
      rw [hW0] at hxW
      simp only [mem_iUnion] at hxW
      obtain ⟨y', hy', hxy'⟩ := hxW
      have hne : (y : D.Space) ≠ y' := by
        intro h
        apply hy
        rw [← hY, h]
        exact hy'
      exact disjoint_left.1 (hb.block_pairwise_disjoint y y.2 y' (hYs hy') hne) hxy hxy'
    change ((D.L : ℝ) ^ (B.level y * 4))⁻¹ * ∑ᶠ x ∈ B.block y, (f : D.BareSite → ℝ) x = 0
    rw [finsum_mem_congr rfl hzero]
    simp
  have hresBare : ∀ w : ↥(B.layerSpaceOn W),
      (B.restrictBare W (B.avgOpAdjoint w) : D.BareSite → ℝ) =
        (B.avgOpAdjoint w : D.BareSite → ℝ) := by
    intro w
    funext x
    change (D.bareSites W).indicator (B.avgOpAdjoint w : D.BareSite → ℝ) x = _
    by_cases hx : x ∈ D.bareSites W
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, hT w w.2 x hx]
  have hresLayer : ∀ f : ↥(B.bareSpaceOn W),
      (B.restrictLayer W (B.avgOp (B.bareSpaceOnIncl W f)) :
          B.LayerFn) =
        B.avgOp (B.bareSpaceOnIncl W f) := by
    intro f
    funext y
    change {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}.indicator
      (B.avgOp (B.bareSpaceOnIncl W f)) y = _
    by_cases hy : (y : D.Space) ∈ B.sitesIn W
    · exact indicator_of_mem (s := {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}) hy _
    · rw [indicator_of_notMem (s := {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}) hy,
        hQ f y hy]
  refine ⟨⟨fun w hw => Submodule.mem_inf.2 ⟨(B.avgOpAdjoint w).2, hT w hw⟩, hQ, hresBare,
    hresLayer⟩, ?_⟩
  intro 𝔟 _ w g hg
  have hrestricted : B.restrictBare W (B.avgOpAdjoint w) = g :=
    Subtype.ext ((hresBare w).trans hg.symm)
  change (B.restrictLayer W (B.avgOp (B.bareSpaceOnIncl W
      ((B.admissibleGreen W 𝔟 * B.admissibleGreen W 𝔟)
        (B.restrictBare W (B.avgOpAdjoint w))))) : B.LayerFn) = _
  rw [hrestricted]
  exact hresLayer _
end YangMills.Construction.Weighted
end
