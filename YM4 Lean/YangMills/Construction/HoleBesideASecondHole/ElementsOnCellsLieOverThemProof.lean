import YangMills.Construction.HoleBesideASecondHole.CurvatureAtAQuietCellProof
import YangMills.Construction.HoleBesideASecondHole.ElementsOnCellsLieOverThem
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HoleSavings
open BlockAverages LumpContours LatticeGauge BlockSites
variable {F : BlockFrame}
theorem mem_sitesBelow_trans (hodd : Odd F.blockSide) (i : ℕ) (hi : i ≤ F.depth) {x : F.Site F.depth}
    {z : F.Site i} {v : F.Cell}
    (hz : z ∈ sitesBelow i x) (hx : x ∈ sitesBelow F.depth v) : z ∈ sitesBelow i v := by
  exact _root_.YangMills.Construction.HoleSavings.QuietCell.mem_sitesBelow_of_mem_sitesBelow
    (F := F) hodd i hi hz hx
theorem plaquetteEnergy_nonneg {U : F.GaugeField 0} (p : F.Site 0 × Fin 4 × Fin 4) :
    0 ≤ plaquetteEnergy U p := by apply _root_.YangMills.Construction.LumpContours.CutAction.plaquetteEnergy_nonneg <;> assumption
theorem norm_sub_re_mul_nonneg {q : ℍ[ℝ]} (g : UnitQuaternion) : 0 ≤ ‖q‖ - (q * (g : ℍ[ℝ])).re := by apply _root_.YangMills.Construction.HoleSavings.QuietCell.sub_re_mul_unit_nonneg <;> assumption
theorem blockFit_nonneg {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    0 ≤ blockFit X X' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
theorem contourFit_nonneg (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (W : F.GaugeField F.depth) (V : F.GaugeField F.top) (c : F.Cell × Fin 4) : 0 ≤ contourFit J₀ h b W V c :=
  norm_sub_re_mul_nonneg _
theorem fst_mem_of_mem_cutPlaquettes {j : ℕ} {X : Finset (F.Site j)} {p : F.Site j × Fin 4 × Fin 4}
    (h : p ∈ cutPlaquettes X) : p.1 ∈ X := (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1
theorem fst_mem_of_mem_cutBonds {j : ℕ} {X : Finset (F.Site j)} {c : F.Site j × Fin 4} (h : c ∈ cutBonds X) :
    c.1 ∈ X := (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1
theorem cutBelow_mono {i j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) : cutBelow i X ⊆ cutBelow i Y := by apply _root_.YangMills.Construction.HoleSavings.QuietCell.cutBelow_subset_cutBelow <;> assumption
theorem cutPlaquettes_mono {j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ cutPlaquettes X) : p ∈ cutPlaquettes Y := by apply _root_.YangMills.Construction.CoreBondMeans.cutPlaquettes_mono <;> assumption
theorem cutBonds_mono {j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) {c : F.Site j × Fin 4}
    (hc : c ∈ cutBonds X) : c ∈ cutBonds Y := by apply _root_.YangMills.Construction.CoreBondMeans.cutBonds_mono <;> assumption
open Classical in
theorem energyOn_le_energyOver : energyOnLeEnergyOverStatement := by
  intro F L g a s θ J₀ D ha hodd hs
  have hexp : ∀ B : Finset F.Cell, D.energyOver B =
      ∑ p ∈ (cutPlaquettes (cutBelow 0 D.chainSites)).filter
          (fun p => ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 B),
          plaquetteEnergy (D.chain 0) p +
        a * ∑ i ∈ Finset.range F.depth, ∑ c ∈ (cutBonds (cutBelow (i + 1) D.chainSites)).filter
          (fun c => c.1 ∈ cutBelow (i + 1) B ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) B),
            blockFit (D.chain i) (D.chain (i + 1)) c +
        a * ∑ c ∈ (cutBonds D.cells).filter (fun c => c.1 ∈ B ∨ c.1 + unitStep F.top c.2 ∈ B), D.topBondFit c := by
    intro B
    simp only [HoleData.energyOver, Finset.sum_filter]
  have htopn : ∀ c, 0 ≤ D.topBondFit c := fun c => contourFit_nonneg _ _ _ _ _ _
  have hall : ∀ B : Finset F.Cell,
      0 ≤ ∑ p ∈ (cutPlaquettes (cutBelow 0 D.chainSites)).filter
          (fun p => ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 B),
        plaquetteEnergy (D.chain 0) p ∧
      0 ≤ a * ∑ i ∈ Finset.range F.depth, ∑ c ∈ (cutBonds (cutBelow (i + 1) D.chainSites)).filter
          (fun c => c.1 ∈ cutBelow (i + 1) B ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) B),
            blockFit (D.chain i) (D.chain (i + 1)) c := by
    intro B
    refine ⟨Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg p, mul_nonneg ha ?_⟩
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ c
  refine ⟨fun X B hXS hXB => ?_, fun B c hc hcB => ?_⟩
  · rw [hexp B]
    have hnest : ∀ i, i ≤ F.depth → ∀ z ∈ cutBelow i (D.chainSites ∩ cutBelow F.depth X), z ∈ cutBelow i B := by
      intro i hi z hz
      obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).2
      exact Finset.mem_biUnion.mpr ⟨v, hXB hv, mem_sitesBelow_trans hodd i hi hzx hxv⟩
    have hlow : D.chainSites ∩ cutBelow F.depth X ⊆ D.chainSites := Finset.inter_subset_left
    have h1 : ∑ p ∈ cutPlaquettes (cutBelow 0 (D.chainSites ∩ cutBelow F.depth X)), plaquetteEnergy (D.chain 0) p ≤
        ∑ p ∈ (cutPlaquettes (cutBelow 0 D.chainSites)).filter
            (fun p => ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 B),
          plaquetteEnergy (D.chain 0) p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => plaquetteEnergy_nonneg p
      exact Finset.mem_filter.mpr ⟨cutPlaquettes_mono (cutBelow_mono hlow) hp, p.1, by simp [plaquetteCorners],
        hnest 0 (Nat.zero_le _) _ (fst_mem_of_mem_cutPlaquettes hp)⟩
    have h2 : ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) (D.chainSites ∩ cutBelow F.depth X)),
          blockFit (D.chain i) (D.chain (i + 1)) c ≤
        ∑ i ∈ Finset.range F.depth, ∑ c ∈ (cutBonds (cutBelow (i + 1) D.chainSites)).filter
          (fun c => c.1 ∈ cutBelow (i + 1) B ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) B),
            blockFit (D.chain i) (D.chain (i + 1)) c := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i + 1 ≤ F.depth := Finset.mem_range.mp hi
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => ?_) fun c _ _ => blockFit_nonneg _ _ c
      exact Finset.mem_filter.mpr ⟨cutBonds_mono (cutBelow_mono hlow) hc,
        Or.inl (hnest (i + 1) hi' _ (fst_mem_of_mem_cutBonds hc))⟩
    have h3 : ∑ c ∈ cutBonds X, D.topBondFit c ≤
        ∑ c ∈ (cutBonds D.cells).filter (fun c => c.1 ∈ B ∨ c.1 + unitStep F.top c.2 ∈ B), D.topBondFit c := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => ?_) fun c _ _ => htopn c
      exact Finset.mem_filter.mpr ⟨cutBonds_mono hXS hc, Or.inl (hXB (fst_mem_of_mem_cutBonds hc))⟩
    unfold HoleData.energyOn cutChainEnergy
    have := mul_le_mul_of_nonneg_left h2 ha
    have := mul_le_mul_of_nonneg_left h3 ha
    linarith
  · rw [hexp B]
    obtain ⟨b1, b2⟩ := hall B
    have h3 : D.topBondFit c ≤
        ∑ c ∈ (cutBonds D.cells).filter (fun c => c.1 ∈ B ∨ c.1 + unitStep F.top c.2 ∈ B), D.topBondFit c :=
      Finset.single_le_sum (f := fun c => D.topBondFit c) (fun c _ => htopn c) (Finset.mem_filter.mpr ⟨hc, hcB⟩)
    have := mul_le_mul_of_nonneg_left h3 ha
    linarith
end YangMills.Construction.HoleSavings
end
