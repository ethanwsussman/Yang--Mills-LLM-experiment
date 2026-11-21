import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyAtTheLeastChartProof
import YangMills.Construction.SummableBoundsOfTheFlow.BondsAtACell
import Mathlib
set_option autoImplicit false
open Finset YangMills.Construction.BlockAverages
namespace YangMills.Construction.CellCounting
variable {F : BlockFrame}
noncomputable def blockCoordinateRange (z : F.Cell) (i : Fin 4) : Finset (ZMod (F.period F.depth i)) :=
  (Ico ((F.blockSide : ℤ) * siteCoords z i - ((F.blockSide : ℤ) - 1) / 2)
      ((F.blockSide : ℤ) * siteCoords z i - ((F.blockSide : ℤ) - 1) / 2 + F.blockSide)).image
    fun k : ℤ => (k : ZMod (F.period F.depth i))
theorem card_blockCoordinateRange (z : F.Cell) (i : Fin 4) : (blockCoordinateRange z i).card ≤ F.blockSide := by
  refine card_image_le.trans ?_
  simp
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem period_depth (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem mem_blockCoordinateRange (hL : 0 < F.blockSide) {x : F.Site F.depth} {z : F.Cell}
    (h : enclosingCell x = z) (i : Fin 4) :
    x i ∈ blockCoordinateRange z i := by
  have hLz : (0 : ℤ) < F.blockSide := by exact_mod_cast hL
  set hh : ℤ := ((F.blockSide : ℤ) - 1) / 2 with hhdef
  set c : ℤ := siteCoords x i with hc
  have hpow : (F.blockSide : ℤ) ^ (F.top - F.depth) = F.blockSide := by simp [BlockFrame.top]
  set u : ℤ := (c + hh) / F.blockSide with hu
  have hz : z i = (u : ZMod (F.period F.top i)) := by
    rw [← h]
    simp only [enclosingCell, siteOfCoords, hpow]
    rfl
  have hcz : ((siteCoords z i : ℤ) : ZMod (F.period F.top i)) = z i := by
    simp [siteCoords]
  have hdvd : ((F.period F.top i : ℕ) : ℤ) ∣ u - siteCoords z i := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    rw [hcz, hz]
  obtain ⟨e, he⟩ := hdvd
  set k : ℤ := (c + hh) % F.blockSide with hk
  have hk0 : 0 ≤ k := Int.emod_nonneg _ hLz.ne'
  have hk1 : k < F.blockSide := Int.emod_lt_of_pos _ hLz
  have hdm : (F.blockSide : ℤ) * u + k = c + hh := Int.mul_ediv_add_emod _ _
  have hcx : ((c : ℤ) : ZMod (F.period F.depth i)) = x i := by
    simp [hc, siteCoords]
  refine mem_image.mpr ⟨(F.blockSide : ℤ) * siteCoords z i - hh + k, mem_Ico.mpr ⟨by linarith, by linarith⟩, ?_⟩
  rw [← hcx]
  have hval : c = (F.blockSide : ℤ) * siteCoords z i - hh + k + ((F.period F.depth i : ℕ) : ℤ) * e := by
    have h1 : u = siteCoords z i + ((F.period F.top i : ℕ) : ℤ) * e := by linarith
    have h2 : ((F.period F.depth i : ℕ) : ℤ) = ((F.period F.top i : ℕ) : ℤ) * F.blockSide := by
      rw [period_top, period_depth]
      push_cast
      ring
    rw [h2]
    rw [h1] at hdm
    linarith
  rw [hval]
  push_cast
  simp
theorem bondsPerCellBounded_holds : BondsPerCellBounded := by
  intro L hL
  refine ⟨L ^ 4 * 4, ?_⟩
  intro F hF ι _ j hj z
  classical
  have hL' : 0 < F.blockSide := by rw [hF]; exact hL
  set T : Finset (F.Site F.depth × Fin 4) := (Fintype.piFinset fun i => blockCoordinateRange z i) ×ˢ univ with hT
  have hcard : T.card ≤ L ^ 4 * 4 := by
    rw [hT, card_product, Fintype.card_piFinset, card_univ, Fintype.card_fin]
    have h1 : ∏ i : Fin 4, (blockCoordinateRange z i).card ≤ ∏ _i : Fin 4, L :=
      prod_le_prod' fun i _ => hF ▸ card_blockCoordinateRange z i
    have h2 : ∏ _i : Fin 4, L = L ^ 4 := by simp
    omega
  refine le_trans ?_ hcard
  apply card_le_card_of_injOn j
  · intro b hb
    have hb' : enclosingCell (j b).1 = z := (mem_filter.mp hb).2
    refine mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => mem_blockCoordinateRange hL' hb' i, mem_univ _⟩
  · exact hj.injOn
end YangMills.Construction.CellCounting
