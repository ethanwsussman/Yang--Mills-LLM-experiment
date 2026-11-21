import YangMills.Construction.ClusterExpansionOfAStep.ShareOfAChainSplitsProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdStepAtMirrorFrames.NearPartsOfTwoTops
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
open BlockOffsets
namespace TwoTopLabels
variable {F : BlockFrame}
def cellIndex (L : ℕ) (z : Fin 4 → ℤ) : Fin 4 → ℤ := fun l => (z l + halfSide L) / (L : ℤ)
def cellRemainder (L : ℕ) (z : Fin 4 → ℤ) : Fin 4 → ℤ := fun l => z l - (L : ℤ) * cellIndex L z l
theorem halfSide_of_eq_two_mul_add_one {L : ℕ} (k : ℕ) (hk : L = 2 * k + 1) : halfSide L = k := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.half_pred_odd <;> assumption
theorem cellRemainder_mem_centredCube {L : ℕ} (hL : Odd L) (z : Fin 4 → ℤ) : cellRemainder L z ∈ centredCube L := by
  rw [mem_centredCube_iff]
  intro l
  obtain ⟨k, hk⟩ := hL
  have hhalf := halfSide_of_eq_two_mul_add_one k hk
  have hLk : (L : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hpos : (0 : ℤ) < L := by rw [hLk]; positivity
  have hdiv := Int.emod_add_mul_ediv (z l + halfSide L) (L : ℤ)
  have hnonneg := Int.emod_nonneg (z l + halfSide L) (ne_of_gt hpos)
  have hlt := Int.emod_lt_of_pos (z l + halfSide L) hpos
  unfold cellRemainder cellIndex
  rw [hhalf] at hdiv hnonneg hlt ⊢
  constructor <;> linarith
theorem mul_abs_cellIndex_le {L : ℕ} (hL : Odd L) (z : Fin 4 → ℤ) (l : Fin 4) :
    (L : ℤ) * |cellIndex L z l| ≤ |z l| + L := by
  have hmem := (mem_centredCube_iff _).1 (cellRemainder_mem_centredCube hL z) l
  have hLpos : (0 : ℤ) < L := by exact_mod_cast hL.pos
  have hhalf : halfSide L ≤ L := by
    unfold halfSide
    omega
  have hsplit : (L : ℤ) * cellIndex L z l = z l - cellRemainder L z l := by
    unfold cellRemainder
    ring
  have habs : |(L : ℤ) * cellIndex L z l| = (L : ℤ) * |cellIndex L z l| := by
    rw [abs_mul, abs_of_pos hLpos]
  rw [← habs, hsplit]
  have hrem : |cellRemainder L z l| ≤ L := abs_le.2 ⟨by linarith [hmem.1], hmem.2.trans hhalf⟩
  exact (abs_sub _ _).trans (by linarith)
theorem cellCentre_add_siteOfCoords_eq (Y : F.Cell) (z : Fin 4 → ℤ) :
    (cellCentre F.depth Y + siteOfCoords F.depth z : F.Site F.depth) =
      cellCentre F.depth (Y + siteOfCoords F.top (cellIndex F.blockSide z)) +
        siteOfCoords F.depth (cellRemainder F.blockSide z) := by
  rw [cellCentre_add F.depth (by simp [BlockFrame.top]) Y (cellIndex F.blockSide z), add_assoc,
    ← siteOfCoords_add]
  congr 2
  funext l
  simp only [top_sub_depth, pow_one, Pi.add_apply, cellRemainder]
  ring
theorem siteOfCoords_injOn {j r : ℕ} (hper : ∀ i, 2 * r + 2 < F.period j i) {a b : Fin 4 → ℤ}
    (ha : WithinRadius r a) (hb : WithinRadius r b)
    (h : (siteOfCoords j a : F.Site j) = siteOfCoords j b) : a = b := by
  funext i
  have hcast : ((a i : ℤ) : ZMod (F.period j i)) = ((b i : ℤ) : ZMod (F.period j i)) := congrFun h i
  have hval := congrArg ZMod.valMinAbs hcast
  have hp : (2 * (r : ℤ) + 2) < (F.period j i : ℤ) := by exact_mod_cast hper i
  rw [valMinAbs_intCast_of_small (Or.inr (by linarith [ha i])),
    valMinAbs_intCast_of_small (Or.inr (by linarith [hb i]))] at hval
  exact hval
variable {F' : BlockFrame}
theorem isAxialTreeBond_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (h o : Fin 4 → ℤ)
    (ho : o ∈ centredCube F.blockSide) (i : Fin 4) :
    IsAxialTreeBond ((cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o : F.Site F.depth), i) ↔
      ¬ o i = halfSide F.blockSide ∧ ∀ l, i < l → o l = 0 := by
  unfold IsAxialTreeBond
  rw [isCrossingBond_iff hL hs _ o ho i]
  simp only [cellOffset_offset hL hs _ o ho]
theorem bondKind_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hL' : Odd F'.blockSide)
    (hs' : ∀ i, 2 ≤ F'.extent i) (hLL : F'.blockSide = F.blockSide)
    (Y : F.Cell) (Y' : F'.Cell) (h h' o : Fin 4 → ℤ) (ho : o ∈ centredCube F.blockSide) (i : Fin 4) :
    (IsCrossingBond ((cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o : F.Site F.depth), i) ↔
      IsCrossingBond ((cellCentre F'.depth (Y' + siteOfCoords F'.top h') + siteOfCoords F'.depth o :
        F'.Site F'.depth), i)) ∧
    (IsAxialTreeBond ((cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o : F.Site F.depth), i) ↔
      IsAxialTreeBond ((cellCentre F'.depth (Y' + siteOfCoords F'.top h') + siteOfCoords F'.depth o :
        F'.Site F'.depth), i)) := by
  have ho' : o ∈ centredCube F'.blockSide := by rw [hLL]; exact ho
  rw [isCrossingBond_iff hL hs _ o ho i, isCrossingBond_iff hL' hs' _ o ho' i, isAxialTreeBond_iff hL hs _ _ o ho i,
    isAxialTreeBond_iff hL' hs' _ _ o ho' i, hLL]
  exact ⟨Iff.rfl, Iff.rfl⟩
theorem distFromOne_mul_inv (g h : UnitQuaternion) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (g * h⁻¹) = ‖(g : ℍ[ℝ]) - (h : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GaugeFixing.norm_mul_inv_sub_one <;> assumption
theorem distFromOne_chartedField_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hL' : Odd F'.blockSide)
    (hs' : ∀ i, 2 ≤ F'.extent i) (hLL : F'.blockSide = F.blockSide)
    (hshort : ∀ u v : imaginaryQuaternions,
      ‖((expUnit u : UnitQuaternion) : ℍ[ℝ]) - ((expUnit v : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖u - v‖)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (h o : Fin 4 → ℤ) (ho : o ∈ centredCube F.blockSide) (i : Fin 4)
    (hV : V (Y + siteOfCoords F.top h) i = V' (Y' + siteOfCoords F'.top h) i) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (chartedField w' V' (cellCentre F'.depth (Y' + siteOfCoords F'.top h) + siteOfCoords F'.depth o) i *
        (chartedField w V (cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o) i)⁻¹) ≤
      ‖w' (cellCentre F'.depth (Y' + siteOfCoords F'.top h) + siteOfCoords F'.depth o) i -
        w (cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o) i‖ := by
  classical
  have ho' : o ∈ centredCube F'.blockSide := by rw [hLL]; exact ho
  obtain ⟨hcross, htree⟩ := bondKind_iff hL hs hL' hs' hLL Y Y' h h o ho i
  unfold chartedField
  by_cases hc : IsCrossingBond ((cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o :
      F.Site F.depth), i)
  · rw [if_pos hc, if_pos (hcross.1 hc), enclosingCell_offset hL hs _ o ho, enclosingCell_offset hL' hs' _ o ho', hV,
      distFromOne_mul_inv]
    have hright : ∀ a b c : UnitQuaternion,
        ‖((a * c : UnitQuaternion) : ℍ[ℝ]) - ((b * c : UnitQuaternion) : ℍ[ℝ])‖ = ‖(a : ℍ[ℝ]) - (b : ℍ[ℝ])‖ := by
      intro a b c
      have hfac : ((a * c : UnitQuaternion) : ℍ[ℝ]) - ((b * c : UnitQuaternion) : ℍ[ℝ]) =
          ((a : ℍ[ℝ]) - (b : ℍ[ℝ])) * (c : ℍ[ℝ]) := by
        rw [sub_mul]
        rfl
      rw [hfac, norm_mul, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, mul_one]
    rw [hright]
    exact hshort _ _
  · rw [if_neg hc, if_neg (fun q => hc (hcross.2 q))]
    by_cases ht : IsAxialTreeBond ((cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o :
        F.Site F.depth), i)
    · rw [if_pos ht, if_pos (htree.1 ht)]
      simp [_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne]
    · rw [if_neg ht, if_neg (fun q => ht (htree.2 q)), distFromOne_mul_inv]
      exact hshort _ _
theorem crossingMove_eq {r : ℕ} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hL' : Odd F'.blockSide)
    (hs' : ∀ i, 2 ≤ F'.extent i) (hLL : F'.blockSide = F.blockSide)
    (hper : ∀ i, 2 * r + 2 < F.period F.top i) (hper' : ∀ i, 2 * r + 2 < F'.period F'.top i)
    (Y : F.Cell) (Y' : F'.Cell) (h o : Fin 4 → ℤ) (ho : o ∈ centredCube F.blockSide) (hh : WithinRadius r h)
    (i : Fin 4) (e : Fin 2 → (Fin 4 → ℤ) × Fin 4) (he : ∀ l, WithinRadius r (e l).1)
    (X : Fin 2 → imaginaryQuaternions) :
    crossingMove (bondsAt Y e) X (cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o) i =
      crossingMove (bondsAt Y' e) X (cellCentre F'.depth (Y' + siteOfCoords F'.top h) + siteOfCoords F'.depth o) i := by
  classical
  have ho' : o ∈ centredCube F'.blockSide := by rw [hLL]; exact ho
  obtain ⟨hcross, -⟩ := bondKind_iff hL hs hL' hs' hLL Y Y' h h o ho i
  funext τ
  unfold crossingMove
  by_cases hc : IsCrossingBond ((cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o :
      F.Site F.depth), i)
  · rw [if_pos hc, if_pos (hcross.1 hc), enclosingCell_offset hL hs _ o ho, enclosingCell_offset hL' hs' _ o ho']
    unfold bondSpread
    refine Finset.sum_congr rfl fun l _ => ?_
    have key : (bondsAt Y e l = (Y + siteOfCoords F.top h, i)) ↔
        (bondsAt Y' e l = (Y' + siteOfCoords F'.top h, i)) := by
      simp only [bondsAt, Prod.mk.injEq, add_right_inj]
      constructor
      · rintro ⟨hsite, hdir⟩
        exact ⟨by rw [siteOfCoords_injOn hper (he l) hh hsite], hdir⟩
      · rintro ⟨hsite, hdir⟩
        exact ⟨by rw [siteOfCoords_injOn hper' (he l) hh hsite], hdir⟩
    by_cases hb : bondsAt Y e l = (Y + siteOfCoords F.top h, i)
    · rw [if_pos hb, if_pos (key.1 hb)]
    · rw [if_neg hb, if_neg (fun q => hb (key.2 q))]
  · rw [if_neg hc, if_neg (fun q => hc (hcross.2 q))]
end TwoTopLabels
end ColdStepAtMirrorFrames
end YangMills.Construction
end
