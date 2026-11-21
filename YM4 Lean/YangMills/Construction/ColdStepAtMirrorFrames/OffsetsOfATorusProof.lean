import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace TorusOffsets
def centredOffset {F : BlockFrame} (Y z : F.Cell) : Fin 4 → ℤ := fun i => ((z - Y) i).valMinAbs
theorem period_top (F : BlockFrame) (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
theorem valMinAbs_intCast_of_lt (n : ℕ) [NeZero n] (a : ℤ) (h : 2 * a.natAbs < n) :
    ((a : ZMod n)).valMinAbs = a := by
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_⟩
  constructor <;> omega
theorem add_siteOfCoords_centredOffset {F : BlockFrame} (Y z : F.Cell) :
    Y + siteOfCoords F.top (centredOffset Y z) = z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.add_siteOfCoords_cellDisplacement <;> assumption
theorem centredOffset_add_siteOfCoords {F : BlockFrame} (hpos : ∀ i, 0 < F.extent i) (Y : F.Cell)
    (v : Fin 4 → ℤ) (hv : ∀ i, 2 * (v i).natAbs < F.extent i) :
    centredOffset Y (Y + siteOfCoords F.top v) = v := by
  funext i
  have hp := period_top F i
  have : NeZero (F.period F.top i) := ⟨by rw [hp]; exact (hpos i).ne'⟩
  have e : ((Y + siteOfCoords F.top v - Y : F.Cell)) i = ((v i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  simp only [centredOffset]
  rw [e]
  exact valMinAbs_intCast_of_lt _ _ (by rw [hp]; exact hv i)
theorem natAbs_centredOffset_le {F : BlockFrame} (Y z : F.Cell) (i : Fin 4) :
    (centredOffset Y z i).natAbs ≤ cellSupDist z Y := by
  unfold cellSupDist centredOffset
  exact Finset.le_sup (f := fun i => ((z i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
theorem natAbs_le_of_withinRadius {r : ℕ} {v : Fin 4 → ℤ} (hv : WithinRadius r v) (i : Fin 4) :
    (v i).natAbs ≤ r := by
  have := hv i
  rw [Int.abs_eq_natAbs] at this
  omega
theorem cellSupDist_add_siteOfCoords {F : BlockFrame} (hpos : ∀ i, 0 < F.extent i) (Y : F.Cell)
    (v : Fin 4 → ℤ) (hv : ∀ i, 2 * (v i).natAbs < F.extent i) :
    cellSupDist (Y + siteOfCoords F.top v) Y = (Finset.univ.sup fun i => (v i).natAbs) ∧
      cellSupDist Y (Y + siteOfCoords F.top v) = (Finset.univ.sup fun i => (v i).natAbs) := by
  constructor
  · unfold cellSupDist
    congr 1
    funext i
    have hp := period_top F i
    have : NeZero (F.period F.top i) := ⟨by rw [hp]; exact (hpos i).ne'⟩
    have e : (Y + siteOfCoords F.top v : F.Cell) i - Y i = ((v i : ℤ) : ZMod (F.period F.top i)) := by
      simp [siteOfCoords]
    rw [e, valMinAbs_intCast_of_lt _ _ (by rw [hp]; exact hv i)]
  · unfold cellSupDist
    congr 1
    funext i
    have hp := period_top F i
    have : NeZero (F.period F.top i) := ⟨by rw [hp]; exact (hpos i).ne'⟩
    have e : Y i - (Y + siteOfCoords F.top v : F.Cell) i = ((-(v i) : ℤ) : ZMod (F.period F.top i)) := by
      simp [siteOfCoords]
    rw [e, valMinAbs_intCast_of_lt _ _ (by rw [hp]; have := hv i; simpa using this)]
    simp
theorem natAbs_valMinAbs_intCast_le (n : ℕ) [NeZero n] (Q : ℤ) :
    ((Q : ZMod n)).valMinAbs.natAbs ≤ Q.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
end TorusOffsets
open TorusOffsets in
theorem torusOffsetsAboutCell_holds (hS : SiteDecomposition) (hB : BlocksCoverLowerLevel) :
    TorusOffsetsAboutCell := by
  intro F r Y hodd hs
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hs i; omega
  have hp : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hb2 : ∀ {v : Fin 4 → ℤ}, WithinRadius r v → ∀ i, 2 * (v i).natAbs < F.extent i := fun hv i => by
    have := natAbs_le_of_withinRadius hv i
    have := hs i
    omega
  obtain ⟨a1, a2, a3, a4⟩ := hS F hodd hs2
  have cell : ∀ (v o : Fin 4 → ℤ) (i : Fin 4), o ∈ centredCube F.blockSide →
      enclosingCell (fineBondAt Y v o i).1 = Y + siteOfCoords F.top v ∧
        cellOffset (fineBondAt Y v o i).1 = o :=
    fun v o i ho => a1 _ _ ho
  refine ⟨cell, ?_, fun v hv => cellSupDist_add_siteOfCoords hp Y v (hb2 hv), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w o o₁ i i₁ hv hw ho ho₁ e
    obtain ⟨c1, c2⟩ := cell v o i ho
    obtain ⟨d1, d2⟩ := cell w o₁ i₁ ho₁
    rw [e] at c1 c2
    have e1 : Y + siteOfCoords F.top v = Y + siteOfCoords F.top w := c1.symm.trans d1
    have e2 := congrArg (centredOffset Y) e1
    rw [centredOffset_add_siteOfCoords hp Y v (hb2 hv), centredOffset_add_siteOfCoords hp Y w (hb2 hw)] at e2
    exact ⟨e2, c2.symm.trans d2⟩
  · intro x i
    have hc := a3 x i
    have hm : ∀ y : F.Site F.depth, y ∈ sitesOfCells (finiteCells F) F.depth := hB F hodd hp
    have ht : IsAxialTreeBond (x, i) ↔ IsTreeBondOffset F.blockSide (cellOffset x) i := by
      unfold IsAxialTreeBond IsTreeBondOffset
      simp only [hc]
    unfold chordBonds innerBonds
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, hm, true_and]
    exact not_congr ht
  · intro x hx
    refine ⟨centredOffset Y (enclosingCell x), cellOffset x, fun i => ?_, (a2 x).2, fun i => ?_⟩
    · have := natAbs_centredOffset_le Y (enclosingCell x) i
      rw [Int.abs_eq_natAbs]
      omega
    · unfold fineBondAt
      rw [add_siteOfCoords_centredOffset, (a2 x).1]
  · intro x i
    rcases a4 x i with e | e
    · rw [e]
      omega
    · rw [e]
      have : cellSupDist (enclosingCell x + unitStep F.top i) Y ≤ cellSupDist (enclosingCell x) Y + 1 := by
        unfold cellSupDist
        refine Finset.sup_le fun l _ => ?_
        have h1 := Finset.le_sup (f := fun i => ((enclosingCell x i - Y i).valMinAbs).natAbs) (Finset.mem_univ l)
        have hpl := period_top F l
        have : NeZero (F.period F.top l) := ⟨by rw [hpl]; exact (hp l).ne'⟩
        have hu : (unitStep (F := F) F.top i l).valMinAbs.natAbs ≤ 1 := by
          have e2 : unitStep (F := F) F.top i l =
              (((Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod (F.period F.top l)) := rfl
          have h3 : ((Pi.single i 1 : Fin 4 → ℤ) l).natAbs ≤ 1 := by
            by_cases hl : l = i
            · subst hl
              simp
            · simp [hl]
          rw [e2, valMinAbs_intCast_of_lt _ _ (by rw [hpl]; have := hs l; omega)]
          exact h3
        have e3 : (enclosingCell x + unitStep F.top i : F.Cell) l - Y l =
            (enclosingCell x l - Y l) + unitStep F.top i l := by
          simp only [Pi.add_apply]
          ring
        show (((enclosingCell x + unitStep F.top i : F.Cell) l - Y l).valMinAbs).natAbs ≤ _
        rw [e3]
        have h4 := ZMod.natAbs_valMinAbs_add_le (enclosingCell x l - Y l) (unitStep F.top i l)
        have h5 : ((enclosingCell x l - Y l).valMinAbs + (unitStep (F := F) F.top i l).valMinAbs).natAbs ≤
            ((enclosingCell x l - Y l).valMinAbs).natAbs + (unitStep (F := F) F.top i l).valMinAbs.natAbs :=
          Int.natAbs_add_le _ _
        have h6 : ((enclosingCell x l - Y l).valMinAbs).natAbs ≤ cellSupDist (enclosingCell x) Y := h1
        omega
      exact this
  · intro y z
    unfold cellSupDist
    congr 1
    funext i
    rw [← neg_sub, ZMod.natAbs_valMinAbs_neg]
  · intro y z
    unfold cellSupDist
    refine Finset.sup_le fun l _ => ?_
    have hpl := period_top F l
    have : NeZero (F.period F.top l) := ⟨by rw [hpl]; exact (hp l).ne'⟩
    have h1 := Finset.le_sup (f := fun i => ((y i - Y i).valMinAbs).natAbs) (Finset.mem_univ l)
    have h2 := Finset.le_sup (f := fun i => ((z i - Y i).valMinAbs).natAbs) (Finset.mem_univ l)
    have e3 : y l - z l = (y l - Y l) + -(z l - Y l) := by ring
    show ((y l - z l).valMinAbs).natAbs ≤ _
    rw [e3]
    have h4 := ZMod.natAbs_valMinAbs_add_le (y l - Y l) (-(z l - Y l))
    have h5 : ((y l - Y l).valMinAbs + (-(z l - Y l)).valMinAbs).natAbs ≤
        ((y l - Y l).valMinAbs).natAbs + ((-(z l - Y l)).valMinAbs).natAbs := Int.natAbs_add_le _ _
    rw [ZMod.natAbs_valMinAbs_neg] at h5
    have h6 : ((y l - Y l).valMinAbs).natAbs ≤ _ := h1
    have h7 : ((z l - Y l).valMinAbs).natAbs ≤ _ := h2
    omega
  · intro x y
    have hLpos : 0 < F.blockSide := hodd.pos
    have key : ∀ i, ((enclosingCell y i - enclosingCell x i).valMinAbs).natAbs * F.blockSide ≤
        siteSupDist y x + F.blockSide := by
      intro i
      have hpn := period_top F i
      have hpt : F.period F.depth i = F.extent i * F.blockSide := by
        simp [BlockFrame.period, BlockFrame.top]
      have : NeZero (F.period F.top i) := ⟨by rw [hpn]; exact (hp i).ne'⟩
      have : NeZero (F.period F.depth i) := ⟨by rw [hpt]; exact (Nat.mul_pos (hp i) hLpos).ne'⟩
      obtain ⟨ey, hoy⟩ := a2 y
      obtain ⟨ex, hox⟩ := a2 x
      set oy := cellOffset y
      set ox := cellOffset x
      set u : ℤ := (y i - x i).valMinAbs with hu
      have huc : ((u : ℤ) : ZMod (F.period F.depth i)) = y i - x i := ZMod.coe_valMinAbs _
      set dd : ℤ := siteCoords (enclosingCell y) i - siteCoords (enclosingCell x) i with hdd
      have hyi : y i = (((F.blockSide : ℤ) * siteCoords (enclosingCell y) i + oy i : ℤ) :
          ZMod (F.period F.depth i)) := by
        have := congrFun ey i
        rw [← this]
        simp [cellCentre, siteOfCoords, BlockFrame.top]
      have hxi : x i = (((F.blockSide : ℤ) * siteCoords (enclosingCell x) i + ox i : ℤ) :
          ZMod (F.period F.depth i)) := by
        have := congrFun ex i
        rw [← this]
        simp [cellCentre, siteOfCoords, BlockFrame.top]
      have hz : (((u - ((F.blockSide : ℤ) * dd + (oy i - ox i)) : ℤ)) : ZMod (F.period F.depth i)) = 0 := by
        rw [Int.cast_sub, huc, hyi, hxi, hdd]
        push_cast
        ring
      obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz
      rw [hpt] at hm
      push_cast at hm
      set Q : ℤ := dd + (F.extent i : ℤ) * m with hQ
      have hLQ : u - (oy i - ox i) = (F.blockSide : ℤ) * Q := by
        rw [hQ]
        linear_combination hm
      have hQc : ((Q : ℤ) : ZMod (F.period F.top i)) = enclosingCell y i - enclosingCell x i := by
        have h1 : ((F.extent i : ℕ) : ZMod (F.period F.top i)) = 0 := by
          rw [← hpn]
          exact ZMod.natCast_self _
        rw [hQ, hdd]
        push_cast
        rw [h1]
        simp only [siteCoords, ZMod.intCast_zmod_cast, zero_mul, add_zero]
      have hv := natAbs_valMinAbs_intCast_le (F.period F.top i) Q
      rw [hQc] at hv
      have hD : u.natAbs ≤ siteSupDist y x := by
        unfold siteSupDist
        exact Finset.le_sup (f := fun i => ((y i - x i).valMinAbs).natAbs) (Finset.mem_univ i)
      obtain ⟨k, hk⟩ := hodd
      have hk' : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
      have h2 : ((F.blockSide : ℤ) - 1) / 2 = k := by rw [hk']; omega
      have hb1 := (Fintype.mem_piFinset.1 hoy) i
      have hb2' := (Fintype.mem_piFinset.1 hox) i
      rw [Finset.mem_Icc, h2] at hb1 hb2'
      have h3 : (F.blockSide : ℤ) * |Q| ≤ |u| + 2 * k := by
        have e1 : |(F.blockSide : ℤ) * Q| = (F.blockSide : ℤ) * |Q| := by rw [abs_mul, Nat.abs_cast]
        rw [← e1, ← hLQ]
        refine (abs_sub _ _).trans ?_
        have : |oy i - ox i| ≤ 2 * k := abs_le.2 ⟨by linarith [hb1.1, hb1.2, hb2'.1, hb2'.2],
          by linarith [hb1.1, hb1.2, hb2'.1, hb2'.2]⟩
        linarith
      have h4 : ((Q.natAbs * F.blockSide : ℕ) : ℤ) ≤ ((siteSupDist y x + F.blockSide : ℕ) : ℤ) := by
        push_cast
        have e3 : |u| = ((u.natAbs : ℕ) : ℤ) := (Int.natCast_natAbs u).symm
        have hD' : ((u.natAbs : ℕ) : ℤ) ≤ (siteSupDist y x : ℤ) := by exact_mod_cast hD
        rw [e3] at h3
        have e4 : |Q| * (F.blockSide : ℤ) = (F.blockSide : ℤ) * |Q| := mul_comm _ _
        linarith
      have h5 : Q.natAbs * F.blockSide ≤ siteSupDist y x + F.blockSide := by exact_mod_cast h4
      exact (Nat.mul_le_mul_right _ hv).trans h5
    have h6 : cellSupDist (enclosingCell y) (enclosingCell x) ≤ (siteSupDist y x + F.blockSide) / F.blockSide := by
      unfold cellSupDist
      exact Finset.sup_le fun i _ => (Nat.le_div_iff_mul_le hLpos).2 (key i)
    exact (Nat.mul_le_mul_left _ h6).trans (Nat.mul_div_le _ _)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
