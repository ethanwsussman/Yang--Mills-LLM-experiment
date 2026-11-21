import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.NormsOnNearCells
import YangMills.Construction.ColdChainAtEveryLevel.OneLeastFieldOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.SizesOfTheMinimalChain
import YangMills.Construction.HoleBesideASecondHole.CellsPutBack
import YangMills.Construction.HoleBesideASecondHole.ChartOfSmallCoordinates
import YangMills.Construction.HoleBesideASecondHole.CostBelowTheTotalOfCoordinates
import YangMills.Construction.HoleBesideASecondHole.CostOnWholeCellsIsTheLeastAction
import YangMills.Construction.HoleBesideASecondHole.LeastSumsOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.MeansOfSmallCoordinates
import YangMills.Construction.HoleBesideASecondHole.ReferenceReadsItsDataNearby
import YangMills.Construction.HoleBesideASecondHole.TermsOfSmallCoordinates
import YangMills.Construction.HoleBesideASecondHole.TermsReadTheirCells
import YangMills.Construction.HoleBesideASecondHole.TotalIsTheSumOfItsTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace Reinsertion
open BlockAverages LumpContours CellTerms
variable {F : BlockFrame}
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem adjointAction_mul (g h : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction (g * h) w = adjointAction g (adjointAction h w) := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_mul <;> assumption
theorem adjointAction_add (g : UnitQuaternion) (v w : ℍ[ℝ]) :
    adjointAction g (v + w) = adjointAction g v + adjointAction g w := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem adjointAction_sub (g : UnitQuaternion) (v w : ℍ[ℝ]) :
    adjointAction g (v - w) = adjointAction g v - adjointAction g w := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (c : ℝ) (w : ℍ[ℝ]) :
    adjointAction g (c • w) = c • adjointAction g w := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem re_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : (adjointAction g w).re = w.re := by apply _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_re <;> assumption
def conjImaginary (g : UnitQuaternion) (w : imaginaryQuaternions) : imaginaryQuaternions :=
  ⟨adjointAction g w, by
    have h : (w : ℍ[ℝ]).re = 0 := w.2
    show (adjointAction g w).re = 0
    rw [re_adjointAction, h]⟩
theorem coe_conjImaginary (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ((conjImaginary g w : imaginaryQuaternions) : ℍ[ℝ]) = adjointAction g w := rfl
theorem natAbs_valMinAbs_intCast_le {p : ℕ} (A : ℤ) : (ZMod.valMinAbs (A : ZMod p)).natAbs ≤ A.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem cellSupDist_comm (x y : F.Cell) : cellSupDist x y = cellSupDist y x := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_self (x : F.Cell) : cellSupDist x x = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
def FarFrom (D : Finset F.Cell) (m : ℕ) (v : F.Cell) : Prop := ∀ d ∈ D, m < cellSupDist v d
theorem FarFrom.of_dist_le {D : Finset F.Cell} {m k : ℕ} {v w : F.Cell} (h : FarFrom D (m + k) v)
    (hw : cellSupDist v w ≤ k) : FarFrom D m w := by
  intro d hd
  have h1 := h d hd
  have h2 := cellSupDist_triangle v w d
  omega
theorem FarFrom.mono {D : Finset F.Cell} {m k : ℕ} {v : F.Cell} (h : FarFrom D m v) (hk : k ≤ m) :
    FarFrom D k v :=
  fun d hd => lt_of_le_of_lt hk (h d hd)
theorem mem_of_farFrom_sdiff {S S₁ : Finset F.Cell} {v : F.Cell} {m : ℕ} (hv : v ∈ S)
    (h : FarFrom (S \ S₁) m v) : v ∈ S₁ := by
  by_contra hc
  have := h v (Finset.mem_sdiff.2 ⟨hv, hc⟩)
  rw [cellSupDist_self] at this
  omega
theorem centredCube_half {M : ℕ} (hM : Odd M) :
    0 ≤ ((M : ℤ) - 1) / 2 ∧ 2 * (((M : ℤ) - 1) / 2) + 1 = (M : ℤ) := by
  obtain ⟨k, hk⟩ := hM
  subst hk
  push_cast
  constructor <;> omega
theorem mem_centredCube_iff {M : ℕ} {h : Fin 4 → ℤ} :
    h ∈ centredCube M ↔ ∀ i, -(((M : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem exists_eq_cellCentre_add (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) (x : F.Site j) :
    ∃ h ∈ centredCube (F.blockSide ^ (F.top - j)), x = cellCentre j (enclosingCell x) + siteOfCoords j h := by
  set M : ℕ := F.blockSide ^ (F.top - j) with hMdef
  have hMo : Odd M := hodd.pow
  have hMp : 0 < (M : ℤ) := by exact_mod_cast hMo.pos
  obtain ⟨h0, h1⟩ := centredCube_half hMo
  have hMz : (F.blockSide : ℤ) ^ (F.top - j) = (M : ℤ) := by simp [hMdef]
  set k : Fin 4 → ℤ := fun i => (siteCoords x i + ((M : ℤ) - 1) / 2) / (M : ℤ) with hk
  refine ⟨fun i => siteCoords x i - (M : ℤ) * k i, ?_, ?_⟩
  · rw [mem_centredCube_iff]
    intro i
    have e := Int.emod_add_mul_ediv (siteCoords x i + ((M : ℤ) - 1) / 2) (M : ℤ)
    have m0 := Int.emod_nonneg (siteCoords x i + ((M : ℤ) - 1) / 2) hMp.ne'
    have m1 := Int.emod_lt_of_pos (siteCoords x i + ((M : ℤ) - 1) / 2) hMp
    simp only [hk]
    constructor <;> omega
  · funext i
    have hc : enclosingCell x = siteOfCoords (F := F) F.top k := by
      simp only [enclosingCell, hk, hMdef]
      try congr 1
      try funext i
      try simp
    have h2 := intCast_mul_eq_of_eq (period_eq_top_mul j hj i)
      (siteCoords_cast (F := F) (j := F.top) k i)
    have hcen : (cellCentre j (enclosingCell x) i : ZMod (F.period j i)) =
        (((M : ℤ) * k i : ℤ) : ZMod (F.period j i)) := by
      simp only [cellCentre, siteOfCoords, hMz] at h2 ⊢
      rw [hc]
      simpa [siteOfCoords, hMz] using h2
    simp only [Pi.add_apply, hcen, siteOfCoords]
    push_cast
    simp [siteCoords]
theorem enclosingCell_cellCentre_add (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) (y : F.Cell)
    {h : Fin 4 → ℤ} (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j y + siteOfCoords j h) = y := by
  set M : ℕ := F.blockSide ^ (F.top - j) with hMdef
  have hMo : Odd M := hodd.pow
  have hMp : 0 < (M : ℤ) := by exact_mod_cast hMo.pos
  obtain ⟨h0, h1⟩ := centredCube_half hMo
  have hMz : (F.blockSide : ℤ) ^ (F.top - j) = (M : ℤ) := by simp [hMdef]
  funext i
  have hb := (mem_centredCube_iff.1 hh) i
  set x : F.Site j := cellCentre j y + siteOfCoords j h with hx
  have hcast : ((siteCoords x i : ℤ) : ZMod (F.period j i)) =
      (((M : ℤ) * siteCoords y i + h i : ℤ) : ZMod (F.period j i)) := by
    simp [siteCoords, hx, cellCentre, siteOfCoords, hMz]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  obtain ⟨t, ht⟩ := hcast
  have hper : ((F.period j i : ℕ) : ℤ) = (F.period F.top i : ℕ) * (M : ℤ) := by
    rw [period_eq_top_mul j hj i, hMz]
  have hcx : siteCoords x i = (M : ℤ) * siteCoords y i + h i - (F.period F.top i : ℕ) * (M : ℤ) * t := by
    rw [hper] at ht
    linarith
  have hq : (siteCoords x i + ((M : ℤ) - 1) / 2) / (M : ℤ) = siteCoords y i - (F.period F.top i : ℕ) * t := by
    have e : siteCoords x i + ((M : ℤ) - 1) / 2 =
        (h i + ((M : ℤ) - 1) / 2) + (M : ℤ) * (siteCoords y i - (F.period F.top i : ℕ) * t) := by
      rw [hcx]; ring
    rw [e, Int.add_mul_ediv_left _ _ hMp.ne', Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]
  simp only [enclosingCell, siteOfCoords, hMdef] at hq ⊢
  rw [show (F.blockSide : ℤ) ^ (F.top - j) = ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) by simp, hq]
  simp [siteCoords]
theorem unitStep_eq_siteOfCoords_single (j : ℕ) (i : Fin 4) :
    unitStep (F := F) j i = siteOfCoords j (Pi.single i 1) := rfl
theorem enclosingCell_add_unitStep (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) (x : F.Site j) (i : Fin 4) :
    enclosingCell (x + unitStep j i) = enclosingCell x ∨
      enclosingCell (x + unitStep j i) = enclosingCell x + unitStep F.top i := by
  obtain ⟨h, hh, hx⟩ := exists_eq_cellCentre_add hodd hj x
  set M : ℕ := F.blockSide ^ (F.top - j) with hMdef
  have hMo : Odd M := hodd.pow
  obtain ⟨h0, h1⟩ := centredCube_half hMo
  have hMz : (F.blockSide : ℤ) ^ (F.top - j) = (M : ℤ) := by simp [hMdef]
  have hb := mem_centredCube_iff.1 hh
  by_cases hc : h i + 1 ≤ ((M : ℤ) - 1) / 2
  · left
    have hin : h + Pi.single i 1 ∈ centredCube M := by
      rw [mem_centredCube_iff]
      intro k
      have := hb k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, Pi.single_eq_same]
        constructor <;> omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]
        exact this
    have e : x + unitStep j i = cellCentre j (enclosingCell x) + siteOfCoords j (h + Pi.single i 1) := by
      rw [siteOfCoords_add, ← add_assoc, ← hx]
      rfl
    rw [e]
    exact enclosingCell_cellCentre_add hodd hj _ hin
  · right
    have hi : h i = ((M : ℤ) - 1) / 2 := by
      have := hb i
      omega
    have hin : h + Pi.single i 1 - (fun k => (M : ℤ) * (Pi.single i (1 : ℤ) : Fin 4 → ℤ) k) ∈ centredCube M := by
      rw [mem_centredCube_iff]
      intro k
      have := hb k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, mul_one]
        constructor <;> omega
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hk, add_zero, mul_zero, sub_zero]
        exact this
    have e : x + unitStep j i = cellCentre j (enclosingCell x + unitStep F.top i) +
        siteOfCoords j (h + Pi.single i 1 - (fun k => (M : ℤ) * (Pi.single i (1 : ℤ) : Fin 4 → ℤ) k)) := by
      rw [unitStep_eq_siteOfCoords_single F.top i, cellCentre_add j hj, hMz, siteOfCoords_sub, siteOfCoords_add]
      conv_lhs => rw [hx]
      rw [unitStep_eq_siteOfCoords_single j i]
      abel
    rw [e]
    exact enclosingCell_cellCentre_add hodd hj _ hin
theorem cellSupDist_enclosingCell_add_unitStep_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {j : ℕ}
    (hj : j ≤ F.top) (x : F.Site j) (i : Fin 4) :
    cellSupDist (enclosingCell x) (enclosingCell (x + unitStep j i)) ≤ 1 := by
  rcases enclosingCell_add_unitStep hodd hj x i with h | h
  · rw [h, cellSupDist_self]
    omega
  · rw [h, cellSupDist_comm]
    apply cellSupDist_add_le hamb (enclosingCell x) (a := Pi.single i 1) (r := 1) (by norm_num)
    intro k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
theorem enclosingCell_mem_of_mem_sitesOfCells (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top)
    {S : Finset F.Cell} {x : F.Site j} (hx : x ∈ sitesOfCells S j) : enclosingCell x ∈ S := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  rw [enclosingCell_cellCentre_add hodd hj y hh]
  exact hy
theorem mem_sitesOfCells_of_enclosingCell_mem (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top)
    {S : Finset F.Cell} {x : F.Site j} (hx : enclosingCell x ∈ S) : x ∈ sitesOfCells S j := by
  obtain ⟨h, hh, e⟩ := exists_eq_cellCentre_add hodd hj x
  exact mem_sitesOfCells.2 ⟨enclosingCell x, hx, h, hh, e⟩
theorem card_centredCube {M : ℕ} (hM : Odd M) : (centredCube M).card = M ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem card_bondsOver_singleton_le (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) (S : Finset F.Cell)
    (v : F.Cell) : (bondsOver S {v} j).card ≤ (F.blockSide ^ (F.top - j)) ^ 4 * 4 := by
  classical
  have hsub : bondsOver S {v} j ⊆
      ((centredCube (F.blockSide ^ (F.top - j))).image fun h => cellCentre j v + siteOfCoords j h) ×ˢ
        (Finset.univ : Finset (Fin 4)) := by
    intro b hb
    simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton] at hb
    obtain ⟨h, hh, e⟩ := exists_eq_cellCentre_add hodd hj b.1
    rw [Finset.mem_product]
    refine ⟨Finset.mem_image.2 ⟨h, hh, ?_⟩, Finset.mem_univ _⟩
    rw [← hb.2]
    exact e.symm
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  refine Nat.mul_le_mul_right 4 ?_
  refine Finset.card_image_le.trans (le_of_eq ?_)
  exact card_centredCube hodd.pow
theorem baseSite_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
def fineSide (F : BlockFrame) : ℕ := F.blockSide ^ F.top
theorem siteCoords_sub_cast (i : Fin 4) (w d : F.Cell) :
    (((siteCoords w i - siteCoords d i : ℤ)) : ZMod (F.period F.top i)) =
      (((w i - d i).valMinAbs : ℤ) : ZMod (F.period F.top i)) := by
  rw [ZMod.coe_valMinAbs]
  simp [siteCoords]
theorem cellCentre_add_sub_cellCentre (i : Fin 4) (w d : F.Cell) (h : Fin 4 → ℤ) :
    (cellCentre 0 w + siteOfCoords 0 h - cellCentre 0 d : F.Site 0) i =
      ((((F.blockSide : ℤ) ^ F.top) * (w i - d i).valMinAbs + h i : ℤ) : ZMod (F.period 0 i)) := by
  have h1 := intCast_mul_eq_of_eq (period_eq_top_mul (F := F) 0 (Nat.zero_le _) i) (siteCoords_sub_cast i w d)
  simp only [Nat.sub_zero] at h1
  simp only [cellCentre, siteOfCoords, Pi.add_apply, Pi.sub_apply, Nat.sub_zero]
  push_cast at h1 ⊢
  rw [← h1]
  ring
theorem supDist_cellCentre_le (hodd : Odd F.blockSide) (w d : F.Cell) {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) :
    supDist (cellCentre 0 w + siteOfCoords 0 h) (cellCentre 0 d) ≤
      fineSide F * cellSupDist w d + (fineSide F - 1) / 2 := by
  have hMo : Odd (fineSide F) := hodd.pow
  obtain ⟨h0, h1⟩ := centredCube_half hMo
  refine Finset.sup_le fun i _ => ?_
  have e := cellCentre_add_sub_cellCentre i w d h
  simp only [Pi.sub_apply] at e
  rw [e]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  have hb := (mem_centredCube_iff.1 hh) i
  have hv : ((w i - d i).valMinAbs).natAbs ≤ cellSupDist w d :=
    Finset.le_sup (f := fun i => ((w i - d i).valMinAbs).natAbs) (Finset.mem_univ i)
  have hN : ((F.blockSide : ℤ) ^ F.top) = (fineSide F : ℤ) := by simp [fineSide]
  rw [hN]
  have hn : (((fineSide F : ℤ) * (w i - d i).valMinAbs + h i).natAbs : ℤ) ≤
      (fineSide F : ℤ) * ((w i - d i).valMinAbs).natAbs + ((fineSide F : ℤ) - 1) / 2 := by
    have a1 : ((((fineSide F : ℤ) * (w i - d i).valMinAbs + h i).natAbs : ℕ) : ℤ) =
        |(fineSide F : ℤ) * (w i - d i).valMinAbs + h i| := by simp
    have a2 : (((w i - d i).valMinAbs.natAbs : ℕ) : ℤ) = |(w i - d i).valMinAbs| := by simp
    rw [a1, a2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (fineSide F : ℤ))]
    have : |h i| ≤ ((fineSide F : ℤ) - 1) / 2 := by
      rw [abs_le]
      have := hb
      simpa [fineSide] using this
    linarith
  have h3 : ((fineSide F : ℤ) - 1) / 2 = (((fineSide F - 1) / 2 : ℕ) : ℤ) := by
    have : 1 ≤ fineSide F := hMo.pos
    omega
  rw [h3] at hn
  have hn' : ((fineSide F : ℤ) * ((w i - d i).valMinAbs).natAbs + (((fineSide F - 1) / 2 : ℕ) : ℤ)) ≤
      ((fineSide F * cellSupDist w d + (fineSide F - 1) / 2 : ℕ) : ℤ) := by
    push_cast
    have := Nat.mul_le_mul_left (fineSide F) hv
    have h5 : ((fineSide F * ((w i - d i).valMinAbs).natAbs : ℕ) : ℤ) ≤
        ((fineSide F * cellSupDist w d : ℕ) : ℤ) := by
      exact_mod_cast this
    push_cast at h5
    linarith
  exact_mod_cast hn.trans hn'
theorem le_supDist_cellCentre (hodd : Odd F.blockSide) (w d : F.Cell) {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) :
    fineSide F * cellSupDist w d ≤
      supDist (cellCentre 0 w + siteOfCoords 0 h) (cellCentre 0 d) + (fineSide F - 1) / 2 := by
  have hMo : Odd (fineSide F) := hodd.pow
  obtain ⟨h0, h1⟩ := centredCube_half hMo
  have hNp : (0 : ℤ) < (fineSide F : ℤ) := by exact_mod_cast hMo.pos
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty
    (fun i => ((w i - d i).valMinAbs).natAbs)
  have hcd : cellSupDist w d = ((w i - d i).valMinAbs).natAbs := hi
  rw [hcd]
  set v : ℤ := (w i - d i).valMinAbs with hvdef
  set m : ℤ := ZMod.valMinAbs ((cellCentre 0 w + siteOfCoords 0 h - cellCentre 0 d : F.Site 0) i) with hm
  have hmle : m.natAbs ≤ supDist (cellCentre 0 w + siteOfCoords 0 h) (cellCentre 0 d) :=
    Finset.le_sup (f := fun i =>
      (((cellCentre 0 w + siteOfCoords 0 h : F.Site 0) i - (cellCentre 0 d) i).valMinAbs).natAbs)
      (Finset.mem_univ i)
  have hcast : ((m : ℤ) : ZMod (F.period 0 i)) = (((fineSide F : ℤ) * v + h i : ℤ) : ZMod (F.period 0 i)) := by
    rw [hm, ZMod.coe_valMinAbs, cellCentre_add_sub_cellCentre i w d h]
    simp [fineSide, hvdef]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  obtain ⟨t, ht⟩ := hcast
  have hper : ((F.period 0 i : ℕ) : ℤ) = (F.period F.top i : ℕ) * (fineSide F : ℤ) := by
    rw [period_eq_top_mul (F := F) 0 (Nat.zero_le _) i]
    simp [fineSide]
  rw [hper] at ht
  set v' : ℤ := v + (F.period F.top i : ℕ) * t with hv'
  have hm2 : m = (fineSide F : ℤ) * v' + h i - 2 * (F.period F.top i : ℕ) * (fineSide F : ℤ) * t := by
    rw [hv']
    linarith
  have hvle : v.natAbs ≤ (v - (F.period F.top i : ℕ) * t).natAbs := by
    have e1 : (((v - (F.period F.top i : ℕ) * t : ℤ)) : ZMod (F.period F.top i)) = w i - d i := by
      push_cast
      simp [hvdef, ZMod.coe_valMinAbs]
    have := natAbs_valMinAbs_intCast_le (p := F.period F.top i) (v - (F.period F.top i : ℕ) * t)
    rw [e1] at this
    exact this
  have hbi := (mem_centredCube_iff.1 hh) i
  have hN : (((F.blockSide ^ F.top : ℕ)) : ℤ) = (fineSide F : ℤ) := by simp [fineSide]
  rw [hN] at hbi
  have e2 : (fineSide F : ℤ) * (v - (F.period F.top i : ℕ) * t) = m - h i := by
    rw [hm2, hv']
    ring
  have hz : (fineSide F : ℤ) * |v| ≤ |m| + ((fineSide F : ℤ) - 1) / 2 := by
    have a1 : |v| ≤ |v - (F.period F.top i : ℕ) * t| := by
      have : ((v.natAbs : ℕ) : ℤ) ≤ (((v - (F.period F.top i : ℕ) * t).natAbs : ℕ) : ℤ) := by
        exact_mod_cast hvle
      simpa using this
    have a2 : (fineSide F : ℤ) * |v - (F.period F.top i : ℕ) * t| = |m - h i| := by
      rw [← e2, abs_mul, abs_of_pos hNp]
    have a3 : |m - h i| ≤ |m| + |h i| := abs_sub _ _
    have a4 : |h i| ≤ ((fineSide F : ℤ) - 1) / 2 := by
      rw [abs_le]
      exact hbi
    have a5 := mul_le_mul_of_nonneg_left a1 hNp.le
    linarith
  have h3 : ((fineSide F : ℤ) - 1) / 2 = (((fineSide F - 1) / 2 : ℕ) : ℤ) := by
    have : 1 ≤ fineSide F := hMo.pos
    omega
  rw [h3] at hz
  have f1 : ((fineSide F * v.natAbs : ℕ) : ℤ) ≤ ((m.natAbs + (fineSide F - 1) / 2 : ℕ) : ℤ) := by
    push_cast
    simpa using hz
  omega
def gapToCentres (D : Finset F.Cell) (x : F.Site 0) : ℕ :=
  sInf ((fun d => supDist x (cellCentre 0 d)) '' (D : Set F.Cell))
open Classical in
def cutoff (D : Finset F.Cell) (x : F.Site 0) : ℝ :=
  if D = ∅ then 1 else max 0 (min 1 (((gapToCentres D x : ℝ) - 201 * fineSide F) / (98 * fineSide F)))
theorem fineSide_pos (hodd : Odd F.blockSide) : 0 < fineSide F := (hodd.pow : Odd (fineSide F)).pos
theorem cutoff_nonneg (D : Finset F.Cell) (x : F.Site 0) : 0 ≤ cutoff D x := by
  unfold cutoff
  split_ifs
  · norm_num
  · exact le_max_left _ _
theorem cutoff_le_one (D : Finset F.Cell) (x : F.Site 0) : cutoff D x ≤ 1 := by
  unfold cutoff
  split_ifs
  · norm_num
  · exact max_le (by norm_num) (min_le_left _ _)
theorem cutoff_eq_zero (hodd : Odd F.blockSide) {D : Finset F.Cell} {w : F.Cell} {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) (hw : ¬ FarFrom D 200 w) :
    cutoff D (cellCentre 0 w + siteOfCoords 0 h) = 0 := by
  have hNp := fineSide_pos (F := F) hodd
  have hNr : (0 : ℝ) < (fineSide F : ℝ) := by exact_mod_cast hNp
  unfold FarFrom at hw
  push Not at hw
  obtain ⟨d, hd, hdw⟩ := hw
  have hne : D ≠ ∅ := by
    rintro rfl
    simp at hd
  have h1 : gapToCentres D (cellCentre 0 w + siteOfCoords 0 h) ≤
      supDist (cellCentre 0 w + siteOfCoords 0 h) (cellCentre 0 d) :=
    Nat.sInf_le ⟨d, hd, rfl⟩
  have h2 := supDist_cellCentre_le hodd w d hh
  have h3 : fineSide F * cellSupDist w d ≤ fineSide F * 200 := Nat.mul_le_mul_left _ hdw
  have h4 : gapToCentres D (cellCentre 0 w + siteOfCoords 0 h) ≤ 201 * fineSide F := by
    have : (fineSide F - 1) / 2 ≤ fineSide F := by omega
    omega
  have h5 : ((gapToCentres D (cellCentre 0 w + siteOfCoords 0 h) : ℕ) : ℝ) ≤ 201 * (fineSide F : ℝ) := by
    exact_mod_cast h4
  unfold cutoff
  rw [if_neg hne]
  apply max_eq_left
  refine (min_le_right _ _).trans ?_
  apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith
theorem cutoff_eq_one (hodd : Odd F.blockSide) {D : Finset F.Cell} {w : F.Cell} {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) (hw : FarFrom D 299 w) :
    cutoff D (cellCentre 0 w + siteOfCoords 0 h) = 1 := by
  have hNp := fineSide_pos (F := F) hodd
  unfold cutoff
  split_ifs with hD
  · rfl
  have hne : ((fun d => supDist (cellCentre 0 w + siteOfCoords 0 h) (cellCentre 0 d)) ''
      (D : Set F.Cell)).Nonempty := by
    obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.2 hD
    exact ⟨_, d, hd, rfl⟩
  obtain ⟨d, hd, e⟩ := Nat.sInf_mem hne
  have h1 := le_supDist_cellCentre hodd w d hh
  rw [show supDist (cellCentre 0 w + siteOfCoords 0 h) (cellCentre 0 d) =
    gapToCentres D (cellCentre 0 w + siteOfCoords 0 h) from e] at h1
  have h2 : 300 ≤ cellSupDist w d := hw d hd
  have h3 : fineSide F * 300 ≤ fineSide F * cellSupDist w d := Nat.mul_le_mul_left _ h2
  have h4 : 299 * fineSide F ≤ gapToCentres D (cellCentre 0 w + siteOfCoords 0 h) + 0 := by
    have : (fineSide F - 1) / 2 ≤ fineSide F := by omega
    omega
  have h5 : 299 * (fineSide F : ℝ) ≤ ((gapToCentres D (cellCentre 0 w + siteOfCoords 0 h) : ℕ) : ℝ) := by
    have : 299 * fineSide F ≤ gapToCentres D (cellCentre 0 w + siteOfCoords 0 h) := by omega
    exact_mod_cast this
  have h6 : (1 : ℝ) ≤ (((gapToCentres D (cellCentre 0 w + siteOfCoords 0 h) : ℕ) : ℝ) - 201 * fineSide F) /
      (98 * fineSide F) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [min_eq_left h6]
  simp
theorem supDist_add_unitStep_le (x p : F.Site 0) (i : Fin 4) :
    supDist (x + unitStep 0 i) p ≤ supDist x p + 1 := by
  refine Finset.sup_le fun k _ => ?_
  have e : (x + unitStep 0 i : F.Site 0) k - p k = (x k - p k) + (unitStep 0 i : F.Site 0) k := by
    simp only [Pi.add_apply]
    abel
  rw [e]
  refine (ZMod.natAbs_valMinAbs_add_le _ _).trans ((Int.natAbs_add_le _ _).trans (add_le_add ?_ ?_))
  · exact Finset.le_sup (f := fun k => ((x k - p k).valMinAbs).natAbs) (Finset.mem_univ k)
  · have := natAbs_valMinAbs_intCast_le (p := F.period 0 k) ((Pi.single i (1 : ℤ) : Fin 4 → ℤ) k)
    refine this.trans ?_
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
theorem supDist_le_add_unitStep (x p : F.Site 0) (i : Fin 4) :
    supDist x p ≤ supDist (x + unitStep 0 i) p + 1 := by
  refine Finset.sup_le fun k _ => ?_
  have e : x k - p k = ((x + unitStep 0 i : F.Site 0) k - p k) + (-(unitStep 0 i : F.Site 0) k) := by
    simp only [Pi.add_apply]
    abel
  rw [e]
  refine (ZMod.natAbs_valMinAbs_add_le _ _).trans ((Int.natAbs_add_le _ _).trans (add_le_add ?_ ?_))
  · exact Finset.le_sup (f := fun k => (((x + unitStep 0 i : F.Site 0) k - p k).valMinAbs).natAbs)
      (Finset.mem_univ k)
  · rw [ZMod.natAbs_valMinAbs_neg]
    have := natAbs_valMinAbs_intCast_le (p := F.period 0 k) ((Pi.single i (1 : ℤ) : Fin 4 → ℤ) k)
    refine this.trans ?_
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
theorem gapToCentres_add_unitStep_le {D : Finset F.Cell} (hD : D ≠ ∅) (x : F.Site 0) (i : Fin 4) :
    gapToCentres D (x + unitStep 0 i) ≤ gapToCentres D x + 1 := by
  have hne : ((fun d => supDist x (cellCentre 0 d)) '' (D : Set F.Cell)).Nonempty := by
    obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.2 hD
    exact ⟨_, d, hd, rfl⟩
  obtain ⟨d, hd, e⟩ := Nat.sInf_mem hne
  have h1 : gapToCentres D (x + unitStep 0 i) ≤ supDist (x + unitStep 0 i) (cellCentre 0 d) :=
    Nat.sInf_le ⟨d, hd, rfl⟩
  have h2 := supDist_add_unitStep_le x (cellCentre 0 d) i
  rw [show supDist x (cellCentre 0 d) = gapToCentres D x from e] at h2
  omega
theorem gapToCentres_le_add_unitStep {D : Finset F.Cell} (hD : D ≠ ∅) (x : F.Site 0) (i : Fin 4) :
    gapToCentres D x ≤ gapToCentres D (x + unitStep 0 i) + 1 := by
  have hne : ((fun d => supDist (x + unitStep 0 i) (cellCentre 0 d)) '' (D : Set F.Cell)).Nonempty := by
    obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.2 hD
    exact ⟨_, d, hd, rfl⟩
  obtain ⟨d, hd, e⟩ := Nat.sInf_mem hne
  have h1 : gapToCentres D x ≤ supDist x (cellCentre 0 d) := Nat.sInf_le ⟨d, hd, rfl⟩
  have h2 := supDist_le_add_unitStep x (cellCentre 0 d) i
  rw [show supDist (x + unitStep 0 i) (cellCentre 0 d) = gapToCentres D (x + unitStep 0 i) from e] at h2
  omega
theorem abs_clamp_sub_clamp_le (a b : ℝ) : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by apply _root_.YangMills.DeltaSharedProofs.p500476 <;> assumption
theorem abs_cutoff_add_unitStep_sub_le (hodd : Odd F.blockSide) (D : Finset F.Cell) (x : F.Site 0) (i : Fin 4) :
    |cutoff D (x + unitStep 0 i) - cutoff D x| ≤ 1 / (fineSide F : ℝ) := by
  have hNp := fineSide_pos (F := F) hodd
  have hNr : (0 : ℝ) < (fineSide F : ℝ) := by exact_mod_cast hNp
  unfold cutoff
  split_ifs with hD
  · simp
  refine (abs_clamp_sub_clamp_le _ _).trans ?_
  have h1 := gapToCentres_add_unitStep_le hD x i
  have h2 := gapToCentres_le_add_unitStep hD x i
  have h1' : ((gapToCentres D (x + unitStep 0 i) : ℕ) : ℝ) ≤ (gapToCentres D x : ℝ) + 1 := by exact_mod_cast h1
  have h2' : ((gapToCentres D x : ℕ) : ℝ) ≤ (gapToCentres D (x + unitStep 0 i) : ℝ) + 1 := by exact_mod_cast h2
  have e : ((gapToCentres D (x + unitStep 0 i) : ℝ) - 201 * fineSide F) / (98 * fineSide F) -
      ((gapToCentres D x : ℝ) - 201 * fineSide F) / (98 * fineSide F) =
      ((gapToCentres D (x + unitStep 0 i) : ℝ) - gapToCentres D x) / (98 * fineSide F) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 98 * fineSide F), div_le_div_iff₀ (by positivity) hNr]
  have h3 : |(gapToCentres D (x + unitStep 0 i) : ℝ) - gapToCentres D x| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith [abs_nonneg ((gapToCentres D (x + unitStep 0 i) : ℝ) - gapToCentres D x)]
theorem baseSite_mem_cell (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) (y : F.Site j) :
    ∃ h ∈ centredCube (F.blockSide ^ F.top), baseSite y = cellCentre 0 (enclosingCell y) + siteOfCoords 0 h := by
  obtain ⟨h, hh, e⟩ := exists_eq_cellCentre_add hodd hj y
  refine ⟨fun i => (F.blockSide : ℤ) ^ j * h i, ?_, ?_⟩
  · rw [mem_centredCube_iff]
    intro i
    have hb := (mem_centredCube_iff.1 hh) i
    have hLp : (1 : ℤ) ≤ (F.blockSide : ℤ) ^ j := by
      have : 1 ≤ F.blockSide ^ j := Nat.one_le_pow _ _ hodd.pos
      exact_mod_cast this
    have hM : ((F.blockSide ^ F.top : ℕ) : ℤ) = (F.blockSide : ℤ) ^ j * ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) := by
      push_cast
      rw [← pow_add]
      congr 1
      omega
    obtain ⟨a0, a1⟩ := centredCube_half (hodd.pow : Odd (F.blockSide ^ (F.top - j)))
    obtain ⟨b0, b1⟩ := centredCube_half (hodd.pow : Odd (F.blockSide ^ F.top))
    set A : ℤ := (((F.blockSide ^ (F.top - j) : ℕ) : ℤ) - 1) / 2 with hA
    set B : ℤ := (((F.blockSide ^ F.top : ℕ) : ℤ) - 1) / 2 with hB
    set P : ℤ := (F.blockSide : ℤ) ^ j with hP
    have hAB : P * A ≤ B := by
      have e1 : 2 * B + 1 = P * (2 * A + 1) := by rw [b1, a1, hM]
      nlinarith
    have h1 : P * h i ≤ P * A := mul_le_mul_of_nonneg_left hb.2 (by omega)
    have h2 : P * (-A) ≤ P * h i := mul_le_mul_of_nonneg_left hb.1 (by omega)
    constructor <;> nlinarith
  · conv_lhs => rw [e]
    rw [baseSite_add j hj, baseSite_cellCentre j hj]
def cutChart (c : F.Site 0 → ℝ) (g : F.Site 0 → UnitQuaternion) (U : ChainChart F) : ChainChart F :=
  ⟨fun x i => c (baseSite x) • conjImaginary (g (baseSite x)) (U.fine x i),
    fun j y i => c (baseSite y) • conjImaginary (g (baseSite y)) (U.coarse j y i)⟩
theorem norm_imaginary_smul (c : ℝ) (w : imaginaryQuaternions) :
    ‖((c • w : imaginaryQuaternions) : ℍ[ℝ])‖ = |c| * ‖(w : ℍ[ℝ])‖ := by
  have : ((c • w : imaginaryQuaternions) : ℍ[ℝ]) = c • (w : ℍ[ℝ]) := rfl
  rw [this, norm_smul, Real.norm_eq_abs]
theorem norm_smul_conjImaginary_le {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) (g : UnitQuaternion)
    (w : imaginaryQuaternions) :
    ‖((c • conjImaginary g w : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ‖(w : ℍ[ℝ])‖ := by
  rw [norm_imaginary_smul, coe_conjImaginary, norm_adjointAction, abs_of_nonneg h0]
  nlinarith [norm_nonneg (w : ℍ[ℝ])]
theorem linearizedCurl_gauge_cut_identity (g0 g1 g2 g3 r1 r2 r3 r4 : UnitQuaternion) (c0 c1 c2 : ℝ)
    (A B C D : ℍ[ℝ]) :
    c0 • adjointAction g0 A + adjointAction (g0 * r1 * g1⁻¹) (c1 • adjointAction g1 B) -
      adjointAction ((g0 * r1 * g1⁻¹) * (g1 * r2 * g3⁻¹) * (g2 * r3 * g3⁻¹)⁻¹) (c2 • adjointAction g2 C) -
      adjointAction ((g0 * r1 * g1⁻¹) * (g1 * r2 * g3⁻¹) * (g2 * r3 * g3⁻¹)⁻¹ * (g0 * r4 * g2⁻¹)⁻¹)
        (c0 • adjointAction g0 D) =
    adjointAction g0 (c0 • (A + adjointAction r1 B - adjointAction (r1 * r2 * r3⁻¹) C -
        adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) D) +
      (c1 - c0) • adjointAction r1 B - (c2 - c0) • adjointAction (r1 * r2 * r3⁻¹) C) := by
  have e1 : (g0 * r1 * g1⁻¹) * (g1 * r2 * g3⁻¹) * (g2 * r3 * g3⁻¹)⁻¹ * g2 = g0 * (r1 * r2 * r3⁻¹) := by group
  have e2 : (g0 * r1 * g1⁻¹) * (g1 * r2 * g3⁻¹) * (g2 * r3 * g3⁻¹)⁻¹ * (g0 * r4 * g2⁻¹)⁻¹ * g0 =
      g0 * (r1 * r2 * r3⁻¹ * r4⁻¹) := by group
  have e3 : (g0 * r1 * g1⁻¹) * g1 = g0 * r1 := by group
  have f1 : adjointAction (g0 * r1 * g1⁻¹) (c1 • adjointAction g1 B) =
      c1 • adjointAction g0 (adjointAction r1 B) := by
    rw [adjointAction_smul, ← adjointAction_mul, e3, adjointAction_mul]
  have f2 : adjointAction ((g0 * r1 * g1⁻¹) * (g1 * r2 * g3⁻¹) * (g2 * r3 * g3⁻¹)⁻¹) (c2 • adjointAction g2 C) =
      c2 • adjointAction g0 (adjointAction (r1 * r2 * r3⁻¹) C) := by
    rw [adjointAction_smul, ← adjointAction_mul, e1, adjointAction_mul]
  have f3 : adjointAction ((g0 * r1 * g1⁻¹) * (g1 * r2 * g3⁻¹) * (g2 * r3 * g3⁻¹)⁻¹ * (g0 * r4 * g2⁻¹)⁻¹)
      (c0 • adjointAction g0 D) = c0 • adjointAction g0 (adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) D) := by
    rw [adjointAction_smul, ← adjointAction_mul, e2, adjointAction_mul]
  rw [f1, f2, f3]
  simp only [adjointAction_add, adjointAction_sub, adjointAction_smul]
  module
theorem sum_comp_le_mul_sum_of_fibres {α β : Type} [DecidableEq β] (P : Finset α) (T : Finset β) (φ : α → β)
    (f : β → ℝ) (m : ℕ) (hf : ∀ b, 0 ≤ f b) (hφ : ∀ p ∈ P, φ p ∈ T)
    (hfib : ∀ b ∈ T, (P.filter fun p => φ p = b).card ≤ m) :
    ∑ p ∈ P, f (φ p) ≤ m * ∑ b ∈ T, f b := by
  rw [← Finset.sum_fiberwise_of_maps_to hφ, Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  have e : ∑ p ∈ P with φ p = b, f (φ p) = ∑ p ∈ P with φ p = b, f b :=
    Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2]
  rw [e, Finset.sum_const, nsmul_eq_mul]
  have : (((P.filter fun p => φ p = b).card : ℕ) : ℝ) ≤ m := by exact_mod_cast hfib b hb
  exact mul_le_mul_of_nonneg_right this (hf b)
theorem cutoff_baseSite_eq_zero (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {D : Finset F.Cell}
    (y : F.Site j) (h : ¬ FarFrom D 200 (enclosingCell y)) : cutoff D (baseSite y) = 0 := by
  obtain ⟨k, hk, e⟩ := baseSite_mem_cell hodd hj y
  rw [e]
  exact cutoff_eq_zero hodd hk h
theorem cutoff_baseSite_eq_one (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {D : Finset F.Cell}
    (y : F.Site j) (h : FarFrom D 299 (enclosingCell y)) : cutoff D (baseSite y) = 1 := by
  obtain ⟨k, hk, e⟩ := baseSite_mem_cell hodd hj y
  rw [e]
  exact cutoff_eq_one hodd hk h
theorem bondsOver_singleton_subset (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {j : ℕ}
    (hj : j ≤ F.top) {S S₁ : Finset F.Cell} {v : F.Cell} (hv : v ∈ S) (hf : FarFrom (S \ S₁) 199 v) :
    bondsOver S {v} j ⊆ bondsOver S₁ {v} j := by
  classical
  intro b hb
  simp only [bondsOver, innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_univ, and_true] at hb ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb
  have hv1 : v ∈ S₁ := mem_of_farFrom_sdiff hv hf
  refine ⟨⟨mem_sitesOfCells_of_enclosingCell_mem hodd hj (h3 ▸ hv1),
    mem_sitesOfCells_of_enclosingCell_mem hodd hj ?_⟩, h3⟩
  have hw := enclosingCell_mem_of_mem_sitesOfCells hodd hj h2
  have hd := cellSupDist_enclosingCell_add_unitStep_le hamb hodd hj b.1 b.2
  rw [h3] at hd
  exact mem_of_farFrom_sdiff hw (FarFrom.of_dist_le (show FarFrom (S \ S₁) (198 + 1) v from hf) hd)
theorem enclosingCell_eq_of_mem_bondsOver_singleton {S : Finset F.Cell} {v : F.Cell} {j : ℕ}
    {b : F.Site j × Fin 4} (hb : b ∈ bondsOver S {v} j) : enclosingCell b.1 = v := by
  classical
  simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton] at hb
  exact hb.2
theorem sum_pow_bondsOver_cut_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {j : ℕ}
    (hj : j ≤ F.top) {S S₁ : Finset F.Cell} {v : F.Cell} (hv : v ∈ S) (e : ℕ) (he : e ≠ 0)
    (w w₁ : F.Site j × Fin 4 → ℝ) (h0 : ∀ b, 0 ≤ w b) (h01 : ∀ b, 0 ≤ w₁ b) (hle : ∀ b, w b ≤ w₁ b)
    (hz : ∀ b, ¬ FarFrom (S \ S₁) 200 (enclosingCell b.1) → w b = 0) :
    (FarFrom (S \ S₁) 199 v ∧ ∑ b ∈ bondsOver S {v} j, w b ^ e ≤ ∑ b ∈ bondsOver S₁ {v} j, w₁ b ^ e) ∨
      ∑ b ∈ bondsOver S {v} j, w b ^ e = 0 := by
  by_cases hf : FarFrom (S \ S₁) 199 v
  · left
    refine ⟨hf, ?_⟩
    calc ∑ b ∈ bondsOver S {v} j, w b ^ e ≤ ∑ b ∈ bondsOver S {v} j, w₁ b ^ e :=
          Finset.sum_le_sum fun b _ => pow_le_pow_left₀ (h0 b) (hle b) e
      _ ≤ ∑ b ∈ bondsOver S₁ {v} j, w₁ b ^ e :=
          Finset.sum_le_sum_of_subset_of_nonneg (bondsOver_singleton_subset hamb hodd hj hv hf)
            fun b _ _ => pow_nonneg (h01 b) e
  · right
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [hz b (fun hc => hf (FarFrom.mono (by rw [← enclosingCell_eq_of_mem_bondsOver_singleton hb]; exact hc)
      (by omega))), zero_pow he]
theorem sum_bondsOver_eq_sum_cells {M : Type} [AddCommMonoid M] {S B : Finset F.Cell} {j : ℕ}
    (f : F.Site j × Fin 4 → M) :
    ∑ b ∈ bondsOver S B j, f b = ∑ v ∈ B, ∑ b ∈ bondsOver S {v} j, f b := by
  classical
  have hm : ∀ b ∈ bondsOver S B j, enclosingCell b.1 ∈ B := by
    intro b hb
    simp only [bondsOver, Finset.mem_filter] at hb
    exact hb.2
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  refine Finset.sum_congr rfl fun v hv => Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2 ▸ hv⟩, h2⟩
theorem sum_plaquettesOver_eq_sum_cells {M : Type} [AddCommMonoid M] {S B : Finset F.Cell} {j : ℕ}
    (f : F.Site j × Fin 4 × Fin 4 → M) :
    ∑ p ∈ plaquettesOver S B j, f p = ∑ v ∈ B, ∑ p ∈ plaquettesOver S {v} j, f p := by
  classical
  have hm : ∀ b ∈ plaquettesOver S B j, enclosingCell b.1 ∈ B := by
    intro b hb
    simp only [plaquettesOver, Finset.mem_filter] at hb
    exact hb.2
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  refine Finset.sum_congr rfl fun v hv => Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp only [plaquettesOver, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2 ▸ hv⟩, h2⟩
theorem card_cellBall_le (S : Finset F.Cell) (z : F.Cell) (r : ℕ) : (cellBall S z r).card ≤ (2 * r + 1) ^ 4 := by
  classical
  have hsub : cellBall S z r ⊆ (centredCube (2 * r + 1)).image fun h => z + siteOfCoords F.top h := by
    intro y hy
    simp only [BlockAverages.cellBall, Finset.mem_filter] at hy
    refine Finset.mem_image.2 ⟨fun i => ((y - z) i).valMinAbs, ?_, ?_⟩
    · rw [mem_centredCube_iff]
      intro i
      have h1 : ((z i - y i).valMinAbs).natAbs ≤ cellSupDist z y :=
        Finset.le_sup (f := fun i => ((z i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
      have h2 : (y - z) i = -(z i - y i) := by
        simp
      rw [h2]
      have h3 : ((-(z i - y i)).valMinAbs).natAbs ≤ r := by
        rw [ZMod.natAbs_valMinAbs_neg]
        exact h1.trans hy.2
      have e : (((2 * r + 1 : ℕ) : ℤ) - 1) / 2 = r := by
        push_cast
        omega
      rw [e]
      omega
    · funext i
      simp [siteOfCoords, ZMod.coe_valMinAbs]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (le_of_eq ?_))
  exact card_centredCube ⟨r, rfl⟩
theorem sum_sq_bondsOver_le (hodd : Odd F.blockSide) {S : Finset F.Cell} {v : F.Cell} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (w : F.Site 0 × Fin 4 → ℝ) (h0 : ∀ b, 0 ≤ w b) (h4 : ∑ b ∈ bondsOver S {v} 0, w b ^ 4 ≤ ρ ^ 4) :
    ∑ b ∈ bondsOver S {v} 0, w b ^ 2 ≤ 2 * (fineSide F : ℝ) ^ 2 * ρ ^ 2 := by
  have hc := card_bondsOver_singleton_le hodd (Nat.zero_le F.top) S v
  have hc' : ((bondsOver S {v} 0).card : ℝ) ≤ 4 * (fineSide F : ℝ) ^ 4 := by
    have : (bondsOver S {v} 0).card ≤ (fineSide F) ^ 4 * 4 := by simpa [fineSide] using hc
    have h2 : (((bondsOver S {v} 0).card : ℕ) : ℝ) ≤ (((fineSide F) ^ 4 * 4 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h2
    linarith
  have h1 := sq_sum_le_card_mul_sum_sq (s := bondsOver S {v} 0) (f := fun b => w b ^ 2)
  have h2 : (∑ b ∈ bondsOver S {v} 0, w b ^ 2) ^ 2 ≤ (2 * (fineSide F : ℝ) ^ 2 * ρ ^ 2) ^ 2 := by
    calc _ ≤ ((bondsOver S {v} 0).card : ℝ) * ∑ b ∈ bondsOver S {v} 0, (w b ^ 2) ^ 2 := h1
      _ = ((bondsOver S {v} 0).card : ℝ) * ∑ b ∈ bondsOver S {v} 0, w b ^ 4 := by
          congr 1
          exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ (4 * (fineSide F : ℝ) ^ 4) * ρ ^ 4 := by
          apply mul_le_mul hc' h4 (Finset.sum_nonneg fun b _ => pow_nonneg (h0 b) 4) (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (Finset.sum_nonneg fun b _ => pow_nonneg (h0 b) 2) (by positivity)).1 h2
theorem adjointAction_zero (g : UnitQuaternion) : adjointAction g 0 = 0 := by
  simp [adjointAction]
theorem plaquette_corners_mem {S : Finset F.Cell} {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) :
    p.1 ∈ sitesOfCells S 0 ∧ p.1 + unitStep 0 p.2.1 ∈ sitesOfCells S 0 ∧
      p.1 + unitStep 0 p.2.2 ∈ sitesOfCells S 0 ∧
      p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ sitesOfCells S 0 := by apply _root_.YangMills.Construction.NearCellNorms.corners_mem_sitesOfCells <;> assumption
theorem farFrom_enclosingCell_add_unitStep (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S S₁ : Finset F.Cell} {x : F.Site 0} (i : Fin 4) {m : ℕ}
    (hf : FarFrom (S \ S₁) (m + 1) (enclosingCell x)) : FarFrom (S \ S₁) m (enclosingCell (x + unitStep 0 i)) :=
  FarFrom.of_dist_le hf (cellSupDist_enclosingCell_add_unitStep_le hamb hodd (Nat.zero_le _) x i)
theorem mem_sitesOfCells_of_farFrom (hodd : Odd F.blockSide) {S S₁ : Finset F.Cell} {x : F.Site 0} {m : ℕ}
    (hx : x ∈ sitesOfCells S 0) (hf : FarFrom (S \ S₁) m (enclosingCell x)) : x ∈ sitesOfCells S₁ 0 :=
  mem_sitesOfCells_of_enclosingCell_mem hodd (Nat.zero_le _)
    (mem_of_farFrom_sdiff (enclosingCell_mem_of_mem_sitesOfCells hodd (Nat.zero_le _) hx) hf)
section Curl
variable {S S₁ : Finset F.Cell} {R₁ R' : F.GaugeField 0} {g : F.Site 0 → UnitQuaternion} {U : ChainChart F}
def GaugeRelatedFar (S S₁ : Finset F.Cell) (R₁ R' : F.GaugeField 0) (g : F.Site 0 → UnitQuaternion) : Prop :=
  ∀ (x : F.Site 0) (i : Fin 4), enclosingCell x ∈ S → FarFrom (S \ S₁) 110 (enclosingCell x) →
    enclosingCell (x + unitStep 0 i) ∈ S → FarFrom (S \ S₁) 110 (enclosingCell (x + unitStep 0 i)) →
    R' x i = g x * R₁ x i * (g (x + unitStep 0 i))⁻¹
theorem coe_cutChart_fine (c : F.Site 0 → ℝ) (y : F.Site 0) (i : Fin 4) :
    (((cutChart c g U).fine y i : imaginaryQuaternions) : ℍ[ℝ]) = c y • adjointAction (g y) (U.fine y i) := by
  simp only [cutChart, baseSite_zero]
  rfl
theorem norm_linearizedCurl_cutChart_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hR : GaugeRelatedFar S S₁ R₁ R' g) {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0)
    (hf : FarFrom (S \ S₁) 199 (enclosingCell p.1)) :
    ‖linearizedCurl R' (cutChart (cutoff (S \ S₁)) g U).fine p‖ ≤ ‖linearizedCurl R₁ U.fine p‖ +
      (1 / (fineSide F : ℝ)) * ‖(U.fine (p.1 + unitStep 0 p.2.1) p.2.2 : ℍ[ℝ])‖ +
      (1 / (fineSide F : ℝ)) * ‖(U.fine (p.1 + unitStep 0 p.2.2) p.2.1 : ℍ[ℝ])‖ := by
  obtain ⟨x, μ, ν⟩ := p
  obtain ⟨c0, c1, c2, c3⟩ := plaquette_corners_mem hp
  simp only at c0 c1 c2 c3 hf
  have z := Nat.zero_le F.top
  have f1 : FarFrom (S \ S₁) 198 (enclosingCell (x + unitStep 0 μ)) :=
    farFrom_enclosingCell_add_unitStep hamb hodd μ hf
  have f2 : FarFrom (S \ S₁) 198 (enclosingCell (x + unitStep 0 ν)) :=
    farFrom_enclosingCell_add_unitStep hamb hodd ν hf
  have f3 : FarFrom (S \ S₁) 197 (enclosingCell (x + unitStep 0 μ + unitStep 0 ν)) :=
    farFrom_enclosingCell_add_unitStep hamb hodd ν f1
  have s0 := enclosingCell_mem_of_mem_sitesOfCells hodd z c0
  have s1 := enclosingCell_mem_of_mem_sitesOfCells hodd z c1
  have s2 := enclosingCell_mem_of_mem_sitesOfCells hodd z c2
  have s3 := enclosingCell_mem_of_mem_sitesOfCells hodd z c3
  have e0 : x + unitStep 0 ν + unitStep 0 μ = x + unitStep 0 μ + unitStep 0 ν := add_right_comm _ _ _
  have r1 := hR x μ s0 (hf.mono (by omega)) s1 (f1.mono (by omega))
  have r2 := hR (x + unitStep 0 μ) ν s1 (f1.mono (by omega)) s3 (f3.mono (by omega))
  have r3 := hR (x + unitStep 0 ν) μ s2 (f2.mono (by omega)) (by rw [e0]; exact s3)
    (by rw [e0]; exact f3.mono (by omega))
  have r4 := hR x ν s0 (hf.mono (by omega)) s2 (f2.mono (by omega))
  rw [e0] at r3
  set c := cutoff (S \ S₁) with hc
  have key : linearizedCurl R' (cutChart c g U).fine (x, μ, ν) = adjointAction (g x)
      (c x • linearizedCurl R₁ U.fine (x, μ, ν) +
        (c (x + unitStep 0 μ) - c x) • adjointAction (R₁ x μ) (U.fine (x + unitStep 0 μ) ν) -
        (c (x + unitStep 0 ν) - c x) •
          adjointAction (R₁ x μ * R₁ (x + unitStep 0 μ) ν * (R₁ (x + unitStep 0 ν) μ)⁻¹)
          (U.fine (x + unitStep 0 ν) μ)) := by
    simp only [linearizedCurl, coe_cutChart_fine]
    rw [r1, r2, r3, r4]
    exact linearizedCurl_gauge_cut_identity (g x) (g (x + unitStep 0 μ)) (g (x + unitStep 0 ν))
      (g (x + unitStep 0 μ + unitStep 0 ν))
      (R₁ x μ) (R₁ (x + unitStep 0 μ) ν) (R₁ (x + unitStep 0 ν) μ) (R₁ x ν) (c x) (c (x + unitStep 0 μ))
      (c (x + unitStep 0 ν)) (U.fine x μ) (U.fine (x + unitStep 0 μ) ν) (U.fine (x + unitStep 0 ν) μ)
      (U.fine x ν)
  rw [key, norm_adjointAction]
  have t1 : ‖c x • linearizedCurl R₁ U.fine (x, μ, ν)‖ ≤ ‖linearizedCurl R₁ U.fine (x, μ, ν)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
    nlinarith [cutoff_le_one (S \ S₁) x, norm_nonneg (linearizedCurl R₁ U.fine (x, μ, ν))]
  have t2 : ‖(c (x + unitStep 0 μ) - c x) • adjointAction (R₁ x μ) (U.fine (x + unitStep 0 μ) ν)‖ ≤
      (1 / (fineSide F : ℝ)) * ‖(U.fine (x + unitStep 0 μ) ν : ℍ[ℝ])‖ := by
    rw [norm_smul, Real.norm_eq_abs, norm_adjointAction]
    exact mul_le_mul_of_nonneg_right (abs_cutoff_add_unitStep_sub_le hodd _ x μ) (norm_nonneg _)
  have t3 : ‖(c (x + unitStep 0 ν) - c x) •
      adjointAction (R₁ x μ * R₁ (x + unitStep 0 μ) ν * (R₁ (x + unitStep 0 ν) μ)⁻¹)
      (U.fine (x + unitStep 0 ν) μ)‖ ≤ (1 / (fineSide F : ℝ)) * ‖(U.fine (x + unitStep 0 ν) μ : ℍ[ℝ])‖ := by
    rw [norm_smul, Real.norm_eq_abs, norm_adjointAction]
    exact mul_le_mul_of_nonneg_right (abs_cutoff_add_unitStep_sub_le hodd _ x ν) (norm_nonneg _)
  exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)
theorem linearizedCurl_cutChart_eq_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {p : F.Site 0 × Fin 4 × Fin 4} (hf : ¬ FarFrom (S \ S₁) 199 (enclosingCell p.1)) :
    linearizedCurl R' (cutChart (cutoff (S \ S₁)) g U).fine p = 0 := by
  obtain ⟨x, μ, ν⟩ := p
  simp only at hf
  have z := Nat.zero_le F.top
  have hz : ∀ y : F.Site 0, ¬ FarFrom (S \ S₁) 200 (enclosingCell y) → ∀ i,
      (((cutChart (cutoff (S \ S₁)) g U).fine y i : imaginaryQuaternions) : ℍ[ℝ]) = 0 := by
    intro y hy i
    rw [coe_cutChart_fine, ← baseSite_zero y, cutoff_baseSite_eq_zero hodd z y hy, zero_smul]
  have h0 := hz x (fun h => hf (h.mono (by omega)))
  have h1 : ¬ FarFrom (S \ S₁) 200 (enclosingCell (x + unitStep 0 μ)) := fun h =>
    hf (FarFrom.of_dist_le (show FarFrom (S \ S₁) (199 + 1) _ from h)
      (by rw [cellSupDist_comm]; exact cellSupDist_enclosingCell_add_unitStep_le hamb hodd z x μ))
  have h2 : ¬ FarFrom (S \ S₁) 200 (enclosingCell (x + unitStep 0 ν)) := fun h =>
    hf (FarFrom.of_dist_le (show FarFrom (S \ S₁) (199 + 1) _ from h)
      (by rw [cellSupDist_comm]; exact cellSupDist_enclosingCell_add_unitStep_le hamb hodd z x ν))
  simp only [linearizedCurl, h0, hz _ h1, hz _ h2, adjointAction_zero, add_zero, sub_zero]
theorem plaquettesOver_singleton_subset (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {v : F.Cell}
    (hv : v ∈ S) (hf : FarFrom (S \ S₁) 199 v) :
    plaquettesOver S {v} 0 ⊆ plaquettesOver S₁ {v} 0 := by
  classical
  intro p hp
  simp only [plaquettesOver, Finset.mem_filter, Finset.mem_singleton] at hp ⊢
  obtain ⟨hp1, hp2⟩ := hp
  refine ⟨?_, hp2⟩
  obtain ⟨c0, c1, c2, c3⟩ := plaquette_corners_mem hp1
  rw [← hp2] at hf
  have f1 : FarFrom (S \ S₁) 198 (enclosingCell (p.1 + unitStep 0 p.2.1)) :=
    farFrom_enclosingCell_add_unitStep hamb hodd _ hf
  have f2 : FarFrom (S \ S₁) 198 (enclosingCell (p.1 + unitStep 0 p.2.2)) :=
    farFrom_enclosingCell_add_unitStep hamb hodd _ hf
  have f3 : FarFrom (S \ S₁) 197 (enclosingCell (p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2)) :=
    farFrom_enclosingCell_add_unitStep hamb hodd _ f1
  have m0 := mem_sitesOfCells_of_farFrom hodd c0 hf
  have m1 := mem_sitesOfCells_of_farFrom hodd c1 f1
  have m2 := mem_sitesOfCells_of_farFrom hodd c2 f2
  have m3 := mem_sitesOfCells_of_farFrom hodd c3 f3
  simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp1 ⊢
  refine ⟨m0, hp1.2.1, ?_⟩
  intro q hq
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact m0
  · exact m1
  · exact m2
  · exact m3
theorem sum_sq_bondsOver_cellBall_le (hodd : Odd F.blockSide) {v : F.Cell} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (w : F.Site 0 × Fin 4 → ℝ) (h0 : ∀ b, 0 ≤ w b) (h4 : ∀ y ∈ S₁, ∑ b ∈ bondsOver S₁ {y} 0, w b ^ 4 ≤ ρ ^ 4) :
    ∑ b ∈ bondsOver S₁ (cellBall S₁ v 1) 0, w b ^ 2 ≤ 162 * (fineSide F : ℝ) ^ 2 * ρ ^ 2 := by
  classical
  rw [sum_bondsOver_eq_sum_cells]
  have h1 : ∀ y ∈ cellBall S₁ v 1, ∑ b ∈ bondsOver S₁ {y} 0, w b ^ 2 ≤ 2 * (fineSide F : ℝ) ^ 2 * ρ ^ 2 := by
    intro y hy
    have hy' : y ∈ S₁ := by
      simp only [BlockAverages.cellBall, Finset.mem_filter] at hy
      exact hy.1
    exact sum_sq_bondsOver_le hodd hρ w h0 (h4 y hy')
  refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
  rw [nsmul_eq_mul]
  have hc : (((cellBall S₁ v 1).card : ℕ) : ℝ) ≤ 81 := by
    have := card_cellBall_le S₁ v 1
    have h2 : (cellBall S₁ v 1).card ≤ 81 := by simpa using this
    exact_mod_cast h2
  have hp : 0 ≤ 2 * (fineSide F : ℝ) ^ 2 * ρ ^ 2 := by positivity
  nlinarith
theorem sum_sq_linearizedCurl_cutChart_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hR : GaugeRelatedFar S S₁ R₁ R' g) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h4 : ∀ y ∈ S₁, ∑ b ∈ bondsOver S₁ {y} 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 ≤ ρ ^ 4)
    (h2 : ∀ y ∈ S₁, ∑ p ∈ plaquettesOver S₁ {y} 0, ‖linearizedCurl R₁ U.fine p‖ ^ 2 ≤ ρ ^ 2)
    {v : F.Cell} (hv : v ∈ S) :
    ∑ p ∈ plaquettesOver S {v} 0, ‖linearizedCurl R' (cutChart (cutoff (S \ S₁)) g U).fine p‖ ^ 2 ≤
      3891 * ρ ^ 2 := by
  classical
  have hNp := fineSide_pos (F := F) hodd
  by_cases hf : FarFrom (S \ S₁) 199 v
  swap
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro p hp
      simp only [plaquettesOver, Finset.mem_filter, Finset.mem_singleton] at hp
      rw [linearizedCurl_cutChart_eq_zero hamb hodd (by rw [hp.2]; exact hf)]
      simp
  have hv1 : v ∈ S₁ := mem_of_farFrom_sdiff hv hf
  set P := plaquettesOver S {v} 0 with hP
  set T := bondsOver S₁ (cellBall S₁ v 1) 0 with hT
  have hmem : ∀ p ∈ P, p ∈ innerPlaquettes S 0 ∧ enclosingCell p.1 = v := by
    intro p hp
    simpa [hP, plaquettesOver] using hp
  have hφ : ∀ (i i' : Fin 4) (x : F.Site 0), enclosingCell x = v → x + unitStep 0 i ∈ sitesOfCells S 0 →
      x + unitStep 0 i + unitStep 0 i' ∈ sitesOfCells S 0 → (x + unitStep 0 i, i') ∈ T := by
    intro i i' x hx h1 h2'
    have f0 : FarFrom (S \ S₁) 199 (enclosingCell x) := hx ▸ hf
    have f1 : FarFrom (S \ S₁) 198 (enclosingCell (x + unitStep 0 i)) :=
      farFrom_enclosingCell_add_unitStep hamb hodd _ f0
    have f2 : FarFrom (S \ S₁) 197 (enclosingCell (x + unitStep 0 i + unitStep 0 i')) :=
      farFrom_enclosingCell_add_unitStep hamb hodd _ f1
    simp only [hT, bondsOver, innerBonds, BlockAverages.cellBall, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      and_true]
    refine ⟨⟨mem_sitesOfCells_of_farFrom hodd h1 f1, mem_sitesOfCells_of_farFrom hodd h2' f2⟩,
      mem_of_farFrom_sdiff (enclosingCell_mem_of_mem_sitesOfCells hodd (Nat.zero_le _) h1) f1, ?_⟩
    rw [← hx]
    exact cellSupDist_enclosingCell_add_unitStep_le hamb hodd (Nat.zero_le _) x i
  have sB : ∑ p ∈ P, ‖(U.fine (p.1 + unitStep 0 p.2.1) p.2.2 : ℍ[ℝ])‖ ^ 2 ≤
      4 * ∑ b ∈ T, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 2 := by
    have := sum_comp_le_mul_sum_of_fibres P T (fun p => (p.1 + unitStep 0 p.2.1, p.2.2))
      (fun b => ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 2) 4 (fun b => by positivity)
      (fun p hp => by
        obtain ⟨a1, a2⟩ := hmem p hp
        obtain ⟨-, c1, -, c3⟩ := plaquette_corners_mem a1
        exact hφ _ _ _ a2 c1 c3)
      (fun b _ => by
        have : (P.filter fun p => (p.1 + unitStep 0 p.2.1, p.2.2) = b).card ≤
            (Finset.univ : Finset (Fin 4)).card := by
          refine Finset.card_le_card_of_injOn (fun p => p.2.1) (fun _ _ => Finset.mem_univ _) ?_
          intro p hp q hq hpq
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
          have e := hp.2.trans hq.2.symm
          simp only [Prod.mk.injEq] at e
          have hpq' : p.2.1 = q.2.1 := hpq
          rw [hpq'] at e
          exact Prod.ext (add_right_cancel e.1) (Prod.ext hpq' e.2)
        simpa using this)
    simpa using this
  have sC : ∑ p ∈ P, ‖(U.fine (p.1 + unitStep 0 p.2.2) p.2.1 : ℍ[ℝ])‖ ^ 2 ≤
      4 * ∑ b ∈ T, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 2 := by
    have := sum_comp_le_mul_sum_of_fibres P T (fun p => (p.1 + unitStep 0 p.2.2, p.2.1))
      (fun b => ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 2) 4 (fun b => by positivity)
      (fun p hp => by
        obtain ⟨a1, a2⟩ := hmem p hp
        obtain ⟨-, -, c2, c3⟩ := plaquette_corners_mem a1
        exact hφ _ _ _ a2 c2 (by rw [add_right_comm]; exact c3))
      (fun b _ => by
        have : (P.filter fun p => (p.1 + unitStep 0 p.2.2, p.2.1) = b).card ≤
            (Finset.univ : Finset (Fin 4)).card := by
          refine Finset.card_le_card_of_injOn (fun p => p.2.2) (fun _ _ => Finset.mem_univ _) ?_
          intro p hp q hq hpq
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
          have e := hp.2.trans hq.2.symm
          simp only [Prod.mk.injEq] at e
          have hpq' : p.2.2 = q.2.2 := hpq
          rw [hpq'] at e
          exact Prod.ext (add_right_cancel e.1) (Prod.ext e.2 hpq')
        simpa using this)
    simpa using this
  have hT2 := sum_sq_bondsOver_cellBall_le (S₁ := S₁) (v := v) hodd hρ (fun b => ‖(U.fine b.1 b.2 : ℍ[ℝ])‖)
    (fun b => norm_nonneg _) h4
  have sA : ∑ p ∈ P, ‖linearizedCurl R₁ U.fine p‖ ^ 2 ≤ ρ ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (plaquettesOver_singleton_subset hamb hodd hv hf)
      fun _ _ _ => by positivity).trans (h2 v hv1)
  have hpt : ∀ p ∈ P, ‖linearizedCurl R' (cutChart (cutoff (S \ S₁)) g U).fine p‖ ^ 2 ≤
      3 * (‖linearizedCurl R₁ U.fine p‖ ^ 2 +
        (1 / (fineSide F : ℝ)) ^ 2 * ‖(U.fine (p.1 + unitStep 0 p.2.1) p.2.2 : ℍ[ℝ])‖ ^ 2 +
        (1 / (fineSide F : ℝ)) ^ 2 * ‖(U.fine (p.1 + unitStep 0 p.2.2) p.2.1 : ℍ[ℝ])‖ ^ 2) := by
    intro p hp
    obtain ⟨a1, a2⟩ := hmem p hp
    have hb := norm_linearizedCurl_cutChart_le (U := U) hamb hodd hR a1 (by rw [a2]; exact hf)
    have n0 := norm_nonneg (linearizedCurl R' (cutChart (cutoff (S \ S₁)) g U).fine p)
    set A := ‖linearizedCurl R₁ U.fine p‖
    set B := (1 / (fineSide F : ℝ)) * ‖(U.fine (p.1 + unitStep 0 p.2.1) p.2.2 : ℍ[ℝ])‖
    set C := (1 / (fineSide F : ℝ)) * ‖(U.fine (p.1 + unitStep 0 p.2.2) p.2.1 : ℍ[ℝ])‖
    have e1 : (1 / (fineSide F : ℝ)) ^ 2 * ‖(U.fine (p.1 + unitStep 0 p.2.1) p.2.2 : ℍ[ℝ])‖ ^ 2 = B ^ 2 := by
      simp only [B]; ring
    have e2 : (1 / (fineSide F : ℝ)) ^ 2 * ‖(U.fine (p.1 + unitStep 0 p.2.2) p.2.1 : ℍ[ℝ])‖ ^ 2 = C ^ 2 := by
      simp only [C]; ring
    rw [e1, e2]
    have h5 : ‖linearizedCurl R' (cutChart (cutoff (S \ S₁)) g U).fine p‖ ^ 2 ≤ (A + B + C) ^ 2 :=
      pow_le_pow_left₀ n0 hb 2
    nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (B - C)]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hinv : (1 / (fineSide F : ℝ)) ^ 2 * (fineSide F : ℝ) ^ 2 = 1 := by
    field_simp
  have hk : 0 ≤ (1 / (fineSide F : ℝ)) ^ 2 := by positivity
  have hB2 : (1 / (fineSide F : ℝ)) ^ 2 * ∑ p ∈ P, ‖(U.fine (p.1 + unitStep 0 p.2.1) p.2.2 : ℍ[ℝ])‖ ^ 2 ≤
      648 * ρ ^ 2 := by
    calc _ ≤ (1 / (fineSide F : ℝ)) ^ 2 * (4 * (162 * (fineSide F : ℝ) ^ 2 * ρ ^ 2)) :=
          mul_le_mul_of_nonneg_left (sB.trans (by linarith)) hk
      _ = 648 * ρ ^ 2 * ((1 / (fineSide F : ℝ)) ^ 2 * (fineSide F : ℝ) ^ 2) := by ring
      _ = _ := by rw [hinv, mul_one]
  have hC2 : (1 / (fineSide F : ℝ)) ^ 2 * ∑ p ∈ P, ‖(U.fine (p.1 + unitStep 0 p.2.2) p.2.1 : ℍ[ℝ])‖ ^ 2 ≤
      648 * ρ ^ 2 := by
    calc _ ≤ (1 / (fineSide F : ℝ)) ^ 2 * (4 * (162 * (fineSide F : ℝ) ^ 2 * ρ ^ 2)) :=
          mul_le_mul_of_nonneg_left (sC.trans (by linarith)) hk
      _ = 648 * ρ ^ 2 * ((1 / (fineSide F : ℝ)) ^ 2 * (fineSide F : ℝ) ^ 2) := by ring
      _ = _ := by rw [hinv, mul_one]
  linarith
end Curl
section Norms
variable {S S₁ : Finset F.Cell} {R₁ R' : F.FieldChain} {g : F.Site 0 → UnitQuaternion} {U : ChainChart F}
  {w : F.SiteWeights}
theorem localNormSq_of_weights_eq_one (hw : ∀ j x, w j x = 1) (S B : Finset F.Cell) (R : F.FieldChain)
    (U : ChainChart F) :
    localNormSq S B R U w =
      Real.sqrt (∑ b ∈ bondsOver S B 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4) +
        ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 +
        ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 := by
  simp only [localNormSq, hw, one_mul]
  rfl
theorem parts_le_of_localNorm_le (hw : ∀ j x, w j x = 1) {v : F.Cell} (hv : v ∈ S₁) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hN : localNorm S₁ (R₁) U w v ≤ ρ) :
    ∑ b ∈ bondsOver S₁ {v} 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 ≤ ρ ^ 4 ∧
      ∑ p ∈ plaquettesOver S₁ {v} 0, ‖linearizedCurl (R₁ 0) U.fine p‖ ^ 2 ≤ ρ ^ 2 ∧
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S₁ {v} (j + 1),
        ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤ ρ ^ 2 := by
  classical
  have hbox : ({v} : Finset F.Cell) ⊆ cellBall S₁ v 3 := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    simp only [BlockAverages.cellBall, Finset.mem_filter]
    exact ⟨hv, by rw [cellSupDist_self]; omega⟩
  have sb : ∀ j, bondsOver S₁ {v} j ⊆ bondsOver S₁ (cellBall S₁ v 3) j := by
    intro j b hb
    simp only [bondsOver, Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, hbox hb.2⟩
  have sp : plaquettesOver S₁ {v} 0 ⊆ plaquettesOver S₁ (cellBall S₁ v 3) 0 := by
    intro b hb
    simp only [plaquettesOver, Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, hbox hb.2⟩
  have hq : localNormSq S₁ (cellBall S₁ v 3) R₁ U w ≤ ρ ^ 2 := (Real.sqrt_le_iff.1 hN).2
  rw [localNormSq_of_weights_eq_one hw] at hq
  set A := ∑ b ∈ bondsOver S₁ (cellBall S₁ v 3) 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 with hA
  set B := ∑ p ∈ plaquettesOver S₁ (cellBall S₁ v 3) 0, ‖linearizedCurl (R₁ 0) U.fine p‖ ^ 2 with hB
  set C := ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S₁ (cellBall S₁ v 3) (j + 1),
    ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 with hC
  have a0 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  have b0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have c0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine (Finset.sum_le_sum_of_subset_of_nonneg (sb 0) fun _ _ _ => by positivity).trans ?_
    have h1 : Real.sqrt A ≤ ρ ^ 2 := by linarith
    have h2 := (Real.sqrt_le_iff.1 h1).2
    calc A ≤ (ρ ^ 2) ^ 2 := h2
      _ = ρ ^ 4 := by ring
  · refine (Finset.sum_le_sum_of_subset_of_nonneg sp fun _ _ _ => by positivity).trans ?_
    linarith
  · refine le_trans (Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (sb (j + 1)) fun _ _ _ => by positivity) ?_
    linarith
theorem localNorm_cutChart_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hw : ∀ j x, w j x = 1)
    (hR : GaugeRelatedFar S S₁ (R₁ 0) (R' 0) g) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hN : ∀ v ∈ S₁, localNorm S₁ R₁ U w v ≤ ρ) (y : F.Cell) :
    localNorm S R' (cutChart (cutoff (S \ S₁)) (fun x => g x) U) w y ≤ 3100 * ρ := by
  classical
  set U' := cutChart (cutoff (S \ S₁)) (fun x => g x) U with hU'
  have h4 := fun v hv => (parts_le_of_localNorm_le hw hv hρ (hN v hv)).1
  have h2 := fun v hv => (parts_le_of_localNorm_le hw hv hρ (hN v hv)).2.1
  have hm := fun v hv => (parts_le_of_localNorm_le hw hv hρ (hN v hv)).2.2
  set B := cellBall S y 3 with hB
  have hBS : ∀ v ∈ B, v ∈ S := by
    intro v hv
    simp only [hB, BlockAverages.cellBall, Finset.mem_filter] at hv
    exact hv.1
  have hcard : ((B.card : ℕ) : ℝ) ≤ 2401 := by
    have := card_cellBall_le S y 3
    have h2 : B.card ≤ 2401 := by simpa using this
    exact_mod_cast h2
  have z := Nat.zero_le F.top
  have p4 : 0 ≤ ρ ^ 4 := by positivity
  have p2 : 0 ≤ ρ ^ 2 := by positivity
  have hA : ∑ b ∈ bondsOver S B 0, ‖(U'.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 ≤ 2401 * ρ ^ 4 := by
    rw [sum_bondsOver_eq_sum_cells]
    have h1 : ∀ v ∈ B, ∑ b ∈ bondsOver S {v} 0, ‖(U'.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 ≤ ρ ^ 4 := by
      intro v hv
      rcases sum_pow_bondsOver_cut_le (S₁ := S₁) hamb hodd z (hBS v hv) 4 (by norm_num)
        (fun b => ‖(U'.fine b.1 b.2 : ℍ[ℝ])‖) (fun b => ‖(U.fine b.1 b.2 : ℍ[ℝ])‖)
        (fun b => norm_nonneg _) (fun b => norm_nonneg _)
        (fun b => norm_smul_conjImaginary_le (cutoff_nonneg _ _) (cutoff_le_one _ _) _ _)
        (fun b hb => by
          simp only [hU', cutChart, cutoff_baseSite_eq_zero hodd z b.1 hb, zero_smul]
          simp) with ⟨hf, hs⟩ | hs
      · exact hs.trans (h4 v (mem_of_farFrom_sdiff (hBS v hv) hf))
      · rw [hs]
        exact p4
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [nsmul_eq_mul]
    nlinarith
  have hC : ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R' 0) U'.fine p‖ ^ 2 ≤ 2401 * (3891 * ρ ^ 2) := by
    rw [sum_plaquettesOver_eq_sum_cells]
    have h1 : ∀ v ∈ B, ∑ p ∈ plaquettesOver S {v} 0, ‖linearizedCurl (R' 0) U'.fine p‖ ^ 2 ≤ 3891 * ρ ^ 2 :=
      fun v hv => sum_sq_linearizedCurl_cutChart_le hamb hodd hR hρ h4 h2 (hBS v hv)
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [nsmul_eq_mul]
    nlinarith
  have hM : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), ‖(U'.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤
      2401 * ρ ^ 2 := by
    have e : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), ‖(U'.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 =
        ∑ v ∈ B, ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S {v} (j + 1),
          ‖(U'.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => sum_bondsOver_eq_sum_cells _
    rw [e]
    have h1 : ∀ v ∈ B, ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S {v} (j + 1),
        ‖(U'.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤ ρ ^ 2 := by
      intro v hv
      have hj : ∀ j ∈ Finset.range (F.top - 1), (v ∈ S₁ ∧ ∑ c ∈ bondsOver S {v} (j + 1),
          ‖(U'.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤
            ∑ c ∈ bondsOver S₁ {v} (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2) ∨
          ∑ c ∈ bondsOver S {v} (j + 1), ‖(U'.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 = 0 := by
        intro j hj
        have hj' : j + 1 ≤ F.top := by
          have := Finset.mem_range.1 hj
          omega
        rcases sum_pow_bondsOver_cut_le (S₁ := S₁) hamb hodd hj' (hBS v hv) 2 (by norm_num)
          (fun c => ‖(U'.coarse j c.1 c.2 : ℍ[ℝ])‖) (fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖)
          (fun c => norm_nonneg _) (fun c => norm_nonneg _)
          (fun c => norm_smul_conjImaginary_le (cutoff_nonneg _ _) (cutoff_le_one _ _) _ _)
          (fun c hc => by
            simp only [hU', cutChart, cutoff_baseSite_eq_zero hodd hj' c.1 hc, zero_smul]
            simp) with ⟨hf, hs⟩ | hs
        · exact Or.inl ⟨mem_of_farFrom_sdiff (hBS v hv) hf, hs⟩
        · exact Or.inr hs
      by_cases hv1 : v ∈ S₁
      · refine le_trans (Finset.sum_le_sum fun j hj' => ?_) (hm v hv1)
        rcases hj j hj' with ⟨-, hs⟩ | hs
        · exact hs
        · rw [hs]
          exact Finset.sum_nonneg fun _ _ => by positivity
      · rw [Finset.sum_eq_zero]
        · exact p2
        · intro j hj'
          rcases hj j hj' with ⟨h, -⟩ | hs
          · exact absurd h hv1
          · exact hs
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [nsmul_eq_mul]
    nlinarith
  have hS : Real.sqrt (∑ b ∈ bondsOver S B 0, ‖(U'.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4) ≤ 49 * ρ ^ 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, hA.trans (le_of_eq ?_)⟩
    ring
  have hfin : localNormSq S B R' U' w ≤ (3100 * ρ) ^ 2 := by
    rw [localNormSq_of_weights_eq_one hw]
    nlinarith
  exact Real.sqrt_le_iff.2 ⟨by positivity, hfin⟩
end Norms
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathDisplacement_replicate (j n : ℕ) (st : PathStep) :
    pathDisplacement (F := F) j (List.replicate n st) = n • stepDisplacement j st := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate <;> assumption
theorem siteOfCoords_eq_sum (j : ℕ) (h : Fin 4 → ℤ) :
    siteOfCoords (F := F) j h = ∑ i, h i • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_eq_sum <;> assumption
theorem pathDisplacement_replicate_axis (j : ℕ) (c : ℤ) (i : Fin 4) :
    pathDisplacement (F := F) j (List.replicate c.natAbs (i, decide (0 ≤ c))) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate_axis <;> assumption
theorem pathDisplacement_axisPath (j : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
def WithinHalfSide (L : ℕ) (o : Fin 4 → ℤ) : Prop := ∀ m, |o m| ≤ ((L : ℤ) - 1) / 2
theorem siteOfCoords_smul_single (j : ℕ) (c : ℤ) (i : Fin 4) :
    siteOfCoords (F := F) j (c • Pi.single i 1) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_single <;> assumption
theorem refineSite_add_mem_sitesBelow (j : ℕ) (y : F.Site (j + 1)) {o : Fin 4 → ℤ}
    (ho : WithinHalfSide F.blockSide o) : refineSite y + siteOfCoords j o ∈ sitesBelow j y := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.refineSite_add_mem_sitesBelow <;> assumption
theorem add_smul_single_apply (o : Fin 4 → ℤ) (c : ℤ) (i m : Fin 4) :
    (o + c • (Pi.single i 1 : Fin 4 → ℤ)) m = o m + if m = i then c else 0 := by apply _root_.YangMills.Construction.GaugeFixing.add_smul_single_apply <;> assumption
def partialOffset (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : ℕ) : Fin 4 → ℤ :=
  fun m => if ((π.symm m : Fin 4) : ℕ) < k then h m else 0
theorem partialOffset_zero (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) : partialOffset h π 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.partialOffset_zero <;> assumption
theorem partialOffset_succ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    partialOffset h π ((k : ℕ) + 1) = partialOffset h π k + h (π k) • Pi.single (π k) 1 := by apply _root_.YangMills.Construction.GaugeFixing.partialOffset_succ <;> assumption
theorem withinHalfSide_partialOffset_add (L : ℕ) (h : Fin 4 → ℤ) (hh : WithinHalfSide L h)
    (π : Equiv.Perm (Fin 4)) (k : Fin 4) (r : ℕ) (hr : r ≤ (h (π k)).natAbs) :
    WithinHalfSide L (partialOffset h π k +
      (if decide (0 ≤ h (π k)) then (r : ℤ) else -(r : ℤ)) • Pi.single (π k) 1) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.axisPathOffset_flow_withinBlock <;> assumption
theorem axisPath_eq_append (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π =
      List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0))) ++
      (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1))) ++
      (List.replicate (h (π 2)).natAbs (π 2, decide (0 ≤ h (π 2))) ++
      (List.replicate (h (π 3)).natAbs (π 3, decide (0 ≤ h (π 3))) ++ []))) := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_eq_append <;> assumption
def axisPiece (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) : List PathStep :=
  List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))
theorem add_partialOffset_add_axisPiece (j : ℕ) (x : F.Site j) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4))
    (k : Fin 4) :
    x + siteOfCoords j (partialOffset h π k) + pathDisplacement j (axisPiece h π k) =
      x + siteOfCoords j (partialOffset h π ((k : ℕ) + 1)) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.add_axisPathFlow <;> assumption
def PathWithin {j : ℕ} (Z : Finset (F.Site j)) : F.Site j → List PathStep → Prop
  | _, [] => True
  | x, st :: r => x ∈ Z ∧ x + stepDisplacement j st ∈ Z ∧ PathWithin Z (x + stepDisplacement j st) r
theorem PathWithin.append {j : ℕ} (Z : Finset (F.Site j)) (l l' : List PathStep) :
    ∀ x, PathWithin Z x l → PathWithin Z (x + pathDisplacement j l) l' → PathWithin Z x (l ++ l') := by
  induction l with
  | nil =>
    intro x _ h
    simpa [pathDisplacement] using h
  | cons st r ih =>
    intro x h h'
    refine ⟨h.1, h.2.1, ih _ h.2.2 ?_⟩
    have e : x + stepDisplacement j st + pathDisplacement j r = x + pathDisplacement j (st :: r) := by
      simp [pathDisplacement, add_assoc]
    rw [e]
    exact h'
theorem PathWithin.replicate {j : ℕ} (Z : Finset (F.Site j)) (st : PathStep) (n : ℕ) :
    ∀ x, (∀ r ≤ n, x + r • stepDisplacement j st ∈ Z) → PathWithin Z x (List.replicate n st) := by
  induction n with
  | zero => intro x _; trivial
  | succ n ih =>
    intro x h
    refine ⟨by simpa using h 0 (Nat.zero_le _), by simpa using h 1 (by omega), ih _ fun r hr => ?_⟩
    have := h (r + 1) (by omega)
    rw [add_smul, one_smul, add_comm (r • _), ← add_assoc] at this
    exact this
theorem pathHolonomy_congr {j : ℕ} (Z : Finset (F.Site j)) (X X' : F.GaugeField j)
    (hX : ∀ x i, x ∈ Z → x + unitStep j i ∈ Z → X x i = X' x i) (l : List PathStep) :
    ∀ x, PathWithin Z x l → pathHolonomy X x l = pathHolonomy X' x l := by
  induction l with
  | nil => intro x _; rfl
  | cons st r ih =>
    intro x h
    simp only [pathHolonomy]
    rw [ih _ h.2.2]
    congr 1
    obtain ⟨d, b⟩ := st
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      have h1 := h.1
      have h2 := h.2.1
      simp only [stepDisplacement, Bool.false_eq_true, if_false] at h2
      rw [hX (x - unitStep j d) d (by simpa [sub_eq_add_neg] using h2) (by simpa using h1)]
    · simp only [linkValue, if_true]
      have h2 := h.2.1
      simp only [stepDisplacement, if_true] at h2
      rw [hX x d h.1 h2]
theorem axisPath_within_sitesBelow (j : ℕ) (hL : Odd F.blockSide) (y : F.Site (j + 1)) (h : Fin 4 → ℤ)
    (hh : WithinHalfSide F.blockSide h) (π : Equiv.Perm (Fin 4)) :
    PathWithin (sitesBelow j y) (refineSite y) (axisPath h π) := by
  have piece : ∀ k : Fin 4, PathWithin (sitesBelow j y) (refineSite y + siteOfCoords j (partialOffset h π k))
      (axisPiece h π k) := by
    intro k
    refine PathWithin.replicate _ _ _ _ fun r hr => ?_
    have h1 := withinHalfSide_partialOffset_add F.blockSide h hh π k r hr
    have e : refineSite y + siteOfCoords j (partialOffset h π k) +
        r • stepDisplacement j (π k, decide (0 ≤ h (π k))) =
        refineSite y + siteOfCoords j (partialOffset h π k +
          (if decide (0 ≤ h (π k)) then (r : ℤ) else -(r : ℤ)) • Pi.single (π k) 1) := by
      rw [siteOfCoords_add, siteOfCoords_smul_single, add_assoc]
      by_cases hc : 0 ≤ h (π k)
      · simp [stepDisplacement, hc]
      · simp [stepDisplacement, hc]
    rw [e]
    exact refineSite_add_mem_sitesBelow j y h1
  rw [axisPath_eq_append]
  have s0 := add_partialOffset_add_axisPiece j (refineSite y) h π 0
  have s1 := add_partialOffset_add_axisPiece j (refineSite y) h π 1
  have s2 := add_partialOffset_add_axisPiece j (refineSite y) h π 2
  have z0 : refineSite y + siteOfCoords j (partialOffset h π ((0 : Fin 4) : ℕ)) = refineSite y := by
    simp [partialOffset_zero, siteOfCoords_zero]
  have p0 := piece 0
  have p1 := piece 1
  have p2 := piece 2
  have p3 := piece 3
  rw [z0] at p0 s0
  refine PathWithin.append _ _ _ _ p0 ?_
  have e01 : refineSite y + pathDisplacement j (axisPiece h π 0) =
      refineSite y + siteOfCoords j (partialOffset h π ((1 : Fin 4) : ℕ)) := s0
  simp only [axisPiece] at e01
  rw [e01]
  refine PathWithin.append _ _ _ _ p1 ?_
  have e12 : refineSite y + siteOfCoords j (partialOffset h π ((1 : Fin 4) : ℕ)) +
      pathDisplacement j (axisPiece h π 1) =
      refineSite y + siteOfCoords j (partialOffset h π ((2 : Fin 4) : ℕ)) := s1
  simp only [axisPiece] at e12
  rw [e12]
  refine PathWithin.append _ _ _ _ p2 ?_
  have e23 : refineSite y + siteOfCoords j (partialOffset h π ((2 : Fin 4) : ℕ)) +
      pathDisplacement j (axisPiece h π 2) =
      refineSite y + siteOfCoords j (partialOffset h π ((3 : Fin 4) : ℕ)) := s2
  simp only [axisPiece] at e23
  rw [e23]
  refine PathWithin.append _ _ _ _ p3 ?_
  trivial
theorem PathWithin.mono {j : ℕ} {Z Z' : Finset (F.Site j)} (hz : Z ⊆ Z') (l : List PathStep) :
    ∀ x, PathWithin Z x l → PathWithin Z' x l := by
  induction l with
  | nil => intro x _; trivial
  | cons st r ih => intro x h; exact ⟨hz h.1, hz h.2.1, ih _ h.2.2⟩
theorem linkValue_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (x : F.Site j)
    (st : PathStep) :
    linkValue (gaugeTransform γ X) x st = γ x * linkValue X x st * (γ (x + stepDisplacement j st))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_gaugeTransform <;> assumption
theorem pathHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy (gaugeTransform γ X) x l =
      γ x * pathHolonomy X x l * (γ (x + pathDisplacement j l))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_gaugeTransform <;> assumption
theorem cellOffset_spec (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (x : F.Site F.depth) :
    WithinHalfSide F.blockSide (cellOffset x) ∧
      cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x) = x := by
  obtain ⟨h, hh, e⟩ := exists_eq_cellCentre_add hodd (Nat.le_succ F.depth) x
  have hn : F.top - F.depth = 1 := by simp [BlockFrame.top]
  rw [hn, pow_one] at hh
  have hb := mem_centredCube_iff.1 hh
  have hL : 0 < F.blockSide := hodd.pos
  have hof : cellOffset x = h := by
    funext i
    have e1 : (x - cellCentre F.depth (enclosingCell x)) i = ((h i : ℤ) : ZMod (F.period F.depth i)) := by
      rw [sub_eq_of_eq_add' e]
      rfl
    simp only [cellOffset, e1]
    apply valMinAbs_intCast_of_small
    rcases hamb with h0 | h0
    · left
      simp [BlockFrame.period, h0 i]
    · right
      have hp : ((F.period F.depth i : ℕ) : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) := by
        simp [BlockFrame.period, hn]
      have hs : (64 : ℤ) ≤ F.extent i := by exact_mod_cast h0 i
      have hi := hb i
      have habs : 2 * |h i| ≤ (F.blockSide : ℤ) - 1 := by
        obtain ⟨k, hk⟩ := hodd
        have hk' : ((F.blockSide : ℤ) - 1) / 2 = k := by
          rw [hk]
          push_cast
          omega
        rw [hk'] at hi
        have hz : (F.blockSide : ℤ) - 1 = 2 * k := by
          rw [hk]
          push_cast
          ring
        rw [hz]
        have : |h i| ≤ k := abs_le.2 hi
        omega
      rw [hp]
      nlinarith
  rw [hof]
  refine ⟨fun m => abs_le.2 (hb m), e.symm⟩
theorem refineSite_eq_cellCentre (y : F.Cell) : refineSite y = cellCentre F.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
theorem sitesBelow_subset_sitesOfCells (hodd : Odd F.blockSide) {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S) :
    sitesBelow F.depth y ⊆ sitesOfCells S F.depth := by
  intro q hq
  have hn : F.top - F.depth = 1 := by simp [BlockFrame.top]
  simp only [sitesBelow] at hq
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hq
  refine mem_sitesOfCells.2 ⟨y, hy, h, ?_, ?_⟩
  · have e : F.top = F.depth + 1 := rfl
    rw [hn]
    simpa [e] using hh
  · funext i
    simp [cellCentre, siteOfCoords, hn]
theorem axialGauge_of_gaugeTransform (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S₁ : Finset F.Cell} {W X : F.GaugeField F.depth} {γ : F.Site F.depth → UnitQuaternion}
    (hW : AgreeOnBonds S₁ F.depth W (gaugeTransform γ X)) {x : F.Site F.depth} (hx : enclosingCell x ∈ S₁)
    (hc : γ (cellCentre F.depth (enclosingCell x)) = 1) (π : Equiv.Perm (Fin 4)) :
    axialGauge π W x = axialGauge π X x * (γ x)⁻¹ := by
  obtain ⟨hin, he⟩ := cellOffset_spec hamb hodd x
  have hp := axisPath_within_sitesBelow F.depth hodd (enclosingCell x) (cellOffset x) hin π
  rw [refineSite_eq_cellCentre] at hp
  have hp' := PathWithin.mono (sitesBelow_subset_sitesOfCells hodd hx) _ _ hp
  have hcongr : ∀ (y : F.Site F.depth) (i : Fin 4), y ∈ sitesOfCells S₁ F.depth →
      y + unitStep F.depth i ∈ sitesOfCells S₁ F.depth → W y i = gaugeTransform γ X y i := by
    intro y i h1 h2
    refine hW (y, i) ?_
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨h1, h2⟩
  unfold axialGauge
  rw [pathHolonomy_congr (sitesOfCells S₁ F.depth) W (gaugeTransform γ X) hcongr _ _ hp',
    pathHolonomy_gaugeTransform, hc, pathDisplacement_axisPath, he, one_mul]
theorem bondCoordinate_of_gaugeTransform (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S₁ : Finset F.Cell} {W X : F.GaugeField F.depth} {γ : F.Site F.depth → UnitQuaternion}
    (hW : AgreeOnBonds S₁ F.depth W (gaugeTransform γ X)) (hc : ∀ z, γ (cellCentre F.depth z) = 1)
    (π : Equiv.Perm (Fin 4)) (V : F.GaugeField F.top) {b : F.Site F.depth × Fin 4}
    (hb : b ∈ innerBonds S₁ F.depth) :
    bondCoordinate π V W b = bondCoordinate π V X b := by
  have z := Nat.le_succ F.depth
  have hb' := hb
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hb'
  have e : gaugeTransform (axialGauge π W) W b.1 b.2 = gaugeTransform (axialGauge π X) X b.1 b.2 := by
    have h1 := axialGauge_of_gaugeTransform hamb hodd hW (enclosingCell_mem_of_mem_sitesOfCells hodd z hb'.1)
      (hc _) π
    have h2 := axialGauge_of_gaugeTransform hamb hodd hW (enclosingCell_mem_of_mem_sitesOfCells hodd z hb'.2)
      (hc _) π
    simp only [gaugeTransform]
    rw [h1, h2, hW b hb]
    simp only [gaugeTransform]
    group
  simp only [bondCoordinate, e]
theorem bondCoordinate_eq_of_minimizers (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {a ρ N0 s : ℝ} {S₁ : Finset F.Cell} {V : F.GaugeField F.top} (h : HasColdMinimizer a ρ N0 s S₁ V)
    {W W' : F.GaugeField F.depth}
    (hW : ∀ W'', blockEnergy a S₁ F.depth W V ≤ blockEnergy a S₁ F.depth W'' V)
    (hW' : ∀ W'', blockEnergy a S₁ F.depth W' V ≤ blockEnergy a S₁ F.depth W'' V) (π : Equiv.Perm (Fin 4))
    {b : F.Site F.depth × Fin 4} (hb : b ∈ innerBonds S₁ F.depth) :
    bondCoordinate π V W b = bondCoordinate π V W' b := by
  obtain ⟨w, -, -, hu⟩ := h
  obtain ⟨γ, hγ, hs⟩ := hu W hW
  obtain ⟨γ', hγ', hs'⟩ := hu W' hW'
  rw [bondCoordinate_of_gaugeTransform hamb hodd hs hγ π V hb,
    bondCoordinate_of_gaugeTransform hamb hodd hs' hγ' π V hb]
section Small
theorem sum_exp_neg_abs_le {c : ℝ} (hc : 0 < c) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) M, Real.exp (-c * |(k : ℝ)|) ≤ 2 / (1 - Real.exp (-c)) := by
  classical
  set q := Real.exp (-c) with hq
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have h1 : ∀ k : ℤ, Real.exp (-c * |(k : ℝ)|) = q ^ k.natAbs := by
    intro k
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    have : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
      rw [Nat.cast_natAbs]
      simp
    rw [this]
    ring
  simp only [h1]
  have h2 := sum_comp_le_mul_sum_of_fibres (Finset.Icc (-(M : ℤ)) M) (Finset.range (M + 1)) Int.natAbs
    (fun m => q ^ m) 2
    (fun m => by positivity)
    (fun k hk => by
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_range]
      omega)
    (fun m _ => by
      have hsub : ((Finset.Icc (-(M : ℤ)) M).filter fun k => k.natAbs = m) ⊆ {(m : ℤ), -(m : ℤ)} := by
        intro k hk
        rw [Finset.mem_filter] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hsub).trans Finset.card_le_two)
  refine h2.trans ?_
  have h3 := mul_neg_geom_sum q (M + 1)
  have h4 : 0 < 1 - q := by linarith
  have h5 : ∑ i ∈ Finset.range (M + 1), q ^ i ≤ 1 / (1 - q) := by
    rw [le_div_iff₀ h4, mul_comm, h3]
    have : 0 ≤ q ^ (M + 1) := by positivity
    linarith
  calc ((2 : ℕ) : ℝ) * ∑ i ∈ Finset.range (M + 1), q ^ i ≤ 2 * (1 / (1 - q)) := by
        push_cast
        linarith
    _ = 2 / (1 - q) := by ring
def expCellCount (del : ℝ) : ℝ := (2 / (1 - Real.exp (-(del / 2)))) ^ 4
theorem expCellCount_pos {del : ℝ} (h : 0 < del) : 0 < expCellCount del := by
  have : Real.exp (-(del / 2)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  unfold expCellCount
  positivity
theorem sum_exp_cellSupDist_le {del : ℝ} (hdel : 0 < del) (S : Finset F.Cell) (y0 : F.Cell) :
    ∑ z ∈ S, Real.exp (-(2 * del) * (cellSupDist z y0 : ℝ)) ≤ expCellCount del := by
  classical
  set o : F.Cell → (Fin 4 → ℤ) := fun z i => ((z i - y0 i).valMinAbs) with ho
  have hinj : Set.InjOn o (S : Set F.Cell) := by
    intro z _ z' _ h
    funext i
    have h1 := congrFun h i
    simp only [ho] at h1
    have h2 := congrArg (fun k : ℤ => (k : ZMod (F.period F.top i))) h1
    simp only [ZMod.coe_valMinAbs] at h2
    exact sub_left_injective h2
  set c := del / 2 with hc
  have hc0 : 0 < c := by positivity
  set M : ℕ := S.sup fun z => cellSupDist z y0 with hM
  have hdist : ∀ z ∈ S, ∀ i, |o z i| ≤ (cellSupDist z y0 : ℤ) := by
    intro z _ i
    have : ((z i - y0 i).valMinAbs).natAbs ≤ cellSupDist z y0 :=
      Finset.le_sup (f := fun i => ((z i - y0 i).valMinAbs).natAbs) (Finset.mem_univ i)
    simp only [ho]
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this
  have hbound : ∀ z ∈ S, Real.exp (-(2 * del) * (cellSupDist z y0 : ℝ)) ≤
      ∏ i, Real.exp (-c * |((o z i : ℤ) : ℝ)|) := by
    intro z hz
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    rw [← Finset.mul_sum]
    have h1 : ∑ i, |((o z i : ℤ) : ℝ)| ≤ 4 * (cellSupDist z y0 : ℝ) := by
      have : ∀ i ∈ (Finset.univ : Finset (Fin 4)), |((o z i : ℤ) : ℝ)| ≤ (cellSupDist z y0 : ℝ) := by
        intro i _
        have := hdist z hz i
        have h2 : ((|o z i| : ℤ) : ℝ) ≤ ((cellSupDist z y0 : ℤ) : ℝ) := by exact_mod_cast this
        simpa using h2
      refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
      simp
    rw [hc]
    nlinarith
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [← Finset.sum_image (f := fun v : Fin 4 → ℤ => ∏ i, Real.exp (-c * |((v i : ℤ) : ℝ)|)) hinj]
  have hsub : S.image o ⊆ Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(M : ℤ)) M := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
    rw [Fintype.mem_piFinset]
    intro i
    have h1 := hdist z hz i
    have h2 : cellSupDist z y0 ≤ M := Finset.le_sup (f := fun z => cellSupDist z y0) hz
    have h3 : (cellSupDist z y0 : ℤ) ≤ M := by exact_mod_cast h2
    rw [Finset.mem_Icc]
    have := abs_le.1 (h1.trans h3)
    exact this
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
    Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le).trans ?_
  have e := Finset.prod_univ_sum (fun _ : Fin 4 => Finset.Icc (-(M : ℤ)) M)
    (fun _ k => Real.exp (-c * |(k : ℝ)|))
  refine (le_of_eq e.symm).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold expCellCount
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) (sum_exp_neg_abs_le hc0 M) 4
theorem localNormSq_nonneg (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    0 ≤ localNormSq S B R U w := by apply _root_.YangMills.Construction.CoordinateSeminorms.localNormSq_nonneg <;> assumption
theorem localNormSq_le_of_weights_le {S B : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F}
    {w : F.SiteWeights} {E : ℝ} (hE : 0 ≤ E) (h0 : ∀ j x, 0 ≤ w j x)
    (hw : ∀ (j : ℕ) (x : F.Site j), enclosingCell x ∈ B → w j x ≤ E) :
    localNormSq S B R U w ≤ E ^ 2 * localNormSq S B R U (fun _ _ => 1) := by
  classical
  have memb : ∀ {j : ℕ} {b : F.Site j × Fin 4}, b ∈ bondsOver S B j → enclosingCell b.1 ∈ B := by
    intro j b hb
    simp only [bondsOver, Finset.mem_filter] at hb
    exact hb.2
  have memp : ∀ {p : F.Site 0 × Fin 4 × Fin 4}, p ∈ plaquettesOver S B 0 → enclosingCell p.1 ∈ B := by
    intro p hp
    simp only [plaquettesOver, Finset.mem_filter] at hp
    exact hp.2
  unfold localNormSq
  simp only [one_mul]
  have a1 : ∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤
      (E ^ 2) ^ 2 * ∑ b ∈ bondsOver S B 0, ‖U.fine b.1 b.2‖ ^ 4 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    have h1 := hw 0 b.1 (memb hb)
    have h2 := h0 0 b.1
    calc (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤ (E * ‖U.fine b.1 b.2‖) ^ 4 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) 4
      _ = _ := by ring
  have a2 : Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) ≤
      E ^ 2 * Real.sqrt (∑ b ∈ bondsOver S B 0, ‖U.fine b.1 b.2‖ ^ 4) := by
    refine (Real.sqrt_le_sqrt a1).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have b1 : ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 ≤
      E ^ 2 * ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have h1 := hw 0 p.1 (memp hp)
    have h2 := h0 0 p.1
    calc (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 ≤ (E * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) 2
      _ = _ := by ring
  have c1 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤
      E ^ 2 * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), ‖U.coarse j c.1 c.2‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have h1 := hw (j + 1) c.1 (memb hc)
    have h2 := h0 (j + 1) c.1
    calc (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤ (E * ‖U.coarse j c.1 c.2‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) 2
      _ = _ := by ring
  nlinarith
theorem supWeightedNorm_le {del : ℝ} (hdel : 0 < del) {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F}
    {B : ℝ} (hB : 0 ≤ B) (hN : ∀ z ∈ S, localNorm S R U (fun _ _ => 1) z ≤ B) :
    supWeightedNorm S del R U ≤ Real.sqrt (Real.exp (6 * del) * expCellCount del) * B := by
  classical
  unfold supWeightedNorm
  refine Real.iSup_le (fun y0 => ?_) (by positivity)
  set w := decayWeights F del 0 0 y0 with hw
  have hw1 : ∀ (j : ℕ) (x : F.Site j), w j x = Real.exp (-del * cellSupDist (enclosingCell x) y0) := by
    intro j x
    simp [hw, decayWeights]
  have hz : ∀ z ∈ S, localNorm S R U w z ^ 2 ≤
      (Real.exp (6 * del) * B ^ 2) * Real.exp (-(2 * del) * (cellSupDist z y0 : ℝ)) := by
    intro z hz
    set E := Real.exp (-del * ((cellSupDist z y0 : ℝ) - 3)) with hE
    have h1 : localNormSq S (cellBall S z 3) R U w ≤ E ^ 2 * localNormSq S (cellBall S z 3) R U (fun _ _ => 1) := by
      refine localNormSq_le_of_weights_le (Real.exp_pos _).le (fun j x => ?_) (fun j x hx => ?_)
      · rw [hw1]
        exact (Real.exp_pos _).le
      · rw [hw1]
        apply Real.exp_le_exp.2
        simp only [BlockAverages.cellBall, Finset.mem_filter] at hx
        have h2 := cellSupDist_triangle z (enclosingCell x) y0
        have h3 : (cellSupDist z y0 : ℝ) ≤ 3 + cellSupDist (enclosingCell x) y0 := by
          have : cellSupDist z y0 ≤ 3 + cellSupDist (enclosingCell x) y0 := by omega
          exact_mod_cast this
        nlinarith
    have h2 : localNormSq S (cellBall S z 3) R U (fun _ _ => 1) ≤ B ^ 2 := (Real.sqrt_le_iff.1 (hN z hz)).2
    have h3 : localNorm S R U w z ^ 2 = localNormSq S (cellBall S z 3) R U w := by
      unfold localNorm
      exact Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)
    rw [h3]
    refine h1.trans ?_
    have h4 : E ^ 2 = Real.exp (6 * del) * Real.exp (-(2 * del) * (cellSupDist z y0 : ℝ)) := by
      rw [hE, sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [h4]
    have h5 : 0 ≤ Real.exp (6 * del) * Real.exp (-(2 * del) * (cellSupDist z y0 : ℝ)) := by positivity
    calc _ ≤ Real.exp (6 * del) * Real.exp (-(2 * del) * (cellSupDist z y0 : ℝ)) * B ^ 2 :=
          mul_le_mul_of_nonneg_left h2 h5
      _ = _ := by ring
  have hsum : ∑ z ∈ S, localNorm S R U w z ^ 2 ≤ (Real.exp (6 * del) * expCellCount del) * B ^ 2 := by
    refine (Finset.sum_le_sum hz).trans ?_
    rw [← Finset.mul_sum]
    have h6 := sum_exp_cellSupDist_le hdel S y0
    have h7 : 0 ≤ Real.exp (6 * del) * B ^ 2 := by positivity
    calc _ ≤ Real.exp (6 * del) * B ^ 2 * expCellCount del := mul_le_mul_of_nonneg_left h6 h7
      _ = _ := by ring
  unfold weightedNorm
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, hsum.trans (le_of_eq ?_)⟩
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (Real.exp_pos _).le (expCellCount_pos hdel).le)]
end Small
open Classical in
def farCells (S S₁ : Finset F.Cell) (m : ℕ) : Finset F.Cell := S.filter (FarFrom (S \ S₁) m)
theorem mem_farCells {S S₁ : Finset F.Cell} {m : ℕ} {v : F.Cell} :
    v ∈ farCells S S₁ m ↔ v ∈ S ∧ FarFrom (S \ S₁) m v := by
  classical
  simp [farCells]
theorem sitesOfCells_top (S : Finset F.Cell) : sitesOfCells S F.top = S := by
  ext y
  exact mem_sitesOfCells_top
theorem sitesOfCells_mono {S S₁ : Finset F.Cell} (h : S₁ ⊆ S) (j : ℕ) : sitesOfCells S₁ j ⊆ sitesOfCells S j :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h
theorem isCold_of_subset {S S₁ : Finset F.Cell} (h : S₁ ⊆ S) {j : ℕ} {r : ℝ} {V : F.GaugeField j}
    (hc : IsCold S j r V) : IsCold S₁ j r V := by
  intro p hp
  refine hc p ?_
  simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp ⊢
  exact ⟨sitesOfCells_mono h j hp.1, hp.2.1, hp.2.2.trans (sitesOfCells_mono h j)⟩
theorem sum_le_sum_far_add_near (S S₁ : Finset F.Cell) (f f₁ : F.Cell → ℝ) (B : ℝ) (hf₁ : ∀ z, 0 ≤ f₁ z)
    (hB : 0 ≤ B) (hfar : ∀ z ∈ S, FarFrom (S \ S₁) 310 z → f z = f₁ z) (hnear : ∀ z ∈ S, f z ≤ B) :
    ∑ z ∈ S, f z ≤ ∑ z ∈ S₁, f₁ z + B * (cellsNear S (S \ S₁) 330).card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not S (FarFrom (S \ S₁) 310)]
  refine add_le_add ?_ ?_
  · calc ∑ z ∈ S with FarFrom (S \ S₁) 310 z, f z = ∑ z ∈ S with FarFrom (S \ S₁) 310 z, f₁ z :=
          Finset.sum_congr rfl fun z hz => by
            rw [Finset.mem_filter] at hz
            exact hfar z hz.1 hz.2
      _ ≤ ∑ z ∈ S₁, f₁ z := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun z _ _ => hf₁ z
          intro z hz
          rw [Finset.mem_filter] at hz
          exact mem_of_farFrom_sdiff hz.1 hz.2
  · have h1 : ∑ z ∈ S with ¬ FarFrom (S \ S₁) 310 z, f z ≤
        ((S.filter fun z => ¬ FarFrom (S \ S₁) 310 z).card : ℝ) * B := by
      have := Finset.sum_le_card_nsmul (S.filter fun z => ¬ FarFrom (S \ S₁) 310 z) f B
        (fun z hz => hnear z (Finset.mem_filter.1 hz).1)
      simpa [nsmul_eq_mul] using this
    have hsub : (S.filter fun z => ¬ FarFrom (S \ S₁) 310 z) ⊆ cellsNear S (S \ S₁) 330 := by
      intro z hz
      rw [Finset.mem_filter] at hz
      obtain ⟨h1, h2⟩ := hz
      unfold FarFrom at h2
      push Not at h2
      obtain ⟨d, hd, hdz⟩ := h2
      simp only [cellsNear, Finset.mem_filter]
      exact ⟨h1, d, hd, by omega⟩
    have h2 : (((S.filter fun z => ¬ FarFrom (S \ S₁) 310 z).card : ℕ) : ℝ) ≤ (cellsNear S (S \ S₁) 330).card := by
      exact_mod_cast Finset.card_le_card hsub
    refine h1.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h2 hB
end Reinsertion
open BlockAverages LumpContours CellTerms Reinsertion
theorem LumpContours.reinsertionCostEstimate_proof (hM1 : BlockAverages.minimalChartSizesStatement)
    (hTot : ChainTerms.chainActionEqSumTermsStatement)
    (hM2 : CellTerms.smallCellTermsStatement) (hCost : LumpContours.chartActionLowerBoundStatement)
    (hM3 : CellTerms.smallChartBoundStatement) (hRead : CellTerms.cellTermsLocalityStatement)
    (hRef : CellTerms.referenceLocalityStatement) (hMean : CellTerms.nonzeroAveragesStatement)
    (hOne : BlockAverages.uniqueMinimizerStatement) (hWhole : LumpContours.WholeCellCostEqualsMinimalAction)
    (hLeast : ChainEnergies.minimalChainEnergiesStatement) : LumpContours.ReinsertionCostEstimate := by
  intro a ha0
  obtain ⟨θ, del, Ca1, -, -, hdel, -, hCa1, L₁, hM1⟩ := hM1 a ha0
  obtain ⟨Ca2, hCa2, L₂, hM2⟩ := hM2 a ha0
  obtain ⟨L₃, hM3⟩ := hM3
  obtain ⟨cR, L₄, hcR, hRef⟩ := hRef
  obtain ⟨L₅, hOne⟩ := hOne a ha0
  obtain ⟨L₆, hMean⟩ := hMean
  set K : ℝ := 3100 * (2 * Ca1) with hKdef
  have hK : 0 < K := by positivity
  refine ⟨Ca2 * (1 + K) ^ 2, by positivity, L₁ + L₂ + L₃ + L₄ + L₅ + L₆, fun L hodd hL => ?_⟩
  obtain ⟨CL1, r1, hCL1, hr1, hM1⟩ := hM1 L hodd (by omega)
  obtain ⟨c2, hc2, hM2⟩ := hM2 L hodd (by omega) del hdel
  obtain ⟨c3, CL3, hc3, hCL3, hM3⟩ := hM3 L hodd (by omega) del hdel
  obtain ⟨σ, N0, hσ, hN0, hOne⟩ := hOne L hodd (by omega) 1 one_pos
  obtain ⟨c6, hc6, hMean⟩ := hMean L hodd (by omega) del hdel
  set D0 : ℝ := Real.sqrt (Real.exp (6 * del) * expCellCount del) with hD0
  have hD0p : 0 ≤ D0 := Real.sqrt_nonneg _
  set T : ℝ := D0 * K + 1 with hT
  have hTp : 0 < T := by positivity
  set T₁ : ℝ := D0 * (2 * Ca1) + 1 with hT₁
  have hT₁p : 0 < T₁ := by positivity
  refine ⟨CL3 * (1 + K), min r1 (min cR (min c2 (min c3 (min σ (min c6 (min (c2 / T) (min (c3 / T)
    (c6 / T₁)))))))),
    by positivity, by
      refine lt_min hr1 (lt_min hcR (lt_min hc2 (lt_min hc3 (lt_min hσ (lt_min hc6 (lt_min ?_ (lt_min ?_ ?_)))))))
      all_goals positivity, ?_⟩
  intro F S S₁ hFL hamb hsub hreg hreg₁ r V hr hr0 hcold
  have b1 : r ≤ r1 := hr0.trans (min_le_left _ _)
  have hr0a := hr0.trans (min_le_right _ _)
  have bR : r ≤ cR := hr0a.trans (min_le_left _ _)
  have hr0b := hr0a.trans (min_le_right _ _)
  have b2 : r ≤ c2 := hr0b.trans (min_le_left _ _)
  have hr0c := hr0b.trans (min_le_right _ _)
  have b3 : r ≤ c3 := hr0c.trans (min_le_left _ _)
  have hr0d := hr0c.trans (min_le_right _ _)
  have bσ : r ≤ σ := hr0d.trans (min_le_left _ _)
  have hr0e := hr0d.trans (min_le_right _ _)
  have b6 : r ≤ c6 := hr0e.trans (min_le_left _ _)
  have hr0f := hr0e.trans (min_le_right _ _)
  have bT2 : r ≤ c2 / T := hr0f.trans (min_le_left _ _)
  have hr0g := hr0f.trans (min_le_right _ _)
  have bT3 : r ≤ c3 / T := hr0g.trans (min_le_left _ _)
  have bT6 : r ≤ c6 / T₁ := hr0g.trans (min_le_right _ _)
  have hoddF : Odd F.blockSide := hFL.symm ▸ hodd
  have z0 := Nat.zero_le F.top
  have zt : F.depth ≤ F.top := Nat.le_succ F.depth
  have hcold₁ : IsCold S₁ F.top r V := isCold_of_subset hsub hcold
  obtain ⟨U₁, hU⟩ := hM1 F 1024 S₁ hFL hamb le_rfl hreg₁ r V hr b1 hcold₁
  set R₁ := referenceFieldChain S₁ V with hR₁
  set R' := referenceFieldChain S V with hR'
  have hCS₁ : farCells S S₁ 110 ⊆ S₁ := fun v hv =>
    mem_of_farFrom_sdiff (mem_farCells.1 hv).1 (mem_farCells.1 hv).2
  have hsame : ∀ z ∈ farCells S S₁ 110, AgreeNear 100 S₁ S V V z := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := mem_farCells.1 hz
    refine ⟨fun y hy => ⟨fun h => hsub h, fun h => ?_⟩, fun _ _ _ _ => rfl⟩
    exact mem_of_farFrom_sdiff h (FarFrom.of_dist_le (show FarFrom (S \ S₁) (10 + 100) z from hz2) hy)
  obtain ⟨-, γ, hγc, hγ⟩ := hRef F 1024 S₁ S (farCells S S₁ 110) r V V hoddF (by rw [hFL]; omega) hamb le_rfl
    hreg₁ hreg hr bR hcold₁ hcold hCS₁ hsame
  set U' := cutChart (cutoff (S \ S₁)) γ U₁ with hU'
  have hTurned : GaugeRelatedFar S S₁ (R₁ 0) (R' 0) γ := by
    intro x i h1 h2 h3 h4
    have := hγ 0 (Nat.succ_pos _) (x, i) ⟨mem_farCells.2 ⟨h1, h2⟩, mem_farCells.2 ⟨h3, h4⟩⟩
    simpa only [gaugeTransform, baseSite_zero] using this
  have hρ : 0 ≤ 2 * Ca1 * r := by positivity
  have hN₁ : ∀ v ∈ S₁, localNorm S₁ R₁ U₁ (fun _ _ => 1) v ≤ 2 * Ca1 * r :=
    fun v hv => hU.localNorm_le_two_mul v hv
  have hnear : ∀ y, localNorm S R' U' (fun _ _ => 1) y ≤ K * r := by
    intro y
    have := localNorm_cutChart_le (w := fun _ _ => 1) (R₁ := R₁) (R' := R') (g := γ) (U := U₁) hamb hoddF
      (fun _ _ => rfl) hTurned hρ hN₁ y
    calc _ ≤ 3100 * (2 * Ca1 * r) := this
      _ = K * r := by rw [hKdef]; ring
  have hKr : 0 ≤ K * r := by positivity
  have hsmall : supWeightedNorm S del R' U' ≤ D0 * (K * r) := supWeightedNorm_le hdel hKr fun z _ => hnear z
  have hsmall₁ : supWeightedNorm S₁ del R₁ U₁ ≤ D0 * (2 * Ca1 * r) := supWeightedNorm_le hdel hρ hN₁
  have le_T : ∀ {c : ℝ}, r ≤ c / T → D0 * (K * r) ≤ c := by
    intro c hc
    rw [le_div_iff₀ hTp] at hc
    have : 0 ≤ r := hr.le
    nlinarith
  have le_T₁ : D0 * (2 * Ca1 * r) ≤ c6 := by
    have hc := bT6
    rw [le_div_iff₀ hT₁p] at hc
    have : 0 ≤ r := hr.le
    nlinarith
  have hC₃ : farCells S S₁ 299 ⊆ farCells S S₁ 110 := by
    intro v hv
    obtain ⟨h1, h2⟩ := mem_farCells.1 hv
    exact mem_farCells.2 ⟨h1, h2.mono (by omega)⟩
  have hturned : IsGaugeRotatedOn (farCells S S₁ 299) γ R₁ R' U₁ U' := by
    refine ⟨fun j hj b hb => hγ j hj b ⟨hC₃ hb.1, hC₃ hb.2⟩, fun b hb => ?_, fun j hj b hb => ?_⟩
    · simp only [hU', cutChart, cutoff_baseSite_eq_one hoddF z0 b.1 (mem_farCells.1 hb.1).2, one_smul]
      rfl
    · simp only [hU', cutChart, cutoff_baseSite_eq_one hoddF (Nat.le_of_lt hj) b.1 (mem_farCells.1 hb.1).2,
        one_smul]
      rfl
  have hmeans : HasNonzeroAveragesOn (farCells S S₁ 299) R₁ U₁ :=
    hMean F 1024 S₁ hFL hamb le_rfl hreg₁ r V hr b6 hcold₁ U₁ (hsmall₁.trans le_T₁) _ (hC₃.trans hCS₁)
  obtain ⟨-, -, hfar⟩ := hRead F (farCells S S₁ 299) γ R₁ R' U₁ U' hoddF hamb hturned hmeans
  obtain ⟨hterm, hcoord⟩ := hfar fun y hy => hγc y (hC₃ hy)
  have hAct : ∀ X : Finset F.Cell, cutEffectiveAction a F.top X V = minimalAction a X F.top V := by
    intro X
    have h1 := (hWhole F a X hoddF ha0.le).2.1 F.top le_rfl V
    rwa [(hWhole F a X hoddF ha0.le).1 F.top le_rfl, sitesOfCells_top] at h1
  have hJ₁ : ∑ z ∈ S₁, chartCellTerms a S₁ R₁ U₁ V z = cutEffectiveAction a F.top S₁ V := by
    rw [hAct, ← hU.action_eq]
    exact ((hTot F a S₁ ha0.le hoddF (chartChain R₁ U₁ V) (chartGauge R₁ U₁)).2).symm
  have hJ : chartAction a S R' U' V ≤ reinsertionBound a (Ca2 * (1 + K) ^ 2) r S S₁ V := by
    have e : chartAction a S R' U' V = ∑ z ∈ S, chartCellTerms a S R' U' V z :=
      (hTot F a S ha0.le hoddF (chartChain R' U' V) (chartGauge R' U')).2
    rw [e]
    unfold reinsertionBound
    rw [← hJ₁]
    have hs := sum_le_sum_far_add_near S S₁ (fun z => chartCellTerms a S R' U' V z)
      (fun z => chartCellTerms a S₁ R₁ U₁ V z)
      (Ca2 * (1 + K) ^ 2 * r ^ 2)
      (fun z => (hTot F a S₁ ha0.le hoddF (chartChain R₁ U₁ V) (chartGauge R₁ U₁)).1 z)
      (by positivity)
      (fun z hz hf => by
        refine (hterm a S₁ S V V z (fun y hy => ?_) fun _ _ _ _ => rfl).symm
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hy
        have hd : cellSupDist z (z + siteOfCoords F.top h) ≤ 1 := by
          rw [cellSupDist_comm]
          refine cellSupDist_add_le hamb z (by norm_num) fun i => ?_
          have := (mem_centredCube_iff.1 hh) i
          rw [abs_le]
          simpa using this
        have hfy : FarFrom (S \ S₁) 309 (z + siteOfCoords F.top h) :=
          FarFrom.of_dist_le (show FarFrom (S \ S₁) (309 + 1) z from hf) hd
        refine ⟨⟨fun h1 => hsub h1, fun h1 => mem_of_farFrom_sdiff h1 hfy⟩, fun h1 => ?_⟩
        exact mem_farCells.2 ⟨hsub h1, hfy.mono (by omega)⟩)
      (fun z hz => by
        have h1 := hM2 F 1024 S hFL hamb le_rfl hreg r V hr b2 hcold U' (hsmall.trans (le_T bT2)) (K * r) z hz
          hKr (fun y _ => hnear y)
        calc _ ≤ Ca2 * (r + K * r) ^ 2 := h1
          _ = _ := by ring)
    exact hs
  have hCost' := hCost F a S ha0.le hoddF R' U' V
  have hcut : cutBelow F.depth S = sitesOfCells S F.depth := (hWhole F a S hoddF ha0.le).1 F.depth zt
  have hbonds : ∀ b ∈ cutBonds (cutBelow F.depth S), b ∈ innerBonds S F.depth := by
    intro b hb
    rw [hcut] at hb
    exact hb
  obtain ⟨hb3, hp3⟩ := hM3 F 1024 S hFL hamb le_rfl hreg r V hr b3 hcold U' (hsmall.trans (le_T bT3)) (K * r) hKr
  refine ⟨hCost'.1.trans hJ, chartFieldTopFixed R' U', hCost'.2.trans hJ, fun b hb => ?_, fun p hp => ?_, ?_⟩
  · calc _ ≤ CL3 * (r + K * r) := hb3 1 b (hbonds b hb) fun y _ => hnear y
      _ = _ := by ring
  · rw [hcut] at hp
    calc _ ≤ CL3 * (r + K * r) := hp3 p hp fun y _ => hnear y
      _ = _ := by ring
  · intro Wl hWl b hb hfb
    have hb' := hbonds b hb
    have hb2 := hb'
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hb2
    have s1 := enclosingCell_mem_of_mem_sitesOfCells hoddF zt hb2.1
    have s2 := enclosingCell_mem_of_mem_sitesOfCells hoddF zt hb2.2
    have f1 : FarFrom (S \ S₁) 320 (enclosingCell b.1) := hfb
    have f2 : FarFrom (S \ S₁) 319 (enclosingCell (b.1 + unitStep F.depth b.2)) :=
      FarFrom.of_dist_le (show FarFrom (S \ S₁) (319 + 1) _ from f1)
        (cellSupDist_enclosingCell_add_unitStep_le hamb hoddF zt b.1 b.2)
    have hB : BondWithin (farCells S S₁ 299) b :=
      ⟨mem_farCells.2 ⟨s1, f1.mono (by omega)⟩, mem_farCells.2 ⟨s2, f2.mono (by omega)⟩⟩
    have hb₁ : b ∈ innerBonds S₁ F.depth := by
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨mem_sitesOfCells_of_enclosingCell_mem hoddF zt (mem_of_farFrom_sdiff s1 f1),
        mem_sitesOfCells_of_enclosingCell_mem hoddF zt (mem_of_farFrom_sdiff s2 f2)⟩
    rw [← hcoord 1 V V b hB fun _ => rfl]
    have hE : ∀ W : F.GaugeField F.depth, plainBlockEnergy a S₁ W V = blockEnergy a S₁ F.depth W V :=
      fun W => (hWhole F a S₁ hoddF ha0.le).2.2 W V
    have hW₁ : ∀ W'', blockEnergy a S₁ F.depth (chartFieldTopFixed R₁ U₁) V ≤ blockEnergy a S₁ F.depth W'' V := by
      intro W''
      rw [← hE, ← hE]
      calc _ ≤ chartAction a S₁ R₁ U₁ V := (hCost F a S₁ ha0.le hoddF R₁ U₁ V).2
        _ = cutEffectiveAction a F.top S₁ V := by rw [hU.action_eq, hAct]
        _ ≤ _ := (hLeast F a ha0.le hoddF).2.2.2.2 S₁ W'' V
    have hWl' : ∀ W'', blockEnergy a S₁ F.depth Wl V ≤ blockEnergy a S₁ F.depth W'' V := by
      intro W''
      rw [← hE, ← hE]
      exact hWl W''
    exact bondCoordinate_eq_of_minimizers hamb hoddF (hOne F 1024 S₁ hFL hamb le_rfl hreg₁ r V hr bσ hcold₁)
      hW₁ hWl' 1 hb₁
end YangMills.Construction
end
