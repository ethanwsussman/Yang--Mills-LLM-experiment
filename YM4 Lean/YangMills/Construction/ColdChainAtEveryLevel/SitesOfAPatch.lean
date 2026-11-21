import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import YangMills.Construction.ColdChainAtEveryLevel.SharesOfTheCellsAtASite
import YangMills.Construction.ColdChainAtEveryLevel.TermsAndVariationsOfAFramedChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open GaugeMap LatticeFractionalIntegration
namespace BlockAverages
namespace PatchLocality
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by
  refine Finset.sup_le fun i _ => ?_
  have h1 : ((x i - y i).valMinAbs).natAbs ≤ cellSupDist x y :=
    Finset.le_sup (f := fun i => ((x i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
  have h2 : ((y i - z i).valMinAbs).natAbs ≤ cellSupDist y z :=
    Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
  have h3 := ZMod.natAbs_valMinAbs_add_le (x i - y i) (y i - z i)
  have e : (x i - y i) + (y i - z i) = x i - z i := by ring
  rw [e] at h3
  show ((x i - z i).valMinAbs).natAbs ≤ _
  omega
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem add_siteOfCoords_cellDisplacement (z y : F.Cell) : z + siteOfCoords F.top (cellDisplacement z y) = y := by
  funext i
  simp [siteOfCoords, cellDisplacement, ZMod.coe_valMinAbs]
theorem abs_cellDisplacement_le {z y : F.Cell} (i : Fin 4) : |cellDisplacement z y i| ≤ cellSupDist y z := by
  have h1 : ((y i - z i).valMinAbs).natAbs ≤ cellSupDist y z :=
    Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
  have : cellDisplacement z y i = (y i - z i).valMinAbs := rfl
  rw [this, Int.abs_eq_natAbs]
  exact_mod_cast h1
theorem two_mul_abs_cellDisplacement_le_period {z y : F.Cell} (i : Fin 4) (hp : 0 < F.period F.top i) :
    2 * |cellDisplacement z y i| ≤ (F.period F.top i : ℤ) := by
  have : NeZero (F.period F.top i) := ⟨hp.ne'⟩
  have h1 := ZMod.natAbs_valMinAbs_le ((y - z) i)
  have : cellDisplacement z y i = ((y - z) i).valMinAbs := rfl
  rw [this, Int.abs_eq_natAbs]
  omega
theorem cellSideLength_mul_cellDisplacement (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {y : F.Cell}
    {A h : Lattice4} {R : ℕ} (hR : R ≤ 25)
    (hA : ∀ i, |A i| ≤ R * cellSideLength F) (hh : h ∈ centredCube (F.blockSide ^ F.top))
    (he : cellCentre 0 z + siteOfCoords 0 A = cellCentre 0 y + siteOfCoords 0 h) (i : Fin 4) :
    cellSideLength F * cellDisplacement z y i = A i - h i := by
  have hL : 0 < F.blockSide := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  have hcs : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
  have hhb : ∀ i, |h i| ≤ (cellSideLength F - 1) / 2 := by
    intro i
    have := (Fintype.mem_piFinset.1 hh) i
    rw [Finset.mem_Icc, hcs] at this
    rw [abs_le]
    exact this
  set w : Lattice4 := cellDisplacement z y with hw
  have hy : y = z + siteOfCoords F.top w := (add_siteOfCoords_cellDisplacement z y).symm
  have hcy : cellCentre 0 y = cellCentre 0 z + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * w i) := by
    conv_lhs => rw [hy]
    exact cellCentre_add 0 (Nat.zero_le _) z w
  have h1 : ((A i : ℤ) : ZMod (F.period 0 i)) = ((cellSideLength F * w i + h i : ℤ) : ZMod (F.period 0 i)) := by
    have h2 := congrFun he i
    rw [hcy] at h2
    simp only [Pi.add_apply, siteOfCoords, Nat.sub_zero] at h2
    rw [add_assoc] at h2
    rw [add_left_cancel h2]
    push_cast [cellSideLength]
    ring
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨e, he'⟩ := h1
  have hb1 := hhb i
  have hb2 := hA i
  have hRz : (R : ℤ) ≤ 25 := by exact_mod_cast hR
  have hfin : cellSideLength F * w i = A i - h i := by
    rcases period_zero_eq_zero_or hamb hL i with h0 | h64
    · have hp : (F.period 0 i : ℤ) = 0 := by exact_mod_cast h0
      rw [hp, zero_mul] at he'
      linarith
    · by_cases he0 : e = 0
      · subst he0
        rw [mul_zero] at he'
        linarith
      · exfalso
        have hp0 : 0 < (F.period 0 i : ℤ) := by nlinarith
        have hper : (F.period 0 i : ℤ) = (F.period F.top i : ℤ) * cellSideLength F := by
          have := period_zero_eq (F := F) F.top le_rfl i
          rw [this]
          simp [cellSideLength]
        have hpn : 0 < F.period F.top i := by
          have : (0 : ℤ) < (F.period F.top i : ℤ) := by
            by_contra hc
            have : (F.period F.top i : ℤ) = 0 := by
              have h2 : (0 : ℤ) ≤ (F.period F.top i : ℤ) := by positivity
              omega
            rw [this, zero_mul] at hper
            omega
          exact_mod_cast this
        have hhalf := two_mul_abs_cellDisplacement_le_period (F := F) (z := z) (y := y) i hpn
        rw [← hw] at hhalf
        have hwN : 2 * (cellSideLength F * |w i|) ≤ (F.period 0 i : ℤ) := by
          rw [hper]
          nlinarith
        have h1e : 1 ≤ |e| := Int.one_le_abs he0
        have hbig : (F.period 0 i : ℤ) ≤ |(F.period 0 i : ℤ) * e| := by
          rw [abs_mul, abs_of_pos hp0]
          nlinarith
        have hsmall : |(F.period 0 i : ℤ) * e| ≤ cellSideLength F * |w i| + |h i| + |A i| := by
          rw [← he']
          have t1 := abs_add_le (cellSideLength F * w i + h i) (- A i)
          have t2 := abs_add_le (cellSideLength F * w i) (h i)
          rw [abs_neg] at t1
          rw [abs_mul, abs_of_pos hN] at t2
          have t3 : cellSideLength F * w i + h i - A i = cellSideLength F * w i + h i + - A i := by ring
          rw [t3]
          linarith
        have hA' : |A i| ≤ 25 * cellSideLength F := hb2.trans (mul_le_mul_of_nonneg_right hRz hN.le)
        have hh2 : 2 * |h i| ≤ cellSideLength F := by omega
        linarith
  exact hfin
theorem cellSupDist_le_of_offsets (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {y : F.Cell}
    {A h : Lattice4} {R : ℕ} (hR : R ≤ 25)
    (hA : ∀ i, |A i| ≤ R * cellSideLength F) (hh : h ∈ centredCube (F.blockSide ^ F.top))
    (he : cellCentre 0 z + siteOfCoords 0 A = cellCentre 0 y + siteOfCoords 0 h) : cellSupDist y z ≤ R + 1 := by
  have hL : 0 < F.blockSide := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  have hcs : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
  have hhb : ∀ i, |h i| ≤ (cellSideLength F - 1) / 2 := by
    intro i
    have := (Fintype.mem_piFinset.1 hh) i
    rw [Finset.mem_Icc, hcs] at this
    rw [abs_le]
    exact this
  refine Finset.sup_le fun i _ => ?_
  show ((y i - z i).valMinAbs).natAbs ≤ R + 1
  have hwi : (y i - z i).valMinAbs = cellDisplacement z y i := rfl
  rw [hwi]
  have hfin := cellSideLength_mul_cellDisplacement hamb hodd hR hA hh he i
  set w : Lattice4 := cellDisplacement z y with hw
  have hb1 := hhb i
  have hb2 := hA i
  have hfb : |cellSideLength F * w i| ≤ (R : ℤ) * cellSideLength F + (cellSideLength F - 1) / 2 := by
    rw [hfin]
    have t1 := abs_add_le (A i) (- h i)
    rw [abs_neg] at t1
    have t3 : A i - h i = A i + - h i := by ring
    rw [t3]
    linarith
  rw [abs_mul, abs_of_pos hN] at hfb
  have hlt : |w i| < (R : ℤ) + 1 := by
    by_contra hge
    rw [not_lt] at hge
    have h1 : ((R : ℤ) + 1) * cellSideLength F ≤ cellSideLength F * |w i| := by nlinarith
    have h2 : ((R : ℤ) + 1) * cellSideLength F = (R : ℤ) * cellSideLength F + cellSideLength F := by ring
    omega
  have := Int.abs_eq_natAbs (w i)
  omega
theorem exists_offset_of_cellCutoff_ne_zero (hodd : Odd F.blockSide) {x : F.Site 0} (hb : cellCutoff x z ≠ 0) :
    ∃ A : Lattice4, (∀ i, |A i| ≤ 1 * cellSideLength F) ∧ x = cellCentre 0 z + siteOfCoords 0 A := by
  have hL : 0 < F.blockSide := hodd.pos
  have hNr : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  refine ⟨fun i => ((x - cellCentre 0 z) i).valMinAbs, fun i => ?_, ?_⟩
  · have h1 : cutoffProfile ((((x - cellCentre 0 z) i).valMinAbs : ℝ) / (F.blockSide : ℝ) ^ F.top) ≠ 0 := by
      intro h0
      apply hb
      unfold cellCutoff
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    have h2 := abs_lt_of_cutoffProfile_ne_zero h1
    rw [abs_div, abs_of_pos hNr, div_lt_iff₀ hNr] at h2
    have h3 : ((|((x - cellCentre 0 z) i).valMinAbs| : ℤ) : ℝ) < (cellSideLength F : ℝ) := by
      have e : (cellSideLength F : ℝ) = (F.blockSide : ℝ) ^ F.top := by simp [cellSideLength]
      rw [e]
      push_cast
      nlinarith
    have h4 : |((x - cellCentre 0 z) i).valMinAbs| < cellSideLength F := by exact_mod_cast h3
    linarith
  · funext i
    simp [siteOfCoords, ZMod.coe_valMinAbs]
theorem exists_cell_of_mem_sitesOfCells (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) {h : Lattice4} (hh : h ∈ centredCube (F.blockSide ^ j)) :
    ∃ y ∈ S, ∃ h' ∈ centredCube (F.blockSide ^ F.top),
      baseSite x + siteOfCoords 0 h = cellCentre 0 y + siteOfCoords 0 h' := by
  obtain ⟨y, hy, h₁, hh₁, rfl⟩ := mem_sitesOfCells.1 hx
  refine ⟨y, hy, fun i => (F.blockSide : ℤ) ^ j * h₁ i + h i, ?_, ?_⟩
  · refine Fintype.mem_piFinset.2 fun i => ?_
    have a1 := Fintype.mem_piFinset.1 hh₁ i
    have a2 := Fintype.mem_piFinset.1 hh i
    rw [Finset.mem_Icc] at a1 a2 ⊢
    set p : ℤ := (F.blockSide : ℤ) ^ j with hp
    set q : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hq
    have hpq : ((F.blockSide ^ F.top : ℕ) : ℤ) = p * q := by
      rw [hp, hq, ← pow_add]
      push_cast
      congr 2
      omega
    have c1 : ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) = q := by rw [hq]; push_cast; rfl
    have c2 : ((F.blockSide ^ j : ℕ) : ℤ) = p := by rw [hp]; push_cast; rfl
    rw [c1] at a1
    rw [c2] at a2
    rw [hpq]
    have oddp : Odd p := by rw [hp]; exact Odd.pow (by exact_mod_cast hodd)
    have oddq : Odd q := by rw [hq]; exact Odd.pow (by exact_mod_cast hodd)
    obtain ⟨u, hu⟩ := oddp
    obtain ⟨v, hv⟩ := oddq
    have hp1 : (p - 1) / 2 = u := by omega
    have hq1 : (q - 1) / 2 = v := by omega
    have hpq1 : (p * q - 1) / 2 = p * v + u := by
      have : p * q - 1 = 2 * (p * v + u) := by
        rw [hv]
        have : p * (2 * v + 1) - 1 = 2 * (p * v) + (p - 1) := by ring
        rw [this, hu]
        ring
      rw [this]
      simp
    have hp0 : 0 ≤ p := by rw [hp]; positivity
    rw [hp1] at a2
    rw [hq1] at a1
    rw [hpq1]
    have b1 : p * (-v) ≤ p * h₁ i := mul_le_mul_of_nonneg_left a1.1 hp0
    have b2 : p * h₁ i ≤ p * v := mul_le_mul_of_nonneg_left a1.2 hp0
    constructor <;> nlinarith [a2.1, a2.2]
  · rw [baseSite_add j hj, baseSite_cellCentre j hj, add_assoc, ← siteOfCoords_add]
    rfl
theorem abs_basisVector_le (μ i : Fin 4) : |basisVector μ i| ≤ 1 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.abs_single_one_le <;> assumption
theorem exists_offset_of_mem_plaquetteCorners {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) {x : F.Site j}
    (hx : x ∈ plaquetteCorners p) :
    ∃ δ : Lattice4, (∀ i, |δ i| ≤ 2) ∧ x = p.1 + siteOfCoords j δ := by
  classical
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, fun i => by simp, by rw [siteOfCoords_zero, add_zero]⟩
  · exact ⟨basisVector p.2.1, fun i => (abs_basisVector_le _ i).trans (by norm_num), rfl⟩
  · exact ⟨basisVector p.2.2, fun i => (abs_basisVector_le _ i).trans (by norm_num), rfl⟩
  · refine ⟨basisVector p.2.1 + basisVector p.2.2, fun i => ?_, ?_⟩
    · have := abs_add_le (basisVector p.2.1 i) (basisVector p.2.2 i)
      have h1 := abs_basisVector_le p.2.1 i
      have h2 := abs_basisVector_le p.2.2 i
      simp only [Pi.add_apply]
      linarith
    · rw [siteOfCoords_add, add_assoc]
      rfl
theorem mem_patchBaseSites_of_cellSupDist_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} (hy : y ∈ S) (hd : cellSupDist z y ≤ 10) {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) :
    cellCentre 0 y + siteOfCoords 0 h ∈ patchBaseSites S z := by
  classical
  have hL : 0 < F.blockSide := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  have hcs : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
  have hhb : ∀ i, -((cellSideLength F - 1) / 2) ≤ h i ∧ h i ≤ (cellSideLength F - 1) / 2 := by
    intro i
    have := (Fintype.mem_piFinset.1 hh) i
    rw [Finset.mem_Icc, hcs] at this
    exact this
  set o : Lattice4 := cellDisplacement z y with ho
  set e := closedOrthant S z with hes
  have hee : ∀ i, e i * e i = 1 := by
    intro i
    rcases he i with h | h <;> rw [h] <;> norm_num
  have hob : ∀ i, -10 ≤ o i ∧ o i ≤ 10 := by
    intro i
    have h1 : |o i| ≤ cellSupDist y z := abs_cellDisplacement_le i
    rw [cellSupDist_comm] at h1
    have h2 : ((cellSupDist z y : ℕ) : ℤ) ≤ 10 := by exact_mod_cast hd
    exact abs_le.1 (h1.trans h2)
  set x' : Lattice4 := fun i => e i * (cellSideLength F * o i + h i) + (cellSideLength F - 1) / 2 with hx'
  refine Finset.mem_image.2 ⟨x', ?_, ?_⟩
  · have hmem : ∀ i, e i * o i * cellSideLength F ≤ x' i ∧ -(10 * cellSideLength F) ≤ x' i ∧
        x' i ≤ 21 * cellSideLength F - 1 := by
      intro i
      have a1 := hob i
      have a2 := hhb i
      have m1 : cellSideLength F * (-10) ≤ cellSideLength F * o i := mul_le_mul_of_nonneg_left a1.1 hN.le
      have m2 : cellSideLength F * o i ≤ cellSideLength F * 10 := mul_le_mul_of_nonneg_left a1.2 hN.le
      simp only [hx']
      rcases he i with h1 | h1 <;> rw [h1] <;> constructor <;> [skip; constructor; skip; constructor] <;> nlinarith
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨(hmem i).2.1, (hmem i).2.2⟩, ?_⟩
    refine ⟨fun i => e i * o i * cellSideLength F, Finset.mem_image.2 ⟨y, ?_, rfl⟩, fun i => (hmem i).1⟩
    exact Finset.mem_filter.2 ⟨hy, hd⟩
  · have hcy : cellCentre 0 y =
        cellCentre 0 z + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * o i) := by
      conv_lhs => rw [← add_siteOfCoords_cellDisplacement z y]
      exact cellCentre_add 0 (Nat.zero_le _) z o
    rw [hcy, add_assoc, ← siteOfCoords_add]
    unfold patchSite
    congr 2
    funext i
    simp only [hx', Pi.add_apply, Nat.sub_zero, cellSideLength]
    have : e i * (e i * (((F.blockSide : ℤ) ^ F.top) * o i + h i) + ((F.blockSide : ℤ) ^ F.top - 1) / 2 -
        ((F.blockSide : ℤ) ^ F.top - 1) / 2) =
        (e i * e i) * (((F.blockSide : ℤ) ^ F.top) * o i + h i) := by ring
    rw [this, hee i, one_mul]
theorem pow_le_cellSideLength (hL : 0 < F.blockSide) {j : ℕ} (hj : j ≤ F.top) :
    (F.blockSide : ℤ) ^ j ≤ cellSideLength F := by
  unfold cellSideLength
  exact pow_le_pow_right₀ (by exact_mod_cast hL) hj
theorem abs_le_of_mem_centredCube {M : ℕ} (hM : 0 < M) {h : Lattice4} (hh : h ∈ centredCube M) (i : Fin 4) :
    |h i| ≤ (M : ℤ) := by
  have := (Fintype.mem_piFinset.1 hh) i
  rw [Finset.mem_Icc] at this
  rw [abs_le]
  constructor <;> omega
theorem cellSupDist_le_four_of_cellCutoff_ne_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {x : F.Site 0} (hb : cellCutoff x z ≠ 0) {δ h : Lattice4}
    {y : F.Cell} (hδ : ∀ i, |δ i| ≤ 2 * cellSideLength F) (hh : h ∈ centredCube (F.blockSide ^ F.top))
    (he : x + siteOfCoords 0 δ = cellCentre 0 y + siteOfCoords 0 h) : cellSupDist z y ≤ 4 := by
  obtain ⟨A, hA, rfl⟩ := exists_offset_of_cellCutoff_ne_zero hodd hb
  rw [cellSupDist_comm]
  refine cellSupDist_le_of_offsets hamb hodd (A := A + δ) (R := 3) (by norm_num) (fun i => ?_) hh ?_
  · have t := abs_add_le (A i) (δ i)
    have h1 := hA i
    have h2 := hδ i
    simp only [Pi.add_apply]
    push_cast
    linarith
  · rw [siteOfCoords_add, ← add_assoc, he]
theorem mem_patchActionTerms_of_cellCutoff_ne_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {t : F.ActionTerm} (ht : t ∈ actionTerms S) (hb : cellCutoff (actionTermSite t) z ≠ 0) :
    t ∈ patchActionTerms S z := by
  classical
  have hL : 0 < F.blockSide := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  rcases t with p | ⟨j, c⟩
  · have hp : p ∈ innerPlaquettes S 0 := Finset.inl_mem_disjSum.1 ht
    refine Finset.inl_mem_disjSum.2 (Finset.mem_filter.2 ⟨hp, fun x hx => ?_⟩)
    have hxs : x ∈ sitesOfCells S 0 := (Finset.mem_filter.1 hp).2.2 hx
    obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hxs
    obtain ⟨δ, hδ, hxδ⟩ := exists_offset_of_mem_plaquetteCorners p hx
    have hd := cellSupDist_le_four_of_cellCutoff_ne_zero hamb hodd hb (δ := δ) (fun i => by
      have := hδ i
      nlinarith) hh hxδ.symm
    exact mem_patchBaseSites_of_cellSupDist_le hamb hodd he hy (by omega) hh
  · have hc := Finset.inr_mem_disjSum.1 ht
    have hj : j ∈ Finset.range F.top := (Finset.mem_sigma.1 hc).1
    have hcb : c ∈ innerBonds S (j + 1) := (Finset.mem_sigma.1 hc).2
    have hj' : j + 1 ≤ F.top := Finset.mem_range.1 hj
    have hcf := Finset.mem_filter.1 hcb
    have h1 : c.1 ∈ sitesOfCells S (j + 1) := (Finset.mem_product.1 hcf.1).1
    have h2 : c.1 + unitStep (j + 1) c.2 ∈ sitesOfCells S (j + 1) := hcf.2
    have hbb : cellCutoff (baseSite c.1) z ≠ 0 := hb
    have hpw := pow_le_cellSideLength (F := F) hL hj'
    have hMpos : 0 < F.blockSide ^ (j + 1) := by positivity
    refine Finset.inr_mem_disjSum.2 (Finset.mem_sigma.2 ⟨hj, Finset.mem_filter.2 ⟨hcb, fun h hh => ?_⟩⟩)
    have hcast : ((F.blockSide ^ (j + 1) : ℕ) : ℤ) = (F.blockSide : ℤ) ^ (j + 1) := by push_cast; rfl
    have hhb : ∀ i, |h i| ≤ cellSideLength F := fun i => by
      have := abs_le_of_mem_centredCube hMpos hh i
      rw [hcast] at this
      linarith
    constructor
    · obtain ⟨y, hy, h', hh', e⟩ := exists_cell_of_mem_sitesOfCells hodd hj' h1 hh
      have hd := cellSupDist_le_four_of_cellCutoff_ne_zero hamb hodd hbb (δ := h) (fun i => by
        have := hhb i
        linarith) hh' e
      rw [e]
      exact mem_patchBaseSites_of_cellSupDist_le hamb hodd he hy (by omega) hh'
    · obtain ⟨y, hy, h', hh', e⟩ := exists_cell_of_mem_sitesOfCells hodd hj' h2 hh
      have e2 : baseSite (c.1 + unitStep (j + 1) c.2) =
          baseSite c.1 + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (j + 1) * basisVector c.2 i) := by
        rw [unitStep_eq]
        exact baseSite_add (j + 1) hj' c.1 (basisVector c.2)
      have hd := cellSupDist_le_four_of_cellCutoff_ne_zero hamb hodd hbb
        (δ := (fun i => (F.blockSide : ℤ) ^ (j + 1) * basisVector c.2 i) + h) (fun i => by
        have t := abs_add_le ((F.blockSide : ℤ) ^ (j + 1) * basisVector c.2 i) (h i)
        have t2 : |(F.blockSide : ℤ) ^ (j + 1) * basisVector c.2 i| ≤ cellSideLength F := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          have := abs_basisVector_le c.2 i
          have hp0 : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ (j + 1) := by positivity
          nlinarith
        have := hhb i
        simp only [Pi.add_apply]
        linarith) hh' (by
          rw [siteOfCoords_add, ← add_assoc, ← e2]
          exact e)
      rw [e]
      exact mem_patchBaseSites_of_cellSupDist_le hamb hodd he hy (by omega) hh'
theorem patchActionTerms_subset : patchActionTerms S z ⊆ actionTerms S := by
  classical
  intro t ht
  rcases t with p | ⟨j, c⟩
  · exact Finset.inl_mem_disjSum.2 (Finset.mem_filter.1 (Finset.inl_mem_disjSum.1 ht)).1
  · have hc := Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 ht)
    exact Finset.inr_mem_disjSum.2 (Finset.mem_sigma.2 ⟨hc.1, (Finset.mem_filter.1 hc.2).1⟩)
theorem actionTermSite_mem_sitesOfCells (hodd : Odd F.blockSide) {t : F.ActionTerm} (ht : t ∈ actionTerms S) :
    actionTermSite t ∈ sitesOfCells S 0 := by
  classical
  rcases t with p | ⟨j, c⟩
  · have hp : p ∈ innerPlaquettes S 0 := Finset.inl_mem_disjSum.1 ht
    exact (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1
  · have hc := Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 ht)
    have hcb : c ∈ innerBonds S (j + 1) := hc.2
    have h1 : c.1 ∈ sitesOfCells S (j + 1) := (Finset.mem_product.1 (Finset.mem_filter.1 hcb).1).1
    have hz : (0 : Lattice4) ∈ centredCube (F.blockSide ^ (j + 1)) := by
      refine Fintype.mem_piFinset.2 fun i => ?_
      have : 0 < F.blockSide ^ (j + 1) := by have := hodd.pos; positivity
      simp only [Pi.zero_apply, Finset.mem_Icc]
      omega
    obtain ⟨y, hy, h', hh', e⟩ := exists_cell_of_mem_sitesOfCells hodd (Finset.mem_range.1 hc.1) h1 hz
    rw [siteOfCoords_zero, add_zero] at e
    show baseSite c.1 ∈ sitesOfCells S 0
    rw [e]
    exact mem_sitesOfCells.2 ⟨y, hy, h', by simpa using hh', rfl⟩
theorem actionTermSite_mem_patchBaseSites (hodd : Odd F.blockSide) {t : F.ActionTerm}
    (ht : t ∈ patchActionTerms S z) : actionTermSite t ∈ patchBaseSites S z := by
  classical
  rcases t with p | ⟨j, c⟩
  · have hp := Finset.mem_filter.1 (Finset.inl_mem_disjSum.1 ht)
    exact hp.2 (by simp [plaquetteCorners, actionTermSite])
  · have hc := Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 ht)
    have hcf := Finset.mem_filter.1 hc.2
    have hz : (0 : Lattice4) ∈ centredCube (F.blockSide ^ (j + 1)) := by
      refine Fintype.mem_piFinset.2 fun i => ?_
      have : 0 < F.blockSide ^ (j + 1) := by have := hodd.pos; positivity
      simp only [Pi.zero_apply, Finset.mem_Icc]
      omega
    have := (hcf.2 0 hz).1
    rwa [siteOfCoords_zero, add_zero] at this
theorem cellSupDist_le_of_mem_patchBaseSites (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {x : F.Site 0} (hx : x ∈ patchBaseSites S z) {y : F.Cell} {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top))
    (e : x = cellCentre 0 y + siteOfCoords 0 h) : cellSupDist y z ≤ 23 := by
  classical
  have hL : 0 < F.blockSide := hodd.pos
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
  have hr := Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx').1
  refine cellSupDist_le_of_offsets hamb hodd
    (A := fun i => closedOrthant S z i * (x' i - (cellSideLength F - 1) / 2)) (R := 22)
    (by norm_num) (fun i => ?_) hh e
  have h1 := Finset.mem_Icc.1 (hr i)
  rcases he i with h2 | h2 <;> rw [h2] <;> rw [abs_le] <;> push_cast <;> constructor <;> omega
theorem cellPartition_nonneg (x : F.Site 0) (y : F.Cell) : 0 ≤ cellPartition S x y :=
  div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
theorem cellPartition_le_one (x : F.Site 0) {y : F.Cell} (hy : y ∈ S) : cellPartition S x y ≤ 1 :=
  div_le_one_of_le₀ (Finset.single_le_sum (f := fun y => cellCutoff x y ^ 2) (fun _ _ => sq_nonneg _) hy)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
theorem sum_cellPartition (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {x : F.Site 0}
    (hx : x ∈ sitesOfCells S 0) : ∑ y ∈ S, cellPartition S x y = 1 := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  have hb := cellCutoff_self hamb hodd y (h := h) (by simpa using hh)
  have hpos : 0 < ∑ y' ∈ S, cellCutoff (cellCentre 0 y + siteOfCoords 0 h) y' ^ 2 := by
    refine lt_of_lt_of_le ?_
      (Finset.single_le_sum (f := fun y' => cellCutoff (cellCentre 0 y + siteOfCoords 0 h) y' ^ 2)
      (fun _ _ => sq_nonneg _) hy)
    simp [hb]
  unfold cellPartition
  rw [← Finset.sum_div, div_self hpos.ne']
theorem cellCutoff_ne_zero_of_cellPartition_ne_zero {x : F.Site 0} {y : F.Cell} (h : cellPartition S x y ≠ 0) :
    cellCutoff x y ≠ 0 :=
  fun hb => h (LocalPartition.cellPartition_eq_zero_of_cellCutoff_eq_zero hb)
theorem card_le_of_cellSupDist_le (b : F.Cell) (r : ℕ) [DecidableEq F.Cell] (A : Finset F.Cell)
    (hA : ∀ z ∈ A, cellSupDist z b ≤ r) : A.card ≤ (2 * r + 1) ^ 4 := by
  have hsub : A ⊆ (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(r : ℤ)) r).image
      (fun h => b + siteOfCoords F.top h) := by
    intro z hz
    refine Finset.mem_image.2 ⟨fun i => ((z - b) i).valMinAbs, ?_, ?_⟩
    · refine Fintype.mem_piFinset.2 fun i => ?_
      have h1 : ((z i - b i).valMinAbs).natAbs ≤ r :=
        (Finset.le_sup (f := fun i => ((z i - b i).valMinAbs).natAbs) (Finset.mem_univ i)).trans (hA z hz)
      rw [Finset.mem_Icc]
      have h2 : ((z - b) i) = z i - b i := rfl
      rw [h2]
      omega
    · funext i
      simp [siteOfCoords, ZMod.coe_valMinAbs]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Fintype.card_piFinset]
  have : ((r : ℤ) + 1 + r).toNat = 2 * r + 1 := by omega
  rw [this]
theorem gaugedBlockFit_nonneg {j : ℕ} (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) : 0 ≤ gaugedBlockFit X k X' c := by
  unfold gaugedBlockFit
  have h1 := quaternion_re_le_norm (gaugedContourAverage X k c * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))
  rw [norm_mul, norm_coe_unitQuaternion, mul_one] at h1
  linarith
theorem actionTermValue_nonneg {a : ℝ} (ha : 0 ≤ a) (X : F.FieldChain) (k : F.SiteGauge) (t : F.ActionTerm) :
    0 ≤ actionTermValue a X k t := by
  rcases t with p | ⟨j, c⟩
  · have h1 := quaternion_re_le_norm ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ])
    rw [norm_coe_unitQuaternion] at h1
    show 0 ≤ 1 - _
    linarith
  · exact mul_nonneg ha (gaugedBlockFit_nonneg _ _ _ _)
theorem relativeEnergyDensity_nonneg {a : ℝ} (ha : 0 ≤ a) (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain)
    (k Γ : F.SiteGauge) (t : F.ActionTerm) : 0 ≤ relativeEnergyDensity a W kW X k Γ t := by
  rcases t with p | ⟨j, c⟩
  · exact sq_nonneg _
  · exact mul_nonneg ha (sq_nonneg _)
theorem sum_actionTerms (S : Finset F.Cell) (f : F.ActionTerm → ℝ) :
    ∑ t ∈ actionTerms S, f t = ∑ p ∈ innerPlaquettes S 0, f (Sum.inl p) +
      ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), f (Sum.inr ⟨j, c⟩) := by
  unfold actionTerms
  rw [Finset.sum_disjSum, Finset.sum_sigma]
theorem sum_patchActionTerms (S : Finset F.Cell) (z : F.Cell) (f : F.ActionTerm → ℝ) :
    ∑ t ∈ patchActionTerms S z, f t = ∑ p ∈ patchPlaquettes S z, f (Sum.inl p) +
      ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, f (Sum.inr ⟨j, c⟩) := by
  unfold patchActionTerms
  rw [Finset.sum_disjSum, Finset.sum_sigma]
theorem gaugedChainAction_eq_sum (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (k : F.SiteGauge) :
    gaugedChainAction a S X k = ∑ t ∈ actionTerms S, actionTermValue a X k t := by
  rw [sum_actionTerms]
  unfold gaugedChainAction wilsonAction
  simp only [actionTermValue]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
theorem patchAction_eq_sum (a : ℝ) (S : Finset F.Cell) (z : F.Cell) (X : F.FieldChain) (k : F.SiteGauge) :
    patchAction a S z X k = ∑ t ∈ patchActionTerms S z, actionTermValue a X k t := by
  rw [sum_patchActionTerms]
  unfold patchAction
  simp only [actionTermValue]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
theorem relativeEnergy_eq_sum (a : ℝ) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k Γ : F.SiteGauge) :
    relativeEnergy a S z W kW X k Γ = ∑ t ∈ patchActionTerms S z, relativeEnergyDensity a W kW X k Γ t := by
  rw [sum_patchActionTerms]
  unfold relativeEnergy
  simp only [relativeEnergyDensity]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
theorem cellSupDist_le_two_of_cellCutoff_ne_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {x : F.Site 0} (hb : cellCutoff x z ≠ 0) {h : Lattice4}
    {y : F.Cell} (hh : h ∈ centredCube (F.blockSide ^ F.top)) (e : x = cellCentre 0 y + siteOfCoords 0 h) :
    cellSupDist z y ≤ 2 := by
  obtain ⟨A, hA, rfl⟩ := exists_offset_of_cellCutoff_ne_zero hodd hb
  rw [cellSupDist_comm]
  exact cellSupDist_le_of_offsets hamb hodd (R := 1) (by norm_num) (fun i => by simpa using hA i) hh e
theorem enclosingCell_actionTermSite (hodd : Odd F.blockSide) {t : F.ActionTerm} (ht : t ∈ actionTerms S) :
    enclosingCell (actionTermSite t) ∈ S ∧ ∃ h ∈ centredCube (F.blockSide ^ F.top),
      actionTermSite t = cellCentre 0 (enclosingCell (actionTermSite t)) + siteOfCoords 0 h := by
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 (actionTermSite_mem_sitesOfCells hodd ht)
  have hc : enclosingCell (actionTermSite t) = y := by
    rw [e]
    exact LocalPartition.enclosingCell_cellCentre_add hodd y h hh
  rw [hc]
  exact ⟨hy, h, by simpa using hh, e⟩
theorem mem_patchBaseSites_of_same_cell (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} {h h' : Lattice4} (hh : h ∈ centredCube (F.blockSide ^ F.top))
    (hh' : h' ∈ centredCube (F.blockSide ^ F.top))
    (hx : cellCentre 0 y + siteOfCoords 0 h ∈ patchBaseSites S z) :
    cellCentre 0 y + siteOfCoords 0 h' ∈ patchBaseSites S z := by
  classical
  have hL : 0 < F.blockSide := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  have hcs : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
  have hhb : ∀ {g : Lattice4}, g ∈ centredCube (F.blockSide ^ F.top) → ∀ i,
      -((cellSideLength F - 1) / 2) ≤ g i ∧ g i ≤ (cellSideLength F - 1) / 2 := by
    intro g hg i
    have := (Fintype.mem_piFinset.1 hg) i
    rw [Finset.mem_Icc, hcs] at this
    exact this
  obtain ⟨x', hx', e⟩ := Finset.mem_image.1 hx
  have hf := Finset.mem_filter.1 hx'
  have hr := Fintype.mem_piFinset.1 hf.1
  obtain ⟨a, ha, hax⟩ := hf.2
  obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 ha
  set m := (cellSideLength F - 1) / 2 with hm
  set σ := closedOrthant S z with hσ
  have hee : ∀ i, σ i * σ i = 1 := by
    intro i
    rcases he i with h | h <;> rw [h] <;> norm_num
  have hAb : ∀ i, |σ i * (x' i - m)| ≤ ((22 : ℕ) : ℤ) * cellSideLength F := by
    intro i
    have h1 := Finset.mem_Icc.1 (hr i)
    rcases he i with h2 | h2 <;> rw [h2] <;> rw [abs_le] <;> push_cast <;> constructor <;> omega
  have hoff := cellSideLength_mul_cellDisplacement (y := y) (A := fun i => σ i * (x' i - m)) (h := h) hamb hodd
    (R := 22) (by norm_num) hAb hh e
  set w : Lattice4 := cellDisplacement z y with hw
  have hxv : ∀ i, x' i = cellSideLength F * (σ i * w i) + σ i * h i + m := by
    intro i
    have h1 := hoff i
    have h2 : σ i * (cellSideLength F * w i + h i) = (σ i * σ i) * (x' i - m) := by
      have : cellSideLength F * w i + h i = σ i * (x' i - m) := by linarith
      rw [this]
      ring
    rw [hee i, one_mul] at h2
    linarith
  set x'' : Lattice4 := fun i => cellSideLength F * (σ i * w i) + σ i * h' i + m with hx''
  have hshift : ∀ {g : Lattice4}, g ∈ centredCube (F.blockSide ^ F.top) → ∀ i,
      0 ≤ σ i * g i + m ∧ σ i * g i + m ≤ cellSideLength F - 1 := by
    intro g hg i
    have h1 := hhb hg i
    rcases he i with h2 | h2 <;> rw [h2] <;> constructor <;> omega
  refine Finset.mem_image.2 ⟨x'', ?_, ?_⟩
  · have hv : ∀ i, -10 ≤ σ i * w i ∧ σ i * w i ≤ 20 ∧
        σ i * cellDisplacement z y₀ i ≤ σ i * w i := by
      intro i
      have h1 := Finset.mem_Icc.1 (hr i)
      have h2 := hshift hh i
      have h3 := hxv i
      have h4 := hax i
      refine ⟨?_, ?_, ?_⟩
      · by_contra hc
        have hc' : σ i * w i + 11 ≤ 0 := by omega
        have : cellSideLength F * (σ i * w i + 11) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN.le hc'
        nlinarith
      · by_contra hc
        have hc' : 21 ≤ σ i * w i := by omega
        have : cellSideLength F * 21 ≤ cellSideLength F * (σ i * w i) := mul_le_mul_of_nonneg_left hc' hN.le
        nlinarith
      · by_contra hc
        have hc' : σ i * w i + 1 ≤ σ i * cellDisplacement z y₀ i := by omega
        have : cellSideLength F * (σ i * w i + 1) ≤ cellSideLength F * (σ i * cellDisplacement z y₀ i) :=
          mul_le_mul_of_nonneg_left hc' hN.le
        have e1 : σ i * cellDisplacement z y₀ i * cellSideLength F =
            cellSideLength F * (σ i * cellDisplacement z y₀ i) := by ring
        simp only [] at h4
        nlinarith
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_, ?_⟩
    · have h1 := (hv i).1
      have h2 := (hv i).2.1
      have h3 := hshift hh' i
      have m1 : cellSideLength F * (-10) ≤ cellSideLength F * (σ i * w i) := mul_le_mul_of_nonneg_left h1 hN.le
      have m2 : cellSideLength F * (σ i * w i) ≤ cellSideLength F * 20 := mul_le_mul_of_nonneg_left h2 hN.le
      simp only [hx'']
      constructor <;> nlinarith [h3.1, h3.2]
    · refine ⟨_, Finset.mem_image.2 ⟨y₀, hy₀, rfl⟩, fun i => ?_⟩
      have h3 := hshift hh' i
      have m1 : cellSideLength F * (σ i * cellDisplacement z y₀ i) ≤ cellSideLength F * (σ i * w i) :=
        mul_le_mul_of_nonneg_left (hv i).2.2 hN.le
      simp only [hx'']
      nlinarith [h3.1]
  · have hcy : cellCentre 0 y =
        cellCentre 0 z + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * w i) := by
      conv_lhs => rw [← add_siteOfCoords_cellDisplacement z y]
      exact cellCentre_add 0 (Nat.zero_le _) z w
    rw [hcy, add_assoc, ← siteOfCoords_add]
    unfold patchSite
    congr 2
    funext i
    simp only [hx'', Pi.add_apply, Nat.sub_zero]
    have e1 : σ i * (cellSideLength F * (σ i * w i) + σ i * h' i + m - m) =
        (σ i * σ i) * (cellSideLength F * w i + h' i) := by ring
    show σ i * (cellSideLength F * (σ i * w i) + σ i * h' i + m - (cellSideLength F - 1) / 2) = _
    rw [← hm, e1, hee i, one_mul]
    simp [cellSideLength]
end PatchLocality
end BlockAverages
end YangMills.Construction
end
