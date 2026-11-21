import YangMills.Construction.ColdChainAtEveryLevel.FramesOfAPatch
import YangMills.Construction.ColdChainAtEveryLevel.FramesOfTwoPatches
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages PatchPoints GaugeMap PatchFrames LatticeFractionalIntegration FiniteDifferences
namespace PatchFrameComparison
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem cellSupDist_triangle (x y w : F.Cell) : cellSupDist x w ≤ cellSupDist x y + cellSupDist y w := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
def stepVector (st : PathStep) : Lattice4 := fun i => (if st.2 then 1 else -1) * (basisVector st.1) i
theorem stepDisplacement_zero_eq (st : PathStep) :
    stepDisplacement (F := F) 0 st = siteOfCoords 0 (stepVector st) := by
  funext i
  rcases st with ⟨k, b⟩
  cases b <;> simp [stepDisplacement, unitStep, siteOfCoords, stepVector, basisVector]
theorem abs_stepVector_le_one (st : PathStep) (i : Fin 4) : |stepVector st i| ≤ 1 := by
  rcases st with ⟨k, b⟩
  by_cases h : i = k
  · subst h
    cases b <;> simp [stepVector, basisVector]
  · cases b <;> simp [stepVector, basisVector, h]
theorem patchChart_add_stepDisplacement (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {x : F.Site 0} {st : PathStep} (ha : patchChart S z x ∈ patchDomain S z) (i : Fin 4) :
    patchChart S z (x + stepDisplacement 0 st) i = patchChart S z x i + closedOrthant S z i * stepVector st i := by
  have hL := hodd.pos
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  set d : ℤ := ((x - cellCentre 0 z) i).valMinAbs with hd
  have hr := patchDomain_coord_bounds ha i
  have ea : patchChart S z x i = closedOrthant S z i * d + (cellSideLength F - 1) / 2 := rfl
  have hdb : |d| < 24 * cellSideLength F := by
    have h2 : |closedOrthant S z i * d| = |d| := by rw [abs_mul, abs_closedOrthant he, one_mul]
    rw [← h2, abs_lt]
    rw [ea] at hr
    constructor <;> omega
  have hsb := abs_le.1 (abs_stepVector_le_one st i)
  have e : (x + stepDisplacement 0 st - cellCentre 0 z : F.Site 0) i =
      ((d + stepVector st i : ℤ) : ZMod (F.period 0 i)) := by
    rw [stepDisplacement_zero_eq, Int.cast_add, hd, ZMod.coe_valMinAbs]
    simp only [Pi.sub_apply, Pi.add_apply, siteOfCoords]
    ring
  have hb : |d + stepVector st i| < 32 * cellSideLength F := by
    obtain ⟨h2, h3⟩ := abs_lt.1 hdb
    rw [abs_lt]
    constructor <;> omega
  show closedOrthant S z i * ((x + stepDisplacement 0 st - cellCentre 0 z : F.Site 0) i).valMinAbs +
    (cellSideLength F - 1) / 2 = _
  rw [e, valMinAbs_of_abs_lt hamb hL i hb, ea]
  ring
theorem supNorm_patchChart_step (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {x : F.Site 0} {st : PathStep} (ha : patchChart S z x ∈ patchDomain S z) :
    supNorm (patchChart S z (x + stepDisplacement 0 st) - patchChart S z x) = 1 := by
  have e : ∀ i, (patchChart S z (x + stepDisplacement 0 st) - patchChart S z x) i =
      closedOrthant S z i * stepVector st i := by
    intro i
    simp only [Pi.sub_apply, patchChart_add_stepDisplacement hamb hodd he ha i]
    ring
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    rw [e i]
    have h1 := abs_stepVector_le_one st i
    have h2 : |closedOrthant S z i * stepVector st i| ≤ 1 := by
      rw [abs_mul, abs_closedOrthant he, one_mul]; exact h1
    have h3 := abs_le.1 h2
    omega
  · have h := Finset.le_sup
      (f := fun i => ((patchChart S z (x + stepDisplacement 0 st) - patchChart S z x) i).natAbs)
      (Finset.mem_univ st.1)
    refine le_trans ?_ h
    show 1 ≤ ((patchChart S z (x + stepDisplacement 0 st) - patchChart S z x) st.1).natAbs
    rw [e st.1]
    have h1 : |stepVector st st.1| = 1 := by
      rcases st with ⟨k, b⟩
      cases b <;> simp [stepVector, basisVector]
    have h2 : |closedOrthant S z st.1 * stepVector st st.1| = 1 := by
      rw [abs_mul, abs_closedOrthant he, one_mul, h1]
    have h3 : closedOrthant S z st.1 * stepVector st st.1 ≠ 0 := by
      intro h0
      rw [h0] at h2
      simp at h2
    omega
def IsNearSite (S : Finset F.Cell) (z : F.Cell) (x : F.Site 0) : Prop :=
  ∃ y ∈ S, cellSupDist z y ≤ 10 ∧ ∃ h ∈ centredCube (F.blockSide ^ F.top), x = cellCentre 0 y + siteOfCoords 0 h
theorem IsNearSite.patchChart_mem (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {x : F.Site 0} (h : IsNearSite S z x) : patchChart S z x ∈ patchDomain S z := by
  obtain ⟨y, hy, hd, h, hh, rfl⟩ := h
  exact patchChart_mem_patchDomain hamb hodd he hy hd hh
theorem norm_sub_le_of_mul_eq {A B P Q : UnitQuaternion} (h : A * P = Q * B) :
    ‖(A : ℍ[ℝ]) - (B : ℍ[ℝ])‖ ≤ ‖(P : ℍ[ℝ]) - 1‖ + ‖(Q : ℍ[ℝ]) - 1‖ := by
  have h' : (A : ℍ[ℝ]) * (P : ℍ[ℝ]) = (Q : ℍ[ℝ]) * (B : ℍ[ℝ]) :=
    congrArg (fun g : UnitQuaternion => (g : ℍ[ℝ])) h
  have e : (A : ℍ[ℝ]) - (B : ℍ[ℝ]) = - ((A : ℍ[ℝ]) * ((P : ℍ[ℝ]) - 1)) + ((Q : ℍ[ℝ]) - 1) * (B : ℍ[ℝ]) := by
    rw [mul_sub, sub_mul, h']
    simp only [mul_one, one_mul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
theorem norm_patchFrameTransition_step_le {V : F.GaugeField F.top} {z z' : F.Cell}
    {R R' : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ} (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (he' : ∀ i, closedOrthant S z' i = 1 ∨ closedOrthant S z' i = -1)
    (hf : IsPatchFrame S V z R Cs r) (hf' : IsPatchFrame S V z' R' Cs r) (hr : 1 ≤ r * cellSideLength F)
    {x : F.Site 0} {st : PathStep} (h1 : IsNearSite S z x) (h2 : IsNearSite S z (x + stepDisplacement 0 st))
    (h1' : IsNearSite S z' x) (h2' : IsNearSite S z' (x + stepDisplacement 0 st)) :
    ‖((patchFrameTransition S V z z' x : UnitQuaternion) : ℍ[ℝ]) -
        ((patchFrameTransition S V z z' (x + stepDisplacement 0 st) : UnitQuaternion) : ℍ[ℝ])‖ ≤
      2 * (Cs / (cellSideLength F : ℝ)) := by
  have m1 := h1.patchChart_mem hamb hodd he
  have m2 := h2.patchChart_mem hamb hodd he
  have m1' := h1'.patchChart_mem hamb hodd he'
  have m2' := h2'.patchChart_mem hamb hodd he'
  have l1 := supNorm_patchChart_step hamb hodd he (st := st) m1
  have l1' := supNorm_patchChart_step hamb hodd he' (st := st) m1'
  have hd : ((supNorm (patchChart S z (x + stepDisplacement 0 st) - patchChart S z x) : ℕ) : ℝ) ≤
      r * cellSideLength F := by
    rw [l1]; simpa using hr
  have hd' : ((supNorm (patchChart S z' (x + stepDisplacement 0 st) - patchChart S z' x) : ℕ) : ℝ) ≤
      r * cellSideLength F := by
    rw [l1']; simpa using hr
  have k1 := hf.leadingTransport_eq _ m1 _ m2 hd
  have k2 := hf'.leadingTransport_eq _ m1' _ m2' hd'
  have n1 := hf.norm_sub_one_le _ m1 _ m2 hd
  have n2 := hf'.norm_sub_one_le _ m1' _ m2' hd'
  rw [l1] at n1
  rw [l1'] at n2
  rw [patchSite_patchChart he, patchSite_patchChart he] at k1
  rw [patchSite_patchChart he', patchSite_patchChart he'] at k2
  have key : patchFrameTransition S V z z' x * R (patchChart S z x) (patchChart S z (x + stepDisplacement 0 st)) =
      R' (patchChart S z' x) (patchChart S z' (x + stepDisplacement 0 st)) *
        patchFrameTransition S V z z' (x + stepDisplacement 0 st) := by
    have k3 := k1.symm.trans k2
    simp only [patchFrameTransition]
    generalize R (patchChart S z x) (patchChart S z (x + stepDisplacement 0 st)) = P at k3 ⊢
    generalize R' (patchChart S z' x) (patchChart S z' (x + stepDisplacement 0 st)) = Q at k3 ⊢
    generalize frameChange S V z x = a at k3 ⊢
    generalize frameChange S V z' x = a' at k3 ⊢
    generalize frameChange S V z (x + stepDisplacement 0 st) = b at k3 ⊢
    generalize frameChange S V z' (x + stepDisplacement 0 st) = b' at k3 ⊢
    have k4 : a * P = a' * Q * b'⁻¹ * b := by
      rw [← k3]
      group
    calc a'⁻¹ * a * P = a'⁻¹ * (a * P) := by group
      _ = a'⁻¹ * (a' * Q * b'⁻¹ * b) := by rw [k4]
      _ = Q * (b'⁻¹ * b) := by group
  refine (norm_sub_le_of_mul_eq key).trans ?_
  have e1 : ((1 : ℕ) : ℝ) / (cellSideLength F : ℝ) = 1 / (cellSideLength F : ℝ) := by simp
  rw [e1] at n1 n2
  have e2 : Cs * (1 / (cellSideLength F : ℝ)) = Cs / (cellSideLength F : ℝ) := by ring
  rw [e2] at n1 n2
  linarith
def IsWalkable (S : Finset F.Cell) (z₀ : F.Cell) (b : Lattice4) : Prop :=
  b ∈ patchDomain S z₀ ∧ ∀ i, -(5 * cellSideLength F) ≤ b i ∧ b i ≤ 6 * cellSideLength F
theorem patchSite_add_basisVector (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (b : Lattice4) (i : Fin 4) :
    patchSite S z (b + basisVector i) = patchSite S z b + stepDisplacement 0 (i, decide (closedOrthant S z i = 1)) := by
  have hs : stepDisplacement (F := F) 0 (i, decide (closedOrthant S z i = 1)) =
      siteOfCoords 0 (fun k => closedOrthant S z k * basisVector i k) := by
    rw [stepDisplacement_zero_eq]
    congr 1
    funext k
    rcases he i with h | h
    · by_cases hk : k = i
      · subst hk
        simp [stepVector, h]
      · simp [stepVector, basisVector, hk]
    · by_cases hk : k = i
      · subst hk
        simp [stepVector, h]
      · simp [stepVector, basisVector, hk]
  rw [hs]
  unfold patchSite
  rw [add_assoc, ← siteOfCoords_add]
  congr 2
  funext k
  simp only [Pi.add_apply]
  ring
theorem IsWalkable.exists_cell (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m) {z₀ : F.Cell}
    (he : ∀ i, closedOrthant S z₀ i = 1 ∨ closedOrthant S z₀ i = -1) {b : Lattice4} (hb : IsWalkable S z₀ b) :
    ∃ y ∈ S, cellSupDist y z₀ ≤ 6 ∧ ∃ h ∈ centredCube (F.blockSide ^ F.top),
      patchSite S z₀ b = cellCentre 0 y + siteOfCoords 0 h := by
  have hL := hodd.pos
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  obtain ⟨y, h, hy, -, hh, e⟩ := exists_cell_of_mem_patchDomain hamb hodd hreg hm hb.1
  refine ⟨y, hy, ?_, h, hh, e⟩
  have hc : enclosingCell (patchSite S z₀ b) = y := by
    rw [e]
    exact enclosingCell_cellCentre_add hodd y h (by simpa using hh)
  rw [← hc]
  refine cellSupDist_enclosingCell_le hodd _ z₀ 6 fun i => ?_
  have e1 : (patchSite S z₀ b - cellCentre 0 z₀ : F.Site 0) i =
      ((closedOrthant S z₀ i * (b i - (cellSideLength F - 1) / 2) : ℤ) : ZMod (F.period 0 i)) := by
    simp [patchSite, siteOfCoords]
  have hbi := hb.2 i
  have hbd : |closedOrthant S z₀ i * (b i - (cellSideLength F - 1) / 2)| ≤ 6 * cellSideLength F := by
    rw [abs_mul, abs_closedOrthant he, one_mul, abs_le]
    constructor <;> omega
  have hlt : |closedOrthant S z₀ i * (b i - (cellSideLength F - 1) / 2)| < 32 * cellSideLength F := by omega
  rw [e1, valMinAbs_of_abs_lt hamb hL i hlt]
  have : ((((closedOrthant S z₀ i * (b i - (cellSideLength F - 1) / 2)).natAbs : ℕ) : ℤ)) ≤
      ((6 * F.blockSide ^ F.top : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    push_cast
    rw [show ((F.blockSide : ℤ) ^ F.top) = cellSideLength F from rfl]
    exact hbd
  exact_mod_cast this
theorem isNearSite_of_mem_cell {z y z₀ : F.Cell} (hy : y ∈ S) (hzy : cellSupDist y z₀ ≤ 6)
    (hz : cellSupDist z₀ z ≤ 2) {x : F.Site 0} {h : Lattice4} (hh : h ∈ centredCube (F.blockSide ^ F.top))
    (e : x = cellCentre 0 y + siteOfCoords 0 h) : IsNearSite S z x := by
  refine ⟨y, hy, ?_, h, hh, e⟩
  rw [cellSupDist_symm]
  exact (cellSupDist_triangle y z₀ z).trans (by omega)
theorem norm_patchFrameTransition_walk_le {V : F.GaugeField F.top} {z z' z₀ : F.Cell} {K : ℝ}
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m) (he₀ : ∀ i, closedOrthant S z₀ i = 1 ∨ closedOrthant S z₀ i = -1)
    (hstep : ∀ x st, IsNearSite S z x → IsNearSite S z (x + stepDisplacement 0 st) → IsNearSite S z' x →
      IsNearSite S z' (x + stepDisplacement 0 st) →
      ‖((patchFrameTransition S V z z' x : UnitQuaternion) : ℍ[ℝ]) -
        ((patchFrameTransition S V z z' (x + stepDisplacement 0 st) : UnitQuaternion) : ℍ[ℝ])‖ ≤ K)
    (hz : cellSupDist z₀ z ≤ 2) (hz' : cellSupDist z₀ z' ≤ 2) (t : Lattice4)
    (ht : ∀ i, t i = 6 * cellSideLength F) :
    ∀ (n : ℕ) (b : Lattice4), IsWalkable S z₀ b → (∀ i, b i ≤ t i) → ∑ i, (t i - b i).toNat = n →
      ‖((patchFrameTransition S V z z' (patchSite S z₀ b) : UnitQuaternion) : ℍ[ℝ]) -
        ((patchFrameTransition S V z z' (patchSite S z₀ t) : UnitQuaternion) : ℍ[ℝ])‖ ≤ n * K := by
  intro n
  induction n with
  | zero =>
    intro b _ hle hs
    have hbt : b = t := by
      funext i
      have h0 := (Finset.sum_eq_zero_iff.1 hs) i (Finset.mem_univ i)
      have := hle i
      omega
    simp [hbt]
  | succ n ih =>
    intro b hb hle hs
    obtain ⟨i, hi⟩ : ∃ i, b i < t i := by
      by_contra hc
      simp only [not_exists, not_lt] at hc
      have : ∑ i, (t i - b i).toNat = 0 := Finset.sum_eq_zero fun i _ => by
        have := hc i
        omega
      omega
    have hL := hodd.pos
    have hN := cellSideLength_pos (F := F) hL
    have hb' : IsWalkable S z₀ (b + basisVector i) := by
      obtain ⟨hp, hr⟩ := hb
      have hu : ∀ k, (b + basisVector i) k = b k + (if k = i then 1 else 0) := by
        intro k
        simp [basisVector, Pi.single_apply]
      refine ⟨?_, fun k => ?_⟩
      · obtain ⟨h1, c, hc, hc2⟩ := Finset.mem_filter.1 hp
        refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun k => ?_, c, hc, fun k => ?_⟩
        · rw [Finset.mem_Icc, hu k]
          have h2 := hr k
          split_ifs <;> constructor <;> omega
        · rw [hu k]
          have := hc2 k
          split_ifs <;> omega
      · rw [hu k]
        have h2 := hr k
        have h3 := hle k
        have h4 := ht k
        by_cases hk : k = i
        · subst hk
          simp only [if_true]
          constructor <;> omega
        · simp only [if_neg hk, add_zero]
          exact h2
    have hle' : ∀ k, (b + basisVector i) k ≤ t k := by
      intro k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, basisVector, Pi.single_eq_same]
        omega
      · simp only [Pi.add_apply, basisVector, Pi.single_apply, if_neg hk, add_zero]
        exact hle k
    have hs' : ∑ k, (t k - (b + basisVector i) k).toNat = n := by
      have e1 : ∑ k, (t k - b k).toNat = (t i - b i).toNat + ∑ k ∈ Finset.univ.erase i, (t k - b k).toNat :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      have e2 : ∑ k, (t k - (b + basisVector i) k).toNat =
          (t i - (b + basisVector i) i).toNat + ∑ k ∈ Finset.univ.erase i, (t k - (b + basisVector i) k).toNat :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      have e3 : ∑ k ∈ Finset.univ.erase i, (t k - (b + basisVector i) k).toNat =
          ∑ k ∈ Finset.univ.erase i, (t k - b k).toNat := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≠ i := Finset.ne_of_mem_erase hk
        simp [basisVector, hk']
      have e4 : (b + basisVector i) i = b i + 1 := by simp [basisVector]
      rw [e2, e3, e4]
      rw [e1] at hs
      omega
    have h1 := ih _ hb' hle' hs'
    obtain ⟨y, hy, hd, h, hh, e⟩ := hb.exists_cell hamb hodd hreg hm he₀
    obtain ⟨y', hy', hd', h', hh', e'⟩ := hb'.exists_cell hamb hodd hreg hm he₀
    rw [patchSite_add_basisVector he₀] at e' h1
    have h2 := hstep (patchSite S z₀ b) (i, decide (closedOrthant S z₀ i = 1))
      (isNearSite_of_mem_cell hy hd hz hh e) (isNearSite_of_mem_cell hy' hd' hz hh' e')
      (isNearSite_of_mem_cell hy hd hz' hh e) (isNearSite_of_mem_cell hy' hd' hz' hh' e')
    have h3 := norm_sub_le_norm_sub_add_norm_sub
      ((patchFrameTransition S V z z' (patchSite S z₀ b) : UnitQuaternion) : ℍ[ℝ])
      ((patchFrameTransition S V z z' (patchSite S z₀ b + stepDisplacement 0 (i, decide (closedOrthant S z₀ i = 1))) :
        UnitQuaternion) : ℍ[ℝ])
      ((patchFrameTransition S V z z' (patchSite S z₀ t) : UnitQuaternion) : ℍ[ℝ])
    push_cast
    nlinarith
theorem mem_cellSites_iff_exists (hodd : Odd F.blockSide) {y : F.Cell} {x : F.Site 0} (hx : x ∈ cellSites S y) :
    y ∈ S ∧ ∃ h ∈ centredCube (F.blockSide ^ F.top), x = cellCentre 0 y + siteOfCoords 0 h := by
  classical
  obtain ⟨hs, hc⟩ := Finset.mem_filter.1 hx
  obtain ⟨y', hy', h, hh, rfl⟩ := mem_sitesOfCells.1 hs
  have e : y' = y := by
    rw [← hc]
    exact (enclosingCell_cellCentre_add hodd y' h hh).symm
  subst e
  exact ⟨hy', h, by simpa using hh, rfl⟩
theorem patchChart_cellCentre_add_bounds (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} (hd : cellSupDist z y ≤ 5) {h : Lattice4} (hh : h ∈ centredCube (F.blockSide ^ F.top)) (i : Fin 4) :
    -(5 * cellSideLength F) ≤ patchChart S z (cellCentre 0 y + siteOfCoords 0 h) i ∧
      patchChart S z (cellCentre 0 y + siteOfCoords 0 h) i ≤ 6 * cellSideLength F := by
  have hL := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  set o : Lattice4 := cellDisplacement z y with ho
  have hob : |o i| ≤ 5 := by
    have h2 := natAbs_valMinAbs_le_cellSupDist y z i
    rw [cellSupDist_symm] at h2
    have h3 : (o i).natAbs ≤ 5 := h2.trans hd
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h3
  have hyz : y = z + siteOfCoords F.top o := eq_add_siteOfCoords_cellDisplacement z y
  have hc := cellCentre_add 0 (Nat.zero_le _) z o
  rw [← hyz] at hc
  have hcs : (F.blockSide : ℤ) ^ (F.top - 0) = cellSideLength F := by simp [cellSideLength]
  rw [hcs] at hc
  have hhb := ((mem_centredCube_iff h).1 hh) i
  have e : (cellCentre 0 y + siteOfCoords 0 h - cellCentre 0 z : F.Site 0) i =
      ((cellSideLength F * o i + h i : ℤ) : ZMod (F.period 0 i)) := by
    rw [hc]
    simp [siteOfCoords]
    ring
  have h2 : |cellSideLength F * o i| ≤ cellSideLength F * 5 := by
    rw [abs_mul, abs_of_pos hN]
    exact mul_le_mul_of_nonneg_left hob hN.le
  have h4 := abs_le.1 h2
  have hb : |cellSideLength F * o i + h i| < 32 * cellSideLength F := by
    rw [abs_lt]
    constructor <;> omega
  have hco : patchChart S z (cellCentre 0 y + siteOfCoords 0 h) i =
      closedOrthant S z i * (cellSideLength F * o i + h i) + (cellSideLength F - 1) / 2 := by
    simp only [patchChart]
    rw [e, valMinAbs_of_abs_lt hamb hL i hb]
  rw [hco]
  rcases he i with hs | hs <;> rw [hs] <;> constructor <;> omega
theorem patchFrameComparison_of_patchFrameExistence (hF : patchFrameExistenceStatement) :
    patchFrameComparisonStatement := by
  obtain ⟨C, r, c, hC, hr, hc, hFr⟩ := hF
  refine ⟨96 * C, c, ⌈1 / r⌉₊ + 1, by positivity, hc, ?_⟩
  intro F m S hodd hL1 hamb hm hreg s V hs hsc hcold z₀ hz₀ z hz z' hz'
  classical
  have hzS : z ∈ S := (Finset.mem_filter.1 hz).1
  have hzS' : z' ∈ S := (Finset.mem_filter.1 hz').1
  have hzd : cellSupDist z₀ z ≤ 2 := (Finset.mem_filter.1 hz).2
  have hzd' : cellSupDist z₀ z' ≤ 2 := (Finset.mem_filter.1 hz').2
  have hL := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  have hm32 : 32 ≤ m := by omega
  obtain ⟨he₀, hcl₀⟩ := closedOrthant_spec (S := S) hreg hm32 z₀
  obtain ⟨he, -⟩ := closedOrthant_spec (S := S) hreg hm32 z
  obtain ⟨he', -⟩ := closedOrthant_spec (S := S) hreg hm32 z'
  obtain ⟨R, hR⟩ := hFr F m S hodd hamb (by omega) hreg s V hs hsc hcold z hzS
  obtain ⟨R', hR'⟩ := hFr F m S hodd hamb (by omega) hreg s V hs hsc hcold z' hzS'
  have hrN : 1 ≤ r * cellSideLength F := by
    have h2 : (1 / r) ≤ (F.blockSide : ℝ) := by
      have h3 := Nat.le_ceil (1 / r)
      have h4 : ((⌈1 / r⌉₊ + 1 : ℕ) : ℝ) ≤ F.blockSide := by exact_mod_cast hL1
      push_cast at h4
      linarith
    have h3 : (F.blockSide : ℝ) ≤ cellSideLength F := by
      have h4 : F.blockSide ≤ F.blockSide ^ F.top := Nat.le_self_pow (by simp) _
      have h5 : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
      have h6 : ((F.blockSide : ℤ)) ≤ cellSideLength F := by rw [← h5]; exact_mod_cast h4
      exact_mod_cast h6
    have h4 : 1 / r ≤ cellSideLength F := h2.trans h3
    rw [div_le_iff₀ hr] at h4
    linarith
  set K : ℝ := 2 * (C * s / (cellSideLength F : ℝ)) with hKd
  have hK : 0 ≤ K := by positivity
  have hstep : ∀ x st, IsNearSite S z x → IsNearSite S z (x + stepDisplacement 0 st) → IsNearSite S z' x →
      IsNearSite S z' (x + stepDisplacement 0 st) →
      ‖((patchFrameTransition S V z z' x : UnitQuaternion) : ℍ[ℝ]) -
        ((patchFrameTransition S V z z' (x + stepDisplacement 0 st) : UnitQuaternion) : ℍ[ℝ])‖ ≤ K :=
    fun x st a1 a2 a3 a4 => norm_patchFrameTransition_step_le hamb hodd he he' hR hR' hrN a1 a2 a3 a4
  set t : Lattice4 := fun _ => 6 * cellSideLength F with ht
  refine ⟨patchFrameTransition S V z z' (patchSite S z₀ t), fun y hy x hx => ?_, fun y hy y' hy' x hx st hx' => ?_⟩
  · obtain ⟨hyS, h, hh, rfl⟩ := mem_cellSites_iff_exists hodd hx
    have hyd : cellSupDist z₀ y ≤ 5 := (Finset.mem_filter.1 hy).2
    set x : F.Site 0 := cellCentre 0 y + siteOfCoords 0 h with hxd
    have hmem : patchChart S z₀ x ∈ patchDomain S z₀ := patchChart_mem_patchDomain hamb hodd he₀ hyS (by omega) hh
    have hbd : ∀ i, -(5 * cellSideLength F) ≤ patchChart S z₀ x i ∧ patchChart S z₀ x i ≤ 6 * cellSideLength F :=
      patchChart_cellCentre_add_bounds hamb hodd he₀ hyd hh
    have hgood : IsWalkable S z₀ (patchChart S z₀ x) := ⟨hmem, hbd⟩
    have hw := norm_patchFrameTransition_walk_le (V := V) (z := z) (z' := z') hamb hodd hreg hm32 he₀ hstep
      hzd hzd' t (fun _ => rfl) _ _ hgood (fun i => (hbd i).2) rfl
    rw [patchSite_patchChart he₀] at hw
    refine hw.trans ?_
    have hn : ((∑ i, (t i - patchChart S z₀ x i).toNat : ℕ) : ℝ) ≤ 44 * (cellSideLength F : ℝ) := by
      have h1 : ∀ i, (((t i - patchChart S z₀ x i).toNat : ℕ) : ℝ) ≤ 11 * (cellSideLength F : ℝ) := by
        intro i
        have h2 := hbd i
        have htv : t i = 6 * cellSideLength F := rfl
        have h3 : t i - patchChart S z₀ x i ≤ 11 * cellSideLength F := by omega
        have h4 : 0 ≤ t i - patchChart S z₀ x i := by omega
        have h5 : (((t i - patchChart S z₀ x i).toNat : ℕ) : ℤ) = t i - patchChart S z₀ x i :=
          Int.toNat_of_nonneg h4
        have h6 : (((t i - patchChart S z₀ x i).toNat : ℕ) : ℤ) ≤ 11 * cellSideLength F := by
          rw [h5]; exact h3
        exact_mod_cast h6
      push_cast
      refine (Finset.sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
      simp
      ring
    have hCs : 0 ≤ C * s := by positivity
    calc _ ≤ (44 * (cellSideLength F : ℝ)) * K := mul_le_mul_of_nonneg_right hn hK
      _ = 88 * (C * s) := by
        rw [hKd]
        field_simp
        ring
      _ ≤ 96 * C * s := by nlinarith
  · obtain ⟨hyS, h, hh, e⟩ := mem_cellSites_iff_exists hodd hx
    obtain ⟨hyS', h', hh', e'⟩ := mem_cellSites_iff_exists hodd hx'
    have hyd : cellSupDist y z₀ ≤ 6 := by
      rw [cellSupDist_symm]
      have := (Finset.mem_filter.1 hy).2
      omega
    have hyd' : cellSupDist y' z₀ ≤ 6 := by
      rw [cellSupDist_symm]
      have := (Finset.mem_filter.1 hy').2
      omega
    refine (hstep x st (isNearSite_of_mem_cell hyS hyd hzd hh e) (isNearSite_of_mem_cell hyS' hyd' hzd hh' e')
      (isNearSite_of_mem_cell hyS hyd hzd' hh e) (isNearSite_of_mem_cell hyS' hyd' hzd' hh' e')).trans ?_
    have hCs : 0 ≤ C * s / (cellSideLength F : ℝ) := by positivity
    rw [hKd]
    have e2 : 96 * C * s / (cellSideLength F : ℝ) = 96 * (C * s / (cellSideLength F : ℝ)) := by ring
    rw [e2]
    linarith
end PatchFrameComparison
end YangMills.Construction
end
