import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceForm
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
import YangMills.Construction.ColdChainAtEveryLevel.CarriedFormsOfTheLevels
set_option autoImplicit false

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open YangMills.Construction.GaugeMap
variable {F : BlockFrame}
def cellBumpSection (S : Finset F.Cell) (V : F.GaugeField F.top) (b : F.Cell → ℍ[ℝ]) : F.Site 0 → ℍ[ℝ] :=
  fun x => ∑ y ∈ S, normalizedBump S x y • adjointAction (frameChange S V y x) (b y)
def cellBumpBoundsStatement : Prop :=
  ∃ (c C : ℝ) (L1 : ℕ), 0 < c ∧ 0 < C ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    L1 ≤ F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m → ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      ∀ (b : F.Cell → ℍ[ℝ]) (B : ℝ), (∀ y ∈ S, ‖b y‖ ≤ B) →
        (∀ y ∈ S, frameCellMean S V y (cellBumpSection S V b) = b y) ∧
        (∀ z ∈ S, cellSiteNorm 4 S (fun _ => 1) (cellBumpSection S V b) z ≤
          C * (cellSideLength F : ℝ) * ‖b z‖) ∧
        (∀ z ∈ S, cellSiteNorm 12 S (fun _ => 1) (cellBumpSection S V b) z ≤
          C * (cellSideLength F : ℝ) ^ (1 / 3 : ℝ) * ‖b z‖) ∧
        (∀ z ∈ S, cellBondNorm 3 S (fun _ => 1)
          (covariantDiff (referenceFieldChain S V 0) (cellBumpSection S V b)) z ≤
            C * (cellSideLength F : ℝ) ^ (1 / 3 : ℝ) * B) ∧
        ∀ z ∈ S, cellPlaquetteNorm (12 / 7) S (fun _ => 1)
          (fun p => adjointAction (plaquetteHolonomy (referenceFieldChain S V 0) p) (cellBumpSection S V b p.1) -
            cellBumpSection S V b p.1) z ≤ C * s * (cellSideLength F : ℝ) ^ (1 / 3 : ℝ) * B
end YangMills.Construction.BlockAverages
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace CellBumps
open BlockAverages GaugeMap LatticeFractionalIntegration LatticePaths
variable {F : BlockFrame}
theorem adjointAction_mul (g h : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction (g * h) w = adjointAction g (adjointAction h w) := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_mul <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem adjointAction_sub (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p - q) = adjointAction g p - adjointAction g q := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (a : ℝ) (p : ℍ[ℝ]) :
    adjointAction g (a • p) = a • adjointAction g p := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem adjointAction_inv_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction g⁻¹ (adjointAction g w) = w := by
  rw [← adjointAction_mul, inv_mul_cancel]
  simp [adjointAction]
theorem norm_adjointAction_sub_self_le (g : UnitQuaternion) (w : ℍ[ℝ]) :
    ‖adjointAction g w - w‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ * ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction_sub_le <;> assumption
theorem sum_rpow_rpow_inv_le {α : Type} (A : Finset α) (g : α → ℝ) (K M q : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hM : (A.card : ℝ) ≤ M) (hg : ∀ a ∈ A, 0 ≤ g a ∧ g a ≤ K) :
    (∑ a ∈ A, g a ^ q) ^ (1 / q) ≤ M ^ (1 / q) * K := by
  have hM0 : 0 ≤ M := le_trans (Nat.cast_nonneg _) hM
  have hKq : 0 ≤ K ^ q := Real.rpow_nonneg hK _
  have h1 : ∑ a ∈ A, g a ^ q ≤ M * K ^ q := by
    calc ∑ a ∈ A, g a ^ q ≤ ∑ _a ∈ A, K ^ q :=
          Finset.sum_le_sum fun a ha => Real.rpow_le_rpow (hg a ha).1 (hg a ha).2 hq.le
      _ = (A.card : ℝ) * K ^ q := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hM hKq
  calc _ ≤ (M * K ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun a ha => Real.rpow_nonneg (hg a ha).1 _) h1 (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hM0 hKq, ← Real.rpow_mul hK, mul_one_div_cancel hq.ne', Real.rpow_one]
theorem pow_four_rpow {N : ℝ} (hN : 0 < N) (q : ℝ) : (N ^ 4) ^ (1 / q) = N ^ (4 * (1 / q)) := by
  rw [← Real.rpow_natCast N 4, ← Real.rpow_mul hN.le]
  norm_num
theorem mul_pow_four_rpow_le {N : ℝ} (hN : 0 < N) {a q : ℝ} (ha : 1 ≤ a) (hq : 1 ≤ q) :
    (a * N ^ 4) ^ (1 / q) ≤ a * N ^ (4 * (1 / q)) := by
  have h0 : 0 < q := by linarith
  rw [Real.mul_rpow (by linarith) (by positivity), pow_four_rpow hN]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hN.le _)
  calc a ^ (1 / q) ≤ a ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ha (by rw [div_le_one h0]; exact hq)
    _ = a := Real.rpow_one a
theorem abs_prod_sub_prod_le (f g : Fin 4 → ℝ) (i : Fin 4) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1)
    (he : ∀ j, j ≠ i → f j = g j) : |∏ j, f j - ∏ j, g j| ≤ |f i - g i| := by
  have e1 := Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)
  have e2 := Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i)
  have e3 : ∏ j ∈ Finset.univ.erase i, g j = ∏ j ∈ Finset.univ.erase i, f j :=
    Finset.prod_congr rfl fun j hj => (he j (Finset.ne_of_mem_erase hj)).symm
  have hP0 : 0 ≤ ∏ j ∈ Finset.univ.erase i, f j := Finset.prod_nonneg fun j _ => (hf j).1
  have hP1 : ∏ j ∈ Finset.univ.erase i, f j ≤ 1 :=
    Finset.prod_le_one (fun j _ => (hf j).1) fun j _ => (hf j).2
  rw [← e1, ← e2, e3, ← sub_mul, abs_mul, abs_of_nonneg hP0]
  exact mul_le_of_le_one_right (abs_nonneg _) hP1
theorem exists_cellSideLength_eq_odd (hodd : Odd F.blockSide) :
    ∃ k : ℤ, 0 ≤ k ∧ cellSideLength F = 2 * k + 1 := by
  obtain ⟨k, hk⟩ := Odd.pow (n := F.top) hodd
  refine ⟨k, by positivity, ?_⟩
  simp only [cellSideLength]
  have : (((F.blockSide ^ F.top : ℕ) : ℤ)) = 2 * (k : ℤ) + 1 := by rw [hk]; push_cast; ring
  rw [← this]
  push_cast
  rfl
theorem neg_le_and_le_iff_two_mul_abs_lt {a k : ℤ} : (-k ≤ a ∧ a ≤ k) ↔ 2 * |a| < 2 * k + 1 := by
  rcases abs_cases a with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
theorem cutoffProfile_lipschitz (t t' : ℝ) :
    |cutoffProfile t - cutoffProfile t'| ≤ cutoffBound * |t - t'| := by
  have hb := cutoffProfile_derivBound
  have hd : Differentiable ℝ cutoffProfile := hb.2.1
  have hb' : ∀ x, |deriv cutoffProfile x| ≤ cutoffBound := hb.2.2.1
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := cutoffProfile) (s := Set.univ) (C := cutoffBound)
    (fun x _ => hd x) (fun x _ => by simpa using hb' x) convex_univ (Set.mem_univ t') (Set.mem_univ t)
  simpa using this
variable (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
omit S V R in
theorem siteOfCoords_add_siteOfCoords {j : ℕ} (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j a + siteOfCoords j b = siteOfCoords j fun i => a i + b i := by apply _root_.YangMills.Construction.BlockLines.siteOfCoords_add_fun <;> assumption
omit S V R in
theorem siteCoords_siteOfCoords {j : ℕ} (a : Fin 4 → ℤ) (i : Fin 4) :
    siteCoords (siteOfCoords (F := F) j a) i = a i % (F.period j i : ℤ) := by apply _root_.YangMills.Construction.BlockLines.siteCoords_siteOfCoords <;> assumption
omit S V R in
theorem period_eq {j : ℕ} (i : Fin 4) :
    (F.period j i : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) := by
  simp [BlockFrame.period]
omit S V R in
theorem enclosingCell_cellCentre_add {j : ℕ} (hodd : Odd F.blockSide) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h) = z := by
  funext i
  have hi := Fintype.mem_piFinset.1 hh i
  rw [Finset.mem_Icc] at hi
  obtain ⟨k, hk⟩ := (Odd.pow (n := F.top - j) hodd)
  have hM : (((F.blockSide ^ (F.top - j) : ℕ) : ℤ)) = 2 * (k : ℤ) + 1 := by
    rw [hk]; push_cast; ring
  have hM' : (F.blockSide : ℤ) ^ (F.top - j) = 2 * (k : ℤ) + 1 := by
    rw [← hM]; push_cast; rfl
  rw [hM] at hi
  have hk2 : ((2 * (k : ℤ) + 1 - 1) / 2) = k := by omega
  rw [hk2] at hi
  simp only [cellCentre, enclosingCell]
  rw [siteOfCoords_add_siteOfCoords]
  change (((siteCoords (siteOfCoords (F := F) j fun i =>
      (F.blockSide : ℤ) ^ (F.top - j) * siteCoords z i + h i) i +
      ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - j) : ℤ) :
        ZMod (F.period F.top i)) = z i
  rw [siteCoords_siteOfCoords, period_eq, hM']
  set M : ℤ := 2 * (k : ℤ) + 1 with hMdef
  set cz : ℤ := siteCoords z i with hcz
  set sd : ℤ := (F.extent i : ℤ) with hsd
  have hcz' : ((cz : ℤ) : ZMod (F.period F.top i)) = z i := ZMod.intCast_zmod_cast (z i)
  set t : ℤ := M * cz + h i with ht
  have e1 : (t % (sd * M) + (M - 1) / 2) / M = cz - sd * (t / (sd * M)) := by
    have hhalf : (M - 1) / 2 = k := by omega
    have hpos : 0 < M := by omega
    rw [Int.emod_def, hhalf]
    have e2 : t - sd * M * (t / (sd * M)) + k = (h i + k) + M * (cz - sd * (t / (sd * M))) := by
      rw [ht]; ring
    rw [e2, Int.add_mul_ediv_left _ _ hpos.ne']
    have e3 : (h i + k) / M = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    rw [e3, zero_add]
  rw [e1]
  have hz0 : ((sd * (t / (sd * M)) : ℤ) : ZMod (F.period F.top i)) = 0 := by
    refine (CharP.intCast_eq_zero_iff (ZMod (F.period F.top i)) (F.period F.top i) _).2 ?_
    rw [period_eq]
    simp only [Nat.sub_self, pow_zero, mul_one]
    exact Dvd.intro _ rfl
  rw [Int.cast_sub, hcz', hz0, sub_zero]
omit V R in
theorem closedOrthant_eq_one_or_neg_one (z : F.Cell) (i : Fin 4) :
    closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 := by
  unfold closedOrthant
  generalize hfind : List.find? _ signVectors = r
  cases r with
  | none => simp
  | some e =>
    have hm := List.mem_of_find?_eq_some hfind
    simp only [Option.getD_some]
    simp only [signVectors, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      fin_cases i <;> simp
omit V R in
theorem signed_offset_mem_centredCube (hodd : Odd F.blockSide) (z : F.Cell) (x : Lattice4)
    (hx : x ∈ cellOffsets F) :
    (fun i => closedOrthant S z i * (x i - (cellSideLength F - 1) / 2)) ∈
      centredCube (F.blockSide ^ (F.top - 0)) := by
  obtain ⟨k, hk⟩ := (Odd.pow (n := F.top) hodd)
  have hM : cellSideLength F = 2 * (k : ℤ) + 1 := by
    simp only [cellSideLength]
    have : (((F.blockSide ^ F.top : ℕ) : ℤ)) = 2 * (k : ℤ) + 1 := by rw [hk]; push_cast; ring
    rw [← this]; push_cast; rfl
  refine Fintype.mem_piFinset.2 fun i => ?_
  have hxi := Fintype.mem_piFinset.1 hx i
  rw [Finset.mem_Ico, hM] at hxi
  rw [Finset.mem_Icc, Nat.sub_zero, hk, hM]
  push_cast
  have h2 : ((2 * (k : ℤ) + 1 - 1) / 2) = k := by omega
  rw [h2]
  rcases closedOrthant_eq_one_or_neg_one S z i with h | h <;> rw [h] <;> omega
omit S V R in
theorem interiorBump_nonneg (s : F.Site 0) (y : F.Cell) : 0 ≤ interiorBump s y :=
  Finset.prod_nonneg fun _ _ => cutoffProfile_nonneg _
omit S V R in
theorem interiorBump_eq_zero_of_ne (hodd : Odd F.blockSide) (y y' : F.Cell) (hne : y ≠ y') (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - 0))) :
    interiorBump (cellCentre 0 y + siteOfCoords 0 h) y' = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hh' := Fintype.mem_piFinset.1 hh i
  rw [Finset.mem_Icc, Nat.sub_zero] at hh'
  obtain ⟨k, hk⟩ := (Odd.pow (n := F.top) hodd)
  have hMn : (((F.blockSide ^ F.top : ℕ) : ℤ)) = 2 * (k : ℤ) + 1 := by rw [hk]; push_cast; ring
  have hM : (F.blockSide : ℤ) ^ F.top = 2 * (k : ℤ) + 1 := by rw [← hMn]; push_cast; rfl
  rw [hMn] at hh'
  have h2 : ((2 * (k : ℤ) + 1 - 1) / 2) = k := by omega
  rw [h2] at hh'
  set cz : ℤ := siteCoords y i with hcz
  set cz' : ℤ := siteCoords y' i with hcz'
  have hyc : ((cz : ℤ) : ZMod (F.period F.top i)) = y i := ZMod.intCast_zmod_cast (y i)
  have hyc' : ((cz' : ℤ) : ZMod (F.period F.top i)) = y' i := ZMod.intCast_zmod_cast (y' i)
  set v : ℤ := ((cellCentre 0 y + siteOfCoords 0 h - cellCentre 0 y' : F.Site 0) i).valMinAbs with hv
  have hvc : ((v : ℤ) : ZMod (F.period 0 i)) =
      (((2 * (k : ℤ) + 1) * cz + h i - (2 * (k : ℤ) + 1) * cz' : ℤ) : ZMod (F.period 0 i)) := by
    rw [hv, ZMod.coe_valMinAbs]
    simp only [cellCentre, Pi.sub_apply, Pi.add_apply, siteOfCoords, Nat.sub_zero, hM]
    push_cast
    rfl
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hvc
  rw [period_eq, Nat.sub_zero, hM] at hq
  set sd : ℤ := (F.extent i : ℤ) with hsd
  set d : ℤ := cz - cz' - sd * q with hd
  have hvd : v = (2 * (k : ℤ) + 1) * d + h i := by
    rw [hd]; linarith
  have hd0 : d ≠ 0 := by
    intro h0
    have e : cz = cz' + sd * q := by rw [hd] at h0; linarith
    apply hi
    rw [← hyc, ← hyc', e, Int.cast_add]
    have hz0 : ((sd * q : ℤ) : ZMod (F.period F.top i)) = 0 := by
      refine (CharP.intCast_eq_zero_iff (ZMod (F.period F.top i)) (F.period F.top i) _).2 ?_
      rw [period_eq]
      simp only [Nat.sub_self, pow_zero, mul_one]
      exact Dvd.intro _ rfl
    rw [hz0, add_zero]
  have habs : (k : ℤ) + 1 ≤ |v| := by
    rcases lt_or_gt_of_ne hd0 with hlt | hgt
    · have : d ≤ -1 := by omega
      have : v ≤ -((k : ℤ) + 1) := by rw [hvd]; nlinarith
      rw [le_abs]; right; linarith
    · have : 1 ≤ d := by omega
      have : (k : ℤ) + 1 ≤ v := by rw [hvd]; nlinarith
      rw [le_abs]; left; exact this
  apply cutoffProfile_eq_zero
  have hside : (cellSideLength F : ℝ) = 2 * (k : ℝ) + 1 := by
    have : cellSideLength F = 2 * (k : ℤ) + 1 := hM
    rw [this]; push_cast; rfl
  have hpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  have habsR : (k : ℝ) + 1 ≤ |(v : ℝ)| := by
    have : (((k : ℤ) + 1 : ℤ) : ℝ) ≤ ((|v| : ℤ) : ℝ) := Int.cast_le.2 habs
    push_cast at this
    exact this
  rw [hside, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2), abs_of_pos hpos,
    le_div_iff₀ hpos]
  nlinarith
omit V R in
theorem interiorBump_le_one (s : F.Site 0) (y : F.Cell) : interiorBump s y ≤ 1 :=
  Finset.prod_le_one (fun _ _ => cutoffProfile_nonneg _) fun _ _ => cutoffProfile_le_one _
def bumpCellMean (S : Finset F.Cell) (y : F.Cell) : ℝ :=
  (1 / (cellSideLength F : ℝ) ^ 4) * ∑ x ∈ cellOffsets F, interiorBump (patchSite S y x) y
omit V R in
theorem normalizedBump_eq (s : F.Site 0) (y : F.Cell) :
    normalizedBump S s y = interiorBump s y / bumpCellMean S y := rfl
omit V R in
theorem bumpCellMean_ge (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hN : 3 ≤ cellSideLength F)
    (y : F.Cell) : 1 / 625 ≤ bumpCellMean S y := by
  classical
  have hL := hodd.pos
  have hNr : (0 : ℝ) < (cellSideLength F : ℝ) := by exact_mod_cast (by omega : 0 < cellSideLength F)
  set k : ℤ := (cellSideLength F - 1) / 2 with hk
  set r : ℤ := cellSideLength F / 5 with hr
  set I : Finset Lattice4 := Fintype.piFinset fun _ : Fin 4 => Finset.Icc (k - r) (k + r) with hI
  have hsub : I ⊆ cellOffsets F := by
    intro x hx
    refine Fintype.mem_piFinset.2 fun i => ?_
    have := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hx i)
    rw [Finset.mem_Ico]
    omega
  have hone : ∀ x ∈ I, interiorBump (patchSite S y x) y = 1 := by
    intro x hx
    refine Finset.prod_eq_one fun i _ => ?_
    have hxi := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hx i)
    have e : (patchSite S y x - cellCentre 0 y) i =
        ((closedOrthant S y i * (x i - k) : ℤ) : ZMod (F.period 0 i)) := by
      simp [patchSite, siteOfCoords, hk]
    have hA : |x i - k| ≤ r := by
      rw [abs_le]
      constructor <;> omega
    have hs : |closedOrthant S y i * (x i - k)| = |x i - k| := by
      rw [abs_mul]
      rcases closedOrthant_eq_one_or_neg_one S y i with h | h <;> rw [h] <;> simp
    have hb : |closedOrthant S y i * (x i - k)| < 32 * cellSideLength F := by
      rw [hs]
      omega
    rw [e, valMinAbs_of_abs_lt hamb hL i hb]
    apply cutoffProfile_eq_one
    have h5 : (5 : ℝ) * |((closedOrthant S y i * (x i - k) : ℤ) : ℝ)| ≤ (cellSideLength F : ℝ) := by
      have : 5 * |closedOrthant S y i * (x i - k)| ≤ cellSideLength F := by
        rw [hs]
        omega
      exact_mod_cast this
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2), abs_of_pos hNr, div_le_iff₀ hNr]
    linarith
  have hcard : (I.card : ℝ) = (2 * (r : ℝ) + 1) ^ 4 := by
    have h1 : (Finset.Icc (k - r) (k + r)).card = (2 * r + 1).toNat := by
      rw [Int.card_Icc]
      congr 1
      ring
    have h2 : I.card = ((2 * r + 1).toNat) ^ 4 := by
      rw [hI, Fintype.card_piFinset]
      simp [h1]
    have h3 : (((2 * r + 1).toNat : ℤ)) = 2 * r + 1 := Int.toNat_of_nonneg (by omega)
    have h4 : (((2 * r + 1).toNat : ℝ)) = 2 * (r : ℝ) + 1 := by
      rw [← Int.cast_natCast, h3]
      push_cast
      ring
    rw [h2]
    push_cast
    rw [h4]
  have hsum : (2 * (r : ℝ) + 1) ^ 4 ≤ ∑ x ∈ cellOffsets F, interiorBump (patchSite S y x) y := by
    calc (2 * (r : ℝ) + 1) ^ 4 = ∑ x ∈ I, interiorBump (patchSite S y x) y := by
          rw [Finset.sum_congr rfl hone, ← hcard]
          simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => interiorBump_nonneg _ _
  have h5 : (cellSideLength F : ℝ) / 5 ≤ 2 * (r : ℝ) + 1 := by
    have : cellSideLength F ≤ 5 * (2 * r + 1) := by omega
    have h' : (cellSideLength F : ℝ) ≤ 5 * (2 * (r : ℝ) + 1) := by exact_mod_cast this
    linarith
  have h6 : ((cellSideLength F : ℝ) / 5) ^ 4 ≤ (2 * (r : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h5 4
  unfold bumpCellMean
  calc (1 : ℝ) / 625 = (1 / (cellSideLength F : ℝ) ^ 4) * ((cellSideLength F : ℝ) / 5) ^ 4 := by
        field_simp
        norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (h6.trans hsum) (by positivity)
omit V R in
theorem normalizedBump_mem_Icc (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hN : 3 ≤ cellSideLength F) (s : F.Site 0) (y : F.Cell) :
    0 ≤ normalizedBump S s y ∧ normalizedBump S s y ≤ 625 := by
  have hD := bumpCellMean_ge S hamb hodd hN y
  have hD0 : 0 < bumpCellMean S y := by linarith
  rw [normalizedBump_eq]
  refine ⟨div_nonneg (interiorBump_nonneg _ _) hD0.le, ?_⟩
  rw [div_le_iff₀ hD0]
  have := interiorBump_le_one s y
  linarith
theorem cellBumpSection_cellCentre_add (hodd : Odd F.blockSide) (b : F.Cell → ℍ[ℝ]) (y : F.Cell) (hy : y ∈ S)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube (F.blockSide ^ (F.top - 0))) :
    cellBumpSection S V b (cellCentre 0 y + siteOfCoords 0 h) =
      normalizedBump S (cellCentre 0 y + siteOfCoords 0 h) y •
        adjointAction (frameChange S V y (cellCentre 0 y + siteOfCoords 0 h)) (b y) := by
  simp only [cellBumpSection]
  refine Finset.sum_eq_single_of_mem y hy fun y' _ hne => ?_
  have h0 := interiorBump_eq_zero_of_ne hodd y y' hne.symm h hh
  simp [normalizedBump, h0]
theorem frameCellMean_cellBumpSection (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hN : 3 ≤ cellSideLength F) (b : F.Cell → ℍ[ℝ]) (y : F.Cell) (hy : y ∈ S) :
    frameCellMean S V y (cellBumpSection S V b) = b y := by
  have hD := bumpCellMean_ge S hamb hodd hN y
  have hD0 : 0 < bumpCellMean S y := by linarith
  have hpoint : ∀ x ∈ cellOffsets F,
      adjointAction (frameChange S V y (patchSite S y x))⁻¹ (cellBumpSection S V b (patchSite S y x)) =
        (interiorBump (patchSite S y x) y / bumpCellMean S y) • b y := by
    intro x hx
    have := cellBumpSection_cellCentre_add S V hodd b y hy _ (signed_offset_mem_centredCube S hodd y x hx)
    have e : cellBumpSection S V b (patchSite S y x) = normalizedBump S (patchSite S y x) y •
        adjointAction (frameChange S V y (patchSite S y x)) (b y) := this
    rw [e, adjointAction_smul, adjointAction_inv_adjointAction]
    rfl
  change (1 / (cellSideLength F : ℝ) ^ 4) • ∑ x ∈ cellOffsets F,
    adjointAction (frameChange S V y (patchSite S y x))⁻¹ (cellBumpSection S V b (patchSite S y x)) = b y
  rw [Finset.sum_congr rfl hpoint, ← Finset.sum_smul, smul_smul]
  have hone : (1 / (cellSideLength F : ℝ) ^ 4) *
      ∑ x ∈ cellOffsets F, interiorBump (patchSite S y x) y / bumpCellMean S y = 1 := by
    rw [← Finset.sum_div, ← mul_div_assoc]
    exact div_self hD0.ne'
  rw [hone, one_smul]
omit V R in
theorem exists_centredCube_of_mem (hodd : Odd F.blockSide) {x : F.Site 0} (hx : x ∈ sitesOfCells S 0) :
    ∃ h ∈ centredCube (F.blockSide ^ (F.top - 0)),
      x = cellCentre 0 (enclosingCell x) + siteOfCoords 0 h ∧ enclosingCell x ∈ S := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  have e := enclosingCell_cellCentre_add hodd y h hh
  refine ⟨h, hh, ?_, ?_⟩
  · rw [e]
  · rw [e]
    exact hy
theorem norm_cellBumpSection_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hN : 3 ≤ cellSideLength F) (b : F.Cell → ℍ[ℝ]) {x : F.Site 0} (hx : x ∈ sitesOfCells S 0) :
    ‖cellBumpSection S V b x‖ ≤ 625 * ‖b (enclosingCell x)‖ := by
  obtain ⟨h, hh, e, hy⟩ := exists_centredCube_of_mem S hodd hx
  have hb := cellBumpSection_cellCentre_add S V hodd b (enclosingCell x) hy h hh
  rw [← e] at hb
  rw [hb, norm_smul, norm_adjointAction, Real.norm_of_nonneg (normalizedBump_mem_Icc S hamb hodd hN x _).1]
  exact mul_le_mul_of_nonneg_right (normalizedBump_mem_Icc S hamb hodd hN x _).2 (norm_nonneg _)
omit V R in
theorem card_le_of_enclosingCell_eq (hodd : Odd F.blockSide) (c : F.Cell) (A : Finset (F.Site 0))
    (hA : ∀ x ∈ A, x ∈ sitesOfCells S 0 ∧ enclosingCell x = c) :
    (A.card : ℝ) ≤ (cellSideLength F : ℝ) ^ 4 := by
  classical
  have hsub : A ⊆ (centredCube (F.blockSide ^ (F.top - 0))).image
      fun h => cellCentre 0 c + siteOfCoords 0 h := by
    intro x hx
    obtain ⟨h1, h2⟩ := hA x hx
    obtain ⟨h, hh, e, _⟩ := exists_centredCube_of_mem S hodd h1
    rw [h2] at e
    exact Finset.mem_image.2 ⟨h, hh, e.symm⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [card_centredCube (hodd.pow (n := F.top - 0))] at h1
  have h2 : (A.card : ℝ) ≤ ((F.blockSide ^ (F.top - 0)) ^ 4 : ℕ) := by exact_mod_cast h1
  refine h2.trans (le_of_eq ?_)
  simp [cellSideLength]
omit V R in
theorem card_pairs_le_of_enclosingCell_eq (hodd : Odd F.blockSide) (c : F.Cell) {β : Type} [Fintype β]
    (A : Finset (F.Site 0 × β))
    (hA : ∀ b ∈ A, b.1 ∈ sitesOfCells S 0 ∧ enclosingCell b.1 = c) :
    (A.card : ℝ) ≤ (Fintype.card β : ℝ) * (cellSideLength F : ℝ) ^ 4 := by
  classical
  have hsub : A ⊆ (A.image Prod.fst) ×ˢ Finset.univ := by
    intro b hb
    exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hb, Finset.mem_univ _⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_univ] at h1
  have h2 := card_le_of_enclosingCell_eq S hodd c (A.image Prod.fst) (by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
    exact hA b hb)
  have h3 : (A.card : ℝ) ≤ ((A.image Prod.fst).card : ℝ) * (Fintype.card β : ℝ) := by exact_mod_cast h1
  calc _ ≤ _ := h3
    _ ≤ (cellSideLength F : ℝ) ^ 4 * (Fintype.card β : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _
omit V R in
theorem interiorBump_cellCentre_add (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) (c : F.Cell)
    (h : Lattice4) (hb : ∀ i, |h i| < 32 * cellSideLength F) :
    interiorBump (cellCentre 0 c + siteOfCoords 0 h) c =
      ∏ i, cutoffProfile (5 / 2 * ((h i : ℤ) : ℝ) / (cellSideLength F : ℝ)) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (cellCentre 0 c + siteOfCoords 0 h - cellCentre 0 c : F.Site 0) i =
      ((h i : ℤ) : ZMod (F.period 0 i)) := by
    simp [siteOfCoords]
  rw [e, valMinAbs_of_abs_lt hamb hL i (hb i)]
omit S V R in
theorem mem_centredCube_iff_two_mul_abs_lt (hodd : Odd F.blockSide) (h : Lattice4) :
    h ∈ centredCube (F.blockSide ^ (F.top - 0)) ↔ ∀ i, 2 * |h i| < cellSideLength F := by
  obtain ⟨k, hk0, hN⟩ := exists_cellSideLength_eq_odd (F := F) hodd
  have hM : (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ)) = cellSideLength F := by simp [cellSideLength]
  rw [mem_centredCube_iff, hM]
  refine forall_congr' fun i => ?_
  rw [hN]
  have e : (2 * k + 1 - 1) / 2 = k := by omega
  rw [e, neg_le_and_le_iff_two_mul_abs_lt]
omit V R in
theorem abs_lt_of_interiorBump_ne_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (c : F.Cell)
    (h : Lattice4) (hh : h ∈ centredCube (F.blockSide ^ (F.top - 0)))
    (hne : interiorBump (cellCentre 0 c + siteOfCoords 0 h) c ≠ 0) (i : Fin 4) :
    25 * |h i| < 9 * cellSideLength F := by
  have hL := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  have hNr : (0 : ℝ) < (cellSideLength F : ℝ) := by exact_mod_cast hN
  have hb : ∀ j, |h j| < 32 * cellSideLength F := by
    intro j
    have := (mem_centredCube_iff_two_mul_abs_lt hodd h).1 hh j
    omega
  rw [interiorBump_cellCentre_add hamb hL c h hb] at hne
  have h1 := Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ i)
  have h2 := abs_lt_of_cutoffProfile_ne_zero h1
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2), abs_of_pos hNr, div_lt_iff₀ hNr] at h2
  have h3 : (25 : ℝ) * |((h i : ℤ) : ℝ)| < 9 * (cellSideLength F : ℝ) := by linarith
  exact_mod_cast h3
omit V R in
theorem cellCentre_add_mem_patch (hodd : Odd F.blockSide) (c : F.Cell) (hc : c ∈ S) (h : Lattice4)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - 0))) :
    cellCentre 0 c + siteOfCoords 0 h ∈ (patchDomain S c).image (patchSite S c) := by
  classical
  obtain ⟨k, hk0, hN⟩ := exists_cellSideLength_eq_odd (F := F) hodd
  have hb := (mem_centredCube_iff_two_mul_abs_lt hodd h).1 hh
  set p : Lattice4 := fun i => closedOrthant S c i * h i + (cellSideLength F - 1) / 2 with hp
  have hsign : ∀ i, closedOrthant S c i * (p i - (cellSideLength F - 1) / 2) = h i := by
    intro i
    simp only [hp]
    rcases closedOrthant_eq_one_or_neg_one S c i with e | e <;> rw [e] <;> ring
  have hpb : ∀ i, 0 ≤ p i ∧ p i < cellSideLength F := by
    intro i
    have h1 := hb i
    have h2 := abs_lt.1 (show |2 * h i| < cellSideLength F by rw [abs_mul]; simpa using h1)
    simp only [hp]
    rcases closedOrthant_eq_one_or_neg_one S c i with e | e <;> rw [e] <;> omega
  refine Finset.mem_image.2 ⟨p, ?_, ?_⟩
  · simp only [patchDomain, Finset.mem_filter]
    refine ⟨Fintype.mem_piFinset.2 fun i => ?_, 0, ?_, fun i => (hpb i).1⟩
    · have := hpb i
      rw [Finset.mem_Icc]
      omega
    · simp only [patchCorners]
      refine Finset.mem_image.2 ⟨c, ?_, ?_⟩
      · simp [cellBall, hc, cellSupDist]
      · funext i
        simp [cellDisplacement]
  · simp only [patchSite]
    congr 2
    funext i
    exact hsign i
omit S V R in
theorem baseSite_zero (x : F.Site 0) : baseSite x = x := by
  simp only [baseSite, pow_zero, one_mul]
  exact siteOfCoords_siteCoords x
omit S V R in
theorem add_basisVector_mem_centredCube (hodd : Odd F.blockSide) (h : Lattice4) (i : Fin 4)
    (hN : 13 ≤ cellSideLength F) (e : ℤ) (he : |e| ≤ 1) (hs : ∀ j, 25 * |h j| < 9 * cellSideLength F) :
    (fun j => h j + e * basisVector i j) ∈ centredCube (F.blockSide ^ (F.top - 0)) := by
  rw [mem_centredCube_iff_two_mul_abs_lt hodd]
  intro j
  have h1 := hs j
  have h2 : |e * basisVector i j| ≤ 1 := by
    rw [abs_mul]
    have : |basisVector i j| ≤ 1 := by
      simp only [basisVector, Pi.single_apply]
      split_ifs <;> simp
    nlinarith [abs_nonneg e, abs_nonneg (basisVector i j)]
  have h3 := abs_add_le (h j) (e * basisVector i j)
  omega
omit V R in
theorem cellCentre_add_siteOfCoords_add (c : F.Cell) (h g : Lattice4) :
    cellCentre 0 c + siteOfCoords 0 h + siteOfCoords 0 g =
      cellCentre 0 c + siteOfCoords 0 fun j => h j + g j := by
  rw [add_assoc, siteOfCoords_add_siteOfCoords]
theorem norm_covariantDiff_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hN : 13 ≤ cellSideLength F) {E : ℝ} (hE : 0 ≤ E)
    (hf : ∀ c ∈ S, ∀ β ∈ innerBonds S 0, baseSite β.1 ∈ (patchDomain S c).image (patchSite S c) →
      baseSite (β.1 + unitStep 0 β.2) ∈ (patchDomain S c).image (patchSite S c) →
      unitDeviation (referenceInPatchFrame S V c 0 β.1 β.2) ≤ E)
    (b : F.Cell → ℍ[ℝ]) {B : ℝ} (hb : ∀ y ∈ S, ‖b y‖ ≤ B) (β : F.Site 0 × Fin 4) (hβ : β ∈ innerBonds S 0) :
    ‖covariantDiff (referenceFieldChain S V 0) (cellBumpSection S V b) β.1 β.2‖ ≤
      625 * (2 * E + 3 * cutoffBound / (cellSideLength F : ℝ)) * B := by
  classical
  obtain ⟨x, i⟩ := β
  have hβ' := Finset.mem_filter.1 hβ
  have hx : x ∈ sitesOfCells S 0 := (Finset.mem_product.1 hβ'.1).1
  have hx' : x + unitStep 0 i ∈ sitesOfCells S 0 := hβ'.2
  have hL := hodd.pos
  have hN3 : 3 ≤ cellSideLength F := by omega
  have hNr : (0 : ℝ) < (cellSideLength F : ℝ) := by exact_mod_cast (by omega : 0 < cellSideLength F)
  have hM1 := one_le_cutoffBound
  obtain ⟨h, hh, ex, hy⟩ := exists_centredCube_of_mem S hodd hx
  obtain ⟨h', hh', ex', hy'⟩ := exists_centredCube_of_mem S hodd hx'
  obtain ⟨y, hyd⟩ : ∃ y, y = enclosingCell x := ⟨_, rfl⟩
  obtain ⟨y', hyd'⟩ : ∃ y', y' = enclosingCell (x + unitStep 0 i) := ⟨_, rfl⟩
  rw [← hyd] at ex hy
  rw [← hyd'] at ex' hy'
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hb y hy)
  have b1 := cellBumpSection_cellCentre_add S V hodd b y hy h hh
  have b2 := cellBumpSection_cellCentre_add S V hodd b y' hy' h' hh'
  rw [← ex] at b1
  rw [← ex'] at b2
  have hnn : 0 ≤ 625 * (2 * E + 3 * cutoffBound / (cellSideLength F : ℝ)) * B := by positivity
  simp only [covariantDiff]
  by_cases hyy : y' = y
  · subst hyy
    have hcb : ∀ g : Lattice4, g ∈ centredCube (F.blockSide ^ (F.top - 0)) →
        ∀ j, |g j| < 32 * cellSideLength F := by
      intro g hg j
      have := (mem_centredCube_iff_two_mul_abs_lt hodd g).1 hg j
      omega
    have hub : ∀ j, |basisVector i j| ≤ 1 := by
      intro j
      simp only [basisVector, Pi.single_apply]
      split_ifs <;> simp
    have hsum : ∀ j, |h j + basisVector i j| < 32 * cellSideLength F := by
      intro j
      have h1 := (mem_centredCube_iff_two_mul_abs_lt hodd h).1 hh j
      have h2 := abs_add_le (h j) (basisVector i j)
      have h3 := hub j
      omega
    have hstep : ∀ j, h' j = h j + basisVector i j := by
      intro j
      have e1 : cellCentre 0 y' + siteOfCoords 0 h' =
          cellCentre 0 y' + siteOfCoords 0 fun j => h j + basisVector i j := by
        rw [← ex', ← cellCentre_add_siteOfCoords_add, ← ex]
        rfl
      have e3 := congrFun (add_left_cancel e1) j
      simp only [siteOfCoords] at e3
      have e4 := congrArg ZMod.valMinAbs e3
      rwa [valMinAbs_of_abs_lt hamb hL j (hcb h' hh' j), valMinAbs_of_abs_lt hamb hL j (hsum j)] at e4
    have p1 : interiorBump x y' =
        ∏ j, cutoffProfile (5 / 2 * ((h j : ℤ) : ℝ) / (cellSideLength F : ℝ)) := by
      rw [← interiorBump_cellCentre_add hamb hL y' h (hcb h hh), ← ex]
    have p2 : interiorBump (x + unitStep 0 i) y' =
        ∏ j, cutoffProfile (5 / 2 * ((h' j : ℤ) : ℝ) / (cellSideLength F : ℝ)) := by
      rw [← interiorBump_cellCentre_add hamb hL y' h' (hcb h' hh'), ← ex']
    have hdψ : |interiorBump (x + unitStep 0 i) y' - interiorBump x y'| ≤
        cutoffBound * (5 / 2 / (cellSideLength F : ℝ)) := by
      rw [p1, p2]
      refine (abs_prod_sub_prod_le _ _ i (fun j => ⟨cutoffProfile_nonneg _, cutoffProfile_le_one _⟩)
        fun j hj => ?_).trans ?_
      · have : basisVector i j = 0 := by simp [basisVector, hj]
        rw [hstep j, this, add_zero]
      · refine (cutoffProfile_lipschitz _ _).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) (by linarith))
        have e : h' i = h i + 1 := by
          rw [hstep i]
          simp [basisVector]
        rw [e]
        push_cast
        rw [show 5 / 2 * ((h i : ℝ) + 1) / (cellSideLength F : ℝ) -
            5 / 2 * (h i : ℝ) / (cellSideLength F : ℝ) = 5 / 2 / (cellSideLength F : ℝ) by ring]
        exact abs_of_pos (by positivity)
    have hD := bumpCellMean_ge S hamb hodd hN3 y'
    have hD0 : 0 < bumpCellMean S y' := by linarith
    set m := normalizedBump S x y' with hm
    set m' := normalizedBump S (x + unitStep 0 i) y' with hm'
    have hmm : |m' - m| ≤ 625 * (cutoffBound * (5 / 2 / (cellSideLength F : ℝ))) := by
      rw [hm, hm', normalizedBump_eq, normalizedBump_eq, ← sub_div, abs_div, abs_of_pos hD0,
        div_le_iff₀ hD0]
      have h5 : 625 * bumpCellMean S y' ≥ 1 := by linarith
      have h6 : 0 ≤ cutoffBound * (5 / 2 / (cellSideLength F : ℝ)) := by positivity
      nlinarith
    have hm'b := normalizedBump_mem_Icc S hamb hodd hN3 (x + unitStep 0 i) y'
    set w := b y' with hw
    set f := frameChange S V y' x with hfd
    set f' := frameChange S V y' (x + unitStep 0 i) with hf'd
    set Rb := referenceFieldChain S V 0 x i with hRb
    set g := referenceInPatchFrame S V y' 0 x i with hg
    have hgm : Rb * f' = f * g := by
      have hgv : g = f⁻¹ * Rb * f' := by
        simp only [hg, referenceInPatchFrame, gaugeTransform, baseSite_zero, inv_inv]
        rfl
      rw [hgv]
      group
    have hT : adjointAction Rb (adjointAction f' w) - adjointAction f w =
        adjointAction f (adjointAction g w - w) := by
      rw [← adjointAction_mul, hgm, adjointAction_mul, adjointAction_sub]
    have hgE : ‖(g : ℍ[ℝ]) - 1‖ ≤ E := by
      refine hf y' hy' (x, i) hβ ?_ ?_
      · simp only [baseSite_zero]
        rw [ex]
        exact cellCentre_add_mem_patch S hodd y' hy' h hh
      · simp only [baseSite_zero]
        rw [ex']
        exact cellCentre_add_mem_patch S hodd y' hy' h' hh'
    have hTn : ‖adjointAction Rb (adjointAction f' w) - adjointAction f w‖ ≤ 2 * E * B := by
      rw [hT, norm_adjointAction]
      refine (norm_adjointAction_sub_self_le g w).trans ?_
      have hw' := hb y' hy'
      have : ‖(g : ℍ[ℝ]) - 1‖ * ‖w‖ ≤ E * B := mul_le_mul hgE hw' (norm_nonneg _) hE
      linarith
    rw [b1, b2, adjointAction_smul]
    have e : m' • adjointAction Rb (adjointAction f' w) - m • adjointAction f w =
        m' • (adjointAction Rb (adjointAction f' w) - adjointAction f w) + (m' - m) • adjointAction f w := by
      simp only [smul_sub, sub_smul]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_adjointAction, Real.norm_of_nonneg hm'b.1, Real.norm_eq_abs]
    have t1 : m' * ‖adjointAction Rb (adjointAction f' w) - adjointAction f w‖ ≤ 625 * (2 * E * B) :=
      mul_le_mul hm'b.2 hTn (norm_nonneg _) (by norm_num)
    have t2 : |m' - m| * ‖w‖ ≤ 625 * (cutoffBound * (5 / 2 / (cellSideLength F : ℝ))) * B :=
      mul_le_mul hmm (hb y' hy') (norm_nonneg _) (by positivity)
    have t3 : 625 * (cutoffBound * (5 / 2 / (cellSideLength F : ℝ))) * B ≤
        625 * (3 * cutoffBound / (cellSideLength F : ℝ)) * B := by
      refine mul_le_mul_of_nonneg_right ?_ hB0
      have : cutoffBound * (5 / 2 / (cellSideLength F : ℝ)) ≤ 3 * cutoffBound / (cellSideLength F : ℝ) := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hNr]
        nlinarith
      linarith
    nlinarith
  · have hz1 : interiorBump x y = 0 := by
      by_contra hne
      have hs := abs_lt_of_interiorBump_ne_zero hamb hodd y h hh (by rw [← ex]; exact hne)
      have hm := add_basisVector_mem_centredCube hodd h i hN 1 (by simp) hs
      have e : x + unitStep 0 i = cellCentre 0 y + siteOfCoords 0 fun j => h j + 1 * basisVector i j := by
        simp only [one_mul]
        rw [← cellCentre_add_siteOfCoords_add, ← ex]
        rfl
      have c1 := enclosingCell_cellCentre_add hodd y _ hm
      rw [← e, ← hyd'] at c1
      exact hyy c1
    have hz2 : interiorBump (x + unitStep 0 i) y' = 0 := by
      by_contra hne
      have hs := abs_lt_of_interiorBump_ne_zero hamb hodd y' h' hh' (by rw [← ex']; exact hne)
      have hm := add_basisVector_mem_centredCube hodd h' i hN (-1) (by simp) hs
      have e : x = cellCentre 0 y' + siteOfCoords 0 fun j => h' j + -1 * basisVector i j := by
        have e0 : (fun j => h' j + -1 * basisVector i j) = fun j => h' j + (-basisVector i) j := by
          funext j
          simp
        rw [e0, ← cellCentre_add_siteOfCoords_add, ← ex', siteOfCoords_neg, ← unitStep_eq]
        abel
      have c1 := enclosingCell_cellCentre_add hodd y' _ hm
      rw [← e, ← hyd] at c1
      exact hyy c1.symm
    rw [b1, b2, normalizedBump_eq, normalizedBump_eq, hz1, hz2]
    simp only [zero_div, zero_smul]
    simpa [adjointAction] using hnn
omit V R in
theorem cellBondNorm_le (hodd : Odd F.blockSide) (c : F.Cell) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ β ∈ innerBonds S 0, ‖f β.1 β.2‖ ≤ K) :
    cellBondNorm 3 S (fun _ => 1) f c ≤ (4 * (cellSideLength F : ℝ) ^ 4) ^ (1 / 3 : ℝ) * K := by
  simp only [cellBondNorm]
  refine sum_rpow_rpow_inv_le (bondsOver S {c} 0) (fun β => 1 * ‖f β.1 β.2‖) K _ 3 (by norm_num) hK ?_
    fun β hβ => ?_
  · have := card_pairs_le_of_enclosingCell_eq S hodd c (bondsOver S {c} 0) (by
      intro β hβ
      have hβ' := Finset.mem_filter.1 hβ
      have hb := Finset.mem_filter.1 hβ'.1
      exact ⟨(Finset.mem_product.1 hb.1).1, by simpa using hβ'.2⟩)
    simpa using this
  · have hβ' := Finset.mem_filter.1 hβ
    exact ⟨by positivity, by simpa using hf β hβ'.1⟩
omit V R in
theorem cellPlaquetteNorm_le (hodd : Odd F.blockSide) (c : F.Cell) (g : F.Site 0 × Fin 4 × Fin 4 → ℍ[ℝ])
    {K : ℝ} (hK : 0 ≤ K) (hg : ∀ p ∈ innerPlaquettes S 0, ‖g p‖ ≤ K) :
    cellPlaquetteNorm (12 / 7) S (fun _ => 1) g c ≤
      (16 * (cellSideLength F : ℝ) ^ 4) ^ (1 / (12 / 7) : ℝ) * K := by
  simp only [cellPlaquetteNorm]
  refine sum_rpow_rpow_inv_le (plaquettesOver S {c} 0) (fun p => 1 * ‖g p‖) K _ (12 / 7) (by norm_num) hK ?_
    fun p hp => ?_
  · have := card_pairs_le_of_enclosingCell_eq S hodd c (plaquettesOver S {c} 0) (by
      intro p hp
      have hp' := Finset.mem_filter.1 hp
      exact ⟨(Finset.mem_product.1 (Finset.mem_filter.1 hp'.1).1).1, by simpa using hp'.2⟩)
    simpa using this
  · have hp' := Finset.mem_filter.1 hp
    exact ⟨by positivity, by simpa using hg p hp'.1⟩
theorem cellBumpBounds (hB : referenceBoundsStatement) : cellBumpBoundsStatement := by
  classical
  obtain ⟨CB, cB, L1, hCB, hcB, hB⟩ := hB
  have hM1 := one_le_cutoffBound
  set K₁ : ℝ := 625 * (2 * CB + 3 * cutoffBound) with hK₁
  set C : ℝ := 625 + 4 * K₁ + 20000 * CB with hC
  have hC4 : 4 * K₁ ≤ C := by
    rw [hC]
    nlinarith
  have hC2 : 20000 * CB ≤ C := by
    rw [hC]
    nlinarith
  refine ⟨min cB 1, C, max L1 13, lt_min hcB one_pos, by linarith, ?_⟩
  intro F m S hodd hLL hamb hm hreg s V hs hsc hcold b B hbB
  have hL1 : L1 ≤ F.blockSide := le_trans (le_max_left _ _) hLL
  have hL13 : 13 ≤ F.blockSide := le_trans (le_max_right _ _) hLL
  have hs1 : s ≤ 1 := le_trans hsc (min_le_right _ _)
  have hN : 13 ≤ cellSideLength F := by
    have h1 : F.blockSide ≤ F.blockSide ^ F.top := Nat.le_self_pow (by simp [BlockFrame.top]) _
    have h2 : (13 : ℤ) ≤ ((F.blockSide ^ F.top : ℕ) : ℤ) := by exact_mod_cast hL13.trans h1
    simpa [cellSideLength] using h2
  have hN3 : 3 ≤ cellSideLength F := by omega
  have hNr : (0 : ℝ) < (cellSideLength F : ℝ) := by exact_mod_cast (by omega : 0 < cellSideLength F)
  set N : ℝ := (cellSideLength F : ℝ) with hNd
  have hls : levelScale F 0 = 1 / N := by
    simp [levelScale, hNd, cellSideLength]
  obtain ⟨h1, h2, _⟩ := hB F m S hodd hL1 hamb hm hreg s V hs (le_trans hsc (min_le_left _ _)) hcold
  refine ⟨fun y hy => frameCellMean_cellBumpSection S V hamb hodd hN3 b y hy, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [cellSiteNorm]
    refine (sum_rpow_rpow_inv_le _ (fun x => 1 * ‖cellBumpSection S V b x‖) (625 * ‖b c‖) (N ^ 4) 4
      (by norm_num) (by positivity) (card_le_of_enclosingCell_eq S hodd c _ fun x hx => ?_)
      fun x hx => ?_).trans ?_
    · have := Finset.mem_filter.1 hx
      exact this
    · have hx' := Finset.mem_filter.1 hx
      have := norm_cellBumpSection_le S V hamb hodd hN3 b hx'.1
      rw [hx'.2] at this
      exact ⟨by positivity, by simpa using this⟩
    · rw [pow_four_rpow hNr, show (4 : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one]
      have : 0 ≤ N * ‖b c‖ := by positivity
      nlinarith
  · intro c hc
    simp only [cellSiteNorm]
    refine (sum_rpow_rpow_inv_le _ (fun x => 1 * ‖cellBumpSection S V b x‖) (625 * ‖b c‖) (N ^ 4) 12
      (by norm_num) (by positivity) (card_le_of_enclosingCell_eq S hodd c _ fun x hx => ?_)
      fun x hx => ?_).trans ?_
    · have := Finset.mem_filter.1 hx
      exact this
    · have hx' := Finset.mem_filter.1 hx
      have := norm_cellBumpSection_le S V hamb hodd hN3 b hx'.1
      rw [hx'.2] at this
      exact ⟨by positivity, by simpa using this⟩
    · rw [pow_four_rpow hNr, show (4 : ℝ) * (1 / 12) = 1 / 3 by norm_num]
      have : 0 ≤ N ^ (1 / 3 : ℝ) * ‖b c‖ := by positivity
      nlinarith
  · intro c hc
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB c hc)
    have hE : 0 ≤ CB * s * levelScale F 0 := by
      rw [hls]
      positivity
    have hpt : ∀ β ∈ innerBonds S 0,
        ‖covariantDiff (referenceFieldChain S V 0) (cellBumpSection S V b) β.1 β.2‖ ≤ K₁ * B / N := by
      intro β hβ
      have h3 : ‖covariantDiff (referenceFieldChain S V 0) (cellBumpSection S V b) β.1 β.2‖ ≤
          625 * (2 * (CB * s * levelScale F 0) + 3 * cutoffBound / N) * B :=
        norm_covariantDiff_le S V hamb hodd hN hE
          (fun c' hc' β' hβ' p1 p2 => h1 0 (Nat.succ_pos _) c' hc' β' hβ' p1 p2) b hbB β hβ
      refine h3.trans ?_
      rw [hls]
      have e : 625 * (2 * (CB * s * (1 / N)) + 3 * cutoffBound / N) * B =
          625 * (2 * CB * s + 3 * cutoffBound) * B / N := by
        field_simp
      rw [e]
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hB0) hNr.le
      rw [hK₁]
      nlinarith
    have hKB : 0 ≤ K₁ * B / N := by positivity
    refine (cellBondNorm_le S hodd c _ hKB hpt).trans ?_
    have h3 := mul_pow_four_rpow_le hNr (a := 4) (q := 3) (by norm_num) (by norm_num)
    have h4 : N ^ (4 * (1 / 3 : ℝ)) = N * N ^ (1 / 3 : ℝ) := by
      rw [show (4 : ℝ) * (1 / 3) = 1 + 1 / 3 by norm_num, Real.rpow_add hNr, Real.rpow_one]
    rw [h4] at h3
    calc (4 * N ^ 4) ^ (1 / 3 : ℝ) * (K₁ * B / N) ≤ 4 * (N * N ^ (1 / 3 : ℝ)) * (K₁ * B / N) :=
          mul_le_mul_of_nonneg_right h3 hKB
      _ = 4 * K₁ * N ^ (1 / 3 : ℝ) * B := by field_simp
      _ ≤ C * N ^ (1 / 3 : ℝ) * B := by gcongr
  · intro c hc
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB c hc)
    have hpt : ∀ p ∈ innerPlaquettes S 0,
        ‖adjointAction (plaquetteHolonomy (referenceFieldChain S V 0) p) (cellBumpSection S V b p.1) -
          cellBumpSection S V b p.1‖ ≤ 2 * (CB * s / N ^ 2) * (625 * B) := by
      intro p hp
      have hp1 : p.1 ∈ sitesOfCells S 0 := (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1
      have hcell := (exists_centredCube_of_mem S hodd hp1).choose_spec.2.2
      have hn := (norm_cellBumpSection_le S V hamb hodd hN3 b hp1).trans
        (mul_le_mul_of_nonneg_left (hbB _ hcell) (by norm_num))
      have hcv : ‖((plaquetteHolonomy (referenceFieldChain S V 0) p : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          CB * s / N ^ 2 := by
        have h3 := h2 0 (Nat.succ_pos _) p hp
        rw [hls] at h3
        refine le_trans h3 (le_of_eq ?_)
        field_simp
      refine (norm_adjointAction_sub_self_le _ _).trans ?_
      have := mul_le_mul hcv hn (norm_nonneg _) (by positivity)
      linarith
    have hKB : 0 ≤ 2 * (CB * s / N ^ 2) * (625 * B) := by positivity
    refine (cellPlaquetteNorm_le S hodd c _ hKB hpt).trans ?_
    have h3 := mul_pow_four_rpow_le hNr (a := 16) (q := 12 / 7) (by norm_num) (by norm_num)
    have h4 : N ^ (4 * (1 / (12 / 7) : ℝ)) = N ^ 2 * N ^ (1 / 3 : ℝ) := by
      rw [show (4 : ℝ) * (1 / (12 / 7)) = 2 + 1 / 3 by norm_num, Real.rpow_add hNr, Real.rpow_two]
    rw [h4] at h3
    calc (16 * N ^ 4) ^ (1 / (12 / 7) : ℝ) * (2 * (CB * s / N ^ 2) * (625 * B))
        ≤ 16 * (N ^ 2 * N ^ (1 / 3 : ℝ)) * (2 * (CB * s / N ^ 2) * (625 * B)) :=
          mul_le_mul_of_nonneg_right h3 hKB
      _ = 20000 * CB * s * N ^ (1 / 3 : ℝ) * B := by
          field_simp
          ring
      _ ≤ C * s * N ^ (1 / 3 : ℝ) * B := by gcongr
end CellBumps
end YangMills.Construction
end
