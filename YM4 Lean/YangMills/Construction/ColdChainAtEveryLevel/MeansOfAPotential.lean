import YangMills.Construction.ColdChainAtEveryLevel.PotentialsInAPatch
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.ColdChainAtEveryLevel.TopAverageInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PotentialMeans
open BlockAverages GaugeMap PatchFrames PatchPoints PatchForms PatchPotentials LatticeFractionalIntegration BondShares
section Flat
theorem mem_centredCube_odd_iff (k : ℕ) (h : Lattice4) :
    h ∈ centredCube (2 * k + 1) ↔ ∀ i, -(k : ℤ) ≤ h i ∧ h i ≤ k := by
  simp [centredCube, Fintype.mem_piFinset]
theorem card_centredCube_odd {M : ℕ} (hM : Odd M) : (centredCube M).card = M ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem sum_centredCube_mul {E : Type} [AddCommMonoid E] {L M : ℕ} (hL : Odd L) (hM : Odd M) (G : Lattice4 → E) :
    ∑ h ∈ centredCube L, ∑ h' ∈ centredCube M, G (fun i => (M : ℤ) * h i + h' i) = ∑ H ∈ centredCube (L * M), G H := by
  classical
  have hc1 := card_centredCube_odd hL
  have hc2 := card_centredCube_odd hM
  have hc3 := card_centredCube_odd (hL.mul hM)
  obtain ⟨k, rfl⟩ := hL
  obtain ⟨l, rfl⟩ := hM
  set φ : Lattice4 × Lattice4 → Lattice4 := fun p i => ((2 * l + 1 : ℕ) : ℤ) * p.1 i + p.2 i with hφ
  have hinj : Set.InjOn φ ((centredCube (2 * k + 1) ×ˢ centredCube (2 * l + 1) : Finset (Lattice4 × Lattice4)) :
      Set (Lattice4 × Lattice4)) := by
    rintro ⟨h, h'⟩ hp ⟨g, g'⟩ hq e
    have hp' := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    have hq' := Finset.mem_product.1 (Finset.mem_coe.1 hq)
    have a1 := (mem_centredCube_odd_iff l h').1 hp'.2
    have a2 := (mem_centredCube_odd_iff l g').1 hq'.2
    have hM0 : (0 : ℤ) < ((2 * l + 1 : ℕ) : ℤ) := by positivity
    have key : ∀ i, h i = g i ∧ h' i = g' i := by
      intro i
      have ei : ((2 * l + 1 : ℕ) : ℤ) * h i + h' i = ((2 * l + 1 : ℕ) : ℤ) * g i + g' i := congrFun e i
      have hd : ((2 * l + 1 : ℕ) : ℤ) ∣ (h' i - g' i) :=
        ⟨g i - h i, by linarith [mul_sub (((2 * l + 1 : ℕ) : ℤ)) (g i) (h i)]⟩
      have hb : |h' i - g' i| < ((2 * l + 1 : ℕ) : ℤ) := by
        have b1 := a1 i
        have b2 := a2 i
        rw [abs_lt]
        push_cast
        constructor <;> omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hd hb
      have h1 : h' i = g' i := by omega
      rw [h1] at ei
      exact ⟨mul_left_cancel₀ hM0.ne' (by linarith), h1⟩
    have e1 : h = g := funext fun i => (key i).1
    have e2 : h' = g' := funext fun i => (key i).2
    rw [e1, e2]
  have e3 : (2 * k + 1) * (2 * l + 1) = 2 * (2 * k * l + k + l) + 1 := by ring
  have hsub : (centredCube (2 * k + 1) ×ˢ centredCube (2 * l + 1)).image φ ⊆
      centredCube ((2 * k + 1) * (2 * l + 1)) := by
    intro H hH
    obtain ⟨⟨h, h'⟩, hp, rfl⟩ := Finset.mem_image.1 hH
    have hp' := Finset.mem_product.1 hp
    have a0 := (mem_centredCube_odd_iff k h).1 hp'.1
    have a1 := (mem_centredCube_odd_iff l h').1 hp'.2
    rw [e3, mem_centredCube_odd_iff]
    intro i
    obtain ⟨b0, b1⟩ := a0 i
    obtain ⟨c0, c1⟩ := a1 i
    have hM0 : (0 : ℤ) ≤ ((2 * l + 1 : ℕ) : ℤ) := by positivity
    have d0 := mul_le_mul_of_nonneg_left b0 hM0
    have d1 := mul_le_mul_of_nonneg_left b1 hM0
    simp only [hφ]
    push_cast at d0 d1 ⊢
    constructor <;> nlinarith
  have himg : (centredCube (2 * k + 1) ×ˢ centredCube (2 * l + 1)).image φ =
      centredCube ((2 * k + 1) * (2 * l + 1)) := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, hc1, hc2, hc3, mul_pow]
  rw [← Finset.sum_product', ← himg, Finset.sum_image hinj]
theorem sum_range_mul {E : Type} [AddCommMonoid E] (L M : ℕ) (G : ℕ → E) :
    ∑ r ∈ Finset.range L, ∑ r' ∈ Finset.range M, G (M * r + r') = ∑ R ∈ Finset.range (L * M), G R := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [mul_comm M L]
variable {F : BlockFrame}
theorem siteOfCoords_zsmul (j : ℕ) (c : ℤ) (a : Lattice4) :
    siteOfCoords (F := F) j (c • a) = c • siteOfCoords j a := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.siteOfCoords_zsmul <;> assumption
theorem baseSite_refineSite_add_line {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) (h h' : Lattice4) (r r' : ℕ)
    (i : Fin 4) :
    baseSite (refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i) + siteOfCoords 0 h' + (r' : ℤ) • unitStep 0 i =
      baseSite y + siteOfCoords 0 (fun k => ((F.blockSide ^ j : ℕ) : ℤ) * h k + h' k) +
        ((F.blockSide ^ j * r + r' : ℕ) : ℤ) • unitStep 0 i := by
  have e1 : refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i =
      refineSite y + siteOfCoords j (h + (r : ℤ) • basisVector i) := by
    rw [siteOfCoords_add, siteOfCoords_zsmul, unitStep_eq, add_assoc]
  rw [e1, baseSite_add j (by omega), baseSite_refineSite j hj]
  simp only [unitStep_eq, ← siteOfCoords_zsmul]
  simp only [add_assoc, ← siteOfCoords_add]
  congr 2
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring
theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem centredCube_one : centredCube 1 = {(0 : Lattice4)} := by
  ext h
  simp [centredCube, funext_iff]
theorem nestedAverage_eq_flat {E : Type} [AddCommMonoid E] [Module ℝ E] (hodd : Odd F.blockSide)
    (f : F.Site 0 → Fin 4 → E) (j : ℕ) (hj : j ≤ F.top) (y : F.Site j) (i : Fin 4) :
    nestedAverage f j y i = (1 / ((F.blockSide : ℝ) ^ j) ^ 4) •
      ∑ h ∈ centredCube (F.blockSide ^ j), ∑ r ∈ Finset.range (F.blockSide ^ j),
        f (baseSite y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i) i := by
  induction j with
  | zero =>
    simp only [pow_zero, centredCube_one, Finset.sum_singleton, Finset.range_one]
    simp [nestedAverage, baseSite_depth_zero, siteOfCoords_zero]
  | succ j ih =>
    have hj' : j ≤ F.top := by omega
    have hM : Odd (F.blockSide ^ j) := hodd.pow
    have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    show bondLineAverage (nestedAverage f j) (y, i) = _
    simp only [bondLineAverage]
    have h1 : ∀ (h : Lattice4) (r : ℕ),
        nestedAverage f j (refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i) i =
          (1 / ((F.blockSide : ℝ) ^ j) ^ 4) • ∑ h' ∈ centredCube (F.blockSide ^ j),
            ∑ r' ∈ Finset.range (F.blockSide ^ j),
              f (baseSite y + siteOfCoords 0 (fun k => ((F.blockSide ^ j : ℕ) : ℤ) * h k + h' k) +
                ((F.blockSide ^ j * r + r' : ℕ) : ℤ) • unitStep 0 i) i := by
      intro h r
      rw [ih hj']
      simp only [baseSite_refineSite_add_line hj y h _ r _ i]
    simp only [h1]
    have e2 : ((F.blockSide : ℝ) ^ (j + 1)) ^ 4 = (F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) ^ j) ^ 4 := by ring
    have e3 : F.blockSide ^ (j + 1) = F.blockSide * F.blockSide ^ j := by ring
    rw [e2, e3, ← sum_centredCube_mul hodd hM (fun H => ∑ R ∈ Finset.range (F.blockSide * F.blockSide ^ j),
      f (baseSite y + siteOfCoords 0 H + (R : ℤ) • unitStep 0 i) i)]
    simp only [← Finset.smul_sum]
    rw [smul_smul]
    have e4 : 1 / (F.blockSide : ℝ) ^ 4 * (1 / ((F.blockSide : ℝ) ^ j) ^ 4) =
        1 / ((F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) ^ j) ^ 4) := by
      field_simp
    rw [e4]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h' _ => ?_
    exact sum_range_mul F.blockSide (F.blockSide ^ j) (fun R =>
      f (baseSite y + siteOfCoords 0 (fun k => ((F.blockSide ^ j : ℕ) : ℤ) * h k + h' k) + (R : ℤ) • unitStep 0 i) i)
theorem nestedAverage_top_eq {E : Type} [AddCommMonoid E] [Module ℝ E] (hodd : Odd F.blockSide)
    (f : F.Site 0 → Fin 4 → E) (y : F.Cell) (i : Fin 4) :
    nestedAverage f F.top y i = (1 / (cellSideLength F : ℝ) ^ 4) •
      ∑ h ∈ centredCube (F.blockSide ^ F.top), ∑ r ∈ Finset.range (F.blockSide ^ F.top),
        f (cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i) i := by
  rw [nestedAverage_eq_flat hodd f F.top le_rfl y i, cellSideLength_cast]
  have e : baseSite y = cellCentre (F := F) 0 y := by
    have h := baseSite_cellCentre (F := F) F.top le_rfl y
    rwa [cellCentre_top] at h
  rw [e]
def siteMean (ψ : F.Site 0 → ℍ[ℝ]) (y : F.Cell) : ℍ[ℝ] :=
  (1 / (cellSideLength F : ℝ) ^ 4) • ∑ h ∈ centredCube (F.blockSide ^ F.top), ψ (cellCentre 0 y + siteOfCoords 0 h)
theorem cellCentre_add_unitStep (y : F.Cell) (i : Fin 4) :
    cellCentre (F := F) 0 (y + unitStep F.top i) =
      cellCentre 0 y + ((F.blockSide ^ F.top : ℕ) : ℤ) • unitStep 0 i := by
  rw [unitStep_eq, cellCentre_add 0 (Nat.zero_le _), unitStep_eq, ← siteOfCoords_zsmul]
  congr 2
theorem sum_lines_eq_siteMean_sub (ψ : F.Site 0 → ℍ[ℝ]) (y : F.Cell) (i : Fin 4) :
    (1 / (cellSideLength F : ℝ) ^ 4) • ∑ h ∈ centredCube (F.blockSide ^ F.top), ∑ r ∈ Finset.range (F.blockSide ^ F.top),
        (ψ (cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i + unitStep 0 i) -
          ψ (cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i)) =
      siteMean ψ (y + unitStep F.top i) - siteMean ψ y := by
  simp only [siteMean]
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  have e : ∀ r : ℕ, cellCentre (F := F) 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i + unitStep 0 i =
      cellCentre 0 y + siteOfCoords 0 h + ((r + 1 : ℕ) : ℤ) • unitStep 0 i := by
    intro r
    push_cast
    rw [add_smul, one_smul, add_assoc]
  simp only [e]
  rw [Finset.sum_range_sub (fun r : ℕ => ψ (cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i))]
  rw [cellCentre_add_unitStep, add_right_comm]
  simp
variable {S : Finset F.Cell}
theorem mem_cellSites_of_centredCube (hodd : Odd F.blockSide) {y : F.Cell} (hy : y ∈ S) {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) :
    cellCentre 0 y + siteOfCoords 0 h ∈ cellSites S y :=
  Finset.mem_filter.2 ⟨mem_sitesOfCells.2 ⟨y, hy, h, by simpa using hh, rfl⟩,
    LocalPartition.enclosingCell_cellCentre_add hodd y h (by simpa using hh)⟩
theorem mem_cellSites_union_of_line (hodd : Odd F.blockSide) {y : F.Cell} {i : Fin 4} (hy : y ∈ S)
    (hy' : y + unitStep F.top i ∈ S) {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) {r : ℕ} (hr : r ≤ F.blockSide ^ F.top) :
    cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i ∈
      cellSites S y ∪ cellSites S (y + unitStep F.top i) := by
  classical
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  have hN : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
  have hb := (mem_centredCube_iff h).1 hh
  have hrz : (r : ℤ) ≤ cellSideLength F := by rw [← hN]; exact_mod_cast hr
  by_cases hc : h i + r ≤ (cellSideLength F - 1) / 2
  · refine Finset.mem_union_left _ ?_
    have hm : h + (r : ℤ) • basisVector i ∈ centredCube (F.blockSide ^ F.top) := by
      rw [mem_centredCube_iff]
      intro k
      have := hb k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one]
        constructor <;> omega
      · simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_of_ne hk, smul_eq_mul, mul_zero, add_zero]
        exact this
    have e : cellCentre (F := F) 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i =
        cellCentre 0 y + siteOfCoords 0 (h + (r : ℤ) • basisVector i) := by
      rw [siteOfCoords_add, siteOfCoords_zsmul, unitStep_eq, add_assoc]
    rw [e]
    exact mem_cellSites_of_centredCube hodd hy hm
  · refine Finset.mem_union_right _ ?_
    have hm : h + ((r : ℤ) - cellSideLength F) • basisVector i ∈ centredCube (F.blockSide ^ F.top) := by
      rw [mem_centredCube_iff]
      intro k
      have := hb k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one]
        constructor <;> omega
      · simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_of_ne hk, smul_eq_mul, mul_zero, add_zero]
        exact this
    have e : cellCentre (F := F) 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i =
        cellCentre 0 (y + unitStep F.top i) + siteOfCoords 0 (h + ((r : ℤ) - cellSideLength F) • basisVector i) := by
      rw [cellCentre_add_unitStep, hN, siteOfCoords_add, siteOfCoords_zsmul, unitStep_eq, sub_smul]
      abel
    rw [e]
    exact mem_cellSites_of_centredCube hodd hy' hm
theorem sum_line_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {y : F.Cell} {i : Fin 4} (hy : y ∈ S)
    (hy' : y + unitStep F.top i ∈ S) (g : F.Site 0 → ℝ) (hg : ∀ t, 0 ≤ g t) {r : ℕ} (hr : r ≤ F.blockSide ^ F.top) :
    ∑ h ∈ centredCube (F.blockSide ^ F.top), g (cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i) ≤
      ∑ t ∈ cellSites S y, g t + ∑ t ∈ cellSites S (y + unitStep F.top i), g t := by
  classical
  have hinj : Set.InjOn (fun h : Lattice4 => cellCentre (F := F) 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i)
      (centredCube (F.blockSide ^ F.top) : Set Lattice4) := by
    intro h hh h' hh' e
    exact siteOfCoords_injOn_centredCube hamb hodd hh hh' (add_left_cancel (add_right_cancel e))
  rw [← Finset.sum_image (f := g) hinj]
  have h1 : (centredCube (F.blockSide ^ F.top)).image
      (fun h : Lattice4 => cellCentre (F := F) 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i) ⊆
      cellSites S y ∪ cellSites S (y + unitStep F.top i) := by
    intro t ht
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 ht
    exact mem_cellSites_union_of_line hodd hy hy' hh hr
  refine (Finset.sum_le_sum_of_subset_of_nonneg h1 fun t _ _ => hg t).trans ?_
  have h2 := Finset.sum_union_inter (s₁ := cellSites S y) (s₂ := cellSites S (y + unitStep F.top i)) (f := g)
  have h3 : 0 ≤ ∑ t ∈ cellSites S y ∩ cellSites S (y + unitStep F.top i), g t := Finset.sum_nonneg fun t _ => hg t
  linarith
theorem cellSideLength_natCast (F : BlockFrame) : ((F.blockSide ^ F.top : ℕ) : ℝ) = (cellSideLength F : ℝ) := by
  simp [cellSideLength]
theorem scale_mul_flatMean_le {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
    (hN : CellNormFamily S Md Lf Sr σ K)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {y : F.Cell} {i : Fin 4} (hy : y ∈ S)
    (hy' : y + unitStep F.top i ∈ S)
    (hd : cellSupDist y (y + unitStep F.top i) ≤ 22) (g : F.Site 0 → ℝ) (hg : ∀ t, 0 ≤ g t) (ρ : ℕ → ℕ)
    (hρ : ∀ r, r < F.blockSide ^ F.top → ρ r ≤ F.blockSide ^ F.top) :
    σ y * ((1 / (cellSideLength F : ℝ) ^ 4) * ∑ h ∈ centredCube (F.blockSide ^ F.top),
        ∑ r ∈ Finset.range (F.blockSide ^ F.top),
          g (cellCentre 0 y + siteOfCoords 0 h + (ρ r : ℤ) • unitStep 0 i)) ≤
      K * Md g y + K * (K * Md g (y + unitStep F.top i)) := by
  have hNp : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hodd.pos
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ t ∈ cellSites S y, g t := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ t ∈ cellSites S (y + unitStep F.top i), g t := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ Finset.sum_nonneg fun t _ => hg t
  have h1 : ∑ h ∈ centredCube (F.blockSide ^ F.top), ∑ r ∈ Finset.range (F.blockSide ^ F.top),
      g (cellCentre 0 y + siteOfCoords 0 h + (ρ r : ℤ) • unitStep 0 i) ≤ (cellSideLength F : ℝ) * (A + B) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _r ∈ Finset.range (F.blockSide ^ F.top), (A + B) := Finset.sum_le_sum fun r hr => by
          rw [hA, hB]
          exact sum_line_le hamb hodd hy hy' g hg (hρ r (Finset.mem_range.1 hr))
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, cellSideLength_natCast]
  have hs := hN.scale_le_of_near y (y + unitStep F.top i) hd
  have hσy := (hN.scale_pos y).le
  have m1 := hN.mean_le g y
  have m2 := hN.mean_le g (y + unitStep F.top i)
  have a1 : ∑ x ∈ cellSites S y, |g x| = A := by
    rw [hA]
    exact Finset.sum_congr rfl fun x _ => abs_of_nonneg (hg x)
  have a2 : ∑ x ∈ cellSites S (y + unitStep F.top i), |g x| = B := by
    rw [hB]
    exact Finset.sum_congr rfl fun x _ => abs_of_nonneg (hg x)
  rw [a1] at m1
  rw [a2] at m2
  have hK : 0 ≤ K := by
    have h0 := hN.scale_pos y
    have h1 := hN.scale_le_of_near y y (by simp [cellSupDist])
    by_contra hn
    have : K * σ y < 0 := mul_neg_of_neg_of_pos (not_le.1 hn) h0
    linarith
  have h2 : σ y * (A + B) ≤ (cellSideLength F : ℝ) ^ 3 * (K * Md g y + K * (K * Md g (y + unitStep F.top i))) := by
    have b1 : σ y * B ≤ K * σ (y + unitStep F.top i) * B := mul_le_mul_of_nonneg_right hs hB0
    have b2 : K * (σ (y + unitStep F.top i) * B) ≤
        K * (K * (cellSideLength F : ℝ) ^ 3 * Md g (y + unitStep F.top i)) :=
      mul_le_mul_of_nonneg_left m2 hK
    nlinarith
  have h3 : σ y * ((1 / (cellSideLength F : ℝ) ^ 4) * ((cellSideLength F : ℝ) * (A + B))) =
      σ y * (A + B) / (cellSideLength F : ℝ) ^ 3 := by
    field_simp
  calc _ ≤ σ y * ((1 / (cellSideLength F : ℝ) ^ 4) * ((cellSideLength F : ℝ) * (A + B))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hσy
    _ = _ := h3
    _ ≤ _ := by
        rw [div_le_iff₀ (by positivity)]
        linarith
end Flat
section Top
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {Cs r Ch : ℝ}
  {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
def sitePotential (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) : ℍ[ℝ] :=
  centredPotential S V z u (patchChart S z t)
theorem patchFrameForm_base_eq (f : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    BlockAverages.patchFrameForm S V z f = PatchForms.patchFrameForm S V z f := by
  funext x i
  simp only [BlockAverages.patchFrameForm, PatchForms.patchFrameForm, baseSite_depth_zero]
theorem norm_step_add_form_le {R : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r Ch)
    (hF : IsPatchFrame S V z R Cs r)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {t : F.Site 0} {i : Fin 4} (ht : t ∈ patchSiteSet S z)
    (ht' : t + unitStep 0 i ∈ patchSiteSet S z) :
    ‖(sitePotential S V z u (t + unitStep 0 i) - sitePotential S V z u t) +
        PatchForms.patchFrameForm S V z (toQuaternionForm u) t i‖ ≤
      ‖primitiveDefect S V z u t i‖ +
        2 * (Cs / (cellSideLength F : ℝ)) * ‖sitePotential S V z u (t + unitStep 0 i)‖ := by
  obtain ⟨T, hT, hl⟩ := exists_leadingTransport_near_one hF h.scale h.ambient h.odd_side (h.closedOrthant_cases z) ht ht'
  obtain ⟨f, hf⟩ : ∃ f, f = frameChange S V z t := ⟨_, rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f', f' = frameChange S V z (t + unitStep 0 i) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = sitePotential S V z u t := ⟨_, rfl⟩
  obtain ⟨p', hp'⟩ : ∃ p', p' = sitePotential S V z u (t + unitStep 0 i) := ⟨_, rfl⟩
  rw [← hf, ← hf'] at hl
  have ed : primitiveDefect S V z u t i =
      toQuaternionForm u t i + (adjointAction (f * T * f'⁻¹) (adjointAction f' p') - adjointAction f p) := by
    simp only [primitiveDefect, covariantDiff, referenceFieldChain_zero_eq, hl]
    rw [hf, hf', hp, hp']
    rfl
  have e0 : adjointAction f⁻¹ (adjointAction (f * T * f'⁻¹) (adjointAction f' p')) = adjointAction T p' := by
    rw [← adjointAction_mul_apply, ← adjointAction_mul_apply]
    congr 1
    group
  have e1 : adjointAction f⁻¹ (primitiveDefect S V z u t i) =
      PatchForms.patchFrameForm S V z (toQuaternionForm u) t i + (adjointAction T p' - p) := by
    rw [ed, adjointAction_apply_add, adjointAction_apply_sub, e0, adjointAction_inv_apply_apply,
      PatchForms.patchFrameForm, hf]
  have e2 : (p' - p) + PatchForms.patchFrameForm S V z (toQuaternionForm u) t i =
      adjointAction f⁻¹ (primitiveDefect S V z u t i) - (adjointAction T p' - p') := by
    rw [e1]
    abel
  rw [← hp, ← hp', e2]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_adjointAction_apply]
  refine add_le_add le_rfl ((norm_adjointAction_apply_sub_le _ _).trans ?_)
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
def meanStepConstant (K Ch : ℝ) : ℝ :=
  (K + K ^ 2) * (1 + 2 * defectConstant K Ch + 2 * potentialConstant K Ch)
theorem meanStepConstant_nonneg (hK : 0 ≤ K) (hCh : 0 ≤ Ch) : 0 ≤ meanStepConstant K Ch := by
  have h1 := defectConstant_nonneg hK hCh
  have h2 := potentialConstant_nonneg hK hCh
  unfold meanStepConstant
  positivity
theorem formNorm_le_formTotal (hN : CellNormFamily S Md Lf Sr σ K) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {x : F.Cell} (hx : x ∈ cellBall S z 20) :
    Md (PatchDifferences.formNormOn S (toQuaternionForm u)) x ≤ formTotal Md S u z :=
  Finset.single_le_sum (f := fun x => Md (PatchDifferences.formNormOn S (toQuaternionForm u)) x)
    (fun _ _ => hN.isSeminorm_base.nonneg _ _) hx
set_option maxHeartbeats 1000000 in
theorem norm_siteMean_step_le {R : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r Ch)
    (hF : IsPatchFrame S V z R Cs r)
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {Gk : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H Gk Ch)
    (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K) (hz : z ∈ S) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {y : F.Cell} {i : Fin 4}
    (hy : y ∈ cellBall S z 10) (hy' : y + unitStep F.top i ∈ cellBall S z 10)
    (hTop : ‖BlockAverages.patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) y i -
        nestedAverage (BlockAverages.patchFrameForm S V z (toQuaternionForm u)) F.top y i‖ ≤
      Cs * nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top y i) :
    σ y * ‖siteMean (sitePotential S V z u) (y + unitStep F.top i) - siteMean (sitePotential S V z u) y‖ ≤
      σ y * ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top y i‖ +
        meanStepConstant K Ch * (curlTotal Sr S V u z + Cs * formTotal Md S u z) := by
  classical
  have hCh := h.kernelConst_nonneg
  have hNp := h.cellSideLength_pos
  have hκ := h.coldnessRatio_nonneg
  have hc0 := h.coldness_nonneg
  have hc1 := h.coldness_le_one
  have hodd := h.odd_side
  obtain ⟨hyS, d1⟩ := Finset.mem_filter.1 hy
  obtain ⟨hyS', d2⟩ := Finset.mem_filter.1 hy'
  have dy : cellSupDist y z ≤ 22 := by rw [cellSupDist_symm]; omega
  have dy' : cellSupDist (y + unitStep F.top i) z ≤ 22 := by rw [cellSupDist_symm]; omega
  have hd : cellSupDist y (y + unitStep F.top i) ≤ 22 := by
    have h1 := cellSupDist_triangle y z (y + unitStep F.top i)
    rw [cellSupDist_symm y z] at h1
    omega
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = Cs / (cellSideLength F : ℝ) := ⟨_, rfl⟩
  rw [← hκd] at hκ
  obtain ⟨A, hA⟩ : ∃ A : F.Site 0 → ℝ, A = defectBound κ Ch S V z u := ⟨_, rfl⟩
  have hA0 : ∀ t, 0 ≤ A t := fun t => by
    rw [hA]
    exact defectBound_nonneg hκ hCh u t
  obtain ⟨Y, hY⟩ : ∃ Y : F.Site 0 → ℝ, Y = potentialNorm S V z u := ⟨_, rfl⟩
  have hY0 : ∀ t, 0 ≤ Y t := fun t => by
    rw [hY]
    exact potentialNorm_nonneg u t
  obtain ⟨B, hB⟩ : ∃ B : F.Site 0 → ℝ, B = fun t => A t + 2 * κ * Y t := ⟨_, rfl⟩
  have hB0 : ∀ t, 0 ≤ B t := fun t => by
    rw [hB]
    exact add_nonneg (hA0 t) (mul_nonneg (by positivity) (hY0 t))
  obtain ⟨us, hus⟩ : ∃ us : F.Site 0 → ℝ, us = PatchDifferences.formNormOn S (toQuaternionForm u) := ⟨_, rfl⟩
  have hus0 : ∀ t, 0 ≤ us t := fun t => by
    rw [hus]
    exact zero_le_formNormOn _ t
  obtain ⟨N', hN'⟩ : ∃ N', N' = F.blockSide ^ F.top := ⟨_, rfl⟩
  obtain ⟨Ln, hLn⟩ : ∃ Ln : Lattice4 → ℕ → F.Site 0,
      Ln = fun (g : Lattice4) (r : ℕ) => cellCentre 0 y + siteOfCoords 0 g + (r : ℤ) • unitStep 0 i := ⟨_, rfl⟩
  have hsucc : ∀ g r, Ln g r + unitStep 0 i = Ln g (r + 1) := by
    intro g r
    rw [hLn]
    simp only []
    push_cast
    rw [add_smul, one_smul, add_assoc]
  have hsite : ∀ {g : Lattice4}, g ∈ centredCube (F.blockSide ^ F.top) → ∀ {r : ℕ}, r ≤ F.blockSide ^ F.top →
      Ln g r ∈ patchSiteSet S z ∧ Ln g r ∈ sitesOfCells S 0 := by
    intro g hg r hr
    have hm := mem_cellSites_union_of_line hodd hyS hyS' hg hr
    have h1 : Ln g r = cellCentre 0 y + siteOfCoords 0 g + (r : ℤ) • unitStep 0 i := by rw [hLn]
    rw [h1]
    rcases Finset.mem_union.1 hm with h2 | h2
    · exact ⟨h.mem_patchSiteSet_of_cellSupDist_le hyS d1 h2, (Finset.mem_filter.1 h2).1⟩
    · exact ⟨h.mem_patchSiteSet_of_cellSupDist_le hyS' d2 h2, (Finset.mem_filter.1 h2).1⟩
  have hpt : ∀ g ∈ centredCube (F.blockSide ^ F.top), ∀ r ∈ Finset.range (F.blockSide ^ F.top),
      ‖(sitePotential S V z u (Ln g r + unitStep 0 i) - sitePotential S V z u (Ln g r)) +
          PatchForms.patchFrameForm S V z (toQuaternionForm u) (Ln g r) i‖ ≤ A (Ln g r) + B (Ln g (r + 1)) := by
    intro g hg r hr
    have hr' := Finset.mem_range.1 hr
    obtain ⟨p0, -⟩ := hsite hg (r := r) hr'.le
    obtain ⟨p1, -⟩ := hsite hg (r := r + 1) hr'
    rw [← hsucc] at p1
    have h1 := norm_step_add_form_le h hF u p0 p1
    have h2 := norm_primitiveDefect_le h hF hk u p0 p1
    rw [← hκd, ← hA] at h2
    rw [← hκd] at h1
    have h3 : ‖sitePotential S V z u (Ln g r + unitStep 0 i)‖ = Y (Ln g r + unitStep 0 i) := by
      rw [hY, potentialNorm, restrictToPatch_of_mem p1]
      rfl
    rw [h3] at h1
    have h4 : B (Ln g (r + 1)) = A (Ln g r + unitStep 0 i) + 2 * κ * Y (Ln g r + unitStep 0 i) := by
      rw [hB, hsucc]
    rw [h4]
    linarith
  have E1 : (1 / (cellSideLength F : ℝ) ^ 4) • ∑ g ∈ centredCube (F.blockSide ^ F.top),
      ∑ r ∈ Finset.range (F.blockSide ^ F.top),
      ((sitePotential S V z u (Ln g r + unitStep 0 i) - sitePotential S V z u (Ln g r)) +
        PatchForms.patchFrameForm S V z (toQuaternionForm u) (Ln g r) i) =
      (siteMean (sitePotential S V z u) (y + unitStep F.top i) - siteMean (sitePotential S V z u) y) +
        nestedAverage (BlockAverages.patchFrameForm S V z (toQuaternionForm u)) F.top y i := by
    rw [patchFrameForm_base_eq, nestedAverage_top_eq hodd, ← sum_lines_eq_siteMean_sub, ← smul_add,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_add_distrib, hLn]
  have E2 : ‖(siteMean (sitePotential S V z u) (y + unitStep F.top i) - siteMean (sitePotential S V z u) y) +
        nestedAverage (BlockAverages.patchFrameForm S V z (toQuaternionForm u)) F.top y i‖ ≤
      (1 / (cellSideLength F : ℝ) ^ 4) * ∑ g ∈ centredCube (F.blockSide ^ F.top),
          ∑ r ∈ Finset.range (F.blockSide ^ F.top), A (Ln g r) +
        (1 / (cellSideLength F : ℝ) ^ 4) * ∑ g ∈ centredCube (F.blockSide ^ F.top),
          ∑ r ∈ Finset.range (F.blockSide ^ F.top), B (Ln g (r + 1)) := by
    rw [← E1, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Finset.sum_add_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g hg => ?_)
    rw [← Finset.sum_add_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => hpt g hg r hr)
  have hPU : nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top y i ≤
      (1 / (cellSideLength F : ℝ) ^ 4) * ∑ g ∈ centredCube (F.blockSide ^ F.top),
        ∑ r ∈ Finset.range (F.blockSide ^ F.top), us (Ln g r) := by
    rw [nestedAverage_top_eq hodd, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g hg => Finset.sum_le_sum fun r hr => ?_) (by positivity)
    have hr' := Finset.mem_range.1 hr
    obtain ⟨-, p0⟩ := hsite hg (r := r) hr'.le
    obtain ⟨-, p1⟩ := hsite hg (r := r + 1) hr'
    rw [← hsucc] at p1
    have h1 := norm_le_formNormOn (S := S) (toQuaternionForm u) (mem_innerBonds_of_step p0 p1 rfl)
    rw [← hus] at h1
    have h2 : Ln g r = cellCentre 0 y + siteOfCoords 0 g + (r : ℤ) • unitStep 0 i := by rw [hLn]
    rwa [← h2]
  have hQ : ‖nestedAverage (BlockAverages.patchFrameForm S V z (toQuaternionForm u)) F.top y i‖ ≤
      ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top y i‖ +
        Cs * nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top y i := by
    have h1 := norm_sub_norm_le (nestedAverage (BlockAverages.patchFrameForm S V z (toQuaternionForm u)) F.top y i)
      (BlockAverages.patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) y i)
    rw [norm_sub_rev] at h1
    have h2 : ‖BlockAverages.patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) y i‖ =
        ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top y i‖ := norm_adjointAction_apply _ _
    rw [h2] at h1
    linarith
  obtain ⟨FA, hFA⟩ : ∃ FA, FA = (1 / (cellSideLength F : ℝ) ^ 4) * ∑ g ∈ centredCube (F.blockSide ^ F.top),
      ∑ r ∈ Finset.range (F.blockSide ^ F.top), A (Ln g r) := ⟨_, rfl⟩
  obtain ⟨FB, hFB⟩ : ∃ FB, FB = (1 / (cellSideLength F : ℝ) ^ 4) * ∑ g ∈ centredCube (F.blockSide ^ F.top),
      ∑ r ∈ Finset.range (F.blockSide ^ F.top), B (Ln g (r + 1)) := ⟨_, rfl⟩
  obtain ⟨FU, hFU⟩ : ∃ FU, FU = (1 / (cellSideLength F : ℝ) ^ 4) * ∑ g ∈ centredCube (F.blockSide ^ F.top),
      ∑ r ∈ Finset.range (F.blockSide ^ F.top), us (Ln g r) := ⟨_, rfl⟩
  rw [← hFA, ← hFB] at E2
  rw [← hFU] at hPU
  have nA : σ y * FA ≤ K * Md A y + K * (K * Md A (y + unitStep F.top i)) := by
    have := scale_mul_flatMean_le hN h.ambient hodd hyS hyS' hd A hA0 (fun r => r) (fun r hr => hr.le)
    rw [hFA, hLn]
    exact this
  have nB : σ y * FB ≤ K * Md B y + K * (K * Md B (y + unitStep F.top i)) := by
    have := scale_mul_flatMean_le hN h.ambient hodd hyS hyS' hd B hB0 (fun r => r + 1) (fun r hr => hr)
    rw [hFB, hLn]
    exact this
  have nU : σ y * FU ≤ K * Md us y + K * (K * Md us (y + unitStep F.top i)) := by
    have := scale_mul_flatMean_le hN h.ambient hodd hyS hyS' hd us hus0 (fun r => r) (fun r hr => hr.le)
    rw [hFU, hLn]
    exact this
  set M1 := curlTotal Sr S V u z with hM1
  set M2 := formTotal Md S u z with hM2
  have hM10 : 0 ≤ M1 := curlTotal_nonneg hN u z
  have hM20 : 0 ≤ M2 := formTotal_nonneg hN u z
  obtain ⟨cD, hcD⟩ : ∃ cD, cD = defectConstant K Ch := ⟨_, rfl⟩
  obtain ⟨cB, hcB⟩ : ∃ cB, cB = potentialConstant K Ch := ⟨_, rfl⟩
  have hcD0 : 0 ≤ cD := hcD ▸ defectConstant_nonneg hK hCh
  have hcB0 : 0 ≤ cB := hcB ▸ potentialConstant_nonneg hK hCh
  obtain ⟨U, hU⟩ : ∃ U, U = M1 + Cs * M2 := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by
    rw [hU]
    positivity
  have bA : ∀ {x : F.Cell}, cellSupDist x z ≤ 22 → Md A x ≤ cD * U := by
    intro x hx
    refine (hN.base_le_target A x).trans ?_
    rw [hA, hκd, hcD, hU]
    exact target_defectBound_le h hF hk hK hN hz u hx
  have bB : ∀ {x : F.Cell}, cellSupDist x z ≤ 22 → Md B x ≤ (cD + 2 * cB) * U := by
    intro x hx
    have h1 : Md B x ≤ Md A x + 2 * κ * Md Y x := by
      rw [hB]
      refine (hN.isSeminorm_base.add_le _ _ x).trans (add_le_add le_rfl ?_)
      rw [hN.isSeminorm_base.smul, abs_of_nonneg (by positivity)]
    have h2 : Md Y x ≤ (cellSideLength F : ℝ) * (cB * (M1 + M2)) := by
      refine (hN.base_le_target Y x).trans ?_
      rw [hY, hcB]
      exact target_potentialNorm_le h hF hk hK hN hz u hx
    have h3 : 2 * κ * Md Y x ≤ 2 * κ * ((cellSideLength F : ℝ) * (cB * (M1 + M2))) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e3 : 2 * κ * ((cellSideLength F : ℝ) * (cB * (M1 + M2))) = 2 * Cs * (cB * (M1 + M2)) := by
      rw [hκd]
      field_simp
    rw [e3] at h3
    have h4 : Cs * (M1 + M2) ≤ U := by
      rw [hU]
      have := mul_le_of_le_one_left hM10 hc1
      linarith
    have h5 : 2 * Cs * (cB * (M1 + M2)) ≤ 2 * cB * U := by
      have := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2 * cB)
      have e : 2 * Cs * (cB * (M1 + M2)) = 2 * cB * (Cs * (M1 + M2)) := by ring
      linarith
    have := bA hx
    linarith
  have hsub : ∀ {x : F.Cell}, x ∈ cellBall S z 10 → x ∈ cellBall S z 20 := by
    intro x hx
    obtain ⟨a, b⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨a, by omega⟩
  have bU : ∀ {x : F.Cell}, x ∈ cellBall S z 10 → Md us x ≤ M2 := by
    intro x hx
    rw [hus]
    exact formNorm_le_formTotal hN u (hsub hx)
  have hσ := (hN.scale_pos y).le
  have c1 : σ y * FA ≤ (K + K ^ 2) * (cD * U) := by
    have a1 := mul_le_mul_of_nonneg_left (bA dy) hK
    have a2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (bA dy') hK) hK
    have e : (K + K ^ 2) * (cD * U) = K * (cD * U) + K * (K * (cD * U)) := by ring
    linarith
  have c2 : σ y * FB ≤ (K + K ^ 2) * ((cD + 2 * cB) * U) := by
    have a1 := mul_le_mul_of_nonneg_left (bB dy) hK
    have a2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (bB dy') hK) hK
    have e : (K + K ^ 2) * ((cD + 2 * cB) * U) = K * ((cD + 2 * cB) * U) + K * (K * ((cD + 2 * cB) * U)) := by ring
    linarith
  have c3 : σ y * FU ≤ (K + K ^ 2) * M2 := by
    have a1 := mul_le_mul_of_nonneg_left (bU hy) hK
    have a2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (bU hy') hK) hK
    have e : (K + K ^ 2) * M2 = K * M2 + K * (K * M2) := by ring
    linarith
  have c4 : Cs * (σ y * FU) ≤ (K + K ^ 2) * U := by
    have a1 := mul_le_mul_of_nonneg_left c3 hc0
    have a2 : Cs * M2 ≤ U := by
      rw [hU]
      linarith
    have a3 := mul_le_mul_of_nonneg_left a2 (by positivity : 0 ≤ K + K ^ 2)
    have e : Cs * ((K + K ^ 2) * M2) = (K + K ^ 2) * (Cs * M2) := by ring
    linarith
  obtain ⟨D, hD⟩ : ∃ D, D = siteMean (sitePotential S V z u) (y + unitStep F.top i) -
      siteMean (sitePotential S V z u) y := ⟨_, rfl⟩
  rw [← hD] at E2 ⊢
  obtain ⟨Pl, hPl⟩ : ∃ Pl, Pl = nestedAverage (BlockAverages.patchFrameForm S V z (toQuaternionForm u)) F.top y i :=
    ⟨_, rfl⟩
  rw [← hPl] at E2 hQ
  have n1 : ‖D‖ ≤ FA + FB + ‖Pl‖ := by
    have := norm_sub_le (D + Pl) Pl
    rw [add_sub_cancel_right] at this
    linarith
  have n2 : ‖Pl‖ ≤ ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top y i‖ + Cs * FU := by
    have := mul_le_mul_of_nonneg_left hPU hc0
    linarith
  have n3 : σ y * ‖D‖ ≤
      σ y * (FA + FB + (‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top y i‖ + Cs * FU)) :=
    mul_le_mul_of_nonneg_left (by linarith) hσ
  have e4 : σ y * (FA + FB + (‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top y i‖ + Cs * FU)) =
      σ y * ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top y i‖ + σ y * FA + σ y * FB +
        Cs * (σ y * FU) := by ring
  rw [e4] at n3
  have e5 : meanStepConstant K Ch * (M1 + Cs * M2) =
      (K + K ^ 2) * (cD * U) + (K + K ^ 2) * ((cD + 2 * cB) * U) + (K + K ^ 2) * U := by
    rw [← hU, meanStepConstant, ← hcD, ← hcB]
    ring
  rw [e5]
  linarith
end Top
section Path
theorem norm_sub_le_of_monotone_path (Mv : Lattice4 → ℍ[ℝ]) {c Bd : ℝ} (hc : 0 ≤ c) (hBd : 0 ≤ Bd)
    (Good : Lattice4 → Prop)
    (hstep : ∀ v i, Good v → Good (v + basisVector i) → c * ‖Mv (v + basisVector i) - Mv v‖ ≤ Bd) (d : ℕ) :
    ∀ v v' : Lattice4, (∀ i, v i ≤ v' i) → ∑ i, (v' i - v i) = d →
      (∀ w : Lattice4, (∀ i, v i ≤ w i ∧ w i ≤ v' i) → Good w) →
      c * ‖Mv v' - Mv v‖ ≤ d * Bd := by
  induction d with
  | zero =>
    intro v v' hle hs _
    have hz : ∀ i ∈ (Finset.univ : Finset (Fin 4)), v' i - v i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => by have := hle i; omega).1 (by simpa using hs)
    have e : v' = v := funext fun i => by have := hz i (Finset.mem_univ i); omega
    rw [e]
    simp
  | succ d ih =>
    intro v v' hle hs hg
    have hex : ∃ i, v i < v' i := by
      by_contra hn
      push Not at hn
      have e : ∑ i, (v' i - v i) = 0 := Finset.sum_eq_zero fun i _ => by
        have := hn i
        have := hle i
        omega
      rw [e] at hs
      push_cast at hs
      omega
    obtain ⟨i, hi⟩ := hex
    have hw : ∀ k, (v + basisVector i) k ≤ v' k := by
      intro k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, basisVector, Pi.single_eq_same]
        omega
      · simp only [Pi.add_apply, basisVector, Pi.single_eq_of_ne hk, add_zero]
        exact hle k
    have hs' : ∑ k, (v' k - (v + basisVector i) k) = d := by
      have e1 : ∑ k, (v' k - (v + basisVector i) k) = ∑ k, (v' k - v k) - ∑ k, basisVector i k := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Pi.add_apply]
        ring
      have e2 : ∑ k, basisVector i k = 1 := by
        simp [basisVector, Pi.single_apply]
      rw [e1, e2, hs]
      push_cast
      ring
    have hv0 : ∀ k, v k ≤ (v + basisVector i) k := by
      intro k
      by_cases hk : k = i
      · subst hk
        simp [basisVector]
      · simp [basisVector, hk]
    have h1 := ih (v + basisVector i) v' hw hs' fun w hwb => hg w fun k => ⟨(hv0 k).trans (hwb k).1, (hwb k).2⟩
    have h2 := hstep v i (hg v fun k => ⟨le_rfl, hle k⟩) (hg _ fun k => ⟨hv0 k, hw k⟩)
    have h3 := norm_add_le (Mv v' - Mv (v + basisVector i)) (Mv (v + basisVector i) - Mv v)
    rw [sub_add_sub_cancel] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 hc
    push_cast
    nlinarith
end Path
section Join
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {Cs r Ch : ℝ}
  {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
theorem enclosingCell_self (y : F.Cell) : enclosingCell y = y := by
  have e : (fun i => (siteCoords y i + ((F.blockSide : ℤ) ^ (F.top - F.top) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - F.top)) = siteCoords y := by
    funext i
    simp
  simp only [enclosingCell, e]
  exact siteOfCoords_siteCoords y
theorem siteMean_self_eq_zero (h : PotentialSetting S V Cs r Ch) (hz : z ∈ S)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    siteMean (sitePotential S V z u) z = 0 := by
  have hL := h.odd_side.pos
  have e1 : siteMean (sitePotential S V z u) z = cellMean F (centredPotential S V z u) := by
    have s : ∑ g ∈ centredCube (F.blockSide ^ F.top), sitePotential S V z u (cellCentre 0 z + siteOfCoords 0 g) =
        ∑ x ∈ cellOffsets F, centredPotential S V z u x :=
      (sum_cellOffsets_patchSite h.odd_side (h.closedOrthant_cases z) (sitePotential S V z u)).symm.trans
        (Finset.sum_congr rfl fun a ha =>
          congrArg (centredPotential S V z u) (h.patchChart_patchSite (mem_patchDomain_of_mem_cellOffsets hz hL ha)))
    exact congrArg (fun q => (1 / (cellSideLength F : ℝ) ^ 4) • q) s
  have e2 : centredPotential S V z u = fun a => localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u) a -
      cellMean F (localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u)) := rfl
  rw [e1, e2, cellMean_sub, cellMean_const hL, sub_self]
theorem norm_siteMean_near_le {R : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r Ch)
    (hF : IsPatchFrame S V z R Cs r)
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {Gk : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H Gk Ch)
    (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K) (hz : z ∈ S) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {z0 : F.Cell} (hz0 : z0 ∈ S)
    (hd : cellSupDist z z0 ≤ 2) {T : F.Cell → ℝ} (hT0 : ∀ y, 0 ≤ T y)
    (hT : ∀ b ∈ innerBonds S F.top,
      σ b.1 * ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top b.1 b.2‖ ≤ T b.1)
    (hTop : ∀ b ∈ innerBonds S F.top, enclosingCell b.1 ∈ cellBall S z 10 →
      enclosingCell (b.1 + unitStep F.top b.2) ∈ cellBall S z 10 →
      ‖BlockAverages.patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) b.1 b.2 -
        nestedAverage (BlockAverages.patchFrameForm S V z (toQuaternionForm u)) F.top b.1 b.2‖ ≤
      Cs * nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top b.1 b.2) :
    σ z0 * ‖siteMean (sitePotential S V z u) z0‖ ≤
      24 * (K * (∑ y ∈ cellBall S z 2, T y +
        meanStepConstant K Ch * (curlTotal Sr S V u z + Cs * formTotal Md S u z))) := by
  classical
  have hCh := h.kernelConst_nonneg
  have hc0 := h.coldness_nonneg
  have he := h.closedOrthant_cases z
  obtain ⟨U, hU⟩ : ∃ U, U = meanStepConstant K Ch * (curlTotal Sr S V u z + Cs * formTotal Md S u z) := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by
    rw [hU]
    exact mul_nonneg (meanStepConstant_nonneg hK hCh) (add_nonneg (curlTotal_nonneg hN u z)
      (mul_nonneg hc0 (formTotal_nonneg hN u z)))
  obtain ⟨TT, hTT⟩ : ∃ TT, TT = ∑ y ∈ cellBall S z 2, T y := ⟨_, rfl⟩
  have hTT0 : 0 ≤ TT := hTT ▸ Finset.sum_nonneg fun y _ => hT0 y
  rw [← hU, ← hTT]
  obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = K * (TT + U) := ⟨_, rfl⟩
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]
    positivity
  rw [← hBd]
  obtain ⟨M, hM⟩ : ∃ M, M = siteMean (sitePotential S V z u) := ⟨_, rfl⟩
  rw [← hM]
  have hσ0 := (hN.scale_pos z0).le
  have bondB : ∀ {y : F.Cell} {i : Fin 4}, y ∈ cellBall S z 2 → y + unitStep F.top i ∈ cellBall S z 2 →
      σ z0 * ‖M (y + unitStep F.top i) - M y‖ ≤ Bd := by
    intro y i hy hy'
    obtain ⟨hyS, d1⟩ := Finset.mem_filter.1 hy
    obtain ⟨hyS', d2⟩ := Finset.mem_filter.1 hy'
    have hy10 : y ∈ cellBall S z 10 := Finset.mem_filter.2 ⟨hyS, by omega⟩
    have hy10' : y + unitStep F.top i ∈ cellBall S z 10 := Finset.mem_filter.2 ⟨hyS', by omega⟩
    have hb : (y, i) ∈ innerBonds S F.top :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_sitesOfCells_top.2 hyS, Finset.mem_univ _⟩,
        mem_sitesOfCells_top.2 hyS'⟩
    have t1 := hTop (y, i) hb (by simpa [enclosingCell_self] using hy10) (by simpa [enclosingCell_self] using hy10')
    have t2 := norm_siteMean_step_le (Sr := Sr) (Md := Md) (σ := σ) h hF hk hK hN hz u hy10 hy10' t1
    rw [← hU, ← hM] at t2
    have t3 := hT (y, i) hb
    simp only [] at t3
    have t4 : T y ≤ TT := by
      rw [hTT]
      exact Finset.single_le_sum (f := T) (fun y _ => hT0 y) hy
    have t5 : σ y * ‖M (y + unitStep F.top i) - M y‖ ≤ TT + U := by linarith
    have dz : cellSupDist z0 y ≤ 22 := by
      have a1 := cellSupDist_triangle z0 z y
      rw [cellSupDist_symm z0 z] at a1
      omega
    have s1 := hN.scale_le_of_near z0 y dz
    have s2 := mul_le_mul_of_nonneg_right s1 (norm_nonneg (M (y + unitStep F.top i) - M y))
    have s3 := mul_le_mul_of_nonneg_left t5 hK
    rw [hBd]
    calc _ ≤ K * σ y * ‖M (y + unitStep F.top i) - M y‖ := s2
      _ = K * (σ y * ‖M (y + unitStep F.top i) - M y‖) := by ring
      _ ≤ _ := s3
  obtain ⟨Good, hGood⟩ : ∃ Good : Lattice4 → Prop,
      Good = fun v => localCell S z v ∈ S ∧ ∀ i, |v i| ≤ 2 := ⟨_, rfl⟩
  have near : ∀ {v : Lattice4}, Good v → localCell S z v ∈ cellBall S z 2 := by
    intro v hv
    rw [hGood] at hv
    refine Finset.mem_filter.2 ⟨hv.1, ?_⟩
    have := cellSupDist_add_le (r := 2) h.ambient z (a := fun i => closedOrthant S z i * v i) (by norm_num)
      (fun i => by
        rw [abs_mul, abs_closedOrthant he, one_mul]
        exact_mod_cast hv.2 i)
    rw [cellSupDist_symm]
    exact this
  have hstep : ∀ v i, Good v → Good (v + basisVector i) →
      σ z0 * ‖(fun v => M (localCell S z v)) (v + basisVector i) - (fun v => M (localCell S z v)) v‖ ≤ Bd := by
    intro v i g1 g2
    have n1 := near g1
    have n2 := near g2
    have e1 : (fun k => closedOrthant S z k * basisVector i k) = (closedOrthant S z i) • basisVector i := by
      funext k
      simp only [basisVector, Pi.smul_apply, smul_eq_mul]
      by_cases hk : k = i
      · subst hk; rfl
      · simp [hk]
    have e2 := localCell_add (S := S) (z := z) v (basisVector i)
    rw [e1] at e2
    simp only []
    rcases he i with hs | hs
    · rw [hs, one_smul] at e2
      have e3 : localCell S z (v + basisVector i) = localCell S z v + unitStep F.top i := e2
      rw [e3]
      rw [e3] at n2
      exact bondB n1 n2
    · rw [hs] at e2
      have e3 : localCell S z v = localCell S z (v + basisVector i) + unitStep F.top i := by
        rw [e2, neg_smul, one_smul, siteOfCoords_neg]
        have : siteOfCoords (F := F) F.top (basisVector i) = unitStep F.top i := rfl
        rw [this]
        abel
      rw [norm_sub_rev]
      have b1 := n1
      rw [e3] at b1
      have := bondB n2 b1
      rwa [← e3] at this
  obtain ⟨v0, hv0⟩ : ∃ v0 : Lattice4, v0 = fun i => closedOrthant S z i * cellDisplacement z z0 i := ⟨_, rfl⟩
  have hv0b : ∀ i, |v0 i| ≤ 2 := by
    intro i
    rw [hv0]
    simp only []
    rw [abs_mul, abs_closedOrthant he, one_mul]
    have h1 : (cellDisplacement z z0 i).natAbs ≤ cellSupDist z0 z := natAbs_valMinAbs_le_cellSupDist z0 z i
    rw [cellSupDist_symm] at h1
    have h2 : (cellDisplacement z z0 i).natAbs ≤ 2 := h1.trans hd
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h2
  have hLv0 : localCell S z v0 = z0 := by
    have e : (fun i => closedOrthant S z i * v0 i) = cellDisplacement z z0 := by
      funext i
      rw [hv0]
      simp only []
      rw [← mul_assoc, closedOrthant_mul_self he, one_mul]
    simp only [localCell, e]
    exact (eq_add_siteOfCoords_cellDisplacement z z0).symm
  have hL0 : localCell S z (0 : Lattice4) = z := by
    have e : (fun i => closedOrthant S z i * (0 : Lattice4) i) = (0 : Lattice4) := by
      funext i
      simp
    simp only [localCell, e, siteOfCoords_zero, add_zero]
  obtain ⟨vp, hvp⟩ : ∃ vp : Lattice4, vp = fun i => max 0 (v0 i) := ⟨_, rfl⟩
  have hvp2 : ∀ i, vp i ≤ 2 := fun i => by
    rw [hvp]
    exact max_le (by norm_num) (abs_le.1 (hv0b i)).2
  have hvp0 : ∀ i, 0 ≤ vp i := fun i => by
    rw [hvp]
    exact le_max_left _ _
  have hvpv : ∀ i, v0 i ≤ vp i := fun i => by
    rw [hvp]
    exact le_max_right _ _
  have closed := h.isOrthantClosedNear z
  have good1 : ∀ w : Lattice4, (∀ i, (0 : Lattice4) i ≤ w i ∧ w i ≤ vp i) → Good w := by
    intro w hw
    rw [hGood]
    refine ⟨?_, fun i => ?_⟩
    · have := closed z hz (by simp [cellSupDist]) (fun i => closedOrthant S z i * w i) (fun i => ?_) (fun i => ?_)
      · exact this
      · rw [← mul_assoc, closedOrthant_mul_self he, one_mul]
        exact (hw i).1
      · rw [abs_mul, abs_closedOrthant he, one_mul]
        have a := hw i
        have b := hvp2 i
        simp only [Pi.zero_apply] at a
        rw [abs_le]
        constructor <;> omega
    · have a := hw i
      have b := hvp2 i
      simp only [Pi.zero_apply] at a
      rw [abs_le]
      constructor <;> omega
  have good2 : ∀ w : Lattice4, (∀ i, v0 i ≤ w i ∧ w i ≤ vp i) → Good w := by
    intro w hw
    rw [hGood]
    refine ⟨?_, fun i => ?_⟩
    · have e := localCell_add (S := S) (z := z) v0 (w - v0)
      rw [add_sub_cancel, hLv0] at e
      rw [e]
      have hd' : cellSupDist z0 z ≤ 32 := by rw [cellSupDist_symm]; omega
      refine closed z0 hz0 hd' _ (fun i => ?_) (fun i => ?_)
      · rw [← mul_assoc, closedOrthant_mul_self he, one_mul]
        have := (hw i).1
        simp only [Pi.sub_apply]
        omega
      · rw [abs_mul, abs_closedOrthant he, one_mul]
        have a := hw i
        have b := hvp2 i
        have c := abs_le.1 (hv0b i)
        simp only [Pi.sub_apply]
        rw [abs_le]
        constructor <;> omega
    · have a := hw i
      have b := hvp2 i
      have c := abs_le.1 (hv0b i)
      rw [abs_le]
      constructor <;> omega
  have sum1 : (0 : ℤ) ≤ ∑ i, (vp i - (0 : Lattice4) i) := Finset.sum_nonneg fun i _ => by simpa using hvp0 i
  have sum2 : (0 : ℤ) ≤ ∑ i, (vp i - v0 i) := Finset.sum_nonneg fun i _ => by
    have := hvpv i
    omega
  have le1 : ∑ i, (vp i - (0 : Lattice4) i) ≤ 8 := by
    calc _ ≤ ∑ _i : Fin 4, (2 : ℤ) := Finset.sum_le_sum fun i _ => by simpa using hvp2 i
      _ = 8 := by simp
  have le2 : ∑ i, (vp i - v0 i) ≤ 16 := by
    calc _ ≤ ∑ _i : Fin 4, (4 : ℤ) := Finset.sum_le_sum fun i _ => by
          have a := hvp2 i
          have c := abs_le.1 (hv0b i)
          omega
      _ = 16 := by simp
  obtain ⟨d1, hd1⟩ : ∃ d1 : ℕ, (d1 : ℤ) = ∑ i, (vp i - (0 : Lattice4) i) := ⟨_, Int.toNat_of_nonneg sum1⟩
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℕ, (d2 : ℤ) = ∑ i, (vp i - v0 i) := ⟨_, Int.toNat_of_nonneg sum2⟩
  have p1 : σ z0 * ‖M (localCell S z vp) - M (localCell S z 0)‖ ≤ d1 * Bd :=
    norm_sub_le_of_monotone_path (fun v => M (localCell S z v)) hσ0 hBd0 Good hstep d1 0 vp (fun i => hvp0 i)
      hd1.symm good1
  have p2 : σ z0 * ‖M (localCell S z vp) - M (localCell S z v0)‖ ≤ d2 * Bd :=
    norm_sub_le_of_monotone_path (fun v => M (localCell S z v)) hσ0 hBd0 Good hstep d2 v0 vp hvpv hd2.symm good2
  rw [hL0] at p1
  rw [hLv0] at p2
  have hzero : M z = 0 := by
    rw [hM]
    exact siteMean_self_eq_zero h hz u
  rw [hzero, sub_zero] at p1
  have r1 : (d1 : ℝ) ≤ 8 := by
    have : (d1 : ℤ) ≤ 8 := hd1 ▸ le1
    exact_mod_cast this
  have r2 : (d2 : ℝ) ≤ 16 := by
    have : (d2 : ℤ) ≤ 16 := hd2 ▸ le2
    exact_mod_cast this
  have q1 := mul_le_mul_of_nonneg_right r1 hBd0
  have q2 := mul_le_mul_of_nonneg_right r2 hBd0
  have t1 := norm_sub_le (M (localCell S z vp)) (M (localCell S z vp) - M z0)
  rw [sub_sub_cancel] at t1
  have t2 := mul_le_mul_of_nonneg_left t1 hσ0
  rw [mul_add] at t2
  linarith
end Join
end PotentialMeans
end YangMills.Construction
end
