import YangMills.Construction.HoleBesideASecondHole.CrowdedCellsAreFew
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours
namespace HoleSavings
namespace CrowdedCells
variable {F : BlockFrame}
theorem period_eq_pow_mul {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (k : Fin 4) :
    F.period i k = F.blockSide ^ (j - i) * F.period j k := by
  simp only [BlockFrame.period]
  have : F.top - i = (F.top - j) + (j - i) := by omega
  rw [this, pow_add]
  ring
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by
  simp [siteCoords]
theorem mem_centredCube_iff {M : ℕ} {o : Fin 4 → ℤ} :
    o ∈ centredCube M ↔ ∀ m, |o m| ≤ ((M : ℤ) - 1) / 2 := by
  simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
theorem odd_blockSide_pow (hL : Odd F.blockSide) (e : ℕ) : Odd (F.blockSide ^ e) := hL.pow
theorem sum_sum_le_mul_sum {A B : Type} (Ps : Finset A) (Q : Finset B) (Qp : A → Finset B) (G : B → ℝ)
    (hG : ∀ q, 0 ≤ G q) (K : ℕ) (hsub : ∀ p ∈ Ps, Qp p ⊆ Q)
    (hmul : ∀ q ∈ Q, ∀ [DecidablePred fun p => q ∈ Qp p], ((Ps.filter fun p => q ∈ Qp p).card) ≤ K) :
    ∑ p ∈ Ps, ∑ q ∈ Qp p, G q ≤ K * ∑ q ∈ Q, G q := by
  classical
  calc ∑ p ∈ Ps, ∑ q ∈ Qp p, G q
      = ∑ p ∈ Ps, ∑ q ∈ Q, (if q ∈ Qp p then G q else 0) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (hsub p hp)]
    _ = ∑ q ∈ Q, ∑ p ∈ Ps, (if q ∈ Qp p then G q else 0) := Finset.sum_comm
    _ ≤ ∑ q ∈ Q, (K : ℝ) * G q := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmul q hq) (hG q)
    _ = _ := (Finset.mul_sum _ _ _).symm
theorem eq_of_mem_sitesBelow {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (hL : Odd F.blockSide)
    {x : F.Site i} {y y' : F.Site j}
    (hx : x ∈ sitesBelow i y) (hx' : x ∈ sitesBelow i y') : y = y' := by
  obtain ⟨h, hh, e1⟩ := Finset.mem_image.1 hx
  obtain ⟨h', hh', e2⟩ := Finset.mem_image.1 hx'
  have a1 := mem_centredCube_iff.1 hh
  have a2 := mem_centredCube_iff.1 hh'
  obtain ⟨q, hq⟩ := odd_blockSide_pow hL (j - i)
  set B := F.blockSide ^ (j - i) with hB
  have hBc : (F.blockSide : ℤ) ^ (j - i) = (B : ℤ) := by rw [hB]; push_cast; rfl
  have hhalf : ((B : ℤ) - 1) / 2 = q := by
    rw [hq]
    push_cast
    omega
  rw [hhalf] at a1 a2
  funext k
  have ek := congrFun (e1.trans e2.symm) k
  simp only [siteOfCoords, hBc] at ek
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_eq_pow_mul hij hj k] at ek
  push_cast at ek
  rw [hBc] at ek
  have hd : (B : ℤ) ∣ h' k - h k := by
    have h3 : (B : ℤ) ∣ (B : ℤ) * siteCoords y' k + h' k - ((B : ℤ) * siteCoords y k + h k) :=
      dvd_trans (Dvd.intro _ rfl) ek
    have h4 : (B : ℤ) * siteCoords y' k + h' k - ((B : ℤ) * siteCoords y k + h k) =
        (B : ℤ) * (siteCoords y' k - siteCoords y k) + (h' k - h k) := by ring
    rw [h4] at h3
    exact (dvd_add_right (Dvd.intro _ rfl)).1 h3
  have hz : h' k - h k = 0 := by
    have b1 := abs_le.1 (a1 k)
    have b2 := abs_le.1 (a2 k)
    refine Int.eq_zero_of_abs_lt_dvd hd ?_
    rw [abs_lt]
    constructor <;> omega
  have h4 : (B : ℤ) * siteCoords y' k + h' k - ((B : ℤ) * siteCoords y k + h k) =
      (B : ℤ) * (siteCoords y' k - siteCoords y k) := by
    have : h' k = h k := by omega
    rw [this]
    ring
  rw [h4] at ek
  have hB0 : (B : ℤ) ≠ 0 := by omega
  have h5 := (mul_dvd_mul_iff_left hB0).1 ek
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, siteCoords_cast, siteCoords_cast] at h5
  exact h5
theorem card_centredCube (M : ℕ) (hM : Odd M) : ((centredCube M).card : ℝ) = (M : ℝ) ^ 4 := by
  have h : ∀ i : Fin 4, (Finset.Icc (-(((M : ℤ) - 1) / 2)) (((M : ℤ) - 1) / 2)).card = M := by
    intro i
    rw [Int.card_Icc]
    obtain ⟨k, rfl⟩ := hM
    push_cast
    omega
  calc ((centredCube M).card : ℝ) = ((∏ i : Fin 4,
        (Finset.Icc (-(((M : ℤ) - 1) / 2)) (((M : ℤ) - 1) / 2)).card : ℕ) : ℝ) := by
        rw [centredCube, Fintype.card_piFinset]
    _ = ((∏ _i : Fin 4, M : ℕ) : ℝ) := by rw [Finset.prod_congr rfl fun i _ => h i]
    _ = _ := by simp
theorem abs_offsetFromCentre_le {L : ℕ} (hL : Odd L) (c : ℤ) :
    |offsetFromCentre L c| ≤ ((L : ℤ) - 1) / 2 := by
  obtain ⟨q, rfl⟩ := hL
  have hh : (((2 * q + 1 : ℕ) : ℤ) - 1) / 2 = q := by
    push_cast
    omega
  unfold offsetFromCentre
  rw [hh]
  have h1 := Int.emod_nonneg (c + q) (show ((2 * q + 1 : ℕ) : ℤ) ≠ 0 by positivity)
  have h2 := Int.emod_lt_of_pos (c + q) (show (0 : ℤ) < ((2 * q + 1 : ℕ) : ℤ) by positivity)
  push_cast at h1 h2 ⊢
  rw [abs_le]
  constructor <;> omega
theorem lumpOf_nonempty {L : ℕ} (hL : Odd L) (g : LumpGrid L) {j : ℕ} (x : F.Site j) :
    (lumpOf g x).Nonempty := by
  refine ⟨siteOfCoords j _, Finset.mem_image.2 ⟨fun i => siteCoords x i - offsetFromCentre L (siteCoords x i) +
      g.lower (offsetFromCentre L (siteCoords x i)),
    Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨le_rfl, ?_⟩, rfl⟩⟩
  have := g.mem_interval _ (abs_offsetFromCentre_le hL (siteCoords x i))
  linarith [this.2.1, this.2.2.1]
theorem nonempty_of_mem_hotLumps {L : ℕ} (hL : Odd L) (g : LumpGrid L) (s : ℝ) {j : ℕ}
    (X : Finset (F.Site j)) (W : F.GaugeField j)
    {l : Finset (F.Site j)} (hl : l ∈ hotLumps g s X W) : l.Nonempty := by
  simp only [hotLumps, Finset.mem_biUnion, Finset.mem_image] at hl
  obtain ⟨p, _, x, _, rfl⟩ := hl
  exact lumpOf_nonempty hL g x
theorem card_cellBall_two_le (y : F.Cell) : (cellBall y 2).card ≤ 625 := by
  unfold cellBall
  refine Finset.card_image_le.trans ?_
  have h := card_centredCube (2 * 2 + 1) ⟨2, by norm_num⟩
  have : (centredCube (2 * 2 + 1)).card = 625 := by
    have h2 : ((centredCube (2 * 2 + 1)).card : ℝ) = ((625 : ℕ) : ℝ) := by
      rw [h]
      norm_num
    exact_mod_cast h2
  omega
theorem mem_cellBall_two_comm (y y' : F.Cell) (h : y' ∈ cellBall y 2) : y ∈ cellBall y' 2 := by
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.1 h
  refine Finset.mem_image.2 ⟨fun i => - o i, ?_, ?_⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    have := mem_centredCube_iff.1 ho k
    simpa using this
  · funext k
    simp [siteOfCoords]
attribute [local irreducible] cellBall
theorem exists_cell_of_mem_nearbyLumps (h : Finset (Finset (F.Site F.depth))) (y : F.Cell)
    (l : Finset (F.Site F.depth)) (hl : l ∈ nearbyLumps h y) (x : F.Site F.depth) (hx : x ∈ l) :
    ∃ y', y' ∈ cellBall y 2 ∧ x ∈ sitesBelow F.depth y' := by
  simp only [nearbyLumps, Finset.mem_filter] at hl
  have h1 := Finset.mem_of_subset hl.2 hx
  simp only [cutBelow, Finset.mem_biUnion] at h1
  obtain ⟨y', h2, h3⟩ := h1
  exact ⟨y', h2, h3⟩
end CrowdedCells
set_option maxRecDepth 100000 in
theorem crowdedCellsBound_holds : CrowdedCellsBound := by
  classical
  intro F L g a s θ J₀ D hFL hL hT
  subst hFL
  have h1 := CrowdedCells.sum_sum_le_mul_sum (D.crowdedCells) D.hotFineLumps
    (nearbyLumps D.hotFineLumps) (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) 625 (fun y _ => Finset.filter_subset _ _) ?_
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    have h2 : ((J₀ * (D.crowdedCells).card : ℕ) : ℝ) ≤
        ∑ y ∈ D.crowdedCells, ((nearbyLumps D.hotFineLumps y).card : ℝ) := by
      have : ∀ y ∈ D.crowdedCells, (J₀ : ℝ) ≤ ((nearbyLumps D.hotFineLumps y).card : ℝ) := by
        intro y hy
        exact_mod_cast (Finset.mem_filter.1 hy).2
      have h3 := Finset.sum_le_sum this
      simp only [Finset.sum_const, nsmul_eq_mul] at h3
      push_cast
      linarith
    have := h2.trans h1
    exact_mod_cast this
  · intro l hl _
    obtain ⟨x0, hx0⟩ := CrowdedCells.nonempty_of_mem_hotLumps hL g s _ D.fineField hl
    by_cases hne : ∃ y ∈ D.crowdedCells, l ∈ nearbyLumps D.hotFineLumps y
    · obtain ⟨y1, _, hy1⟩ := hne
      have hblock : ∀ y, l ∈ nearbyLumps D.hotFineLumps y →
          ∃ y', y' ∈ cellBall y 2 ∧ x0 ∈ sitesBelow F.depth y' := by
        intro y hy
        exact CrowdedCells.exists_cell_of_mem_nearbyLumps D.hotFineLumps y l hy x0 hx0
      obtain ⟨y0, _, hy0⟩ := hblock y1 hy1
      have hsub : ((D.crowdedCells).filter fun y => l ∈ nearbyLumps D.hotFineLumps y) ⊆ cellBall y0 2 := by
        intro y hy
        obtain ⟨y', h1, h2⟩ := hblock y (Finset.mem_filter.1 hy).2
        have e := CrowdedCells.eq_of_mem_sitesBelow (by show F.depth ≤ F.depth + 1; omega) le_rfl hL h2 hy0
        rw [e] at h1
        exact CrowdedCells.mem_cellBall_two_comm _ _ h1
      exact (Finset.card_le_card hsub).trans (CrowdedCells.card_cellBall_two_le y0)
    · have : ((D.crowdedCells).filter fun y => l ∈ nearbyLumps D.hotFineLumps y) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun y hy h => hne ⟨y, hy, h⟩
      rw [this]
      simp
end HoleSavings
end YangMills.Construction
end
