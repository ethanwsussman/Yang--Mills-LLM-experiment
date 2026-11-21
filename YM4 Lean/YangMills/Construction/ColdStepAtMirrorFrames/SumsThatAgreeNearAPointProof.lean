import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbersProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace DecayingSums
variable {F : BlockFrame}
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem mem_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
def offset (z Y : F.Cell) : Fin 4 → ℤ := fun i => (Y i - z i).valMinAbs
theorem natAbs_offset_le (z Y : F.Cell) (i : Fin 4) : (offset z Y i).natAbs ≤ cellSupDist Y z :=
  Finset.le_sup (f := fun i => ((Y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
theorem add_siteOfCoords_offset (z Y : F.Cell) : z + siteOfCoords F.top (offset z Y) = Y := by
  funext i
  simp only [Pi.add_apply, siteOfCoords, offset, ZMod.coe_valMinAbs]
  ring
theorem offset_injective (z : F.Cell) : Function.Injective (offset z) := by
  intro Y Y' h
  rw [← add_siteOfCoords_offset z Y, ← add_siteOfCoords_offset z Y', h]
theorem valMinAbs_intCast_of_lt {p : ℕ} {A : ℤ} (h : 2 * |A| < p) : ((A : ZMod p)).valMinAbs = A := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.valMinAbs_intCast_of_two_mul_abs_lt <;> assumption
theorem offset_add_siteOfCoords (z : F.Cell) {h : Fin 4 → ℤ} (hh : ∀ i, 2 * |h i| < F.extent i) :
    offset z (z + siteOfCoords F.top h) = h := by
  funext i
  unfold offset
  simp only [Pi.add_apply, add_sub_cancel_left, siteOfCoords]
  exact valMinAbs_intCast_of_lt (by rw [period_top]; exact hh i)
def axisDecay (β : ℝ) (x : ℤ) : ℝ := Real.exp (-(β / 4 * |(x : ℝ)|))
theorem summable_axisDecay {β : ℝ} (hβ : 0 < β) : Summable (axisDecay β) := by
  have hg : Summable fun n : ℕ => (Real.exp (-(β / 4))) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by
      rw [Real.exp_lt_one_iff]
      linarith)
  have e : ∀ n : ℕ, Real.exp (-(β / 4)) ^ n = Real.exp (-(β / 4 * (n : ℝ))) := fun n => by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hg.congr fun n => ?_
    rw [e]
    simp [axisDecay]
  · refine hg.congr fun n => ?_
    rw [e]
    simp [axisDecay]
theorem exp_neg_mul_le_prod_axisDecay (β : ℝ) (hβ : 0 < β) (z Y : F.Cell) :
    Real.exp (-(β * cellSupDist Y z)) ≤ ∏ i, axisDecay β (offset z Y i) := by
  unfold axisDecay
  rw [← Real.exp_sum, Real.exp_le_exp]
  have h : ∀ i : Fin 4, |((offset z Y i : ℤ) : ℝ)| ≤ cellSupDist Y z := fun i => by
    have h1 := natAbs_offset_le z Y i
    have h2 : |((offset z Y i : ℤ) : ℝ)| = ((offset z Y i).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2]
    exact_mod_cast h1
  rw [Fin.sum_univ_four]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  nlinarith
theorem sum_exp_neg_le {β : ℝ} (hβ : 0 < β) (z : F.Cell) (S : Finset F.Cell) :
    ∑ Y ∈ S, Real.exp (-(β * cellSupDist Y z)) ≤ (∑' x, axisDecay β x) ^ 4 := by
  classical
  have hpos : ∀ x, 0 ≤ axisDecay β x := fun x => (Real.exp_pos _).le
  set t : Fin 4 → Finset ℤ := fun i => S.image fun Y => offset z Y i with ht
  calc ∑ Y ∈ S, Real.exp (-(β * cellSupDist Y z))
      ≤ ∑ Y ∈ S, ∏ i, axisDecay β (offset z Y i) :=
        Finset.sum_le_sum fun Y _ => exp_neg_mul_le_prod_axisDecay β hβ z Y
    _ = ∑ u ∈ S.image (offset z), ∏ i, axisDecay β (u i) :=
        (Finset.sum_image (f := fun u : Fin 4 → ℤ => ∏ i, axisDecay β (u i))
          fun _ _ _ _ h => offset_injective z h).symm
    _ ≤ ∑ u ∈ Fintype.piFinset t, ∏ i, axisDecay β (u i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun u _ _ => Finset.prod_nonneg fun i _ => hpos _
        intro u hu
        obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hu
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_image.mpr ⟨Y, hY, rfl⟩
    _ = ∏ i : Fin 4, ∑ x ∈ t i, axisDecay β x := (Finset.prod_univ_sum t fun _ x => axisDecay β x).symm
    _ ≤ ∏ _i : Fin 4, ∑' x, axisDecay β x := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun x _ => hpos x) fun i _ => ?_
        exact (summable_axisDecay hβ).sum_le_tsum _ fun x _ => hpos x
    _ = (∑' x, axisDecay β x) ^ 4 := by simp
def cube (R : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R
theorem mem_cube {R : ℕ} {h : Fin 4 → ℤ} : h ∈ cube R ↔ ∀ i, |h i| ≤ (R : ℤ) := by
  unfold cube
  rw [Fintype.mem_piFinset]
  simp only [Finset.mem_Icc, abs_le]
theorem cellSupDist_add_le (z : F.Cell) {h : Fin 4 → ℤ} {R : ℕ} (hh : ∀ i, |h i| ≤ (R : ℤ))
    (hs : ∀ i, 2 * R < F.extent i) : cellSupDist (z + siteOfCoords F.top h) z ≤ R := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.cellSupDist_add_siteOfCoords_le <;> assumption
open Classical in
theorem sum_near_eq_sum_cube (hw : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (R : ℕ) (hs : ∀ i, 2 * R < F.extent i)
    (G : F.Cell → ℝ) :
    ∑ Y ∈ (finiteCells F).filter (fun Y => cellSupDist Y z ≤ R), G Y =
      ∑ h ∈ cube R, G (z + siteOfCoords F.top h) := by
  refine Finset.sum_bij' (fun Y _ => offset z Y) (fun h _ => z + siteOfCoords F.top h) ?_ ?_ ?_ ?_ ?_
  · intro Y hY
    rw [mem_cube]
    intro i
    have h1 := natAbs_offset_le z Y i
    have h2 := (Finset.mem_filter.mp hY).2
    rw [Int.abs_eq_natAbs]
    omega
  · intro h hh
    rw [mem_cube] at hh
    exact Finset.mem_filter.mpr ⟨mem_finiteCells hw _, cellSupDist_add_le z hh hs⟩
  · intro Y _
    exact add_siteOfCoords_offset z Y
  · intro h hh
    rw [mem_cube] at hh
    exact offset_add_siteOfCoords z fun i => by
      have := hh i
      have := hs i
      omega
  · intro Y _
    rw [add_siteOfCoords_offset]
end DecayingSums
open DecayingSums in
theorem decayingSumsClose_holds : DecayingSumsClose := by
  classical
  intro β hβ
  have hM0 : 0 < (∑' x, axisDecay β x) := by
    have h1 : axisDecay β 0 ≤ ∑' x, axisDecay β x :=
      (summable_axisDecay hβ).le_tsum 0 fun x _ => (Real.exp_pos _).le
    have h2 : 0 < axisDecay β 0 := Real.exp_pos _
    linarith
  refine ⟨(∑' x, axisDecay β x) ^ 4, by positivity, fun F z _ => sum_exp_neg_le hβ z _, ?_⟩
  intro F F' G G' z z' R T A hw hw' hs hs' hT hA hnear hfar hfar'
  set M : ℝ := (∑' x, axisDecay β x) ^ 4 with hM
  set S := finiteCells F with hS
  set S' := finiteCells F' with hS'
  have split : ∀ {E : BlockFrame} (P : Finset E.Cell) (z₀ : E.Cell) (H : E.Cell → ℝ),
      ∑ Y ∈ P, H Y = ∑ Y ∈ P.filter (fun Y => cellSupDist Y z₀ ≤ R), H Y +
        ∑ Y ∈ P.filter (fun Y => ¬ cellSupDist Y z₀ ≤ R), H Y := fun P z₀ H =>
    (Finset.sum_filter_add_sum_filter_not P _ H).symm
  rw [split S z G, split S' z' G', sum_near_eq_sum_cube hw z R hs G, sum_near_eq_sum_cube hw' z' R hs' G']
  have hfarsum : ∀ {E : BlockFrame} (P : Finset E.Cell) (z₀ : E.Cell) (H : E.Cell → ℝ),
      (∀ Y, R < cellSupDist Y z₀ → |H Y| ≤ A * Real.exp (-(β * cellSupDist Y z₀))) →
      |∑ Y ∈ P.filter (fun Y => ¬ cellSupDist Y z₀ ≤ R), H Y| ≤ A * M := by
    intro E P z₀ H hH
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ Y ∈ P.filter (fun Y => ¬ cellSupDist Y z₀ ≤ R), |H Y|
        ≤ ∑ Y ∈ P.filter (fun Y => ¬ cellSupDist Y z₀ ≤ R), A * Real.exp (-(β * cellSupDist Y z₀)) :=
          Finset.sum_le_sum fun Y hY => hH Y (not_le.mp (Finset.mem_filter.mp hY).2)
      _ = A * ∑ Y ∈ P.filter (fun Y => ¬ cellSupDist Y z₀ ≤ R), Real.exp (-(β * cellSupDist Y z₀)) := by
          rw [Finset.mul_sum]
      _ ≤ A * M := mul_le_mul_of_nonneg_left (sum_exp_neg_le hβ z₀ _) hA
  have h1 := hfarsum S z G hfar
  have h2 := hfarsum S' z' G' hfar'
  have h3 : |∑ h ∈ cube R, G (z + siteOfCoords F.top h) - ∑ h ∈ cube R, G' (z' + siteOfCoords F'.top h)| ≤
      T * M := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ h ∈ cube R, |G (z + siteOfCoords F.top h) - G' (z' + siteOfCoords F'.top h)|
        ≤ ∑ h ∈ cube R, T * Real.exp (-(β * cellSupDist (z + siteOfCoords F.top h) z)) :=
          Finset.sum_le_sum fun h hh => hnear h (mem_cube.mp hh)
      _ = T * ∑ Y ∈ S.filter (fun Y => cellSupDist Y z ≤ R), Real.exp (-(β * cellSupDist Y z)) := by
          rw [sum_near_eq_sum_cube hw z R hs fun Y => Real.exp (-(β * cellSupDist Y z)), Finset.mul_sum]
      _ ≤ T * M := mul_le_mul_of_nonneg_left (sum_exp_neg_le hβ z _) hT
  rw [show ∀ a b c d : ℝ, a + b - (c + d) = (a - c) + (b - d) from fun a b c d => by ring]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add_right (abs_sub _ _) _).trans ?_
  nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
