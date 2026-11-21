import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.SumsOverTheEvaluations
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
open YangMills.Construction.EvaluationSums
variable {F : BlockFrame} {S : Finset F.Cell} {j : ℕ}
open Classical in
def bondsOnRegion (S R : Finset F.Cell) (j : ℕ) : Finset (F.Site j × Fin 4) :=
  (innerBonds S j).filter fun b => enclosingCell b.1 ∈ R ∧ enclosingCell (b.1 + unitStep j b.2) ∈ R
def QuarticBound (S R : Finset F.Cell) (Q : ℝ) (e : VariationSlot F → ℝ) : Prop :=
  ∀ j, j < F.top → ∑ b ∈ bondsOnRegion S R j, e (slotOfBond j b.1 b.2) ^ 4 ≤ Q ^ 4 ∧
    ∑ y ∈ sitesOfCells R (j + 1), e (slotOfLink j y) ^ 4 ≤ Q ^ 4
def ScaledQuarticBound (S R : Finset F.Cell) (P : ℝ) (f : VariationSlot F → ℝ) : Prop :=
  ∀ j, j < F.top → _root_.YangMills.Construction.EvaluationSums.levelScale F j ^ 4 * ∑ b ∈ bondsOnRegion S R j, f (slotOfBond j b.1 b.2) ^ 4 ≤ P ^ 4 ∧
    _root_.YangMills.Construction.EvaluationSums.levelScale F j ^ 4 * ∑ y ∈ sitesOfCells R (j + 1), f (slotOfLink j y) ^ 4 ≤ P ^ 4
theorem sqrt_le_sq_of_le_pow_four {A P : ℝ} (hP : 0 ≤ P) (h : A ≤ P ^ 4) : √A ≤ P ^ 2 := by
  have : √A ≤ √(P ^ 4) := Real.sqrt_le_sqrt h
  have e : P ^ 4 = (P ^ 2) ^ 2 := by ring
  rwa [e, Real.sqrt_sq (by positivity)] at this
theorem mul_sqrt_sum_sq_le_of_quartic {ι : Type} (s : Finset ι) (f e g : ι → ℝ) {ℓ P Q : ℝ} (hℓ : 0 ≤ ℓ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h1 : ℓ ^ 4 * ∑ i ∈ s, f i ^ 4 ≤ P ^ 4) (h2 : ∑ i ∈ s, e i ^ 4 ≤ Q ^ 4) (hf : ∀ i ∈ s, 0 ≤ f i)
    (he : ∀ i ∈ s, 0 ≤ e i) (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ f i * e i) :
    ℓ * √(∑ i ∈ s, g i ^ 2) ≤ P * Q := by
  set Af := ∑ i ∈ s, f i ^ 4 with hAf
  set Ae := ∑ i ∈ s, e i ^ 4 with hAe
  have h3 : ∑ i ∈ s, g i ^ 2 ≤ √Af * √Ae := by
    have h4 : ∑ i ∈ s, g i ^ 2 ≤ ∑ i ∈ s, f i ^ 2 * e i ^ 2 := by
      refine Finset.sum_le_sum fun i hi => ?_
      obtain ⟨a, b⟩ := hg i hi
      have : g i ^ 2 ≤ (f i * e i) ^ 2 := pow_le_pow_left₀ a b 2
      rwa [mul_pow] at this
    refine h4.trans ((Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans (le_of_eq ?_))
    simp only [hAf, hAe]
    congr 2 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have h5 : √Ae ≤ Q ^ 2 := sqrt_le_sq_of_le_pow_four hQ h2
  have h6 : ℓ ^ 2 * √Af ≤ P ^ 2 := by
    have := sqrt_le_sq_of_le_pow_four hP h1
    rwa [Real.sqrt_mul (by positivity), show ℓ ^ 4 = (ℓ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)] at this
  have h7 : ℓ ^ 2 * ∑ i ∈ s, g i ^ 2 ≤ (P * Q) ^ 2 := by
    calc _ ≤ ℓ ^ 2 * (√Af * √Ae) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (ℓ ^ 2 * √Af) * √Ae := by ring
      _ ≤ P ^ 2 * Q ^ 2 := mul_le_mul h6 h5 (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have h8 : ℓ * √(∑ i ∈ s, g i ^ 2) = √(ℓ ^ 2 * ∑ i ∈ s, g i ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hℓ]
  rw [h8]
  refine (Real.sqrt_le_sqrt h7).trans ?_
  rw [Real.sqrt_sq (by positivity)]
theorem scaled_sqrt_sum_sq_le {R : Finset F.Cell} {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) {f e g : VariationSlot F → ℝ} (hf : ∀ u, 0 ≤ f u)
    (he : ∀ u, 0 ≤ e u) (hg0 : ∀ u, 0 ≤ g u) (hg : ∀ u, g u ≤ f u * e u) (hF : ScaledQuarticBound S R P f) (hE : QuarticBound S R Q e) :
    (∀ j, j < F.top → _root_.YangMills.Construction.EvaluationSums.levelScale F j * √(∑ b ∈ bondsOnRegion S R j, g (slotOfBond j b.1 b.2) ^ 2) ≤ P * Q) ∧
      ∀ j, j < F.top → _root_.YangMills.Construction.EvaluationSums.levelScale F j * √(∑ y ∈ sitesOfCells R (j + 1), g (slotOfLink j y) ^ 2) ≤ P * Q := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have h1 := (hF j hj).1
    have h2 := (hE j hj).1
    exact mul_sqrt_sum_sq_le_of_quartic (bondsOnRegion S R j) (fun b : F.Site j × Fin 4 => f (slotOfBond j b.1 b.2))
      (fun b : F.Site j × Fin 4 => e (slotOfBond j b.1 b.2)) (fun b : F.Site j × Fin 4 => g (slotOfBond j b.1 b.2))
      (levelScale_nonneg F j) hP hQ h1 h2 (fun b _ => hf (slotOfBond j b.1 b.2))
      (fun b _ => he (slotOfBond j b.1 b.2)) fun b _ => ⟨hg0 (slotOfBond j b.1 b.2), hg (slotOfBond j b.1 b.2)⟩
  · have h1 := (hF j hj).2
    have h2 := (hE j hj).2
    exact mul_sqrt_sum_sq_le_of_quartic (sitesOfCells R (j + 1)) (fun y : F.Site (j + 1) => f (slotOfLink j y))
      (fun y : F.Site (j + 1) => e (slotOfLink j y)) (fun y : F.Site (j + 1) => g (slotOfLink j y))
      (levelScale_nonneg F j) hP hQ h1 h2 (fun y _ => hf (slotOfLink j y))
      (fun y _ => he (slotOfLink j y)) fun y _ => ⟨hg0 (slotOfLink j y), hg (slotOfLink j y)⟩
theorem enclosingCell_of_mem_sitesOfCells_singleton {x : F.Site j} {v : F.Cell} (hodd : Odd F.blockSide)
    (hx : x ∈ sitesOfCells {v} j) : enclosingCell x = v := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  obtain rfl : y = v := by simpa using hy
  exact LocalPartition.enclosingCell_cellCentre_add hodd y h hh
theorem mem_sitesOfCells_of_enclosingCell_mem {R : Finset F.Cell} (hodd : Odd F.blockSide) {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) (hc : enclosingCell x ∈ R) : x ∈ sitesOfCells R j := by
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hx
  have : enclosingCell x = y := by rw [e]; exact LocalPartition.enclosingCell_cellCentre_add hodd y h hh
  exact mem_sitesOfCells.2 ⟨y, this ▸ hc, h, hh, e⟩
theorem mem_sitesOfCells_mono {R R' : Finset F.Cell} (h : R ⊆ R') {x : F.Site j} (hx : x ∈ sitesOfCells R j) :
    x ∈ sitesOfCells R' j := by
  obtain ⟨y, hy, a, ha, e⟩ := mem_sitesOfCells.1 hx
  exact mem_sitesOfCells.2 ⟨y, h hy, a, ha, e⟩
theorem card_sitesOfCells_le (hodd : Odd F.blockSide) (R : Finset F.Cell) (j : ℕ) :
    ((sitesOfCells R j).card : ℝ) ≤ R.card * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 4 := by
  classical
  have h1 : (sitesOfCells R j).card ≤ R.card * (F.blockSide ^ (F.top - j)) ^ 4 := by
    unfold sitesOfCells
    refine Finset.card_biUnion_le_card_mul _ _ _ fun z _ => ?_
    refine Finset.card_image_le.trans (le_of_eq ?_)
    exact LatticePaths.card_centredCube (Odd.pow hodd)
  exact_mod_cast h1
theorem levelScale_mul_pow (hL : 0 < F.blockSide) (j : ℕ) : _root_.YangMills.Construction.EvaluationSums.levelScale F j * (F.blockSide : ℝ) ^ (F.top - j) = 1 := by
  have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
  unfold _root_.YangMills.Construction.EvaluationSums.levelScale
  rw [← mul_pow, one_div, inv_mul_cancel₀ this.ne', one_pow]
theorem levelScale_mul_blockSide (hL : 0 < F.blockSide) {j : ℕ} (hj : j < F.top) :
    _root_.YangMills.Construction.EvaluationSums.levelScale F j * F.blockSide = _root_.YangMills.Construction.EvaluationSums.levelScale F (j + 1) := by apply _root_.YangMills.Construction.ReferenceBounds.levelScale_mul_blockSide <;> assumption
theorem levelScale_le_succ (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top) : _root_.YangMills.Construction.EvaluationSums.levelScale F j ≤ _root_.YangMills.Construction.EvaluationSums.levelScale F (j + 1) := by
  have h : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  rw [← levelScale_mul_blockSide hodd.pos hj]
  exact le_mul_of_one_le_right (levelScale_nonneg F j) h
theorem levelScale_le_one (hodd : Odd F.blockSide) (j : ℕ) : _root_.YangMills.Construction.EvaluationSums.levelScale F j ≤ 1 := by
  have h : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  unfold _root_.YangMills.Construction.EvaluationSums.levelScale
  refine pow_le_one₀ (by positivity) ?_
  rw [one_div]
  exact inv_le_one_of_one_le₀ h
theorem card_bondsOnRegion_le (hodd : Odd F.blockSide) (R : Finset F.Cell) (j : ℕ) (hj : j ≤ F.top) :
    ((bondsOnRegion S R j).card : ℝ) ≤ 4 * (R.card * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 4) := by
  classical
  have h1 : bondsOnRegion S R j ⊆ sitesOfCells R j ×ˢ (Finset.univ : Finset (Fin 4)) := by
    intro b hb
    have hb' := Finset.mem_filter.1 hb
    refine Finset.mem_product.2
      ⟨mem_sitesOfCells_of_enclosingCell_mem hodd (ChartCoordinates.innerBonds_ends hb'.1).1 hb'.2.1, Finset.mem_univ _⟩
  have h2 := Finset.card_le_card h1
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h2
  have h3 : ((bondsOnRegion S R j).card : ℝ) ≤ (sitesOfCells R j).card * 4 := by exact_mod_cast h2
  have := card_sitesOfCells_le hodd R j
  nlinarith
theorem scaledQuarticBound_one (hodd : Odd F.blockSide) {R : Finset F.Cell} (hR : R.card ≤ 17 ^ 4) :
    ScaledQuarticBound S R 51 (fun _ : VariationSlot F => 1) := by
  have hRr : (R.card : ℝ) ≤ 17 ^ 4 := by exact_mod_cast hR
  intro j hj
  have hs := levelScale_nonneg F j
  constructor
  · simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 := card_bondsOnRegion_le (S := S) hodd R j hj.le
    have h2 : _root_.YangMills.Construction.EvaluationSums.levelScale F j ^ 4 * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 4 = 1 := by
      rw [← mul_pow, levelScale_mul_pow hodd.pos, one_pow]
    calc _ ≤ _root_.YangMills.Construction.EvaluationSums.levelScale F j ^ 4 * (4 * (R.card * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 4)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * R.card * (_root_.YangMills.Construction.EvaluationSums.levelScale F j ^ 4 * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 4) := by ring
      _ ≤ _ := by rw [h2]; norm_num; linarith
  · simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 := card_sitesOfCells_le hodd R (j + 1)
    have h2 : _root_.YangMills.Construction.EvaluationSums.levelScale F (j + 1) ^ 4 * ((F.blockSide : ℝ) ^ (F.top - (j + 1))) ^ 4 = 1 := by
      rw [← mul_pow, levelScale_mul_pow hodd.pos, one_pow]
    have h3 : _root_.YangMills.Construction.EvaluationSums.levelScale F j ^ 4 ≤ _root_.YangMills.Construction.EvaluationSums.levelScale F (j + 1) ^ 4 := pow_le_pow_left₀ hs (levelScale_le_succ hodd hj) 4
    calc _ ≤ _root_.YangMills.Construction.EvaluationSums.levelScale F (j + 1) ^ 4 * (R.card * ((F.blockSide : ℝ) ^ (F.top - (j + 1))) ^ 4) :=
          mul_le_mul h3 h1 (by positivity) (by positivity)
      _ = R.card * (_root_.YangMills.Construction.EvaluationSums.levelScale F (j + 1) ^ 4 * ((F.blockSide : ℝ) ^ (F.top - (j + 1))) ^ 4) := by ring
      _ ≤ _ := by rw [h2]; norm_num; linarith
end YangMills.Construction.BlockAverages.VariationRates
end
