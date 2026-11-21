import YangMills.Construction.LawInAState.FormsDominatedBySites
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open Matrix
namespace YangMills.Construction.QuadraticConcentration
section SiteDomination
variable {ι V S : Type} [Fintype ι] [DecidableEq ι] [Fintype S]
  {g : ι → S → ℝ} {Y : V → Finset S} {M : V → Matrix ι ι ℝ} {Near : V → V → Prop} {In : Set ι}
  {c₀ G Nc τ τ₂ : ℝ}
private def siteEntryBound (g : ι → S → ℝ) (Y : V → Finset S) (c₀ : ℝ) (v : V) (i j : ι) : ℝ := c₀ * ∑ y ∈ Y v, g i y * g j y
private def siteMass (g : ι → S → ℝ) (Y : V → Finset S) (v : V) (i : ι) : ℝ := ∑ y ∈ Y v, g i y
private lemma siteMass_nonneg (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (v : V) (i : ι) : 0 ≤ siteMass g Y v i :=
  Finset.sum_nonneg fun y _ => H.nonneg i y
private lemma siteMass_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (v : V) (i : ι) : siteMass g Y v i ≤ G :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ => H.nonneg i y).trans (H.row_sum_le i)
private lemma sum_siteMass_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (hG : 0 ≤ G) (v : V) :
    ∑ i, siteMass g Y v i ≤ Nc * G := by
  simp only [siteMass]
  rw [Finset.sum_comm]
  calc ∑ y ∈ Y v, ∑ i, g i y ≤ ∑ _y ∈ Y v, G := Finset.sum_le_sum fun y _ => H.col_sum_le y
    _ = (Y v).card * G := by simp
    _ ≤ Nc * G := mul_le_mul_of_nonneg_right (H.card_le v) hG
private lemma siteEntryBound_nonneg (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (v : V) (i j : ι) :
    0 ≤ siteEntryBound g Y c₀ v i j :=
  mul_nonneg h0 (Finset.sum_nonneg fun y _ => mul_nonneg (H.nonneg i y) (H.nonneg j y))
private lemma sum_siteEntryBound_le_mass (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hG : 0 ≤ G) (v : V) (i : ι) :
    ∑ j, siteEntryBound g Y c₀ v i j ≤ c₀ * G * siteMass g Y v i := by
  simp only [siteEntryBound, siteMass]
  calc ∑ j, c₀ * ∑ y ∈ Y v, g i y * g j y = c₀ * ∑ y ∈ Y v, g i y * ∑ j, g j y := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]
    _ ≤ c₀ * ∑ y ∈ Y v, g i y * G := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) h0
        exact mul_le_mul_of_nonneg_left (H.col_sum_le y) (H.nonneg i y)
    _ = c₀ * G * ∑ y ∈ Y v, g i y := by rw [← Finset.sum_mul]; ring
private lemma sum_siteEntryBound_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hG : 0 ≤ G) (v : V) (i : ι) :
    ∑ j, siteEntryBound g Y c₀ v i j ≤ c₀ * G ^ 2 := by
  refine (sum_siteEntryBound_le_mass H h0 hG v i).trans ?_
  have := siteMass_le H v i
  calc c₀ * G * siteMass g Y v i ≤ c₀ * G * G := mul_le_mul_of_nonneg_left this (by positivity)
    _ = c₀ * G ^ 2 := by ring
private lemma sum_abs_entry_row_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hG : 0 ≤ G) (v : V) (i : ι) :
    ∑ j, |M v i j| ≤ c₀ * G ^ 2 :=
  (Finset.sum_le_sum fun j _ => H.entry_le v i j).trans (sum_siteEntryBound_le H h0 hG v i)
private lemma entry_comm (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (v : V) (i j : ι) : M v i j = M v j i := by
  have := congrFun (congrFun (H.symm v) i) j
  simpa [Matrix.transpose_apply] using this.symm
private lemma sum_abs_entry_col_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hG : 0 ≤ G) (v : V) (j : ι) :
    ∑ i, |M v i j| ≤ c₀ * G ^ 2 := by
  simp_rw [entry_comm H v _ j]
  exact sum_abs_entry_row_le H h0 hG v j
private lemma mulVec_dotProduct_self_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hG : 0 ≤ G) (v : V) (t : ι → ℝ) :
    (M v).mulVec t ⬝ᵥ (M v).mulVec t ≤ c₀ * G ^ 2 * ∑ i, ∑ j, |M v i j| * t j ^ 2 := by
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.mul_sum]
  have e : (M v).mulVec t i = ∑ j, M v i j * t j := by simp [Matrix.mulVec, dotProduct]
  rw [e]
  have h1 : |∑ j, M v i j * t j| ≤ ∑ j, |M v i j| * |t j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
  have h2 : (∑ j, |M v i j| * |t j|) ^ 2 ≤ (∑ j, |M v i j|) * ∑ j, |M v i j| * t j ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun j _ => abs_nonneg _) (fun j _ => by positivity) fun j _ => ?_
    rw [mul_pow, sq_abs (t j)]; ring
  have h3 : (∑ j, M v i j * t j) * (∑ j, M v i j * t j) ≤ (∑ j, |M v i j| * |t j|) ^ 2 := by
    rw [← sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  refine h3.trans (h2.trans ?_)
  exact mul_le_mul_of_nonneg_right (sum_abs_entry_row_le H h0 hG v i) (Finset.sum_nonneg fun j _ => by positivity)
private lemma dotProduct_mulVec_sq_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hG : 0 ≤ G) (v : V) (s t : ι → ℝ) :
    (s ⬝ᵥ (M v).mulVec t) ^ 2 ≤ (c₀ * G ^ 2) ^ 2 * (s ⬝ᵥ s) * (t ⬝ᵥ t) := by
  have h1 : (s ⬝ᵥ (M v).mulVec t) ^ 2 ≤ (s ⬝ᵥ s) * ((M v).mulVec t ⬝ᵥ (M v).mulVec t) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ s ((M v).mulVec t)
    simpa only [dotProduct, sq] using this
  have h2 : ∑ i, ∑ j, |M v i j| * t j ^ 2 ≤ c₀ * G ^ 2 * (t ⬝ᵥ t) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    simp only [dotProduct, Finset.mul_sum, ← sq]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (sum_abs_entry_col_le H h0 hG v j) (by positivity)
  have hs : 0 ≤ s ⬝ᵥ s := by simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have ha : 0 ≤ c₀ * G ^ 2 := by positivity
  calc (s ⬝ᵥ (M v).mulVec t) ^ 2 ≤ (s ⬝ᵥ s) * ((M v).mulVec t ⬝ᵥ (M v).mulVec t) := h1
    _ ≤ (s ⬝ᵥ s) * (c₀ * G ^ 2 * (c₀ * G ^ 2 * (t ⬝ᵥ t))) :=
        mul_le_mul_of_nonneg_left ((mulVec_dotProduct_self_le H h0 hG v t).trans (mul_le_mul_of_nonneg_left h2 ha)) hs
    _ = (c₀ * G ^ 2) ^ 2 * (s ⬝ᵥ s) * (t ⬝ᵥ t) := by ring
private lemma weighted_abs_sum_le_vectorMass (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hG : 0 ≤ G) (hN : 0 ≤ Nc) (ht2 : 0 ≤ τ₂)
    {φ₀ Fm : ℝ} (hφ : 0 ≤ φ₀) (hFm : 0 ≤ Fm) {F : ι → ℝ}
    (hIn : ∀ i ∈ In, |F i| ≤ φ₀) (hall : ∀ i, |F i| ≤ Fm) (v : V) :
    ∑ i, ∑ j, |M v i j| * F j ^ 2 ≤ vectorMass c₀ G Nc τ₂ φ₀ Fm := by
  classical
  have inner : ∀ y ∈ Y v, ∑ j, g j y * F j ^ 2 ≤ G * φ₀ ^ 2 + τ₂ * Fm ^ 2 := by
    intro y hy
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ In)]
    refine add_le_add ?_ ?_
    · calc ∑ j ∈ Finset.univ.filter (fun j => j ∈ In), g j y * F j ^ 2
          ≤ ∑ j ∈ Finset.univ.filter (fun j => j ∈ In), g j y * φ₀ ^ 2 := by
            refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (H.nonneg j y)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hIn j (Finset.mem_filter.1 hj).2) 2
        _ = (∑ j ∈ Finset.univ.filter (fun j => j ∈ In), g j y) * φ₀ ^ 2 := by rw [Finset.sum_mul]
        _ ≤ G * φ₀ ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => H.nonneg j y).trans (H.col_sum_le y)
    · calc ∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ In), g j y * F j ^ 2
          ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ In), g j y * Fm ^ 2 := by
            refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (H.nonneg j y)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hall j) 2
        _ = (∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ In), g j y) * Fm ^ 2 := by rw [Finset.sum_mul]
        _ ≤ τ₂ * Fm ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have := H.outside_mass_le v y hy
            convert this
  calc ∑ i, ∑ j, |M v i j| * F j ^ 2 ≤ ∑ i, ∑ j, siteEntryBound g Y c₀ v i j * F j ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (H.entry_le v i j) (by positivity)
    _ = c₀ * ∑ y ∈ Y v, (∑ i, g i y) * ∑ j, g j y * F j ^ 2 := by
        have h1 : ∀ i, ∑ j, siteEntryBound g Y c₀ v i j * F j ^ 2 = c₀ * ∑ y ∈ Y v, g i y * ∑ j, g j y * F j ^ 2 := by
          intro i
          have : ∑ j, siteEntryBound g Y c₀ v i j * F j ^ 2 = c₀ * ∑ j, ∑ y ∈ Y v, g i y * (g j y * F j ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [siteEntryBound]
            rw [mul_assoc, Finset.sum_mul]
            congr 1
            exact Finset.sum_congr rfl fun y _ => by ring
          rw [this, Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]
        simp_rw [h1]
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun y _ => by rw [Finset.sum_mul]
    _ ≤ c₀ * ∑ _y ∈ Y v, G * (G * φ₀ ^ 2 + τ₂ * Fm ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y hy => ?_) h0
        exact mul_le_mul (H.col_sum_le y) (inner y hy) (Finset.sum_nonneg fun j _ => mul_nonneg (H.nonneg j y) (by positivity)) hG
    _ = c₀ * ((Y v).card * (G * (G * φ₀ ^ 2 + τ₂ * Fm ^ 2))) := by simp
    _ ≤ c₀ * (Nc * (G * (G * φ₀ ^ 2 + τ₂ * Fm ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (H.card_le v) (by positivity)) h0
    _ = vectorMass c₀ G Nc τ₂ φ₀ Fm := by simp only [vectorMass]; ring
private lemma abs_dotProduct_mulVec_self_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (v : V) (F : ι → ℝ) :
    |F ⬝ᵥ (M v).mulVec F| ≤ ∑ i, ∑ j, |M v i j| * F j ^ 2 := by
  have e : F ⬝ᵥ (M v).mulVec F = ∑ i, ∑ j, F i * (M v i j * F j) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have h1 : |∑ i, ∑ j, F i * (M v i j * F j)| ≤ ∑ i, ∑ j, |M v i j| * ((F i ^ 2 + F j ^ 2) / 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have : |F i * (M v i j * F j)| = |M v i j| * (|F i| * |F j|) := by rw [abs_mul, abs_mul]; ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    nlinarith [sq_nonneg (|F i| - |F j|), sq_abs (F i), sq_abs (F j)]
  have h2 : ∑ i, ∑ j, |M v i j| * F i ^ 2 = ∑ i, ∑ j, |M v i j| * F j ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [entry_comm H v j i]
  have h3 : ∑ i, ∑ j, |M v i j| * ((F i ^ 2 + F j ^ 2) / 2) =
      (1 / 2) * (∑ i, ∑ j, |M v i j| * F i ^ 2) + (1 / 2) * ∑ i, ∑ j, |M v i j| * F j ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  refine h1.trans (le_of_eq ?_)
  rw [h3, h2]; ring
private lemma trace_mul_self_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hG : 0 ≤ G) (hN : 0 ≤ Nc) (v : V) :
    Matrix.trace (M v * M v) ≤ c₀ ^ 2 * G ^ 4 * Nc := by
  have e : Matrix.trace (M v * M v) = ∑ i, ∑ j, M v i j * M v j i := by
    simp [Matrix.trace, Matrix.mul_apply]
  have ha : 0 ≤ c₀ * G ^ 2 := by positivity
  have term : ∀ i j, M v i j * M v j i ≤ c₀ * G ^ 2 * siteEntryBound g Y c₀ v i j := by
    intro i j
    have h1 : M v j i = M v i j := (entry_comm H v i j).symm
    rw [h1, ← sq, ← sq_abs]
    have h2 : |M v i j| ≤ siteEntryBound g Y c₀ v i j := H.entry_le v i j
    have h3 : siteEntryBound g Y c₀ v i j ≤ c₀ * G ^ 2 :=
      (Finset.single_le_sum (f := fun j => siteEntryBound g Y c₀ v i j) (fun j _ => siteEntryBound_nonneg H h0 v i j) (Finset.mem_univ j)).trans
        (sum_siteEntryBound_le H h0 hG v i)
    have h4 := abs_nonneg (M v i j)
    nlinarith
  rw [e]
  calc ∑ i, ∑ j, M v i j * M v j i ≤ ∑ i, ∑ j, c₀ * G ^ 2 * siteEntryBound g Y c₀ v i j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => term i j
    _ = c₀ * G ^ 2 * ∑ i, ∑ j, siteEntryBound g Y c₀ v i j := by simp only [Finset.mul_sum]
    _ ≤ c₀ * G ^ 2 * ∑ i, c₀ * G * siteMass g Y v i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => sum_siteEntryBound_le_mass H h0 hG v i) ha
    _ = c₀ * G ^ 2 * (c₀ * G * ∑ i, siteMass g Y v i) := by simp only [Finset.mul_sum]
    _ ≤ c₀ * G ^ 2 * (c₀ * G * (Nc * G)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_siteMass_le H hG v) (by positivity)) ha
    _ = c₀ ^ 2 * G ^ 4 * Nc := by ring
private lemma sum_siteMass_mul_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (hN : 0 ≤ Nc) (ht : 0 ≤ τ) {v w : V} (hn : ¬ Near v w) :
    ∑ i, siteMass g Y v i * siteMass g Y w i ≤ Nc ^ 2 * τ := by
  simp only [siteMass, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  calc ∑ y ∈ Y v, ∑ i, ∑ y' ∈ Y w, g i y * g i y' = ∑ y ∈ Y v, ∑ y' ∈ Y w, ∑ i, g i y * g i y' :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ ≤ ∑ y ∈ Y v, ∑ _y' ∈ Y w, τ := Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun y' hy' => H.overlap_le v w hn y hy y' hy'
    _ = (Y v).card * ((Y w).card * τ) := by simp
    _ ≤ Nc * (Nc * τ) := by
        have h1 := H.card_le v
        have h2 := H.card_le w
        exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 ht) (by positivity) hN
    _ = Nc ^ 2 * τ := by ring
private lemma sum_siteEntryBound_mul_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (ht : 0 ≤ τ) {v w : V} (hn : ¬ Near v w) (i k : ι) :
    ∑ j, siteEntryBound g Y c₀ v i j * siteEntryBound g Y c₀ w j k ≤ c₀ ^ 2 * τ * (siteMass g Y v i * siteMass g Y w k) := by
  have e : ∑ j, siteEntryBound g Y c₀ v i j * siteEntryBound g Y c₀ w j k =
      c₀ ^ 2 * ∑ y ∈ Y v, ∑ y' ∈ Y w, (g i y * g k y') * ∑ j, g j y * g j y' := by
    have s1 : ∀ j, siteEntryBound g Y c₀ v i j * siteEntryBound g Y c₀ w j k =
        c₀ ^ 2 * ∑ y ∈ Y v, ∑ y' ∈ Y w, (g i y * g j y) * (g j y' * g k y') := by
      intro j
      simp only [siteEntryBound]
      rw [mul_mul_mul_comm, Finset.sum_mul_sum, sq]
    simp_rw [s1]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  have : ∑ y ∈ Y v, ∑ y' ∈ Y w, (g i y * g k y') * ∑ j, g j y * g j y' ≤
      ∑ y ∈ Y v, ∑ y' ∈ Y w, (g i y * g k y') * τ :=
    Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun y' hy' =>
      mul_le_mul_of_nonneg_left (H.overlap_le v w hn y hy y' hy') (mul_nonneg (H.nonneg i y) (H.nonneg k y'))
  calc c₀ ^ 2 * ∑ y ∈ Y v, ∑ y' ∈ Y w, (g i y * g k y') * ∑ j, g j y * g j y'
      ≤ c₀ ^ 2 * ∑ y ∈ Y v, ∑ y' ∈ Y w, (g i y * g k y') * τ := mul_le_mul_of_nonneg_left this (by positivity)
    _ = c₀ ^ 2 * τ * (siteMass g Y v i * siteMass g Y w k) := by
        simp only [siteMass]
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y' _ => by ring
private lemma abs_trace_mul_le_of_not_near (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hN : 0 ≤ Nc) (ht : 0 ≤ τ)
    {v w : V} (hn : ¬ Near v w) : |Matrix.trace (M v * M w)| ≤ c₀ ^ 2 * Nc ^ 2 * τ ^ 2 := by
  have e : Matrix.trace (M v * M w) = ∑ i, ∑ j, M v i j * M w j i := by
    simp [Matrix.trace, Matrix.mul_apply]
  rw [e]
  have h1 : ∀ i j, |M v i j * M w j i| ≤ siteEntryBound g Y c₀ v i j * siteEntryBound g Y c₀ w j i := fun i j => by
    rw [abs_mul]
    exact mul_le_mul (H.entry_le v i j) (H.entry_le w j i) (abs_nonneg _) (siteEntryBound_nonneg H h0 v i j)
  have h2 : ∀ i, ∑ j, siteEntryBound g Y c₀ v i j * siteEntryBound g Y c₀ w j i ≤ c₀ ^ 2 * τ * (siteMass g Y v i * siteMass g Y w i) :=
    fun i => sum_siteEntryBound_mul_le H h0 ht hn i i
  have h3 : ∑ i, c₀ ^ 2 * τ * (siteMass g Y v i * siteMass g Y w i) ≤ c₀ ^ 2 * τ * (Nc ^ 2 * τ) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_siteMass_mul_le H hN ht hn) (by positivity)
  calc |∑ i, ∑ j, M v i j * M w j i| ≤ ∑ i, ∑ j, |M v i j * M w j i| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, siteEntryBound g Y c₀ v i j * siteEntryBound g Y c₀ w j i :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ ≤ ∑ i, c₀ ^ 2 * τ * (siteMass g Y v i * siteMass g Y w i) := Finset.sum_le_sum fun i _ => h2 i
    _ ≤ c₀ ^ 2 * τ * (Nc ^ 2 * τ) := h3
    _ = c₀ ^ 2 * Nc ^ 2 * τ ^ 2 := by ring
private lemma sum_siteMass_sq_le (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (hG : 0 ≤ G) (v : V) :
    ∑ i, siteMass g Y v i ^ 2 ≤ G * (Nc * G) := by
  calc ∑ i, siteMass g Y v i ^ 2 ≤ ∑ i, G * siteMass g Y v i := Finset.sum_le_sum fun i _ => by
        rw [sq]; exact mul_le_mul_of_nonneg_right (siteMass_le H v i) (siteMass_nonneg H v i)
    _ = G * ∑ i, siteMass g Y v i := by rw [Finset.mul_sum]
    _ ≤ G * (Nc * G) := mul_le_mul_of_nonneg_left (sum_siteMass_le H hG v) hG
private lemma trace_mul_transpose_le_of_not_near (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hG : 0 ≤ G) (hN : 0 ≤ Nc) (ht : 0 ≤ τ)
    {v w : V} (hn : ¬ Near v w) : Matrix.trace ((M v * M w) * (M v * M w)ᵀ) ≤ (c₀ ^ 2 * τ * Nc * G ^ 2) ^ 2 := by
  have e0 : ∀ A : Matrix ι ι ℝ, Matrix.trace (A * Aᵀ) = ∑ i, ∑ k, (A i k) ^ 2 := fun A => by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply, sq]
  have e := e0 (M v * M w)
  have e1 : ∀ i k, |(M v * M w) i k| ≤ c₀ ^ 2 * τ * (siteMass g Y v i * siteMass g Y w k) := fun i k => by
    rw [Matrix.mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_siteEntryBound_mul_le H h0 ht hn i k))
    rw [abs_mul]
    exact mul_le_mul (H.entry_le v i j) (H.entry_le w j k) (abs_nonneg _) (siteEntryBound_nonneg H h0 v i j)
  rw [e]
  calc ∑ i, ∑ k, ((M v * M w) i k) ^ 2 ≤ ∑ i, ∑ k, (c₀ ^ 2 * τ) ^ 2 * (siteMass g Y v i ^ 2 * siteMass g Y w k ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
          rw [← sq_abs, ← mul_pow, ← mul_pow]
          have := e1 i k
          refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
          simpa [mul_assoc] using this
    _ = (c₀ ^ 2 * τ) ^ 2 * ((∑ i, siteMass g Y v i ^ 2) * ∑ k, siteMass g Y w k ^ 2) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (c₀ ^ 2 * τ) ^ 2 * ((G * (Nc * G)) * (G * (Nc * G))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul (sum_siteMass_sq_le H hG v) (sum_siteMass_sq_le H hG w) (Finset.sum_nonneg fun k _ => by positivity) (by positivity)
    _ = (c₀ ^ 2 * τ * Nc * G ^ 2) ^ 2 := by ring
private lemma abs_mulVec_dotProduct_le_of_not_near (H : DominatedBySites g Y M Near In c₀ G Nc τ τ₂) (h0 : 0 ≤ c₀) (hG : 0 ≤ G) (hN : 0 ≤ Nc) (ht : 0 ≤ τ)
    {Fm : ℝ} (hFm : 0 ≤ Fm) {F : ι → ℝ} (hall : ∀ i, |F i| ≤ Fm) {v w : V} (hn : ¬ Near v w) :
    |(M v).mulVec F ⬝ᵥ (M w).mulVec F| ≤ Fm ^ 2 * c₀ ^ 2 * G ^ 2 * Nc ^ 2 * τ := by
  have row : ∀ (u : V) (i : ι), |(M u).mulVec F i| ≤ Fm * (c₀ * G * siteMass g Y u i) := by
    intro u i
    have e : (M u).mulVec F i = ∑ j, M u i j * F j := by simp [Matrix.mulVec, dotProduct]
    rw [e]
    calc |∑ j, M u i j * F j| ≤ ∑ j, siteEntryBound g Y c₀ u i j * Fm :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
            rw [abs_mul]
            exact mul_le_mul (H.entry_le u i j) (hall j) (abs_nonneg _) (siteEntryBound_nonneg H h0 u i j))
      _ = Fm * ∑ j, siteEntryBound g Y c₀ u i j := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ Fm * (c₀ * G * siteMass g Y u i) := mul_le_mul_of_nonneg_left (sum_siteEntryBound_le_mass H h0 hG u i) hFm
  simp only [dotProduct]
  calc |∑ i, (M v).mulVec F i * (M w).mulVec F i| ≤ ∑ i, (Fm * (c₀ * G * siteMass g Y v i)) * (Fm * (c₀ * G * siteMass g Y w i)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul (row v i) (row w i) (abs_nonneg _)
            (mul_nonneg hFm (mul_nonneg (by positivity) (siteMass_nonneg H v i))))
    _ = Fm ^ 2 * c₀ ^ 2 * G ^ 2 * ∑ i, siteMass g Y v i * siteMass g Y w i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ Fm ^ 2 * c₀ ^ 2 * G ^ 2 * (Nc ^ 2 * τ) := mul_le_mul_of_nonneg_left (sum_siteMass_mul_le H hN ht hn) (by positivity)
    _ = Fm ^ 2 * c₀ ^ 2 * G ^ 2 * Nc ^ 2 * τ := by ring
end SiteDomination
theorem sitesDominatedFormFamily_holds : sitesDominatedFormFamilyStatement := by
  intro ι V S _ _ _ g Y M Near In c₀ G Nc τ τ₂ φ₀ Fm A φ ε F h0 hG hN ht ht2 hφ hFm hε H hIn hall hA h1 h2 e1 e2 e3
  refine ⟨H.symm, fun v s t => dotProduct_mulVec_sq_le H h0 hG v s t, fun v => (trace_mul_self_le H h0 hG hN v).trans hA, fun v => ?_, fun v => ?_,
    fun v w hn => (abs_trace_mul_le_of_not_near H h0 hN ht hn).trans e1, fun v w hn => ?_,
    fun v w hn => (abs_mulVec_dotProduct_le_of_not_near H h0 hG hN ht hFm hall hn).trans e3⟩
  · have m := weighted_abs_sum_le_vectorMass H h0 hG hN ht2 hφ hFm hIn hall v
    exact (mulVec_dotProduct_self_le H h0 hG v F).trans ((mul_le_mul_of_nonneg_left m (by positivity)).trans h1)
  · exact (abs_dotProduct_mulVec_self_le H v F).trans ((weighted_abs_sum_le_vectorMass H h0 hG hN ht2 hφ hFm hIn hall v).trans h2)
  · refine (trace_mul_transpose_le_of_not_near H h0 hG hN ht hn).trans ?_
    exact pow_le_pow_left₀ (by positivity) e2 2
end YangMills.Construction.QuadraticConcentration
end
