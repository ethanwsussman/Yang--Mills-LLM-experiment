import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import YangMills.Construction.Lattice.PathRearrangement
import YangMills.Construction.Lattice.SpreadOfAContourFamily
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ContourSpread
open YangMills.Construction.Matrices
section Preliminaries
variable {E α : Type*} [SeminormedAddCommGroup E]
theorem norm_sub_le_of_le_of_le (a b c : E) {s t : ℝ} (h₁ : ‖a - b‖ ≤ s) (h₂ : ‖b - c‖ ≤ t) :
    ‖a - c‖ ≤ s + t := by
  have h : a - c = (a - b) + (b - c) := by abel
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)
def replicatedDirections (c : α → ℕ) (l : List α) : List α := l.flatMap fun μ => List.replicate (c μ) μ
def unorderedPairs (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) - 1) / 2
theorem unorderedPairs_succ (k : ℕ) : unorderedPairs (k + 1) = unorderedPairs k + k := by
  unfold unorderedPairs
  push_cast
  ring
theorem length_unitSteps_le (c : α → ℕ) (h : ℝ) (hc : ∀ μ, (c μ : ℝ) ≤ h) (l : List α) :
    ((replicatedDirections c l).length : ℝ) ≤ l.length * h := by
  induction l with
  | nil => simp [replicatedDirections]
  | cons μ l ih =>
    have : (replicatedDirections c (μ :: l)).length = c μ + (replicatedDirections c l).length := by
      simp [replicatedDirections]
    rw [this]
    push_cast [List.length_cons]
    linarith [hc μ]
variable (H : List α → E) (F : List α → Prop) (r : ℝ)
theorem norm_sub_moveLetter_le (hF : ∀ a b : List α, a.Perm b → F a → F b)
    (hx : ∀ (pre : List α) (μ ν : α) (post : List α), F (pre ++ μ :: ν :: post) →
      ‖H (pre ++ μ :: ν :: post) - H (pre ++ ν :: μ :: post)‖ ≤ r)
    (w pre : List α) (μ : α) (post : List α) (hf : F (pre ++ (w ++ μ :: post))) :
    ‖H (pre ++ (w ++ μ :: post)) - H (pre ++ (μ :: w ++ post))‖ ≤ w.length * r := by
  induction w generalizing pre with
  | nil => simp
  | cons v w ih =>
    have h₁ := ih (pre ++ [v]) (by simpa using hf)
    have hp : (pre ++ (v :: w ++ μ :: post)).Perm (pre ++ v :: μ :: (w ++ post)) :=
      List.Perm.append_left pre (List.Perm.cons v List.perm_middle)
    have h₂ := hx pre v μ (w ++ post) (hF _ _ hp hf)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h₁ h₂ ⊢
    have := norm_sub_le_of_le_of_le _ _ _ h₁ h₂
    simp only [List.length_cons]
    push_cast
    linarith
theorem norm_sub_moveFlow_le (hF : ∀ a b : List α, a.Perm b → F a → F b) (hr : 0 ≤ r)
    (hx : ∀ (pre : List α) (μ ν : α) (post : List α), F (pre ++ μ :: ν :: post) →
      ‖H (pre ++ μ :: ν :: post) - H (pre ++ ν :: μ :: post)‖ ≤ r)
    (k : ℕ) (w pre : List α) (μ : α) (post : List α)
    (hf : F (pre ++ (w ++ (List.replicate k μ ++ post)))) :
    ‖H (pre ++ (w ++ (List.replicate k μ ++ post))) -
        H (pre ++ (List.replicate k μ ++ (w ++ post)))‖ ≤ k * w.length * r := by
  induction k generalizing pre with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append] at hf ⊢
    have h₁ := norm_sub_moveLetter_le H F r hF hx w pre μ (List.replicate k μ ++ post) hf
    have hp : (pre ++ (w ++ μ :: (List.replicate k μ ++ post))).Perm
        ((pre ++ [μ]) ++ (w ++ (List.replicate k μ ++ post))) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact List.Perm.append_left pre List.perm_middle
    have h₂ := ih (pre ++ [μ]) (hF _ _ hp hf)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h₁ h₂ ⊢
    have := norm_sub_le_of_le_of_le _ _ _ h₁ h₂
    push_cast
    nlinarith
theorem norm_sub_elemFlows_perm_le (hF : ∀ a b : List α, a.Perm b → F a → F b) (hr : 0 ≤ r)
    (hx : ∀ (pre : List α) (μ ν : α) (post : List α), F (pre ++ μ :: ν :: post) →
      ‖H (pre ++ μ :: ν :: post) - H (pre ++ ν :: μ :: post)‖ ≤ r)
    (c : α → ℕ) (h : ℝ) (hc : ∀ μ, (c μ : ℝ) ≤ h) (l' l pre : List α) (hp : l.Perm l')
    (hf : F (pre ++ replicatedDirections c l)) :
    ‖H (pre ++ replicatedDirections c l) - H (pre ++ replicatedDirections c l')‖ ≤
      unorderedPairs l.length * h ^ 2 * r := by
  induction l' generalizing l pre with
  | nil =>
    obtain rfl := hp.eq_nil
    simp [unorderedPairs]
  | cons μ l' ih =>
    obtain ⟨a, b, rfl⟩ := List.append_of_mem (hp.mem_iff.2 List.mem_cons_self)
    have hp' : (a ++ b).Perm l' := (List.perm_middle.symm.trans hp).cons_inv
    have ea : replicatedDirections c (a ++ μ :: b) =
        replicatedDirections c a ++ (List.replicate (c μ) μ ++ replicatedDirections c b) := by
      simp [replicatedDirections, List.flatMap_append, List.flatMap_cons]
    have eb : replicatedDirections c (μ :: l') = List.replicate (c μ) μ ++ replicatedDirections c l' := by
      simp [replicatedDirections, List.flatMap_cons]
    have ec : replicatedDirections c (a ++ b) = replicatedDirections c a ++ replicatedDirections c b := by
      simp [replicatedDirections, List.flatMap_append]
    rw [ea] at hf ⊢
    rw [eb]
    have h₁ := norm_sub_moveFlow_le H F r hF hr hx (c μ) (replicatedDirections c a) pre μ
      (replicatedDirections c b) hf
    have hq : (pre ++ (replicatedDirections c a ++ (List.replicate (c μ) μ ++ replicatedDirections c b))).Perm
        ((pre ++ List.replicate (c μ) μ) ++ replicatedDirections c (a ++ b)) := by
      rw [ec]
      simp only [List.append_assoc]
      exact List.Perm.append_left pre (List.perm_append_comm_assoc _ _ _)
    have h₂ := ih (a ++ b) (pre ++ List.replicate (c μ) μ) hp' (hF _ _ hq hf)
    rw [ec] at h₂
    simp only [List.append_assoc] at h₂
    have h₃ := norm_sub_le_of_le_of_le _ _ _ h₁ h₂
    refine h₃.trans ?_
    have hh : 0 ≤ h := le_trans (Nat.cast_nonneg _) (hc μ)
    have hlen : ((replicatedDirections c a).length : ℝ) ≤ a.length * h := length_unitSteps_le c h hc a
    have hA : (c μ : ℝ) * (replicatedDirections c a).length ≤ ((a ++ b).length : ℝ) * h ^ 2 := by
      have h₄ : (c μ : ℝ) * (replicatedDirections c a).length ≤ h * (a.length * h) :=
        mul_le_mul (hc μ) hlen (Nat.cast_nonneg _) hh
      have h₅ : (a.length : ℝ) ≤ (a ++ b).length := by
        simp
      nlinarith [mul_nonneg hh hh]
    have hlen' : (a ++ μ :: b).length = (a ++ b).length + 1 := by simp; omega
    rw [hlen', unorderedPairs_succ]
    have := mul_le_mul_of_nonneg_right hA hr
    nlinarith
end Preliminaries
section Paths
variable {L m : ℕ} {j : ℤ}
def axisSign (n : Fin 4 → ℤ) (μ : Fin 4) : ℤ := if 0 ≤ n μ then 1 else -1
def signedUnitStep (n : Fin 4 → ℤ) (μ : Fin 4) : UnitStepVec L m j :=
  ⟨axisSign n μ • unitStep L m j μ, ⟨μ, by unfold axisSign; split_ifs <;> simp⟩⟩
def wordSteps (n : Fin 4 → ℤ) (w : List (Fin 4)) : StepWord L m j := w.map (signedUnitStep n)
def stepTotal (s : StepWord L m j) : Site L m j :=
  (s.map fun u : UnitStepVec L m j => (u : Site L m j)).sum
theorem pathOfWord_append (z : Site L m j) (s t : StepWord L m j) :
    pathOfWord z (s ++ t) = pathOfWord z s ++ pathOfWord (z + stepTotal s) t := by
  induction s generalizing z with
  | nil => simp [pathOfWord, stepTotal]
  | cons a s ih => simp [pathOfWord, ih, stepTotal, add_assoc]
theorem stepTotal_wordSteps (n : Fin 4 → ℤ) (w : List (Fin 4)) :
    stepTotal (wordSteps n w : StepWord L m j) =
      ∑ μ, ((w.count μ : ℤ) * axisSign n μ) • unitStep L m j μ := by
  induction w with
  | nil => simp [stepTotal, wordSteps]
  | cons ν w ih =>
    have h : stepTotal (wordSteps n (ν :: w) : StepWord L m j) =
        axisSign n ν • unitStep L m j ν + stepTotal (wordSteps n w : StepWord L m j) := by
      simp [stepTotal, wordSteps, signedUnitStep]
    rw [h, ih]
    have h₂ : ∀ μ, (((ν :: w).count μ : ℤ) * axisSign n μ) • unitStep L m j μ =
        ((w.count μ : ℤ) * axisSign n μ) • unitStep L m j μ +
          if ν = μ then axisSign n ν • unitStep L m j ν else 0 := by
      intro μ
      by_cases hν : ν = μ
      · subst hν
        simp [add_mul, add_smul]
      · simp [hν]
    simp only [h₂, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    abel
theorem natAbs_mul_axisSign (n : Fin 4 → ℤ) (μ : Fin 4) :
    ((n μ).natAbs : ℤ) * axisSign n μ = n μ := by
  unfold axisSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (not_le.mp h)]
theorem forwardFlow_eq_pathOfWord (n : Fin 4 → ℤ) (μ : Fin 4) (hs : 0 ≤ n μ) (k : ℕ)
    (z : Site L m j) :
    forwardAxisPath z μ k = pathOfWord z (wordSteps n (List.replicate k μ)) := by
  have hv : ((signedUnitStep n μ : UnitStepVec L m j) : Site L m j) = unitStep L m j μ := by
    simp [signedUnitStep, axisSign, hs]
  induction k generalizing z with
  | zero => simp [forwardAxisPath, wordSteps, pathOfWord]
  | succ k ih =>
    simp only [forwardAxisPath, List.replicate_succ, wordSteps, List.map_cons, pathOfWord]
    rw [hv, ih]
    refine congrArg₂ _ (Bond.ext rfl ?_) rfl
    simp [Bond.forwardFrom, bondOfStep, hv]
theorem backwardFlow_eq_pathOfWord (n : Fin 4 → ℤ) (μ : Fin 4) (hs : ¬ 0 ≤ n μ) (k : ℕ)
    (z : Site L m j) :
    backwardAxisPath z μ k = pathOfWord z (wordSteps n (List.replicate k μ)) := by
  have hv : ((signedUnitStep n μ : UnitStepVec L m j) : Site L m j) = -unitStep L m j μ := by
    simp [signedUnitStep, axisSign, hs]
  induction k generalizing z with
  | zero => simp [backwardAxisPath, wordSteps, pathOfWord]
  | succ k ih =>
    simp only [backwardAxisPath, List.replicate_succ, wordSteps, List.map_cons, pathOfWord]
    rw [hv, ← sub_eq_add_neg, ih]
    refine congrArg₂ _ (Bond.ext rfl ?_) rfl
    simp [Bond.backwardFrom, bondOfStep, hv, sub_eq_add_neg]
theorem flowAlong_eq_pathOfWord (n : Fin 4 → ℤ) (μ : Fin 4) (z : Site L m j) :
    flowAlong z μ (n μ) = pathOfWord z (wordSteps n (List.replicate (n μ).natAbs μ)) := by
  unfold flowAlong
  split_ifs with h
  · rw [forwardFlow_eq_pathOfWord n μ h]
    congr 3
    omega
  · rw [backwardFlow_eq_pathOfWord n μ h]
    congr 3
    omega
theorem stepTotal_replicate (n : Fin 4 → ℤ) (μ : Fin 4) :
    stepTotal (wordSteps n (List.replicate (n μ).natAbs μ) : StepWord L m j) =
      n μ • unitStep L m j μ := by
  simp only [stepTotal, wordSteps, List.map_replicate, List.sum_replicate, signedUnitStep]
  rw [← natCast_zsmul, smul_smul, natAbs_mul_axisSign]
theorem stepsThroughAxes_eq_pathOfWord (n : Fin 4 → ℤ) (l : List (Fin 4)) (z : Site L m j) :
    stepsThroughAxes n z l = pathOfWord z (wordSteps n (replicatedDirections (fun μ => (n μ).natAbs) l)) := by
  induction l generalizing z with
  | nil => simp [stepsThroughAxes, replicatedDirections, wordSteps, pathOfWord]
  | cons μ l ih =>
    have e : (wordSteps n (replicatedDirections (fun μ => (n μ).natAbs) (μ :: l)) : StepWord L m j) =
        wordSteps n (List.replicate (n μ).natAbs μ) ++
          wordSteps n (replicatedDirections (fun μ => (n μ).natAbs) l) := by
      simp [wordSteps, replicatedDirections, List.flatMap_cons]
    rw [e, pathOfWord_append, stepTotal_replicate, ← flowAlong_eq_pathOfWord]
    simp only [stepsThroughAxes, ih]
def CountsWithin (n : Fin 4 → ℤ) (w : List (Fin 4)) : Prop := ∀ μ, w.count μ ≤ (n μ).natAbs
theorem CountsWithin.of_perm {n : Fin 4 → ℤ} {a b : List (Fin 4)} (hp : a.Perm b)
    (h : CountsWithin n a) : CountsWithin n b := fun μ => (hp.count_eq μ) ▸ h μ
theorem CountsWithin.of_append_left {n : Fin 4 → ℤ} {a b : List (Fin 4)}
    (h : CountsWithin n (a ++ b)) : CountsWithin n a :=
  fun μ => le_trans (by simp [List.count_append]) (h μ)
theorem count_repeatedSteps (c : Fin 4 → ℕ) (l : List (Fin 4)) (hl : l.Nodup) (μ : Fin 4) :
    (replicatedDirections c l).count μ = if μ ∈ l then c μ else 0 := by
  induction l with
  | nil => simp [replicatedDirections]
  | cons ν l ih =>
    obtain ⟨hν, hl'⟩ := List.nodup_cons.mp hl
    have e : replicatedDirections c (ν :: l) = List.replicate (c ν) ν ++ replicatedDirections c l := by
      simp [replicatedDirections, List.flatMap_cons]
    rw [e, List.count_append, ih hl', List.count_replicate]
    by_cases h : ν = μ
    · subst h
      simp [hν]
    · by_cases h' : μ ∈ l
      · simp [h, h', Ne.symm h]
      · simp [h, h', Ne.symm h]
theorem countsWithin_repeatedSteps (n : Fin 4 → ℤ) (l : List (Fin 4)) (hl : l.Nodup) :
    CountsWithin n (replicatedDirections (fun μ => (n μ).natAbs) l) := by
  intro μ
  rw [count_repeatedSteps _ l hl]
  split_ifs <;> simp
end Paths
theorem inv_mem_compactGaugeGroup {W : ComplexMatrix2} (hW : W ∈ compactGaugeGroup) :
    W⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem ne_neg_one_of_operatorNorm_sub_one_lt {X : ComplexMatrix2}
    (hX : ComplexMatrix2.operatorNorm (X - 1) < 1) : X ≠ -1 := by
  rintro rfl
  have e : (-1 - 1 : ComplexMatrix2) = (-2 : ℂ) • (1 : ComplexMatrix2) := by
    rw [neg_smul, two_smul]
    abel
  have h : ComplexMatrix2.operatorNorm (-1 - 1 : ComplexMatrix2) = 2 := by
    rw [e, ComplexMatrix2.operatorNorm, norm_smul, CStarRing.norm_one]
    simp
  linarith
theorem rotationAngle_le_of_isLogMean {ι : Type*} [Fintype ι]
    (hnorm : ComplexMatrix2.OperatorNormUnderConjugation)
    (ha : ComplexMatrix2.SpecialUnitaryAngleBounds) (F : ι → ComplexMatrix2)
    (hF : ∀ i, F i ∈ compactGaugeGroup) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ i i', ComplexMatrix2.operatorNorm (F i - F i') ≤ B) (W : ComplexMatrix2)
    (hW : ComplexMatrix2.IsLogMean compactGaugeGroup F W) (i : ι) :
    ComplexMatrix2.operatorNorm (F i * W⁻¹ - 1) ≤ ComplexMatrix2.rotationAngle (F i * W⁻¹) ∧
      ComplexMatrix2.rotationAngle (F i * W⁻¹) ≤ 2 * Real.pi / (3 * Real.sqrt 3) * B := by
  obtain ⟨-, h2, -, h4, -, -, -, h8, h9, -⟩ := ha
  obtain ⟨hn1, -⟩ := hnorm
  obtain ⟨hWG, hlt, hsum⟩ := hW
  have hWinv : W⁻¹ ∈ compactGaugeGroup := inv_mem_compactGaugeGroup hWG
  have hWi : ∀ i, F i * W⁻¹ ∈ ComplexMatrix2.specialUnitary :=
    fun i => Submonoid.mul_mem _ (hF i) hWinv
  have hdom : ∀ i, F i * W⁻¹ ∈ ComplexMatrix2.unitaryLogDomain :=
    fun i => ⟨hWi i, ne_neg_one_of_operatorNorm_sub_one_lt (hlt i)⟩
  have hlow : ∀ i, ComplexMatrix2.operatorNorm (F i * W⁻¹ - 1) ≤
      ComplexMatrix2.rotationAngle (F i * W⁻¹) :=
    fun i => (h2 _ (hWi i)).2.2.2.2.2
  have hsmall : ∀ i, ComplexMatrix2.rotationAngle (F i * W⁻¹) < Real.pi / 3 :=
    fun i => ((h4 _ (hdom i)).2.1).1 (hlt i)
  have hzero : ∑ i, ComplexMatrix2.unitaryLieLog (F i * W⁻¹) = 0 := by
    have e : ∀ i, ComplexMatrix2.logSeries (F i * W⁻¹) =
        Complex.I • ComplexMatrix2.unitaryLieLog (F i * W⁻¹) :=
      fun i => ((h4 _ (hdom i)).2.2 (hsmall i)).symm
    simp only [e] at hsum
    rw [← Finset.smul_sum] at hsum
    exact (smul_eq_zero.mp hsum).resolve_left Complex.I_ne_zero
  refine ⟨hlow i, ?_⟩
  have hc : 0 ≤ 2 * Real.pi / (3 * Real.sqrt 3) := by positivity
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => ComplexMatrix2.rotationAngle (F i * W⁻¹)) ⟨i, Finset.mem_univ i⟩
  have hM : 0 ≤ ComplexMatrix2.rotationAngle (F i₀ * W⁻¹) := (norm_nonneg _).trans (hlow i₀)
  rcases hM.eq_or_lt with hM0 | hMpos
  · have := hmax i (Finset.mem_univ i)
    rw [← hM0] at this
    exact this.trans (mul_nonneg hc hB)
  set M := ComplexMatrix2.rotationAngle (F i₀ * W⁻¹) with hMdef
  have hsin := h9 M hMpos (hsmall i₀)
  have hMpi : M < Real.pi := (hsmall i₀).trans (by linarith [Real.pi_pos])
  have hdiff : ∀ i', ComplexMatrix2.operatorNorm (ComplexMatrix2.unitaryLieLog (F i * W⁻¹) -
      ComplexMatrix2.unitaryLieLog (F i' * W⁻¹)) ≤ 2 * Real.pi / (3 * Real.sqrt 3) * B := by
    intro i'
    have h₁ := (h8 M hMpos hMpi).2 _ (hWi i) _ (hWi i') (hmax i (Finset.mem_univ i))
      (hmax i' (Finset.mem_univ i'))
    have h₂ : ComplexMatrix2.operatorNorm (F i * W⁻¹ - F i' * W⁻¹) =
        ComplexMatrix2.operatorNorm (F i - F i') := by
      have := hn1 (F i - F i') 1 W⁻¹ (Submonoid.one_mem _)
        (Matrix.specialUnitaryGroup_le_unitaryGroup hWinv)
      rw [one_mul] at this
      rw [← sub_mul, this]
    rw [h₂] at h₁
    exact h₁.trans (mul_le_mul hsin.le (hd i i') (norm_nonneg _) hc)
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    have : Nonempty ι := ⟨i⟩
    exact_mod_cast Fintype.card_pos
  have hsmul : ((Fintype.card ι : ℂ)) • ComplexMatrix2.unitaryLieLog (F i * W⁻¹) =
      ∑ i', (ComplexMatrix2.unitaryLieLog (F i * W⁻¹) -
        ComplexMatrix2.unitaryLieLog (F i' * W⁻¹)) := by
    rw [Finset.sum_sub_distrib, hzero, sub_zero, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  have hnorm' : (Fintype.card ι : ℝ) *
      ComplexMatrix2.operatorNorm (ComplexMatrix2.unitaryLieLog (F i * W⁻¹)) ≤
      (Fintype.card ι : ℝ) * (2 * Real.pi / (3 * Real.sqrt 3) * B) := by
    have e : ComplexMatrix2.operatorNorm
        (((Fintype.card ι : ℂ)) • ComplexMatrix2.unitaryLieLog (F i * W⁻¹)) =
        (Fintype.card ι : ℝ) *
          ComplexMatrix2.operatorNorm (ComplexMatrix2.unitaryLieLog (F i * W⁻¹)) := by
      rw [ComplexMatrix2.operatorNorm, norm_smul, Complex.norm_natCast]
    rw [← e, hsmul]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ fun i' _ => hdiff i').trans ?_
    simp [Finset.card_univ]
  rw [← (h4 _ (hdom i)).1]
  exact le_of_mul_le_mul_left hnorm' hcard
section Block
variable {L m : ℕ} {j : ℤ}
theorem coe_toSublattice (y : Site L m j) {j' : ℤ} (h : (y : FourTorus L m) ∈ sublattice L m j') :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : Site L m j' => (x : FourTorus L m) = y) ⟨⟨y, h⟩, rfl⟩
theorem coe_sum_zsmul_unitStep (p : Fin 4 → ℤ) :
    ((∑ μ, p μ • unitStep L m j μ : Site L m j) : FourTorus L m) =
      ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L j) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coe_sum_zsmul_unitStep <;> assumption
theorem mem_unitBlock_of_countsWithin (y : Site L m j)
    (hB : RefinedBlockEqOffsetImage L m j 1 y) (n : Fin 4 → ℤ)
    (hn : ∀ μ, 2 * |n μ| ≤ (L : ℤ) - 1) {w : List (Fin 4)} (hw : CountsWithin n w) :
    ((y.toSublattice (j + (1 : ℕ)) +
        stepTotal (wordSteps n w : StepWord L m (j + (1 : ℕ))) :
      Site L m (j + (1 : ℕ))) : FourTorus L m) ∈ unitBlock y := by
  show _ ∈ refinedBlock 1 y
  rw [hB.1]
  refine ⟨fun μ => (w.count μ : ℤ) * axisSign n μ, ?_, ?_⟩
  · intro μ
    have hs : |axisSign n μ| = 1 := by
      unfold axisSign
      split_ifs <;> simp
    have h₁ : (w.count μ : ℤ) ≤ |n μ| := by
      have := hw μ
      rw [Int.abs_eq_natAbs]
      exact_mod_cast this
    have h₂ := hn μ
    simp only [abs_mul, hs, mul_one, Nat.abs_cast, pow_one]
    linarith
  · simp only [refinedOffsetSite, offsetSite]
    rw [stepTotal_wordSteps]
theorem stepTotal_wordSteps_concat (n : Fin 4 → ℤ) (z : Site L m j) (a : List (Fin 4))
    (μ : Fin 4) :
    z + stepTotal (wordSteps n a : StepWord L m j) + (signedUnitStep n μ : UnitStepVec L m j) =
      z + stepTotal (wordSteps n (a ++ [μ]) : StepWord L m j) := by
  simp [stepTotal, wordSteps, add_assoc]
theorem mem_bondsInside_of_prefix (y : Site L m j) (hB : RefinedBlockEqOffsetImage L m j 1 y)
    (n : Fin 4 → ℤ) (hn : ∀ μ, 2 * |n μ| ≤ (L : ℤ) - 1) (pre w : List (Fin 4))
    (hf : CountsWithin n (pre ++ w)) :
    ∀ b ∈ pathOfWord (y.toSublattice (j + (1 : ℕ)) +
        stepTotal (wordSteps n pre : StepWord L m (j + (1 : ℕ))))
        (wordSteps n w : StepWord L m (j + (1 : ℕ))),
      b ∈ (bondsInside (unitBlock y) : Set (Bond L m (j + (1 : ℕ)))) := by
  induction w generalizing pre with
  | nil => simp [wordSteps, pathOfWord]
  | cons μ w ih =>
    intro b hb
    have hf' : CountsWithin n ((pre ++ [μ]) ++ w) := by simpa using hf
    have e : (wordSteps n (μ :: w) : StepWord L m (j + (1 : ℕ))) =
        signedUnitStep n μ :: wordSteps n w := rfl
    rw [e, pathOfWord, stepTotal_wordSteps_concat, List.mem_cons] at hb
    rcases hb with rfl | hb
    · refine ⟨mem_unitBlock_of_countsWithin y hB n hn
        (CountsWithin.of_append_left (b := μ :: w) hf), ?_⟩
      show ((_ + _ : Site L m (j + (1 : ℕ))) : FourTorus L m) ∈ _
      rw [stepTotal_wordSteps_concat]
      exact mem_unitBlock_of_countsWithin y hB n hn (CountsWithin.of_append_left hf')
    · exact ih (pre ++ [μ]) hf' b hb
theorem mem_bondsInside_pathOfWord (y : Site L m j) (hB : RefinedBlockEqOffsetImage L m j 1 y)
    (n : Fin 4 → ℤ) (hn : ∀ μ, 2 * |n μ| ≤ (L : ℤ) - 1) (w : List (Fin 4))
    (hf : CountsWithin n w) :
    ∀ b ∈ pathOfWord (y.toSublattice (j + (1 : ℕ))) (wordSteps n w : StepWord L m (j + (1 : ℕ))),
      b ∈ (bondsInside (unitBlock y) : Set (Bond L m (j + (1 : ℕ)))) := by
  have h := mem_bondsInside_of_prefix y hB n hn [] w (by simpa using hf)
  have e : y.toSublattice (j + (1 : ℕ)) +
      stepTotal (wordSteps n [] : StepWord L m (j + (1 : ℕ))) = y.toSublattice (j + (1 : ℕ)) := by
    simp [stepTotal, wordSteps]
  rwa [e] at h
theorem boundaryBonds_mem_bondsInside {j' : ℤ} (X : Set (FourTorus L m)) (p : Plaquette L m j')
    (hp : ∀ c ∈ p.vertices, (c : FourTorus L m) ∈ X) :
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInside X : Set (Bond L m j')) := by
  have c₁ := hp p.origin (by simp [Plaquette.vertices])
  have c₂ := hp (p.origin + unitStep L m j' p.firstAxis) (by simp [Plaquette.vertices])
  have c₃ := hp (p.origin + unitStep L m j' p.firstAxis + unitStep L m j' p.secondAxis)
    (by simp [Plaquette.vertices])
  have c₄ := hp (p.origin + unitStep L m j' p.secondAxis) (by simp [Plaquette.vertices])
  intro b hb
  simp only [Plaquette.boundaryBonds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨c₁, c₂⟩
  · exact ⟨c₂, c₃⟩
  · refine ⟨?_, c₄⟩
    show ((p.origin + unitStep L m j' p.secondAxis + unitStep L m j' p.firstAxis :
      Site L m j') : FourTorus L m) ∈ X
    rw [add_right_comm]
    exact c₃
  · exact ⟨c₄, c₁⟩
theorem pathHolonomy_mem_specialUnitary {j' : ℤ} {ℬ : Set (Bond L m j')}
    {V : Bond L m j' → ComplexMatrix2} (hV : IsGaugeField compactGaugeGroup ℬ V)
    (Γ : List (Bond L m j')) (h : ∀ b ∈ Γ, b ∈ ℬ) :
    pathHolonomy V Γ ∈ ComplexMatrix2.specialUnitary := by
  refine Submonoid.list_prod_mem _ ?_
  intro W hW
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hW
  exact hV.1 b (h b hb)
theorem blockPlaquetteDefect_nonneg {j' : ℤ} (y : Site L m j) (V : Bond L m j' → ComplexMatrix2) :
    0 ≤ blockPlaquetteDefect y V :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem operatorNorm_plaquetteHolonomy_sub_one_le {j' : ℤ}
    (ha : ComplexMatrix2.SpecialUnitaryAngleBounds) (y : Site L m j)
    (V : Bond L m j' → ComplexMatrix2)
    (hV : IsGaugeField compactGaugeGroup (bondsInside (unitBlock y) : Set (Bond L m j')) V)
    (p : Plaquette L m j') (hp : ∀ c ∈ p.vertices, (c : FourTorus L m) ∈ unitBlock y) :
    ComplexMatrix2.operatorNorm (plaquetteHolonomy V p - 1) ≤ blockPlaquetteDefect y V := by
  obtain ⟨-, h2, -⟩ := ha
  have hbdd : BddAbove (Set.range fun q : (plaquettesInside (unitBlock y) :
      Set (Plaquette L m j')) => ComplexMatrix2.operatorNorm (plaquetteHolonomy V q - 1)) := by
    refine ⟨2, ?_⟩
    rintro _ ⟨q, rfl⟩
    have hW : plaquetteHolonomy V q ∈ ComplexMatrix2.specialUnitary :=
      pathHolonomy_mem_specialUnitary hV _ (boundaryBonds_mem_bondsInside _ _ q.2)
    show ComplexMatrix2.operatorNorm (plaquetteHolonomy V q - 1) ≤ 2
    rw [(h2 _ hW).1]
    linarith [Real.sin_le_one (ComplexMatrix2.rotationAngle (plaquetteHolonomy V q) / 2)]
  exact le_ciSup hbdd (⟨p, hp⟩ : (plaquettesInside (unitBlock y) : Set (Plaquette L m j')))
theorem sum_coe_eq_stepTotal {j' : ℤ} (s : StepWord L m j') :
    (s.map fun u => (u : Site L m j')).sum = stepTotal s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp [stepTotal] at ih ⊢
    simpa using ih
theorem norm_wordHolonomy_swap_le (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hj : -(m : ℤ) ≤ j) (hr : PathRearrangementBound)
    (ha : ComplexMatrix2.SpecialUnitaryAngleBounds) (y : Site L m j)
    (hB : RefinedBlockEqOffsetImage L m j 1 y) (n : Fin 4 → ℤ)
    (hn : ∀ μ, 2 * |n μ| ≤ (L : ℤ) - 1) (V : Bond L m (j + (1 : ℕ)) → ComplexMatrix2)
    (hV : IsGaugeField compactGaugeGroup
      (bondsInside (unitBlock y) : Set (Bond L m (j + (1 : ℕ)))) V)
    (pre : List (Fin 4)) (μ ν : Fin 4) (post : List (Fin 4))
    (hf : CountsWithin n (pre ++ μ :: ν :: post)) :
    ‖wordHolonomy V (y.toSublattice (j + (1 : ℕ))) (wordSteps n (pre ++ μ :: ν :: post)) -
      wordHolonomy V (y.toSublattice (j + (1 : ℕ))) (wordSteps n (pre ++ ν :: μ :: post))‖ ≤
      blockPlaquetteDefect y V := by
  have hf' : CountsWithin n (pre ++ ν :: μ :: post) :=
    hf.of_perm ((List.Perm.swap ν μ post).append_left pre)
  let e : AdjacentSwap L m (j + (1 : ℕ)) :=
    ⟨wordSteps n pre, signedUnitStep n μ, signedUnitStep n ν, wordSteps n post⟩
  have hs : e.original = wordSteps n (pre ++ μ :: ν :: post) := by
    simp [AdjacentSwap.original, e, wordSteps]
  have ht : e.swapped = wordSteps n (pre ++ ν :: μ :: post) := by
    simp [AdjacentSwap.swapped, e, wordSteps]
  have hclosed : IsReversalClosed
      (bondsInside (unitBlock y) : Set (Bond L m (j + (1 : ℕ)))) := fun b hb => ⟨hb.2, hb.1⟩
  obtain ⟨hi, hii⟩ := hr L m hL.1 hL.2 hm (j + (1 : ℕ)) (by push_cast; omega) _ V hclosed hV
    (y.toSublattice (j + (1 : ℕ)))
  have hbs : ∀ b ∈ pathOfWord (y.toSublattice (j + (1 : ℕ))) e.original,
      b ∈ (bondsInside (unitBlock y) : Set (Bond L m (j + (1 : ℕ)))) := by
    rw [hs]
    exact mem_bondsInside_pathOfWord y hB n hn _ hf
  have hbt : ∀ b ∈ pathOfWord (y.toSublattice (j + (1 : ℕ))) e.swapped,
      b ∈ (bondsInside (unitBlock y) : Set (Bond L m (j + (1 : ℕ)))) := by
    rw [ht]
    exact mem_bondsInside_pathOfWord y hB n hn _ hf'
  obtain ⟨hpar, hnon⟩ := hi e hbs hbt
  rw [← hs, ← ht]
  by_cases hp : e.IsCollinear
  · rw [hpar hp, sub_self, norm_zero]
    exact blockPlaquetteDefect_nonneg y V
  · obtain ⟨⟨p, hpl⟩, -⟩ := hnon hp
    have hstart : e.cornerSite (y.toSublattice (j + (1 : ℕ))) = y.toSublattice (j + (1 : ℕ)) +
        stepTotal (wordSteps n pre : StepWord L m (j + (1 : ℕ))) :=
      congrArg (y.toSublattice (j + (1 : ℕ)) + ·) (sum_coe_eq_stepTotal _)
    have h₀ : CountsWithin n pre := CountsWithin.of_append_left (b := μ :: ν :: post) hf
    have h₁ : CountsWithin n (pre ++ [μ]) :=
      CountsWithin.of_append_left (b := ν :: post) (by simpa using hf)
    have h₂ : CountsWithin n (pre ++ [ν]) :=
      CountsWithin.of_append_left (b := μ :: post) (by simpa using hf')
    have h₃ : CountsWithin n (pre ++ [μ] ++ [ν]) :=
      CountsWithin.of_append_left (b := post) (by simpa using hf)
    have hc : ∀ c ∈ p.vertices, (c : FourTorus L m) ∈ unitBlock y := by
      rw [hpl]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro c (rfl | rfl | rfl | rfl)
      · rw [hstart]
        exact mem_unitBlock_of_countsWithin y hB n hn h₀
      · rw [hstart]
        show ((_ + ((signedUnitStep n μ : UnitStepVec L m (j + (1 : ℕ))) :
          Site L m (j + (1 : ℕ))) : Site L m (j + (1 : ℕ))) : FourTorus L m) ∈ _
        rw [stepTotal_wordSteps_concat]
        exact mem_unitBlock_of_countsWithin y hB n hn h₁
      · rw [hstart]
        show ((_ + ((signedUnitStep n ν : UnitStepVec L m (j + (1 : ℕ))) :
          Site L m (j + (1 : ℕ))) : Site L m (j + (1 : ℕ))) : FourTorus L m) ∈ _
        rw [stepTotal_wordSteps_concat]
        exact mem_unitBlock_of_countsWithin y hB n hn h₂
      · rw [hstart]
        show ((_ + ((signedUnitStep n μ : UnitStepVec L m (j + (1 : ℕ))) :
          Site L m (j + (1 : ℕ))) +
          ((signedUnitStep n ν : UnitStepVec L m (j + (1 : ℕ))) : Site L m (j + (1 : ℕ))) :
          Site L m (j + (1 : ℕ))) : FourTorus L m) ∈ _
        rw [stepTotal_wordSteps_concat, stepTotal_wordSteps_concat]
        exact mem_unitBlock_of_countsWithin y hB n hn h₃
    have hb := boundaryBonds_mem_bondsInside _ p hc
    have hchain := (hii 1 ![e.original, e.swapped] (fun _ => e) (fun _ => p)
      (fun l => by
        obtain rfl : l = 0 := Subsingleton.elim _ _
        simp)
      (fun l b hb' => by
        fin_cases l
        · exact hbs b hb'
        · exact hbt b hb')
      (fun _ _ => ⟨hpl, hb⟩)).2
    have hle := operatorNorm_plaquetteHolonomy_sub_one_le ha y V hV p hc
    simp only [Finset.sum_filter, Fin.sum_univ_one] at hchain
    rw [if_pos hp] at hchain
    exact (by simpa using hchain : _ ≤ _).trans hle
end Block
section Main
variable {L m : ℕ}
theorem contourFamilySpread_at {j j' : ℤ} (hjj : j' = j + (1 : ℕ))
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) ≤ j)
    (hb : BlockPartition.Properties) (hnorm : ComplexMatrix2.OperatorNormUnderConjugation)
    (hr : PathRearrangementBound) (ha : ComplexMatrix2.SpecialUnitaryAngleBounds)
    (y : Site L m j) (V : Bond L m j' → ComplexMatrix2)
    (hV : IsGaugeField compactGaugeGroup (bondsInside (unitBlock y) : Set (Bond L m j')) V)
    (x : Site L m j') (hx : (x : FourTorus L m) ∈ unitBlock y) :
    (∀ Γ ∈ contourSet y x, ∀ Γ' ∈ contourSet y x,
      ComplexMatrix2.operatorNorm (pathHolonomy V Γ - pathHolonomy V Γ') ≤
        contourSwapConstant L * blockPlaquetteDefect y V) ∧
    ComplexMatrix2.familyDiameter (contourHolonomies V y x) ≤
      contourSwapConstant L * blockPlaquetteDefect y V ∧
    (HasContourMean V y x →
      ComplexMatrix2.IsLogMean compactGaugeGroup (contourHolonomies V y x)
        (meanContourHolonomy V y x) ∧
      ∀ Γ ∈ contourSet y x,
        ComplexMatrix2.operatorNorm (pathHolonomy V Γ * (meanContourHolonomy V y x)⁻¹ - 1) ≤
          ComplexMatrix2.rotationAngle (pathHolonomy V Γ * (meanContourHolonomy V y x)⁻¹) ∧
        ComplexMatrix2.rotationAngle (pathHolonomy V Γ * (meanContourHolonomy V y x)⁻¹) ≤
          2 * Real.pi / (3 * Real.sqrt 3) * contourSwapConstant L *
            blockPlaquetteDefect y V ∧
        2 * Real.pi / (3 * Real.sqrt 3) * contourSwapConstant L * blockPlaquetteDefect y V =
          Real.pi / Real.sqrt 3 * ((L : ℝ) - 1) ^ 2 * blockPlaquetteDefect y V) := by
  subst hjj
  obtain ⟨hP₁, hP₂, -⟩ := hb L m hL hm j 1 0 hj
  have hB := hP₁ y
  have hy : (y : FourTorus L m) ∈ sublattice L m (j + (1 : ℕ)) := hP₂.2.1 y.2
  have hex : ∃ n, IsBlockOffset y x n := by
    have hx' : (x : FourTorus L m) ∈ refinedBlock 1 y := hx
    rw [hB.1] at hx'
    obtain ⟨p, hp, hpx⟩ := hx'
    refine ⟨p, ?_, fun μ => by simpa using hp μ⟩
    rw [← hpx]
    simp only [refinedOffsetSite, offsetSite, AddSubgroup.coe_add]
    rw [coe_toSublattice y hy, add_sub_cancel_left, coe_sum_zsmul_unitStep]
  have hspec : IsBlockOffset y x (blockOffset y x) := Classical.epsilon_spec hex
  obtain ⟨-, hn⟩ := hspec
  generalize hndef : blockOffset y x = n at hn
  have hr₀ := blockPlaquetteDefect_nonneg y V
  have hLreal : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hc : ∀ μ, (((n μ).natAbs : ℕ) : ℝ) ≤ ((L : ℝ) - 1) / 2 := by
    intro μ
    have h₁ : (2 * ((n μ).natAbs : ℤ) : ℤ) ≤ (L : ℤ) - 1 := by
      rw [← Int.abs_eq_natAbs]
      exact hn μ
    have h₁' : 2 * ((n μ).natAbs : ℤ) + 1 ≤ (L : ℤ) := by linarith
    have h₂ : 2 * ((n μ).natAbs : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast h₁'
    linarith
  have hwords : ∀ l l' : List (Fin 4), l.Perm l' → l.Nodup → l.length ≤ 4 →
      ComplexMatrix2.operatorNorm (wordHolonomy V (y.toSublattice (j + (1 : ℕ)))
          (wordSteps n (replicatedDirections (fun μ => (n μ).natAbs) l)) -
        wordHolonomy V (y.toSublattice (j + (1 : ℕ)))
          (wordSteps n (replicatedDirections (fun μ => (n μ).natAbs) l'))) ≤
        contourSwapConstant L * blockPlaquetteDefect y V := by
    intro l l' hp hl hlen
    have h₁ := norm_sub_elemFlows_perm_le
      (fun w => wordHolonomy V (y.toSublattice (j + (1 : ℕ))) (wordSteps n w)) (CountsWithin n)
      (blockPlaquetteDefect y V) (fun _ _ hp hf => hf.of_perm hp) hr₀
      (norm_wordHolonomy_swap_le hL hm hj hr ha y hB n hn V hV) (fun μ => (n μ).natAbs)
      (((L : ℝ) - 1) / 2) hc l' l [] hp (by simpa using countsWithin_repeatedSteps n l hl)
    simp only [List.nil_append] at h₁
    refine h₁.trans ?_
    have h₆ : unorderedPairs l.length ≤ 6 := by
      interval_cases l.length <;> norm_num [unorderedPairs]
    have h₇ : unorderedPairs l.length * (((L : ℝ) - 1) / 2) ^ 2 ≤ contourSwapConstant L := by
      have : 0 ≤ (((L : ℝ) - 1) / 2) ^ 2 := by positivity
      unfold contourSwapConstant
      nlinarith
    exact mul_le_mul_of_nonneg_right h₇ hr₀
  have hdirs : ∀ σ : AxisOrdering y x, ∀ μ : Fin 4,
      μ ∈ (List.finRange _).map (fun i => ((σ i : offsetAxes y x) : Fin 4)) ↔
        μ ∈ offsetAxes y x := by
    intro σ μ
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (σ i).2
    · intro h
      exact ⟨σ.symm ⟨μ, h⟩, by simp⟩
  have hnodup : ∀ σ : AxisOrdering y x,
      ((List.finRange _).map (fun i => ((σ i : offsetAxes y x) : Fin 4))).Nodup := fun σ =>
    (List.nodup_finRange _).map (Subtype.val_injective.comp σ.injective)
  have hlen : ∀ σ : AxisOrdering y x,
      ((List.finRange _).map (fun i => ((σ i : offsetAxes y x) : Fin 4))).length ≤ 4 := by
    intro σ
    simpa using Finset.card_le_univ (offsetAxes y x)
  have hvalue : ∀ σ : AxisOrdering y x, contourHolonomies V y x σ =
      wordHolonomy V (y.toSublattice (j + (1 : ℕ)))
        (wordSteps n (replicatedDirections (fun μ => (n μ).natAbs) ((List.finRange _).map
          (fun i => ((σ i : offsetAxes y x) : Fin 4))))) := by
    intro σ
    show pathHolonomy V (stepsThroughAxes (blockOffset y x) _ _) = _
    rw [hndef, stepsThroughAxes_eq_pathOfWord]
  have hpair : ∀ σ σ' : AxisOrdering y x,
      ComplexMatrix2.operatorNorm (contourHolonomies V y x σ - contourHolonomies V y x σ') ≤
        contourSwapConstant L * blockPlaquetteDefect y V := by
    intro σ σ'
    rw [hvalue, hvalue]
    refine hwords _ _ ?_ (hnodup σ) (hlen σ)
    exact (List.perm_ext_iff_of_nodup (hnodup σ) (hnodup σ')).2
      fun μ => (hdirs σ μ).trans (hdirs σ' μ).symm
  have hmem : ∀ σ : AxisOrdering y x, contourHolonomies V y x σ ∈ compactGaugeGroup := by
    intro σ
    rw [hvalue]
    exact pathHolonomy_mem_specialUnitary hV _
      (mem_bondsInside_pathOfWord y hB n hn _ (countsWithin_repeatedSteps n _ (hnodup σ)))
  have hbound : 0 ≤ contourSwapConstant L * blockPlaquetteDefect y V :=
    mul_nonneg (by unfold contourSwapConstant; positivity) hr₀
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨σ, rfl⟩ _ ⟨σ', rfl⟩
    exact hpair σ σ'
  · refine Real.iSup_le (fun p => ?_) hbound
    rw [hnorm.2.2.2.1 _ _ (Matrix.specialUnitaryGroup_le_unitaryGroup (hmem p.1))
      (Matrix.specialUnitaryGroup_le_unitaryGroup (hmem p.2))]
    exact hpair p.1 p.2
  · intro hA
    have hmean : ComplexMatrix2.IsLogMean compactGaugeGroup (contourHolonomies V y x)
        (meanContourHolonomy V y x) :=
      Classical.epsilon_spec hA.exists
    refine ⟨hmean, ?_⟩
    rintro _ ⟨σ, rfl⟩
    have h := rotationAngle_le_of_isLogMean hnorm ha (contourHolonomies V y x) hmem _ hbound
      hpair _ hmean σ
    refine ⟨h.1, ?_, ?_⟩
    · rw [mul_assoc]
      exact h.2
    · have h₃ : Real.sqrt 3 ≠ 0 := by positivity
      unfold contourSwapConstant
      field_simp
theorem contourFamilySpread_holds (hb : BlockPartition.Properties)
    (hnorm : ComplexMatrix2.OperatorNormUnderConjugation) (hr : PathRearrangementBound)
    (ha : ComplexMatrix2.SpecialUnitaryAngleBounds) : ContourFamilySpread := by
  intro L m K hL hm n hn y V hV x hx
  exact contourFamilySpread_at (by simp only [levelDepth]; push_cast; ring) hL hm
    (by simp only [levelDepth]; omega) hb hnorm hr ha y V hV x hx
end Main
end YangMills.Construction.PeriodicLattice.ContourSpread
