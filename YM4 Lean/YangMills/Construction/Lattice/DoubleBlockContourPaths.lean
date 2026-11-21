import YangMills.Construction.Lattice.SpreadOfAContourFamilyProof
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import Mathlib
open YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.PeriodicLattice.DoubleBlock.Contours
section ListPerm
variable {α : Type*}
theorem exists_equiv_get_of_perm {a b : List α} (h : a.Perm b) :
    ∃ e : Fin a.length ≃ Fin b.length, ∀ i, a.get i = b.get (e i) := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i => rfl⟩
  | @cons x l l' _ ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨(finSuccEquiv _).trans ((Equiv.optionCongr e).trans (finSuccEquiv _).symm),
      fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simpa using he i
  | @swap x y l =>
    refine ⟨Equiv.swap (0 : Fin (l.length + 2)) 1, fun i => ?_⟩
    rcases i with ⟨_ | _ | k, hi⟩
    · have : Equiv.swap (0 : Fin (l.length + 2)) 1 ⟨0, hi⟩ = 1 := Equiv.swap_apply_left _ _
      erw [this]
      rfl
    · have : Equiv.swap (0 : Fin (l.length + 2)) 1 ⟨1, hi⟩ = 0 := Equiv.swap_apply_right _ _
      erw [this]
      rfl
    · have : Equiv.swap (0 : Fin (l.length + 2)) 1 ⟨k + 2, hi⟩ = ⟨k + 2, hi⟩ :=
        Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      erw [this]
      rfl
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨e₁, h₁⟩ := ih₁
    obtain ⟨e₂, h₂⟩ := ih₂
    exact ⟨e₁.trans e₂, fun i => (h₁ i).trans (h₂ _)⟩
end ListPerm
section Preliminaries
variable {L m : ℕ} {j : ℤ}
theorem isPermutationOf_of_listPerm {a b : StepWord L m j} (h : a.Perm b) :
    IsPermutationOf a b := by
  obtain ⟨e, he⟩ := exists_equiv_get_of_perm h
  have hl : a.length = b.length := h.length_eq
  refine ⟨(finCongr hl.symm).trans e, ?_⟩
  refine List.ext_get (by simp [hl]) fun i h₁ h₂ => ?_
  have := he ⟨i, h₁⟩
  simpa using this
def replicatedDirections (c : Fin 4 → ℕ) (l : List (Fin 4)) : List (Fin 4) :=
  l.flatMap fun μ => List.replicate (c μ) μ
def axisSign (n : Fin 4 → ℤ) (μ : Fin 4) : ℤ := if 0 ≤ n μ then 1 else -1
def signedUnitStep (n : Fin 4 → ℤ) (μ : Fin 4) : UnitStepVec L m j :=
  ⟨axisSign n μ • unitStep L m j μ, ⟨μ, by unfold axisSign; split_ifs <;> simp⟩⟩
def wordSteps (n : Fin 4 → ℤ) (w : List (Fin 4)) : StepWord L m j := w.map (signedUnitStep n)
def totalStep (s : StepWord L m j) : Site L m j :=
  (s.map fun u : UnitStepVec L m j => (u : Site L m j)).sum
theorem pathOfWord_append_split (z : Site L m j) (s t : StepWord L m j) :
    pathOfWord z (s ++ t) = pathOfWord z s ++ pathOfWord (z + totalStep s) t := by
  induction s generalizing z with
  | nil => simp [pathOfWord, totalStep]
  | cons a s ih => simp [pathOfWord, ih, totalStep, add_assoc]
theorem pathOfWord_injective_word (z : Site L m j) {s t : StepWord L m j}
    (h : pathOfWord z s = pathOfWord z t) : s = t := by
  induction s generalizing z t with
  | nil =>
    cases t with
    | nil => rfl
    | cons b t => simp [pathOfWord] at h
  | cons a s ih =>
    cases t with
    | nil => simp [pathOfWord] at h
    | cons b t =>
      simp only [pathOfWord, List.cons.injEq] at h
      have hab : a = b := Subtype.ext (add_left_cancel (congrArg Bond.target h.1))
      subst hab
      rw [ih (z + a) h.2]
theorem sum_count_smul_bump (sg : Fin 4 → ℤ) (c c' : Fin 4 → ℕ) (ν : Fin 4)
    (h : ∀ μ, c' μ = c μ + if ν = μ then 1 else 0) :
    ∑ μ, ((c' μ : ℤ) * sg μ) • unitStep L m j μ =
      sg ν • unitStep L m j ν + ∑ μ, ((c μ : ℤ) * sg μ) • unitStep L m j μ := by
  have h₂ : ∀ μ, ((c' μ : ℤ) * sg μ) • unitStep L m j μ =
      ((c μ : ℤ) * sg μ) • unitStep L m j μ + if ν = μ then sg ν • unitStep L m j ν else 0 := by
    intro μ
    by_cases hν : ν = μ
    · subst hν
      simp [h, add_mul, add_smul]
    · simp [h, hν]
  simp only [h₂, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  abel
theorem totalStep_wordSteps (n : Fin 4 → ℤ) (w : List (Fin 4)) :
    totalStep (wordSteps n w : StepWord L m j) =
      ∑ μ, ((w.count μ : ℤ) * axisSign n μ) • unitStep L m j μ := by
  induction w with
  | nil => simp [totalStep, wordSteps]
  | cons ν w ih =>
    have h : totalStep (wordSteps n (ν :: w) : StepWord L m j) =
        axisSign n ν • unitStep L m j ν + totalStep (wordSteps n w : StepWord L m j) := by
      simp [totalStep, wordSteps, signedUnitStep]
    rw [h, ih, sum_count_smul_bump (axisSign n) (fun μ => w.count μ) (fun μ => (ν :: w).count μ) ν]
    intro μ
    by_cases hν : ν = μ
    · subst hν
      simp
    · simp [hν]
theorem natAbs_mul_axisSign (n : Fin 4 → ℤ) (μ : Fin 4) :
    ((n μ).natAbs : ℤ) * axisSign n μ = n μ := by apply _root_.YangMills.Construction.PeriodicLattice.ContourSpread.natAbs_mul_axisSign <;> assumption
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
theorem totalStep_replicate_natAbs (n : Fin 4 → ℤ) (μ : Fin 4) :
    totalStep (wordSteps n (List.replicate (n μ).natAbs μ) : StepWord L m j) =
      n μ • unitStep L m j μ := by
  simp only [totalStep, wordSteps, List.map_replicate, List.sum_replicate, signedUnitStep]
  rw [← natCast_zsmul, smul_smul, natAbs_mul_axisSign]
theorem stepsThroughAxes_eq_pathOfWord (n : Fin 4 → ℤ) (l : List (Fin 4)) (z : Site L m j) :
    stepsThroughAxes n z l =
      pathOfWord z (wordSteps n (replicatedDirections (fun μ => (n μ).natAbs) l)) := by
  induction l generalizing z with
  | nil => simp [stepsThroughAxes, replicatedDirections, wordSteps, pathOfWord]
  | cons μ l ih =>
    have e : (wordSteps n (replicatedDirections (fun μ => (n μ).natAbs) (μ :: l)) : StepWord L m j) =
        wordSteps n (List.replicate (n μ).natAbs μ) ++
          wordSteps n (replicatedDirections (fun μ => (n μ).natAbs) l) := by
      simp [wordSteps, replicatedDirections, List.flatMap_cons]
    rw [e, pathOfWord_append_split, totalStep_replicate_natAbs, ← flowAlong_eq_pathOfWord]
    simp only [stepsThroughAxes, ih]
theorem count_repeatedSteps (c : Fin 4 → ℕ) (l : List (Fin 4)) (hl : l.Nodup) (μ : Fin 4) :
    (replicatedDirections c l).count μ = if μ ∈ l then c μ else 0 := by apply _root_.YangMills.Construction.PeriodicLattice.ContourSpread.count_repeatedSteps <;> assumption
theorem length_eq_sum_letterCount (w : List (Fin 4)) : w.length = ∑ μ, w.count μ := by
  induction w with
  | nil => simp
  | cons ν w ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons, ← ih]
    simp
theorem mem_partialSumSites_nil {z x : Site L m j} : x ∈ partialSumSites z [] ↔ x = z := by
  constructor
  · rintro ⟨I, rfl⟩
    obtain rfl : I = ∅ := Finset.eq_empty_of_forall_notMem fun i => i.elim0
    simp
  · rintro rfl
    exact ⟨∅, by simp⟩
theorem mem_partialSumSites_cons {z x : Site L m j} {s : UnitStepVec L m j}
    {t : StepWord L m j} :
    x ∈ partialSumSites z (s :: t) ↔
      x ∈ partialSumSites z t ∨ x ∈ partialSumSites (z + (s : Site L m j)) t := by
  constructor
  · rintro ⟨I, rfl⟩
    let f : Fin (t.length + 1) → Site L m j :=
      fun i => (((s :: t).get i : UnitStepVec L m j) : Site L m j)
    have hI : ∑ i ∈ I, (((s :: t).get i : UnitStepVec L m j) : Site L m j) =
        (if (0 : Fin (t.length + 1)) ∈ I then (s : Site L m j) else 0) +
          ∑ i ∈ Finset.univ.filter (fun i : Fin t.length => i.succ ∈ I),
            ((t.get i : UnitStepVec L m j) : Site L m j) := by
      have e₁ : ∑ i ∈ I, (((s :: t).get i : UnitStepVec L m j) : Site L m j) =
          ∑ i : Fin (t.length + 1), if i ∈ I then f i else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
        rfl
      rw [e₁, Fin.sum_univ_succ, Finset.sum_filter]
      rfl
    rw [hI]
    by_cases h0 : (0 : Fin (t.length + 1)) ∈ I
    · right
      exact ⟨_, by rw [if_pos h0, add_assoc]⟩
    · left
      exact ⟨_, by rw [if_neg h0, zero_add]⟩
  · rintro (⟨J, rfl⟩ | ⟨J, rfl⟩)
    · refine ⟨J.map (Fin.succEmb _), ?_⟩
      rw [Finset.sum_map]
      rfl
    · refine ⟨insert (0 : Fin (t.length + 1)) (J.map (Fin.succEmb _)), ?_⟩
      rw [Finset.sum_insert (by simp), Finset.sum_map, add_assoc]
      rfl
theorem exists_mem_partialSumSites_of_append {z x : Site L m j} {a b : StepWord L m j}
    (h : x ∈ partialSumSites z (a ++ b)) :
    ∃ u ∈ partialSumSites z a, x ∈ partialSumSites u b := by
  induction a generalizing z with
  | nil => exact ⟨z, mem_partialSumSites_nil.2 rfl, h⟩
  | cons s a ih =>
    rcases mem_partialSumSites_cons.1 h with h | h
    · obtain ⟨u, hu, hx⟩ := ih h
      exact ⟨u, mem_partialSumSites_cons.2 (Or.inl hu), hx⟩
    · obtain ⟨u, hu, hx⟩ := ih h
      exact ⟨u, mem_partialSumSites_cons.2 (Or.inr hu), hx⟩
theorem exists_nsmul_of_mem_partialSumSites_replicate {z x : Site L m j} {u : UnitStepVec L m j}
    {t : ℕ} (h : x ∈ partialSumSites z (List.replicate t u)) :
    ∃ r : ℕ, r ≤ t ∧ x = z + r • (u : Site L m j) := by
  induction t generalizing z with
  | zero => exact ⟨0, le_rfl, by simpa using mem_partialSumSites_nil.1 h⟩
  | succ t ih =>
    rw [List.replicate_succ] at h
    rcases mem_partialSumSites_cons.1 h with h | h
    · obtain ⟨r, hr, rfl⟩ := ih h
      exact ⟨r, by omega, rfl⟩
    · obtain ⟨r, hr, rfl⟩ := ih h
      exact ⟨r + 1, by omega, by rw [add_smul, one_smul]; abel⟩
theorem mem_partialSumSites_wordSteps (n : Fin 4 → ℤ) (w : List (Fin 4)) (z x : Site L m j) :
    x ∈ partialSumSites z (wordSteps n w) ↔ ∃ c : Fin 4 → ℕ, (∀ μ, c μ ≤ w.count μ) ∧
      x = z + ∑ μ, ((c μ : ℤ) * axisSign n μ) • unitStep L m j μ := by
  induction w generalizing z with
  | nil =>
    have e : (wordSteps n [] : StepWord L m j) = [] := rfl
    rw [e, mem_partialSumSites_nil]
    constructor
    · rintro rfl
      exact ⟨0, by simp, by simp⟩
    · rintro ⟨c, hc, rfl⟩
      have : ∀ μ, c μ = 0 := fun μ => by simpa using hc μ
      simp [this]
  | cons ν w ih =>
    have e : (wordSteps n (ν :: w) : StepWord L m j) = signedUnitStep n ν :: wordSteps n w := rfl
    have hs : ((signedUnitStep n ν : UnitStepVec L m j) : Site L m j) =
        axisSign n ν • unitStep L m j ν := rfl
    have hcnt : ∀ μ, (ν :: w).count μ = w.count μ + if ν = μ then 1 else 0 := by
      intro μ
      by_cases h : ν = μ
      · subst h
        simp
      · simp [h]
    rw [e, mem_partialSumSites_cons, ih, ih]
    constructor
    · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
      · exact ⟨c, fun μ => (hc μ).trans (by rw [hcnt]; omega), rfl⟩
      · refine ⟨fun μ => c μ + if ν = μ then 1 else 0, fun μ => ?_, ?_⟩
        · rw [hcnt]
          have := hc μ
          beta_reduce
          omega
        · rw [sum_count_smul_bump (axisSign n) c _ ν fun _ => rfl, hs, add_assoc]
    · rintro ⟨c, hc, rfl⟩
      by_cases h0 : c ν = 0
      · left
        refine ⟨c, fun μ => ?_, rfl⟩
        have := hc μ
        rw [hcnt] at this
        by_cases h : ν = μ
        · subst h
          omega
        · simpa [h] using this
      · right
        refine ⟨fun μ => c μ - if ν = μ then 1 else 0, fun μ => ?_, ?_⟩
        · have := hc μ
          rw [hcnt] at this
          beta_reduce
          omega
        · rw [sum_count_smul_bump (axisSign n) (fun μ => c μ - if ν = μ then 1 else 0) c ν, hs,
            add_assoc]
          intro μ
          by_cases h : ν = μ
          · subst h
            simp
            omega
          · simp [h]
theorem endpoints_mem_partialSumSites (z : Site L m j) (s : StepWord L m j) :
    ∀ b ∈ pathOfWord z s, b.source ∈ partialSumSites z s ∧ b.target ∈ partialSumSites z s := by
  induction s generalizing z with
  | nil => simp [pathOfWord]
  | cons a s ih =>
    intro b hb
    rw [pathOfWord, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨⟨∅, by simp [bondOfStep]⟩,
        mem_partialSumSites_cons.2 (Or.inr ⟨∅, by simp [bondOfStep]⟩)⟩
    · obtain ⟨h₁, h₂⟩ := ih _ b hb
      exact ⟨mem_partialSumSites_cons.2 (Or.inr h₁), mem_partialSumSites_cons.2 (Or.inr h₂)⟩
theorem sign_eq_axisSign (n : Fin 4 → ℤ) (μ : Fin 4) (h : n μ ≠ 0) :
    (n μ).sign = axisSign n μ := by
  unfold axisSign
  split_ifs with h₀
  · exact Int.sign_eq_one_of_pos (lt_of_le_of_ne h₀ h.symm)
  · exact Int.sign_eq_neg_one_of_neg (not_le.mp h₀)
theorem partialSumSites_eq_signedBoxSites (n : Fin 4 → ℤ) (w : List (Fin 4))
    (hw : ∀ μ, w.count μ = (n μ).natAbs) (z : Site L m j) :
    partialSumSites z (wordSteps n w) = signedBoxSites z n := by
  ext x
  rw [mem_partialSumSites_wordSteps]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun μ => (c μ : ℤ), fun μ _ => ⟨by positivity, ?_⟩, ?_⟩
    · have := hc μ
      rw [hw] at this
      show (c μ : ℤ) ≤ |n μ|
      rw [Int.abs_eq_natAbs]
      exact_mod_cast this
    · congr 1
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun μ _ => ?_
      by_cases h : n μ = 0
      · have : c μ = 0 := by simpa [hw, h] using hc μ
        simp [h, this]
      · simp [h, sign_eq_axisSign n μ h]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun μ => if n μ ≠ 0 then (t μ).toNat else 0, fun μ => ?_, ?_⟩
    · rw [hw]
      by_cases h : n μ = 0
      · simp [h]
      · have := ht μ h
        simp only [ne_eq, h, not_false_eq_true, if_true]
        rw [Int.abs_eq_natAbs] at this
        omega
    · congr 1
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun μ _ => ?_
      by_cases h : n μ = 0
      · simp [h]
      · have := ht μ h
        simp [h, sign_eq_axisSign n μ h, Int.toNat_of_nonneg this.1]
end Preliminaries
section Coordinates
variable {L m : ℕ} {j j' : ℤ}
theorem coe_toSublattice (hL : 0 < L) (y : Site L m j) (h : j ≤ j') :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coe_toSublattice <;> assumption
theorem coe_zsmul_unitStep (k : ℤ) (μ : Fin 4) :
    ((k • unitStep L m j μ : Site L m j) : FourTorus L m) =
      pointOnAxis L m μ ((k : ℝ) * meshSize L j) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coe_zsmul_unitStep <;> assumption
theorem coe_sum_zsmul_unitStep (p : Fin 4 → ℤ) :
    ((∑ μ, p μ • unitStep L m j μ : Site L m j) : FourTorus L m) =
      ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L j) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coe_sum_zsmul_unitStep <;> assumption
theorem torusProj_eq_sum_pointOnAxis (p : Fin 4 → ℤ) (s : ℝ) :
    torusProj (torusSide L m) (fun μ => s * (p μ : ℝ)) =
      ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * s) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.torusProj_eq_sum <;> assumption
theorem int_eq_zero_of_mul_meshSize_coe_eq_zero (hL : 0 < L) (a : ℤ)
    (h : (((a : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m)) = 0)
    (hb : |(a : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + j')) : a = 0 := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.int_eq_zero_of_coe_mul_meshSize <;> assumption
theorem coeffs_eq_of_sum_pointOnAxis_eq (hL : 0 < L) (p q : Fin 4 → ℤ)
    (h : ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L j') =
      ∑ μ, pointOnAxis L m μ ((q μ : ℝ) * meshSize L j'))
    (hb : ∀ μ, |((p μ - q μ : ℤ) : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + j')) : p = q := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coefficients_eq_of_sum_eq <;> assumption
theorem axialPath_eq_forwardFlow (hL : 0 < L)
    (hN : (L : ℝ) < (L : ℝ) ^ ((m : ℤ) + j')) (z z' : Site L m j') (ν : Fin 4)
    (hz : z' = z + L • unitStep L m j' ν) : axialPath z z' = forwardAxisPath z ν L := by
  subst hz
  have hwit : IsAxialDisplacement z (z + L • unitStep L m j' ν) ν (L : ℤ) :=
    ⟨by simp, by simpa using hN⟩
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement z (z + L • unitStep L m j' ν) q.1 q.2 :=
    ⟨(ν, (L : ℤ)), hwit⟩
  have hq : hex.choose = (ν, (L : ℤ)) := by
    obtain ⟨h₁, h₂⟩ := hex.choose_spec
    rcases hc : hex.choose with ⟨μ, a⟩
    rw [hc] at h₁ h₂
    simp only at h₁ h₂
    have h₃ : ((L : ℤ) • unitStep L m j' ν : Site L m j') = a • unitStep L m j' μ := by
      rw [natCast_zsmul, ← h₁]
      abel
    have h₄ := congrFun (congrArg (fun w : Site L m j' => (w : FourTorus L m)) h₃) ν
    simp only [coe_zsmul_unitStep] at h₄
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have ha : |(a : ℝ)| < (L : ℝ) ^ ((m : ℤ) + j') := by
      simpa using h₂
    by_cases hμ : μ = ν
    · subst hμ
      simp only [pointOnAxis, Pi.single_eq_same] at h₄
      have h₅ : (((((L : ℤ) - a : ℤ) : ℝ) * meshSize L j' : ℝ) :
          AddCircle (torusSide L m)) = 0 := by
        push_cast at h₄ ⊢
        rw [sub_mul, AddCircle.coe_sub, h₄, sub_self]
      have h₆ := int_eq_zero_of_mul_meshSize_coe_eq_zero hL _ h₅ (by
        push_cast
        have := abs_sub (L : ℝ) (a : ℝ)
        rw [abs_of_pos hLr] at this
        linarith)
      have h₇ : a = (L : ℤ) := by omega
      rw [h₇]
    · have hne : ν ≠ μ := fun h => hμ h.symm
      simp only [pointOnAxis, Pi.single_eq_same, Pi.single_eq_of_ne hne] at h₄
      have h₆ := int_eq_zero_of_mul_meshSize_coe_eq_zero hL (L : ℤ) (by simpa using h₄) (by
        simp only [Int.cast_natCast]
        rw [abs_of_pos hLr]
        linarith)
      omega
  unfold axialPath
  rw [dif_pos hex, hq]
  simp [flowAlong]
end Coordinates
section Blocks
variable {L m : ℕ} {j j' : ℤ}
theorem mem_unitBlock_iff_of_eq (hj' : j' = j + (1 : ℕ)) (y : Site L m j)
    (hB : refinedBlock 1 y = blockAsGrid 1 y) (z : FourTorus L m) :
    z ∈ unitBlock y ↔ ∃ p : Fin 4 → ℤ, (∀ μ, 2 * |p μ| ≤ (L : ℤ) - 1) ∧
      z = (y : FourTorus L m) + ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L j') := by
  subst hj'
  show z ∈ refinedBlock 1 y ↔ _
  rw [hB]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, fun μ => ?_, by rw [torusProj_eq_sum_pointOnAxis]⟩
    have h := hp μ
    rw [pow_one] at h
    have : ((2 * |p μ| : ℤ) : ℝ) ≤ (((L : ℤ) - 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, fun μ => ?_, by rw [torusProj_eq_sum_pointOnAxis]⟩
    have h : ((2 * |p μ| : ℤ) : ℝ) ≤ (((L : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hp μ
    push_cast at h
    rw [pow_one]
    linarith
structure RefinementData (L m : ℕ) (j j' : ℤ) : Prop where
  side_ge : 13 ≤ L
  side_odd : Odd L
  exponent_pos : 0 < m
  level_nonneg : 0 ≤ j
  fine_eq : j' = j + (1 : ℕ)
  block_eq : ∀ y : Site L m j, refinedBlock 1 y = blockAsGrid 1 y
namespace RefinementData
variable (D : RefinementData L m j j')
include D
theorem side_pos : 0 < L := by
  have := D.side_ge
  omega
theorem level_le : j ≤ j' := by
  rw [D.fine_eq]
  push_cast
  omega
theorem side_lt_zpow : (L : ℝ) < (L : ℝ) ^ ((m : ℤ) + j') := by
  have h13 : (13 : ℝ) ≤ L := by exact_mod_cast D.side_ge
  have h₁ : (2 : ℤ) ≤ (m : ℤ) + j' := by
    have := D.fine_eq
    have := D.level_nonneg
    have := D.exponent_pos
    push_cast at *
    omega
  have h₂ := zpow_le_zpow_right₀ (a := (L : ℝ)) (by linarith) h₁
  have h₃ : (L : ℝ) ^ (2 : ℤ) = (L : ℝ) * L := by
    rw [zpow_ofNat, sq]
  have h₄ : (L : ℝ) * 13 ≤ (L : ℝ) * L := mul_le_mul_of_nonneg_left h13 (by linarith)
  rw [h₃] at h₂
  linarith
theorem mem_unitBlock (y : Site L m j) (z : FourTorus L m) :
    z ∈ unitBlock y ↔ ∃ p : Fin 4 → ℤ, (∀ μ, 2 * |p μ| ≤ (L : ℤ) - 1) ∧
      z = (y : FourTorus L m) + ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L j') :=
  mem_unitBlock_iff_of_eq D.fine_eq y (D.block_eq y) z
theorem offset_unique {y : Site L m j} {x : Site L m j'} {n n' : Fin 4 → ℤ}
    (h : IsBlockOffset y x n) (h' : IsBlockOffset y x n') : n = n' := by
  refine coeffs_eq_of_sum_pointOnAxis_eq D.side_pos n n' (h.1.symm.trans h'.1) fun μ => ?_
  have h₁ : |n μ - n' μ| ≤ (L : ℤ) - 1 := by
    have := abs_sub (n μ) (n' μ)
    have := h.2 μ
    have := h'.2 μ
    linarith
  have h₂ : |((n μ - n' μ : ℤ) : ℝ)| ≤ (L : ℝ) - 1 := by
    calc |((n μ - n' μ : ℤ) : ℝ)| = ((|n μ - n' μ| : ℤ) : ℝ) := Int.cast_abs.symm
      _ ≤ (((L : ℤ) - 1 : ℤ) : ℝ) := Int.cast_le.mpr h₁
      _ = (L : ℝ) - 1 := by push_cast; ring
  have := D.side_lt_zpow
  have hL : (0 : ℝ) < L := by exact_mod_cast D.side_pos
  linarith
theorem exists_offset (y : Site L m j) (x : Site L m j') (hx : (x : FourTorus L m) ∈ unitBlock y) :
    ∃ n : Fin 4 → ℤ, IsBlockOffset y x n := by
  obtain ⟨p, hp, h⟩ := (D.mem_unitBlock y _).1 hx
  exact ⟨p, sub_eq_iff_eq_add'.2 h, hp⟩
theorem eq_add_sum_of_offset {y : Site L m j} {x : Site L m j'} {n : Fin 4 → ℤ}
    (h : IsBlockOffset y x n) : x = y.toSublattice j' + ∑ μ, n μ • unitStep L m j' μ := by
  apply Subtype.ext
  rw [AddSubgroup.coe_add, coe_toSublattice D.side_pos y D.level_le, coe_sum_zsmul_unitStep]
  exact sub_eq_iff_eq_add'.1 h.1
theorem add_sum_mem_unitBlock (y : Site L m j) (p : Fin 4 → ℤ)
    (hp : ∀ μ, 2 * |p μ| ≤ (L : ℤ) - 1) :
    ((y.toSublattice j' + ∑ μ, p μ • unitStep L m j' μ : Site L m j') : FourTorus L m) ∈
      unitBlock y :=
  (D.mem_unitBlock y _).2 ⟨p, hp, by
    rw [AddSubgroup.coe_add, coe_toSublattice D.side_pos y D.level_le, coe_sum_zsmul_unitStep]⟩
theorem target_toSublattice_eq (c : Bond L m j) (ν : Fin 4)
    (hν : c.target = c.source + unitStep L m j ν) :
    c.target.toSublattice j' = c.source.toSublattice j' + L • unitStep L m j' ν := by
  apply Subtype.ext
  rw [AddSubgroup.coe_add, coe_toSublattice D.side_pos _ D.level_le,
    coe_toSublattice D.side_pos _ D.level_le, hν, AddSubgroup.coe_add]
  congr 1
  rw [← natCast_zsmul, coe_zsmul_unitStep]
  show pointOnAxis L m ν (meshSize L j) = _
  congr 1
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast D.side_pos.ne'
  unfold meshSize
  rw [D.fine_eq]
  push_cast
  rw [neg_add, zpow_add₀ hL, zpow_neg _ (1 : ℤ), zpow_one]
  field_simp
end RefinementData
theorem two_mul_abs_le_iff {a B : ℤ} : 2 * |a| ≤ B ↔ -B ≤ 2 * a ∧ 2 * a ≤ B := by
  rcases abs_cases a with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> omega
theorem add_sum_add_nsmul_mem_bondDoubleBlock (D : RefinementData L m j j') (c : Bond L m j)
    (ν : Fin 4)
    (hE : c.target.toSublattice j' = c.source.toSublattice j' + L • unitStep L m j' ν)
    (p : Fin 4 → ℤ) (hp : ∀ μ, 2 * |p μ| ≤ (L : ℤ) - 1) (r : ℕ) (hr : r ≤ L) :
    ((c.source.toSublattice j' + ∑ μ, p μ • unitStep L m j' μ + r • unitStep L m j' ν :
      Site L m j') : FourTorus L m) ∈ bondDoubleBlock c := by
  obtain ⟨h, hh⟩ := D.side_odd
  have hsum : ∀ a : ℤ, ∑ μ, (p μ + if μ = ν then a else 0) • unitStep L m j' μ =
      ∑ μ, p μ • unitStep L m j' μ + a • unitStep L m j' ν := by
    intro a
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hpν := two_mul_abs_le_iff.1 (hp ν)
  by_cases hc : 2 * (p ν + r) ≤ (L : ℤ) - 1
  · left
    have := D.add_sum_mem_unitBlock c.source (fun μ => p μ + if μ = ν then (r : ℤ) else 0)
      (fun μ => by
        by_cases hμ : μ = ν
        · subst hμ
          simp only [if_true]
          exact two_mul_abs_le_iff.2 ⟨by omega, hc⟩
        · simpa [hμ] using hp μ)
    rw [hsum, natCast_zsmul, ← add_assoc] at this
    exact this
  · right
    have := D.add_sum_mem_unitBlock c.target
      (fun μ => p μ + if μ = ν then (r : ℤ) - L else 0) (fun μ => by
        by_cases hμ : μ = ν
        · subst hμ
          simp only [if_true]
          exact two_mul_abs_le_iff.2 ⟨by omega, by omega⟩
        · simpa [hμ] using hp μ)
    rw [hsum, hE, sub_smul, natCast_zsmul, natCast_zsmul] at this
    have e : c.source.toSublattice j' + L • unitStep L m j' ν +
        (∑ μ, p μ • unitStep L m j' μ + (r • unitStep L m j' ν - L • unitStep L m j' ν)) =
        c.source.toSublattice j' + ∑ μ, p μ • unitStep L m j' μ + r • unitStep L m j' ν := by
      abel
    rw [e] at this
    exact this
variable {y : Site L m j} {x : Site L m j'}
theorem axisSequence_nodup (σ : AxisOrdering y x) : (axisSequence σ).Nodup :=
  List.Nodup.map (fun _ _ h => σ.injective (Subtype.ext h)) (List.nodup_finRange _)
theorem mem_axisSequence (σ : AxisOrdering y x) (μ : Fin 4) :
    μ ∈ axisSequence σ ↔ μ ∈ offsetAxes y x := by
  unfold axisSequence
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (σ i).2
  · intro h
    exact ⟨σ.symm ⟨μ, h⟩, by simp⟩
def orderedWord (σ : AxisOrdering y x) : List (Fin 4) :=
  replicatedDirections (fun μ => (blockOffset y x μ).natAbs) (axisSequence σ)
theorem count_orderedWord (σ : AxisOrdering y x) (μ : Fin 4) :
    (orderedWord σ).count μ = (blockOffset y x μ).natAbs := by
  unfold orderedWord
  rw [count_repeatedSteps _ _ (axisSequence_nodup σ)]
  split_ifs with h
  · rfl
  · rw [mem_axisSequence] at h
    simp only [offsetAxes, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h
    simp [h]
theorem orderedContour_eq_pathOfWord (σ : AxisOrdering y x) :
    orderedContour y x σ =
      pathOfWord (y.toSublattice j') (wordSteps (blockOffset y x) (orderedWord σ)) :=
  stepsThroughAxes_eq_pathOfWord _ _ _
theorem totalStep_of_counts (n : Fin 4 → ℤ) (w : List (Fin 4))
    (hw : ∀ μ, w.count μ = (n μ).natAbs) :
    totalStep (wordSteps n w : StepWord L m j') = ∑ μ, n μ • unitStep L m j' μ := by
  rw [totalStep_wordSteps]
  simp only [hw, natAbs_mul_axisSign]
theorem length_of_counts (n : Fin 4 → ℤ) (w : List (Fin 4))
    (hw : ∀ μ, w.count μ = (n μ).natAbs) :
    (wordSteps n w : StepWord L m j').length = ∑ μ, (n μ).natAbs := by
  simp only [wordSteps, List.length_map]
  rw [length_eq_sum_letterCount]
  simp only [hw]
theorem sum_abs_le_of_two_mul_abs_le (n : Fin 4 → ℤ) (hn : ∀ μ, 2 * |n μ| ≤ (L : ℤ) - 1) :
    ∑ μ, |n μ| ≤ 2 * ((L : ℤ) - 1) := by
  rw [Fin.sum_univ_four]
  have := hn 0
  have := hn 1
  have := hn 2
  have := hn 3
  linarith
theorem sum_natAbs_le_of_two_mul_abs_le (n : Fin 4 → ℤ) (hn : ∀ μ, 2 * |n μ| ≤ (L : ℤ) - 1) :
    ((∑ μ, (n μ).natAbs : ℕ) : ℤ) ≤ 2 * ((L : ℤ) - 1) := by
  have e : ((∑ μ, (n μ).natAbs : ℕ) : ℤ) = ∑ μ, |n μ| := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun μ _ => Int.natCast_natAbs _
  rw [e]
  exact sum_abs_le_of_two_mul_abs_le n hn
theorem two_mul_abs_mul_axisSign_le {n : Fin 4 → ℤ} (hn : ∀ μ, 2 * |n μ| ≤ (L : ℤ) - 1)
    {c : Fin 4 → ℕ} (hc : ∀ μ, c μ ≤ (n μ).natAbs) (μ : Fin 4) :
    2 * |(c μ : ℤ) * axisSign n μ| ≤ (L : ℤ) - 1 := by
  have hs : |axisSign n μ| = 1 := by
    unfold axisSign
    split_ifs <;> simp
  have h₁ : (c μ : ℤ) ≤ |n μ| := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hc μ
  have h₂ := hn μ
  simp only [abs_mul, hs, mul_one, Nat.abs_cast]
  linarith
theorem blockSiteContours_of_offset (D : RefinementData L m j j') (y : Site L m j)
    (x : Site L m j') (n : Fin 4 → ℤ) (hn : IsBlockOffset y x n) : BlockSiteContours y x n := by
  obtain rfl : n = blockOffset y x := D.offset_unique hn (Classical.epsilon_spec ⟨n, hn⟩)
  have hdecode : ∀ (σ : AxisOrdering y x) (s : StepWord L m j'),
      pathOfWord (y.toSublattice j') s = orderedContour y x σ →
        s = wordSteps (blockOffset y x) (orderedWord σ) :=
    fun σ s h => pathOfWord_injective_word _ (h.trans (orderedContour_eq_pathOfWord σ))
  have hsite : ∀ z ∈ signedBoxSites (y.toSublattice j') (blockOffset y x),
      (z : FourTorus L m) ∈ unitBlock y := by
    rintro z ⟨t, ht, rfl⟩
    have e : ∑ μ ∈ Finset.univ.filter (fun μ => blockOffset y x μ ≠ 0),
        (t μ * (blockOffset y x μ).sign) • unitStep L m j' μ =
        ∑ μ, (if blockOffset y x μ ≠ 0 then t μ * (blockOffset y x μ).sign else 0) •
          unitStep L m j' μ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun μ _ => ?_
      split_ifs <;> simp
    rw [e]
    refine D.add_sum_mem_unitBlock y _ fun μ => ?_
    have hL : 0 < (L : ℤ) - 1 := by
      have := D.side_ge
      omega
    by_cases h : blockOffset y x μ = 0
    · simp only [h, ne_eq, not_true_eq_false, if_false, abs_zero, mul_zero]
      exact hL.le
    · have hs : |(blockOffset y x μ).sign| = 1 := by
        rcases lt_or_gt_of_ne h with h' | h'
        · rw [Int.sign_eq_neg_one_of_neg h']
          simp
        · rw [Int.sign_eq_one_of_pos h']
          simp
      have h₁ := ht μ h
      have h₂ := hn.2 μ
      simp only [ne_eq, h, not_false_eq_true, if_true]
      rw [abs_mul, hs, mul_one, abs_of_nonneg h₁.1]
      linarith [h₁.2]
  refine ⟨sum_abs_le_of_two_mul_abs_le _ hn.2, ?_, ?_, ?_, hsite, ?_⟩
  · rintro _ ⟨σ, rfl⟩
    exact ⟨_, length_of_counts _ _ (count_orderedWord σ), (orderedContour_eq_pathOfWord σ).symm⟩
  · rintro _ ⟨σ, rfl⟩ _ ⟨σ', rfl⟩ s s' h h'
    rw [hdecode σ s h, hdecode σ' s' h']
    refine isPermutationOf_of_listPerm (List.Perm.map _ (List.perm_iff_count.2 fun μ => ?_))
    rw [count_orderedWord, count_orderedWord]
  · rintro _ ⟨σ, rfl⟩ s h
    rw [hdecode σ s h]
    exact partialSumSites_eq_signedBoxSites _ _ (count_orderedWord σ) _
  · rintro _ ⟨σ, rfl⟩ b hb
    rw [orderedContour_eq_pathOfWord] at hb
    obtain ⟨h₁, h₂⟩ := endpoints_mem_partialSumSites _ _ b hb
    rw [partialSumSites_eq_signedBoxSites _ _ (count_orderedWord σ)] at h₁ h₂
    exact ⟨hsite _ h₁, hsite _ h₂⟩
theorem pathOfWord_replicate_positive (z : Site L m j') (ν : Fin 4) (k : ℕ) :
    pathOfWord z (List.replicate k (positiveUnitStep L m j' ν)) = forwardAxisPath z ν k := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, pathOfWord, ih]
    rfl
theorem exists_ordering_of_eq (A B : Finset (Fin 4)) (h : B = A) (σ : Fin A.card ≃ A) :
    ∃ σ' : Fin B.card ≃ B, (List.finRange _).map (fun i => ((σ' i : B) : Fin 4)) =
      (List.finRange _).map fun i => ((σ i : A) : Fin 4) := by
  subst h
  exact ⟨σ, rfl⟩
theorem contoursAcrossBond_of_mem (D : RefinementData L m j j') (c : Bond L m j) (ν : Fin 4)
    (hν : c.target = c.source + unitStep L m j ν) (x : Site L m j')
    (hx : (x : FourTorus L m) ∈ unitBlock c.source)
    (σ : AxisOrdering c.source x) (aw : StepWord L m j')
    (haw : pathOfWord (c.source.toSublattice j') aw = orderedContour c.source x σ) :
    ContoursAcrossBond c ν x σ aw := by
  have hspec : IsBlockOffset c.source x (blockOffset c.source x) :=
    Classical.epsilon_spec (D.exists_offset c.source x hx)
  obtain ⟨n, hn⟩ : ∃ n, n = blockOffset c.source x := ⟨_, rfl⟩
  rw [← hn] at hspec
  have hw : ∀ μ, (orderedWord σ).count μ = (n μ).natAbs := fun μ => by
    rw [hn, count_orderedWord]
  have haw' : aw = wordSteps n (orderedWord σ) := by
    rw [hn]
    exact pathOfWord_injective_word _ (haw.trans (orderedContour_eq_pathOfWord σ))
  have hE := D.target_toSublattice_eq c ν hν
  have hxe := D.eq_add_sum_of_offset hspec
  have hsum : totalStep aw = ∑ μ, n μ • unitStep L m j' μ := by
    rw [haw']
    exact totalStep_of_counts n _ hw
  have hlen : aw.length = ∑ μ, (n μ).natAbs := by
    rw [haw']
    exact length_of_counts n _ hw
  have hxsum : c.source.toSublattice j' + totalStep aw = x := by rw [hsum, ← hxe]
  have hsites : ∀ z ∈ partialSumSites (c.source.toSublattice j') aw, ∃ p : Fin 4 → ℤ,
      (∀ μ, 2 * |p μ| ≤ (L : ℤ) - 1) ∧
        z = c.source.toSublattice j' + ∑ μ, p μ • unitStep L m j' μ := by
    intro z hz
    rw [haw', mem_partialSumSites_wordSteps] at hz
    obtain ⟨e, he, rfl⟩ := hz
    exact ⟨_, two_mul_abs_mul_axisSign_le hspec.2 (c := e) (fun μ => by rw [← hw]; exact he μ),
      rfl⟩
  have hbd : blockOffset c.target (x + L • unitStep L m j' ν) = n := by
    have hEc : (c.target : FourTorus L m) =
        (c.source : FourTorus L m) + ((L • unitStep L m j' ν : Site L m j') : FourTorus L m) := by
      have := congrArg (fun w : Site L m j' => (w : FourTorus L m)) hE
      simp only [AddSubgroup.coe_add] at this
      rwa [coe_toSublattice D.side_pos _ D.level_le, coe_toSublattice D.side_pos _ D.level_le]
        at this
    have hd : ((x + L • unitStep L m j' ν : Site L m j') : FourTorus L m) -
        (c.target : FourTorus L m) = (x : FourTorus L m) - (c.source : FourTorus L m) := by
      rw [AddSubgroup.coe_add, hEc]
      abel
    have hp : IsBlockOffset c.target (x + L • unitStep L m j' ν) =
        IsBlockOffset c.source x := by
      funext q
      unfold IsBlockOffset
      rw [hd]
    unfold blockOffset
    rw [hp, hn]
    rfl
  have hdir : offsetAxes c.target (x + L • unitStep L m j' ν) = offsetAxes c.source x := by
    unfold offsetAxes
    rw [hbd, hn]
  unfold ContoursAcrossBond
  intro x' ew sourceSite targetSite
  have hx' : x' = targetSite + ∑ μ, n μ • unitStep L m j' μ := by
    show x + L • unitStep L m j' ν = c.target.toSublattice j' + _
    rw [hE, add_right_comm, ← hxe]
  have hsumew : totalStep ew = L • unitStep L m j' ν := by
    simp only [totalStep, ew, List.map_replicate, List.sum_replicate]
    rfl
  have hs₁ : axialPath x x' = forwardAxisPath x ν L :=
    axialPath_eq_forwardFlow D.side_pos D.side_lt_zpow _ _ ν rfl
  have hs₂ : axialPath sourceSite targetSite = forwardAxisPath sourceSite ν L :=
    axialPath_eq_forwardFlow D.side_pos D.side_lt_zpow _ _ ν hE
  have hA : pathOfWord sourceSite (aw ++ ew) = orderedContour c.source x σ ++ axialPath x x' := by
    rw [pathOfWord_append_split, hxsum, pathOfWord_replicate_positive, hs₁, haw]
  have hB : pathOfWord sourceSite (ew ++ aw) =
      axialPath sourceSite targetSite ++ pathOfWord targetSite aw := by
    have e : sourceSite + totalStep ew = targetSite := by rw [hsumew]; exact hE.symm
    rw [pathOfWord_append_split, e, pathOfWord_replicate_positive, hs₂]
  have hSA : ∀ z ∈ partialSumSites sourceSite (aw ++ ew),
      (z : FourTorus L m) ∈ bondDoubleBlock c := by
    intro z hz
    obtain ⟨u, hu, hz⟩ := exists_mem_partialSumSites_of_append hz
    obtain ⟨r, hr, rfl⟩ := exists_nsmul_of_mem_partialSumSites_replicate hz
    obtain ⟨p, hp, rfl⟩ := hsites u hu
    exact add_sum_add_nsmul_mem_bondDoubleBlock D c ν hE p hp r hr
  have hSB : ∀ z ∈ partialSumSites sourceSite (ew ++ aw),
      (z : FourTorus L m) ∈ bondDoubleBlock c := by
    intro z hz
    obtain ⟨u, hu, hz⟩ := exists_mem_partialSumSites_of_append hz
    obtain ⟨r, hr, rfl⟩ := exists_nsmul_of_mem_partialSumSites_replicate hu
    rw [haw', mem_partialSumSites_wordSteps] at hz
    obtain ⟨e, he, rfl⟩ := hz
    have := add_sum_add_nsmul_mem_bondDoubleBlock D c ν hE _
      (two_mul_abs_mul_axisSign_le hspec.2 (c := e) (fun μ => by rw [← hw]; exact he μ)) r hr
    rw [add_right_comm] at this
    exact this
  have hsA : ∀ b ∈ axialPath x x',
      (b.source : FourTorus L m) ∈ bondDoubleBlock c ∧
        (b.target : FourTorus L m) ∈ bondDoubleBlock c := by
    intro b hb
    have hb' : b ∈ pathOfWord sourceSite (aw ++ ew) := by
      rw [hA]
      exact List.mem_append_right _ hb
    obtain ⟨h₁, h₂⟩ := endpoints_mem_partialSumSites _ _ b hb'
    exact ⟨hSA _ h₁, hSA _ h₂⟩
  have hsB : ∀ b ∈ axialPath sourceSite targetSite,
      (b.source : FourTorus L m) ∈ bondDoubleBlock c ∧
        (b.target : FourTorus L m) ∈ bondDoubleBlock c := by
    intro b hb
    have hb' : b ∈ pathOfWord sourceSite (ew ++ aw) := by
      rw [hB]
      exact List.mem_append_left _ hb
    obtain ⟨h₁, h₂⟩ := endpoints_mem_partialSumSites _ _ b hb'
    exact ⟨hSB _ h₁, hSB _ h₂⟩
  have hlenew : ew.length = L := List.length_replicate ..
  refine ⟨?_, ?_, isPermutationOf_of_listPerm List.perm_append_comm,
    isPermutationOf_of_listPerm List.perm_append_comm, by simp [hlenew],
    by simp [hlenew, add_comm], ?_, hA, hB, hSA, hSB, hsA, hsB⟩
  · rw [hx']
    exact D.add_sum_mem_unitBlock c.target n hspec.2
  · obtain ⟨σ', hσ'⟩ := exists_ordering_of_eq _ _ hdir σ
    refine ⟨σ', hσ', ?_⟩
    show _ = stepsThroughAxes (blockOffset c.target (x + L • unitStep L m j' ν))
      (c.target.toSublattice j') (axisSequence σ')
    have hσ'' : axisSequence σ' = axisSequence σ := hσ'
    rw [hbd, hσ'', stepsThroughAxes_eq_pathOfWord, haw', hn]
    rfl
  · rw [hlen]
    have := sum_natAbs_le_of_two_mul_abs_le n hspec.2
    omega
end Blocks
theorem doubleBlockContoursStatement_holds (hc : StandardPartitionCubeGeometry) :
    DoubleBlockContoursStatement := by
  intro L m K hodd h13 hm k hk c
  have hj : 0 ≤ levelDepth K (k + 1) := by
    simp only [levelDepth]
    omega
  have D : RefinementData L m (levelDepth K (k + 1)) (levelDepth K k) :=
    ⟨h13, hodd, hm, hj, by simp only [levelDepth]; push_cast; ring, fun y =>
      ((hc L m hodd h13 hm _ (by omega)).1 1).1 y⟩
  refine ⟨fun y hy => ⟨?_, fun x hx => ⟨D.exists_offset y x hx,
      fun n hn => blockSiteContours_of_offset D y x n hn⟩⟩,
    fun ν hν x hx σ aw haw => contoursAcrossBond_of_mem D c ν hν x hx σ aw haw⟩
  rcases hy with rfl | rfl
  · exact Set.subset_union_left
  · exact Set.subset_union_right
end YangMills.Construction.PeriodicLattice.DoubleBlock.Contours
