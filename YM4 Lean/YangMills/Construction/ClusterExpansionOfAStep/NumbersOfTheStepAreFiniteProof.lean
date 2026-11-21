import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStepAreFinite
import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.SummableBoundsOfTheFlow.OneNumberOfOneTotalProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusLumps.PotentialSums
open YangMills.Construction.BlockAverages
theorem summable_exp_neg_mul_natAbs {r : ℝ} (hr : 0 < r) :
    Summable fun k : ℤ => Real.exp (-(r * (k.natAbs : ℝ))) := by apply _root_.YangMills.SharedProofs.p17292 <;> assumption
theorem natAbs_le_offsetNorm (x : Fin 4 → ℤ) (i : Fin 4) : (x i).natAbs ≤ offsetNorm x := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem summable_exp_neg_offsetNorm {r : ℝ} (hr : 0 < r) :
    Summable fun x : Fin 4 → ℤ => Real.exp (-(r * (offsetNorm x : ℝ))) := by
  set g : ℤ → ℝ := fun k => Real.exp (-(r / 4 * (k.natAbs : ℝ))) with hgdef
  have hg : Summable g := summable_exp_neg_mul_natAbs (by positivity)
  have hg0 : ∀ k, 0 ≤ g k := fun _ => (Real.exp_pos _).le
  have s2 : Summable fun p : ℤ × ℤ => g p.1 * g p.2 := hg.mul_of_nonneg hg hg0 hg0
  have s3 : Summable fun p : ℤ × ℤ × ℤ => g p.1 * (g p.2.1 * g p.2.2) :=
    hg.mul_of_nonneg s2 hg0 fun p => mul_nonneg (hg0 _) (hg0 _)
  have s4 : Summable fun p : ℤ × ℤ × ℤ × ℤ => g p.1 * (g p.2.1 * (g p.2.2.1 * g p.2.2.2)) :=
    hg.mul_of_nonneg s3 hg0 fun p => mul_nonneg (hg0 _) (mul_nonneg (hg0 _) (hg0 _))
  have hinj : Function.Injective fun x : Fin 4 → ℤ => ((x 0, x 1, x 2, x 3) : ℤ × ℤ × ℤ × ℤ) := by
    intro x x' e
    simp only [Prod.mk.injEq] at e
    funext i
    fin_cases i
    exacts [e.1, e.2.1, e.2.2.1, e.2.2.2]
  have hs := s4.comp_injective hinj
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) ?_ hs
  intro x
  have e4 : (fun p : ℤ × ℤ × ℤ × ℤ => g p.1 * (g p.2.1 * (g p.2.2.1 * g p.2.2.2))) ∘
      (fun x : Fin 4 → ℤ => ((x 0, x 1, x 2, x 3) : ℤ × ℤ × ℤ × ℤ)) =
      fun x => Real.exp (∑ i : Fin 4, -(r / 4 * ((x i).natAbs : ℝ))) := by
    funext x
    simp only [Function.comp, hgdef, Fin.sum_univ_four]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e4]
  simp only []
  rw [Real.exp_le_exp]
  have : ∑ i : Fin 4, (x i).natAbs ≤ 4 * offsetNorm x := by
    calc ∑ i : Fin 4, (x i).natAbs ≤ ∑ _i : Fin 4, offsetNorm x :=
          Finset.sum_le_sum fun i _ => natAbs_le_offsetNorm x i
      _ = 4 * offsetNorm x := by simp
  have h2 : (∑ i : Fin 4, ((x i).natAbs : ℝ)) ≤ 4 * (offsetNorm x : ℝ) := by exact_mod_cast this
  have : ∑ i : Fin 4, -(r / 4 * ((x i).natAbs : ℝ)) = -(r / 4 * ∑ i : Fin 4, ((x i).natAbs : ℝ)) := by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [this]
  nlinarith
theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
theorem potentialNorm_le_offsetNorm (c : LatticeBond) : potentialNorm c ≤ offsetNorm c.1 := by
  have hb : ∀ ν : Fin 4, ‖((c.1 ν : ℤ) : ℝ) • unitPlaneCurvature ν c.2‖ ≤
      (if ν = 0 ∧ c.2 = 1 then (offsetNorm c.1 : ℝ) else 0) +
        (if ν = 1 ∧ c.2 = 0 then (offsetNorm c.1 : ℝ) else 0) := by
    intro ν
    have hz : |((c.1 ν : ℤ) : ℝ)| ≤ offsetNorm c.1 := by
      have := natAbs_le_offsetNorm c.1 ν
      have h3 : ((c.1 ν).natAbs : ℝ) ≤ offsetNorm c.1 := by exact_mod_cast this
      rwa [Nat.cast_natAbs, Int.cast_abs] at h3
    rw [norm_smul, Real.norm_eq_abs]
    by_cases h1 : ν = 0 ∧ c.2 = 1
    · have : unitPlaneCurvature ν c.2 = quaternionI := by
        simp [unitPlaneCurvature, planeCurvature, h1.1, h1.2]
      rw [this, norm_quaternionI, if_pos h1]
      have h4 : ¬ (ν = 1 ∧ c.2 = 0) := by
        rintro ⟨h5, -⟩
        rw [h1.1] at h5
        exact absurd h5 (by decide)
      rw [if_neg h4]
      simpa using hz
    · by_cases h2 : ν = 1 ∧ c.2 = 0
      · have : unitPlaneCurvature ν c.2 = -quaternionI := by
          simp [unitPlaneCurvature, planeCurvature, h2.1, h2.2]
        rw [this, norm_neg, norm_quaternionI, if_pos h2, if_neg h1]
        simpa using hz
      · have : unitPlaneCurvature ν c.2 = 0 := by
          simp only [unitPlaneCurvature, planeCurvature]
          rw [if_neg h1, if_neg h2]
        rw [this, if_neg h1, if_neg h2]
        simp
  have hsum : ‖∑ ν, ((c.1 ν : ℤ) : ℝ) • unitPlaneCurvature ν c.2‖ ≤ 2 * (offsetNorm c.1 : ℝ) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun ν _ => hb ν).trans ?_)
    rw [Finset.sum_add_distrib]
    have hn : (0 : ℝ) ≤ offsetNorm c.1 := Nat.cast_nonneg _
    have e1 : ∑ ν : Fin 4, (if ν = 0 ∧ c.2 = 1 then (offsetNorm c.1 : ℝ) else 0) ≤ offsetNorm c.1 := by
      by_cases h : c.2 = 1
      · simp [h]
      · simp [h, hn]
    have e2 : ∑ ν : Fin 4, (if ν = 1 ∧ c.2 = 0 then (offsetNorm c.1 : ℝ) else 0) ≤ offsetNorm c.1 := by
      by_cases h : c.2 = 0
      · simp [h]
      · simp [h, hn]
    linarith
  unfold potentialNorm linearPotential
  rw [norm_smul]
  have : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [this]
  linarith
theorem offsetNorm_fst_le_bondPairDiam (c c' : LatticeBond) : offsetNorm c.1 ≤ bondPairDiam c c' :=
  (le_max_left _ _).trans (le_max_left _ _)
theorem offsetNorm_snd_le_bondPairDiam (c c' : LatticeBond) : offsetNorm c'.1 ≤ bondPairDiam c c' :=
  (le_max_right _ _).trans (le_max_left _ _)
theorem summable_offsetNorm_mul_exp {r : ℝ} (hr : 0 < r) :
    Summable fun c : LatticeBond => (offsetNorm c.1 : ℝ) * Real.exp (-(r * (offsetNorm c.1 : ℝ))) := by
  have h1 : Summable fun x : Fin 4 → ℤ =>
      (2 / r) * Real.exp (-(r / 2 * (offsetNorm x : ℝ))) :=
    (summable_exp_neg_offsetNorm (r := r / 2) (by positivity)).mul_left _
  have h2 : Summable fun x : Fin 4 → ℤ => (offsetNorm x : ℝ) * Real.exp (-(r * (offsetNorm x : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) ?_ h1
    intro x
    set m : ℝ := (offsetNorm x : ℝ)
    have hm : r / 2 * m + 1 ≤ Real.exp (r / 2 * m) := by
      have := Real.add_one_le_exp (r / 2 * m)
      linarith
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have e : Real.exp (-(r * m)) = Real.exp (-(r / 2 * m)) * Real.exp (-(r / 2 * m)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [e]
    have e2 : Real.exp (-(r / 2 * m)) * Real.exp (r / 2 * m) = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 : m ≤ (2 / r) * Real.exp (r / 2 * m) := by
      have : (2 / r) * (r / 2 * m + 1) ≤ (2 / r) * Real.exp (r / 2 * m) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      have h4 : (2 / r) * (r / 2 * m + 1) = m + 2 / r := by field_simp
      have h5 : 0 ≤ 2 / r := by positivity
      linarith
    calc m * (Real.exp (-(r / 2 * m)) * Real.exp (-(r / 2 * m)))
        ≤ ((2 / r) * Real.exp (r / 2 * m)) * (Real.exp (-(r / 2 * m)) * Real.exp (-(r / 2 * m))) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (2 / r) * Real.exp (-(r / 2 * m)) * (Real.exp (-(r / 2 * m)) * Real.exp (r / 2 * m)) := by ring
      _ = (2 / r) * Real.exp (-(r / 2 * m)) := by rw [e2]; ring
  have h3 := h2.mul_of_nonneg (hasSum_fintype (fun _ : Fin 4 => (1 : ℝ))).summable
    (fun x => by positivity) (fun _ => zero_le_one)
  simpa using h3
theorem summable_potentialNorm_pairs {r : ℝ} (hr : 0 < r) :
    Summable fun cc : LatticeBond × LatticeBond => potentialNorm cc.1 * potentialNorm cc.2 *
      Real.exp (-(r * bondPairDiam cc.1 cc.2)) := by
  have hs := summable_offsetNorm_mul_exp (r := r / 2) (by positivity)
  have hp := hs.mul_of_nonneg hs (fun c => by positivity) (fun c => by positivity)
  refine Summable.of_nonneg_of_le (fun cc => ?_) (fun cc => ?_) hp
  · have := norm_nonneg (linearPotential unitPlaneCurvature cc.1)
    have := norm_nonneg (linearPotential unitPlaneCurvature cc.2)
    unfold potentialNorm
    positivity
  · have h1 := potentialNorm_le_offsetNorm cc.1
    have h2 := potentialNorm_le_offsetNorm cc.2
    have n2 : 0 ≤ potentialNorm cc.2 := norm_nonneg _
    have d1 : (offsetNorm cc.1.1 : ℝ) ≤ bondPairDiam cc.1 cc.2 := by
      exact_mod_cast offsetNorm_fst_le_bondPairDiam cc.1 cc.2
    have d2 : (offsetNorm cc.2.1 : ℝ) ≤ bondPairDiam cc.1 cc.2 := by
      exact_mod_cast offsetNorm_snd_le_bondPairDiam cc.1 cc.2
    have e : Real.exp (-(r * bondPairDiam cc.1 cc.2)) ≤
        Real.exp (-(r / 2 * (offsetNorm cc.1.1 : ℝ))) * Real.exp (-(r / 2 * (offsetNorm cc.2.1 : ℝ))) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith
    calc potentialNorm cc.1 * potentialNorm cc.2 * Real.exp (-(r * bondPairDiam cc.1 cc.2))
        ≤ (offsetNorm cc.1.1 : ℝ) * (offsetNorm cc.2.1 : ℝ) *
            (Real.exp (-(r / 2 * (offsetNorm cc.1.1 : ℝ))) *
              Real.exp (-(r / 2 * (offsetNorm cc.2.1 : ℝ)))) := by
          gcongr
      _ = _ := by ring
theorem expansionWeight_pos (rt n₁ : ℝ) (m : ℕ) : 0 < expansionWeight rt n₁ m :=
  mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
theorem exp_le_expansionWeight (rt n₁ : ℝ) (m : ℕ) :
    Real.exp (rt / 2 ^ 10 * m) ≤ expansionWeight rt n₁ m := by
  unfold expansionWeight
  have : (1 : ℝ) ≤ max 1 (((m : ℝ) / n₁) ^ 16000) := le_max_left _ _
  nlinarith [Real.exp_pos (rt / 2 ^ 10 * m)]
theorem bddAbove_expansionWeight_mul_exp {rt n₁ : ℝ} (hrt : 0 < rt) (hn : 0 < n₁) :
    BddAbove (Set.range fun m : ℕ => expansionWeight rt n₁ m * Real.exp (-(2 * (rt / 2 ^ 10) * m))) := by
  have hd : 0 < rt / 2 ^ 10 := by positivity
  set d := rt / 2 ^ 10 with hdd
  have ht : Filter.Tendsto (fun y : ℝ => y ^ 16000 * Real.exp (-y)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 16000
  have hdm : Filter.Tendsto (fun m : ℕ => d * (m : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hd
  have ht' : Filter.Tendsto (fun m : ℕ => ((m : ℝ)) ^ 16000 * Real.exp (-d * (m : ℝ)))
      Filter.atTop (nhds 0) := by
    have h1 := (ht.comp hdm).const_mul ((1 / d) ^ 16000)
    simp only [mul_zero] at h1
    refine h1.congr fun m => ?_
    simp only [Function.comp]
    have e1 : (1 / d) ^ 16000 * (d * (m : ℝ)) ^ 16000 = (m : ℝ) ^ 16000 := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [← mul_assoc, e1]
    congr 2
    ring
  obtain ⟨M, hM⟩ := ht'.bddAbove_range
  refine ⟨max 1 (M / n₁ ^ 16000), ?_⟩
  rintro _ ⟨m, rfl⟩
  have hm : ((m : ℝ)) ^ 16000 * Real.exp (-d * (m : ℝ)) ≤ M := hM ⟨m, rfl⟩
  have e : Real.exp (d * m) * Real.exp (-(2 * d * m)) = Real.exp (-d * (m : ℝ)) := by
    rw [← Real.exp_add]
    ring_nf
  have h1 : Real.exp (-d * (m : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  have hq : 0 < n₁ ^ 16000 := by positivity
  simp only [expansionWeight]
  rw [mul_assoc, e]
  rcases le_total 1 (((m : ℝ) / n₁) ^ 16000) with h | h
  · rw [max_eq_right h]
    refine le_trans ?_ (le_max_right _ _)
    rw [div_pow, le_div_iff₀ hq]
    calc ((m : ℝ)) ^ 16000 / n₁ ^ 16000 * Real.exp (-d * (m : ℝ)) * n₁ ^ 16000
        = ((m : ℝ)) ^ 16000 * Real.exp (-d * (m : ℝ)) := by field_simp
      _ ≤ M := hm
  · rw [max_eq_left h]
    refine le_trans ?_ (le_max_left _ _)
    simpa using h1
theorem potentialSumsFinite : PotentialSumsFinite := by
  intro rt n₁ hrt hn
  have hB := summable_potentialNorm_pairs (r := rt / 2 ^ 6) (by positivity)
  have hd : 0 < rt / 2 ^ 10 := by positivity
  have hG0 := summable_potentialNorm_pairs (r := rt / 2 ^ 10) hd
  have nn : ∀ c, 0 ≤ potentialNorm c := fun c => norm_nonneg _
  have hG : Summable (fun cc : LatticeBond × LatticeBond => potentialNorm cc.1 * potentialNorm cc.2 /
      expansionWeight rt n₁ (bondPairDiam cc.1 cc.2)) := by
    refine Summable.of_nonneg_of_le (fun cc => ?_) (fun cc => ?_) hG0
    · exact div_nonneg (mul_nonneg (nn _) (nn _)) (expansionWeight_pos _ _ _).le
    · rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (nn _) (nn _))
      rw [Real.exp_neg]
      exact inv_anti₀ (Real.exp_pos _) (exp_le_expansionWeight _ _ _)
  have hb := bddAbove_expansionWeight_mul_exp hrt hn
  have hle : ∀ m : ℕ, expansionWeight rt n₁ m * Real.exp (-(2 * (rt / 2 ^ 10) * m)) ≤
      weightGrowthSup rt n₁ :=
    fun m => le_ciSup hb m
  refine ⟨hB, hG, hb, hle, ?_, ?_, ?_⟩
  · exact tsum_nonneg fun cc => mul_nonneg (mul_nonneg (nn _) (nn _)) (Real.exp_pos _).le
  · exact mul_nonneg (by norm_num) (tsum_nonneg fun cc =>
      div_nonneg (mul_nonneg (nn _) (nn _)) (expansionWeight_pos _ _ _).le)
  · have := hle 0
    simpa [expansionWeight] using this
end YangMills.Construction.TorusLumps.PotentialSums
end
