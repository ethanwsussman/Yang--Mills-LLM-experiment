import YangMills.Construction.ColdChainAtEveryLevel.LineOfANearlyConstantKernel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open FiniteDifferences
namespace NearlyConstantKernel
section Pointwise
variable {ι : Type} {s : Finset ι} {u : ι → ℝ} {e : ι → ι → ι → ℍ[ℝ]} {η : ℝ}
theorem norm_convexCombination_le (hu : ∀ i ∈ s, 0 ≤ u i) (hs : ∑ i ∈ s, u i = 1) {g : ι → ℍ[ℝ]} {d : ℝ}
    (hg : ∀ i ∈ s, ‖g i‖ ≤ d) : ‖∑ i ∈ s, (u i : ℍ[ℝ]) * g i‖ ≤ d := by
  calc ‖∑ i ∈ s, (u i : ℍ[ℝ]) * g i‖ ≤ ∑ i ∈ s, ‖(u i : ℍ[ℝ]) * g i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, u i * d := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, Quaternion.norm_coe, Real.norm_eq_abs, abs_of_nonneg (hu i hi)]
        exact mul_le_mul_of_nonneg_left (hg i hi) (hu i hi)
    _ = d := by rw [← Finset.sum_mul, hs, one_mul]
theorem norm_perturbationApply_le (hu : ∀ i ∈ s, 0 ≤ u i) (hs : ∑ i ∈ s, u i = 1) {i : ι}
    (he : ∀ i' ∈ s, ∀ i'' ∈ s, ‖e i i' i''‖ ≤ η) (hη : 0 ≤ η) {g : ι → ℍ[ℝ]} {d : ℝ} (hd : 0 ≤ d)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ d) : ‖perturbationApply s u e g i‖ ≤ η * d := by
  unfold perturbationApply
  have h1 : ∀ i' ∈ s, ‖∑ i'' ∈ s, (u i'' : ℍ[ℝ]) * (e i i' i'' * g i'')‖ ≤ η * d := by
    intro i' hi'
    refine norm_convexCombination_le hu hs fun i'' hi'' => ?_
    rw [norm_mul]
    exact mul_le_mul (he i' hi' i'' hi'') (hg i'' hi'') (norm_nonneg _) hη
  have h2 := norm_convexCombination_le hu hs h1
  simpa only [Finset.mul_sum] using h2
theorem perturbationApply_sub (g g' : ι → ℍ[ℝ]) (i : ι) :
    perturbationApply s u e g i - perturbationApply s u e g' i =
      perturbationApply s u e (fun j => g j - g' j) i := by
  simp only [perturbationApply, ← Finset.sum_sub_distrib, mul_sub]
theorem perturbationMean_sub (g g' : ι → ℍ[ℝ]) :
    perturbationMean s u e g - perturbationMean s u e g' = perturbationMean s u e (fun j => g j - g' j) := by
  simp only [perturbationMean, ← Finset.sum_sub_distrib, ← mul_sub]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [perturbationApply_sub g g' i]
theorem norm_perturbationMean_le (hu : ∀ i ∈ s, 0 ≤ u i) (hs : ∑ i ∈ s, u i = 1)
    (he : ∀ i ∈ s, ∀ i' ∈ s, ∀ i'' ∈ s, ‖e i i' i''‖ ≤ η) (hη : 0 ≤ η) {g : ι → ℍ[ℝ]} {d : ℝ} (hd : 0 ≤ d)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ d) : ‖perturbationMean s u e g‖ ≤ η * d :=
  norm_convexCombination_le hu hs fun i hi => norm_perturbationApply_le hu hs (he i hi) hη hd hg
theorem norm_eigenStep_sub_le (hu : ∀ i ∈ s, 0 ≤ u i) (hs : ∑ i ∈ s, u i = 1)
    (he : ∀ i ∈ s, ∀ i' ∈ s, ∀ i'' ∈ s, ‖e i i' i''‖ ≤ η) (hη : 0 ≤ η) {a b : ι → ℍ[ℝ]} {d : ℝ} (hd : 0 ≤ d)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 2) (hb : ∀ i ∈ s, ‖b i‖ ≤ 2) (hab : ∀ i ∈ s, ‖a i - b i‖ ≤ d) {i : ι}
    (hi : i ∈ s) : ‖eigenStep s u e a i - eigenStep s u e b i‖ ≤ 5 * η * d := by
  have h1 : ‖perturbationApply s u e a i - perturbationApply s u e b i‖ ≤ η * d := by
    rw [perturbationApply_sub a b i]
    exact norm_perturbationApply_le hu hs (he i hi) hη hd hab
  have h2 : ‖perturbationMean s u e a - perturbationMean s u e b‖ ≤ η * d := by
    rw [perturbationMean_sub]
    exact norm_perturbationMean_le hu hs he hη hd hab
  have h3 : ‖perturbationMean s u e a‖ ≤ η * 2 := norm_perturbationMean_le hu hs he hη (by norm_num) ha
  have e1 : eigenStep s u e a i - eigenStep s u e b i =
      (perturbationApply s u e a i - perturbationApply s u e b i) - (a i - b i) * perturbationMean s u e a -
        b i * (perturbationMean s u e a - perturbationMean s u e b) := by
    simp only [eigenStep, sub_mul, mul_sub]
    abel
  rw [e1]
  have h4 : ‖(a i - b i) * perturbationMean s u e a‖ ≤ d * (η * 2) := by
    rw [norm_mul]
    exact mul_le_mul (hab i hi) h3 (norm_nonneg _) hd
  have h5 : ‖b i * (perturbationMean s u e a - perturbationMean s u e b)‖ ≤ 2 * (η * d) := by
    rw [norm_mul]
    exact mul_le_mul (hb i hi) h2 (norm_nonneg _) (by norm_num)
  calc _ ≤ ‖perturbationApply s u e a i - perturbationApply s u e b i‖ +
        ‖(a i - b i) * perturbationMean s u e a‖ +
        ‖b i * (perturbationMean s u e a - perturbationMean s u e b)‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ 5 * η * d := by nlinarith
end Pointwise
section Bounds
variable {A ι : Type} [AddCommGroup A] {len : A → ℝ}
def realToQuaternionHom : ℝ →+ ℍ[ℝ] := AddMonoidHom.mk' (fun r => (r : ℍ[ℝ])) (fun a b => by simp)
theorem finiteDiffBound_coe {k : ℕ} {D : Set A} {B : ℝ} {f : A → ℝ} (h : FiniteDiffBound len k D B f) :
    FiniteDiffBound len k D B (fun x => ((f x : ℝ) : ℍ[ℝ])) :=
  (h.map realToQuaternionHom fun w => by simp [realToQuaternionHom]).congr fun _ => rfl
theorem finiteDiffBound_perturbationApply (hl : ∀ a, 0 ≤ len a) {D : Set A} {s : Finset ι} {w : ι → A → ℝ}
    {e : ι → ι → ι → ℍ[ℝ]} {g : A → ι → ℍ[ℝ]} {Bw H η : ℝ} {K : ℕ} {i : ι} (hK : s.card ≤ K) (hBw : 0 ≤ Bw)
    (hH : 0 ≤ H) (hη : 0 ≤ η) (he : ∀ i' ∈ s, ∀ i'' ∈ s, ‖e i i' i''‖ ≤ η)
    (hw : ∀ i ∈ s, FiniteDiffBound len 3 D Bw (w i))
    (hg : ∀ i ∈ s, FiniteDiffBound len 3 D H (fun x => g x i)) :
    FiniteDiffBound len 3 D ((K : ℝ) ^ 2 * (512 * Bw ^ 2) * (η * H))
      (fun x => perturbationApply s (fun i => w i x) e (g x) i) := by
  have hterm : ∀ i' ∈ s, ∀ i'' ∈ s, FiniteDiffBound len 3 D (512 * Bw ^ 2 * (η * H))
      (fun x => ((w i' x : ℝ) : ℍ[ℝ]) * (((w i'' x : ℝ) : ℍ[ℝ]) * (e i i' i'' * g x i''))) := by
    intro i' hi' i'' hi''
    have c1 : FiniteDiffBound len 3 D η (fun _ : A => e i i' i'') :=
      (FiniteDiffBound.const hl _).bound_mono hl (he i' hi' i'' hi'')
    have m1 := FiniteDiffBound.mul hl hη hH c1 (hg i'' hi'')
    have m2 := FiniteDiffBound.mul hl hBw (by positivity) (finiteDiffBound_coe (hw i'' hi'')) m1
    have m3 := FiniteDiffBound.mul hl hBw (by positivity) (finiteDiffBound_coe (hw i' hi')) m2
    have e1 : (2 : ℝ) ^ 3 * Bw * (2 ^ 3 * Bw * (2 ^ 3 * η * H)) = 512 * Bw ^ 2 * (η * H) := by ring
    rw [e1] at m3
    exact m3
  have hb : 0 ≤ 512 * Bw ^ 2 * (η * H) := by positivity
  have inner : ∀ i' ∈ s, FiniteDiffBound len 3 D ((K : ℝ) * (512 * Bw ^ 2 * (η * H)))
      (fun x => ∑ i'' ∈ s, ((w i' x : ℝ) : ℍ[ℝ]) * (((w i'' x : ℝ) : ℍ[ℝ]) * (e i i' i'' * g x i''))) := by
    intro i' hi'
    have := FiniteDiffBound.sum hl s (fun _ _ => hb) (hterm i' hi')
    refine this.bound_mono hl ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hb
  have hb2 : 0 ≤ (K : ℝ) * (512 * Bw ^ 2 * (η * H)) := by positivity
  have outer := FiniteDiffBound.sum hl s (fun _ _ => hb2) inner
  refine outer.bound_mono hl ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (s.card : ℝ) * ((K : ℝ) * (512 * Bw ^ 2 * (η * H))) ≤
      (K : ℝ) * ((K : ℝ) * (512 * Bw ^ 2 * (η * H))) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hb2
  calc _ ≤ _ := this
    _ = _ := by ring
theorem finiteDiffBound_perturbationMean (hl : ∀ a, 0 ≤ len a) {D : Set A} {s : Finset ι} {w : ι → A → ℝ}
    {e : ι → ι → ι → ℍ[ℝ]} {g : A → ι → ℍ[ℝ]} {Bw H η : ℝ} {K : ℕ} (hK : s.card ≤ K) (hBw : 0 ≤ Bw)
    (hH : 0 ≤ H) (hη : 0 ≤ η) (he : ∀ i ∈ s, ∀ i' ∈ s, ∀ i'' ∈ s, ‖e i i' i''‖ ≤ η)
    (hw : ∀ i ∈ s, FiniteDiffBound len 3 D Bw (w i))
    (hg : ∀ i ∈ s, FiniteDiffBound len 3 D H (fun x => g x i)) :
    FiniteDiffBound len 3 D ((K : ℝ) * (8 * Bw * ((K : ℝ) ^ 2 * (512 * Bw ^ 2) * (η * H))))
      (fun x => perturbationMean s (fun i => w i x) e (g x)) := by
  have hb : 0 ≤ 8 * Bw * ((K : ℝ) ^ 2 * (512 * Bw ^ 2) * (η * H)) := by positivity
  have hterm : ∀ i ∈ s, FiniteDiffBound len 3 D (8 * Bw * ((K : ℝ) ^ 2 * (512 * Bw ^ 2) * (η * H)))
      (fun x => ((w i x : ℝ) : ℍ[ℝ]) * perturbationApply s (fun i => w i x) e (g x) i) := by
    intro i hi
    have := FiniteDiffBound.mul hl hBw (by positivity) (finiteDiffBound_coe (hw i hi))
      (finiteDiffBound_perturbationApply hl hK hBw hH hη (he i hi) hw hg)
    norm_num at this ⊢
    exact this
  have := FiniteDiffBound.sum hl s (fun _ _ => hb) hterm
  refine this.bound_mono hl ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hb
def eigenStepIterate (s : Finset ι) (w : ι → A → ℝ) (e : ι → ι → ι → ℍ[ℝ]) : ℕ → A → ι → ℍ[ℝ]
  | 0, _, _ => 1
  | n + 1, x, i => eigenStep s (fun i => w i x) e (eigenStepIterate s w e n x) i
theorem tendsto_perturbationApply {s : Finset ι} {u : ι → ℝ} {e : ι → ι → ι → ℍ[ℝ]} {a : ℕ → ι → ℍ[ℝ]}
    {b : ι → ℍ[ℝ]} (i : ι) (h : ∀ j ∈ s, Filter.Tendsto (fun n => a n j) Filter.atTop (nhds (b j))) :
    Filter.Tendsto (fun n => perturbationApply s u e (a n) i) Filter.atTop
      (nhds (perturbationApply s u e b i)) := by
  refine tendsto_finsetSum _ fun i' _ => tendsto_finsetSum _ fun i'' hi'' => ?_
  exact ((h i'' hi'').const_mul _ |>.const_mul _).const_mul _
theorem tendsto_perturbationMean {s : Finset ι} {u : ι → ℝ} {e : ι → ι → ι → ℍ[ℝ]} {a : ℕ → ι → ℍ[ℝ]}
    {b : ι → ℍ[ℝ]} (h : ∀ j ∈ s, Filter.Tendsto (fun n => a n j) Filter.atTop (nhds (b j))) :
    Filter.Tendsto (fun n => perturbationMean s u e (a n)) Filter.atTop (nhds (perturbationMean s u e b)) :=
  tendsto_finsetSum _ fun i _ => (tendsto_perturbationApply i h).const_mul _
theorem sum_coe_eq_one {s : Finset ι} {u : ι → ℝ} (hs : ∑ i ∈ s, u i = 1) : ∑ i ∈ s, (u i : ℍ[ℝ]) = 1 := by
  have := map_sum realToQuaternionHom u s
  simp only [realToQuaternionHom, AddMonoidHom.mk'_apply, hs] at this
  simpa using this.symm
end Bounds
theorem eigenvectorNearOne_holds : EigenvectorNearOne := by
  intro K Bw hBw
  set c1 : ℝ := (K : ℝ) ^ 2 * (512 * Bw ^ 2) with hc1
  set c2 : ℝ := (K : ℝ) * (8 * Bw * c1) with hc2
  set C : ℝ := 2 * (c1 + 16 * c2) + 1 with hC
  have hCpos : 0 < C := by positivity
  refine ⟨min (1 / C) (1 / 10), C, lt_min (by positivity) (by norm_num), hCpos, ?_⟩
  intro A ι _ len D s w e η hl hK hη0 hηc he hw hw0 hw1
  have hη10 : η ≤ 1 / 10 := hηc.trans (min_le_right _ _)
  have hCη : C * η ≤ 1 := by
    have : η ≤ 1 / C := hηc.trans (min_le_left _ _)
    rw [le_div_iff₀ hCpos] at this
    linarith
  have hCη0 : 0 ≤ C * η := by positivity
  set Hn := eigenStepIterate s w e with hHn
  have hdec : ∀ n, ∀ i ∈ s, FiniteDiffBound len 3 D (C * η) (fun x => Hn n x i - 1) := by
    intro n
    induction n with
    | zero =>
      intro i _
      have := FiniteDiffBound.zero (W := ℍ[ℝ]) (k := 3) (S := D) hl hCη0
      refine this.congr fun x => ?_
      simp [hHn, eigenStepIterate]
    | succ n ih =>
      intro i hi
      have hg : ∀ i ∈ s, FiniteDiffBound len 3 D 2 (fun x => Hn n x i) := by
        intro i hi
        have h1 := (ih i hi).add (FiniteDiffBound.const (W := ℍ[ℝ]) (k := 3) (S := D) hl 1)
        have h2 : C * η + ‖(1 : ℍ[ℝ])‖ ≤ 2 := by simp; linarith
        exact (h1.bound_mono hl h2).congr fun x => by simp
      have a1 := finiteDiffBound_perturbationApply (i := i) hl hK hBw (by norm_num) hη0 (he i hi) hw hg
      have a2 := finiteDiffBound_perturbationMean hl hK hBw (by norm_num) hη0 he hw hg
      have a3 := FiniteDiffBound.mul hl (by norm_num) (by positivity) (hg i hi) a2
      have a4 := a1.sub a3
      have hb : (K : ℝ) ^ 2 * (512 * Bw ^ 2) * (η * 2) +
          2 ^ 3 * 2 * ((K : ℝ) * (8 * Bw * ((K : ℝ) ^ 2 * (512 * Bw ^ 2) * (η * 2)))) ≤ C * η := by
        have : (K : ℝ) ^ 2 * (512 * Bw ^ 2) * (η * 2) +
          2 ^ 3 * 2 * ((K : ℝ) * (8 * Bw * ((K : ℝ) ^ 2 * (512 * Bw ^ 2) * (η * 2)))) =
            (2 * (c1 + 16 * c2)) * η := by rw [hc2, hc1]; ring
        rw [this, hC]
        nlinarith
      refine (a4.bound_mono hl hb).congr fun x => ?_
      simp only [hHn, eigenStepIterate, eigenStep]
      abel
  have hball : ∀ n, ∀ x ∈ D, ∀ i ∈ s, ‖Hn n x i‖ ≤ 2 := by
    intro n x hx i hi
    have h1 := (hdec n i hi).norm_le x hx
    have : ‖Hn n x i‖ ≤ ‖Hn n x i - 1‖ + ‖(1 : ℍ[ℝ])‖ := by
      simpa using norm_add_le (Hn n x i - 1) 1
    simp at this
    linarith
  have hclose : ∀ x ∈ D, ∀ n, ∀ i ∈ s, ‖Hn (n + 1) x i - Hn n x i‖ ≤ 2 * (1 / 2) ^ n := by
    intro x hx n
    have hu := hw0 x hx
    have hs := hw1 x hx
    induction n with
    | zero =>
      intro i hi
      have h1 := (hdec 1 i hi).norm_le x hx
      have : Hn 0 x i = 1 := by simp [hHn, eigenStepIterate]
      rw [this]
      simp only [zero_add, pow_zero, mul_one]
      linarith
    | succ n ih =>
      intro i hi
      have := norm_eigenStep_sub_le hu hs he hη0 (by positivity) (hball (n + 1) x hx) (hball n x hx) ih hi
      have e1 : Hn (n + 1 + 1) x i = eigenStep s (fun i => w i x) e (Hn (n + 1) x) i := rfl
      have e2 : Hn (n + 1) x i = eigenStep s (fun i => w i x) e (Hn n x) i := rfl
      rw [e1, e2]
      refine this.trans ?_
      have : (0 : ℝ) ≤ 2 * (1 / 2) ^ n := by positivity
      have e3 : 2 * (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) * (2 * (1 / 2) ^ n) := by ring
      rw [e3]
      nlinarith
  have hcauchy : ∀ x ∈ D, ∀ i ∈ s, CauchySeq (fun n => Hn n x i) := by
    intro x hx i hi
    refine cauchySeq_of_le_geometric (1 / 2) 2 (by norm_num) fun n => ?_
    rw [dist_comm, dist_eq_norm]
    exact hclose x hx n i hi
  have hex : ∀ x i, ∃ l : ℍ[ℝ], x ∈ D → i ∈ s →
      Filter.Tendsto (fun n => Hn n x i) Filter.atTop (nhds l) := by
    intro x i
    by_cases hc : x ∈ D ∧ i ∈ s
    · obtain ⟨l, hl'⟩ := cauchySeq_tendsto_of_complete (hcauchy x hc.1 i hc.2)
      exact ⟨l, fun _ _ => hl'⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose h htend0 using hex
  have htend : ∀ x ∈ D, ∀ i ∈ s, Filter.Tendsto (fun n => Hn n x i) Filter.atTop (nhds (h x i)) :=
    fun x hx i hi => htend0 x i hx hi
  have hball' : ∀ x ∈ D, ∀ i ∈ s, ‖h x i‖ ≤ 2 := fun x hx i hi =>
    le_of_tendsto (htend x hx i hi).norm (Filter.Eventually.of_forall fun n => hball n x hx i hi)
  have hfix : ∀ x ∈ D, ∀ i ∈ s, eigenStep s (fun i => w i x) e (h x) i = h x i := by
    intro x hx i hi
    have t1 : Filter.Tendsto (fun n => Hn (n + 1) x i) Filter.atTop (nhds (h x i)) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2 (htend x hx i hi)
    have t2 : Filter.Tendsto (fun n => Hn (n + 1) x i) Filter.atTop
        (nhds (eigenStep s (fun i => w i x) e (h x) i)) := by
      have a1 := tendsto_perturbationApply (u := fun i => w i x) (e := e) i (htend x hx)
      have a2 := tendsto_perturbationMean (u := fun i => w i x) (e := e) (htend x hx)
      exact (tendsto_const_nhds.add a1).sub ((htend x hx i hi).mul a2)
    exact tendsto_nhds_unique t2 t1
  have hmean : ∀ x ∈ D, ∑ i ∈ s, (w i x : ℍ[ℝ]) * h x i = 1 := by
    intro x hx
    have hu := hw0 x hx
    have hs := hw1 x hx
    set l := perturbationMean s (fun i => w i x) e (h x) with hlmean
    set c := ∑ i ∈ s, (w i x : ℍ[ℝ]) * h x i with hc
    have hln : ‖l‖ ≤ η * 2 := norm_perturbationMean_le hu hs he hη0 (by norm_num) (hball' x hx)
    have e1 : c = 1 + l - c * l := by
      have e0 : c = ∑ i ∈ s, (w i x : ℍ[ℝ]) *
          (1 + perturbationApply s (fun i => w i x) e (h x) i - h x i * l) :=
        Finset.sum_congr rfl fun i hi => by
          conv_lhs => rw [← hfix x hx i hi]
          rfl
      have e00 : ∑ i ∈ s, (w i x : ℍ[ℝ]) * (h x i * l) = c * l := by
        rw [hc, Finset.sum_mul]
        simp only [mul_assoc]
      have e01 : ∑ i ∈ s, (w i x : ℍ[ℝ]) * perturbationApply s (fun i => w i x) e (h x) i = l := rfl
      calc c = _ := e0
        _ = 1 + l - c * l := by
          simp only [mul_sub, mul_add, mul_one, Finset.sum_sub_distrib, Finset.sum_add_distrib]
          rw [sum_coe_eq_one hs, e00, e01]
    have e2 : (c - 1) * (1 + l) = 0 := by
      have : (c - 1) * (1 + l) = c - (1 + l - c * l) - 1 + 1 + l - l := by
        simp only [sub_mul, mul_add, mul_one, one_mul]
        abel
      rw [this, ← e1]
      abel
    have e3 : (1 + l) ≠ 0 := by
      intro h0
      have : l = -1 := by
        have := eq_neg_of_add_eq_zero_right h0
        exact this
      rw [this] at hln
      simp at hln
      linarith
    have e4 := (mul_eq_zero.1 e2).resolve_right e3
    exact sub_eq_zero.1 e4
  refine ⟨h, fun i hi => ?_, hmean, ?_, ?_⟩
  · refine FiniteDiffBound.of_tendsto (us := fun n x => Hn n x i - 1) (fun n => hdec n i hi) ?_
    exact fun x hx => (htend x hx i hi).sub_const 1
  · intro x hx i hi
    have := hfix x hx i hi
    simp only [eigenStep] at this
    calc 1 + perturbationApply s (fun i => w i x) e (h x) i
        = (1 + perturbationApply s (fun i => w i x) e (h x) i -
              h x i * perturbationMean s (fun i => w i x) e (h x)) +
            h x i * perturbationMean s (fun i => w i x) e (h x) := by abel
      _ = h x i + h x i * perturbationMean s (fun i => w i x) e (h x) := by rw [this]
      _ = h x i * (1 + perturbationMean s (fun i => w i x) e (h x)) := by rw [mul_add, mul_one]
  · intro x hx h' hb hm l hlq i hi
    have hu := hw0 x hx
    have hs := hw1 x hx
    have hl1 : l = 1 + perturbationMean s (fun i => w i x) e h' := by
      have e1 : ∑ i ∈ s, (w i x : ℍ[ℝ]) * (1 + perturbationApply s (fun i => w i x) e h' i) =
          1 + perturbationMean s (fun i => w i x) e h' := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib]
        rw [sum_coe_eq_one hs]
        rfl
      have e2 : ∑ i ∈ s, (w i x : ℍ[ℝ]) * (1 + perturbationApply s (fun i => w i x) e h' i) = l := by
        rw [Finset.sum_congr rfl fun i hi => by rw [hlq i hi]]
        simp only [← mul_assoc]
        rw [← Finset.sum_mul, hm, one_mul]
      rw [← e2, e1]
    have hfix' : ∀ i ∈ s, eigenStep s (fun i => w i x) e h' i = h' i := by
      intro i hi
      simp only [eigenStep]
      rw [hlq i hi, hl1]
      simp only [mul_add, mul_one]
      abel
    have hb2 : ∀ i ∈ s, ‖h' i‖ ≤ 2 := by
      intro i hi
      have : ‖h' i‖ ≤ ‖h' i - 1‖ + ‖(1 : ℍ[ℝ])‖ := by
        simpa using norm_add_le (h' i - 1) 1
      have h1 := hb i hi
      simp at this
      linarith
    have hd : ∀ n : ℕ, ∀ i ∈ s, ‖h' i - h x i‖ ≤ 4 * (1 / 2) ^ n := by
      intro n
      induction n with
      | zero =>
        intro i hi
        have h1 := hb2 i hi
        have h2 := hball' x hx i hi
        have := norm_sub_le (h' i) (h x i)
        simp only [pow_zero, mul_one]
        linarith
      | succ n ih =>
        intro i hi
        have := norm_eigenStep_sub_le hu hs he hη0 (by positivity) hb2 (hball' x hx) ih hi
        rw [hfix' i hi, hfix x hx i hi] at this
        refine this.trans ?_
        have h0 : (0 : ℝ) ≤ 4 * (1 / 2) ^ n := by positivity
        have e3 : 4 * (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) * (4 * (1 / 2) ^ n) := by ring
        rw [e3]
        nlinarith
    have hlim : Filter.Tendsto (fun n : ℕ => 4 * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul 4
      simpa using this
    have h0 : ‖h' i - h x i‖ ≤ 0 :=
      ge_of_tendsto' hlim fun n => hd n i hi
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
end NearlyConstantKernel
end YangMills.Construction
end
