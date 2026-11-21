import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.DifferencesInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeFractionalIntegration
namespace StaircaseHomotopy
section Lines
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (w : Lattice4 → Fin 4 → E) (y : Lattice4) (i : Fin 4)
theorem lineSum_zero : lineSum w y i 0 = 0 := by simp [lineSum]
theorem lineSum_add_one (n : ℤ) :
    lineSum w y i (n + 1) = lineSum w y i n + w (y + n • basisVector i) i := by
  unfold lineSum
  rcases le_or_gt 0 n with hn | hn
  · have e1 : Finset.Ico (0 : ℤ) (n + 1) = insert n (Finset.Ico 0 n) := by
      ext r
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have e2 : Finset.Ico (n + 1) (0 : ℤ) = ∅ := by
      ext r
      simp only [Finset.mem_Ico, Finset.notMem_empty, iff_false]
      omega
    have e3 : Finset.Ico n (0 : ℤ) = ∅ := by
      ext r
      simp only [Finset.mem_Ico, Finset.notMem_empty, iff_false]
      omega
    rw [e1, e2, e3, Finset.sum_insert (by simp)]
    simp only [Finset.sum_empty, sub_zero]
    abel
  · have e1 : Finset.Ico n (0 : ℤ) = insert n (Finset.Ico (n + 1) 0) := by
      ext r
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have e2 : Finset.Ico (0 : ℤ) (n + 1) = ∅ := by
      ext r
      simp only [Finset.mem_Ico, Finset.notMem_empty, iff_false]
      omega
    have e3 : Finset.Ico (0 : ℤ) n = ∅ := by
      ext r
      simp only [Finset.mem_Ico, Finset.notMem_empty, iff_false]
      omega
    rw [e1, e2, e3, Finset.sum_insert (by simp)]
    simp only [Finset.sum_empty, zero_sub]
    abel
theorem lineSum_sub_one (n : ℤ) :
    lineSum w y i (n - 1) = lineSum w y i n - w (y + (n - 1) • basisVector i) i := by
  have key := lineSum_add_one w y i (n - 1)
  rw [sub_add_cancel] at key
  rw [key]
  abel
theorem lineSum_add (n m : ℤ) :
    lineSum w y i (n + m) = lineSum w y i n + lineSum w (y + n • basisVector i) i m := by
  induction m using Int.induction_on with
  | zero => simp [lineSum_zero]
  | succ k ih =>
    rw [← add_assoc, lineSum_add_one, ih, lineSum_add_one w (y + n • basisVector i), add_assoc]
    congr 3
    rw [add_smul, add_assoc]
  | pred k ih =>
    have e : n + (-(k : ℤ) - 1) = (n + -(k : ℤ)) - 1 := by ring
    rw [e, lineSum_sub_one, ih, lineSum_sub_one w (y + n • basisVector i), add_sub_assoc]
    congr 3
    rw [add_assoc, ← add_smul]
    congr 2
    ring
theorem lineSum_one : lineSum w y i 1 = w y i := by
  have key := lineSum_add_one w y i 0
  simpa [lineSum_zero] using key
theorem lineSum_latticeDifference (φ : Lattice4 → E) (n : ℤ) :
    lineSum (latticeDifference φ) y i n = φ (y + n • basisVector i) - φ y := by
  induction n using Int.induction_on with
  | zero => simp [lineSum_zero]
  | succ k ih =>
    rw [lineSum_add_one, ih]
    simp only [latticeDifference]
    have hk : y + ((k : ℤ) + 1) • basisVector i = y + (k : ℤ) • basisVector i + basisVector i := by
      rw [add_smul, one_smul, add_assoc]
    rw [hk]
    abel
  | pred k ih =>
    rw [lineSum_sub_one, ih]
    simp only [latticeDifference]
    have hk : y + (-(k : ℤ)) • basisVector i =
        y + (-(k : ℤ) - 1) • basisVector i + basisVector i := by
      rw [add_assoc, ← add_one_zsmul]
      congr 2
      ring
    rw [hk]
    abel
theorem plaquetteCurl_strip (k s : Fin 4) (n : ℤ) :
    w y k + lineSum w (y + basisVector k) s n - lineSum w y s n - w (y + n • basisVector s) k =
      - lineSum (fun z _ => plaquetteCurl w z s k) y s n := by
  induction n using Int.induction_on with
  | zero => simp [lineSum_zero]
  | succ m ih =>
    rw [lineSum_add_one, lineSum_add_one, lineSum_add_one, neg_add, ← ih]
    simp only [plaquetteCurl]
    have e1 : y + basisVector k + (m : ℤ) • basisVector s =
        y + (m : ℤ) • basisVector s + basisVector k := by abel
    have e2 : y + ((m : ℤ) + 1) • basisVector s = y + (m : ℤ) • basisVector s + basisVector s := by
      rw [add_smul, one_smul, add_assoc]
    rw [e1, e2]
    abel
  | pred m ih =>
    rw [lineSum_sub_one, lineSum_sub_one, lineSum_sub_one, neg_sub,
      sub_eq_add_neg _ (lineSum _ _ _ _), add_comm _ (- lineSum _ _ _ _), ← ih]
    simp only [plaquetteCurl]
    have e1 : y + basisVector k + (-(m : ℤ) - 1) • basisVector s =
        y + (-(m : ℤ) - 1) • basisVector s + basisVector k := by
      abel
    have e2 : y + (-(m : ℤ)) • basisVector s =
        y + (-(m : ℤ) - 1) • basisVector s + basisVector s := by
      rw [add_assoc, ← add_one_zsmul]
      congr 2
      ring
    rw [e1, e2]
    abel
theorem plaquetteCurl_strip_of_mem (c : ℤ) (hc : c = 0 ∨ c = 1) (k s : Fin 4) (n : ℤ) :
    c • w y k + lineSum w (y + c • basisVector k) s n - lineSum w y s n -
        c • w (y + n • basisVector s) k =
      - c • lineSum (fun z _ => plaquetteCurl w z s k) y s n := by
  rcases hc with rfl | rfl
  · simp
  · simp only [one_smul, neg_smul]
    exact plaquetteCurl_strip w y k s n
theorem lineSum_segment_ends (ε ε' : ℤ) (h : ε = 0 ∨ ε = 1) (h' : ε' = 0 ∨ ε' = 1) (k : Fin 4)
    (n : ℤ) :
    ε • w y k + lineSum w (y + ε • basisVector k) k (n + ε' - ε) - lineSum w y k n -
      ε' • w (y + n • basisVector k) k = 0 := by
  have h1 : lineSum w y k (n + ε') =
      lineSum w y k ε + lineSum w (y + ε • basisVector k) k (n + ε' - ε) := by
    rw [← lineSum_add]
    congr 1
    ring
  have h2 := lineSum_add w y k n ε'
  have h3 : ∀ (z : Lattice4) (e : ℤ), (e = 0 ∨ e = 1) → lineSum w z k e = e • w z k := by
    intro z e he
    rcases he with rfl | rfl
    · simp [lineSum_zero]
    · simp [lineSum_one]
  rw [h3 _ _ h] at h1
  rw [h3 _ _ h'] at h2
  have h4 : lineSum w (y + ε • basisVector k) k (n + ε' - ε) =
      lineSum w y k n + ε' • w (y + n • basisVector k) k - ε • w y k := by
    rw [← h2, h1]
    abel
  rw [h4]
  abel
end Lines
section Stairs
theorem basisVector_apply (s i : Fin 4) : basisVector s i = if i = s then 1 else 0 := by
  simp [basisVector, Pi.single_apply]
theorem staircasePoint_zero (u v : Lattice4) : staircasePoint u v 0 = u := by
  funext i
  simp [staircasePoint]
theorem staircasePoint_four (u v : Lattice4) : staircasePoint u v 4 = v := by
  funext i
  simp [staircasePoint, i.isLt]
theorem staircasePoint_succ (u v : Lattice4) (s : Fin 4) :
    staircasePoint u v ((s : ℕ) + 1) = staircasePoint u v s + (v s - u s) • basisVector s := by
  funext i
  simp only [staircasePoint, Pi.add_apply, Pi.smul_apply, basisVector_apply, smul_eq_mul]
  by_cases h : i = s
  · subst h
    simp
  · have hne : (i : ℕ) ≠ s := fun e => h (Fin.ext e)
    simp only [h, if_false, mul_zero, add_zero]
    by_cases h2 : (i : ℕ) < s
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]
def stageOffset (k : Fin 4) (ε ε' : ℤ) (s : ℕ) : ℤ := if s ≤ k then ε else ε'
theorem stageOffset_mem (k : Fin 4) (ε ε' : ℤ) (h : ε = 0 ∨ ε = 1) (h' : ε' = 0 ∨ ε' = 1)
    (s : ℕ) : stageOffset k ε ε' s = 0 ∨ stageOffset k ε ε' s = 1 := by
  unfold stageOffset
  split_ifs
  · exact h
  · exact h'
theorem staircasePoint_add_basisVector (u v : Lattice4) (ε ε' : ℤ) (k : Fin 4) (s : ℕ) :
    staircasePoint (u + ε • basisVector k) (v + ε' • basisVector k) s =
      staircasePoint u v s + stageOffset k ε ε' s • basisVector k := by
  funext i
  simp only [staircasePoint, stageOffset, Pi.add_apply, Pi.smul_apply, basisVector_apply,
    smul_eq_mul]
  by_cases h : i = k
  · subst h
    by_cases h2 : (i : ℕ) < s
    · have h3 : ¬ s ≤ (i : ℕ) := by omega
      simp [h2, h3]
    · have h3 : s ≤ (i : ℕ) := by omega
      simp [h2, h3]
  · simp only [h, if_false, mul_zero, add_zero]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (w : Lattice4 → Fin 4 → E)
theorem staircaseSum_strip (ε ε' : ℤ) (h : ε = 0 ∨ ε = 1) (h' : ε' = 0 ∨ ε' = 1) (k : Fin 4)
    (u v : Lattice4) :
    ε • w u k + staircaseSum w (u + ε • basisVector k) (v + ε' • basisVector k) -
        staircaseSum w u v - ε' • w v k =
      ∑ s : Fin 4, if s = k then 0 else
        - stageOffset k ε ε' s •
          lineSum (fun z _ => plaquetteCurl w z s k) (staircasePoint u v s) s (v s - u s) := by
  set S : ℕ → E := fun s => stageOffset k ε ε' s • w (staircasePoint u v s) k with hS
  have A : ∀ s : Fin 4, S s + lineSum w
        (staircasePoint (u + ε • basisVector k) (v + ε' • basisVector k) s) s
        ((v + ε' • basisVector k) s - (u + ε • basisVector k) s) -
        lineSum w (staircasePoint u v s) s (v s - u s) -
        S ((s : ℕ) + 1) = if s = k then 0 else
        - stageOffset k ε ε' s •
          lineSum (fun z _ => plaquetteCurl w z s k) (staircasePoint u v s) s (v s - u s) := by
    intro s
    simp only [hS]
    rw [staircasePoint_add_basisVector, staircasePoint_succ]
    by_cases hs : s = k
    · subst hs
      have e1 : stageOffset s ε ε' s = ε := by simp [stageOffset]
      have e2 : stageOffset s ε ε' ((s : ℕ) + 1) = ε' := by simp [stageOffset]
      have e3 : (v + ε' • basisVector s) s - (u + ε • basisVector s) s = (v s - u s) + ε' - ε := by
        simp only [Pi.add_apply, Pi.smul_apply, basisVector_apply, smul_eq_mul, if_true]
        ring
      rw [e1, e2, e3, if_pos rfl]
      exact lineSum_segment_ends w _ ε ε' h h' s _
    · have hne : (s : ℕ) ≠ k := fun e => hs (Fin.ext e)
      have e2 : stageOffset k ε ε' ((s : ℕ) + 1) = stageOffset k ε ε' s := by
        simp only [stageOffset]
        by_cases h3 : (s : ℕ) ≤ k
        · rw [if_pos h3, if_pos (by omega)]
        · rw [if_neg h3, if_neg (by omega)]
      have e3 : (v + ε' • basisVector k) s - (u + ε • basisVector k) s = v s - u s := by
        simp only [Pi.add_apply, Pi.smul_apply, basisVector_apply, smul_eq_mul, if_neg hs]
        ring
      rw [e2, e3, if_neg hs]
      exact plaquetteCurl_strip_of_mem w _ _ (stageOffset_mem k ε ε' h h' s) k s _
  have e0 : S 0 = ε • w u k := by
    simp only [hS, staircasePoint_zero]
    simp [stageOffset]
  have e4 : S 4 = ε' • w v k := by
    simp only [hS, staircasePoint_four]
    have hk4 : ¬ 4 ≤ (k : ℕ) := by
      have := k.isLt
      omega
    simp [stageOffset, hk4]
  rw [← e0, ← e4, ← Finset.sum_congr rfl fun s _ => A s]
  simp only [staircaseSum, Fin.sum_univ_four]
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [v0, v1, v2, v3]
  abel
theorem staircaseSum_latticeDifference (φ : Lattice4 → E) (u v : Lattice4) :
    staircaseSum (latticeDifference φ) u v = φ v - φ u := by
  simp only [staircaseSum, lineSum_latticeDifference, ← staircasePoint_succ, Fin.sum_univ_four]
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [v0, v1, v2, v3]
  rw [show (0 + 1 : ℕ) = 1 from rfl, show (1 + 1 : ℕ) = 2 from rfl, show (2 + 1 : ℕ) = 3 from rfl,
    show (3 + 1 : ℕ) = 4 from rfl, staircasePoint_zero, staircasePoint_four]
  abel
end Stairs
section Dyadic
def pathOffset (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (k : Fin 4) (m : ℕ) : ℤ :=
  dyadicPathPoint K (x + basisVector k) ω m k - dyadicPathPoint K x ω m k
theorem ediv_sub_cases (A B D : ℤ) (hB : 0 ≤ B) (hBD : B ≤ D) (hD : 0 < D) :
    (A - B) / D = A / D ∨ (A - B) / D = A / D - 1 := by
  have h1 : (A - B) / D ≤ A / D := Int.ediv_le_ediv hD (by omega)
  have h2 : (A - D) / D ≤ (A - B) / D := Int.ediv_le_ediv hD (by omega)
  have h3 : (A - D) / D = A / D - 1 := by
    have hAD : A - D = A + D * (-1) := by ring
    rw [hAD, Int.add_mul_ediv_left _ _ hD.ne']
    ring
  omega
theorem pathOffset_mem (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (k : Fin 4) (m : ℕ)
    (hm : m ≤ K + 1) : pathOffset K x ω k m = 0 ∨ pathOffset K x ω k m = 1 := by
  cases m with
  | zero =>
    right
    simp [pathOffset, dyadicPathPoint, basisVector_apply]
  | succ m =>
    simp only [pathOffset, dyadicPathPoint, Pi.add_apply, basisVector_apply, if_true]
    have hpow : (2 : ℤ) ^ m ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
    have h := ediv_sub_cases (2 ^ m * ((ω k).1 - x k) + (ω k).2) (2 ^ m) (2 ^ K) (by positivity)
      hpow (by positivity)
    have e : (2 : ℤ) ^ m * ((ω k).1 - (x k + 1)) + (ω k).2 =
        2 ^ m * ((ω k).1 - x k) + (ω k).2 - 2 ^ m := by ring
    rw [e]
    rcases h with h | h <;> rw [h] <;> omega
theorem dyadicPathPoint_add_basisVector (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (k : Fin 4)
    (m : ℕ) :
    dyadicPathPoint K (x + basisVector k) ω m =
      dyadicPathPoint K x ω m + pathOffset K x ω k m • basisVector k := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVector_apply]
  by_cases h : i = k
  · subst h
    simp [pathOffset]
  · simp only [h, if_false, mul_zero, add_zero]
    cases m with
    | zero => simp [dyadicPathPoint, basisVector_apply, h]
    | succ m => simp [dyadicPathPoint, basisVector_apply, h]
theorem dyadicPathPoint_last (K : ℕ) (x : Lattice4) (ω : StaircaseSample)
    (ht : ∀ i, 0 ≤ (ω i).2 ∧ (ω i).2 < 2 ^ K) :
    dyadicPathPoint K x ω (K + 1) = fun i => (ω i).1 := by
  funext i
  simp only [dyadicPathPoint]
  have hD : (0 : ℤ) < 2 ^ K := by positivity
  rw [add_comm (2 ^ K * _) _, Int.add_mul_ediv_left _ _ hD.ne',
    Int.ediv_eq_zero_of_lt (ht i).1 (ht i).2]
  ring
theorem pathOffset_last (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (k : Fin 4)
    (ht : ∀ i, 0 ≤ (ω i).2 ∧ (ω i).2 < 2 ^ K) : pathOffset K x ω k (K + 1) = 0 := by
  simp only [pathOffset, dyadicPathPoint_last _ _ _ ht, sub_self]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (w : Lattice4 → Fin 4 → E)
def stageStripSum (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (k : Fin 4) (m : ℕ) : E :=
  ∑ s : Fin 4, if s = k then 0 else
    - stageOffset k (pathOffset K x ω k m) (pathOffset K x ω k (m + 1)) s •
      lineSum (fun z _ => plaquetteCurl w z s k)
        (staircasePoint (dyadicPathPoint K x ω m) (dyadicPathPoint K x ω (m + 1)) s) s
        (dyadicPathPoint K x ω (m + 1) s - dyadicPathPoint K x ω m s)
theorem dyadicPathSum_strip (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (k : Fin 4)
    (ht : ∀ i, 0 ≤ (ω i).2 ∧ (ω i).2 < 2 ^ K) :
    w x k + dyadicPathSum K w (x + basisVector k) ω - dyadicPathSum K w x ω =
      ∑ m ∈ Finset.range (K + 1), stageStripSum w K x ω k m := by
  have hm : ∀ m ∈ Finset.range (K + 1), stageStripSum w K x ω k m =
      (pathOffset K x ω k m • w (dyadicPathPoint K x ω m) k +
        staircaseSum w (dyadicPathPoint K (x + basisVector k) ω m)
          (dyadicPathPoint K (x + basisVector k) ω (m + 1)) -
        staircaseSum w (dyadicPathPoint K x ω m) (dyadicPathPoint K x ω (m + 1)) -
        pathOffset K x ω k (m + 1) • w (dyadicPathPoint K x ω (m + 1)) k) := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [dyadicPathPoint_add_basisVector K x ω k m, dyadicPathPoint_add_basisVector K x ω k (m + 1)]
    exact (staircaseSum_strip w _ _ (pathOffset_mem K x ω k m (by omega))
      (pathOffset_mem K x ω k (m + 1) (by omega)) k _ _).symm
  rw [Finset.sum_congr rfl hm]
  have htel := Finset.sum_range_sub'
    (fun m => pathOffset K x ω k m • w (dyadicPathPoint K x ω m) k) (K + 1)
  have e0 : pathOffset K x ω k 0 = 1 := by simp [pathOffset, dyadicPathPoint, basisVector_apply]
  have ep : dyadicPathPoint K x ω 0 = x := rfl
  rw [pathOffset_last K x ω k ht, zero_smul, e0, one_smul, sub_zero, ep] at htel
  simp only [dyadicPathSum]
  rw [← htel, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  abel
theorem dyadicPathSum_latticeDifference (K : ℕ) (φ : Lattice4 → E) (x : Lattice4)
    (ω : StaircaseSample) (ht : ∀ i, 0 ≤ (ω i).2 ∧ (ω i).2 < 2 ^ K) :
    dyadicPathSum K (latticeDifference φ) x ω = φ (fun i => (ω i).1) - φ x := by
  simp only [dyadicPathSum, staircaseSum_latticeDifference]
  rw [Finset.sum_range_sub (fun m => φ (dyadicPathPoint K x ω m)), dyadicPathPoint_last K x ω ht]
  rfl
end Dyadic
section Coefficients
def lineCoefficient {ι : Type} [DecidableEq ι] (e : ℤ → ι) (n : ℤ) (τ : ι) : ℝ :=
  (∑ r ∈ Finset.Ico (0 : ℤ) n, if τ = e r then (1 : ℝ) else 0) -
    ∑ r ∈ Finset.Ico n (0 : ℤ), if τ = e r then (1 : ℝ) else 0
theorem sum_lineCoefficient_smul {ι E : Type} [DecidableEq ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : ℤ → ι) (n : ℤ) (T : Finset ι) (f : ι → E)
    (h : ∀ r, (r ∈ Finset.Ico (0 : ℤ) n ∨ r ∈ Finset.Ico n (0 : ℤ)) → e r ∈ T) :
    ∑ τ ∈ T, lineCoefficient e n τ • f τ =
      ∑ r ∈ Finset.Ico (0 : ℤ) n, f (e r) - ∑ r ∈ Finset.Ico n (0 : ℤ), f (e r) := by
  simp only [lineCoefficient, sub_smul, Finset.sum_smul, Finset.sum_sub_distrib]
  have key : ∀ R : Finset ℤ, (∀ r ∈ R, e r ∈ T) →
      ∑ τ ∈ T, ∑ r ∈ R, (if τ = e r then (1 : ℝ) else 0) • f τ = ∑ r ∈ R, f (e r) := by
    intro R hR
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' T (e r) f, if_pos (hR r hr)]
  rw [key _ fun r hr => h r (Or.inl hr), key _ fun r hr => h r (Or.inr hr)]
theorem abs_lineCoefficient_le {ι : Type} [DecidableEq ι] (e : ℤ → ι)
    (he : Function.Injective e) (n : ℤ) (τ : ι) (Q : Prop)
    (hQ : ∀ r, (r ∈ Finset.Ico (0 : ℤ) n ∨ r ∈ Finset.Ico n (0 : ℤ)) → τ = e r → Q)
    [Decidable Q] : |lineCoefficient e n τ| ≤ if Q then 1 else 0 := by
  have one : ∀ R : Finset ℤ, ∑ r ∈ R, (if τ = e r then (1 : ℝ) else 0) ≤ 1 := by
    intro R
    rw [Finset.sum_boole]
    have hcard : (R.filter fun r => τ = e r).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      exact he ((Finset.mem_filter.1 ha).2.symm.trans (Finset.mem_filter.1 hb).2)
    exact_mod_cast hcard
  have nn : ∀ R : Finset ℤ, 0 ≤ ∑ r ∈ R, (if τ = e r then (1 : ℝ) else 0) := fun R =>
    Finset.sum_nonneg fun r _ => by split_ifs <;> norm_num
  by_cases hq : Q
  · rw [if_pos hq]
    unfold lineCoefficient
    rcases le_or_gt 0 n with h | h
    · have e3 : Finset.Ico n (0 : ℤ) = ∅ := by
        ext r
        simp only [Finset.mem_Ico, Finset.notMem_empty, iff_false]
        omega
      rw [e3, Finset.sum_empty, sub_zero, abs_of_nonneg (nn _)]
      exact one _
    · have e3 : Finset.Ico (0 : ℤ) n = ∅ := by
        ext r
        simp only [Finset.mem_Ico, Finset.notMem_empty, iff_false]
        omega
      rw [e3, Finset.sum_empty, zero_sub, abs_neg, abs_of_nonneg (nn _)]
      exact one _
  · rw [if_neg hq]
    have z : ∀ R : Finset ℤ, (∀ r ∈ R, τ ≠ e r) →
        ∑ r ∈ R, (if τ = e r then (1 : ℝ) else 0) = 0 :=
      fun R hR => Finset.sum_eq_zero fun r hr => if_neg (hR r hr)
    unfold lineCoefficient
    rw [z _ fun r hr h => hq (hQ r (Or.inl hr) h), z _ fun r hr h => hq (hQ r (Or.inr hr) h)]
    simp
end Coefficients
section Geometry
variable {l : ℕ} {c : Lattice4}
theorem mem_sampleBox_coord {ω : StaircaseSample} (hω : ω ∈ sampleBox l c) (i : Fin 4) :
    c i ≤ (ω i).1 ∧ (ω i).1 < c i + l ∧ 0 ≤ (ω i).2 ∧ (ω i).2 < 2 ^ dyadicDepth l := by
  have hi := (Fintype.mem_piFinset.1 hω) i
  rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico] at hi
  exact ⟨hi.1.1, hi.1.2, hi.2.1, hi.2.2⟩
theorem endpoint_mem_cornerCube {ω : StaircaseSample} (hω : ω ∈ sampleBox l c) :
    (fun i => (ω i).1) ∈ cornerCube l c := by
  refine Fintype.mem_piFinset.2 fun i => ?_
  rw [Finset.mem_Ico]
  exact ⟨(mem_sampleBox_coord hω i).1, (mem_sampleBox_coord hω i).2.1⟩
theorem rounded_fraction_between (K m : ℕ) (hm : m ≤ K) (d t : ℤ) (h0 : 0 ≤ t) (h1 : t < 2 ^ K) :
    min 0 d ≤ (2 ^ m * d + t) / 2 ^ K ∧ (2 ^ m * d + t) / 2 ^ K ≤ max 0 d := by
  have hD : (0 : ℤ) < 2 ^ K := by positivity
  have hM : (0 : ℤ) < 2 ^ m := by positivity
  have hMD : (2 : ℤ) ^ m ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hm
  constructor
  · rcases le_or_gt 0 d with hd | hd
    · rw [min_eq_left hd]
      exact Int.ediv_nonneg (by positivity) hD.le
    · rw [min_eq_right hd.le]
      apply Int.le_ediv_of_mul_le hD
      nlinarith
  · rcases le_or_gt 0 d with hd | hd
    · rw [max_eq_right hd]
      have hlt : (2 ^ m * d + t) / 2 ^ K < d + 1 := by
        apply Int.ediv_lt_of_lt_mul hD
        nlinarith
      omega
    · rw [max_eq_left hd.le]
      have hlt : (2 ^ m * d + t) / 2 ^ K < 1 := by
        apply Int.ediv_lt_of_lt_mul hD
        nlinarith
      omega
theorem dyadicPathPoint_between (K : ℕ) (x : Lattice4) (ω : StaircaseSample)
    (ht : ∀ i, 0 ≤ (ω i).2 ∧ (ω i).2 < 2 ^ K) (m : ℕ) (hm : m ≤ K + 1) (i : Fin 4) :
    min (x i) (ω i).1 ≤ dyadicPathPoint K x ω m i ∧
      dyadicPathPoint K x ω m i ≤ max (x i) (ω i).1 := by
  cases m with
  | zero =>
    simp only [dyadicPathPoint]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  | succ m =>
    simp only [dyadicPathPoint]
    have hb := rounded_fraction_between K m (by omega) ((ω i).1 - x i) (ω i).2 (ht i).1 (ht i).2
    rcases le_total (x i) (ω i).1 with h | h
    · rw [min_eq_left h, max_eq_right h]
      rw [min_eq_left (by omega), max_eq_right (by omega)] at hb
      omega
    · rw [min_eq_right h, max_eq_left h]
      rw [min_eq_right (by omega), max_eq_left (by omega)] at hb
      omega
theorem staircaseLine_between (K : ℕ) (x : Lattice4) (ω : StaircaseSample)
    (ht : ∀ i, 0 ≤ (ω i).2 ∧ (ω i).2 < 2 ^ K) (m : ℕ) (hm : m ≤ K) (s : Fin 4) (r : ℤ)
    (hr : (0 ≤ r ∧ r ≤ dyadicPathPoint K x ω (m + 1) s - dyadicPathPoint K x ω m s) ∨
      (dyadicPathPoint K x ω (m + 1) s - dyadicPathPoint K x ω m s ≤ r ∧ r ≤ 0)) (i : Fin 4) :
    min (x i) (ω i).1 ≤ (staircasePoint (dyadicPathPoint K x ω m)
        (dyadicPathPoint K x ω (m + 1)) s + r • basisVector s) i ∧
      (staircasePoint (dyadicPathPoint K x ω m) (dyadicPathPoint K x ω (m + 1)) s +
        r • basisVector s) i ≤ max (x i) (ω i).1 := by
  have h1 := dyadicPathPoint_between K x ω ht m (by omega) i
  have h2 := dyadicPathPoint_between K x ω ht (m + 1) (by omega) i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVector_apply, staircasePoint]
  by_cases hi : i = s
  · subst hi
    simp only [lt_irrefl, if_false, if_true, mul_one]
    rcases hr with hr | hr <;> constructor <;> omega
  · simp only [hi, if_false, mul_zero, add_zero]
    split_ifs
    · exact h2
    · exact h1
end Geometry
section Counts
theorem dyadicDepth_bounds (l : ℕ) (hl : 1 ≤ l) :
    81 * (l : ℤ) ≤ 2 ^ dyadicDepth l ∧ (2 : ℤ) ^ dyadicDepth l < 162 * l := by
  have h1 : 81 * l ≤ 2 ^ dyadicDepth l := Nat.le_pow_clog (by norm_num) _
  have hx : 1 < 81 * l := by omega
  have h2 : 2 ^ (dyadicDepth l).pred < 81 * l := Nat.pow_pred_clog_lt_self (by norm_num) hx
  have hK : 0 < dyadicDepth l := Nat.clog_pos (by norm_num) (by omega)
  have h3 : 2 ^ dyadicDepth l = 2 * 2 ^ (dyadicDepth l).pred := by
    rw [← pow_succ', Nat.pred_eq_sub_one, Nat.sub_add_cancel hK]
  constructor
  · exact_mod_cast h1
  · have hlt : 2 ^ dyadicDepth l < 162 * l := by omega
    exact_mod_cast hlt
def pathCoordinate (K : ℕ) (xj : ℤ) : ℕ → ℤ × ℤ → ℤ
  | 0, _ => xj
  | g + 1, a => xj + (2 ^ g * (a.1 - xj) + a.2) / 2 ^ K
theorem dyadicPathPoint_apply_eq (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (g : ℕ) (j : Fin 4) :
    dyadicPathPoint K x ω g j = pathCoordinate K (x j) g (ω j) := by
  cases g <;> rfl
theorem card_filter_dyadic_window_le (K g : ℕ) (hg : g ≤ K) (L : ℤ) (Q : Finset ℤ) :
    (Q.filter fun q => L ≤ 2 ^ g * q ∧ 2 ^ g * q < L + 2 ^ K).card ≤ 2 ^ (K - g) := by
  have hM : (0 : ℤ) < 2 ^ g := by positivity
  set L' : ℤ := - ((-L) / 2 ^ g) with hL'
  have hLL : L ≤ 2 ^ g * L' := by
    have hle := Int.mul_ediv_self_le (x := -L) (k := 2 ^ g) hM.ne'
    rw [hL']
    linarith
  have hsub : (Q.filter fun q => L ≤ 2 ^ g * q ∧ 2 ^ g * q < L + 2 ^ K) ⊆
      Finset.Ico L' (L' + 2 ^ (K - g)) := by
    intro q hq
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hq
    rw [Finset.mem_Ico]
    constructor
    · have hq' : -q ≤ (-L) / 2 ^ g := by
        apply Int.le_ediv_of_mul_le hM
        nlinarith
      rw [hL']
      linarith
    · have hD : (2 : ℤ) ^ K = 2 ^ g * 2 ^ (K - g) := by
        rw [← pow_add, Nat.add_sub_cancel' hg]
      have hlt : 2 ^ g * q < 2 ^ g * (L' + 2 ^ (K - g)) := by
        rw [mul_add, ← hD]
        linarith
      exact lt_of_mul_lt_mul_left hlt hM.le
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Ico] at hcard
  have e : (L' + 2 ^ (K - g) - L').toNat = 2 ^ (K - g) := by
    rw [add_sub_cancel_left]
    exact_mod_cast Int.toNat_natCast (2 ^ (K - g))
  rwa [e] at hcard
theorem card_filter_pathCoordinate_le (l : ℕ) (hl : 1 ≤ l) (ci xj zj : ℤ) (g m : ℕ)
    (hg : g ≤ dyadicDepth l + 1) (hmg : m ≤ g) :
    (((Finset.Ico ci (ci + l) ×ˢ Finset.Ico (0 : ℤ) (2 ^ dyadicDepth l)).filter
        fun a => zj = pathCoordinate (dyadicDepth l) xj g a).card : ℝ) ≤
      ((Finset.Ico ci (ci + l) ×ˢ Finset.Ico (0 : ℤ) (2 ^ dyadicDepth l)).card : ℝ) *
        (1296 / 2 ^ m) := by
  set K := dyadicDepth l with hK
  set A := Finset.Ico ci (ci + l) ×ˢ Finset.Ico (0 : ℤ) (2 ^ K) with hA
  cases g with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    have hle : ((A.filter fun a => zj = pathCoordinate K xj 0 a).card : ℝ) ≤ (A.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    norm_num
    linarith
  | succ g =>
    have hgK : g ≤ K := by omega
    have hcardT : (Finset.Ico (0 : ℤ) (2 ^ K)).card = 2 ^ K := by
      rw [Int.card_Ico, sub_zero]
      exact_mod_cast Int.toNat_natCast (2 ^ K)
    have hcardQ : (Finset.Ico ci (ci + l)).card = l := by
      rw [Int.card_Ico]
      simp
    have hA' : (A.card : ℝ) = (l : ℝ) * 2 ^ K := by
      rw [hA, Finset.card_product, hcardT, hcardQ]
      push_cast
      ring
    have hfib : (A.filter fun a => zj = pathCoordinate K xj (g + 1) a).card ≤
        2 ^ K * 2 ^ (K - g) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.Ico (0 : ℤ) (2 ^ K))]
      · calc _ ≤ ∑ t ∈ Finset.Ico (0 : ℤ) (2 ^ K), 2 ^ (K - g) := by
              apply Finset.sum_le_sum
              intro t _
              set cc := zj - xj with hcc
              set L := cc * 2 ^ K - t + 2 ^ g * xj with hL
              have hinj := Finset.card_le_card_of_injOn (s := ((A.filter fun a =>
                  zj = pathCoordinate K xj (g + 1) a).filter fun a => a.2 = t))
                (t := ((Finset.Ico ci (ci + l)).filter fun q =>
                  L ≤ 2 ^ g * q ∧ 2 ^ g * q < L + 2 ^ K)) Prod.fst ?_ ?_
              · exact hinj.trans (card_filter_dyadic_window_le K g hgK L _)
              · intro a ha
                have ha' := Finset.mem_coe.1 ha
                obtain ⟨h1, h2⟩ := Finset.mem_filter.1 ha'
                obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
                refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(Finset.mem_product.1 h3).1, ?_⟩)
                simp only [pathCoordinate] at h4
                have hD : (0 : ℤ) < 2 ^ K := by positivity
                have hdiv : (2 ^ g * (a.1 - xj) + a.2) / 2 ^ K = cc := by
                  rw [hcc]
                  omega
                have e1 := Int.mul_ediv_self_le (x := 2 ^ g * (a.1 - xj) + a.2) (k := 2 ^ K) hD.ne'
                have e2 := Int.lt_mul_ediv_self_add (x := 2 ^ g * (a.1 - xj) + a.2) (k := 2 ^ K) hD
                rw [hdiv] at e1 e2
                rw [h2] at e1 e2
                rw [hL]
                constructor <;> nlinarith
              · intro a ha b hb hab
                have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
                have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
                exact Prod.ext hab (h1.trans h2.symm)
          _ = _ := by
              rw [Finset.sum_const, hcardT, smul_eq_mul]
      · intro a ha
        exact (Finset.mem_product.1 (Finset.mem_filter.1 ha).1).2
    have h1 : ((A.filter fun a => zj = pathCoordinate K xj (g + 1) a).card : ℝ) ≤
        (2 : ℝ) ^ K * 2 ^ (K - g) := by exact_mod_cast hfib
    rw [hA']
    refine h1.trans ?_
    have hfact := (dyadicDepth_bounds l hl).2
    have hfact' : (2 : ℝ) ^ K < 162 * l := by exact_mod_cast hfact
    have hpow : (2 : ℝ) ^ (K - g) * 2 ^ m ≤ 2 * 2 ^ K := by
      have e : (2 : ℝ) ^ (K - g) * 2 ^ (g + 1) = 2 * 2 ^ K := by
        rw [← pow_add, show K - g + (g + 1) = K + 1 by omega, pow_succ]
        ring
      rw [← e]
      gcongr
      norm_num
    have hm2 : (0 : ℝ) < 2 ^ m := by positivity
    have hK2 : (0 : ℝ) < 2 ^ K := by positivity
    rw [show (l : ℝ) * 2 ^ K * (1296 / 2 ^ m) = (2 : ℝ) ^ K * ((l : ℝ) * 1296 / 2 ^ m) by ring]
    apply mul_le_mul_of_nonneg_left _ hK2.le
    rw [le_div_iff₀ hm2]
    nlinarith
end Counts
section Stages
theorem supNorm_le_of_abs_le {v : Lattice4} {R : ℕ} (h : ∀ i, |v i| ≤ (R : ℤ)) : supNorm v ≤ R := by
  simp only [supNorm, Finset.sup_le_iff, Finset.mem_univ, true_imp_iff]
  intro i
  have hi := h i
  rw [Int.abs_eq_natAbs] at hi
  omega
def StageHits (K : ℕ) (x z : Lattice4) (s : Fin 4) (m : ℕ) (ω : StaircaseSample) : Prop :=
  ∀ j, j ≠ s → z j = staircasePoint (dyadicPathPoint K x ω m) (dyadicPathPoint K x ω (m + 1)) s j
open Classical in
theorem card_filter_stageHits_le (l : ℕ) (hl : 1 ≤ l) (c x z : Lattice4) (s : Fin 4) (m : ℕ)
    (hm : m ≤ dyadicDepth l) :
    (((sampleBox l c).filter fun ω => StageHits (dyadicDepth l) x z s m ω).card : ℝ) ≤
      ((sampleBox l c).card : ℝ) * (1296 / 2 ^ m) ^ 3 := by
  set K := dyadicDepth l with hK
  set A : Fin 4 → Finset (ℤ × ℤ) := fun i =>
    Finset.Ico (c i) (c i + l) ×ˢ Finset.Ico (0 : ℤ) (2 ^ K) with hA
  set g : Fin 4 → ℕ := fun j => if (j : ℕ) < s then m + 1 else m with hg
  set B : Fin 4 → Finset (ℤ × ℤ) := fun j =>
    if j = s then A j else (A j).filter fun a => z j = pathCoordinate K (x j) (g j) a with hB
  have hsub : ((sampleBox l c).filter fun ω => StageHits K x z s m ω) ⊆ Fintype.piFinset B := by
    intro ω hω
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hω
    refine Fintype.mem_piFinset.2 fun j => ?_
    have hAj : ω j ∈ A j := (Fintype.mem_piFinset.1 h1) j
    by_cases hj : j = s
    · simp only [hB, if_pos hj]
      exact hAj
    · simp only [hB, if_neg hj]
      refine Finset.mem_filter.2 ⟨hAj, ?_⟩
      rw [h2 j hj]
      simp only [staircasePoint, hg]
      split_ifs <;> exact dyadicPathPoint_apply_eq _ _ _ _ _
  set R : ℝ := 1296 / 2 ^ m with hR
  set f : Fin 4 → ℝ := fun j => if j = s then 1 else R with hf
  have hb : ∀ j, ((B j).card : ℝ) ≤ ((A j).card : ℝ) * f j := by
    intro j
    by_cases hj : j = s
    · simp [hB, hf, hj]
    · simp only [hB, hf, if_neg hj]
      have hgj : g j ≤ K + 1 := by
        simp only [hg]
        split_ifs <;> omega
      have hmg : m ≤ g j := by
        simp only [hg]
        split_ifs <;> omega
      exact card_filter_pathCoordinate_le l hl (c j) (x j) (z j) (g j) m hgj hmg
  have hprod : ∏ j, f j = R ^ 3 := by
    fin_cases s <;> simp [hf, Fin.prod_univ_four] <;> ring
  calc _ ≤ ((Fintype.piFinset B).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = ∏ j, ((B j).card : ℝ) := by rw [Fintype.card_piFinset]; push_cast; rfl
    _ ≤ ∏ j, (((A j).card : ℝ) * f j) :=
        Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _) fun j _ => hb j
    _ = (∏ j, ((A j).card : ℝ)) * ∏ j, f j := Finset.prod_mul_distrib
    _ = _ := by
        rw [hprod]
        congr 1
        have hc : (sampleBox l c).card = ∏ j, (A j).card := by
          simp only [sampleBox, Fintype.card_piFinset, hA, hK]
        rw [hc]
        push_cast
        rfl
theorem geom_sum_le_inv_one_sub (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, r ^ i ≤ 1 / (1 - r) := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.geom_sum_le_inv_one_sub <;> assumption
theorem sum_dyadic_scales_le (ρ n : ℕ) :
    ∑ m ∈ Finset.range n, (if ρ ≤ 2 ^ m then (1 / 8 : ℝ) ^ m else 0) ≤
      2 * (1 / ((max 1 ρ : ℕ) : ℝ) ^ 3) := by
  set ρ' := max 1 ρ with hρ'
  have h1 : 1 ≤ ρ' := le_max_left _ _
  set m1 := Nat.clog 2 ρ' with hm1
  have h2 : ρ' ≤ 2 ^ m1 := Nat.le_pow_clog (by norm_num) _
  have hsub : (Finset.range n).filter (fun m => ρ ≤ 2 ^ m) ⊆ Finset.Ico m1 n := by
    intro m hm
    obtain ⟨h3, h4⟩ := Finset.mem_filter.1 hm
    rw [Finset.mem_Ico]
    refine ⟨Nat.clog_le_of_le_pow ?_, Finset.mem_range.1 h3⟩
    exact max_le Nat.one_le_two_pow h4
  rw [← Finset.sum_filter]
  calc _ ≤ ∑ m ∈ Finset.Ico m1 n, (1 / 8 : ℝ) ^ m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity
    _ = (1 / 8 : ℝ) ^ m1 * ∑ i ∈ Finset.range (n - m1), (1 / 8 : ℝ) ^ i := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_add]
    _ ≤ (1 / 8 : ℝ) ^ m1 * 2 := by
        gcongr
        refine (geom_sum_le_inv_one_sub (1 / 8) (by norm_num) (by norm_num) _).trans ?_
        norm_num
    _ ≤ _ := by
        rw [mul_comm]
        gcongr
        have h8 : (ρ' : ℝ) ^ 3 ≤ 8 ^ m1 := by
          have hρ2 : (ρ' : ℝ) ≤ 2 ^ m1 := by exact_mod_cast h2
          calc (ρ' : ℝ) ^ 3 ≤ ((2 : ℝ) ^ m1) ^ 3 := by gcongr
            _ = 8 ^ m1 := by
                rw [← pow_mul, mul_comm, pow_mul]
                norm_num
        rw [one_div_pow]
        exact one_div_le_one_div_of_le (by positivity) h8
theorem dyadicPathPoint_near (l : ℕ) (hl : 1 ≤ l) (c x : Lattice4)
    (hx : ∀ i, |x i - c i| ≤ 40 * (l : ℤ)) (ω : StaircaseSample) (hω : ω ∈ sampleBox l c)
    (m g : ℕ) (hg : g ≤ m + 1) (i : Fin 4) :
    |dyadicPathPoint (dyadicDepth l) x ω g i - x i| ≤ ((2 ^ m : ℕ) : ℤ) := by
  cases g with
  | zero => simp [dyadicPathPoint]
  | succ g =>
    simp only [dyadicPathPoint, add_sub_cancel_left]
    obtain ⟨a1, a2, a3, a4⟩ := mem_sampleBox_coord hω i
    have hxi := abs_le.1 (hx i)
    have hf := (dyadicDepth_bounds l hl).1
    set D : ℤ := 2 ^ dyadicDepth l with hD
    have hDpos : 0 < D := by positivity
    set M : ℤ := 2 ^ g with hM
    have hMpos : 0 < M := by positivity
    have h1 : (M * ((ω i).1 - x i) + (ω i).2) / D < M + 1 := by
      apply Int.ediv_lt_of_lt_mul hDpos
      nlinarith
    have h2 : -M ≤ (M * ((ω i).1 - x i) + (ω i).2) / D := by
      apply Int.le_ediv_of_mul_le hDpos
      nlinarith
    have hMm : M ≤ ((2 ^ m : ℕ) : ℤ) := by
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [abs_le]
    constructor <;> omega
theorem staircaseLine_near (l : ℕ) (hl : 1 ≤ l) (c x : Lattice4)
    (hx : ∀ i, |x i - c i| ≤ 40 * (l : ℤ)) (ω : StaircaseSample) (hω : ω ∈ sampleBox l c)
    (m : ℕ) (s : Fin 4) (r : ℤ)
    (hr : (0 ≤ r ∧ r ≤ dyadicPathPoint (dyadicDepth l) x ω (m + 1) s -
        dyadicPathPoint (dyadicDepth l) x ω m s) ∨
      (dyadicPathPoint (dyadicDepth l) x ω (m + 1) s - dyadicPathPoint (dyadicDepth l) x ω m s ≤ r ∧
        r ≤ 0)) :
    supNorm (x - (staircasePoint (dyadicPathPoint (dyadicDepth l) x ω m)
      (dyadicPathPoint (dyadicDepth l) x ω (m + 1)) s + r • basisVector s)) ≤ 2 ^ m := by
  apply supNorm_le_of_abs_le
  intro i
  have h1 := abs_le.1 (dyadicPathPoint_near l hl c x hx ω hω m m (by omega) i)
  have h2 := abs_le.1 (dyadicPathPoint_near l hl c x hx ω hω m (m + 1) le_rfl i)
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVector_apply,
    staircasePoint]
  rw [abs_le]
  by_cases hi : i = s
  · subst hi
    simp only [lt_irrefl, if_false, if_true, mul_one]
    rcases hr with hr | hr <;> constructor <;> omega
  · simp only [hi, if_false, mul_zero, add_zero]
    split_ifs <;> constructor <;> omega
end Stages
section Assembly
def stageStart (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (m : ℕ) (s : Fin 4) : Lattice4 :=
  staircasePoint (dyadicPathPoint K x ω m) (dyadicPathPoint K x ω (m + 1)) s
def stageLength (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (m : ℕ) (s : Fin 4) : ℤ :=
  dyadicPathPoint K x ω (m + 1) s - dyadicPathPoint K x ω m s
def stageBond (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (m : ℕ) (s : Fin 4) :
    ℤ → Lattice4 × Fin 4 :=
  fun r => (stageStart K x ω m s + r • basisVector s, s)
def stagePlaquette (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (m : ℕ) (s k : Fin 4) :
    ℤ → Lattice4 × Fin 4 × Fin 4 :=
  fun r => (stageStart K x ω m s + r • basisVector s, s, k)
theorem translate_line_injective (y : Lattice4) (s : Fin 4) :
    Function.Injective fun r : ℤ => y + r • basisVector s := by
  intro r r' h
  have hs := congrFun h s
  simpa [basisVector_apply] using hs
theorem stageBond_injective (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (m : ℕ) (s : Fin 4) :
    Function.Injective (stageBond K x ω m s) := fun _ _ h =>
  translate_line_injective _ s (congrArg Prod.fst h)
theorem stagePlaquette_injective (K : ℕ) (x : Lattice4) (ω : StaircaseSample) (m : ℕ)
    (s k : Fin 4) : Function.Injective (stagePlaquette K x ω m s k) := fun _ _ h =>
  translate_line_injective _ s (congrArg Prod.fst h)
theorem segment_bounds_of_mem_Ico {r n : ℤ}
    (h : r ∈ Finset.Ico (0 : ℤ) n ∨ r ∈ Finset.Ico n (0 : ℤ)) :
    ((0 ≤ r ∧ r ≤ n) ∨ (n ≤ r ∧ r ≤ 0)) ∧
      ((0 ≤ r + 1 ∧ r + 1 ≤ n) ∨ (n ≤ r + 1 ∧ r + 1 ≤ 0)) := by
  rw [Finset.mem_Ico, Finset.mem_Ico] at h
  omega
variable {l : ℕ} {c : Lattice4}
theorem sampleBox_card_pos (l : ℕ) (c : Lattice4) (hl : 1 ≤ l) :
    0 < ((sampleBox l c).card : ℝ) := by
  have hne : (sampleBox l c).Nonempty := by
    refine ⟨fun i => (c i, 0), Fintype.mem_piFinset.2 fun i => ?_⟩
    rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]
    have h2 : (0 : ℤ) < 2 ^ dyadicDepth l := by positivity
    have h3 : (0 : ℤ) < l := by exact_mod_cast hl
    exact ⟨⟨le_rfl, by simpa using h3⟩, le_rfl, h2⟩
  exact_mod_cast Finset.card_pos.2 hne
theorem offsets_of_mem_sampleBox {ω : StaircaseSample} (hω : ω ∈ sampleBox l c) :
    ∀ i, 0 ≤ (ω i).2 ∧ (ω i).2 < 2 ^ dyadicDepth l := fun i =>
  ⟨(mem_sampleBox_coord hω i).2.2.1, (mem_sampleBox_coord hω i).2.2.2⟩
theorem stageLine_mem {P : Finset Lattice4} (hP : IsFilledToward l c P) {x : Lattice4} (hx : x ∈ P)
    {ω : StaircaseSample} (hω : ω ∈ sampleBox l c) {m : ℕ} (hm : m ≤ dyadicDepth l) (s : Fin 4)
    (r : ℤ)
    (hr : (0 ≤ r ∧ r ≤ stageLength (dyadicDepth l) x ω m s) ∨
      (stageLength (dyadicDepth l) x ω m s ≤ r ∧ r ≤ 0)) :
    stageStart (dyadicDepth l) x ω m s + r • basisVector s ∈ P :=
  hP.2.2 x hx _ (endpoint_mem_cornerCube hω) _
    (staircaseLine_between _ x ω (offsets_of_mem_sampleBox hω) m hm s r hr)
theorem stageBond_mem {P : Finset Lattice4} (hP : IsFilledToward l c P) {x : Lattice4} (hx : x ∈ P)
    {ω : StaircaseSample} (hω : ω ∈ sampleBox l c) {m : ℕ} (hm : m ≤ dyadicDepth l) (s : Fin 4)
    (r : ℤ)
    (hr : r ∈ Finset.Ico (0 : ℤ) (stageLength (dyadicDepth l) x ω m s) ∨
      r ∈ Finset.Ico (stageLength (dyadicDepth l) x ω m s) (0 : ℤ)) :
    stageBond (dyadicDepth l) x ω m s r ∈ bondsOf P := by
  obtain ⟨h1, h2⟩ := segment_bounds_of_mem_Ico hr
  have a := stageLine_mem hP hx hω hm s r h1
  have b := stageLine_mem hP hx hω hm s (r + 1) h2
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨a, Finset.mem_univ _⟩, ?_⟩
  simp only [stageBond]
  rwa [add_smul, one_smul, ← add_assoc] at b
theorem stagePlaquette_mem {P : Finset Lattice4} (hP : IsFilledToward l c P) {x : Lattice4}
    (hx : x ∈ P) {k : Fin 4} (hx' : x + basisVector k ∈ P) {ω : StaircaseSample}
    (hω : ω ∈ sampleBox l c) {m : ℕ} (hm : m ≤ dyadicDepth l) (s : Fin 4) (hs : s ≠ k)
    (h1 : stageOffset k (pathOffset (dyadicDepth l) x ω k m)
      (pathOffset (dyadicDepth l) x ω k (m + 1)) s = 1)
    (r : ℤ) (hr : r ∈ Finset.Ico (0 : ℤ) (stageLength (dyadicDepth l) x ω m s) ∨
      r ∈ Finset.Ico (stageLength (dyadicDepth l) x ω m s) (0 : ℤ)) :
    stagePlaquette (dyadicDepth l) x ω m s k r ∈ orientedPlaquettesOf P := by
  obtain ⟨g1, g2⟩ := segment_bounds_of_mem_Ico hr
  set K := dyadicDepth l
  have hstart : stageStart K (x + basisVector k) ω m s = stageStart K x ω m s + basisVector k := by
    simp only [stageStart]
    rw [dyadicPathPoint_add_basisVector K x ω k m, dyadicPathPoint_add_basisVector K x ω k (m + 1),
      staircasePoint_add_basisVector, h1, one_smul]
  have hlen : stageLength K (x + basisVector k) ω m s = stageLength K x ω m s := by
    simp only [stageLength]
    rw [dyadicPathPoint_add_basisVector K x ω k m, dyadicPathPoint_add_basisVector K x ω k (m + 1)]
    simp [basisVector_apply, hs]
  have a := stageLine_mem hP hx hω hm s r g1
  have b := stageLine_mem hP hx hω hm s (r + 1) g2
  have a' := stageLine_mem hP hx' hω hm s r (by rw [hlen]; exact g1)
  have b' := stageLine_mem hP hx' hω hm s (r + 1) (by rw [hlen]; exact g2)
  rw [hstart] at a' b'
  rw [add_smul, one_smul, ← add_assoc] at b b'
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨a, Finset.mem_univ _⟩, hs, b, ?_, ?_⟩
  · simp only [stagePlaquette]
    have e : stageStart K x ω m s + r • basisVector s + basisVector k =
        stageStart K x ω m s + basisVector k + r • basisVector s := by abel
    rwa [e]
  · simp only [stagePlaquette]
    have e : stageStart K x ω m s + r • basisVector s + basisVector s + basisVector k =
        stageStart K x ω m s + basisVector k + r • basisVector s + basisVector s := by abel
    rwa [e]
open Classical in
theorem sum_abs_stage_le (l : ℕ) (hl : 1 ≤ l) (c x z : Lattice4)
    (T : StaircaseSample → ℕ → Fin 4 → ℝ)
    (hT : ∀ ω ∈ sampleBox l c, ∀ m, m ≤ dyadicDepth l → ∀ s, |T ω m s| ≤
      if StageHits (dyadicDepth l) x z s m ω ∧ supNorm (x - z) ≤ 2 ^ m then 1 else 0) :
    1 / ((sampleBox l c).card : ℝ) * ∑ ω ∈ sampleBox l c,
      ∑ m ∈ Finset.range (dyadicDepth l + 1), ∑ s, |T ω m s| ≤
        8 * 1296 ^ 3 * cubicKernel (x - z) := by
  set K := dyadicDepth l
  set n : ℝ := ((sampleBox l c).card : ℝ) with hn
  have hn0 : 0 < n := sampleBox_card_pos l c hl
  set ρ := supNorm (x - z) with hρ
  have hone : ∀ m ∈ Finset.range (K + 1), ∀ s, ∑ ω ∈ sampleBox l c, |T ω m s| ≤
      n * (1296 ^ 3 * if ρ ≤ 2 ^ m then (1 / 8 : ℝ) ^ m else 0) := by
    intro m hm s
    rw [Finset.mem_range] at hm
    by_cases hnear : ρ ≤ 2 ^ m
    · rw [if_pos hnear]
      calc _ ≤ ∑ ω ∈ sampleBox l c, if StageHits K x z s m ω then (1 : ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro ω hω
            refine (hT ω hω m (by omega) s).trans ?_
            simp only [hnear, and_true]
            exact le_rfl
        _ = (((sampleBox l c).filter fun ω => StageHits K x z s m ω).card : ℝ) := by
            rw [Finset.sum_boole]
        _ ≤ n * (1296 / 2 ^ m) ^ 3 := card_filter_stageHits_le l hl c x z s m (by omega)
        _ = _ := by
            congr 1
            rw [div_pow, ← pow_mul, mul_comm m 3, pow_mul, one_div_pow]
            norm_num
            ring
    · rw [if_neg hnear, mul_zero, mul_zero]
      apply Finset.sum_nonpos
      intro ω hω
      have hle := hT ω hω m (by omega) s
      simp only [hnear, and_false, if_false] at hle
      exact hle
  have hswap : ∑ ω ∈ sampleBox l c, ∑ m ∈ Finset.range (K + 1), ∑ s, |T ω m s| =
      ∑ m ∈ Finset.range (K + 1), ∑ s, ∑ ω ∈ sampleBox l c, |T ω m s| := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_comm]
  rw [hswap]
  have hsc := sum_dyadic_scales_le ρ (K + 1)
  calc _ ≤ 1 / n * ∑ m ∈ Finset.range (K + 1), ∑ s : Fin 4,
        n * (1296 ^ 3 * if ρ ≤ 2 ^ m then (1 / 8 : ℝ) ^ m else 0) := by
        gcongr with m hm s
        exact hone m hm s
    _ = 4 * 1296 ^ 3 *
        ∑ m ∈ Finset.range (K + 1), (if ρ ≤ 2 ^ m then (1 / 8 : ℝ) ^ m else 0) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        field_simp
        norm_num
        ring
    _ ≤ 4 * 1296 ^ 3 * (2 * (1 / ((max 1 ρ : ℕ) : ℝ) ^ 3)) := by gcongr
    _ = _ := by
        simp only [cubicKernel, hρ]
        ring
end Assembly
section Kernels
open Classical
def pathKernel (l : ℕ) (c : Lattice4) (P : Finset Lattice4) (x : Lattice4) (b : Lattice4 × Fin 4) :
    ℝ :=
  if x ∈ P then 1 / ((sampleBox l c).card : ℝ) * ∑ ω ∈ sampleBox l c,
    ∑ m ∈ Finset.range (dyadicDepth l + 1), ∑ s : Fin 4,
      lineCoefficient (stageBond (dyadicDepth l) x ω m s) (stageLength (dyadicDepth l) x ω m s) b
  else 0
def stripCoefficient (K : ℕ) (x : Lattice4) (k : Fin 4) (ω : StaircaseSample) (m : ℕ) (s : Fin 4)
    (p : Lattice4 × Fin 4 × Fin 4) : ℝ :=
  if s = k then 0 else
    -(stageOffset k (pathOffset K x ω k m) (pathOffset K x ω k (m + 1)) s : ℝ) *
      lineCoefficient (stagePlaquette K x ω m s k) (stageLength K x ω m s) p
def curlKernel (l : ℕ) (c : Lattice4) (P : Finset Lattice4) (b : Lattice4 × Fin 4)
    (p : Lattice4 × Fin 4 × Fin 4) : ℝ :=
  if b.1 ∈ P then 1 / ((sampleBox l c).card : ℝ) * ∑ ω ∈ sampleBox l c,
    ∑ m ∈ Finset.range (dyadicDepth l + 1), ∑ s : Fin 4,
      stripCoefficient (dyadicDepth l) b.1 b.2 ω m s p
  else 0
theorem cubicKernel_nonneg (v : Lattice4) : 0 ≤ cubicKernel v := by apply _root_.YangMills.Construction.PatchDifferences.cubicKernel_nonneg_apply <;> assumption
theorem abs_triple_sum_le (Ω : Finset StaircaseSample) (M : Finset ℕ)
    (T : StaircaseSample → ℕ → Fin 4 → ℝ) :
    |∑ ω ∈ Ω, ∑ m ∈ M, ∑ s, T ω m s| ≤ ∑ ω ∈ Ω, ∑ m ∈ M, ∑ s, |T ω m s| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  exact Finset.abs_sum_le_sum_abs _ _
theorem abs_pathKernel_le {P : Finset Lattice4} {l : ℕ} {c : Lattice4} (hl : 1 ≤ l)
    (hP : IsFilledToward l c P) (x : Lattice4) (b : Lattice4 × Fin 4) :
    |pathKernel l c P x b| ≤ 8 * 1296 ^ 3 * cubicKernel (x - b.1) := by
  unfold pathKernel
  split_ifs with hx
  · have hn0 := sampleBox_card_pos l c hl
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine (mul_le_mul_of_nonneg_left (abs_triple_sum_le _ _ _) (by positivity)).trans ?_
    apply sum_abs_stage_le l hl c x b.1
    intro ω hω m hm s
    apply abs_lineCoefficient_le _ (stageBond_injective _ _ _ _ _)
    intro r hr hb
    obtain ⟨h1, -⟩ := segment_bounds_of_mem_Ico hr
    have hb1 : b.1 = stageStart (dyadicDepth l) x ω m s + r • basisVector s := congrArg Prod.fst hb
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [hb1]
      simp [stageStart, basisVector_apply, hj]
    · rw [hb1]
      exact staircaseLine_near l hl c x (hP.2.1 x hx) ω hω m s r h1
  · simp only [abs_zero]
    exact mul_nonneg (by norm_num) (cubicKernel_nonneg _)
theorem abs_curlKernel_le {P : Finset Lattice4} {l : ℕ} {c : Lattice4} (hl : 1 ≤ l)
    (hP : IsFilledToward l c P) (b : Lattice4 × Fin 4) (p : Lattice4 × Fin 4 × Fin 4) :
    |curlKernel l c P b p| ≤ 8 * 1296 ^ 3 * cubicKernel (b.1 - p.1) := by
  unfold curlKernel
  split_ifs with hx
  · have hn0 := sampleBox_card_pos l c hl
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine (mul_le_mul_of_nonneg_left (abs_triple_sum_le _ _ _) (by positivity)).trans ?_
    apply sum_abs_stage_le l hl c b.1 p.1
    intro ω hω m hm s
    unfold stripCoefficient
    have hrhs : (0 : ℝ) ≤ if StageHits (dyadicDepth l) b.1 p.1 s m ω ∧
        supNorm (b.1 - p.1) ≤ 2 ^ m then 1 else 0 := by
      split_ifs <;> norm_num
    split_ifs at hrhs ⊢ with h1 h2 h2
    · simp
    · simp
    · rw [abs_mul, abs_neg]
      have hs : |(stageOffset b.2 (pathOffset (dyadicDepth l) b.1 ω b.2 m)
          (pathOffset (dyadicDepth l) b.1 ω b.2 (m + 1)) s : ℝ)| ≤ 1 := by
        rcases stageOffset_mem b.2 _ _ (pathOffset_mem (dyadicDepth l) b.1 ω b.2 m (by omega))
          (pathOffset_mem (dyadicDepth l) b.1 ω b.2 (m + 1) (by omega)) s with h | h <;>
          rw [h] <;> simp
      have hc := abs_lineCoefficient_le (stagePlaquette (dyadicDepth l) b.1 ω m s b.2)
        (stagePlaquette_injective _ _ _ _ _ _) (stageLength (dyadicDepth l) b.1 ω m s) p
        (StageHits (dyadicDepth l) b.1 p.1 s m ω ∧ supNorm (b.1 - p.1) ≤ 2 ^ m) (by
          intro r hr hb
          obtain ⟨g1, -⟩ := segment_bounds_of_mem_Ico hr
          have hb1 : p.1 = stageStart (dyadicDepth l) b.1 ω m s + r • basisVector s :=
            congrArg Prod.fst hb
          refine ⟨?_, ?_⟩
          · intro j hj
            rw [hb1]
            simp [stageStart, basisVector_apply, hj]
          · rw [hb1]
            exact staircaseLine_near l hl c b.1 (hP.2.1 b.1 hx) ω hω m s r g1)
      rw [if_pos h2] at hc
      calc _ ≤ 1 * 1 := mul_le_mul hs hc (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    · rw [abs_mul, abs_neg]
      have hc := abs_lineCoefficient_le (stagePlaquette (dyadicDepth l) b.1 ω m s b.2)
        (stagePlaquette_injective _ _ _ _ _ _) (stageLength (dyadicDepth l) b.1 ω m s) p
        (StageHits (dyadicDepth l) b.1 p.1 s m ω ∧ supNorm (b.1 - p.1) ≤ 2 ^ m) (by
          intro r hr hb
          obtain ⟨g1, -⟩ := segment_bounds_of_mem_Ico hr
          have hb1 : p.1 = stageStart (dyadicDepth l) b.1 ω m s + r • basisVector s :=
            congrArg Prod.fst hb
          refine ⟨?_, ?_⟩
          · intro j hj
            rw [hb1]
            simp [stageStart, basisVector_apply, hj]
          · rw [hb1]
            exact staircaseLine_near l hl c b.1 (hP.2.1 b.1 hx) ω hω m s r g1)
      rw [if_neg h2] at hc
      have h0 : |lineCoefficient (stagePlaquette (dyadicDepth l) b.1 ω m s b.2)
          (stageLength (dyadicDepth l) b.1 ω m s) p| = 0 := le_antisymm hc (abs_nonneg _)
      rw [h0, mul_zero]
  · simp only [abs_zero]
    exact mul_nonneg (by norm_num) (cubicKernel_nonneg _)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem smul_triple_sum_comm {ι : Type} (Ω : Finset StaircaseSample) (M : Finset ℕ)
    (B : Finset ι) (L : StaircaseSample → ℕ → Fin 4 → ι → ℝ) (f : ι → E) (a : ℝ) :
    ∑ b ∈ B, (a * ∑ ω ∈ Ω, ∑ m ∈ M, ∑ s, L ω m s b) • f b =
      a • ∑ ω ∈ Ω, ∑ m ∈ M, ∑ s, ∑ b ∈ B, L ω m s b • f b := by
  simp only [mul_smul, Finset.sum_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
theorem randomPathMean_eq_sum {P : Finset Lattice4} {l : ℕ} {c : Lattice4}
    (hP : IsFilledToward l c P) (w : Lattice4 → Fin 4 → E) (x : Lattice4) (hx : x ∈ P) :
    randomPathMean l c w x = ∑ b ∈ bondsOf P, pathKernel l c P x b • w b.1 b.2 := by
  simp only [pathKernel, if_pos hx]
  rw [smul_triple_sum_comm (sampleBox l c) (Finset.range (dyadicDepth l + 1)) (bondsOf P)
    (fun ω m s b => lineCoefficient (stageBond (dyadicDepth l) x ω m s)
      (stageLength (dyadicDepth l) x ω m s) b)
    (fun b => w b.1 b.2)]
  unfold randomPathMean
  congr 1
  apply Finset.sum_congr rfl
  intro ω hω
  unfold dyadicPathSum
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  unfold staircaseSum
  apply Finset.sum_congr rfl
  intro s _
  rw [sum_lineCoefficient_smul _ _ _ _ fun r hr => stageBond_mem hP hx hω (by omega) s r hr]
  rfl
theorem curl_add_randomPathMean_sub_eq_sum {P : Finset Lattice4} {l : ℕ} {c : Lattice4}
    (hl : 1 ≤ l) (hP : IsFilledToward l c P) (w : Lattice4 → Fin 4 → E) (x : Lattice4) (k : Fin 4)
    (hx : x ∈ P) (hx' : x + basisVector k ∈ P) :
    w x k + (randomPathMean l c w (x + basisVector k) - randomPathMean l c w x) =
      ∑ p ∈ orientedPlaquettesOf P, curlKernel l c P (x, k) p • plaquetteCurl w p.1 p.2.1 p.2.2 := by
  have hn0 := sampleBox_card_pos l c hl
  simp only [curlKernel, if_pos hx]
  rw [smul_triple_sum_comm (sampleBox l c) (Finset.range (dyadicDepth l + 1))
    (orientedPlaquettesOf P)
    (fun ω m s p => stripCoefficient (dyadicDepth l) x k ω m s p)
    (fun p => plaquetteCurl w p.1 p.2.1 p.2.2)]
  have hconst : w x k = (1 / ((sampleBox l c).card : ℝ)) • ∑ ω ∈ sampleBox l c, w x k := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div_mul_cancel hn0.ne',
      one_smul]
  have hleft : w x k + (randomPathMean l c w (x + basisVector k) - randomPathMean l c w x) =
      (1 / ((sampleBox l c).card : ℝ)) • ∑ ω ∈ sampleBox l c,
        (w x k + dyadicPathSum (dyadicDepth l) w (x + basisVector k) ω -
          dyadicPathSum (dyadicDepth l) w x ω) := by
    unfold randomPathMean
    nth_rw 1 [hconst]
    rw [← smul_sub, ← smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 1
    abel
  rw [hleft]
  congr 1
  apply Finset.sum_congr rfl
  intro ω hω
  rw [dyadicPathSum_strip w _ x ω k (offsets_of_mem_sampleBox hω)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  unfold stageStripSum
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s = k
  · simp [stripCoefficient, hs]
  · rw [if_neg hs]
    simp only [stripCoefficient, if_neg hs]
    rcases stageOffset_mem k _ _ (pathOffset_mem (dyadicDepth l) x ω k m (by omega))
      (pathOffset_mem (dyadicDepth l) x ω k (m + 1) (by omega)) s with h | h
    · rw [h]
      simp
    · rw [h]
      simp only [Int.cast_one, neg_mul, one_mul, neg_smul, one_smul, Finset.sum_neg_distrib]
      rw [sum_lineCoefficient_smul _ _ _ (fun p => plaquetteCurl w p.1 p.2.1 p.2.2)
        fun r hr => stagePlaquette_mem hP hx hx' hω (by omega) s hs h r hr]
      rfl
theorem sub_endpointMean_eq {l : ℕ} {c : Lattice4} (hl : 1 ≤ l) (φ : Lattice4 → E) (x : Lattice4) :
    φ x - endpointMean l c φ = - randomPathMean l c (latticeDifference φ) x := by
  have hn0 := sampleBox_card_pos l c hl
  have hconst : φ x = (1 / ((sampleBox l c).card : ℝ)) • ∑ ω ∈ sampleBox l c, φ x := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div_mul_cancel hn0.ne',
      one_smul]
  unfold randomPathMean endpointMean
  nth_rw 1 [hconst]
  rw [← smul_sub, ← smul_neg, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ω hω
  rw [dyadicPathSum_latticeDifference _ φ x ω (offsets_of_mem_sampleBox hω)]
  abel
end Kernels
end StaircaseHomotopy
theorem randomStaircaseHomotopy : randomStaircaseHomotopyStatement := by
  refine ⟨8 * 1296 ^ 3, by norm_num, ?_⟩
  intro l c P hl hP
  refine ⟨StaircaseHomotopy.curlKernel l c P, StaircaseHomotopy.pathKernel l c P,
    fun b p => StaircaseHomotopy.abs_curlKernel_le hl hP b p,
    fun x b => StaircaseHomotopy.abs_pathKernel_le hl hP x b, ?_⟩
  intro E _ _
  exact ⟨fun w x hx => StaircaseHomotopy.randomPathMean_eq_sum hP w x hx,
    fun w x i hx hx' => StaircaseHomotopy.curl_add_randomPathMean_sub_eq_sum hl hP w x i hx hx',
    fun φ x _ => StaircaseHomotopy.sub_endpointMean_eq hl φ x⟩
end LatticeFractionalIntegration
end YangMills.Construction
end
