import YangMills.Construction.ColdChainAtEveryLevel.FractionalIntegrationOnTheLatticeProof
import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormulaProof
import YangMills.Construction.ColdChainAtEveryLevel.NearlyFlatPairingProof
import YangMills.Construction.ColdChainAtEveryLevel.PowerWeightsThroughTheKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFractionalIntegration
namespace PowerWeightKernel
abbrev shellRatio : ℝ := 9 / 16
theorem pow_sum_le_mul_sum_div_pow {ι : Type} (J : Finset ι) (c T : ι → ℝ) (hc : ∀ j ∈ J, 0 < c j)
    (hT : ∀ j ∈ J, 0 ≤ T j) (A : ℝ) (hA : ∑ j ∈ J, c j ≤ A) (a : ℕ) (ha : 1 ≤ a) :
    (∑ j ∈ J, T j) ^ a ≤ A ^ (a - 1) * ∑ j ∈ J, T j ^ a / c j ^ (a - 1) := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty, mul_zero]
    rw [zero_pow (by omega)]
  set W := ∑ j ∈ J, c j with hW
  have hWpos : 0 < W := Finset.sum_pos hc hne
  have hmean := Real.pow_arith_mean_le_arith_mean_pow J (fun j => c j / W)
    (fun j => T j / c j * W) (fun j hj => (div_pos (hc j hj) hWpos).le)
    (by rw [← Finset.sum_div, div_self hWpos.ne'])
    (fun j hj => mul_nonneg (div_nonneg (hT j hj) (hc j hj).le) hWpos.le) a
  have e1 : ∑ j ∈ J, c j / W * (T j / c j * W) = ∑ j ∈ J, T j := by
    apply Finset.sum_congr rfl
    intro j hj
    have := (hc j hj).ne'
    field_simp
  rw [e1] at hmean
  refine hmean.trans ?_
  have e2 : ∀ j ∈ J, c j / W * (T j / c j * W) ^ a = W ^ (a - 1) * (T j ^ a / c j ^ (a - 1)) := by
    intro j hj
    have h1 := (hc j hj).ne'
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h2 := hWpos.ne'
    rw [mul_pow, div_pow, pow_succ W b, pow_succ (c j) b]
    field_simp
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum]
  have hW0 : 0 ≤ ∑ j ∈ J, T j ^ a / c j ^ (a - 1) :=
    Finset.sum_nonneg fun j hj => div_nonneg (pow_nonneg (hT j hj) _) (pow_pos (hc j hj) _).le
  gcongr
theorem geom_sum_shellRatio_le (m : ℕ) : ∑ k ∈ Finset.range m, shellRatio ^ k ≤ 5 / 2 := by
  have : (∑ k ∈ Finset.range m, shellRatio ^ k) * (1 - shellRatio) = 1 - shellRatio ^ m :=
    geom_sum_mul_neg _ _
  have hp : 0 ≤ shellRatio ^ m := by positivity
  norm_num at this ⊢
  nlinarith
theorem sum_shellRatio_pow_dist_le (n i : ℕ) :
    ∑ j ∈ Finset.range n, shellRatio ^ (Nat.dist i j) ≤ 5 := by
  have hsub : Finset.range n ⊆ Finset.range (i + 1) ∪ Finset.Ico (i + 1) n := by
    intro j hj
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    rw [Finset.mem_range] at hj
    omega
  have hdisj : Disjoint (Finset.range (i + 1)) (Finset.Ico (i + 1) n) := by
    rw [Finset.disjoint_left]
    intro j h3 h4
    rw [Finset.mem_range] at h3
    rw [Finset.mem_Ico] at h4
    omega
  have h1 : ∑ j ∈ Finset.range (i + 1), shellRatio ^ (Nat.dist i j) ≤ 5 / 2 := by
    have e : ∑ j ∈ Finset.range (i + 1), shellRatio ^ (Nat.dist i j) =
        ∑ j ∈ Finset.range (i + 1), shellRatio ^ (i + 1 - 1 - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      congr 1
      unfold Nat.dist
      omega
    rw [e, Finset.sum_range_reflect (fun k => shellRatio ^ k) (i + 1)]
    exact geom_sum_shellRatio_le _
  have h2 : ∑ j ∈ Finset.Ico (i + 1) n, shellRatio ^ (Nat.dist i j) ≤ 5 / 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have e : ∀ k ∈ Finset.range (n - (i + 1)),
        shellRatio ^ (Nat.dist i (i + 1 + k)) ≤ shellRatio ^ k := by
      intro k _
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      unfold Nat.dist
      omega
    exact (Finset.sum_le_sum e).trans (geom_sum_shellRatio_le _)
  calc _ ≤ ∑ j ∈ Finset.range (i + 1) ∪ Finset.Ico (i + 1) n, shellRatio ^ (Nat.dist i j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity
    _ = _ + _ := Finset.sum_union hdisj
    _ ≤ 5 := by linarith
theorem sum_pow_le_pow_sum_of_nonneg {ι : Type} (J : Finset ι) (β : ι → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (s : ℕ) (hs : 1 ≤ s) : ∑ j ∈ J, β j ^ s ≤ (∑ j ∈ J, β j) ^ s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [pow_succ (∑ j ∈ J, β j), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [pow_succ, mul_comm, mul_comm _ (β j)]
  apply mul_le_mul_of_nonneg_left _ (hβ j)
  apply pow_le_pow_left₀ (hβ j)
  exact Finset.single_le_sum (fun i _ => hβ i) hj
theorem schur_test_shells {X : Type} (n s : ℕ) (hs : 1 ≤ s) (E : ℕ → Finset X) (T : ℕ → X → ℝ)
    (β : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hT : ∀ j x, 0 ≤ T j x) (hβ : ∀ j, 0 ≤ β j)
    (hM : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, ∑ x ∈ E i, (T j x) ^ (2 * s) ≤
      B * (shellRatio ^ (Nat.dist i j)) ^ (2 * s) * β j ^ s) :
    ∑ i ∈ Finset.range n, ∑ x ∈ E i, (∑ j ∈ Finset.range n, T j x) ^ (2 * s) ≤
      5 ^ (2 * s) * B * (∑ j ∈ Finset.range n, β j) ^ s := by
  set a := 2 * s with ha
  have ha1 : 1 ≤ a := by omega
  have hcpos : ∀ i j : ℕ, 0 < shellRatio ^ (Nat.dist i j) := fun i j => by positivity
  have hrow : ∀ i ∈ Finset.range n, ∑ x ∈ E i, (∑ j ∈ Finset.range n, T j x) ^ a ≤
      5 ^ (a - 1) * (B * ∑ j ∈ Finset.range n, shellRatio ^ (Nat.dist i j) * β j ^ s) := by
    intro i hi
    calc _ ≤ ∑ x ∈ E i, 5 ^ (a - 1) * ∑ j ∈ Finset.range n,
          T j x ^ a / (shellRatio ^ (Nat.dist i j)) ^ (a - 1) := by
          apply Finset.sum_le_sum
          intro x _
          exact pow_sum_le_mul_sum_div_pow _ _ _ (fun j _ => hcpos i j) (fun j _ => hT j x) 5
            (sum_shellRatio_pow_dist_le n i) a ha1
      _ = 5 ^ (a - 1) * ∑ j ∈ Finset.range n, (∑ x ∈ E i, T j x ^ a) /
          (shellRatio ^ (Nat.dist i j)) ^ (a - 1) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_div]
      _ ≤ 5 ^ (a - 1) * ∑ j ∈ Finset.range n,
          (B * (shellRatio ^ (Nat.dist i j)) ^ a * β j ^ s) /
          (shellRatio ^ (Nat.dist i j)) ^ (a - 1) := by
          gcongr with j hj
          exact hM i hi j hj
      _ = _ := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          have h1 := (hcpos i j).ne'
          obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
          rw [hb]
          simp only [Nat.add_sub_cancel]
          rw [pow_succ (shellRatio ^ (Nat.dist i j)) b]
          field_simp
  have hβs : ∀ j, 0 ≤ β j ^ s := fun j => pow_nonneg (hβ j) _
  calc _ ≤ ∑ i ∈ Finset.range n, 5 ^ (a - 1) * (B * ∑ j ∈ Finset.range n,
        shellRatio ^ (Nat.dist i j) * β j ^ s) := Finset.sum_le_sum hrow
    _ = 5 ^ (a - 1) * (B * ∑ j ∈ Finset.range n,
          (∑ i ∈ Finset.range n, shellRatio ^ (Nat.dist i j)) * β j ^ s) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ 5 ^ (a - 1) * (B * ∑ j ∈ Finset.range n, 5 * β j ^ s) := by
        gcongr with j hj
        · exact hβs j
        · have : ∑ i ∈ Finset.range n, shellRatio ^ (Nat.dist i j) =
              ∑ i ∈ Finset.range n, shellRatio ^ (Nat.dist j i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Nat.dist_comm]
          rw [this]
          exact sum_shellRatio_pow_dist_le n j
    _ = 5 ^ (a - 1) * 5 * B * ∑ j ∈ Finset.range n, β j ^ s := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ 5 ^ (a - 1) * 5 * B * (∑ j ∈ Finset.range n, β j) ^ s := by
        gcongr
        exact sum_pow_le_pow_sum_of_nonneg _ _ hβ s hs
    _ = _ := by
        rw [← pow_succ, Nat.sub_add_cancel ha1]
section Geometry
theorem abs_apply_le_supNorm (v : Lattice4) (i : Fin 4) : |v i| ≤ (supNorm v : ℤ) := by
  have h : (v i).natAbs ≤ supNorm v :=
    Finset.le_sup (f := fun i => (v i).natAbs) (Finset.mem_univ i)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h
theorem supNorm_le_of_forall {v : Lattice4} {R : ℕ} (h : ∀ i, |v i| ≤ (R : ℤ)) :
    supNorm v ≤ R := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.StaircaseHomotopy.supNorm_le_of_abs_le <;> assumption
theorem supNorm_add_le (a b : Lattice4) : supNorm (a + b) ≤ supNorm a + supNorm b := by apply _root_.YangMills.Construction.LatticePaths.supNorm_add_le <;> assumption
theorem supNorm_sub_comm (a b : Lattice4) : supNorm (a - b) = supNorm (b - a) := by apply _root_.YangMills.Construction.FlatPairing.supNorm_sub_comm <;> assumption
def cube (x : Lattice4) (R : ℕ) : Finset Lattice4 :=
  Fintype.piFinset fun i => Finset.Icc (x i - R) (x i + R)
theorem mem_cube {x y : Lattice4} {R : ℕ} : y ∈ cube x R ↔ supNorm (y - x) ≤ R := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · intro h
    apply supNorm_le_of_forall
    intro i
    have := h i
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have h2 : (supNorm (y - x) : ℤ) ≤ R := by exact_mod_cast h
    have := abs_le.1 ((abs_apply_le_supNorm (y - x) i).trans h2)
    simp only [Pi.sub_apply] at this
    constructor <;> linarith [this.1, this.2]
theorem card_cube (x : Lattice4) (R : ℕ) : ((cube x R).card : ℝ) = (2 * (R : ℝ) + 1) ^ 4 := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.card_cube <;> assumption
theorem card_le_of_supNorm_sub_le (A : Finset Lattice4) (p : Lattice4) (B : ℕ)
    (h : ∀ x ∈ A, supNorm (x - p) ≤ B) : (A.card : ℝ) ≤ (2 * (B : ℝ) + 1) ^ 4 := by
  rw [← card_cube p B]
  exact_mod_cast Finset.card_le_card fun x hx => mem_cube.2 (h x hx)
theorem cubicKernel_nonneg (v : Lattice4) : 0 ≤ cubicKernel v := by apply _root_.YangMills.Construction.PatchDifferences.cubicKernel_nonneg_apply <;> assumption
theorem cubicKernel_le_of_le (v : Lattice4) (t : ℕ) (ht : 1 ≤ t) (h : t ≤ supNorm v) :
    cubicKernel v ≤ 1 / (t : ℝ) ^ 3 := by
  unfold cubicKernel
  apply one_div_le_one_div_of_le (by positivity)
  have : (t : ℝ) ≤ ((max 1 (supNorm v) : ℕ) : ℝ) := by
    exact_mod_cast h.trans (le_max_right _ _)
  gcongr
theorem sum_cubicKernel_cube_le (ρ : ℕ) :
    ∑ v ∈ cube 0 ρ, cubicKernel v ≤ 1 + 80 * (ρ : ℝ) := by
  induction ρ with
  | zero =>
    have : cube (0 : Lattice4) 0 = {0} := by
      ext v
      rw [mem_cube, Finset.mem_singleton, sub_zero]
      constructor
      · intro h
        funext i
        have := abs_apply_le_supNorm v i
        have h2 : supNorm v = 0 := by omega
        rw [h2] at this
        simpa using this
      · rintro rfl
        simp [supNorm]
    rw [this, Finset.sum_singleton]
    simp [cubicKernel, supNorm]
  | succ ρ ih =>
    have hsub : cube (0 : Lattice4) ρ ⊆ cube 0 (ρ + 1) := by
      intro v hv
      rw [mem_cube] at hv ⊢
      omega
    have hc : (((cube (0 : Lattice4) (ρ + 1)) \ cube 0 ρ).card : ℝ) =
        (2 * ((ρ + 1 : ℕ) : ℝ) + 1) ^ 4 - (2 * (ρ : ℝ) + 1) ^ 4 := by
      rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), card_cube,
        card_cube]
    have hterm : ∀ v ∈ cube (0 : Lattice4) (ρ + 1) \ cube 0 ρ, cubicKernel v ≤
        1 / ((ρ + 1 : ℕ) : ℝ) ^ 3 := by
      intro v hv
      rw [Finset.mem_sdiff, mem_cube, mem_cube, sub_zero] at hv
      apply cubicKernel_le_of_le v (ρ + 1) (by omega)
      omega
    rw [← Finset.sum_sdiff hsub]
    have h1 := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [nsmul_eq_mul, hc] at h1
    have h2 : ((2 * ((ρ + 1 : ℕ) : ℝ) + 1) ^ 4 - (2 * (ρ : ℝ) + 1) ^ 4) *
        (1 / ((ρ + 1 : ℕ) : ℝ) ^ 3) ≤ 80 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      push_cast
      have : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
      nlinarith [sq_nonneg (ρ : ℝ), pow_nonneg this 3, pow_nonneg this 2]
    push_cast at ih h2 h1 ⊢
    linarith
theorem young_sq_le (k : Lattice4 → ℝ) (hk : ∀ v, 0 ≤ k v) (S : Finset Lattice4)
    (hS : ∀ v, v ∉ S → k v = 0) (D E : Finset Lattice4) (g : Lattice4 → ℝ) :
    ∑ x ∈ E, (∑ y ∈ D, k (x - y) * g y) ^ 2 ≤ (∑ v ∈ S, k v) ^ 2 * ∑ y ∈ D, g y ^ 2 := by
  classical
  set A := ∑ v ∈ S, k v with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun v _ => hk v
  have hsum : ∀ (T : Finset Lattice4) (φ : Lattice4 → Lattice4), Function.Injective φ →
      ∑ y ∈ T, k (φ y) ≤ A := by
    intro T φ hφ
    rw [← Finset.sum_image (f := k) (g := φ) (s := T) fun a _ b _ h => hφ h]
    rw [← Finset.sum_filter_ne_zero]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      by_contra hvS
      exact (Finset.mem_filter.1 hv).2 (hS v hvS)
    · exact fun v _ _ => hk v
  have hrow : ∀ x ∈ E, (∑ y ∈ D, k (x - y) * g y) ^ 2 ≤ A * ∑ y ∈ D, k (x - y) * g y ^ 2 := by
    intro x _
    have hc := Finset.sum_mul_sq_le_sq_mul_sq D (fun y => Real.sqrt (k (x - y)))
      (fun y => Real.sqrt (k (x - y)) * g y)
    have e1 : ∀ y, Real.sqrt (k (x - y)) * (Real.sqrt (k (x - y)) * g y) = k (x - y) * g y := by
      intro y
      rw [← mul_assoc, Real.mul_self_sqrt (hk _)]
    have e2 : ∀ y, Real.sqrt (k (x - y)) ^ 2 = k (x - y) := fun y => Real.sq_sqrt (hk _)
    have e3 : ∀ y, (Real.sqrt (k (x - y)) * g y) ^ 2 = k (x - y) * g y ^ 2 := by
      intro y
      rw [mul_pow, e2]
    simp only [e1, e2, e3] at hc
    refine hc.trans ?_
    have hB := hsum D (fun y => x - y) (fun a b h => by simpa using h)
    have h0 : 0 ≤ ∑ y ∈ D, k (x - y) * g y ^ 2 :=
      Finset.sum_nonneg fun y _ => mul_nonneg (hk _) (sq_nonneg _)
    gcongr
  calc _ ≤ ∑ x ∈ E, A * ∑ y ∈ D, k (x - y) * g y ^ 2 := Finset.sum_le_sum hrow
    _ = A * ∑ y ∈ D, (∑ x ∈ E, k (x - y)) * g y ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ A * ∑ y ∈ D, A * g y ^ 2 := by
        gcongr with y _
        exact hsum E (fun x => x - y) (fun a b h => by simpa using h)
    _ = _ := by
        rw [← Finset.mul_sum]
        ring
end Geometry
section Shells
variable (N : ℕ) (p : Lattice4)
def shellIndex (x : Lattice4) : ℕ := Nat.log 2 (clippedRadius N p x)
variable {N}
theorem one_le_clippedRadius (hN : 1 ≤ N) (x : Lattice4) : 1 ≤ clippedRadius N p x :=
  le_min hN (le_max_left _ _)
theorem clippedRadius_le (x : Lattice4) : clippedRadius N p x ≤ N := min_le_left _ _
theorem two_pow_shellIndex_le (hN : 1 ≤ N) (x : Lattice4) :
    2 ^ shellIndex N p x ≤ clippedRadius N p x :=
  Nat.pow_log_le_self 2 (by have := one_le_clippedRadius p hN x; omega)
theorem lt_two_pow_shellIndex_succ (x : Lattice4) :
    clippedRadius N p x < 2 ^ (shellIndex N p x + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) _
theorem supNorm_le_clippedRadius_of_lt (x : Lattice4) (h : clippedRadius N p x < N) :
    supNorm (x - p) ≤ clippedRadius N p x := by
  simp only [clippedRadius, min_def, max_def] at h ⊢
  split_ifs at h ⊢ <;> omega
theorem clippedRadius_le_supNorm_of_one_lt (x : Lattice4) (h : 1 < clippedRadius N p x) :
    clippedRadius N p x ≤ supNorm (x - p) := by
  simp only [clippedRadius, min_def, max_def] at h ⊢
  split_ifs at h ⊢ <;> omega
theorem shellIndex_le_log (x : Lattice4) : shellIndex N p x ≤ Nat.log 2 N :=
  Nat.log_mono_right (clippedRadius_le p x)
theorem supNorm_lt_of_shellIndex_lt_log (hN : 1 ≤ N) (x : Lattice4)
    (h : shellIndex N p x < Nat.log 2 N) :
    supNorm (x - p) < 2 ^ (shellIndex N p x + 1) := by
  have h1 := lt_two_pow_shellIndex_succ (N := N) p x
  have h2 : 2 ^ (shellIndex N p x + 1) ≤ 2 ^ Nat.log 2 N :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have := supNorm_le_clippedRadius_of_lt (N := N) p x (by omega)
  omega
theorem two_pow_le_supNorm_of_shellIndex_add_two_le (hN : 1 ≤ N) (x y : Lattice4)
    (h : shellIndex N p y + 2 ≤ shellIndex N p x) :
    2 ^ (shellIndex N p x - 1) ≤ supNorm (x - y) := by
  set i := shellIndex N p x with hi
  set j := shellIndex N p y with hj
  obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hpi : 2 ^ i = 2 * 2 ^ i' := by rw [hi', pow_succ]; ring
  have h1 : 2 ^ i ≤ clippedRadius N p x := two_pow_shellIndex_le p hN x
  have h2 : clippedRadius N p y < 2 ^ (j + 1) := lt_two_pow_shellIndex_succ p y
  have h3 : 2 ^ (j + 1) ≤ 2 ^ i' := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 1 ≤ 2 ^ i' := Nat.one_le_two_pow
  have h5 := clippedRadius_le (N := N) p x
  have h6 : clippedRadius N p x ≤ supNorm (x - p) := clippedRadius_le_supNorm_of_one_lt p x (by
    have : 2 ≤ 2 ^ i := by rw [hpi]; omega
    omega)
  have h7 : supNorm (y - p) ≤ clippedRadius N p y :=
    supNorm_le_clippedRadius_of_lt p y (by omega)
  have h8 : supNorm (x - p) ≤ supNorm (x - y) + supNorm (y - p) := by
    have : x - p = (x - y) + (y - p) := by abel
    rw [this]
    exact supNorm_add_le _ _
  have : i - 1 = i' := by omega
  rw [this]
  omega
theorem two_rpow_inv_eight_le : (2 : ℝ) ^ (1 / 8 : ℝ) ≤ 9 / 8 := by
  have h : (2 : ℝ) ≤ (9 / 8 : ℝ) ^ (8 : ℕ) := by norm_num
  calc (2 : ℝ) ^ (1 / 8 : ℝ) ≤ ((9 / 8 : ℝ) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) h (by norm_num)
    _ = 9 / 8 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
theorem rpow_neg_le_rpow_inv_eight (t M θ : ℝ) (ht : 0 < t) (hM : 1 ≤ M) (h1 : t ≤ M)
    (h2 : 1 / t ≤ M) (hθ : |θ| ≤ 1 / 8) : t ^ (-θ) ≤ M ^ (1 / 8 : ℝ) := by
  rcases le_total 0 θ with h | h
  · have e : t ^ (-θ) = (1 / t) ^ θ := by
      rw [Real.rpow_neg ht.le, one_div, Real.inv_rpow ht.le]
    rw [e]
    have hθ' : θ ≤ 1 / 8 := (le_abs_self θ).trans hθ
    calc (1 / t) ^ θ ≤ M ^ θ := Real.rpow_le_rpow (by positivity) h2 h
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hM hθ'
  · have hθ' : -θ ≤ 1 / 8 := (neg_le_abs θ).trans hθ
    calc t ^ (-θ) ≤ M ^ (-θ) := Real.rpow_le_rpow ht.le h1 (by linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hM hθ'
theorem radialPowerWeight_pos (hN : 1 ≤ N) (θ : ℝ) (x : Lattice4) :
    0 < radialPowerWeight N p θ x := by
  unfold radialPowerWeight
  have h1 : (0 : ℝ) < clippedRadius N p x := by exact_mod_cast one_le_clippedRadius p hN x
  positivity
theorem radialPowerWeight_le_of_shellIndex (hN : 1 ≤ N) (θ : ℝ) (hθ : |θ| ≤ 1 / 8)
    (x y : Lattice4) :
    radialPowerWeight N p θ x ≤
      (9 / 8) ^ (Nat.dist (shellIndex N p x) (shellIndex N p y) + 1) *
        radialPowerWeight N p θ y := by
  set k := Nat.dist (shellIndex N p x) (shellIndex N p y) with hk
  have hx : (0 : ℝ) < clippedRadius N p x := by exact_mod_cast one_le_clippedRadius p hN x
  have hy : (0 : ℝ) < clippedRadius N p y := by exact_mod_cast one_le_clippedRadius p hN y
  set M : ℝ := 2 ^ (k + 1) with hM
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hxy : (clippedRadius N p x : ℝ) ≤ M * clippedRadius N p y := by
    have h1 : clippedRadius N p x < 2 ^ (shellIndex N p x + 1) := lt_two_pow_shellIndex_succ p x
    have h2 : 2 ^ shellIndex N p y ≤ clippedRadius N p y := two_pow_shellIndex_le p hN y
    have h3 : shellIndex N p x + 1 ≤ (k + 1) + shellIndex N p y := by
      simp only [hk, Nat.dist]
      omega
    have h4 : 2 ^ (shellIndex N p x + 1) ≤ 2 ^ (k + 1) * 2 ^ shellIndex N p y := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) h3
    have : clippedRadius N p x ≤ 2 ^ (k + 1) * clippedRadius N p y :=
      h1.le.trans (h4.trans (Nat.mul_le_mul_left _ h2))
    rw [hM]
    exact_mod_cast this
  have hyx : (clippedRadius N p y : ℝ) ≤ M * clippedRadius N p x := by
    have h1 : clippedRadius N p y < 2 ^ (shellIndex N p y + 1) := lt_two_pow_shellIndex_succ p y
    have h2 : 2 ^ shellIndex N p x ≤ clippedRadius N p x := two_pow_shellIndex_le p hN x
    have h3 : shellIndex N p y + 1 ≤ (k + 1) + shellIndex N p x := by
      simp only [hk, Nat.dist]
      omega
    have h4 : 2 ^ (shellIndex N p y + 1) ≤ 2 ^ (k + 1) * 2 ^ shellIndex N p x := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) h3
    have : clippedRadius N p y ≤ 2 ^ (k + 1) * clippedRadius N p x :=
      h1.le.trans (h4.trans (Nat.mul_le_mul_left _ h2))
    rw [hM]
    exact_mod_cast this
  set t : ℝ := (clippedRadius N p x : ℝ) / clippedRadius N p y with ht
  have htpos : 0 < t := by positivity
  have h1 : t ≤ M := by rw [ht, div_le_iff₀ hy]; exact hxy
  have h2 : 1 / t ≤ M := by
    rw [ht, one_div_div, div_le_iff₀ hx]
    exact hyx
  have hb := rpow_neg_le_rpow_inv_eight t M θ htpos hM1 h1 h2 hθ
  have hMb : M ^ (1 / 8 : ℝ) ≤ (9 / 8) ^ (k + 1) := by
    rw [hM, ← Real.rpow_natCast 2 (k + 1), ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) two_rpow_inv_eight_le _
  have hsplit : ((clippedRadius N p x : ℝ) / N) = t * ((clippedRadius N p y : ℝ) / N) := by
    rw [ht]
    field_simp
  unfold radialPowerWeight
  rw [hsplit, Real.mul_rpow htpos.le (by positivity)]
  gcongr
  exact hb.trans hMb
end Shells
section Estimates
theorem truncatedCubicKernel_nonneg (R N : ℕ) (v : Lattice4) : 0 ≤ truncatedCubicKernel R N v := by
  unfold truncatedCubicKernel
  split_ifs
  · exact cubicKernel_nonneg v
  · exact le_rfl
theorem truncatedCubicKernel_le (R N : ℕ) (v : Lattice4) :
    truncatedCubicKernel R N v ≤ cubicKernel v := by
  unfold truncatedCubicKernel
  split_ifs
  · exact le_rfl
  · exact cubicKernel_nonneg v
theorem supNorm_le_of_truncatedCubicKernel_ne_zero {R N : ℕ} {v : Lattice4}
    (h : truncatedCubicKernel R N v ≠ 0) : supNorm v ≤ R * N := by
  by_contra hc
  exact h (if_neg hc)
variable {N : ℕ} (R : ℕ) (p : Lattice4)
def shellReach (m : ℕ) : ℕ := (R + 2) * 2 ^ (m + 1)
theorem supNorm_le_shellReach_of_lt_log (hN : 1 ≤ N) (w : Lattice4)
    (h : shellIndex N p w < Nat.log 2 N) :
    supNorm (w - p) ≤ shellReach R (shellIndex N p w) := by
  have := supNorm_lt_of_shellIndex_lt_log p hN w h
  unfold shellReach
  nlinarith [Nat.one_le_two_pow (n := shellIndex N p w + 1)]
theorem supNorm_le_shellReach_of_lt (hN : 1 ≤ N) (z w : Lattice4) (hzw : supNorm (z - w) ≤ R * N)
    (hlow : shellIndex N p w < shellIndex N p z) :
    supNorm (z - p) ≤ shellReach R (shellIndex N p z) := by
  have hJ := shellIndex_le_log (N := N) p z
  rcases Nat.lt_or_ge (shellIndex N p z) (Nat.log 2 N) with h | h
  · exact supNorm_le_shellReach_of_lt_log R p hN z h
  · have hz : shellIndex N p z = Nat.log 2 N := le_antisymm hJ h
    have hw := supNorm_lt_of_shellIndex_lt_log p hN w (by omega)
    have h1 : supNorm (z - p) ≤ supNorm (z - w) + supNorm (w - p) := by
      have : z - p = (z - w) + (w - p) := by abel
      rw [this]
      exact supNorm_add_le _ _
    have h2 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h3 : 2 ^ (shellIndex N p w + 1) ≤ 2 ^ (Nat.log 2 N + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : R * N ≤ R * 2 ^ (Nat.log 2 N + 1) := Nat.mul_le_mul_left _ h2.le
    unfold shellReach
    rw [hz]
    nlinarith
theorem card_le_of_shellReach (A : Finset Lattice4) (m : ℕ)
    (h : ∀ x ∈ A, supNorm (x - p) ≤ shellReach R m) :
    (A.card : ℝ) ≤ 16 * (2 * (R : ℝ) + 5) ^ 4 * 16 ^ m := by
  refine (card_le_of_supNorm_sub_le A p _ h).trans ?_
  have e : (2 * ((shellReach R m : ℕ) : ℝ) + 1) ≤ (2 * (R : ℝ) + 5) * 2 ^ (m + 1) := by
    have h1 : (1 : ℝ) ≤ 2 ^ (m + 1) := one_le_pow₀ (by norm_num)
    simp only [shellReach]
    push_cast
    nlinarith
  calc _ ≤ ((2 * (R : ℝ) + 5) * 2 ^ (m + 1)) ^ 4 := by gcongr
    _ = _ := by
        rw [mul_pow, ← pow_mul, mul_comm (m + 1) 4, pow_mul, pow_succ]
        norm_num
        ring
theorem farFactor_le_low (j k : ℕ) :
    (8 / 8 ^ (j + k) : ℝ) ^ 2 * ((9 / 8 : ℝ) ^ (k + 1)) ^ 2 * 16 ^ j ≤
      81 * (1 / 4) ^ (j + k) * (shellRatio ^ k) ^ 2 := by
  have e1 : (8 / 8 ^ (j + k) : ℝ) ^ 2 = 64 * ((1 / 64) ^ j * (1 / 64) ^ k) := by
    rw [div_pow, ← pow_mul, mul_comm (j + k) 2, pow_mul, ← pow_add ((1 / 64 : ℝ)) j k, one_div_pow]
    norm_num
    ring
  have e2 : ((9 / 8 : ℝ) ^ (k + 1)) ^ 2 = (81 / 64) * (81 / 64) ^ k := by
    rw [← pow_mul, mul_comm (k + 1) 2, pow_mul, pow_succ]
    norm_num
    ring
  have e3 : (1 / 64 : ℝ) ^ j * 16 ^ j = (1 / 4) ^ j := by
    rw [← mul_pow]
    norm_num
  have e4 : (shellRatio ^ k) ^ 2 = (81 / 256) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have e5 : ((1 / 64 : ℝ) * (81 / 64)) ^ k ≤ ((1 / 4 : ℝ) * (81 / 256)) ^ k := by
    apply pow_le_pow_left₀ (by norm_num)
    norm_num
  rw [mul_pow, mul_pow] at e5
  rw [e1, e2, e4, pow_add ((1 / 4 : ℝ)) j k]
  calc _ = 81 * ((1 / 64 : ℝ) ^ j * 16 ^ j) * ((1 / 64) ^ k * (81 / 64) ^ k) := by ring
    _ = 81 * (1 / 4) ^ j * ((1 / 64) ^ k * (81 / 64) ^ k) := by rw [e3]
    _ ≤ 81 * (1 / 4) ^ j * ((1 / 4) ^ k * (81 / 256) ^ k) := by gcongr
    _ = _ := by ring
theorem farFactor_le_high (i k : ℕ) :
    (8 / 8 ^ (i + k) : ℝ) ^ 2 * ((9 / 8 : ℝ) ^ (k + 1)) ^ 2 * 16 ^ (i + k) ≤
      81 * (1 / 4) ^ i * (shellRatio ^ k) ^ 2 := by
  have e1 : (8 / 8 ^ (i + k) : ℝ) ^ 2 = 64 * (1 / 64) ^ (i + k) := by
    rw [div_pow, ← pow_mul, mul_comm (i + k) 2, pow_mul, one_div_pow]
    norm_num
    ring
  have e2 : ((9 / 8 : ℝ) ^ (k + 1)) ^ 2 = (81 / 64) * (81 / 64) ^ k := by
    rw [← pow_mul, mul_comm (k + 1) 2, pow_mul, pow_succ]
    norm_num
    ring
  have e3 : (1 / 64 : ℝ) ^ (i + k) * 16 ^ (i + k) = (1 / 4) ^ (i + k) := by
    rw [← mul_pow]
    norm_num
  have e4 : (shellRatio ^ k) ^ 2 = (81 / 256) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have e5 : (1 / 4 : ℝ) ^ k * (81 / 64) ^ k = (81 / 256) ^ k := by
    rw [← mul_pow]
    norm_num
  rw [e1, e2, e4, ← e5]
  calc _ = 81 * ((1 / 64 : ℝ) ^ (i + k) * 16 ^ (i + k)) * (81 / 64) ^ k := by ring
    _ = 81 * (1 / 4) ^ (i + k) * (81 / 64) ^ k := by rw [e3]
    _ ≤ _ := by
        rw [pow_add]
        apply le_of_eq
        ring
theorem truncatedCubicKernel_le_of_far (hN : 1 ≤ N) (x y : Lattice4)
    (h : 2 ≤ Nat.dist (shellIndex N p x) (shellIndex N p y)) :
    truncatedCubicKernel R N (x - y) ≤ 8 / 8 ^ (max (shellIndex N p x) (shellIndex N p y)) := by
  refine (truncatedCubicKernel_le R N _).trans ?_
  have hm : ∃ m, m + 1 = max (shellIndex N p x) (shellIndex N p y) ∧
      2 ^ m ≤ supNorm (x - y) := by
    unfold Nat.dist at h
    rcases Nat.lt_or_ge (shellIndex N p x) (shellIndex N p y) with hlt | hge
    · refine ⟨shellIndex N p y - 1, ?_, ?_⟩
      · rw [max_eq_right hlt.le]
        omega
      · rw [supNorm_sub_comm]
        exact two_pow_le_supNorm_of_shellIndex_add_two_le p hN y x (by omega)
    · refine ⟨shellIndex N p x - 1, ?_, ?_⟩
      · rw [max_eq_left hge]
        omega
      · exact two_pow_le_supNorm_of_shellIndex_add_two_le p hN x y (by omega)
  obtain ⟨m, hm1, hm2⟩ := hm
  rw [← hm1]
  refine (cubicKernel_le_of_le _ (2 ^ m) Nat.one_le_two_pow hm2).trans (le_of_eq ?_)
  push_cast
  rw [← pow_mul, mul_comm m 3, pow_mul, pow_succ]
  norm_num
  field_simp
  ring
end Estimates
section Main
theorem farFactor_le (i j : ℕ) (hk : 2 ≤ Nat.dist i j) :
    (8 / 8 ^ (max i j) : ℝ) ^ 2 * ((9 / 8 : ℝ) ^ (Nat.dist i j + 1)) ^ 2 * 16 ^ j ≤
      81 * (1 / 4) ^ i * (shellRatio ^ (Nat.dist i j)) ^ 2 := by
  rcases Nat.le_total i j with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : Nat.dist i (i + k) = k := by simp [Nat.dist]
    rw [e, max_eq_right h]
    exact farFactor_le_high i k
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : Nat.dist (j + k) j = k := by simp [Nat.dist]
    rw [e, max_eq_left h]
    exact farFactor_le_low j k
variable {N : ℕ} (R : ℕ) (p : Lattice4) (θ : ℝ) (D E : Finset Lattice4) (f : Lattice4 → ℝ)
def shellPart (N : ℕ) (p : Lattice4) (A : Finset Lattice4) (j : ℕ) : Finset Lattice4 :=
  A.filter fun y => shellIndex N p y = j
def shellEnergy (N : ℕ) (p : Lattice4) (θ : ℝ) (D : Finset Lattice4) (f : Lattice4 → ℝ)
    (j : ℕ) : ℝ :=
  ∑ y ∈ shellPart N p D j, (radialPowerWeight N p θ y * f y) ^ 2
def countConstant (R : ℕ) : ℝ := 16 * (2 * (R : ℝ) + 5) ^ 4
theorem countConstant_pos (R : ℕ) : 0 < countConstant R := by
  unfold countConstant
  positivity
theorem supNorm_le_shellReach_of_kernel_ne_zero (hN : 1 ≤ N) (x y : Lattice4)
    (hk : 2 ≤ Nat.dist (shellIndex N p x) (shellIndex N p y))
    (hK : truncatedCubicKernel R N (x - y) ≠ 0) :
    supNorm (x - p) ≤ shellReach R (shellIndex N p x) := by
  have hd := supNorm_le_of_truncatedCubicKernel_ne_zero hK
  unfold Nat.dist at hk
  rcases Nat.lt_or_ge (shellIndex N p x) (shellIndex N p y) with h | h
  · exact supNorm_le_shellReach_of_lt_log R p hN x (lt_of_lt_of_le h (shellIndex_le_log p y))
  · exact supNorm_le_shellReach_of_lt R p hN x y hd (by omega)
theorem weighted_kernel_sum_nonneg (hN : 1 ≤ N) (hf : ∀ y, 0 ≤ f y) (x : Lattice4)
    (A : Finset Lattice4) :
    0 ≤ radialPowerWeight N p θ x * ∑ y ∈ A, truncatedCubicKernel R N (x - y) * f y :=
  mul_nonneg (radialPowerWeight_pos p hN θ x).le
    (Finset.sum_nonneg fun y _ => mul_nonneg (truncatedCubicKernel_nonneg _ _ _) (hf y))
theorem sq_far_shell_le (hN : 1 ≤ N) (hθ : |θ| ≤ 1 / 8) (hf : ∀ y, 0 ≤ f y) (x : Lattice4)
    (j : ℕ) (hk : 2 ≤ Nat.dist (shellIndex N p x) j) :
    (radialPowerWeight N p θ x *
        ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ 2 ≤
      81 * countConstant R * (1 / 4) ^ shellIndex N p x *
        (shellRatio ^ (Nat.dist (shellIndex N p x) j)) ^ 2 * shellEnergy N p θ D f j := by
  set i := shellIndex N p x with hi
  set k := Nat.dist i j with hkk
  set κ : ℝ := 8 / 8 ^ (max i j) with hκ
  set A : ℝ := (9 / 8) ^ (k + 1) with hA
  set g : Lattice4 → ℝ := fun y => radialPowerWeight N p θ y * f y with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => mul_nonneg (radialPowerWeight_pos p hN θ y).le (hf y)
  have hκ0 : 0 ≤ κ := by positivity
  have hA0 : 0 ≤ A := by positivity
  set D' := (shellPart N p D j).filter fun y => supNorm (y - p) ≤ shellReach R j with hD'
  have hterm : ∀ y ∈ shellPart N p D j,
      radialPowerWeight N p θ x * (truncatedCubicKernel R N (x - y) * f y) ≤
      if supNorm (y - p) ≤ shellReach R j then κ * A * g y else 0 := by
    intro y hy
    have hsy : shellIndex N p y = j := (Finset.mem_filter.1 hy).2
    have hdist : Nat.dist (shellIndex N p x) (shellIndex N p y) = k := by rw [hsy]
    by_cases hK : truncatedCubicKernel R N (x - y) = 0
    · rw [hK, zero_mul, mul_zero]
      split_ifs
      · exact mul_nonneg (mul_nonneg hκ0 hA0) (hg0 y)
      · exact le_rfl
    · have hin : supNorm (y - p) ≤ shellReach R j := by
        rw [← hsy]
        apply supNorm_le_shellReach_of_kernel_ne_zero R p hN y x
        · rw [Nat.dist_comm, hdist]
          exact hk
        · intro h0
          apply hK
          have : truncatedCubicKernel R N (x - y) = truncatedCubicKernel R N (y - x) := by
            unfold truncatedCubicKernel cubicKernel
            rw [supNorm_sub_comm]
          rw [this, h0]
      rw [if_pos hin]
      have h1 : radialPowerWeight N p θ x ≤ A * radialPowerWeight N p θ y := by
        have := radialPowerWeight_le_of_shellIndex p hN θ hθ x y
        rwa [hdist] at this
      have h2 : truncatedCubicKernel R N (x - y) ≤ κ := by
        have := truncatedCubicKernel_le_of_far R p hN x y (by rw [hdist]; exact hk)
        rwa [hsy] at this
      have hfy := hf y
      have hK0 := truncatedCubicKernel_nonneg R N (x - y)
      calc _ ≤ (A * radialPowerWeight N p θ y) * (κ * f y) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hfy) (mul_nonneg hK0 hfy)
              (mul_nonneg hA0 (radialPowerWeight_pos p hN θ y).le)
        _ = _ := by simp only [hg]; ring
  have hsum : radialPowerWeight N p θ x *
      ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y ≤
      κ * A * ∑ y ∈ D', g y := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [hD', Finset.sum_filter]
  have hc : (∑ y ∈ D', g y) ^ 2 ≤ countConstant R * 16 ^ j * shellEnergy N p θ D f j := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := D') (f := g)
    have h2 : (D'.card : ℝ) ≤ countConstant R * 16 ^ j :=
      card_le_of_shellReach R p D' j fun y hy => (Finset.mem_filter.1 hy).2
    have h3 : ∑ y ∈ D', g y ^ 2 ≤ shellEnergy N p θ D f j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun y _ _ => sq_nonneg _
    have h4 : 0 ≤ ∑ y ∈ D', g y ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
    have h5 : 0 ≤ countConstant R * 16 ^ j := mul_nonneg (countConstant_pos R).le (by positivity)
    exact h1.trans (mul_le_mul h2 h3 h4 h5)
  have hnum := farFactor_le i j hk
  have hE0 : 0 ≤ shellEnergy N p θ D f j := Finset.sum_nonneg fun y _ => sq_nonneg _
  calc _ ≤ (κ * A * ∑ y ∈ D', g y) ^ 2 :=
        pow_le_pow_left₀ (weighted_kernel_sum_nonneg R p θ f hN hf x _) hsum 2
    _ = κ ^ 2 * A ^ 2 * (∑ y ∈ D', g y) ^ 2 := by ring
    _ ≤ κ ^ 2 * A ^ 2 * (countConstant R * 16 ^ j * shellEnergy N p θ D f j) := by gcongr
    _ = (κ ^ 2 * A ^ 2 * 16 ^ j) * (countConstant R * shellEnergy N p θ D f j) := by ring
    _ ≤ (81 * (1 / 4) ^ i * (shellRatio ^ k) ^ 2) * (countConstant R * shellEnergy N p θ D f j) := by
        apply mul_le_mul_of_nonneg_right hnum (mul_nonneg (countConstant_pos R).le hE0)
    _ = _ := by ring
theorem sum_shellPart_eq_sum_filter_shellReach (hN : 1 ≤ N) (i j : ℕ) (hk : 2 ≤ Nat.dist i j)
    (F : ℝ → Lattice4 → ℝ) (hF : ∀ x, F 0 x = 0) :
    ∑ x ∈ shellPart N p E i,
        F (∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) x =
      ∑ x ∈ (shellPart N p E i).filter (fun x => supNorm (x - p) ≤ shellReach R i),
        F (∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) x := by
  symm
  apply Finset.sum_filter_of_ne
  intro x hx hne
  by_contra hout
  apply hne
  have hzero : ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    have hsy : shellIndex N p y = j := (Finset.mem_filter.1 hy).2
    have hsx : shellIndex N p x = i := (Finset.mem_filter.1 hx).2
    by_cases hK : truncatedCubicKernel R N (x - y) = 0
    · rw [hK, zero_mul]
    · exfalso
      apply hout
      rw [← hsx]
      exact supNorm_le_shellReach_of_kernel_ne_zero R p hN x y (by rw [hsx, hsy]; exact hk) hK
  rw [hzero]
  exact hF x
theorem sum_pow_four_far_shell_le (hN : 1 ≤ N) (hθ : |θ| ≤ 1 / 8) (hf : ∀ y, 0 ≤ f y) (i j : ℕ)
    (hk : 2 ≤ Nat.dist i j) :
    ∑ x ∈ shellPart N p E i,
        (radialPowerWeight N p θ x *
          ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ (2 * 2) ≤
      countConstant R * (81 * countConstant R) ^ 2 * (shellRatio ^ (Nat.dist i j)) ^ (2 * 2) *
        shellEnergy N p θ D f j ^ 2 := by
  rw [sum_shellPart_eq_sum_filter_shellReach R p D E f hN i j hk
    (fun t x => (radialPowerWeight N p θ x * t) ^ (2 * 2)) (fun x => by simp)]
  set X := (shellPart N p E i).filter fun x => supNorm (x - p) ≤ shellReach R i with hX
  set Y : ℝ := 81 * countConstant R * (1 / 4) ^ i * (shellRatio ^ (Nat.dist i j)) ^ 2 *
    shellEnergy N p θ D f j with hY
  have hE0 : 0 ≤ shellEnergy N p θ D f j := Finset.sum_nonneg fun y _ => sq_nonneg _
  have hY0 : 0 ≤ Y := mul_nonneg (by have := countConstant_pos R; positivity) hE0
  have hterm : ∀ x ∈ X, (radialPowerWeight N p θ x *
      ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ (2 * 2) ≤ Y ^ 2 := by
    intro x hx
    have hsx : shellIndex N p x = i := (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).2
    have hQ := sq_far_shell_le R p θ D f hN hθ hf x j (by rw [hsx]; exact hk)
    rw [hsx] at hQ
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hQ 2
  have hcard : (X.card : ℝ) ≤ countConstant R * 16 ^ i :=
    card_le_of_shellReach R p X i fun x hx => (Finset.mem_filter.1 hx).2
  calc _ ≤ (X.card : ℝ) * Y ^ 2 := by
        have := Finset.sum_le_card_nsmul X _ _ hterm
        rwa [nsmul_eq_mul] at this
    _ ≤ (countConstant R * 16 ^ i) * Y ^ 2 := by gcongr
    _ = _ := by
        have e : (16 : ℝ) ^ i * ((1 / 4) ^ i) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm i 2, pow_mul, ← mul_pow]
          norm_num
        have hz : (shellRatio ^ (Nat.dist i j)) ^ (2 * 2) =
            ((shellRatio ^ (Nat.dist i j)) ^ 2) ^ 2 := by
          rw [pow_mul]
        rw [hY, hz]
        calc _ = countConstant R * (81 * countConstant R) ^ 2 *
              ((shellRatio ^ (Nat.dist i j)) ^ 2) ^ 2 *
              shellEnergy N p θ D f j ^ 2 * ((16 : ℝ) ^ i * ((1 / 4) ^ i) ^ 2) := by ring
          _ = _ := by rw [e, mul_one]
theorem sum_sq_div_far_shell_le (hN : 1 ≤ N) (hθ : |θ| ≤ 1 / 8) (hf : ∀ y, 0 ≤ f y) (i j : ℕ)
    (hk : 2 ≤ Nat.dist i j) :
    ∑ x ∈ shellPart N p E i, (radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
        ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ (2 * 1) ≤
      countConstant R * (81 * countConstant R) * (shellRatio ^ (Nat.dist i j)) ^ (2 * 1) *
        shellEnergy N p θ D f j ^ 1 := by
  rw [sum_shellPart_eq_sum_filter_shellReach R p D E f hN i j hk
    (fun t x => (radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) * t) ^ (2 * 1))
    (fun x => by simp)]
  set X := (shellPart N p E i).filter fun x => supNorm (x - p) ≤ shellReach R i with hX
  set Y : ℝ := 81 * countConstant R * (1 / 4) ^ i * (shellRatio ^ (Nat.dist i j)) ^ 2 *
    shellEnergy N p θ D f j with hY
  have hE0 : 0 ≤ shellEnergy N p θ D f j := Finset.sum_nonneg fun y _ => sq_nonneg _
  have hY0 : 0 ≤ Y := mul_nonneg (by have := countConstant_pos R; positivity) hE0
  have hterm : ∀ x ∈ X, (radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
      ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ (2 * 1) ≤
      (1 / 4) ^ i * Y := by
    intro x hx
    have hsx : shellIndex N p x = i := (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).2
    have hQ := sq_far_shell_le R p θ D f hN hθ hf x j (by rw [hsx]; exact hk)
    rw [hsx] at hQ
    have hr : (2 : ℝ) ^ i ≤ (clippedRadius N p x : ℝ) := by
      have := two_pow_shellIndex_le p hN x
      rw [hsx] at this
      exact_mod_cast this
    have hr0 : (0 : ℝ) < (clippedRadius N p x : ℝ) := lt_of_lt_of_le (by positivity) hr
    have e : (radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
        ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ (2 * 1) =
        (1 / (clippedRadius N p x : ℝ) ^ 2) * (radialPowerWeight N p θ x *
          ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ 2 := by
      rw [show (2 * 1 : ℕ) = 2 from rfl, mul_pow, div_pow, mul_pow]
      field_simp
    rw [e]
    have h4 : 1 / (clippedRadius N p x : ℝ) ^ 2 ≤ (1 / 4) ^ i := by
      have : (4 : ℝ) ^ i ≤ (clippedRadius N p x : ℝ) ^ 2 := by
        calc (4 : ℝ) ^ i = ((2 : ℝ) ^ i) ^ 2 := by
              rw [← pow_mul, mul_comm, pow_mul]
              norm_num
          _ ≤ _ := by gcongr
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) this
    exact mul_le_mul h4 hQ (sq_nonneg _) (by positivity)
  have hcard : (X.card : ℝ) ≤ countConstant R * 16 ^ i :=
    card_le_of_shellReach R p X i fun x hx => (Finset.mem_filter.1 hx).2
  calc _ ≤ (X.card : ℝ) * ((1 / 4) ^ i * Y) := by
        have := Finset.sum_le_card_nsmul X _ _ hterm
        rwa [nsmul_eq_mul] at this
    _ ≤ (countConstant R * 16 ^ i) * ((1 / 4) ^ i * Y) := by
        apply mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
        have e : (16 : ℝ) ^ i * ((1 / 4) ^ i * (1 / 4) ^ i) = 1 := by
          rw [← mul_pow, ← mul_pow]
          norm_num
        rw [hY]
        calc _ = countConstant R * (81 * countConstant R) * (shellRatio ^ (Nat.dist i j)) ^ 2 *
              shellEnergy N p θ D f j * ((16 : ℝ) ^ i * ((1 / 4) ^ i * (1 / 4) ^ i)) := by ring
          _ = _ := by rw [e, mul_one, pow_one, mul_one]
end Main
section Near
variable {N : ℕ} (R : ℕ) (p : Lattice4) (θ : ℝ) (D E : Finset Lattice4) (f : Lattice4 → ℝ)
theorem radialPowerWeight_le_of_near (hN : 1 ≤ N) (hθ : |θ| ≤ 1 / 8) (x y : Lattice4)
    (hk : Nat.dist (shellIndex N p x) (shellIndex N p y) ≤ 1) :
    radialPowerWeight N p θ x ≤ (81 / 64) * radialPowerWeight N p θ y := by
  have h1 := radialPowerWeight_le_of_shellIndex p hN θ hθ x y
  have hy := radialPowerWeight_pos p hN θ y
  have h2 : (9 / 8 : ℝ) ^ (Nat.dist (shellIndex N p x) (shellIndex N p y) + 1) ≤ (9 / 8) ^ 2 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  refine h1.trans ?_
  calc _ ≤ (9 / 8 : ℝ) ^ 2 * radialPowerWeight N p θ y := by gcongr
    _ = _ := by norm_num
theorem sum_pow_four_near_shell_le (CH : ℝ)
    (hH : ∀ (D E : Finset Lattice4) (g : Lattice4 → ℝ), (∀ y, 0 ≤ g y) →
      ∑ x ∈ E, (∑ y ∈ D, cubicKernel (x - y) * g y) ^ 4 ≤ CH * (∑ y ∈ D, g y ^ 2) ^ 2)
    (hN : 1 ≤ N) (hθ : |θ| ≤ 1 / 8) (hf : ∀ y, 0 ≤ f y) (i j : ℕ) (hk : Nat.dist i j ≤ 1) :
    ∑ x ∈ shellPart N p E i,
        (radialPowerWeight N p θ x *
          ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ (2 * 2) ≤
      (81 / 64) ^ 4 * CH * shellEnergy N p θ D f j ^ 2 := by
  set g : Lattice4 → ℝ := fun y => radialPowerWeight N p θ y * f y with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => mul_nonneg (radialPowerWeight_pos p hN θ y).le (hf y)
  have hpt : ∀ x ∈ shellPart N p E i, radialPowerWeight N p θ x *
      ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y ≤
      (81 / 64) * ∑ y ∈ shellPart N p D j, cubicKernel (x - y) * g y := by
    intro x hx
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y hy
    have hsx : shellIndex N p x = i := (Finset.mem_filter.1 hx).2
    have hsy : shellIndex N p y = j := (Finset.mem_filter.1 hy).2
    have h1 := radialPowerWeight_le_of_near p θ hN hθ x y (by rw [hsx, hsy]; exact hk)
    have h2 := truncatedCubicKernel_le R N (x - y)
    have h3 := truncatedCubicKernel_nonneg R N (x - y)
    have hfy := hf y
    have hu := radialPowerWeight_pos p hN θ y
    calc _ ≤ ((81 / 64) * radialPowerWeight N p θ y) * (cubicKernel (x - y) * f y) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hfy) (mul_nonneg h3 hfy) (by positivity)
      _ = _ := by simp only [hg]; ring
  calc _ ≤ ∑ x ∈ shellPart N p E i, (81 / 64) ^ 4 *
        (∑ y ∈ shellPart N p D j, cubicKernel (x - y) * g y) ^ 4 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [← mul_pow]
        exact pow_le_pow_left₀ (weighted_kernel_sum_nonneg R p θ f hN hf x _) (hpt x hx) 4
    _ = (81 / 64) ^ 4 * ∑ x ∈ shellPart N p E i,
        (∑ y ∈ shellPart N p D j, cubicKernel (x - y) * g y) ^ 4 := by rw [Finset.mul_sum]
    _ ≤ (81 / 64) ^ 4 * (CH * (∑ y ∈ shellPart N p D j, g y ^ 2) ^ 2) := by
        gcongr
        exact hH _ _ g hg0
    _ = _ := by
        simp only [shellEnergy, hg]
        ring
theorem supNorm_sub_le_of_near (hN : 1 ≤ N) (x y : Lattice4)
    (hk : Nat.dist (shellIndex N p x) (shellIndex N p y) ≤ 1) (hd : supNorm (x - y) ≤ R * N) :
    supNorm (x - y) ≤ (R + 8) * 2 ^ (shellIndex N p x + 2) := by
  set i := shellIndex N p x with hi
  set j := shellIndex N p y with hj
  have hji : j ≤ i + 1 := by
    unfold Nat.dist at hk
    omega
  have hp : 0 < 2 ^ (i + 2) := by positivity
  by_cases h : i < Nat.log 2 N ∧ j < Nat.log 2 N
  · have h1 := supNorm_lt_of_shellIndex_lt_log p hN x h.1
    have h2 := supNorm_lt_of_shellIndex_lt_log p hN y h.2
    have h3 : supNorm (x - y) ≤ supNorm (x - p) + supNorm (y - p) := by
      have : x - y = (x - p) + (p - y) := by abel
      rw [this]
      refine (supNorm_add_le _ _).trans ?_
      rw [supNorm_sub_comm p y]
    have h4 : 2 ^ (j + 1) ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ^ (i + 1) ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  · have hJ : Nat.log 2 N ≤ i + 1 := by
      rw [not_and_or] at h
      omega
    have h2 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h3 : 2 ^ (Nat.log 2 N + 1) ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : R * N ≤ R * 2 ^ (i + 2) := Nat.mul_le_mul_left _ (h2.le.trans h3)
    nlinarith
theorem sum_sq_div_near_shell_le (hN : 1 ≤ N) (hθ : |θ| ≤ 1 / 8) (hf : ∀ y, 0 ≤ f y) (i j : ℕ)
    (hk : Nat.dist i j ≤ 1) :
    ∑ x ∈ shellPart N p E i, (radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
        ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ (2 * 1) ≤
      (81 / 64) ^ 2 * 81 ^ 2 * 16 * ((R : ℝ) + 8) ^ 2 * shellEnergy N p θ D f j ^ 1 := by
  classical
  set g : Lattice4 → ℝ := fun y => radialPowerWeight N p θ y * f y with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => mul_nonneg (radialPowerWeight_pos p hN θ y).le (hf y)
  set ρ : ℕ := (R + 8) * 2 ^ (i + 2) with hρ
  set kt : Lattice4 → ℝ := fun v => if supNorm v ≤ ρ then cubicKernel v else 0 with hkt
  have hkt0 : ∀ v, 0 ≤ kt v := by
    intro v
    simp only [hkt]
    split_ifs
    · exact cubicKernel_nonneg v
    · exact le_rfl
  have hsupp : ∀ v, v ∉ cube 0 ρ → kt v = 0 := by
    intro v hv
    rw [mem_cube, sub_zero] at hv
    exact if_neg hv
  have hA : ∑ v ∈ cube 0 ρ, kt v ≤ 81 * (ρ : ℝ) := by
    have h1 : ∑ v ∈ cube 0 ρ, kt v ≤ ∑ v ∈ cube 0 ρ, cubicKernel v := by
      apply Finset.sum_le_sum
      intro v _
      simp only [hkt]
      split_ifs
      · exact le_rfl
      · exact cubicKernel_nonneg v
    have h2 := sum_cubicKernel_cube_le ρ
    have h3 : (1 : ℝ) ≤ ρ := by
      have : 1 ≤ ρ := by
        rw [hρ]
        have : 1 ≤ 2 ^ (i + 2) := Nat.one_le_two_pow
        nlinarith
      exact_mod_cast this
    linarith
  have hA0 : 0 ≤ ∑ v ∈ cube 0 ρ, kt v := Finset.sum_nonneg fun v _ => hkt0 v
  have hpt : ∀ x ∈ shellPart N p E i, radialPowerWeight N p θ x *
      ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y ≤
      (81 / 64) * ∑ y ∈ shellPart N p D j, kt (x - y) * g y := by
    intro x hx
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y hy
    have hsx : shellIndex N p x = i := (Finset.mem_filter.1 hx).2
    have hsy : shellIndex N p y = j := (Finset.mem_filter.1 hy).2
    have h1 := radialPowerWeight_le_of_near p θ hN hθ x y (by rw [hsx, hsy]; exact hk)
    have h3 := truncatedCubicKernel_nonneg R N (x - y)
    have hfy := hf y
    have hu := radialPowerWeight_pos p hN θ y
    by_cases hK : truncatedCubicKernel R N (x - y) = 0
    · rw [hK, zero_mul, mul_zero]
      exact mul_nonneg (by norm_num) (mul_nonneg (hkt0 _) (hg0 y))
    · have hd := supNorm_le_of_truncatedCubicKernel_ne_zero hK
      have hc := supNorm_sub_le_of_near R p hN x y (by rw [hsx, hsy]; exact hk) hd
      rw [hsx] at hc
      have h2 : truncatedCubicKernel R N (x - y) ≤ kt (x - y) := by
        simp only [hkt]
        rw [if_pos hc]
        exact truncatedCubicKernel_le R N _
      calc _ ≤ ((81 / 64) * radialPowerWeight N p θ y) * (kt (x - y) * f y) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hfy) (mul_nonneg h3 hfy) (by positivity)
        _ = _ := by simp only [hg]; ring
  have hterm : ∀ x ∈ shellPart N p E i, (radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
      ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ (2 * 1) ≤
      (1 / 4) ^ i * (81 / 64) ^ 2 * (∑ y ∈ shellPart N p D j, kt (x - y) * g y) ^ 2 := by
    intro x hx
    have hsx : shellIndex N p x = i := (Finset.mem_filter.1 hx).2
    have hr : (2 : ℝ) ^ i ≤ (clippedRadius N p x : ℝ) := by
      have := two_pow_shellIndex_le p hN x
      rw [hsx] at this
      exact_mod_cast this
    have hr0 : (0 : ℝ) < (clippedRadius N p x : ℝ) := lt_of_lt_of_le (by positivity) hr
    have e : (radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
        ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ (2 * 1) =
        (1 / (clippedRadius N p x : ℝ) ^ 2) * (radialPowerWeight N p θ x *
          ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ 2 := by
      rw [show (2 * 1 : ℕ) = 2 from rfl, mul_pow, div_pow, mul_pow]
      field_simp
    rw [e]
    have h4 : 1 / (clippedRadius N p x : ℝ) ^ 2 ≤ (1 / 4) ^ i := by
      have : (4 : ℝ) ^ i ≤ (clippedRadius N p x : ℝ) ^ 2 := by
        calc (4 : ℝ) ^ i = ((2 : ℝ) ^ i) ^ 2 := by
              rw [← pow_mul, mul_comm, pow_mul]
              norm_num
          _ ≤ _ := by gcongr
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) this
    have h5 := pow_le_pow_left₀ (weighted_kernel_sum_nonneg R p θ f hN hf x _) (hpt x hx) 2
    have h6 : (radialPowerWeight N p θ x *
        ∑ y ∈ shellPart N p D j, truncatedCubicKernel R N (x - y) * f y) ^ 2 ≤
        (81 / 64) ^ 2 * (∑ y ∈ shellPart N p D j, kt (x - y) * g y) ^ 2 := by
      rw [← mul_pow]
      exact h5
    calc _ ≤ (1 / 4) ^ i * ((81 / 64) ^ 2 * (∑ y ∈ shellPart N p D j, kt (x - y) * g y) ^ 2) :=
          mul_le_mul h4 h6 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hyoung := young_sq_le kt hkt0 (cube 0 ρ) hsupp (shellPart N p D j) (shellPart N p E i) g
  calc _ ≤ ∑ x ∈ shellPart N p E i, (1 / 4) ^ i * (81 / 64) ^ 2 *
        (∑ y ∈ shellPart N p D j, kt (x - y) * g y) ^ 2 := Finset.sum_le_sum hterm
    _ = (1 / 4) ^ i * (81 / 64) ^ 2 * ∑ x ∈ shellPart N p E i,
        (∑ y ∈ shellPart N p D j, kt (x - y) * g y) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / 4) ^ i * (81 / 64) ^ 2 * ((81 * (ρ : ℝ)) ^ 2 * shellEnergy N p θ D f j) := by
        gcongr
        refine hyoung.trans ?_
        simp only [shellEnergy, hg]
        gcongr
    _ = _ := by
        have e : (1 / 4 : ℝ) ^ i * ((2 : ℝ) ^ (i + 2)) ^ 2 = 16 := by
          have : ((2 : ℝ) ^ (i + 2)) ^ 2 = 16 * 4 ^ i := by
            have h4 : (4 : ℝ) ^ i = ((2 : ℝ) ^ i) ^ 2 := by
              rw [← pow_mul, mul_comm, pow_mul]
              norm_num
            rw [h4, pow_add]
            ring
          rw [this]
          calc _ = 16 * ((1 / 4 : ℝ) ^ i * 4 ^ i) := by ring
            _ = 16 := by
                rw [← mul_pow]
                norm_num
        simp only [hρ]
        push_cast
        rw [pow_one]
        calc _ = (81 / 64) ^ 2 * 81 ^ 2 * ((R : ℝ) + 8) ^ 2 * shellEnergy N p θ D f j *
              ((1 / 4 : ℝ) ^ i * ((2 : ℝ) ^ (i + 2)) ^ 2) := by ring
          _ = _ := by
              rw [e]
              ring
end Near
end PowerWeightKernel
theorem powerWeightKernelStatement_of_hardyLittlewoodSobolev
    (hH : hardyLittlewoodSobolevStatement) : powerWeightKernelStatement := by
  open PowerWeightKernel in
  obtain ⟨C0, hC0, h0⟩ := hH 2 4 (by norm_num) (by norm_num) (by norm_num)
  have hH4 : ∀ (D E : Finset Lattice4) (g : Lattice4 → ℝ), (∀ y, 0 ≤ g y) →
      ∑ x ∈ E, (∑ y ∈ D, cubicKernel (x - y) * g y) ^ 4 ≤ C0 ^ 4 * (∑ y ∈ D, g y ^ 2) ^ 2 := by
    intro D E g hg
    have h := h0 D E g
    have hI : ∀ x, 0 ≤ ∑ y ∈ D, cubicKernel (x - y) * g y := fun x =>
      Finset.sum_nonneg fun y _ => mul_nonneg (PowerWeightKernel.cubicKernel_nonneg _) (hg y)
    have e1 : ∑ x ∈ E, |∑ y ∈ D, cubicKernel (x - y) * g y| ^ (4 : ℝ) =
        ∑ x ∈ E, (∑ y ∈ D, cubicKernel (x - y) * g y) ^ 4 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_of_nonneg (hI x)]
      exact_mod_cast Real.rpow_natCast _ 4
    have e2 : ∑ y ∈ D, |g y| ^ (2 : ℝ) = ∑ y ∈ D, g y ^ 2 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_of_nonneg (hg y)]
      exact_mod_cast Real.rpow_natCast _ 2
    rw [e1, e2] at h
    set t := ∑ x ∈ E, (∑ y ∈ D, cubicKernel (x - y) * g y) ^ 4 with ht
    set S := ∑ y ∈ D, g y ^ 2 with hS
    have ht0 : 0 ≤ t := Finset.sum_nonneg fun x _ => by positivity
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun y _ => sq_nonneg _
    have h1 : t = (t ^ (1 / 4 : ℝ)) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
      norm_num
    have h2 : (S ^ (1 / 2 : ℝ)) ^ 4 = S ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0, ← Real.rpow_natCast]
      norm_num
    rw [h1]
    calc _ ≤ (C0 * S ^ (1 / 2 : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) h 4
      _ = _ := by rw [mul_pow, h2]
  intro R
  set CH := C0 ^ 4 with hCH
  have hCHpos : 0 < CH := by positivity
  have hcn := PowerWeightKernel.countConstant_pos R
  set B4 : ℝ := PowerWeightKernel.countConstant R * (81 * PowerWeightKernel.countConstant R) ^ 2 +
    (81 / 64) ^ 4 * CH * (16 / 9) ^ 4 with hB4
  set B2 : ℝ := PowerWeightKernel.countConstant R * (81 * PowerWeightKernel.countConstant R) +
    (81 / 64) ^ 2 * 81 ^ 2 * 16 * ((R : ℝ) + 8) ^ 2 * (16 / 9) ^ 2 with hB2
  have hB4pos : 0 < B4 := by positivity
  have hB2pos : 0 < B2 := by positivity
  refine ⟨5 ^ 4 * B4 + 5 ^ 2 * B2, by positivity, ?_⟩
  intro N p θ D E f hN hθ hf
  set n := Nat.log 2 N + 1 with hn
  have hmap : ∀ A : Finset Lattice4, ∀ x ∈ A,
      PowerWeightKernel.shellIndex N p x ∈ Finset.range n := by
    intro A x _
    rw [Finset.mem_range]
    have := PowerWeightKernel.shellIndex_le_log (N := N) p x
    omega
  have hβ : ∀ j, 0 ≤ PowerWeightKernel.shellEnergy N p θ D f j := fun j =>
    Finset.sum_nonneg fun y _ => sq_nonneg _
  have hβsum : ∑ j ∈ Finset.range n, PowerWeightKernel.shellEnergy N p θ D f j =
      ∑ y ∈ D, (radialPowerWeight N p θ y * f y) ^ 2 :=
    Finset.sum_fiberwise_of_maps_to (hmap D) _
  set Sg := ∑ y ∈ D, (radialPowerWeight N p θ y * f y) ^ 2 with hSg
  have hsplit : ∀ x, ∑ y ∈ D, truncatedCubicKernel R N (x - y) * f y = ∑ j ∈ Finset.range n,
      ∑ y ∈ PowerWeightKernel.shellPart N p D j, truncatedCubicKernel R N (x - y) * f y :=
    fun x => (Finset.sum_fiberwise_of_maps_to (hmap D) _).symm
  have hzt : ∀ (k a : ℕ), k ≤ 1 →
      1 ≤ (16 / 9 : ℝ) ^ a * (PowerWeightKernel.shellRatio ^ k) ^ a := by
    intro k a hk
    rw [← mul_pow]
    apply one_le_pow₀
    interval_cases k <;> norm_num [PowerWeightKernel.shellRatio]
  constructor
  · have hS := PowerWeightKernel.schur_test_shells n 2 (by norm_num)
      (PowerWeightKernel.shellPart N p E)
      (fun j x => radialPowerWeight N p θ x *
        ∑ y ∈ PowerWeightKernel.shellPart N p D j, truncatedCubicKernel R N (x - y) * f y)
      (PowerWeightKernel.shellEnergy N p θ D f) B4 hB4pos.le
      (fun j x => PowerWeightKernel.weighted_kernel_sum_nonneg R p θ f hN hf x _) hβ (by
        intro i _ j _
        rcases Nat.lt_or_ge (Nat.dist i j) 2 with hk | hk
        · have h1 := PowerWeightKernel.sum_pow_four_near_shell_le R p θ D E f CH hH4 hN hθ hf i j
            (by omega)
          have h2 := hzt (Nat.dist i j) (2 * 2) (by omega)
          have hE := pow_nonneg (hβ j) 2
          refine h1.trans ?_
          have hA : 0 ≤ (81 / 64 : ℝ) ^ 4 * CH := by positivity
          have h3 : (81 / 64 : ℝ) ^ 4 * CH ≤
              B4 * (PowerWeightKernel.shellRatio ^ (Nat.dist i j)) ^ (2 * 2) := by
            have hz : 0 ≤ (PowerWeightKernel.shellRatio ^ (Nat.dist i j)) ^ (2 * 2) := by
              positivity
            have h4 : (81 / 64 : ℝ) ^ 4 * CH * (16 / 9) ^ 4 ≤ B4 := by
              rw [hB4]
              have : 0 ≤ PowerWeightKernel.countConstant R *
                  (81 * PowerWeightKernel.countConstant R) ^ 2 := by positivity
              linarith
            calc _ = (81 / 64 : ℝ) ^ 4 * CH * 1 := by ring
              _ ≤ (81 / 64 : ℝ) ^ 4 * CH * ((16 / 9 : ℝ) ^ (2 * 2) *
                  (PowerWeightKernel.shellRatio ^ (Nat.dist i j)) ^ (2 * 2)) := by gcongr
              _ = ((81 / 64 : ℝ) ^ 4 * CH * (16 / 9) ^ 4) *
                  (PowerWeightKernel.shellRatio ^ (Nat.dist i j)) ^ (2 * 2) := by ring
              _ ≤ _ := by gcongr
          gcongr
        · have h1 := PowerWeightKernel.sum_pow_four_far_shell_le R p θ D E f hN hθ hf i j hk
          refine h1.trans ?_
          have hE := pow_nonneg (hβ j) 2
          have hz : 0 ≤ (PowerWeightKernel.shellRatio ^ (Nat.dist i j)) ^ (2 * 2) := by
            positivity
          have h4 : PowerWeightKernel.countConstant R *
              (81 * PowerWeightKernel.countConstant R) ^ 2 ≤ B4 := by
            rw [hB4]
            have : 0 ≤ (81 / 64 : ℝ) ^ 4 * CH * (16 / 9) ^ 4 := by positivity
            linarith
          gcongr)
    rw [hβsum] at hS
    have hfib : ∑ x ∈ E,
        (radialPowerWeight N p θ x * ∑ y ∈ D, truncatedCubicKernel R N (x - y) * f y) ^ 4 =
        ∑ i ∈ Finset.range n, ∑ x ∈ PowerWeightKernel.shellPart N p E i,
          (∑ j ∈ Finset.range n, radialPowerWeight N p θ x *
            ∑ y ∈ PowerWeightKernel.shellPart N p D j,
              truncatedCubicKernel R N (x - y) * f y) ^ (2 * 2) := by
      rw [← Finset.sum_fiberwise_of_maps_to (hmap E)]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      rw [hsplit x, Finset.mul_sum]
    rw [hfib]
    refine hS.trans ?_
    have h2 : 0 ≤ 5 ^ 2 * B2 * Sg ^ 2 := by positivity
    have h3 : (5 ^ 4 * B4 + 5 ^ 2 * B2) * Sg ^ 2 =
        5 ^ (2 * 2) * B4 * Sg ^ 2 + 5 ^ 2 * B2 * Sg ^ 2 := by
      ring
    linarith
  · have hT : ∀ j x, 0 ≤ radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
        ∑ y ∈ PowerWeightKernel.shellPart N p D j, truncatedCubicKernel R N (x - y) * f y := by
      intro j x
      have hr : (0 : ℝ) < (clippedRadius N p x : ℝ) := by
        exact_mod_cast PowerWeightKernel.one_le_clippedRadius p hN x
      have hu := PowerWeightKernel.radialPowerWeight_pos p hN θ x
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ =>
        mul_nonneg (PowerWeightKernel.truncatedCubicKernel_nonneg _ _ _) (hf y))
    have hS := PowerWeightKernel.schur_test_shells n 1 le_rfl
      (PowerWeightKernel.shellPart N p E)
      (fun j x => radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
        ∑ y ∈ PowerWeightKernel.shellPart N p D j, truncatedCubicKernel R N (x - y) * f y)
      (PowerWeightKernel.shellEnergy N p θ D f) B2 hB2pos.le hT hβ (by
        intro i _ j _
        rcases Nat.lt_or_ge (Nat.dist i j) 2 with hk | hk
        · have h1 := PowerWeightKernel.sum_sq_div_near_shell_le R p θ D E f hN hθ hf i j
            (by omega)
          have h2 := hzt (Nat.dist i j) (2 * 1) (by omega)
          have hE := pow_nonneg (hβ j) 1
          refine h1.trans ?_
          set A : ℝ := (81 / 64) ^ 2 * 81 ^ 2 * 16 * ((R : ℝ) + 8) ^ 2 with hA
          have h3 : A ≤ B2 * (PowerWeightKernel.shellRatio ^ (Nat.dist i j)) ^ (2 * 1) := by
            have hz : 0 ≤ (PowerWeightKernel.shellRatio ^ (Nat.dist i j)) ^ (2 * 1) := by
              positivity
            have h4 : A * (16 / 9) ^ 2 ≤ B2 := by
              rw [hB2]
              have : 0 ≤ PowerWeightKernel.countConstant R *
                  (81 * PowerWeightKernel.countConstant R) := by positivity
              linarith
            calc _ = A * 1 := by ring
              _ ≤ A * ((16 / 9 : ℝ) ^ (2 * 1) *
                  (PowerWeightKernel.shellRatio ^ (Nat.dist i j)) ^ (2 * 1)) := by gcongr
              _ = (A * (16 / 9) ^ 2) *
                  (PowerWeightKernel.shellRatio ^ (Nat.dist i j)) ^ (2 * 1) := by ring
              _ ≤ _ := by gcongr
          gcongr
        · have h1 := PowerWeightKernel.sum_sq_div_far_shell_le R p θ D E f hN hθ hf i j hk
          refine h1.trans ?_
          have hE := pow_nonneg (hβ j) 1
          have hz : 0 ≤ (PowerWeightKernel.shellRatio ^ (Nat.dist i j)) ^ (2 * 1) := by
            positivity
          have h4 : PowerWeightKernel.countConstant R *
              (81 * PowerWeightKernel.countConstant R) ≤ B2 := by
            rw [hB2]
            have : 0 ≤ (81 / 64 : ℝ) ^ 2 * 81 ^ 2 * 16 * ((R : ℝ) + 8) ^ 2 * (16 / 9) ^ 2 := by
              positivity
            linarith
          gcongr)
    rw [hβsum] at hS
    have hfib : ∑ x ∈ E, (radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
        ∑ y ∈ D, truncatedCubicKernel R N (x - y) * f y) ^ 2 =
        ∑ i ∈ Finset.range n, ∑ x ∈ PowerWeightKernel.shellPart N p E i,
          (∑ j ∈ Finset.range n, radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
            ∑ y ∈ PowerWeightKernel.shellPart N p D j,
              truncatedCubicKernel R N (x - y) * f y) ^ (2 * 1) := by
      rw [← Finset.sum_fiberwise_of_maps_to (hmap E)]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      rw [hsplit x, Finset.mul_sum]
    rw [hfib]
    refine hS.trans ?_
    have h2 : 0 ≤ 5 ^ 4 * B4 * Sg := by positivity
    have h3 : (5 ^ 4 * B4 + 5 ^ 2 * B2) * Sg = 5 ^ (2 * 1) * B2 * Sg ^ 1 + 5 ^ 4 * B4 * Sg := by
      ring
    linarith
end YangMills.Construction.LatticeFractionalIntegration
end
