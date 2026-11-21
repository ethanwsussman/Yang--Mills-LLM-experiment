import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.DifferencesInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeFractionalIntegration
def cube (x : Lattice4) (R : ℕ) : Finset Lattice4 :=
  Fintype.piFinset fun i => Finset.Icc (x i - R) (x i + R)
theorem mem_cube {x y : Lattice4} {R : ℕ} : y ∈ cube x R ↔ ∀ i, |y i - x i| ≤ (R : ℤ) := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]
theorem card_cube (x : Lattice4) (R : ℕ) : ((cube x R).card : ℝ) = (2 * (R : ℝ) + 1) ^ 4 := by
  have h : ∀ i : Fin 4, (Finset.Icc (x i - R) (x i + R)).card = 2 * R + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  simp only [cube, Fintype.card_piFinset, h]
  simp
theorem supNorm_le_iff {v : Lattice4} {R : ℕ} : supNorm v ≤ R ↔ ∀ i, |v i| ≤ (R : ℤ) := by
  simp only [supNorm, Finset.sup_le_iff, Finset.mem_univ, true_imp_iff]
  constructor
  · intro h i
    have := h i
    rw [Int.abs_eq_natAbs]
    omega
  · intro h i
    have := h i
    rw [Int.abs_eq_natAbs] at this
    omega
theorem exists_disjoint_cube_subfamily (ρ : Lattice4 → ℕ) (T : Finset Lattice4) :
    ∃ T' ⊆ T, (∀ x ∈ T', ∀ y ∈ T', x ≠ y → Disjoint (cube x (ρ x)) (cube y (ρ y))) ∧
      ∀ x ∈ T, ∃ x' ∈ T', ρ x ≤ ρ x' ∧ ¬ Disjoint (cube x (ρ x)) (cube x' (ρ x')) := by
  induction' hn : T.card using Nat.strong_induction_on with n ih generalizing T
  rcases T.eq_empty_or_nonempty with rfl | hT
  · exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨x0, hx0, hmax⟩ := T.exists_max_image ρ hT
  set T1 := T.filter fun x => Disjoint (cube x (ρ x)) (cube x0 (ρ x0)) with hT1
  have hself : ¬ Disjoint (cube x0 (ρ x0)) (cube x0 (ρ x0)) := by
    rw [disjoint_self]
    have : x0 ∈ cube x0 (ρ x0) := by
      rw [mem_cube]
      intro i
      simp
    intro h
    rw [h] at this
    simp at this
  have hlt : T1.card < n := by
    rw [← hn]
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have := h hx0
    rw [hT1, Finset.mem_filter] at this
    exact hself this.2
  obtain ⟨T', hsub, hdis, hcov⟩ := ih _ hlt T1 rfl
  refine ⟨insert x0 T', ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hx0
    · exact (Finset.mem_filter.1 (hsub hx)).1
  · intro x hx y hy hxy
    rcases Finset.mem_insert.1 hx with rfl | hx' <;> rcases Finset.mem_insert.1 hy with rfl | hy'
    · exact absurd rfl hxy
    · exact ((Finset.mem_filter.1 (hsub hy')).2).symm
    · exact (Finset.mem_filter.1 (hsub hx')).2
    · exact hdis x hx' y hy' hxy
  · intro x hx
    by_cases hd : Disjoint (cube x (ρ x)) (cube x0 (ρ x0))
    · obtain ⟨x', hx', h1, h2⟩ := hcov x (Finset.mem_filter.2 ⟨hx, hd⟩)
      exact ⟨x', Finset.mem_insert_of_mem hx', h1, h2⟩
    · exact ⟨x0, Finset.mem_insert_self _ _, hmax x hx, hd⟩
def cubeSum (D : Finset Lattice4) (g : Lattice4 → ℝ) (x : Lattice4) (R : ℕ) : ℝ :=
  ∑ y ∈ D.filter (· ∈ cube x R), g y
theorem cubeSum_weakType (D : Finset Lattice4) (g : Lattice4 → ℝ) (hg : ∀ y, 0 ≤ g y) (u : ℝ)
    (hu : 0 < u) (T : Finset Lattice4) (ρ : Lattice4 → ℕ)
    (h : ∀ x ∈ T, u * (2 * (ρ x : ℝ) + 1) ^ 4 < cubeSum D g x (ρ x)) :
    u * T.card ≤ 16 * ∑ y ∈ D, g y := by
  obtain ⟨T', hsub, hdis, hcov⟩ := exists_disjoint_cube_subfamily ρ T
  have hcover : T ⊆ T'.biUnion fun x => cube x (2 * ρ x) := by
    intro x hx
    obtain ⟨x', hx', h1, h2⟩ := hcov x hx
    refine Finset.mem_biUnion.2 ⟨x', hx', ?_⟩
    obtain ⟨z, hz1, hz2⟩ := Finset.not_disjoint_iff.1 h2
    rw [mem_cube] at hz1 hz2 ⊢
    intro i
    have a1 := abs_le.1 (hz1 i)
    have a2 := abs_le.1 (hz2 i)
    have : (ρ x : ℤ) ≤ ρ x' := by exact_mod_cast h1
    push_cast
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have hcard : (T.card : ℝ) ≤ ∑ x ∈ T', 16 * (2 * (ρ x : ℝ) + 1) ^ 4 := by
    calc (T.card : ℝ) ≤ ((T'.biUnion fun x => cube x (2 * ρ x)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcover
      _ ≤ ((∑ x ∈ T', (cube x (2 * ρ x)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ _ := by
          push_cast
          apply Finset.sum_le_sum
          intro x _
          rw [card_cube]
          push_cast
          have h0 : (0 : ℝ) ≤ ρ x := Nat.cast_nonneg _
          have h1 : 2 * (2 * (ρ x : ℝ)) + 1 ≤ 2 * (2 * (ρ x : ℝ) + 1) := by linarith
          calc (2 * (2 * (ρ x : ℝ)) + 1) ^ 4 ≤ (2 * (2 * (ρ x : ℝ) + 1)) ^ 4 := by
                gcongr
            _ = 16 * (2 * (ρ x : ℝ) + 1) ^ 4 := by ring
  have hsum : ∑ x ∈ T', cubeSum D g x (ρ x) ≤ ∑ y ∈ D, g y := by
    have hd : (T' : Set Lattice4).PairwiseDisjoint fun x => D.filter (· ∈ cube x (ρ x)) := by
      intro x hx y hy hxy
      have := hdis x hx y hy hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left] at this ⊢
      intro z hz1 hz2
      exact this (Finset.mem_filter.1 hz1).2 (Finset.mem_filter.1 hz2).2
    simp only [cubeSum]
    rw [← Finset.sum_biUnion hd]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      obtain ⟨x, _, hz⟩ := Finset.mem_biUnion.1 hz
      exact (Finset.mem_filter.1 hz).1
    · intro z _ _
      exact hg z
  calc u * T.card ≤ u * ∑ x ∈ T', 16 * (2 * (ρ x : ℝ) + 1) ^ 4 := by gcongr
    _ = 16 * ∑ x ∈ T', u * (2 * (ρ x : ℝ) + 1) ^ 4 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ ≤ 16 * ∑ x ∈ T', cubeSum D g x (ρ x) := by
        gcongr with x hx
        exact (h x (hsub hx)).le
    _ ≤ _ := by gcongr
def maximalFunction (D : Finset Lattice4) (f : Lattice4 → ℝ) (x : Lattice4) : ℝ :=
  ⨆ R : ℕ, cubeSum D f x R / (2 * (R : ℝ) + 1) ^ 4
theorem bddAbove_cubeAverage (D : Finset Lattice4) (f : Lattice4 → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : Lattice4) :
    BddAbove (Set.range fun R : ℕ => cubeSum D f x R / (2 * (R : ℝ) + 1) ^ 4) := by
  refine ⟨∑ y ∈ D, f y, ?_⟩
  rintro _ ⟨R, rfl⟩
  have h1 : cubeSum D f x R ≤ ∑ y ∈ D, f y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun z _ _ => hf z
  have h0 : 0 ≤ cubeSum D f x R := Finset.sum_nonneg fun z _ => hf z
  have h2 : (1 : ℝ) ≤ (2 * (R : ℝ) + 1) ^ 4 := by
    apply one_le_pow₀
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    linarith
  exact (div_le_self h0 h2).trans h1
theorem maximalFunction_nonneg (D : Finset Lattice4) (f : Lattice4 → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : Lattice4) : 0 ≤ maximalFunction D f x := by
  have h := le_ciSup (bddAbove_cubeAverage D f hf x) 0
  have h0 : 0 ≤ cubeSum D f x 0 := Finset.sum_nonneg fun z _ => hf z
  refine le_trans ?_ h
  positivity
theorem maximalFunction_le_sum (D : Finset Lattice4) (f : Lattice4 → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : Lattice4) : maximalFunction D f x ≤ ∑ y ∈ D, f y := by
  apply ciSup_le
  intro R
  obtain ⟨b, hb⟩ := bddAbove_cubeAverage D f hf x
  have h1 : cubeSum D f x R ≤ ∑ y ∈ D, f y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun z _ _ => hf z
  have h0 : 0 ≤ cubeSum D f x R := Finset.sum_nonneg fun z _ => hf z
  have h2 : (1 : ℝ) ≤ (2 * (R : ℝ) + 1) ^ 4 := by
    apply one_le_pow₀
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    linarith
  exact (div_le_self h0 h2).trans h1
theorem cubeSum_le_maximalFunction (D : Finset Lattice4) (f : Lattice4 → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : Lattice4) (R : ℕ) :
    cubeSum D f x R ≤ (2 * (R : ℝ) + 1) ^ 4 * maximalFunction D f x := by
  have h := le_ciSup (bddAbove_cubeAverage D f hf x) R
  have h2 : (0 : ℝ) < (2 * (R : ℝ) + 1) ^ 4 := by positivity
  change _ ≤ maximalFunction D f x at h
  rw [div_le_iff₀ h2] at h
  linarith
theorem maximalFunction_distribution (D E : Finset Lattice4) (f : Lattice4 → ℝ)
    (hf : ∀ y, 0 ≤ f y) (s : ℝ) (hs : 0 < s) :
    s * (E.filter fun x => s < maximalFunction D f x).card ≤
      32 * ∑ y ∈ D.filter (fun y => s / 2 < f y), f y := by
  classical
  set T := E.filter fun x => s < maximalFunction D f x with hT
  set g : Lattice4 → ℝ := fun y => if s / 2 < f y then f y else 0 with hgdef
  have hg : ∀ y, 0 ≤ g y := by
    intro y
    simp only [hgdef]
    split_ifs
    · exact hf y
    · exact le_rfl
  have hex : ∀ x ∈ T, ∃ R : ℕ, s / 2 * (2 * (R : ℝ) + 1) ^ 4 < cubeSum D g x R := by
    intro x hx
    have hx2 := (Finset.mem_filter.1 hx).2
    obtain ⟨R, hR⟩ := exists_lt_of_lt_ciSup hx2
    refine ⟨R, ?_⟩
    have hpos : (0 : ℝ) < (2 * (R : ℝ) + 1) ^ 4 := by positivity
    rw [lt_div_iff₀ hpos] at hR
    have hsplit : cubeSum D f x R ≤ cubeSum D g x R + s / 2 * (2 * (R : ℝ) + 1) ^ 4 := by
      have hc : ((D.filter (· ∈ cube x R)).card : ℝ) ≤ (2 * (R : ℝ) + 1) ^ 4 := by
        rw [← card_cube x R]
        have : D.filter (· ∈ cube x R) ⊆ cube x R := fun z hz => (Finset.mem_filter.1 hz).2
        exact_mod_cast Finset.card_le_card this
      have hpt : ∀ y ∈ D.filter (· ∈ cube x R), f y ≤ g y + s / 2 := by
        intro y _
        simp only [hgdef]
        split_ifs with h
        · linarith
        · linarith [not_lt.1 h]
      calc cubeSum D f x R ≤ ∑ y ∈ D.filter (· ∈ cube x R), (g y + s / 2) :=
            Finset.sum_le_sum hpt
        _ = cubeSum D g x R + ((D.filter (· ∈ cube x R)).card : ℝ) * (s / 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
            rfl
        _ ≤ _ := by
            have : (0 : ℝ) ≤ s / 2 := by positivity
            nlinarith
    nlinarith
  choose! ρ hρ using hex
  have hw := cubeSum_weakType D g hg (s / 2) (by positivity) T ρ hρ
  have hsum : ∑ y ∈ D, g y = ∑ y ∈ D.filter (fun y => s / 2 < f y), f y := by
    rw [Finset.sum_filter]
  rw [hsum] at hw
  linarith
theorem dyadic_level_sum_le (lam ε v : ℝ) (hlam : 0 < lam) (hε : 0 < ε) (hv : 0 < v) (n : ℕ) :
    (∑ i ∈ (Finset.range n).filter (fun i => lam * 2 ^ i < v), (lam * 2 ^ i) ^ ε) *
        ((2 : ℝ) ^ ε - 1) ≤ (min (lam * 2 ^ n) (2 * v)) ^ ε := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.filter_empty, Finset.sum_empty, zero_mul]
    apply Real.rpow_nonneg
    apply le_min <;> positivity
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have hsn : 0 < lam * 2 ^ n := by positivity
    split_ifs with h
    · rw [Finset.sum_insert (by simp)]
      have e1 : min (lam * 2 ^ n) (2 * v) = lam * 2 ^ n := min_eq_left (by linarith)
      have e2 : min (lam * 2 ^ (n + 1)) (2 * v) = 2 * (lam * 2 ^ n) := by
        rw [pow_succ, min_eq_left (by nlinarith)]
        ring
      rw [e1] at ih
      rw [e2, Real.mul_rpow (by norm_num) hsn.le]
      nlinarith
    · have hmono : min (lam * 2 ^ n) (2 * v) ≤ min (lam * 2 ^ (n + 1)) (2 * v) := by
        apply min_le_min_right
        rw [pow_succ]
        nlinarith
      refine ih.trans ?_
      apply Real.rpow_le_rpow _ hmono hε.le
      apply le_min <;> positivity
theorem maximalFunction_strongType (p : ℝ) (hp : 1 < p) : ∃ C : ℝ, 0 < C ∧
    ∀ (D E : Finset Lattice4) (f : Lattice4 → ℝ),
    (∀ y, 0 ≤ f y) → ∑ x ∈ E, maximalFunction D f x ^ p ≤ C * ∑ y ∈ D, f y ^ p := by
  classical
  set ε := p - 1 with hε
  have hε0 : 0 < ε := by linarith
  have hρ : (1 : ℝ) < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε0
  have hρ0 : 0 < (2 : ℝ) ^ ε - 1 := by linarith
  refine ⟨32 * (2 : ℝ) ^ p * (4 : ℝ) ^ ε / ((2 : ℝ) ^ ε - 1), by positivity, ?_⟩
  intro D E f hf
  set M := maximalFunction D f with hM
  have hM0 : ∀ x, 0 ≤ M x := maximalFunction_nonneg D f hf
  have hrhs : 0 ≤ ∑ y ∈ D, f y ^ p := Finset.sum_nonneg fun y _ => Real.rpow_nonneg (hf y) _
  set E' := E.filter fun x => 0 < M x with hE'
  have hsplit : ∑ x ∈ E, M x ^ p = ∑ x ∈ E', M x ^ p := by
    rw [hE', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · rfl
    · have : M x = 0 := le_antisymm (not_lt.1 h) (hM0 x)
      rw [this, Real.zero_rpow (by linarith)]
  rw [hsplit]
  rcases E'.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    positivity
  obtain ⟨xm, hxm, hmin⟩ := E'.exists_min_image M hne
  have hxm0 : 0 < M xm := (Finset.mem_filter.1 hxm).2
  set lam := M xm / 2 with hlam
  have hlam0 : 0 < lam := by positivity
  have hlt : ∀ x ∈ E', lam < M x := by
    intro x hx
    have := hmin x hx
    linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((∑ y ∈ D, f y) / lam) (one_lt_two : (1 : ℝ) < 2)
  have htop : ∀ x, M x ≤ lam * 2 ^ n := by
    intro x
    have h1 := maximalFunction_le_sum D f hf x
    rw [div_lt_iff₀ hlam0] at hn
    have : M x ≤ ∑ y ∈ D, f y := h1
    nlinarith
  have hlevel : ∀ x ∈ E', M x ^ p ≤ ∑ i ∈ Finset.range n,
      if lam * 2 ^ i < M x then (lam * 2 ^ (i + 1)) ^ p else 0 := by
    intro x hx
    have hP : ∃ k, M x ≤ lam * 2 ^ k := ⟨n, htop x⟩
    have hk := Nat.find_spec hP
    have hkn : Nat.find hP ≤ n := Nat.find_min' hP (htop x)
    have hk0 : Nat.find hP ≠ 0 := by
      intro h0
      rw [h0] at hk
      have := hlt x hx
      simp at hk
      linarith
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hmin' : ¬ M x ≤ lam * 2 ^ i := Nat.find_min hP (by omega)
    have hin : i ∈ Finset.range n := Finset.mem_range.2 (by omega)
    have hterm : M x ^ p ≤ (lam * 2 ^ (i + 1)) ^ p := by
      apply Real.rpow_le_rpow (hM0 x) _ (by linarith)
      rw [hi] at hk
      exact hk
    refine hterm.trans ?_
    have hsingle := Finset.single_le_sum (f := fun i => if lam * 2 ^ i < M x then
        (lam * 2 ^ (i + 1)) ^ p else 0) (s := Finset.range n) (by
        intro j _
        split_ifs
        · positivity
        · exact le_rfl) hin
    simp only [not_le.1 hmin', if_true] at hsingle
    exact hsingle
  have hcount : ∀ i, (lam * 2 ^ (i + 1)) ^ p * ((E'.filter fun x => lam * 2 ^ i < M x).card : ℝ) ≤
      (2 : ℝ) ^ p * (lam * 2 ^ i) ^ ε *
        (32 * ∑ y ∈ D, if lam * 2 ^ i < 2 * f y then f y else 0) := by
    intro i
    have hs : 0 < lam * 2 ^ i := by positivity
    have hd := maximalFunction_distribution D E f hf (lam * 2 ^ i) hs
    have hsub : ((E'.filter fun x => lam * 2 ^ i < M x).card : ℝ) ≤
        ((E.filter fun x => lam * 2 ^ i < maximalFunction D f x).card : ℝ) := by
      have : E'.filter (fun x => lam * 2 ^ i < M x) ⊆
          E.filter fun x => lam * 2 ^ i < maximalFunction D f x := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨(Finset.mem_filter.1 hx.1).1, hx.2⟩
      exact_mod_cast Finset.card_le_card this
    have hfil : ∑ y ∈ D.filter (fun y => lam * 2 ^ i / 2 < f y), f y =
        ∑ y ∈ D, if lam * 2 ^ i < 2 * f y then f y else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      have : (lam * 2 ^ i / 2 < f y) ↔ (lam * 2 ^ i < 2 * f y) := by
        constructor <;> intro h <;> linarith
      simp only [this]
    rw [hfil] at hd
    have hpow : (lam * 2 ^ (i + 1)) ^ p = (2 : ℝ) ^ p * (lam * 2 ^ i) ^ ε * (lam * 2 ^ i) := by
      have e1 : lam * 2 ^ (i + 1) = 2 * (lam * 2 ^ i) := by rw [pow_succ]; ring
      rw [e1, Real.mul_rpow (by norm_num) hs.le]
      have e2 : (lam * 2 ^ i) ^ p = (lam * 2 ^ i) ^ ε * (lam * 2 ^ i) := by
        have : p = ε + 1 := by rw [hε]; ring
        rw [this, Real.rpow_add hs, Real.rpow_one]
      rw [e2]
      ring
    rw [hpow]
    have hnn : 0 ≤ (2 : ℝ) ^ p * (lam * 2 ^ i) ^ ε := by positivity
    calc _ = (2 : ℝ) ^ p * (lam * 2 ^ i) ^ ε *
          ((lam * 2 ^ i) * ((E'.filter fun x => lam * 2 ^ i < M x).card : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ p * (lam * 2 ^ i) ^ ε *
          ((lam * 2 ^ i) * ((E.filter fun x => lam * 2 ^ i < maximalFunction D f x).card : ℝ)) := by
          gcongr
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hnn
          exact hd
  have hinner : ∀ y ∈ D, f y * ∑ i ∈ Finset.range n,
      (if lam * 2 ^ i < 2 * f y then (lam * 2 ^ i) ^ ε else 0) ≤
        (4 : ℝ) ^ ε / ((2 : ℝ) ^ ε - 1) * f y ^ p := by
    intro y _
    rcases (hf y).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith)]
      simp
    · have hl := dyadic_level_sum_le lam ε (2 * f y) hlam0 hε0 (by positivity) n
      rw [← Finset.sum_filter]
      have hmin2 : (min (lam * 2 ^ n) (2 * (2 * f y))) ^ ε ≤ (4 : ℝ) ^ ε * f y ^ ε := by
        rw [← Real.mul_rpow (by norm_num) hpos.le]
        apply Real.rpow_le_rpow _ _ hε0.le
        · apply le_min <;> positivity
        · refine (min_le_right _ _).trans ?_
          linarith
      have hS := hl.trans hmin2
      have hS' : ∑ i ∈ (Finset.range n).filter (fun i => lam * 2 ^ i < 2 * f y), (lam * 2 ^ i) ^ ε ≤
          (4 : ℝ) ^ ε * f y ^ ε / ((2 : ℝ) ^ ε - 1) := by
        rw [le_div_iff₀ hρ0]
        exact hS
      have hfp : f y ^ p = f y * f y ^ ε := by
        have : p = 1 + ε := by rw [hε]; ring
        rw [this, Real.rpow_add hpos, Real.rpow_one]
      rw [hfp]
      calc _ ≤ f y * ((4 : ℝ) ^ ε * f y ^ ε / ((2 : ℝ) ^ ε - 1)) := by gcongr
        _ = _ := by ring
  calc ∑ x ∈ E', M x ^ p ≤ ∑ x ∈ E', ∑ i ∈ Finset.range n,
        (if lam * 2 ^ i < M x then (lam * 2 ^ (i + 1)) ^ p else 0) := Finset.sum_le_sum hlevel
    _ = ∑ i ∈ Finset.range n, (lam * 2 ^ (i + 1)) ^ p *
          ((E'.filter fun x => lam * 2 ^ i < M x).card : ℝ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ i ∈ Finset.range n, (2 : ℝ) ^ p * (lam * 2 ^ i) ^ ε *
          (32 * ∑ y ∈ D, if lam * 2 ^ i < 2 * f y then f y else 0) :=
        Finset.sum_le_sum fun i _ => hcount i
    _ = 32 * (2 : ℝ) ^ p * ∑ y ∈ D, f y * ∑ i ∈ Finset.range n,
          (if lam * 2 ^ i < 2 * f y then (lam * 2 ^ i) ^ ε else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
    _ ≤ 32 * (2 : ℝ) ^ p * ∑ y ∈ D, (4 : ℝ) ^ ε / ((2 : ℝ) ^ ε - 1) * f y ^ p := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner) (by positivity)
    _ = _ := by
        rw [← Finset.mul_sum]
        ring
theorem cubicKernel_le_dyadic (J : ℕ) (v : Lattice4) (hv : supNorm v ≤ 2 ^ J) :
    ∃ j ≤ J, (∀ i, |v i| ≤ ((2 ^ j : ℕ) : ℤ)) ∧ cubicKernel v ≤ 8 * (1 / 8 : ℝ) ^ j := by
  have hP : ∃ k, supNorm v ≤ 2 ^ k := ⟨J, hv⟩
  have hk := Nat.find_spec hP
  refine ⟨Nat.find hP, Nat.find_min' hP hv, supNorm_le_iff.1 hk, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hP) with h0 | hpos
  · rw [h0]
    have hm : (1 : ℝ) ≤ ((max 1 (supNorm v) : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have : cubicKernel v ≤ 1 := by
      unfold cubicKernel
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ hm
    norm_num
    linarith
  · obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hmin : ¬ supNorm v ≤ 2 ^ i := Nat.find_min hP (by omega)
    have h2 : (2 : ℝ) ^ i ≤ ((max 1 (supNorm v) : ℕ) : ℝ) := by
      have : 2 ^ i ≤ max 1 (supNorm v) := le_trans (not_le.1 hmin).le (le_max_right _ _)
      exact_mod_cast this
    unfold cubicKernel
    rw [hi]
    have h3 : (8 : ℝ) ^ i ≤ ((max 1 (supNorm v) : ℕ) : ℝ) ^ 3 := by
      calc (8 : ℝ) ^ i = ((2 : ℝ) ^ i) ^ 3 := by
            rw [← pow_mul, mul_comm, pow_mul]
            norm_num
        _ ≤ _ := by gcongr
    have h8 : (0 : ℝ) < 8 ^ i := by positivity
    calc 1 / ((max 1 (supNorm v) : ℕ) : ℝ) ^ 3 ≤ 1 / (8 : ℝ) ^ i := by
          apply one_div_le_one_div_of_le h8 h3
      _ = _ := by
          rw [Nat.succ_eq_add_one, pow_succ, one_div_pow]
          field_simp
theorem cubicKernel_nonneg (v : Lattice4) : 0 ≤ cubicKernel v := by apply _root_.YangMills.Construction.PatchDifferences.cubicKernel_nonneg_apply <;> assumption
theorem kernel_convolution_le (D : Finset Lattice4) (f : Lattice4 → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : Lattice4) (J : ℕ) (hJ : ∀ y ∈ D, supNorm (x - y) ≤ 2 ^ J) :
    ∑ y ∈ D, cubicKernel (x - y) * f y ≤
      8 * ∑ j ∈ Finset.range (J + 1), (1 / 8 : ℝ) ^ j * cubeSum D f x (2 ^ j) := by
  classical
  have hswap : 8 * ∑ j ∈ Finset.range (J + 1), (1 / 8 : ℝ) ^ j * cubeSum D f x (2 ^ j) =
      ∑ y ∈ D, 8 * ∑ j ∈ Finset.range (J + 1),
        (if y ∈ cube x (2 ^ j) then (1 / 8 : ℝ) ^ j * f y else 0) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [cubeSum, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp
  rw [hswap]
  apply Finset.sum_le_sum
  intro y hy
  obtain ⟨j, hj, hin, hk⟩ := cubicKernel_le_dyadic J (x - y) (hJ y hy)
  have hmem : y ∈ cube x (2 ^ j) := by
    rw [mem_cube]
    intro i
    have := hin i
    rw [Pi.sub_apply, abs_sub_comm] at this
    exact this
  have hs := Finset.single_le_sum (f := fun j => if y ∈ cube x (2 ^ j) then
      (1 / 8 : ℝ) ^ j * f y else 0) (s := Finset.range (J + 1)) (by
      intro k _
      split_ifs
      · have := hf y
        positivity
      · exact le_rfl) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  simp only [hmem, if_true] at hs
  calc cubicKernel (x - y) * f y ≤ 8 * (1 / 8 : ℝ) ^ j * f y := by
        gcongr
        exact hf y
    _ = 8 * ((1 / 8 : ℝ) ^ j * f y) := by ring
    _ ≤ _ := by gcongr
theorem sum_range_two_pow_le (k : ℕ) : ∑ i ∈ Finset.range k, (2 : ℝ) ^ i ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith
theorem sum_range_geom_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, r ^ i ≤ 1 / (1 - r) := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.geom_sum_le_inv_one_sub <;> assumption
theorem sum_min_geom_le (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ M B : ℝ, 0 ≤ M → 0 ≤ B →
    ∀ n : ℕ, ∑ j ∈ Finset.range n, min ((2 : ℝ) ^ j * M) (((2 : ℝ) ^ (-ε)) ^ j * B) ≤
      C * (M ^ (ε / (1 + ε)) * B ^ (1 / (1 + ε))) := by
  set r := (2 : ℝ) ^ (-ε) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨2 + 1 / (1 - r), by positivity, ?_⟩
  intro M B hM hB n
  set η := ε / (1 + ε) with hη
  set θ := 1 / (1 + ε) with hθ
  have hθη : θ + η = 1 := by
    rw [hθ, hη]
    field_simp
  have hθ0 : 0 < θ := by positivity
  have hrhs : 0 ≤ (2 + 1 / (1 - r)) * (M ^ η * B ^ θ) := by
    have := Real.rpow_nonneg hM η
    have := Real.rpow_nonneg hB θ
    positivity
  rcases hM.eq_or_lt with hM0 | hMpos
  · refine le_trans (Finset.sum_nonpos fun j _ => ?_) hrhs
    rw [← hM0, mul_zero]
    exact min_le_left _ _
  rcases hB.eq_or_lt with hB0 | hBpos
  · refine le_trans (Finset.sum_nonpos fun j _ => ?_) hrhs
    rw [← hB0, mul_zero]
    exact min_le_right _ _
  by_cases hBM : B ≤ M
  · have hb : B ≤ M ^ η * B ^ θ := by
      calc B = B ^ η * B ^ θ := by
            rw [← Real.rpow_add hBpos, add_comm, hθη, Real.rpow_one]
        _ ≤ _ := by
            gcongr
    calc ∑ j ∈ Finset.range n, min ((2 : ℝ) ^ j * M) (r ^ j * B) ≤
          ∑ j ∈ Finset.range n, r ^ j * B := Finset.sum_le_sum fun j _ => min_le_right _ _
      _ = (∑ j ∈ Finset.range n, r ^ j) * B := by rw [Finset.sum_mul]
      _ ≤ 1 / (1 - r) * (M ^ η * B ^ θ) := by
          apply mul_le_mul (sum_range_geom_le r hr0.le hr1 n) hb hBpos.le (by positivity)
      _ ≤ _ := by
          have : 0 ≤ M ^ η * B ^ θ := by positivity
          nlinarith
  · have hBM' : M < B := not_le.1 hBM
    set T := (B / M) ^ θ with hT
    have hq1 : 1 ≤ B / M := by
      rw [one_le_div hMpos]
      exact hBM'.le
    have hT1 : 1 ≤ T := Real.one_le_rpow hq1 hθ0.le
    have hTpos : 0 < T := by linarith
    have hTM : T * M = M ^ η * B ^ θ := by
      rw [hT, Real.div_rpow hBpos.le hMpos.le]
      have : M = M ^ θ * M ^ η := by
        rw [← Real.rpow_add hMpos, hθη, Real.rpow_one]
      calc B ^ θ / M ^ θ * M = B ^ θ / M ^ θ * (M ^ θ * M ^ η) := by rw [← this]
        _ = _ := by
            field_simp
    have hTB : T ^ (-ε) * B = M ^ η * B ^ θ := by
      have e1 : T ^ (-ε) = (B / M) ^ (-η) := by
        rw [hT, ← Real.rpow_mul (by positivity)]
        congr 1
        rw [hθ, hη]
        field_simp
      rw [e1, Real.div_rpow hBpos.le hMpos.le, Real.rpow_neg hBpos.le, Real.rpow_neg hMpos.le]
      have : B = B ^ θ * B ^ η := by
        rw [← Real.rpow_add hBpos, hθη, Real.rpow_one]
      calc (B ^ η)⁻¹ / (M ^ η)⁻¹ * B = (B ^ η)⁻¹ / (M ^ η)⁻¹ * (B ^ θ * B ^ η) := by rw [← this]
        _ = _ := by
            field_simp
    obtain ⟨j0, h1, h2⟩ := exists_nat_pow_near hT1 (one_lt_two : (1 : ℝ) < 2)
    have hsub : Finset.range n ⊆ Finset.range (j0 + 1) ∪ Finset.Ico (j0 + 1) n := by
      intro j hj
      rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      rw [Finset.mem_range] at hj
      omega
    have hdisj : Disjoint (Finset.range (j0 + 1)) (Finset.Ico (j0 + 1) n) := by
      rw [Finset.disjoint_left]
      intro j h3 h4
      rw [Finset.mem_range] at h3
      rw [Finset.mem_Ico] at h4
      omega
    have hnn : ∀ j, 0 ≤ min ((2 : ℝ) ^ j * M) (r ^ j * B) := by
      intro j
      apply le_min <;> positivity
    have hfirst : ∑ j ∈ Finset.range (j0 + 1), min ((2 : ℝ) ^ j * M) (r ^ j * B) ≤
        2 * (T * M) := by
      calc _ ≤ ∑ j ∈ Finset.range (j0 + 1), (2 : ℝ) ^ j * M :=
            Finset.sum_le_sum fun j _ => min_le_left _ _
        _ = (∑ j ∈ Finset.range (j0 + 1), (2 : ℝ) ^ j) * M := by rw [Finset.sum_mul]
        _ ≤ (2 : ℝ) ^ (j0 + 1) * M := by
            gcongr
            exact sum_range_two_pow_le _
        _ ≤ 2 * T * M := by
            gcongr
            rw [pow_succ]
            linarith
        _ = _ := by ring
    have hsecond : ∑ j ∈ Finset.Ico (j0 + 1) n, min ((2 : ℝ) ^ j * M) (r ^ j * B) ≤
        1 / (1 - r) * (T ^ (-ε) * B) := by
      have hrT : r ^ (j0 + 1) ≤ T ^ (-ε) := by
        have : r ^ (j0 + 1) = ((2 : ℝ) ^ (j0 + 1)) ^ (-ε) := by
          rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num)]
          congr 1
          ring
        rw [this]
        exact Real.rpow_le_rpow_of_nonpos hTpos h2.le (by linarith)
      calc _ ≤ ∑ j ∈ Finset.Ico (j0 + 1) n, r ^ j * B :=
            Finset.sum_le_sum fun j _ => min_le_right _ _
        _ = (∑ j ∈ Finset.Ico (j0 + 1) n, r ^ j) * B := by rw [Finset.sum_mul]
        _ = (r ^ (j0 + 1) * ∑ i ∈ Finset.range (n - (j0 + 1)), r ^ i) * B := by
            rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [pow_add]
        _ ≤ (T ^ (-ε) * (1 / (1 - r))) * B := by
            gcongr
            exact sum_range_geom_le r hr0.le hr1 _
        _ = _ := by ring
    calc _ ≤ ∑ j ∈ Finset.range (j0 + 1) ∪ Finset.Ico (j0 + 1) n,
          min ((2 : ℝ) ^ j * M) (r ^ j * B) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hnn j
      _ = _ + _ := Finset.sum_union hdisj
      _ ≤ 2 * (T * M) + 1 / (1 - r) * (T ^ (-ε) * B) := add_le_add hfirst hsecond
      _ = _ := by
          rw [hTM, hTB]
          ring
theorem dyadic_cubeSum_le (p : ℝ) (hp : 1 < p) (hp4 : p < 4) (D : Finset Lattice4)
    (f : Lattice4 → ℝ) (hf : ∀ y, 0 ≤ f y) (x : Lattice4) (j : ℕ) :
    (1 / 8 : ℝ) ^ j * cubeSum D f x (2 ^ j) ≤
      81 * min ((2 : ℝ) ^ j * maximalFunction D f x)
        (((2 : ℝ) ^ (-(4 / p - 1))) ^ j * (∑ y ∈ D, f y ^ p) ^ (1 / p)) := by
  set R : ℕ := 2 ^ j with hR
  have hRr : (R : ℝ) = (2 : ℝ) ^ j := by rw [hR]; push_cast; rfl
  have hside : 2 * (R : ℝ) + 1 ≤ 3 * (2 : ℝ) ^ j := by
    rw [hRr]
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith
  have h8 : (1 / 8 : ℝ) ^ j * ((3 * (2 : ℝ) ^ j) ^ 4) = 81 * (2 : ℝ) ^ j := by
    have : (3 * (2 : ℝ) ^ j) ^ 4 = 81 * ((2 : ℝ) ^ 4) ^ j := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j 4]
      norm_num
    rw [this]
    have e : (1 / 8 : ℝ) ^ j * ((2 : ℝ) ^ 4) ^ j = 2 ^ j := by
      rw [← mul_pow]
      norm_num
    calc _ = 81 * ((1 / 8 : ℝ) ^ j * ((2 : ℝ) ^ 4) ^ j) := by ring
      _ = _ := by rw [e]
  have hMnn := maximalFunction_nonneg D f hf x
  have ha : (1 / 8 : ℝ) ^ j * cubeSum D f x R ≤ 81 * ((2 : ℝ) ^ j * maximalFunction D f x) := by
    have h1 := cubeSum_le_maximalFunction D f hf x R
    calc _ ≤ (1 / 8 : ℝ) ^ j * ((3 * (2 : ℝ) ^ j) ^ 4 * maximalFunction D f x) := by
          gcongr
          refine h1.trans ?_
          gcongr
      _ = ((1 / 8 : ℝ) ^ j * ((3 * (2 : ℝ) ^ j) ^ 4)) * maximalFunction D f x := by ring
      _ = _ := by
          rw [h8]
          ring
  set q' := p.conjExponent with hq'
  have hconj : p.HolderConjugate q' := Real.HolderConjugate.conjExponent hp
  have hinv : 1 / q' = 1 - 1 / p := by
    have := hconj.inv_add_inv_eq_one
    rw [one_div, one_div]
    linarith
  set Dc := D.filter (· ∈ cube x R) with hDc
  have hold := Real.inner_le_Lp_mul_Lq Dc f (fun _ => (1 : ℝ)) hconj
  have hq0 : 0 < q' := hconj.symm.pos
  have hone : ∑ i ∈ Dc, |(1 : ℝ)| ^ q' = (Dc.card : ℝ) := by
    simp
  rw [hone] at hold
  simp only [mul_one] at hold
  have hS1 : ∑ i ∈ Dc, |f i| ^ p ≤ ∑ y ∈ D, f y ^ p := by
    calc _ = ∑ i ∈ Dc, f i ^ p := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_of_nonneg (hf i)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun z _ _ =>
          Real.rpow_nonneg (hf z) _
  have hcard : (Dc.card : ℝ) ≤ (3 * (2 : ℝ) ^ j) ^ 4 := by
    calc (Dc.card : ℝ) ≤ ((cube x R).card : ℝ) := by
          have : Dc ⊆ cube x R := fun z hz => (Finset.mem_filter.1 hz).2
          exact_mod_cast Finset.card_le_card this
      _ = (2 * (R : ℝ) + 1) ^ 4 := card_cube x R
      _ ≤ _ := by gcongr
  have hB0 : 0 ≤ (∑ y ∈ D, f y ^ p) ^ (1 / p) :=
    Real.rpow_nonneg (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (hf y) _) _
  have hbox : cubeSum D f x R ≤ (∑ y ∈ D, f y ^ p) ^ (1 / p) *
      ((3 * (2 : ℝ) ^ j) ^ 4) ^ (1 / q') := by
    refine hold.trans ?_
    apply mul_le_mul
    · apply Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity) hS1 (by positivity)
    · apply Real.rpow_le_rpow (by positivity) hcard (by positivity)
    · positivity
    · exact hB0
  have hpow : (1 / 8 : ℝ) ^ j * ((3 * (2 : ℝ) ^ j) ^ 4) ^ (1 / q') ≤
      81 * ((2 : ℝ) ^ (-(4 / p - 1))) ^ j := by
    have e1 : ((3 * (2 : ℝ) ^ j) ^ 4) ^ (1 / q') =
        (3 : ℝ) ^ (4 * (1 / q')) * ((2 : ℝ) ^ (4 * (1 / q'))) ^ j := by
      rw [← Real.rpow_natCast (3 * (2 : ℝ) ^ j) 4, ← Real.rpow_mul (by positivity),
        Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast 2 j, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast _ j,
        ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    have e2 : (1 / 8 : ℝ) ^ j * ((2 : ℝ) ^ (4 * (1 / q'))) ^ j =
        ((2 : ℝ) ^ (-(4 / p - 1))) ^ j := by
      rw [← mul_pow]
      congr 1
      have : (-(4 / p - 1)) = 4 * (1 / q') + (-3 : ℝ) := by
        rw [hinv]
        ring
      rw [this, Real.rpow_add (by norm_num)]
      have : (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 := by
        rw [Real.rpow_neg (by norm_num)]
        norm_num
      rw [this]
      ring
    have e3 : (3 : ℝ) ^ (4 * (1 / q')) ≤ 81 := by
      have hle : 4 * (1 / q') ≤ (4 : ℕ) := by
        rw [hinv]
        have : 0 < 1 / p := by positivity
        push_cast
        linarith
      calc (3 : ℝ) ^ (4 * (1 / q')) ≤ (3 : ℝ) ^ ((4 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
        _ = 81 := by
            rw [Real.rpow_natCast]
            norm_num
    rw [e1]
    calc _ = (3 : ℝ) ^ (4 * (1 / q')) * ((1 / 8 : ℝ) ^ j * ((2 : ℝ) ^ (4 * (1 / q'))) ^ j) := by
          ring
      _ = (3 : ℝ) ^ (4 * (1 / q')) * ((2 : ℝ) ^ (-(4 / p - 1))) ^ j := by rw [e2]
      _ ≤ _ := by gcongr
  have hb : (1 / 8 : ℝ) ^ j * cubeSum D f x R ≤
      81 * (((2 : ℝ) ^ (-(4 / p - 1))) ^ j * (∑ y ∈ D, f y ^ p) ^ (1 / p)) := by
    calc _ ≤ (1 / 8 : ℝ) ^ j * ((∑ y ∈ D, f y ^ p) ^ (1 / p) *
          ((3 * (2 : ℝ) ^ j) ^ 4) ^ (1 / q')) := by gcongr
      _ = ((1 / 8 : ℝ) ^ j * ((3 * (2 : ℝ) ^ j) ^ 4) ^ (1 / q')) *
          (∑ y ∈ D, f y ^ p) ^ (1 / p) := by ring
      _ ≤ (81 * ((2 : ℝ) ^ (-(4 / p - 1))) ^ j) * (∑ y ∈ D, f y ^ p) ^ (1 / p) := by gcongr
      _ = _ := by ring
  have := le_min ha hb
  rwa [← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 81)] at this
theorem hardyLittlewoodSobolev : hardyLittlewoodSobolevStatement := by
  intro p q hp hp4 hpq
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by
    have : 0 < 1 / q := by
      rw [hpq]
      have : 1 / 4 < 1 / p := one_div_lt_one_div_of_lt hp0 hp4
      linarith
    exact one_div_pos.1 this
  set ε := 4 / p - 1 with hε
  have hε0 : 0 < ε := by
    have : 1 < 4 / p := by rw [one_lt_div hp0]; exact hp4
    linarith
  have h1ε : 1 + ε = 4 / p := by rw [hε]; ring
  have hθ : 1 / (1 + ε) = p / 4 := by rw [h1ε]; field_simp
  have hη : ε / (1 + ε) = 1 - p / 4 := by
    rw [h1ε, hε]
    field_simp
  have hq : q * (1 - p / 4) = p := by
    have h : 1 / q * (p * 4) = 4 - p := by
      rw [hpq]
      field_simp
    field_simp at h ⊢
    linarith
  have hq2 : q * (p / 4) + p = q := by
    have := hq
    linarith
  obtain ⟨C1, hC1, hmin⟩ := sum_min_geom_le ε hε0
  obtain ⟨Cs, hCs, hstrong⟩ := maximalFunction_strongType p hp
  set A := 8 * 81 * C1 with hA
  have hApos : 0 < A := by positivity
  refine ⟨A * Cs ^ (1 / q), by positivity, ?_⟩
  intro D E f
  set g : Lattice4 → ℝ := fun y => |f y| with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => abs_nonneg _
  set S := ∑ y ∈ D, g y ^ p with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun y _ => Real.rpow_nonneg (hg0 y) _
  set B := S ^ (1 / p) with hB
  have hB0 : 0 ≤ B := Real.rpow_nonneg hS0 _
  have hBp : B ^ p = S := by
    rw [hB, ← Real.rpow_mul hS0]
    field_simp
    exact Real.rpow_one _
  set M := maximalFunction D g with hM
  have hM0 : ∀ x, 0 ≤ M x := maximalFunction_nonneg D g hg0
  have hpoint : ∀ x, |∑ y ∈ D, cubicKernel (x - y) * f y| ≤
      A * (M x ^ (1 - p / 4) * B ^ (p / 4)) := by
    intro x
    have habs : |∑ y ∈ D, cubicKernel (x - y) * f y| ≤ ∑ y ∈ D, cubicKernel (x - y) * g y := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (cubicKernel_nonneg _)]
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ y ∈ D, supNorm (x - y) ≤ 2 ^ J := by
      refine ⟨D.sup fun y => supNorm (x - y), fun y hy => ?_⟩
      have h1 : supNorm (x - y) ≤ D.sup fun y => supNorm (x - y) :=
        Finset.le_sup (f := fun y => supNorm (x - y)) hy
      exact h1.trans Nat.lt_two_pow_self.le
    have hconv := kernel_convolution_le D g hg0 x J hJ
    have hterm : ∑ j ∈ Finset.range (J + 1), (1 / 8 : ℝ) ^ j * cubeSum D g x (2 ^ j) ≤
        81 * ∑ j ∈ Finset.range (J + 1), min ((2 : ℝ) ^ j * M x)
          (((2 : ℝ) ^ (-ε)) ^ j * B) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      exact dyadic_cubeSum_le p hp hp4 D g hg0 x j
    have hfin := hmin (M x) B (hM0 x) hB0 (J + 1)
    rw [hη, hθ] at hfin
    calc _ ≤ _ := habs
      _ ≤ _ := hconv
      _ ≤ 8 * (81 * (C1 * (M x ^ (1 - p / 4) * B ^ (p / 4)))) := by
          gcongr
          exact hterm.trans (by gcongr)
      _ = _ := by
          rw [hA]
          ring
  have hsum : ∑ x ∈ E, |∑ y ∈ D, cubicKernel (x - y) * f y| ^ q ≤
      A ^ q * B ^ (q * (p / 4)) * (Cs * S) := by
    calc _ ≤ ∑ x ∈ E, (A ^ q * B ^ (q * (p / 4))) * M x ^ p := by
          apply Finset.sum_le_sum
          intro x _
          have hMx := hM0 x
          calc _ ≤ (A * (M x ^ (1 - p / 4) * B ^ (p / 4))) ^ q :=
                Real.rpow_le_rpow (abs_nonneg _) (hpoint x) hq0.le
            _ = _ := by
                have m1 : 0 ≤ M x ^ (1 - p / 4) := Real.rpow_nonneg hMx _
                have m2 : 0 ≤ B ^ (p / 4) := Real.rpow_nonneg hB0 _
                rw [Real.mul_rpow hApos.le (mul_nonneg m1 m2), Real.mul_rpow m1 m2,
                  ← Real.rpow_mul hMx, ← Real.rpow_mul hB0, mul_comm (1 - p / 4) q, hq,
                  mul_comm (p / 4) q]
                ring
      _ = (A ^ q * B ^ (q * (p / 4))) * ∑ x ∈ E, M x ^ p := by rw [Finset.mul_sum]
      _ ≤ _ := by
          have := hstrong D E g hg0
          gcongr
  have hfinal : A ^ q * B ^ (q * (p / 4)) * (Cs * S) = (A * Cs ^ (1 / q) * B) ^ q := by
    rw [Real.mul_rpow (by positivity) hB0, Real.mul_rpow hApos.le (by positivity),
      ← Real.rpow_mul hCs.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
    have : B ^ q = B ^ (q * (p / 4)) * S := by
      rw [← hBp]
      nth_rw 1 [← hq2]
      rcases hB0.eq_or_lt with h0 | hpos
      · rw [← h0]
        rw [Real.zero_rpow (by positivity), Real.zero_rpow hp0.ne']
        simp
      · rw [Real.rpow_add hpos]
    rw [this]
    ring
  rw [hfinal] at hsum
  calc _ ≤ ((A * Cs ^ (1 / q) * B) ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun x _ => by positivity) hsum (by positivity)
    _ = _ := by
        rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hq0.ne', Real.rpow_one]
end LatticeFractionalIntegration
end YangMills.Construction
end
