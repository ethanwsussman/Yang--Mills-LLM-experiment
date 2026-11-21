import YangMills.Construction.FreeEnergiesOfTheFlow.SumOverTheLevelsOfTheFlow
import YangMills.Construction.ResponseInTheExpansion.ManyLevelsOfSeveralSupportsProof
import YangMills.Construction.ResponseInTheExpansion.SitesOfAFunctionAtALevelProof
import YangMills.Construction.TransfersOffTheWalk.ProductsLevelByLevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TransfersOffTheWalk
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion YangMills.Construction.FreeEnergies YangMills.Construction.ClusterExpansionOfAStep
namespace SeparatedProducts
section
variable {p : ℕ} (L : ℕ) [NeZero L] (c : (t n : ℕ) → [NeZero n] → Fin p → ℝ) (C C₀ rt : ℝ) (Dr : ℕ → ℝ)
private def levelIncrement (I : Finset (Fin p)) (t n : ℕ) [NeZero n] : ℝ :=
  C * (∑ i ∈ I, c t (n * L) i) ^ 2 * Real.exp (-(rt * Dr t / 2 ^ 7)) * ∏ i ∈ I, (4 * (C₀ * c t (n * L) i))
private def productError (g : ℕ → Finset (Fin p) → ℝ) : (t n : ℕ) → [NeZero n] → Finset (Fin p) → ℝ
  | 0, _, _, _ => 0
  | t + 1, n, _, I => levelIncrement L c C C₀ rt Dr I t n +
      g t I * ∑ J ∈ I.powerset, productError g t (n * L) J * ∏ i ∈ I \ J, (2 * (C₀ * c t (n * L) i))
private def heldBound (m : ℕ → ℝ) : (t n : ℕ) → [NeZero n] → Finset (Fin p) → ℝ
  | 0, _, _, _ => 0
  | t + 1, n, _, I => heldBound m t (n * L) I * (m t * (3 / 2 : ℝ) ^ I.card) + levelIncrement L c C C₀ rt Dr I t n
private def levelSpread (I : Finset (Fin p)) : (t n : ℕ) → [NeZero n] → ℕ → ℝ
  | 0, _, _, _ => 0
  | t + 1, n, _, k => levelSpread I t (n * L) (k + 1) + (3 / 2 : ℝ) ^ (I.card * k) * levelIncrement L c C C₀ rt Dr I t n
variable {L c C C₀ rt Dr}
private theorem levelIncrement_nonneg (hc : ∀ (t n : ℕ) [NeZero n] (i : Fin p), 0 ≤ c t n i) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (I : Finset (Fin p)) (t n : ℕ) [NeZero n] : 0 ≤ levelIncrement L c C C₀ rt Dr I t n := by
  unfold levelIncrement
  have h1 : 0 ≤ ∏ i ∈ I, (4 * (C₀ * c t (n * L) i)) := Finset.prod_nonneg fun i _ =>
    mul_nonneg (by norm_num) (mul_nonneg hC₀ (hc t (n * L) i))
  exact mul_nonneg (mul_nonneg (mul_nonneg hC (sq_nonneg _)) (Real.exp_pos _).le) h1
private theorem heldBound_nonneg (hc : ∀ (t n : ℕ) [NeZero n] (i : Fin p), 0 ≤ c t n i) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    {m : ℕ → ℝ} (hm : ∀ t, 0 ≤ m t) : ∀ (t n : ℕ) [NeZero n] (I : Finset (Fin p)), 0 ≤ heldBound L c C C₀ rt Dr m t n I := by
  intro t
  induction t with
  | zero => intro n _ I; simp [heldBound]
  | succ t ih =>
    intro n _ I
    simp only [heldBound]
    exact add_nonneg (mul_nonneg (ih (n * L) I) (mul_nonneg (hm t) (by positivity))) (levelIncrement_nonneg hc hC hC₀ I t n)
private theorem productError_nonneg (hc : ∀ (t n : ℕ) [NeZero n] (i : Fin p), 0 ≤ c t n i) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    {g : ℕ → Finset (Fin p) → ℝ} (hg : ∀ t I, 0 ≤ g t I) :
    ∀ (t n : ℕ) [NeZero n] (I : Finset (Fin p)), 0 ≤ productError L c C C₀ rt Dr g t n I := by
  intro t
  induction t with
  | zero => intro n _ I; simp [productError]
  | succ t ih =>
    intro n _ I
    simp only [productError]
    refine add_nonneg (levelIncrement_nonneg hc hC hC₀ I t n) (mul_nonneg (hg t I) (Finset.sum_nonneg fun J _ => ?_))
    exact mul_nonneg (ih (n * L) J) (Finset.prod_nonneg fun i _ =>
      mul_nonneg (by norm_num) (mul_nonneg hC₀ (hc t (n * L) i)))
private theorem increment_mul_prod_le (C' E C₀' : ℝ) (hC : 0 ≤ C') (hE : 0 ≤ E) (hC₀ : 0 ≤ C₀') {I J : Finset (Fin p)}
    (hJ : J ⊆ I) (a cc : Fin p → ℝ) (ha : ∀ i, 0 ≤ a i) (hcc0 : ∀ i, 0 ≤ cc i)
    (hcc : ∀ i ∈ I \ J, cc i ≤ 2 * (C₀' * a i)) :
    C' * (∑ i ∈ J, a i) ^ 2 * E * (∏ i ∈ J, (4 * (C₀' * a i))) * ∏ i ∈ I \ J, cc i ≤
      (1 / 2 : ℝ) ^ (I \ J).card * (C' * (∑ i ∈ I, a i) ^ 2 * E * ∏ i ∈ I, (4 * (C₀' * a i))) := by
  have hS : ∑ i ∈ J, a i ≤ ∑ i ∈ I, a i := Finset.sum_le_sum_of_subset_of_nonneg hJ fun i _ _ => ha i
  have hS0 : 0 ≤ ∑ i ∈ J, a i := Finset.sum_nonneg fun i _ => ha i
  have hSq : (∑ i ∈ J, a i) ^ 2 ≤ (∑ i ∈ I, a i) ^ 2 := pow_le_pow_left₀ hS0 hS 2
  have hP0 : 0 ≤ ∏ i ∈ J, (4 * (C₀' * a i)) := Finset.prod_nonneg fun i _ =>
    mul_nonneg (by norm_num) (mul_nonneg hC₀ (ha i))
  have hQ0 : 0 ≤ ∏ i ∈ I \ J, cc i := Finset.prod_nonneg fun i _ => hcc0 i
  have hQ : ∏ i ∈ I \ J, cc i ≤ (1 / 2 : ℝ) ^ (I \ J).card * ∏ i ∈ I \ J, (4 * (C₀' * a i)) := by
    calc ∏ i ∈ I \ J, cc i ≤ ∏ i ∈ I \ J, ((1 / 2 : ℝ) * (4 * (C₀' * a i))) :=
          Finset.prod_le_prod (fun i _ => hcc0 i) fun i hi => by
            have := hcc i hi
            linarith
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hI : ∏ i ∈ I, (4 * (C₀' * a i)) = (∏ i ∈ I \ J, (4 * (C₀' * a i))) * ∏ i ∈ J, (4 * (C₀' * a i)) :=
    (Finset.prod_sdiff hJ).symm
  rw [hI]
  have hA : C' * (∑ i ∈ J, a i) ^ 2 * E * ∏ i ∈ J, (4 * (C₀' * a i)) ≤
      C' * (∑ i ∈ I, a i) ^ 2 * E * ∏ i ∈ J, (4 * (C₀' * a i)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSq hC) hE) hP0
  have hB0 : 0 ≤ C' * (∑ i ∈ I, a i) ^ 2 * E * ∏ i ∈ J, (4 * (C₀' * a i)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (sq_nonneg _)) hE) hP0
  calc _ ≤ C' * (∑ i ∈ I, a i) ^ 2 * E * (∏ i ∈ J, (4 * (C₀' * a i))) *
        ((1 / 2 : ℝ) ^ (I \ J).card * ∏ i ∈ I \ J, (4 * (C₀' * a i))) := mul_le_mul hA hQ hQ0 hB0
    _ = _ := by ring
private theorem levelIncrement_mul_prod_le (hc : ∀ (t n : ℕ) [NeZero n] (i : Fin p), 0 ≤ c t n i) (hC : 0 ≤ C)
    (hC₀ : 0 ≤ C₀) {I J : Finset (Fin p)} (hJ : J ⊆ I) (t n : ℕ) [NeZero n] (cc : Fin p → ℝ) (hcc0 : ∀ i, 0 ≤ cc i)
    (hcc : ∀ i ∈ I \ J, cc i ≤ 2 * (C₀ * c t (n * L) i)) :
    levelIncrement L c C C₀ rt Dr J t n * ∏ i ∈ I \ J, cc i ≤
      (1 / 2 : ℝ) ^ (I \ J).card * levelIncrement L c C C₀ rt Dr I t n :=
  increment_mul_prod_le C _ C₀ hC (Real.exp_pos _).le hC₀ hJ (fun i => c t (n * L) i) cc (fun i => hc t (n * L) i)
    hcc0 hcc
private theorem heldBound_mul_prod_le (hc : ∀ (t n : ℕ) [NeZero n] (i : Fin p), 0 ≤ c t n i)
    (hmono : ∀ (t n : ℕ) [NeZero n] (i : Fin p), c (t + 1) n i ≤ c t (n * L) i) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    {m : ℕ → ℝ} (hm : ∀ t, 0 ≤ m t) :
    ∀ (t n : ℕ) [NeZero n] {I J : Finset (Fin p)} (_ : J ⊆ I) (cc : Fin p → ℝ) (_ : ∀ i, 0 ≤ cc i)
      (_ : ∀ i ∈ I \ J, cc i ≤ 2 * (C₀ * c t n i)),
      heldBound L c C C₀ rt Dr m t n J * ∏ i ∈ I \ J, cc i ≤
        (1 / 2 : ℝ) ^ (I \ J).card * heldBound L c C C₀ rt Dr m t n I := by
  intro t
  induction t with
  | zero => intro n _ I J _ cc _ _; simp [heldBound]
  | succ t ih =>
    intro n _ I J hJ cc h0 hcc
    have hcc' : ∀ i ∈ I \ J, cc i ≤ 2 * (C₀ * c t (n * L) i) := fun i hi =>
      (hcc i hi).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hmono t n i) hC₀) (by norm_num))
    have h1 := ih (n * L) hJ cc h0 hcc'
    have h2 := levelIncrement_mul_prod_le (L := L) (rt := rt) (Dr := Dr) hc hC hC₀ hJ t n cc h0 hcc'
    have hpow : (3 / 2 : ℝ) ^ J.card ≤ (3 / 2 : ℝ) ^ I.card :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hJ)
    have hHI := heldBound_nonneg (L := L) (rt := rt) (Dr := Dr) hc hC hC₀ hm t (n * L) I
    simp only [heldBound]
    calc _ = (heldBound L c C C₀ rt Dr m t (n * L) J * ∏ i ∈ I \ J, cc i) * (m t * (3 / 2 : ℝ) ^ J.card) +
          levelIncrement L c C C₀ rt Dr J t n * ∏ i ∈ I \ J, cc i := by ring
      _ ≤ ((1 / 2 : ℝ) ^ (I \ J).card * heldBound L c C C₀ rt Dr m t (n * L) I) * (m t * (3 / 2 : ℝ) ^ I.card) +
          (1 / 2 : ℝ) ^ (I \ J).card * levelIncrement L c C C₀ rt Dr I t n :=
        add_le_add (mul_le_mul h1 (mul_le_mul_of_nonneg_left hpow (hm t))
          (mul_nonneg (hm t) (by positivity)) (by positivity)) h2
      _ = _ := by ring
private theorem sum_powerset_half_pow [DecidableEq (Fin p)] (I : Finset (Fin p)) :
    ∑ J ∈ I.powerset, (1 / 2 : ℝ) ^ (I \ J).card = (3 / 2 : ℝ) ^ I.card := by
  have h := Finset.prod_add (fun _ : Fin p => (1 : ℝ)) (fun _ : Fin p => (1 / 2 : ℝ)) I
  have e : ∏ _i ∈ I, ((1 : ℝ) + 1 / 2) = (3 / 2 : ℝ) ^ I.card := by
    rw [Finset.prod_const]
    norm_num
  rw [← e, h]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp
private theorem productError_le_heldBound (hc : ∀ (t n : ℕ) [NeZero n] (i : Fin p), 0 ≤ c t n i)
    (hmono : ∀ (t n : ℕ) [NeZero n] (i : Fin p), c (t + 1) n i ≤ c t (n * L) i) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    {m : ℕ → ℝ} (hm : ∀ t, 0 ≤ m t) {g : ℕ → Finset (Fin p) → ℝ} (hg0 : ∀ t I, 0 ≤ g t I) (hg : ∀ t I, g t I ≤ m t) :
    ∀ (t n : ℕ) [NeZero n] (I : Finset (Fin p)),
      productError L c C C₀ rt Dr g t n I ≤ heldBound L c C C₀ rt Dr m t n I := by
  intro t
  induction t with
  | zero => intro n _ I; simp [productError, heldBound]
  | succ t ih =>
    intro n _ I
    have hcc0 : ∀ i, 0 ≤ 2 * (C₀ * c t (n * L) i) := fun i =>
      mul_nonneg (by norm_num) (mul_nonneg hC₀ (hc t (n * L) i))
    have hterm : ∀ J ∈ I.powerset,
        productError L c C C₀ rt Dr g t (n * L) J * ∏ i ∈ I \ J, (2 * (C₀ * c t (n * L) i)) ≤
        (1 / 2 : ℝ) ^ (I \ J).card * heldBound L c C C₀ rt Dr m t (n * L) I := fun J hJ =>
      (mul_le_mul_of_nonneg_right (ih (n * L) J) (Finset.prod_nonneg fun i _ => hcc0 i)).trans
        (heldBound_mul_prod_le hc hmono hC hC₀ hm t (n * L) (Finset.mem_powerset.1 hJ) _ hcc0 fun i _ => le_rfl)
    have hsum : ∑ J ∈ I.powerset, productError L c C C₀ rt Dr g t (n * L) J * ∏ i ∈ I \ J, (2 * (C₀ * c t (n * L) i)) ≤
        (3 / 2 : ℝ) ^ I.card * heldBound L c C C₀ rt Dr m t (n * L) I := by
      calc _ ≤ ∑ J ∈ I.powerset, (1 / 2 : ℝ) ^ (I \ J).card * heldBound L c C C₀ rt Dr m t (n * L) I :=
            Finset.sum_le_sum hterm
        _ = _ := by rw [← Finset.sum_mul, sum_powerset_half_pow]
    have hs0 : 0 ≤ ∑ J ∈ I.powerset,
        productError L c C C₀ rt Dr g t (n * L) J * ∏ i ∈ I \ J, (2 * (C₀ * c t (n * L) i)) :=
      Finset.sum_nonneg fun J _ => mul_nonneg (productError_nonneg hc hC hC₀ hg0 t (n * L) J)
        (Finset.prod_nonneg fun i _ => hcc0 i)
    simp only [productError, heldBound]
    have := mul_le_mul (hg t I) hsum hs0 (hm t)
    linarith
private theorem heldBound_le_levelSpread (hc : ∀ (t n : ℕ) [NeZero n] (i : Fin p), 0 ≤ c t n i) (hC : 0 ≤ C)
    (hC₀ : 0 ≤ C₀) {ε : ℕ → ℝ} (hε : ∀ t, 0 ≤ ε t) (I : Finset (Fin p)) :
    ∀ (t n : ℕ) [NeZero n] (k : ℕ),
      heldBound L c C C₀ rt Dr (fun t => Real.exp (ε t)) t n I * (3 / 2 : ℝ) ^ (I.card * k) ≤
        Real.exp (∑ v ∈ Finset.range t, ε v) * levelSpread L c C C₀ rt Dr I t n k := by
  intro t
  induction t with
  | zero => intro n _ k; simp [heldBound, levelSpread]
  | succ t ih =>
    intro n _ k
    have h1 := ih (n * L) (k + 1)
    have hE : Real.exp (∑ v ∈ Finset.range (t + 1), ε v) =
        Real.exp (∑ v ∈ Finset.range t, ε v) * Real.exp (ε t) := by
      rw [Finset.sum_range_succ, Real.exp_add]
    have hone : 1 ≤ Real.exp (∑ v ∈ Finset.range (t + 1), ε v) :=
      Real.one_le_exp (Finset.sum_nonneg fun v _ => hε v)
    have hst := levelIncrement_nonneg (L := L) (rt := rt) (Dr := Dr) hc hC hC₀ I t n
    have hk : (3 / 2 : ℝ) ^ (I.card * (k + 1)) = (3 / 2 : ℝ) ^ (I.card * k) * (3 / 2 : ℝ) ^ I.card := by
      rw [Nat.mul_add, pow_add, mul_one]
    have hp : 0 ≤ (3 / 2 : ℝ) ^ (I.card * k) * levelIncrement L c C C₀ rt Dr I t n := mul_nonneg (by positivity) hst
    simp only [heldBound, levelSpread]
    calc _ = (heldBound L c C C₀ rt Dr (fun t => Real.exp (ε t)) t (n * L) I * (3 / 2 : ℝ) ^ (I.card * (k + 1))) *
          Real.exp (ε t) + (3 / 2 : ℝ) ^ (I.card * k) * levelIncrement L c C C₀ rt Dr I t n := by rw [hk]; ring
      _ ≤ (Real.exp (∑ v ∈ Finset.range t, ε v) * levelSpread L c C C₀ rt Dr I t (n * L) (k + 1)) * Real.exp (ε t) +
          Real.exp (∑ v ∈ Finset.range (t + 1), ε v) *
            ((3 / 2 : ℝ) ^ (I.card * k) * levelIncrement L c C C₀ rt Dr I t n) :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) (le_mul_of_one_le_left hp hone)
      _ = _ := by rw [hE]; ring
private theorem sq_le_two_pow_succ (k : ℕ) : k ^ 2 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h := Nat.lt_two_pow_self (n := k)
    have e : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    have e' : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [e]
    nlinarith
private theorem three_halves_pow_le_exp (P : ℕ) {c' Lr : ℝ} (hc : 0 < c') (hL : 2 ≤ Lr) (k : ℕ) :
    (3 / 2 : ℝ) ^ (P * k) ≤ Real.exp ((P : ℝ) ^ 2 / (2 * c')) * Real.exp (c' * Lr ^ k) := by
  have h1 : (3 / 2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h2 : (3 / 2 : ℝ) ^ (P * k) ≤ Real.exp ((P : ℝ) * k) := by
    calc (3 / 2 : ℝ) ^ (P * k) ≤ (Real.exp 1) ^ (P * k) := pow_le_pow_left₀ (by norm_num) h1 _
      _ = Real.exp ((P : ℝ) * k) := by
        rw [← Real.exp_nat_mul]
        push_cast
        ring_nf
  refine h2.trans ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  have hk2 : ((k : ℝ)) ^ 2 ≤ 2 * Lr ^ k := by
    have a : ((k ^ 2 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast sq_le_two_pow_succ k
    push_cast at a
    have b : (2 : ℝ) ^ k ≤ Lr ^ k := pow_le_pow_left₀ (by norm_num) hL k
    have e : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    linarith
  have hmain : (P : ℝ) * k ≤ (P : ℝ) ^ 2 / (2 * c') + c' * (k : ℝ) ^ 2 / 2 := by
    have e : (P : ℝ) ^ 2 / (2 * c') + c' * (k : ℝ) ^ 2 / 2 - (P : ℝ) * k = ((P : ℝ) - c' * k) ^ 2 / (2 * c') := by
      field_simp
      ring
    have : 0 ≤ ((P : ℝ) - c' * k) ^ 2 / (2 * c') := by positivity
    linarith
  have : c' * (k : ℝ) ^ 2 / 2 ≤ c' * Lr ^ k := by nlinarith
  linarith
private theorem three_halves_pow_mul_exp_le (P : ℕ) {rt' Lr Dn D₀ : ℝ} (hrt : 0 < rt') (hL : 2 ≤ Lr) (k : ℕ)
    (hD : D₀ ≤ Dn) (h8 : 8 * Lr ^ k ≤ Dn) :
    (3 / 2 : ℝ) ^ (P * k) * Real.exp (-(rt' * Dn / 2 ^ 7)) ≤
      Real.exp ((P : ℝ) ^ 2 / (2 * (rt' / 2 ^ 5))) * Real.exp (-(rt' * D₀ / 2 ^ 8)) := by
  have hc : 0 < rt' / 2 ^ 5 := by positivity
  have h1 := three_halves_pow_le_exp P hc hL k
  have h2 : Real.exp (rt' / 2 ^ 5 * Lr ^ k) * Real.exp (-(rt' * Dn / 2 ^ 7)) ≤ Real.exp (-(rt' * D₀ / 2 ^ 8)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith
  calc _ ≤ (Real.exp ((P : ℝ) ^ 2 / (2 * (rt' / 2 ^ 5))) * Real.exp (rt' / 2 ^ 5 * Lr ^ k)) *
        Real.exp (-(rt' * Dn / 2 ^ 7)) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((P : ℝ) ^ 2 / (2 * (rt' / 2 ^ 5))) *
        (Real.exp (rt' / 2 ^ 5 * Lr ^ k) * Real.exp (-(rt' * Dn / 2 ^ 7))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
end
section
private theorem supDist_fineBlock_bounds (L : ℕ) [NeZero L] (hL : Odd L) (t n : ℕ) [NeZero n] {y y' : TorusSite n}
    {c c' : TorusSite (fineSide L t n)} (hc : c ∈ fineBlock L t n y) (hc' : c' ∈ fineBlock L t n y') :
    _root_.YangMills.Construction.TorusFields.supDist c c' + 1 ≤ L ^ t * _root_.YangMills.Construction.TorusFields.supDist y y' + L ^ t ∧ L ^ t * _root_.YangMills.Construction.TorusFields.supDist y y' + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist c c' + L ^ t := by apply _root_.YangMills.SharedProofs.p19253 <;> assumption
private theorem side_mul_supDist_parent_le (L : ℕ) [NeZero L] (hL : Odd L) (n : ℕ) [NeZero n] (a a' : TorusSite (n * L)) :
    L * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L a) (parentBlock L a') + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist a a' + L := by
  have hm : ∀ x : TorusSite (n * L), x ∈ fineBlock L 1 n (parentBlock L x) := by
    intro x
    rw [fineBlock]
    exact Finset.mem_biUnion.2 ⟨x, by simp [sitesInBlocks], Finset.mem_singleton_self _⟩
  have h := (supDist_fineBlock_bounds L hL 1 n (hm a) (hm a')).2
  rw [pow_one] at h
  exact h
end
section
set_option linter.unusedSectionVars false
variable {L : ℕ} [NeZero L]
open Classical in
private theorem image_parentBlock_weightSupportSites {t n : ℕ} [NeZero n] (f : PlaquetteWeight (fineSide L (t + 1) n)) :
    (weightSupportSites L t (n * L) f).image (parentBlock L) = weightSupportSites L (t + 1) n f := by apply _root_.YangMills.SharedProofs.p19152 <;> assumption
private theorem weightLipschitz_le_succ (hL : 1 ≤ L) (t : ℕ) {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    weightLipschitz L t h ≤ weightLipschitz L (t + 1) h := by apply _root_.YangMills.SharedProofs.p58015 <;> assumption
private theorem weightNorm_le_succ (hL : 1 ≤ L) (t : ℕ) {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    weightNorm L t h ≤ weightNorm L (t + 1) h :=
  max_le_max le_rfl (weightLipschitz_le_succ hL t h)
private theorem parentBlock_mem_functionSites {t n : ℕ} [NeZero n] {f : FinePlaquetteFunction} {y : TorusSite (n * L)}
    (h : y ∈ functionSites L f t (n * L)) : parentBlock L y ∈ functionSites L f (t + 1) n := by
  classical
  have hs := image_parentBlock_weightSupportSites (L := L) (t := t) (n := n) (fineWeight f (fineSide L (t + 1) n))
  have h1 : parentBlock L y ∈
      (weightSupportSites L t (n * L) (fineWeight f (fineSide L (t + 1) n))).image (parentBlock L) :=
    Finset.mem_image_of_mem _ h
  rw [hs] at h1
  exact h1
private theorem card_functionSites_succ_le {t n : ℕ} [NeZero n] (f : FinePlaquetteFunction) :
    ((functionSites L f (t + 1) n).card : ℝ) ≤ ((functionSites L f t (n * L)).card : ℝ) := by
  classical
  have hs := image_parentBlock_weightSupportSites (L := L) (t := t) (n := n) (fineWeight f (fineSide L (t + 1) n))
  have h1 : (weightSupportSites L (t + 1) n (fineWeight f (fineSide L (t + 1) n))).card ≤
      (weightSupportSites L t (n * L) (fineWeight f (fineSide L (t + 1) n))).card := by
    rw [← hs]
    exact Finset.card_image_le
  exact_mod_cast h1
private theorem one_le_meanSiteScore {n : ℕ} [NeZero n] {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w)
    (B Y : Finset (TorusSite n)) (ω : Y → Ω) : 1 ≤ meanSiteScore s B Y ω := by apply _root_.YangMills.SharedProofs.p16546 <;> assumption
end
section
variable {p : ℕ}
private def widenedDist (L s : ℕ) (D : ℕ → ℝ) (u : ℕ) : ℕ := ⌈max (D u) (8 * (L : ℝ) ^ (s - 1 - u))⌉₊
private theorem le_widenedDist (L s : ℕ) (D : ℕ → ℝ) (u : ℕ) : D u ≤ (widenedDist L s D u : ℝ) :=
  (le_max_left _ _).trans (Nat.le_ceil _)
private theorem eight_le_widenedDist (L s : ℕ) (D : ℕ → ℝ) (u : ℕ) :
    8 * (L : ℝ) ^ (s - 1 - u) ≤ (widenedDist L s D u : ℝ) :=
  (le_max_right _ _).trans (Nat.le_ceil _)
private theorem separated_widen_aux (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hL : Odd ℓ.side) (x D : ℕ → ℝ)
    (f : Fin p → FinePlaquetteFunction) (s : ℕ) :
    ∀ (t n : ℕ) [NeZero n] (k : ℕ), t + k = s →
      (∀ i j, i ≠ j → ∀ y ∈ functionSites ℓ.side (f i) t n, ∀ y' ∈ functionSites ℓ.side (f j) t n,
        12 * ℓ.side ^ k + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist y y') →
      SeparatedAlongTower ℓ x D t n (fun i => fineWeight (f i) (fineSide ℓ.side t n)) →
      SeparatedAlongTower ℓ x (fun u => (widenedDist ℓ.side s D u : ℝ)) t n
        (fun i => fineWeight (f i) (fineSide ℓ.side t n)) := by
  intro t
  induction t with
  | zero => intro n _ k _ _ _; trivial
  | succ t ih =>
    intro n _ k hk hd hA
    obtain ⟨⟨hr, h8, hsep⟩, hrest⟩ := hA
    refine ⟨⟨hr.trans (le_widenedDist _ _ _ _), lt_of_lt_of_le h8 (le_widenedDist _ _ _ _), ?_⟩,
      ih (n * ℓ.side) (k + 1) (by omega) ?_ hrest⟩
    · intro i j hij y hy y' hy'
      have h1 := hsep i j hij y hy y' hy'
      have h2 := hd i j hij y hy y' hy'
      have hLk : 1 ≤ ℓ.side ^ k := Nat.one_le_pow _ _ (NeZero.pos _)
      have h5 : 4 ≤ _root_.YangMills.Construction.TorusFields.supDist y y' := by omega
      have hk' : s - 1 - t = k := by omega
      have hc : ((_root_.YangMills.Construction.TorusFields.supDist y y' - 4 : ℕ) : ℝ) = (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) - 4 := by
        rw [Nat.cast_sub h5]
        norm_num
      have hmax : max (D t) (8 * (ℓ.side : ℝ) ^ (s - 1 - t)) ≤ ((_root_.YangMills.Construction.TorusFields.supDist y y' - 4 : ℕ) : ℝ) := by
        rw [hc, hk']
        refine max_le (by linarith) ?_
        have a : ((12 * ℓ.side ^ k + 1 : ℕ) : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) := by exact_mod_cast h2
        push_cast at a
        have b : (1 : ℝ) ≤ (ℓ.side : ℝ) ^ k := by exact_mod_cast hLk
        linarith
      have h3 : widenedDist ℓ.side s D t ≤ _root_.YangMills.Construction.TorusFields.supDist y y' - 4 := Nat.ceil_le.2 hmax
      have h4 : widenedDist ℓ.side s D t + 4 ≤ _root_.YangMills.Construction.TorusFields.supDist y y' := by omega
      show (widenedDist ℓ.side s D t : ℝ) + 4 ≤ (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ)
      exact_mod_cast h4
    · intro i j hij a ha a' ha'
      have hp := side_mul_supDist_parent_le ℓ.side hL n a a'
      have hd' := hd i j hij _ (parentBlock_mem_functionSites ha) _ (parentBlock_mem_functionSites ha')
      have h := Nat.mul_le_mul_left ℓ.side hd'
      have e : ℓ.side * (12 * ℓ.side ^ k + 1) = 12 * ℓ.side ^ (k + 1) + ℓ.side := by ring
      omega
private theorem separated_widen (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hL : Odd ℓ.side) (x D : ℕ → ℝ)
    (f : Fin p → FinePlaquetteFunction) (s n : ℕ) [NeZero n]
    (hA : SeparatedAlongTower ℓ x D s n (fun i => fineWeight (f i) (fineSide ℓ.side s n))) :
    SeparatedAlongTower ℓ x (fun u => (widenedDist ℓ.side s D u : ℝ)) s n
      (fun i => fineWeight (f i) (fineSide ℓ.side s n)) := by
  cases s with
  | zero => trivial
  | succ s' =>
    refine separated_widen_aux ℓ hL x D f (s' + 1) (s' + 1) n 0 (by omega) ?_ hA
    intro i j hij y hy y' hy'
    obtain ⟨⟨_, h8, hsep⟩, _⟩ := hA
    have h1 := hsep i j hij y hy y' hy'
    have h2 : (12 : ℝ) < (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ) := by linarith
    have h3 : 12 < _root_.YangMills.Construction.TorusFields.supDist y y' := by exact_mod_cast h2
    simp only [pow_zero, mul_one]
    omega
private def siteCounts (L : ℕ) [NeZero L] (f : Fin p → FinePlaquetteFunction) : (t n : ℕ) → [NeZero n] → Fin p → ℝ :=
  fun t n _ i => ((functionSites L (f i) t n).card : ℝ)
private theorem levelSpread_nonneg {L : ℕ} [NeZero L] {c : (t n : ℕ) → [NeZero n] → Fin p → ℝ} {C C₀ rt : ℝ}
    {Dr : ℕ → ℝ} (hc : ∀ (t n : ℕ) [NeZero n] (i : Fin p), 0 ≤ c t n i) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (I : Finset (Fin p)) : ∀ (t n : ℕ) [NeZero n] (k : ℕ), 0 ≤ levelSpread L c C C₀ rt Dr I t n k := by
  intro t
  induction t with
  | zero => intro n _ k; simp [levelSpread]
  | succ t ih =>
    intro n _ k
    simp only [levelSpread]
    exact add_nonneg (ih (n * L) (k + 1)) (mul_nonneg (by positivity) (levelIncrement_nonneg hc hC hC₀ I t n))
private theorem levelSpread_le_separationError (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (f : Fin p → FinePlaquetteFunction) {C A E C₀ : ℝ}
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hE : 0 ≤ E) {Dr D₀ : ℕ → ℝ} (s : ℕ)
    (hrate : ∀ u k, u + 1 + k = s → (3 / 2 : ℝ) ^ (p * k) * Real.exp (-(ℓ.rt * Dr u / 2 ^ 7)) ≤
      A * Real.exp (-(ℓ.rt * D₀ u / 2 ^ 8))) :
    ∀ (t n : ℕ) [NeZero n] (k : ℕ), t + k = s →
      E * levelSpread ℓ.side (siteCounts ℓ.side f) C C₀ ℓ.rt Dr Finset.univ t n k ≤
        separationError ℓ (E * (C * A)) C₀ D₀ t n (fun i => fineWeight (f i) (fineSide ℓ.side t n)) := by
  intro t
  induction t with
  | zero => intro n _ k _; simp [levelSpread, separationError]
  | succ t ih =>
    intro n _ k hk
    have h1 := ih (n * ℓ.side) (k + 1) (by omega)
    have h2 := hrate t k (by omega)
    have hterm : E * ((3 / 2 : ℝ) ^ ((Finset.univ : Finset (Fin p)).card * k) *
        levelIncrement ℓ.side (siteCounts ℓ.side f) C C₀ ℓ.rt Dr Finset.univ t n) ≤
      E * (C * A) * (∑ i, ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) ^ 2 *
        Real.exp (-(ℓ.rt * D₀ t / 2 ^ 8)) *
        ∏ i, (4 * C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) := by
      have hP : ∏ i, (4 * (C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ))) =
          ∏ i, (4 * C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) :=
        Finset.prod_congr rfl fun i _ => by ring
      have hP0 : 0 ≤ ∏ i, (4 * C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) :=
        Finset.prod_nonneg fun i _ => mul_nonneg (by positivity) (Nat.cast_nonneg _)
      simp only [Finset.card_univ, Fintype.card_fin]
      unfold levelIncrement siteCounts
      rw [hP]
      have hB : 0 ≤ E * C * (∑ i, ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) ^ 2 *
          ∏ i, (4 * C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hE hC) (sq_nonneg _)) hP0
      calc _ = (E * C * (∑ i, ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) ^ 2 *
            ∏ i, (4 * C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ))) *
            ((3 / 2 : ℝ) ^ (p * k) * Real.exp (-(ℓ.rt * Dr t / 2 ^ 7))) := by ring
        _ ≤ (E * C * (∑ i, ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) ^ 2 *
            ∏ i, (4 * C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ))) *
            (A * Real.exp (-(ℓ.rt * D₀ t / 2 ^ 8))) := mul_le_mul_of_nonneg_left h2 hB
        _ = _ := by ring
    have e : separationError ℓ (E * (C * A)) C₀ D₀ (t + 1) n
        (fun i => fineWeight (f i) (fineSide ℓ.side (t + 1) n)) =
        separationError ℓ (E * (C * A)) C₀ D₀ t (n * ℓ.side)
          (fun i => fineWeight (f i) (fineSide ℓ.side t (n * ℓ.side))) +
          E * (C * A) * (∑ i, ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) ^ 2 *
            Real.exp (-(ℓ.rt * D₀ t / 2 ^ 8)) *
            ∏ i, (4 * C₀ * ((functionSites ℓ.side (f i) t (n * ℓ.side)).card : ℝ)) := rfl
    rw [e]
    simp only [levelSpread]
    rw [mul_add]
    exact add_le_add h1 hterm
end
private theorem followsFlow_mono {Tb : ParameterAssignment} {y : ℝ} {T : StageTower (Tb.stepParameters y)}
    {S : ScoredStageTower T} {β : ℝ} {tp t : ℕ} (h : S.FollowsFlow β tp) (ht : t ≤ tp) : S.FollowsFlow β t where
  isFlowStep := fun u hu => h.isFlowStep u (hu.trans ht)
  startsAtWilson := h.startsAtWilson
  bottom_coupling := h.bottom_coupling
  isCutoff_bottom := h.isCutoff_bottom
  marksMeasurable := h.marksMeasurable
  params_eq := h.params_eq
  N₀_eq := h.N₀_eq
  coeff_zero := h.coeff_zero
  score_zero := h.score_zero
  cold_zero := h.cold_zero
  hull_zero := h.hull_zero
  score_succ := fun u hu => h.score_succ u (lt_of_lt_of_le hu ht)
  cold_succ := fun u hu => h.cold_succ u (lt_of_lt_of_le hu ht)
  hull_succ := fun u hu => h.hull_succ u (lt_of_lt_of_le hu ht)
  isAdmissible := fun u hu => h.isAdmissible u (hu.trans ht)
  coeff_near_one := fun u hu => h.coeff_near_one u (hu.trans ht)
private theorem atResponseParameters_of_two {P Q R : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (hP : AtResponseParameters P) (hQ : AtResponseParameters Q)
    (H : ∀ T K y, T.Admissible → P T K y → Q T K y → R T K y) : AtResponseParameters R := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, h₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, hr₂, h₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hodd hL T hTa hTL hD hcs hOn hrt hC K
  obtain ⟨y₁, hy₁⟩ := h₁ L hodd ((le_max_left _ _).trans hL) T hTa hTL hD hcs hOn
    (hrt.trans (min_le_left _ _)) ((le_max_left _ _).trans hC) K
  obtain ⟨y₂, hy₂⟩ := h₂ L hodd ((le_max_right _ _).trans hL) T hTa hTL hD hcs hOn
    (hrt.trans (min_le_right _ _)) ((le_max_right _ _).trans hC) K
  exact ⟨max y₁ y₂, fun y hy hR => H T K y hD (hy₁ y ((le_max_left _ _).trans hy) hR)
    (hy₂ y ((le_max_right _ _).trans hy) hR)⟩
end SeparatedProducts
open SeparatedProducts in
theorem separatedProductsStatement_holds (hP : productInductionStatement) (hS : levelSumBoundStatement) :
    separatedProductsStatement := by
  refine atResponseParameters_of_two hP hS ?_
  intro Tb Kr y hD h₁ h₂ p
  obtain ⟨C, hC, hr⟩ := h₁ p
  have hrt : 0 < (Tb.stepParameters y).rt := hD.rt_pos
  have hL2n : 2 ≤ (Tb.stepParameters y).side := le_trans (by norm_num) hD.L_ge
  have hL2 : (2 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by exact_mod_cast hL2n
  have hL1 : 1 ≤ (Tb.stepParameters y).side := by omega
  have hodd : Odd (Tb.stepParameters y).side := hD.L_odd
  refine ⟨Real.exp (2 ^ p * (p.factorial : ℝ)) *
    (C * Real.exp ((p : ℝ) ^ 2 / (2 * ((Tb.stepParameters y).rt / 2 ^ 5)))), by positivity, ?_⟩
  intro T S β s n _ D f hK hrun hreach hblock hsize hap
  obtain ⟨hHad, hBase, hStep⟩ := hr T S β f hK
  refine ⟨hHad s n Finset.univ hrun hreach hblock, ?_⟩
  have hC₀ : 0 ≤ Kr.C₀ := by
    have hfit := (hrun.isAdmissible 0 (Nat.zero_le s)).params_admissible
    have hk : (S.setup 0).responseParams = Kr := (hrun.params_eq 0).trans hK
    rw [hk] at hfit
    have e := hfit.C₀_eq
    have h1 := hfit.N₀_nonneg
    have h2 := hfit.Kc_ge
    have h3 : 1 ≤ (Tb.stepParameters y).coupling := hD.a_ge
    have h4 : ((T.stage 0).toStepSetup).params = Tb.stepParameters y := rfl
    rw [e]
    rw [h4]
    linarith
  have hcards : ∀ (t m : ℕ) [NeZero m] (i : Fin p), 0 ≤ siteCounts (Tb.stepParameters y).side f t m i :=
    fun t m _ i => Nat.cast_nonneg _
  have hmono : ∀ (t m : ℕ) [NeZero m] (i : Fin p),
      siteCounts (Tb.stepParameters y).side f (t + 1) m i ≤
        siteCounts (Tb.stepParameters y).side f t (m * (Tb.stepParameters y).side) i :=
    fun t m _ i => card_functionSites_succ_le (f i)
  let Dr : ℕ → ℝ := fun u => (widenedDist (Tb.stepParameters y).side s D u : ℝ)
  let g : ℕ → Finset (Fin p) → ℝ := fun t I =>
    Real.exp (2 ^ I.card * (I.card.factorial : ℝ) *
      Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β t)))
  let ε : ℕ → ℝ := fun t =>
    2 ^ p * (p.factorial : ℝ) * Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β t))
  have hε : ∀ t, 0 ≤ ε t := fun t => by positivity
  have hg0 : ∀ t I, 0 ≤ g t I := fun t I => (Real.exp_pos _).le
  have hg : ∀ t I, g t I ≤ Real.exp (ε t) := by
    intro t I
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    have hc : I.card ≤ p := by simpa using Finset.card_le_univ I
    have a : (2 : ℝ) ^ I.card ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hc
    have b : (I.card.factorial : ℝ) ≤ (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hc
    exact mul_le_mul a b (Nat.cast_nonneg _) (by positivity)
  have main : ∀ t, t ≤ s → ∀ (m : ℕ) [NeZero m], IsBlockTorusSide (Tb.stepParameters y) m →
      (∀ i, weightNorm (Tb.stepParameters y).side t
        (fineWeight (f i) (fineSide (Tb.stepParameters y).side t m)) ≤ 1) →
      SeparatedAlongTower (Tb.stepParameters y) (flowCoupling (Tb.stepParameters y) β) Dr t m
        (fun i => fineWeight (f i) (fineSide (Tb.stepParameters y).side t m)) →
      ∀ I : Finset (Fin p), ∀ᵐ u ∂(markedSampleLaw T β t m),
        |conditionalProduct S β f I t m u - ∏ i ∈ I, fittedResponse S (f i) t m (stageState T t m u)| ≤
          productError (Tb.stepParameters y).side (siteCounts (Tb.stepParameters y).side f) C Kr.C₀
            (Tb.stepParameters y).rt Dr g t m I *
            ∏ i ∈ I, scoreMeanOver S (f i) t m (stageState T t m u) := by
    intro t
    induction t with
    | zero =>
      intro _ m _ hm _ _ I
      filter_upwards [hBase m I (followsFlow_mono hrun (Nat.zero_le s))
        (fun j hj => hreach j (hj.trans (Nat.zero_le s))) hm] with u hu
      rw [hu]
      simp [productError]
    | succ t ih =>
      intro ht m _ hm hsz hA I
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hA
      have hm' : IsBlockTorusSide (Tb.stepParameters y) (m * (Tb.stepParameters y).side) :=
        ⟨dvd_mul_left _ _, hm.2.trans (Nat.le_mul_of_pos_right _ (NeZero.pos _))⟩
      have hsz' : ∀ i, weightNorm (Tb.stepParameters y).side t
          (fineWeight (f i) (fineSide (Tb.stepParameters y).side t (m * (Tb.stepParameters y).side))) ≤ 1 :=
        fun i => (weightNorm_le_succ hL1 t _).trans (hsz i)
      exact hStep t m I (widenedDist (Tb.stepParameters y).side s D t)
        (fun J => productError (Tb.stepParameters y).side (siteCounts (Tb.stepParameters y).side f) C Kr.C₀
          (Tb.stepParameters y).rt Dr g t (m * (Tb.stepParameters y).side) J)
        (followsFlow_mono hrun ht) (fun j hj => hreach j (hj.trans ht)) hm hsz h1 (by
          have h2' : (8 : ℝ) < (widenedDist (Tb.stepParameters y).side s D t : ℝ) := h2
          exact_mod_cast h2') h3
        (fun J _ => productError_nonneg hcards hC hC₀ hg0 t _ J)
        (fun J _ => ih (Nat.le_of_succ_le ht) (m * (Tb.stepParameters y).side) hm' hsz' h4 J)
  have hfull := main s le_rfl n hblock hsize
    (separated_widen (Tb.stepParameters y) hodd (flowCoupling (Tb.stepParameters y) β) D f s n hap) Finset.univ
  have hsum : ∑ v ∈ Finset.range s, ε v ≤ 2 ^ p * (p.factorial : ℝ) := by
    have h := (h₂ β s hreach 0 (Nat.zero_le s)).1
    rw [← Finset.range_eq_Ico] at h
    have e : ∑ v ∈ Finset.range s, ε v = 2 ^ p * (p.factorial : ℝ) *
        ∑ v ∈ Finset.range s, Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β v)) := by
      rw [Finset.mul_sum]
    rw [e]
    have hpos : (0 : ℝ) ≤ 2 ^ p * (p.factorial : ℝ) := by positivity
    nlinarith
  have hrate : ∀ u k, u + 1 + k = s →
      (3 / 2 : ℝ) ^ (p * k) * Real.exp (-((Tb.stepParameters y).rt * Dr u / 2 ^ 7)) ≤
        Real.exp ((p : ℝ) ^ 2 / (2 * ((Tb.stepParameters y).rt / 2 ^ 5))) *
          Real.exp (-((Tb.stepParameters y).rt * D u / 2 ^ 8)) := by
    intro u k hk
    have hk' : s - 1 - u = k := by omega
    have h8 := eight_le_widenedDist (Tb.stepParameters y).side s D u
    rw [hk'] at h8
    exact three_halves_pow_mul_exp_le p hrt hL2 k (le_widenedDist _ _ _ _) h8
  have hErr : productError (Tb.stepParameters y).side (siteCounts (Tb.stepParameters y).side f) C Kr.C₀
      (Tb.stepParameters y).rt Dr g s n Finset.univ ≤
      separationError (Tb.stepParameters y) (Real.exp (2 ^ p * (p.factorial : ℝ)) *
        (C * Real.exp ((p : ℝ) ^ 2 / (2 * ((Tb.stepParameters y).rt / 2 ^ 5))))) Kr.C₀ D s n
        (fun i => fineWeight (f i) (fineSide (Tb.stepParameters y).side s n)) := by
    have a := productError_le_heldBound (L := (Tb.stepParameters y).side) (rt := (Tb.stepParameters y).rt) (Dr := Dr)
      hcards hmono hC hC₀ (m := fun t => Real.exp (ε t)) (fun t => (Real.exp_pos _).le) hg0 hg s n Finset.univ
    have b := heldBound_le_levelSpread (L := (Tb.stepParameters y).side) (rt := (Tb.stepParameters y).rt) (Dr := Dr)
      hcards hC hC₀ hε Finset.univ s n 0
    have c := levelSpread_le_separationError (Tb.stepParameters y) f hC hC₀
      (Real.exp_pos (2 ^ p * (p.factorial : ℝ))).le s hrate s n 0 (by omega)
    have d := levelSpread_nonneg (L := (Tb.stepParameters y).side) (rt := (Tb.stepParameters y).rt) (Dr := Dr)
      hcards hC hC₀ Finset.univ s n 0
    simp only [Nat.mul_zero, pow_zero, mul_one] at b
    calc _ ≤ _ := a
      _ ≤ _ := b
      _ ≤ Real.exp (2 ^ p * (p.factorial : ℝ)) * levelSpread (Tb.stepParameters y).side
          (siteCounts (Tb.stepParameters y).side f) C Kr.C₀ (Tb.stepParameters y).rt Dr Finset.univ s n 0 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hsum) d
      _ ≤ _ := c
  have hscore := (hrun.isAdmissible s le_rfl).price.nonneg
  filter_upwards [hfull] with u hu
  have hMaj : 0 ≤ ∏ i, scoreMeanOver S (f i) s n (stageState T s n u) := Finset.prod_nonneg fun i _ =>
    zero_le_one.trans (one_le_meanSiteScore hscore _ _ _)
  exact hu.trans (mul_le_mul_of_nonneg_right hErr hMaj)
end YangMills.Construction.TransfersOffTheWalk
end
