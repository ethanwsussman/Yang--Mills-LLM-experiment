import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.FreeEnergiesOfTheFlow.ValuesOnTwoToriProof
import YangMills.Construction.SixteenPointsOnASmallTorus.ErrorOfTheCopies
import YangMills.Construction.SixteenPointsOnASmallTorus.SitesOfACopy
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies.ReflectedMomentErrorProof
section RealBounds
private theorem pow_mul_exp_neg_le_factorial_div {X c : ℝ} (hX : 0 ≤ X) (hc : 0 < c) (n : ℕ) :
    X ^ n * Real.exp (-(c * X)) ≤ (n.factorial : ℝ) / c ^ n := by
  have h := Real.pow_div_factorial_le_exp (c * X) (by positivity) n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hcn : 0 < c ^ n := by positivity
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ hcn, Real.exp_neg]
  have he := Real.exp_pos (c * X)
  rw [show X ^ n * (Real.exp (c * X))⁻¹ * c ^ n = (c ^ n * X ^ n) * (Real.exp (c * X))⁻¹ by ring]
  rw [← div_eq_mul_inv, div_le_iff₀ he]
  exact h.trans (le_of_eq (mul_comm _ _))
abbrev _root_.YangMills.SharedProofs.p10986 := @pow_mul_exp_neg_le_factorial_div
private theorem geometric_term_bound {m c X : ℝ} {N j : ℕ} (hm : 1 ≤ m) (hc : 0 < c) (hN : m * 2 ^ 17 ≤ 2 ^ N) (hX : 2 ^ j ≤ X) :
    m ^ j * ((j : ℝ) + 1) ^ 16 * X ^ 72 * Real.exp (-(c * X)) ≤
      ((N + 72).factorial : ℝ) / c ^ (N + 72) * (1 / 2) ^ j := by
  have hX0 : 0 ≤ X := le_trans (by positivity) hX
  have hj : (j : ℝ) + 1 ≤ 2 ^ j := by
    have : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    exact_mod_cast this
  have h1 : m ^ j * ((j : ℝ) + 1) ^ 16 * 2 ^ j ≤ X ^ N := by
    calc m ^ j * ((j : ℝ) + 1) ^ 16 * 2 ^ j ≤ m ^ j * ((2 : ℝ) ^ j) ^ 16 * 2 ^ j := by
          gcongr
      _ = (m * 2 ^ 17) ^ j := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
          congr 2
          ring
      _ ≤ ((2 : ℝ) ^ N) ^ j := pow_le_pow_left₀ (by positivity) hN j
      _ = ((2 : ℝ) ^ j) ^ N := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ X ^ N := pow_le_pow_left₀ (by positivity) hX N
  have h2 : m ^ j * ((j : ℝ) + 1) ^ 16 ≤ X ^ N * (1 / 2) ^ j := by
    have e : m ^ j * ((j : ℝ) + 1) ^ 16 = m ^ j * ((j : ℝ) + 1) ^ 16 * 2 ^ j * (1 / 2) ^ j := by
      rw [mul_assoc _ ((2 : ℝ) ^ j), ← mul_pow]
      norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have h3 := pow_mul_exp_neg_le_factorial_div hX0 hc (N + 72)
  calc m ^ j * ((j : ℝ) + 1) ^ 16 * X ^ 72 * Real.exp (-(c * X))
      ≤ X ^ N * (1 / 2) ^ j * X ^ 72 * Real.exp (-(c * X)) := by gcongr
    _ = X ^ (N + 72) * Real.exp (-(c * X)) * (1 / 2) ^ j := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 (by positivity)
private def stepConstant (Cb Lr c' c : ℝ) : ℝ :=
  Cb * (16 * 81 * Lr ^ 4) ^ 2 * Real.exp c' * (4 * c * 81 * Lr ^ 4) ^ 16
private def factorialConstant (N : ℕ) (c' : ℝ) : ℝ := ((N + 72).factorial : ℝ) / c' ^ (N + 72)
private theorem stepConstant_nonneg {Cb Lr c' c : ℝ} (hCb : 0 ≤ Cb) (hL : 0 ≤ Lr) (hc : 0 ≤ c) :
    0 ≤ stepConstant Cb Lr c' c :=
  mul_nonneg (mul_nonneg (mul_nonneg hCb (sq_nonneg _)) (Real.exp_pos _).le) (pow_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) (by norm_num)) (pow_nonneg hL 4)) 16)
private theorem factorialConstant_nonneg {N : ℕ} {c' : ℝ} (hc : 0 ≤ c') : 0 ≤ factorialConstant N c' :=
  div_nonneg (Nat.cast_nonneg _) (pow_nonneg hc _)
private theorem stepTerm_rearrange (m Cb e₁ e₂ Lr X c : ℝ) (j : ℕ) :
    m ^ j * (Cb * (((16 : ℕ) : ℝ) * (81 * (Lr * X) ^ 4)) ^ 2 * (e₁ * e₂)) * (((j : ℝ) + 1) * (4 * c * (81 * (Lr * X) ^ 4))) ^ 16 =
      (Cb * (16 * 81 * Lr ^ 4) ^ 2 * e₁ * (4 * c * 81 * Lr ^ 4) ^ 16) * (m ^ j * ((j : ℝ) + 1) ^ 16 * X ^ 72 * e₂) := by
  push_cast
  ring
private theorem sum_sizes_le {u s j : ℕ} {ρ Lr X c : ℝ} {a : ℕ → ℝ} (ha : ∀ t, 0 < a t) (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hL : 1 ≤ Lr) (hstep : ∀ t, a (t + 1) = a t * Lr) (hau : ρ / a u = Lr * X) (hcard : s - u = j + 1) :
    ∑ v ∈ Finset.Ico u s, 4 * c * (81 * (ρ / a v) ^ 4) ≤ ((j : ℝ) + 1) * (4 * c * (81 * (Lr * X) ^ 4)) := by
  have hadd : ∀ i, a u ≤ a (u + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [← add_assoc, hstep]
      exact ih.trans (le_mul_of_one_le_right (ha _).le hL)
  have hAv : ∀ v ∈ Finset.Ico u s, 4 * c * (81 * (ρ / a v) ^ 4) ≤ 4 * c * (81 * (Lr * X) ^ 4) := by
    intro v hv
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (Finset.mem_Ico.mp hv).1
    have h1 : ρ / a (u + i) ≤ Lr * X := by
      rw [← hau]
      exact div_le_div_of_nonneg_left hρ.le (ha u) (hadd i)
    have h2 : (ρ / a (u + i)) ^ 4 ≤ (Lr * X) ^ 4 :=
      pow_le_pow_left₀ (div_nonneg hρ.le (ha _).le) h1 4
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by norm_num)) (mul_nonneg (by norm_num) hc)
  have h1 := Finset.sum_le_card_nsmul _ _ _ hAv
  rw [Nat.card_Ico, hcard, nsmul_eq_mul] at h1
  refine h1.trans (le_of_eq ?_)
  push_cast
  ring
private theorem single_step_bound {u s j N : ℕ} {Lr ρ rt c' Cb c m : ℝ} {a : ℕ → ℝ} {Du : ℕ} (ha : ∀ t, 0 < a t)
    (hstep : ∀ t, a (t + 1) = a t * Lr) (hL : 2 ≤ Lr) (hρ : a s ≤ ρ) (hD : Du = ⌊ρ / a (u + 1)⌋₊) (hc'0 : 0 < c')
    (hc' : rt = c' * 2 ^ 7) (hCb : 0 ≤ Cb) (hc0 : 0 ≤ c) (hm : 1 ≤ m) (hN : m * 2 ^ 17 ≤ 2 ^ N) (hsj : s = u + 1 + j) :
    m ^ j * (Cb * (((16 : ℕ) : ℝ) * (81 * (ρ / a u) ^ 4)) ^ 2 * Real.exp (-(rt * Du / 2 ^ 7))) *
        (∑ v ∈ Finset.Ico u s, 4 * c * (81 * (ρ / a v) ^ 4)) ^ 16 ≤
      stepConstant Cb Lr c' c * factorialConstant N c' * (1 / 2) ^ j := by
  have hLpos : 0 < Lr := lt_of_lt_of_le two_pos hL
  have hL1 : 1 ≤ Lr := le_trans one_le_two hL
  have hρ0 : 0 < ρ := lt_of_lt_of_le (ha s) hρ
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = ρ / a (u + 1) := ⟨_, rfl⟩
  have hX : 2 ^ j ≤ X := by
    have hadd : ∀ i, a (u + 1 + i) = a (u + 1) * Lr ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [← add_assoc, hstep, ih, pow_succ, mul_assoc]
    have e := hadd j
    rw [← hsj] at e
    rw [hXd, le_div_iff₀ (ha _)]
    have h2 : (2 : ℝ) ^ j ≤ Lr ^ j := pow_le_pow_left₀ (by norm_num) hL j
    calc (2 : ℝ) ^ j * a (u + 1) ≤ Lr ^ j * a (u + 1) := mul_le_mul_of_nonneg_right h2 (ha _).le
      _ = a s := by rw [e, mul_comm]
      _ ≤ ρ := hρ
  have hau : ρ / a u = Lr * X := by
    rw [hXd, hstep]
    have h1 := (ha u).ne'
    have h2 := hLpos.ne'
    field_simp
  have hV := sum_sizes_le (s := s) (j := j) ha hρ0 hc0 hL1 hstep hau (by omega)
  have hV0 : 0 ≤ ∑ v ∈ Finset.Ico u s, 4 * c * (81 * (ρ / a v) ^ 4) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (mul_nonneg (by norm_num) hc0)
      (mul_nonneg (by norm_num) (pow_nonneg (div_nonneg hρ0.le (ha v).le) 4))
  have hexp : Real.exp (-(rt * Du / 2 ^ 7)) ≤ Real.exp c' * Real.exp (-(c' * X)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hfl : X < (Du : ℝ) + 1 := by
      rw [hD, ← hXd]
      exact Nat.lt_floor_add_one X
    have e : rt * (Du : ℝ) / 2 ^ 7 = c' * Du := by
      rw [hc']
      field_simp
    rw [e]
    have h1 := mul_lt_mul_of_pos_left hfl hc'0
    rw [mul_add, mul_one] at h1
    exact le_of_lt (by linarith)
  have hK : m ^ j * ((j : ℝ) + 1) ^ 16 * X ^ 72 * Real.exp (-(c' * X)) ≤ factorialConstant N c' * (1 / 2) ^ j :=
    geometric_term_bound hm hc'0 hN hX
  have hmj : 0 ≤ m ^ j := pow_nonneg (le_trans zero_le_one hm) j
  have hpre : 0 ≤ Cb * (((16 : ℕ) : ℝ) * (81 * (Lr * X) ^ 4)) ^ 2 := mul_nonneg hCb (sq_nonneg _)
  have hG0 := stepConstant_nonneg (c' := c') hCb hLpos.le hc0
  calc m ^ j * (Cb * (((16 : ℕ) : ℝ) * (81 * (ρ / a u) ^ 4)) ^ 2 * Real.exp (-(rt * Du / 2 ^ 7))) *
        (∑ v ∈ Finset.Ico u s, 4 * c * (81 * (ρ / a v) ^ 4)) ^ 16
      ≤ m ^ j * (Cb * (((16 : ℕ) : ℝ) * (81 * (Lr * X) ^ 4)) ^ 2 * (Real.exp c' * Real.exp (-(c' * X)))) *
        (((j : ℝ) + 1) * (4 * c * (81 * (Lr * X) ^ 4))) ^ 16 := by
        rw [hau]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hpre) hmj)
          (pow_le_pow_left₀ hV0 hV 16) (pow_nonneg hV0 16)
          (mul_nonneg hmj (mul_nonneg hpre (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)))
    _ = stepConstant Cb Lr c' c * (m ^ j * ((j : ℝ) + 1) ^ 16 * X ^ 72 * Real.exp (-(c' * X))) :=
        stepTerm_rearrange _ _ _ _ _ _ _ _
    _ ≤ stepConstant Cb Lr c' c * (factorialConstant N c' * (1 / 2) ^ j) := mul_le_mul_of_nonneg_left hK hG0
    _ = stepConstant Cb Lr c' c * factorialConstant N c' * (1 / 2) ^ j := (mul_assoc _ _ _).symm
private theorem sum_steps_bound {s N : ℕ} {Lr ρ rt c' Cb c m : ℝ} {a : ℕ → ℝ} {D : ℕ → ℕ} (ha : ∀ t, 0 < a t)
    (hstep : ∀ t, a (t + 1) = a t * Lr) (hL : 2 ≤ Lr) (hρ : a s ≤ ρ) (hD : ∀ u, D u = ⌊ρ / a (u + 1)⌋₊) (hc'0 : 0 < c')
    (hc' : rt = c' * 2 ^ 7) (hCb : 0 ≤ Cb) (hc0 : 0 ≤ c) (hm : 1 ≤ m) (hN : m * 2 ^ 17 ≤ 2 ^ N) :
    ∑ u ∈ Finset.range s, m ^ (s - 1 - u) * (Cb * (((16 : ℕ) : ℝ) * (81 * (ρ / a u) ^ 4)) ^ 2 * Real.exp (-(rt * D u / 2 ^ 7))) *
        (∑ v ∈ Finset.Ico u s, 4 * c * (81 * (ρ / a v) ^ 4)) ^ 16 ≤
      stepConstant Cb Lr c' c * factorialConstant N c' * 2 := by
  have hterm : ∀ u ∈ Finset.range s, m ^ (s - 1 - u) * (Cb * (((16 : ℕ) : ℝ) * (81 * (ρ / a u) ^ 4)) ^ 2 *
        Real.exp (-(rt * D u / 2 ^ 7))) * (∑ v ∈ Finset.Ico u s, 4 * c * (81 * (ρ / a v) ^ 4)) ^ 16 ≤
      stepConstant Cb Lr c' c * factorialConstant N c' * (1 / 2) ^ (s - 1 - u) := by
    intro u hu
    have hus : u < s := Finset.mem_range.mp hu
    exact single_step_bound ha hstep hL hρ (hD u) hc'0 hc' hCb hc0 hm hN (by omega)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_range_reflect (fun j => ((1 : ℝ) / 2) ^ j) s]
  exact mul_le_mul_of_nonneg_left (sum_geometric_two_le s)
    (mul_nonneg (stepConstant_nonneg hCb (le_trans zero_le_two hL) hc0) (factorialConstant_nonneg hc'0.le))
open Classical in
private theorem recursion_step_bound {ι : Type} (I : Finset ι) (E : Finset ι → ℝ) (b : ι → ℝ) {M m W : ℝ} {s : ℕ} (g V : ℕ → ℝ)
    (hg : ∀ u, 0 ≤ g u) (hV : ∀ u, 0 ≤ V u) (hM : |M| ≤ m)
    (hE : ∀ J ∈ I.powerset, |E J| ≤ ∑ u ∈ Finset.range s, g u * V u ^ J.card) (hb : ∀ i, |b i| ≤ W) :
    |M * ∑ J ∈ I.powerset, E J * ∏ i ∈ I \ J, b i| ≤ m * ∑ u ∈ Finset.range s, g u * (V u + W) ^ I.card := by
  rw [abs_mul]
  refine mul_le_mul hM ?_ (abs_nonneg _) ((abs_nonneg _).trans hM)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hJ : ∀ J ∈ I.powerset, |E J * ∏ i ∈ I \ J, b i| ≤
      ∑ u ∈ Finset.range s, g u * (V u ^ J.card * W ^ (I.card - J.card)) := by
    intro J hJm
    have hJI := Finset.mem_powerset.mp hJm
    rw [abs_mul, Finset.abs_prod]
    have hp : ∏ i ∈ I \ J, |b i| ≤ W ^ (I.card - J.card) := by
      calc ∏ i ∈ I \ J, |b i| ≤ ∏ _i ∈ I \ J, W := Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hb i
        _ = W ^ (I.card - J.card) := by rw [Finset.prod_const, Finset.card_sdiff_of_subset hJI]
    have hs0 : 0 ≤ ∑ u ∈ Finset.range s, g u * V u ^ J.card :=
      Finset.sum_nonneg fun u _ => mul_nonneg (hg u) (pow_nonneg (hV u) _)
    calc |E J| * ∏ i ∈ I \ J, |b i| ≤ (∑ u ∈ Finset.range s, g u * V u ^ J.card) * W ^ (I.card - J.card) :=
          mul_le_mul (hE J hJm) hp (Finset.prod_nonneg fun i _ => abs_nonneg _) hs0
      _ = _ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun u _ => by ring
  refine (Finset.sum_le_sum hJ).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow]
end RealBounds
section MomentRecursion
variable {ℓ : TorusLumps.StepParameters}
  (hL : ∀ c : WeightedResponses.ChainStage ℓ, ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup) (lam : ℝ) (x : ℕ → ℝ)
  (z₀ : ResponseInTheExpansion.StageWithResponse ℓ)
private def SupportBoundedBelow {ι : Type} (A : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → (ι → ResponseInTheExpansion.StageWeight hL lam x z₀ s n) → Prop
  | 0, _, _, _ => True
  | s + 1, n, _, f => SupportBoundedBelow A s (n * ℓ.side) f ∧
      ∀ i, ((ResponseInTheExpansion.weightSupportSites ℓ.side (ResponseInTheExpansion.stageStep hL lam x z₀ s).depth
        (n * ℓ.side) (f i)).card : ℝ) ≤ A s
set_option maxHeartbeats 1000000 in
open Classical in
private theorem abs_momentError_le {ch : ℝ} {C : ℕ → ℝ} {D : ℕ → ℕ} {Cb c : ℝ} {p : ℕ} {A : ℕ → ℝ}
    (hch : 0 ≤ ch) (hC : ∀ q ≤ p, |C q| ≤ Cb) (hCb : 0 ≤ Cb) (hc : 0 ≤ c) (hA : ∀ u, 0 ≤ A u) {ι : Type} :
    ∀ (s n : ℕ) [NeZero n] (I : Finset ι) (f : ι → ResponseInTheExpansion.StageWeight hL lam x z₀ s n),
      (∀ t < s, |(ResponseInTheExpansion.stageResponse hL lam x z₀ t).responseParams.C₀| ≤ c) →
      (∀ t < s, 0 ≤ (ResponseInTheExpansion.stageStep hL lam x z₀ t).coupling) →
      I.card ≤ p → SupportBoundedBelow hL lam x z₀ A s n f →
      |ResponseInTheExpansion.momentError hL lam x z₀ ch C D s n I f| ≤
        ∑ u ∈ Finset.range s, Real.exp (2 ^ p * (p.factorial : ℝ)) ^ (s - 1 - u) *
          (Cb * ((p : ℝ) * A u) ^ 2 * Real.exp (-(ℓ.rt * D u / 2 ^ 7))) *
          (∑ v ∈ Finset.Ico u s, 4 * c * A v) ^ I.card := by
  intro s
  induction s with
  | zero =>
    intro n _ I f _ _ _ _
    simp [ResponseInTheExpansion.momentError]
  | succ s ih =>
    intro n _ I f hK hx hI hS
    rw [SupportBoundedBelow] at hS
    obtain ⟨hS', hAs⟩ := hS
    have hKs := hK s (by omega)
    have hxs := hx s (by omega)
    have hK' : ∀ t < s, |(ResponseInTheExpansion.stageResponse hL lam x z₀ t).responseParams.C₀| ≤ c :=
      fun t ht => hK t (by omega)
    have hx' : ∀ t < s, 0 ≤ (ResponseInTheExpansion.stageStep hL lam x z₀ t).coupling := fun t ht => hx t (by omega)
    rw [ResponseInTheExpansion.momentError]
    set m : ℝ := Real.exp (2 ^ p * (p.factorial : ℝ)) with hmdef
    have hm0 : 0 ≤ m := (Real.exp_pos _).le
    set a : ι → ℝ := fun i => ((ResponseInTheExpansion.weightSupportSites ℓ.side
      (ResponseInTheExpansion.stageStep hL lam x z₀ s).depth (n * ℓ.side) (f i)).card : ℝ) with ha
    have ha0 : ∀ i, 0 ≤ a i := fun i => by simp only [ha]; positivity
    set C₀ := (ResponseInTheExpansion.stageResponse hL lam x z₀ s).responseParams.C₀ with hC₀
    set W : ℝ := 4 * c * A s with hWdef
    have hW0 : 0 ≤ W := mul_nonneg (by positivity) (hA s)
    set ex : ℝ := Real.exp (-(ℓ.rt * D s / 2 ^ 7)) with hex
    have hex0 : 0 ≤ ex := (Real.exp_pos _).le
    have hca : ∀ i, |C₀ * a i| ≤ c * A s := fun i => by
      rw [abs_mul, abs_of_nonneg (ha0 i)]
      exact mul_le_mul hKs (hAs i) (ha0 i) hc
    have hb2 : ∀ i, |2 * (C₀ * a i)| ≤ W := fun i => by
      have h1 := hca i
      have h2 : 0 ≤ c * A s := mul_nonneg hc (hA s)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hWdef]
      nlinarith
    have hb4 : ∀ i, |4 * (C₀ * a i)| ≤ W := fun i => by
      have h1 := hca i
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), hWdef]
      nlinarith
    set τ : ℝ := Cb * ((p : ℝ) * A s) ^ 2 * ex with hτ
    have hτ0 : 0 ≤ τ := by
      have := hA s
      positivity
    have hT : |C I.card * (∑ i ∈ I, a i) ^ 2 * ex * ∏ i ∈ I, (4 * (C₀ * a i))| ≤ τ * W ^ I.card := by
      have hsum0 : 0 ≤ ∑ i ∈ I, a i := Finset.sum_nonneg fun i _ => ha0 i
      have hsum : ∑ i ∈ I, a i ≤ (p : ℝ) * A s := by
        calc ∑ i ∈ I, a i ≤ ∑ _i ∈ I, A s := Finset.sum_le_sum fun i _ => hAs i
          _ = (I.card : ℝ) * A s := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (p : ℝ) * A s := mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (hA s)
      have hprod : |∏ i ∈ I, (4 * (C₀ * a i))| ≤ W ^ I.card := by
        rw [Finset.abs_prod]
        calc ∏ i ∈ I, |4 * (C₀ * a i)| ≤ ∏ _i ∈ I, W := Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hb4 i
          _ = W ^ I.card := by rw [Finset.prod_const]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hex0, abs_of_nonneg (pow_nonneg hsum0 2)]
      have h2 : (∑ i ∈ I, a i) ^ 2 ≤ ((p : ℝ) * A s) ^ 2 := pow_le_pow_left₀ hsum0 hsum 2
      have h3 := hC I.card hI
      have h4 : |C I.card| * (∑ i ∈ I, a i) ^ 2 ≤ Cb * ((p : ℝ) * A s) ^ 2 :=
        mul_le_mul h3 h2 (pow_nonneg hsum0 2) hCb
      have h5 : |C I.card| * (∑ i ∈ I, a i) ^ 2 * ex ≤ τ := mul_le_mul_of_nonneg_right h4 hex0
      exact mul_le_mul h5 hprod (abs_nonneg _) hτ0
    have hM : |Real.exp (2 ^ I.card * (I.card.factorial : ℝ) *
        Real.exp (-(7 * ch * (ResponseInTheExpansion.stageStep hL lam x z₀ s).coupling)))| ≤ m := by
      rw [abs_of_pos (Real.exp_pos _), hmdef]
      apply Real.exp_le_exp.mpr
      have e₀ : Real.exp (-(7 * ch * (ResponseInTheExpansion.stageStep hL lam x z₀ s).coupling)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := mul_nonneg hch hxs
        linarith
      have e₁ : (2 : ℝ) ^ I.card ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hI
      have e₂ : (I.card.factorial : ℝ) ≤ (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hI
      calc (2 : ℝ) ^ I.card * (I.card.factorial : ℝ) *
            Real.exp (-(7 * ch * (ResponseInTheExpansion.stageStep hL lam x z₀ s).coupling))
          ≤ (2 : ℝ) ^ I.card * (I.card.factorial : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left e₀ (by positivity)
        _ = (2 : ℝ) ^ I.card * (I.card.factorial : ℝ) := mul_one _
        _ ≤ 2 ^ p * (p.factorial : ℝ) := mul_le_mul e₁ e₂ (by positivity) (by positivity)
    set g : ℕ → ℝ := fun u => m ^ (s - 1 - u) * (Cb * ((p : ℝ) * A u) ^ 2 * Real.exp (-(ℓ.rt * D u / 2 ^ 7))) with hg
    set V : ℕ → ℝ := fun u => ∑ v ∈ Finset.Ico u s, 4 * c * A v with hV
    have hg0 : ∀ u, 0 ≤ g u := fun u => by
      have := hA u
      simp only [hg]
      positivity
    have hV0 : ∀ u, 0 ≤ V u := fun u => Finset.sum_nonneg fun v _ => mul_nonneg (by positivity) (hA v)
    have hR := recursion_step_bound I (fun J => ResponseInTheExpansion.momentError hL lam x z₀ ch C D s (n * ℓ.side) J f)
      (fun i => 2 * (C₀ * a i)) g V hg0 hV0 hM
      (fun J hJ => ih (n * ℓ.side) J f hK' hx' ((Finset.card_le_card (Finset.mem_powerset.mp hJ)).trans hI) hS') hb2
    refine (abs_add_le _ _).trans ?_
    rw [Finset.sum_range_succ]
    have hlast : m ^ (s + 1 - 1 - s) * (Cb * ((p : ℝ) * A s) ^ 2 * Real.exp (-(ℓ.rt * D s / 2 ^ 7))) *
        (∑ v ∈ Finset.Ico s (s + 1), 4 * c * A v) ^ I.card = τ * W ^ I.card := by
      have e₁ : s + 1 - 1 - s = 0 := by omega
      rw [e₁, pow_zero, one_mul, Nat.Ico_succ_singleton, Finset.sum_singleton]
    have hrest : ∑ u ∈ Finset.range s, m ^ (s + 1 - 1 - u) * (Cb * ((p : ℝ) * A u) ^ 2 * Real.exp (-(ℓ.rt * D u / 2 ^ 7))) *
        (∑ v ∈ Finset.Ico u (s + 1), 4 * c * A v) ^ I.card = m * ∑ u ∈ Finset.range s, g u * (V u + W) ^ I.card := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      have hus : u < s := Finset.mem_range.mp hu
      have e₁ : s + 1 - 1 - u = (s - 1 - u) + 1 := by omega
      rw [e₁, Finset.sum_Ico_succ_top hus.le, pow_succ]
      simp only [hg, hV]
      ring
    rw [hlast, hrest]
    exact (add_le_add hT hR).trans (le_of_eq (add_comm _ _))
end MomentRecursion
section ReflectedCopies
private theorem card_reflectedWeight_support (hS : reflectedWeightSupportStatement) {L : ℕ} [NeZero L] (hodd : Odd L)
    {K κ : ℕ} {ρ H : ℝ} {Λ : NNReal} {h : TestFunctions.EuclideanFourSpace → ℝ} (hρ : 0 < ρ)
    (hρl : ρ ≤ cellLength L K κ / 4) (hsrc : IsLocalizedSource (cellLength L K κ) ρ H Λ h)
    {t t' n : ℕ} [NeZero n] (ht : t' = t) (hn : n = twoCellSide L κ t) (htκ : t ≤ κ) (h3 : 3 * levelSpacing L K t ≤ ρ)
    (k : Fin 4 → Fin 2) :
    ((ResponseInTheExpansion.weightSupportSites L t' n
      (reflectedWeight (levelSpacing L K 0) (L ^ κ) (fun μ => (k μ : ℕ)) h)).card : ℝ) ≤
      81 * (ρ / levelSpacing L K t) ^ 4 := by
  subst ht
  subst hn
  exact hS L hodd K κ t' ρ H Λ h htκ hρ hρl hsrc h3 k
private theorem supportBounded_reflectedWeights (hS : reflectedWeightSupportStatement) {ℓ : TorusLumps.StepParameters}
    (hL : ∀ c : WeightedResponses.ChainStage ℓ, ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup) (lam : ℝ) (x : ℕ → ℝ)
    (z₀ : ResponseInTheExpansion.StageWithResponse ℓ) (hodd : Odd ℓ.side)
    {K κ s : ℕ} {ρ H : ℝ} {Λ : NNReal} {h : TestFunctions.EuclideanFourSpace → ℝ} (hρ : 0 < ρ)
    (hρl : ρ ≤ cellLength ℓ.side K κ / 4) (hsrc : IsLocalizedSource (cellLength ℓ.side K κ) ρ H Λ h)
    (hlev : ∀ t < s, (ResponseInTheExpansion.stageStep hL lam x z₀ t).depth = t) (hsκ : s ≤ κ)
    (h3 : ∀ t < s, 3 * levelSpacing ℓ.side K t ≤ ρ) :
    ∀ (t n : ℕ) [NeZero n], t ≤ s → n = twoCellSide ℓ.side κ t →
      SupportBoundedBelow hL lam x z₀ (fun u => 81 * (ρ / levelSpacing ℓ.side K u) ^ 4) t n
        (fun k : Fin 4 → Fin 2 => reflectedWeight (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) (fun μ => (k μ : ℕ)) h) := by
  intro t
  induction t with
  | zero =>
    intro n _ _ _
    rw [SupportBoundedBelow]
    trivial
  | succ t ih =>
    intro n _ hts hn
    have hnL : n * ℓ.side = twoCellSide ℓ.side κ t := by
      have e : κ - t = (κ - (t + 1)) + 1 := by omega
      rw [hn, twoCellSide, twoCellSide, e, pow_succ]
      ring
    rw [SupportBoundedBelow]
    exact ⟨ih (n * ℓ.side) (by omega) hnL, fun k =>
      card_reflectedWeight_support hS hodd hρ hρl hsrc (hlev t (by omega)) hnL (by omega) (h3 t (by omega)) k⟩
end ReflectedCopies
section SpacingLemmas
variable {L : ℕ}
private theorem levelSpacing_pos_of (hL : 0 < L) (K t : ℕ) : 0 < levelSpacing L K t := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.meshAt_pos <;> assumption
private theorem levelSpacing_succ (hL : 0 < L) (K t : ℕ) : levelSpacing L K (t + 1) = levelSpacing L K t * L := by
  unfold levelSpacing
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [← zpow_add_one₀ hL']
  congr 1
  push_cast
  ring
private theorem levelSpacing_add (hL : 0 < L) (K u j : ℕ) :
    levelSpacing L K (u + j) = levelSpacing L K u * (L : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [← add_assoc, levelSpacing_succ hL, ih, pow_succ]; ring
private theorem levelSpacing_mono (hL : 1 ≤ L) (K : ℕ) {t t' : ℕ} (h : t ≤ t') :
    levelSpacing L K t ≤ levelSpacing L K t' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [levelSpacing_add hL]
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ j := one_le_pow₀ (by exact_mod_cast hL)
  have h2 := levelSpacing_pos_of hL K t
  nlinarith
private theorem cellLength_eq_levelSpacing (hL : 0 < L) (K κ : ℕ) : cellLength L K κ = levelSpacing L K κ := by
  have := levelSpacing_add hL K 0 κ
  rw [zero_add] at this
  rw [cellLength, this, mul_comm]
end SpacingLemmas
private theorem gasRate_nonneg (T : RenormalizationStepParameters.ParameterAssignment) (hT : T.Admissible) : 0 ≤ T.gasRate := by apply _root_.YangMills.SharedProofs.p19490 <;> assumption
private theorem one_le_clusterRange {x : ℝ} (hx : 1 ≤ x) : (1 : ℝ) ≤ (TorusLumps.clusterRange x : ℝ) := by
  have h : 0 < TorusLumps.clusterRange x := by
    unfold TorusLumps.clusterRange
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
  exact_mod_cast h
set_option maxHeartbeats 1000000 in
theorem reflectedMomentError_of_support (hS : reflectedWeightSupportStatement) : reflectedMomentErrorStatement := by
  unfold reflectedMomentErrorStatement ForAllLargeFloors ForAllInitialStages
  refine ⟨fun _ => 1, fun _ => one_pos, ?_⟩
  intro T hT _ Kr
  refine ⟨1, ?_⟩
  intro y hy Cs hCs
  have hLge : 2 ≤ T.side := le_trans (by norm_num) hT.L_ge
  have hL0 : 0 < T.side := by omega
  have hLr : (2 : ℝ) ≤ (T.side : ℝ) := by exact_mod_cast hLge
  have hrt : 0 < T.rt := hT.rt_pos
  set Cb : ℝ := ∑ q ∈ Finset.range 17, Cs q with hCbdef
  have hCb : 0 ≤ Cb := Finset.sum_nonneg fun q _ => hCs q
  have hC : ∀ q ≤ 16, |Cs q| ≤ Cb := fun q hq => by
    rw [abs_of_nonneg (hCs q)]
    exact Finset.single_le_sum (f := Cs) (fun i _ => hCs i) (Finset.mem_range.mpr (by omega))
  set c : ℝ := |Kr.C₀| with hcdef
  have hc0 : 0 ≤ c := abs_nonneg _
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = Real.exp (2 ^ 16 * ((16 : ℕ).factorial : ℝ)) := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    rw [hmdef]
    exact Real.one_le_exp (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (m * 2 ^ 17) (one_lt_two (α := ℝ))
  have hc'0 : 0 < T.rt / 2 ^ 7 := div_pos hrt (by norm_num)
  have hLr0 : (0 : ℝ) ≤ (T.side : ℝ) := Nat.cast_nonneg _
  refine ⟨stepConstant Cb T.side (T.rt / 2 ^ 7) c * factorialConstant N (T.rt / 2 ^ 7) * 2,
    mul_nonneg (mul_nonneg (stepConstant_nonneg hCb hLr0 hc0) (factorialConstant_nonneg hc'0.le)) (by norm_num), ?_⟩
  intro Ξ _ β hL z₀ _ K κ s ρ H Λ h hdat _ hρ hρl hsrc hlev hst
  have hfit : s ≤ K ∧ FitsAtLevel (T.stepParameters y) β K ρ s := by
    classical
    unfold radiusLevel at hlev
    split_ifs at hlev with hex
    obtain ⟨t, htK, ht⟩ := hex
    have e := Option.some.inj hlev
    subst e
    exact ⟨Nat.findGreatest_le K, Nat.findGreatest_spec htK ht⟩
  obtain ⟨hsK, hfits⟩ := hfit
  have hfl : ∀ t ≤ s, 1 ≤ (TorusLumps.couplingFlow (T.stepParameters y) β t).1 := fun t ht => by
    have h1 := hdat.coupling_ge t (ht.trans hsK)
    have h2 : (T.stepParameters y).y₁ = y := rfl
    linarith
  have hr : (1 : ℝ) ≤ rangeAtLevel (T.stepParameters y) β s := one_le_clusterRange (hfl s le_rfl)
  have has : 0 < levelSpacing T.side K s := levelSpacing_pos_of hL0 K s
  have hfits' : 2 ^ 11 * rangeAtLevel (T.stepParameters y) β s * levelSpacing T.side K s ≤ ρ := hfits
  have hasρ : 2 ^ 11 * levelSpacing T.side K s ≤ ρ := by
    refine le_trans ?_ hfits'
    have : (2 : ℝ) ^ 11 ≤ 2 ^ 11 * rangeAtLevel (T.stepParameters y) β s := by nlinarith
    exact mul_le_mul_of_nonneg_right this has.le
  have hsκ : s ≤ κ := by
    by_contra hlt
    have h1 : levelSpacing T.side K κ ≤ levelSpacing T.side K s := levelSpacing_mono hL0 K (by omega)
    have h2 : ρ ≤ levelSpacing T.side K κ / 4 := by rw [← cellLength_eq_levelSpacing hL0]; exact hρl
    norm_num at hasρ
    linarith
  have h3 : ∀ t < s, 3 * levelSpacing T.side K t ≤ ρ := fun t ht => by
    have h1 : levelSpacing T.side K t ≤ levelSpacing T.side K s := levelSpacing_mono hL0 K ht.le
    norm_num at hasρ
    linarith
  have hodd : Odd (T.stepParameters y).side := hT.L_odd
  have hlv : ∀ t < s,
      (ResponseInTheExpansion.stageStep hL T.lam (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β) z₀ t).depth = t :=
    fun t ht => (hst t ht.le).depth_eq
  have hKt : ∀ t < s, |(ResponseInTheExpansion.stageResponse hL T.lam
      (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β) z₀ t).responseParams.C₀| ≤ c := fun t ht => by
    have e : (ResponseInTheExpansion.stageResponse hL T.lam
        (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β) z₀ t).responseParams = Kr :=
      (hst t ht.le).params_eq
    rw [e]
  have hxt : ∀ t < s, 0 ≤ (ResponseInTheExpansion.stageStep hL T.lam
      (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β) z₀ t).coupling := fun t ht => by
    have e : (ResponseInTheExpansion.stageStep hL T.lam
        (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β) z₀ t).coupling =
        ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β t :=
      (hst t ht.le).coupling_eq
    rw [e]
    have := hfl t ht.le
    exact le_trans zero_le_one this
  have hSU := supportBounded_reflectedWeights hS hL T.lam (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β)
    z₀ hodd hρ hρl hsrc hlv hsκ h3 s (twoCellSide T.side κ s) le_rfl rfl
  have hA0 : ∀ u, 0 ≤ 81 * (ρ / levelSpacing T.side K u) ^ 4 := fun u => by
    have := levelSpacing_pos_of hL0 K u
    positivity
  have hcard : (Finset.univ : Finset (Fin 4 → Fin 2)).card = 16 := by
    simp [Finset.card_univ]
  have hab := abs_momentError_le hL T.lam (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β) z₀
    (ch := T.gasRate) (C := Cs) (D := radiusInStageUnits T.side K ρ) (p := 16)
    (A := fun u => 81 * (ρ / levelSpacing T.side K u) ^ 4) (gasRate_nonneg T hT) hC hCb hc0 hA0
    s (twoCellSide T.side κ s) Finset.univ _ hKt hxt hcard.le hSU
  rw [hcard, ← hmdef] at hab
  have hsum := sum_steps_bound (s := s) (N := N) (Lr := (T.side : ℝ)) (ρ := ρ) (rt := T.rt) (c' := T.rt / 2 ^ 7)
    (Cb := Cb) (c := c) (m := m) (a := levelSpacing T.side K) (D := radiusInStageUnits T.side K ρ)
    (levelSpacing_pos_of hL0 K) (levelSpacing_succ hL0 K) hLr
    (by norm_num at hasρ; linarith) (fun u => rfl) hc'0 (by ring) hCb hc0 hm1 hN.le
  exact (le_abs_self _).trans (hab.trans hsum)
end YangMills.Construction.SmallTorusCopies.ReflectedMomentErrorProof
end
