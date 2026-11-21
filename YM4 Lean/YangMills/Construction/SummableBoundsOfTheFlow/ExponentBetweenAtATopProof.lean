import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrameProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
set_option linter.unusedSectionVars false
namespace YangMills.Construction
open Set BlockAverages ColdStepAtMirrorFrames IteratedDerivative Interpolation
namespace Interpolation
namespace AtTop
theorem coe_le_coe_of_le {n m : ℕ} (h : n ≤ m) : ((n : ℕ) : WithTop ℕ∞) ≤ ((m : ℕ) : WithTop ℕ∞) := by
  exact_mod_cast h
section Sums
variable {ι : Type} [Fintype ι]
def weightedSq (a d : ι → ℝ) (γ : ℝ) : ℝ := ∑ b, Real.exp (-(γ * d b)) * a b ^ 2
theorem weightedSq_nonneg (a d : ι → ℝ) (γ : ℝ) : 0 ≤ weightedSq a d γ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
theorem sum_sq_le_weightedSq (Q : Finset ι) (a d : ι → ℝ) (γ : ℝ) (hQ : ∀ b ∈ Q, d b = 0) :
    ∑ b ∈ Q, a b ^ 2 ≤ weightedSq a d γ := by
  have h1 : ∑ b ∈ Q, a b ^ 2 = ∑ b ∈ Q, Real.exp (-(γ * d b)) * a b ^ 2 :=
    Finset.sum_congr rfl fun b hb => by simp [hQ b hb]
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q)
    fun _ _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
theorem sum_sq_exp_le_weightedSq (a d : ι → ℝ) (g γ : ℝ) (hd : ∀ b, 0 ≤ d b) (hg : γ ≤ g) :
    ∑ b, a b ^ 2 * Real.exp (-(g * d b)) ≤ weightedSq a d γ := by
  refine Finset.sum_le_sum fun b _ => ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
  nlinarith [hd b]
theorem double_sum_le (Q : Finset ι) (a d : ι → ℝ) (N : ℕ) (g γ Wt : ℝ) (hQ : ∀ b ∈ Q, d b = 0)
    (hN : Q.card ≤ N) (hd : ∀ b, 0 ≤ d b) (hg : γ ≤ g)
    (hW : ∑ b, Real.exp (-(g * d b)) ≤ Wt) :
    ∑ b ∈ Q, ∑ b', a b * a b' * Real.exp (-(g * d b')) ≤ (Wt + N) / 2 * weightedSq a d γ := by
  set sq := weightedSq a d γ with hsq
  have hsq0 : 0 ≤ sq := weightedSq_nonneg _ _ _
  have hA := sum_sq_le_weightedSq Q a d γ hQ
  have hB := sum_sq_exp_le_weightedSq a d g γ hd hg
  have hW0 : 0 ≤ Wt := (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans hW
  have h1 : ∀ b ∈ Q, ∑ b', a b * a b' * Real.exp (-(g * d b')) ≤ a b ^ 2 / 2 * Wt + sq / 2 := by
    intro b _
    have h2 : ∀ b', a b * a b' * Real.exp (-(g * d b')) ≤
        a b ^ 2 / 2 * Real.exp (-(g * d b')) + a b' ^ 2 * Real.exp (-(g * d b')) / 2 := by
      intro b'
      have : a b * a b' ≤ a b ^ 2 / 2 + a b' ^ 2 / 2 := by nlinarith [sq_nonneg (a b - a b')]
      have := mul_le_mul_of_nonneg_right this (Real.exp_pos (-(g * d b'))).le
      linarith
    refine (Finset.sum_le_sum fun b' _ => h2 b').trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    have h3 : a b ^ 2 / 2 * ∑ b', Real.exp (-(g * d b')) ≤ a b ^ 2 / 2 * Wt :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    linarith
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul]
  have h4 : (Q.card : ℝ) ≤ N := by exact_mod_cast hN
  have h5 : (∑ b ∈ Q, a b ^ 2) / 2 * Wt ≤ sq / 2 * Wt := by
    have := mul_le_mul_of_nonneg_right hA hW0
    linarith
  have h6 : (Q.card : ℝ) * (sq / 2) ≤ N * (sq / 2) := mul_le_mul_of_nonneg_right h4 (by positivity)
  nlinarith
theorem sum_le_sqrt_weightedSq (Q : Finset ι) (a d : ι → ℝ) (N : ℕ) (γ : ℝ) (hQ : ∀ b ∈ Q, d b = 0)
    (hN : Q.card ≤ N) :
    ∑ b ∈ Q, a b ≤ ((N : ℝ) + 1) * Real.sqrt (weightedSq a d γ) := by
  set sq := weightedSq a d γ with hsq
  have hsq0 : 0 ≤ sq := weightedSq_nonneg _ _ _
  have h1 := sq_sum_le_card_mul_sum_sq (s := Q) (f := a)
  have hA := sum_sq_le_weightedSq Q a d γ hQ
  have h4 : (Q.card : ℝ) ≤ N := by exact_mod_cast hN
  have h5 : (∑ b ∈ Q, a b) ^ 2 ≤ (((N : ℝ) + 1) ^ 2) * sq := by
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    calc (∑ b ∈ Q, a b) ^ 2 ≤ Q.card * ∑ b ∈ Q, a b ^ 2 := h1
      _ ≤ N * sq := mul_le_mul h4 hA (Finset.sum_nonneg fun _ _ => sq_nonneg _) hn
      _ ≤ ((N : ℝ) + 1) ^ 2 * sq := mul_le_mul_of_nonneg_right (by nlinarith) hsq0
  have h6 := Real.le_sqrt_of_sq_le h5
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at h6
theorem sum_exp_le_sqrt_weightedSq (a d : ι → ℝ) (g γ Wt : ℝ) (hd : ∀ b, 0 ≤ d b) (hg : γ ≤ g)
    (hW : ∑ b, Real.exp (-(g * d b)) ≤ Wt) :
    ∑ b, a b * Real.exp (-(g * d b)) ≤ (Wt + 1) * Real.sqrt (weightedSq a d γ) := by
  set sq := weightedSq a d γ with hsq
  have hsq0 : 0 ≤ sq := weightedSq_nonneg _ _ _
  have hW0 : 0 ≤ Wt := (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans hW
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun b => a b * Real.exp (-(γ / 2 * d b))) (fun b => Real.exp (-((g - γ / 2) * d b)))
  have e1 : ∀ b, a b * Real.exp (-(γ / 2 * d b)) * Real.exp (-((g - γ / 2) * d b)) =
      a b * Real.exp (-(g * d b)) := by
    intro b
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have e2 : ∀ b, (a b * Real.exp (-(γ / 2 * d b))) ^ 2 = Real.exp (-(γ * d b)) * a b ^ 2 := by
    intro b
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm]
    congr 2
    push_cast
    ring
  have e3 : ∀ b, Real.exp (-((g - γ / 2) * d b)) ^ 2 ≤ Real.exp (-(g * d b)) := by
    intro b
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    push_cast
    nlinarith [hd b]
  simp only [e1, e2] at h1
  have h2 : ∑ b, Real.exp (-((g - γ / 2) * d b)) ^ 2 ≤ Wt :=
    (Finset.sum_le_sum fun b _ => e3 b).trans hW
  have h5 : (∑ b, a b * Real.exp (-(g * d b))) ^ 2 ≤ ((Wt + 1) ^ 2) * sq := by
    calc _ ≤ sq * ∑ b, Real.exp (-((g - γ / 2) * d b)) ^ 2 := h1
      _ ≤ sq * Wt := mul_le_mul_of_nonneg_left h2 hsq0
      _ ≤ (Wt + 1) ^ 2 * sq := by nlinarith [mul_nonneg hsq0 hW0, mul_nonneg hsq0 (sq_nonneg Wt)]
  have h6 := Real.le_sqrt_of_sq_le h5
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at h6
end Sums
section Forms
variable {F : BlockFrame} {k : ℕ}
abbrev JointSpace (F : BlockFrame) (k : ℕ) : Type := StepVariable (finiteCells F) × (Fin k → ℝ)
abbrev paramList (F : BlockFrame) (k : ℕ) : List (JointSpace F k) :=
  parameterDirections _ _ (parameterBasis k)
theorem paramList_length : (paramList F k).length = k := by simp [parameterDirections, parameterBasis]
theorem iteratedFDeriv_param_eq_derivAlong (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (ζ : StepVariable (finiteCells F)) (hf : ContDiffAt ℝ (k : WithTop ℕ∞) f (ζ, 0)) :
    iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => f (ζ, τ)) 0 (fun l => Pi.single l 1) =
      derivAlong f (paramList F k) (ζ, 0) := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.iteratedFDeriv_parameters_eq <;> assumption
theorem iteratedFDeriv_param_fderiv_eq_derivAlong (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (ζ w : StepVariable (finiteCells F)) (hf : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f (ζ, 0)) :
    iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => fderiv ℝ (fun ζ' => f (ζ', τ)) ζ w) 0
        (fun l => Pi.single l 1) =
      derivAlong f (paramList F k ++ [(w, 0)]) (ζ, 0) := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.iteratedFDeriv_parameters_fderiv_eq <;> assumption
theorem fderiv_fderiv_eq_derivAlong (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ)
    (η u v : StepVariable (finiteCells F)) (hf : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) f (η, 0)) :
    fderiv ℝ (fun ζ => fderiv ℝ (fun ζ' => f (ζ', 0)) ζ u) η v =
      derivAlong f [(v, 0), (u, 0)] (η, 0) := by apply _root_.YangMills.DeltaSharedProofs.p502347 <;> assumption
theorem abs_le_norm_mul_of_homogeneous {g : EuclideanSpace ℝ (Fin 3) → ℝ} {B : ℝ}
    (hg : ∀ (c : ℝ) (e : EuclideanSpace ℝ (Fin 3)), g (c • e) = c * g e)
    (h : ∀ e, ‖e‖ = 1 → |g e| ≤ B) (e : EuclideanSpace ℝ (Fin 3)) : |g e| ≤ ‖e‖ * B := by
  by_cases he : e = 0
  · subst he
    have := hg 0 0
    simp at this
    simp [this]
  · have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
    have hu : ‖‖e‖⁻¹ • e‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have e1 : e = ‖e‖ • (‖e‖⁻¹ • e) := by
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    have h1 := h _ hu
    rw [e1, hg, abs_mul, abs_of_nonneg (norm_nonneg _)]
    have e2 : ‖‖e‖ • (‖e‖⁻¹ • e)‖ = ‖e‖ := by rw [← e1]
    rw [e2]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
abbrev bondSlot (k : ℕ) (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) :
    JointSpace F k :=
  variableDirection (Fin k → ℝ) (Pi.single b e)
theorem bondSlot_smul (b : ↥(chordBonds (finiteCells F))) (c : ℝ) (e : EuclideanSpace ℝ (Fin 3)) :
    (bondSlot k b (c • e) : JointSpace F k) = c • bondSlot k b e := by
  simp [bondSlot, variableDirection, Pi.single_smul]
variable (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
  (η : StepVariable (finiteCells F)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
theorem derivAlong_params_le (h : JointMixedDerivEqDerivAlong) {B : ℝ}
    (hs : ContDiffAt ℝ (k : WithTop ℕ∞) (rotatedEval G V c X) (η, 0))
    (hB : |jointMixedDeriv (l := 0) G η V Fin.elim0 Fin.elim0 c X| ≤ B) :
    |derivAlong (rotatedEval G V c X) (paramList F k) (η, 0)| ≤ B := by
  have := (h F V G η k c X).2 0 Fin.elim0 Fin.elim0 (by simpa using hs)
  rw [this] at hB
  simpa [pointDirections] using hB
theorem derivAlong_one_bond_le (h : JointMixedDerivEqDerivAlong) (R : DerivAlongRules (JointSpace F k) ℝ)
    {B : ℝ} (hs : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0))
    (b : ↥(chordBonds (finiteCells F)))
    (hB : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → |jointMixedDeriv (l := 1) G η V ![b] ![u] c X| ≤ B)
    (e : EuclideanSpace ℝ (Fin 3)) :
    |derivAlong (rotatedEval G V c X) (bondSlot k b e :: paramList F k) (η, 0)| ≤ ‖e‖ * B := by
  refine abs_le_norm_mul_of_homogeneous
    (g := fun e => derivAlong (rotatedEval G V c X) (bondSlot k b e :: paramList F k) (η, 0)) ?_ ?_ e
  · intro r e
    have := R.smul_slot (rotatedEval G V c X) (η, 0) [] (paramList F k) r (bondSlot k b e)
      (by simpa [parameterDirections, parameterBasis, add_comm] using hs)
    simpa [bondSlot_smul] using this
  · intro u hu
    have e1 := (h F V G η k c X).2 1 ![b] ![u] (by simpa [add_comm] using hs)
    have := hB u hu
    rw [e1] at this
    simpa [pointDirections] using this
theorem derivAlong_two_bonds_le (h : JointMixedDerivEqDerivAlong) (R : DerivAlongRules (JointSpace F k) ℝ)
    {B : ℝ} (hs : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0))
    (b b' : ↥(chordBonds (finiteCells F)))
    (hB : ∀ u u' : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → ‖u'‖ = 1 →
      |jointMixedDeriv (l := 2) G η V ![b', b] ![u', u] c X| ≤ B)
    (e e' : EuclideanSpace ℝ (Fin 3)) :
    |derivAlong (rotatedEval G V c X) (bondSlot k b' e' :: bondSlot k b e :: paramList F k) (η, 0)| ≤
      ‖e‖ * ‖e'‖ * B := by
  have hlen : ∀ (x y : JointSpace F k), ContDiffAt ℝ (((x :: y :: paramList F k).length : ℕ) : WithTop ℕ∞)
      (rotatedEval G V c X) (η, 0) := fun x y => by
    rw [show (x :: y :: paramList F k).length = k + 2 by simp [paramList_length]]; exact hs
  have hlen' : ∀ (x y : JointSpace F k),
      ContDiffAt ℝ ((([x] ++ y :: paramList F k).length : ℕ) : WithTop ℕ∞)
      (rotatedEval G V c X) (η, 0) := fun x y => by
    rw [show ([x] ++ y :: paramList F k).length = k + 2 by simp [paramList_length]]; exact hs
  have step : ∀ e' : EuclideanSpace ℝ (Fin 3), ‖e'‖ = 1 → ∀ e : EuclideanSpace ℝ (Fin 3),
      |derivAlong (rotatedEval G V c X) (bondSlot k b' e' :: bondSlot k b e :: paramList F k) (η, 0)| ≤
        ‖e‖ * B := by
    intro e' he'
    refine abs_le_norm_mul_of_homogeneous (g := fun e => derivAlong (rotatedEval G V c X)
      (bondSlot k b' e' :: bondSlot k b e :: paramList F k) (η, 0)) ?_ ?_
    · intro r e
      have := R.smul_slot (rotatedEval G V c X) (η, 0) [bondSlot k b' e'] (paramList F k) r
        (bondSlot k b e) (hlen' _ _)
      simpa [bondSlot_smul] using this
    · intro u hu
      have e1 := (h F V G η k c X).2 2 ![b', b] ![e', u] (by simpa [add_comm] using hs)
      have := hB u e' hu he'
      rw [e1] at this
      simpa [pointDirections, List.ofFn_succ] using this
  have := abs_le_norm_mul_of_homogeneous (g := fun e' => derivAlong (rotatedEval G V c X)
      (bondSlot k b' e' :: bondSlot k b e :: paramList F k) (η, 0))
    (B := ‖e‖ * B) (fun r e' => by
      have := R.smul_slot (rotatedEval G V c X) (η, 0) [] (bondSlot k b e :: paramList F k) r
        (bondSlot k b' e') (hlen _ _)
      simpa [bondSlot_smul] using this) (fun u hu => step u hu e) e'
  calc _ ≤ ‖e'‖ * (‖e‖ * B) := this
    _ = ‖e‖ * ‖e'‖ * B := by ring
theorem derivAlong_three_bonds_le (h : JointMixedDerivEqDerivAlong)
    (R : DerivAlongRules (JointSpace F k) ℝ) {B : ℝ}
    (hs : ContDiffAt ℝ ((k + 3 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0))
    (b b' b'' : ↥(chordBonds (finiteCells F)))
    (hB : ∀ u u' u'' : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → ‖u'‖ = 1 → ‖u''‖ = 1 →
      |jointMixedDeriv (l := 3) G η V ![b'', b', b] ![u'', u', u] c X| ≤ B)
    (e e' e'' : EuclideanSpace ℝ (Fin 3)) :
    |derivAlong (rotatedEval G V c X)
        (bondSlot k b'' e'' :: bondSlot k b' e' :: bondSlot k b e :: paramList F k) (η, 0)| ≤
      ‖e‖ * ‖e'‖ * ‖e''‖ * B := by
  have hA : ∀ (x y z : JointSpace F k),
      ContDiffAt ℝ (((x :: y :: z :: paramList F k).length : ℕ) : WithTop ℕ∞)
      (rotatedEval G V c X) (η, 0) := fun x y z => by
    rw [show (x :: y :: z :: paramList F k).length = k + 3 by simp [paramList_length]]; exact hs
  have hB' : ∀ (x y z : JointSpace F k),
      ContDiffAt ℝ ((([x] ++ y :: z :: paramList F k).length : ℕ) : WithTop ℕ∞)
      (rotatedEval G V c X) (η, 0) := fun x y z => by
    rw [show ([x] ++ y :: z :: paramList F k).length = k + 3 by simp [paramList_length]]; exact hs
  have hC : ∀ (x y z : JointSpace F k),
      ContDiffAt ℝ ((([x, y] ++ z :: paramList F k).length : ℕ) : WithTop ℕ∞)
      (rotatedEval G V c X) (η, 0) := fun x y z => by
    rw [show ([x, y] ++ z :: paramList F k).length = k + 3 by simp [paramList_length]]; exact hs
  have s1 : ∀ e'' e' : EuclideanSpace ℝ (Fin 3), ‖e''‖ = 1 → ‖e'‖ = 1 → ∀ e : EuclideanSpace ℝ (Fin 3),
      |derivAlong (rotatedEval G V c X)
          (bondSlot k b'' e'' :: bondSlot k b' e' :: bondSlot k b e :: paramList F k) (η, 0)| ≤
        ‖e‖ * B := by
    intro e'' e' h'' h'
    refine abs_le_norm_mul_of_homogeneous (g := fun e => derivAlong (rotatedEval G V c X)
      (bondSlot k b'' e'' :: bondSlot k b' e' :: bondSlot k b e :: paramList F k) (η, 0)) ?_ ?_
    · intro r e
      have := R.smul_slot (rotatedEval G V c X) (η, 0) [bondSlot k b'' e'', bondSlot k b' e']
        (paramList F k) r (bondSlot k b e) (hC _ _ _)
      simpa [bondSlot_smul] using this
    · intro u hu
      have e1 := (h F V G η k c X).2 3 ![b'', b', b] ![e'', e', u] (by simpa [add_comm] using hs)
      have := hB u e' e'' hu h' h''
      rw [e1] at this
      simpa [pointDirections, List.ofFn_succ] using this
  have s2 : ∀ e'' : EuclideanSpace ℝ (Fin 3), ‖e''‖ = 1 → ∀ e' : EuclideanSpace ℝ (Fin 3),
      |derivAlong (rotatedEval G V c X)
          (bondSlot k b'' e'' :: bondSlot k b' e' :: bondSlot k b e :: paramList F k) (η, 0)| ≤
        ‖e'‖ * (‖e‖ * B) := by
    intro e'' h''
    refine abs_le_norm_mul_of_homogeneous (g := fun e' => derivAlong (rotatedEval G V c X)
      (bondSlot k b'' e'' :: bondSlot k b' e' :: bondSlot k b e :: paramList F k) (η, 0)) ?_ ?_
    · intro r e'
      have := R.smul_slot (rotatedEval G V c X) (η, 0) [bondSlot k b'' e'']
        (bondSlot k b e :: paramList F k) r (bondSlot k b' e') (hB' _ _ _)
      simpa [bondSlot_smul] using this
    · intro u hu
      exact s1 e'' u h'' hu e
  have := abs_le_norm_mul_of_homogeneous (g := fun e'' => derivAlong (rotatedEval G V c X)
    (bondSlot k b'' e'' :: bondSlot k b' e' :: bondSlot k b e :: paramList F k) (η, 0))
    (B := ‖e'‖ * (‖e‖ * B))
    (fun r e'' => by
      have := R.smul_slot (rotatedEval G V c X) (η, 0) []
        (bondSlot k b' e' :: bondSlot k b e :: paramList F k) r (bondSlot k b'' e'') (hA _ _ _)
      simpa [bondSlot_smul] using this) (fun u hu => s2 u hu e') e''
  calc _ ≤ ‖e''‖ * (‖e'‖ * (‖e‖ * B)) := this
    _ = ‖e‖ * ‖e'‖ * ‖e''‖ * B := by ring
end Forms
section Spans
variable {F : BlockFrame}
theorem siteSupDist_eq_cellSupDist (y z : F.Cell) : siteSupDist y z = cellSupDist y z := rfl
theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
theorem bondSpan_le_diameter {k : ℕ} {P : Finset F.Cell} {Y : F.Cell} {c : Fin k → F.Site F.top × Fin 4}
    (hY : Y ∈ P) (hc : ∀ l, (c l).1 ∈ P) : bondSpan Y c ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.bondSpan_le_cellSetDiameter <;> assumption
theorem bondSpanWithCell_le_diameter {k : ℕ} {P : Finset F.Cell} {Y z : F.Cell}
    {c : Fin k → F.Site F.top × Fin 4}
    (hY : Y ∈ P) (hz : z ∈ P) (hc : ∀ l, (c l).1 ∈ P) : bondSpanWithCell Y z c ≤ cellSetDiameter P := by apply _root_.YangMills.SharedProofs.p114969 <;> assumption
theorem bondSpan_le_two_mul (hD : SupDistCellComparison) {k : ℕ} {Y : F.Cell}
    {c : Fin k → F.Site F.top × Fin 4} {R : ℕ} (h : ∀ l, cellSupDist Y (c l).1 ≤ R) :
    bondSpan Y c ≤ 2 * R := by
  unfold bondSpan
  refine max_le (Finset.sup_le fun l _ => (h l).trans (by omega)) (Finset.sup_le fun l _ =>
    Finset.sup_le fun l' _ => ?_)
  obtain ⟨-, h2, h3⟩ := hD.1 F F.top Y (c l).1 (c l').1
  obtain ⟨-, h4, -⟩ := hD.1 F F.top (c l).1 Y (c l').1
  have h5 := (hD.1 F F.top (c l).1 Y (c l').1).2.2
  have h6 := h l
  have h7 := h l'
  simp only [siteSupDist_eq_cellSupDist] at h2 h4 h5 ⊢
  omega
theorem exp_le_exp_mul_exp {δ κ d S n : ℝ} (hκ : 0 < κ) (hr : 2 ^ 7 * κ ≤ δ) (hd : d ≤ S) (hn : n ≤ S)
    (hd0 : 0 ≤ d) (hn0 : 0 ≤ n) :
    Real.exp (-(δ * S)) ≤ Real.exp (-(δ / 2 * d)) * Real.exp (-(2 ^ 6 * κ * n)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hδ : 0 ≤ δ := by nlinarith
  have h1 : δ / 2 * d ≤ δ / 2 * S := mul_le_mul_of_nonneg_left hd (by positivity)
  have h2 : 2 ^ 6 * κ * n ≤ δ / 2 * n := mul_le_mul_of_nonneg_right (by linarith) hn0
  have h3 : δ / 2 * n ≤ δ / 2 * S := mul_le_mul_of_nonneg_left hn (by positivity)
  linarith
theorem exp_le_exp_of_rate {δ κ S n : ℝ} (hκ : 0 < κ) (hr : 2 ^ 7 * κ ≤ δ) (hn : n ≤ S) (hn0 : 0 ≤ n) :
    Real.exp (-(δ * S)) ≤ Real.exp (-(2 ^ 6 * κ * n)) := by
  refine Real.exp_le_exp.2 ?_
  have h2 : 2 ^ 6 * κ * n ≤ δ * n := mul_le_mul_of_nonneg_right (by linarith) hn0
  have hδ : 0 ≤ δ := by nlinarith
  have h3 : δ * n ≤ δ * S := mul_le_mul_of_nonneg_left hn hδ
  linarith
theorem exp_le_exp_of_coeff {κ S n : ℝ} (hκ : 0 < κ) (hn : n ≤ S) (hn0 : 0 ≤ n) :
    Real.exp (-(2 ^ 8 * κ * S)) ≤ Real.exp (-(2 ^ 6 * κ * n)) := by
  refine Real.exp_le_exp.2 ?_
  have h2 : 2 ^ 6 * κ * n ≤ 2 ^ 8 * κ * n := mul_le_mul_of_nonneg_right (by linarith) hn0
  have h3 : 2 ^ 8 * κ * n ≤ 2 ^ 8 * κ * S := mul_le_mul_of_nonneg_left hn (by positivity)
  linarith
end Spans
section Core
variable {F : BlockFrame}
structure TopData (s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm : ℝ) (m N : ℕ) (Kf : ℕ → ℝ) (Dk : ℕ → ℕ → ℝ)
    (V : F.GaugeField F.top) : Prop where
  nonempty : Nonempty ↥(chordBonds (finiteCells F))
  ρ_pos : 0 < ρ
  κ_pos : 0 < κ
  rate_le : 2 ^ 10 * κ ≤ δ₂
  one_le_x : 1 ≤ x
  Ctω_nonneg : 0 ≤ Ct * ω
  x_Ctω_le_one : x * (Ct * ω) ≤ 1
  Cg_nonneg : 0 ≤ Cg
  Ch_nonneg : 0 ≤ Ch
  Dm_nonneg : 0 ≤ Dm
  Dk_le : ∀ l j, l ≤ 3 → j ≤ 3 → Dk l j ≤ Dm
  card_le : ∀ z : F.Cell, (cellChordBonds z).card ≤ N
  weight_sum_le : ∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
    Real.exp (-(δ₂ / 2 * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ Wt
  kernels : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
    HasInterpolationKernels s a ρA κ κ₂ δ₂ x m Kf Dk V η
  slopeSmall : InterpolatedSlopeSmall s a ρA δ₂ Ct ω x m V
  gap_le : ∀ (η : StepVariable (finiteCells F)) (c₀ : F.Site F.top × Fin 4), (∀ b, ‖η b‖ < ρ) →
    c₀ ∈ innerBonds (finiteCells F) F.top →
      |haarGapExcess a x (interpolatedField s a ρA m V η) c₀| ≤ Cg
  haar_le : ∀ (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))), (∀ b, ‖η b‖ < ρ) →
    |haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2)| ≤ Ch
variable {s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm : ℝ} {m N : ℕ} {Kf : ℕ → ℝ} {Dk : ℕ → ℕ → ℝ}
  {V : F.GaugeField F.top} {k : ℕ}
theorem energy_contDiffAt (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V)
    (hA : JointMixedDerivEqDerivAlong) (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ ρ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (n : ℕ) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (rotatedEval (interpolatedEnergy s a ρA m) V c X) (ζ, 0) :=
  (hA F V _ ζ k c X).1 D.nonempty
    (fun l b u hl hu => ((D.kernels ζ hζ).energy l k b u c X hl hu hX).1) n
theorem gap_contDiffAt (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V)
    (hA : JointMixedDerivEqDerivAlong) (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ ρ)
    (c₀ : F.Site F.top × Fin 4) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (n : ℕ) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (rotatedEval (contourHaarGap s a ρA x m c₀) V c X) (ζ, 0) :=
  (hA F V _ ζ k c X).1 D.nonempty
    (fun l b u hl hu => ((D.kernels ζ hζ).gap c₀ l k b u c X (by omega) hu hX).1) n
theorem haar_contDiffAt (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V)
    (hA : JointMixedDerivEqDerivAlong) (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ ρ)
    (b₀ : ↥(chordBonds (finiteCells F))) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (n : ℕ) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (rotatedEval (interpolatedHaarLogRatio s a ρA m b₀) V c X) (ζ, 0) :=
  (hA F V _ ζ k c X).1 D.nonempty
    (fun l b u hl hu => ((D.kernels ζ hζ).haar b₀ l k b u c X (by omega) hu hX).1) n
theorem smul_mem_ball {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : ∀ b, ‖(v • η) b‖ ≤ ρ := by
  intro b
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hv.1]
  nlinarith [norm_nonneg (η b), hη b, hv.2]
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem derivAlong_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : DerivAlongRules E ℝ)
    (f g : E → ℝ) (p : E) (l : List E) (hf : ContDiffAt ℝ (l.length : WithTop ℕ∞) f p)
    (hg : ContDiffAt ℝ (l.length : WithTop ℕ∞) g p) :
    derivAlong (fun q => f q - g q) l p = derivAlong f l p - derivAlong g l p := by
  have hg' : ContDiffAt ℝ (l.length : WithTop ℕ∞) (fun q => (-1 : ℝ) • g q) p := hg.const_smul (-1 : ℝ)
  have h1 := R.add f (fun q => (-1 : ℝ) • g q) p l hf hg'
  have h2 := R.smul (-1) g p l hg
  simp only [sub_eq_add_neg]
  rw [h2] at h1
  simpa using h1
theorem derivAlong_sum {E κ' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (R' : DerivAlongRules E ℝ)
    (Q : Finset κ') (g : κ' → E → ℝ) (p : E) (l : List E)
    (h : ∀ b ∈ Q, ContDiffAt ℝ (l.length : WithTop ℕ∞) (g b) p) :
    derivAlong (fun q => ∑ b ∈ Q, g b q) l p = ∑ b ∈ Q, derivAlong (g b) l p := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    have := R'.smul 0 (fun _ => (0 : ℝ)) p l contDiffAt_const
    simpa using this
  | insert a s ha ih =>
    have hs : ContDiffAt ℝ (l.length : WithTop ℕ∞) (fun q => ∑ b ∈ s, g b q) p :=
      ContDiffAt.sum fun b hb => h b (Finset.mem_insert_of_mem hb)
    simp only [Finset.sum_insert ha]
    rw [R'.add _ _ _ _ (h a (Finset.mem_insert_self a s)) hs,
      ih fun b hb => h b (Finset.mem_insert_of_mem hb)]
theorem derivAlong_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ₀ : ℝ) (l : List E)
    (hl : l ≠ []) : derivAlong (fun _ : E => κ₀) l = fun _ => 0 := by
  induction l with
  | nil => exact absurd rfl hl
  | cons u l ih =>
    funext q
    by_cases h0 : l = []
    · subst h0
      simp [derivAlong]
    · simp [derivAlong, ih h0]
def gapTerm (s a ρA x : ℝ) (m : ℕ) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (c₀ : F.Site F.top × Fin 4) (p : JointSpace F k) : ℝ :=
  rotatedEval (contourHaarGap s a ρA x m c₀) V c X p - haarGap (a * x)
theorem gapTerm_contDiffAt (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V)
    (hA : JointMixedDerivEqDerivAlong) (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ ρ)
    (c₀ : F.Site F.top × Fin 4) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (n : ℕ) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (gapTerm s a ρA x m V c X c₀) (ζ, 0) :=
  (gap_contDiffAt D hA ζ hζ c₀ c X hX n).sub contDiffAt_const
theorem derivAlong_gapTerm (R : DerivAlongRules (JointSpace F k) ℝ)
    (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V)
    (hA : JointMixedDerivEqDerivAlong) (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ ρ)
    (c₀ : F.Site F.top × Fin 4) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (l : List (JointSpace F k)) (hl : l ≠ []) :
    derivAlong (gapTerm s a ρA x m V c X c₀) l (ζ, 0) =
      derivAlong (rotatedEval (contourHaarGap s a ρA x m c₀) V c X) l (ζ, 0) := by
  have := derivAlong_sub R (rotatedEval (contourHaarGap s a ρA x m c₀) V c X) (fun _ => haarGap (a * x))
    (ζ, 0) l (gap_contDiffAt D hA ζ hζ c₀ c X hX _) contDiffAt_const
  rw [derivAlong_const _ l hl] at this
  have e : gapTerm s a ρA x m V c X c₀ =
      fun q => rotatedEval (contourHaarGap s a ρA x m c₀) V c X q - haarGap (a * x) := rfl
  rw [e]
  simpa using this
theorem exponent_expansion (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hRay : RayGradientSumSmoothAndBounded) (hRead : cellExponentRotatedEvalStatement)
    (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ ρ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
      (rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X) (η, 0) ∧
    ∀ l : List (JointSpace F k), l.length ≤ k + 2 →
      derivAlong (rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X) l (η, 0) =
        x * derivAlong (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X)
          (cellChordBonds Y)) l (η, 0) -
        (∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
          derivAlong (gapTerm s a ρA x m V c X c₀) l (η, 0)) -
        ∑ b ∈ cellChordBonds Y, derivAlong (rotatedEval (interpolatedHaarLogRatio s a ρA m b) V c X) l (η, 0) := by
  have R := hL.1 (JointSpace F k) ℝ
  have hs : ∀ v ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, ContDiffAt ℝ (n : WithTop ℕ∞)
      (rotatedEval (interpolatedEnergy s a ρA m) V c X) (v • η, 0) := fun v hv n =>
    energy_contDiffAt D hA (v • η) (smul_mem_ball hη hv) c X hX n
  have hray : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
      (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) (cellChordBonds Y)) (η, 0) := by
    have := (hRay _ _ (Fin k → ℝ) (rotatedEval (interpolatedEnergy s a ρA m) V c X) (cellChordBonds Y) η
      (parameterBasis k) (fun v hv => hs v hv _)).1
    simpa [parameterBasis] using this
  have e := (hRead.1 F s a ρA x m Y V η k c X fun v hv => hs v hv 1)
  have hg : ∀ n : ℕ, ContDiffAt ℝ (n : WithTop ℕ∞) (fun p => ∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter
      (fun c => c.1 = Y), gapTerm s a ρA x m V c X c₀ p) (η, 0) := fun n =>
    ContDiffAt.sum fun c₀ _ => gapTerm_contDiffAt D hA η hη c₀ c X hX n
  have hh : ∀ n : ℕ, ContDiffAt ℝ (n : WithTop ℕ∞) (fun p => ∑ b ∈ cellChordBonds Y,
      rotatedEval (interpolatedHaarLogRatio s a ρA m b) V c X p) (η, 0) := fun n =>
    ContDiffAt.sum fun b _ => haar_contDiffAt D hA η hη b c X hX n
  have hx : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fun p => x *
      rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) (cellChordBonds Y) p) (η, 0) :=
    contDiffAt_const.mul hray
  refine ⟨((hx.sub (hg _)).sub (hh _)).congr_of_eventuallyEq e, fun l hl => ?_⟩
  have hlen : ((l.length : ℕ) : WithTop ℕ∞) ≤ ((k + 2 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hl
  rw [(R.congr _ _ _ l e).self_of_nhds]
  have e2 := derivAlong_sub R (fun p => x * rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X)
      (cellChordBonds Y) p - ∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        (rotatedEval (contourHaarGap s a ρA x m c₀) V c X p - haarGap (a * x)))
    (fun p => ∑ b ∈ cellChordBonds Y, rotatedEval (interpolatedHaarLogRatio s a ρA m b) V c X p) (η, 0) l
    ((hx.of_le hlen).sub (hg _)) (hh _)
  have e3 := derivAlong_sub R (fun p => x * rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X)
      (cellChordBonds Y) p) (fun p => ∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        (rotatedEval (contourHaarGap s a ρA x m c₀) V c X p - haarGap (a * x))) (η, 0) l
    (hx.of_le hlen) (hg _)
  have e4 := R.smul x (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) (cellChordBonds Y))
    (η, 0) l (hray.of_le hlen)
  simp only [smul_eq_mul] at e4
  have e5 := derivAlong_sum R ((innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y))
    (gapTerm s a ρA x m V c X) (η, 0) l (fun c₀ _ => gapTerm_contDiffAt D hA η hη c₀ c X hX _)
  have e6 := derivAlong_sum R (cellChordBonds Y)
    (fun b => rotatedEval (interpolatedHaarLogRatio s a ρA m b) V c X) (η, 0) l
    (fun b _ => haar_contDiffAt D hA η hη b c X hX _)
  have e5' : derivAlong (fun p => ∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      (rotatedEval (contourHaarGap s a ρA x m c₀) V c X p - haarGap (a * x))) l (η, 0) =
      ∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        derivAlong (gapTerm s a ρA x m V c X c₀) l (η, 0) := e5
  rw [e2, e3, e4, e5', e6]
theorem energy_first_deriv_le (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hRead : cellExponentRotatedEvalStatement) (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V)
    (hk : k ≤ 3) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) :
    |derivAlong (rotatedEval (interpolatedEnergy s a ρA m) V c X) (paramList F k ++ [bondSlot k b e]) (0, 0)| ≤
      ‖e‖ * (Ct * ω * Real.exp (-(δ₂ / 8 * (bondListDistance (enclosingCell b.1.1) c : ℝ)))) := by
  have R := hL.1 (JointSpace F k) ℝ
  have h0 : ∀ b : ↥(chordBonds (finiteCells F)), ‖(0 : StepVariable (finiteCells F)) b‖ ≤ ρ := fun b => by
    simpa using D.ρ_pos.le
  have hsm := fun n : ℕ => energy_contDiffAt D hA 0 h0 c X hX n
  refine abs_le_norm_mul_of_homogeneous (g := fun e => derivAlong (rotatedEval (interpolatedEnergy s a ρA m) V c X)
    (paramList F k ++ [bondSlot k b e]) (0, 0)) ?_ ?_ e
  · intro r e
    have := R.smul_slot (rotatedEval (interpolatedEnergy s a ρA m) V c X) (0, 0) (paramList F k) [] r
      (bondSlot k b e) (hsm _)
    simpa [bondSlot_smul] using this
  · intro u hu
    have hd := D.slopeSmall.deriv_decay b.1 b.2 (toImaginary u) (by rw [norm_toImaginary, hu]) k c X hk hX
    have hev : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), interpolatedSlope s a ρA m b.1 (toImaginary u)
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) =
        derivAlong (rotatedEval (interpolatedEnergy s a ρA m) V c X) [bondSlot k b u] (0, τ) := by
      have hc : Filter.Tendsto (fun τ : Fin k → ℝ => ((0 : StepVariable (finiteCells F)), τ)) (𝓝 0)
          (𝓝 (0, 0)) :=
        (by fun_prop : Continuous fun τ : Fin k → ℝ => ((0 : StepVariable (finiteCells F)), τ)).tendsto 0
      filter_upwards [hc.eventually ((hsm 1).eventually (by simp))] with τ hτ
      exact hRead.2 F s a ρA m k V c X τ b u (hτ.differentiableAt (by simp))
    have e1 := Filter.EventuallyEq.iteratedFDeriv ℝ (show _ =ᶠ[𝓝 (0 : Fin k → ℝ)] _ from hev) k
    have e2 := iteratedFDeriv_param_eq_derivAlong hL
      (derivAlong (rotatedEval (interpolatedEnergy s a ρA m) V c X) [bondSlot k b u]) 0
      ((hL.1 _ ℝ).contDiffAt _ _ k _ (hsm _))
    rw [(hL.1 _ ℝ).append]
    rw [← e2, ← e1.self_of_nhds]
    exact hd
theorem energy_second_deriv_le (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V) (hk : k ≤ 3)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ ρ) (b b' : ↥(chordBonds (finiteCells F)))
    (e e' : EuclideanSpace ℝ (Fin 3)) :
    |derivAlong (rotatedEval (interpolatedEnergy s a ρA m) V c X)
        (bondSlot k b' e' :: (paramList F k ++ [bondSlot k b e])) (ζ, 0)| ≤
      ‖e‖ * ‖e'‖ * (Dm * Real.exp (-(δ₂ * (cellSetDiameter (∅ ∪ chordBondCells ![b', b] ∪
        topBondCells c) : ℝ)))) := by
  have R := hL.1 (JointSpace F k) ℝ
  have hsm := fun n : ℕ => energy_contDiffAt D hA ζ hζ c X hX n
  have hp : (bondSlot k b' e' :: (paramList F k ++ [bondSlot k b e])).Perm
      (bondSlot k b' e' :: bondSlot k b e :: paramList F k) :=
    List.Perm.cons _ (List.perm_append_singleton _ _)
  rw [R.perm _ _ _ _ hp (hsm _)]
  refine derivAlong_two_bonds_le _ V ζ c X hA R (hsm _) b b' (fun u u' hu hu' => ?_) e e'
  have := ((D.kernels ζ hζ).energy 2 k ![b', b] ![u', u] c X le_rfl
    (fun i => by fin_cases i <;> simp [hu, hu']) hX).2
  refine this.trans ?_
  exact mul_le_mul_of_nonneg_right (D.Dk_le 2 k (by omega) hk) (Real.exp_pos _).le
theorem energy_third_deriv_le (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) (hX : AreUnitVectors X)
    (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ ρ) (b b' b'' : ↥(chordBonds (finiteCells F)))
    (e e' e'' : EuclideanSpace ℝ (Fin 3)) :
    |derivAlong (rotatedEval (interpolatedEnergy s a ρA m) V c X)
        [bondSlot 0 b'' e'', bondSlot 0 b' e', bondSlot 0 b e] (ζ, 0)| ≤
      ‖e‖ * ‖e'‖ * ‖e''‖ * (Dm * Real.exp (-(δ₂ * (cellSetDiameter (∅ ∪ chordBondCells ![b'', b', b] ∪
        topBondCells c) : ℝ)))) := by
  have R := hL.1 (JointSpace F 0) ℝ
  have hsm := fun n : ℕ => energy_contDiffAt D hA ζ hζ c X hX n
  have hl : paramList F 0 = [] := by simp [parameterDirections, parameterBasis]
  have := derivAlong_three_bonds_le _ V ζ c X hA R (hsm _) b b' b'' (B := Dm * Real.exp (-(δ₂ *
    (cellSetDiameter (∅ ∪ chordBondCells ![b'', b', b] ∪ topBondCells c) : ℝ))))
    (fun u u' u'' hu hu' hu'' => by
      have h1 := ((D.kernels ζ hζ).energy 3 0 ![b'', b', b] ![u'', u', u] c X (by norm_num)
        (fun i => by fin_cases i <;> simp [hu, hu', hu'']) hX).2
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_right (D.Dk_le 3 0 (by omega) (by omega)) (Real.exp_pos _).le) e e' e''
  rwa [hl] at this
theorem leftTranslate_bondSpread_zero {j : ℕ} {W : F.GaugeField j} {k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X 0) W = W := by apply _root_.YangMills.Construction.Interpolation.TopVariation.leftTranslate_bondSpread_zero <;> assumption
theorem enclosingCell_of_mem {Y : F.Cell} {b : ↥(chordBonds (finiteCells F))} (hb : b ∈ cellChordBonds Y) :
    enclosingCell b.1.1 = Y := by
  simpa [cellChordBonds] using hb
theorem mem_topBondCells {P : Finset F.Cell} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} (l : Fin k) :
    (c l).1 ∈ P ∪ topBondCells c := by
  simp only [topBondCells, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨l, rfl⟩
theorem mem_chordBondCells {P R : Finset F.Cell} {l : ℕ} {b : Fin l → ↥(chordBonds (finiteCells F))}
    (i : Fin l) : enclosingCell (b i).1.1 ∈ P ∪ chordBondCells b ∪ R := by
  simp only [chordBondCells, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨i, rfl⟩)
theorem mem_union_left_left {P R Q : Finset F.Cell} {u : F.Cell} (h : u ∈ P) : u ∈ P ∪ Q ∪ R :=
  Finset.mem_union_left _ (Finset.mem_union_left _ h)
theorem card_innerBonds_at_cell_le (Y : F.Cell) :
    ((innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y)).card ≤ 4 := by
  classical
  have := Finset.card_le_card_of_injOn (s := (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y))
    (t := (Finset.univ : Finset (Fin 4))) (fun c => c.2) (fun _ _ => by simp) (by
      intro c hc c' hc' h
      have h1 : c.1 = Y := by simpa using (Finset.mem_filter.1 hc).2
      have h2 : c'.1 = Y := by simpa using (Finset.mem_filter.1 hc').2
      exact Prod.ext (h1.trans h2.symm) h)
  simpa using this
theorem gapTerm_params_le (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V) (hk : k ≤ 3)
    (Y : F.Cell) (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < ρ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (c₀ : F.Site F.top × Fin 4)
    (hc₀ : c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y)) :
    |derivAlong (gapTerm s a ρA x m V c X c₀) (paramList F k) (η, 0)| ≤
      (Cg + Dm) * Real.exp (-(2 ^ 6 * κ * (bondSpan Y c : ℝ))) := by
  have hηc : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
  have hY : c₀.1 = Y := (Finset.mem_filter.1 hc₀).2
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hl : paramList F 0 = [] := by simp [parameterDirections, parameterBasis]
    have hE : bondSpan Y c = 0 := by simp [bondSpan]
    rw [hl, hE]
    change |gapTerm s a ρA x m V c X c₀ (η, 0)| ≤ _
    have h1 := D.gap_le η c₀ hη (Finset.mem_filter.1 hc₀).1
    have h2 : gapTerm s a ρA x m V c X c₀ (η, 0) =
        haarGapExcess a x (interpolatedField s a ρA m V η) c₀ := by
      simp only [gapTerm, rotatedEval, contourHaarGap, haarGapExcess, leftTranslate_bondSpread_zero]
    rw [h2]
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    linarith [D.Dm_nonneg]
  · have hne : paramList F k ≠ [] := by
      intro h
      have := paramList_length (F := F) (k := k)
      rw [h] at this
      simp at this
      omega
    have hR := hL.1 (JointSpace F k) ℝ
    rw [derivAlong_gapTerm hR D hA η hηc c₀ c X hX _ hne]
    have h1 := ((D.kernels η hηc).gap c₀ 0 k Fin.elim0 Fin.elim0 c X (by omega) (fun i => i.elim0) hX).2
    have h2 := derivAlong_params_le _ V η c X hA (gap_contDiffAt D hA η hηc c₀ c X hX _) h1
    refine h2.trans ?_
    have hm : Y ∈ ({c₀.1} ∪ chordBondCells (l := 0) Fin.elim0 ∪ topBondCells c : Finset F.Cell) :=
      mem_union_left_left (by simp [hY])
    have h3 := exp_le_exp_of_coeff D.κ_pos (show (bondSpan Y c : ℝ) ≤ (cellSetDiameter ({c₀.1} ∪
      chordBondCells (l := 0) Fin.elim0 ∪ topBondCells c) : ℝ) by
        exact_mod_cast bondSpan_le_diameter hm fun l => mem_topBondCells l) (Nat.cast_nonneg _)
    have h4 := D.Dk_le 0 k (by omega) hk
    calc _ ≤ Dm * Real.exp (-(2 ^ 6 * κ * (bondSpan Y c : ℝ))) :=
          mul_le_mul h4 h3 (Real.exp_pos _).le D.Dm_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [D.Cg_nonneg]) (Real.exp_pos _).le
theorem haar_params_le (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V) (hk : k ≤ 3)
    (Y : F.Cell) (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < ρ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (b₀ : ↥(chordBonds (finiteCells F))) (hb₀ : b₀ ∈ cellChordBonds Y) :
    |derivAlong (rotatedEval (interpolatedHaarLogRatio s a ρA m b₀) V c X) (paramList F k) (η, 0)| ≤
      (Ch + Dm) * Real.exp (-(2 ^ 6 * κ * (bondSpan Y c : ℝ))) := by
  have hηc : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
  have hY := enclosingCell_of_mem hb₀
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hl : paramList F 0 = [] := by simp [parameterDirections, parameterBasis]
    have hE : bondSpan Y c = 0 := by simp [bondSpan]
    rw [hl, hE]
    change |rotatedEval (interpolatedHaarLogRatio s a ρA m b₀) V c X (η, 0)| ≤ _
    have h1 := D.haar_le η b₀ hη
    have h2 : rotatedEval (interpolatedHaarLogRatio s a ρA m b₀) V c X (η, 0) =
        haarLogRatio (interpolatedCoords s a ρA m V η b₀.1.1 b₀.1.2) := by
      simp only [rotatedEval, interpolatedHaarLogRatio, leftTranslate_bondSpread_zero]
    rw [h2]
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    linarith [D.Dm_nonneg]
  · have h1 := ((D.kernels η hηc).haar b₀ 0 k Fin.elim0 Fin.elim0 c X (by omega) (fun i => i.elim0) hX).2
    have h2 := derivAlong_params_le _ V η c X hA (haar_contDiffAt D hA η hηc b₀ c X hX _) h1
    refine h2.trans ?_
    have hm : Y ∈ ({enclosingCell b₀.1.1} ∪ chordBondCells (l := 0) Fin.elim0 ∪ topBondCells c :
        Finset F.Cell) :=
      mem_union_left_left (by simp [hY])
    have h3 := exp_le_exp_of_coeff D.κ_pos (show (bondSpan Y c : ℝ) ≤ (cellSetDiameter
      ({enclosingCell b₀.1.1} ∪ chordBondCells (l := 0) Fin.elim0 ∪ topBondCells c) : ℝ) by
        exact_mod_cast bondSpan_le_diameter hm fun l => mem_topBondCells l) (Nat.cast_nonneg _)
    have h4 := D.Dk_le 0 k (by omega) hk
    calc _ ≤ Dm * Real.exp (-(2 ^ 6 * κ * (bondSpan Y c : ℝ))) :=
          mul_le_mul h4 h3 (Real.exp_pos _).le D.Dm_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [D.Ch_nonneg]) (Real.exp_pos _).le
theorem cellSupDist_le_bondListDistance {k : ℕ} {Y : F.Cell} (c : Fin k → F.Site F.top × Fin 4) (l : Fin k) :
    cellSupDist Y (c l).1 ≤ bondListDistance Y c :=
  Finset.le_sup (f := fun l => cellSupDist Y (c l).1) (Finset.mem_univ l)
theorem exp_bondListDistance_le (hDist : SupDistCellComparison) {κ δ₂ : ℝ} (hκ : 0 < κ)
    (hr : 2 ^ 10 * κ ≤ δ₂) {k j : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    (c' : Fin j → F.Site F.top × Fin 4) (h : ∀ l, cellSupDist Y (c' l).1 ≤ bondListDistance Y c) :
    Real.exp (-(δ₂ / 8 * (bondListDistance Y c : ℝ))) ≤ Real.exp (-(2 ^ 6 * κ * (bondSpan Y c' : ℝ))) := by
  refine Real.exp_le_exp.2 ?_
  have h1 : (bondSpan Y c' : ℝ) ≤ 2 * (bondListDistance Y c : ℝ) := by
    exact_mod_cast bondSpan_le_two_mul hDist h
  have h2 : 2 ^ 6 * κ * (bondSpan Y c' : ℝ) ≤ 2 ^ 6 * κ * (2 * (bondListDistance Y c : ℝ)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 2 ^ 6 * κ * (2 * (bondListDistance Y c : ℝ)) ≤ δ₂ / 8 * (bondListDistance Y c : ℝ) := by
    nlinarith
  linarith
theorem exp_diameter_pair_le {κ δ₂ : ℝ} (hr : 2 ^ 7 * κ ≤ δ₂) (hκ : 0 < κ) {k : ℕ} {Y : F.Cell}
    {b : ↥(chordBonds (finiteCells F))} (hb : enclosingCell b.1.1 = Y) (b' : ↥(chordBonds (finiteCells F)))
    (c : Fin k → F.Site F.top × Fin 4) :
    Real.exp (-(δ₂ * (cellSetDiameter (∅ ∪ chordBondCells ![b', b] ∪ topBondCells c) : ℝ))) ≤
      Real.exp (-(δ₂ / 2 * (cellSupDist (enclosingCell b'.1.1) Y : ℝ))) *
        Real.exp (-(2 ^ 6 * κ * (bondSpan Y c : ℝ))) := by
  have m1 : enclosingCell b'.1.1 ∈ (∅ ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) := by
    simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b', b]) 0
  have m2 : Y ∈ (∅ ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) := by
    rw [← hb]
    simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b', b]) 1
  refine exp_le_exp_mul_exp hκ hr ?_ ?_ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact_mod_cast cellSupDist_le_diameter m1 m2
  · exact_mod_cast bondSpan_le_diameter m2 fun l => mem_topBondCells l
theorem deriv_top_le (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hRay : RayGradientSumSmoothAndBounded) (hRead : cellExponentRotatedEvalStatement)
    (hDist : SupDistCellComparison)
    (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V) {C : ℝ}
    (hC : (N : ℝ) * ρ + (Wt + N) / 2 * Dm + 4 * (Cg + Dm) + N * (Ch + Dm) ≤ C) (hk : k ≤ 3)
    (Y : F.Cell) (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < ρ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    |bondDeriv (fun V' => interpolatedBlockExponent s a ρA x m Y V' η) V c X| ≤
      C * (x * localSqNorm κ Y η + 1) * Real.exp (-(2 ^ 6 * κ * (bondSpan Y c : ℝ))) := by
  have hηc : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
  obtain ⟨hΨ, hexp⟩ := exponent_expansion hL hA hRay hRead D Y η hηc c X hX
  have e0 : bondDeriv (fun V' => interpolatedBlockExponent s a ρA x m Y V' η) V c X =
      derivAlong (rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X)
        (paramList F k) (η, 0) :=
    iteratedFDeriv_param_eq_derivAlong hL _ η (hΨ.of_le (coe_le_coe_of_le (by omega)))
  rw [e0, hexp (paramList F k) (by simp [paramList_length])]
  set E := Real.exp (-(2 ^ 6 * κ * (bondSpan Y c : ℝ))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set Q := cellChordBonds Y with hQ
  set Ad : ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b => Ct * ω * Real.exp (-(δ₂ / 8 * (bondListDistance (enclosingCell b.1.1) c : ℝ))) with hAd
  set Dd : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b b' => Dm * Real.exp (-(δ₂ * (cellSetDiameter (∅ ∪ chordBondCells ![b', b] ∪
      topBondCells c) : ℝ))) with hDd
  have hDd0 : ∀ b b', 0 ≤ Dd b b' := fun b b' => mul_nonneg D.Dm_nonneg (Real.exp_pos _).le
  have hbd := (hRay _ _ (Fin k → ℝ) (rotatedEval (interpolatedEnergy s a ρA m) V c X) Q η (parameterBasis k)
    (fun v hv => energy_contDiffAt D hA (v • η) (smul_mem_ball hηc hv) c X hX _)).2.1 Ad Dd hDd0
    (fun b e => energy_first_deriv_le hL hA hRead D hk c X hX b e)
    (fun v hv b b' e e' => energy_second_deriv_le hL hA D hk c X hX (v • η) (smul_mem_ball hηc hv) b b' e e')
  have hval := hbd.value_le
  have hκ := D.κ_pos
  have hr7 : 2 ^ 7 * κ ≤ δ₂ := by nlinarith [D.rate_le]
  have hx0 : 0 ≤ x := by linarith [D.one_le_x]
  have hρ := D.ρ_pos
  set d : ↥(chordBonds (finiteCells F)) → ℝ := fun b => (cellSupDist (enclosingCell b.1.1) Y : ℝ) with hd
  set av : ↥(chordBonds (finiteCells F)) → ℝ := fun b => ‖η b‖ with hav
  have hd0 : ∀ b, 0 ≤ d b := fun b => Nat.cast_nonneg _
  have hQ0 : ∀ b ∈ Q, d b = 0 := fun b hb => by
    simp only [hd]
    rw [enclosingCell_of_mem hb]
    have := (hDist.1 F F.top Y Y Y).1
    rw [siteSupDist_eq_cellSupDist] at this
    exact_mod_cast this
  have hg : 2 ^ 6 * κ ≤ δ₂ / 2 := by linarith
  have hAb : ∀ b ∈ Q, Ad b ≤ Ct * ω * E := by
    intro b hb
    simp only [hAd]
    rw [enclosingCell_of_mem hb]
    exact mul_le_mul_of_nonneg_left
      (exp_bondListDistance_le hDist hκ D.rate_le _ _ _ (fun l => cellSupDist_le_bondListDistance c l))
      D.Ctω_nonneg
  have hDb : ∀ b ∈ Q, ∀ b', Dd b b' ≤ Dm * E * Real.exp (-(δ₂ / 2 * d b')) := by
    intro b hb b'
    simp only [hDd]
    have h1 := exp_diameter_pair_le hr7 hκ (enclosingCell_of_mem hb) b' c
    calc _ ≤ Dm * (Real.exp (-(δ₂ / 2 * d b')) * E) := mul_le_mul_of_nonneg_left h1 D.Dm_nonneg
      _ = _ := by ring
  have hW0 : 0 ≤ Wt := (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans (D.weight_sum_le Y)
  have key : ∀ b ∈ Q, ‖η b‖ * (Ad b + ∑ b', ‖η b'‖ * Dd b b') ≤
      ρ * (Ct * ω * E) + Dm * E * ∑ b', av b * av b' * Real.exp (-(δ₂ / 2 * d b')) := by
    intro b hb
    rw [mul_add]
    refine add_le_add (mul_le_mul (hηc b) (hAb b hb) (mul_nonneg D.Ctω_nonneg (Real.exp_pos _).le)
      hρ.le) ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun b' _ => ?_
    have h1 := hDb b hb b'
    have h2 : 0 ≤ ‖η b‖ * ‖η b'‖ := by positivity
    calc ‖η b‖ * (‖η b'‖ * Dd b b') = ‖η b‖ * ‖η b'‖ * Dd b b' := by ring
      _ ≤ ‖η b‖ * ‖η b'‖ * (Dm * E * Real.exp (-(δ₂ / 2 * d b'))) := mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by simp only [hav]; ring
  have h2 := double_sum_le Q av d N (δ₂ / 2) (2 ^ 6 * κ) Wt hQ0 (D.card_le Y) hd0 hg (D.weight_sum_le Y)
  have hsq : weightedSq av d (2 ^ 6 * κ) = localSqNorm κ Y η := rfl
  rw [hsq] at h2
  set sq := localSqNorm κ Y η with hsqd
  have hsq0 : 0 ≤ sq := weightedSq_nonneg av d (2 ^ 6 * κ)
  have hcard : (Q.card : ℝ) ≤ N := by exact_mod_cast D.card_le Y
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h3 : |derivAlong (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) Q)
      (paramList F k) (η, 0)| ≤ N * (ρ * (Ct * ω * E)) + Dm * E * ((Wt + N) / 2 * sq) := by
    refine hval.trans ((Finset.sum_le_sum key).trans ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    have h4 : 0 ≤ ρ * (Ct * ω * E) := by have := D.Ctω_nonneg; positivity
    exact add_le_add (mul_le_mul_of_nonneg_right hcard h4)
      (mul_le_mul_of_nonneg_left h2 (mul_nonneg D.Dm_nonneg hE0.le))
  have hG : |∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      derivAlong (gapTerm s a ρA x m V c X c₀) (paramList F k) (η, 0)| ≤ 4 * ((Cg + Dm) * E) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c₀ hc₀ =>
      gapTerm_params_le hL hA D hk Y η hη c X hX c₀ hc₀).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    have h5 : ((((innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y)).card : ℕ) : ℝ) ≤ 4 := by
      exact_mod_cast card_innerBonds_at_cell_le Y
    exact mul_le_mul_of_nonneg_right h5 (mul_nonneg (add_nonneg D.Cg_nonneg D.Dm_nonneg) hE0.le)
  have hH : |∑ b ∈ Q, derivAlong (rotatedEval (interpolatedHaarLogRatio s a ρA m b) V c X)
      (paramList F k) (η, 0)| ≤ N * ((Ch + Dm) * E) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun b hb =>
      haar_params_le hL hA D hk Y η hη c X hX b hb).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (mul_nonneg (add_nonneg D.Ch_nonneg D.Dm_nonneg) hE0.le)
  have h6 : x * (N * (ρ * (Ct * ω * E))) ≤ N * ρ * E := by
    have := mul_le_mul_of_nonneg_right D.x_Ctω_le_one (show 0 ≤ N * ρ * E by positivity)
    nlinarith
  have hP0 : 0 ≤ (Wt + N) / 2 * Dm := mul_nonneg (by positivity) D.Dm_nonneg
  have hR0 : 0 ≤ (N : ℝ) * ρ + 4 * (Cg + Dm) + N * (Ch + Dm) := by
    have := D.Cg_nonneg; have := D.Ch_nonneg; have := D.Dm_nonneg; positivity
  have hfin : x * sq * ((Wt + N) / 2 * Dm) + ((N : ℝ) * ρ + 4 * (Cg + Dm) + N * (Ch + Dm)) ≤
      C * (x * sq + 1) := by
    have hxs : 0 ≤ x * sq := mul_nonneg hx0 hsq0
    have h7 : x * sq * ((Wt + N) / 2 * Dm) ≤ x * sq * C :=
      mul_le_mul_of_nonneg_left (by linarith) hxs
    have h8 : (N : ℝ) * ρ + 4 * (Cg + Dm) + N * (Ch + Dm) ≤ C := by linarith
    nlinarith
  have habs : ∀ u v w : ℝ, |u - v - w| ≤ |u| + |v| + |w| := fun u v w => by
    have h1 := abs_sub (u - v) w
    have h2 := abs_sub u v
    linarith
  refine (habs _ _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hx0]
  have h9 : x * |derivAlong (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) Q)
      (paramList F k) (η, 0)| ≤ N * ρ * E + x * sq * ((Wt + N) / 2 * Dm) * E := by
    have := mul_le_mul_of_nonneg_left h3 hx0
    rw [mul_add] at this
    refine this.trans (add_le_add h6 (le_of_eq ?_))
    ring
  calc _ ≤ (N * ρ * E + x * sq * ((Wt + N) / 2 * Dm) * E) + 4 * ((Cg + Dm) * E) + N * ((Ch + Dm) * E) :=
        add_le_add (add_le_add h9 hG) hH
    _ = (x * sq * ((Wt + N) / 2 * Dm) + ((N : ℝ) * ρ + 4 * (Cg + Dm) + N * (Ch + Dm))) * E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfin hE0.le
theorem deriv_top_partial_le (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hRay : RayGradientSumSmoothAndBounded) (hRead : cellExponentRotatedEvalStatement)
    (hDist : SupDistCellComparison)
    (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V) {C : ℝ}
    (hC : Dm * (N + 1) + 1 + Dm * (Wt + 1) + 4 * Dm + N * Dm ≤ C) (hk : k ≤ 3)
    (Y : F.Cell) (η : StepVariable (finiteCells F)) (b₀ : ↥(chordBonds (finiteCells F))) (e : BondVector)
    (hη : ∀ b, ‖η b‖ < ρ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (he : ‖e‖ = 1) :
    |bondDeriv (fun V' => bondPartialDeriv (interpolatedBlockExponent s a ρA x m Y V') b₀ η e) V c X| ≤
      C * (x * Real.sqrt (localSqNorm κ Y η) + 1) *
        Real.exp (-(2 ^ 6 * κ * (bondSpanWithCell Y (enclosingCell b₀.1.1) c : ℝ))) := by
  have hηc : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
  have R := hL.1 (JointSpace F k) ℝ
  obtain ⟨hΨ, hexp⟩ := exponent_expansion hL hA hRay hRead D Y η hηc c X hX
  have e0 : bondDeriv (fun V' => bondPartialDeriv (interpolatedBlockExponent s a ρA x m Y V') b₀ η e) V c X =
      derivAlong (rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X)
        (paramList F k ++ [bondSlot k b₀ e]) (η, 0) :=
    iteratedFDeriv_param_fderiv_eq_derivAlong hL _ η (bondVariation b₀ e)
      (hΨ.of_le (coe_le_coe_of_le (by omega)))
  rw [e0, hexp _ (by simp [paramList_length])]
  set E := Real.exp (-(2 ^ 6 * κ * (bondSpanWithCell Y (enclosingCell b₀.1.1) c : ℝ))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set Q := cellChordBonds Y with hQ
  set Ad : ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b => Ct * ω * Real.exp (-(δ₂ / 8 * (bondListDistance (enclosingCell b.1.1) c : ℝ))) with hAd
  set Dd : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b b' => Dm * Real.exp (-(δ₂ * (cellSetDiameter (∅ ∪ chordBondCells ![b', b] ∪
      topBondCells c) : ℝ))) with hDd
  have hDd0 : ∀ b b', 0 ≤ Dd b b' := fun b b' => mul_nonneg D.Dm_nonneg (Real.exp_pos _).le
  have hbd := (hRay _ _ (Fin k → ℝ) (rotatedEval (interpolatedEnergy s a ρA m) V c X) Q η (parameterBasis k)
    (fun v hv => energy_contDiffAt D hA (v • η) (smul_mem_ball hηc hv) c X hX _)).2.1 Ad Dd hDd0
    (fun b e => energy_first_deriv_le hL hA hRead D hk c X hX b e)
    (fun v hv b b' e e' => energy_second_deriv_le hL hA D hk c X hX (v • η) (smul_mem_ball hηc hv) b b' e e')
  have hval := hbd.deriv_le b₀ e
  rw [he, one_mul] at hval
  have hκ := D.κ_pos
  have hr7 : 2 ^ 7 * κ ≤ δ₂ := by nlinarith [D.rate_le]
  have hx0 : 0 ≤ x := by linarith [D.one_le_x]
  set d : ↥(chordBonds (finiteCells F)) → ℝ := fun b => (cellSupDist (enclosingCell b.1.1) Y : ℝ) with hd
  set av : ↥(chordBonds (finiteCells F)) → ℝ := fun b => ‖η b‖ with hav
  have hd0 : ∀ b, 0 ≤ d b := fun b => Nat.cast_nonneg _
  have hQ0 : ∀ b ∈ Q, d b = 0 := fun b hb => by
    simp only [hd]
    rw [enclosingCell_of_mem hb]
    have := (hDist.1 F F.top Y Y Y).1
    rw [siteSupDist_eq_cellSupDist] at this
    exact_mod_cast this
  have hg : 2 ^ 6 * κ ≤ δ₂ / 2 := by nlinarith [D.rate_le]
  have hsq : weightedSq av d (2 ^ 6 * κ) = localSqNorm κ Y η := rfl
  set r := Real.sqrt (localSqNorm κ Y η) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hW0 : 0 ≤ Wt := (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans (D.weight_sum_le Y)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hcard : (Q.card : ℝ) ≤ N := by exact_mod_cast D.card_le Y
  have h1 : ∑ b ∈ Q, ‖η b‖ * Dd b b₀ ≤ Dm * E * (((N : ℝ) + 1) * r) := by
    have hs1 := sum_le_sqrt_weightedSq Q av d N (2 ^ 6 * κ) hQ0 (D.card_le Y)
    rw [hsq] at hs1
    have hb1 : ∀ b ∈ Q, ‖η b‖ * Dd b b₀ ≤ Dm * E * av b := by
      intro b hb
      have m1 : enclosingCell b₀.1.1 ∈ (∅ ∪ chordBondCells ![b₀, b] ∪ topBondCells c : Finset F.Cell) := by
        simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b₀, b]) 0
      have m2 : Y ∈ (∅ ∪ chordBondCells ![b₀, b] ∪ topBondCells c : Finset F.Cell) := by
        rw [← enclosingCell_of_mem hb]
        simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b₀, b]) 1
      have h3 := exp_le_exp_of_rate hκ hr7 (show (bondSpanWithCell Y (enclosingCell b₀.1.1) c : ℝ) ≤
        (cellSetDiameter (∅ ∪ chordBondCells ![b₀, b] ∪ topBondCells c) : ℝ) by
          exact_mod_cast bondSpanWithCell_le_diameter m2 m1 fun l => mem_topBondCells l) (Nat.cast_nonneg _)
      have h4 : Dd b b₀ ≤ Dm * E := mul_le_mul_of_nonneg_left h3 D.Dm_nonneg
      have := mul_le_mul_of_nonneg_left h4 (norm_nonneg (η b))
      simp only [hav]
      linarith
    refine (Finset.sum_le_sum hb1).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hs1 (mul_nonneg D.Dm_nonneg hE0.le)
  have h2 : (if b₀ ∈ Q then Ad b₀ + ∑ b', ‖η b'‖ * Dd b₀ b' else 0) ≤
      Ct * ω * E + Dm * E * ((Wt + 1) * r) := by
    have hnn : 0 ≤ Ct * ω * E + Dm * E * ((Wt + 1) * r) := by
      have := D.Ctω_nonneg; have := D.Dm_nonneg; positivity
    split_ifs with hb0
    · have hY := enclosingCell_of_mem hb0
      have hs3 := sum_exp_le_sqrt_weightedSq av d (δ₂ / 2) (2 ^ 6 * κ) Wt hd0 hg (D.weight_sum_le Y)
      rw [hsq] at hs3
      have ha : Ad b₀ ≤ Ct * ω * E := by
        simp only [hAd, hE]
        rw [hY]
        refine mul_le_mul_of_nonneg_left (exp_bondListDistance_le hDist hκ D.rate_le _ c _ fun l => ?_)
          D.Ctω_nonneg
        refine Fin.cases ?_ (fun i => ?_) l
        · have : cellSupDist Y Y = 0 := by
            have := (hDist.1 F F.top Y Y Y).1
            rwa [siteSupDist_eq_cellSupDist] at this
          simp [this]
        · simpa using cellSupDist_le_bondListDistance c i
      have hb1 : ∀ b', ‖η b'‖ * Dd b₀ b' ≤ Dm * E * (av b' * Real.exp (-(δ₂ / 2 * d b'))) := by
        intro b'
        have m1 : enclosingCell b'.1.1 ∈ (∅ ∪ chordBondCells ![b', b₀] ∪ topBondCells c : Finset F.Cell) := by
          simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b', b₀]) 0
        have m2 : Y ∈ (∅ ∪ chordBondCells ![b', b₀] ∪ topBondCells c : Finset F.Cell) := by
          rw [← hY]
          simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b', b₀]) 1
        have h3 := exp_le_exp_mul_exp hκ hr7 (show d b' ≤
          (cellSetDiameter (∅ ∪ chordBondCells ![b', b₀] ∪ topBondCells c) : ℝ) by
            simp only [hd]
            exact_mod_cast cellSupDist_le_diameter m1 m2)
          (show (bondSpanWithCell Y (enclosingCell b₀.1.1) c : ℝ) ≤
            (cellSetDiameter (∅ ∪ chordBondCells ![b', b₀] ∪ topBondCells c) : ℝ) by
              rw [hY]
              exact_mod_cast bondSpanWithCell_le_diameter m2 m2 fun l => mem_topBondCells l)
          (hd0 b') (Nat.cast_nonneg _)
        have h4 : Dd b₀ b' ≤ Dm * (Real.exp (-(δ₂ / 2 * d b')) * E) :=
          mul_le_mul_of_nonneg_left h3 D.Dm_nonneg
        have := mul_le_mul_of_nonneg_left h4 (norm_nonneg (η b'))
        simp only [hav]
        nlinarith
      have h5 : ∑ b', ‖η b'‖ * Dd b₀ b' ≤ Dm * E * ((Wt + 1) * r) := by
        refine (Finset.sum_le_sum fun b' _ => hb1 b').trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hs3 (mul_nonneg D.Dm_nonneg hE0.le)
      linarith
    · exact hnn
  have h3 : |derivAlong (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) Q)
      (paramList F k ++ [bondSlot k b₀ e]) (η, 0)| ≤
      Dm * E * (((N : ℝ) + 1) * r) + (Ct * ω * E + Dm * E * ((Wt + 1) * r)) :=
    hval.trans (add_le_add h1 h2)
  have hlist : ∀ (f : JointSpace F k → ℝ), ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f (η, 0) →
      derivAlong f (paramList F k ++ [bondSlot k b₀ e]) (η, 0) =
        derivAlong f (bondSlot k b₀ e :: paramList F k) (η, 0) :=
    fun f hf => R.perm _ _ _ _ (List.perm_append_singleton _ _) (by
      rw [show (paramList F k ++ [bondSlot k b₀ e]).length = k + 1 by simp [paramList_length]]; exact hf)
  have hne : paramList F k ++ [bondSlot k b₀ e] ≠ [] := by simp
  have hG : |∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      derivAlong (gapTerm s a ρA x m V c X c₀) (paramList F k ++ [bondSlot k b₀ e]) (η, 0)| ≤
        4 * (Dm * E) := by
    have hb1 : ∀ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        |derivAlong (gapTerm s a ρA x m V c X c₀) (paramList F k ++ [bondSlot k b₀ e]) (η, 0)| ≤
          Dm * E := by
      intro c₀ hc₀
      have hY : c₀.1 = Y := (Finset.mem_filter.1 hc₀).2
      rw [derivAlong_gapTerm R D hA η hηc c₀ c X hX _ hne,
        hlist _ (gap_contDiffAt D hA η hηc c₀ c X hX _)]
      have h4 := derivAlong_one_bond_le _ V η c X hA R (gap_contDiffAt D hA η hηc c₀ c X hX _) b₀
        (B := Dm * E) (fun u hu => by
        have h5 := ((D.kernels η hηc).gap c₀ 1 k ![b₀] ![u] c X (by omega)
          (fun i => by fin_cases i; simpa using hu) hX).2
        refine h5.trans (mul_le_mul (D.Dk_le 1 k (by omega) hk)
          (exp_le_exp_of_coeff hκ ?_ (Nat.cast_nonneg _)) (Real.exp_pos _).le D.Dm_nonneg)
        have m1 : Y ∈ ({c₀.1} ∪ chordBondCells ![b₀] ∪ topBondCells c : Finset F.Cell) :=
          mem_union_left_left (by simp [hY])
        have m2 : enclosingCell b₀.1.1 ∈ ({c₀.1} ∪ chordBondCells ![b₀] ∪ topBondCells c : Finset F.Cell) := by
          simpa using mem_chordBondCells (P := {c₀.1}) (R := topBondCells c) (b := ![b₀]) 0
        exact_mod_cast bondSpanWithCell_le_diameter m1 m2 fun l => mem_topBondCells l) e
      rwa [he, one_mul] at h4
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hb1).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    have h5 : ((((innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y)).card : ℕ) : ℝ) ≤ 4 := by
      exact_mod_cast card_innerBonds_at_cell_le Y
    exact mul_le_mul_of_nonneg_right h5 (mul_nonneg D.Dm_nonneg hE0.le)
  have hH : |∑ b ∈ Q, derivAlong (rotatedEval (interpolatedHaarLogRatio s a ρA m b) V c X)
      (paramList F k ++ [bondSlot k b₀ e]) (η, 0)| ≤ N * (Dm * E) := by
    have hb1 : ∀ b ∈ Q, |derivAlong (rotatedEval (interpolatedHaarLogRatio s a ρA m b) V c X)
        (paramList F k ++ [bondSlot k b₀ e]) (η, 0)| ≤ Dm * E := by
      intro b hb
      have hY := enclosingCell_of_mem hb
      rw [hlist _ (haar_contDiffAt D hA η hηc b c X hX _)]
      have h4 := derivAlong_one_bond_le _ V η c X hA R (haar_contDiffAt D hA η hηc b c X hX _) b₀
        (B := Dm * E) (fun u hu => by
        have h5 := ((D.kernels η hηc).haar b 1 k ![b₀] ![u] c X (by omega)
          (fun i => by fin_cases i; simpa using hu) hX).2
        refine h5.trans (mul_le_mul (D.Dk_le 1 k (by omega) hk)
          (exp_le_exp_of_coeff hκ ?_ (Nat.cast_nonneg _)) (Real.exp_pos _).le D.Dm_nonneg)
        have m1 : Y ∈ ({enclosingCell b.1.1} ∪ chordBondCells ![b₀] ∪ topBondCells c : Finset F.Cell) :=
          mem_union_left_left (by simp [hY])
        have m2 : enclosingCell b₀.1.1 ∈
            ({enclosingCell b.1.1} ∪ chordBondCells ![b₀] ∪ topBondCells c : Finset F.Cell) := by
          simpa using mem_chordBondCells (P := {enclosingCell b.1.1}) (R := topBondCells c) (b := ![b₀]) 0
        exact_mod_cast bondSpanWithCell_le_diameter m1 m2 fun l => mem_topBondCells l) e
      rwa [he, one_mul] at h4
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hb1).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (mul_nonneg D.Dm_nonneg hE0.le)
  have habs : ∀ u v w : ℝ, |u - v - w| ≤ |u| + |v| + |w| := fun u v w => by
    have h1 := abs_sub (u - v) w
    have h2 := abs_sub u v
    linarith
  refine (habs _ _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hx0]
  have h9 : x * (Ct * ω * E) ≤ E := by
    have := mul_le_mul_of_nonneg_right D.x_Ctω_le_one hE0.le
    nlinarith
  have hxr : 0 ≤ x * r := mul_nonneg hx0 hr0
  have h10 : x * |derivAlong (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) Q)
      (paramList F k ++ [bondSlot k b₀ e]) (η, 0)| ≤
      (x * r * (Dm * (N + 1) + Dm * (Wt + 1)) + 1) * E := by
    have := mul_le_mul_of_nonneg_left h3 hx0
    refine this.trans ?_
    nlinarith
  have hfin : x * r * (Dm * (N + 1) + Dm * (Wt + 1)) + 1 + 4 * Dm + N * Dm ≤ C * (x * r + 1) := by
    have hDm := D.Dm_nonneg
    have a1 : 0 ≤ Dm * (N + 1) + Dm * (Wt + 1) := by positivity
    have a2 : 0 ≤ 4 * Dm + N * Dm := by positivity
    have h7 : x * r * (Dm * (N + 1) + Dm * (Wt + 1)) ≤ x * r * C :=
      mul_le_mul_of_nonneg_left (by linarith) hxr
    nlinarith
  calc _ ≤ (x * r * (Dm * (N + 1) + Dm * (Wt + 1)) + 1) * E + 4 * (Dm * E) + N * (Dm * E) :=
        add_le_add (add_le_add h10 hG) hH
    _ = (x * r * (Dm * (N + 1) + Dm * (Wt + 1)) + 1 + 4 * Dm + N * Dm) * E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfin hE0.le
theorem max_cellSupDist_le_diameter {P : Finset F.Cell} {Y u v : F.Cell} (hY : Y ∈ P) (hu : u ∈ P)
    (hv : v ∈ P) :
    max (cellSupDist Y u : ℝ) (max (cellSupDist Y v : ℝ) (cellSupDist u v : ℝ)) ≤
      (cellSetDiameter P : ℝ) := by
  have h1 : (cellSupDist Y u : ℝ) ≤ cellSetDiameter P := by exact_mod_cast cellSupDist_le_diameter hY hu
  have h2 : (cellSupDist Y v : ℝ) ≤ cellSetDiameter P := by exact_mod_cast cellSupDist_le_diameter hY hv
  have h3 : (cellSupDist u v : ℝ) ≤ cellSetDiameter P := by exact_mod_cast cellSupDist_le_diameter hu hv
  exact max_le h1 (max_le h2 h3)
theorem second_deriv_le (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hRay : RayGradientSumSmoothAndBounded) (hRead : cellExponentRotatedEvalStatement)
    (D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V) {C : ℝ}
    (hC : (N : ℝ) * ρ * Dm + 2 * Dm + 4 * Dm + N * Dm ≤ C)
    (Y : F.Cell) (η : StepVariable (finiteCells F)) (b b' : ↥(chordBonds (finiteCells F)))
    (e e' : BondVector) (hη : ∀ b, ‖η b‖ < ρ) (he : ‖e‖ = 1) (he' : ‖e'‖ = 1) :
    |secondDerivAlong (interpolatedBlockExponent s a ρA x m Y V) η (bondVariation b e) (bondVariation b' e')| ≤
      C * x * Real.exp (-(2 ^ 6 * κ * max (cellSupDist Y (enclosingCell b.1.1) : ℝ)
        (max (cellSupDist Y (enclosingCell b'.1.1) : ℝ)
          (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ)))) := by
  have hηc : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
  have R := hL.1 (JointSpace F 0) ℝ
  set c : Fin 0 → F.Site F.top × Fin 4 := Fin.elim0 with hc
  set X : Fin 0 → imaginaryQuaternions := Fin.elim0 with hXd
  have hX : AreUnitVectors X := fun i => i.elim0
  have hl : paramList F 0 = [] := by simp [parameterDirections, parameterBasis]
  obtain ⟨hΨ, hexp⟩ := exponent_expansion hL hA hRay hRead D Y η hηc c X hX
  have e0 : secondDerivAlong (interpolatedBlockExponent s a ρA x m Y V) η (bondVariation b e)
      (bondVariation b' e') =
      derivAlong (rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X)
        [bondSlot 0 b' e', bondSlot 0 b e] (η, 0) := by
    have h1 := fderiv_fderiv_eq_derivAlong hL
      (rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X) η
      (bondVariation b e) (bondVariation b' e') (by simpa using hΨ)
    have hf : (fun ζ' => rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X
        (ζ', 0)) = interpolatedBlockExponent s a ρA x m Y V := by
      funext ζ'
      simp only [rotatedEval, leftTranslate_bondSpread_zero]
    rw [hf] at h1
    exact h1
  rw [e0, hexp _ (by simp)]
  set M : ℝ := max (cellSupDist Y (enclosingCell b.1.1) : ℝ)
    (max (cellSupDist Y (enclosingCell b'.1.1) : ℝ)
      (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ)) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (Nat.cast_nonneg _)
  set E := Real.exp (-(2 ^ 6 * κ * M)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set Q := cellChordBonds Y with hQ
  set Dd : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b b' => Dm * Real.exp (-(δ₂ * (cellSetDiameter (∅ ∪ chordBondCells ![b', b] ∪
      topBondCells c) : ℝ))) with hDd
  set Hh : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) →
      ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b b' b'' => Dm * Real.exp (-(δ₂ * (cellSetDiameter (∅ ∪ chordBondCells ![b'', b', b] ∪
      topBondCells c) : ℝ))) with hHh
  have hDd0 : ∀ b b', 0 ≤ Dd b b' := fun b b' => mul_nonneg D.Dm_nonneg (Real.exp_pos _).le
  have hHh0 : ∀ b b' b'', 0 ≤ Hh b b' b'' := fun b b' b'' => mul_nonneg D.Dm_nonneg (Real.exp_pos _).le
  have hval := (hRay _ _ (Fin 0 → ℝ) (rotatedEval (interpolatedEnergy s a ρA m) V c X) Q η (parameterBasis 0)
    (fun v hv => energy_contDiffAt D hA (v • η) (smul_mem_ball hηc hv) c X hX _)).2.2
    (by simp [parameterBasis]) Dd Hh hDd0 hHh0
    (fun v hv b b' e e' => by
      have := energy_second_deriv_le hL hA D (Nat.zero_le 3) c X hX (v • η) (smul_mem_ball hηc hv) b b' e e'
      rw [hl] at this
      exact this)
    (fun v hv b b' b'' e e' e'' =>
      energy_third_deriv_le hL hA D c X hX (v • η) (smul_mem_ball hηc hv) b b' b'' e e' e'')
    b b' e e'
  rw [he, he', one_mul, one_mul] at hval
  have hκ := D.κ_pos
  have hr7 : 2 ^ 7 * κ ≤ δ₂ := by nlinarith [D.rate_le]
  have hx1 := D.one_le_x
  have hx0 : 0 ≤ x := by linarith
  have hDm := D.Dm_nonneg
  have hρ := D.ρ_pos
  have hcard : (Q.card : ℝ) ≤ N := by exact_mod_cast D.card_le Y
  have hDE : 0 ≤ Dm * E := mul_nonneg hDm hE0.le
  have h1 : ∑ b'' ∈ Q, ‖η b''‖ * Hh b'' b b' ≤ N * (ρ * (Dm * E)) := by
    have hb1 : ∀ b'' ∈ Q, ‖η b''‖ * Hh b'' b b' ≤ ρ * (Dm * E) := by
      intro b'' hb''
      have m0 : enclosingCell b'.1.1 ∈
          (∅ ∪ chordBondCells ![b', b, b''] ∪ topBondCells c : Finset F.Cell) := by
        simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b', b, b'']) 0
      have m1 : enclosingCell b.1.1 ∈
          (∅ ∪ chordBondCells ![b', b, b''] ∪ topBondCells c : Finset F.Cell) := by
        simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b', b, b'']) 1
      have m2 : Y ∈ (∅ ∪ chordBondCells ![b', b, b''] ∪ topBondCells c : Finset F.Cell) := by
        rw [← enclosingCell_of_mem hb'']
        simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b', b, b'']) 2
      have h3 := exp_le_exp_of_rate hκ hr7 (max_cellSupDist_le_diameter m2 m1 m0) hM0
      exact mul_le_mul (hηc b'') (mul_le_mul_of_nonneg_left h3 hDm) (hHh0 _ _ _) hρ.le
    refine (Finset.sum_le_sum hb1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have h2 : (if b ∈ Q then Dd b b' else 0) ≤ Dm * E := by
    split_ifs with hb
    · have m0 : enclosingCell b'.1.1 ∈ (∅ ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) := by
        simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b', b]) 0
      have m1 : enclosingCell b.1.1 ∈ (∅ ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) := by
        simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b', b]) 1
      have m2 : Y ∈ (∅ ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) := by
        rw [← enclosingCell_of_mem hb]
        exact m1
      exact mul_le_mul_of_nonneg_left (exp_le_exp_of_rate hκ hr7 (max_cellSupDist_le_diameter m2 m1 m0) hM0) hDm
    · exact hDE
  have h3 : (if b' ∈ Q then Dd b' b else 0) ≤ Dm * E := by
    split_ifs with hb
    · have m0 : enclosingCell b.1.1 ∈ (∅ ∪ chordBondCells ![b, b'] ∪ topBondCells c : Finset F.Cell) := by
        simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b, b']) 0
      have m1 : enclosingCell b'.1.1 ∈ (∅ ∪ chordBondCells ![b, b'] ∪ topBondCells c : Finset F.Cell) := by
        simpa using mem_chordBondCells (P := ∅) (R := topBondCells c) (b := ![b, b']) 1
      have m2 : Y ∈ (∅ ∪ chordBondCells ![b, b'] ∪ topBondCells c : Finset F.Cell) := by
        rw [← enclosingCell_of_mem hb]
        exact m1
      exact mul_le_mul_of_nonneg_left (exp_le_exp_of_rate hκ hr7 (max_cellSupDist_le_diameter m2 m0 m1) hM0) hDm
    · exact hDE
  have hray : |derivAlong (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) Q)
      [bondSlot 0 b' e', bondSlot 0 b e] (η, 0)| ≤ N * (ρ * (Dm * E)) + Dm * E + Dm * E :=
    hval.trans (add_le_add (add_le_add h1 h2) h3)
  have hne : ([bondSlot 0 b' e', bondSlot 0 b e] : List (JointSpace F 0)) ≠ [] := by simp
  have hG : |∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      derivAlong (gapTerm s a ρA x m V c X c₀) [bondSlot 0 b' e', bondSlot 0 b e] (η, 0)| ≤
        4 * (Dm * E) := by
    have hb1 : ∀ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        |derivAlong (gapTerm s a ρA x m V c X c₀) [bondSlot 0 b' e', bondSlot 0 b e] (η, 0)| ≤ Dm * E := by
      intro c₀ hc₀
      have hY : c₀.1 = Y := (Finset.mem_filter.1 hc₀).2
      rw [derivAlong_gapTerm R D hA η hηc c₀ c X hX _ hne]
      have h4 := derivAlong_two_bonds_le _ V η c X hA R (gap_contDiffAt D hA η hηc c₀ c X hX _) b b'
        (B := Dm * E) (fun u u' hu hu' => by
          have h5 := ((D.kernels η hηc).gap c₀ 2 0 ![b', b] ![u', u] c X (by omega)
            (fun i => by fin_cases i <;> simp [hu, hu']) hX).2
          refine h5.trans (mul_le_mul (D.Dk_le 2 0 (by omega) (by omega)) (exp_le_exp_of_coeff hκ ?_ hM0)
            (Real.exp_pos _).le hDm)
          have m1 : Y ∈ ({c₀.1} ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) :=
            mem_union_left_left (by simp [hY])
          have m2 : enclosingCell b'.1.1 ∈
              ({c₀.1} ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) := by
            simpa using mem_chordBondCells (P := {c₀.1}) (R := topBondCells c) (b := ![b', b]) 0
          have m3 : enclosingCell b.1.1 ∈
              ({c₀.1} ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) := by
            simpa using mem_chordBondCells (P := {c₀.1}) (R := topBondCells c) (b := ![b', b]) 1
          exact max_cellSupDist_le_diameter m1 m3 m2) e e'
      rw [he, he', one_mul, one_mul, hl] at h4
      exact h4
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hb1).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    have h5 : ((((innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y)).card : ℕ) : ℝ) ≤ 4 := by
      exact_mod_cast card_innerBonds_at_cell_le Y
    exact mul_le_mul_of_nonneg_right h5 hDE
  have hH : |∑ b₀ ∈ Q, derivAlong (rotatedEval (interpolatedHaarLogRatio s a ρA m b₀) V c X)
      [bondSlot 0 b' e', bondSlot 0 b e] (η, 0)| ≤ N * (Dm * E) := by
    have hb1 : ∀ b₀ ∈ Q, |derivAlong (rotatedEval (interpolatedHaarLogRatio s a ρA m b₀) V c X)
        [bondSlot 0 b' e', bondSlot 0 b e] (η, 0)| ≤ Dm * E := by
      intro b₀ hb₀
      have hY := enclosingCell_of_mem hb₀
      have h4 := derivAlong_two_bonds_le _ V η c X hA R (haar_contDiffAt D hA η hηc b₀ c X hX _) b b'
        (B := Dm * E) (fun u u' hu hu' => by
          have h5 := ((D.kernels η hηc).haar b₀ 2 0 ![b', b] ![u', u] c X (by omega)
            (fun i => by fin_cases i <;> simp [hu, hu']) hX).2
          refine h5.trans (mul_le_mul (D.Dk_le 2 0 (by omega) (by omega)) (exp_le_exp_of_coeff hκ ?_ hM0)
            (Real.exp_pos _).le hDm)
          have m1 : Y ∈ ({enclosingCell b₀.1.1} ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) :=
            mem_union_left_left (by simp [hY])
          have m2 : enclosingCell b'.1.1 ∈
              ({enclosingCell b₀.1.1} ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) := by
            simpa using mem_chordBondCells (P := {enclosingCell b₀.1.1}) (R := topBondCells c)
              (b := ![b', b]) 0
          have m3 : enclosingCell b.1.1 ∈
              ({enclosingCell b₀.1.1} ∪ chordBondCells ![b', b] ∪ topBondCells c : Finset F.Cell) := by
            simpa using mem_chordBondCells (P := {enclosingCell b₀.1.1}) (R := topBondCells c)
              (b := ![b', b]) 1
          exact max_cellSupDist_le_diameter m1 m3 m2) e e'
      rw [he, he', one_mul, one_mul, hl] at h4
      exact h4
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hb1).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hDE
  have habs : ∀ u v w : ℝ, |u - v - w| ≤ |u| + |v| + |w| := fun u v w => by
    have h1 := abs_sub (u - v) w
    have h2 := abs_sub u v
    linarith
  refine (habs _ _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hx0]
  have hT : 0 ≤ 4 * (Dm * E) + N * (Dm * E) := by positivity
  have e1 : x * |derivAlong (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) Q)
      [bondSlot 0 b' e', bondSlot 0 b e] (η, 0)| ≤ x * (N * (ρ * (Dm * E)) + Dm * E + Dm * E) :=
    mul_le_mul_of_nonneg_left hray hx0
  have e2 : 4 * (Dm * E) + N * (Dm * E) ≤ x * (4 * (Dm * E) + N * (Dm * E)) := by nlinarith
  have e3 : x * ((N : ℝ) * ρ * Dm + 2 * Dm + 4 * Dm + N * Dm) * E ≤ C * x * E := by
    have := mul_le_mul_of_nonneg_left hC hx0
    have := mul_le_mul_of_nonneg_right this hE0.le
    nlinarith
  calc _ ≤ x * (N * (ρ * (Dm * E)) + Dm * E + Dm * E) + 4 * (Dm * E) + N * (Dm * E) := by
        linarith [e1, hG, hH]
    _ ≤ x * (N * (ρ * (Dm * E)) + Dm * E + Dm * E) + x * (4 * (Dm * E) + N * (Dm * E)) := by linarith
    _ = x * ((N : ℝ) * ρ * Dm + 2 * Dm + 4 * Dm + N * Dm) * E := by ring
    _ ≤ _ := e3
end Core
end AtTop
open AtTop in
theorem interpolatedExponentBoundsAtTop (hL : DerivAlongRulesHold)
    (hA : JointMixedDerivEqDerivAlong) (hRay : RayGradientSumSmoothAndBounded)
    (hRead : cellExponentRotatedEvalStatement) (hDist : SupDistCellComparison) :
    interpolatedExponentBoundsAtTopStatement := by
  intro F s a ρA ρ x κ κ₂ δ₂ Ct ω C Cg Ch Wt Dm m N Kf Dk V hne hρ hκ hr hx hω0 hωx hCg hCh hDm hDl hcount hW
    hK hS hgap hhaar hC1 hC2 hC3
  have D : TopData s a ρA ρ x κ κ₂ δ₂ Ct ω Cg Ch Wt Dm m N Kf Dk V :=
    ⟨hne, hρ, hκ, hr, hx, hω0, hωx, hCg, hCh, hDm, hDl, hcount, hW, hK, hS, hgap, hhaar⟩
  exact ⟨fun Y η k c X hη hk hX => deriv_top_le hL hA hRay hRead hDist D hC1 hk Y η hη c X hX,
    fun Y η b e k c X hη hk hX he =>
      deriv_top_partial_le hL hA hRay hRead hDist D hC2 hk Y η b e hη c X hX he,
    fun Y η b b' e e' hη he he' => by
      have h := second_deriv_le hL hA hRay hRead D hC3 Y η b b' e e' hη he he'
      push_cast
      exact h⟩
end Interpolation
end YangMills.Construction
end
