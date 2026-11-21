import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbers
import YangMills.Construction.ColdStepAtMirrorFrames.ComponentsOfAFieldAlongAnElement
import YangMills.Construction.ColdStepAtMirrorFrames.ContourOfAChartField
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyAboutAChartPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.GlueOfTwoCharts
import YangMills.Construction.ColdStepAtMirrorFrames.HaarExcessNearZero
import YangMills.Construction.ColdStepAtMirrorFrames.OneLeastChart
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.SumsOverCellsAndBonds
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTwoMoves
import YangMills.Construction.ResponseInTheExpansion.ChartsOnTwoTori
import YangMills.Construction.ResponseInTheExpansion.EntriesMoveByTheirKernels
import YangMills.Construction.ResponseInTheExpansion.EntriesOnTwoTori
import YangMills.Construction.RunningCouplingSlope.InverseOfTheHessianOfTheChart
import YangMills.Construction.RunningCouplingSlope.ValueOfTheDensityOfTheStepOnTwoToriAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.BondsNearACellPairByOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.DistancesOfOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.HaarTermIsBounded
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeMovesByItsKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.StepDensityLocality
section Abstract
variable {I I' ι : Type} [Fintype I] [Fintype I'] [Fintype ι] [DecidableEq I] [DecidableEq I'] [DecidableEq ι]
private theorem sum_eq_sum_comp_add_sum_compl {e : ι → I} (he : Function.Injective e) (f : I → ℝ) :
    ∑ x, f x = ∑ l, f (e l) + ∑ x ∈ (Finset.univ.image e)ᶜ, f x := by
  rw [← Finset.sum_add_sum_compl (Finset.univ.image e) f, Finset.sum_image fun _ _ _ _ h => he h]
private theorem sum_comp_le_sum {e : ι → I} (he : Function.Injective e) {f : I → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ l, f (e l) ≤ ∑ x, f x := by
  rw [sum_eq_sum_comp_add_sum_compl he f]
  have : 0 ≤ ∑ x ∈ (Finset.univ.image e)ᶜ, f x := Finset.sum_nonneg fun x _ => hf x
  linarith
private theorem sum_compl_image_le_sum {e : ι → I} {f : I → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ (Finset.univ.image e)ᶜ, f x ≤ ∑ x, f x :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => hf x
private theorem exp_neg_two_mul_le_mul {γ s d : ℝ} (hγ : 0 ≤ γ) (h : s ≤ d) :
    Real.exp (-(2 * γ * d)) ≤ Real.exp (-(γ * s)) * Real.exp (-(γ * d)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith
private theorem exp_neg_two_mul_le {γ d : ℝ} (hγ : 0 ≤ γ) (h : 0 ≤ d) : Real.exp (-(2 * γ * d)) ≤ Real.exp (-(γ * d)) := by
  apply Real.exp_le_exp.2
  nlinarith [mul_nonneg hγ h]
private structure DecayingInverse (γ A B K : ℝ) (d : I → I → ℝ) (D : I → ℝ) (O R G : Matrix I I ℝ) : Prop where
  rate_pos : 0 < γ
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  K_nonneg : 0 ≤ K
  dist_nonneg : ∀ i j, 0 ≤ d i j
  dist_symm : ∀ i j, d i j = d j i
  dist_triangle : ∀ i j, D i ≤ D j + d i j
  inv_mul : R * O = 1
  mul_inv : O * R = 1
  abs_inv_le : ∀ i j, |R i j| ≤ A * Real.exp (-(2 * γ * d i j))
  abs_op_le : ∀ i j, |O i j| ≤ B * Real.exp (-(2 * γ * d i j))
  abs_aux_le : ∀ i j, |G i j| ≤ B * Real.exp (-(2 * γ * d i j))
  sum_exp_le : ∀ i, ∑ j, Real.exp (-(γ * d i j)) ≤ K
private structure IndexPairing (m : ℝ) (D : I → ℝ) (D' : I' → ℝ) (e : ι → I) (e' : ι → I') : Prop where
  injective_left : Function.Injective e
  injective_right : Function.Injective e'
  dist_eq : ∀ k, D (e k) = D' (e' k)
  surj_left : ∀ x, D x ≤ m → ∃ k, e k = x
  surj_right : ∀ x, D' x ≤ m → ∃ k, e' k = x
variable {γ A B K m : ℝ} {d : I → I → ℝ} {D : I → ℝ} {O R G : Matrix I I ℝ}
  {d' : I' → I' → ℝ} {D' : I' → ℝ} {O' R' G' : Matrix I' I' ℝ} {e : ι → I} {e' : ι → I'}
private theorem DecayingInverse.abs_inv_le_const (h : DecayingInverse γ A B K d D O R G) (i j : I) : |R i j| ≤ A := by
  refine (h.abs_inv_le i j).trans ?_
  have : Real.exp (-(2 * γ * d i j)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have := mul_nonneg h.rate_pos.le (h.dist_nonneg i j)
    linarith
  have := h.A_nonneg
  nlinarith
private theorem DecayingInverse.sum_comp_le (h : DecayingInverse γ A B K d D O R G) (he : Function.Injective e) (i : I) :
    ∑ l, Real.exp (-(γ * d i (e l))) ≤ K :=
  (sum_comp_le_sum he (f := fun x => Real.exp (-(γ * d i x))) fun _ => (Real.exp_pos _).le).trans (h.sum_exp_le i)
private theorem DecayingInverse.sum_compl_le (h : DecayingInverse γ A B K d D O R G) (i : I) :
    ∑ x ∈ (Finset.univ.image e)ᶜ, Real.exp (-(γ * d i x)) ≤ K :=
  (sum_compl_image_le_sum (f := fun x => Real.exp (-(γ * d i x))) fun _ => (Real.exp_pos _).le).trans (h.sum_exp_le i)
private theorem IndexPairing.lt_of_not_mem (hP : IndexPairing m D D' e e') {x : I} (hx : x ∈ (Finset.univ.image e)ᶜ) : m < D x := by
  by_contra hc
  obtain ⟨k, hk⟩ := hP.surj_left x (not_lt.1 hc)
  exact (Finset.mem_compl.1 hx) (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩)
private def inverseDefect (O' : Matrix I' I' ℝ) (R : Matrix I I ℝ) (e : ι → I) (e' : ι → I') (b : ι) (x : I') : ℝ :=
  ∑ l, O' x (e' l) * R (e l) (e b) - if x = e' b then 1 else 0
private theorem inv_sub_inv_eq_sum (hP : IndexPairing m D D' e e') (hR' : R' * O' = 1) (a b : ι) :
    R (e a) (e b) - R' (e' a) (e' b) = ∑ x, R' (e' a) x * inverseDefect O' R e e' b x := by
  have h1 : ∀ l, ∑ x, R' (e' a) x * O' x (e' l) = if a = l then 1 else 0 := by
    intro l
    have := congrFun (congrFun hR' (e' a)) (e' l)
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [this]
    simp [hP.injective_right.eq_iff]
  have h2 : ∑ x, R' (e' a) x * ∑ l, O' x (e' l) * R (e l) (e b) = R (e a) (e b) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ x, R' (e' a) x * (O' x (e' l) * R (e l) (e b)) =
        (if a = l then 1 else 0) * R (e l) (e b) := by
      intro l
      rw [← h1 l, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp only [this]
    simp
  unfold inverseDefect
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h2]
  simp
private theorem abs_inverseDefect_le_near (hS : DecayingInverse γ A B K d D O R G) (hP : IndexPairing m D D' e e') {ε : ℝ}
    (hε : 0 ≤ ε) (k b : ι) (hk : D (e k) ≤ m / 2) (hc : ∀ l, |O (e k) (e l) - O' (e' k) (e' l)| ≤ ε) :
    |inverseDefect O' R e e' b (e' k)| ≤ ε * A * K + A * B * K * Real.exp (-(γ * (m / 2))) := by
  have hγ := hS.rate_pos
  have hA := hS.A_nonneg
  have hB := hS.B_nonneg
  have hone : (if e' k = e' b then (1 : ℝ) else 0) = ∑ x, O (e k) x * R x (e b) := by
    have := congrFun (congrFun hS.mul_inv (e k)) (e b)
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [this]
    simp [hP.injective_left.eq_iff, hP.injective_right.eq_iff]
  have hsplit := sum_eq_sum_comp_add_sum_compl hP.injective_left (fun x => O (e k) x * R x (e b))
  have e1 : inverseDefect O' R e e' b (e' k) =
      ∑ l, (O' (e' k) (e' l) - O (e k) (e l)) * R (e l) (e b) -
        ∑ x ∈ (Finset.univ.image e)ᶜ, O (e k) x * R x (e b) := by
    unfold inverseDefect
    rw [hone, hsplit]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have b1 : |∑ l, (O' (e' k) (e' l) - O (e k) (e l)) * R (e l) (e b)| ≤ ε * A * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ l, |(O' (e' k) (e' l) - O (e k) (e l)) * R (e l) (e b)| ≤
        ε * A * Real.exp (-(γ * d (e b) (e l))) := by
      intro l
      rw [abs_mul, abs_sub_comm]
      have h1 := hc l
      have h2 := (hS.abs_inv_le (e l) (e b)).trans (mul_le_mul_of_nonneg_left
        (exp_neg_two_mul_le hγ.le (hS.dist_nonneg _ _)) hA)
      rw [hS.dist_symm (e l) (e b)] at h2
      calc _ ≤ ε * (A * Real.exp (-(γ * d (e b) (e l)))) :=
            mul_le_mul h1 h2 (abs_nonneg _) hε
        _ = _ := by ring
    refine (Finset.sum_le_sum fun l _ => this l).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hS.sum_comp_le hP.injective_left (e b)) (mul_nonneg hε hA)
  have b2 : |∑ x ∈ (Finset.univ.image e)ᶜ, O (e k) x * R x (e b)| ≤ A * B * K * Real.exp (-(γ * (m / 2))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ x ∈ (Finset.univ.image e)ᶜ, |O (e k) x * R x (e b)| ≤
        A * B * Real.exp (-(γ * (m / 2))) * Real.exp (-(γ * d (e k) x)) := by
      intro x hx
      rw [abs_mul]
      have hm := hP.lt_of_not_mem hx
      have ht := hS.dist_triangle x (e k)
      have hd : m / 2 ≤ d (e k) x := by
        rw [hS.dist_symm (e k) x]
        linarith
      have h1 := (hS.abs_op_le (e k) x).trans (mul_le_mul_of_nonneg_left (exp_neg_two_mul_le_mul hγ.le hd) hB)
      calc _ ≤ (B * (Real.exp (-(γ * (m / 2))) * Real.exp (-(γ * d (e k) x)))) * A :=
            mul_le_mul h1 (hS.abs_inv_le_const _ _) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.mul_sum]
    calc _ ≤ A * B * Real.exp (-(γ * (m / 2))) * K :=
          mul_le_mul_of_nonneg_left (hS.sum_compl_le (e k)) (by positivity)
      _ = _ := by ring
  rw [e1]
  exact (abs_sub _ _).trans (add_le_add b1 b2)
private theorem abs_inverseDefect_le (hS : DecayingInverse γ A B K d D O R G) (hS' : DecayingInverse γ A B K d' D' O' R' G')
    (hP : IndexPairing m D D' e e') (b : ι) (x : I') :
    |inverseDefect O' R e e' b x| ≤ A * B * K + 1 := by
  have hγ := hS.rate_pos
  have hA := hS.A_nonneg
  have hB := hS.B_nonneg
  have h1 : |∑ l, O' x (e' l) * R (e l) (e b)| ≤ A * B * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ l, |O' x (e' l) * R (e l) (e b)| ≤ A * B * Real.exp (-(γ * d' x (e' l))) := by
      intro l
      rw [abs_mul]
      have h2 := (hS'.abs_op_le x (e' l)).trans
        (mul_le_mul_of_nonneg_left (exp_neg_two_mul_le hγ.le (hS'.dist_nonneg _ _)) hB)
      calc _ ≤ (B * Real.exp (-(γ * d' x (e' l)))) * A :=
            mul_le_mul h2 (hS.abs_inv_le_const _ _) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum fun l _ => this l).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hS'.sum_comp_le hP.injective_right x) (by positivity)
  have h2 : |(if x = e' b then (1 : ℝ) else 0)| ≤ 1 := by
    split_ifs <;> simp
  unfold inverseDefect
  exact (abs_sub _ _).trans (add_le_add h1 h2)
private theorem abs_inv_sub_inv_le (hS : DecayingInverse γ A B K d D O R G) (hS' : DecayingInverse γ A B K d' D' O' R' G')
    (hP : IndexPairing m D D' e e') (hm : 0 ≤ m) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ k l, D (e k) ≤ m / 2 → |O (e k) (e l) - O' (e' k) (e' l)| ≤ ε) (a b : ι) (ha : D (e a) ≤ m / 4) :
    |R (e a) (e b) - R' (e' a) (e' b)| ≤
      A * K * (ε * A * K + (2 * (A * B * K) + 1) * Real.exp (-(γ * (m / 4)))) := by
  have hγ := hS.rate_pos
  have hA := hS.A_nonneg
  have hB := hS.B_nonneg
  have hK := hS.K_nonneg
  set Tot : ℝ := ε * A * K + (2 * (A * B * K) + 1) * Real.exp (-(γ * (m / 4))) with hTot
  have hABK : 0 ≤ A * B * K := by positivity
  have hx := Real.exp_pos (-(γ * (m / 4)))
  have hxx : Real.exp (-(γ * (m / 2))) ≤ Real.exp (-(γ * (m / 4))) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hterm : ∀ x, |R' (e' a) x * inverseDefect O' R e e' b x| ≤ A * Tot * Real.exp (-(γ * d' (e' a) x)) := by
    intro x
    rw [abs_mul]
    by_cases hxn : D' x ≤ m / 2
    · obtain ⟨k, rfl⟩ := hP.surj_right x (by linarith)
      have hk : D (e k) ≤ m / 2 := by rw [hP.dist_eq]; exact hxn
      have h1 := abs_inverseDefect_le_near hS hP hε k b hk fun l => hc k l hk
      have h2 : |inverseDefect O' R e e' b (e' k)| ≤ Tot := by
        refine h1.trans ?_
        rw [hTot]
        have : A * B * K * Real.exp (-(γ * (m / 2))) ≤ A * B * K * Real.exp (-(γ * (m / 4))) :=
          mul_le_mul_of_nonneg_left hxx hABK
        nlinarith
      have h3 := (hS'.abs_inv_le (e' a) (e' k)).trans (mul_le_mul_of_nonneg_left
        (exp_neg_two_mul_le hγ.le (hS'.dist_nonneg _ _)) hA)
      calc _ ≤ (A * Real.exp (-(γ * d' (e' a) (e' k)))) * Tot :=
            mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · have hxn' : m / 2 < D' x := not_le.1 hxn
      have ha' : D' (e' a) ≤ m / 4 := by rw [← hP.dist_eq]; exact ha
      have ht := hS'.dist_triangle x (e' a)
      have hd : m / 4 ≤ d' (e' a) x := by
        rw [hS'.dist_symm (e' a) x]
        linarith
      have h1 := abs_inverseDefect_le hS hS' hP b x
      have h3 := (hS'.abs_inv_le (e' a) x).trans (mul_le_mul_of_nonneg_left (exp_neg_two_mul_le_mul hγ.le hd) hA)
      have hy := Real.exp_pos (-(γ * d' (e' a) x))
      calc _ ≤ (A * (Real.exp (-(γ * (m / 4))) * Real.exp (-(γ * d' (e' a) x)))) * (A * B * K + 1) :=
            mul_le_mul h3 h1 (abs_nonneg _) (by positivity)
        _ = A * ((A * B * K + 1) * Real.exp (-(γ * (m / 4)))) * Real.exp (-(γ * d' (e' a) x)) := by ring
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA) hy.le
            rw [hTot]
            have : 0 ≤ ε * A * K := by positivity
            nlinarith
  rw [inv_sub_inv_eq_sum hP hS'.inv_mul a b]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun x _ => hterm x).trans ?_)
  rw [← Finset.mul_sum]
  calc _ ≤ A * Tot * K := mul_le_mul_of_nonneg_left (hS'.sum_exp_le _) (by positivity)
    _ = _ := by ring
private theorem abs_mul_inv_diag_sub_le (hS : DecayingInverse γ A B K d D O R G)
    (hS' : DecayingInverse γ A B K d' D' O' R' G') (hP : IndexPairing m D D' e e') (hm : 0 ≤ m) {ε ρ : ℝ} (hε : 0 ≤ ε)
    (hρ : 0 ≤ ρ) (a : ι) (hG : ∀ l, |G (e a) (e l) - G' (e' a) (e' l)| ≤ ε)
    (hR : ∀ l, D (e l) ≤ m / 4 → |R (e l) (e a) - R' (e' l) (e' a)| ≤ ρ)
    (ha : D (e a) ≤ m / 8) :
    |(G * R) (e a) (e a) - (G' * R') (e' a) (e' a)| ≤
      K * (ε * A + B * ρ + 4 * (A * B) * Real.exp (-(γ * (m / 8)))) := by
  have hγ := hS.rate_pos
  have hA := hS.A_nonneg
  have hB := hS.B_nonneg
  set X : ℝ := Real.exp (-(γ * (m / 8))) with hX
  have ha' : D' (e' a) ≤ m / 8 := by rw [← hP.dist_eq]; exact ha
  rw [Matrix.mul_apply, Matrix.mul_apply,
    sum_eq_sum_comp_add_sum_compl hP.injective_left (fun x => G (e a) x * R x (e a)),
    sum_eq_sum_comp_add_sum_compl hP.injective_right (fun x => G' (e' a) x * R' x (e' a))]
  have tail : |∑ x ∈ (Finset.univ.image e)ᶜ, G (e a) x * R x (e a)| ≤ A * B * K * X := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ x ∈ (Finset.univ.image e)ᶜ, |G (e a) x * R x (e a)| ≤ A * B * X * Real.exp (-(γ * d (e a) x)) := by
      intro x hx
      rw [abs_mul]
      have hm' := hP.lt_of_not_mem hx
      have ht := hS.dist_triangle x (e a)
      have hd : m / 8 ≤ d (e a) x := by
        rw [hS.dist_symm (e a) x]
        linarith
      have h1 := (hS.abs_aux_le (e a) x).trans (mul_le_mul_of_nonneg_left (exp_neg_two_mul_le_mul hγ.le hd) hB)
      calc _ ≤ (B * (X * Real.exp (-(γ * d (e a) x)))) * A :=
            mul_le_mul h1 (hS.abs_inv_le_const _ _) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.mul_sum]
    calc _ ≤ A * B * X * K := mul_le_mul_of_nonneg_left (hS.sum_compl_le (e a)) (by positivity)
      _ = _ := by ring
  have tail' : |∑ x ∈ (Finset.univ.image e')ᶜ, G' (e' a) x * R' x (e' a)| ≤ A * B * K * X := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ x ∈ (Finset.univ.image e')ᶜ, |G' (e' a) x * R' x (e' a)| ≤
        A * B * X * Real.exp (-(γ * d' (e' a) x)) := by
      intro x hx
      rw [abs_mul]
      have hm' : m < D' x := by
        by_contra hc
        obtain ⟨k, hk⟩ := hP.surj_right x (not_lt.1 hc)
        exact (Finset.mem_compl.1 hx) (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩)
      have ht := hS'.dist_triangle x (e' a)
      have hd : m / 8 ≤ d' (e' a) x := by
        rw [hS'.dist_symm (e' a) x]
        linarith
      have h1 := (hS'.abs_aux_le (e' a) x).trans (mul_le_mul_of_nonneg_left (exp_neg_two_mul_le_mul hγ.le hd) hB)
      calc _ ≤ (B * (X * Real.exp (-(γ * d' (e' a) x)))) * A :=
            mul_le_mul h1 (hS'.abs_inv_le_const _ _) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.mul_sum]
    calc _ ≤ A * B * X * K := mul_le_mul_of_nonneg_left (hS'.sum_compl_le (e' a)) (by positivity)
      _ = _ := by ring
  have hterm : ∀ l, |G (e a) (e l) * R (e l) (e a) - G' (e' a) (e' l) * R' (e' l) (e' a)| ≤
      (ε * A + A * B * X) * Real.exp (-(γ * d (e a) (e l))) +
        (B * ρ + A * B * X) * Real.exp (-(γ * d' (e' a) (e' l))) := by
    intro l
    by_cases hl : D (e l) ≤ m / 4
    · have e1 : G (e a) (e l) * R (e l) (e a) - G' (e' a) (e' l) * R' (e' l) (e' a) =
          (G (e a) (e l) - G' (e' a) (e' l)) * R (e l) (e a) +
            G' (e' a) (e' l) * (R (e l) (e a) - R' (e' l) (e' a)) := by ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have h2 := (hS.abs_inv_le (e l) (e a)).trans
        (mul_le_mul_of_nonneg_left (exp_neg_two_mul_le hγ.le (hS.dist_nonneg _ _)) hA)
      rw [hS.dist_symm (e l) (e a)] at h2
      have h3 := (hS'.abs_aux_le (e' a) (e' l)).trans
        (mul_le_mul_of_nonneg_left (exp_neg_two_mul_le hγ.le (hS'.dist_nonneg _ _)) hB)
      have c1 : |G (e a) (e l) - G' (e' a) (e' l)| * |R (e l) (e a)| ≤ ε * (A * Real.exp (-(γ * d (e a) (e l)))) :=
        mul_le_mul (hG l) h2 (abs_nonneg _) hε
      have c2 : |G' (e' a) (e' l)| * |R (e l) (e a) - R' (e' l) (e' a)| ≤
          (B * Real.exp (-(γ * d' (e' a) (e' l)))) * ρ :=
        mul_le_mul h3 (hR l hl) (abs_nonneg _) (by positivity)
      have c3 : 0 ≤ A * B * X * Real.exp (-(γ * d (e a) (e l))) := by positivity
      have c4 : 0 ≤ A * B * X * Real.exp (-(γ * d' (e' a) (e' l))) := by positivity
      nlinarith
    · have hl' : m / 4 < D (e l) := not_le.1 hl
      have t1 := hS.dist_triangle (e l) (e a)
      have t2 := hS'.dist_triangle (e' l) (e' a)
      rw [← hP.dist_eq l, ← hP.dist_eq a] at t2
      have hd : m / 8 ≤ d (e a) (e l) := by
        rw [hS.dist_symm (e a) (e l)]
        linarith
      have hd' : m / 8 ≤ d' (e' a) (e' l) := by
        rw [hS'.dist_symm (e' a) (e' l)]
        linarith
      have h1 := (hS.abs_aux_le (e a) (e l)).trans (mul_le_mul_of_nonneg_left (exp_neg_two_mul_le_mul hγ.le hd) hB)
      have h1' := (hS'.abs_aux_le (e' a) (e' l)).trans
        (mul_le_mul_of_nonneg_left (exp_neg_two_mul_le_mul hγ.le hd') hB)
      have c1 : |G (e a) (e l) * R (e l) (e a)| ≤ (B * (X * Real.exp (-(γ * d (e a) (e l))))) * A := by
        rw [abs_mul]
        exact mul_le_mul h1 (hS.abs_inv_le_const _ _) (abs_nonneg _) (by positivity)
      have c2 : |G' (e' a) (e' l) * R' (e' l) (e' a)| ≤ (B * (X * Real.exp (-(γ * d' (e' a) (e' l))))) * A := by
        rw [abs_mul]
        exact mul_le_mul h1' (hS'.abs_inv_le_const _ _) (abs_nonneg _) (by positivity)
      have c3 : 0 ≤ ε * A * Real.exp (-(γ * d (e a) (e l))) := by positivity
      have c4 : 0 ≤ B * ρ * Real.exp (-(γ * d' (e' a) (e' l))) := by positivity
      refine (abs_sub _ _).trans ?_
      nlinarith
  have main : |∑ l, G (e a) (e l) * R (e l) (e a) - ∑ l, G' (e' a) (e' l) * R' (e' l) (e' a)| ≤
      (ε * A + A * B * X) * K + (B * ρ + A * B * X) * K := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun l _ => hterm l).trans ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left (hS.sum_comp_le hP.injective_left _) (by positivity))
      (mul_le_mul_of_nonneg_left (hS'.sum_comp_le hP.injective_right _) (by positivity))
  have e2 : ∀ p q t t' : ℝ, p + t - (q + t') = (p - q) + t - t' := fun _ _ _ _ => by ring
  rw [e2]
  have := abs_sub ((∑ l, G (e a) (e l) * R (e l) (e a) - ∑ l, G' (e' a) (e' l) * R' (e' l) (e' a)) +
    ∑ x ∈ (Finset.univ.image e)ᶜ, G (e a) x * R x (e a))
    (∑ x ∈ (Finset.univ.image e')ᶜ, G' (e' a) x * R' x (e' a))
  have h2 := abs_add_le (∑ l, G (e a) (e l) * R (e l) (e a) - ∑ l, G' (e' a) (e' l) * R' (e' l) (e' a))
    (∑ x ∈ (Finset.univ.image e)ᶜ, G (e a) x * R x (e a))
  nlinarith
end Abstract
end YangMills.Construction.RunningCouplingSlope.StepDensityLocality
end
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.StepDensityLocality
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters
section Calculus
variable {ι : Type} [Fintype ι]
private theorem secondDerivAlong_eq_iteratedFDeriv {f : BondField ι → ℝ} {p : BondField ι} (h : ContDiffAt ℝ 2 f p)
    (u v : BondField ι) : secondDerivAlong f p u v = iteratedFDeriv ℝ 2 f p ![v, u] := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyLocal.secondDerivAlong_eq_iteratedFDeriv <;> assumption
private theorem iteratedFDeriv_comp_clm_zero {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (g : A →L[ℝ] BondField ι) (f : BondField ι → ℝ) (k : ℕ) (hf : ContDiffAt ℝ k f 0) (v : Fin k → A) :
    iteratedFDeriv ℝ k (f ∘ g) 0 v = iteratedFDeriv ℝ k f 0 (fun l => g (v l)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyLocal.iteratedFDeriv_comp_continuousLinearMap_zero <;> assumption
private theorem fderiv_fderiv_apply_zero {f : BondField ι → ℝ} (hf : ContDiffAt ℝ 3 f 0) (u v : BondField ι) :
    fderiv ℝ (fun ζ => fderiv ℝ f ζ v) 0 u = fderiv ℝ (fderiv ℝ f) 0 u v := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  have h3 := ((h2.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const v (0 : BondField ι))).fderiv
  rw [h3]
  simp
private theorem secondDerivAlong_eq_iteratedFDeriv_swap {f : BondField ι → ℝ} (hf : ContDiffAt ℝ 3 f 0)
    (u v : BondField ι) : secondDerivAlong f 0 u v = iteratedFDeriv ℝ 2 f 0 ![u, v] := by
  rw [← secondDerivAlong_eq_iteratedFDeriv (hf.of_le (by norm_num)) v u]
  unfold secondDerivAlong
  rw [fderiv_fderiv_apply_zero hf, fderiv_fderiv_apply_zero hf]
  exact (hf.isSymmSndFDerivAt (by simp; norm_num)).eq v u
end Calculus
section Kernels
variable {F : BlockFrame}
private abbrev CoordIndex (F : BlockFrame) : Type := ChartCoord F
private def bondDirection (b : ↥(chordBonds (finiteCells F))) (e : BondVector) :
    F.Site F.depth × Fin 4 × imaginaryQuaternions :=
  (b.1.1, b.1.2, toImaginary e)
private def indexDirection (i : CoordIndex F) : F.Site F.depth × Fin 4 × imaginaryQuaternions :=
  bondDirection i.1 (EuclideanSpace.single i.2 (1 : ℝ))
private theorem stepCoordinates_bondVariation (hLC : ImaginaryCoordinatesIsometric)
    (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (bondVariation b e : StepVariable (finiteCells F)) x i =
      directionCoordinate (.inl (bondDirection b e)) x i := by
  classical
  obtain ⟨_, hsm, _⟩ := hLC
  have z0 : toImaginary (0 : BondVector) = 0 := by
    have := hsm 0 (0 : BondVector)
    simpa using this
  simp only [stepCoordinates, directionCoordinate, bondDirection]
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h]
    by_cases hb : b = ⟨(x, i), h⟩
    · subst hb
      simp [bondVariation]
    · have h1 : ¬ (b.1.1 = x ∧ b.1.2 = i) := fun hh => hb (Subtype.ext (Prod.ext hh.1 hh.2))
      refine Eq.trans ?_ (if_neg h1).symm
      have : (bondVariation b e : StepVariable (finiteCells F)) ⟨(x, i), h⟩ = 0 := by
        simp [bondVariation, Ne.symm hb]
      rw [this, z0]
  · rw [dif_neg h]
    have h1 : ¬ (b.1.1 = x ∧ b.1.2 = i) := fun hh => h (by
      have : (x, i) = b.1 := Prod.ext hh.1.symm hh.2.symm
      rw [this]
      exact b.2)
    exact (if_neg h1).symm
private def stepCoordinatesLinear (hLC : ImaginaryCoordinatesIsometric) (x : F.Site F.depth) (i : Fin 4) :
    StepVariable (finiteCells F) →ₗ[ℝ] imaginaryQuaternions where
  toFun η := stepCoordinates η x i
  map_add' η ζ := by
    classical
    obtain ⟨ha, _⟩ := hLC
    simp only [stepCoordinates]
    split_ifs
    · exact ha _ _
    · simp
  map_smul' c η := by
    classical
    obtain ⟨_, hs, _⟩ := hLC
    simp only [stepCoordinates, RingHom.id_apply]
    split_ifs
    · exact hs _ _
    · simp
private theorem leftTranslate_zero (V : F.GaugeField F.top) :
    leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.SharedProofs.p46723 <;> assumption
private theorem chartRestriction_eq (hLC : ImaginaryCoordinatesIsometric) (a : ℝ)
    (p : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    {k : ℕ} (bs : Fin k → ↥(chordBonds (finiteCells F))) (es : Fin k → BondVector) (σ : Fin k → ℝ) :
    chartRestriction a p V (fun l => .inl (bondDirection (bs l) (es l))) σ =
      chartedEnergyAt a p V (∑ l, σ l • (bondVariation (bs l) (es l) : StepVariable (finiteCells F))) := by
  have e1 : ∀ x i, ∑ l, σ l • directionCoordinate (.inl (bondDirection (bs l) (es l))) x i =
      stepCoordinates (∑ l, σ l • (bondVariation (bs l) (es l) : StepVariable (finiteCells F))) x i := fun x i => by
    have := map_sum (stepCoordinatesLinear hLC x i)
      (fun l => σ l • (bondVariation (bs l) (es l) : StepVariable (finiteCells F))) Finset.univ
    refine Eq.trans ?_ this.symm
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul]
    show _ = σ l • stepCoordinates (bondVariation (bs l) (es l) : StepVariable (finiteCells F)) x i
    rw [stepCoordinates_bondVariation hLC]
  have e2 : leftTranslate (fun y i => ∑ l, σ l •
      directionMove (.inl (bondDirection (bs l) (es l)) : ChartDirection F) y i) V = V := by
    have : (fun y i => ∑ l, σ l • directionMove (.inl (bondDirection (bs l) (es l)) : ChartDirection F) y i) =
        fun _ _ => (0 : imaginaryQuaternions) := by
      funext y i
      exact Finset.sum_eq_zero fun l _ => by simp [directionMove]
    rw [this]
    exact leftTranslate_zero V
  unfold chartRestriction chartedEnergyAt
  rw [e2]
  simp only [e1]
private def variationLine {k : ℕ} (bs : Fin k → ↥(chordBonds (finiteCells F))) (es : Fin k → BondVector) :
    (Fin k → ℝ) →L[ℝ] StepVariable (finiteCells F) :=
  ∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight
    (bondVariation (bs l) (es l) : StepVariable (finiteCells F))
private theorem variationLine_apply {k : ℕ} (bs : Fin k → ↥(chordBonds (finiteCells F))) (es : Fin k → BondVector)
    (σ : Fin k → ℝ) :
    variationLine bs es σ = ∑ l, σ l • (bondVariation (bs l) (es l) : StepVariable (finiteCells F)) := by
  simp [variationLine]
private theorem variationLine_single {k : ℕ} (bs : Fin k → ↥(chordBonds (finiteCells F))) (es : Fin k → BondVector)
    (l : Fin k) : variationLine bs es (Pi.single l 1) = bondVariation (bs l) (es l) := by
  classical
  rw [variationLine_apply, Finset.sum_eq_single l]
  · simp
  · intro j _ hj
    simp [hj]
  · simp
private theorem chartHessian_eq_chartMixedDeriv (hLC : ImaginaryCoordinatesIsometric) (a : ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (hf : ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0) (i j : CoordIndex F) :
    chartHessian a w V i j = chartMixedDeriv a w V ![Sum.inl (indexDirection i), Sum.inl (indexDirection j)] := by
  set bs : Fin 2 → ↥(chordBonds (finiteCells F)) := ![i.1, j.1] with hbs
  set es : Fin 2 → BondVector := ![EuclideanSpace.single i.2 (1 : ℝ), EuclideanSpace.single j.2 (1 : ℝ)] with hes
  have e0 : (![Sum.inl (indexDirection i), Sum.inl (indexDirection j)] : Fin 2 → ChartDirection F) =
      fun l => .inl (bondDirection (bs l) (es l)) := by
    funext l
    fin_cases l <;> rfl
  have e1 : chartRestriction a w V (fun l => .inl (bondDirection (bs l) (es l))) =
      chartedEnergyAt a w V ∘ variationLine bs es := by
    funext σ
    rw [chartRestriction_eq hLC, Function.comp, variationLine_apply]
  have hf2 : ContDiffAt ℝ (2 : ℕ) (chartedEnergyAt a w V) 0 := hf.of_le (by norm_num)
  unfold chartMixedDeriv
  rw [e0, e1, iteratedFDeriv_comp_clm_zero _ _ 2 hf2]
  simp only [variationLine_single]
  have e2 : (fun l => (bondVariation (bs l) (es l) : StepVariable (finiteCells F))) =
      ![bondVariation i.1 (EuclideanSpace.single i.2 (1 : ℝ)), bondVariation j.1 (EuclideanSpace.single j.2 (1 : ℝ))] := by
    funext l
    fin_cases l <;> rfl
  rw [e2, ← secondDerivAlong_eq_iteratedFDeriv_swap hf]
  rfl
end Kernels
section Tops
variable {F : BlockFrame}
private structure MatchesStepParameters (T : ParameterAssignment) (c : ColdChainParameters) : Prop where
  delta_eq : c.δ₁ = T.δ₁
  lam_eq : c.lam = T.lam
  ρA_eq : c.ρA = T.ρA
  σA_eq : c.σA = T.σA
  N_eq : c.N = T.N
  admissible : c.Admissible T.coupling T.side
private def minimizer (a ρ : ℝ) (V : F.GaugeField F.top) : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  minimizingCoordinates a (finiteCells F) V ρ
private theorem coordsAboveFrame_eq (a ρ : ℝ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    coordsAboveFrame true a ρ 0 V η = fun x k => minimizer a ρ V x k + stepCoordinates η x k := by
  funext x k
  simp [coordsAboveFrame, stepFrame, minimizingBondCoordinate, minimizer]
private theorem chartedHessian_eq (a ρ : ℝ) (V : F.GaugeField F.top) :
    chartedHessian a ρ V 0 = chartHessian a (minimizer a ρ V) V := by
  funext i j
  unfold chartedHessian chartHessian chartedEnergyAtMinimizer
  simp only [coordsAboveFrame_eq]
private theorem stepCoordinates_zero (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  split_ifs
  · exact Subtype.ext (by simp [toImaginary]; rfl)
  · rfl
private theorem coordsAboveFrame_zero (a ρ : ℝ) (V : F.GaugeField F.top) :
    coordsAboveFrame true a ρ 0 V 0 = minimizer a ρ V := by
  rw [coordsAboveFrame_eq]
  funext x k
  rw [stepCoordinates_zero, add_zero]
abbrev _root_.YangMills.DeltaSharedProofs.p501121 := @coordsAboveFrame_zero
private theorem blockTorus_facts {L : ℕ} (hF : IsBlockTorus L F) (hL : Odd L) :
    Odd F.blockSide ∧ (∀ i, 2 ≤ F.extent i) ∧ (∀ i, 0 < F.extent i) := by
  obtain ⟨hFL, n, hn, hside⟩ := hF
  refine ⟨hFL ▸ hL, fun i => ?_, fun i => ?_⟩ <;> rw [hside i] <;> omega
private theorem isSmallCurvature_of_isCold (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j ≤ F.top)
    {s : ℝ} {X : F.GaugeField j} (h : IsCold (finiteCells F) j s X) : IsSmallCurvature s X := by
  intro p hp
  refine h p ?_
  unfold innerPlaquettes
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨mem_sitesOfCells_finiteCells hodd hs hj _, hp, fun x _ => mem_sitesOfCells_finiteCells hodd hs hj x⟩
abbrev _root_.YangMills.SharedProofs.p16091 := @isSmallCurvature_of_isCold
private theorem isCold_of_isSmallCurvature {j : ℕ} {s : ℝ} {X : F.GaugeField j} (h : IsSmallCurvature s X) :
    IsCold (finiteCells F) j s X := by
  intro p hp
  refine h p ?_
  unfold innerPlaquettes at hp
  simp only [Finset.mem_filter] at hp
  exact hp.2.1
variable {T : ParameterAssignment} {c : ColdChainParameters}
private structure MinimizerFacts (T : ParameterAssignment) (V : F.GaugeField F.top)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) : Prop where
  vanish_off : ∀ b, b ∉ chordBonds (finiteCells F) → w b.1 b.2 = 0
  norm_le : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ T.ρA
  norm_le_threshold : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ T.N 0 * (9 / 8 * T.threshold)
  small_curvature : IsSmallCurvature (9 / 8 * T.threshold / 8) (chartedField w V)
private theorem threshold_facts (hD : T.Admissible) : 0 < T.threshold ∧ 9 / 8 * T.threshold ≤ T.σA := by
  have h1 := hD.σ_pos
  have h2 := hD.σ_le
  exact ⟨h1, by linarith⟩
private theorem minimizerFacts (hOL : MinimizingChartUnique) (hD : T.Admissible) (hT : MatchesStepParameters T c)
    (hF : IsBlockTorus T.side F) {V : F.GaugeField F.top} (hV : IsSmallCurvature (9 / 8 * T.threshold) V) :
    MinimizerFacts T V (minimizer T.coupling T.ρA V) := by
  obtain ⟨hodd, hs2, hs1⟩ := blockTorus_facts hF hD.L_odd
  obtain ⟨hσ, hσA⟩ := threshold_facts hD
  obtain ⟨-, -, -, -, hρ1, -⟩ := hD.chain
  have hcl := hT.admissible.estimates F (9 / 8 * T.threshold) V hF (by positivity) (by rw [hT.σA_eq]; exact hσA) hV
  have hleast : HasColdMinimizer T.coupling T.ρA (T.N 0) (9 / 8 * T.threshold) (finiteCells F) V := by
    have h := hcl.minimizer
    rwa [hT.ρA_eq, hT.N_eq] at h
  obtain ⟨w, ⟨w0, w1, w2⟩, -, -⟩ := id hleast
  have hw : IsMinimizingChart T.coupling (finiteCells F) V T.ρA w :=
    ⟨w0, fun b hb => (w1 b hb).trans (min_le_left _ _), w2⟩
  have hw' : IsMinimizingChart T.coupling (finiteCells F) V T.ρA (minimizer T.coupling T.ρA V) := by
    have hex : ∃ w, IsMinimizingChart T.coupling (finiteCells F) V T.ρA w := ⟨w, hw⟩
    unfold minimizer minimizingCoordinates
    rw [dif_pos hex]
    exact hex.choose_spec
  have hone := hOL F T.coupling T.ρA (T.N 0) (9 / 8 * T.threshold) V _ hodd hs2 hρ1 hleast hw'
  refine ⟨hw'.1, hw'.2.1, ?_, isSmallCurvature_of_isCold hodd hs1 (Nat.le_succ _) hone.2⟩
  intro b hb
  rw [← hone.1 w hw]
  exact (w1 b hb).trans (min_le_right _ _)
private theorem admissible_of_near (hM : ChartLipschitz.ChartedFieldLipschitz) (hD : T.Admissible)
    (hF : IsBlockTorus T.side F) {V : F.GaugeField F.top} {w v : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : MinimizerFacts T V w) {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ T.threshold / 16)
    (hv : ∀ z i, ‖v z i - w z i‖ ≤ g) : IsAdmissibleChartPoint T.side T.σA v V := by
  obtain ⟨hσ, hσA⟩ := threshold_facts hD
  obtain ⟨-, -, -, -, -, -, -, hNpos, -⟩ := hD.chain
  have hL0 : (0 : ℝ) < T.side := by
    have := hD.L_odd.pos
    exact_mod_cast this
  have hσL := hD.σ_L
  have hN := hNpos 0
  refine ⟨fun b hb => ?_, fun p hp => ?_⟩
  · have h1 := hw.norm_le_threshold b hb
    have h2 := hv b.1 b.2
    have h3 : ‖v b.1 b.2‖ ≤ ‖w b.1 b.2‖ + g := by
      have := norm_add_le (v b.1 b.2 - w b.1 b.2) (w b.1 b.2)
      rw [sub_add_cancel] at this
      linarith
    have h4 : ‖v b.1 b.2‖ ≤ 2 * ((T.N 0 + 1) * T.threshold) := by nlinarith
    refine h4.trans ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have h1 := (hM.2 F v w V g hv hg0).2 p
    have h2 := hw.small_curvature p hp
    linarith
private def InverseDecayAt (T : ParameterAssignment) (CS κ : ℝ) : Prop :=
  ∀ F : BlockFrame, F.blockSide = T.side → IsLargeCubicTorus F →
      ∀ (s : ℝ) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ T.σA →
        IsCold (finiteCells F) F.top s V → IsBaseCoordinate T.ρA T.σA V w →
        (∀ i j, |chartHessian T.coupling w V i j| ≤ CS * Real.exp (-(T.δ₁ * coordDist i j))) ∧
        ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
          IsUnit (u • chartHessian T.coupling w V + (1 - u) • T.lam •
            (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)) ∧
          ∀ i j, |(u • chartHessian T.coupling w V + (1 - u) • T.lam •
              (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ))⁻¹ i j| ≤
            2 / T.lam * Real.exp (-(2 * κ * coordDist i j))
private def interpolatedOp (H : Matrix (CoordIndex F) (CoordIndex F) ℝ) (lam u : ℝ) :
    Matrix (CoordIndex F) (CoordIndex F) ℝ :=
  u • H + (1 - u) • lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)
private def distFromCell (Y : F.Cell) (i : CoordIndex F) : ℝ := (cellSupDist (enclosingCell i.1.1.1) Y : ℕ)
private theorem sum_exp_coordDist_le (hcov : BlocksCoverLowerLevel) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) {κ M : ℝ} (hM : ∀ (F : BlockFrame) (c : F.Cell), (∀ i, 2 ≤ F.extent i) →
      ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ M) (i : CoordIndex F) :
    ∑ j : CoordIndex F, Real.exp (-(κ * (coordDist i j : ℝ))) ≤ 3 * (4 * ((centredCube F.blockSide).card : ℝ) * M) := by
  set g : F.Cell → ℝ := fun z => Real.exp (-(κ * cellSupDist z (enclosingCell i.1.1.1))) with hg
  have e1 : ∑ j : CoordIndex F, Real.exp (-(κ * (coordDist i j : ℝ))) =
      3 * ∑ b ∈ chordBonds (finiteCells F), g (enclosingCell b.1) := by
    rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort (chordBonds (finiteCells F)) fun b => g (enclosingCell b.1),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb : ∀ α : Fin 3, Real.exp (-(κ * (coordDist i (b, α) : ℝ))) = g (enclosingCell b.1.1) := fun α => by
      unfold coordDist
      rw [CellSums.cellSupDist_comm (enclosingCell i.1.1.1)]
    simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [e1]
  have h2 := CellSums.sum_bonds_le_sum_cells hcov hodd hs g (fun _ => (Real.exp_pos _).le)
    (chordBonds (finiteCells F))
  have h3 := hM F (enclosingCell i.1.1.1) hs
  have h4 : (0 : ℝ) ≤ 4 * ((centredCube F.blockSide).card : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left h3 h4
  linarith
private theorem decayingInverse_of_top (hcov : BlocksCoverLowerLevel) (hOL : MinimizingChartUnique) (hD : T.Admissible)
    (hT : MatchesStepParameters T c) {CS κ M : ℝ} (hCS : 0 ≤ CS) (hκ : 0 < κ) (hκδ : κ ≤ T.δ₁ / 8) (hI : InverseDecayAt T CS κ)
    (hMs : ∀ (F : BlockFrame) (c : F.Cell), (∀ i, 2 ≤ F.extent i) →
      ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ M) (hM0 : 0 ≤ M)
    (hF : IsBlockTorus T.side F) {V : F.GaugeField F.top} (hV : IsSmallCurvature (9 / 8 * T.threshold) V) (Y : F.Cell)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    DecayingInverse κ (2 / T.lam) (CS + T.lam) (3 * (4 * ((centredCube T.side).card : ℝ) * M))
      (fun i j : CoordIndex F => (coordDist i j : ℝ)) (distFromCell Y)
      (interpolatedOp (chartedHessian T.coupling T.ρA V 0) T.lam u)
      (interpolatedOp (chartedHessian T.coupling T.ρA V 0) T.lam u)⁻¹
      (chartedHessian T.coupling T.ρA V 0 - T.lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) := by
  obtain ⟨hodd, hs2, hs1⟩ := blockTorus_facts hF hD.L_odd
  obtain ⟨hσ, hσA⟩ := threshold_facts hD
  obtain ⟨hδ, -, hlam, -⟩ := hD.chain
  have hw := minimizerFacts hOL hD hT hF hV
  have hFL : F.blockSide = T.side := hF.1
  have hfl : IsBaseCoordinate T.ρA T.σA V (minimizer T.coupling T.ρA V) := by
    refine ⟨hw.vanish_off, hw.norm_le, fun b hb => ?_, ?_⟩
    · refine (hw.norm_le_threshold b hb).trans ?_
      have hL0 : (0 : ℝ) < T.side := by
        have := hD.L_odd.pos
        exact_mod_cast this
      have hσL := hD.σ_L
      obtain ⟨-, -, -, -, -, -, -, hNpos, -⟩ := hD.chain
      have hN := hNpos 0
      rw [hFL, le_div_iff₀ (by positivity)]
      nlinarith
    · intro p hp
      have := isCold_of_isSmallCurvature hw.small_curvature p hp
      linarith
  obtain ⟨hent, hinv⟩ := hI F hFL hF.2 (9 / 8 * T.threshold) V _ (by positivity) hσA (isCold_of_isSmallCurvature hV) hfl
  obtain ⟨hunit, hRle⟩ := hinv u hu0 hu1
  have eH := chartedHessian_eq T.coupling T.ρA V
  have eO : interpolatedOp (chartedHessian T.coupling T.ρA V 0) T.lam u =
      u • chartHessian T.coupling (minimizer T.coupling T.ρA V) V +
        (1 - u) • T.lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ) := by
    rw [eH]
    rfl
  have hdet : IsUnit (interpolatedOp (chartedHessian T.coupling T.ρA V 0) T.lam u).det := by
    rw [eO]
    exact (Matrix.isUnit_iff_isUnit_det _).1 hunit
  set H := chartedHessian T.coupling T.ρA V 0 with hH
  have hdec : ∀ i j : CoordIndex F, |H i j| ≤ CS * Real.exp (-(2 * κ * (coordDist i j : ℝ))) := by
    intro i j
    have h1 := hent i j
    rw [← eH] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCS)
    have : (0 : ℝ) ≤ (coordDist i j : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hone : ∀ i j : CoordIndex F,
      |(1 : Matrix (CoordIndex F) (CoordIndex F) ℝ) i j| ≤ Real.exp (-(2 * κ * (coordDist i j : ℝ))) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have : coordDist i i = 0 := by
        unfold coordDist cellSupDist
        simp
      simp [this]
    · rw [Matrix.one_apply_ne hij, abs_zero]
      exact (Real.exp_pos _).le
  refine ⟨hκ, by positivity, by positivity, by positivity, fun i j => Nat.cast_nonneg _, fun i j => ?_, fun i j => ?_,
    Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet, fun i j => ?_, fun i j => ?_, fun i j => ?_,
    fun i => ?_⟩
  · unfold coordDist
    rw [CellSums.cellSupDist_comm]
  · show distFromCell Y i ≤ distFromCell Y j + (coordDist i j : ℝ)
    unfold distFromCell coordDist
    have := CellSums.cellSupDist_triangle hs1 (enclosingCell i.1.1.1) (enclosingCell j.1.1.1) Y
    have h3 : cellSupDist (enclosingCell i.1.1.1) Y ≤
        cellSupDist (enclosingCell j.1.1.1) Y + cellSupDist (enclosingCell i.1.1.1) (enclosingCell j.1.1.1) := by
      omega
    exact_mod_cast h3
  · rw [eO]
    exact hRle i j
  · have e : interpolatedOp H T.lam u i j =
        u * H i j + (1 - u) * (T.lam * (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ) i j) := by
      simp [interpolatedOp, Matrix.add_apply, Matrix.smul_apply]
    rw [e]
    have hE := Real.exp_pos (-(2 * κ * (coordDist i j : ℝ)))
    have a1 := hdec i j
    have a2 := hone i j
    have b1 : |u * H i j| ≤ CS * Real.exp (-(2 * κ * (coordDist i j : ℝ))) := by
      rw [abs_mul, abs_of_nonneg hu0]
      nlinarith [abs_nonneg (H i j)]
    have b2 : |(1 - u) * (T.lam * (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ) i j)| ≤
        T.lam * Real.exp (-(2 * κ * (coordDist i j : ℝ))) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - u), abs_of_pos hlam]
      have := abs_nonneg ((1 : Matrix (CoordIndex F) (CoordIndex F) ℝ) i j)
      have h5 : T.lam * |(1 : Matrix (CoordIndex F) (CoordIndex F) ℝ) i j| ≤
          T.lam * Real.exp (-(2 * κ * (coordDist i j : ℝ))) :=
        mul_le_mul_of_nonneg_left a2 hlam.le
      have h6 : 0 ≤ T.lam * |(1 : Matrix (CoordIndex F) (CoordIndex F) ℝ) i j| := by positivity
      nlinarith
    refine (abs_add_le _ _).trans ?_
    linarith
  · have e : (H - T.lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) i j =
        H i j - T.lam * (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ) i j := by
      simp [Matrix.sub_apply, Matrix.smul_apply]
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos hlam]
    have := mul_le_mul_of_nonneg_left (hone i j) hlam.le
    have := hdec i j
    linarith
  · have h := sum_exp_coordDist_le hcov hodd hs2 hMs i
    rwa [hFL] at h
end Tops
end YangMills.Construction.RunningCouplingSlope.StepDensityLocality
end
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open scoped Quaternion
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters TorusComparison Estimates ChartResponse
  SecondOrderMoves ChartLipschitz
namespace StepDensityLocality
section Offsets
variable {F F' : BlockFrame}
private theorem add_siteOfCoords_zero (G : BlockFrame) (Z : G.Cell) : Z + siteOfCoords G.top (0 : Fin 4 → ℤ) = Z := by
  funext i
  simp [siteOfCoords]
abbrev _root_.YangMills.SharedProofs.p55653 := @add_siteOfCoords_zero
private theorem offsets_unique (hD : cellOffsetStatement) (hS : SiteDecomposition) {G : BlockFrame}
    (hG : Odd G.blockSide) {q : ℕ} (hs : ∀ i, 2 * q + 2 < G.extent i) (Z : G.Cell) {h h₁ o o₁ : Fin 4 → ℤ}
    {k k₁ : Fin 4} (hh : ∀ l, 2 * |h l| ≤ q) (hh₁ : ∀ l, 2 * |h₁ l| ≤ q) (ho : o ∈ centredCube G.blockSide)
    (ho₁ : o₁ ∈ centredCube G.blockSide) (e : (fineBondAt Z h o k).1 = (fineBondAt Z h₁ o₁ k₁).1) : h = h₁ ∧ o = o₁ := by
  have hs2 : ∀ i, 2 ≤ G.extent i := fun i => by
    have := hs i
    omega
  have e1 : cellCentre G.depth (Z + siteOfCoords G.top h) + siteOfCoords G.depth o =
      cellCentre G.depth (Z + siteOfCoords G.top h₁) + siteOfCoords G.depth o₁ := e
  obtain ⟨c1, c2⟩ := (hS G hG hs2).1 (Z + siteOfCoords G.top h) o ho
  obtain ⟨c3, c4⟩ := (hS G hG hs2).1 (Z + siteOfCoords G.top h₁) o₁ ho₁
  have e3 : Z + siteOfCoords G.top h = Z + siteOfCoords G.top h₁ := by
    rw [← c1, e1, c3]
  have e4 : o = o₁ := by
    rw [← c2, e1, c4]
  obtain ⟨-, -, -, hd⟩ := hD G hG hs2
  have a1 := (hd q hs Z h h₁ hh hh₁).1
  have a2 := (hd q hs Z h₁ h hh₁ hh).1
  refine ⟨?_, e4⟩
  rw [e3] at a1
  rw [← a1, a2]
private theorem cellSupDist_offset (hD : cellOffsetStatement) {G : BlockFrame} (hG : Odd G.blockSide) {q : ℕ}
    (hs : ∀ i, 2 * q + 2 < G.extent i) (Z : G.Cell) {h : Fin 4 → ℤ} (hh : ∀ l, 2 * |h l| ≤ q) :
    cellSupDist (Z + siteOfCoords G.top h) Z = Finset.univ.sup fun i => (h i).natAbs := by
  have hs2 : ∀ i, 2 ≤ G.extent i := fun i => by
    have := hs i
    omega
  obtain ⟨-, -, -, hd⟩ := hD G hG hs2
  have h0 : ∀ l, 2 * |(0 : Fin 4 → ℤ) l| ≤ (q : ℤ) := fun l => by simp
  have a := (hd q hs Z h 0 hh h0).2
  rw [add_siteOfCoords_zero] at a
  rw [a]
  simp
private theorem cellSupDist_offset_le (hD : cellOffsetStatement) {G : BlockFrame} (hG : Odd G.blockSide) {q r : ℕ}
    (hs : ∀ i, 2 * q + 2 < G.extent i) (Z : G.Cell) {h : Fin 4 → ℤ} (hh : ∀ l, 2 * |h l| ≤ q)
    (hr : WithinRadius r h) : cellSupDist (Z + siteOfCoords G.top h) Z ≤ r := by
  rw [cellSupDist_offset hD hG hs Z hh]
  refine Finset.sup_le fun i _ => ?_
  have := hr i
  rw [Int.abs_eq_natAbs] at this
  omega
private def SameOffsets (Y : F.Cell) (Y' : F'.Cell) (Q : ℕ) (i : CoordIndex F) (i' : CoordIndex F') : Prop :=
  i.2 = i'.2 ∧ ∃ (h o : Fin 4 → ℤ) (k : Fin 4), (∀ l, 2 * |h l| ≤ Q) ∧ o ∈ centredCube F.blockSide ∧
    i.1.1 = fineBondAt Y h o k ∧ i'.1.1 = fineBondAt Y' h o k
private theorem directionCoordinate_match (hD : cellOffsetStatement) (hS : SiteDecomposition) (hG : Odd F.blockSide)
    (hG' : Odd F'.blockSide) (hL : F'.blockSide = F.blockSide) {Q : ℕ} (hs : ∀ i, 2 * Q + 2 < F.extent i)
    (hs' : ∀ i, 2 * Q + 2 < F'.extent i) {Y : F.Cell} {Y' : F'.Cell} {i : CoordIndex F} {i' : CoordIndex F'}
    (hi : SameOffsets Y Y' Q i i') {h o : Fin 4 → ℤ} (k : Fin 4)
    (hh : ∀ l, 2 * |h l| ≤ Q) (ho : o ∈ centredCube F.blockSide) :
    directionCoordinate (.inl (indexDirection i)) (fineBondAt Y h o k).1 k =
      directionCoordinate (.inl (indexDirection i')) (fineBondAt Y' h o k).1 k := by
  obtain ⟨e0, h₀, o₀, k₀, hh₀, ho₀, e₁, e₂⟩ := hi
  have ho' : o ∈ centredCube F'.blockSide := hL ▸ ho
  have ho₀' : o₀ ∈ centredCube F'.blockSide := hL ▸ ho₀
  have p1 : (indexDirection i).1 = (fineBondAt Y h₀ o₀ k₀).1 := by
    show i.1.1.1 = _
    rw [e₁]
  have p2 : (indexDirection i).2.1 = k₀ := by
    show i.1.1.2 = _
    rw [e₁]
    rfl
  have p1' : (indexDirection i').1 = (fineBondAt Y' h₀ o₀ k₀).1 := by
    show i'.1.1.1 = _
    rw [e₂]
  have p2' : (indexDirection i').2.1 = k₀ := by
    show i'.1.1.2 = _
    rw [e₂]
    rfl
  have p3 : (indexDirection i).2.2 = (indexDirection i').2.2 := by
    show toImaginary (EuclideanSpace.single i.2 (1 : ℝ)) = toImaginary (EuclideanSpace.single i'.2 (1 : ℝ))
    rw [e0]
  simp only [directionCoordinate]
  by_cases hc : (indexDirection i).1 = (fineBondAt Y h o k).1 ∧ (indexDirection i).2.1 = k
  · have hc' : (indexDirection i').1 = (fineBondAt Y' h o k).1 ∧ (indexDirection i').2.1 = k := by
      obtain ⟨a, b⟩ := hc
      rw [p1] at a
      rw [p2] at b
      obtain ⟨rfl, rfl⟩ := offsets_unique hD hS hG hs Y hh₀ hh ho₀ ho a
      exact ⟨p1', p2'.trans b⟩
    exact (if_pos hc).trans (p3.trans (if_pos hc').symm)
  · have hc' : ¬ ((indexDirection i').1 = (fineBondAt Y' h o k).1 ∧ (indexDirection i').2.1 = k) := by
      rintro ⟨a, b⟩
      rw [p1'] at a
      rw [p2'] at b
      obtain ⟨rfl, rfl⟩ := offsets_unique hD hS hG' hs' Y' hh₀ hh ho₀' ho' a
      exact hc ⟨p1, p2.trans b⟩
    exact (if_neg hc).trans (if_neg hc').symm
private def pairedIndex {ι : Type} {G : BlockFrame} (j : ι → ↥(chordBonds (finiteCells G))) (k : ι × Fin 3) :
    CoordIndex G := (j k.1, k.2)
private theorem indexPairing_of_short (hD : cellOffsetStatement) (hG : Odd F.blockSide) (hG' : Odd F'.blockSide)
    (hL : F'.blockSide = F.blockSide) {q : ℕ} (hs : ∀ i, 2 * q + 2 < F.extent i) (hs' : ∀ i, 2 * q + 2 < F'.extent i)
    {Y : F.Cell} {Y' : F'.Cell} {ι : Type} {j : ι → ↥(chordBonds (finiteCells F))}
    {j' : ι → ↥(chordBonds (finiteCells F'))} (hN : IsShortPairing Y Y' q j j') :
    IndexPairing ((q : ℝ) / 2) (distFromCell Y) (distFromCell Y') (pairedIndex j) (pairedIndex j') := by
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    have := hs i
    omega
  have hs2' : ∀ i, 2 ≤ F'.extent i := fun i => by
    have := hs' i
    omega
  have cov : ∀ {G : BlockFrame} (Z : G.Cell) (l : ι → ↥(chordBonds (finiteCells G)))
      (hr : ∀ b, b ∈ bondsNearCell Z q ↔ ∃ i, l i = b) (x : CoordIndex G), distFromCell Z x ≤ (q : ℝ) / 2 →
      ∃ k, pairedIndex l k = x := by
    intro G Z l hr x hx
    have h1 : 2 * cellSupDist (enclosingCell x.1.1.1) Z ≤ q := by
      unfold distFromCell at hx
      have : (2 : ℝ) * (cellSupDist (enclosingCell x.1.1.1) Z : ℝ) ≤ q := by linarith
      exact_mod_cast this
    have h2 : x.1 ∈ bondsNearCell Z q := by
      simp only [bondsNearCell, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h1
    obtain ⟨i, hi⟩ := (hr _).1 h2
    exact ⟨(i, x.2), by simp [pairedIndex, hi]⟩
  refine ⟨fun a b e => ?_, fun a b e => ?_, fun k => ?_, cov Y j hN.isBoxPairing.mem_left_iff,
    cov Y' j' hN.isBoxPairing.mem_right_iff⟩
  · have e1 : (pairedIndex j a).1 = (pairedIndex j b).1 := congrArg Prod.fst e
    have e2 : (pairedIndex j a).2 = (pairedIndex j b).2 := congrArg Prod.snd e
    exact Prod.ext (hN.isBoxPairing.injective_left e1) e2
  · have e1 : (pairedIndex j' a).1 = (pairedIndex j' b).1 := congrArg Prod.fst e
    have e2 : (pairedIndex j' a).2 = (pairedIndex j' b).2 := congrArg Prod.snd e
    exact Prod.ext (hN.isBoxPairing.injective_right e1) e2
  · obtain ⟨h, o, i, hh, ho, e₁, e₂⟩ := hN.short_offsets k.1
    have ho' : o ∈ centredCube F'.blockSide := hL ▸ ho
    have c1 : enclosingCell (j k.1).1.1 = Y + siteOfCoords F.top h := by
      rw [e₁]
      exact (hD F hG hs2).1 Y h o i ho
    have c2 : enclosingCell (j' k.1).1.1 = Y' + siteOfCoords F'.top h := by
      rw [e₂]
      exact (hD F' hG' hs2').1 Y' h o i ho'
    unfold distFromCell pairedIndex
    simp only
    rw [c1, c2, cellSupDist_offset hD hG hs Y hh, cellSupDist_offset hD hG' hs' Y' hh]
end Offsets
section Glue
variable {F F' : BlockFrame} {T : ParameterAssignment} {c : ColdChainParameters}
private structure Inputs : Prop where
  cover : BlocksCoverLowerLevel
  unique : MinimizingChartUnique
  imaginary : ImaginaryCoordinatesIsometric
  lipschitz : ChartedFieldLipschitz
  offsets : cellOffsetStatement
  sites : SiteDecomposition
  glue : TwoChartsGlue
  pairs : bondsNearCellsPairStatement
  contour : ChartedFieldContourBound
private structure AgreeingTops (T : ParameterAssignment) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell)
    (Y' : F'.Cell) (r : ℕ) : Prop where
  torus : IsBlockTorus T.side F
  torus' : IsBlockTorus T.side F'
  level : F'.depth = F.depth
  cold : IsSmallCurvature (9 / 8 * T.threshold) V
  cold' : IsSmallCurvature (9 / 8 * T.threshold) V'
  agree : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r
variable {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
private theorem AgreeingTops.extent_gt (P : AgreeingTops T V V' Y Y' r) (hD : T.Admissible) :
    (∀ i, 2 * r + 2 < F.extent i) ∧ ∀ i, 2 * r + 2 < F'.extent i := by
  obtain ⟨a1, a2, -, -⟩ := P.agree
  obtain ⟨-, -, s1⟩ := blockTorus_facts P.torus hD.L_odd
  obtain ⟨-, -, s2⟩ := blockTorus_facts P.torus' hD.L_odd
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rcases a1 i with h | h
    · have := s1 i
      omega
    · exact h
  · rcases a2 i with h | h
    · have := s2 i
      omega
    · exact h
private def closeness (T : ParameterAssignment) (r : ℕ) : ℝ :=
  T.N 0 * (9 / 8 * T.threshold) * Real.exp (-(T.δ₁ * ((r : ℝ) / 2)))
private theorem coordinatesCloseOnBall (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c)
    (P : AgreeingTops T V V' Y Y' r) (hr : 2 ≤ r) :
    CoordinatesCloseOnBall T.side Y Y' (r / 2) (closeness T r) (minimizer T.coupling T.ρA V)
      (minimizer T.coupling T.ρA V') := by
  obtain ⟨hσ, hσA⟩ := threshold_facts hD
  obtain ⟨hδ, -, -, -, -, -, -, hNpos, -⟩ := hD.chain
  obtain ⟨hodd, hs2, hs1⟩ := blockTorus_facts P.torus hD.L_odd
  obtain ⟨hs, hs'⟩ := P.extent_gt hD
  have hL3 : 3 ≤ F.blockSide := by
    have := hD.L_ge
    rw [P.torus.1]
    have h40 : 3 ≤ 2 ^ 40 := by norm_num
    omega
  have hcl := hT.admissible.estimates F (9 / 8 * T.threshold) V P.torus (by positivity)
    (by rw [hT.σA_eq]; exact hσA) P.cold
  have hloc := (hcl.locality F' V' Y Y' r (by rw [P.torus'.1, P.torus.1]) P.level P.torus'.2 P.cold' P.agree).2.1
  intro h o i hh ho hb
  have hFL : F.blockSide = T.side := P.torus.1
  have ho' : o ∈ centredCube F.blockSide := by rw [hFL]; exact ho
  have hq : ∀ l, 2 * |h l| ≤ (r : ℤ) := fun l => by
    have := hh l
    push_cast at this
    omega
  have hs0 : ∀ i, 2 * r + 2 < F.extent i := hs
  have hcell : enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h := (tl.offsets F hodd hs2).1 Y h o i ho'
  have hd : cellSupDist (Y + siteOfCoords F.top h) Y ≤ r / 2 := cellSupDist_offset_le tl.offsets hodd hs0 Y hq hh
  have hY : cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) ≤ r / 2 := by
    rw [hcell, CellSums.cellSupDist_comm]
    exact hd
  have hnext : cellSupDist Y (enclosingCell ((fineBondAt Y h o i).1 + unitStep F.depth i)) ≤ r := by
    have t := CellSums.cellSupDist_triangle hs1 Y (enclosingCell (fineBondAt Y h o i).1)
      (enclosingCell ((fineBondAt Y h o i).1 + unitStep F.depth i))
    have n1 := CellSums.cellSupDist_add_unitStep_le tl.cover hodd hL3 hs2 (fineBondAt Y h o i).1 i
    omega
  have hbox : WithinRadius r h := fun l => by
    have := hh l
    push_cast at this
    have h2 : ((r / 2 : ℕ) : ℤ) ≤ r := by exact_mod_cast Nat.div_le_self _ _
    omega
  have h1 := (hloc h o i ho' hb hbox hnext).1
  rw [hT.delta_eq, hT.N_eq, hT.ρA_eq] at h1
  refine h1.trans ?_
  unfold closeness
  have hN := hNpos 0
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have h3 : (cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) : ℝ) ≤ (r : ℝ) / 2 := by
    have : ((cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) : ℕ) : ℝ) ≤ ((r / 2 : ℕ) : ℝ) := by
      exact_mod_cast hY
    exact this.trans Nat.cast_div_le
  nlinarith
private structure IsGluingMove (T : ParameterAssignment) (r : ℕ) (Y : F.Cell) (Y' : F'.Cell)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions)
    (Δ : StepVariable (finiteCells F)) : Prop where
  norm_le : ∀ b, ‖Δ b‖ ≤ closeness T r
  vanish_off : ∀ b, b ∉ ballChordBonds F Y (r / 2) → Δ b = 0
  shift_eq : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius (r / 2) h → o ∈ centredCube T.side →
    fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
    ColdStepAtMirrorFrames.shiftCoordinates w Δ (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i
private theorem closeness_nonneg (hD : T.Admissible) : 0 ≤ closeness T r := by
  obtain ⟨hσ, -⟩ := threshold_facts hD
  obtain ⟨-, -, -, -, -, -, -, hNpos, -⟩ := hD.chain
  have := hNpos 0
  unfold closeness
  positivity
private theorem exists_gluingMove (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c)
    (P : AgreeingTops T V V' Y Y' r) (hr : 2 ≤ r) :
    ∃ Δ, IsGluingMove T r Y Y' (minimizer T.coupling T.ρA V) (minimizer T.coupling T.ρA V') Δ := by
  obtain ⟨hodd, -, -⟩ := blockTorus_facts P.torus hD.L_odd
  obtain ⟨hs, -⟩ := P.extent_gt hD
  have hN := coordinatesCloseOnBall tl hD hT P hr
  have hFL : F.blockSide = T.side := P.torus.1
  have hLL : F.blockSide = F'.blockSide := by rw [P.torus.1, P.torus'.1]
  rw [← hFL] at hN
  obtain ⟨Δ, wx, h1, h2, h3, h4⟩ := tl.glue F F' Y Y' (r / 2) (closeness T r) _ _ hLL hodd (fun i => by
    have := hs i
    omega) (closeness_nonneg hD) hN
  refine ⟨Δ, h1, h2, fun h o i hh ho hb => ?_⟩
  exact (h3 _ hb).symm.trans (h4 h o i hh (by rw [hFL]; exact ho))
private theorem norm_stepCoordinates_glue_le {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions} {Δ : StepVariable (finiteCells F)} (hD : T.Admissible)
    (hG : IsGluingMove T r Y Y' w w' Δ) (z : F.Site F.depth) (i : Fin 4) :
    ‖stepCoordinates Δ z i‖ ≤ closeness T r :=
  norm_stepCoordinates_le Δ (closeness_nonneg hD) hG.norm_le z i
end Glue
end StepDensityLocality
end YangMills.Construction.RunningCouplingSlope
end
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open scoped Quaternion
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters TorusComparison Estimates ChartResponse
  SecondOrderMoves ChartLipschitz
namespace StepDensityLocality
section Entries
variable {F F' : BlockFrame} {T : ParameterAssignment} {c : ColdChainParameters}
private def EntryComparisonAt (a : ℝ) (L : ℕ) (c : ColdChainParameters) (ϱ C : ℝ) : Prop :=
  ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions)
    (p' q' : F'.Site F'.depth × Fin 4 × imaginaryQuaternions), 1 ≤ r → IsBlockTorus L F → IsBlockTorus L F' →
    F'.depth = F.depth →
    ‖p.2.2‖ = 1 → ‖q.2.2‖ = 1 → ‖p'.2.2‖ = 1 → ‖q'.2.2‖ = 1 →
    (∀ s u, 0 ≤ s → s ≤ ϱ → 0 ≤ u → u ≤ ϱ →
      IsAdmissibleChartPoint L c.σA (shiftTwice p q s u w) V ∧
        IsAdmissibleChartPoint L c.σA (shiftTwice p' q' s u w') V') →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
    (∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube L →
      fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
      w (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i ∧
      directionCoordinate (Sum.inl p) (fineBondAt Y h o i).1 i =
        directionCoordinate (Sum.inl p') (fineBondAt Y' h o i).1 i ∧
      directionCoordinate (Sum.inl q) (fineBondAt Y h o i).1 i =
        directionCoordinate (Sum.inl q') (fineBondAt Y' h o i).1 i) →
    8 * cellSupDist (enclosingCell p.1) Y ≤ r → 8 * cellSupDist (enclosingCell p'.1) Y' ≤ r →
    |chartMixedDeriv a w V ![Sum.inl p, Sum.inl q] - chartMixedDeriv a w' V' ![Sum.inl p', Sum.inl q']| ≤
      C * Real.exp (-(c.δ₁ / 16 * r))
private def EntryLipschitzAt (a : ℝ) (L : ℕ) (c : ColdChainParameters) (C : ℝ) : Prop :=
  ∀ (F : BlockFrame) (w u : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (Bt : Finset (F.Site F.depth × Fin 4)) (Bn : Finset (F.Site F.top × Fin 4))
    (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions),
    IsBlockTorus L F → ‖p.2.2‖ = 1 → ‖q.2.2‖ = 1 →
    (∀ b, b ∉ Bt → u b.1 b.2 = 0) → (∀ b, b ∉ Bn → v b.1 b.2 = 0) →
    (∀ (θ : F.Site F.depth → Fin 4 → ℝ) (ϑ : F.Site F.top → Fin 4 → ℝ), (∀ z i, 0 ≤ θ z i ∧ θ z i ≤ 1) →
      (∀ y i, 0 ≤ ϑ y i ∧ ϑ y i ≤ 1) →
      IsAdmissibleChartPoint L c.σA (fun z i => w z i + θ z i • u z i) (leftTranslate (fun y i => ϑ y i • v y i) V)) →
    |chartMixedDeriv a (fun z i => w z i + u z i) (leftTranslate v V) ![Sum.inl p, Sum.inl q] -
        chartMixedDeriv a w V ![Sum.inl p, Sum.inl q]| ≤
      ∑ b ∈ Bt, C * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell p.1) (enclosingCell q.1))
          (cellSupDist (enclosingCell p.1) (enclosingCell b.1)) : ℕ))) * ‖u b.1 b.2‖ +
        ∑ b ∈ Bn, C * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell p.1) (enclosingCell q.1))
          (cellSupDist (enclosingCell p.1) b.1) : ℕ))) * ‖v b.1 b.2‖
private def EnergySmoothAt (a : ℝ) (L : ℕ) (c : ColdChainParameters) : Prop :=
  ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions), ∀ V : F.GaugeField F.top,
    IsBlockTorus L F → IsAdmissibleChartPoint L c.σA w V → ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0
private theorem norm_directionCoordinate_le (z : F.Site F.depth × Fin 4 × imaginaryQuaternions) (x : F.Site F.depth)
    (i : Fin 4) (hz : ‖z.2.2‖ = 1) :
    ‖directionCoordinate (Sum.inl z : ChartDirection F) x i‖ ≤ 1 := by
  simp only [directionCoordinate]
  split_ifs
  · exact hz.le
  · simp
private theorem norm_shiftTwice_sub_le (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions) (hp : ‖p.2.2‖ = 1)
    (hq : ‖q.2.2‖ = 1) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (z : F.Site F.depth) (i : Fin 4) :
    ‖shiftTwice p q s u w z i - w z i‖ ≤ s + u := by
  have e : shiftTwice p q s u w z i - w z i =
      s • directionCoordinate (Sum.inl p : ChartDirection F) z i +
        u • directionCoordinate (Sum.inl q : ChartDirection F) z i := by
    simp only [shiftTwice, DirectionalDerivatives.shiftCoordinates]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg hu]
  have h1 := norm_directionCoordinate_le p z i hp
  have h2 := norm_directionCoordinate_le q z i hq
  nlinarith [norm_nonneg (directionCoordinate (Sum.inl p : ChartDirection F) z i),
    norm_nonneg (directionCoordinate (Sum.inl q : ChartDirection F) z i)]
private theorem norm_indexDirection (tl : Inputs) (i : CoordIndex F) : ‖(indexDirection i).2.2‖ = 1 := by
  obtain ⟨_, _, hn, _⟩ := tl.imaginary
  show ‖toImaginary (EuclideanSpace.single i.2 (1 : ℝ))‖ = 1
  rw [hn]
  simp
variable {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
private theorem agreeOnBall_half (P : AgreeingTops T V V' Y Y' r) (hD : T.Admissible) :
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' (r / 2) := by
  obtain ⟨hs, hs'⟩ := P.extent_gt hD
  obtain ⟨-, -, a3, a4⟩ := P.agree
  have hin : ∀ {h : Fin 4 → ℤ}, WithinRadius (r / 2) h → WithinRadius r h := fun {h} hh i => by
    have := hh i
    push_cast at this
    omega
  refine ⟨fun i => Or.inr ?_, fun i => Or.inr ?_, fun h hh => a3 h (hin hh), fun b hb => a4 b ⟨hin hb.1, hin hb.2⟩⟩
  · have := hs i
    omega
  · have := hs' i
    omega
private theorem card_ballChordBonds_le (tl : Inputs) (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {κ M : ℝ}
    (hκ : 0 ≤ κ)
    (hM : ∀ (F : BlockFrame) (c : F.Cell), (∀ i, 2 ≤ F.extent i) →
      ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ M)
    (Y : F.Cell) (q : ℕ) :
    (((ballChordBonds F Y q).image Subtype.val).card : ℝ) ≤
      Real.exp (κ * q) * (4 * ((centredCube F.blockSide).card : ℝ) * M) := by
  set B := (ballChordBonds F Y q).image Subtype.val with hB
  set g : F.Cell → ℝ := fun z => Real.exp (-(κ * cellSupDist z Y)) with hg
  have h1 : ∀ b ∈ B, (1 : ℝ) ≤ Real.exp (κ * q) * g (enclosingCell b.1) := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
    simp only [ballChordBonds, Finset.mem_filter, Finset.mem_univ, true_and] at hb'
    rw [hg]
    simp only
    rw [← Real.exp_add]
    apply Real.one_le_exp
    have : ((cellSupDist (enclosingCell b'.1.1) Y : ℕ) : ℝ) ≤ q := by exact_mod_cast hb'
    nlinarith
  have h2 : (B.card : ℝ) ≤ ∑ b ∈ B, Real.exp (κ * q) * g (enclosingCell b.1) := by
    have := Finset.sum_le_sum h1
    simpa using this
  refine h2.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h3 := CellSums.sum_bonds_le_sum_cells tl.cover hodd hs g (fun _ => (Real.exp_pos _).le) B
  refine h3.trans (mul_le_mul_of_nonneg_left (hM F Y hs) (by positivity))
private theorem abs_chartedHessian_sub_le (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c) {C₁ C₂ κ M : ℝ}
    (hC₂ : 0 ≤ C₂) (hκ : 0 ≤ κ) (hE : EntryComparisonAt T.coupling T.side c (T.threshold / 64) C₁)
    (hMv : EntryLipschitzAt T.coupling T.side c C₂) (hSm : EnergySmoothAt T.coupling T.side c)
    (hMs : ∀ (F : BlockFrame) (c : F.Cell), (∀ i, 2 ≤ F.extent i) →
      ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ M)
    (P : AgreeingTops T V V' Y Y' r) (hr : 2 ≤ r) (hgap : closeness T r ≤ T.threshold / 32)
    {Δ : StepVariable (finiteCells F)}
    (hG : IsGluingMove T r Y Y' (minimizer T.coupling T.ρA V) (minimizer T.coupling T.ρA V') Δ)
    {i j : CoordIndex F} {i' j' : CoordIndex F'} (hi : SameOffsets Y Y' (2 * (r / 2)) i i')
    (hj : SameOffsets Y Y' (2 * (r / 2)) j j')
    (hn : 8 * cellSupDist (enclosingCell i.1.1.1) Y ≤ r / 2) (hn' : 8 * cellSupDist (enclosingCell i'.1.1.1) Y' ≤ r / 2) :
    |chartedHessian T.coupling T.ρA V 0 i j - chartedHessian T.coupling T.ρA V' 0 i' j'| ≤
      C₁ * Real.exp (-(T.δ₁ / 16 * ((r / 2 : ℕ) : ℝ))) +
        C₂ * closeness T r * (Real.exp (κ * ((r / 2 : ℕ) : ℝ)) * (4 * ((centredCube T.side).card : ℝ) * M)) := by
  obtain ⟨hσ, hσA⟩ := threshold_facts hD
  obtain ⟨hodd, hs2, hs1⟩ := blockTorus_facts P.torus hD.L_odd
  obtain ⟨hodd', hs2', hs1'⟩ := blockTorus_facts P.torus' hD.L_odd
  obtain ⟨hs, hs'⟩ := P.extent_gt hD
  have hFL : F.blockSide = T.side := P.torus.1
  have hLL : F'.blockSide = F.blockSide := by rw [P.torus.1, P.torus'.1]
  have hw := minimizerFacts tl.unique hD hT P.torus P.cold
  have hw' := minimizerFacts tl.unique hD hT P.torus' P.cold'
  set w := minimizer T.coupling T.ρA V with hwdef
  set w' := minimizer T.coupling T.ρA V' with hw'def
  have hg0 := closeness_nonneg (r := r) hD
  have hΔ := norm_stepCoordinates_glue_le hD hG
  have hsmall0 : IsAdmissibleChartPoint T.side T.σA w V :=
    admissible_of_near tl.lipschitz hD P.torus hw le_rfl (by positivity) fun z i => by simp
  have hsmall0' : IsAdmissibleChartPoint T.side T.σA w' V' :=
    admissible_of_near tl.lipschitz hD P.torus' hw' le_rfl (by positivity) fun z i => by simp
  have hσc : c.σA = T.σA := hT.σA_eq
  have hf : ContDiffAt ℝ 3 (chartedEnergyAt T.coupling w V) 0 := hSm F w V P.torus (by rw [hσc]; exact hsmall0)
  have hf' : ContDiffAt ℝ 3 (chartedEnergyAt T.coupling w' V') 0 :=
    hSm F' w' V' P.torus' (by rw [hσc]; exact hsmall0')
  have eH : chartedHessian T.coupling T.ρA V 0 i j =
      chartMixedDeriv T.coupling w V ![Sum.inl (indexDirection i), Sum.inl (indexDirection j)] := by
    rw [chartedHessian_eq]
    exact chartHessian_eq_chartMixedDeriv tl.imaginary _ _ _ hf i j
  have eH' : chartedHessian T.coupling T.ρA V' 0 i' j' =
      chartMixedDeriv T.coupling w' V' ![Sum.inl (indexDirection i'), Sum.inl (indexDirection j')] := by
    rw [chartedHessian_eq]
    exact chartHessian_eq_chartMixedDeriv tl.imaginary _ _ _ hf' i' j'
  have hui := norm_indexDirection tl i
  have huj := norm_indexDirection tl j
  have hui' := norm_indexDirection tl i'
  have huj' := norm_indexDirection tl j'
  have hQ : ∀ i, 2 * (2 * (r / 2)) + 2 < F.extent i := fun i => by
    have := hs i
    omega
  have hQ' : ∀ i, 2 * (2 * (r / 2)) + 2 < F'.extent i := fun i => by
    have := hs' i
    omega
  have k1 := hE F F' (ColdStepAtMirrorFrames.shiftCoordinates w Δ) w' V V' Y Y' (r / 2) (indexDirection i)
    (indexDirection j) (indexDirection i') (indexDirection j')
    (by omega) P.torus P.torus' P.level hui huj hui' huj' (fun s u s0 s1 u0 u1 => ⟨?_, ?_⟩) (agreeOnBall_half P hD)
    (fun h o k hh ho hb => ?_) hn hn'
  · have k2 := hMv F w (stepCoordinates Δ) V (fun _ _ => 0) ((ballChordBonds F Y (r / 2)).image Subtype.val) ∅
      (indexDirection i) (indexDirection j) P.torus hui huj ?_ (fun _ _ => rfl) ?_
    · have e3 : leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := leftTranslate_zero V
      rw [e3, Finset.sum_empty, add_zero] at k2
      have e4 : (fun z k => w z k + stepCoordinates Δ z k) = ColdStepAtMirrorFrames.shiftCoordinates w Δ := rfl
      rw [e4] at k2
      have b1 : ∑ b ∈ (ballChordBonds F Y (r / 2)).image Subtype.val,
          C₂ * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell (indexDirection i).1)
            (enclosingCell (indexDirection j).1))
            (cellSupDist (enclosingCell (indexDirection i).1) (enclosingCell b.1)) : ℕ))) *
              ‖stepCoordinates Δ b.1 b.2‖ ≤
          C₂ * closeness T r * (Real.exp (κ * ((r / 2 : ℕ) : ℝ)) * (4 * ((centredCube T.side).card : ℝ) * M)) := by
        have hδ : 0 ≤ c.δ₁ := hT.admissible.positivity.1.le
        have t : ∀ b ∈ (ballChordBonds F Y (r / 2)).image Subtype.val,
            C₂ * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell (indexDirection i).1)
              (enclosingCell (indexDirection j).1))
              (cellSupDist (enclosingCell (indexDirection i).1) (enclosingCell b.1)) : ℕ))) *
                ‖stepCoordinates Δ b.1 b.2‖ ≤ C₂ * closeness T r := by
          intro b _
          have x1 : Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell (indexDirection i).1)
              (enclosingCell (indexDirection j).1))
              (cellSupDist (enclosingCell (indexDirection i).1) (enclosingCell b.1)) : ℕ))) ≤ 1 := by
            apply Real.exp_le_one_iff.2
            have := mul_nonneg hδ (Nat.cast_nonneg (max (cellSupDist (enclosingCell (indexDirection i).1)
              (enclosingCell (indexDirection j).1))
              (cellSupDist (enclosingCell (indexDirection i).1) (enclosingCell b.1))))
            linarith
          have x2 := hΔ b.1 b.2
          calc _ ≤ C₂ * 1 * closeness T r := by gcongr
            _ = _ := by ring
        refine (Finset.sum_le_sum t).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        have hc := card_ballChordBonds_le tl hodd hs2 hκ hMs Y (r / 2)
        rw [hFL] at hc
        exact mul_le_mul_of_nonneg_left hc (by positivity)
      rw [eH, eH']
      have hδc : c.δ₁ = T.δ₁ := hT.delta_eq
      rw [hδc] at k1
      have t1 := abs_sub_le (chartMixedDeriv T.coupling w V ![Sum.inl (indexDirection i), Sum.inl (indexDirection j)])
        (chartMixedDeriv T.coupling (ColdStepAtMirrorFrames.shiftCoordinates w Δ) V
          ![Sum.inl (indexDirection i), Sum.inl (indexDirection j)])
        (chartMixedDeriv T.coupling w' V' ![Sum.inl (indexDirection i'), Sum.inl (indexDirection j')])
      have k3 := k2.trans b1
      rw [abs_sub_comm] at k3
      linarith
    · intro b hb
      by_cases hc : b ∈ chordBonds (finiteCells F)
      · have hoff : (⟨b, hc⟩ : ↥(chordBonds (finiteCells F))) ∉ ballChordBonds F Y (r / 2) := fun h => hb
          (Finset.mem_image.2 ⟨_, h, rfl⟩)
        have h0 := hG.vanish_off _ hoff
        have e5 : stepCoordinates Δ b.1 b.2 = toImaginary (Δ ⟨b, hc⟩) := dif_pos hc
        rw [e5, h0]
        obtain ⟨_, hsm, _⟩ := tl.imaginary
        have := hsm 0 (0 : BondVector)
        simpa using this
      · exact dif_neg hc
    · intro θ ϑ hθ _
      have e6 : leftTranslate (fun y i => ϑ y i • (0 : imaginaryQuaternions)) V = V := by
        simp only [smul_zero]
        exact leftTranslate_zero V
      rw [e6]
      rw [hσc]
      refine admissible_of_near tl.lipschitz hD P.torus hw hg0 (by linarith) fun z k => ?_
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hθ z k).1]
      have := hΔ z k
      have := norm_nonneg (stepCoordinates Δ z k)
      have := hθ z k
      nlinarith
  · rw [hσc]
    refine admissible_of_near tl.lipschitz hD P.torus hw (g := s + u + closeness T r) (by linarith) (by linarith)
      fun z k => ?_
    have a1 := norm_shiftTwice_sub_le (indexDirection i) (indexDirection j) hui huj s0 u0
      (ColdStepAtMirrorFrames.shiftCoordinates w Δ) z k
    have a2 := hΔ z k
    have e7 : shiftTwice (indexDirection i) (indexDirection j) s u (ColdStepAtMirrorFrames.shiftCoordinates w Δ) z k -
        w z k =
        (shiftTwice (indexDirection i) (indexDirection j) s u (ColdStepAtMirrorFrames.shiftCoordinates w Δ) z k -
          ColdStepAtMirrorFrames.shiftCoordinates w Δ z k) + stepCoordinates Δ z k := by
      simp only [ColdStepAtMirrorFrames.shiftCoordinates]
      abel
    rw [e7]
    exact (norm_add_le _ _).trans (add_le_add a1 a2)
  · rw [hσc]
    exact admissible_of_near tl.lipschitz hD P.torus' hw' (g := s + u) (by linarith) (by linarith) fun z k =>
      norm_shiftTwice_sub_le (indexDirection i') (indexDirection j') hui' huj' s0 u0 w' z k
  · have hh' : ∀ l, 2 * |h l| ≤ ((2 * (r / 2) : ℕ) : ℤ) := fun l => by
      have := hh l
      push_cast at this ⊢
      omega
    have ho' : o ∈ centredCube F.blockSide := by rw [hFL]; exact ho
    exact ⟨hG.shift_eq h o k hh ho hb, directionCoordinate_match tl.offsets tl.sites hodd hodd' hLL hQ hQ' hi k hh' ho',
      directionCoordinate_match tl.offsets tl.sites hodd hodd' hLL hQ hQ' hj k hh' ho'⟩
end Entries
end StepDensityLocality
end YangMills.Construction.RunningCouplingSlope
end
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open scoped Quaternion
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters TorusComparison Estimates ChartResponse
  SecondOrderMoves ChartLipschitz
namespace StepDensityLocality
section Shares
variable {F F' : BlockFrame} {T : ParameterAssignment} {c : ColdChainParameters}
private structure ParameterConstants (T : ParameterAssignment) (c : ColdChainParameters) (CS κ M C₁ C₂ : ℝ) : Prop where
  CS_nonneg : 0 ≤ CS
  κ_pos : 0 < κ
  κ_le : κ ≤ T.δ₁ / 8
  inverse : InverseDecayAt T CS κ
  sums : ∀ (F : BlockFrame) (c : F.Cell), (∀ i, 2 ≤ F.extent i) →
    ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ M
  M_nonneg : 0 ≤ M
  C₁_nonneg : 0 ≤ C₁
  C₂_nonneg : 0 ≤ C₂
  entries : EntryComparisonAt T.coupling T.side c (T.threshold / 64) C₁
  moves : EntryLipschitzAt T.coupling T.side c C₂
  smooth : EnergySmoothAt T.coupling T.side c
private def inverseConst (T : ParameterAssignment) : ℝ := 2 / T.lam
private def opConst (T : ParameterAssignment) (CS : ℝ) : ℝ := CS + T.lam
private def sumConst (T : ParameterAssignment) (M : ℝ) : ℝ := 3 * (4 * ((centredCube T.side).card : ℝ) * M)
private def densityError (T : ParameterAssignment) (κ M C₁ C₂ : ℝ) (r : ℕ) : ℝ :=
  C₁ * Real.exp (-(T.δ₁ / 16 * ((r / 2 : ℕ) : ℝ))) +
    C₂ * closeness T r * (Real.exp (κ * ((r / 2 : ℕ) : ℝ)) * (4 * ((centredCube T.side).card : ℝ) * M))
private theorem abs_interpolatedOp_sub_le {ι : Type} {H : Matrix (CoordIndex F) (CoordIndex F) ℝ}
    {H' : Matrix (CoordIndex F') (CoordIndex F') ℝ} {e : ι → CoordIndex F} {e' : ι → CoordIndex F'}
    (he : Function.Injective e) (he' : Function.Injective e') {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (lam : ℝ) (k l : ι) :
    |interpolatedOp H lam u (e k) (e l) - interpolatedOp H' lam u (e' k) (e' l)| ≤ |H (e k) (e l) - H' (e' k) (e' l)| := by
  classical
  have h1 : (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ) (e k) (e l) =
      (1 : Matrix (CoordIndex F') (CoordIndex F') ℝ) (e' k) (e' l) := by
    simp [Matrix.one_apply, he.eq_iff, he'.eq_iff]
  have e1 : interpolatedOp H lam u (e k) (e l) - interpolatedOp H' lam u (e' k) (e' l) =
      u * (H (e k) (e l) - H' (e' k) (e' l)) := by
    simp only [interpolatedOp, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h1]
    ring
  rw [e1, abs_mul, abs_of_nonneg hu0]
  nlinarith [abs_nonneg (H (e k) (e l) - H' (e' k) (e' l))]
private theorem sub_smul_one_sub_eq {ι : Type} {H : Matrix (CoordIndex F) (CoordIndex F) ℝ}
    {H' : Matrix (CoordIndex F') (CoordIndex F') ℝ} {e : ι → CoordIndex F} {e' : ι → CoordIndex F'}
    (he : Function.Injective e) (he' : Function.Injective e') (lam : ℝ) (k l : ι) :
    (H - lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) (e k) (e l) -
      (H' - lam • (1 : Matrix (CoordIndex F') (CoordIndex F') ℝ)) (e' k) (e' l) =
      H (e k) (e l) - H' (e' k) (e' l) := by
  classical
  have h1 : (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ) (e k) (e l) =
      (1 : Matrix (CoordIndex F') (CoordIndex F') ℝ) (e' k) (e' l) := by
    simp [Matrix.one_apply, he.eq_iff, he'.eq_iff]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, h1]
  ring
private theorem sum_exp_distFromCell_le (hcov : BlocksCoverLowerLevel) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) {κ M : ℝ} (hM : ∀ (F : BlockFrame) (c : F.Cell), (∀ i, 2 ≤ F.extent i) →
      ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ M) (Y : F.Cell) :
    ∑ j : CoordIndex F, Real.exp (-(κ * distFromCell Y j)) ≤ 3 * (4 * ((centredCube F.blockSide).card : ℝ) * M) := by
  set g : F.Cell → ℝ := fun z => Real.exp (-(κ * cellSupDist z Y)) with hg
  have e1 : ∑ j : CoordIndex F, Real.exp (-(κ * distFromCell Y j)) =
      3 * ∑ b ∈ chordBonds (finiteCells F), g (enclosingCell b.1) := by
    rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort (chordBonds (finiteCells F)) fun b => g (enclosingCell b.1),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb : ∀ α : Fin 3, Real.exp (-(κ * distFromCell Y (b, α))) = g (enclosingCell b.1.1) := fun α => rfl
    simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [e1]
  have h2 := CellSums.sum_bonds_le_sum_cells hcov hodd hs g (fun _ => (Real.exp_pos _).le)
    (chordBonds (finiteCells F))
  have h3 := hM F Y hs
  have h4 : (0 : ℝ) ≤ 4 * ((centredCube F.blockSide).card : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left h3 h4
  linarith
private theorem eq_iff_cellSupDist_eq_zero (hD : cellOffsetStatement) {G : BlockFrame} (hG : Odd G.blockSide)
    (hs : ∀ i, 2 ≤ G.extent i) (z Y : G.Cell) : z = Y ↔ cellSupDist z Y = 0 := by
  constructor
  · rintro rfl
    unfold cellSupDist
    simp
  · intro h
    obtain ⟨-, a2, a3, -⟩ := hD G hG hs
    have h0 : cellOffset Y z = 0 := by
      funext i
      have := a3 Y z i
      rw [h] at this
      simpa using this
    have := a2 Y z
    rw [h0, add_siteOfCoords_zero] at this
    exact this.symm
private theorem decayingInverse_at (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c) {CS κ M C₁ C₂ : ℝ}
    (hN : ParameterConstants T c CS κ M C₁ C₂) (hF : IsBlockTorus T.side F) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature (9 / 8 * T.threshold) V) (Y : F.Cell) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    DecayingInverse κ (inverseConst T) (opConst T CS) (sumConst T M)
      (fun i j : CoordIndex F => (coordDist i j : ℝ)) (distFromCell Y)
      (interpolatedOp (chartedHessian T.coupling T.ρA V 0) T.lam u)
      (interpolatedOp (chartedHessian T.coupling T.ρA V 0) T.lam u)⁻¹
      (chartedHessian T.coupling T.ρA V 0 - T.lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) :=
  decayingInverse_of_top tl.cover tl.unique hD hT hN.CS_nonneg hN.κ_pos hN.κ_le hN.inverse hN.sums hN.M_nonneg hF hV Y
    hu0 hu1
private theorem abs_hessianCellShare_le (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c) {CS κ M C₁ C₂ : ℝ}
    (hN : ParameterConstants T c CS κ M C₁ C₂) (hF : IsBlockTorus T.side F) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature (9 / 8 * T.threshold) V) (Y : F.Cell) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |hessianCellShare T.coupling T.ρA T.lam Y V u| ≤
      sumConst T M * (inverseConst T * opConst T CS * sumConst T M) := by
  classical
  obtain ⟨hodd, hs2, -⟩ := blockTorus_facts hF hD.L_odd
  have hS := decayingInverse_at tl hD hT hN hF hV Y hu0 hu1
  have hγ := hS.rate_pos
  have hA := hS.A_nonneg
  have hB := hS.B_nonneg
  have hK := hS.K_nonneg
  have hFL : F.blockSide = T.side := hF.1
  have hterm : ∀ i : CoordIndex F,
      |((chartedHessian T.coupling T.ρA V 0 - T.lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) *
        (interpolatedOp (chartedHessian T.coupling T.ρA V 0) T.lam u)⁻¹) i i| ≤
      inverseConst T * opConst T CS * sumConst T M := by
    intro i
    rw [Matrix.mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ x : CoordIndex F,
        |(chartedHessian T.coupling T.ρA V 0 - T.lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) i x *
          (interpolatedOp (chartedHessian T.coupling T.ρA V 0) T.lam u)⁻¹ x i| ≤
        inverseConst T * opConst T CS * Real.exp (-(κ * (coordDist i x : ℝ))) := by
      intro x
      rw [abs_mul]
      have h1 := (hS.abs_aux_le i x).trans
        (mul_le_mul_of_nonneg_left (exp_neg_two_mul_le hγ.le (hS.dist_nonneg _ _)) hB)
      calc _ ≤ (opConst T CS * Real.exp (-(κ * (coordDist i x : ℝ)))) * inverseConst T :=
            mul_le_mul h1 (hS.abs_inv_le_const _ _) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum fun x _ => this x).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hS.sum_exp_le i) (by positivity)
  have e0 : hessianCellShare T.coupling T.ρA T.lam Y V u = ∑ i : CoordIndex F, if enclosingCell i.1.1.1 = Y then
      ((chartedHessian T.coupling T.ρA V 0 - T.lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) *
        (interpolatedOp (chartedHessian T.coupling T.ρA V 0) T.lam u)⁻¹) i i else 0 := rfl
  rw [e0]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hs : ∀ i : CoordIndex F, |(if enclosingCell i.1.1.1 = Y then
      ((chartedHessian T.coupling T.ρA V 0 - T.lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) *
        (interpolatedOp (chartedHessian T.coupling T.ρA V 0) T.lam u)⁻¹) i i else 0)| ≤
      (inverseConst T * opConst T CS * sumConst T M) * Real.exp (-(κ * distFromCell Y i)) := by
    intro i
    split_ifs with hc
    · have : distFromCell Y i = 0 := by
        unfold distFromCell
        rw [hc]
        have := (eq_iff_cellSupDist_eq_zero tl.offsets hodd hs2 Y Y).1 rfl
        simp [this]
      rw [this]
      simpa using hterm i
    · simp only [abs_zero]
      positivity
  refine (Finset.sum_le_sum fun i _ => hs i).trans ?_
  rw [← Finset.mul_sum]
  have h2 := sum_exp_distFromCell_le tl.cover hodd hs2 hN.sums Y
  rw [hFL] at h2
  calc _ ≤ (inverseConst T * opConst T CS * sumConst T M) * sumConst T M :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring
variable {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
private theorem abs_hessianCellShare_sub_le (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c)
    {CS κ M C₁ C₂ : ℝ} (hNum : ParameterConstants T c CS κ M C₁ C₂)
    (P : AgreeingTops T V V' Y Y' r) (hr : 2 ≤ r) (hgap : closeness T r ≤ T.threshold / 32)
    {Δ : StepVariable (finiteCells F)}
    (hG : IsGluingMove T r Y Y' (minimizer T.coupling T.ρA V) (minimizer T.coupling T.ρA V') Δ)
    {ι : Type} [Fintype ι] [DecidableEq ι] {j : ι → ↥(chordBonds (finiteCells F))}
    {j' : ι → ↥(chordBonds (finiteCells F'))}
    (hN : IsShortPairing Y Y' (r / 2 / 2) j j') {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |hessianCellShare T.coupling T.ρA T.lam Y V u - hessianCellShare T.coupling T.ρA T.lam Y' V' u| ≤
      sumConst T M * (sumConst T M * (densityError T κ M C₁ C₂ r * inverseConst T + opConst T CS *
        (inverseConst T * sumConst T M * (densityError T κ M C₁ C₂ r * inverseConst T * sumConst T M +
          (2 * (inverseConst T * opConst T CS * sumConst T M) + 1) *
            Real.exp (-(κ * (((r / 2 / 2 : ℕ) : ℝ) / 2 / 4))))) +
        4 * (inverseConst T * opConst T CS) * Real.exp (-(κ * (((r / 2 / 2 : ℕ) : ℝ) / 2 / 8))))) := by
  classical
  obtain ⟨hodd, hs2, -⟩ := blockTorus_facts P.torus hD.L_odd
  obtain ⟨hodd', hs2', -⟩ := blockTorus_facts P.torus' hD.L_odd
  obtain ⟨hs, hs'⟩ := P.extent_gt hD
  have hLL : F'.blockSide = F.blockSide := by rw [P.torus.1, P.torus'.1]
  have hFL : F.blockSide = T.side := P.torus.1
  have hq : ∀ i, 2 * (r / 2 / 2) + 2 < F.extent i := fun i => by
    have := hs i
    omega
  have hq' : ∀ i, 2 * (r / 2 / 2) + 2 < F'.extent i := fun i => by
    have := hs' i
    omega
  have hS := decayingInverse_at tl hD hT hNum P.torus P.cold Y hu0 hu1
  have hS' := decayingInverse_at tl hD hT hNum P.torus' P.cold' Y' hu0 hu1
  have hP := indexPairing_of_short tl.offsets hodd hodd' hLL hq hq' hN
  set e := pairedIndex (ι := ι) j with he
  set e' := pairedIndex (ι := ι) j' with he'
  set m : ℝ := ((r / 2 / 2 : ℕ) : ℝ) / 2 with hm
  have hm0 : 0 ≤ m := by positivity
  set ε := densityError T κ M C₁ C₂ r with hε
  have hg0 := closeness_nonneg (r := r) hD
  have hε0 : 0 ≤ ε := by
    have := hNum.C₁_nonneg
    have := hNum.C₂_nonneg
    have := hNum.M_nonneg
    rw [hε]
    unfold densityError
    positivity
  set H := chartedHessian T.coupling T.ρA V 0 with hH
  set H' := chartedHessian T.coupling T.ρA V' 0 with hH'
  have hsame : ∀ k, SameOffsets Y Y' (2 * (r / 2)) (e k) (e' k) := by
    intro k
    obtain ⟨h, o, kk, hh, ho, e₁, e₂⟩ := hN.short_offsets k.1
    refine ⟨rfl, h, o, kk, fun l => ?_, ho, e₁, e₂⟩
    have := hh l
    push_cast at this ⊢
    omega
  have hentry : ∀ k l, distFromCell Y (e k) ≤ m / 2 → |H (e k) (e l) - H' (e' k) (e' l)| ≤ ε := by
    intro k l hk
    have hk' : distFromCell Y' (e' k) ≤ m / 2 := by rw [← hP.dist_eq]; exact hk
    have cast1 : ∀ {G : BlockFrame} {Z : G.Cell} {x : CoordIndex G}, distFromCell Z x ≤ m / 2 →
        8 * cellSupDist (enclosingCell x.1.1.1) Z ≤ r / 2 := by
      intro G Z x hx
      unfold distFromCell at hx
      have h4 : 4 * (cellSupDist (enclosingCell x.1.1.1) Z : ℝ) ≤ ((r / 2 / 2 : ℕ) : ℝ) := by
        rw [hm] at hx
        linarith
      have h5 : 4 * cellSupDist (enclosingCell x.1.1.1) Z ≤ r / 2 / 2 := by exact_mod_cast h4
      omega
    exact abs_chartedHessian_sub_le tl hD hT hNum.C₂_nonneg hNum.κ_pos.le hNum.entries hNum.moves hNum.smooth
      hNum.sums P hr hgap hG (hsame k) (hsame l) (cast1 hk) (cast1 hk')
  have hc : ∀ k l, distFromCell Y (e k) ≤ m / 2 →
      |interpolatedOp H T.lam u (e k) (e l) - interpolatedOp H' T.lam u (e' k) (e' l)| ≤ ε := fun k l hk =>
    (abs_interpolatedOp_sub_le hP.injective_left hP.injective_right hu0 hu1 T.lam k l).trans (hentry k l hk)
  set ρ₀ : ℝ := inverseConst T * sumConst T M * (ε * inverseConst T * sumConst T M +
    (2 * (inverseConst T * opConst T CS * sumConst T M) + 1) * Real.exp (-(κ * (m / 4)))) with hρ₀
  have hρ0 : 0 ≤ ρ₀ := by
    have := hS.A_nonneg
    have := hS.B_nonneg
    have := hS.K_nonneg
    rw [hρ₀]
    positivity
  have hres : ∀ a b, distFromCell Y (e a) ≤ m / 4 →
      |(interpolatedOp H T.lam u)⁻¹ (e a) (e b) - (interpolatedOp H' T.lam u)⁻¹ (e' a) (e' b)| ≤ ρ₀ :=
    fun a b ha => abs_inv_sub_inv_le hS hS' hP hm0 hε0 hc a b ha
  have hprod : ∀ a, distFromCell Y (e a) ≤ m / 8 →
      |((H - T.lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) * (interpolatedOp H T.lam u)⁻¹) (e a) (e a) -
        ((H' - T.lam • (1 : Matrix (CoordIndex F') (CoordIndex F') ℝ)) * (interpolatedOp H' T.lam u)⁻¹) (e' a) (e' a)| ≤
      sumConst T M * (ε * inverseConst T + opConst T CS * ρ₀ +
        4 * (inverseConst T * opConst T CS) * Real.exp (-(κ * (m / 8)))) := by
    intro a ha
    refine abs_mul_inv_diag_sub_le hS hS' hP hm0 hε0 hρ0 a (fun l => ?_) (fun l hl => hres l a hl) ha
    rw [sub_smul_one_sub_eq hP.injective_left hP.injective_right]
    exact hentry a l (by linarith)
  set Pb : ℝ := sumConst T M * (ε * inverseConst T + opConst T CS * ρ₀ +
    4 * (inverseConst T * opConst T CS) * Real.exp (-(κ * (m / 8)))) with hPb
  have hPb0 : 0 ≤ Pb := by
    have := hS.A_nonneg
    have := hS.B_nonneg
    have := hS.K_nonneg
    rw [hPb]
    positivity
  set f : CoordIndex F → ℝ := fun i => if enclosingCell i.1.1.1 = Y then
    ((H - T.lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) * (interpolatedOp H T.lam u)⁻¹) i i else 0 with hf
  set f' : CoordIndex F' → ℝ := fun i => if enclosingCell i.1.1.1 = Y' then
    ((H' - T.lam • (1 : Matrix (CoordIndex F') (CoordIndex F') ℝ)) * (interpolatedOp H' T.lam u)⁻¹) i i else 0
    with hf'
  have e0 : hessianCellShare T.coupling T.ρA T.lam Y V u = ∑ i, f i := rfl
  have e0' : hessianCellShare T.coupling T.ρA T.lam Y' V' u = ∑ i, f' i := rfl
  have hcell : ∀ i : CoordIndex F, enclosingCell i.1.1.1 = Y ↔ distFromCell Y i = 0 := fun i => by
    rw [eq_iff_cellSupDist_eq_zero tl.offsets hodd hs2]
    unfold distFromCell
    exact_mod_cast Iff.rfl
  have hcell' : ∀ i : CoordIndex F', enclosingCell i.1.1.1 = Y' ↔ distFromCell Y' i = 0 := fun i => by
    rw [eq_iff_cellSupDist_eq_zero tl.offsets hodd' hs2']
    unfold distFromCell
    exact_mod_cast Iff.rfl
  have t0 : ∑ x ∈ (Finset.univ.image e)ᶜ, f x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have h1 := hP.lt_of_not_mem hx
    have h2 : enclosingCell x.1.1.1 ≠ Y := fun h => by
      have := (hcell x).1 h
      linarith
    simp [hf, h2]
  have t0' : ∑ x ∈ (Finset.univ.image e')ᶜ, f' x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have h1 : m < distFromCell Y' x := by
      by_contra hcn
      obtain ⟨k, hk⟩ := hP.surj_right x (not_lt.1 hcn)
      exact (Finset.mem_compl.1 hx) (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩)
    have h2 : enclosingCell x.1.1.1 ≠ Y' := fun h => by
      have := (hcell' x).1 h
      linarith
    simp [hf', h2]
  rw [e0, e0', sum_eq_sum_comp_add_sum_compl hP.injective_left f, sum_eq_sum_comp_add_sum_compl hP.injective_right f',
    t0, t0', add_zero, add_zero, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k, |f (e k) - f' (e' k)| ≤ Pb * Real.exp (-(κ * distFromCell Y (e k))) := by
    intro k
    by_cases h0 : distFromCell Y (e k) = 0
    · have c1 := (hcell (e k)).2 h0
      have c2 := (hcell' (e' k)).2 (by rw [← hP.dist_eq]; exact h0)
      simp only [hf, hf', c1, c2, if_true]
      rw [h0]
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      exact hprod k (by rw [h0]; positivity)
    · have c1 : enclosingCell (e k).1.1.1 ≠ Y := fun h => h0 ((hcell _).1 h)
      have c2 : enclosingCell (e' k).1.1.1 ≠ Y' := fun h => h0 (by rw [hP.dist_eq]; exact (hcell' _).1 h)
      simp only [hf, hf', if_neg c1, if_neg c2, sub_zero, abs_zero]
      positivity
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  rw [← Finset.mul_sum]
  have h2 := sum_exp_distFromCell_le tl.cover hodd hs2 hNum.sums Y
  rw [hFL] at h2
  have h3 := (sum_comp_le_sum hP.injective_left (f := fun x => Real.exp (-(κ * distFromCell Y x)))
    fun _ => (Real.exp_pos _).le).trans h2
  calc _ ≤ Pb * sumConst T M := mul_le_mul_of_nonneg_left h3 hPb0
    _ = _ := by ring
private theorem continuousOn_hessianCellShare (a ρ lam : ℝ) (Y : F.Cell) (V : F.GaugeField F.top)
    (hdet : ∀ u ∈ Set.Icc (0 : ℝ) 1, (interpolatedOp (chartedHessian a ρ V 0) lam u).det ≠ 0) :
    ContinuousOn (hessianCellShare a ρ lam Y V) (Set.Icc 0 1) := by
  classical
  set H := chartedHessian a ρ V 0 with hH
  have hO : Continuous fun u : ℝ => interpolatedOp H lam u := by
    unfold interpolatedOp
    fun_prop
  have hinv : ∀ x y : CoordIndex F, ContinuousOn (fun u : ℝ => (interpolatedOp H lam u)⁻¹ x y) (Set.Icc 0 1) := by
    intro x y
    have e : (fun u : ℝ => (interpolatedOp H lam u)⁻¹ x y) =
        fun u => ((interpolatedOp H lam u).det)⁻¹ * (interpolatedOp H lam u).adjugate x y := by
      funext u
      simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
    rw [e]
    exact (hO.matrix_det.continuousOn.inv₀ hdet).mul (hO.matrix_adjugate.matrix_elem x y).continuousOn
  have e0 : hessianCellShare a ρ lam Y V = fun u => ∑ i : CoordIndex F, if enclosingCell i.1.1.1 = Y then
      ∑ x, (H - lam • (1 : Matrix (CoordIndex F) (CoordIndex F) ℝ)) i x * (interpolatedOp H lam u)⁻¹ x i else 0 := by
    funext u
    rfl
  rw [e0]
  refine continuousOn_finsetSum _ fun i _ => ?_
  split_ifs
  · exact continuousOn_finsetSum _ fun x _ => continuousOn_const.mul (hinv x i)
  · exact continuousOn_const
private theorem abs_integral_sub_le {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) (hg : ContinuousOn g (Set.Icc 0 1))
    {C : ℝ} (h : ∀ u ∈ Set.Icc (0 : ℝ) 1, |f u - g u| ≤ C) :
    |(∫ u in (0 : ℝ)..1, f u) - ∫ u in (0 : ℝ)..1, g u| ≤ C := by
  have i1 : IntervalIntegrable f MeasureTheory.volume 0 1 := hf.intervalIntegrable_of_Icc (by norm_num)
  have i2 : IntervalIntegrable g MeasureTheory.volume 0 1 := hg.intervalIntegrable_of_Icc (by norm_num)
  rw [← intervalIntegral.integral_sub i1 i2]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (f := fun u => f u - g u) (C := C)
    (fun u hu => by
      rw [Set.uIoc_of_le (by norm_num)] at hu
      exact h u ⟨hu.1.le, hu.2⟩)
  simpa using this
private theorem abs_integral_le {f : ℝ → ℝ} {C : ℝ} (h : ∀ u ∈ Set.Icc (0 : ℝ) 1, |f u| ≤ C) :
    |∫ u in (0 : ℝ)..1, f u| ≤ C := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (f := f) (C := C)
    (fun u hu => by
      rw [Set.uIoc_of_le (by norm_num)] at hu
      exact h u ⟨hu.1.le, hu.2⟩)
  simpa using this
private theorem det_ne_zero_of_decayingInverse {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] {γ A B K : ℝ}
    {d : ι₀ → ι₀ → ℝ} {D : ι₀ → ℝ} {O R G : Matrix ι₀ ι₀ ℝ} (h : DecayingInverse γ A B K d D O R G) : O.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h.mul_inv
  rw [Matrix.det_mul, h0] at this
  simp at this
end Shares
end StepDensityLocality
end YangMills.Construction.RunningCouplingSlope
end
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open scoped Quaternion
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters TorusComparison Estimates ChartResponse
  SecondOrderMoves ChartLipschitz
namespace StepDensityLocality
section Parts
variable {F F' : BlockFrame} {T : ParameterAssignment} {c : ColdChainParameters}
private def contourLogTerm (a ρ : ℝ) (Y : F.Cell) (V : F.GaugeField F.top) : ℝ :=
  ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
    Real.log ‖contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖
private def haarLogTerm (a ρ : ℝ) (Y : F.Cell) (V : F.GaugeField F.top) : ℝ :=
  ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
    haarLogRatio (coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2) else 0
private theorem stepDensity_eq (a ρ lam : ℝ) (Y : F.Cell) (V : F.GaugeField F.top) :
    stepDensity a ρ lam Y V = -(1 / 2) * (∫ τ in (0 : ℝ)..1, hessianCellShare a ρ lam Y V τ) +
      3 / 2 * contourLogTerm a ρ Y V + haarLogTerm a ρ Y V := rfl
private theorem sum_innerBonds_cell (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (Y : F.Cell)
    (g : F.Site F.top × Fin 4 → ℝ) :
    ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y), g c = ∑ d : Fin 4, g (Y, d) := by
  classical
  have e : (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y) =
      Finset.univ.image fun d : Fin 4 => (Y, d) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨c.2, Prod.ext h.symm rfl⟩
    · rintro ⟨d, rfl⟩
      refine ⟨?_, rfl⟩
      unfold innerBonds
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨mem_sitesOfCells_finiteCells hodd hs le_rfl _, mem_sitesOfCells_finiteCells hodd hs le_rfl _⟩
  rw [e, Finset.sum_image fun a _ b _ h => (Prod.ext_iff.1 h).2]
private theorem contourLogTerm_eq (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (a ρ : ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top) :
    contourLogTerm a ρ Y V = ∑ d : Fin 4,
      Real.log ‖contourAverage (chartedField (minimizer a ρ V) V) ((Y, d) : F.Site F.top × Fin 4)‖ := by
  unfold contourLogTerm
  rw [sum_innerBonds_cell hodd hs]
  refine Finset.sum_congr rfl fun d _ => ?_
  show Real.log ‖contourAverage (chartedField (coordsAboveFrame true a ρ 0 V 0) V) _‖ = _
  rw [coordsAboveFrame_zero]
private theorem norm_contourAverage_mem (tl : Inputs) (hD : T.Admissible) (hF : IsBlockTorus T.side F)
    {V : F.GaugeField F.top} {v : F.Site F.depth → Fin 4 → imaginaryQuaternions} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : 5 * (T.side : ℝ) * ε ≤ 1 / 2) (hv : ∀ b ∈ chordBonds (finiteCells F), ‖v b.1 b.2‖ ≤ ε)
    (c' : F.Site F.top × Fin 4) :
    1 / 2 ≤ ‖contourAverage (chartedField v V) c'‖ ∧ ‖contourAverage (chartedField v V) c'‖ ≤ 1 := by
  obtain ⟨hodd, hs2, -⟩ := blockTorus_facts hF hD.L_odd
  have hFL : F.blockSide = T.side := hF.1
  refine norm_contourAverage_bounds hodd _ V c' fun h π hh => ?_
  have h2 := tl.contour F v V ε hodd hs2 hε0 hv c' h π hh
  have h3 : 5 * (F.blockSide : ℝ) * ε ≤ 1 / 2 := by
    rw [hFL]
    exact hε
  exact h2.trans h3
private theorem abs_log_le_one {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 1) : |Real.log x| ≤ 1 := by
  have := abs_log_sub_log_le h1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
  rw [Real.log_one, sub_zero] at this
  refine this.trans ?_
  rw [abs_of_nonpos (by linarith)]
  linarith
abbrev _root_.YangMills.SharedProofs.p60921 := @abs_log_le_one
private theorem side_mul_le_half (hD : T.Admissible) :
    5 * (T.side : ℝ) * (2 * ((T.N 0 + 1) * T.threshold)) ≤ 1 / 2 := by
  obtain ⟨hσ, -⟩ := threshold_facts hD
  have h := hD.σ_L
  nlinarith
private theorem norm_minimizer_add_le (hD : T.Admissible) {V : F.GaugeField F.top}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} (hw : MinimizerFacts T V w) {g : ℝ}
    (hg : g ≤ T.threshold / 16) {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds (finiteCells F)) :
    ‖w b.1 b.2‖ + g ≤ 2 * ((T.N 0 + 1) * T.threshold) := by
  obtain ⟨hσ, -⟩ := threshold_facts hD
  obtain ⟨-, -, -, -, -, -, -, hNpos, -⟩ := hD.chain
  have := hNpos 0
  have := hw.norm_le_threshold b hb
  nlinarith
private theorem abs_contourLogTerm_le (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c)
    (hF : IsBlockTorus T.side F) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature (9 / 8 * T.threshold) V) (Y : F.Cell) : |contourLogTerm T.coupling T.ρA Y V| ≤ 4 := by
  obtain ⟨hodd, -, hs1⟩ := blockTorus_facts hF hD.L_odd
  obtain ⟨hσ, -⟩ := threshold_facts hD
  obtain ⟨-, -, -, -, -, -, -, hNpos, -⟩ := hD.chain
  have hN := hNpos 0
  have hw := minimizerFacts tl.unique hD hT hF hV
  rw [contourLogTerm_eq hodd hs1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ d : Fin 4, |Real.log ‖contourAverage (chartedField (minimizer T.coupling T.ρA V) V)
      ((Y, d) : F.Site F.top × Fin 4)‖| ≤ 1 := by
    intro d
    obtain ⟨a1, a2⟩ := norm_contourAverage_mem tl hD hF (V := V) (v := minimizer T.coupling T.ρA V) (by positivity)
      (side_mul_le_half hD)
      (fun b hb => by
        have := norm_minimizer_add_le hD hw (g := 0) (by positivity) hb
        linarith) ((Y, d) : F.Site F.top × Fin 4)
    exact abs_log_le_one a1 a2
  refine (Finset.sum_le_sum fun d _ => this d).trans ?_
  simp
variable {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
private def ContourAgreementAt (L : ℕ) (c : ColdChainParameters) : Prop :=
  ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ), 1 ≤ r → IsBlockTorus L F → IsBlockTorus L F' →
    F'.depth = F.depth → IsAdmissibleChartPoint L c.σA w V → IsAdmissibleChartPoint L c.σA w' V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
    (∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube L →
      fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
      w (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i) →
    ∀ (g : Fin 4 → ℤ) (d : Fin 4), WithinRadius r g → WithinRadius r (g + Pi.single d 1) →
      contourAverage (chartedField w V) ((Y + siteOfCoords F.top g, d) : F.Site (F.depth + 1) × Fin 4) =
        contourAverage (chartedField w' V') ((Y' + siteOfCoords F'.top g, d) : F'.Site (F'.depth + 1) × Fin 4)
private theorem abs_contourLogTerm_sub_le (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c)
    (hMn : ContourAgreementAt T.side c) (P : AgreeingTops T V V' Y Y' r) (hr : 2 ≤ r)
    (hgap : closeness T r ≤ T.threshold / 32) {Δ : StepVariable (finiteCells F)}
    (hG : IsGluingMove T r Y Y' (minimizer T.coupling T.ρA V) (minimizer T.coupling T.ρA V') Δ) :
    |contourLogTerm T.coupling T.ρA Y V - contourLogTerm T.coupling T.ρA Y' V'| ≤
      4 * (10 * (T.side : ℝ) * closeness T r) := by
  obtain ⟨hσ, -⟩ := threshold_facts hD
  obtain ⟨hodd, hs2, hs1⟩ := blockTorus_facts P.torus hD.L_odd
  obtain ⟨hodd', hs2', hs1'⟩ := blockTorus_facts P.torus' hD.L_odd
  obtain ⟨-, -, -, -, -, -, -, hNpos, -⟩ := hD.chain
  have hN := hNpos 0
  have hFL : F.blockSide = T.side := P.torus.1
  have hw := minimizerFacts tl.unique hD hT P.torus P.cold
  have hw' := minimizerFacts tl.unique hD hT P.torus' P.cold'
  set w := minimizer T.coupling T.ρA V with hwdef
  set w' := minimizer T.coupling T.ρA V' with hw'def
  have hg0 := closeness_nonneg (r := r) hD
  have hΔ := norm_stepCoordinates_glue_le hD hG
  have hσc : c.σA = T.σA := hT.σA_eq
  have hsy : IsAdmissibleChartPoint T.side c.σA (ColdStepAtMirrorFrames.shiftCoordinates w Δ) V := by
    rw [hσc]
    exact admissible_of_near tl.lipschitz hD P.torus hw hg0 (by linarith) fun z k => by
      simp only [ColdStepAtMirrorFrames.shiftCoordinates, add_sub_cancel_left]
      exact hΔ z k
  have hs' : IsAdmissibleChartPoint T.side c.σA w' V' := by
    rw [hσc]
    exact admissible_of_near tl.lipschitz hD P.torus' hw' le_rfl (by positivity) fun z k => by simp
  have hε0 : 0 ≤ 2 * ((T.N 0 + 1) * T.threshold) := by positivity
  rw [contourLogTerm_eq hodd hs1, contourLogTerm_eq hodd' hs1', ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ d : Fin 4, |Real.log ‖contourAverage (chartedField w V) ((Y, d) : F.Site F.top × Fin 4)‖ -
      Real.log ‖contourAverage (chartedField w' V') ((Y', d) : F'.Site F'.top × Fin 4)‖| ≤
        10 * (T.side : ℝ) * closeness T r := by
    intro d
    have hbox0 : WithinRadius (r / 2) (0 : Fin 4 → ℤ) := fun i => by
      simp only [Pi.zero_apply, abs_zero]
      exact Int.natCast_nonneg _
    have hbox1 : WithinRadius (r / 2) ((0 : Fin 4 → ℤ) + Pi.single d 1) := fun i => by
      have : 1 ≤ r / 2 := by omega
      by_cases hi : i = d
      · subst hi
        simp only [Pi.add_apply, Pi.zero_apply, zero_add, Pi.single_eq_same, abs_one]
        exact_mod_cast this
      · simp only [Pi.add_apply, Pi.zero_apply, zero_add, Pi.single_eq_of_ne hi, abs_zero]
        exact Int.natCast_nonneg _
    have e1 := hMn F F' (ColdStepAtMirrorFrames.shiftCoordinates w Δ) w' V V' Y Y' (r / 2) (by omega) P.torus P.torus'
      P.level hsy hs' (agreeOnBall_half P hD) (fun h o i hh ho hb => hG.shift_eq h o i hh ho hb) 0 d hbox0 hbox1
    have e2 : contourAverage (chartedField (ColdStepAtMirrorFrames.shiftCoordinates w Δ) V)
        ((Y, d) : F.Site F.top × Fin 4) =
        contourAverage (chartedField w' V') ((Y', d) : F'.Site F'.top × Fin 4) := by
      have x1 := add_siteOfCoords_zero F Y
      have x2 := add_siteOfCoords_zero F' Y'
      have := e1
      simp only [add_siteOfCoords_zero] at this
      exact this
    have a1 := norm_contourAverage_mem tl hD P.torus (V := V) (v := w) hε0 (side_mul_le_half hD) (fun b hb => by
      have := norm_minimizer_add_le hD hw (g := 0) (by positivity) hb
      linarith) ((Y, d) : F.Site F.top × Fin 4)
    have a2 := norm_contourAverage_mem tl hD P.torus (V := V) (v := ColdStepAtMirrorFrames.shiftCoordinates w Δ) hε0
      (side_mul_le_half hD) (fun b hb => by
      have h1 := norm_minimizer_add_le hD hw (g := closeness T r) (by linarith) hb
      have h2 := hΔ b.1 b.2
      have h3 : ‖ColdStepAtMirrorFrames.shiftCoordinates w Δ b.1 b.2‖ ≤ ‖w b.1 b.2‖ + ‖stepCoordinates Δ b.1 b.2‖ :=
        norm_add_le _ _
      linarith) ((Y, d) : F.Site F.top × Fin 4)
    have a3 := norm_contourAverage_sub_le tl.lipschitz hodd (ColdStepAtMirrorFrames.shiftCoordinates w Δ) w V hg0
      (fun z k => by
        simp only [ColdStepAtMirrorFrames.shiftCoordinates, add_sub_cancel_left]
        exact hΔ z k) ((Y, d) : F.Site F.top × Fin 4)
    rw [← e2]
    refine (abs_log_sub_log_le a1.1 a2.1).trans ?_
    have a4 := abs_norm_sub_norm_le (contourAverage (chartedField w V) ((Y, d) : F.Site F.top × Fin 4))
      (contourAverage (chartedField (ColdStepAtMirrorFrames.shiftCoordinates w Δ) V) ((Y, d) : F.Site F.top × Fin 4))
    rw [norm_sub_rev] at a4
    rw [hFL] at a3
    linarith
  refine (Finset.sum_le_sum fun d _ => hterm d).trans ?_
  simp
private theorem haarLogRatio_lipschitz (hH : HaarLogRatioNearZero) : ∃ Ch : ℝ, 0 ≤ Ch ∧
    ∀ u v : imaginaryQuaternions, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → |haarLogRatio u - haarLogRatio v| ≤ Ch * ‖u - v‖ := by
  obtain ⟨C, hC, h⟩ := hH
  refine ⟨C, hC.le, fun u v hu hv => ?_⟩
  have hconv : Convex ℝ (Metric.closedBall (0 : imaginaryQuaternions) 1) := convex_closedBall _ _
  have := hconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := haarLogRatio) (C := C) (x := v) (y := u)
    (fun x hx => by
      have hx' : ‖x‖ ≤ 1 := by simpa using hx
      exact (h x hx').1.differentiableAt (by norm_num))
    (fun x hx => by
      have hx' : ‖x‖ ≤ 1 := by simpa using hx
      refine ContinuousLinearMap.opNorm_le_bound _ hC.le fun e => ?_
      rw [Real.norm_eq_abs]
      exact (h x hx').2.1 e) (by simpa using hv) (by simpa using hu)
  simpa [Real.norm_eq_abs] using this
abbrev _root_.YangMills.SharedProofs.p83653 := @haarLogRatio_lipschitz
private theorem haarLogTerm_eq (a ρ : ℝ) (Y : F.Cell) (V : F.GaugeField F.top) :
    haarLogTerm a ρ Y V = ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      haarLogRatio (minimizer a ρ V b.1.1 b.1.2) else 0 := by
  unfold haarLogTerm
  rw [coordsAboveFrame_zero]
private theorem sum_exp_chordBonds_le (tl : Inputs) (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {κ M : ℝ}
    (hM : ∀ (F : BlockFrame) (c : F.Cell), (∀ i, 2 ≤ F.extent i) →
      ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ M)
    (Y : F.Cell) :
    ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(κ * cellSupDist (enclosingCell b.1.1) Y)) ≤
      4 * ((centredCube F.blockSide).card : ℝ) * M := by
  have h1 := CellSums.sum_bonds_le_sum_cells tl.cover hodd hs (fun z => Real.exp (-(κ * cellSupDist z Y)))
    (fun _ => (Real.exp_pos _).le) (chordBonds (finiteCells F))
  rw [← Finset.sum_coe_sort] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (hM F Y hs) (by positivity))
private theorem abs_haarLogTerm_le (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c)
    (hB : haarLogRatioBoundStatement) {κ M : ℝ}
    (hM : ∀ (F : BlockFrame) (c : F.Cell), (∀ i, 2 ≤ F.extent i) →
      ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ M)
    (hF : IsBlockTorus T.side F) {V : F.GaugeField F.top} (hV : IsSmallCurvature (9 / 8 * T.threshold) V) (Y : F.Cell) :
    |haarLogTerm T.coupling T.ρA Y V| ≤ 4 * ((centredCube T.side).card : ℝ) * M := by
  obtain ⟨hodd, hs2, -⟩ := blockTorus_facts hF hD.L_odd
  obtain ⟨-, -, -, -, hρ1, -⟩ := hD.chain
  have hFL : F.blockSide = T.side := hF.1
  have hw := minimizerFacts tl.unique hD hT hF hV
  rw [haarLogTerm_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h := sum_exp_chordBonds_le tl hodd hs2 hM Y
  rw [hFL] at h
  refine le_trans (Finset.sum_le_sum fun b _ => ?_) h
  split_ifs with hc
  · have hb : ‖minimizer T.coupling T.ρA V b.1.1 b.1.2‖ ≤ 1 := (hw.norm_le b.1 b.2).trans hρ1
    have h0 : cellSupDist (enclosingCell b.1.1) Y = 0 := (eq_iff_cellSupDist_eq_zero tl.offsets hodd hs2 _ _).1 hc
    rw [h0]
    simpa using hB _ hb
  · simp only [abs_zero]
    exact (Real.exp_pos _).le
private theorem abs_haarLogTerm_sub_le (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c) {Ch κ M : ℝ}
    (hCh0 : 0 ≤ Ch)
    (hCh : ∀ u v : imaginaryQuaternions, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → |haarLogRatio u - haarLogRatio v| ≤ Ch * ‖u - v‖)
    (hM : ∀ (F : BlockFrame) (c : F.Cell), (∀ i, 2 ≤ F.extent i) →
      ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ M)
    (P : AgreeingTops T V V' Y Y' r) (hr : 2 ≤ r)
    {ι : Type} [Fintype ι] [DecidableEq ι] {j : ι → ↥(chordBonds (finiteCells F))}
    {j' : ι → ↥(chordBonds (finiteCells F'))}
    (hN : IsShortPairing Y Y' (r / 2 / 2) j j') :
    |haarLogTerm T.coupling T.ρA Y V - haarLogTerm T.coupling T.ρA Y' V'| ≤
      Ch * closeness T r * (4 * ((centredCube T.side).card : ℝ) * M) := by
  classical
  obtain ⟨hodd, hs2, -⟩ := blockTorus_facts P.torus hD.L_odd
  obtain ⟨hodd', hs2', -⟩ := blockTorus_facts P.torus' hD.L_odd
  obtain ⟨hs, hs'⟩ := P.extent_gt hD
  obtain ⟨-, -, -, -, hρ1, -⟩ := hD.chain
  have hFL : F.blockSide = T.side := P.torus.1
  have hLL : F'.blockSide = F.blockSide := by rw [P.torus.1, P.torus'.1]
  have hw := minimizerFacts tl.unique hD hT P.torus P.cold
  have hw' := minimizerFacts tl.unique hD hT P.torus' P.cold'
  have hNear := coordinatesCloseOnBall tl hD hT P hr
  have hg0 := closeness_nonneg (r := r) hD
  have hq : ∀ i, 2 * (r / 2 / 2) + 2 < F.extent i := fun i => by
    have := hs i
    omega
  have hq' : ∀ i, 2 * (r / 2 / 2) + 2 < F'.extent i := fun i => by
    have := hs' i
    omega
  have hP := indexPairing_of_short tl.offsets hodd hodd' hLL hq hq' hN
  set w := minimizer T.coupling T.ρA V with hwdef
  set w' := minimizer T.coupling T.ρA V' with hw'def
  set f : ↥(chordBonds (finiteCells F)) → ℝ := fun b =>
    if enclosingCell b.1.1 = Y then haarLogRatio (w b.1.1 b.1.2) else 0 with hf
  set f' : ↥(chordBonds (finiteCells F')) → ℝ := fun b =>
    if enclosingCell b.1.1 = Y' then haarLogRatio (w' b.1.1 b.1.2) else 0 with hf'
  have tail : ∀ {G : BlockFrame} (Z : G.Cell) (l : ι → ↥(chordBonds (finiteCells G)))
      (hrg : ∀ b, b ∈ bondsNearCell Z (r / 2 / 2) ↔ ∃ i, l i = b) (hG : Odd G.blockSide) (hG2 : ∀ i, 2 ≤ G.extent i)
      (x : ↥(chordBonds (finiteCells G))), x ∈ (Finset.univ.image l)ᶜ → enclosingCell x.1.1 ≠ Z := by
    intro G Z l hrg hG hG2 x hx hc
    have h0 : cellSupDist (enclosingCell x.1.1) Z = 0 := (eq_iff_cellSupDist_eq_zero tl.offsets hG hG2 _ _).1 hc
    have hm : x ∈ bondsNearCell Z (r / 2 / 2) := by
      simp only [bondsNearCell, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    obtain ⟨k, hk⟩ := (hrg x).1 hm
    exact (Finset.mem_compl.1 hx) (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩)
  have t0 : ∑ x ∈ (Finset.univ.image j)ᶜ, f x = 0 := Finset.sum_eq_zero fun x hx => by
    simp [hf, tail Y j hN.isBoxPairing.mem_left_iff hodd hs2 x hx]
  have t0' : ∑ x ∈ (Finset.univ.image j')ᶜ, f' x = 0 := Finset.sum_eq_zero fun x hx => by
    simp [hf', tail Y' j' hN.isBoxPairing.mem_right_iff hodd' hs2' x hx]
  have hterm : ∀ k, |f (j k) - f' (j' k)| ≤
      Ch * closeness T r * Real.exp (-(κ * cellSupDist (enclosingCell (j k).1.1) Y)) := by
    intro k
    have hdd : cellSupDist (enclosingCell (j k).1.1) Y = cellSupDist (enclosingCell (j' k).1.1) Y' := by
      have := hP.dist_eq (k, 0)
      unfold distFromCell pairedIndex at this
      exact_mod_cast this
    by_cases h0 : enclosingCell (j k).1.1 = Y
    · have z0 := (eq_iff_cellSupDist_eq_zero tl.offsets hodd hs2 _ _).1 h0
      have h0' : enclosingCell (j' k).1.1 = Y' :=
        (eq_iff_cellSupDist_eq_zero tl.offsets hodd' hs2' _ _).2 (by rw [← hdd]; exact z0)
      simp only [hf, hf', if_pos h0, if_pos h0', z0, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
      obtain ⟨h, o, kk, hh, ho, e₁, e₂⟩ := hN.short_offsets k
      have hbox : WithinRadius (r / 2) h := fun l => by
        have := hh l
        push_cast at this ⊢
        have h3 := abs_nonneg (h l)
        omega
      have hb : fineBondAt Y h o kk ∈ chordBonds (finiteCells F) := by
        rw [← e₁]
        exact (j k).2
      have n1 := hNear h o kk hbox (by rw [← hFL]; exact ho) hb
      have n2 : ‖((w (j k).1.1 (j k).1.2 : imaginaryQuaternions) : ℍ[ℝ]) -
          (w' (j' k).1.1 (j' k).1.2 : imaginaryQuaternions)‖ ≤ closeness T r := by
        rw [e₁, e₂]
        exact n1
      have s1 : ‖w (j k).1.1 (j k).1.2‖ ≤ 1 := (hw.norm_le _ (j k).2).trans hρ1
      have s2 : ‖w' (j' k).1.1 (j' k).1.2‖ ≤ 1 := (hw'.norm_le _ (j' k).2).trans hρ1
      refine (hCh _ _ s1 s2).trans (mul_le_mul_of_nonneg_left ?_ hCh0)
      exact n2
    · have h0' : enclosingCell (j' k).1.1 ≠ Y' := fun h => by
        have z0 := (eq_iff_cellSupDist_eq_zero tl.offsets hodd' hs2' _ _).1 h
        exact h0 ((eq_iff_cellSupDist_eq_zero tl.offsets hodd hs2 _ _).2 (by rw [hdd]; exact z0))
      simp only [hf, hf', if_neg h0, if_neg h0', sub_zero, abs_zero]
      positivity
  rw [haarLogTerm_eq, haarLogTerm_eq]
  show |∑ b, f b - ∑ b, f' b| ≤ _
  rw [sum_eq_sum_comp_add_sum_compl hN.isBoxPairing.injective_left f,
    sum_eq_sum_comp_add_sum_compl hN.isBoxPairing.injective_right f', t0, t0', add_zero, add_zero,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => hterm k).trans ?_)
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h3 := sum_exp_chordBonds_le tl hodd hs2 hM Y
  rw [hFL] at h3
  exact (sum_comp_le_sum hN.isBoxPairing.injective_left
    (f := fun b => Real.exp (-(κ * cellSupDist (enclosingCell b.1.1) Y)))
    fun _ => (Real.exp_pos _).le).trans h3
end Parts
end StepDensityLocality
end YangMills.Construction.RunningCouplingSlope
end
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open scoped Quaternion
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters TorusComparison Estimates ChartResponse
  SecondOrderMoves ChartLipschitz
namespace StepDensityLocality
section Final
variable {F F' : BlockFrame} {T : ParameterAssignment} {c : ColdChainParameters}
private theorem abs_combination_le (a b d : ℝ) {A B D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hd : |d| ≤ D) :
    |-(1 / 2) * a + 3 / 2 * b + d| ≤ 1 / 2 * A + 3 / 2 * B + D := by
  rw [abs_le] at *
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hd.1, hd.2]
private def densityBound (T : ParameterAssignment) (CS M : ℝ) : ℝ :=
  1 / 2 * (sumConst T M * (inverseConst T * opConst T CS * sumConst T M)) + 3 / 2 * 4 +
    4 * ((centredCube T.side).card : ℝ) * M
private theorem abs_stepDensity_le (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c)
    (hB : haarLogRatioBoundStatement) {CS κ M C₁ C₂ : ℝ}
    (hN : ParameterConstants T c CS κ M C₁ C₂) (hF : IsBlockTorus T.side F) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature (9 / 8 * T.threshold) V)
    (Y : F.Cell) : |stepDensity T.coupling T.ρA T.lam Y V| ≤ densityBound T CS M := by
  rw [stepDensity_eq]
  have h1 := abs_integral_le (f := hessianCellShare T.coupling T.ρA T.lam Y V) fun u hu =>
    abs_hessianCellShare_le tl hD hT hN hF hV Y hu.1 hu.2
  have h2 := abs_contourLogTerm_le tl hD hT hF hV Y
  have h3 := abs_haarLogTerm_le tl hD hT hB hN.sums hF hV Y
  exact abs_combination_le _ _ _ h1 h2 h3
private def shareError (T : ParameterAssignment) (CS κ M C₁ C₂ : ℝ) (r : ℕ) : ℝ :=
  sumConst T M * (sumConst T M * (densityError T κ M C₁ C₂ r * inverseConst T + opConst T CS *
    (inverseConst T * sumConst T M * (densityError T κ M C₁ C₂ r * inverseConst T * sumConst T M +
      (2 * (inverseConst T * opConst T CS * sumConst T M) + 1) *
        Real.exp (-(κ * (((r / 2 / 2 : ℕ) : ℝ) / 2 / 4))))) +
    4 * (inverseConst T * opConst T CS) * Real.exp (-(κ * (((r / 2 / 2 : ℕ) : ℝ) / 2 / 8)))))
variable {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
private theorem abs_stepDensity_sub_le (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c)
    {CS κ M C₁ C₂ Ch : ℝ} (hN : ParameterConstants T c CS κ M C₁ C₂)
    (hMn : ContourAgreementAt T.side c) (hCh0 : 0 ≤ Ch)
    (hCh : ∀ u v : imaginaryQuaternions, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → |haarLogRatio u - haarLogRatio v| ≤ Ch * ‖u - v‖)
    (P : AgreeingTops T V V' Y Y' r) (hr : 2 ≤ r) (hgap : closeness T r ≤ T.threshold / 32) :
    |stepDensity T.coupling T.ρA T.lam Y V - stepDensity T.coupling T.ρA T.lam Y' V'| ≤
      1 / 2 * shareError T CS κ M C₁ C₂ r + 3 / 2 * (4 * (10 * (T.side : ℝ) * closeness T r)) +
        Ch * closeness T r * (4 * ((centredCube T.side).card : ℝ) * M) := by
  obtain ⟨hodd, -, -⟩ := blockTorus_facts P.torus hD.L_odd
  obtain ⟨hs, hs'⟩ := P.extent_gt hD
  have hLL : F'.blockSide = F.blockSide := by rw [P.torus.1, P.torus'.1]
  obtain ⟨Δ, hG⟩ := exists_gluingMove tl hD hT P hr
  obtain ⟨ι, _, _, j, j', hNp⟩ := tl.pairs F F' Y Y' (r / 2 / 2) hodd hLL (fun i => by
    have := hs i
    omega) (fun i => by
    have := hs' i
    omega)
  have c1 : ContinuousOn (hessianCellShare T.coupling T.ρA T.lam Y V) (Set.Icc 0 1) :=
    continuousOn_hessianCellShare _ _ _ Y V fun u hu =>
      det_ne_zero_of_decayingInverse (decayingInverse_at tl hD hT hN P.torus P.cold Y hu.1 hu.2)
  have c2 : ContinuousOn (hessianCellShare T.coupling T.ρA T.lam Y' V') (Set.Icc 0 1) :=
    continuousOn_hessianCellShare _ _ _ Y' V' fun u hu =>
      det_ne_zero_of_decayingInverse (decayingInverse_at tl hD hT hN P.torus' P.cold' Y' hu.1 hu.2)
  have h1 := abs_integral_sub_le c1 c2 (C := shareError T CS κ M C₁ C₂ r) fun u hu =>
    abs_hessianCellShare_sub_le tl hD hT hN P hr hgap hG hNp hu.1 hu.2
  have h2 := abs_contourLogTerm_sub_le tl hD hT hMn P hr hgap hG
  have h3 := abs_haarLogTerm_sub_le tl hD hT hCh0 hCh hN.sums P hr hNp
  rw [stepDensity_eq, stepDensity_eq]
  set I₁ := ∫ τ in (0 : ℝ)..1, hessianCellShare T.coupling T.ρA T.lam Y V τ
  set I₂ := ∫ τ in (0 : ℝ)..1, hessianCellShare T.coupling T.ρA T.lam Y' V' τ
  have e : -(1 / 2) * I₁ + 3 / 2 * contourLogTerm T.coupling T.ρA Y V + haarLogTerm T.coupling T.ρA Y V -
      (-(1 / 2) * I₂ + 3 / 2 * contourLogTerm T.coupling T.ρA Y' V' + haarLogTerm T.coupling T.ρA Y' V') =
      -(1 / 2) * (I₁ - I₂) + 3 / 2 * (contourLogTerm T.coupling T.ρA Y V - contourLogTerm T.coupling T.ρA Y' V') +
        (haarLogTerm T.coupling T.ρA Y V - haarLogTerm T.coupling T.ρA Y' V') := by ring
  rw [e]
  exact abs_combination_le _ _ _ h1 h2 h3
private theorem radius_halves (r : ℕ) : (r : ℝ) - 1 ≤ 2 * ((r / 2 : ℕ) : ℝ) ∧ 2 * ((r / 2 : ℕ) : ℝ) ≤ r ∧
    (r : ℝ) - 3 ≤ 4 * ((r / 2 / 2 : ℕ) : ℝ) := by
  have h1 : r ≤ 2 * (r / 2) + 1 := by omega
  have h2 : 2 * (r / 2) ≤ r := by omega
  have h3 : r ≤ 4 * (r / 2 / 2) + 3 := by omega
  have h1' : (r : ℝ) ≤ 2 * ((r / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
  have h2' : 2 * ((r / 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast h2
  have h3' : (r : ℝ) ≤ 4 * ((r / 2 / 2 : ℕ) : ℝ) + 3 := by exact_mod_cast h3
  exact ⟨by linarith, h2', by linarith⟩
private theorem closeness_le (hD : T.Admissible) {κ : ℝ} (hκ : 0 < κ) (hκδ : κ ≤ T.δ₁ / 8) (r : ℕ) :
    closeness T r ≤ T.N 0 * (9 / 8 * T.threshold) * Real.exp (-(κ / 64 * r)) := by
  obtain ⟨hσ, -⟩ := threshold_facts hD
  obtain ⟨-, -, -, -, -, -, -, hNpos, -⟩ := hD.chain
  have := hNpos 0
  unfold closeness
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  nlinarith
private theorem densityError_le (hD : T.Admissible) {κ M C₁ C₂ : ℝ} (hκ : 0 < κ) (hκδ : κ ≤ T.δ₁ / 8) (hM : 0 ≤ M)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (r : ℕ) :
    densityError T κ M C₁ C₂ r ≤ (C₁ * Real.exp κ + C₂ * (T.N 0 * (9 / 8 * T.threshold)) *
      (4 * ((centredCube T.side).card : ℝ) * M)) * Real.exp (-(κ / 64 * r)) := by
  obtain ⟨hσ, -⟩ := threshold_facts hD
  obtain ⟨-, -, -, -, -, -, -, hNpos, -⟩ := hD.chain
  have hN := hNpos 0
  obtain ⟨r1, r2, -⟩ := radius_halves r
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ ((r / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have t1 : Real.exp (-(T.δ₁ / 16 * ((r / 2 : ℕ) : ℝ))) ≤ Real.exp κ * Real.exp (-(κ / 64 * r)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have t2 : closeness T r * Real.exp (κ * ((r / 2 : ℕ) : ℝ)) ≤
      T.N 0 * (9 / 8 * T.threshold) * Real.exp (-(κ / 64 * r)) := by
    unfold closeness
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    nlinarith
  unfold densityError
  have u1 := mul_le_mul_of_nonneg_left t1 hC₁
  have u2 := mul_le_mul_of_nonneg_left t2 (by positivity : 0 ≤ C₂ * (4 * ((centredCube T.side).card : ℝ) * M))
  nlinarith
private theorem shareError_le (hD : T.Admissible) {CS κ M C₁ C₂ : ℝ} (hCS : 0 ≤ CS) (hκ : 0 < κ) (hκδ : κ ≤ T.δ₁ / 8)
    (hM : 0 ≤ M) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (r : ℕ) {E : ℝ}
    (hE : E = C₁ * Real.exp κ + C₂ * (T.N 0 * (9 / 8 * T.threshold)) * (4 * ((centredCube T.side).card : ℝ) * M)) :
    shareError T CS κ M C₁ C₂ r ≤ sumConst T M * (sumConst T M * (E * inverseConst T + opConst T CS *
      (inverseConst T * sumConst T M * (E * inverseConst T * sumConst T M +
        (2 * (inverseConst T * opConst T CS * sumConst T M) + 1) * Real.exp κ)) +
      4 * (inverseConst T * opConst T CS) * Real.exp κ)) * Real.exp (-(κ / 64 * r)) := by
  obtain ⟨-, -, hlam, -⟩ := hD.chain
  have hA : 0 ≤ inverseConst T := by
    unfold inverseConst
    positivity
  have hB : 0 ≤ opConst T CS := by
    unfold opConst
    positivity
  have hK : 0 ≤ sumConst T M := by
    unfold sumConst
    positivity
  set X := Real.exp (-(κ / 64 * r)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have he := densityError_le hD hκ hκδ hM hC₁ hC₂ r
  rw [← hE] at he
  obtain ⟨-, -, r3⟩ := radius_halves r
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have e1 : Real.exp (-(κ * (((r / 2 / 2 : ℕ) : ℝ) / 2 / 4))) ≤ Real.exp κ * X := by
    rw [hX, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have e2 : Real.exp (-(κ * (((r / 2 / 2 : ℕ) : ℝ) / 2 / 8))) ≤ Real.exp κ * X := by
    rw [hX, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  unfold shareError
  calc _ ≤ sumConst T M * (sumConst T M * ((E * X) * inverseConst T + opConst T CS *
        (inverseConst T * sumConst T M * ((E * X) * inverseConst T * sumConst T M +
          (2 * (inverseConst T * opConst T CS * sumConst T M) + 1) * (Real.exp κ * X))) +
        4 * (inverseConst T * opConst T CS) * (Real.exp κ * X))) := by gcongr
    _ = _ := by ring
private theorem closeness_le_threshold (hD : T.Admissible) {r : ℕ} (hr : 72 * T.N 0 / T.δ₁ ≤ r) :
    closeness T r ≤ T.threshold / 32 := by
  obtain ⟨hσ, -⟩ := threshold_facts hD
  obtain ⟨hδ, -, -, -, -, -, -, hNpos, -⟩ := hD.chain
  have hN := hNpos 0
  rw [div_le_iff₀ hδ] at hr
  set x := T.δ₁ * ((r : ℝ) / 2) with hx
  have hx1 : 36 * T.N 0 ≤ x := by
    rw [hx]
    nlinarith
  have h1 : Real.exp (-x) * (x + 1) ≤ 1 := by
    have h2 := Real.add_one_le_exp x
    have h3 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-x)).le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h3
  have hE := Real.exp_pos (-x)
  have h4 : 36 * T.N 0 * Real.exp (-x) ≤ 1 := by nlinarith
  unfold closeness
  rw [← hx]
  nlinarith
private theorem exists_decay_const (tl : Inputs) (hD : T.Admissible) (hT : MatchesStepParameters T c) {CS κ M C₁ C₂ Ch : ℝ}
    (hNum : ParameterConstants T c CS κ M C₁ C₂) (hMn : ContourAgreementAt T.side c) (hCh0 : 0 ≤ Ch)
    (hCh : ∀ u v : imaginaryQuaternions, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → |haarLogRatio u - haarLogRatio v| ≤ Ch * ‖u - v‖)
    (hB : haarLogRatioBoundStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell)
      (Y' : F'.Cell) (r : ℕ), AgreeingTops T V V' Y Y' r →
      |stepDensity T.coupling T.ρA T.lam Y V - stepDensity T.coupling T.ρA T.lam Y' V'| ≤
        C * Real.exp (-(κ / 64 * r)) := by
  obtain ⟨hσ, -⟩ := threshold_facts hD
  obtain ⟨hδ, -, hlam, -, -, -, -, hNpos, -⟩ := hD.chain
  have hN0 := hNpos 0
  have hk0 := hNum.κ_pos
  have hκδ := hNum.κ_le
  have hM0 := hNum.M_nonneg
  have hC₁ := hNum.C₁_nonneg
  have hC₂ := hNum.C₂_nonneg
  have hCS0 := hNum.CS_nonneg
  obtain ⟨S, hS0, hSle⟩ : ∃ S : ℝ, 0 ≤ S ∧ ∀ r, shareError T CS κ M C₁ C₂ r ≤ S * Real.exp (-(κ / 64 * r)) := by
    have hA : 0 ≤ inverseConst T := by
      unfold inverseConst
      positivity
    have hB' : 0 ≤ opConst T CS := by
      unfold opConst
      positivity
    have hK : 0 ≤ sumConst T M := by
      unfold sumConst
      positivity
    have hE0 : 0 ≤ C₁ * Real.exp κ + C₂ * (T.N 0 * (9 / 8 * T.threshold)) *
        (4 * ((centredCube T.side).card : ℝ) * M) := by positivity
    exact ⟨_, by positivity, fun r => shareError_le hD hCS0 hk0 hκδ hM0 hC₁ hC₂ r rfl⟩
  obtain ⟨g₀, hg0, hgle⟩ : ∃ g₀ : ℝ, 0 ≤ g₀ ∧ ∀ r : ℕ, closeness T r ≤ g₀ * Real.exp (-(κ / 64 * r)) :=
    ⟨_, by positivity, closeness_le hD hk0 hκδ⟩
  obtain ⟨Q, hQ0, hQ⟩ : ∃ Q : ℝ, 0 ≤ Q ∧ Q = 4 * ((centredCube T.side).card : ℝ) * M := ⟨_, by positivity, rfl⟩
  have hL0 : (0 : ℝ) ≤ T.side := Nat.cast_nonneg _
  obtain ⟨Cb, hCb0, hCb⟩ : ∃ Cb : ℝ, 0 ≤ Cb ∧
      Cb = 1 / 2 * S + 3 / 2 * (4 * (10 * (T.side : ℝ) * g₀)) + Ch * g₀ * Q :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℕ, R₀ = ⌈72 * T.N 0 / T.δ₁⌉₊ + 2 := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀0, hB₀⟩ : ∃ B₀ : ℝ, 0 ≤ B₀ ∧ B₀ = densityBound T CS M := by
    refine ⟨_, ?_, rfl⟩
    have hA : 0 ≤ inverseConst T := by
      unfold inverseConst
      positivity
    have hB' : 0 ≤ opConst T CS := by
      unfold opConst
      positivity
    have hK : 0 ≤ sumConst T M := by
      unfold sumConst
      positivity
    unfold densityBound
    positivity
  obtain ⟨e₀, he₀0, he₀⟩ : ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ = Real.exp (κ / 64 * R₀) := ⟨_, Real.exp_pos _, rfl⟩
  refine ⟨Cb + 2 * B₀ * e₀ + 1, by positivity, fun F F' V V' Y Y' r P => ?_⟩
  obtain ⟨X, hX0, hX⟩ : ∃ X : ℝ, 0 < X ∧ X = Real.exp (-(κ / 64 * r)) := ⟨_, Real.exp_pos _, rfl⟩
  rw [← hX]
  by_cases hr : R₀ ≤ r
  · have hr2 : 2 ≤ r := by omega
    have hgs : 72 * T.N 0 / T.δ₁ ≤ r := by
      have h1 := Nat.le_ceil (72 * T.N 0 / T.δ₁)
      have h2 : ((⌈72 * T.N 0 / T.δ₁⌉₊ : ℕ) : ℝ) ≤ r := by
        have : ⌈72 * T.N 0 / T.δ₁⌉₊ ≤ r := by omega
        exact_mod_cast this
      exact h1.trans h2
    have h1 := abs_stepDensity_sub_le tl hD hT hNum hMn hCh0 hCh P hr2 (closeness_le_threshold hD hgs)
    have h2 := hSle r
    have h3 := hgle r
    rw [← hX] at h2 h3
    rw [← hQ] at h1
    have a1 : 3 / 2 * (4 * (10 * (T.side : ℝ) * closeness T r)) ≤ 3 / 2 * (4 * (10 * (T.side : ℝ) * (g₀ * X))) := by
      gcongr
    have a2 : Ch * closeness T r * Q ≤ Ch * (g₀ * X) * Q := by gcongr
    have e : (Cb + 2 * B₀ * e₀ + 1) * X = 1 / 2 * (S * X) + 3 / 2 * (4 * (10 * (T.side : ℝ) * (g₀ * X))) +
        Ch * (g₀ * X) * Q + 2 * B₀ * e₀ * X + X := by
      rw [hCb]
      ring
    have a3 : 0 ≤ 2 * B₀ * e₀ * X := by positivity
    rw [e]
    linarith
  · have hr' : (r : ℝ) ≤ R₀ := by
      have : r ≤ R₀ := by omega
      exact_mod_cast this
    have h1 := abs_stepDensity_le tl hD hT hB hNum P.torus P.cold Y
    have h2 := abs_stepDensity_le tl hD hT hB hNum P.torus' P.cold' Y'
    rw [← hB₀] at h1 h2
    have h3 : 1 ≤ e₀ * X := by
      rw [hX, he₀, ← Real.exp_add]
      apply Real.one_le_exp
      have : κ / 64 * (r : ℝ) ≤ κ / 64 * R₀ := by gcongr
      linarith
    have h4 := abs_sub (stepDensity T.coupling T.ρA T.lam Y V) (stepDensity T.coupling T.ρA T.lam Y' V')
    have h5 : 2 * B₀ * 1 ≤ 2 * B₀ * (e₀ * X) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have e : (Cb + 2 * B₀ * e₀ + 1) * X = Cb * X + 2 * B₀ * (e₀ * X) + X := by ring
    have a3 : 0 ≤ Cb * X := by positivity
    rw [e]
    linarith
end Final
end StepDensityLocality
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters TorusComparison Estimates ChartResponse
  SecondOrderMoves ChartLipschitz
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters TorusComparison Estimates ChartResponse
  SecondOrderMoves ChartLipschitz
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters TorusComparison Estimates ChartResponse
  SecondOrderMoves ChartLipschitz
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters TorusComparison Estimates ChartResponse
  SecondOrderMoves ChartLipschitz
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity RenormalizationStepParameters TorusComparison Estimates ChartResponse
  SecondOrderMoves ChartLipschitz
open StepDensityLocality in
theorem stepDensityLocality (hI : ChartHessianInverseDecay)
    (hCl : AdmissibleParametersExist) (hEn : ChartEnergyDerivBounds)
    (hEnt : HessianEntryAgreeOnTwoTori) (hMv : HessianEntryLipschitz) (hCh : SharesAndContoursAgreeOnTwoTori)
    (hcov : BlocksCoverLowerLevel) (hOL : MinimizingChartUnique) (hLC : ImaginaryCoordinatesIsometric)
    (hShort : ChartedFieldLipschitz) (hDist : cellOffsetStatement) (hSites : SiteDecomposition)
    (hGlue : TwoChartsGlue) (hPairs : bondsNearCellsPairStatement)
    (hCont : ChartedFieldContourBound) (hH : HaarLogRatioNearZero) (hB : haarLogRatioBoundStatement) :
    stepDensityLocalityStatement := by
  obtain ⟨CS, κ, hCS, hκ, hall⟩ := hI
  have tl : Inputs := ⟨hcov, hOL, hLC, hShort, hDist, hSites, hGlue, hPairs, hCont⟩
  refine ⟨fun l => κ l / 64, fun l => by have := hκ l; positivity, fun T hD => ?_⟩
  obtain ⟨hκδ, hInv⟩ := hall T hD
  obtain ⟨c, eδ, -, elam, eρ, eσ, -, eN, hHo⟩ :=
    hCl T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N hD.a_ge hD.L_odd hD.chain
  have hT : MatchesStepParameters T c := ⟨eδ, elam, eρ, eσ, eN, hHo⟩
  obtain ⟨hσ, -⟩ := threshold_facts hD
  obtain ⟨C₁, hC₁, hE⟩ := hEnt T.coupling T.side c hD.a_ge hD.L_odd hD.L_ge hHo (T.threshold / 64) (by positivity)
  obtain ⟨C₂, hC₂, hMv'⟩ := hMv T.coupling T.side c hD.a_ge hD.L_odd hD.L_ge hHo
  obtain ⟨C₃, -, hC3⟩ := hCh T.coupling T.side c hD.a_ge hD.L_odd hD.L_ge hHo
  obtain ⟨Ce, -, hen⟩ := hEn T.coupling T.side c hD.a_ge hD.L_odd hD.L_ge hHo
  obtain ⟨M, hM0, hMs⟩ := CellSums.exists_bound_sum_exp_cellSupDist (κ T.toChainParameters) (hκ _)
  obtain ⟨Ch, hCh0, hChL⟩ := haarLogRatio_lipschitz hH
  have hSm : EnergySmoothAt T.coupling T.side c := fun F w V hF hs => by
    have hz := hLC.2.2.2.2.2.1 F w
    refine (hen F w 0 V hF ?_).1
    rw [hz]
    exact hs
  have hMn : ContourAgreementAt T.side c := fun F F' w w' V V' Y Y' r h1 h2 h3 h4 h5 h6 h7 h8 =>
    (hC3 F F' w w' V V' Y Y' r h1 h2 h3 h4 h5 h6 h7 h8).2
  have hNum : ParameterConstants T c (CS T.toChainParameters) (κ T.toChainParameters) M C₁ C₂ :=
    ⟨(hCS _).le, hκ _, hκδ, hInv, hMs, hM0, hC₁.le, hC₂.le, hE, hMv', hSm⟩
  obtain ⟨C, hC, hfin⟩ := exists_decay_const tl hD hT hNum hMn hCh0 hChL hB
  refine ⟨C, hC, fun t n n' hn hn' Y Y' V V' r hV hV' hag => ?_⟩
  exact hfin _ _ V V' Y Y' r ⟨⟨rfl, n, hn, fun _ => rfl⟩, ⟨rfl, n', hn', fun _ => rfl⟩, rfl, hV, hV', hag⟩
end YangMills.Construction.RunningCouplingSlope
end
