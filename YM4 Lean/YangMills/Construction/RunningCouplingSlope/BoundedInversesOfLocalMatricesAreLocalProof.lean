import YangMills.Construction.LinearAlgebra.ExponentialDecayOfInverseBySchurTest
import YangMills.Construction.RunningCouplingSlope.BoundedInversesOfLocalMatricesAreLocal
import YangMills.Construction.RunningCouplingSlope.MixedDerivativeByCellsProof
import YangMills.Construction.RunningCouplingSlope.TheOrbitMapReadsNearCellsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
section Vectors
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
private def euclidNorm (x : ι → ℂ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖
private theorem euclidNorm_nonneg (x : ι → ℂ) : 0 ≤ euclidNorm x := norm_nonneg _
private theorem euclidNorm_sq (x : ι → ℂ) : euclidNorm x ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  unfold euclidNorm
  rw [EuclideanSpace.norm_sq_eq]
private theorem euclidNorm_add_le (x y : ι → ℂ) : euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by
  unfold euclidNorm
  rw [WithLp.toLp_add]
  exact norm_add_le _ _
private theorem euclidNorm_zero : euclidNorm (0 : ι → ℂ) = 0 := by
  have h := euclidNorm_sq (0 : ι → ℂ)
  simpa using h
private theorem euclidNorm_sum_le {Y : Type} (s : Finset Y) (f : Y → ι → ℂ) :
    euclidNorm (∑ y ∈ s, f y) ≤ ∑ y ∈ s, euclidNorm (f y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [euclidNorm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (euclidNorm_add_le _ _).trans (by linarith)
variable [DecidableEq ι]
private theorem euclidNorm_mulVec_le (A : Matrix ι' ι ℂ) (x : ι → ℂ) :
    euclidNorm (A.mulVec x) ≤ ‖A‖ * euclidNorm x :=
  Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
private theorem opNorm_le_of_euclidNorm (A : Matrix ι' ι ℂ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x, euclidNorm (A.mulVec x) ≤ K * euclidNorm x) : ‖A‖ ≤ K := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  exact h x.ofLp
end Vectors
section Blocks
variable {Y ι ι' : Type} [Fintype Y] [Fintype ι] [Fintype ι']
open Classical in
private def cellPart (c : ι → Y) (y : Y) (x : ι → ℂ) : ι → ℂ := fun i => if c i = y then x i else 0
private theorem sum_sq_euclidNorm_cellPart (c : ι → Y) (x : ι → ℂ) :
    ∑ y, euclidNorm (cellPart c y x) ^ 2 = euclidNorm x ^ 2 := by
  classical
  simp only [euclidNorm_sq, cellPart]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (c i)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp
private theorem euclidNorm_cellPart_le (c : ι → Y) (y : Y) (x : ι → ℂ) :
    euclidNorm (cellPart c y x) ≤ euclidNorm x := by
  classical
  refine (sq_le_sq₀ (euclidNorm_nonneg _) (euclidNorm_nonneg _)).1 ?_
  simp only [euclidNorm_sq, cellPart]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · exact le_rfl
  · simp
private theorem cellPart_mulVec (c : ι → Y) (c' : ι' → Y) (A : Matrix ι' ι ℂ) (x : ι → ℂ) (y' : Y) :
    cellPart c' y' (A.mulVec x) = ∑ y, (blockBetween c c' A y' y).mulVec (cellPart c y x) := by
  classical
  funext p
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, cellPart, blockBetween]
  rw [Finset.sum_comm]
  by_cases hp : c' p = y'
  · simp only [hp, if_true, true_and]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single (c q)]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  · simp [hp]
private theorem blockBetween_mulVec (c : ι → Y) (c' : ι' → Y) (A : Matrix ι' ι ℂ) (x : ι → ℂ)
    (y' y : Y) :
    (blockBetween c c' A y' y).mulVec x = cellPart c' y' (A.mulVec (cellPart c y x)) := by
  classical
  funext p
  simp only [Matrix.mulVec, dotProduct, cellPart, blockBetween]
  by_cases hp : c' p = y'
  · simp only [hp, if_true, true_and]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  · simp [hp]
variable [DecidableEq ι]
private theorem norm_blockBetween_le (c : ι → Y) (c' : ι' → Y) (A : Matrix ι' ι ℂ) (y' y : Y) :
    ‖blockBetween c c' A y' y‖ ≤ ‖A‖ := by
  refine opNorm_le_of_euclidNorm _ (norm_nonneg _) fun x => ?_
  rw [blockBetween_mulVec]
  calc euclidNorm (cellPart c' y' (A.mulVec (cellPart c y x)))
        ≤ euclidNorm (A.mulVec (cellPart c y x)) := euclidNorm_cellPart_le _ _ _
    _ ≤ ‖A‖ * euclidNorm (cellPart c y x) := euclidNorm_mulVec_le _ _
    _ ≤ ‖A‖ * euclidNorm x := mul_le_mul_of_nonneg_left (euclidNorm_cellPart_le _ _ _) (norm_nonneg _)
private theorem schur_test (c : ι → Y) (c' : ι' → Y) (A : Matrix ι' ι ℂ) (b : Y → Y → ℝ)
    (hb0 : ∀ y' y, 0 ≤ b y' y) (hb : ∀ y' y, ‖blockBetween c c' A y' y‖ ≤ b y' y) {R : ℝ}
    (hR : 0 ≤ R) (hrow : ∀ y', ∑ y, b y' y ≤ R) (hcol : ∀ y, ∑ y', b y' y ≤ R) : ‖A‖ ≤ R := by
  refine opNorm_le_of_euclidNorm _ hR fun x => ?_
  obtain ⟨u, hu⟩ : ∃ u : Y → ℝ, u = fun y => euclidNorm (cellPart c y x) := ⟨_, rfl⟩
  have hu0 : ∀ y, 0 ≤ u y := fun y => by rw [hu]; exact euclidNorm_nonneg _
  have hv : ∀ y', euclidNorm (cellPart c' y' (A.mulVec x)) ≤ ∑ y, b y' y * u y := by
    intro y'
    rw [cellPart_mulVec c]
    refine (euclidNorm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    refine (euclidNorm_mulVec_le _ _).trans ?_
    rw [hu]
    exact mul_le_mul_of_nonneg_right (hb y' y) (euclidNorm_nonneg _)
  have hcs : ∀ y', (∑ y, b y' y * u y) ^ 2 ≤ R * ∑ y, b y' y * u y ^ 2 := by
    intro y'
    have h1 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset Y)
      (r := fun y => b y' y * u y) (f := fun y => b y' y) (g := fun y => b y' y * u y ^ 2)
      (fun y _ => hb0 _ _) (fun y _ => mul_nonneg (hb0 _ _) (sq_nonneg _))
      (fun y _ => le_of_eq (by ring))
    exact h1.trans (mul_le_mul_of_nonneg_right (hrow y')
      (Finset.sum_nonneg fun y _ => mul_nonneg (hb0 _ _) (sq_nonneg _)))
  have hmain : euclidNorm (A.mulVec x) ^ 2 ≤ (R * euclidNorm x) ^ 2 := by
    calc euclidNorm (A.mulVec x) ^ 2 = ∑ y', euclidNorm (cellPart c' y' (A.mulVec x)) ^ 2 :=
          (sum_sq_euclidNorm_cellPart c' _).symm
      _ ≤ ∑ y', (∑ y, b y' y * u y) ^ 2 :=
          Finset.sum_le_sum fun y' _ => pow_le_pow_left₀ (euclidNorm_nonneg _) (hv y') 2
      _ ≤ ∑ y', R * ∑ y, b y' y * u y ^ 2 := Finset.sum_le_sum fun y' _ => hcs y'
      _ = R * ∑ y, (∑ y', b y' y) * u y ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ R * ∑ y, R * u y ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hR
          exact mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _)
      _ = (R * euclidNorm x) ^ 2 := by
          rw [← Finset.mul_sum, hu, sum_sq_euclidNorm_cellPart]
          ring
  exact (sq_le_sq₀ (euclidNorm_nonneg _) (mul_nonneg hR (euclidNorm_nonneg _))).1 hmain
end Blocks
private theorem abs_exp_sub_one_le_mul_exp (t : ℝ) : |Real.exp t - 1| ≤ |t| * Real.exp |t| := by apply _root_.YangMills.Construction.LinearAlgebra.DecayingInverse.abs_exp_sub_one_le_abs_mul_exp_abs <;> assumption
private theorem weighted_exp_sub_one_le {t β θ x : ℝ} (hθ : 0 < θ) (hβ0 : 0 ≤ β) (hβ : β ≤ θ / 4)
    (hx : 0 ≤ x) (ht : |t| ≤ β * x) :
    |Real.exp t - 1| * Real.exp (-(θ * x)) ≤ β * (4 / θ) * Real.exp (-(θ / 2 * x)) := by
  have h1 : x ≤ 4 / θ * Real.exp (θ / 4 * x) := by
    have h := Real.add_one_le_exp (θ / 4 * x)
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
    nlinarith
  have h2 : Real.exp |t| ≤ Real.exp (θ / 4 * x) :=
    Real.exp_le_exp.2 (ht.trans (mul_le_mul_of_nonneg_right hβ hx))
  have h3 : |Real.exp t - 1| ≤ β * x * Real.exp (θ / 4 * x) :=
    (abs_exp_sub_one_le_mul_exp t).trans
      (mul_le_mul ht h2 (Real.exp_pos _).le (mul_nonneg hβ0 hx))
  have h4 : β * x ≤ β * (4 / θ * Real.exp (θ / 4 * x)) := mul_le_mul_of_nonneg_left h1 hβ0
  have e : Real.exp (θ / 4 * x) * Real.exp (θ / 4 * x) * Real.exp (-(θ * x)) =
      Real.exp (-(θ / 2 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc |Real.exp t - 1| * Real.exp (-(θ * x))
      ≤ β * (4 / θ * Real.exp (θ / 4 * x)) * Real.exp (θ / 4 * x) * Real.exp (-(θ * x)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact h3.trans (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le)
    _ = β * (4 / θ) * (Real.exp (θ / 4 * x) * Real.exp (θ / 4 * x) * Real.exp (-(θ * x))) := by
        ring
    _ = β * (4 / θ) * Real.exp (-(θ / 2 * x)) := by rw [e]
section Inverse
variable {Y ι : Type} [Fintype Y] [Fintype ι] [DecidableEq ι]
private def inverseDecayRate (M θ K S : ℝ) : ℝ := min (θ / 4) (θ / (8 * M * S * K))
private theorem norm_blockBetween_inv_le (d : Y → Y → ℝ) (hd0 : ∀ a b, 0 ≤ d a b)
    (hself : ∀ a, d a a = 0) (hsym : ∀ a b, d a b = d b a)
    (htri : ∀ a b c, d a c ≤ d a b + d b c) (c : ι → Y)
    (T : Matrix ι ι ℂ) {M θ K S : ℝ} (hM : 0 < M) (hθ : 0 < θ) (hK : 0 < K) (hS0 : 0 < S)
    (hS : ∀ y', ∑ y, Real.exp (-(θ / 2 * d y' y)) ≤ S)
    (hT : ∀ y' y, ‖blockBetween c c T y' y‖ ≤ M * Real.exp (-(θ * d y' y)))
    (hu : IsUnit (Matrix.det T)) (hinv : ‖T⁻¹‖ ≤ K) (y' y₀ : Y) :
    ‖blockBetween c c T⁻¹ y' y₀‖ ≤ 2 * K * Real.exp (-(inverseDecayRate M θ K S * d y' y₀)) := by
  classical
  obtain ⟨β, hβ⟩ : ∃ β, β = inverseDecayRate M θ K S := ⟨_, rfl⟩
  rw [← hβ]
  have hβ0 : 0 < β := by
    rw [hβ]
    exact lt_min (by positivity) (by positivity)
  have hβ1 : β ≤ θ / 4 := by rw [hβ]; exact min_le_left _ _
  have hβ2 : β ≤ θ / (8 * M * S * K) := by rw [hβ]; exact min_le_right _ _
  obtain ⟨w, hw⟩ : ∃ w : Y → ℝ, w = fun y => Real.exp (β * d y y₀) := ⟨_, rfl⟩
  have hw0 : ∀ y, w y ≠ 0 := fun y => by rw [hw]; exact (Real.exp_pos _).ne'
  obtain ⟨D, hD⟩ : ∃ D : Matrix ι ι ℂ, D = Matrix.diagonal fun i => (w (c i) : ℂ) := ⟨_, rfl⟩
  obtain ⟨Di, hDi⟩ : ∃ Di : Matrix ι ι ℂ, Di = Matrix.diagonal fun i => ((w (c i))⁻¹ : ℂ) :=
    ⟨_, rfl⟩
  have hDD : D * Di = 1 := by
    rw [hD, hDi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (by exact_mod_cast hw0 _)
  have hDD' : Di * D = 1 := by
    rw [hD, hDi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (by exact_mod_cast hw0 _)
  have hTi : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hu
  have hiT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hu
  obtain ⟨Tw, hTw⟩ : ∃ Tw, Tw = D * T * Di := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = D * T⁻¹ * Di := ⟨_, rfl⟩
  have hTB : Tw * B = 1 := by
    rw [hTw, hB]
    calc D * T * Di * (D * T⁻¹ * Di) = D * (T * ((Di * D) * T⁻¹)) * Di := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDD', Matrix.one_mul, hTi, Matrix.mul_one, hDD]
  have entry : ∀ (A : Matrix ι ι ℂ) p q, (D * A * Di) p q =
      ((w (c p) / w (c q) : ℝ) : ℂ) * A p q := by
    intro A p q
    rw [hD, hDi, Matrix.mul_diagonal, Matrix.diagonal_mul]
    push_cast
    ring
  have blockD : ∀ (A : Matrix ι ι ℂ) a b, blockBetween c c (D * A * Di) a b =
      ((w a / w b : ℝ) : ℂ) • blockBetween c c A a b := by
    intro A a b
    ext p q
    simp only [blockBetween, Matrix.smul_apply, smul_eq_mul, entry]
    split_ifs with h
    · rw [h.1, h.2]
    · simp
  have hA : ‖Tw - T‖ ≤ 1 / (2 * K) := by
    have hbound : ∀ a b, |w a / w b - 1| * (M * Real.exp (-(θ * d a b))) ≤
        M * (β * (4 / θ)) * Real.exp (-(θ / 2 * d a b)) := by
      intro a b
      have hq : w a / w b = Real.exp (β * d a y₀ - β * d b y₀) := by
        rw [hw, Real.exp_sub]
      have ht : |β * d a y₀ - β * d b y₀| ≤ β * d a b := by
        rw [← mul_sub, abs_mul, abs_of_pos hβ0]
        refine mul_le_mul_of_nonneg_left ?_ hβ0.le
        rw [abs_le]
        constructor
        · have := htri b a y₀
          rw [hsym b a] at this
          linarith
        · have := htri a b y₀
          linarith
      have := weighted_exp_sub_one_le hθ hβ0.le hβ1 (hd0 a b) ht
      rw [hq]
      calc |Real.exp (β * d a y₀ - β * d b y₀) - 1| * (M * Real.exp (-(θ * d a b)))
          = M * (|Real.exp (β * d a y₀ - β * d b y₀) - 1| * Real.exp (-(θ * d a b))) := by ring
        _ ≤ M * (β * (4 / θ) * Real.exp (-(θ / 2 * d a b))) :=
            mul_le_mul_of_nonneg_left this hM.le
        _ = _ := by ring
    have hsmall : M * (β * (4 / θ)) * S ≤ 1 / (2 * K) := by
      have h1 : β * (8 * M * S * K) ≤ θ := by
        have hpos : 0 < 8 * M * S * K := by positivity
        exact (le_div_iff₀ hpos).1 hβ2
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)]
      have e : M * (β * (4 / θ)) * S * (2 * K) = β * (8 * M * S * K) / θ := by
        field_simp
        ring
      rw [e, div_le_one hθ]
      exact h1
    refine schur_test c c (Tw - T)
      (fun a b => M * (β * (4 / θ)) * Real.exp (-(θ / 2 * d a b)))
      (fun a b => by positivity) (fun a b => ?_) (by positivity) (fun a => ?_) (fun b => ?_)
    · have hsplit : blockBetween c c (Tw - T) a b =
          (((w a / w b - 1 : ℝ)) : ℂ) • blockBetween c c T a b := by
        have h0 : blockBetween c c (Tw - T) a b =
            blockBetween c c Tw a b - blockBetween c c T a b := by
          ext p q
          simp only [blockBetween, Matrix.sub_apply]
          split_ifs <;> simp
        rw [h0, hTw, blockD]
        push_cast
        rw [sub_smul, one_smul]
      rw [hsplit, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hT a b) (abs_nonneg _)).trans (hbound a b)
    · rw [← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left (hS a) (by positivity)).trans hsmall
    · have : ∑ y', M * (β * (4 / θ)) * Real.exp (-(θ / 2 * d y' b)) =
          M * (β * (4 / θ)) * ∑ y', Real.exp (-(θ / 2 * d b y')) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y' _ => by rw [hsym y' b]
      rw [this]
      exact (mul_le_mul_of_nonneg_left (hS b) (by positivity)).trans hsmall
  have hBeq : B = T⁻¹ - T⁻¹ * ((Tw - T) * B) := by
    have h1 : (Tw - T) * B = 1 - T * B := by
      rw [Matrix.sub_mul, hTB]
    rw [h1, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hiT, Matrix.one_mul]
    abel
  have hBn : ‖B‖ ≤ 2 * K := by
    have h1 : ‖B‖ ≤ K + K * (1 / (2 * K) * ‖B‖) := by
      calc ‖B‖ = ‖T⁻¹ - T⁻¹ * ((Tw - T) * B)‖ := by rw [← hBeq]
        _ ≤ ‖T⁻¹‖ + ‖T⁻¹ * ((Tw - T) * B)‖ := norm_sub_le _ _
        _ ≤ ‖T⁻¹‖ + ‖T⁻¹‖ * (‖Tw - T‖ * ‖B‖) := by
            gcongr
            exact (Matrix.l2_opNorm_mul _ _).trans
              (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
        _ ≤ K + K * (1 / (2 * K) * ‖B‖) := by
            gcongr
    have h2 : K * (1 / (2 * K) * ‖B‖) = ‖B‖ / 2 := by
      field_simp
    linarith
  have hblock : blockBetween c c B y' y₀ =
      ((Real.exp (β * d y' y₀) : ℝ) : ℂ) • blockBetween c c T⁻¹ y' y₀ := by
    rw [hB, blockD]
    have : w y' / w y₀ = Real.exp (β * d y' y₀) := by
      rw [hw]
      simp [hself]
    rw [this]
  have h3 : Real.exp (β * d y' y₀) * ‖blockBetween c c T⁻¹ y' y₀‖ ≤ 2 * K := by
    have h := (norm_blockBetween_le c c B y' y₀).trans hBn
    rw [hblock, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    exact h
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  linarith
end Inverse
section Distance
variable {L n k : ℕ}
private theorem cellDist_nonneg (y y' : Tower.Vertex L n k k) : 0 ≤ cellDist y y' := by apply _root_.YangMills.SharedProofs.p2231 <;> assumption
private theorem cellDist_self (y : Tower.Vertex L n k k) : cellDist y y = 0 := by apply _root_.YangMills.SharedProofs.p28613 <;> assumption
private theorem cellDist_comm (y y' : Tower.Vertex L n k k) : cellDist y y' = cellDist y' y := by apply _root_.YangMills.SharedProofs.p19196 <;> assumption
private theorem cellDist_triangle (a b c : Tower.Vertex L n k k) :
    cellDist a c ≤ cellDist a b + cellDist b c := by apply _root_.YangMills.SharedProofs.p82152 <;> assumption
private theorem exists_injective_supDist_le [NeZero (2 * L ^ n)] :
    ∃ φ : Tower.Vertex L n k k → TorusFields.TorusSite (2 * L ^ n), Function.Injective φ ∧
      ∀ y y', (TorusFields.supDist (φ y) (φ y') : ℝ) ≤ cellDist y y' := by apply _root_.YangMills.SharedProofs.p77197 <;> assumption
private theorem exists_fintype_sum_exp_le (hL : 0 < L) {r S : ℝ} (hr : 0 < r)
    (hS : ∀ (N : ℕ) [NeZero N] (y : TorusFields.TorusSite N),
      ∑ x : TorusFields.TorusSite N, Real.exp (-(r * TorusFields.supDist y x)) ≤ S) :
    ∃ _ : Fintype (Tower.Vertex L n k k), ∀ y' : Tower.Vertex L n k k,
      ∑ y, Real.exp (-(r * cellDist y' y)) ≤ S := by
  classical
  have : NeZero (2 * L ^ n) := ⟨by positivity⟩
  obtain ⟨φ, hinj, hle⟩ := exists_injective_supDist_le (L := L) (n := n) (k := k)
  refine ⟨Fintype.ofInjective φ hinj, fun y' => ?_⟩
  letI : Fintype (Tower.Vertex L n k k) := Fintype.ofInjective φ hinj
  obtain ⟨g, hg⟩ : ∃ g : TorusFields.TorusSite (2 * L ^ n) → ℝ,
      g = fun x => Real.exp (-(r * TorusFields.supDist (φ y') x)) := ⟨_, rfl⟩
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rw [hg]; exact (Real.exp_pos _).le
  calc ∑ y, Real.exp (-(r * cellDist y' y)) ≤ ∑ y, g (φ y) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [hg]
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left (hle y' y) hr.le
        linarith
    _ = ∑ x ∈ Finset.univ.image φ, g x := (Finset.sum_image fun a _ b _ h => hinj h).symm
    _ ≤ ∑ x, g x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun x _ _ => hg0 x
    _ ≤ S := by rw [hg]; exact hS _ _
end Distance
theorem localMatricesBoundedAndInverseLocal_of_expDecayTorusSum
    (hSum : SlopeCoefficient.ExpDecayTorusSumBounded) :
    LocalMatricesBoundedAndInverseLocal := by
  refine ⟨fun θ hθ => ?_, fun M θ K hM hθ hK => ?_⟩
  · obtain ⟨S, hS0, hS⟩ := hSum θ hθ
    refine ⟨S, hS0, ?_⟩
    intro L n k ι ι' _ _ _ c c' T M hL hn hM hloc
    have hL0 : 0 < L := by
      have := hL.2
      omega
    obtain ⟨_, hsum⟩ := exists_fintype_sum_exp_le (L := L) (n := n) (k := k) hL0 hθ hS
    refine schur_test c c' T (fun y' y => M * Real.exp (-(θ * cellDist y' y)))
      (fun _ _ => by positivity) (fun y' y => ?_) (by positivity) (fun y' => ?_) (fun y => ?_)
    · simpa using hloc y' y
    · rw [← Finset.mul_sum, mul_comm S M]
      exact mul_le_mul_of_nonneg_left (hsum y') hM
    · have : ∑ y', M * Real.exp (-(θ * cellDist y' y)) =
          M * ∑ y', Real.exp (-(θ * cellDist y y')) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y' _ => by rw [cellDist_comm y' y]
      rw [this, mul_comm S M]
      exact mul_le_mul_of_nonneg_left (hsum y) hM
  · obtain ⟨S, hS0, hS⟩ := hSum (θ / 2) (by positivity)
    refine ⟨2 * K, inverseDecayRate M θ K S, by positivity,
      lt_min (by positivity) (by positivity), ?_⟩
    intro L n k ι _ _ c T hL hn hloc hu hinv y' y
    have hL0 : 0 < L := by
      have := hL.2
      omega
    obtain ⟨_, hsum⟩ := exists_fintype_sum_exp_le (L := L) (n := n) (k := k) hL0 (half_pos hθ) hS
    have := norm_blockBetween_inv_le cellDist cellDist_nonneg cellDist_self cellDist_comm
      cellDist_triangle c T hM hθ hK hS0 hsum (fun a b => by simpa using hloc a b) hu hinv y' y
    simpa using this
end YangMills.Construction.RunningCouplingSlope
end
