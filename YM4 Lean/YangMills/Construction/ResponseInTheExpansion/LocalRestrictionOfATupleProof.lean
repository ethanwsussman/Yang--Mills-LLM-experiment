import YangMills.Construction.LawInAState.CovarianceBelowTheAveragesProof
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelow
import YangMills.Construction.ResponseInTheExpansion.LocalRestrictionOfATuple
import YangMills.Construction.ResponseInTheExpansion.MeansOfAWeight
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheCurvatureOfALevel
import YangMills.Construction.ResponseInTheExpansion.PairingsOfASum
import YangMills.Construction.ResponseInTheExpansion.TheFieldIsNearOneAlongTheChain
import YangMills.Construction.ResponseInTheExpansion.TheLocalEventIsLikely
import YangMills.Construction.ResponseInTheExpansion.TheMaxwellCovarianceAtLongDistance
import YangMills.Construction.ResponseInTheExpansion.TheResponseIsAQuadraticFormOfTheCurvature
import YangMills.Construction.ResponseInTheExpansion.TheWeightsOfATupleAreLocal
import YangMills.Construction.ResponseInTheExpansion.TheWindowHasATower
import YangMills.Construction.ResponseInTheExpansion.TracesOfTheKernelsAreTheLaw
import YangMills.Construction.ResponseInTheExpansion.TwoPointFunctionByTotalCovariance
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages WeightedResponses TorusFields TorusLumps RenormalizationStepParameters LinearResponse
open Classical
open MeasureTheory
section Restriction
variable {Y : Type} [Fintype Y]
private theorem sum_subtype_eq_of_zero (Box : Y → Prop) (f : Y → ℝ) (h : ∀ y, ¬ Box y → f y = 0) :
    ∑ a : {y // Box y}, f a.1 = ∑ y, f y := by
  have h1 : ∑ y ∈ Finset.univ.filter Box, f y = ∑ a : {y // Box y}, f a.1 :=
    Finset.sum_subtype _ (by simp) f
  rw [← h1]
  exact Finset.sum_subset (Finset.subset_univ _) fun y _ hy => h y (by simpa using hy)
private def boxInclusion (Box : Y → Prop) : Matrix Y {y // Box y} ℝ := fun y a => if y = a.1 then 1 else 0
private def boxProjection (Box : Y → Prop) : Matrix {y // Box y} Y ℝ := Matrix.transpose (boxInclusion Box)
private theorem boxInclusion_mul {X : Type} [Fintype X] (Box : Y → Prop) (a : Matrix {y // Box y} X ℝ) (y : Y) (b : X) :
    (boxInclusion Box * a) y b = if h : Box y then a ⟨y, h⟩ b else 0 := by
  simp only [Matrix.mul_apply, boxInclusion]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨y, h⟩]
    · simp
    · intro c _ hc
      have : y ≠ c.1 := fun e => hc (Subtype.ext e.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    have : y ≠ c.1 := fun e => h (e ▸ c.2)
    simp [this]
private theorem mul_boxProjection {X : Type} [Fintype X] (Box : Y → Prop) (a : Matrix X {y // Box y} ℝ) (y : X) (y' : Y) :
    (a * boxProjection Box) y y' = if h : Box y' then a y ⟨y', h⟩ else 0 := by
  simp only [Matrix.mul_apply, boxProjection, boxInclusion, Matrix.transpose_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨y', h⟩]
    · simp
    · intro c _ hc
      have : y' ≠ c.1 := fun e => hc (Subtype.ext e.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    have : y' ≠ c.1 := fun e => h (e ▸ c.2)
    simp [this]
private theorem boxProjection_mul {X : Type} [Fintype X] (Box : Y → Prop) (N : Matrix Y X ℝ) (a : {y // Box y}) (b : X) :
    (boxProjection Box * N) a b = N a.1 b := by
  simp only [Matrix.mul_apply, boxProjection, boxInclusion, Matrix.transpose_apply]
  rw [Finset.sum_eq_single a.1]
  · simp
  · intro c _ hc
    simp [hc]
  · simp
private theorem mul_boxInclusion {X : Type} [Fintype X] [DecidableEq X] (Box : Y → Prop) (N : Matrix X Y ℝ) (a : X) (b : {y // Box y}) :
    (N * boxInclusion Box) a b = N a b.1 := by
  simp only [Matrix.mul_apply, boxInclusion]
  rw [Finset.sum_eq_single b.1]
  · simp
  · intro c _ hc
    simp [hc]
  · simp
private theorem eq_conj_submatrix_of_support (Box : Y → Prop) (K : Matrix Y Y ℝ) (hK : ∀ a b, K a b ≠ 0 → Box a ∧ Box b) :
    K = boxInclusion Box * (K.submatrix (Subtype.val : {y // Box y} → Y) Subtype.val) * boxProjection Box := by
  ext a b
  refine Eq.trans ?_ (mul_boxProjection Box (boxInclusion Box * (K.submatrix (Subtype.val : {y // Box y} → Y) Subtype.val)) a b).symm
  by_cases hb : Box b
  · rw [dif_pos hb, boxInclusion_mul]
    by_cases ha : Box a
    · rw [dif_pos ha]
      rfl
    · rw [dif_neg ha]
      by_contra h0
      exact ha (hK a b h0).1
  · rw [dif_neg hb]
    by_contra h0
    exact hb (hK a b h0).2
private theorem prod_map_mul_boxInclusion (Box : Y → Prop) (R : Matrix {y // Box y} Y ℝ) (l : List (Matrix {y // Box y} {y // Box y} ℝ)) :
    (l.map fun a => boxInclusion Box * a * R).prod * boxInclusion Box = boxInclusion Box * (l.map fun a => a * R * boxInclusion Box).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [Matrix.mul_assoc, ih]
    simp only [Matrix.mul_assoc]
private theorem trace_prod_map_conj (Box : Y → Prop) (R : Matrix {y // Box y} Y ℝ) (a : Matrix {y // Box y} {y // Box y} ℝ)
    (l : List (Matrix {y // Box y} {y // Box y} ℝ)) :
    Matrix.trace (((a :: l).map fun a => boxInclusion Box * a * R).prod) =
      Matrix.trace (((a :: l).map fun a => a * R * boxInclusion Box).prod) := by
  simp only [List.map_cons, List.prod_cons]
  rw [Matrix.mul_assoc (boxInclusion Box) a R, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, prod_map_mul_boxInclusion]
  simp only [Matrix.mul_assoc]
private theorem cyclicTraceSum_submatrix (Box : Y → Prop) {q : ℕ} (K : Fin (q + 1) → Matrix Y Y ℝ) (T : Matrix Y Y ℝ)
    (hK : ∀ i a b, K i a b ≠ 0 → Box a ∧ Box b) :
    cyclicTraceSum (fun i => (K i).submatrix (Subtype.val : {y // Box y} → Y) Subtype.val)
      (T.submatrix (Subtype.val : {y // Box y} → Y) Subtype.val) = cyclicTraceSum K T := by
  unfold cyclicTraceSum
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold kernelCycleTrace
  set R := boxProjection Box * T with hR
  set κ : Fin (q + 1) → Matrix {y // Box y} {y // Box y} ℝ := fun i => (K i).submatrix Subtype.val Subtype.val with hκ
  have hT : T.submatrix (Subtype.val : {y // Box y} → Y) Subtype.val = R * boxInclusion Box := by
    ext a b
    rw [mul_boxInclusion, hR, boxProjection_mul]
    rfl
  have e1 : (List.ofFn fun i : Fin (q + 1) => κ (s i) * T.submatrix (Subtype.val : {y // Box y} → Y) Subtype.val) =
      (List.ofFn fun i : Fin (q + 1) => κ (s i)).map fun a => a * R * boxInclusion Box := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp, hT, Matrix.mul_assoc]
  have e2 : (List.ofFn fun i : Fin (q + 1) => K (s i) * T) =
      (List.ofFn fun i : Fin (q + 1) => κ (s i)).map fun a => boxInclusion Box * a * R := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp]
    have := eq_conj_submatrix_of_support Box (K (s i)) (hK (s i))
    conv_lhs => rw [this]
    rw [hR]
    exact Matrix.mul_assoc _ _ _
  rw [e1, e2, List.ofFn_succ]
  convert (trace_prod_map_conj Box R _ _).symm
end Restriction
section Pairings
private def wickConstant (Bd : ℝ) : ℝ := 2 ^ 16 * ((Nat.factorial 16 : ℕ) : ℝ) ^ 2 * (Bd + 2) ^ 16
private theorem wickPairingSum_sub_le (hP : matchingSumPropertiesStatement) {r : ℕ} (hr : r ≤ 16) (G G' : Fin r → Fin r → ℝ) {Bd d : ℝ}
    (hBd : 0 ≤ Bd) (hG : ∀ i j, |G' i j| ≤ Bd) (hd : ∀ i j, |G i j - G' i j| ≤ d) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |wickPairingSum G - wickPairingSum G'| ≤ wickConstant Bd * d := by
  obtain ⟨h1, -, h3⟩ := hP
  obtain ⟨hempty, hadd, hb1, hb2, -⟩ := h3 (Fin r)
  set b := Bd + 2 with hb
  have hb1' : 1 ≤ b := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hsq : Bd ≤ b ^ 2 := by nlinarith
  have hsq1 : d ≤ b ^ 2 := by nlinarith
  set Dm : Fin r → Fin r → ℝ := fun i j => G i j - G' i j with hDm
  have e1 : matchingSum Finset.univ G = ∑ I ∈ (Finset.univ : Finset (Fin r)).powerset, matchingSum I G' * matchingSum (Finset.univ \ I) Dm := by
    have := hadd Finset.univ G' Dm
    rw [← this]
    congr 1
    funext i j
    simp [hDm]
  have hmem : (Finset.univ : Finset (Fin r)) ∈ (Finset.univ : Finset (Fin r)).powerset := Finset.mem_powerset.2 subset_rfl
  rw [h1 r G, h1 r G', e1, ← Finset.add_sum_erase _ _ hmem, Finset.sdiff_self, hempty Dm, mul_one,
    add_sub_cancel_left]
  have hfac : ∀ I : Finset (Fin r), ((I.card).factorial : ℝ) ≤ (Nat.factorial 16 : ℕ) := by
    intro I
    have h2 : I.card ≤ 16 := by
      have := Finset.card_le_univ I
      simp at this
      omega
    exact_mod_cast Nat.factorial_le h2
  have hterm : ∀ I ∈ (Finset.univ : Finset (Fin r)).powerset.erase Finset.univ,
      |matchingSum I G' * matchingSum (Finset.univ \ I) Dm| ≤ ((Nat.factorial 16 : ℕ) : ℝ) ^ 2 * b ^ 16 * d := by
    intro I hI
    have hne : (Finset.univ \ I : Finset (Fin r)).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      exact (Finset.mem_erase.1 hI).1 (Finset.eq_univ_of_forall fun i => hsub (Finset.mem_univ i))
    have a1 := hb1 I G' b hb0 fun i j => ?_
    have a2 := hb2 (Finset.univ \ I) Dm b d hb0 hne hsq1 hd
    · have hcard : I.card + (Finset.univ \ I : Finset (Fin r)).card = r := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ I)]
        simp only [Finset.card_univ, Fintype.card_fin]
        have := Finset.card_le_univ I
        simp at this
        omega
      rw [abs_mul]
      have hF := hfac I
      have hF' := hfac (Finset.univ \ I)
      have b1 : b ^ I.card * b ^ ((Finset.univ \ I : Finset (Fin r)).card - 2) ≤ b ^ 16 := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hb1' (by omega)
      calc |matchingSum I G'| * |matchingSum (Finset.univ \ I) Dm|
          ≤ (((I.card).factorial : ℝ) * b ^ I.card) *
            ((((Finset.univ \ I : Finset (Fin r)).card).factorial : ℝ) * d * b ^ ((Finset.univ \ I : Finset (Fin r)).card - 2)) :=
            mul_le_mul a1 a2 (abs_nonneg _) (by positivity)
        _ ≤ (((Nat.factorial 16 : ℕ) : ℝ) * b ^ I.card) *
            (((Nat.factorial 16 : ℕ) : ℝ) * d * b ^ ((Finset.univ \ I : Finset (Fin r)).card - 2)) := by
            gcongr
        _ = ((Nat.factorial 16 : ℕ) : ℝ) ^ 2 * (b ^ I.card * b ^ ((Finset.univ \ I : Finset (Fin r)).card - 2)) * d := by ring
        _ ≤ ((Nat.factorial 16 : ℕ) : ℝ) ^ 2 * b ^ 16 * d := by gcongr
    · exact (hG i j).trans hsq
  have hcount : (((Finset.univ : Finset (Fin r)).powerset.erase Finset.univ).card : ℝ) ≤ 2 ^ 16 := by
    have h4 : ((Finset.univ : Finset (Fin r)).powerset.erase Finset.univ).card ≤ 2 ^ r := by
      refine (Finset.card_erase_le).trans ?_
      simp
    have h5 : (2 : ℕ) ^ r ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) hr
    exact_mod_cast h4.trans h5
  calc |∑ I ∈ (Finset.univ : Finset (Fin r)).powerset.erase Finset.univ, matchingSum I G' * matchingSum (Finset.univ \ I) Dm|
      ≤ ∑ I ∈ (Finset.univ : Finset (Fin r)).powerset.erase Finset.univ, ((Nat.factorial 16 : ℕ) : ℝ) ^ 2 * b ^ 16 * d :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = (((Finset.univ : Finset (Fin r)).powerset.erase Finset.univ).card : ℝ) * (((Nat.factorial 16 : ℕ) : ℝ) ^ 2 * b ^ 16 * d) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ 16 * (((Nat.factorial 16 : ℕ) : ℝ) ^ 2 * b ^ 16 * d) := by gcongr
    _ = wickConstant Bd * d := by
        unfold wickConstant
        ring
end Pairings
section Parts
variable {Ω : Type} [MeasurableSpace Ω] {Y : Type} [Fintype Y]
private def symmetrize (K : Matrix Y Y ℝ) : Matrix Y Y ℝ := fun a b => (K a b + K b a) / 2
private theorem symmetrize_support (Box : Y → Prop) {K : Matrix Y Y ℝ} (hK : ∀ a b, K a b ≠ 0 → Box a ∧ Box b) (a b : Y)
    (h : symmetrize K a b ≠ 0) : Box a ∧ Box b := by
  by_cases h1 : K a b = 0
  · by_cases h2 : K b a = 0
    · exact absurd (by simp [symmetrize, h1, h2]) h
    · exact ⟨(hK b a h2).2, (hK b a h2).1⟩
  · exact hK a b h1
private theorem quadraticForm_submatrix_symmetrize (Box : Y → Prop) (K : Matrix Y Y ℝ) (hK : ∀ a b, K a b ≠ 0 → Box a ∧ Box b)
    (g : Y → imaginaryQuaternions) :
    quadraticForm ((symmetrize K).submatrix (Subtype.val : {y // Box y} → Y) Subtype.val) (fun a => g a.1) = quadraticForm K g := by
  unfold quadraticForm
  congr 1
  set sc : Y → Y → ℝ := fun a b => ∑ e : Fin 3, imaginaryComponent e (g a) * imaginaryComponent e (g b) with hsc
  have hs : ∀ a b, sc a b = sc b a := fun a b => Finset.sum_congr rfl fun e _ => mul_comm _ _
  have hoff : ∀ a b, ¬ (Box a ∧ Box b) → symmetrize K a b = 0 := fun a b h => by
    by_contra h0
    exact h (symmetrize_support Box hK a b h0)
  have e1 : ∑ a : {y // Box y}, ∑ b : {y // Box y}, (symmetrize K).submatrix Subtype.val Subtype.val a b * sc a.1 b.1 =
      ∑ a : Y, ∑ b : Y, symmetrize K a b * sc a b := by
    have i1 : ∀ a : {y // Box y}, ∑ b : {y // Box y}, (symmetrize K).submatrix Subtype.val Subtype.val a b * sc a.1 b.1 =
        ∑ b : Y, symmetrize K a.1 b * sc a.1 b := fun a =>
      sum_subtype_eq_of_zero Box (fun b => symmetrize K a.1 b * sc a.1 b) fun b hb => by
        rw [hoff _ _ fun h => hb h.2, zero_mul]
    simp only [i1]
    refine sum_subtype_eq_of_zero Box (fun a => ∑ b : Y, symmetrize K a b * sc a b) fun a ha => ?_
    exact Finset.sum_eq_zero fun b _ => by rw [hoff _ _ fun h => ha h.1, zero_mul]
  have e2 : ∑ a : Y, ∑ b : Y, symmetrize K a b * sc a b = ∑ a : Y, ∑ b : Y, K a b * sc a b := by
    have h1 : ∑ a : Y, ∑ b : Y, K b a * sc a b = ∑ a : Y, ∑ b : Y, K a b * sc a b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs]
    have h2 : ∑ a : Y, ∑ b : Y, symmetrize K a b * sc a b =
        (∑ a : Y, ∑ b : Y, K a b * sc a b + ∑ a : Y, ∑ b : Y, K b a * sc a b) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [symmetrize]
      ring
    rw [h2, h1]
    ring
  exact e1.trans e2
private theorem sum_abs_submatrix_symmetrize_le (Box : Y → Prop) (K : Matrix Y Y ℝ) (hK : ∀ a b, K a b ≠ 0 → Box a ∧ Box b) :
    ∑ a : {y // Box y}, ∑ b : {y // Box y}, |(symmetrize K).submatrix Subtype.val Subtype.val a b| ≤ ∑ a : Y, ∑ b : Y, |K a b| := by
  have hoff : ∀ a b, ¬ (Box a ∧ Box b) → symmetrize K a b = 0 := fun a b h => by
    by_contra h0
    exact h (symmetrize_support Box hK a b h0)
  have e1 : ∑ a : {y // Box y}, ∑ b : {y // Box y}, |(symmetrize K).submatrix Subtype.val Subtype.val a b| =
      ∑ a : Y, ∑ b : Y, |symmetrize K a b| := by
    have i1 : ∀ a : {y // Box y}, ∑ b : {y // Box y}, |(symmetrize K).submatrix Subtype.val Subtype.val a b| =
        ∑ b : Y, |symmetrize K a.1 b| := fun a =>
      sum_subtype_eq_of_zero Box (fun b => |symmetrize K a.1 b|) fun b hb => by rw [hoff _ _ fun h => hb h.2, abs_zero]
    simp only [i1]
    refine sum_subtype_eq_of_zero Box (fun a => ∑ b : Y, |symmetrize K a b|) fun a ha => ?_
    exact Finset.sum_eq_zero fun b _ => by rw [hoff _ _ fun h => ha h.1, abs_zero]
  rw [e1]
  have h1 : ∑ a : Y, ∑ b : Y, |K b a| = ∑ a : Y, ∑ b : Y, |K a b| := Finset.sum_comm
  calc ∑ a : Y, ∑ b : Y, |symmetrize K a b| ≤ ∑ a : Y, ∑ b : Y, (|K a b| + |K b a|) / 2 := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        simp only [symmetrize]
        rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ = (∑ a : Y, ∑ b : Y, |K a b| + ∑ a : Y, ∑ b : Y, |K b a|) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ a : Y, ∑ b : Y, |K a b| := by
        rw [h1]
        ring
private theorem one_le_wickConstant {b : ℝ} (hb : 0 ≤ b) : 1 ≤ wickConstant b := by
  unfold wickConstant
  have h1 : (1 : ℝ) ≤ 2 ^ 16 := by norm_num
  have h2 : (1 : ℝ) ≤ ((Nat.factorial 16 : ℕ) : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast Nat.factorial_pos 16)
  have h3 : (1 : ℝ) ≤ (b + 2) ^ 16 := one_le_pow₀ (by linarith)
  calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr
private theorem localEstimate_of_box (hP : matchingSumPropertiesStatement) (μ : Measure Ω) (Box : Y → Prop) {q : ℕ}
    (F : Fin (q + 1) → Ω → ℝ) (G : Ω → Y → imaginaryQuaternions) (A B : Set Ω) (K : Fin (q + 1) → Matrix Y Y ℝ) (T Tt : Matrix Y Y ℝ)
    (c : Fin (q + 1) → ℝ) (x n C C₁ P d : ℝ) (Cr xr : ℕ → ℝ) (hx : 1 ≤ x) (hd0 : 0 ≤ d) (hdx : d ≤ x ^ (-(1 / 2 : ℝ)))
    (hC₁ : 0 ≤ C₁) (hCC : C₁ + wickConstant (C₁ + 1) ≤ C) (hA : MeasurableSet A) (hsym : Tt.IsSymm)
    (hcm : ∀ a e, Box a → AEStronglyMeasurable (Set.indicator A fun ω => imaginaryComponent e (G ω a)) μ)
    (hcb : ∃ Bg : ℝ, ∀ᵐ ω ∂μ, ω ∈ A → ∀ a e, Box a → |imaginaryComponent e (G ω a)| ≤ Bg)
    (hT : ∀ a b, Box a → Box b → |T a b - Tt a b| ≤ d) (hTb : ∀ a b, Box a → Box b → |T a b| ≤ C₁)
    (hM : ∀ (r : ℕ) (a : Fin r → Y) (e : Fin r → Fin 3), r ≤ 16 → (∀ j, Box (a j)) →
      Integrable (Set.indicator A fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) μ ∧
      |∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) ω ∂μ -
        x ^ (-(r : ℝ) / 2) * wickPairingSum fun i i' => if e i = e i' then T (a i) (a i') else 0| ≤
        C₁ * x ^ (-((r : ℝ) + 1) / 2 + 2 / 1000))
    (hK : ∀ i a b, K i a b ≠ 0 → Box a ∧ Box b)
    (hSz : ∀ i, ∑ a, ∑ b, |K i a b| ≤ C * n ^ 4 * Real.log x ^ 24)
    (hnear : ∀ (i : Fin (q + 1)) (r : ℕ), 1 ≤ r → xr r ≤ x →
      ∫⁻ ω, ENNReal.ofReal (Set.indicator (A ∩ B) (fun ω => |F i ω - c i - quadraticForm (K i) (G ω)| ^ (2 * r)) ω) ∂μ ≤
        ENNReal.ofReal ((Cr r * n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000)) ^ (2 * r)))
    (hrare : μ.real Aᶜ ≤ C * x ^ (-P)) (hrareB : μ.real (A ∩ Bᶜ) ≤ C * x ^ (-P)) :
    IsLocalQuadraticObservable μ F (fun ω (a : {y // Box y}) => G ω a.1) A B
      (fun i => (symmetrize (K i)).submatrix Subtype.val Subtype.val) (Tt.submatrix Subtype.val Subtype.val) c x n C P Cr xr ∧
    cyclicTraceSum (fun i => (symmetrize (K i)).submatrix (Subtype.val : {y // Box y} → Y) Subtype.val)
        (Tt.submatrix Subtype.val Subtype.val) = cyclicTraceSum (fun i => symmetrize (K i)) Tt := by
  have hx0 : 0 < x := by linarith
  have hd1 : d ≤ 1 := hdx.trans (Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num))
  have hBd : 0 ≤ C₁ + 1 := by linarith
  have hpc := one_le_wickConstant hBd
  have hTt : ∀ a b, Box a → Box b → |Tt a b| ≤ C₁ + 1 := fun a b ha hb => by
    have h1 := hT a b ha hb
    have h2 := hTb a b ha hb
    have h3 : |Tt a b| ≤ |T a b| + |T a b - Tt a b| := by
      have := abs_sub_abs_le_abs_sub (Tt a b) (T a b)
      rw [abs_sub_comm (Tt a b)] at this
      linarith
    linarith
  refine ⟨⟨hA, fun a e => hcm a.1 e a.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrare, hrareB⟩, ?_⟩
  · obtain ⟨Bg, hBg⟩ := hcb
    refine ⟨Bg, ?_⟩
    filter_upwards [hBg] with ω hω hA' a e
    exact hω hA' a.1 e a.2
  · intro r a e hr
    obtain ⟨h1, h2⟩ := hM r (fun j => (a j).1) e hr fun j => (a j).2
    refine ⟨h1, ?_⟩
    set Gp : Fin r → Fin r → ℝ := fun i i' => if e i = e i' then T (a i).1 (a i').1 else 0 with hGp
    set Gq : Fin r → Fin r → ℝ := fun i i' => if e i = e i' then Tt (a i).1 (a i').1 else 0 with hGq
    have hclose := wickPairingSum_sub_le hP hr Gp Gq hBd (fun i i' => by
      simp only [hGq]
      split_ifs
      · exact hTt _ _ (a i).2 (a i').2
      · simpa using hBd) (fun i i' => by
      simp only [hGp, hGq]
      split_ifs
      · exact hT _ _ (a i).2 (a i').2
      · simpa using hd0) hd0 hd1
    set X := x ^ (-((r : ℝ) + 1) / 2 + 2 / 1000) with hX
    have hX0 : 0 < X := Real.rpow_pos_of_pos hx0 _
    have hxr : 0 < x ^ (-(r : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
    have hrp : x ^ (-(r : ℝ) / 2) * d ≤ X := by
      have h3 : x ^ (-(r : ℝ) / 2) * d ≤ x ^ (-(r : ℝ) / 2) * x ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hdx hxr.le
      rw [← Real.rpow_add hx0] at h3
      refine h3.trans (Real.rpow_le_rpow_of_exponent_le hx ?_)
      linarith
    have e1 : (∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i).1)) ω ∂μ) - x ^ (-(r : ℝ) / 2) * wickPairingSum Gq =
        ((∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i).1)) ω ∂μ) - x ^ (-(r : ℝ) / 2) * wickPairingSum Gp) +
          x ^ (-(r : ℝ) / 2) * (wickPairingSum Gp - wickPairingSum Gq) := by ring
    show |(∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i).1)) ω ∂μ) - x ^ (-(r : ℝ) / 2) * wickPairingSum Gq| ≤ C * X
    rw [e1]
    have h4 : |x ^ (-(r : ℝ) / 2) * (wickPairingSum Gp - wickPairingSum Gq)| ≤ wickConstant (C₁ + 1) * X := by
      rw [abs_mul, abs_of_pos hxr]
      calc x ^ (-(r : ℝ) / 2) * |wickPairingSum Gp - wickPairingSum Gq| ≤ x ^ (-(r : ℝ) / 2) * (wickConstant (C₁ + 1) * d) :=
            mul_le_mul_of_nonneg_left hclose hxr.le
        _ = wickConstant (C₁ + 1) * (x ^ (-(r : ℝ) / 2) * d) := by ring
        _ ≤ wickConstant (C₁ + 1) * X := mul_le_mul_of_nonneg_left hrp (by linarith)
    calc _ ≤ |(∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i).1)) ω ∂μ) - x ^ (-(r : ℝ) / 2) * wickPairingSum Gp| +
          |x ^ (-(r : ℝ) / 2) * (wickPairingSum Gp - wickPairingSum Gq)| := abs_add_le _ _
      _ ≤ C₁ * X + wickConstant (C₁ + 1) * X := add_le_add h2 h4
      _ = (C₁ + wickConstant (C₁ + 1)) * X := by ring
      _ ≤ C * X := mul_le_mul_of_nonneg_right hCC hX0.le
  · ext a b
    exact congrFun (congrFun hsym a.1) b.1
  · intro a b
    have := hTt a.1 b.1 a.2 b.2
    show |Tt a.1 b.1| ≤ C
    linarith
  · intro i
    ext a b
    show (K i b.1 a.1 + K i a.1 b.1) / 2 = (K i a.1 b.1 + K i b.1 a.1) / 2
    ring
  · intro i
    exact (sum_abs_submatrix_symmetrize_le Box (K i) (hK i)).trans (hSz i)
  · intro i r hr hxr
    have e : (fun ω => |F i ω - c i - quadraticForm ((symmetrize (K i)).submatrix (Subtype.val : {y // Box y} → Y) Subtype.val)
        (fun a => G ω a.1)| ^ (2 * r)) = fun ω => |F i ω - c i - quadraticForm (K i) (G ω)| ^ (2 * r) := by
      funext ω
      rw [quadraticForm_submatrix_symmetrize Box (K i) (hK i) (G ω)]
    show ∫⁻ ω, ENNReal.ofReal (Set.indicator (A ∩ B) (fun ω => |F i ω - c i - quadraticForm
      ((symmetrize (K i)).submatrix (Subtype.val : {y // Box y} → Y) Subtype.val) (fun a => G ω a.1)| ^ (2 * r)) ω) ∂μ ≤ _
    rw [e]
    exact hnear i r hr hxr
  · exact cyclicTraceSum_submatrix Box (fun i => symmetrize (K i)) Tt fun i a b h => symmetrize_support Box (hK i) a b h
end Parts
section Sizes
private theorem card_supBall_le {n : ℕ} [NeZero n] (o : TorusSite n) {R : ℝ} (hR : 0 ≤ R) : ((supBall o R).card : ℝ) ≤ (2 * R + 1) ^ 4 := by
  set r := ⌊R⌋₊ with hr
  set φ : TorusSite n → Fin 4 → ℤ := fun z i => (z i - o i).valMinAbs with hφ
  have hmaps : ∀ z ∈ supBall o R, φ z ∈ Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(r : ℤ)) r := by
    intro z hz
    have h1 : (supDist z o : ℝ) ≤ R := (Finset.mem_filter.1 hz).2
    have h2 : supDist z o ≤ r := Nat.le_floor h1
    have h3 := (supDist_le_iff z o r).1 h2
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_
    have h4 := h3 i
    have h5 : |((z i - o i).valMinAbs)| ≤ (r : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h4
    exact abs_le.1 h5
  have hinj : Set.InjOn φ (supBall o R) := by
    intro z _ z' _ h
    funext i
    have h1 := congrArg (fun f : Fin 4 → ℤ => ((f i : ℤ) : ZMod n)) h
    simp only [hφ, ZMod.coe_valMinAbs] at h1
    exact sub_left_injective h1
  have h1 := Finset.card_le_card_of_injOn φ hmaps hinj
  rw [Fintype.card_piFinset] at h1
  simp only [Finset.prod_const, Int.card_Icc, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (((r : ℤ) + 1 - -(r : ℤ)).toNat : ℝ) = 2 * (r : ℝ) + 1 := by
    have : ((r : ℤ) + 1 - -(r : ℤ)).toNat = 2 * r + 1 := by omega
    rw [this]
    push_cast
    ring
  have h3 : (r : ℝ) ≤ R := Nat.floor_le hR
  calc ((supBall o R).card : ℝ) ≤ (((r : ℤ) + 1 - -(r : ℤ)).toNat : ℝ) ^ 4 := by exact_mod_cast h1
    _ = (2 * (r : ℝ) + 1) ^ 4 := by rw [h2]
    _ ≤ (2 * R + 1) ^ 4 := by
      refine pow_le_pow_left₀ (by positivity) (by linarith) 4
private def orientedPlaquettesNear {S : ℕ} [NeZero S] (z : TorusSite S) (ρ : ℝ) : Finset (OrientedPlaquette S) :=
  Finset.univ.filter fun a => (supDist a.1.1 z : ℝ) ≤ ρ
private theorem card_orientedPlaquettesNear_le {S : ℕ} [NeZero S] (z : TorusSite S) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((orientedPlaquettesNear z ρ).card : ℝ) ≤ 16 * (2 * ρ + 1) ^ 4 := by
  have hmaps : ∀ a ∈ orientedPlaquettesNear z ρ, a.1 ∈ (supBall z ρ) ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4)) := by
    intro a ha
    refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 ha).2⟩
  have hinj : Set.InjOn (fun a : OrientedPlaquette S => a.1) (orientedPlaquettesNear z ρ) := fun a _ b _ h => Subtype.ext h
  have h1 := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product, Finset.card_univ] at h1
  have h2 : Fintype.card (Fin 4 × Fin 4) = 16 := by simp
  rw [h2] at h1
  have h3 := card_supBall_le z hρ
  calc ((orientedPlaquettesNear z ρ).card : ℝ) ≤ ((supBall z ρ).card : ℝ) * 16 := by exact_mod_cast h1
    _ ≤ (2 * ρ + 1) ^ 4 * 16 := by gcongr
    _ = _ := by ring
private theorem sum_abs_localKernel_le {S : ℕ} [NeZero S] {ρ del size : ℝ} {κ : TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ}
    (hκ : IsLocalKernel ρ del size κ) (hρ : 0 ≤ ρ) (hdel : 0 ≤ del) (hs : 0 ≤ size) (z : TorusSite S) :
    ∑ a : OrientedPlaquette S, ∑ b : OrientedPlaquette S, |κ z a.1 b.1| ≤ (16 * (2 * ρ + 1) ^ 4) ^ 2 * size := by
  have hoff : ∀ a b : OrientedPlaquette S, a ∉ orientedPlaquettesNear z ρ ∨ b ∉ orientedPlaquettesNear z ρ → κ z a.1 b.1 = 0 := by
    intro a b h
    refine hκ.support z a.1 b.1 ?_
    rcases h with h | h
    · left
      by_contra h2
      exact h (Finset.mem_filter.2 ⟨Finset.mem_univ _, not_lt.1 h2⟩)
    · right
      by_contra h2
      exact h (Finset.mem_filter.2 ⟨Finset.mem_univ _, not_lt.1 h2⟩)
  have hbd : ∀ a b : OrientedPlaquette S, |κ z a.1 b.1| ≤ size := by
    intro a b
    refine (hκ.decay z a.1 b.1).trans ?_
    have h1 : 0 ≤ del * max (supDist a.1.1 z : ℝ) (supDist b.1.1 z : ℝ) :=
      mul_nonneg hdel (le_max_of_le_left (by positivity))
    have h2 : Real.exp (-(del * max (supDist a.1.1 z : ℝ) (supDist b.1.1 z : ℝ))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc _ ≤ size * 1 := mul_le_mul_of_nonneg_left h2 hs
      _ = size := mul_one _
  have e1 : ∑ a : OrientedPlaquette S, ∑ b : OrientedPlaquette S, |κ z a.1 b.1| =
      ∑ a ∈ orientedPlaquettesNear z ρ, ∑ b ∈ orientedPlaquettesNear z ρ, |κ z a.1 b.1| := by
    symm
    refine (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_).trans (Finset.sum_congr rfl fun a _ => ?_)
    · exact Finset.sum_eq_zero fun b _ => by rw [hoff a b (Or.inl ha), abs_zero]
    · refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_
      rw [hoff a b (Or.inr hb), abs_zero]
  rw [e1]
  have hc := card_orientedPlaquettesNear_le z hρ
  calc ∑ a ∈ orientedPlaquettesNear z ρ, ∑ b ∈ orientedPlaquettesNear z ρ, |κ z a.1 b.1|
      ≤ ∑ _a ∈ orientedPlaquettesNear z ρ, ∑ _b ∈ orientedPlaquettesNear z ρ, size :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hbd a b
    _ = ((orientedPlaquettesNear z ρ).card : ℝ) ^ 2 * size := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (16 * (2 * ρ + 1) ^ 4) ^ 2 * size := by
        gcongr
end Sizes
section Kernels
variable {S : ℕ} [NeZero S]
private def symmetrizeKernel (κ : TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ) :
    TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ :=
  fun z p p' => (κ z p p' + κ z p' p) / 2
private theorem isLocalKernel_symmetrizeKernel {ρ del size : ℝ} {κ : TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ}
    (h : IsLocalKernel ρ del size κ) : IsLocalKernel ρ del size (symmetrizeKernel κ) := by
  refine ⟨fun y p p' hp => ?_, fun y p p' => ?_⟩
  · simp only [symmetrizeKernel]
    rw [h.support y p p' hp, h.support y p' p hp.symm]
    simp
  · simp only [symmetrizeKernel]
    have h1 := h.decay y p p'
    have h2 := h.decay y p' p
    rw [max_comm] at h2
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num), div_le_iff₀ (by norm_num)]
    have := abs_add_le (κ y p p') (κ y p' p)
    linarith
private theorem isNormalizedShareForm_symmetrizeKernel {err : ℝ} {κ : TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ}
    (h : IsNormalizedShareForm err κ) : IsNormalizedShareForm err (symmetrizeKernel κ) := by
  intro y μ ν ρ τ h1 h2
  have a1 := h y μ ν ρ τ h1 h2
  have a2 := h y ρ τ μ ν h2 h1
  set P₁ := (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette S => p.2 = (μ, ν)) with hP₁
  set P₂ := (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette S => p.2 = (ρ, τ)) with hP₂
  have e : ∑ p ∈ P₁, ∑ p' ∈ P₂, symmetrizeKernel κ y p p' =
      ((∑ p ∈ P₁, ∑ p' ∈ P₂, κ y p p') + ∑ p' ∈ P₂, ∑ p ∈ P₁, κ y p' p) / 2 := by
    rw [Finset.sum_comm (s := P₂) (t := P₁), ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    rfl
  have hc : (if ((μ, ν) : Fin 4 × Fin 4) = (ρ, τ) then (1 : ℝ) else 0) = if ((ρ, τ) : Fin 4 × Fin 4) = (μ, ν) then 1 else 0 := by
    simp only [eq_comm]
  rw [e]
  rw [← hc] at a2
  rw [abs_le] at a1 a2 ⊢
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
private theorem symmetrize_responseKernel (A : Finset (TorusSite S)) (hat : TorusSite S → ℝ) (al : ℝ)
    (ka kr : TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ) :
    symmetrize (responseKernel A hat al ka kr) = responseKernel A hat al (symmetrizeKernel ka) (symmetrizeKernel kr) := by
  ext a b
  simp only [symmetrize, responseKernel, symmetrizeKernel]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring
private theorem responseKernel_support {o : TorusSite S} {nn ρ del C C' al : ℝ} (A : Finset (TorusSite S)) (hat : TorusSite S → ℝ)
    {ka kr : TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ} (hA : A ⊆ supBall o (12 * nn)) (hka : IsLocalKernel ρ del C ka)
    (hkr : IsLocalKernel ρ del C' kr) (hρ : ρ ≤ 7 * nn) (a b : OrientedPlaquette S)
    (h : responseKernel A hat al ka kr a b ≠ 0) :
    a.1.1 ∈ supBall o (19 * nn) ∧ b.1.1 ∈ supBall o (19 * nn) := by
  obtain ⟨z, hz, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hnear : ¬ (ρ < (supDist a.1.1 z : ℝ) ∨ ρ < (supDist b.1.1 z : ℝ)) := by
    intro hc
    apply hne
    rw [hka.support z a.1 b.1 hc, hkr.support z a.1 b.1 hc]
    simp
  push_neg at hnear
  have hzo : (supDist z o : ℝ) ≤ 12 * nn := (Finset.mem_filter.1 (hA hz)).2
  have tri : ∀ c : TorusSite S, (supDist c z : ℝ) ≤ ρ → c ∈ supBall o (19 * nn) := by
    intro c hc
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have h1 : (supDist c o : ℝ) ≤ (supDist c z : ℝ) + (supDist z o : ℝ) := by
      exact_mod_cast supDist_triangle c z o
    linarith
  exact ⟨tri _ hnear.1, tri _ hnear.2⟩
private theorem sum_abs_responseKernel_le {nn ρ del C C' al : ℝ} (o : TorusSite S) (A : Finset (TorusSite S)) (hat : TorusSite S → ℝ)
    {ka kr : TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ} (hA : A ⊆ supBall o (12 * nn)) (hn : 0 ≤ nn) (hρ : 0 ≤ ρ) (hdel : 0 ≤ del)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hhat : ∀ z, |hat z| ≤ 1) (hal : |al| ≤ 2) (hka : IsLocalKernel ρ del C ka)
    (hkr : IsLocalKernel ρ del C' kr) :
    ∑ a, ∑ b, |responseKernel A hat al ka kr a b| ≤ (24 * nn + 1) ^ 4 * ((16 * (2 * ρ + 1) ^ 4) ^ 2 * (2 * C + C')) := by
  have hterm : ∀ a b : OrientedPlaquette S, |responseKernel A hat al ka kr a b| ≤ ∑ z ∈ A, (2 * |ka z a.1 b.1| + |kr z a.1 b.1|) := by
    intro a b
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
    rw [abs_mul, abs_mul]
    have h1 := hhat z
    have : |hat z| * |al| ≤ 1 * 2 := mul_le_mul h1 hal (abs_nonneg _) (by norm_num)
    have h2 := abs_nonneg (ka z a.1 b.1)
    nlinarith
  have e : ∑ a : OrientedPlaquette S, ∑ b : OrientedPlaquette S, ∑ z ∈ A, (2 * |ka z a.1 b.1| + |kr z a.1 b.1|) =
      ∑ z ∈ A, (2 * (∑ a : OrientedPlaquette S, ∑ b : OrientedPlaquette S, |ka z a.1 b.1|) + ∑ a : OrientedPlaquette S, ∑ b : OrientedPlaquette S, |kr z a.1 b.1|) := by
    rw [show (∑ a : OrientedPlaquette S, ∑ b : OrientedPlaquette S, ∑ z ∈ A, (2 * |ka z a.1 b.1| + |kr z a.1 b.1|)) =
      ∑ a : OrientedPlaquette S, ∑ z ∈ A, ∑ b : OrientedPlaquette S, (2 * |ka z a.1 b.1| + |kr z a.1 b.1|) from
        Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have hz : ∀ z ∈ A, 2 * (∑ a : OrientedPlaquette S, ∑ b : OrientedPlaquette S, |ka z a.1 b.1|) + ∑ a : OrientedPlaquette S, ∑ b : OrientedPlaquette S, |kr z a.1 b.1| ≤
      (16 * (2 * ρ + 1) ^ 4) ^ 2 * (2 * C + C') := by
    intro z _
    have h1 := sum_abs_localKernel_le hka hρ hdel hC z
    have h2 := sum_abs_localKernel_le hkr hρ hdel hC' z
    nlinarith
  have hcard : (A.card : ℝ) ≤ (24 * nn + 1) ^ 4 := by
    have h1 : (A.card : ℝ) ≤ ((supBall o (12 * nn)).card : ℝ) := by exact_mod_cast Finset.card_le_card hA
    have h2 := card_supBall_le o (show (0 : ℝ) ≤ 12 * nn by linarith)
    have e2 : 2 * (12 * nn) + 1 = 24 * nn + 1 := by ring
    rw [e2] at h2
    exact h1.trans h2
  have hpos : 0 ≤ (16 * (2 * ρ + 1) ^ 4) ^ 2 * (2 * C + C') := by positivity
  calc ∑ a, ∑ b, |responseKernel A hat al ka kr a b|
      ≤ ∑ a : OrientedPlaquette S, ∑ b : OrientedPlaquette S, ∑ z ∈ A, (2 * |ka z a.1 b.1| + |kr z a.1 b.1|) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
    _ = _ := e
    _ ≤ ∑ _z ∈ A, (16 * (2 * ρ + 1) ^ 4) ^ 2 * (2 * C + C') := Finset.sum_le_sum hz
    _ = (A.card : ℝ) * ((16 * (2 * ρ + 1) ^ 4) ^ 2 * (2 * C + C')) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hpos
private theorem sum_plaquettesIn_eq (f : TorusPlaquette S → ℝ) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite S)), f p = ∑ a : OrientedPlaquette S, f a.1 := by
  refine Finset.sum_subtype _ (fun p => ?_) f
  simp [plaquettesIn]
abbrev _root_.YangMills.SharedProofs.p68842 := @sum_plaquettesIn_eq
private theorem half_sum_eq_quadraticForm (A : Finset (TorusSite S)) (hat : TorusSite S → ℝ) (al : ℝ)
    (ka kr : TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ)
    (hhat : ∀ z, z ∉ A → hat z = 0) (hkr : ∀ z, z ∉ A → ∀ p p', kr z p p' = 0) (g : TorusPlaquette S → imaginaryQuaternions) :
    (1 / 2 : ℝ) * ∑ z, ∑ p ∈ plaquettesIn Finset.univ, ∑ p' ∈ plaquettesIn Finset.univ,
      (hat z * al * ka z p p' + kr z p p') * ∑ e : Fin 3, imaginaryComponent e (g p) * imaginaryComponent e (g p') =
    quadraticForm (responseKernel A hat al ka kr) fun a => g a.1 := by
  unfold quadraticForm
  congr 1
  simp only [sum_plaquettesIn_eq, responseKernel]
  rw [← Finset.sum_subset (Finset.subset_univ A) fun z _ hz => ?_]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
  · refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [hhat z hz, hkr z hz]
    simp
end Kernels
section Floors
private theorem side_exponent_bounds {L m M : ℕ} {x : ℝ} (hL : 2 ≤ L) (hlog : 2 * Real.log L + 3 ≤ Real.log x)
    (hM : (M : ℝ) ≤ Real.log x ^ 2) (hside : Real.exp (Real.log x ^ 3) ≤ 2 * (L : ℝ) ^ m) :
    2 * M + 1 ≤ m ∧ Real.exp (3 * Real.log x ^ 2) ≤ 2 * (L : ℝ) ^ (m - 2 * M) := by
  set t := Real.log x with ht
  set Λ := Real.log L with hΛ
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h2 : ∀ j : ℕ, Real.log (2 * (L : ℝ) ^ j) = Real.log 2 + j * Λ := by
    intro j
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hm : t ^ 3 ≤ Real.log 2 + m * Λ := by
    rw [← h2]
    have := Real.log_le_log (Real.exp_pos _) hside
    rwa [Real.log_exp] at this
  have hsq : 0 ≤ t ^ 2 := sq_nonneg t
  have hbig : (2 * Λ + 3) * t ^ 2 ≤ t ^ 3 := by
    have : t ^ 3 = t * t ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hlog hsq
  have hM2 : 2 * (M : ℝ) * Λ ≤ 2 * t ^ 2 * Λ := by
    have := mul_le_mul_of_nonneg_right hM hΛ0
    nlinarith
  have h9 : 9 ≤ t ^ 2 := by nlinarith
  have hgt : 2 * M + 1 ≤ m := by
    by_contra hc
    have hle : (m : ℝ) ≤ 2 * M := by
      have : m ≤ 2 * M := by omega
      exact_mod_cast this
    have h3 := mul_le_mul_of_nonneg_right hle hΛ0
    nlinarith
  refine ⟨hgt, ?_⟩
  have hdiff : (((m - 2 * M : ℕ) : ℝ)) = (m : ℝ) - 2 * M := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hlogN : 3 * t ^ 2 ≤ Real.log (2 * (L : ℝ) ^ (m - 2 * M)) := by
    rw [h2, hdiff]
    nlinarith
  calc Real.exp (3 * t ^ 2) ≤ Real.exp (Real.log (2 * (L : ℝ) ^ (m - 2 * M))) := Real.exp_le_exp.2 hlogN
    _ = 2 * (L : ℝ) ^ (m - 2 * M) := Real.exp_log (by positivity)
private theorem four_zpow_neg_chainDepth_le {x : ℝ} (hx : 0 < x) (h2 : 2 ≤ Real.log x) :
    (4 : ℝ) ^ (-(chainDepth x : ℤ)) ≤ x⁻¹ := by
  set t := Real.log x with ht
  have hfl : t ^ 2 < (chainDepth x : ℝ) + 1 := Nat.lt_floor_add_one _
  have hM : t ≤ chainDepth x := by nlinarith
  have h1 : x ≤ (4 : ℝ) ^ chainDepth x := by
    have a1 : x = Real.exp t := (Real.exp_log hx).symm
    have a2 : Real.exp t ≤ Real.exp (chainDepth x : ℝ) := Real.exp_le_exp.2 hM
    have a3 : Real.exp (chainDepth x : ℝ) = Real.exp 1 ^ chainDepth x := by
      rw [← Real.exp_nat_mul, mul_one]
    have a4 : Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9
      linarith
    have a5 := pow_le_pow_left₀ (Real.exp_pos 1).le a4 (chainDepth x)
    linarith
  rw [zpow_neg, zpow_natCast]
  exact inv_anti₀ hx h1
private theorem scaleWindow_bounds {L : ℕ} {x n vt : ℝ} (hL2 : 2 ≤ L) (e1 : 2 * Real.log L + 3 ≤ Real.log x)
    (e4 : Real.log x ^ 3 ≤ x ^ ((1 : ℝ) / 100)) (e5 : 2 / vt ≤ x ^ ((1 : ℝ) / 100)) (e7 : 1 ≤ x) (hvt0 : 0 < vt)
    (habove : 2 ^ 12 * (L : ℝ) * (clusterRange x : ℝ) ≤ n) :
    1 ≤ n ∧ 2 ≤ vt * n ∧ logCubeScale x ≤ 7 * n ∧ logCubeScale x ≤ Real.log x ^ 3 := by
  have hL1 : (1 : ℝ) ≤ L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
    linarith
  have hLog0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  have ht3 : 3 ≤ Real.log x := by linarith
  have hrange : x ^ ((1 : ℝ) / 100) ≤ clusterRange x := Nat.le_ceil _
  have hnx : x ^ ((1 : ℝ) / 100) ≤ n := by
    have h2 : (0 : ℝ) ≤ clusterRange x := Nat.cast_nonneg _
    have h3 : (1 : ℝ) * (clusterRange x : ℝ) ≤ 2 ^ 12 * (L : ℝ) * clusterRange x :=
      mul_le_mul_of_nonneg_right (by nlinarith) h2
    linarith
  have hn1 : 1 ≤ n := (Real.one_le_rpow e7 (by norm_num)).trans hnx
  have hvn : 2 ≤ vt * n := by
    have h1 : 2 / vt ≤ n := e5.trans hnx
    rw [div_le_iff₀ hvt0] at h1
    linarith
  have hρ : logCubeScale x ≤ Real.log x ^ 3 := Nat.floor_le (by positivity)
  exact ⟨hn1, hvn, by linarith, hρ⟩
private theorem exists_side_of_scaleWindow {L m M n₀ : ℕ} {x : ℝ} (hL2 : 2 ≤ L) (e1 : 2 * Real.log L + 3 ≤ Real.log x) (e2 : (n₀ : ℝ) ≤ x)
    (e7 : 1 ≤ x) (hM : (M : ℝ) ≤ Real.log x ^ 2) (hw : Real.exp (Real.log x ^ 3) ≤ 2 * (L : ℝ) ^ m) :
    ∃ (N w : ℕ), N = 2 * L ^ (w + 1) ∧ 0 < N ∧ L ∣ N ∧ n₀ ≤ N ∧ (2 : ℝ) ^ 10 * localBoxRadius x ≤ N ∧
      fineSide L M (fineSide L M N) = 2 * L ^ m := by
  have hx0 : 0 < x := by linarith
  have hL1 : (1 : ℝ) ≤ L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
    linarith
  have hLog0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  obtain ⟨hgt, hbigN⟩ := side_exponent_bounds hL2 e1 hM hw
  refine ⟨2 * L ^ (m - 2 * M), m - 2 * M - 1, by
    congr 2
    omega, by positivity, ?_, ?_, ?_, ?_⟩
  · exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2
  · have h1 : x ≤ Real.exp (3 * Real.log x ^ 2) := by
      calc x = Real.exp (Real.log x) := (Real.exp_log hx0).symm
        _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)
    have h2 : (n₀ : ℝ) ≤ 2 * (L : ℝ) ^ (m - 2 * M) := e2.trans (h1.trans hbigN)
    exact_mod_cast h2
  · have h1 : localBoxRadius x ≤ x ^ ((1 : ℝ) / 20) := Nat.floor_le (by positivity)
    have h2 : x ^ ((1 : ℝ) / 20) = Real.exp (Real.log x * (1 / 20)) := Real.rpow_def_of_pos hx0 _
    have h3 : (2 : ℝ) ^ 10 ≤ Real.exp 10 := by
      have a1 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have a2 := pow_le_pow_left₀ (by norm_num) a1 10
      rw [← Real.exp_nat_mul] at a2
      norm_num at a2 ⊢
      exact a2
    have h4 : Real.exp 10 * Real.exp (Real.log x * (1 / 20)) ≤ Real.exp (3 * Real.log x ^ 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith
    have h5 : (0 : ℝ) ≤ localBoxRadius x := Nat.cast_nonneg _
    have h6 : ((2 * L ^ (m - 2 * M) : ℕ) : ℝ) = 2 * (L : ℝ) ^ (m - 2 * M) := by
      push_cast
      ring
    rw [h6]
    calc (2 : ℝ) ^ 10 * localBoxRadius x ≤ Real.exp 10 * Real.exp (Real.log x * (1 / 20)) := by
          rw [← h2]
          exact mul_le_mul h3 h1 h5 (Real.exp_pos _).le
      _ ≤ _ := h4.trans hbigN
  · rw [fineSide_eq, fineSide_eq, mul_assoc, mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
private theorem kernel_size_arith {n ρ t C₀ : ℝ} (hn : 1 ≤ n) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ t ^ 3) (ht : 1 ≤ t) (hC₀ : 0 ≤ C₀) :
    (24 * n + 1) ^ 4 * ((16 * (2 * ρ + 1) ^ 4) ^ 2 * (2 * C₀ + 2 * C₀)) ≤ (25 : ℝ) ^ 4 * (16 ^ 2 * 3 ^ 8) * (4 * C₀) * n ^ 4 * t ^ 24 := by
  have h1 : 24 * n + 1 ≤ 25 * n := by linarith
  have ht3 : 1 ≤ t ^ 3 := one_le_pow₀ ht
  have h2 : 2 * ρ + 1 ≤ 3 * t ^ 3 := by linarith
  have h3 : (24 * n + 1) ^ 4 ≤ (25 * n) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
  have h4 : (2 * ρ + 1) ^ 4 ≤ (3 * t ^ 3) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
  have h5 : (16 * (2 * ρ + 1) ^ 4) ^ 2 ≤ (16 * (3 * t ^ 3) ^ 4) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc (24 * n + 1) ^ 4 * ((16 * (2 * ρ + 1) ^ 4) ^ 2 * (2 * C₀ + 2 * C₀))
      ≤ (25 * n) ^ 4 * ((16 * (3 * t ^ 3) ^ 4) ^ 2 * (2 * C₀ + 2 * C₀)) := by gcongr
    _ = _ := by ring
private theorem abs_mul_inv_le_rpow {x c : ℝ} (hx : 1 ≤ x) (h : (|c| + 1) ^ 2 ≤ x) : |c| * x⁻¹ ≤ x ^ (-(1 / 2 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set w := x ^ ((1 : ℝ) / 2) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hx0 _
  have hww : w * w = x := by
    rw [hw, ← Real.rpow_add hx0]
    norm_num
  have e : x ^ (-(1 / 2 : ℝ)) = w⁻¹ := by
    rw [Real.rpow_neg hx0.le]
  rw [e, ← hww, mul_inv]
  have h1 : |c| ≤ w := by
    have : (|c| + 1) ^ 2 ≤ w ^ 2 := by
      rw [pow_two w, hww]
      exact h
    have h2 := abs_le_of_sq_le_sq this hw0.le
    have h3 := le_abs_self (|c| + 1)
    linarith
  have h2 : 0 < w⁻¹ := inv_pos.2 hw0
  calc |c| * (w⁻¹ * w⁻¹) = (|c| * w⁻¹) * w⁻¹ := by ring
    _ ≤ (w * w⁻¹) * w⁻¹ := by gcongr
    _ = w⁻¹ := by rw [mul_inv_cancel₀ hw0.ne', one_mul]
end Floors
section Table
variable (Tb : ParameterAssignment) (y : ℝ)
private def CurvatureMomentsOnBox : Prop :=
  ∃ C x₀ : ℝ, ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))),
    ∀ w : ℕ, N = 2 * (Tb.stepParameters y).side ^ (w + 1) → IsLocalChainAbove Tb y T β k N nn x₀ →
    MeasurableSet {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o} ∧
    (∀ (p : TorusPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))) (e : Fin 3),
      p ∈ plaquettesIn Finset.univ → p.1 ∈ supBall o (19 * nn) →
      AEStronglyMeasurable (Set.indicator {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o}
        (fun u => imaginaryComponent e (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn (couplingFlow (Tb.stepParameters y) β k).1 N u o p)))
        (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 + chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) ∧
      ∀ᵐ u ∂(markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 + chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N),
        IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o →
        |imaginaryComponent e (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn (couplingFlow (Tb.stepParameters y) β k).1 N u o p)| ≤ C) ∧
    (∀ (r : ℕ) (p : Fin r → TorusPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)))
      (e : Fin r → Fin 3), r ≤ 16 → (∀ j, p j ∈ plaquettesIn Finset.univ ∧ (p j).1 ∈ supBall o (19 * nn)) →
      Integrable (Set.indicator {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o}
        (fun u => ∏ j, imaginaryComponent (e j) (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn (couplingFlow (Tb.stepParameters y) β k).1 N u o (p j))))
        (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 + chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) ∧
      |∫ u, Set.indicator {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o}
          (fun u => ∏ j, imaginaryComponent (e j) (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn (couplingFlow (Tb.stepParameters y) β k).1 N u o (p j))) u
          ∂(markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 + chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) -
        (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(r : ℝ) / 2) * wickPairingSum fun i j =>
          if e i = e j then accumulatedCovariance Tb.coupling Tb.ρA (Tb.stepParameters y).side k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
            (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (curlFunctional (p i)) (curlFunctional (p j)) else 0| ≤
        C * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-((r : ℝ) + 1) / 2 + 2 / 1000)) ∧
    ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)))),
      ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)))),
      p.1 ∈ supBall o (19 * nn) → p'.1 ∈ supBall o (19 * nn) →
      |accumulatedCovariance Tb.coupling Tb.ρA (Tb.stepParameters y).side k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
        (curlFunctional p) (curlFunctional p')| ≤ C
private theorem IsLocalKernel.mono_size {n : ℕ} [NeZero n] {ρ del s s' : ℝ} {κ : TorusSite n → TorusPlaquette n → TorusPlaquette n → ℝ}
    (h : IsLocalKernel ρ del s κ) (hs : s ≤ s') : IsLocalKernel ρ del s' κ :=
  ⟨h.support, fun y p p' => (h.decay y p p').trans (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le)⟩
private theorem localEstimate_at_side (hP : matchingSumPropertiesStatement) (hMean : WeightsCloseToBlockMeans)
    (hMeans : BlockMeanIsLinearAndLocal) (hodd : Odd (Tb.stepParameters y).side)
    {del C₀ C₁ C d P tgt err : ℝ} (Cq xq : ℕ → ℝ) {q : ℕ}
    (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k : ℕ) (nn : ℝ) (al : ℕ → ℝ)
    (hx : 1 ≤ (couplingFlow (Tb.stepParameters y) β k).1) (hd0 : 0 ≤ d) (hdx : d ≤ (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ)))
    (hn0 : 0 ≤ nn) (hρ7 : logCubeScale (couplingFlow (Tb.stepParameters y) β k).1 ≤ 7 * nn) (hdel : 0 < del) (hC₀ : 0 ≤ C₀) (hal : |al k| ≤ 2)
    (hC₁ : 0 ≤ C₁) (hCC : C₁ + wickConstant (C₁ + 1) ≤ C)
    (hCsz : (24 * nn + 1) ^ 4 * ((16 * (2 * logCubeScale (couplingFlow (Tb.stepParameters y) β k).1 + 1) ^ 4) ^ 2 * (2 * C₀ + 2 * C₀)) ≤
      C * nn ^ 4 * Real.log (couplingFlow (Tb.stepParameters y) β k).1 ^ 24)
    {S : ℕ} [NeZero S] :
    ∀ (h : Fin (q + 1) → PlaquetteWeight (fineSide (Tb.stepParameters y).side k S)) (o : TorusSite S)
      (hsites : ∀ i, weightSupportSites (Tb.stepParameters y).side k S (h i) ⊆ supBall o (12 * nn)) (hsup : ∀ i, weightSup (h i) ≤ 1)
      (ka : TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ) (kr : Fin (q + 1) → TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ)
      (κ₀ : Fin (q + 1) → ℝ)
      (Tt : TorusPlaquette S → TorusPlaquette S → ℝ) (hTs : ∀ p p', Tt p p' = Tt p' p)
      (hka : IsLocalKernel (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) del C₀ ka)
      (hkr : ∀ i, IsLocalKernel (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) del (2 * C₀) (kr i))
      (hkz : ∀ i z, z ∉ weightSupportSites (Tb.stepParameters y).side k S (h i) → ∀ p p', kr i z p p' = 0)
      (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (hμ : IsProbabilityMeasure μ) (Φ : Ω → MarkedSample (Tb.stepParameters y) k S)
      (G : Ω → TorusPlaquette S → imaginaryQuaternions) (A B : Set Ω) (Tm : TorusPlaquette S → TorusPlaquette S → ℝ)
      (hA : MeasurableSet A)
      (hcm : ∀ (p : TorusPlaquette S) e, p ∈ plaquettesIn Finset.univ → p.1 ∈ supBall o (19 * nn) →
        AEStronglyMeasurable (Set.indicator A fun ω => imaginaryComponent e (G ω p)) μ)
      (hcb : ∃ Bg : ℝ, ∀ᵐ ω ∂μ, ω ∈ A → ∀ (p : TorusPlaquette S) e, p ∈ plaquettesIn Finset.univ → p.1 ∈ supBall o (19 * nn) →
        |imaginaryComponent e (G ω p)| ≤ Bg)
      (hMo : ∀ (r : ℕ) (p : Fin r → TorusPlaquette S) (e : Fin r → Fin 3), r ≤ 16 →
        (∀ j, p j ∈ plaquettesIn Finset.univ ∧ (p j).1 ∈ supBall o (19 * nn)) →
        Integrable (Set.indicator A fun u => ∏ j, imaginaryComponent (e j) (G u (p j))) μ ∧
        |∫ u, Set.indicator A (fun u => ∏ j, imaginaryComponent (e j) (G u (p j))) u ∂μ -
          (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(r : ℝ) / 2) * wickPairingSum (fun i j => if e i = e j then Tm (p i) (p j) else 0)| ≤
          C₁ * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-((r : ℝ) + 1) / 2 + 2 / 1000))
      (hTb : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite S)), ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite S)),
        p.1 ∈ supBall o (19 * nn) → p'.1 ∈ supBall o (19 * nn) → |Tm p p'| ≤ C₁)
      (hTd : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite S)), ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite S)), |Tm p p' - Tt p p'| ≤ d)
      (hnear : ∀ (i : Fin (q + 1)) (r : ℕ), 1 ≤ r → xq r ≤ (couplingFlow (Tb.stepParameters y) β k).1 →
        ∫⁻ u, ENNReal.ofReal (Set.indicator (A ∩ B) (fun u => |response T β al k S (h i) (Φ u) - κ₀ i -
          (1 / 2) * ∑ z, ∑ p ∈ plaquettesIn Finset.univ, ∑ p' ∈ plaquettesIn Finset.univ,
            (blockMean (Tb.stepParameters y).side k S z (h i) * al k * ka z p p' + kr i z p p') * ∑ e : Fin 3,
              imaginaryComponent e (G u p) * imaginaryComponent e (G u p')| ^ (2 * r)) u) ∂μ ≤
          ENNReal.ofReal ((Cq r * nn ^ 4 * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(3 / 2 : ℝ) + 6 / 1000)) ^ (2 * r)))
      (hrare : μ.real Aᶜ ≤ C * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-P))
      (hrareB : μ.real (A ∩ Bᶜ) ≤ C * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-P))
      (hTr : |cyclicTraceSum (fun i => responseKernel (weightSupportSites (Tb.stepParameters y).side k S (h i))
          (fun z => blockMean (Tb.stepParameters y).side k S z (h i)) (al k)
          (symmetrizeKernel ka) (symmetrizeKernel (kr i))) (fun a b : OrientedPlaquette S => Tt a.1 b.1) - tgt| ≤ err),
      ∃ (I : Type) (_ : Fintype I) (G' : Ω → I → imaginaryQuaternions) (κ : Fin (q + 1) → Matrix I I ℝ) (Tc : Matrix I I ℝ),
        IsLocalQuadraticObservable μ (fun i ω => response T β al k S (h i) (Φ ω)) G' A B κ Tc κ₀ (couplingFlow (Tb.stepParameters y) β k).1 nn C P Cq xq ∧
        |cyclicTraceSum κ Tc - tgt| ≤ err := by
  intro h o hsites hsup ka kr κ₀ Tt hTs hka hkr hkz Ω _ μ hμ Φ G A B Tm hA hcm hcb hMo hTb hTd hnear hrare hrareB hTr
  have hmemP : ∀ a : OrientedPlaquette S, a.1 ∈ plaquettesIn (Finset.univ : Finset (TorusSite S)) := fun a => by
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a.2, fun _ _ => trivial⟩
  set Box : OrientedPlaquette S → Prop := fun a => a.1.1 ∈ supBall o (19 * nn) with hBox
  set hat : Fin (q + 1) → TorusSite S → ℝ := fun i z => blockMean (Tb.stepParameters y).side k S z (h i) with hhatdef
  set Kk : Fin (q + 1) → Matrix (OrientedPlaquette S) (OrientedPlaquette S) ℝ := fun i =>
    responseKernel (weightSupportSites (Tb.stepParameters y).side k S (h i)) (hat i) (al k) ka (kr i) with hKk
  have hhat : ∀ i z, |hat i z| ≤ 1 := fun i z => ((hMean (Tb.stepParameters y).side hodd k S z).1 (h i)).trans (hsup i)
  have hhat0 : ∀ i z, z ∉ weightSupportSites (Tb.stepParameters y).side k S (h i) → hat i z = 0 := by
    intro i z hz
    have hM := hMeans (Tb.stepParameters y).side hodd k S z
    have h1 := hM.2.2 (h i) (fun p => 0 * h i p + 0 * h i p) fun p hp => by
      by_contra hne
      have hne' : h i p ≠ 0 := fun e => hne (by simp [e])
      exact hz (Finset.mem_filter.2 ⟨Finset.mem_univ _, p, hp, hne'⟩)
    have h2 := hM.2.1 0 0 (h i) (h i)
    simp only [hhatdef]
    rw [h1, h2]
    ring
  have hρ0 : 0 ≤ logCubeScale (couplingFlow (Tb.stepParameters y) β k).1 := Nat.cast_nonneg _
  have hK : ∀ i a b, Kk i a b ≠ 0 → Box a ∧ Box b := fun i a b hne =>
    responseKernel_support (weightSupportSites (Tb.stepParameters y).side k S (h i)) (hat i) (hsites i) hka (hkr i) hρ7 a b hne
  have hSz : ∀ i, ∑ a, ∑ b, |Kk i a b| ≤ C * nn ^ 4 * Real.log (couplingFlow (Tb.stepParameters y) β k).1 ^ 24 := fun i =>
    (sum_abs_responseKernel_le o (weightSupportSites (Tb.stepParameters y).side k S (h i)) (hat i) (hsites i) hn0 hρ0 hdel.le hC₀
      (by positivity) (hhat i) hal hka (hkr i)).trans hCsz
  have hC₁' : ∀ (a b : OrientedPlaquette S), Box a → Box b → |Tm a.1 b.1 - Tt a.1 b.1| ≤ d := fun a b _ _ => hTd _ (hmemP a) _ (hmemP b)
  have hform : ∀ i ω, (1 / 2 : ℝ) * ∑ z, ∑ p ∈ plaquettesIn Finset.univ, ∑ p' ∈ plaquettesIn Finset.univ,
      (blockMean (Tb.stepParameters y).side k S z (h i) * al k * ka z p p' + kr i z p p') * ∑ e : Fin 3,
        imaginaryComponent e (G ω p) * imaginaryComponent e (G ω p') =
      quadraticForm (Kk i) (fun a => G ω a.1) := fun i ω =>
    half_sum_eq_quadraticForm (weightSupportSites (Tb.stepParameters y).side k S (h i)) (hat i) (al k) ka (kr i) (hhat0 i) (hkz i) (G ω)
  obtain ⟨r₁, r₂⟩ := localEstimate_of_box hP μ Box (fun i ω => response T β al k S (h i) (Φ ω)) (fun ω a => G ω a.1) A B Kk
    (fun a b => Tm a.1 b.1) (fun a b => Tt a.1 b.1) κ₀ (couplingFlow (Tb.stepParameters y) β k).1 nn C C₁ P d Cq xq hx hd0 hdx hC₁ hCC hA
    (by
      ext a b
      exact hTs b.1 a.1)
    (fun a e hb => hcm a.1 e (hmemP a) hb)
    (by
      obtain ⟨Bg, hBg⟩ := hcb
      refine ⟨Bg, ?_⟩
      filter_upwards [hBg] with ω hω hA' a e hb
      exact hω hA' a.1 e (hmemP a) hb)
    hC₁' (fun a b ha hb => hTb _ (hmemP a) _ (hmemP b) ha hb)
    (fun r a e hr hb => hMo r (fun j => (a j).1) e hr fun j => ⟨hmemP (a j), hb j⟩)
    hK hSz
    (fun i r hr hxr => by
      have := hnear i r hr hxr
      simp only [hform] at this
      exact this)
    hrare hrareB
  refine ⟨_, _, _, _, _, r₁, ?_⟩
  rw [r₂]
  have e : (fun i => symmetrize (Kk i)) = fun i => responseKernel (weightSupportSites (Tb.stepParameters y).side k S (h i))
      (fun z => blockMean (Tb.stepParameters y).side k S z (h i)) (al k) (symmetrizeKernel ka) (symmetrizeKernel (kr i)) := by
    funext i
    exact symmetrize_responseKernel _ _ _ _ _
  rw [e]
  exact hTr
set_option maxHeartbeats 4000000 in
private theorem localEstimate_at_parameters (hP : matchingSumPropertiesStatement) (hLaw : sampleBelowLawStatement)
    (hId : TwoPointByTotalCovarianceStatement) (hMean : WeightsCloseToBlockMeans)
    (hMeans : BlockMeanIsLinearAndLocal) (hLoc : testWeightsLocalStatement) (hfit : (Tb.stepParameters y).Admissible)
    (hfl : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side) (hodd : Odd (Tb.stepParameters y).side)
    (gM : CurvatureMomentsOnBox Tb y)
    (gQ : quadraticResponseAt Tb y)
    (gS : ∃ C : ℝ, ∀ (k d n : ℕ) [NeZero n], Tb.n₀ ≤ n →
      ∃ Tt : TorusPlaquette (fineSide (Tb.stepParameters y).side d n) → TorusPlaquette (fineSide (Tb.stepParameters y).side d n) → ℝ,
        IsMaxwellCovariance Tb.coupling (Tb.stepParameters y).side k Tt ∧
        ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side d n))),
          ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side d n))),
            |accumulatedCovariance Tb.coupling Tb.ρA (Tb.stepParameters y).side k d n (curlFunctional p) (curlFunctional p') - Tt p p'| ≤
              C * (4 : ℝ) ^ (-(d : ℤ)))
    (gX : ∃ C : ℝ, ∀ (k N : ℕ) [NeZero N], Tb.n₀ ≤ N → ∀ Tt : TorusPlaquette N → TorusPlaquette N → ℝ,
      IsMaxwellCovariance Tb.coupling (Tb.stepParameters y).side k Tt →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)), ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)),
        1 ≤ sqNorm (plaquetteCentreDisplacement p p') → sqNorm (plaquetteCentreDisplacement p p') ≤ ((N : ℝ) / 8) ^ 2 →
        |Tt p p' - continuumCurvatureKernel (plaquetteCentreDisplacement p p') p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
          C * (sqNorm (plaquetteCentreDisplacement p p') ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ))))
    (gO : nearIdentityAlongChainAt Tb y)
    (gL : ∃ c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k e N : ℕ) [NeZero N] (nn : ℝ)
      (o : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))),
      N = 2 * (Tb.stepParameters y).side ^ e → IsLocalChainAbove Tb y T β k N nn x₀ →
      MeasureTheory.Measure.real (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 + chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
        {u | ¬ IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o} ≤
        Real.exp (-(c * (couplingFlow (Tb.stepParameters y) β k).1)))
    (gT : responseKernelTracesAt (Tb.stepParameters y)) : localQuadraticEstimateAt Tb y := by
  intro Kr hKr vt hvt0 hvt1 P
  obtain ⟨C₁, x₁, gM⟩ := gM
  obtain ⟨Cq, xq, Cf, del, c, x₂, hdel, hc, gQ⟩ := gQ Kr hKr
  obtain ⟨C₄, gS⟩ := gS
  obtain ⟨C₅, gX⟩ := gX
  obtain ⟨C₆, x₆, gO⟩ := gO P
  obtain ⟨c₇, x₇, hc₇, gL⟩ := gL
  set C₀ := |Cf| + |C₅| + 1 with hC₀def
  have hC₀ : 0 ≤ C₀ := by positivity
  obtain ⟨C₈, x₈, gT⟩ := gT vt del c C₀ hvt0 hvt1 hdel hc
  set C₁' := |C₁| + 1 with hC₁'def
  have hC₁' : 0 ≤ C₁' := by positivity
  set Csz := (25 : ℝ) ^ 4 * (16 ^ 2 * 3 ^ 8) * (4 * C₀) with hCszdef
  have hCsz0 : 0 ≤ Csz := by positivity
  set C := C₁' + wickConstant (C₁' + 1) + Csz + |C₆| + |C₈| + 1 with hCdef
  have hpc := one_le_wickConstant (show 0 ≤ C₁' + 1 by positivity)
  have hE : ∀ᶠ x : ℝ in Filter.atTop, 2 * Real.log ((Tb.stepParameters y).side : ℝ) + 3 ≤ Real.log x ∧ (Tb.n₀ : ℝ) ≤ x ∧ (|C₄| + 1) ^ 2 ≤ x ∧
      Real.log x ^ 3 ≤ x ^ ((1 : ℝ) / 100) ∧ 2 / vt ≤ x ^ ((1 : ℝ) / 100) ∧ Real.exp (-(c₇ * x)) ≤ x ^ (-P) ∧ 1 ≤ x ∧
      x₁ ≤ x ∧ x₂ ≤ x ∧ x₆ ≤ x ∧ x₇ ≤ x ∧ x₈ ≤ x := by
    have t1 := Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log ((Tb.stepParameters y).side : ℝ) + 3)
    have t2 := Filter.eventually_ge_atTop (Tb.n₀ : ℝ)
    have t3 := Filter.eventually_ge_atTop ((|C₄| + 1) ^ 2)
    have t4 := (isLittleO_log_rpow_rpow_atTop (r := 3) (s := 1 / 100) (by norm_num)).def (c := 1) one_pos
    have t5 := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 100 by norm_num)).eventually_ge_atTop (2 / vt)
    have t6 := (isLittleO_exp_neg_mul_rpow_atTop hc₇ (-P)).def (c := 1) one_pos
    filter_upwards [t1, t2, t3, t4, t5, t6, Filter.eventually_ge_atTop (1 : ℝ), Filter.eventually_ge_atTop x₁,
      Filter.eventually_ge_atTop x₂, Filter.eventually_ge_atTop x₆, Filter.eventually_ge_atTop x₇,
      Filter.eventually_ge_atTop x₈] with x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    refine ⟨a1, a2, a3, ?_, a5, ?_, a7, a8, a9, a10, a11, a12⟩
    · have hx0 : 0 < x := by linarith
      have hlog : 0 ≤ Real.log x := Real.log_nonneg a7
      have e1 : ‖Real.log x ^ (3 : ℝ)‖ = Real.log x ^ 3 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _)]
        norm_cast
      have e2 : ‖x ^ ((1 : ℝ) / 100)‖ = x ^ ((1 : ℝ) / 100) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      rw [e1, e2, one_mul] at a4
      exact a4
    · have hx0 : 0 < x := by linarith
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at a6
      simpa using a6
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hE
  refine ⟨Cq, xq, C, x₀, ?_⟩
  intro q β k m n al T Sc tp hq1 hq3 hw hnum hal hk hSK hSflow hSal hstand hcut hcoin f hf
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := hx₀ _ hw.le_coupling
  have hL2 : 2 ≤ (Tb.stepParameters y).side := T.two_le_side
  obtain ⟨hn1, hvn, hρ7, hρ⟩ := scaleWindow_bounds hL2 e1 e4 e5 e7 hvt0 hw.lower_le
  obtain ⟨N, eN, hNe, hNpos, hdiv, hn₀N, hside, hS⟩ := exists_side_of_scaleWindow (M := chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
    hL2 e1 e2 e7 (Nat.floor_le (by positivity)) hw.side_ge
  haveI hNne : NeZero N := ⟨hNpos.ne'⟩
  have hOL : ∀ x' : ℝ, x' ≤ (couplingFlow (Tb.stepParameters y) β k).1 → IsLocalChainAbove Tb y T β k N n x' := fun x' h =>
    ⟨h, hw.flow_ge, hstand, hcut, hcoin, hside, hn1, hw.le_upper⟩
  obtain ⟨hsup, hlip, o, ho⟩ := hLoc (Tb.stepParameters y) hodd m k q n vt f hn1 hvt0 hf
  have hn0 : 0 ≤ n := by linarith
  have hx0 : 0 < (couplingFlow (Tb.stepParameters y) β k).1 := by linarith
  have hLog0 : 0 ≤ Real.log ((Tb.stepParameters y).side : ℝ) := Real.log_nonneg (by
    have : (2 : ℝ) ≤ (Tb.stepParameters y).side := by exact_mod_cast hL2
    linarith)
  have ht3 : 3 ≤ Real.log (couplingFlow (Tb.stepParameters y) β k).1 := by linarith
  have hρ0 : 0 ≤ logCubeScale (couplingFlow (Tb.stepParameters y) β k).1 := Nat.cast_nonneg _
  have hCC : C₁' + wickConstant (C₁' + 1) ≤ C := by
    rw [hCdef]
    have := abs_nonneg C₆
    have := abs_nonneg C₈
    linarith
  have hCsz' : (24 * n + 1) ^ 4 * ((16 * (2 * logCubeScale (couplingFlow (Tb.stepParameters y) β k).1 + 1) ^ 4) ^ 2 * (2 * C₀ + 2 * C₀)) ≤
      C * n ^ 4 * Real.log (couplingFlow (Tb.stepParameters y) β k).1 ^ 24 := by
    refine (kernel_size_arith hn1 hρ0 hρ (by linarith) hC₀).trans ?_
    have h1 : Csz ≤ C := by
      rw [hCdef]
      have := abs_nonneg C₆
      have := abs_nonneg C₈
      linarith
    have h2 : 0 ≤ n ^ 4 := by positivity
    have h3 : 0 ≤ Real.log (couplingFlow (Tb.stepParameters y) β k).1 ^ 24 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) h3
  have hdx := abs_mul_inv_le_rpow e7 e3
  have hd0 : 0 ≤ |C₄| * (couplingFlow (Tb.stepParameters y) β k).1⁻¹ := by positivity
  have hxinv : ((couplingFlow (Tb.stepParameters y) β k).1) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos e7 (by norm_num)
  have key : ∀ (S : ℕ) [NeZero S], fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) = S →
      ∀ (h : Fin (q + 1) → PlaquetteWeight (fineSide (Tb.stepParameters y).side k S)) (o : TorusSite S), (∀ i, weightSup (h i) ≤ 1) →
      (∀ i, weightLipschitz (Tb.stepParameters y).side k (h i) ≤ 2 / (vt * n)) →
      (∀ (i : Fin (q + 1)) (z : TorusSite S) (p : TorusPlaquette (fineSide (Tb.stepParameters y).side k S)), z ∉ supBall o (12 * n) →
        IsPlaquetteAt (Tb.stepParameters y).side k z p → h i p = 0) →
      ∀ tgt err : ℝ,
      (∀ (ka : TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ) (kr : Fin (q + 1) → TorusSite S → TorusPlaquette S → TorusPlaquette S → ℝ)
        (Tc : Matrix (OrientedPlaquette S) (OrientedPlaquette S) ℝ),
        IsLocalKernel (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) del C₀ ka →
        IsNormalizedShareForm (Real.exp (-(c * logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) ka →
        (∀ i, IsLocalKernel (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) del
          (C₀ * ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ)) + 1 / (vt * n))) (kr i)) →
        (∀ p p' : OrientedPlaquette S, 1 ≤ sqNorm (plaquetteCentreDisplacement p.1 p'.1) →
          sqNorm (plaquetteCentreDisplacement p.1 p'.1) ≤ ((S : ℝ) / 8) ^ 2 →
          |Tc p p' - continuumCurvatureKernel (plaquetteCentreDisplacement p.1 p'.1) p.1.2.1 p.1.2.2 p'.1.2.1 p'.1.2.2| ≤
            C₀ * (sqNorm (plaquetteCentreDisplacement p.1 p'.1) ^ (-(5 / 2 : ℝ)) + (S : ℝ) ^ (-(4 : ℤ))) +
              (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(50 : ℝ))) →
        |cyclicTraceSum (fun i => responseKernel (weightSupportSites (Tb.stepParameters y).side k S (h i))
          (fun z => blockMean (Tb.stepParameters y).side k S z (h i)) (al k) ka (kr i)) Tc - tgt| ≤ err) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ) (Φ : Ω → MarkedSample (Tb.stepParameters y) k S) (I : Type)
        (_ : Fintype I) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω) (κ : Fin (q + 1) → Matrix I I ℝ) (Tc : Matrix I I ℝ) (c : Fin (q + 1) → ℝ),
        Measurable Φ ∧ Measure.map Φ μ = markedSampleLaw T β k S ∧
        IsLocalQuadraticObservable μ (fun i ω => response T β al k S (h i) (Φ ω)) G A B κ Tc c (couplingFlow (Tb.stepParameters y) β k).1 n C P Cq xq ∧
        |cyclicTraceSum κ Tc - tgt| ≤ err := by
    intro S _ hS'
    subst hS'
    intro h o hsup hlip ho tgt err hTr
    obtain ⟨hAm, hcm, hMo, hTb⟩ := gM T β k N n o eN hNe (hOL x₁ e8)
    obtain ⟨ka, hka, hform, hrest⟩ := gQ T Sc β k tp N n vt al o (hOL x₂ e9) hdiv hnum hal hk hSK hSflow hSal hvt0 hvt1 hvn
    choose κ₀ kr hkr hz hnr using fun i => hrest (h i) (hsup i) (hlip i) (ho i)
    have hn₀1 : Tb.n₀ ≤ fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N := by
      rw [fineSide_eq]
      exact hn₀N.trans (Nat.le_mul_of_pos_right _ (by positivity))
    have hn₀2 : Tb.n₀ ≤ fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) := by
      rw [fineSide_eq (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)]
      exact hn₀1.trans (Nat.le_mul_of_pos_right _ (by positivity))
    obtain ⟨Tt, hTt, hclose⟩ := gS k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) hn₀1
    have hXm := gX k _ hn₀2 Tt hTt
    have hμ : IsProbabilityMeasure (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) :=
      (hId (Tb.stepParameters y) hfit hfl T hcut hcoin β al _ N).1
    obtain ⟨hb1, hb2⟩ := (hLaw (Tb.stepParameters y) hfit hfl T hcut hcoin β al).1 (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N
    obtain ⟨hb3, hb4⟩ := (hLaw (Tb.stepParameters y) hfit hfl T hcut hcoin β al).1 k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
    have hΦ : Measurable fun u => sampleBelow (Tb.stepParameters y) k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) _
        (sampleBelow (Tb.stepParameters y) (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u) := hb3.comp hb1
    have hmap : Measure.map (fun u => sampleBelow (Tb.stepParameters y) k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) _
        (sampleBelow (Tb.stepParameters y) (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u))
        (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 + chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) =
        markedSampleLaw T β k _ := by
      have h1 := Measure.map_map (μ := markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) hb3 hb1
      rw [hb2, hb4] at h1
      exact h1.symm
    have hsites : ∀ i, weightSupportSites (Tb.stepParameters y).side k _ (h i) ⊆ supBall o (12 * n) := by
      intro i z hz'
      obtain ⟨p, hp, hne⟩ := (Finset.mem_filter.1 hz').2
      by_contra hc'
      exact hne (ho i z p hc' hp)
    have hkr' : ∀ i, IsLocalKernel (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) del
        (C₀ * ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ)) + 1 / (vt * n))) (kr i) := by
      intro i
      refine (hkr i).mono_size (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have := le_abs_self Cf
      have := abs_nonneg C₅
      rw [hC₀def]
      linarith
    have hkr2 : ∀ i, IsLocalKernel (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) del (2 * C₀) (kr i) := by
      intro i
      refine (hkr' i).mono_size ?_
      have h1 : 1 / (vt * n) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      nlinarith
    have hka' : IsLocalKernel (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) del C₀ ka := hka.mono_size (by
      have := le_abs_self Cf
      have := abs_nonneg C₅
      rw [hC₀def]
      linarith)
    have hTs : ∀ p p', Tt p p' = Tt p' p := hTt.1
    have hd : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite _)), ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite _)),
        |accumulatedCovariance Tb.coupling Tb.ρA (Tb.stepParameters y).side k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
          (curlFunctional p) (curlFunctional p') - Tt p p'| ≤ |C₄| * (couplingFlow (Tb.stepParameters y) β k).1⁻¹ := by
      intro p hp p' hp'
      refine (hclose p hp p' hp').trans ?_
      have h1 := four_zpow_neg_chainDepth_le hx0 (by linarith)
      have h2 := le_abs_self C₄
      have h3 : (0 : ℝ) < (4 : ℝ) ^ (-(chainDepth (couplingFlow (Tb.stepParameters y) β k).1 : ℤ)) := zpow_pos (by norm_num) _
      calc C₄ * (4 : ℝ) ^ (-(chainDepth (couplingFlow (Tb.stepParameters y) β k).1 : ℤ)) ≤
            |C₄| * (4 : ℝ) ^ (-(chainDepth (couplingFlow (Tb.stepParameters y) β k).1 : ℤ)) :=
            mul_le_mul_of_nonneg_right h2 h3.le
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have hC1le : C₁ ≤ C₁' := by
      have := le_abs_self C₁
      rw [hC₁'def]
      linarith
    have hrare₁ := gL T β k (eN + 1) N n o hNe (hOL x₇ e11)
    have hrare₂ := gO T β k N n o (hOL x₆ e10) hdiv
    have hpow0 : 0 < (couplingFlow (Tb.stepParameters y) β k).1 ^ (-P) := Real.rpow_pos_of_pos hx0 _
    have hC1 : 1 ≤ C := by
      rw [hCdef]
      have := abs_nonneg C₆
      have := abs_nonneg C₈
      linarith
    have hC6 : C₆ ≤ C := by
      have := le_abs_self C₆
      have := abs_nonneg C₈
      rw [hCdef]
      linarith
    have hmemP : ∀ a : OrientedPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)),
        a.1 ∈ plaquettesIn (Finset.univ : Finset (TorusSite _)) := fun a => by
      simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a.2, fun _ _ => trivial⟩
    have hTc : ∀ p p' : OrientedPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)),
        1 ≤ sqNorm (plaquetteCentreDisplacement p.1 p'.1) →
        sqNorm (plaquetteCentreDisplacement p.1 p'.1) ≤
          (((fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
            (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) : ℕ) : ℝ) / 8) ^ 2 →
        |Tt p.1 p'.1 - continuumCurvatureKernel (plaquetteCentreDisplacement p.1 p'.1) p.1.2.1 p.1.2.2 p'.1.2.1 p'.1.2.2| ≤
          C₀ * (sqNorm (plaquetteCentreDisplacement p.1 p'.1) ^ (-(5 / 2 : ℝ)) +
            ((fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
              (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) : ℕ) : ℝ) ^ (-(4 : ℤ))) +
            (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(50 : ℝ)) := by
      intro p p' a b
      refine (hXm p.1 (hmemP p) p'.1 (hmemP p') a b).trans ?_
      have h0 : 0 ≤ sqNorm (plaquetteCentreDisplacement p.1 p'.1) ^ (-(5 / 2 : ℝ)) +
          ((fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
            (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) : ℕ) : ℝ) ^ (-(4 : ℤ)) :=
        add_nonneg (Real.rpow_nonneg (by linarith) _) (zpow_nonneg (Nat.cast_nonneg _) _)
      have h1 : C₅ ≤ C₀ := by
        have := le_abs_self C₅
        have := abs_nonneg Cf
        rw [hC₀def]
        linarith
      have h2 : 0 ≤ (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(50 : ℝ)) := Real.rpow_nonneg hx0.le _
      have h3 := mul_le_mul_of_nonneg_right h1 h0
      linarith
    have hcb : ∃ Bg : ℝ, ∀ᵐ ω ∂(markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N),
        ω ∈ {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o} →
        ∀ (p : TorusPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))) (e : Fin 3),
        p ∈ plaquettesIn Finset.univ → p.1 ∈ supBall o (19 * n) →
        |imaginaryComponent e (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) n
          (couplingFlow (Tb.stepParameters y) β k).1 N ω o p)| ≤ Bg := by
      refine ⟨C₁, ?_⟩
      have hall : ∀ (p : TorusPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))) (e : Fin 3),
          ∀ᵐ ω ∂(markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
            chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N),
          IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N ω o →
            p ∈ plaquettesIn Finset.univ → p.1 ∈ supBall o (19 * n) →
          |imaginaryComponent e (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) n
            (couplingFlow (Tb.stepParameters y) β k).1 N ω o p)| ≤ C₁ := by
        intro p e
        by_cases hp : p ∈ plaquettesIn Finset.univ ∧ p.1 ∈ supBall o (19 * n)
        · filter_upwards [(hcm p e hp.1 hp.2).2] with ω hω h1 _ _
          exact hω h1
        · exact Filter.Eventually.of_forall fun ω _ a b => absurd ⟨a, b⟩ hp
      filter_upwards [ae_all_iff.2 fun p => ae_all_iff.2 fun e => hall p e] with ω hω h1 p e a b
      exact hω p e h1 a b
    obtain ⟨I, iI, G', κ, Tc, hr, hb⟩ := localEstimate_at_side Tb y hP hMean hMeans hodd (del := del) (C₀ := C₀) (C₁ := C₁') (C := C)
      (d := |C₄| * (couplingFlow (Tb.stepParameters y) β k).1⁻¹) (P := P) (tgt := tgt) (err := err) Cq xq T β k n al e7 hd0 hdx hn0 hρ7
      hdel hC₀ hal hC₁' hCC hCsz'
      h o hsites hsup ka kr κ₀ Tt hTs hka' hkr2 hz
      (MarkedSample (Tb.stepParameters y) (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) _ hμ
      (fun u => sampleBelow (Tb.stepParameters y) k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) _
        (sampleBelow (Tb.stepParameters y) (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u))
      (fun u p => sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) n (couplingFlow (Tb.stepParameters y) β k).1 N u o p)
      {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o}
      {u | IsGaugeSmallAlong T k n (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1)
        ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 4 : ℝ))) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
        (sampleBelow (Tb.stepParameters y) (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u) o
        (axialGaugeAt (Tb.stepParameters y) (topField (Tb.stepParameters y) (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
          (sampleBelow (Tb.stepParameters y) (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
            (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u))
          (siteAbove (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
            (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) o))}
      (fun p p' => accumulatedCovariance Tb.coupling Tb.ρA (Tb.stepParameters y).side k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
        (curlFunctional p) (curlFunctional p'))
      hAm (fun p e a b => (hcm p e a b).1) hcb
      (fun r p e hr hj => ⟨(hMo r p e hr hj).1, (hMo r p e hr hj).2.trans
        (mul_le_mul_of_nonneg_right hC1le (Real.rpow_nonneg hx0.le _))⟩)
      (fun p hp p' hp' a b => (hTb p hp p' hp' a b).trans hC1le) hd
      (fun i r hr hxr => hnr i r hr hxr)
      (hrare₁.trans (e6.trans (le_mul_of_one_le_left hpow0.le hC1)))
      (hrare₂.trans (mul_le_mul_of_nonneg_right hC6 hpow0.le))
      (hTr (symmetrizeKernel ka) (fun i => symmetrizeKernel (kr i)) (fun a b => Tt a.1 b.1) (isLocalKernel_symmetrizeKernel hka')
        (isNormalizedShareForm_symmetrizeKernel (hform))
        (fun i => isLocalKernel_symmetrizeKernel (hkr' i)) hTc)
    exact ⟨_, _, _, hμ, _, I, iI, G', _, _, κ, Tc, κ₀, hΦ, hmap, hr, hb⟩
  have hcast : ((2 * (Tb.stepParameters y).side ^ m : ℕ) : ℝ) = 2 * ((Tb.stepParameters y).side : ℝ) ^ m := by
    push_cast
    ring
  refine key (2 * (Tb.stepParameters y).side ^ m) hS (fun i => testWeight (Tb.stepParameters y).side k m (f i)) o hsup hlip ho _ _
    fun ka kr Tc h₁ h₂ h₃ h₄ => ?_
  refine (gT q k m (couplingFlow (Tb.stepParameters y) β k).1 n (al k) f ka kr Tc hq1 hq3 e12 hw.lower_le hw.le_upper hw.side_ge hal hf h₁ h₂ h₃
    (fun p p' a b => ?_)).trans ?_
  · have := h₄ p p' a (by rw [hcast]; exact b)
    rw [hcast] at this
    exact this
  · have h1 : C₈ ≤ C := by
      have := le_abs_self C₈
      have := abs_nonneg C₆
      rw [hCdef]
      linarith
    have h2 : 0 ≤ (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ)) + 1 / n :=
      add_nonneg (Real.rpow_nonneg hx0.le _) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 h2
end Table
section ParameterChoices
private theorem holdsOnParameters_and {P Q : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P)
    (hQ : HoldsOnParameterFamilies Q) : HoldsOnParameterFamilies fun T y => P T y ∧ Q T y := by apply _root_.YangMills.SharedProofs.p24215 <;> assumption
private theorem holdsOnParameters_mono {P Q : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P)
    (h : ∀ T y, P T y → Q T y) : HoldsOnParameterFamilies Q := by apply _root_.YangMills.SharedProofs.p25084 <;> assumption
private theorem holdsOnParameters_odd_side : HoldsOnParameterFamilies fun T y => Odd (T.stepParameters y).side := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L hodd _ T _ hTL _ _ _ _ _ => ⟨0, fun y _ _ _ => ?_⟩⟩
  show Odd T.side
  rw [hTL]
  exact hodd
private theorem curvatureMomentsOnBox_holds (hMo : levelCurvatureMomentsStatement) : HoldsOnParameterFamilies CurvatureMomentsOnBox := by
  refine holdsOnParameters_mono hMo fun Tb y g => ?_
  choose Cf xf g using g
  have hC : ∀ r, r ≤ 16 → Cf r ≤ ∑ j ∈ Finset.range 17, |Cf j| := fun r hr =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cf j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  have hX : ∀ r, r ≤ 16 → xf r ≤ ∑ j ∈ Finset.range 17, |xf j| := fun r hr =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |xf j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  have hX0 : 0 ≤ ∑ j ∈ Finset.range 17, |xf j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ j ∈ Finset.range 17, |Cf j|, ∑ j ∈ Finset.range 17, |xf j| + 1, fun T β k N _ nn o w hNw hOL => ?_⟩
  have hx1 : 0 ≤ (couplingFlow (Tb.stepParameters y) β k).1 := by
    have := hOL.floor_le
    linarith
  have hfl : ∀ r, r ≤ 16 → IsLocalChainAbove Tb y T β k N nn (xf r) := fun r hr =>
    ⟨by
      have := hOL.floor_le
      have := hX r hr
      linarith, hOL.coupling_ge, hOL.onFamily, hOL.cutoff, hOL.measurable, hOL.side_ge, hOL.one_le, hOL.le_rpow⟩
  refine ⟨(g 0 T β k N nn o Fin.elim0 Fin.elim0 w hNw (hfl 0 (by omega)) fun j => j.elim0).1, ?_, ?_, ?_⟩
  · intro p e hp hb
    have h1 := g 1 T β k N nn o (fun _ => p) (fun _ => e) w hNw (hfl 1 (by omega)) fun _ => ⟨hp, hb⟩
    refine ⟨h1.2.1 0, ?_⟩
    filter_upwards [h1.2.2.1] with u hu h2
    exact (hu h2 0).trans (hC 1 (by omega))
  · intro r p e hr hj
    have h1 := g r T β k N nn o p e w hNw (hfl r hr) hj
    exact ⟨h1.2.2.2.2.1, h1.2.2.2.2.2.trans (mul_le_mul_of_nonneg_right (hC r hr) (Real.rpow_nonneg hx1 _))⟩
  · intro p hp p' hp' hb hb'
    have h1 := g 2 T β k N nn o ![p, p'] ![0, 0] w hNw (hfl 2 (by omega)) (by
      intro j
      fin_cases j
      · exact ⟨hp, hb⟩
      · exact ⟨hp', hb'⟩)
    exact (h1.2.2.2.1 0 1 rfl).trans (hC 2 (by omega))
end ParameterChoices
theorem localQuadraticEstimateStatement_holds (hP : matchingSumPropertiesStatement) (hLaw : sampleBelowLawStatement)
    (hId : TwoPointByTotalCovarianceStatement) (hMean : WeightsCloseToBlockMeans)
    (hMeans : BlockMeanIsLinearAndLocal) (hLoc : testWeightsLocalStatement) (hWin : windowTowerExistsStatement)
    (hMo : levelCurvatureMomentsStatement) (hQu : quadraticResponseStatement)
    (hSt : StepCovariancesSumToMaxwellStatement) (hMx : maxwellCovarianceLongDistanceStatement)
    (hOm : nearIdentityAlongChainStatement) (hLe : localEventLikelyStatement)
    (hTr : responseKernelTracesStatement) : localQuadraticEstimateStatement := by
  have H := holdsOnParameters_and (holdsOnParameters_and (holdsOnParameters_and (holdsOnParameters_and
    (holdsOnParameters_and (holdsOnParameters_and (holdsOnParameters_and (holdsOnParameters_and hWin
    holdsOnParameters_odd_side) (curvatureMomentsOnBox_holds hMo)) hQu) hSt) hMx) hOm) hLe) hTr
  exact holdsOnParameters_mono H fun Tb y ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2, _⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ =>
    localEstimate_at_parameters Tb y hP hLaw hId hMean hMeans hLoc a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
end YangMills.Construction.ResponseInTheExpansion
end
