import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfGProof
import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjectionsProof
import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernelProof
import YangMills.Construction.TransferOperators.FieldsKeepProductCoefficientSpaces
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsOfAProductIsAProductProof
import YangMills.Construction.TransferOperators.RapidDecayGivesASmoothFunction
import YangMills.Construction.TransferOperators.SmoothFunctionsDecayRapidly
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.HilbertSpaceBasics
open YangMills.Construction.SpinHarmonics.SeveralVariables
open YangMills.Construction.TransferOperators.GibbsHaarKernels
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SpinHarmonics.SmoothToSobolevDecayProof
section Smooth
variable {J : Type}
theorem continuous_of_mem_smoothSet {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) :
    Continuous F :=
  Set.mem_iInter.1 hF 0
theorem smoothOrder_one_of_mem {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) :
    F ∈ smoothOrder 1 :=
  Set.mem_iInter.1 hF 1
theorem rightField_mem_smoothSet {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) (b : J)
    (i : Fin 3) : rightField b i F ∈ smoothSet := by apply _root_.YangMills.Construction.SpinHarmonics.FieldCalculus.rightField_mem_smoothSet <;> assumption
end Smooth
section Classes
variable {J : Type} [Finite J]
theorem memLp_two_of_continuous {F : (J → specialUnitary) → ℂ} (hF : Continuous F) :
    MemLp F 2 (haarPi J) := by apply _root_.YangMills.Construction.TransferOperators.SandwichProduct.memLp_two_of_continuous <;> assumption
theorem toHaarL2_coeFn_ae {F : (J → specialUnitary) → ℂ} (hF : Continuous F) :
    (toHaarL2 F : (J → specialUnitary) → ℂ) =ᵐ[haarPi J] F := by
  rw [toHaarL2, dif_pos (memLp_two_of_continuous hF)]
  exact MemLp.coeFn_toLp _
theorem toHaarL2_eq_toLp (f : C(J → specialUnitary, ℂ)) :
    toHaarL2 (f : (J → specialUnitary) → ℂ) =
      ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ f := by apply _root_.YangMills.Construction.SpinHarmonics.IsotypicPartSums.toHaarL2_continuousMap <;> assumption
theorem toHaarL2_smul (c : ℂ) (f : C(J → specialUnitary, ℂ)) :
    toHaarL2 ((c • f : C(J → specialUnitary, ℂ)) : (J → specialUnitary) → ℂ) =
      c • toHaarL2 (f : (J → specialUnitary) → ℂ) := by
  rw [toHaarL2_eq_toLp, toHaarL2_eq_toLp, map_smul]
theorem inner_peterWeylVec_toHaarL2 (α : PeterWeylIndex J) {F : (J → specialUnitary) → ℂ}
    (hF : Continuous F) :
    (inner ℂ (peterWeylVec α) (toHaarL2 F) : ℂ) =
      ∫ u, star (peterWeylFn α u) * F u ∂haarPi J := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [toHaarL2_coeFn_ae hF, ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
    (haarPi J) (peterWeylFn α)] with u h₁ h₂
  have h₃ : (peterWeylVec α : (J → specialUnitary) → ℂ) u = peterWeylFn α u := h₂
  rw [h₁, h₃, RCLike.inner_apply, mul_comm]
  rfl
theorem integrable_of_continuous_on_power {F : (J → specialUnitary) → ℂ} (hF : Continuous F) :
    Integrable F (haarPi J) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
end Classes
theorem norm_map_le_of_isOrthProjOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsOrthProjOp P) (x : E) :
    ‖P x‖ ≤ ‖x‖ := by
  obtain ⟨h₁, h₂⟩ := hP
  have hin : (inner ℂ (P x) (P x) : ℂ) = inner ℂ x (P x) := by
    have hs : (inner ℂ (P x) (P x) : ℂ) = inner ℂ x (P (P x)) := by
      conv_lhs => rw [h₁]
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      simp only [← ContinuousLinearMap.star_eq_adjoint, ← h₁]
    have hq : P (P x) = P x := by
      have := congrArg (fun A : E →L[ℂ] E => A x) h₂
      exact this.symm
    rw [hs, hq]
  have hn : ‖P x‖ * ‖P x‖ ≤ ‖x‖ * ‖P x‖ := by
    have h₃ : ‖(inner ℂ (P x) (P x) : ℂ)‖ = ‖P x‖ * ‖P x‖ := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two]
    rw [← h₃, hin]
    exact norm_inner_le_norm x (P x)
  by_cases h0 : ‖P x‖ = 0
  · rw [h0]
    exact norm_nonneg x
  · exact le_of_mul_le_mul_right hn (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))
section Laplacian
variable {J : Type} [Fintype J]
def oneSubLaplacian (F : (J → specialUnitary) → ℂ) : (J → specialUnitary) → ℂ :=
  fun u => F u - ∑ b, ∑ i, rightField b i (rightField b i F) u
def casimirTotal (l : J → HalfNatural) : ℝ := ∑ b, (l b).toReal * ((l b).toReal + 1)
theorem halfNatural_toReal_nonneg (t : HalfNatural) : 0 ≤ t.toReal := by apply _root_.YangMills.Construction.TransferOperators.SqrtLinkFacts.halfNatural_toReal_nonneg <;> assumption
theorem casimirTotal_nonneg (l : J → HalfNatural) : 0 ≤ casimirTotal l :=
  Finset.sum_nonneg fun b _ =>
    mul_nonneg (halfNatural_toReal_nonneg _) (by linarith [halfNatural_toReal_nonneg (l b)])
theorem weightSum_eq_sum (l : J → HalfNatural) : weightSum l = ∑ b, (l b).toReal :=
  finsum_eq_sum_of_fintype _
theorem weightSum_nonneg (l : J → HalfNatural) : 0 ≤ weightSum l := by
  rw [weightSum_eq_sum]
  exact Finset.sum_nonneg fun b _ => halfNatural_toReal_nonneg _
theorem one_add_weightSum_sq_le [Nonempty J] (l : J → HalfNatural) :
    (1 + weightSum l) ^ 2 ≤ 2 * (Fintype.card J : ℝ) * (1 + casimirTotal l) := by
  have hn : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hcs : (∑ b, (l b).toReal) ^ 2 ≤ (Fintype.card J : ℝ) * ∑ b, (l b).toReal ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun b => (l b).toReal)
  have hsq : ∑ b, (l b).toReal ^ 2 ≤ casimirTotal l :=
    Finset.sum_le_sum fun b _ => by nlinarith [halfNatural_toReal_nonneg (l b)]
  rw [weightSum_eq_sum]
  set t := ∑ b, (l b).toReal
  have h₁ : t ^ 2 ≤ (Fintype.card J : ℝ) * casimirTotal l :=
    hcs.trans (mul_le_mul_of_nonneg_left hsq (by linarith))
  nlinarith [sq_nonneg (1 - t)]
variable (hC : FieldCalculus.AllRules) [Nonempty J]
include hC
theorem oneSubLaplacian_mem_smoothSet {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) :
    oneSubLaplacian F ∈ smoothSet := by
  obtain ⟨⟨A, hA⟩, -⟩ := (hC.2.2 J).2.1 ⊤
  have hA' : (A : Set ((J → specialUnitary) → ℂ)) = smoothSet := by
    simpa [smoothOfENatOrder] using hA
  have hmem : ∀ {G : (J → specialUnitary) → ℂ}, G ∈ smoothSet → G ∈ A := fun {G} hG => by
    rw [← hA'] at hG
    exact hG
  have hform : oneSubLaplacian F = F - ∑ b, ∑ i, rightField b i (rightField b i F) := by
    funext u
    simp [oneSubLaplacian, Finset.sum_apply]
  have h : oneSubLaplacian F ∈ A := by
    rw [hform]
    exact A.sub_mem (hmem hF) (A.sum_mem fun b _ => A.sum_mem fun i _ =>
      hmem (rightField_mem_smoothSet (rightField_mem_smoothSet hF b i) b i))
  rw [← hA']
  exact h
theorem iterate_oneSubLaplacian_mem {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet)
    (k : ℕ) : (oneSubLaplacian^[k] F) ∈ smoothSet := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact oneSubLaplacian_mem_smoothSet hC ih
theorem integral_star_mul_rightField_rightField {φ F : (J → specialUnitary) → ℂ}
    (hφ : φ ∈ smoothSet) (hF : F ∈ smoothSet) (b : J) (i : Fin 3) :
    ∫ u, star (φ u) * rightField b i (rightField b i F) u ∂haarPi J =
      ∫ u, star (rightField b i (rightField b i φ) u) * F u ∂haarPi J := by
  have hskew := (hC.2.2 J).2.2.2.2.2.2.1
  have h₁ := (hskew b i φ (rightField b i F) (smoothOrder_one_of_mem hφ)
    (smoothOrder_one_of_mem (rightField_mem_smoothSet hF b i))).2
  have h₂ := (hskew b i (rightField b i φ) F
    (smoothOrder_one_of_mem (rightField_mem_smoothSet hφ b i)) (smoothOrder_one_of_mem hF)).2
  rw [h₂, h₁, neg_neg]
theorem integral_star_mul_oneSubLaplacian {φ F : (J → specialUnitary) → ℂ}
    (hφ : φ ∈ smoothSet) (hF : F ∈ smoothSet) (c : J → ℝ)
    (hc : ∀ (b : J) (u : J → specialUnitary),
      -∑ i, rightField b i (rightField b i φ) u = (c b : ℂ) * φ u) :
    ∫ u, star (φ u) * oneSubLaplacian F u ∂haarPi J =
      ((1 + ∑ b, c b : ℝ) : ℂ) * ∫ u, star (φ u) * F u ∂haarPi J := by
  have hφc := continuous_of_mem_smoothSet hφ
  have hint : ∀ {G : (J → specialUnitary) → ℂ}, G ∈ smoothSet →
      Integrable (fun u => star (φ u) * G u) (haarPi J) := fun hG =>
    integrable_of_continuous_on_power (hφc.star.mul (continuous_of_mem_smoothSet hG))
  have hint' : ∀ {G G' : (J → specialUnitary) → ℂ}, G ∈ smoothSet → G' ∈ smoothSet →
      Integrable (fun u => star (G u) * G' u) (haarPi J) := fun hG hG' =>
    integrable_of_continuous_on_power
      ((continuous_of_mem_smoothSet hG).star.mul (continuous_of_mem_smoothSet hG'))
  have hff : ∀ (b : J) (i : Fin 3), rightField b i (rightField b i F) ∈ smoothSet := fun b i =>
    rightField_mem_smoothSet (rightField_mem_smoothSet hF b i) b i
  have hfφ : ∀ (b : J) (i : Fin 3), rightField b i (rightField b i φ) ∈ smoothSet := fun b i =>
    rightField_mem_smoothSet (rightField_mem_smoothSet hφ b i) b i
  have hb : ∀ b : J, ∑ i, ∫ u, star (φ u) * rightField b i (rightField b i F) u ∂haarPi J =
      -((c b : ℂ) * ∫ u, star (φ u) * F u ∂haarPi J) := by
    intro b
    simp only [integral_star_mul_rightField_rightField hC hφ hF b]
    rw [← integral_finsetSum _ fun i _ => hint' (hfφ b i) hF, ← integral_const_mul,
      ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have hu := hc b u
    have hs : ∑ i, rightField b i (rightField b i φ) u = -((c b : ℂ) * φ u) := by
      rw [← hu, neg_neg]
    simp only [← Finset.sum_mul, ← star_sum, hs]
    simp [mul_assoc]
  have hexp : (fun u => star (φ u) * oneSubLaplacian F u) =
      fun u => star (φ u) * F u - ∑ b, ∑ i, star (φ u) * rightField b i (rightField b i F) u := by
    funext u
    simp only [oneSubLaplacian, mul_sub, Finset.mul_sum]
  rw [hexp, integral_sub (hint hF)
    (integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun i _ => hint (hff b i)),
    integral_finsetSum _ fun b _ => integrable_finsetSum _ fun i _ => hint (hff b i)]
  simp only [integral_finsetSum _ fun i _ => hint (hff _ i), hb]
  push_cast
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring
end Laplacian
section Components
variable {J : Type} [Fintype J] [Nonempty J]
theorem inner_toHaarL2_iterate (hC : FieldCalculus.AllRules)
    (hS : SeveralVariables.SeveralVariablesFacts) (hF : FieldsPreserveIsotypicSpans.Statement)
    {G : (J → specialUnitary) → ℂ} (hG : G ∈ smoothSet) (l : J → HalfNatural)
    (α : PeterWeylIndex J) (hα : spins α = l) (k : ℕ) :
    (inner ℂ (peterWeylVec α) (toHaarL2 (oneSubLaplacian^[k] G)) : ℂ) =
      ((1 + casimirTotal l : ℝ) : ℂ) ^ k * inner ℂ (peterWeylVec α) (toHaarL2 G) := by
  have hfacts := hS J l ⟨0⟩
  have hmem : peterWeylFn α ∈ prodCoeffSpan l := by
    rw [← hfacts.1.2.2.1]
    exact Submodule.subset_span ⟨α, hα, rfl⟩
  have hpoly : IsEntryPolynomial (peterWeylFn α : (J → specialUnitary) → ℂ) :=
    hfacts.2.2.2.2.2.1.2.1 _ hmem
  have hsm : (peterWeylFn α : (J → specialUnitary) → ℂ) ∈ smoothSet :=
    (hC.2.2 J).2.2.2.2.2.1.1 _ hpoly
  have hcas := fun (b : J) (u : J → specialUnitary) => (hF J l (peterWeylFn α) hmem).2.1 b u
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := iterate_oneSubLaplacian_mem hC hG k
    rw [Function.iterate_succ_apply',
      inner_peterWeylVec_toHaarL2 α
        (continuous_of_mem_smoothSet (oneSubLaplacian_mem_smoothSet hC hk)),
      integral_star_mul_oneSubLaplacian hC hsm hk
        (fun b => (l b).toReal * ((l b).toReal + 1)) hcas,
      ← inner_peterWeylVec_toHaarL2 α (continuous_of_mem_smoothSet hk), ih, pow_succ]
    simp only [casimirTotal]
    ring
theorem isotypicPartSum_iterate (hC : FieldCalculus.AllRules)
    (hS : SeveralVariables.SeveralVariablesFacts) (hF : FieldsPreserveIsotypicSpans.Statement)
    {G : (J → specialUnitary) → ℂ} (hG : G ∈ smoothSet) (l : J → HalfNatural) (k : ℕ) :
    isotypicPartSum l (toHaarL2 (oneSubLaplacian^[k] G)) =
      (((1 + casimirTotal l : ℝ) : ℂ) ^ k) • isotypicPartSum l (toHaarL2 G) := by
  simp only [isotypicPartSum, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hw : spins α = l := (finite_indicesWithSpins l).mem_toFinset.1 hα
  rw [inner_toHaarL2_iterate hC hS hF hG l α hw k]
theorem pow_mul_norm_isotypicProj_le (hC : FieldCalculus.AllRules)
    (hS : SeveralVariables.SeveralVariablesFacts) (hF : FieldsPreserveIsotypicSpans.Statement)
    (hK : IsotypicPartSums.Statement)
    {G : (J → specialUnitary) → ℂ} (hG : G ∈ smoothSet) (l : J → HalfNatural) (k : ℕ) :
    (1 + casimirTotal l) ^ k * ‖isotypicProj l (toHaarL2 G)‖ ≤
      ‖toHaarL2 (oneSubLaplacian^[k] G)‖ := by
  have hproj : IsOrthProjOp (isotypicProj l) :=
    (hS J l ⟨0⟩).1.2.2.2.2.2.1.1
  have hcl := fun V : HaarL2 J => ((hK J).1 l V).2.2
  have heq : isotypicProj l (toHaarL2 (oneSubLaplacian^[k] G)) =
      (((1 + casimirTotal l : ℝ) : ℂ) ^ k) • isotypicProj l (toHaarL2 G) := by
    rw [← hcl, ← hcl, isotypicPartSum_iterate hC hS hF hG l k, toHaarL2_smul]
  have hpos : 0 ≤ 1 + casimirTotal l := by linarith [casimirTotal_nonneg l]
  have hnorm : ‖(((1 + casimirTotal l : ℝ) : ℂ) ^ k)‖ = (1 + casimirTotal l) ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos]
  calc (1 + casimirTotal l) ^ k * ‖isotypicProj l (toHaarL2 G)‖
      = ‖isotypicProj l (toHaarL2 (oneSubLaplacian^[k] G))‖ := by
        rw [heq, norm_smul, hnorm]
    _ ≤ _ := norm_map_le_of_isOrthProjOp hproj _
theorem sobolevDecay_lt_top (hC : FieldCalculus.AllRules)
    (hS : SeveralVariables.SeveralVariablesFacts) (hF : FieldsPreserveIsotypicSpans.Statement)
    (hK : IsotypicPartSums.Statement)
    {G : (J → specialUnitary) → ℂ} (hG : G ∈ smoothSet) (q : ℕ) :
    sobolevDecay q (toHaarL2 G) < ∞ := by
  refine lt_of_le_of_lt (b := ENNReal.ofReal ((2 * (Fintype.card J : ℝ)) ^ q *
    ‖toHaarL2 (oneSubLaplacian^[q] G)‖)) (iSup_le fun l => ENNReal.ofReal_le_ofReal ?_)
    ENNReal.ofReal_lt_top
  have hw : 1 ≤ 1 + weightSum l := by linarith [weightSum_nonneg l]
  have hnorm := norm_nonneg (isotypicProj l (toHaarL2 G))
  have hpow : (1 + weightSum l) ^ q ≤ (2 * (Fintype.card J : ℝ) * (1 + casimirTotal l)) ^ q :=
    calc (1 + weightSum l) ^ q ≤ ((1 + weightSum l) ^ 2) ^ q := by
          refine pow_le_pow_left₀ (by linarith) ?_ q
          nlinarith
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (one_add_weightSum_sq_le l) q
  calc (1 + weightSum l) ^ q * ‖isotypicProj l (toHaarL2 G)‖
      ≤ (2 * (Fintype.card J : ℝ) * (1 + casimirTotal l)) ^ q *
          ‖isotypicProj l (toHaarL2 G)‖ := mul_le_mul_of_nonneg_right hpow hnorm
    _ = (2 * (Fintype.card J : ℝ)) ^ q *
          ((1 + casimirTotal l) ^ q * ‖isotypicProj l (toHaarL2 G)‖) := by
        rw [mul_pow]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_mul_norm_isotypicProj_le hC hS hF hK hG l q)
        (by positivity)
end Components
theorem smoothToSobolevDecay (hD : SobolevDecayToSmoothStatement)
    (hF : FieldsPreserveIsotypicSpans.Statement)
    (hK : IsotypicPartSums.Statement)
    (hC : FieldCalculus.AllRules)
    (hS : SeveralVariables.SeveralVariablesFacts)
    (hP : YangMills.Construction.TransferOperators.GibbsHaarKernels.Statement) :
    SmoothToSobolevDecayStatement := by
  intro J _ _ G hG
  cases nonempty_fintype J
  have hdec : ∀ q, sobolevDecay q (toHaarL2 G) < ∞ := sobolevDecay_lt_top hC hS hF hK hG
  refine ⟨hdec, ?_⟩
  obtain ⟨-, S, hSm, hsum, hae, -⟩ := hD J (toHaarL2 G) hdec
  have hSG : S = G := (hP.2.1 J).2.2.2 S G (continuous_of_mem_smoothSet hSm)
    (continuous_of_mem_smoothSet hG) (hae.trans (toHaarL2_coeFn_ae (continuous_of_mem_smoothSet hG)))
  rw [hSG] at hsum
  exact hsum
end YangMills.Construction.SpinHarmonics.SmoothToSobolevDecayProof
end
