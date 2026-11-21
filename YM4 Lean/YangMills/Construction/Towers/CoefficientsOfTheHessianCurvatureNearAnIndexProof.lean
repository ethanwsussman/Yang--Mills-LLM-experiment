import YangMills.Construction.Towers.CoefficientsOfTheHalfPlaquetteTraceNearAnIndexProof
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWavesProof
import YangMills.Construction.Matrices.ConjugationByFourExpExpansionProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsFromAnExpansion
import YangMills.Construction.Towers.CoefficientsOfTheHessianCurvatureNearAnIndex
import YangMills.Construction.Towers.FactsOnThePartsOfTheHessianOfTheWilsonActionProof
import YangMills.Construction.Towers.HessianCurvatureKernelOfAFieldIsLocalProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CurvatureKernelCoeffs
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Tower.FullSpace.FinestLatticeNeighbours
open YangMills.Construction.Matrices.ComplexMatrix2.FourExpConjugation (bracket)
theorem norm_bracket_le_two_mul (X Y : ComplexMatrix2) : ‖bracket X Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by apply _root_.YangMills.SharedProofs.p42284 <;> assumption
theorem bracket_add_fst (X X' Y : ComplexMatrix2) : bracket (X + X') Y = bracket X Y + bracket X' Y := by
  simp only [bracket, add_mul, mul_add]
  abel
theorem bracket_smul_fst (c : ℂ) (X Y : ComplexMatrix2) : bracket (c • X) Y = c • bracket X Y := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]
theorem bracketSumOrdered_add_fst (Z₁ Z₂ Z' : Fin 4 → ComplexMatrix2) :
    bracketSumOrdered (Z₁ + Z₂) Z' = bracketSumOrdered Z₁ Z' + bracketSumOrdered Z₂ Z' := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.bracketSumOrdered_add_left <;> assumption
theorem bracketSumOrdered_add_snd (Z Z₁ Z₂ : Fin 4 → ComplexMatrix2) :
    bracketSumOrdered Z (Z₁ + Z₂) = bracketSumOrdered Z Z₁ + bracketSumOrdered Z Z₂ := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.bracketSumOrdered_add_right <;> assumption
theorem bracketSumOrdered_smul_fst (c : ℂ) (Z Z' : Fin 4 → ComplexMatrix2) :
    bracketSumOrdered (c • Z) Z' = c • bracketSumOrdered Z Z' := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.bracketSumOrdered_smul_left <;> assumption
theorem bracketSumOrdered_smul_snd (c : ℂ) (Z Z' : Fin 4 → ComplexMatrix2) :
    bracketSumOrdered Z (c • Z') = c • bracketSumOrdered Z Z' := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.bracketSumOrdered_smul_right <;> assumption
theorem norm_bracketSumOrdered_le {Z Z' : Fin 4 → ComplexMatrix2} {α α' : ℝ} (hα : 0 ≤ α)
    (hα' : 0 ≤ α') (hZ : ∀ j, ‖Z j‖ ≤ α) (hZ' : ∀ j, ‖Z' j‖ ≤ α') :
    ‖bracketSumOrdered Z Z'‖ ≤ 32 * (α * α') := by
  have hterm : ∀ i j, ‖Z i * Z' j - Z' j * Z i‖ ≤ 2 * (α * α') := fun i j => by
    calc ‖Z i * Z' j - Z' j * Z i‖ ≤ ‖Z i * Z' j‖ + ‖Z' j * Z i‖ := norm_sub_le _ _
      _ ≤ ‖Z i‖ * ‖Z' j‖ + ‖Z' j‖ * ‖Z i‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ α * α' + α' * α := by
          gcongr
          exacts [hZ i, hZ' j, hZ' j, hZ i]
      _ = 2 * (α * α') := by ring
  have hin : ∀ i, ‖∑ i' ∈ Finset.Ioi i, (Z i * Z' i' - Z' i' * Z i)‖ ≤ 8 * (α * α') := fun i => by
    calc ‖∑ i' ∈ Finset.Ioi i, (Z i * Z' i' - Z' i' * Z i)‖
        ≤ ∑ _i' ∈ Finset.Ioi i, 2 * (α * α') := norm_sum_le_of_le _ fun j _ => hterm i j
      _ = ((Finset.Ioi i).card : ℝ) * (2 * (α * α')) := by simp
      _ ≤ 4 * (2 * (α * α')) := by
          have : (Finset.Ioi i).card ≤ 4 := by
            simpa using Finset.card_le_univ (Finset.Ioi i)
          have h' : ((Finset.Ioi i).card : ℝ) ≤ 4 := by exact_mod_cast this
          gcongr
      _ = 8 * (α * α') := by ring
  calc ‖bracketSumOrdered Z Z'‖ ≤ ∑ _i : Fin 4, 8 * (α * α') := norm_sum_le_of_le _ fun i _ => hin i
    _ = 32 * (α * α') := by simp; ring
def signedFamily (A : Fin 4 → ComplexMatrix2) : Fin 4 → ComplexMatrix2 := fun i => transportSign i • A i
theorem signedFamily_add (A B : Fin 4 → ComplexMatrix2) :
    signedFamily (A + B) = signedFamily A + signedFamily B := by
  funext i
  simp [signedFamily, smul_add]
theorem signedFamily_smul (c : ℂ) (A : Fin 4 → ComplexMatrix2) :
    signedFamily (c • A) = c • signedFamily A := by
  funext i
  simp only [signedFamily, Pi.smul_apply]
  rw [smul_comm]
theorem norm_signedFamily (A : Fin 4 → ComplexMatrix2) (i : Fin 4) : ‖signedFamily A i‖ = ‖A i‖ := by
  have hs : ‖transportSign i‖ = 1 := by
    fin_cases i <;> simp [transportSign]
  rw [signedFamily, norm_smul, hs, one_mul]
def traceLin : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun := ComplexMatrix2.fullTrace
  map_add' X Y := by simp [ComplexMatrix2.fullTrace, Matrix.trace_add]
  map_smul' c X := by simp [ComplexMatrix2.fullTrace, Matrix.trace_smul]
def trilinearConst : ℝ := 16 * ‖LinearMap.toContinuousLinearMap traceLin‖
theorem trilinearConst_nonneg : 0 ≤ trilinearConst := by
  have := norm_nonneg (LinearMap.toContinuousLinearMap traceLin)
  unfold trilinearConst
  positivity
def trilinear (A A' : Fin 4 → ComplexMatrix2) (F : ComplexMatrix2) : ℂ :=
  (Complex.I / 2) * traceLin (bracketSumOrdered (signedFamily A) (signedFamily A') * F)
theorem trilinear_add_fst (A B A' : Fin 4 → ComplexMatrix2) (F : ComplexMatrix2) :
    trilinear (A + B) A' F = trilinear A A' F + trilinear B A' F := by
  simp only [trilinear, signedFamily_add, bracketSumOrdered_add_fst, add_mul, map_add, mul_add]
theorem trilinear_add_snd (A A' B' : Fin 4 → ComplexMatrix2) (F : ComplexMatrix2) :
    trilinear A (A' + B') F = trilinear A A' F + trilinear A B' F := by
  simp only [trilinear, signedFamily_add, bracketSumOrdered_add_snd, add_mul, map_add, mul_add]
theorem trilinear_add_thd (A A' : Fin 4 → ComplexMatrix2) (F G : ComplexMatrix2) :
    trilinear A A' (F + G) = trilinear A A' F + trilinear A A' G := by
  simp only [trilinear, mul_add, map_add]
theorem trilinear_smul_fst (c : ℂ) (A A' : Fin 4 → ComplexMatrix2) (F : ComplexMatrix2) :
    trilinear (c • A) A' F = c * trilinear A A' F := by
  simp only [trilinear, signedFamily_smul, bracketSumOrdered_smul_fst, smul_mul_assoc, map_smul,
    smul_eq_mul]
  ring
theorem trilinear_smul_snd (c : ℂ) (A A' : Fin 4 → ComplexMatrix2) (F : ComplexMatrix2) :
    trilinear A (c • A') F = c * trilinear A A' F := by
  simp only [trilinear, signedFamily_smul, bracketSumOrdered_smul_snd, smul_mul_assoc, map_smul,
    smul_eq_mul]
  ring
theorem trilinear_smul_thd (c : ℂ) (A A' : Fin 4 → ComplexMatrix2) (F : ComplexMatrix2) :
    trilinear A A' (c • F) = c * trilinear A A' F := by
  simp only [trilinear, mul_smul_comm, map_smul, smul_eq_mul]
  ring
theorem trilinear_zero_thd (A A' : Fin 4 → ComplexMatrix2) : trilinear A A' 0 = 0 := by
  simp [trilinear]
theorem norm_trilinear_le {A A' : Fin 4 → ComplexMatrix2} {F : ComplexMatrix2} {α α' φ : ℝ}
    (hα : 0 ≤ α) (hα' : 0 ≤ α') (hA : ∀ i, ‖A i‖ ≤ α) (hA' : ∀ i, ‖A' i‖ ≤ α') (hF : ‖F‖ ≤ φ) :
    ‖trilinear A A' F‖ ≤ trilinearConst * α * α' * φ := by
  have hb := norm_bracketSumOrdered_le (Z := signedFamily A) (Z' := signedFamily A') hα hα'
    (fun i => (norm_signedFamily A i).le.trans (hA i))
    (fun i => (norm_signedFamily A' i).le.trans (hA' i))
  have ht := (LinearMap.toContinuousLinearMap traceLin).le_opNorm
    (bracketSumOrdered (signedFamily A) (signedFamily A') * F)
  have hm := norm_mul_le (bracketSumOrdered (signedFamily A) (signedFamily A')) F
  have hK := norm_nonneg (LinearMap.toContinuousLinearMap traceLin)
  have hI : ‖Complex.I / 2‖ = 1 / 2 := by simp
  have h1 : ‖bracketSumOrdered (signedFamily A) (signedFamily A') * F‖ ≤ 32 * (α * α') * φ :=
    hm.trans (mul_le_mul hb hF (norm_nonneg _) (by positivity))
  rw [trilinear, norm_mul, hI]
  have h2 : ‖traceLin (bracketSumOrdered (signedFamily A) (signedFamily A') * F)‖ ≤
      ‖LinearMap.toContinuousLinearMap traceLin‖ * (32 * (α * α') * φ) :=
    (ht.trans (mul_le_mul_of_nonneg_left h1 hK))
  calc 1 / 2 * ‖traceLin (bracketSumOrdered (signedFamily A) (signedFamily A') * F)‖
      ≤ 1 / 2 * (‖LinearMap.toContinuousLinearMap traceLin‖ * (32 * (α * α') * φ)) := by
        linarith
    _ = trilinearConst * α * α' * φ := by
        unfold trilinearConst
        ring
theorem trilinear_third_order {Y Y' a a' D D' : Fin 4 → ComplexMatrix2} {F₁ F₂ R : ComplexMatrix2}
    {C m : ℝ} (hC : 0 ≤ C)
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hY : ∀ i, ‖Y i‖ ≤ C) (hY' : ∀ i, ‖Y' i‖ ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C * m) (ha' : ∀ i, ‖a' i‖ ≤ C * m)
    (hD : ∀ i, ‖D i‖ ≤ C * m ^ 2) (hD' : ∀ i, ‖D' i‖ ≤ C * m ^ 2)
    (hF₁ : ‖F₁‖ ≤ C * m) (hF₂ : ‖F₂‖ ≤ C * m ^ 2) (hR : ‖R‖ ≤ C * m ^ 3) :
    ‖trilinear (Y + a + D) (Y' + a' + D') (F₁ + F₂ + R) - trilinear Y Y' F₁ -
        (trilinear Y Y' F₂ + trilinear a Y' F₁ + trilinear Y a' F₁)‖ ≤
      23 * trilinearConst * C ^ 3 * m ^ 3 := by
  have e : trilinear (Y + a + D) (Y' + a' + D') (F₁ + F₂ + R) - trilinear Y Y' F₁ -
        (trilinear Y Y' F₂ + trilinear a Y' F₁ + trilinear Y a' F₁) =
      trilinear (Y + a + D) (Y' + a' + D') R + trilinear D (Y' + a' + D') F₁ +
        trilinear Y D' F₁ + trilinear a (a' + D') F₁ + trilinear (a + D) (Y' + a' + D') F₂ +
        trilinear Y (a' + D') F₂ := by
    simp only [trilinear_add_fst, trilinear_add_snd, trilinear_add_thd]
    ring
  have hm2 : m ^ 2 ≤ m := by nlinarith
  have hCm : 0 ≤ C * m := mul_nonneg hC hm
  have hCm2 : C * m ^ 2 ≤ C * m := mul_le_mul_of_nonneg_left hm2 hC
  have hCm1 : C * m ≤ C := by nlinarith
  have hs : ∀ {Z : Fin 4 → ComplexMatrix2} {b d : Fin 4 → ComplexMatrix2}, (∀ i, ‖Z i‖ ≤ C) →
      (∀ i, ‖b i‖ ≤ C * m) → (∀ i, ‖d i‖ ≤ C * m ^ 2) → ∀ i, ‖(Z + b + d) i‖ ≤ 3 * C :=
    fun {Z b d} hZ hb hd i => by
    have h1 := norm_add_le (Z i + b i) (d i)
    have h2 := norm_add_le (Z i) (b i)
    have := hZ i
    have := hb i
    have := hd i
    simp only [Pi.add_apply]
    linarith
  have hs' : ∀ {b d : Fin 4 → ComplexMatrix2}, (∀ i, ‖b i‖ ≤ C * m) →
      (∀ i, ‖d i‖ ≤ C * m ^ 2) → ∀ i, ‖(b + d) i‖ ≤ 2 * (C * m) := fun {b d} hb hd i => by
    have h1 := norm_add_le (b i) (d i)
    have := hb i
    have := hd i
    simp only [Pi.add_apply]
    linarith
  have hC3 : 0 ≤ 3 * C := by positivity
  have hCm' : 0 ≤ 2 * (C * m) := by positivity
  have hCmm : 0 ≤ C * m ^ 2 := by positivity
  have t1 : ‖trilinear (Y + a + D) (Y' + a' + D') R‖ ≤ 9 * (trilinearConst * C ^ 3 * m ^ 3) :=
    (norm_trilinear_le hC3 hC3 (hs hY ha hD) (hs hY' ha' hD') hR).trans (le_of_eq (by ring))
  have t2 : ‖trilinear D (Y' + a' + D') F₁‖ ≤ 3 * (trilinearConst * C ^ 3 * m ^ 3) :=
    (norm_trilinear_le hCmm hC3 hD (hs hY' ha' hD') hF₁).trans (le_of_eq (by ring))
  have t3 : ‖trilinear Y D' F₁‖ ≤ 1 * (trilinearConst * C ^ 3 * m ^ 3) :=
    (norm_trilinear_le hC hCmm hY hD' hF₁).trans (le_of_eq (by ring))
  have t4 : ‖trilinear a (a' + D') F₁‖ ≤ 2 * (trilinearConst * C ^ 3 * m ^ 3) :=
    (norm_trilinear_le hCm hCm' ha (hs' ha' hD') hF₁).trans (le_of_eq (by ring))
  have t5 : ‖trilinear (a + D) (Y' + a' + D') F₂‖ ≤ 6 * (trilinearConst * C ^ 3 * m ^ 3) :=
    (norm_trilinear_le hCm' hC3 (hs' ha hD) (hs hY' ha' hD') hF₂).trans (le_of_eq (by ring))
  have t6 : ‖trilinear Y (a' + D') F₂‖ ≤ 2 * (trilinearConst * C ^ 3 * m ^ 3) :=
    (norm_trilinear_le hC hCm' hY (hs' ha' hD') hF₂).trans (le_of_eq (by ring))
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have n1 := norm_add_le (trilinear (Y + a + D) (Y' + a' + D') R + trilinear D (Y' + a' + D') F₁ +
    trilinear Y D' F₁ + trilinear a (a' + D') F₁) (trilinear (a + D) (Y' + a' + D') F₂)
  have n2 := norm_add_le (trilinear (Y + a + D) (Y' + a' + D') R + trilinear D (Y' + a' + D') F₁ +
    trilinear Y D' F₁) (trilinear a (a' + D') F₁)
  have n3 := norm_add_le (trilinear (Y + a + D) (Y' + a' + D') R + trilinear D (Y' + a' + D') F₁)
    (trilinear Y D' F₁)
  have n4 := norm_add_le (trilinear (Y + a + D) (Y' + a' + D') R) (trilinear D (Y' + a' + D') F₁)
  linarith
def expProduct (Z : Fin 4 → ComplexMatrix2) : ComplexMatrix2 :=
  (List.ofFn fun j => ComplexMatrix2.matExp (Z j)).prod
def halfBracketSum (Z Z' : Fin 4 → ComplexMatrix2) : ComplexMatrix2 :=
  (1 / 2 : ℂ) • bracketSumOrdered Z Z'
theorem halfBracketSum_self (Z : Fin 4 → ComplexMatrix2) :
    halfBracketSum Z Z = ComplexMatrix2.halfCommutatorSum Z := rfl
theorem halfBracketSum_add_fst (Z₁ Z₂ Z' : Fin 4 → ComplexMatrix2) :
    halfBracketSum (Z₁ + Z₂) Z' = halfBracketSum Z₁ Z' + halfBracketSum Z₂ Z' := by
  simp only [halfBracketSum, bracketSumOrdered_add_fst, smul_add]
theorem halfBracketSum_add_snd (Z Z₁ Z₂ : Fin 4 → ComplexMatrix2) :
    halfBracketSum Z (Z₁ + Z₂) = halfBracketSum Z Z₁ + halfBracketSum Z Z₂ := by
  simp only [halfBracketSum, bracketSumOrdered_add_snd, smul_add]
theorem halfBracketSum_smul_fst (c : ℂ) (Z Z' : Fin 4 → ComplexMatrix2) :
    halfBracketSum (c • Z) Z' = c • halfBracketSum Z Z' := by
  simp only [halfBracketSum, bracketSumOrdered_smul_fst]
  rw [smul_comm]
theorem halfBracketSum_smul_snd (c : ℂ) (Z Z' : Fin 4 → ComplexMatrix2) :
    halfBracketSum Z (c • Z') = c • halfBracketSum Z Z' := by
  simp only [halfBracketSum, bracketSumOrdered_smul_snd]
  rw [smul_comm]
theorem norm_halfBracketSum_le {Z Z' : Fin 4 → ComplexMatrix2} {α α' : ℝ} (hα : 0 ≤ α)
    (hα' : 0 ≤ α') (hZ : ∀ j, ‖Z j‖ ≤ α) (hZ' : ∀ j, ‖Z' j‖ ≤ α') :
    ‖halfBracketSum Z Z'‖ ≤ 16 * (α * α') := by
  have h := norm_bracketSumOrdered_le hα hα' hZ hZ'
  rw [halfBracketSum, norm_smul]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  linarith
theorem matExp_mul_matExp_neg (A : ComplexMatrix2) :
    ComplexMatrix2.matExp A * ComplexMatrix2.matExp (-A) = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.matExp_mul_matExp_neg <;> assumption
theorem list_prod_ofFn_four (f : Fin 4 → ComplexMatrix2) :
    (List.ofFn f).prod = f 0 * f 1 * f 2 * f 3 := by
  simp [List.ofFn_succ, mul_assoc]
theorem halfCommutatorSum_fin_four (Z : Fin 4 → ComplexMatrix2) :
    ComplexMatrix2.halfCommutatorSum Z = (1 / 2 : ℂ) • ((Z 0 * Z 1 - Z 1 * Z 0) +
      (Z 0 * Z 2 - Z 2 * Z 0) + (Z 0 * Z 3 - Z 3 * Z 0) + (Z 1 * Z 2 - Z 2 * Z 1) +
      (Z 1 * Z 3 - Z 3 * Z 1) + (Z 2 * Z 3 - Z 3 * Z 2)) := by apply _root_.YangMills.SharedProofs.p20090 <;> assumption
theorem expProduct_sub_inv_expansion (hE : ComplexMatrix2.ExpProductExpansionAndConjugation)
    (Z : Fin 4 → ComplexMatrix2) (hle : ∑ j, ‖Z j‖ ≤ 1) :
    ‖expProduct Z - (expProduct Z)⁻¹ - (2 : ℂ) • ∑ j, Z j -
        (2 : ℂ) • ComplexMatrix2.halfCommutatorSum Z‖ ≤ (∑ j, ‖Z j‖) ^ 3 := by
  set ϱ : ℝ := ∑ j, ‖Z j‖ with hρ
  set s : ComplexMatrix2 := ∑ j, Z j with hs
  set W : ComplexMatrix2 := ComplexMatrix2.halfCommutatorSum Z with hW
  set P : ComplexMatrix2 := expProduct Z with hP
  set Z' : Fin 4 → ComplexMatrix2 := ![-Z 3, -Z 2, -Z 1, -Z 0] with hZ'
  set Q : ComplexMatrix2 := expProduct Z' with hQ
  have hϱ' : ϱ = ∑ j, ComplexMatrix2.operatorNorm (Z' j) := by
    rw [hρ]
    simp only [hZ', ComplexMatrix2.operatorNorm, Fin.sum_univ_four]
    simp
    ring
  have hs' : -s = ∑ j, Z' j := by
    rw [hs]
    simp only [hZ', Fin.sum_univ_four]
    simp
    abel
  have hW' : -W = ComplexMatrix2.halfCommutatorSum Z' := by
    rw [hW, halfCommutatorSum_fin_four, halfCommutatorSum_fin_four, ← smul_neg]
    congr 1
    simp only [hZ']
    simp
    abel
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, expProduct, expProduct, list_prod_ofFn_four, list_prod_ofFn_four]
    simp only [hZ']
    simp only [Matrix.cons_val]
    have e0 := matExp_mul_matExp_neg (Z 0)
    have e1 := matExp_mul_matExp_neg (Z 1)
    have e2 := matExp_mul_matExp_neg (Z 2)
    have e3 := matExp_mul_matExp_neg (Z 3)
    calc ComplexMatrix2.matExp (Z 0) * ComplexMatrix2.matExp (Z 1) * ComplexMatrix2.matExp (Z 2) *
          ComplexMatrix2.matExp (Z 3) *
          (ComplexMatrix2.matExp (-Z 3) * ComplexMatrix2.matExp (-Z 2) *
            ComplexMatrix2.matExp (-Z 1) * ComplexMatrix2.matExp (-Z 0))
        = ComplexMatrix2.matExp (Z 0) * (ComplexMatrix2.matExp (Z 1) *
            (ComplexMatrix2.matExp (Z 2) * (ComplexMatrix2.matExp (Z 3) *
              ComplexMatrix2.matExp (-Z 3)) * ComplexMatrix2.matExp (-Z 2)) *
            ComplexMatrix2.matExp (-Z 1)) * ComplexMatrix2.matExp (-Z 0) := by
          simp only [mul_assoc]
      _ = 1 := by rw [e3, mul_one, e2, mul_one, e1, mul_one, e0]
  have hinv : P⁻¹ = Q := Matrix.inv_eq_right_inv hPQ
  obtain ⟨-, -, a, b⟩ := hE.1 4 Z ϱ s W P rfl rfl rfl rfl
  obtain ⟨-, -, c, d⟩ := hE.1 4 Z' ϱ (-s) (-W) Q hϱ' hs' hW' rfl
  have hexp : Real.exp ϱ ≤ 3 := by
    have h1 : Real.exp ϱ ≤ Real.exp 1 := Real.exp_le_exp.mpr hle
    have h2 := Real.exp_one_lt_d9
    linarith
  have htail : 1 / 6 * ϱ ^ 3 * Real.exp ϱ ≤ 1 / 2 * ϱ ^ 3 := by
    have : 0 ≤ ϱ ^ 3 := by positivity
    nlinarith
  have e : P - P⁻¹ - (2 : ℂ) • s - (2 : ℂ) • W =
      (P - 1 - s - (1 / 2 : ℂ) • s ^ 2 - W) - (Q - 1 - -s - (1 / 2 : ℂ) • (-s) ^ 2 - -W) := by
    rw [hinv, neg_sq]
    module
  rw [e]
  have := norm_sub_le (P - 1 - s - (1 / 2 : ℂ) • s ^ 2 - W)
    (Q - 1 - -s - (1 / 2 : ℂ) • (-s) ^ 2 - -W)
  linarith
def conjConst : ℝ := 10 * Real.exp 1 ^ 2 + 3
theorem conjConst_nonneg : 0 ≤ conjConst := by
  unfold conjConst
  positivity
theorem norm_sum_fin_four_le {Z : Fin 4 → ComplexMatrix2} {u : ℝ} (hZ : ∀ j, ‖Z j‖ ≤ u) :
    ‖∑ j, Z j‖ ≤ 4 * u := by
  calc ‖∑ j, Z j‖ ≤ ∑ _j : Fin 4, u := norm_sum_le_of_le _ fun j _ => hZ j
    _ = 4 * u := by simp
theorem sum_norm_fin_four_le {Z : Fin 4 → ComplexMatrix2} {u : ℝ} (hZ : ∀ j, ‖Z j‖ ≤ u) :
    ∑ j, ‖Z j‖ ≤ 4 * u := by
  calc ∑ j, ‖Z j‖ ≤ ∑ _j : Fin 4, u := Finset.sum_le_sum fun j _ => hZ j
    _ = 4 * u := by simp
theorem conjugateBy_expProduct_remainder
    (hX : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion)
    (Z : Fin 4 → ComplexMatrix2) (Y : ComplexMatrix2) {u : ℝ} (hu : 0 ≤ u) (hu1 : 4 * u ≤ 1)
    (hZ : ∀ j, ‖Z j‖ ≤ u) :
    ‖ComplexMatrix2.conjugateBy (expProduct Z) Y - Y - bracket (∑ j, Z j) Y‖ ≤
      conjConst * (16 * u ^ 2) * ‖Y‖ := by
  set ϱ : ℝ := ∑ j, ‖Z j‖ with hρ
  have h0 : 0 ≤ ϱ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have h4 : ϱ ≤ 4 * u := sum_norm_fin_four_le hZ
  have h1 : ϱ ≤ 1 := h4.trans hu1
  obtain ⟨a, -, c⟩ := hX Z Y ϱ (∑ j, Z j) (ComplexMatrix2.halfCommutatorSum Z) (expProduct Z)
    rfl h1 rfl rfl rfl
  set Q : ComplexMatrix2 := (1 / 2 : ℂ) • bracket (∑ j, Z j) (bracket (∑ j, Z j) Y) +
    bracket (ComplexMatrix2.halfCommutatorSum Z) Y with hQ
  have hn := norm_add_le
    (ComplexMatrix2.conjugateBy (expProduct Z) Y - Y - bracket (∑ j, Z j) Y - Q) Q
  rw [sub_add_cancel] at hn
  have h3 : ϱ ^ 3 ≤ ϱ ^ 2 := by nlinarith [sq_nonneg ϱ]
  have h2 : ϱ ^ 2 ≤ 16 * u ^ 2 := by nlinarith
  calc _ ≤ 10 * Real.exp 1 ^ 2 * ϱ ^ 3 * ‖Y‖ + 3 * ϱ ^ 2 * ‖Y‖ := by linarith
    _ ≤ 10 * Real.exp 1 ^ 2 * ϱ ^ 2 * ‖Y‖ + 3 * ϱ ^ 2 * ‖Y‖ := by gcongr
    _ = conjConst * ϱ ^ 2 * ‖Y‖ := by
        unfold conjConst
        ring
    _ ≤ _ := by
        have := conjConst_nonneg
        gcongr
abbrev ExponentArray : Type := Fin 4 → Fin 4 → ComplexMatrix2
def bracketTerm (Y : Fin 4 → ComplexMatrix2) : ExponentArray →ₗ[ℂ] Fin 4 → ComplexMatrix2 where
  toFun E := fun l => bracket (∑ j, E l j) (Y l)
  map_add' E E' := by
    funext l
    simp only [Pi.add_apply, Finset.sum_add_distrib, bracket_add_fst]
  map_smul' c E := by
    funext l
    simp only [Pi.smul_apply, ← Finset.smul_sum, bracket_smul_fst, RingHom.id_apply]
theorem bracketTerm_apply (Y : Fin 4 → ComplexMatrix2) (E : ExponentArray) (l : Fin 4) :
    bracketTerm Y E l = bracket (∑ j, E l j) (Y l) := rfl
def curvLinear (c : ℂ) : ExponentArray →ₗ[ℂ] ComplexMatrix2 where
  toFun E := c • ∑ j, E 3 j
  map_add' E E' := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add]
  map_smul' d E := by
    simp only [Pi.smul_apply, ← Finset.smul_sum, RingHom.id_apply]
    rw [smul_comm]
theorem curvLinear_apply (c : ℂ) (E : ExponentArray) :
    curvLinear c E = c • ∑ j, E 3 j := rfl
def curvQuadratic (c : ℂ) : ExponentArray →ₗ[ℂ] ExponentArray →ₗ[ℂ] ComplexMatrix2 :=
  LinearMap.mk₂ ℂ (fun E E' => c • (halfBracketSum (E 3) (E' 3) + halfBracketSum (E' 3) (E 3)))
    (fun E₁ E₂ E' => by
      simp only [Pi.add_apply, halfBracketSum_add_fst, halfBracketSum_add_snd, smul_add]
      abel)
    (fun d E E' => by
      simp only [Pi.smul_apply, halfBracketSum_smul_fst, halfBracketSum_smul_snd]
      module)
    (fun E E₁ E₂ => by
      simp only [Pi.add_apply, halfBracketSum_add_fst, halfBracketSum_add_snd, smul_add]
      abel)
    (fun d E E' => by
      simp only [Pi.smul_apply, halfBracketSum_smul_fst, halfBracketSum_smul_snd]
      module)
theorem curvQuadratic_apply (c : ℂ) (E E' : ExponentArray) :
    curvQuadratic c E E' = c • (halfBracketSum (E 3) (E' 3) + halfBracketSum (E' 3) (E 3)) := rfl
def linearPart (c : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) : ExponentArray →ₗ[ℂ] ℂ where
  toFun E := trilinear Y Y' (curvLinear c E)
  map_add' E E' := by
    simp only [map_add, trilinear_add_thd]
  map_smul' d E := by
    simp only [map_smul, trilinear_smul_thd, RingHom.id_apply, smul_eq_mul]
theorem linearPart_apply (c : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) (E : ExponentArray) :
    linearPart c Y Y' E = trilinear Y Y' (curvLinear c E) := rfl
def quadraticPart (c : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) :
    ExponentArray →ₗ[ℂ] ExponentArray →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun E E' => trilinear Y Y' (curvQuadratic c E E') +
      trilinear (bracketTerm Y E) Y' (curvLinear c E') +
      trilinear (bracketTerm Y E') Y' (curvLinear c E) +
      trilinear Y (bracketTerm Y' E) (curvLinear c E') +
      trilinear Y (bracketTerm Y' E') (curvLinear c E))
    (fun E₁ E₂ E' => by
      simp only [map_add, LinearMap.add_apply, trilinear_add_fst, trilinear_add_snd,
        trilinear_add_thd]
      ring)
    (fun d E E' => by
      simp only [map_smul, LinearMap.smul_apply, trilinear_smul_fst, trilinear_smul_snd,
        trilinear_smul_thd, smul_eq_mul]
      ring)
    (fun E E₁ E₂ => by
      simp only [map_add, LinearMap.add_apply, trilinear_add_fst, trilinear_add_snd,
        trilinear_add_thd]
      ring)
    (fun d E E' => by
      simp only [map_smul, LinearMap.smul_apply, trilinear_smul_fst, trilinear_smul_snd,
        trilinear_smul_thd, smul_eq_mul]
      ring)
theorem quadraticPart_apply (c : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) (E E' : ExponentArray) :
    quadraticPart c Y Y' E E' = trilinear Y Y' (curvQuadratic c E E') +
      trilinear (bracketTerm Y E) Y' (curvLinear c E') +
      trilinear (bracketTerm Y E') Y' (curvLinear c E) +
      trilinear Y (bracketTerm Y' E) (curvLinear c E') +
      trilinear Y (bracketTerm Y' E') (curvLinear c E) := rfl
theorem quadraticPart_comm (c : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) (E E' : ExponentArray) :
    quadraticPart c Y Y' E E' = quadraticPart c Y Y' E' E := by
  have h : curvQuadratic c E E' = curvQuadratic c E' E := by
    rw [curvQuadratic_apply, curvQuadratic_apply, add_comm]
  rw [quadraticPart_apply, quadraticPart_apply, h]
  ring
def faceTerm (σ : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) (E : ExponentArray) : ℂ :=
  trilinear (fun l => ComplexMatrix2.conjugateBy (expProduct (E l)) (Y l))
    (fun l => ComplexMatrix2.conjugateBy (expProduct (E l)) (Y' l))
    (σ • (expProduct (E 3) - (expProduct (E 3))⁻¹))
theorem faceTerm_zero (σ : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) : faceTerm σ Y Y' 0 = 0 := by
  have h : expProduct (0 : Fin 4 → ComplexMatrix2) = 1 := by
    simp [expProduct, List.ofFn_succ, NormedSpace.exp_zero]
  simp [faceTerm, h, trilinear_zero_thd]
def expansionConst (σ : ℂ) (B : ℝ) : ℝ := (9 + 16 * conjConst) * B + 104 * ‖σ‖
theorem faceTerm_expansion (hE : ComplexMatrix2.ExpProductExpansionAndConjugation)
    (hX : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion) (σ : ℂ)
    {Y Y' : Fin 4 → ComplexMatrix2} {E : ExponentArray} {B u : ℝ} (hB : 0 ≤ B)
    (hY : ∀ i, ‖Y i‖ ≤ B) (hY' : ∀ i, ‖Y' i‖ ≤ B) (hu : 0 ≤ u) (hu1 : 4 * u ≤ 1)
    (hEu : ∀ l j, ‖E l j‖ ≤ u) :
    ‖faceTerm σ Y Y' E - linearPart (2 * σ) Y Y' E - (1 / 2 : ℂ) * quadraticPart (2 * σ) Y Y' E E‖ ≤
      23 * trilinearConst * expansionConst σ B ^ 3 * u ^ 3 := by
  set C : ℝ := expansionConst σ B with hCdef
  have hG := conjConst_nonneg
  have hσ := norm_nonneg σ
  have hGB : 0 ≤ conjConst * B := mul_nonneg hG hB
  have hCe : C = 9 * B + 16 * (conjConst * B) + 104 * ‖σ‖ := by
    rw [hCdef, expansionConst]
    ring
  have hC : 0 ≤ C := by rw [hCe]; positivity
  have hu2 : 0 ≤ u ^ 2 := by positivity
  have hu3 : 0 ≤ u ^ 3 := by positivity
  have hσ2 : ‖(2 : ℂ) * σ‖ = 2 * ‖σ‖ := by simp
  set a := bracketTerm Y E with ha_def
  set a' := bracketTerm Y' E with ha'_def
  set D : Fin 4 → ComplexMatrix2 :=
    fun l => ComplexMatrix2.conjugateBy (expProduct (E l)) (Y l) - Y l - a l with hD_def
  set D' : Fin 4 → ComplexMatrix2 :=
    fun l => ComplexMatrix2.conjugateBy (expProduct (E l)) (Y' l) - Y' l - a' l with hD'_def
  set s : ComplexMatrix2 := ∑ j, E 3 j with hs_def
  set W : ComplexMatrix2 := ComplexMatrix2.halfCommutatorSum (E 3) with hW_def
  set P : ComplexMatrix2 := expProduct (E 3) with hP_def
  set F₁ : ComplexMatrix2 := curvLinear (2 * σ) E with hF₁_def
  set F₂ : ComplexMatrix2 := (2 * σ) • W with hF₂_def
  set R : ComplexMatrix2 := σ • (P - P⁻¹ - (2 : ℂ) • s - (2 : ℂ) • W) with hR_def
  have eA : (fun l => ComplexMatrix2.conjugateBy (expProduct (E l)) (Y l)) = Y + a + D := by
    funext l
    simp only [hD_def, Pi.add_apply]
    abel
  have eA' : (fun l => ComplexMatrix2.conjugateBy (expProduct (E l)) (Y' l)) = Y' + a' + D' := by
    funext l
    simp only [hD'_def, Pi.add_apply]
    abel
  have eF : σ • (P - P⁻¹) = F₁ + F₂ + R := by
    rw [hF₁_def, curvLinear_apply, hF₂_def, hR_def]
    module
  have hmem : ∀ {Z : Fin 4 → ComplexMatrix2}, (∀ i, ‖Z i‖ ≤ B) → ∀ l, ‖bracketTerm Z E l‖ ≤ C * u :=
    fun {Z} hZ l => by
      rw [bracketTerm_apply]
      have h1 := norm_bracket_le_two_mul (∑ j, E l j) (Z l)
      have h2 : ‖∑ j, E l j‖ ≤ 4 * u := norm_sum_fin_four_le (hEu l)
      have h3 : 2 * ‖∑ j, E l j‖ * ‖Z l‖ ≤ 2 * (4 * u) * B := by
        have := hZ l
        gcongr
      have h4 : 8 * B ≤ C := by rw [hCe]; linarith
      nlinarith
  have hrem : ∀ {Z : Fin 4 → ComplexMatrix2}, (∀ i, ‖Z i‖ ≤ B) → ∀ l,
      ‖ComplexMatrix2.conjugateBy (expProduct (E l)) (Z l) - Z l - bracketTerm Z E l‖ ≤ C * u ^ 2 :=
    fun {Z} hZ l => by
    have h1 := conjugateBy_expProduct_remainder hX (E l) (Z l) hu hu1 (hEu l)
    have h2 : conjConst * (16 * u ^ 2) * ‖Z l‖ ≤ conjConst * (16 * u ^ 2) * B := by
      have := hZ l
      gcongr
    have h4 : 16 * (conjConst * B) ≤ C := by rw [hCe]; linarith
    have h5 : 16 * (conjConst * B) * u ^ 2 ≤ C * u ^ 2 :=
      mul_le_mul_of_nonneg_right h4 hu2
    rw [bracketTerm_apply]
    calc _ ≤ conjConst * (16 * u ^ 2) * B := h1.trans h2
      _ = 16 * (conjConst * B) * u ^ 2 := by ring
      _ ≤ _ := h5
  have hF₁ : ‖F₁‖ ≤ C * u := by
    rw [hF₁_def, curvLinear_apply, norm_smul, hσ2]
    have h2 : ‖s‖ ≤ 4 * u := norm_sum_fin_four_le (hEu 3)
    have h3 : 2 * ‖σ‖ * ‖s‖ ≤ 2 * ‖σ‖ * (4 * u) := by gcongr
    have h4 : 8 * ‖σ‖ ≤ C := by rw [hCe]; linarith
    nlinarith
  have hWn : ‖W‖ ≤ 16 * u ^ 2 := by
    have h := norm_halfBracketSum_le hu hu (hEu 3) (hEu 3)
    rw [halfBracketSum_self] at h
    nlinarith
  have hF₂ : ‖F₂‖ ≤ C * u ^ 2 := by
    rw [hF₂_def, norm_smul, hσ2]
    have h3 : 2 * ‖σ‖ * ‖W‖ ≤ 2 * ‖σ‖ * (16 * u ^ 2) := by gcongr
    have h4 : 32 * ‖σ‖ ≤ C := by rw [hCe]; linarith
    nlinarith
  have hR : ‖R‖ ≤ C * u ^ 3 := by
    have h4 : ∑ j, ‖E 3 j‖ ≤ 4 * u := sum_norm_fin_four_le (hEu 3)
    have h0 : 0 ≤ ∑ j, ‖E 3 j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    have h1 := expProduct_sub_inv_expansion hE (E 3) (h4.trans hu1)
    have h2 : (∑ j, ‖E 3 j‖) ^ 3 ≤ (4 * u) ^ 3 := pow_le_pow_left₀ h0 h4 3
    have h3 : ‖P - P⁻¹ - (2 : ℂ) • s - (2 : ℂ) • W‖ ≤ 64 * u ^ 3 := by
      refine h1.trans (h2.trans (le_of_eq ?_))
      ring
    rw [hR_def, norm_smul]
    have h5 : ‖σ‖ * ‖P - P⁻¹ - (2 : ℂ) • s - (2 : ℂ) • W‖ ≤ ‖σ‖ * (64 * u ^ 3) := by gcongr
    have h6 : 64 * ‖σ‖ ≤ C := by rw [hCe]; linarith
    nlinarith
  have hBC : ∀ {Z : Fin 4 → ComplexMatrix2}, (∀ i, ‖Z i‖ ≤ B) → ∀ i, ‖Z i‖ ≤ C := fun {Z} hZ i => by
    have h4 : B ≤ C := by rw [hCe]; linarith
    exact (hZ i).trans h4
  have hmain := trilinear_third_order (Y := Y) (Y' := Y') (a := a) (a' := a') (D := D) (D' := D')
    (F₁ := F₁) (F₂ := F₂) (R := R) hC hu (by linarith) (hBC hY) (hBC hY') (hmem hY) (hmem hY')
    (hrem hY) (hrem hY') hF₁ hF₂ hR
  have e1 : faceTerm σ Y Y' E = trilinear (Y + a + D) (Y' + a' + D') (F₁ + F₂ + R) := by
    rw [faceTerm, eA, eA', eF]
  have eS : curvQuadratic (2 * σ) E E = F₂ + F₂ := by
    rw [curvQuadratic_apply, halfBracketSum_self, hF₂_def, smul_add]
  have e2 : (1 / 2 : ℂ) * quadraticPart (2 * σ) Y Y' E E =
      trilinear Y Y' F₂ + trilinear a Y' F₁ + trilinear Y a' F₁ := by
    rw [quadraticPart_apply, eS, trilinear_add_thd]
    ring
  rw [e1, e2, linearPart_apply]
  exact hmain
theorem norm_linearPart_le {c : ℂ} {Y Y' : Fin 4 → ComplexMatrix2} {E : ExponentArray} {B M : ℝ}
    (hB : 0 ≤ B) (hY : ∀ i, ‖Y i‖ ≤ B) (hY' : ∀ i, ‖Y' i‖ ≤ B) (h : ‖curvLinear c E‖ ≤ M) :
    ‖linearPart c Y Y' E‖ ≤ trilinearConst * B * B * M :=
  norm_trilinear_le hB hB hY hY' h
theorem norm_bracketTerm_le {Y : Fin 4 → ComplexMatrix2} {E : ExponentArray} {B v : ℝ} (hB : 0 ≤ B)
    (hY : ∀ i, ‖Y i‖ ≤ B) (hE : ∀ l j, ‖E l j‖ ≤ v) (l : Fin 4) :
    ‖bracketTerm Y E l‖ ≤ 8 * v * B := by
  rw [bracketTerm_apply]
  have h1 := norm_bracket_le_two_mul (∑ j, E l j) (Y l)
  have h2 : ‖∑ j, E l j‖ ≤ 4 * v := norm_sum_fin_four_le (hE l)
  have h3 : 2 * ‖∑ j, E l j‖ * ‖Y l‖ ≤ 2 * (4 * v) * B := by
    have := hY l
    have : 0 ≤ 4 * v := (norm_nonneg _).trans h2
    gcongr
  linarith
theorem norm_quadraticPart_le {c : ℂ} {Y Y' : Fin 4 → ComplexMatrix2} {E E' : ExponentArray}
    {B v M : ℝ} (hB : 0 ≤ B) (hv : 0 ≤ v) (hvM : v ≤ M) (hY : ∀ i, ‖Y i‖ ≤ B)
    (hY' : ∀ i, ‖Y' i‖ ≤ B) (hE : ∀ l j, ‖E l j‖ ≤ v) (hE' : ∀ l j, ‖E' l j‖ ≤ v)
    (hs : ‖curvLinear c E‖ ≤ M) (hs' : ‖curvLinear c E'‖ ≤ M) (hc : ‖c‖ * v ^ 2 ≤ M ^ 2) :
    ‖quadraticPart c Y Y' E E'‖ ≤ 64 * trilinearConst * B ^ 2 * M ^ 2 := by
  have hM : 0 ≤ M := hv.trans hvM
  have hS : ‖curvQuadratic c E E'‖ ≤ 32 * M ^ 2 := by
    rw [curvQuadratic_apply, norm_smul]
    have h1 := norm_halfBracketSum_le hv hv (hE 3) (hE' 3)
    have h2 := norm_halfBracketSum_le hv hv (hE' 3) (hE 3)
    have h3 := norm_add_le (halfBracketSum (E 3) (E' 3)) (halfBracketSum (E' 3) (E 3))
    have h4 : ‖halfBracketSum (E 3) (E' 3) + halfBracketSum (E' 3) (E 3)‖ ≤ 32 * v ^ 2 := by
      nlinarith
    calc ‖c‖ * _ ≤ ‖c‖ * (32 * v ^ 2) := by gcongr
      _ = 32 * (‖c‖ * v ^ 2) := by ring
      _ ≤ _ := by linarith
  have hm : ∀ {Z : Fin 4 → ComplexMatrix2} {G : ExponentArray}, (∀ i, ‖Z i‖ ≤ B) →
      (∀ l j, ‖G l j‖ ≤ v) → ∀ l, ‖bracketTerm Z G l‖ ≤ 8 * M * B := fun {Z G} hZ hG l => by
    refine (norm_bracketTerm_le hB hZ hG l).trans ?_
    gcongr
  have hMB : 0 ≤ 8 * M * B := by positivity
  have t1 : ‖trilinear Y Y' (curvQuadratic c E E')‖ ≤ 32 * (trilinearConst * B ^ 2 * M ^ 2) :=
    (norm_trilinear_le hB hB hY hY' hS).trans (le_of_eq (by ring))
  have t2 : ‖trilinear (bracketTerm Y E) Y' (curvLinear c E')‖ ≤
      8 * (trilinearConst * B ^ 2 * M ^ 2) :=
    (norm_trilinear_le hMB hB (hm hY hE) hY' hs').trans (le_of_eq (by ring))
  have t3 : ‖trilinear (bracketTerm Y E') Y' (curvLinear c E)‖ ≤
      8 * (trilinearConst * B ^ 2 * M ^ 2) :=
    (norm_trilinear_le hMB hB (hm hY hE') hY' hs).trans (le_of_eq (by ring))
  have t4 : ‖trilinear Y (bracketTerm Y' E) (curvLinear c E')‖ ≤
      8 * (trilinearConst * B ^ 2 * M ^ 2) :=
    (norm_trilinear_le hB hMB hY (hm hY' hE) hs').trans (le_of_eq (by ring))
  have t5 : ‖trilinear Y (bracketTerm Y' E') (curvLinear c E)‖ ≤
      8 * (trilinearConst * B ^ 2 * M ^ 2) :=
    (norm_trilinear_le hB hMB hY (hm hY' hE') hs).trans (le_of_eq (by ring))
  rw [quadraticPart_apply]
  have n1 := norm_add_le (trilinear Y Y' (curvQuadratic c E E') +
    trilinear (bracketTerm Y E) Y' (curvLinear c E') +
    trilinear (bracketTerm Y E') Y' (curvLinear c E) +
    trilinear Y (bracketTerm Y' E) (curvLinear c E'))
    (trilinear Y (bracketTerm Y' E') (curvLinear c E))
  have n2 := norm_add_le (trilinear Y Y' (curvQuadratic c E E') +
    trilinear (bracketTerm Y E) Y' (curvLinear c E') +
    trilinear (bracketTerm Y E') Y' (curvLinear c E))
    (trilinear Y (bracketTerm Y' E) (curvLinear c E'))
  have n3 := norm_add_le (trilinear Y Y' (curvQuadratic c E E') +
    trilinear (bracketTerm Y E) Y' (curvLinear c E'))
    (trilinear (bracketTerm Y E') Y' (curvLinear c E))
  have n4 := norm_add_le (trilinear Y Y' (curvQuadratic c E E'))
    (trilinear (bracketTerm Y E) Y' (curvLinear c E'))
  linarith
def exponentCoeff : Fin 4 → Fin 4 → ℂ :=
  ![![0, 0, 0, 0], ![Complex.I, 0, 0, 0], ![Complex.I, Complex.I, -Complex.I, 0],
    ![Complex.I, Complex.I, -Complex.I, -Complex.I]]
theorem norm_exponentCoeff_le (l j : Fin 4) : ‖exponentCoeff l j‖ ≤ 1 := by
  fin_cases l <;> fin_cases j <;> simp [exponentCoeff]
def cornerTransports (W : Fin 4 → ComplexMatrix2) : Fin 4 → ComplexMatrix2 :=
  ![1, W 0, W 0 * W 1 * (W 2)⁻¹, W 0 * W 1 * (W 2)⁻¹ * (W 3)⁻¹]
theorem inv_matExp_I_smul (X : ComplexMatrix2) :
    (ComplexMatrix2.matExp (Complex.I • X))⁻¹ = ComplexMatrix2.matExp ((-Complex.I) • X) := by
  rw [neg_smul]
  exact (Matrix.exp_neg _).symm
theorem cornerTransports_matExp (x : Fin 4 → ComplexMatrix2) (l : Fin 4) :
    cornerTransports (fun j => ComplexMatrix2.matExp (Complex.I • x j)) l =
      expProduct fun j => exponentCoeff l j • x j := by
  fin_cases l <;>
    simp [cornerTransports, expProduct, exponentCoeff, List.ofFn_succ, inv_matExp_I_smul, mul_assoc]
variable {L k : ℕ}
def sideStart (p : Face L k 0) : Fin 4 → Vertex L k 0 :=
  ![p.corner, p.corner + InfiniteLattice.axisStep _ p.lowAxis,
    p.corner + InfiniteLattice.axisStep _ p.highAxis, p.corner]
def sideAxis (p : Face L k 0) : Fin 4 → Fin 4 :=
  ![p.lowAxis, p.highAxis, p.lowAxis, p.highAxis]
theorem faceEdge_eq_forwardFrom (p : Face L k 0) (i : Fin 4) :
    faceEdge p i = InfiniteLattice.Link.forwardFrom (sideStart p i) (sideAxis p i) := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.faceEdge_eq_forwardFrom <;> assumption
def sideEdge (p : Face L k 0) (i : Fin 4) : PeriodicOperators.PosEdge L k 0 :=
  ⟨faceEdge p i, sideAxis p i, by
    rw [faceEdge_eq_forwardFrom]
    simp [InfiniteLattice.Link.forwardFrom]⟩
theorem initial_sideEdge (p : Face L k 0) (i : Fin 4) : (sideEdge p i).1.initial = sideStart p i := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.initial_posEdgeOfFace <;> assumption
theorem sideStart_coord (hη : 0 < finestMesh L k) (p : Face L k 0) (i : Fin 4) (μ : Fin 4) :
    0 ≤ (sideStart p i : InfiniteLattice.AmbientSpace) μ -
        (p.corner : InfiniteLattice.AmbientSpace) μ ∧
      (sideStart p i : InfiniteLattice.AmbientSpace) μ -
          (p.corner : InfiniteLattice.AmbientSpace) μ ≤ finestMesh L k := by
  have hs : ∀ ν, 0 ≤ ((InfiniteLattice.axisStep (meshAt L k 0) ν : Vertex L k 0) :
        InfiniteLattice.AmbientSpace) μ ∧
      ((InfiniteLattice.axisStep (meshAt L k 0) ν : Vertex L k 0) :
        InfiniteLattice.AmbientSpace) μ ≤ finestMesh L k := fun ν => by
    change 0 ≤ (Pi.single ν (finestMesh L k) : InfiniteLattice.AmbientSpace) μ ∧
      (Pi.single ν (finestMesh L k) : InfiniteLattice.AmbientSpace) μ ≤ _
    by_cases h : μ = ν
    · subst h
      rw [Pi.single_eq_same]
      exact ⟨hη.le, le_rfl⟩
    · rw [Pi.single_eq_of_ne h]
      exact ⟨le_rfl, hη.le⟩
  fin_cases i
  · simpa [sideStart] using hη.le
  · simpa [sideStart] using hs _
  · simpa [sideStart] using hs _
  · simpa [sideStart] using hη.le
theorem sideStart_withinBox (hη : 0 < finestMesh L k) (p : Face L k 0) (i j : Fin 4) :
    WithinBox (2 * finestMesh L k) (sideStart p j) (sideStart p i) := by
  intro μ
  obtain ⟨a, b⟩ := sideStart_coord hη p i μ
  obtain ⟨c, d⟩ := sideStart_coord hη p j μ
  rw [abs_le]
  constructor <;> linarith
theorem corner_withinBox (hη : 0 < finestMesh L k) (p : Face L k 0) (i : Fin 4) :
    WithinBox (2 * finestMesh L k) p.corner (sideStart p i) := by
  intro μ
  obtain ⟨a, b⟩ := sideStart_coord hη p i μ
  rw [abs_le]
  constructor <;> linarith
def IsSideOf (c : PeriodicOperators.PosEdge L k 0) (p : Face L k 0) : Prop :=
  ∃ i, sideEdge p i = c
theorem withinBox_of_isSideOf (hη : 0 < finestMesh L k) {c c' : PeriodicOperators.PosEdge L k 0}
    {p : Face L k 0} (h : IsSideOf c p) (h' : IsSideOf c' p) :
    WithinBox (2 * finestMesh L k) c.1.initial c'.1.initial := by
  obtain ⟨i, rfl⟩ := h
  obtain ⟨j, rfl⟩ := h'
  rw [initial_sideEdge, initial_sideEdge]
  exact sideStart_withinBox hη p j i
theorem mem_faceEdges_of_isSideOf {c : PeriodicOperators.PosEdge L k 0}
    {p : Face L k 0} (h : IsSideOf c p) :
    (c : InfiniteLattice.Link (meshAt L k 0)) ∈ faceEdges p := by
  obtain ⟨i, rfl⟩ := h
  change faceEdge p i ∈ faceEdges p
  exact List.getElem_mem _
theorem finite_isSideOf (hP : YangMills.Construction.Tower.FacesContainingEdge.Holds)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (c : PeriodicOperators.PosEdge L k 0) : {p : Face L k 0 | IsSideOf c p}.Finite := by
  refine ((hP L hL k 0 (Nat.zero_le k)).2.2.2 {c} (Set.finite_singleton c)).subset ?_
  intro p h
  exact ⟨c, rfl, mem_faceEdges_of_isSideOf h⟩
def facesOfEdge (hP : YangMills.Construction.Tower.FacesContainingEdge.Holds)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (c : PeriodicOperators.PosEdge L k 0) : Finset (Face L k 0) :=
  (finite_isSideOf hP hL c).toFinset
theorem card_facesOfEdge_le (hP : YangMills.Construction.Tower.FacesContainingEdge.Holds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (c : PeriodicOperators.PosEdge L k 0) :
    (facesOfEdge hP hL c).card ≤ 6 := by
  have h := (hP L hL k 0 (Nat.zero_le k)).2.2.1 c
  have h' : (↑(facesOfEdge hP hL c) : Set (Face L k 0)).encard ≤ 6 := by
    refine (Set.encard_le_encard ?_).trans h
    intro p hp
    exact mem_faceEdges_of_isSideOf ((finite_isSideOf hP hL c).mem_toFinset.1 hp)
  rw [Set.encard_coe_eq_coe_finsetCard] at h'
  exact_mod_cast h'
abbrev CoeffField (L k : ℕ) : Type := Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ
def valueAt (b : PeriodicOperators.PosEdge L k 0) : CoeffField L k →ₗ[ℂ] ComplexMatrix2 where
  toFun ζ := ofPauliCoeffs ζ b
  map_add' f g := by simp [ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp [ofPauliCoeffs, mul_smul, Finset.smul_sum]
def exponentsOn (p : Face L k 0) : CoeffField L k →ₗ[ℂ] ExponentArray :=
  LinearMap.pi fun l => LinearMap.pi fun j => exponentCoeff l j • valueAt (sideEdge p j)
theorem exponentsOn_apply (p : Face L k 0) (ζ : CoeffField L k) (l j : Fin 4) :
    exponentsOn p ζ l j = exponentCoeff l j • ofPauliCoeffs ζ (sideEdge p j) := rfl
theorem norm_exponentsOn_le (p : Face L k 0) (ζ : CoeffField L k) (l j : Fin 4) {m : ℝ}
    (h : ‖ofPauliCoeffs ζ (sideEdge p j)‖ ≤ m) : ‖exponentsOn p ζ l j‖ ≤ m := by
  rw [exponentsOn_apply, norm_smul]
  calc _ ≤ 1 * ‖ofPauliCoeffs ζ (sideEdge p j)‖ :=
        mul_le_mul_of_nonneg_right (norm_exponentCoeff_le l j) (norm_nonneg _)
    _ ≤ m := by simpa using h
theorem ofCoeffs_posEdge (f : CoeffField L k) (b : PeriodicOperators.PosEdge L k 0) :
    (edgePauliCoordinates L k 0).ofCoeffs f b.1 = ofPauliCoeffs f b := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.extendOddly_ofCoeffs_pos <;> assumption
def edgeMatrices (U : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) : Fin 4 → ComplexMatrix2 :=
  fun i => U (faceEdge p i)
def edgeValues (b : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) : Fin 4 → ComplexMatrix2 :=
  fun i => b (faceEdge p i)
theorem faceTransports_eq {U : Edge L k 0 → ComplexMatrix2}
    (hU : ∀ b : Edge L k 0, U b.opposite = (U b)⁻¹) (p : Face L k 0) :
    faceTransports U p = cornerTransports (edgeMatrices U p) := by
  funext i
  fin_cases i <;>
    simp [cornerTransports, edgeMatrices, faceTransports, faceVariable, linkHolonomy, faceBoundary,
      faceEdge, faceEdges, hU, mul_assoc]
theorem edgeMatrices_gaugeField (ζ : CoeffField L k) (p : Face L k 0) :
    edgeMatrices (gaugeFieldOfForm L k ζ) p =
      fun j => ComplexMatrix2.matExp (Complex.I • ofPauliCoeffs ζ (sideEdge p j)) := by
  classical
  funext j
  have hb : (faceEdge p j).IsPositivelyOriented := (sideEdge p j).2
  have h := ofCoeffs_posEdge ζ (sideEdge p j)
  simp only [edgeMatrices, gaugeFieldOfForm, expForm, expTwist, if_pos hb, Pi.one_apply, mul_one]
  exact congrArg (fun X => ComplexMatrix2.matExp (Complex.I • X)) h
theorem faceTransports_gaugeField (ζ : CoeffField L k)
    (hcfg : gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (p : Face L k 0) (l : Fin 4) :
    faceTransports (gaugeFieldOfForm L k ζ) p l = expProduct (exponentsOn p ζ l) := by
  rw [faceTransports_eq hcfg.2, edgeMatrices_gaugeField]
  exact cornerTransports_matExp _ l
theorem faceVariable_eq {U : Edge L k 0 → ComplexMatrix2}
    (hU : ∀ b : Edge L k 0, U b.opposite = (U b)⁻¹) (p : Face L k 0) :
    faceVariable U p = cornerTransports (edgeMatrices U p) 3 :=
  congrFun (faceTransports_eq hU p) 3
def faceContribution (U b b' : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) : ℂ :=
  (Complex.I / 2) * ComplexMatrix2.fullTrace
    (bracketSumOrdered (transportedForm U b p) (transportedForm U b' p) * curvatureMatrix U p)
def curvScale (L k : ℕ) : ℂ := 1 / (2 * Complex.I * (finestMesh L k : ℂ) ^ 2)
theorem faceContribution_gaugeField (ζ : CoeffField L k)
    (hcfg : gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (b b' : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) :
    faceContribution (gaugeFieldOfForm L k ζ) b b' p =
      faceTerm (curvScale L k) (edgeValues b p) (edgeValues b' p) (exponentsOn p ζ) := by
  have hT := fun l => faceTransports_gaugeField ζ hcfg p l
  have hV : ∀ c : Edge L k 0 → ComplexMatrix2, transportedForm (gaugeFieldOfForm L k ζ) c p =
      signedFamily fun l =>
        ComplexMatrix2.conjugateBy (expProduct (exponentsOn p ζ l)) (edgeValues c p l) := fun c => by
    funext i
    simp only [transportedForm, signedFamily, hT, edgeValues]
  have h3 : faceVariable (gaugeFieldOfForm L k ζ) p = expProduct (exponentsOn p ζ 3) := by
    rw [faceVariable_eq hcfg.2, edgeMatrices_gaugeField]
    exact cornerTransports_matExp _ 3
  have hS : curvatureMatrix (gaugeFieldOfForm L k ζ) p =
      curvScale L k • (expProduct (exponentsOn p ζ 3) - (expProduct (exponentsOn p ζ 3))⁻¹) := by
    rw [curvatureMatrix, h3, curvScale]
  rw [faceContribution, faceTerm, trilinear, hV, hV, hS]
  rfl
theorem bracketSumOrdered_zero_fst (Y : Fin 4 → ComplexMatrix2) : bracketSumOrdered 0 Y = 0 := by
  simp [bracketSumOrdered]
theorem bracketSumOrdered_zero_snd (Y : Fin 4 → ComplexMatrix2) : bracketSumOrdered Y 0 = 0 := by
  simp [bracketSumOrdered]
theorem transportedForm_eq_zero (U b : Edge L k 0 → ComplexMatrix2) (p : Face L k 0)
    (h : ∀ i, b (faceEdge p i) = 0) : transportedForm U b p = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.transportedForm_eq_zero <;> assumption
theorem faceContribution_zero_fst (U b b' : Edge L k 0 → ComplexMatrix2) (p : Face L k 0)
    (h : ∀ i, b (faceEdge p i) = 0) : faceContribution U b b' p = 0 := by
  simp [faceContribution, transportedForm_eq_zero U b p h, bracketSumOrdered_zero_fst,
    ComplexMatrix2.fullTrace]
theorem faceContribution_zero_snd (U b b' : Edge L k 0 → ComplexMatrix2) (p : Face L k 0)
    (h : ∀ i, b' (faceEdge p i) = 0) : faceContribution U b b' p = 0 := by
  simp [faceContribution, transportedForm_eq_zero U b' p h, bracketSumOrdered_zero_snd,
    ComplexMatrix2.fullTrace]
open Classical in
theorem basisForm_faceEdge (a : Fin 3) (c : PeriodicOperators.PosEdge L k 0)
    (p : Face L k 0) (i : Fin 4) :
    basisForm a c (faceEdge p i) = if sideEdge p i = c then ComplexMatrix2.pauliFamily a else 0 := by
  have hpos : (faceEdge p i).IsPositivelyOriented := (sideEdge p i).2
  simp only [basisForm, extendOddly, if_pos hpos]
  by_cases h : sideEdge p i = c
  · rw [if_pos h]
    exact if_pos (congrArg Subtype.val h)
  · rw [if_neg h]
    exact if_neg fun e => h (Subtype.ext e)
theorem basisForm_faceEdge_of_not (a : Fin 3) {c : PeriodicOperators.PosEdge L k 0}
    {p : Face L k 0} (h : ¬ IsSideOf c p) (i : Fin 4) :
    basisForm a c (faceEdge p i) = 0 := by
  classical
  rw [basisForm_faceEdge, if_neg fun e => h ⟨i, e⟩]
theorem curvatureBilinear_basis_eq (U : Edge L k 0 → ComplexMatrix2) (a a' : Fin 3)
    (c c' : PeriodicOperators.PosEdge L k 0) (Ω : Finset (Face L k 0))
    (hΩ : ∀ p, IsSideOf c p → IsSideOf c' p → p ∈ Ω) :
    curvatureBilinear U (basisForm a c) (basisForm a' c') =
      ((finestMesh L k : ℂ) ^ 4) *
        ∑ p ∈ Ω, faceContribution U (basisForm a c) (basisForm a' c') p := by
  rw [curvatureBilinear]
  congr 1
  refine finsum_eq_sum_of_support_subset
    (fun p => faceContribution U (basisForm a c) (basisForm a' c') p) ?_
  intro p hp
  by_contra hne
  apply hp
  by_cases h : IsSideOf c p
  · by_cases h' : IsSideOf c' p
    · exact absurd (hΩ p h h') hne
    · exact faceContribution_zero_snd _ _ _ _ fun i => basisForm_faceEdge_of_not a' h' i
  · exact faceContribution_zero_fst _ _ _ _ fun i => basisForm_faceEdge_of_not a h i
theorem finestMesh_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.finestMesh_pos <;> assumption
theorem curvatureKernel_eq_sum (hK : YangMills.Construction.Tower.FullSpace.CurvatureKernelEntries)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (U : Edge L k 0 → ComplexMatrix2)
    (a a' : Fin 3) (c c' : PeriodicOperators.PosEdge L k 0) (Ω : Finset (Face L k 0))
    (hΩ : ∀ p, IsSideOf c p → IsSideOf c' p → p ∈ Ω) :
    curvatureKernel U (a, c) (a', c') =
      (1 / 2 : ℂ) * (∑ p ∈ Ω, faceContribution U (basisForm a c) (basisForm a' c') p +
        ∑ p ∈ Ω, faceContribution U (basisForm a' c') (basisForm a c) p) := by
  have hη : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (finestMesh_pos (k := k) hL).ne'
  have h := hK L hL k hk U (a, c) (a', c')
  simp only at h
  rw [h, curvatureBilinear_basis_eq U a a' c c' Ω hΩ,
    curvatureBilinear_basis_eq U a' a c' c Ω fun p h h' => hΩ p h' h]
  push_cast
  field_simp
def pauliNormSum : ℝ := ∑ e, ‖ComplexMatrix2.pauliFamily e‖
theorem pauliNormSum_nonneg : 0 ≤ pauliNormSum := Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem norm_ofPauliCoeffs_le {σ : Type} (f : Fin 3 × σ → ℂ) (b : σ) {m : ℝ}
    (h : ∀ e, ‖f (e, b)‖ ≤ m) : ‖ofPauliCoeffs f b‖ ≤ pauliNormSum * m := by apply _root_.YangMills.Construction.Tower.FullSpace.HalfFaceTraceNearIndex.norm_ofPauliCoeffs_le <;> assumption
def basisValues (a : Fin 3) (c : PeriodicOperators.PosEdge L k 0) :
    Face L k 0 → Fin 4 → ComplexMatrix2 :=
  fun p => edgeValues (basisForm a c) p
theorem norm_basisValues_le (a : Fin 3) (c : PeriodicOperators.PosEdge L k 0)
    (p : Face L k 0) (i : Fin 4) : ‖basisValues a c p i‖ ≤ pauliNormSum := by
  classical
  change ‖basisForm a c (faceEdge p i)‖ ≤ _
  rw [basisForm_faceEdge]
  split_ifs
  · exact Finset.single_le_sum (f := fun e => ‖ComplexMatrix2.pauliFamily e‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  · simpa using pauliNormSum_nonneg
def entryLinear (Ω : Finset (Face L k 0)) (X X' : Face L k 0 → Fin 4 → ComplexMatrix2) :
    CoeffField L k →ₗ[ℂ] ℂ :=
  (1 / 2 : ℂ) • ∑ p ∈ Ω, ((linearPart (2 * curvScale L k) (X p) (X' p)).comp (exponentsOn p) +
    (linearPart (2 * curvScale L k) (X' p) (X p)).comp (exponentsOn p))
def entryQuadratic (Ω : Finset (Face L k 0)) (X X' : Face L k 0 → Fin 4 → ComplexMatrix2) :
    CoeffField L k →ₗ[ℂ] CoeffField L k →ₗ[ℂ] ℂ :=
  (1 / 2 : ℂ) • ∑ p ∈ Ω,
    ((quadraticPart (2 * curvScale L k) (X p) (X' p)).compl₁₂ (exponentsOn p) (exponentsOn p) +
      (quadraticPart (2 * curvScale L k) (X' p) (X p)).compl₁₂ (exponentsOn p) (exponentsOn p))
theorem entryLinear_apply (Ω : Finset (Face L k 0))
    (X X' : Face L k 0 → Fin 4 → ComplexMatrix2) (ζ : CoeffField L k) :
    entryLinear Ω X X' ζ = (1 / 2 : ℂ) * ∑ p ∈ Ω,
      (linearPart (2 * curvScale L k) (X p) (X' p) (exponentsOn p ζ) +
        linearPart (2 * curvScale L k) (X' p) (X p) (exponentsOn p ζ)) := by
  simp only [entryLinear, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.comp_apply, smul_eq_mul]
theorem entryQuadratic_apply (Ω : Finset (Face L k 0))
    (X X' : Face L k 0 → Fin 4 → ComplexMatrix2) (ζ ζ' : CoeffField L k) :
    entryQuadratic Ω X X' ζ ζ' = (1 / 2 : ℂ) * ∑ p ∈ Ω,
      (quadraticPart (2 * curvScale L k) (X p) (X' p) (exponentsOn p ζ) (exponentsOn p ζ') +
        quadraticPart (2 * curvScale L k) (X' p) (X p) (exponentsOn p ζ) (exponentsOn p ζ')) := by
  simp only [entryQuadratic, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.compl₁₂_apply, smul_eq_mul]
theorem curvatureKernel_gaugeField
    (hK : YangMills.Construction.Tower.FullSpace.CurvatureKernelEntries)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hcfg : ∀ ζ : CoeffField L k,
      gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (a a' : Fin 3) (c c' : PeriodicOperators.PosEdge L k 0)
    (Ω : Finset (Face L k 0)) (hΩ : ∀ p, IsSideOf c' p → IsSideOf c p → p ∈ Ω)
    (ζ : CoeffField L k) :
    curvatureKernel (gaugeFieldOfForm L k ζ) (a', c') (a, c) =
      (1 / 2 : ℂ) * ∑ p ∈ Ω,
        (faceTerm (curvScale L k) (basisValues a' c' p) (basisValues a c p) (exponentsOn p ζ) +
          faceTerm (curvScale L k) (basisValues a c p) (basisValues a' c' p) (exponentsOn p ζ)) := by
  rw [curvatureKernel_eq_sum hK hL hk _ a' a c' c Ω hΩ, ← Finset.sum_add_distrib]
  simp only [faceContribution_gaugeField ζ (hcfg ζ), basisValues]
theorem norm_half_sum_add_le {α : Type} (Ω : Finset α) (f g : α → ℂ) {b : ℝ}
    (hf : ∀ p ∈ Ω, ‖f p‖ ≤ b) (hg : ∀ p ∈ Ω, ‖g p‖ ≤ b) :
    ‖(1 / 2 : ℂ) * ∑ p ∈ Ω, (f p + g p)‖ ≤ Ω.card * b := by
  have h : ‖∑ p ∈ Ω, (f p + g p)‖ ≤ Ω.card * (2 * b) := by
    have := norm_sum_le_of_le (f := fun p => f p + g p) (n := fun _ => 2 * b) Ω fun p hp =>
      (norm_add_le _ _).trans (by linarith [hf p hp, hg p hp])
    simpa using this
  rw [norm_mul]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  linarith
def remainderConst (L k : ℕ) : ℝ :=
  23 * trilinearConst * expansionConst (curvScale L k) pauliNormSum ^ 3 * pauliNormSum ^ 3
theorem curvatureKernel_remainder (hE : ComplexMatrix2.ExpProductExpansionAndConjugation)
    (hX : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion)
    (hK : YangMills.Construction.Tower.FullSpace.CurvatureKernelEntries)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hcfg : ∀ ζ : CoeffField L k,
      gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (a a' : Fin 3) (c c' : PeriodicOperators.PosEdge L k 0)
    (Ω : Finset (Face L k 0)) (hΩ : ∀ p, IsSideOf c' p → IsSideOf c p → p ∈ Ω)
    (ζ : CoeffField L k) {m : ℝ} (hm : 0 ≤ m) (hr : 4 * (pauliNormSum * m) ≤ 1)
    (hζ : ∀ p ∈ Ω, ∀ j e, ‖ζ (e, sideEdge p j)‖ ≤ m) :
    ‖curvatureKernel (gaugeFieldOfForm L k ζ) (a', c') (a, c) -
        curvatureKernel (gaugeFieldOfForm L k 0) (a', c') (a, c) -
        entryLinear Ω (basisValues a' c') (basisValues a c) ζ -
        (1 / 2 : ℂ) * entryQuadratic Ω (basisValues a' c') (basisValues a c) ζ ζ‖ ≤
      (Ω.card * remainderConst L k) * m ^ 3 := by
  have hP := pauliNormSum_nonneg
  have e0 : curvatureKernel (gaugeFieldOfForm L k 0) (a', c') (a, c) = 0 :=
    (curvatureKernel_gaugeField hK hL hk hcfg a a' c c' Ω hΩ 0).trans
      (by simp [map_zero, faceTerm_zero])
  have hu : 0 ≤ pauliNormSum * m := mul_nonneg hP hm
  have hEu : ∀ p ∈ Ω, ∀ l j, ‖exponentsOn p ζ l j‖ ≤ pauliNormSum * m := fun p hp l j =>
    norm_exponentsOn_le p ζ l j (norm_ofPauliCoeffs_le ζ _ fun e => hζ p hp j e)
  have ht : ∀ (X X' : Fin 4 → ComplexMatrix2), (∀ i, ‖X i‖ ≤ pauliNormSum) →
      (∀ i, ‖X' i‖ ≤ pauliNormSum) →
      ∀ p ∈ Ω, ‖faceTerm (curvScale L k) X X' (exponentsOn p ζ) -
          linearPart (2 * curvScale L k) X X' (exponentsOn p ζ) -
          (1 / 2 : ℂ) * quadraticPart (2 * curvScale L k) X X' (exponentsOn p ζ)
            (exponentsOn p ζ)‖ ≤ remainderConst L k * m ^ 3 := fun X X' hX₁ hX₂ p hp => by
    refine (faceTerm_expansion hE hX _ hP hX₁ hX₂ hu hr (hEu p hp)).trans (le_of_eq ?_)
    rw [remainderConst]
    ring
  have e : curvatureKernel (gaugeFieldOfForm L k ζ) (a', c') (a, c) -
        curvatureKernel (gaugeFieldOfForm L k 0) (a', c') (a, c) -
        entryLinear Ω (basisValues a' c') (basisValues a c) ζ -
        (1 / 2 : ℂ) * entryQuadratic Ω (basisValues a' c') (basisValues a c) ζ ζ =
      (1 / 2 : ℂ) * ∑ p ∈ Ω,
        ((faceTerm (curvScale L k) (basisValues a' c' p) (basisValues a c p) (exponentsOn p ζ) -
            linearPart (2 * curvScale L k) (basisValues a' c' p) (basisValues a c p)
              (exponentsOn p ζ) -
            (1 / 2 : ℂ) * quadraticPart (2 * curvScale L k) (basisValues a' c' p)
              (basisValues a c p) (exponentsOn p ζ) (exponentsOn p ζ)) +
          (faceTerm (curvScale L k) (basisValues a c p) (basisValues a' c' p) (exponentsOn p ζ) -
            linearPart (2 * curvScale L k) (basisValues a c p) (basisValues a' c' p)
              (exponentsOn p ζ) -
            (1 / 2 : ℂ) * quadraticPart (2 * curvScale L k) (basisValues a c p)
              (basisValues a' c' p) (exponentsOn p ζ) (exponentsOn p ζ))) := by
    rw [e0, curvatureKernel_gaugeField hK hL hk hcfg a a' c c' Ω hΩ ζ, entryLinear_apply,
      entryQuadratic_apply, sub_zero]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [e]
  refine (norm_half_sum_add_le Ω _ _ (b := remainderConst L k * m ^ 3)
    (fun p hp => ht _ _ (norm_basisValues_le a' c' p) (norm_basisValues_le a c p) p hp)
    (fun p hp => ht _ _ (norm_basisValues_le a c p) (norm_basisValues_le a' c' p) p hp)).trans
    (le_of_eq ?_)
  ring
theorem coeffs_eq_entryForms (hT : PeriodicOperators.ExpansionCoefficients.Claim)
    (hE : ComplexMatrix2.ExpProductExpansionAndConjugation)
    (hX : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion)
    (hK : YangMills.Construction.Tower.FullSpace.CurvatureKernelEntries)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hcfg : ∀ ζ : CoeffField L k,
      gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (hB : IsPeriodic (colourEdges L k 0))
    (hloc : IsLocalOpFun (remainderIndex L k) (colourEdges L k 0)
      (colourEdges L k 0) (fun f => curvatureKernel (gaugeFieldOfForm L k f)))
    (a a' : Fin 3) (c c' : PeriodicOperators.PosEdge L k 0)
    (Ω : Finset (Face L k 0)) (hΩ : ∀ p, IsSideOf c' p → IsSideOf c p → p ∈ Ω)
    (ζ ζ' : CoeffField L k) :
    coeffOne (remainderIndex L k) (colourEdges L k 0) (colourEdges L k 0)
        (fun f => curvatureKernel (gaugeFieldOfForm L k f)) ζ (a', c') (a, c) =
      entryLinear Ω (basisValues a' c') (basisValues a c) ζ ∧
    coeffTwo (remainderIndex L k) (colourEdges L k 0) (colourEdges L k 0)
        (fun f => curvatureKernel (gaugeFieldOfForm L k f)) ζ ζ' (a', c') (a, c) =
      entryQuadratic Ω (basisValues a' c') (basisValues a c) ζ ζ' := by
  classical
  have hP := pauliNormSum_nonneg
  set Sf : Finset (Fin 3 × PeriodicOperators.PosEdge L k 0) :=
    insert (0, c') (Ω.biUnion fun p => Finset.univ.image fun q : Fin 3 × Fin 4 =>
      ((q.1, sideEdge p q.2) : Fin 3 × PeriodicOperators.PosEdge L k 0)) with hSf
  have hmem : ∀ p ∈ Ω, ∀ (e : Fin 3) (j : Fin 4), (e, sideEdge p j) ∈ Sf := fun p hp e j =>
    Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2
      ⟨(e, j), Finset.mem_univ _, rfl⟩⟩)
  have hcongr : ∀ ζ₁ ζ₂ : CoeffField L k,
      (∀ κ ∈ (Sf : Set (Fin 3 × PeriodicOperators.PosEdge L k 0)), ζ₁ κ = ζ₂ κ) → ∀ p ∈ Ω,
      exponentsOn p ζ₁ = exponentsOn p ζ₂ := fun ζ₁ ζ₂ h p hp => by
    funext l j
    simp only [exponentsOn_apply, ofPauliCoeffs]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [h (e, sideEdge p j) (hmem p hp e j)]
  have hsym : ∀ ζ₁ ζ₂ : CoeffField L k, entryQuadratic Ω (basisValues a' c') (basisValues a c) ζ₁ ζ₂ =
      entryQuadratic Ω (basisValues a' c') (basisValues a c) ζ₂ ζ₁ := fun ζ₁ ζ₂ => by
    rw [entryQuadratic_apply, entryQuadratic_apply]
    refine congrArg (fun x => (1 / 2 : ℂ) * x) (Finset.sum_congr rfl fun p _ => ?_)
    rw [quadraticPart_comm _ (basisValues a' c' p), quadraticPart_comm _ (basisValues a c p)]
  have hread : ∀ ζ₁ ζ₂ : CoeffField L k,
      (∀ κ ∈ (Sf : Set (Fin 3 × PeriodicOperators.PosEdge L k 0)), ζ₁ κ = ζ₂ κ) →
      entryLinear Ω (basisValues a' c') (basisValues a c) ζ₁ =
          entryLinear Ω (basisValues a' c') (basisValues a c) ζ₂ ∧
        ∀ ξ : CoeffField L k, entryQuadratic Ω (basisValues a' c') (basisValues a c) ζ₁ ξ =
          entryQuadratic Ω (basisValues a' c') (basisValues a c) ζ₂ ξ := fun ζ₁ ζ₂ h => by
    refine ⟨?_, fun ξ => ?_⟩
    · rw [entryLinear_apply, entryLinear_apply]
      refine congrArg (fun x => (1 / 2 : ℂ) * x) (Finset.sum_congr rfl fun p hp => ?_)
      rw [hcongr ζ₁ ζ₂ h p hp]
    · rw [entryQuadratic_apply, entryQuadratic_apply]
      refine congrArg (fun x => (1 / 2 : ℂ) * x) (Finset.sum_congr rfl fun p hp => ?_)
      rw [hcongr ζ₁ ζ₂ h p hp]
  have hbd : ∀ (ζ₁ : CoeffField L k) (m : ℝ), m ≤ 1 / (4 * pauliNormSum + 1) →
      (∀ κ ∈ (Sf : Set (Fin 3 × PeriodicOperators.PosEdge L k 0)), ‖ζ₁ κ‖ ≤ m) →
      ‖curvatureKernel (gaugeFieldOfForm L k ζ₁) (a', c') (a, c) -
        curvatureKernel (gaugeFieldOfForm L k 0) (a', c') (a, c) -
        entryLinear Ω (basisValues a' c') (basisValues a c) ζ₁ -
        (1 / 2 : ℂ) * entryQuadratic Ω (basisValues a' c') (basisValues a c) ζ₁ ζ₁‖ ≤
      (Ω.card * remainderConst L k) * m ^ 3 := by
    intro ζ₁ m hm h
    have hm0 : 0 ≤ m := (norm_nonneg _).trans (h (0, c') (Finset.mem_insert_self _ _))
    have hr : 4 * (pauliNormSum * m) ≤ 1 := by
      have h1 : (4 * pauliNormSum + 1) * m ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4 * pauliNormSum + 1)
        rwa [mul_one_div_cancel (by positivity)] at this
      nlinarith
    exact curvatureKernel_remainder hE hX hK hL hk hcfg a a' c c' Ω hΩ ζ₁ hm0 hr
      fun p hp j e => h _ (hmem p hp e j)
  exact hT (remainderIndex L k) (colourEdges L k 0) (colourEdges L k 0) hB hB hB _ hloc
    (a', c') (a, c) (Sf : Set (Fin 3 × PeriodicOperators.PosEdge L k 0)) (Finset.finite_toSet Sf)
    (entryLinear Ω (basisValues a' c') (basisValues a c))
    (entryQuadratic Ω (basisValues a' c') (basisValues a c))
    (1 / (4 * pauliNormSum + 1)) (Ω.card * remainderConst L k)
    (by positivity) hsym hread hbd ζ ζ'
theorem ofPauliCoeffs_smul (c : ℂ) (A : CoeffField L k)
    (b : PeriodicOperators.PosEdge L k 0) :
    ofPauliCoeffs (c • A) b = c • ofPauliCoeffs A b :=
  map_smul (valueAt b) c A
theorem curvLinear_scaled (hη : 0 < finestMesh L k) (A : CoeffField L k) (p : Face L k 0) :
    curvLinear (2 * curvScale L k) (exponentsOn p (((finestMesh L k : ℝ) : ℂ) • A)) =
      scaledEdgeCoboundary ((edgePauliCoordinates L k 0).ofCoeffs A) p := by
  have hη' : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  set X : Fin 4 → ComplexMatrix2 := fun j => ofPauliCoeffs A (sideEdge p j) with hX
  have hv : ∀ i, (edgePauliCoordinates L k 0).ofCoeffs A (faceEdge p i) = X i :=
    fun i => ofCoeffs_posEdge A (sideEdge p i)
  have hd : edgeCoboundary ((edgePauliCoordinates L k 0).ofCoeffs A) p = X 0 + X 1 - X 2 - X 3 := by
    change (edgePauliCoordinates L k 0).ofCoeffs A (faceEdge p 0) +
      (edgePauliCoordinates L k 0).ofCoeffs A (faceEdge p 1) -
      (edgePauliCoordinates L k 0).ofCoeffs A (faceEdge p 2) -
      (edgePauliCoordinates L k 0).ofCoeffs A (faceEdge p 3) = _
    rw [hv, hv, hv, hv]
  have hc : 2 * curvScale L k * (Complex.I * ((finestMesh L k : ℝ) : ℂ)) =
      (((finestMesh L k)⁻¹ : ℝ) : ℂ) := by
    rw [curvScale]
    push_cast
    field_simp
  have e : curvLinear (2 * curvScale L k)
        (exponentsOn p (((finestMesh L k : ℝ) : ℂ) • A)) =
      (2 * curvScale L k * (Complex.I * ((finestMesh L k : ℝ) : ℂ))) •
        (X 0 + X 1 - X 2 - X 3) := by
    rw [curvLinear_apply, Fin.sum_univ_four]
    simp only [exponentsOn_apply, ofPauliCoeffs_smul]
    have f0 : exponentCoeff 3 0 = Complex.I := by simp [exponentCoeff]
    have f1 : exponentCoeff 3 1 = Complex.I := by simp [exponentCoeff]
    have f2 : exponentCoeff 3 2 = -Complex.I := by simp [exponentCoeff]
    have f3 : exponentCoeff 3 3 = -Complex.I := by simp [exponentCoeff]
    rw [f0, f1, f2, f3]
    simp only [hX]
    module
  rw [e, hc]
  change _ = (meshAt L k 0)⁻¹ • edgeCoboundary ((edgePauliCoordinates L k 0).ofCoeffs A) p
  rw [hd]
  ext r s
  simp [finestMesh]
theorem norm_two_curvScale_mul (hη : 0 < finestMesh L k) :
    ‖2 * curvScale L k‖ * (finestMesh L k) ^ 2 = 1 := by
  have hη' := hη.ne'
  rw [curvScale]
  simp [abs_of_pos hη]
  field_simp
theorem norm_exponentsOn_scaled_le (hη : 0 < finestMesh L k) (A : CoeffField L k)
    (p : Face L k 0) {M : ℝ} (hA : ∀ j, ‖ofPauliCoeffs A (sideEdge p j)‖ ≤ M) (l j : Fin 4) :
    ‖exponentsOn p (((finestMesh L k : ℝ) : ℂ) • A) l j‖ ≤ finestMesh L k * M := by
  refine norm_exponentsOn_le p _ l j ?_
  rw [ofPauliCoeffs_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hη.le]
  exact mul_le_mul_of_nonneg_left (hA j) hη.le
theorem curvatureKernelCoeffsBounded_holds (hT : PeriodicOperators.ExpansionCoefficients.Claim)
    (hX : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion)
    (hE : ComplexMatrix2.ExpProductExpansionAndConjugation)
    (hLoc : YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.CurvatureKernelIsLocal)
    (hK : YangMills.Construction.Tower.FullSpace.CurvatureKernelEntries)
    (hEnt : YangMills.Construction.Tower.FullSpace.GaugeFieldOfFormEntries)
    (hP : YangMills.Construction.Tower.FacesContainingEdge.Holds)
    (hI : PeriodicOperators.TowerIndexSets.Claim) :
    YangMills.Construction.Tower.FullSpace.CurvatureKernelCoeffs.CurvatureKernelCoeffsBounded := by
  classical
  intro L hL
  have hκ := trilinearConst_nonneg
  have hπ := pauliNormSum_nonneg
  refine ⟨384 * trilinearConst * pauliNormSum ^ 2, by positivity, fun k hk => ?_⟩
  have hη : 0 < finestMesh L k := finestMesh_pos hL
  have hη1 : finestMesh L k ≤ 1 := by
    have hL1 : (1 : ℝ) ≤ L := by
      have := hL.2
      exact_mod_cast (by omega : 1 ≤ L)
    exact zpow_le_one_of_nonpos₀ hL1 (by simp)
  have hcfg := (hEnt L hL k).1
  obtain ⟨-, hB, -⟩ := hI L hL k 0 (Nat.zero_le k)
  have hloc : IsLocalOpFun (remainderIndex L k) (colourEdges L k 0)
      (colourEdges L k 0) (fun f => curvatureKernel (gaugeFieldOfForm L k f)) :=
    ⟨1, 2 * finestMesh L k, (hLoc L hL k hk).1 1 one_pos⟩
  have hco := fun a a' c c' Ω hΩ ζ ζ' =>
    coeffs_eq_entryForms hT hE hX hK hL hk hcfg hB hloc a a' c c' Ω hΩ ζ ζ'
  refine ⟨?_, ?_⟩
  · rintro ζ ζ' ⟨a', c'⟩ ⟨a, c⟩ hfar
    obtain ⟨h₁, h₂⟩ := hco a a' c c' ∅
      (fun p h' h => absurd (withinBox_of_isSideOf hη h h') hfar) ζ ζ'
    refine ⟨h₁.trans ?_, h₂.trans ?_⟩
    · exact (entryLinear_apply _ _ _ _).trans (by simp)
    · exact (entryQuadratic_apply _ _ _ _ _).trans (by simp)
  · rintro A A' M ⟨a', c'⟩ ⟨a, c⟩ hM hA hA'
    set Ω : Finset (Face L k 0) := facesOfEdge hP hL c' ∩ facesOfEdge hP hL c with hΩdef
    have hΩ : ∀ p, IsSideOf c' p → IsSideOf c p → p ∈ Ω := fun p h h' =>
      Finset.mem_inter.2 ⟨(finite_isSideOf hP hL c').mem_toFinset.2 h,
        (finite_isSideOf hP hL c).mem_toFinset.2 h'⟩
    have hΩ' : ∀ p ∈ Ω, IsSideOf c' p := fun p hp =>
      (finite_isSideOf hP hL c').mem_toFinset.1 (Finset.mem_inter.1 hp).1
    have hcard : (Ω.card : ℝ) ≤ 6 := by
      have h1 : Ω.card ≤ (facesOfEdge hP hL c').card :=
        Finset.card_le_card Finset.inter_subset_left
      have h2 := card_facesOfEdge_le hP hL c'
      exact_mod_cast h1.trans h2
    have hbond : ∀ {B : CoeffField L k}, FieldBoundedNear L k c'.1.initial B M → ∀ p ∈ Ω, ∀ j,
        ‖ofPauliCoeffs B (sideEdge p j)‖ ≤ M := fun {B} hB' p hp j =>
      hB'.1 (sideEdge p j) (withinBox_of_isSideOf hη ⟨j, rfl⟩ (hΩ' p hp))
    have hstr : ∀ {B : CoeffField L k}, FieldBoundedNear L k c'.1.initial B M → ∀ p ∈ Ω,
        ‖curvLinear (2 * curvScale L k)
          (exponentsOn p (((finestMesh L k : ℝ) : ℂ) • B))‖ ≤ M := fun {B} hB' p hp => by
      rw [curvLinear_scaled hη]
      obtain ⟨i, hi⟩ := hΩ' p hp
      refine hB'.2 p ?_
      rw [← hi, initial_sideEdge]
      exact corner_withinBox hη p i
    have hv : finestMesh L k * M ≤ M := by nlinarith
    have hv0 : 0 ≤ finestMesh L k * M := mul_nonneg hη.le hM
    have hc : ‖2 * curvScale L k‖ * (finestMesh L k * M) ^ 2 ≤ M ^ 2 := by
      have := norm_two_curvScale_mul hη
      calc _ = (‖2 * curvScale L k‖ * finestMesh L k ^ 2) * M ^ 2 := by ring
        _ = M ^ 2 := by rw [this, one_mul]
        _ ≤ M ^ 2 := le_rfl
    obtain ⟨h₁, -⟩ := hco a a' c c' Ω hΩ (((finestMesh L k : ℝ) : ℂ) • A)
      (((finestMesh L k : ℝ) : ℂ) • A')
    obtain ⟨-, h₂⟩ := hco a a' c c' Ω hΩ (((finestMesh L k : ℝ) : ℂ) • A)
      (((finestMesh L k : ℝ) : ℂ) • A')
    refine ⟨(congrArg norm h₁).le.trans ?_, (congrArg norm h₂).le.trans ?_⟩
    · refine (le_of_eq (congrArg norm (entryLinear_apply _ _ _ _))).trans ?_
      refine (norm_half_sum_add_le Ω _ _ (b := trilinearConst * pauliNormSum * pauliNormSum * M)
        (fun p hp => norm_linearPart_le hπ (norm_basisValues_le a' c' p)
          (norm_basisValues_le a c p) (hstr hA p hp))
        (fun p hp => norm_linearPart_le hπ (norm_basisValues_le a c p)
          (norm_basisValues_le a' c' p) (hstr hA p hp))).trans ?_
      have hb : 0 ≤ trilinearConst * pauliNormSum * pauliNormSum * M := by positivity
      have h6 : (Ω.card : ℝ) * (trilinearConst * pauliNormSum * pauliNormSum * M) ≤
          6 * (trilinearConst * pauliNormSum * pauliNormSum * M) :=
        mul_le_mul_of_nonneg_right hcard hb
      nlinarith
    · refine (le_of_eq (congrArg norm (entryQuadratic_apply _ _ _ _ _))).trans ?_
      have hs : ∀ (X X' : Fin 4 → ComplexMatrix2), (∀ i, ‖X i‖ ≤ pauliNormSum) →
          (∀ i, ‖X' i‖ ≤ pauliNormSum) → ∀ p ∈ Ω,
          ‖quadraticPart (2 * curvScale L k) X X'
            (exponentsOn p (((finestMesh L k : ℝ) : ℂ) • A))
            (exponentsOn p (((finestMesh L k : ℝ) : ℂ) • A'))‖ ≤
          64 * trilinearConst * pauliNormSum ^ 2 * M ^ 2 := fun X X' hX₁ hX₂ p hp =>
        norm_quadraticPart_le hπ hv0 hv hX₁ hX₂
          (norm_exponentsOn_scaled_le hη A p (hbond hA p hp))
          (norm_exponentsOn_scaled_le hη A' p (hbond hA' p hp)) (hstr hA p hp) (hstr hA' p hp) hc
      refine (norm_half_sum_add_le Ω _ _ (b := 64 * trilinearConst * pauliNormSum ^ 2 * M ^ 2)
        (fun p hp => hs _ _ (norm_basisValues_le a' c' p) (norm_basisValues_le a c p) p hp)
        (fun p hp => hs _ _ (norm_basisValues_le a c p) (norm_basisValues_le a' c' p) p hp)).trans ?_
      have hb : 0 ≤ 64 * trilinearConst * pauliNormSum ^ 2 * M ^ 2 := by positivity
      have h6 := mul_le_mul_of_nonneg_right hcard hb
      calc _ ≤ 6 * (64 * trilinearConst * pauliNormSum ^ 2 * M ^ 2) := h6
        _ = _ := by ring
end YangMills.Construction.Tower.FullSpace.CurvatureKernelCoeffs
end
