import YangMills.Construction.Matrices.ConjugationInvariantForms
import YangMills.Construction.Towers.ChainRuleAtTheSideInfinityInTheLeftChartProof
import YangMills.Construction.Towers.ConfigurationsNearOneHaveSmallIterates
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.SmallIterates
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.IteratedSmallFieldMeans (AdmissibleConstants)
theorem opposite_isPositivelyOriented_of_not {a : ℝ} (ha : 0 < a)
    {b : YangMills.Construction.InfiniteLattice.Link a} (h : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpaceChainRule.opposite_isPositivelyOriented_of_not <;> assumption
theorem extendOddly_mem {a : ℝ} (ha : 0 < a)
    {f : YangMills.Construction.InfiniteLattice.Link a → ComplexMatrix2}
    (h : ∀ b : YangMills.Construction.InfiniteLattice.Link a, b.IsPositivelyOriented →
      f b ∈ ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms a := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.extendOddly_mem <;> assumption
theorem extendOddly_norm_le {a : ℝ} (ha : 0 < a)
    {f : YangMills.Construction.InfiniteLattice.Link a → ComplexMatrix2} {r : ℝ}
    (h : ∀ b : YangMills.Construction.InfiniteLattice.Link a, b.IsPositivelyOriented →
      ComplexMatrix2.operatorNorm (f b) ≤ r)
    (b : YangMills.Construction.InfiniteLattice.Link a) :
    ComplexMatrix2.operatorNorm (extendOddly f b) ≤ r := by
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly, if_pos hb]
    exact h b hb
  · rw [extendOddly, if_neg hb]
    show ‖-f b.opposite‖ ≤ r
    rw [norm_neg]
    exact h _ (opposite_isPositivelyOriented_of_not ha hb)
variable {L k : ℕ}
theorem finestMesh_pos (hL : 0 < L) (k : ℕ) : 0 < finestMesh L k :=
  zpow_pos (by exact_mod_cast hL) _
theorem pointwiseBounds_of_small {r C : ℝ} (hN : AdmissibleConstants L r C) (hk : 1 ≤ k)
    {a : Edge L k 0 → ComplexMatrix2}
    (ha : a ∈ complexEdgeForms (meshAt L k 0))
    (hs : ∀ b, ComplexMatrix2.operatorNorm (a b) ≤ r) :
    IteratedSmallFieldMeans.PointwiseConditions L k C a := by
  obtain ⟨_, _, _, hall⟩ := hN
  exact (hall k hk).2.pointwise a ⟨ha, iSup_le fun b => ENNReal.ofReal_le_ofReal (hs b)⟩
theorem expForm_of_pos (B : Edge L k 0 → ComplexMatrix2) {b : Edge L k 0}
    (hb : b.IsPositivelyOriented) :
    expForm B b = ComplexMatrix2.matExp (Complex.I • B b) := by
  show expTwist B 1 b = _
  rw [expTwist, if_pos hb]
  simp
theorem expForm_of_not_pos (B : Edge L k 0 → ComplexMatrix2) {b : Edge L k 0}
    (hb : ¬b.IsPositivelyOriented) :
    expForm B b = (ComplexMatrix2.matExp (Complex.I • B b.opposite))⁻¹ := by
  show expTwist B 1 b = _
  rw [expTwist, if_neg hb]
  simp
def logForm (L k : ℕ) (W : Edge L k 0 → ComplexMatrix2) : Edge L k 0 → ComplexMatrix2 :=
  extendOddly fun b => (Complex.I * (finestMesh L k : ℂ))⁻¹ • ComplexMatrix2.logSeries (W b)
theorem I_smul_mesh_smul_inv_smul (hL : 0 < L) (X : ComplexMatrix2) :
    Complex.I • finestMesh L k • (Complex.I * (finestMesh L k : ℂ))⁻¹ • X = X := by
  have hη : (finestMesh L k : ℂ) ≠ 0 := by
    exact_mod_cast (finestMesh_pos hL k).ne'
  rw [← Complex.coe_smul, smul_smul, smul_smul,
    mul_inv_cancel₀ (mul_ne_zero Complex.I_ne_zero hη), one_smul]
theorem remainderGaugeField_logForm (hL : 0 < L)
    (hE : ComplexMatrix2.ExpLogEstimates) {W : Edge L k 0 → ComplexMatrix2}
    (hW : W ∈ fieldsValuedIn L k 0 YangMills.Construction.PeriodicLattice.complexGaugeGroup)
    (hs : ∀ b, ComplexMatrix2.operatorNorm (W b - 1) < 1 / 2) :
    remainderGaugeField (logForm L k W) = W := by
  have ha : 0 < meshAt L k 0 := finestMesh_pos hL k
  have hexp : ∀ b : Edge L k 0, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • scaledRemainderForm (logForm L k W) b) = W b := by
    intro b hb
    have h := (hE.2.2.2.1 (W b - 1) ((hs b).trans (by norm_num))).2.2.2.2
    rw [add_sub_cancel] at h
    show ComplexMatrix2.matExp (Complex.I • finestMesh L k • logForm L k W b) = W b
    rw [logForm, extendOddly, if_pos hb, I_smul_mesh_smul_inv_smul hL, h]
  funext b
  show expForm _ b = W b
  by_cases hb : b.IsPositivelyOriented
  · rw [expForm_of_pos _ hb]
    exact hexp b hb
  · rw [expForm_of_not_pos _ hb, hexp _ (opposite_isPositivelyOriented_of_not ha hb)]
    exact (hW.2 b.opposite).symm
theorem logForm_mem (hL : 0 < L) (hE : ComplexMatrix2.ExpLogEstimates)
    {W : Edge L k 0 → ComplexMatrix2}
    (hW : W ∈ fieldsValuedIn L k 0 YangMills.Construction.PeriodicLattice.complexGaugeGroup)
    (hs : ∀ b, ComplexMatrix2.operatorNorm (W b - 1) < 1 / 2) :
    logForm L k W ∈ complexEdgeForms (meshAt L k 0) := by
  refine extendOddly_mem (finestMesh_pos hL k) fun b _ => ?_
  refine ComplexMatrix2.traceless.smul_mem _ (hE.2.2.2.2.2.2.1 (W b) (hW.1 b) ?_).2
  have := hs b
  linarith
theorem logForm_norm_le (hL : 0 < L) (hE : ComplexMatrix2.ExpLogEstimates)
    {W : Edge L k 0 → ComplexMatrix2} {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hs : ∀ b, ComplexMatrix2.operatorNorm (W b - 1) < δ) (b : Edge L k 0) :
    ComplexMatrix2.operatorNorm (logForm L k W b) ≤ 2 * δ / finestMesh L k := by
  have hη := finestMesh_pos hL k
  refine extendOddly_norm_le hη (fun b _ => ?_) b
  have hlt : ComplexMatrix2.operatorNorm (W b - 1) < 1 := (hs b).trans_le (by linarith)
  have h := hE.2.2.2.1 (W b - 1) hlt
  have h₁ := h.1.trans h.2.1
  rw [add_sub_cancel] at h₁
  have h₀ : 0 ≤ ComplexMatrix2.operatorNorm (W b - 1) := norm_nonneg _
  have h₂ : ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries (W b)) ≤ 2 * δ := by
    refine h₁.trans ?_
    rw [div_le_iff₀ (by linarith [hs b])]
    nlinarith [hs b]
  show ‖(Complex.I * (finestMesh L k : ℂ))⁻¹ • ComplexMatrix2.logSeries (W b)‖ ≤ _
  rw [norm_smul, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hη.le, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right h₂ hη.le
theorem backgroundOfCoeffs_mem (hL : 0 < L)
    (f : YangMills.Construction.LocalKernels.FieldIdx L k hL → ℂ) :
    backgroundOfCoeffs hL f ∈ complexEdgeForms (meshAt L k 0) := by
  refine extendOddly_mem (a := meshAt L k 0) (finestMesh_pos hL k) fun b hb => ?_
  rw [dif_pos hb]
  exact Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (ConjugationInvariants.pauliFamily_mem_traceless a)
theorem backgroundOfCoeffs_norm_le (hL : 0 < L)
    {f : YangMills.Construction.LocalKernels.FieldIdx L k hL → ℂ}
    {s : ℝ} (hf : ∀ κ, ‖f κ‖ ≤ s) (b : Edge L k 0) :
    ComplexMatrix2.operatorNorm (backgroundOfCoeffs hL f b) ≤
      s * ∑ a, ‖ComplexMatrix2.pauliFamily a‖ := by
  refine extendOddly_norm_le (a := meshAt L k 0) (finestMesh_pos hL k) (fun b hb => ?_) b
  rw [dif_pos hb]
  show ‖∑ a, _‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)
theorem remainderGaugeField_inv_mesh_smul (hL : 0 < L) (B : Edge L k 0 → ComplexMatrix2) :
    remainderGaugeField (((finestMesh L k : ℂ))⁻¹ • B) = expForm B := by
  have hη : (finestMesh L k : ℂ) ≠ 0 := by
    exact_mod_cast (finestMesh_pos hL k).ne'
  show expForm (finestMesh L k • ((finestMesh L k : ℂ))⁻¹ • B) = _
  congr 1
  funext b
  show finestMesh L k • ((finestMesh L k : ℂ))⁻¹ • B b = B b
  rw [← Complex.coe_smul, smul_smul, mul_inv_cancel₀ hη, one_smul]
theorem smallIteratesNearOne_of (h₁ : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (h₂ : Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (h₃ : ComplexMatrix2.ExpLogEstimates) : SmallIteratesNearOne := by
  intro L hL hS k hk
  have hρ : 0 < polydiscRadius L := (h₁.1 L hS).2.2.pos
  have hN := h₂.1 L hS
  obtain ⟨hr, -, -, -⟩ := id hN
  have hη := finestMesh_pos hL k
  set r := Tower.IteratedSmallFieldMeans.smallRadius L
  set C := Tower.IteratedSmallFieldMeans.boundConstant L
  refine ⟨?_, ?_⟩
  · by_cases hk1 : k = 1
    · subst hk1
      refine ⟨fun _ => polydiscRadius L, fun _ _ => hρ, fun _ _ => le_rfl, rfl,
        fun W hW hb => ⟨⟨hW, fun j hj => ?_⟩, fun j hj b => ?_⟩⟩
      · obtain rfl : j = 0 := by omega
        exact ⟨hW, hb⟩
      · obtain rfl : j = 0 := by omega
        exact hb b
    · set δ : ℝ := min (polydiscRadius L) (min (1 / 2) (r * finestMesh L k / 2)) with hδ
      have hδ0 : 0 < δ := lt_min hρ (lt_min (by norm_num) (by positivity))
      have hδρ : δ ≤ polydiscRadius L := min_le_left _ _
      have hδ2 : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
      have hδr : δ ≤ r * finestMesh L k / 2 := (min_le_right _ _).trans (min_le_right _ _)
      refine ⟨fun j => if j = 0 then δ else polydiscRadius L, fun j _ => ?_,
        fun j _ => ?_, ?_, fun W hW hb => ?_⟩
      · dsimp only
        split_ifs
        exacts [hδ0, hρ]
      · dsimp only
        rw [if_neg (Nat.succ_ne_zero j)]
        split_ifs
        exacts [hδρ, le_rfl]
      · dsimp only
        rw [if_neg (by omega)]
      · have hb' : ∀ b, ComplexMatrix2.operatorNorm (W b - 1) < δ := fun b => by simpa using hb b
        have hb₂ : ∀ b, ComplexMatrix2.operatorNorm (W b - 1) < 1 / 2 :=
          fun b => (hb' b).trans_le hδ2
        have hbound : ∀ b, ComplexMatrix2.operatorNorm (logForm L k W b) ≤ r := fun b => by
          refine (logForm_norm_le hL h₃ hδ2 hb' b).trans ?_
          rw [div_le_iff₀ hη]
          linarith
        have H := pointwiseBounds_of_small hN hk (logForm_mem hL h₃ hW hb₂) hbound
        have e := remainderGaugeField_logForm hL h₃ hW hb₂
        have hcov := H.mem_smallIterate
        rw [e] at hcov
        refine ⟨hcov, fun j hj b => ?_⟩
        by_cases h0 : j = 0
        · subst h0
          show ComplexMatrix2.operatorNorm (W b - 1) < if (0 : ℕ) = 0 then δ else polydiscRadius L
          rw [if_pos rfl]
          exact hb' b
        · show _ < if j = 0 then δ else polydiscRadius L
          rw [if_neg h0]
          have hh := H.norm_sub_one_lt_half j (by omega) b
          rw [IteratedSmallFieldMeans.meanIterate, e] at hh
          linarith
  · set P : ℝ := ∑ a, ‖ComplexMatrix2.pauliFamily a‖ with hP
    refine ⟨r * finestMesh L k / (P + 1), by positivity, fun f hf => ?_⟩
    obtain ⟨s, hs, hfs⟩ := hf
    have hs' : max s 0 < r * finestMesh L k / (P + 1) := max_lt hs (by positivity)
    have hbound : ∀ b, ComplexMatrix2.operatorNorm
        ((((finestMesh L k : ℂ))⁻¹ • backgroundOfCoeffs hL f) b) ≤ r := fun b => by
      have hb : ‖backgroundOfCoeffs hL f b‖ ≤ max s 0 * P :=
        backgroundOfCoeffs_norm_le hL (fun κ => (hfs κ).trans (le_max_left s 0)) b
      show ‖((finestMesh L k : ℂ))⁻¹ • backgroundOfCoeffs hL f b‖ ≤ r
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hη.le, inv_mul_eq_div,
        div_le_iff₀ hη]
      have h₄ : max s 0 * (P + 1) < r * finestMesh L k :=
        (lt_div_iff₀ (by positivity)).1 hs'
      have h₅ : 0 ≤ max s 0 := le_max_right _ _
      nlinarith
    have H := pointwiseBounds_of_small hN hk
      (Submodule.smul_mem _ _ (backgroundOfCoeffs_mem hL f)) hbound
    have hcov := H.mem_smallIterate
    rw [remainderGaugeField_inv_mesh_smul hL] at hcov
    exact hcov
end YangMills.Construction.Tower.FullSpace.SmallIterates
