import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.LogarithmicChartsOfASpaceOfConfigurations
import YangMills.Construction.Matrices.MatrixOperationsKeepHolomorphy
import YangMills.Construction.Matrices.NormExpLogBasics
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ConfigurationLogCharts
open YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Matrices.LogChartsAroundFamily
open YangMills.Construction.Matrices.ComplexMatrix2
variable {σ : Type}
private theorem inv_mem_specialUnitary {V : ComplexMatrix2} (hV : V ∈ (specialUnitary : Set ComplexMatrix2)) :
    V⁻¹ ∈ (specialUnitary : Set ComplexMatrix2) := by
  have hV' := Matrix.mem_specialUnitaryGroup_iff.mp hV
  have hinv : V⁻¹ = star V := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hV'.1)
  rw [hinv]
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_star]
    exact Matrix.mem_unitaryGroup_iff'.mp hV'.1
  · rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hV'.2, star_one]
abbrev _root_.YangMills.DeltaSharedProofs.p3037 := @inv_mem_specialUnitary
abbrev _root_.YangMills.SharedProofs.p33390 := @inv_mem_specialUnitary
private theorem det_eq_one_of_mem {V : ComplexMatrix2} (hV : V ∈ (specialUnitary : Set ComplexMatrix2)) :
    V.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.mp hV).2
private theorem inv_mul_cancel_of_mem {V : ComplexMatrix2}
    (hV : V ∈ (specialUnitary : Set ComplexMatrix2)) : V⁻¹ * V = 1 :=
  Matrix.nonsing_inv_mul V (by rw [det_eq_one_of_mem hV]; exact isUnit_one)
private theorem mul_inv_cancel_of_mem {V : ComplexMatrix2}
    (hV : V ∈ (specialUnitary : Set ComplexMatrix2)) : V * V⁻¹ = 1 :=
  Matrix.mul_nonsing_inv V (by rw [det_eq_one_of_mem hV]; exact isUnit_one)
private theorem operatorNorm_mul_inv_sub_one (hE : NormExpLogBasics) {V : ComplexMatrix2}
    (hV : V ∈ (specialUnitary : Set ComplexMatrix2)) (Y : ComplexMatrix2) :
    operatorNorm (Y * V⁻¹ - 1) = operatorNorm (Y - V) := by
  obtain ⟨⟨-, -, -, hunit, -⟩, -⟩ := hE
  have h1 : (1 : ComplexMatrix2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := one_mem _
  have h := hunit (Y * V⁻¹ - 1) 1 V h1 (Matrix.mem_specialUnitaryGroup_iff.mp hV).1
  rw [← h]
  congr 1
  rw [one_mul, sub_mul, mul_assoc, inv_mul_cancel_of_mem hV, mul_one, one_mul]
private def quotientBall (r : ℝ) (V₀ : σ → ComplexMatrix2) : Set (σ → ComplexMatrix2) :=
  {Y | ∀ b, operatorNorm (Y b * (V₀ b)⁻¹ - 1) < r}
private theorem isOpen_quotientBall [Finite σ] (r : ℝ) (V₀ : σ → ComplexMatrix2) :
    IsOpen (quotientBall r V₀) := by
  have h : quotientBall r V₀ =
      ⋂ b, {Y : σ → ComplexMatrix2 | operatorNorm (Y b * (V₀ b)⁻¹ - 1) < r} := by
    ext Y
    simp [quotientBall]
  rw [h]
  refine isOpen_iInter_of_finite fun b => isOpen_lt ?_ continuous_const
  exact (((continuous_apply b).mul continuous_const).sub continuous_const).norm
private theorem exists_quotientBall_subset [Fintype σ] (hE : NormExpLogBasics)
    {V₀ : σ → ComplexMatrix2} (hV : ∀ b, V₀ b ∈ (specialUnitary : Set ComplexMatrix2))
    {O : Set (σ → ComplexMatrix2)} (hO : IsOpen O) (hx : V₀ ∈ O)
    {ρ : ℝ} (hρ : 0 < ρ) : ∃ ρ', 0 < ρ' ∧ ρ' ≤ ρ ∧ quotientBall ρ' V₀ ⊆ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO V₀ hx
  refine ⟨min ρ ε, lt_min hρ hε, min_le_left _ _, fun Y hY => hball ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro b
  rw [dist_eq_norm]
  show operatorNorm (Y b - V₀ b) < ε
  rw [← operatorNorm_mul_inv_sub_one hE (hV b)]
  exact (hY b).trans_le (min_le_right _ _)
private theorem quotientBall_basis [Fintype σ] (hE : NormExpLogBasics) {V₀ : σ → ComplexMatrix2}
    (hV : ∀ b, V₀ b ∈ (specialUnitary : Set ComplexMatrix2)) {P : Set (σ → ComplexMatrix2)}
    (hP : V₀ ∈ P) {ρ : ℝ} (hρ : 0 < ρ) :
    IsNeighbourhoodBasis P V₀ ρ fun ρ' => quotientBall ρ' V₀ ∩ P := by
  unfold IsNeighbourhoodBasis
  constructor
  · intro ρ' h0 _
    refine ⟨⟨_, isOpen_quotientBall ρ' V₀, rfl⟩, ?_, hP⟩
    intro b
    rw [mul_inv_cancel_of_mem (hV b), sub_self]
    show ‖(0 : ComplexMatrix2)‖ < ρ'
    rw [norm_zero]
    exact h0
  · rintro D ⟨O, hO, rfl⟩ ⟨hx, -⟩
    obtain ⟨ρ', h0, h1, hs⟩ := exists_quotientBall_subset hE hV hO hx hρ
    exact ⟨ρ', h0, h1, inter_subset_inter_left _ hs⟩
private theorem chartNeighbourhood_eq (ρ' : ℝ) (V₀ : σ → ComplexMatrix2) :
    chartNeighbourhood ρ' V₀ = quotientBall ρ' V₀ ∩ unimodularPi σ := by
  ext W
  exact and_comm
private theorem compactPi_subset_unimodularPi : compactPi σ ⊆ unimodularPi σ :=
  fun _ hW b => det_eq_one_of_mem (hW b)
private theorem chartNeighbourhood_inter_compactPi (ρ' : ℝ) (V₀ : σ → ComplexMatrix2) :
    chartNeighbourhood ρ' V₀ ∩ compactPi σ = quotientBall ρ' V₀ ∩ compactPi σ := by
  rw [chartNeighbourhood_eq, inter_assoc, inter_eq_right.mpr compactPi_subset_unimodularPi]
private theorem matExp_logSeries (hL : ExpLogEstimates) {Y : ComplexMatrix2}
    (h : operatorNorm (Y - 1) < 1) : matExp (logSeries Y) = Y := by
  obtain ⟨-, -, -, h4, -⟩ := hL
  have h' := (h4 (Y - 1) h).2.2.2.2
  rwa [add_sub_cancel] at h'
private theorem operatorNorm_logSeries_lt (hL : ExpLogEstimates) {Y : ComplexMatrix2} {ρ : ℝ}
    (hρ : ρ < 1) (h : operatorNorm (Y - 1) < ρ) :
    operatorNorm (logSeries Y) < -Real.log (1 - ρ) := by
  obtain ⟨-, -, -, h4, -⟩ := hL
  have h' := (h4 (Y - 1) (h.trans hρ)).1
  rw [add_sub_cancel] at h'
  have hlt : Real.log (1 - ρ) < Real.log (1 - operatorNorm (Y - 1)) :=
    Real.log_lt_log (by linarith) (by linarith)
  linarith
private theorem chart_value_mem_traceless (hL : ExpLogEstimates) {Y : ComplexMatrix2}
    (hd : Y.det = 1) (hn : operatorNorm (Y - 1) ≤ 9 / 10) :
    Complex.I⁻¹ • logSeries Y ∈ traceless := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hL
  exact traceless.smul_mem _ (h7 Y hd hn).2
private theorem det_expTimesUnitary (hL : ExpLogEstimates) {B V : ComplexMatrix2}
    (hB : B ∈ traceless) (hV : V.det = 1) : (expTimesUnitary B V).det = 1 := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := hL
  have ht : fullTrace (Complex.I • B) = 0 := traceless.smul_mem _ hB
  rw [expTimesUnitary, Matrix.det_mul, h6, ht, Complex.exp_zero, hV, one_mul]
private theorem operatorNorm_le_supNorm [Finite σ] (B : σ → ComplexMatrix2) (b : σ) :
    operatorNorm (B b) ≤ supNorm B :=
  le_ciSup (Set.finite_range fun b => operatorNorm (B b)).bddAbove b
private theorem supNorm_lt [Finite σ] {B : σ → ComplexMatrix2} {r : ℝ} (hr : 0 < r)
    (h : ∀ b, operatorNorm (B b) < r) : supNorm B < r := by
  rcases isEmpty_or_nonempty σ with he | he
  · simpa [supNorm, Real.iSup_of_isEmpty] using hr
  · obtain ⟨b, hb⟩ := exists_eq_ciSup_of_finite (f := fun b => operatorNorm (B b))
    unfold supNorm
    rw [← hb]
    exact h b
private theorem mem_tracelessFunctions {B : σ → ComplexMatrix2} :
    B ∈ tracelessFunctions σ ↔ ∀ b, B b ∈ traceless := by
  unfold tracelessFunctions
  rw [Submodule.mem_pi]
  simp
private theorem logHolomorphic_of [Fintype σ] (hL : ExpLogEstimates)
    (hM : HolomorphyClosureStatement) {V₀ : σ → ComplexMatrix2}
    (hV : ∀ b, V₀ b ∈ (specialUnitary : Set ComplexMatrix2)) {ρ : ℝ} (hρ : ρ ≤ 9 / 10) :
    LogHolomorphic V₀ ρ := by
  unfold LogHolomorphic
  constructor
  · rintro W ⟨hW, hn⟩
    refine SetLike.mem_coe.mpr (mem_tracelessFunctions.mpr fun b => ?_)
    refine chart_value_mem_traceless hL ?_ ((hn b).le.trans hρ)
    rw [Matrix.det_mul, det_eq_one_of_mem (inv_mem_specialUnitary (hV b))]
    rw [show (W b).det = 1 from hW b, one_mul]
  · intro bs
    have hopen : IsRelativelyOpen (GroupLieProduct σ Empty)
        (asGroupFactors '' chartNeighbourhood ρ V₀) := by
      refine ⟨(fun p b => p (.inl b)) ⁻¹' quotientBall ρ V₀,
        (isOpen_quotientBall ρ V₀).preimage (continuous_pi fun b => continuous_apply _), ?_⟩
      ext p
      constructor
      · rintro ⟨W, ⟨hW, hn⟩, rfl⟩
        refine ⟨hn, ?_⟩
        rintro (b | e)
        · exact hW b
        · exact e.elim
      · rintro ⟨h1, h2⟩
        refine ⟨fun b => p (.inl b), ⟨fun b => h2 (.inl b), h1⟩, ?_⟩
        funext x
        rcases x with b | e
        · rfl
        · exact e.elim
    obtain ⟨hconst, hcoord, -, hmul, hlin, -, -, hlog, -, -, -⟩ :=
      hM σ Empty bs (asGroupFactors '' chartNeighbourhood ρ V₀) hopen
    refine ⟨hopen, fun i => i.elim, fun k => ⟨?_, ?_⟩⟩
    · rintro _ ⟨W, ⟨hW, hn⟩, rfl⟩
      refine chart_value_mem_traceless hL ?_ ((hn k).le.trans hρ)
      rw [Matrix.det_mul, det_eq_one_of_mem (inv_mem_specialUnitary (hV k)), mul_one]
      exact hW k
    · have h1 := hmul _ _ (hcoord (.inl k)) (hconst (V₀ k)⁻¹)
      have hmaps : MapsTo (fun p : σ ⊕ Empty → ComplexMatrix2 => p (.inl k) * (V₀ k)⁻¹)
          (asGroupFactors '' chartNeighbourhood ρ V₀) logBall := by
        rintro _ ⟨W, ⟨-, hn⟩, rfl⟩
        exact (hn k).trans_le (hρ.trans (by norm_num))
      exact hlin (Complex.I⁻¹ • LinearMap.id) _ (hlog _ h1 hmaps)
private theorem expHolomorphic_of [Fintype σ] (hL : ExpLogEstimates)
    (hM : HolomorphyClosureStatement) (hC : ExpChartHolomorphy.ExpChartTheory)
    {V₀ : σ → ComplexMatrix2} (hV : ∀ b, V₀ b ∈ (specialUnitary : Set ComplexMatrix2)) :
    ExpHolomorphic V₀ := by
  unfold ExpHolomorphic
  constructor
  · intro B hB b
    exact det_expTimesUnitary hL (mem_tracelessFunctions.mp (SetLike.mem_coe.mp hB) b)
      (det_eq_one_of_mem (hV b))
  · intro bs
    have hopen : IsRelativelyOpen (GroupLieProduct Empty σ) (GroupLieProduct Empty σ) :=
      ⟨univ, isOpen_univ, (univ_inter _).symm⟩
    obtain ⟨hconst, hcoord, -, hmul, hlin, -, hexp, -⟩ :=
      hM Empty σ bs (GroupLieProduct Empty σ) hopen
    refine ⟨hopen, fun i => ?_, fun k => k.elim⟩
    have hmaps : MapsTo (fun p => expOnProduct V₀ p (.inl i))
        (GroupLieProduct Empty σ) unitDeterminant :=
      fun p hp => det_expTimesUnitary hL (hp (.inr i)) (det_eq_one_of_mem (hV i))
    refine ((hC.2.2.2.1 Empty σ).2.1 bs _ _ hopen hmaps).mpr ?_
    exact hmul _ _ (hexp _ (hlin (Complex.I • LinearMap.id) _ (hcoord (.inr i)))) (hconst (V₀ i))
private theorem leftInverseOfExp_of [Finite σ] (hL : ExpLogEstimates)
    {V₀ : σ → ComplexMatrix2} (hV : ∀ b, V₀ b ∈ (specialUnitary : Set ComplexMatrix2))
    {ρ : ℝ} (h0 : 0 < ρ) (hρ : ρ ≤ 9 / 10) : LeftInverseOfExp V₀ ρ := by
  unfold LeftInverseOfExp
  have hρ1 : ρ < 1 := by linarith
  have hpos : 0 < -Real.log (1 - ρ) := by
    have := Real.log_neg (x := 1 - ρ) (by linarith) (by linarith)
    linarith
  refine ⟨fun W hW => ?_, ?_⟩
  · obtain ⟨-, hn⟩ := hW
    constructor
    · funext b
      show matExp (Complex.I • Complex.I⁻¹ • logSeries (W b * (V₀ b)⁻¹)) * V₀ b = W b
      rw [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul,
        matExp_logSeries hL ((hn b).trans hρ1), mul_assoc, inv_mul_cancel_of_mem (hV b),
        mul_one]
    · refine supNorm_lt hpos fun b => ?_
      show ‖Complex.I⁻¹ • logSeries (W b * (V₀ b)⁻¹)‖ < _
      rw [norm_smul, norm_inv, Complex.norm_I, inv_one, one_mul]
      exact operatorNorm_logSeries_lt hL hρ1 (hn b)
  · rintro W ⟨⟨-, hn⟩, hr⟩
    unfold hermitianTracelessFunctions
    rw [Submodule.mem_pi]
    intro b _
    have hY : W b * (V₀ b)⁻¹ ∈ (specialUnitary : Set ComplexMatrix2) :=
      mul_mem (hr b) (inv_mem_specialUnitary (hV b))
    obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hL
    obtain ⟨H, -, hlog, -, -, -, hdet⟩ :=
      h8 _ (Matrix.mem_specialUnitaryGroup_iff.mp hY).1 ((hn b).trans hρ1)
    obtain ⟨-, hsu, -⟩ := hdet (det_eq_one_of_mem hY)
    show Complex.I⁻¹ • logSeries (W b * (V₀ b)⁻¹) ∈ hermitianTraceless
    rw [hlog, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    exact hsu
private theorem expRightInverse_of [Finite σ] (hL : ExpLogEstimates)
    {V₀ : σ → ComplexMatrix2} (hV : ∀ b, V₀ b ∈ (specialUnitary : Set ComplexMatrix2))
    {ρ : ℝ} (h0 : 0 < ρ) (hρ : ρ ≤ 9 / 10) : ExpRightInverse V₀ ρ := by
  unfold ExpRightInverse
  intro B hB hn
  have hBm := mem_tracelessFunctions.mp hB
  have hsmall : ∀ b, operatorNorm (Complex.I • B b) < Real.log (1 + ρ) := fun b => by
    show ‖Complex.I • B b‖ < _
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (operatorNorm_le_supNorm B b).trans_lt hn
  have hquot : ∀ b, expTimesUnitaryFamily B V₀ b * (V₀ b)⁻¹ = matExp (Complex.I • B b) :=
    fun b => by
      show matExp (Complex.I • B b) * V₀ b * (V₀ b)⁻¹ = _
      rw [mul_assoc, mul_inv_cancel_of_mem (hV b), mul_one]
  refine ⟨⟨fun b => det_expTimesUnitary hL (hBm b) (det_eq_one_of_mem (hV b)), fun b => ?_⟩, ?_⟩
  · rw [hquot]
    obtain ⟨h1, -⟩ := hL
    have hle := (h1 (Complex.I • B b)).2
    have hlt := Real.exp_lt_exp.mpr (hsmall b)
    rw [Real.exp_log (by linarith)] at hlt
    linarith
  · funext b
    show Complex.I⁻¹ • logSeries (expTimesUnitaryFamily B V₀ b * (V₀ b)⁻¹) = B b
    obtain ⟨-, -, -, -, h5, -⟩ := hL
    have hlt : operatorNorm (Complex.I • B b) < Real.log 2 :=
      (hsmall b).trans (Real.log_lt_log (by linarith) (by linarith))
    rw [hquot, (h5 _ hlt).2, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem statement_holds (hE : NormExpLogBasics) (hL : ExpLogEstimates)
    (hM : HolomorphyClosureStatement) (hC : ExpChartHolomorphy.ExpChartTheory) :
    Statement := by
  intro σ _ V₀ ρ hc
  obtain ⟨hV, h0, hρ'⟩ := hc
  have hρ : ρ ≤ 9 / 10 := hρ'
  have hV' : ∀ b, V₀ b ∈ (specialUnitary : Set ComplexMatrix2) := hV
  refine ⟨?_, logHolomorphic_of hL hM hV' hρ, leftInverseOfExp_of hL hV' h0 hρ,
    expRightInverse_of hL hV' h0 hρ, expHolomorphic_of hL hM hC hV'⟩
  unfold NeighbourhoodsBasis
  constructor
  · have h := quotientBall_basis hE hV' (P := unimodularPi σ)
      (compactPi_subset_unimodularPi hV) h0
    simpa only [chartNeighbourhood_eq] using h
  · have h := quotientBall_basis hE hV' (P := compactPi σ) hV h0
    simpa only [chartNeighbourhood_inter_compactPi] using h
end YangMills.Construction.Matrices.ConfigurationLogCharts
