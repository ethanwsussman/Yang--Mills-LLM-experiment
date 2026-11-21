import YangMills.Construction.RunningCouplingSlope.BlocksOfTheMixedSaddlesAndThePeriodsForm
import YangMills.Construction.RunningCouplingSlope.LogarithmsOfThePlainIterates
import YangMills.Construction.RunningCouplingSlope.ThePlainSaddlesDescend
import YangMills.Construction.Towers.DifferencesGiveTheTwoOperatorsAtOneOnTheUnitLatticeProof
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.PolydiscServesAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.SaddleDescent
open Tower PeriodicOperators Matrices
open Tower.ResponseOperators (ClassFnEqForm)
open LocalKernels LocalKernels.Periodisation
open OneLoop (pauliCoordinateEquiv)
private theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem exists_matExp_near_one {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X : ComplexMatrix2, ComplexMatrix2.operatorNorm X < δ →
      ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • X) - 1) < ρ ∧
        ComplexMatrix2.operatorNorm ((ComplexMatrix2.matExp (Complex.I • X))⁻¹ - 1) < ρ := by
  let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
  have hc : Continuous fun X : ComplexMatrix2 => ComplexMatrix2.matExp (Complex.I • X) :=
    NormedSpace.exp_continuous.comp (continuous_const_smul _)
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hc 0 ρ hρ
  refine ⟨δ, hδ, fun X hX => ?_⟩
  have key : ∀ Y : ComplexMatrix2, ComplexMatrix2.operatorNorm Y < δ →
      ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • Y) - 1) < ρ := by
    intro Y hY
    have h₁ := h Y (by simpa [dist_eq_norm] using hY)
    have h₂ : ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2)) = 1 := by
      simp [ComplexMatrix2.matExp, NormedSpace.exp_zero]
    rw [h₂, dist_eq_norm] at h₁
    exact h₁
  refine ⟨key X hX, ?_⟩
  have e : (ComplexMatrix2.matExp (Complex.I • X))⁻¹ = ComplexMatrix2.matExp (Complex.I • (-X)) := by
    rw [smul_neg]
    exact (Matrix.exp_neg _).symm
  rw [e]
  exact key (-X) (by simpa [ComplexMatrix2.operatorNorm] using hX)
section Group
variable {L n k j : ℕ}
private theorem bond_opposite_opposite {L m : ℕ} {j : ℤ} (b : PeriodicLattice.Bond L m j) :
    b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
private theorem expTwist_mem_fieldsIn (hCL : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ complexEdgeForms L n k j) :
    PeriodicLattice.expTwist A (fun _ => 1) ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  classical
  have hone : (fun _ => 1 : Edge L n k j → ComplexMatrix2) ∈
      fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
    ⟨fun _ _ => by simp [ComplexMatrix2.unitDeterminant], fun _ _ => by simp⟩
  have hleft := (((hCL.2.2 L k j hL hj).1 n hn).1.1).2 _ hone A hA
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • A b) * 1 ∈ PeriodicLattice.complexGaugeGroup := by
    intro b hb
    have h : LeftChartFields.leftExpMul ((1 : ℂ) • A b) 1 ∈
        PeriodicLattice.complexGaugeGroup := (hleft ⟨b, hb⟩).1 1
    rw [one_smul] at h
    exact h
  have hdet : ∀ M : ComplexMatrix2, M ∈ PeriodicLattice.complexGaugeGroup → IsUnit M.det :=
    fun M hM => by
      have h : M.det = 1 := hM
      rw [h]
      exact isUnit_one
  have hinv : ∀ M : ComplexMatrix2, M ∈ PeriodicLattice.complexGaugeGroup →
      M⁻¹ ∈ PeriodicLattice.complexGaugeGroup :=
    fun M hM => by
      have h : M.det = 1 := hM
      show (M⁻¹).det = 1
      rw [Matrix.det_nonsing_inv, h]
      simp
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · unfold PeriodicLattice.expTwist
    by_cases hb : b.IsPositivelyOriented
    · rw [if_pos hb]
      exact hpos b hb
    · rw [if_neg hb]
      have hr : b.opposite.IsPositivelyOriented := by
        rcases hx b with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h hb
        · exact h
      exact hinv _ (hpos _ hr)
  · unfold PeriodicLattice.expTwist
    rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [if_neg h₂, if_pos h₁, bond_opposite_opposite]
    · rw [if_pos h₁, if_neg h₂]
      exact (Matrix.nonsing_inv_nonsing_inv _ (hdet _ (hpos _ h₁))).symm
end Group
section Field
variable {L n k : ℕ}
private theorem opposite_isPositivelyOriented_of_not {j : ℕ} {b : FullSpace.Edge L k j}
    (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.InfiniteSideAdmissibility.fullSpace_opposite_isPositivelyOriented <;> assumption
private theorem ofCoeffs_of_positive {j : ℕ} (c : (FullSpace.edgePauliCoordinates L k j).Index → ℂ)
    {b : FullSpace.Edge L k j} (hb : b.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.Construction.Tower.IdentityOperators.ofCoeffs_of_positive <;> assumption
private theorem form_mem_traceless {r : edgeFormSpace L n k 0} {b : Edge L n k 0}
    (hb : b.IsPositivelyOriented) :
    (r : Edge L n k 0 → ComplexMatrix2) b ∈ ComplexMatrix2.traceless :=
  (r.2.1 b hb).2
private theorem fullField_eq_liftGaugeField (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hP : PeriodicLattice.LevelBondOrientationDichotomy) (hk : 0 < k)
    (hq : ∀ b : FullSpace.Edge L k 0,
      (b.IsPositivelyOriented → (FullSpace.projEdge L n k 0 b).IsPositivelyOriented) ∧
        (FullSpace.projEdge L n k 0 b).opposite = FullSpace.projEdge L n k 0 b.opposite)
    (hv : ∀ b : PeriodicOperators.PosEdge L k 0,
      (projPositiveEdge L n k 0 b).1 = FullSpace.projEdge L n k 0 b.1)
    (r : edgeFormSpace L n k 0) (g : (colourEdges L k 0).QuotMod (periodSide L n) → ℝ)
    (hg : ClassFnEqForm L n k 0 (restrictToPositiveEdges (r : Edge L n k 0 → ComplexMatrix2))
      (fun x => (g x : ℂ))) :
    FullSpace.BackgroundJets.gaugeFieldOfForm L k
        (liftQuotField (colourEdges L k 0) (periodSide L n) fun x => (g x : ℂ)) =
      liftGaugeField L n k 0
        (PeriodicLattice.expTwist (r : Edge L n k 0 → ComplexMatrix2) (trivialField L n k 0)) := by
  classical
  have hF : ∀ b : FullSpace.Edge L k 0, b.IsPositivelyOriented →
      (FullSpace.edgePauliCoordinates L k 0).ofCoeffs
        (liftQuotField (colourEdges L k 0) (periodSide L n) fun x => (g x : ℂ)) b =
      (r : Edge L n k 0 → ComplexMatrix2) (FullSpace.projEdge L n k 0 b) := by
    intro b hb
    refine (ofCoeffs_of_positive _ hb).trans ?_
    have hpq := (hq b).1 hb
    have e : ∀ a : Fin 3, liftQuotField (colourEdges L k 0) (periodSide L n)
        (fun x => (g x : ℂ)) (a, ⟨b, hb⟩) =
        pauliCoeff a ((r : Edge L n k 0 → ComplexMatrix2) (FullSpace.projEdge L n k 0 b)) := by
      intro a
      have h := hg (a, ⟨b, hb⟩)
      refine Eq.trans h ?_
      show pauliCoeff a ((r : Edge L n k 0 → ComplexMatrix2)
        (projPositiveEdge L n k 0 ⟨b, hb⟩).1) = _
      rw [hv]
    show ∑ a, _ • ComplexMatrix2.pauliFamily a = _
    exact (Finset.sum_congr rfl fun a _ =>
      congrArg (fun w : ℂ => w • ComplexMatrix2.pauliFamily a) (e a)).trans
      (sum_pauliCoeff_smul (form_mem_traceless hpq))
  funext b
  show FullSpace.expTwist _ 1 b =
    PeriodicLattice.expTwist (r : Edge L n k 0 → ComplexMatrix2) (trivialField L n k 0)
      (FullSpace.projEdge L n k 0 b)
  unfold FullSpace.expTwist PeriodicLattice.expTwist
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb, if_pos ((hq b).1 hb), hF b hb]
    rfl
  · have hr := opposite_isPositivelyOriented_of_not hb
    have hrq : (FullSpace.projEdge L n k 0 b).opposite.IsPositivelyOriented := by
      rw [(hq b).2]
      exact (hq b.opposite).1 hr
    have hnq : ¬(FullSpace.projEdge L n k 0 b).IsPositivelyOriented := by
      rcases hP L n k hL hn hk 0 (Nat.zero_le k) (FullSpace.projEdge L n k 0 b) with
        ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd hrq h
      · exact h
    rw [if_neg hb, if_neg hnq, hF _ hr, (hq b).2]
    rfl
end Field
section Blocks
variable {L n k : ℕ}
private theorem edgeSaddle_periodizesTo {a : ℝ} {U : Edge L n k 0 → ComplexMatrix2}
    (hb : MixedSaddleBlocksPeriodize a L n k U)
    {g : (colourEdges L k 0).QuotMod (periodSide L n) → ℂ}
    (hf : FullSpace.BackgroundJets.gaugeFieldOfForm L k
        (liftQuotField (colourEdges L k 0) (periodSide L n) g) =
      liftGaugeField L n k 0 U) :
    PeriodizesTo (FullLattice.edgeSaddleOfForm a L k) (edgeIndexProj L n k) (saddleMatrix a U)
      (periodSide L n) g := by
  intro ι' ι
  show periodization _ _ (FullLattice.edgeSaddle a L k
    (FullSpace.BackgroundJets.gaugeFieldOfForm L k
      (liftQuotField (colourEdges L k 0) (periodSide L n) g))) (periodSide L n) ι' ι = _
  rw [hf]
  rcases ι' with i' | c' <;> rcases ι with i | c
  · exact hb.X i' i
  · exact hb.Qt i' c
  · exact hb.Q c' i
  · show ∑' m, -(FullLattice.noiseCovariance a L k (liftGaugeField L n k 0 U) k c' _) =
      -(noiseCovariance a L n k U k _ _)
    rw [tsum_neg]
    exact congrArg Neg.neg (hb.covariance c' c)
private theorem vertexSaddle_periodizesTo {a : ℝ} {U : Edge L n k 0 → ComplexMatrix2}
    (hb : MixedSaddleBlocksPeriodize a L n k U)
    {g : (colourEdges L k 0).QuotMod (periodSide L n) → ℂ}
    (hf : FullSpace.BackgroundJets.gaugeFieldOfForm L k
        (liftQuotField (colourEdges L k 0) (periodSide L n) g) =
      liftGaugeField L n k 0 U) :
    PeriodizesTo (FullLattice.vertexSaddleOfForm L k) (ghostIndexProj L n k) (ghostMatrix U)
      (periodSide L n) g := by
  intro ι' ι
  show periodization _ _ (FullLattice.vertexSaddle L k
    (FullSpace.BackgroundJets.gaugeFieldOfForm L k
      (liftQuotField (colourEdges L k 0) (periodSide L n) g))) (periodSide L n) ι' ι = _
  rw [hf]
  rcases ι' with i' | c' <;> rcases ι with i | c
  · exact hb.Delta i' i
  · exact hb.Rt i' c
  · exact hb.R c' i
  · show ∑' _ : Fin 4 → ℤ, (0 : ℂ) = 0
    exact tsum_zero
end Blocks
theorem saddleKernelsPeriodize_holds (hBl : MixedSaddleBlocksPeriodizeNearIdentity)
    (hLog : MeanIterateLogarithms)
    (hI : IteratedSmallFieldMeans.IteratedMeansClaim)
    (hCL : LeftChartFields.Claim)
    (hP : LocalKernels.Periodisation.PeriodisationHolds)
    (hQ : EdgeProjectionProperties)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy) : SaddleKernelsPeriodize := by
  classical
  intro a _ L hL k hk
  obtain ⟨ρ₁, hρ₁, hB⟩ := hBl L hL
  obtain ⟨ρ₂, hρ₂, hlog⟩ := hLog L hL
  obtain ⟨hρ₃, -, -, hnum⟩ := hI.1 L hL
  obtain ⟨δ, hδ, hexp⟩ := exists_matExp_near_one hρ₁
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hη : 0 < finestMesh L k := by
    have : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
    exact zpow_pos this _
  set T : ℝ := ∑ a : Fin 3, ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily a) + 1 with hT
  have hTpos : 0 < T := by
    have : 0 ≤ ∑ a : Fin 3, ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily a) :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  set τ : ℝ := min (IteratedSmallFieldMeans.smallRadius L) (min ρ₂ (δ / 20)) with hτ
  have hτpos : 0 < τ := lt_min hρ₃ (lt_min hρ₂ (by linarith))
  refine ⟨finestMesh L k * τ / T, by positivity, fun r g hg hsm => ?_⟩
  obtain ⟨hcells, -⟩ := hP L hL k n hn
  have hzero : 0 ≤ k := Nat.zero_le k
  have hsurj := ((hcells 0 hzero).1 .edge).1
  have hvq := (hcells 0 hzero).2.2.1
  have hq := (hQ L n k 0 hL hn hzero).1
  have hrev : ∀ b : Edge L n k 0, ¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented := by
    intro b hb
    rcases hO L n k hL hn (by omega) 0 hzero b with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact absurd h₁ hb
    · exact h₁
  have hpos : ∀ b : Edge L n k 0, b.IsPositivelyOriented →
      ComplexMatrix2.operatorNorm ((r : Edge L n k 0 → ComplexMatrix2) b) ≤ finestMesh L k * τ := by
    intro b hb
    obtain ⟨c, hc⟩ := hsurj ⟨b, hb⟩
    have hco : ∀ a : Fin 3, ‖pauliCoeff a ((r : Edge L n k 0 → ComplexMatrix2) b)‖ ≤
        finestMesh L k * τ / T := by
      intro a
      have h := hg (a, c)
      have e : toPauliCoeffs (restrictToPositiveEdges (r : Edge L n k 0 → ComplexMatrix2))
          (a, projPositiveEdge L n k 0 c) =
            pauliCoeff a ((r : Edge L n k 0 → ComplexMatrix2) b) := by
        have hc' : projPositiveEdge L n k 0 c = ⟨b, hb⟩ := hc
        rw [hc']
        rfl
      rw [← e, ← h, Complex.norm_real, Real.norm_eq_abs]
      exact (hsm _).le
    rw [← sum_pauliCoeff_smul (form_mem_traceless (r := r) hb)]
    calc ComplexMatrix2.operatorNorm
          (∑ a, pauliCoeff a ((r : Edge L n k 0 → ComplexMatrix2) b) • ComplexMatrix2.pauliFamily a)
        ≤ ∑ a, ‖pauliCoeff a ((r : Edge L n k 0 → ComplexMatrix2) b) •
            ComplexMatrix2.pauliFamily a‖ :=
          norm_sum_le _ _
      _ ≤ ∑ a : Fin 3, finestMesh L k * τ / T *
            ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily a) :=
          Finset.sum_le_sum fun a _ => (norm_smul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hco a) (norm_nonneg _))
      _ = finestMesh L k * τ / T *
            ∑ a : Fin 3, ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily a) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ finestMesh L k * τ / T * T :=
          mul_le_mul_of_nonneg_left (by rw [hT]; linarith) (by positivity)
      _ = finestMesh L k * τ := by field_simp
  have hall : ∀ b : Edge L n k 0,
      ComplexMatrix2.operatorNorm ((r : Edge L n k 0 → ComplexMatrix2) b) ≤ finestMesh L k * τ := by
    intro b
    by_cases hb : b.IsPositivelyOriented
    · exact hpos b hb
    · have h := hpos _ (hrev b hb)
      have e : (r : Edge L n k 0 → ComplexMatrix2) b.opposite =
          -(r : Edge L n k 0 → ComplexMatrix2) b := r.2.2 b
      rw [e] at h
      simpa [ComplexMatrix2.operatorNorm] using h
  set v : Edge L n k 0 → ComplexMatrix2 :=
    (((finestMesh L k)⁻¹ : ℝ) : ℂ) • (r : Edge L n k 0 → ComplexMatrix2) with hv
  have hrc : (r : Edge L n k 0 → ComplexMatrix2) ∈ complexEdgeForms L n k 0 :=
    ⟨fun b hb => (r.2.1 b hb).2, r.2.2⟩
  have hvc : v ∈ complexEdgeForms L n k 0 := Submodule.smul_mem _ _ hrc
  have hvb : ∀ b, ComplexMatrix2.operatorNorm (v b) ≤ τ := by
    intro b
    have e : ComplexMatrix2.operatorNorm (v b) ≤ ‖(((finestMesh L k)⁻¹ : ℝ) : ℂ)‖ *
        ComplexMatrix2.operatorNorm ((r : Edge L n k 0 → ComplexMatrix2) b) := by
      show ‖(((finestMesh L k)⁻¹ : ℝ) : ℂ) • (r : Edge L n k 0 → ComplexMatrix2) b‖ ≤ _
      exact norm_smul_le _ _
    have e' : ‖(((finestMesh L k)⁻¹ : ℝ) : ℂ)‖ = (finestMesh L k)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη)]
    rw [e'] at e
    refine e.trans ?_
    calc (finestMesh L k)⁻¹ * ComplexMatrix2.operatorNorm ((r : Edge L n k 0 → ComplexMatrix2) b)
        ≤ (finestMesh L k)⁻¹ * (finestMesh L k * τ) :=
          mul_le_mul_of_nonneg_left (hall b) (inv_pos.2 hη).le
      _ = τ := by field_simp
  have hsup : maxOperatorNorm v ≤ ENNReal.ofReal τ :=
    iSup_le fun b => ENNReal.ofReal_le_ofReal (hvb b)
  have hsupR : (maxOperatorNorm v).toReal ≤ τ := ENNReal.toReal_le_of_le_ofReal hτpos.le hsup
  have hU : remainderGaugeField v =
      PeriodicLattice.expTwist (r : Edge L n k 0 → ComplexMatrix2) (trivialField L n k 0) := by
    have e : finestMesh L k • v = (r : Edge L n k 0 → ComplexMatrix2) := by
      funext b
      show finestMesh L k • ((((finestMesh L k)⁻¹ : ℝ) : ℂ) •
        (r : Edge L n k 0 → ComplexMatrix2) b) = _
      rw [← algebraMap_smul ℂ (finestMesh L k), smul_smul]
      have : algebraMap ℝ ℂ (finestMesh L k) * (((finestMesh L k)⁻¹ : ℝ) : ℂ) = 1 := by
        rw [Complex.coe_algebraMap, ← Complex.ofReal_mul, mul_inv_cancel₀ hη.ne',
          Complex.ofReal_one]
      rw [this, one_smul]
    show PeriodicLattice.expTwist (finestMesh L k • v) _ = _
    rw [e]
    rfl
  have hv₂ : v ∈ IteratedSmallFieldMeans.smallFormBall L n k ρ₂ :=
    ⟨hvc, hsup.trans (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hv₃ : v ∈ IteratedSmallFieldMeans.smallFormBall L n k
      (IteratedSmallFieldMeans.smallRadius L) :=
    ⟨hvc, hsup.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))⟩
  obtain ⟨hit, hsm', -⟩ := hlog n k hn hk v hv₂
  have hxy : ∀ (j : ℕ), j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
    intro j hj b
    rcases hO L n k hL hn (by omega) j hj b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₁, h₂⟩
  have hsmall : MeanChainNearIdentity ρ₁ L n k (remainderGaugeField v) := by
    refine ⟨((hnum k hk).1 n hn).pointwise v hv₃ |>.mem_smallIterate, hsm',
      fun j hj b => ?_, fun j hj => ?_⟩
    · obtain ⟨A, -, eA, hA⟩ := hit j hj.le
      have hone : meshAt L k j ≤ 1 := by
        have h1 : (1 : ℝ) ≤ L := by
          have : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
          linarith
        exact zpow_le_one_of_nonpos₀ h1 (by omega)
      have hlev : 0 < meshAt L k j := by
        have : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
        exact zpow_pos this _
      have hAb : ∀ c, ComplexMatrix2.operatorNorm (A c) < δ := by
        intro c
        have h₁ : ENNReal.ofReal (ComplexMatrix2.operatorNorm (A c)) ≤ maxOperatorNorm A :=
          le_iSup (fun i => ENNReal.ofReal (ComplexMatrix2.operatorNorm (A i))) c
        have h₂ := h₁.trans hA
        have h₃ : 0 ≤ 10 * meshAt L k j * (maxOperatorNorm v).toReal := by positivity
        have h₄ := (ENNReal.ofReal_le_ofReal_iff h₃).1 h₂
        have h₅ : τ ≤ δ / 20 := (min_le_right _ _).trans (min_le_right _ _)
        have h₆ : 10 * meshAt L k j * (maxOperatorNorm v).toReal ≤ 10 * 1 * τ := by
          have : 0 ≤ (maxOperatorNorm v).toReal := ENNReal.toReal_nonneg
          gcongr
        linarith
      rw [eA]
      unfold PeriodicLattice.expTwist
      by_cases hb : b.IsPositivelyOriented
      · rw [if_pos hb, mul_one]
        exact (hexp _ (hAb b)).1
      · rw [if_neg hb, mul_one]
        exact (hexp _ (hAb b.opposite)).2
    · rcases Nat.lt_or_eq_of_le hj with h | rfl
      · exact (hsm' j h).1
      · obtain ⟨A, hA, eA, -⟩ := hit j hj
        rw [eA]
        exact expTwist_mem_fieldsIn hCL hL hn hj (hxy j hj) hA
  have hblocks := hB a k n hk hn _ hsmall
  have hfield := fullField_eq_liftGaugeField hL hn hO (by omega)
    (fun b => ⟨(hq b).2.2.1, (hq b).2.2.2⟩) hvq r g hg
  rw [← hU] at hfield ⊢
  exact ⟨edgeSaddle_periodizesTo hblocks hfield, vertexSaddle_periodizesTo hblocks hfield⟩
end YangMills.Construction.RunningCouplingSlope.SaddleDescent
end
