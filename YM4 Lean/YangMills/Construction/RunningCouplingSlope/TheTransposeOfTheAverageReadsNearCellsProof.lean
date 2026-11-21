import YangMills.Construction.RunningCouplingSlope.TheGhostOfTheWholeChainHasABoundedInverseAtOneProof
import YangMills.Construction.RunningCouplingSlope.TheOtherConstraintReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheTermOfTheBackgroundGaugeReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheTransposeOfTheAverageReadsNearCells
import YangMills.Construction.Towers.IteratedAveragesReadOnlyTheBlocksAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Filter Set
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.SmoothingTransposeLocality
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.IteratedSmallFieldMeans (HolomorphicInEntries smallFormBall)
open YangMills.Construction.Tower.LeftChartFields (scalarCoords)
private theorem analyticOnNhd_of_differentiableOn_coords
    (hA : Matrices.ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    {I : Type} [Fintype I] {S : Set (I → ℂ)} (hS : IsOpen S) {g : (I → ℂ) → ℂ}
    (hg : DifferentiableOn ℂ g S) : AnalyticOnNhd ℂ g S := by apply _root_.YangMills.SharedProofs.p33934 <;> assumption
section ScaledForms
variable {L n k : ℕ}
open Classical in
private def orientationSign (b : Edge L n k 0) : ℂ := if b.IsPositivelyOriented then 1 else -1
open Classical in
private def positiveRepresentative (b : Edge L n k 0) : PositiveEdge L n k 0 :=
  if h : b.IsPositivelyOriented then ⟨b, h⟩
  else ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩
private theorem norm_orientationSign (b : Edge L n k 0) : ‖orientationSign b‖ = 1 := by
  unfold orientationSign
  split_ifs <;> simp
private theorem complexFineValues_eq_sum (w : TripleCoordIndex L n k → ℂ) (b : Edge L n k 0) :
    complexFineValues w b =
      ∑ a, (orientationSign b * w (.inl (.inl (a, positiveRepresentative b)))) •
        Matrices.ComplexMatrix2.pauliFamily a := by
  by_cases hb : b.IsPositivelyOriented
  · simp [complexFineValues, edgeFormOfPositiveValues, hb, ofPauliCoeffs, orientationSign,
      positiveRepresentative]
  · have hr := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    simp [complexFineValues, edgeFormOfPositiveValues, hb, hr, ofPauliCoeffs, orientationSign,
      positiveRepresentative]
private theorem complexFineValues_opposite
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (w : TripleCoordIndex L n k → ℂ) (b : Edge L n k 0) :
    complexFineValues w b.opposite = -complexFineValues w b := by apply _root_.YangMills.SharedProofs.p52422 <;> assumption
private theorem coe_pauliCoordinateEquiv_symm (c : Fin 3 → ℂ) :
    ((OneLoop.pauliCoordinateEquiv.symm c : Matrices.ComplexMatrix2.traceless) :
      Matrices.ComplexMatrix2) = ∑ b, c b • Matrices.ComplexMatrix2.pauliFamily b := by apply _root_.YangMills.Construction.Tower.FullSpace.IterLocality.pauliCoordinateEquiv_symm_coe <;> assumption
private theorem sum_smul_pauli_mem_traceless (c : Fin 3 → ℂ) :
    ∑ b, c b • Matrices.ComplexMatrix2.pauliFamily b ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
private def scaledForm (w : TripleCoordIndex L n k → ℂ) : Edge L n k 0 → Matrices.ComplexMatrix2 :=
  ((((finestMesh L k)⁻¹ : ℝ) : ℂ)) • complexFineValues w
private theorem scaledForm_apply (w : TripleCoordIndex L n k → ℂ) (b : Edge L n k 0) :
    scaledForm w b = ∑ a, ((((finestMesh L k)⁻¹ : ℝ) : ℂ) * orientationSign b *
      w (.inl (.inl (a, positiveRepresentative b)))) • Matrices.ComplexMatrix2.pauliFamily a := by
  simp only [scaledForm, Pi.smul_apply, complexFineValues_eq_sum, Finset.smul_sum, smul_smul,
    mul_assoc]
private theorem scaledForm_mem
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (w : TripleCoordIndex L n k → ℂ) : scaledForm w ∈ complexEdgeForms L n k 0 := by
  refine Submodule.smul_mem _ _ ⟨fun b _ => ?_, fun b => complexFineValues_opposite hx w b⟩
  rw [complexFineValues_eq_sum]
  exact sum_smul_pauli_mem_traceless _
private theorem complexChainPoint_fine_eq (hη : 0 < finestMesh L k) (w : TripleCoordIndex L n k → ℂ) :
    (complexChainPoint w).fine = remainderGaugeField (scaledForm w) := by
  have e : finestMesh L k • scaledForm w = complexFineValues w := by
    funext b
    ext i j
    simp [scaledForm, hη.ne']
  show PeriodicLattice.expTwist (complexFineValues w) (unitPoint L n k).fine =
    PeriodicLattice.expTwist (finestMesh L k • scaledForm w) 1
  rw [e]
  rfl
private def pauliNormSum : ℝ := ∑ a, ‖Matrices.ComplexMatrix2.pauliFamily a‖
private theorem pauliNormSum_nonneg : 0 ≤ pauliNormSum :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
private theorem norm_scaledForm_le [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)] (hη : 0 < finestMesh L k)
    (w : TripleCoordIndex L n k → ℂ) (b : Edge L n k 0) :
    ‖scaledForm w b‖ ≤ (finestMesh L k)⁻¹ * pauliNormSum * ‖w‖ := by
  rw [scaledForm_apply]
  calc _ ≤ ∑ a, ‖((((finestMesh L k)⁻¹ : ℝ) : ℂ) * orientationSign b *
        w (.inl (.inl (a, positiveRepresentative b)))) • Matrices.ComplexMatrix2.pauliFamily a‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a, ((finestMesh L k)⁻¹ * ‖w‖) * ‖Matrices.ComplexMatrix2.pauliFamily a‖ :=
        Finset.sum_le_sum fun a _ => by
        rw [norm_smul, norm_mul, norm_mul, norm_orientationSign, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.2 hη.le)]
        gcongr
        exact norm_le_pi_norm w _
    _ = _ := by
        rw [← Finset.mul_sum]
        simp only [pauliNormSum]
        ring
private lemma levelVertexCell_fine (x : Vertex L n k 0) : levelVertexCell x = fineVertexCell x := by apply _root_.YangMills.SharedProofs.p6946 <;> assumption
private lemma levelVertexCell_top (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) (hc : NeighbouringFineVertexCells) (ht : TopEdgesAndCubes)
    (y : Vertex L n k k) : levelVertexCell y = y := by apply _root_.YangMills.SharedProofs.p53151 <;> assumption
private theorem tripleCoordIndexCell_near {r : ℝ} {y : Vertex L n k k} {b : Edge L n k 0}
    (hb : b ∈ edgesNearCell r y) (a : Fin 3) :
    cellDist (tripleCoordIndexCell
      (.inl (.inl (a, positiveRepresentative b)) : TripleCoordIndex L n k)) y ≤ r := by
  change cellDist (levelVertexCell (positiveRepresentative b).1.source) y ≤ r
  rw [levelVertexCell_fine]
  by_cases h : b.IsPositivelyOriented
  · have e : positiveRepresentative b = ⟨b, h⟩ := dif_pos h
    rw [e]
    exact hb.1
  · have e : positiveRepresentative b =
        ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩ := dif_neg h
    rw [e]
    exact hb.2
private def tracelessPauliBasis : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless :=
  Module.Basis.ofEquivFun OneLoop.pauliCoordinateEquiv
private theorem coe_tracelessPauliBasis (c : Fin 3) :
    ((tracelessPauliBasis c : Matrices.ComplexMatrix2.traceless) : Matrices.ComplexMatrix2) =
      Matrices.ComplexMatrix2.pauliFamily c := by
  rw [tracelessPauliBasis, Module.Basis.coe_ofEquivFun, coe_pauliCoordinateEquiv_symm]
  simp [Pi.single_apply]
private theorem isLocallyHolomorphic_comp_scaledForm
    (hAn : Matrices.ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    (hO : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hη : 0 < finestMesh L k)
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
    {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {G : (Edge L n k 0 → Matrices.ComplexMatrix2) → Matrix ι' ι ℂ} {ρ C r : ℝ} (hρ : 0 < ρ)
    (H : IsLocalNearCells c c' G ρ C r) :
    IsLocallyHolomorphicFamily (tripleCoordIndexCell (L := L) (n := n) (k := k)) c c'
      (fun w => G (scaledForm w)) (ρ * finestMesh L k / (pauliNormSum + 1)) C r := by
  classical
  have hP : 0 ≤ pauliNormSum := pauliNormSum_nonneg
  have hP1 : 0 < pauliNormSum + 1 := by linarith
  set ρ₁ : ℝ := ρ * pauliNormSum / (pauliNormSum + 1) with hρ₁
  have h₁0 : 0 ≤ ρ₁ := by positivity
  have h₁ρ : ρ₁ < ρ := by
    rw [hρ₁, div_lt_iff₀ hP1]
    nlinarith
  have small : ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ)
      (ρ * finestMesh L k / (pauliNormSum + 1)), ∀ b, ‖scaledForm w b‖ ≤ ρ₁ := by
    intro w hw b
    have hw' := mem_ball_zero_iff.1 hw
    refine (norm_scaledForm_le hη w b).trans ?_
    have h2 : (finestMesh L k)⁻¹ * pauliNormSum * ‖w‖ ≤
        (finestMesh L k)⁻¹ * pauliNormSum * (ρ * finestMesh L k / (pauliNormSum + 1)) := by
      gcongr
    refine h2.trans (le_of_eq ?_)
    rw [hρ₁]
    field_simp
  have hsup : ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ)
      (ρ * finestMesh L k / (pauliNormSum + 1)),
      maxOperatorNorm (scaledForm w) < ENNReal.ofReal ρ := by
    intro w hw
    refine lt_of_le_of_lt (iSup_le fun b => ENNReal.ofReal_le_ofReal (small w hw b)) ?_
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 h₁ρ
  have hmem : ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ)
      (ρ * finestMesh L k / (pauliNormSum + 1)), scaledForm w ∈ smallFormBall L n k ρ :=
    fun w hw => ⟨scaledForm_mem hx w, (hsup w hw).le⟩
  refine ⟨fun p q => ?_, fun w hw => H.norm_le _ (hmem w hw), fun p q w hw w' hw' h => ?_,
    fun w hw p q hpq => H.eq_zero_of_far _ (hmem w hw) p q hpq⟩
  · obtain ⟨F, f, hf, he⟩ := H.holomorphic p q
    obtain ⟨-, hν⟩ := hf tracelessPauliBasis
    let ν : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
    have H₁ := hν ν
    have D₁ := (hO _ _ _ _ H₁.1).1 H₁
    let Λ : (TripleCoordIndex L n k → ℂ) → Coordinates.ComplexCoordinates (Fintype.card F * 3) :=
      fun w m =>
        (((finestMesh L k)⁻¹ : ℝ) : ℂ) * orientationSign (ν.symm (finProdFinEquiv.symm m).1).1 *
          w (.inl (.inl ((finProdFinEquiv.symm m).2,
            positiveRepresentative (ν.symm (finProdFinEquiv.symm m).1).1)))
    have hΛ : Differentiable ℂ Λ := by
      refine differentiable_pi.2 fun m => ?_
      exact (differentiable_const _).mul (differentiable_apply _)
    have tup : ∀ w, Matrices.GroupLieProduct.tupleOfCoords tracelessPauliBasis ν (Λ w) =
        fun i : F => scaledForm w i := by
      intro w
      funext i
      rw [scaledForm_apply]
      simp only [Matrices.GroupLieProduct.tupleOfCoords,
        Coordinates.ComplexCoordinates.tracelessTuple, coe_tracelessPauliBasis, Λ,
        Equiv.symm_apply_apply]
    have maps : MapsTo Λ (Metric.ball 0 (ρ * finestMesh L k / (pauliNormSum + 1)))
        (Matrices.GroupLieProduct.tupleOfCoords tracelessPauliBasis ν ⁻¹'
          Matrices.GroupLieProduct.supBall F ρ) := by
      intro w hw
      show Matrices.GroupLieProduct.tupleOfCoords tracelessPauliBasis ν (Λ w) ∈
        Matrices.GroupLieProduct.supBall F ρ
      rw [tup w]
      refine ⟨fun i => ?_, lt_of_le_of_lt (Real.iSup_le (fun i => small w hw i) h₁0) h₁ρ⟩
      show scaledForm w i ∈ Matrices.ComplexMatrix2.traceless
      rw [scaledForm_apply]
      exact sum_smul_pauli_mem_traceless _
    have D₂ := differentiableOn_pi.1 (D₁.comp hΛ.differentiableOn maps) 0
    refine (analyticOnNhd_of_differentiableOn_coords hAn Metric.isOpen_ball D₂).congr
      Metric.isOpen_ball ?_
    intro w hw
    show f (Matrices.GroupLieProduct.tupleOfCoords tracelessPauliBasis ν (Λ w)) = _
    rw [tup w]
    exact he _ (scaledForm_mem hx w) (hsup w hw)
  · refine H.eq_of_eqOn p q _ (hmem w hw) _ (hmem w' hw') fun b hb => ?_
    rw [scaledForm_apply, scaledForm_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [h _ (tripleCoordIndexCell_near hb a)]
private lemma meshTranspose_eq {σ σ' : Type} (K : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) :
    Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k) K) =
      (unitNormScale L k * unitNormScale L k) • (Matrix.of K).transpose := by apply _root_.YangMills.SharedProofs.p28483 <;> assumption
end ScaledForms
theorem smoothingTransposeIsLocal_holds (hA : MeanKernelsAreLocalNearCells)
    (hcl : LocallyHolomorphicFamiliesClosed)
    (hO : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hAn : Matrices.ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    (hc : NeighbouringFineVertexCells) (ht : TopEdgesAndCubes) :
    SmoothingTransposeIsLocal := by
  intro L hL k hk
  obtain ⟨ρ, C, r, hρ, hC, hr, H⟩ := hA L hL
  obtain ⟨n₀, Hn⟩ := H k hk
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hη : 0 < finestMesh L k := by
    unfold finestMesh meshAt
    positivity
  have hP : 0 ≤ pauliNormSum := pauliNormSum_nonneg
  refine ⟨ρ * finestMesh L k / (pauliNormSum + 1),
    ‖((finestMesh L k ^ 2 : ℝ) : ℂ)‖ * C, 2 * r, by positivity, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop n₀, eventually_gt_atTop 0] with n h₀ hn
  intro iW iT iS iK dK
  let dS : DecidableEq (Fin 3 × Vertex L n k 0) := Classical.decEq _
  let iB : Fintype (Fin 3 × PositiveEdge L n k 0) :=
    Fintype.ofInjective (Sum.inl : _ → LevelFormIndex L n k) Sum.inl_injective
  let dB : DecidableEq (Fin 3 × PositiveEdge L n k 0) := Classical.decEq _
  let dT : DecidableEq (Fin 3 × PositiveEdge L n k k) := Classical.decEq _
  have hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have R := (Hn n h₀ hn).2.2.1
  have B := isLocallyHolomorphic_comp_scaledForm hAn hO hη hx hρ R
  have T := (hcl L n k).transpose hr B
  have S := (hcl L n k).smul ((finestMesh L k ^ 2 : ℝ) : ℂ) T
  have e1 : (fineIndexCell : Fin 3 × Vertex L n k 0 → Vertex L n k k) = colouredVertexCell :=
    funext fun p => levelVertexCell_fine p.2
  have e2 : (fun p : Fin 3 × Vertex L n k k => levelVertexCell p.2) = vertexCell :=
    funext fun p => levelVertexCell_top hL hn hk hc ht p.2
  have key : ∀ w : TripleCoordIndex L n k → ℂ, ((finestMesh L k ^ 4 : ℝ) : ℂ) •
      (Matrix.of (rescaledOperators L n k (complexChainPoint w).fine).Rt :
        Matrix (Fin 3 × Vertex L n k 0) (Fin 3 × Vertex L n k k) ℂ) =
      ((finestMesh L k ^ 2 : ℝ) : ℂ) • (unitNormScale L k •
        Matrix.of (rescaledOperators L n k (remainderGaugeField (scaledForm w))).R).transpose := by
    intro w
    rw [complexChainPoint_fine_eq hη w]
    change _ • Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k) _) = _
    rw [meshTranspose_eq, Matrix.transpose_smul, smul_smul, smul_smul]
    congr 1
    have h0 : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    simp only [unitNormScale]
    push_cast
    field_simp
  rw [e1, e2, funext key]
  exact S
end YangMills.Construction.RunningCouplingSlope.SmoothingTransposeLocality
end
