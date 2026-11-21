import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.Matrices.HolomorphicOnMatrixFamilies
import YangMills.Construction.Matrices.TracelessHolomorphyDifferentiable
import YangMills.Construction.RunningCouplingSlope.AverageFamiliesReadNearCells
import YangMills.Construction.RunningCouplingSlope.ColourCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreClosed
import YangMills.Construction.RunningCouplingSlope.MapsOfTheBackgroundGaugeInColours
import YangMills.Construction.RunningCouplingSlope.TheHessianOfTheSoftActionReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheOrbitMapReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheTermOfTheBackgroundGaugeReadsNearCells
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.GaugeSliceResidualLocal
open Tower
open Matrices
open Tower.IteratedSmallFieldMeans (HolomorphicInEntries smallFormBall)
open Tower.LeftChartFields (scalarCoords)
section Holomorphy
private theorem analyticOnNhd_of_differentiableOn
    (hM : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    {I : Type} [Fintype I] {O : Set (I → ℂ)} (hO : IsOpen O) {φ : (I → ℂ) → ℂ}
    (hφ : DifferentiableOn ℂ φ O) : AnalyticOnNhd ℂ φ O := by
  let ent : ComplexMatrix2 →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ 0 0)
  let sc : ℂ →L[ℂ] ComplexMatrix2 := LinearMap.toContinuousLinearMap
    (LinearMap.toSpanSingleton ℂ ComplexMatrix2 (1 : ComplexMatrix2))
  let down : (I → ComplexMatrix2) →L[ℂ] (I → ℂ) :=
    ContinuousLinearMap.pi fun i => ent.comp (ContinuousLinearMap.proj i)
  let up : (I → ℂ) →L[ℂ] (I → ComplexMatrix2) :=
    ContinuousLinearMap.pi fun i => sc.comp (ContinuousLinearMap.proj i)
  have hes : ∀ c : ℂ, ent (sc c) = c := fun c => by
    show (c • (1 : ComplexMatrix2)) 0 0 = c
    simp
  have hdu : ∀ w, down (up w) = w := fun w => funext fun i => hes (w i)
  have hO' : IsOpen (down ⁻¹' O) := hO.preimage down.continuous
  have hf : DifferentiableOn ℂ (fun X => sc (φ (down X))) (down ⁻¹' O) :=
    sc.differentiable.comp_differentiableOn
      (hφ.comp down.differentiable.differentiableOn fun X hX => hX)
  have ha := hM I _ _ hO' hf
  intro w hw
  have h1 : AnalyticAt ℂ (fun X => sc (φ (down X))) (up w) :=
    ha (up w) (by show down (up w) ∈ O; rw [hdu]; exact hw)
  have h1' : AnalyticAt ℂ ((fun X => sc (φ (down X))) ∘ up) w :=
    AnalyticAt.comp h1 (up.analyticAt w)
  have h2 : AnalyticAt ℂ (ent ∘ ((fun X => sc (φ (down X))) ∘ up)) w :=
    AnalyticAt.comp (ent.analyticAt _) h1'
  refine h2.congr (Eventually.of_forall fun u => ?_)
  show ent (sc (φ (down (up u)))) = φ u
  rw [hes, hdu]
abbrev _root_.YangMills.SharedProofs.p33934 := @analyticOnNhd_of_differentiableOn
private theorem analyticOnNhd_comp_linear
    (hM : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    (hT : GroupLieProduct.HolomorphicOnTracelessIffDifferentiable)
    {β I : Type} [Fintype I] {S : Set (β → ComplexMatrix2)} {g : (β → ComplexMatrix2) → ℂ} {ρ ρ' t : ℝ}
    (hg : HolomorphicInEntries scalarCoords S ρ g) (v : (I → ℂ) →ₗ[ℂ] (β → ComplexMatrix2))
    (hv : ∀ w b, v w b ∈ ComplexMatrix2.traceless) (ht : t < ρ) (ht0 : 0 ≤ t)
    (hS : ∀ w ∈ Metric.ball (0 : I → ℂ) ρ', v w ∈ S ∧ ∀ b, ComplexMatrix2.operatorNorm (v w b) ≤ t) :
    AnalyticOnNhd ℂ (fun w => g (v w)) (Metric.ball 0 ρ') := by
  obtain ⟨F, f, hf, hfe⟩ := hg
  let b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.Basis.ofEquivFun OneLoop.pauliCoordinateEquiv
  have hlin : IsLinearMap ℂ (scalarCoords : ℂ ≃ Coordinates.ComplexCoordinates 1) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨-, hd⟩ := (hT F ℂ 1 b scalarCoords hlin _ f).1 (hf b)
  let Φ : (I → ℂ) →ₗ[ℂ] ↥(GroupLieProduct.tracelessPiSubmodule F) :=
    { toFun := fun w => ⟨fun i => v w i.1, fun i _ => hv w i.1⟩
      map_add' := fun w w' => by
        refine Subtype.ext (funext fun i => ?_)
        show v (w + w') i.1 = v w i.1 + v w' i.1
        rw [map_add]
        rfl
      map_smul' := fun c w => by
        refine Subtype.ext (funext fun i => ?_)
        show v (c • w) i.1 = c • v w i.1
        rw [map_smul]
        rfl }
  let Φc : (I → ℂ) →L[ℂ] ↥(GroupLieProduct.tracelessPiSubmodule F) :=
    LinearMap.toContinuousLinearMap Φ
  have h1 : DifferentiableOn ℂ (fun w => f (fun i : F => v w i.1)) (Metric.ball 0 ρ') := by
    refine hd.comp Φc.differentiable.differentiableOn fun w hw => ?_
    refine ⟨fun i => hv w i.1, ?_⟩
    exact lt_of_le_of_lt (Real.iSup_le (fun i => (hS w hw).2 i.1) ht0) ht
  refine (analyticOnNhd_of_differentiableOn hM Metric.isOpen_ball h1).congr Metric.isOpen_ball
    fun w hw => ?_
  refine hfe _ (hS w hw).1 ?_
  have hρ : 0 < ρ := lt_of_le_of_lt ht0 ht
  refine lt_of_le_of_lt (iSup_le fun x => ENNReal.ofReal_le_ofReal ((hS w hw).2 x)) ?_
  exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 ht
end Holomorphy
section Form
variable {L n k : ℕ}
private theorem complexFineValues_of_pos (w : TripleCoordIndex L n k → ℂ) {b : Edge L n k 0}
    (h : b.IsPositivelyOriented) :
    complexFineValues w b = ∑ a, w (.inl (.inl (a, ⟨b, h⟩))) • ComplexMatrix2.pauliFamily a := by
  simp [complexFineValues, edgeFormOfPositiveValues, dif_pos h, ofPauliCoeffs]
private theorem complexFineValues_of_neg (w : TripleCoordIndex L n k → ℂ) {b : Edge L n k 0}
    (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    complexFineValues w b =
      -∑ a, w (.inl (.inl (a, ⟨b.opposite, h'⟩))) • ComplexMatrix2.pauliFamily a := by
  simp [complexFineValues, edgeFormOfPositiveValues, dif_neg h, dif_pos h', ofPauliCoeffs]
private def complexFineValuesLinear (L n k : ℕ) :
    (TripleCoordIndex L n k → ℂ) →ₗ[ℂ] (Edge L n k 0 → ComplexMatrix2) where
  toFun := complexFineValues
  map_add' w w' := by
    funext b
    by_cases h : b.IsPositivelyOriented
    · simp [complexFineValues_of_pos _ h, add_smul, Finset.sum_add_distrib]
    · by_cases h' : b.opposite.IsPositivelyOriented
      · simp [complexFineValues_of_neg _ h h', add_smul, Finset.sum_add_distrib]
        abel
      · simp [complexFineValues, edgeFormOfPositiveValues, dif_neg h, dif_neg h']
  map_smul' c w := by
    funext b
    by_cases h : b.IsPositivelyOriented
    · simp [complexFineValues_of_pos _ h, Finset.smul_sum, smul_smul]
    · by_cases h' : b.opposite.IsPositivelyOriented
      · simp [complexFineValues_of_neg _ h h', Finset.smul_sum, smul_smul]
      · simp [complexFineValues, edgeFormOfPositiveValues, dif_neg h, dif_neg h']
private def coordForm (L n k : ℕ) :
    (TripleCoordIndex L n k → ℂ) →ₗ[ℂ] (Edge L n k 0 → ComplexMatrix2) :=
  (((finestMesh L k)⁻¹ : ℝ) : ℂ) • complexFineValuesLinear L n k
private theorem coordForm_apply (w : TripleCoordIndex L n k → ℂ) (b : Edge L n k 0) :
    coordForm L n k w b = (((finestMesh L k)⁻¹ : ℝ) : ℂ) • complexFineValues w b :=
  rfl
private theorem sum_smul_pauli_mem (c : Fin 3 → ℂ) :
    ∑ a, c a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
private theorem complexFineValues_mem
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (w : TripleCoordIndex L n k → ℂ) (b : Edge L n k 0) :
    complexFineValues w b ∈ ComplexMatrix2.traceless := by
  rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [complexFineValues_of_pos w h₁]
    exact sum_smul_pauli_mem _
  · rw [complexFineValues_of_neg w h₂ h₁]
    exact Submodule.neg_mem _ (sum_smul_pauli_mem _)
private theorem complexFineValues_opposite
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (w : TripleCoordIndex L n k → ℂ) (b : Edge L n k 0) :
    complexFineValues w b.opposite = -complexFineValues w b := by
  have hc : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
  rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have h₃ : b.opposite.opposite.IsPositivelyOriented := by rw [hc]; exact h₁
    rw [complexFineValues_of_neg w h₂ h₃, complexFineValues_of_pos w h₁]
    congr 2
  · rw [complexFineValues_of_pos w h₁, complexFineValues_of_neg w h₂ h₁, neg_neg]
abbrev _root_.YangMills.SharedProofs.p52422 := @complexFineValues_opposite
private theorem coordForm_mem
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (w : TripleCoordIndex L n k → ℂ) :
    coordForm L n k w ∈ complexEdgeForms L n k 0 := by
  refine ⟨fun b _ => ?_, fun b => ?_⟩
  · rw [coordForm_apply]
    exact Submodule.smul_mem _ _ (complexFineValues_mem hx w b)
  · rw [coordForm_apply, coordForm_apply, complexFineValues_opposite hx, smul_neg]
private theorem norm_complexFineValues_le
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [Fintype (TripleCoordIndex L n k)] (w : TripleCoordIndex L n k → ℂ) (b : Edge L n k 0) :
    ‖complexFineValues w b‖ ≤ (∑ a, ‖ComplexMatrix2.pauliFamily a‖) * ‖w‖ := by
  have h : ∀ c : Fin 3 → TripleCoordIndex L n k,
      ‖∑ a, w (c a) • ComplexMatrix2.pauliFamily a‖ ≤
        (∑ a, ‖ComplexMatrix2.pauliFamily a‖) * ‖w‖ := by
    intro c
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w _) (norm_nonneg _)
  rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [complexFineValues_of_pos w h₁]
    exact h _
  · rw [complexFineValues_of_neg w h₂ h₁, norm_neg]
    exact h _
private theorem levelVertexCell_eq (x : Vertex L n k 0) : levelVertexCell x = fineVertexCell x := by apply _root_.YangMills.SharedProofs.p6946 <;> assumption
private theorem tripleCoordIndexCell_inl (a : Fin 3) (c : PositiveEdge L n k 0) :
    tripleCoordIndexCell (.inl (.inl (a, c)) : TripleCoordIndex L n k) = fineVertexCell c.1.source :=
  levelVertexCell_eq _
private theorem coordForm_eqOn
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {w w' : TripleCoordIndex L n k → ℂ} {y : Vertex L n k k} {r : ℝ}
    (h : ∀ i, cellDist (tripleCoordIndexCell i) y ≤ r → w i = w' i) :
    Set.EqOn (coordForm L n k w) (coordForm L n k w') (edgesNearCell r y) := by
  intro b hb
  rw [coordForm_apply, coordForm_apply]
  congr 1
  rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [complexFineValues_of_pos w h₁, complexFineValues_of_pos w' h₁]
    exact Finset.sum_congr rfl fun a _ => by
      rw [h _ (by rw [tripleCoordIndexCell_inl]; exact hb.1)]
  · rw [complexFineValues_of_neg w h₂ h₁, complexFineValues_of_neg w' h₂ h₁]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by
      rw [h _ (by rw [tripleCoordIndexCell_inl]; exact hb.2)]
private theorem isLocallyHolomorphic_comp_coordForm
    (hM : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    (hT : GroupLieProduct.HolomorphicOnTracelessIffDifferentiable)
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [Fintype (TripleCoordIndex L n k)] {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {F : (Edge L n k 0 → ComplexMatrix2) → Matrix ι' ι ℂ} {ρ₁ C r ρ t : ℝ} (ht : t < ρ₁) (ht0 : 0 ≤ t)
    (hρ : ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ b,
      ComplexMatrix2.operatorNorm (coordForm L n k w b) ≤ t)
    (hF : IsLocalNearCells c c' F ρ₁ C r) :
    IsLocallyHolomorphicFamily tripleCoordIndexCell c c' (fun w => F (coordForm L n k w))
      ρ C r := by
  have small : ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
      coordForm L n k w ∈ smallFormBall L n k ρ₁ := fun w hw =>
    ⟨coordForm_mem hx w, iSup_le fun b => ENNReal.ofReal_le_ofReal ((hρ w hw b).trans ht.le)⟩
  refine ⟨fun p q => ?_, fun w hw => hF.norm_le _ (small w hw),
    fun p q w hw w' hw' h => hF.eq_of_eqOn p q _ (small w hw) _ (small w' hw') (coordForm_eqOn hx h),
    fun w hw p q h => hF.eq_zero_of_far _ (small w hw) p q h⟩
  exact analyticOnNhd_comp_linear hM hT (hF.holomorphic p q) (coordForm L n k)
    (fun w b => Submodule.smul_mem _ _ (complexFineValues_mem hx w b)) ht ht0
    fun w hw => ⟨coordForm_mem hx w, hρ w hw⟩
end Form
section Real
variable {L n k : ℕ}
private theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [Fintype (Fin 3 × Vertex L n k 0)]
  [Fintype (Fin 3 × Vertex L n k k)]
private theorem sum_toPauliCoeffs_smul (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k 0) :
    ∑ a, toPauliCoeffs (restrictToPositiveEdges (B : Edge L n k 0 → ComplexMatrix2)) (a, c) •
        ComplexMatrix2.pauliFamily a =
      (B : Edge L n k 0 → ComplexMatrix2) c.1 := by
  have hB : (B : Edge L n k 0 → ComplexMatrix2) ∈ complexEdgeForms L n k 0 :=
    ⟨fun b hb => (B.2.1 b hb).2, B.2.2⟩
  have hm : (B : Edge L n k 0 → ComplexMatrix2) c.1 ∈ ComplexMatrix2.traceless := hB.1 c.1 c.2
  have h := sum_pauliCoeff_smul hm
  exact h
private theorem complexFineValues_complexify
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ) :
    complexFineValues (complexifyCoords x) =
      ((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = (tripleOfCoords P x).1 := ⟨_, rfl⟩
  rw [← hξ]
  have hco : ∀ ι, complexifyCoords x (.inl (.inl ι)) =
      toPauliCoeffs (restrictToPositiveEdges (ξ.1 : Edge L n k 0 → ComplexMatrix2)) ι := by
    intro ι
    rw [P.formCoords_base]
    have : P.formCoords ξ = fun p => x (.inl p) := by
      rw [hξ]
      exact LinearEquiv.apply_symm_apply _ _
    rw [this]
    rfl
  have hpos : ∀ c : PositiveEdge L n k 0,
      ∑ a, complexifyCoords x (.inl (.inl (a, c))) • ComplexMatrix2.pauliFamily a =
        (ξ.1 : Edge L n k 0 → ComplexMatrix2) c.1 := by
    intro c
    simp only [hco]
    exact sum_toPauliCoeffs_smul ξ.1 c
  funext b
  rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [complexFineValues_of_pos _ h₁]
    exact hpos ⟨b, h₁⟩
  · rw [complexFineValues_of_neg _ h₂ h₁, hpos ⟨b.opposite, h₁⟩, ξ.1.2.2 b, neg_neg]
private theorem smul_ofReal_inv_smul {η : ℝ} (hη : η ≠ 0) (X : ComplexMatrix2) :
    η • (((η⁻¹ : ℝ) : ℂ) • X) = X := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hη]
  simp
private theorem fine_pointOfCoords
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hη : finestMesh L k ≠ 0) (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ) :
    (pointOfCoords P x).fine =
      remainderGaugeField (coordForm L n k (complexifyCoords x)) := by
  have e : scaledRemainderForm (coordForm L n k (complexifyCoords x)) =
      ((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) := by
    funext b
    show finestMesh L k • ((((finestMesh L k)⁻¹ : ℝ) : ℂ) •
      complexFineValues (complexifyCoords x) b) = _
    rw [smul_ofReal_inv_smul hη, complexFineValues_complexify hx P x]
  unfold remainderGaugeField IdentityExpChart.expForm
  rw [e]
  rfl
private theorem expTwist_of_pos {A U : Edge L n k 0 → ComplexMatrix2} {b : Edge L n k 0}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by
  simp [PeriodicLattice.expTwist, if_pos hb]
private theorem expTwist_of_neg {A U : Edge L n k 0 → ComplexMatrix2} {b : Edge L n k 0}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by
  simp [PeriodicLattice.expTwist, if_neg hb]
private theorem matExp_mem_compact {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
private theorem inv_mem_compact {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem inv_inv_of_mem_compact {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
private theorem expTwist_one_mem_fieldSpace
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A : Edge L n k 0 → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k 0) :
    PeriodicLattice.expTwist A (fun _ => 1) ∈ fieldSpace L n k 0 := by
  have hpos : ∀ b : Edge L n k 0, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • A b) * 1 ∈ PeriodicLattice.compactGaugeGroup :=
    fun b hb => by
      rw [mul_one]
      exact matExp_mem_compact (hA.1 b hb)
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [expTwist_of_pos h₁]
      exact hpos b h₁
    · rw [expTwist_of_neg h₂]
      exact inv_mem_compact (hpos _ h₁)
  · rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hc : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
      rw [expTwist_of_pos h₁, expTwist_of_neg h₂, hc]
    · rw [expTwist_of_pos h₁, expTwist_of_neg h₂, inv_inv_of_mem_compact (hpos _ h₁)]
private theorem tendsto_matExp_mul_one {f : (TripleCoordIndex L n k → ℝ) → ComplexMatrix2}
    (hf : ContinuousAt f 0) (h0 : f 0 = 0) :
    Tendsto (fun x => ComplexMatrix2.matExp (Complex.I • f x) * 1) (𝓝 0) (𝓝 1) := by
  have h₁ : ContinuousAt (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2) (Complex.I • f 0) :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) _).differentiableAt.continuousAt
  have h₂ : ContinuousAt (fun x => Complex.I • f x) (0 : TripleCoordIndex L n k → ℝ) :=
    hf.const_smul Complex.I
  have h₃ := (ContinuousAt.comp (f := fun x => Complex.I • f x) h₁ h₂).tendsto
  simp only [Function.comp, h0, smul_zero, NormedSpace.exp_zero] at h₃
  refine h₃.congr fun x => ?_
  simp [ComplexMatrix2.matExp]
private theorem continuousAt_complexFineValues [Fintype (TripleCoordIndex L n k)]
    (b : Edge L n k 0) :
    ContinuousAt (fun x : TripleCoordIndex L n k → ℝ => complexFineValues (complexifyCoords x) b)
      0 := by
  let T : (TripleCoordIndex L n k → ℂ) →ₗ[ℂ] ComplexMatrix2 :=
    LinearMap.proj b ∘ₗ complexFineValuesLinear L n k
  have h₁ : Continuous T := LinearMap.continuous_of_finiteDimensional T
  have h₂ : Continuous (fun x : TripleCoordIndex L n k → ℝ => complexifyCoords x) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  exact (h₁.comp h₂).continuousAt
private theorem fine_pointOfCoords_eq (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ) :
    (pointOfCoords P x).fine = PeriodicLattice.expTwist
      ((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) (fun _ => 1) := rfl
private theorem tendsto_fine_pointOfCoords
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (P : PauliCoordinates L n k) :
    Tendsto (fun x => (pointOfCoords P x).fine) (𝓝 0)
      (𝓝[fieldSpace L n k 0] fun _ => (1 : ComplexMatrix2)) := by
  have hv : ∀ x b, ((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) b =
      complexFineValues (complexifyCoords x) b := fun x b =>
    (congrFun (complexFineValues_complexify hx P x) b).symm
  have h00 : ∀ b : Edge L n k 0, complexFineValues
      (complexifyCoords (0 : TripleCoordIndex L n k → ℝ)) b = 0 := fun b => by
    have e : complexifyCoords (0 : TripleCoordIndex L n k → ℝ) = 0 := by
      funext i
      simp [complexifyCoords]
    rw [e]
    exact congrFun (map_zero (complexFineValuesLinear L n k)) b
  have hb : ∀ b : Edge L n k 0, b.IsPositivelyOriented → Tendsto (fun x =>
      ComplexMatrix2.matExp
        (Complex.I • ((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) b) * 1)
      (𝓝 0) (𝓝 1) := fun b _ => by
    simp only [hv]
    exact tendsto_matExp_mul_one (continuousAt_complexFineValues b) (h00 b)
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_, Eventually.of_forall fun x => ?_⟩
  · rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine (hb b h₁).congr fun x => ?_
      rw [fine_pointOfCoords_eq, expTwist_of_pos h₁]
    · have hinv : ContinuousAt (Ring.inverse : ComplexMatrix2 → ComplexMatrix2)
          ((1 : ComplexMatrix2ˣ) : ComplexMatrix2) :=
        NormedRing.inverse_continuousAt 1
      have h₃ : Tendsto (fun x => Ring.inverse
          (ComplexMatrix2.matExp (Complex.I •
            ((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) b.opposite) * 1))
          (𝓝 0) (𝓝 (Ring.inverse ((1 : ComplexMatrix2ˣ) : ComplexMatrix2))) :=
        hinv.tendsto.comp (hb b.opposite h₁)
      have e1 : Ring.inverse ((1 : ComplexMatrix2ˣ) : ComplexMatrix2) = 1 := by simp
      rw [e1] at h₃
      refine h₃.congr fun x => ?_
      rw [fine_pointOfCoords_eq, expTwist_of_neg h₂, Matrix.nonsing_inv_eq_ringInverse]
  · rw [fine_pointOfCoords_eq]
    exact expTwist_one_mem_fieldSpace hx (tripleOfCoords P x).1.1.2
private theorem sum_over_sum {A B : Type} [Fintype A] [Fintype B] [i : Fintype (A ⊕ B)]
    (f : A ⊕ B → ℂ) : ∑ q, f q = ∑ a, f (.inl a) + ∑ b, f (.inr b) := by
  rw [Subsingleton.elim i (instFintypeSum A B)]
  exact Fintype.sum_sum_type f
private def baseWeights (L n k : ℕ) : LevelFormIndex L n k → ℂ :=
  Sum.elim (fun _ => 1) fun _ => 0
private theorem toPauliCoeffs_adjoint [DecidableEq (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k 0)]
    [Fintype (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))]
    (Ψb : edgeFormSpace L n k 0 ≃ₗ[ℝ] (Fin 3 × PositiveEdge L n k 0 → ℝ))
    (hΨb : ∀ (f : edgeFormSpace L n k 0) ι,
      toPauliCoeffs (restrictToPositiveEdges (f : Edge L n k 0 → ComplexMatrix2)) ι =
        ((Ψb f ι : ℝ) : ℂ))
    (hpb : ∀ f g : edgeFormSpace L n k 0, edgeFormPairing (f : Edge L n k 0 → ComplexMatrix2)
      (g : Edge L n k 0 → ComplexMatrix2) = ((∑ ι, Ψb f ι * Ψb g ι : ℝ) : ℂ))
    (Ψs : vertexFunctionSpace L n k 0 ≃ₗ[ℝ] (Fin 3 × Vertex L n k 0 → ℝ))
    (hΨs : ∀ (f : vertexFunctionSpace L n k 0) ι,
      toPauliCoeffs (f : Vertex L n k 0 → ComplexMatrix2) ι = ((Ψs f ι : ℝ) : ℂ))
    (hps : ∀ f g : vertexFunctionSpace L n k 0,
      traceFinsumPairing (f : Vertex L n k 0 → ComplexMatrix2)
        (g : Vertex L n k 0 → ComplexMatrix2) = ((∑ ι, Ψs f ι * Ψs g ι : ℝ) : ℂ))
    (P : PauliCoordinates L n k) (D : Matrix (LevelFormIndex L n k) (Fin 3 × Vertex L n k 0) ℂ)
    (T : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0)
    (M : vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)
    (hT : ∀ (x : edgeFormSpace L n k 0) (l : vertexFunctionSpace L n k 0),
      traceFinsumPairing (T x : Vertex L n k 0 → ComplexMatrix2) (l : Vertex L n k 0 → ComplexMatrix2) =
        edgeFormPairing (x : Edge L n k 0 → ComplexMatrix2) (M l : Edge L n k 0 → ComplexMatrix2))
    (hD : ∀ l : vertexFunctionSpace L n k 0, ∃ η : LevelForms L n k,
      (η.1 : Edge L n k 0 → ComplexMatrix2) = (M l : Edge L n k 0 → ComplexMatrix2) ∧
      complexifyCoords (P.formCoords η) =
        D.mulVec (toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2)))
    (ξ : LevelForms L n k) :
    toPauliCoeffs (T ξ.1 : Vertex L n k 0 → ComplexMatrix2) =
      (D.transpose * Matrix.diagonal (baseWeights L n k)).mulVec
        (complexifyCoords (P.formCoords ξ)) := by
  classical
  funext ι
  set l := Ψs.symm (Pi.single ι 1) with hl
  have hcl : toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2) = Pi.single ι 1 := by
    funext j
    rw [hΨs, hl, LinearEquiv.apply_symm_apply]
    by_cases hj : j = ι
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  have e1 : toPauliCoeffs (T ξ.1 : Vertex L n k 0 → ComplexMatrix2) ι =
      traceFinsumPairing (T ξ.1 : Vertex L n k 0 → ComplexMatrix2)
        (l : Vertex L n k 0 → ComplexMatrix2) := by
    rw [hps, hΨs, hl]
    simp only [LinearEquiv.apply_symm_apply]
    rw [Finset.sum_eq_single ι]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  obtain ⟨η, h₁, h₂⟩ := hD l
  have e2 : edgeFormPairing (ξ.1 : Edge L n k 0 → ComplexMatrix2)
      (M l : Edge L n k 0 → ComplexMatrix2) =
      ∑ p, complexifyCoords (P.formCoords ξ) (.inl p) * D (.inl p) ι := by
    rw [← h₁, hpb]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    have e3 := congrFun h₂ (.inl p)
    rw [hcl] at e3
    have e4 : complexifyCoords (P.formCoords η) (.inl p) = ((Ψb η.1 p : ℝ) : ℂ) := by
      rw [← hΨb, P.formCoords_base]
      rfl
    have e5 : complexifyCoords (P.formCoords ξ) (.inl p) = ((Ψb ξ.1 p : ℝ) : ℂ) := by
      rw [← hΨb, P.formCoords_base]
      rfl
    rw [e5, ← e4, e3]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e1, hT, e2]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal, Matrix.transpose_apply]
  rw [sum_over_sum]
  simp [baseWeights, mul_comm]
private theorem sq_norm_eq_dot
    (Ψs : vertexFunctionSpace L n k 0 ≃ₗ[ℝ] (Fin 3 × Vertex L n k 0 → ℝ))
    (hΨs : ∀ (f : vertexFunctionSpace L n k 0) ι,
      toPauliCoeffs (f : Vertex L n k 0 → ComplexMatrix2) ι = ((Ψs f ι : ℝ) : ℂ))
    (hps : ∀ f g : vertexFunctionSpace L n k 0,
      traceFinsumPairing (f : Vertex L n k 0 → ComplexMatrix2)
        (g : Vertex L n k 0 → ComplexMatrix2) = ((∑ ι, Ψs f ι * Ψs g ι : ℝ) : ℂ))
    (g : vertexFunctionSpace L n k 0) :
    ((traceFinsumNorm (g : Vertex L n k 0 → ComplexMatrix2) ^ 2 : ℝ) : ℂ) =
      toPauliCoeffs (g : Vertex L n k 0 → ComplexMatrix2) ⬝ᵥ
        toPauliCoeffs (g : Vertex L n k 0 → ComplexMatrix2) := by
  have e : (traceFinsumPairing (g : Vertex L n k 0 → ComplexMatrix2)
      (g : Vertex L n k 0 → ComplexMatrix2)).re = ∑ ι, Ψs g ι * Ψs g ι := by
    rw [hps, Complex.ofReal_re]
  have h0 : 0 ≤ ∑ ι, Ψs g ι * Ψs g ι := Finset.sum_nonneg fun ι _ => mul_self_nonneg _
  unfold traceFinsumNorm
  rw [e, Real.sq_sqrt h0]
  simp only [dotProduct, hΨs]
  push_cast
  rfl
private theorem dot_mulVec_self {J Q : Type} [Fintype J] [Fintype Q] (T : Matrix J Q ℂ)
    (w : Q → ℂ) : T.mulVec w ⬝ᵥ T.mulVec w = w ⬝ᵥ (T.transpose * T).mulVec w := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]
private theorem toPauliCoeffs_residual [DecidableEq (Fin 3 × Vertex L n k 0)]
    (Ψs : vertexFunctionSpace L n k 0 ≃ₗ[ℝ] (Fin 3 × Vertex L n k 0 → ℝ))
    (hΨs : ∀ (f : vertexFunctionSpace L n k 0) ι,
      toPauliCoeffs (f : Vertex L n k 0 → ComplexMatrix2) ι = ((Ψs f ι : ℝ) : ℂ))
    (d : vertexFunctionSpace L n k 0)
    (A : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k)
    (At : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0)
    (R : Matrix (Fin 3 × Vertex L n k k) (Fin 3 × Vertex L n k 0) ℂ) (c : ℝ)
    (hA : ∀ (l : vertexFunctionSpace L n k 0) y,
      toPauliCoeffs (A l : Vertex L n k k → ComplexMatrix2) y =
        ∑ x, R y x * toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2) x)
    (hAt : ∀ (g : vertexFunctionSpace L n k k) x,
      toPauliCoeffs (At g : Vertex L n k 0 → ComplexMatrix2) x =
        ∑ y, R y x * toPauliCoeffs (g : Vertex L n k k → ComplexMatrix2) y) :
    toPauliCoeffs ((d - c • At (A d) : vertexFunctionSpace L n k 0) :
        Vertex L n k 0 → ComplexMatrix2) =
      (1 + (-(c : ℂ)) • (R.transpose * R)).mulVec
        (toPauliCoeffs (d : Vertex L n k 0 → ComplexMatrix2)) := by
  funext x
  have e1 : toPauliCoeffs ((d - c • At (A d) : vertexFunctionSpace L n k 0) :
      Vertex L n k 0 → ComplexMatrix2) x =
      toPauliCoeffs (d : Vertex L n k 0 → ComplexMatrix2) x -
        (c : ℂ) * toPauliCoeffs (At (A d) : Vertex L n k 0 → ComplexMatrix2) x := by
    simp only [hΨs, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rfl
  rw [e1, hAt]
  simp only [hA]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  ring
end Real
theorem gaugeSliceResidualIsLocal (hA : MeanKernelsAreLocalNearCells)
    (hO : GaugeOrbitMapIsLocal)
    (hCl : LocallyHolomorphicFamiliesClosed)
    (hMaps : BackgroundGaugeMapsInColourCoeffs)
    (hCol : PauliCoordsOrthonormal)
    (hY : Tower.RealLinearMaps.RealLinearMapsStatement)
    (hQ : Tower.RealQuadraticTransposes.Statement)
    (hM : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    (hT : GroupLieProduct.HolomorphicOnTracelessIffDifferentiable) :
    GaugeSliceResidualIsLocal := by
  intro L hL k hk
  obtain ⟨ρA, CA, rA, hρA, hCA, hrA, hAk⟩ := hA L hL
  obtain ⟨ρO, CO, rO, hρO, hCO, hrO, hOk⟩ := hO L hL k hk
  obtain ⟨n₀, hn₀⟩ := hAk k hk
  have hLpos : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hη : 0 < finestMesh L k := by
    unfold finestMesh meshAt
    exact zpow_pos hLpos _
  have hu : unitNormScale L k ≠ 0 := by
    unfold unitNormScale
    exact_mod_cast (inv_pos.2 (pow_pos hη 2)).ne'
  set S : ℝ := (∑ a, ‖ComplexMatrix2.pauliFamily a‖) + 1 with hS
  have hSpos : 0 < S := by positivity
  set t : ℝ := ρA / 2 with ht
  have htρ : t < ρA := by rw [ht]; linarith
  have ht0 : 0 ≤ t := by positivity
  set ρ : ℝ := min ρO (t * finestMesh L k / S) with hρdef
  have hρpos : 0 < ρ := lt_min hρO (by positivity)
  set c : ℝ := (L : ℝ) ^ (4 * k) with hc
  set c' : ℂ := (c : ℂ) * ((unitNormScale L k)⁻¹) ^ 2 with hc'
  set CT : ℝ := (1 + ‖-c'‖ * (CA * CA)) * (CO * 1) with hCT
  set rT : ℝ := (2 * rA + rA) + (2 * rO + 0) with hrT
  refine ⟨ρ, CT * CT, 2 * rT + rT, hρpos, by positivity, by positivity, ?_⟩
  filter_upwards [hOk, eventually_ge_atTop n₀, eventually_gt_atTop 0] with n hOn hn₁ hn
  intro _ _ _ _ _ _ _ _ _ P
  have hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  let fa : Fintype (Fin 3 × PositiveEdge L n k 0) :=
    Fintype.ofInjective (Sum.inl : _ → LevelFormIndex L n k) Sum.inl_injective
  let fb : Fintype (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) :=
    Fintype.ofInjective (Sum.inr : _ → LevelFormIndex L n k) Sum.inr_injective
  let da : DecidableEq (Fin 3 × PositiveEdge L n k 0) := Classical.decEq _
  let dt : DecidableEq (Fin 3 × Vertex L n k k) := Classical.decEq _
  have closed := hCl L n k
  obtain ⟨D, hDr, hDx⟩ := hOn P
  have hR := (hn₀ n hn₁ hn).2.2.1
  have hfine : (fineIndexCell : Fin 3 × Vertex L n k 0 → Vertex L n k k) = colouredVertexCell :=
    funext fun p => levelVertexCell_eq p.2
  rw [hfine] at hDr
  have hbound : ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ b,
      ComplexMatrix2.operatorNorm (coordForm L n k w b) ≤ t := by
    intro w hw b
    have hw' : ‖w‖ ≤ t * finestMesh L k / S := by
      have : ‖w‖ < ρ := by simpa using hw
      exact this.le.trans (min_le_right _ _)
    show ‖coordForm L n k w b‖ ≤ t
    rw [coordForm_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h₁ := norm_complexFineValues_le hx w b
    have h₂ : (∑ a, ‖ComplexMatrix2.pauliFamily a‖) * ‖w‖ ≤ S * ‖w‖ :=
      mul_le_mul_of_nonneg_right (by rw [hS]; linarith) (norm_nonneg _)
    have h₃ : S * ‖w‖ ≤ t * finestMesh L k := by
      have := mul_le_mul_of_nonneg_left hw' hSpos.le
      rwa [mul_div_cancel₀ _ hSpos.ne'] at this
    calc (finestMesh L k)⁻¹ * ‖complexFineValues w b‖
        ≤ (finestMesh L k)⁻¹ * (t * finestMesh L k) :=
          mul_le_mul_of_nonneg_left (h₁.trans (h₂.trans h₃)) (by positivity)
      _ = t := by field_simp
  have Rf := isLocallyHolomorphic_comp_coordForm hM hT hx htρ ht0 hbound hR
  have Dm : IsLocallyHolomorphicFamily tripleCoordIndexCell colouredVertexCell levelFormIndexCell
      D ρ CO rO := closed.mono (min_le_left _ _) le_rfl le_rfl hDr
  have Rt := closed.transpose hrA Rf
  have RR := closed.mul (by positivity) hrA Rt Rf
  have W := closed.add
    (closed.one tripleCoordIndexCell colouredVertexCell ρ (2 * rA + rA) (by positivity))
    (closed.smul (-c') RR)
  have Dt := closed.transpose hrO Dm
  have Ef : IsLocallyHolomorphicFamily tripleCoordIndexCell levelFormIndexCell levelFormIndexCell
      (fun _ => Matrix.diagonal (baseWeights L n k)) ρ 1 0 := by
    refine ⟨fun _ _ => analyticOnNhd_const, fun _ _ => ?_, fun _ _ _ _ _ _ _ => rfl,
      fun w hw p q h => ?_⟩
    · rw [Matrix.l2_opNorm_diagonal]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun q => ?_
      rcases q with q | q <;> simp [baseWeights]
    · by_cases hpq : p = q
      · subst hpq
        have h₁ := (closed.one tripleCoordIndexCell levelFormIndexCell ρ 0 le_rfl).eq_zero_of_far
          w hw p p h
        simp at h₁
      · exact Matrix.diagonal_apply_ne _ hpq
  have DE := closed.mul (by positivity) le_rfl Dt Ef
  have Tm := closed.mul (by positivity) (by positivity) W DE
  have Tt := closed.transpose (by positivity) Tm
  have Gm := closed.mul (by positivity) (by positivity) Tt Tm
  refine ⟨_, Gm, ?_⟩
  have hU := tendsto_fine_pointOfCoords hx P
  filter_upwards [hDx, hU.eventually (hMaps L hL k n hk hn)] with x hD hm ξ
  obtain ⟨-, hA2, hA3, -⟩ := hm
  obtain ⟨Ψb, hΨb, hpb⟩ := (hCol L n k 0 hL hn (Nat.zero_le k)).1
  obtain ⟨Ψs, hΨs, hps⟩ := (hCol L n k 0 hL hn (Nat.zero_le k)).2
  have hUc : (pointOfCoords P x).fine ∈ fieldSpace L n k 0 := by
    rw [fine_pointOfCoords_eq]
    exact expTwist_one_mem_fieldSpace hx (tripleOfCoords P x).1.1.2
  have hUb := fine_pointOfCoords hx hη.ne' P x
  obtain ⟨U, hUdef⟩ : ∃ U, U = (pointOfCoords P x).fine := ⟨_, rfl⟩
  rw [← hUdef] at hA2 hA3 hUc hUb
  rw [← hUdef]
  obtain ⟨T', -, -, -, hadj⟩ := (hQ L n k hL hn hk).1 0 (Nat.zero_le k) _ hUc
  obtain ⟨T₀, hT₀⟩ := (hY L n k hL hn hk).2.covDiff_isLinear 0 (Nat.zero_le k) _ hUc
  have vD : ∀ l : vertexFunctionSpace L n k 0,
      (covDiffLinear L n k U l : Edge L n k 0 → ComplexMatrix2) =
        covDiff U (l : Vertex L n k 0 → ComplexMatrix2) :=
    Classical.epsilon_spec
      (p := fun T : vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 =>
        ∀ l : vertexFunctionSpace L n k 0, (T l : Edge L n k 0 → ComplexMatrix2) =
          covDiff U (l : Vertex L n k 0 → ComplexMatrix2)) ⟨T₀, hT₀⟩
  have hD' : ∀ l : vertexFunctionSpace L n k 0, ∃ η : LevelForms L n k,
      (η.1 : Edge L n k 0 → ComplexMatrix2) =
        (covDiffLinear L n k U l : Edge L n k 0 → ComplexMatrix2) ∧
      complexifyCoords (P.formCoords η) = (D (complexifyCoords x)).mulVec
        (toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2)) := by
    intro l
    obtain ⟨η, e₁, e₂⟩ := hD l
    refine ⟨η, ?_, ?_⟩
    · rw [vD, hUdef]
      exact congrArg Prod.fst e₁
    · rw [e₂]
      congr 1
      funext ι
      exact (P.ghostCoords_fst (l, 0) ι).symm
  have dual := toPauliCoeffs_adjoint Ψb hΨb hpb Ψs hΨs hps P (D (complexifyCoords x))
    (covDiffRealTranspose L n k U) (covDiffLinear L n k U)
    (fun x' l => hadj x' l) hD' ξ
  have htop : (rescaledOperators L n k U).coarse = 1 := by
    show meshAt L k k = 1
    simp [meshAt]
  have hA3' : ∀ (g : vertexFunctionSpace L n k k) y,
      toPauliCoeffs (iterAverageRealTranspose L n k U g : Vertex L n k 0 → ComplexMatrix2) y =
        ∑ w, (Matrix.of (rescaledOperators L n k U).R : Matrix _ _ ℂ) w y *
          toPauliCoeffs (g : Vertex L n k k → ComplexMatrix2) w := by
    intro g y
    rw [hA3]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hRt : (rescaledOperators L n k U).Rt y w =
        ((((rescaledOperators L n k U).coarse ^ 4 / (rescaledOperators L n k U).eta ^ 4 : ℝ)) : ℂ) *
          (rescaledOperators L n k U).R w y := rfl
    have he : (rescaledOperators L n k U).eta = finestMesh L k := rfl
    rw [hRt, htop, he]
    have hηC : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hη.ne'
    simp only [Matrix.of_apply]
    push_cast
    field_simp
  have term := toPauliCoeffs_residual Ψs hΨs (covDiffRealTranspose L n k U ξ.1)
    (iterAverageLinear L n k U) (iterAverageRealTranspose L n k U)
    (Matrix.of (rescaledOperators L n k U).R) c hA2 hA3'
  have eW : (1 + (-(c : ℂ)) • ((Matrix.of (rescaledOperators L n k U).R :
        Matrix (Fin 3 × Vertex L n k k) (Fin 3 × Vertex L n k 0) ℂ).transpose *
        Matrix.of (rescaledOperators L n k U).R)) =
      1 + (-c') • ((unitNormScale L k • (Matrix.of (rescaledOperators L n k U).R :
        Matrix (Fin 3 × Vertex L n k k) (Fin 3 × Vertex L n k 0) ℂ)).transpose *
        (unitNormScale L k • (Matrix.of (rescaledOperators L n k U).R :
          Matrix (Fin 3 × Vertex L n k k) (Fin 3 × Vertex L n k 0) ℂ))) := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    congr 2
    rw [hc']
    field_simp
  have key : toPauliCoeffs (gaugeSliceResidual U ξ.1 : Vertex L n k 0 → ComplexMatrix2) =
      ((1 + (-c') • ((unitNormScale L k • (Matrix.of (rescaledOperators L n k U).R :
        Matrix (Fin 3 × Vertex L n k k) (Fin 3 × Vertex L n k 0) ℂ)).transpose *
        (unitNormScale L k • (Matrix.of (rescaledOperators L n k U).R :
          Matrix (Fin 3 × Vertex L n k k) (Fin 3 × Vertex L n k 0) ℂ)))) *
        ((D (complexifyCoords x)).transpose * Matrix.diagonal (baseWeights L n k))).mulVec
        (complexifyCoords (P.formCoords ξ)) := by
    rw [← Matrix.mulVec_mulVec, ← dual, ← eW]
    exact term
  rw [sq_norm_eq_dot Ψs hΨs hps, key, dot_mulVec_self, hUb]
end YangMills.Construction.RunningCouplingSlope.GaugeSliceResidualLocal
end
