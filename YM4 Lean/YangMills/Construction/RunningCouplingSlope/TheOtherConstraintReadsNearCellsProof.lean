import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.AmbientSpaceOfTheRealPairsOnADomain
import YangMills.Construction.Lattice.NumberOfAStepWithTwoRegions
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.RunningCouplingSlope.FewIndicesLieNearACell
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheMovementsOfTheChainReadNearCells
import YangMills.Construction.RunningCouplingSlope.TheOtherConstraintReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TopBondsAndTheirBlocks
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.GaugeConstraintLocality
open Tower Matrices
section SchurTest
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
private theorem norm_le_sqrt_of_row_col_sums (A : Matrix α β ℂ) {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hrow : ∀ p, ∑ q, ‖A p q‖ ≤ R) (hcol : ∀ q, ∑ p, ‖A p q‖ ≤ S) :
    ‖A‖ ≤ Real.sqrt (R * S) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  set g : β → ℂ := WithLp.ofLp x with hg
  have e1 : ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := α) (n := β)).trans
      LinearMap.toContinuousLinearMap A) x = WithLp.toLp 2 (A.mulVec g) := by
    simp [Matrix.toLpLin_apply, hg]
  rw [e1]
  have nx : ‖x‖ = Real.sqrt (∑ q, ‖g q‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  have ny : ‖(WithLp.toLp 2 (A.mulVec g) : EuclideanSpace ℂ α)‖ =
      Real.sqrt (∑ p, ‖A.mulVec g p‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  rw [nx, ny, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have row : ∀ p, ‖A.mulVec g p‖ ^ 2 ≤ R * ∑ q, ‖A p q‖ * ‖g q‖ ^ 2 := by
    intro p
    have h1 : ‖A.mulVec g p‖ ≤ ∑ q, ‖A p q‖ * ‖g q‖ := by
      simp only [Matrix.mulVec, dotProduct]
      exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => norm_mul _ _))
    have h2 : (∑ q, ‖A p q‖ * ‖g q‖) ^ 2 ≤
        (∑ q, ‖A p q‖) * ∑ q, ‖A p q‖ * ‖g q‖ ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun q _ => norm_nonneg _)
        (fun q _ => by positivity) (fun q _ => le_of_eq (by ring))
    calc ‖A.mulVec g p‖ ^ 2 ≤ (∑ q, ‖A p q‖ * ‖g q‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ q, ‖A p q‖) * ∑ q, ‖A p q‖ * ‖g q‖ ^ 2 := h2
      _ ≤ R * ∑ q, ‖A p q‖ * ‖g q‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow p)
            (Finset.sum_nonneg fun q _ => by positivity)
  calc ∑ p, ‖A.mulVec g p‖ ^ 2 ≤ ∑ p, R * ∑ q, ‖A p q‖ * ‖g q‖ ^ 2 :=
        Finset.sum_le_sum fun p _ => row p
    _ = R * ∑ q, (∑ p, ‖A p q‖) * ‖g q‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ R * ∑ q, S * ‖g q‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_) hR
        exact mul_le_mul_of_nonneg_right (hcol q) (by positivity)
    _ = R * S * ∑ q, ‖g q‖ ^ 2 := by
        rw [← Finset.mul_sum, mul_assoc]
abbrev _root_.YangMills.SharedProofs.p34885 := @norm_le_sqrt_of_row_col_sums
end SchurTest
section AnalyticTools
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private theorem analyticAt_inv_of_det_ne_zero {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀)
    (hu : (f p₀).det ≠ 0) :
    AnalyticAt ℝ (fun y => (f y)⁻¹) p₀ := by apply _root_.YangMills.SharedProofs.p24898 <;> assumption
private theorem analyticAt_const_smul_matrix (c : ℂ) {f : E → ComplexMatrix2}
    (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => c • f p) p₀ := by apply _root_.YangMills.SharedProofs.p44577 <;> assumption
private theorem analyticAt_matExp_comp {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => ComplexMatrix2.matExp (f p)) p₀ :=
  AnalyticAt.comp (g := ComplexMatrix2.matExp) (NormedSpace.exp_analytic (𝕂 := ℝ) _) hf
end AnalyticTools
section LatticeTools
variable {L n k j : ℕ}
private theorem expTwist_of_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
private theorem expTwist_of_not_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
private theorem matExp_I_smul_mem_compact {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
private theorem mul_mem_compact {g g' : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hg' : g' ∈ PeriodicLattice.compactGaugeGroup) :
    g * g' ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
private theorem expTwist_mem_fieldSpace
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A U : Edge L n k j → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k j)
    (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.expTwist A U ∈ fieldSpace L n k j := by apply _root_.YangMills.SharedProofs.p8814 <;> assumption
end LatticeTools
section ChainFamilies
variable {L n k : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private structure LatticeFinitenessFacts (L n k : ℕ) : Prop where
  finite_edge : ∀ j, Finite (Edge L n k j)
  finite_vertex : ∀ j, Finite (Vertex L n k j)
  xor_opposite : ∀ j ≤ k, ∀ b : Edge L n k j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
private theorem latticeFinitenessFacts_of (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) : LatticeFinitenessFacts L n k := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have : NeZero L := ⟨by omega⟩
  have hb : ∀ j, Finite (Edge L n k j) := fun j => PeriodicLattice.instFiniteBond _
  have hs : ∀ j, Finite (Vertex L n k j) := fun j =>
    SeparatedSequences.BaseParameters.site_finite (by omega) n _
  exact ⟨hb, hs, fun j hj b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b⟩
private theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p5970 <;> assumption
private theorem isAnalyticFamily_expMove (F : LatticeFinitenessFacts L n k) {X : E → ChainPoint L n k}
    (hX : IsAnalyticFamilyThroughUnit X p₀) {g : E → LevelForms L n k} (hg₀ : g p₀ = 0)
    (hg₁ : ∀ b, AnalyticAt ℝ (fun p => ((g p).1 : Edge L n k 0 → ComplexMatrix2) b) p₀)
    (hg₂ : ∀ (i : Fin k) (c : Edge L n k (i + 1)),
      AnalyticAt ℝ (fun p => ((g p).2 i : Edge L n k (i + 1) → ComplexMatrix2) c) p₀) :
    IsAnalyticFamilyThroughUnit (fun p => expMove (g p) (X p)) p₀ := by
  have hval : ∀ b : Edge L n k 0, AnalyticAt ℝ (fun p => ComplexMatrix2.matExp
      (Complex.I • ((g p).1 : Edge L n k 0 → ComplexMatrix2) b) * (X p).fine b) p₀ := fun b =>
    (analyticAt_matExp_comp (analyticAt_const_smul_matrix _ (hg₁ b))).mul (hX.analyticAt_fine b)
  refine ⟨?_, fun b => ?_, fun i c => ?_, ?_⟩
  · show expMove (g p₀) (X p₀) = _
    rw [hg₀, hX.eq_unit, expMove_zero_unitPoint]
  · by_cases hb : b.IsPositivelyOriented
    · exact (hval b).congr (Eventually.of_forall fun p => (expTwist_of_pos hb).symm)
    · refine (analyticAt_inv_of_det_ne_zero (hval b.opposite) ?_).congr
        (Eventually.of_forall fun p => (expTwist_of_not_pos hb).symm)
      have h1 : ((g p₀).1 : Edge L n k 0 → ComplexMatrix2) b.opposite = 0 := by
        rw [hg₀]
        rfl
      have h2 : (X p₀).fine b.opposite = 1 := by
        rw [hX.eq_unit]
        rfl
      simp [h1, h2, ComplexMatrix2.matExp, NormedSpace.exp_zero]
  · exact (analyticAt_matExp_comp (analyticAt_const_smul_matrix _ (hg₂ i c.1))).mul
      (hX.analyticAt_noise i c)
  · filter_upwards [hX.eventually_compact] with p h
    exact ⟨expTwist_mem_fieldSpace (F.xor_opposite 0 (Nat.zero_le k)) (g p).1.2 h.1, fun i c =>
      mul_mem_compact (matExp_I_smul_mem_compact (((g p).2 i).2.1 c.1 c.2)) (h.2 i c)⟩
private theorem isAnalyticFamily_const_unit (_F : LatticeFinitenessFacts L n k) (p₀ : E) :
    IsAnalyticFamilyThroughUnit (fun _ : E => unitPoint L n k) p₀ := by
  refine ⟨rfl, fun _ => analyticAt_const, fun _ _ => analyticAt_const, ?_⟩
  refine Eventually.of_forall fun _ => ⟨⟨fun b _ => ?_, fun b _ => ?_⟩, fun _ _ => ?_⟩
  · exact Submonoid.one_mem _
  · simp [unitPoint]
  · exact Submonoid.one_mem _
private theorem isAnalyticFamily_expMove_linear (F : LatticeFinitenessFacts L n k)
    [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] LevelForms L n k) {X : E → ChainPoint L n k}
    (hX : IsAnalyticFamilyThroughUnit X 0) :
    IsAnalyticFamilyThroughUnit (fun p => expMove (A p) (X p)) 0 := by
  refine isAnalyticFamily_expMove F hX (map_zero A) (fun b => ?_) fun i c => ?_
  · let T : LevelForms L n k →ₗ[ℝ] ComplexMatrix2 :=
      { toFun := fun ξ => (ξ.1 : Edge L n k 0 → ComplexMatrix2) b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap (T ∘ₗ A)).analyticAt _
  · let T : LevelForms L n k →ₗ[ℝ] ComplexMatrix2 :=
      { toFun := fun ξ => (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap (T ∘ₗ A)).analyticAt _
private theorem isAnalyticFamily_pointOfCoords [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)] [Fintype (GhostCoordIndex L n k)]
    [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
    (F : LatticeFinitenessFacts L n k)
    (P : PauliCoordinates L n k) : IsAnalyticFamilyThroughUnit (pointOfCoords P) 0 := by
  have h := isAnalyticFamily_expMove_linear F (P.formCoords.symm.toLinearMap ∘ₗ
    (LinearMap.funLeft ℝ ℝ (Sum.inl : LevelFormIndex L n k → TripleCoordIndex L n k)))
    (isAnalyticFamily_const_unit F 0)
  have e : pointOfCoords P = fun x => expMove ((P.formCoords.symm.toLinearMap ∘ₗ
      (LinearMap.funLeft ℝ ℝ (Sum.inl : LevelFormIndex L n k → TripleCoordIndex L n k))) x)
      (unitPoint L n k) := by
    funext x
    rfl
  rw [e]
  exact h
end ChainFamilies
section Entries
variable {L n k : ℕ}
private theorem exists_clm_eq_pauliCoeff (a : Fin 3) :
    ∃ T : ComplexMatrix2 →L[ℂ] ℂ, ∀ X ∈ ComplexMatrix2.traceless, T X = pauliCoeff a X := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.exists_clm_pauliCoeff <;> assumption
private def adjugateCLM : ComplexMatrix2 →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.adjugate
      map_add' := fun X Y => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring
      map_smul' := fun c X => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] }
private lemma conjugateBy_eq_of_det_eq_one {W : ComplexMatrix2} (h : W.det = 1) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy W A = W * A * adjugateCLM W := by
  have e : W⁻¹ = Matrix.adjugate W := by simp [Matrix.inv_def, h]
  simp [ComplexMatrix2.conjugateBy, e, adjugateCLM]
private lemma isLocallyHolomorphicNear_conj_combination {I : Type} [Fintype I]
    {e : I → Vertex L n k k} {y : Vertex L n k k}
    {ρ C K R : ℝ} {Y W D D' : (I → ℂ) → ComplexMatrix2} (T : ComplexMatrix2 →L[ℂ] ℂ)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hY : IsLocallyHolomorphicNear e y Y ρ C R) (hD : IsLocallyHolomorphicNear e y D ρ C R)
    (hD' : IsLocallyHolomorphicNear e y D' ρ C R) (hW : IsLocallyHolomorphicNear e y W ρ K R)
    (hdet : ∀ w ∈ Metric.ball (0 : I → ℂ) ρ, (W w).det = 1) :
    IsLocallyHolomorphicNear e y
      (fun w => T (Y w + (ComplexMatrix2.conjugateBy (W w) (D' w) - D w))) ρ
      (‖T‖ * (C + (K * C * (‖adjugateCLM‖ * K) + C))) R := by
  have hval : ∀ w ∈ Metric.ball (0 : I → ℂ) ρ,
      T (Y w + (ComplexMatrix2.conjugateBy (W w) (D' w) - D w)) =
      T (Y w + (W w * D' w * adjugateCLM (W w) - D w)) := fun w hw => by
    rw [conjugateBy_eq_of_det_eq_one (hdet w hw)]
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw w' hw' h => ?_⟩
  · have hb : AnalyticAt ℂ (fun w => T (Y w + (W w * D' w * adjugateCLM (W w) - D w))) w := by
      have h₁ := hY.holomorphic w hw
      have h₂ := hW.holomorphic w hw
      have h₃ := hD'.holomorphic w hw
      have h₄ := hD.holomorphic w hw
      have h₅ : AnalyticAt ℂ (fun w => adjugateCLM (W w)) w :=
        (adjugateCLM.analyticAt _).comp h₂
      exact (T.analyticAt _).comp (h₁.add (((h₂.mul h₃).mul h₅).sub h₄))
    refine hb.congr ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
    exact (hval v hv).symm
  · rw [hval w hw]
    refine (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have h₁ := hY.norm_le w hw
    have h₂ := hW.norm_le w hw
    have h₃ := hD'.norm_le w hw
    have h₄ := hD.norm_le w hw
    have h₅ : ‖adjugateCLM (W w)‖ ≤ ‖adjugateCLM‖ * K :=
      (adjugateCLM.le_opNorm _).trans (mul_le_mul_of_nonneg_left h₂ (norm_nonneg _))
    have h₆ : ‖W w * D' w‖ ≤ K * C :=
      (norm_mul_le _ _).trans (mul_le_mul h₂ h₃ (norm_nonneg _) hK)
    have h₇ : ‖W w * D' w * adjugateCLM (W w)‖ ≤ K * C * (‖adjugateCLM‖ * K) :=
      (norm_mul_le _ _).trans (mul_le_mul h₆ h₅ (norm_nonneg _) (by positivity))
    calc ‖Y w + (W w * D' w * adjugateCLM (W w) - D w)‖
        ≤ ‖Y w‖ + ‖W w * D' w * adjugateCLM (W w) - D w‖ := norm_add_le _ _
      _ ≤ ‖Y w‖ + (‖W w * D' w * adjugateCLM (W w)‖ + ‖D w‖) := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by gcongr
  · simp only [hY.depends_near w hw w' hw' h, hW.depends_near w hw w' hw' h,
      hD.depends_near w hw w' hw' h, hD'.depends_near w hw w' hw' h]
private lemma sum_le_of_supported_card_le {ι : Type} [Fintype ι] {f : ι → ℝ} {S : ι → Prop}
    {B : ℝ} {N : ℕ}
    (hB : 0 ≤ B) (h0 : ∀ q, ¬ S q → f q = 0) (h1 : ∀ q, f q ≤ B)
    (hN : Nat.card {q // S q} ≤ N) : ∑ q, f q ≤ B * N := by
  classical
  have e : ∑ q, f q = ∑ q ∈ Finset.univ.filter S, f q := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun q _ hq => ?_).symm
    exact h0 q fun hs => hq (by simp [hs])
  have hc : (Finset.univ.filter S).card ≤ N := by
    have : (Finset.univ.filter S).card = Nat.card {q // S q} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    omega
  rw [e]
  calc ∑ q ∈ Finset.univ.filter S, f q ≤ ∑ _q ∈ Finset.univ.filter S, B :=
        Finset.sum_le_sum fun q _ => h1 q
    _ = (Finset.univ.filter S).card * B := by simp
    _ ≤ N * B := by gcongr
    _ = B * N := mul_comm _ _
private lemma levelVertexCell_self (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k)
    (hc : NeighbouringFineVertexCells) (ht : TopEdgesAndCubes)
    (y : Vertex L n k k) : levelVertexCell y = y := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  set x : Vertex L n k 0 := y.toSublattice (PeriodicLattice.levelDepth k 0) with hx
  have hcoe : (x : PeriodicLattice.FourTorus L n) = y := by
    have hd : PeriodicLattice.levelDepth k k ≤ PeriodicLattice.levelDepth k 0 := by
      simp [PeriodicLattice.levelDepth]
    have h : ∃ x : Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) = y :=
      ⟨⟨y, PeriodicLattice.sublattice_mono hLp n hd y.2⟩, rfl⟩
    exact Classical.epsilon_spec h
  have hb : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y := by
    refine ⟨?_, ?_⟩
    · rw [hcoe]
      exact PeriodicLattice.site_mem_cubeAround y
    · have := x.2
      simpa [PeriodicLattice.levelDepth] using this
  exact (ht L hL n k hn hk).2.2 _ _ _ ((hc L hL n k).2.2.1 x) hb
abbrev _root_.YangMills.SharedProofs.p53151 := @levelVertexCell_self
end Entries
theorem gaugeConstraintMatrixIsLocal_holds (hF : LevelFieldsHolomorphicAndLocal)
    (hM : BasisTransportAndDriftAreLocal)
    (hN : FewIndicesNearCell) (hMaps : AnalyticFamilyTransportAndGauge)
    (hC : NeighbouringFineVertexCells) (hT : TopEdgesAndCubes) :
    GaugeConstraintMatrixIsLocal := by
  intro L hL k hk
  obtain ⟨ρ₁, C₁, r₁, hρ₁, hC₁, hr₁, F⟩ := hF L hL k hk
  obtain ⟨ρ₂, C₂, r₂, hρ₂, hC₂, hr₂, M⟩ := hM L hL k hk
  obtain ⟨N, hNn⟩ := hN L hL k hk (r₁ + r₂ + 2)
  choose T hTp using exists_clm_eq_pauliCoeff
  set ρ := min ρ₁ ρ₂ with hρ
  have hρpos : 0 < ρ := lt_min hρ₁ hρ₂
  set R := r₁ + r₂ + 2 with hR
  have hRpos : 0 ≤ R := by positivity
  set K := ‖(1 : ComplexMatrix2)‖ + C₁ * ρ with hKdef
  have hK : 0 ≤ K := by positivity
  set B₀ := C₂ + (K * C₂ * (‖adjugateCLM‖ * K) + C₂) with hB₀
  have hB₀p : 0 ≤ B₀ := by positivity
  set B := (∑ a, ‖T a‖) * B₀ with hB
  have hBp : 0 ≤ B := by positivity
  refine ⟨ρ, B * N, R, hρpos, by positivity, hRpos, ?_⟩
  filter_upwards [F, M, hNn, eventually_gt_atTop 0] with n F M Nn hn
  intro _ _ _ _ _ _ _ _ _ P
  obtain ⟨hreal, hconf, hW, -⟩ := F P
  have hcell := hC L hL n k
  obtain ⟨sym, tri, -, -⟩ := hcell
  have htop := hT L hL n k hn hk
  have ball₁ : ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
      z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ₁ := fun z hz =>
    Metric.ball_subset_ball (min_le_left _ _) hz
  have ball₂ : ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
      z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ₂ := fun z hz =>
    Metric.ball_subset_ball (min_le_right _ _) hz
  have ballN : ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, ‖z‖ < ρ := fun z hz => by
    simpa using hz
  have target_near : ∀ b : Edge L n k k,
      cellDist (levelVertexCell b.source) (levelVertexCell b.target) ≤ 2 := fun b => by
    rw [levelVertexCell_self hL hn hk hC hT, levelVertexCell_self hL hn hk hC hT]
    exact htop.2.1 b
  have field : ∀ b : Edge L n k k,
      IsLocallyHolomorphicNear tripleCoordIndexCell (levelVertexCell b.source)
        (fun z => levelField (complexChainPoint z) k b) ρ K R := by
    intro b
    obtain ⟨a₁, a₂, a₃⟩ := hW k le_rfl b
    refine ⟨fun z hz => a₁ z (ball₁ z hz), fun z hz => ?_, fun z hz z' hz' h =>
      a₃ z (ball₁ z hz) z' (ball₁ z' hz') fun i hi => h i (by linarith)⟩
    have h₁ := a₂ z (ball₁ z hz)
    have h₂ : ‖levelField (complexChainPoint z) k b - 1‖ ≤ C₁ * ρ :=
      h₁.trans (mul_le_mul_of_nonneg_left (ballN z hz).le hC₁)
    calc ‖levelField (complexChainPoint z) k b‖
        = ‖(levelField (complexChainPoint z) k b - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖levelField (complexChainPoint z) k b - 1‖ + ‖(1 : ComplexMatrix2)‖ := norm_add_le _ _
      _ ≤ K := by rw [hKdef]; linarith
  have det_one : ∀ (b : Edge L n k k), ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
      (levelField (complexChainPoint z) k b).det = 1 := fun b z hz =>
    (show PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup Set.univ _ from
      hconf k le_rfl z (ball₁ z hz)).1 b (Set.mem_univ b)
  have value : ∀ (q : LevelFormIndex L n k) (b : PositiveEdge L n k k) (z),
      shiftedGaugeValues (complexChainPoint z) (coordBasisForm P q) b.1 =
        tangentTransport (complexChainPoint z) (coordBasisForm P q) k b.1 +
          (ComplexMatrix2.conjugateBy (levelField (complexChainPoint z) k b.1)
              (chainDrift (complexChainPoint z) (coordBasisForm P q) k b.1.target) -
            chainDrift (complexChainPoint z) (coordBasisForm P q) k b.1.source) := by
    intro q b z
    simp [shiftedGaugeValues, covDiff, extendOddly, b.2]
  have entry : ∀ (p : Fin 3 × PositiveEdge L n k k) (q : LevelFormIndex L n k),
      IsLocallyHolomorphicNear tripleCoordIndexCell (topIndexCell p)
        (fun z => T p.1 (shiftedGaugeValues (complexChainPoint z) (coordBasisForm P q) p.2.1))
        ρ B R := by
    intro p q
    have e₁ := ((M P q).1 k le_rfl p.2.1).1
    have e₂ := ((M P q).2 k le_rfl p.2.1.source).1
    have e₃ := ((M P q).2 k le_rfl p.2.1.target).1
    have sh : ∀ {f : (TripleCoordIndex L n k → ℂ) → ComplexMatrix2},
        IsLocallyHolomorphicNear tripleCoordIndexCell (levelVertexCell p.2.1.source) f ρ₂ C₂ r₂ →
        IsLocallyHolomorphicNear tripleCoordIndexCell (levelVertexCell p.2.1.source) f ρ C₂ R :=
      fun h =>
      ⟨fun z hz => h.holomorphic z (ball₂ z hz), fun z hz => h.norm_le z (ball₂ z hz),
        fun z hz z' hz' hh => h.depends_near z (ball₂ z hz) z' (ball₂ z' hz') fun i hi =>
          hh i (by linarith)⟩
    have e₃' : IsLocallyHolomorphicNear tripleCoordIndexCell (levelVertexCell p.2.1.source)
        (fun z => chainDrift (complexChainPoint z) (coordBasisForm P q) k p.2.1.target)
        ρ C₂ R := by
      refine ⟨fun z hz => e₃.holomorphic z (ball₂ z hz), fun z hz => e₃.norm_le z (ball₂ z hz),
        fun z hz z' hz' hh => e₃.depends_near z (ball₂ z hz) z' (ball₂ z' hz') fun i hi =>
          hh i ?_⟩
      have h₁ := tri (tripleCoordIndexCell i) (levelVertexCell p.2.1.target)
        (levelVertexCell p.2.1.source)
      have h₂ := target_near p.2.1
      rw [sym] at h₂
      linarith
    have h := isLocallyHolomorphicNear_conj_combination (T p.1) hC₂ hK (sh e₁) (sh e₂) e₃'
      (field p.2.1) (det_one p.2.1)
    refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz z' hz' hh => ?_⟩
    · simpa only [value q p.2] using h.holomorphic z hz
    · simp only [value q p.2]
      refine (h.norm_le z hz).trans ?_
      rw [hB]
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun a => ‖T a‖) (fun a _ => norm_nonneg _)
          (Finset.mem_univ p.1)) hB₀p
    · simp only [value q p.2]
      exact h.depends_near z hz z' hz' hh
  have far : ∀ (p : Fin 3 × PositiveEdge L n k k) (q : LevelFormIndex L n k),
      R < cellDist (topIndexCell p) (levelFormIndexCell q) →
      ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
        T p.1 (shiftedGaugeValues (complexChainPoint z) (coordBasisForm P q) p.2.1) = 0 := by
    intro p q hpq z hz
    have hpq' : R < cellDist (levelVertexCell p.2.1.source) (levelFormIndexCell q) := hpq
    have z₁ := ((M P q).1 k le_rfl p.2.1).2 (by linarith) z (ball₂ z hz)
    have z₂ := ((M P q).2 k le_rfl p.2.1.source).2 (by linarith) z (ball₂ z hz)
    have z₃ : chainDrift (complexChainPoint z) (coordBasisForm P q) k p.2.1.target = 0 := by
      refine ((M P q).2 k le_rfl p.2.1.target).2 ?_ z (ball₂ z hz)
      have h₁ := tri (levelVertexCell p.2.1.source) (levelVertexCell p.2.1.target)
        (levelFormIndexCell q)
      have h₂ := target_near p.2.1
      linarith
    rw [value q p.2, z₁, z₂, z₃]
    simp [ComplexMatrix2.conjugateBy]
  refine ⟨fun z => Matrix.of fun p q =>
    T p.1 (shiftedGaugeValues (complexChainPoint z) (coordBasisForm P q) p.2.1),
      ⟨fun p q => ?_, fun z hz => ?_, fun p q z hz z' hz' h => ?_, fun z hz p q h => ?_⟩, ?_⟩
  · exact (entry p q).holomorphic
  · have hs : ‖Matrix.of (fun (p : Fin 3 × PositiveEdge L n k k) (q : LevelFormIndex L n k) =>
        T p.1 (shiftedGaugeValues (complexChainPoint z) (coordBasisForm P q) p.2.1))‖ ≤
        Real.sqrt ((B * N) * (B * N)) := by
      refine norm_le_sqrt_of_row_col_sums _ (by positivity) (by positivity) (fun p => ?_)
        fun q => ?_
      · refine sum_le_of_supported_card_le
          (S := fun q => cellDist (topIndexCell p) (levelFormIndexCell q) ≤ R)
          hBp (fun q hq => ?_) (fun q => (entry p q).norm_le z hz) (Nn _).1
        rw [Matrix.of_apply, far p q (not_le.1 hq) z hz, norm_zero]
      · refine sum_le_of_supported_card_le
          (S := fun p => cellDist (levelFormIndexCell q) (topIndexCell p) ≤ R)
          hBp (fun p hp => ?_) (fun p => (entry p q).norm_le z hz) (Nn _).2
        have hp' := not_le.1 hp
        rw [sym] at hp'
        rw [Matrix.of_apply, far p q hp' z hz, norm_zero]
    rwa [Real.sqrt_mul_self (by positivity)] at hs
  · exact (entry p q).depends_near z hz z' hz' h
  · exact far p q h z hz
  · have fam := isAnalyticFamily_pointOfCoords (latticeFinitenessFacts_of hL hn) P
    have maps := (hMaps L hL k n hk hn _ _ _ fam).2
    filter_upwards [maps] with x hx
    ext p q
    set τ := tripleOfCoords P x with hτ
    set X := pointOfCoords P x with hX
    have hXm : expMove τ.1 (unitPoint L n k) = X := rfl
    have hcp : complexChainPoint (complexifyCoords x) = X := hreal x
    have hval := hx.1 (coordBasisForm P q)
    set μ := shiftedGaugeMap X (coordBasisForm P q) with hμ
    have e₁ : gaugeConstraintMatrix P τ p q = ((P.topFormCoords μ p : ℝ) : ℂ) := by
      unfold gaugeConstraintMatrix complexMatrixOfLinearMap
      rw [hXm, Matrix.map_apply, LinearMap.toMatrix'_apply]
      rfl
    have e₂ := P.topFormCoords_apply μ p
    have hmem : (μ : Edge L n k k → ComplexMatrix2) p.2.1 ∈ ComplexMatrix2.traceless :=
      (μ.2.1 p.2.1 p.2.2).2
    rw [e₁, ← e₂, Matrix.of_apply, hcp, ← hval, hTp _ _ hmem]
    rfl
end YangMills.Construction.RunningCouplingSlope.GaugeConstraintLocality
end
