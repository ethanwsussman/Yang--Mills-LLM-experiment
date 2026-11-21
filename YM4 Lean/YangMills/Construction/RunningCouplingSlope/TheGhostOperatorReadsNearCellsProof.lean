import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreClosed
import YangMills.Construction.RunningCouplingSlope.FieldsOfAFamilyThroughOne
import YangMills.Construction.RunningCouplingSlope.MapsOfTheBackgroundGaugeInColours
import YangMills.Construction.RunningCouplingSlope.TheAverageOfTheChainReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheGhostOperatorReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheLaplacianOfTheFineLatticeReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheTransposeOfTheAverageReadsNearCells
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter Tower Matrices
open scoped Topology Matrix.Norms.L2Operator
namespace RunningCouplingSlope.GhostOperatorLocality
section Analysis
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private theorem analyticAt_inv_of_det_ne_zero {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀)
    (hdet : (f p₀).det ≠ 0) :
    AnalyticAt ℝ (fun y => (f y)⁻¹) p₀ := by apply _root_.YangMills.SharedProofs.p24898 <;> assumption
private theorem analyticAt_const_smul (c : ℂ) {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => c • f p) p₀ := by apply _root_.YangMills.SharedProofs.p44577 <;> assumption
private theorem analyticAt_matExp {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => ComplexMatrix2.matExp (f p)) p₀ :=
  AnalyticAt.comp (g := ComplexMatrix2.matExp) (NormedSpace.exp_analytic (𝕂 := ℝ) _) hf
end Analysis
section Points
variable {L n k m : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem expTwist_of_pos {A U : Edge L n k m → ComplexMatrix2} {b : Edge L n k m}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
private theorem expTwist_of_not_pos {A U : Edge L n k m → ComplexMatrix2} {b : Edge L n k m}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
private theorem matExp_I_smul_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
private theorem mul_mem_compact {g g' : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hg' : g' ∈ PeriodicLattice.compactGaugeGroup) : g * g' ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
private theorem expTwist_mem_fieldSpace
    (hx : ∀ b : Edge L n k m, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A U : Edge L n k m → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k m)
    (hU : U ∈ fieldSpace L n k m) :
    PeriodicLattice.expTwist A U ∈ fieldSpace L n k m := by apply _root_.YangMills.SharedProofs.p8814 <;> assumption
private theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p5970 <;> assumption
private theorem isAnalyticFamilyThroughUnit_of_linear
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] LevelForms L n k) :
    IsAnalyticFamilyThroughUnit (fun p => expMove (A p) (unitPoint L n k)) 0 := by
  have h₁ : ∀ b : Edge L n k 0,
      AnalyticAt ℝ (fun p => ((A p).1 : Edge L n k 0 → ComplexMatrix2) b) 0 := by
    intro b
    let T : LevelForms L n k →ₗ[ℝ] ComplexMatrix2 :=
      { toFun := fun ξ => (ξ.1 : Edge L n k 0 → ComplexMatrix2) b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap (T ∘ₗ A)).analyticAt _
  have h₂ : ∀ (i : Fin k) (c : Edge L n k (i + 1)),
      AnalyticAt ℝ (fun p => ((A p).2 i : Edge L n k (i + 1) → ComplexMatrix2) c) 0 := by
    intro i c
    let T : LevelForms L n k →ₗ[ℝ] ComplexMatrix2 :=
      { toFun := fun ξ => (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap (T ∘ₗ A)).analyticAt _
  have hval : ∀ b : Edge L n k 0, AnalyticAt ℝ (fun p => ComplexMatrix2.matExp
      (Complex.I • ((A p).1 : Edge L n k 0 → ComplexMatrix2) b) * (unitPoint L n k).fine b) 0 :=
    fun b => (analyticAt_matExp (analyticAt_const_smul _ (h₁ b))).mul analyticAt_const
  have hunit : (unitPoint L n k).fine ∈ fieldSpace L n k 0 := by
    refine ⟨fun b _ => Submonoid.one_mem _, fun b _ => ?_⟩
    simp [unitPoint]
  refine ⟨?_, fun b => ?_, fun i c => ?_, ?_⟩
  · show expMove (A 0) (unitPoint L n k) = _
    rw [map_zero, expMove_zero_unitPoint]
  · by_cases hb : b.IsPositivelyOriented
    · exact (hval b).congr (Eventually.of_forall fun p => (expTwist_of_pos hb).symm)
    · refine (analyticAt_inv_of_det_ne_zero (hval b.opposite) ?_).congr
        (Eventually.of_forall fun p => (expTwist_of_not_pos hb).symm)
      have h4 : (unitPoint L n k).fine b.opposite = 1 := rfl
      simp [h4, ComplexMatrix2.matExp, NormedSpace.exp_zero]
  · exact (analyticAt_matExp (analyticAt_const_smul _ (h₂ i c.1))).mul analyticAt_const
  · refine Eventually.of_forall fun p =>
      ⟨expTwist_mem_fieldSpace hx (A p).1.2 hunit, fun i c => ?_⟩
    exact mul_mem_compact (matExp_I_smul_mem (((A p).2 i).2.1 c.1 c.2)) (Submonoid.one_mem _)
end Points
section Entries
variable {L n k : ℕ}
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem ofPauliCoeffs_toPauliCoeffs {σ : Type} {l : σ → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    ofPauliCoeffs (toPauliCoeffs l) = l := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
private theorem sum_mul_single_comp {J K : Type} [Fintype J] [DecidableEq K] {φ : J → K}
    (hφ : Function.Injective φ) (f : J → ℂ) (q : J) :
    ∑ x, f x * (((Pi.single (φ q) (1 : ℝ) : K → ℝ) (φ x) : ℝ) : ℂ) = f q := by
  rw [Finset.sum_eq_single q]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (fun h => hb (hφ h))]
  · simp
private theorem sum_mul_single_of_ne {J K : Type} [Fintype J] [DecidableEq K] {φ : J → K} {κ : K}
    (h : ∀ x, φ x ≠ κ) (f : J → ℂ) :
    ∑ x, f x * (((Pi.single κ (1 : ℝ) : K → ℝ) (φ x) : ℝ) : ℂ) = 0 :=
  Finset.sum_eq_zero fun x _ => by simp [Pi.single_eq_of_ne (h x)]
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
  [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)]
private theorem ghostBlockOperator_matrix_eq (P : PauliCoordinates L n k) (X : ChainPoint L n k)
    (fRt : ∀ (g : vertexFunctionSpace L n k k) x,
      toPauliCoeffs (iterAverageRealTranspose L n k X.fine g : Vertex L n k 0 → ComplexMatrix2) x =
        ∑ y, ((finestMesh L k ^ 4 : ℝ) : ℂ) * (rescaledOperators L n k X.fine).Rt x y *
          toPauliCoeffs (g : Vertex L n k k → ComplexMatrix2) y)
    (fD : ∀ (l : vertexFunctionSpace L n k 0) x,
      toPauliCoeffs (covDiffRealTranspose L n k X.fine
          (covDiffLinear L n k X.fine l) : Vertex L n k 0 → ComplexMatrix2) x =
        ∑ x', ((finestMesh L k ^ 2 : ℝ) : ℂ) * (rescaledOperators L n k X.fine).Delta x x' *
          toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2) x')
    (hS : ∀ l : vertexFunctionSpace L n k 0,
      (composedCubeAverageLinear X l : Vertex L n k k → ComplexMatrix2) =
        composedCubeAverage X k (l : Vertex L n k 0 → ComplexMatrix2)) :
    complexMatrixOfLinearMap P.ghostCoords P.ghostCoords (ghostBlockOperator X) =
      Matrix.fromBlocks
        (((finestMesh L k ^ 2 : ℝ) : ℂ) • Matrix.of (rescaledOperators L n k X.fine).Delta)
        (((finestMesh L k ^ 4 : ℝ) : ℂ) • Matrix.of (rescaledOperators L n k X.fine).Rt)
        (Matrix.of fun p q => toPauliCoeffs (composedCubeAverage X k
          (ofPauliCoeffs (UnitGaugeDirections.basisFunction q))) p) 0 := by
  have hsl : ∀ (l : vertexFunctionSpace L n k 0) x,
      (l : Vertex L n k 0 → ComplexMatrix2) x ∈ ComplexMatrix2.traceless := fun l x =>
    (l.2 x (Set.mem_univ x)).2
  have add0 : ∀ (a b : vertexFunctionSpace L n k 0) ι,
      toPauliCoeffs ((a + b : vertexFunctionSpace L n k 0) : Vertex L n k 0 → ComplexMatrix2) ι =
        toPauliCoeffs (a : Vertex L n k 0 → ComplexMatrix2) ι +
          toPauliCoeffs (b : Vertex L n k 0 → ComplexMatrix2) ι := by
    intro a b ι
    have e : ((a + b, 0) : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k) =
        (a, 0) + (b, 0) := by simp
    have h1 := P.ghostCoords_fst (a + b, 0) ι
    have h2 := P.ghostCoords_fst (a, 0) ι
    have h3 := P.ghostCoords_fst (b, 0) ι
    simp only at h1 h2 h3
    rw [h1, h2, h3, e, map_add, Pi.add_apply, Complex.ofReal_add]
  ext row col
  have entry : complexMatrixOfLinearMap P.ghostCoords P.ghostCoords (ghostBlockOperator X) row col =
      ((P.ghostCoords (ghostBlockOperator X (P.ghostCoords.symm (Pi.single col 1))) row : ℝ) : ℂ) := by
    simp [complexMatrixOfLinearMap, LinearMap.toMatrix'_apply]
  rw [entry]
  set w := P.ghostCoords.symm (Pi.single col 1) with hw
  have hc : ∀ κ, P.ghostCoords w κ = (Pi.single col (1 : ℝ) : GhostCoordIndex L n k → ℝ) κ := by
    intro κ
    simp [hw]
  have c₁ : ∀ ι, toPauliCoeffs (w.1 : Vertex L n k 0 → ComplexMatrix2) ι =
      (((Pi.single col (1 : ℝ) : GhostCoordIndex L n k → ℝ) (.inl ι) : ℝ) : ℂ) := fun ι => by
    rw [P.ghostCoords_fst, hc]
  have c₂ : ∀ ι, toPauliCoeffs (w.2 : Vertex L n k k → ComplexMatrix2) ι =
      (((Pi.single col (1 : ℝ) : GhostCoordIndex L n k → ℝ) (.inr ι) : ℝ) : ℂ) := fun ι => by
    rw [P.ghostCoords_snd, hc]
  rcases row with x | y
  · rw [← P.ghostCoords_fst (ghostBlockOperator X w) x]
    have e : (ghostBlockOperator X w).1 =
        covDiffRealTranspose L n k X.fine (covDiffLinear L n k X.fine w.1) +
          iterAverageRealTranspose L n k X.fine w.2 := rfl
    rw [e, add0, fD w.1 x, fRt w.2 x]
    simp only [c₁, c₂]
    rcases col with q | q
    · rw [sum_mul_single_comp Sum.inl_injective
        (fun x' => ((finestMesh L k ^ 2 : ℝ) : ℂ) * (rescaledOperators L n k X.fine).Delta x x'),
        sum_mul_single_of_ne (fun y => Sum.inr_ne_inl)
        (fun y => ((finestMesh L k ^ 4 : ℝ) : ℂ) * (rescaledOperators L n k X.fine).Rt x y), add_zero]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    · rw [sum_mul_single_of_ne (fun x' => Sum.inl_ne_inr)
        (fun x' => ((finestMesh L k ^ 2 : ℝ) : ℂ) * (rescaledOperators L n k X.fine).Delta x x'),
        sum_mul_single_comp Sum.inr_injective
        (fun y => ((finestMesh L k ^ 4 : ℝ) : ℂ) * (rescaledOperators L n k X.fine).Rt x y), zero_add]
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  · rw [← P.ghostCoords_snd (ghostBlockOperator X w) y]
    have e : (ghostBlockOperator X w).2 = composedCubeAverageLinear X w.1 := rfl
    rw [e]
    rcases col with q | q
    · rw [hS w.1]
      have h1 : (w.1 : Vertex L n k 0 → ComplexMatrix2) =
          ofPauliCoeffs (UnitGaugeDirections.basisFunction q) := by
        rw [← ofPauliCoeffs_toPauliCoeffs (hsl w.1)]
        congr 1
        funext ι
        rw [c₁]
        by_cases h : ι = q
        · subst h
          simp [UnitGaugeDirections.basisFunction]
        · simp [UnitGaugeDirections.basisFunction, h]
      rw [h1]
      rfl
    · have h1 : w.1 = 0 := by
        apply Subtype.ext
        rw [← ofPauliCoeffs_toPauliCoeffs (hsl w.1)]
        funext x
        simp only [ofPauliCoeffs, c₁]
        simp
      rw [h1, map_zero]
      simp only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      exact Eq.trans (by simp [toPauliCoeffs, pauliCoeff_zero]) rfl
end Entries
theorem ghostOperatorLocallyHolomorphic_of (hcl : LocallyHolomorphicFamiliesClosed)
    (hD : FineLaplacianIsLocallyHolomorphic)
    (hR : SmoothingTransposeIsLocal)
    (hA : ComposedAverageIsLocallyHolomorphic)
    (hF : LevelFieldsHolomorphicAndLocal)
    (hT : LevelFieldsAnalyticAlongFamily)
    (hM : BackgroundGaugeMapsInColourCoeffs)
    (hY : RealLinearMaps.RealLinearMapsStatement) :
    GhostOperatorLocallyHolomorphic := by
  intro L hL k hk
  obtain ⟨ρ₁, C₁, r₁, p₁, c₁, s₁, H₁⟩ := hD L hL k hk
  obtain ⟨ρ₂, C₂, r₂, p₂, c₂, s₂, H₂⟩ := hR L hL k hk
  obtain ⟨ρ₃, C₃, r₃, p₃, c₃, s₃, H₃⟩ := hA L hL k hk
  obtain ⟨ρ₄, C₄, r₄, -, -, -, H₄⟩ := hF L hL k hk
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  refine ⟨min ρ₁ (min ρ₂ ρ₃), C₁ + C₂ + C₃ + 0, max r₁ (max r₂ r₃),
    lt_min p₁ (lt_min p₂ p₃), by positivity, le_max_of_le_left s₁, ?_⟩
  filter_upwards [H₁, H₂, H₃, H₄, eventually_gt_atTop 0] with n a₁ a₂ a₃ a₄ hn
  intro iW dW iP dP iG dG iS iT P
  letI dS : DecidableEq (Fin 3 × Vertex L n k 0) := Classical.decEq _
  letI dT : DecidableEq (Fin 3 × Vertex L n k k) := Classical.decEq _
  obtain rfl : iG = instFintypeSum _ _ := Subsingleton.elim _ _
  obtain rfl : dG = instDecidableEqSum := Subsingleton.elim _ _
  letI : Fintype (Fin 3 × PositiveEdge L n k 0) :=
    Fintype.ofInjective (Sum.inl : _ → LevelFormIndex L n k) Sum.inl_injective
  have K := hcl L n k
  have le₁ : min ρ₁ (min ρ₂ ρ₃) ≤ ρ₁ := min_le_left _ _
  have le₂ : min ρ₁ (min ρ₂ ρ₃) ≤ ρ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have le₃ : min ρ₁ (min ρ₂ ρ₃) ≤ ρ₃ := (min_le_right _ _).trans (min_le_right _ _)
  have m₁ : r₁ ≤ max r₁ (max r₂ r₃) := le_max_left _ _
  have m₂ : r₂ ≤ max r₁ (max r₂ r₃) := (le_max_left _ _).trans (le_max_right _ _)
  have m₃ : r₃ ≤ max r₁ (max r₂ r₃) := (le_max_right _ _).trans (le_max_right _ _)
  have zero : IsLocallyHolomorphicFamily (L := L) (n := n) (k := k) tripleCoordIndexCell
      (fun p : Fin 3 × Vertex L n k k => levelVertexCell p.2)
      (fun p : Fin 3 × Vertex L n k k => levelVertexCell p.2)
      (fun _ => (0 : Matrix (Fin 3 × Vertex L n k k) (Fin 3 × Vertex L n k k) ℂ))
      (min ρ₁ (min ρ₂ ρ₃)) 0 (max r₁ (max r₂ r₃)) :=
    ⟨fun _ _ => analyticOnNhd_const, fun _ _ => by simp, fun _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ _ => rfl⟩
  refine ⟨fun z => Matrix.fromBlocks
      (((finestMesh L k ^ 2 : ℝ) : ℂ) •
        Matrix.of (rescaledOperators L n k (complexChainPoint z).fine).Delta)
      (((finestMesh L k ^ 4 : ℝ) : ℂ) •
        Matrix.of (rescaledOperators L n k (complexChainPoint z).fine).Rt)
      (composedAverageMatrix z) 0,
    K.fromBlocks (K.mono le₁ le_rfl m₁ a₁) (K.mono le₂ le_rfl m₂ a₂) (K.mono le₃ le_rfl m₃ a₃) zero, ?_⟩
  have hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  let g : (TripleCoordIndex L n k → ℝ) →ₗ[ℝ] LevelForms L n k :=
    P.formCoords.symm.toLinearMap ∘ₗ LinearMap.funLeft ℝ ℝ Sum.inl
  have hfam : IsAnalyticFamilyThroughUnit (fun x => expMove (g x) (unitPoint L n k)) 0 :=
    isAnalyticFamilyThroughUnit_of_linear hx g
  obtain ⟨hF₁, -, hF₃⟩ := hT L hL k n hk hn _ _ 0 hfam
  have hone : (expMove (g 0) (unitPoint L n k)).fine = fun _ => 1 := by
    rw [hfam.eq_unit]
    rfl
  have tendsto_one : ∀ {ι : Type} {V : (TripleCoordIndex L n k → ℝ) → ι → ComplexMatrix2},
      (∀ b, ContinuousAt (fun p => V p b) 0) → (∀ b, V 0 b = 1) → ∀ {D : Set (ι → ComplexMatrix2)},
      (∀ᶠ p in 𝓝 0, V p ∈ D) → Tendsto V (𝓝 0) (𝓝[D] fun _ => (1 : ComplexMatrix2)) := by
    intro ι V hV h1 D hD'
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_, hD'⟩
    have h := (hV b).tendsto
    rwa [h1 b] at h
  have hUt : Tendsto (fun x => (expMove (g x) (unitPoint L n k)).fine) (𝓝 0)
      (𝓝[fieldSpace L n k 0] fun _ => (1 : ComplexMatrix2)) :=
    tendsto_one (fun b => (hfam.analyticAt_fine b).continuousAt) (fun b => congrFun hone b)
      (hfam.eventually_compact.mono fun p h => h.1)
  have hWt : ∀ m < k, Tendsto (fun x => levelField (expMove (g x) (unitPoint L n k)) m) (𝓝 0)
      (𝓝[fieldSpace L n k m] fun _ => (1 : ComplexMatrix2)) := fun m hm =>
    tendsto_one (fun b => (hF₁ m hm.le b).1.continuousAt) (fun b => (hF₁ m hm.le b).2)
      (hF₃.mono fun p h => h.2 m hm.le)
  have hlin : ∀ m ≤ k, ∀ᶠ x in 𝓝 (0 : TripleCoordIndex L n k → ℝ),
      ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k m,
        ∀ l : vertexFunctionSpace L n k 0,
        (T l : Vertex L n k m → ComplexMatrix2) =
          composedCubeAverage (expMove (g x) (unitPoint L n k)) m
            (l : Vertex L n k 0 → ComplexMatrix2) := by
    intro m
    induction m with
    | zero => exact fun _ => Eventually.of_forall fun p => ⟨LinearMap.id, fun l => rfl⟩
    | succ m ih =>
      intro hm
      have h₁ := (hWt m (by omega)).eventually
        ((hY L n k hL hn hk).1 m (by omega)).adjointCubeAverage_isLinear
      filter_upwards [ih (by omega), h₁] with p h₂ h₃
      obtain ⟨T, hT'⟩ := h₂
      obtain ⟨T', hT''⟩ := h₃
      refine ⟨T' ∘ₗ T, fun l => ?_⟩
      show (T' (T l) : Vertex L n k (m + 1) → ComplexMatrix2) =
        adjointCubeAverage (levelField _ m) (composedCubeAverage _ m l)
      rw [hT'', hT']
  filter_upwards [hUt.eventually (hM L hL k n hk hn), hlin k le_rfl] with x h₁ h₂
  obtain ⟨-, -, fRt, fD⟩ := h₁
  have hS : ∀ l : vertexFunctionSpace L n k 0,
      (composedCubeAverageLinear (expMove (g x) (unitPoint L n k)) l :
          Vertex L n k k → ComplexMatrix2) =
        composedCubeAverage (expMove (g x) (unitPoint L n k)) k
          (l : Vertex L n k 0 → ComplexMatrix2) := fun l =>
    Classical.epsilon_spec (p := fun T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k =>
      ∀ y : vertexFunctionSpace L n k 0, (T y : Vertex L n k k → ComplexMatrix2) =
        composedCubeAverage (expMove (g x) (unitPoint L n k)) k y) h₂ l
  have hp : complexChainPoint (complexifyCoords x) = expMove (g x) (unitPoint L n k) :=
    (a₄ P).1 x
  have e := ghostBlockOperator_matrix_eq P _ fRt fD hS
  show complexMatrixOfLinearMap P.ghostCoords P.ghostCoords
    (ghostBlockOperator (expMove (g x) (unitPoint L n k))) = _
  have e₂ : composedAverageMatrix (complexifyCoords x) =
      Matrix.of fun p q => toPauliCoeffs (composedCubeAverage (expMove (g x) (unitPoint L n k)) k
        (ofPauliCoeffs (UnitGaugeDirections.basisFunction q))) p := by
    unfold composedAverageMatrix
    rw [hp]
    rfl
  show _ = Matrix.fromBlocks
    (_ • Matrix.of (rescaledOperators L n k (complexChainPoint (complexifyCoords x)).fine).Delta)
    (_ • Matrix.of (rescaledOperators L n k (complexChainPoint (complexifyCoords x)).fine).Rt)
    (composedAverageMatrix (complexifyCoords x)) 0
  rw [e, e₂, hp]
end RunningCouplingSlope.GhostOperatorLocality
end YangMills.Construction
end
