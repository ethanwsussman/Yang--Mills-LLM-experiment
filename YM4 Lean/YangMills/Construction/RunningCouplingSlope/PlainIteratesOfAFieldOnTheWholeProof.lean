import YangMills.Construction.OneLoop.PauliMatrixComputations
import YangMills.Construction.RunningCouplingSlope.PlainAverageNearOneOnTheWhole
import YangMills.Construction.RunningCouplingSlope.PlainIteratesOfAFieldOnTheWhole
import YangMills.Construction.RunningCouplingSlope.PlainStepAtRealConfigurationsOnTheWhole
import YangMills.Construction.RunningCouplingSlope.PlainStepIsAnalyticOnTheWhole
import YangMills.Construction.RunningCouplingSlope.PlainStepOnTheFormsOnTheWhole
import YangMills.Construction.RunningCouplingSlope.PlainStepUnderTranslationsOnTheWhole
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.AveragingCommutesWithIsometriesAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
namespace FieldIterates
open YangMills.Construction.Matrices (ComplexMatrix2)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
open YangMills.Construction.Tower (pauliCoeff ofPauliCoeffs toPauliCoeffs meshAt polydiscRadius)
open YangMills.Construction.Tower.FullSpace (Edge Vertex complexEdgeForms edgeFormSpace pushField)
open YangMills.Construction.PeriodicOperators
  (colourEdges intShift castVec shiftEdge shiftField fieldExtend fieldValues IsSupBelow PeriodicData
    PosEdge)
private instance : CompleteSpace ComplexMatrix2 := FiniteDimensional.complete ℂ ComplexMatrix2
section PauliCoordinates
private def pauliCoeffLinear (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
  map_add' X Y := by
    fin_cases a <;> simp <;> ring
  map_smul' c X := by
    fin_cases a <;> simp <;> ring
private def pauliCoeffCLM (a : Fin 3) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (pauliCoeffLinear a)
private theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem real_smul_eq_ofReal_smul (x : ℝ) (X : ComplexMatrix2) : x • X = (x : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
end PauliCoordinates
section EdgeForms
variable {L k i : ℕ}
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k m : ℕ) :
    0 < meshAt L k m := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private theorem pos_or_opposite_pos {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
private theorem not_pos_opposite {a : ℝ} (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
private def edgeForm (ζ : (colourEdges L k i).Carrier → ℂ) : Edge L k i → ComplexMatrix2 :=
  (Tower.FullSpace.edgePauliCoordinates L k i).ofCoeffs ζ
private theorem edgeForm_of_pos (ζ : (colourEdges L k i).Carrier → ℂ) {b : Edge L k i}
    (h : b.IsPositivelyOriented) :
    edgeForm ζ b = ∑ a, ζ (a, ⟨b, h⟩) • ComplexMatrix2.pauliFamily a := by
  simp only [edgeForm, Tower.FullSpace.edgePauliCoordinates, Tower.FullSpace.extendOddly, if_pos h, dif_pos h,
    ofPauliCoeffs]
abbrev _root_.YangMills.DeltaSharedProofs.p500947 := @edgeForm_of_pos
private theorem edgeForm_of_not_pos (ζ : (colourEdges L k i).Carrier → ℂ) {b : Edge L k i}
    (h : ¬ b.IsPositivelyOriented) : edgeForm ζ b = -edgeForm ζ b.opposite := by
  have hr : b.opposite.IsPositivelyOriented := (pos_or_opposite_pos b).resolve_left h
  simp only [edgeForm, Tower.FullSpace.edgePauliCoordinates, Tower.FullSpace.extendOddly, if_neg h, if_pos hr]
abbrev _root_.YangMills.DeltaSharedProofs.p500478 := @edgeForm_of_not_pos
private theorem edgeForm_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ζ : (colourEdges L k i).Carrier → ℂ) (b : Edge L k i) :
    edgeForm ζ b.opposite = -edgeForm ζ b := by
  by_cases h : b.IsPositivelyOriented
  · exact edgeForm_of_not_pos ζ (not_pos_opposite (meshAt_pos hL k i) h)
  · rw [edgeForm_of_not_pos ζ h, neg_neg]
abbrev _root_.YangMills.DeltaSharedProofs.p501817 := @edgeForm_opposite
private theorem edgeForm_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ζ : (colourEdges L k i).Carrier → ℂ) :
    edgeForm ζ ∈ complexEdgeForms (meshAt L k i) := by
  refine ⟨fun b hb => ?_, edgeForm_opposite hL ζ⟩
  rw [edgeForm_of_pos ζ hb]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (pauliFamily_mem_traceless a)
abbrev _root_.YangMills.DeltaSharedProofs.p502175 := @edgeForm_mem
private theorem edgeForm_add (ζ ζ' : (colourEdges L k i).Carrier → ℂ) :
    edgeForm (ζ + ζ') = edgeForm ζ + edgeForm ζ' := by
  have hp : ∀ (b : Edge L k i), b.IsPositivelyOriented →
      edgeForm (ζ + ζ') b = edgeForm ζ b + edgeForm ζ' b := by
    intro b h
    simp only [edgeForm_of_pos _ h]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => add_smul _ _ _
  funext b
  by_cases h : b.IsPositivelyOriented
  · exact hp b h
  · have hr : b.opposite.IsPositivelyOriented := (pos_or_opposite_pos b).resolve_left h
    simp only [Pi.add_apply, edgeForm_of_not_pos _ h, hp _ hr, neg_add]
abbrev _root_.YangMills.DeltaSharedProofs.p502563 := @edgeForm_add
private theorem edgeForm_smul (c : ℂ) (ζ : (colourEdges L k i).Carrier → ℂ) :
    edgeForm (c • ζ) = c • edgeForm ζ := by
  have hp : ∀ (b : Edge L k i), b.IsPositivelyOriented →
      edgeForm (c • ζ) b = c • edgeForm ζ b := by
    intro b h
    simp only [edgeForm_of_pos _ h, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => mul_smul _ _ _
  funext b
  by_cases h : b.IsPositivelyOriented
  · exact hp b h
  · have hr : b.opposite.IsPositivelyOriented := (pos_or_opposite_pos b).resolve_left h
    simp only [Pi.smul_apply, edgeForm_of_not_pos _ h, hp _ hr, smul_neg]
abbrev _root_.YangMills.DeltaSharedProofs.p501730 := @edgeForm_smul
end EdgeForms
section Distances
variable {L k : ℕ}
private theorem meshAt_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i ≤ k) :
    meshAt L k i ≤ 1 := by apply _root_.YangMills.SharedProofs.p8023 <;> assumption
private theorem dist_initial_of_mem_doubleCube (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hm : m < k) {c : Edge L k (m + 1)}
    (hc : c.IsPositivelyOriented) {x : AmbientSpace}
    (hx : x ∈ Tower.FullSpace.doubleCube L (meshAt L k m) c) :
    ‖x - (c.initial : AmbientSpace)‖ ≤ 3 / 2 := by
  have H := (hZ L hL k 1 (m + 1) (by omega) (by omega) (by omega)).2.2.2.2.2.1
  obtain ⟨ν, hν, hb⟩ := H.sites_near c hc x hx
  have hle := meshAt_le_one (k := k) hL (i := m + 1) (by omega)
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun ρ => ?_
  have hco : (x - (c.initial : AmbientSpace)) ρ = (ν ρ : ℝ) * meshAt L k m := by
    rw [hν]
    simp [Tower.FullSpace.offsetPoint, Finset.sum_apply, Pi.single_apply]
  rw [hco, Real.norm_eq_abs]
  have := hb ρ
  have h2 : (3 / 2 : ℝ) * meshAt L k (m + 1) ≤ 3 / 2 := by linarith
  exact (this.trans_le h2).le
abbrev _root_.YangMills.SharedProofs.p114653 := @dist_initial_of_mem_doubleCube
private theorem edge_length_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ}
    (hi : i ≤ k) (b : Edge L k i) :
    ‖(b.terminal : AmbientSpace) - (b.initial : AmbientSpace)‖ ≤ 1 := by
  have hle := meshAt_le_one (k := k) hL hi
  have ha := meshAt_pos hL k i
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun ρ => ?_
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · have e : (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) =
        ((InfiniteLattice.axisStep (meshAt L k i) μ : InfiniteLattice.LatticePoint _) :
          AmbientSpace) := by
      rw [← h]
      rfl
    rw [e]
    by_cases hμ : ρ = μ
    · subst hμ
      simp [InfiniteLattice.axisStep, abs_of_pos ha, hle]
    · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hμ]
  · have e : (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) =
        -((InfiniteLattice.axisStep (meshAt L k i) μ : InfiniteLattice.LatticePoint _) :
          AmbientSpace) := by
      have := congrArg
        (fun s : InfiniteLattice.LatticePoint (meshAt L k i) => (s : AmbientSpace)) h
      simpa using this
    rw [e]
    by_cases hμ : ρ = μ
    · subst hμ
      simp [InfiniteLattice.axisStep, abs_of_pos ha, hle]
    · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hμ]
end Distances
section NearIdentity
variable {L k : ℕ}
private theorem inv_sub_one_le {A : ComplexMatrix2} (hA : A ∈ PeriodicLattice.complexGaugeGroup)
    {ε : ℝ} (hε : ε ≤ 1 / 2) (h : ComplexMatrix2.operatorNorm (A - 1) ≤ ε) :
    ComplexMatrix2.operatorNorm (A⁻¹ - 1) ≤ 2 * ε := by
  have hd : IsUnit A.det := by
    have e : A.det = 1 := hA
    rw [e]
    exact isUnit_one
  have h' : ‖A - 1‖ ≤ ε := h
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans h'
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hd
  have e : A⁻¹ - 1 = -(A⁻¹ * (A - 1)) := by
    rw [mul_sub, hinv, mul_one]
    abel
  have h1 : ‖A⁻¹ - 1‖ ≤ ‖A⁻¹‖ * ε := by
    rw [e, norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h' (norm_nonneg _))
  have h2 : ‖A⁻¹‖ ≤ 1 + ‖A⁻¹ - 1‖ := by
    have := norm_add_le (A⁻¹ - 1) (1 : ComplexMatrix2)
    rw [sub_add_cancel, norm_one] at this
    linarith
  show ‖A⁻¹ - 1‖ ≤ 2 * ε
  nlinarith [norm_nonneg (A⁻¹)]
private theorem inv_inv_of_mem_complexGaugeGroup {X : ComplexMatrix2}
    (h : X ∈ PeriodicLattice.complexGaugeGroup) : X⁻¹⁻¹ = X := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
private theorem inv_mem_complexGaugeGroup {X : ComplexMatrix2}
    (h : X ∈ PeriodicLattice.complexGaugeGroup) : X⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
private theorem nearIdentityFields_mono {m : ℕ} {δ δ' : ℝ} (h : δ ≤ δ') :
    nearIdentityFields L k m δ ⊆ nearIdentityFields L k m δ' :=
  fun _ hV => ⟨hV.1, fun b => (hV.2 b).trans_le h⟩
private theorem nextMeanIterate_near (hN : NormalizedMeanNearIdentity)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k m : ℕ, m < k →
      ∀ V ∈ nearIdentityFields L k m δ, nextMeanIterate V ∈ nearIdentityFields L k (m + 1) ε := by
  set ε₀ := min (ε / 4) (1 / 2) with hε₀
  have hp : 0 < ε₀ := lt_min (by positivity) (by norm_num)
  obtain ⟨δ, hδ, H⟩ := hN L hL ε₀ hp
  refine ⟨δ, hδ, fun k m hm V hV => ?_⟩
  have hnear := fun (c : Edge L k (m + 1)) (hc : c.IsPositivelyOriented) =>
    H k m hm V hV.1 hV.2 c hc
  have ha := meshAt_pos hL k (m + 1)
  have hpos : ∀ c : Edge L k (m + 1), c.IsPositivelyOriented →
      nextMeanIterate V c = normalizedMean V c :=
    fun c hc => if_pos hc
  have hneg : ∀ c : Edge L k (m + 1), ¬ c.IsPositivelyOriented →
      nextMeanIterate V c = (normalizedMean V c.opposite)⁻¹ := fun c hc => if_neg hc
  refine ⟨⟨fun c => ?_, fun c => ?_⟩, fun c => ?_⟩
  · by_cases hc : c.IsPositivelyOriented
    · rw [hpos c hc]
      exact (hnear c hc).2.2.2.1
    · rw [hneg c hc]
      exact inv_mem_complexGaugeGroup
        (hnear _ ((pos_or_opposite_pos c).resolve_left hc)).2.2.2.1
  · by_cases hc : c.IsPositivelyOriented
    · rw [hneg _ (not_pos_opposite ha hc), hpos c hc]
      rfl
    · have hr := (pos_or_opposite_pos c).resolve_left hc
      rw [hpos _ hr, hneg c hc]
      exact (inv_inv_of_mem_complexGaugeGroup (hnear _ hr).2.2.2.1).symm
  · by_cases hc : c.IsPositivelyOriented
    · rw [hpos c hc]
      exact (hnear c hc).2.2.1.trans_le ((min_le_left _ _).trans (by linarith))
    · have hr := (pos_or_opposite_pos c).resolve_left hc
      rw [hneg c hc]
      have h1 := inv_sub_one_le (hnear _ hr).2.2.2.1 (min_le_right _ _) (hnear _ hr).2.2.1.le
      have h2 : 2 * ε₀ < ε := by
        have := min_le_left (ε / 4) (1 / 2 : ℝ)
        linarith
      exact h1.trans_lt h2
end NearIdentity
section StepProperties
private structure StepProperties (L k : ℕ) (δ : ℝ) : Prop where
  analytic : ∀ m : ℕ, m < k → ∀ (l : ℕ)
      (W : Coordinates.ComplexCoordinates l → Edge L k m → ComplexMatrix2)
      (p : Coordinates.ComplexCoordinates l), (∀ b, AnalyticAt ℂ (fun w => W w b) p) →
      (∀ᶠ w in 𝓝 p, W w ∈ nearIdentityFields L k m δ) →
      (∀ c, AnalyticAt ℂ (fun w => nextMeanIterate (W w) c) p) ∧
      (∀ c : Edge L k (m + 1), c.IsPositivelyOriented →
        AnalyticAt ℂ (fun w => (meanRadius (W w) c)⁻¹) p) ∧
      (∀ B ∈ complexEdgeForms (meshAt L k m), ∀ c,
        AnalyticAt ℂ (fun w => meanCovariantStep (W w) B c) p) ∧
      ∀ (y : Vertex L k (m + 1)) (x : Vertex L k m),
        x ∈ Tower.FullSpace.cubeVertices L (meshAt L k m) y →
        AnalyticAt ℂ (fun w => Tower.FullSpace.complexContourMean L (W w) y x) p
  forms : ∀ m : ℕ, m < k → ∀ V ∈ nearIdentityFields L k m δ,
      (∀ B ∈ complexEdgeForms (meshAt L k m),
        meanCovariantStep V B ∈ complexEdgeForms (meshAt L k (m + 1))) ∧
      (∀ B ∈ complexEdgeForms (meshAt L k m),
        ∀ B' ∈ complexEdgeForms (meshAt L k m), ∀ w : ℂ,
          meanCovariantStep V (w • B + B') =
            w • meanCovariantStep V B + meanCovariantStep V B') ∧
      (∀ c : Edge L k (m + 1), c.IsPositivelyOriented →
        ∀ B ∈ complexEdgeForms (meshAt L k m),
        (∀ b ∈ Tower.FullSpace.doubleCubeLinks L (meshAt L k m) c, B b = 0) →
          meanCovariantStep V B c = 0) ∧
      ∀ c : Edge L k (m + 1), c.IsPositivelyOriented → ∀ V' ∈ nearIdentityFields L k m δ,
        (∀ b ∈ Tower.FullSpace.doubleCubeLinks L (meshAt L k m) c, V b = V' b) →
          meanRadius V c = meanRadius V' c ∧ normalizedMean V c = normalizedMean V' c ∧
          (∀ B ∈ complexEdgeForms (meshAt L k m),
            meanCovariantStep V B c = meanCovariantStep V' B c) ∧
          ∀ y : Vertex L k (m + 1), (y = c.initial ∨ y = c.terminal) →
            ∀ x ∈ Tower.FullSpace.cubeVertices L (meshAt L k m) y,
              Tower.FullSpace.complexContourMean L V y x =
                Tower.FullSpace.complexContourMean L V' y x
  shift : ∀ m : ℕ, m < k → ∀ n : Fin 4 → ℤ, ∀ V ∈ nearIdentityFields L k m δ,
      nextMeanIterate (pushField (intShift n) V) = pushField (intShift n) (nextMeanIterate V) ∧
      ∀ c : Edge L k (m + 1), c.IsPositivelyOriented →
        meanRadius (pushField (intShift n) V) (Tower.FullSpace.edgeImage (intShift n) c) =
            meanRadius V c ∧
        ∀ B ∈ complexEdgeForms (meshAt L k m),
          meanCovariantStep (pushField (intShift n) V)
              (Tower.FullSpace.isometryOnTangent (intShift n) V B)
              (Tower.FullSpace.edgeImage (intShift n) c) =
            meanCovariantStep V B c
  compact : ∀ m : ℕ, m < k → ∀ V ∈ nearIdentityFields L k m δ,
      (∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) →
      (∀ c, nextMeanIterate V c ∈ PeriodicLattice.compactGaugeGroup) ∧
      (∀ c : Edge L k (m + 1), c.IsPositivelyOriented → (meanRadius V c).im = 0) ∧
      ∀ B ∈ edgeFormSpace (meshAt L k m), ∀ c,
        meanCovariantStep V B c ∈ ComplexMatrix2.hermitianTraceless
  radius : δ ≤ polydiscRadius L
private theorem exists_stepProperties (hAn : MeanStepAnalytic) (hF : MeanStepOnForms)
    (hT : MeanStepShiftCovariant) (hR : MeanStepAtCompactFields)
    (hS : Tower.SmoothingNearIdentity) {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ ≤ δ₀ → ∀ k : ℕ, StepProperties L k δ := by
  obtain ⟨δ₂, h₂, H₂⟩ := hAn L hL
  obtain ⟨δ₃, h₃, H₃⟩ := hF L hL
  obtain ⟨δ₄, h₄, H₄⟩ := hT L hL
  obtain ⟨δ₅, h₅, H₅⟩ := hR L hL
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  refine ⟨min (min δ₂ δ₃) (min (min δ₄ δ₅) (polydiscRadius L)),
    lt_min (lt_min h₂ h₃) (lt_min (lt_min h₄ h₅) hρ), fun δ hδ k => ?_⟩
  have l₂ : δ ≤ δ₂ := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have l₃ : δ ≤ δ₃ := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have l₄ : δ ≤ δ₄ :=
    hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have l₅ : δ ≤ δ₅ :=
    hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have lρ : δ ≤ polydiscRadius L := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨?_, ?_, ?_, ?_, lρ⟩
  · intro m hm l W p hW hs
    exact H₂ k m hm l W p hW (hs.mono fun w h => nearIdentityFields_mono l₂ h)
  · intro m hm V hV
    obtain ⟨a₁, a₂, a₃, a₄⟩ := H₃ k m hm V (nearIdentityFields_mono l₃ hV)
    exact ⟨a₁, a₂, a₃, fun c hc V' hV' he => a₄ c hc V' (nearIdentityFields_mono l₃ hV') he⟩
  · intro m hm n V hV
    exact H₄ k m hm n V (nearIdentityFields_mono l₄ hV)
  · intro m hm V hV hr
    exact H₅ k m hm V (nearIdentityFields_mono l₅ hV) hr
end StepProperties
section InitialField
variable {L k : ℕ}
private abbrev initialField (f : (colourEdges L k 0).Carrier → ℂ) : Edge L k 0 → ComplexMatrix2 :=
  Tower.FullSpace.BackgroundJets.gaugeFieldOfForm L k f
private theorem initialField_of_pos (f : (colourEdges L k 0).Carrier → ℂ) {b : Edge L k 0}
    (h : b.IsPositivelyOriented) :
    initialField f b = ComplexMatrix2.matExp (Complex.I • edgeForm f b) := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.gaugeFieldOfForm_of_pos <;> assumption
private theorem initialField_of_not_pos (f : (colourEdges L k 0).Carrier → ℂ) {b : Edge L k 0}
    (h : ¬ b.IsPositivelyOriented) :
    initialField f b = (ComplexMatrix2.matExp (Complex.I • edgeForm f b.opposite))⁻¹ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.gaugeFieldOfForm_of_not_pos <;> assumption
private theorem one_mem_fieldsValuedIn :
    (1 : Edge L k 0 → ComplexMatrix2) ∈
      Tower.FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup :=
  ⟨fun b => Matrix.det_one, fun b => by simp⟩
private theorem matExp_mem (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (f : (colourEdges L k 0).Carrier → ℂ)
    {b : Edge L k 0} (hb : b.IsPositivelyOriented) :
    ComplexMatrix2.matExp (Complex.I • edgeForm f b) ∈ PeriodicLattice.complexGaugeGroup := by
  have h := (((hA.2.2 L k 0 hL (Nat.zero_le _)).2.1.1).2 1 one_mem_fieldsValuedIn (edgeForm f)
    (edgeForm_mem hL f) ⟨b, hb⟩).1 1
  have h' : ComplexMatrix2.matExp (Complex.I • ((1 : ℂ) • edgeForm f b)) * (1 : ComplexMatrix2) ∈
      PeriodicLattice.complexGaugeGroup := h
  rwa [one_smul, mul_one] at h'
private theorem initialField_mem (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (f : (colourEdges L k 0).Carrier → ℂ) :
    initialField f ∈ Tower.FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := by
  have ha := meshAt_pos hL k 0
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [initialField_of_pos f hb]
      exact matExp_mem hA hL f hb
    · rw [initialField_of_not_pos f hb]
      exact inv_mem_complexGaugeGroup
        (matExp_mem hA hL f ((pos_or_opposite_pos b).resolve_left hb))
  · by_cases hb : b.IsPositivelyOriented
    · rw [initialField_of_not_pos f (not_pos_opposite ha hb), initialField_of_pos f hb]
      rfl
    · have hr := (pos_or_opposite_pos b).resolve_left hb
      rw [initialField_of_pos f hr, initialField_of_not_pos f hb]
      exact (inv_inv_of_mem_complexGaugeGroup (matExp_mem hA hL f hr)).symm
private theorem norm_pauliFamily (a : Fin 3) : ‖ComplexMatrix2.pauliFamily a‖ = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.norm_pauliFamily <;> assumption
private theorem norm_edgeForm_le (f : (colourEdges L k 0).Carrier → ℂ) {r : ℝ}
    (h : ∀ κ, ‖f κ‖ ≤ r) {b : Edge L k 0} (hb : b.IsPositivelyOriented) :
    ‖edgeForm f b‖ ≤ 3 * r := by
  rw [edgeForm_of_pos f hb]
  calc ‖∑ a, f (a, ⟨b, hb⟩) • ComplexMatrix2.pauliFamily a‖
        ≤ ∑ a, ‖f (a, ⟨b, hb⟩) • ComplexMatrix2.pauliFamily a‖ := norm_sum_le _ _
    _ = ∑ a, ‖f (a, ⟨b, hb⟩)‖ := by simp only [norm_smul, norm_pauliFamily, mul_one]
    _ ≤ ∑ _a : Fin 3, r := Finset.sum_le_sum fun a _ => h _
    _ = 3 * r := by simp
private theorem initialField_near (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ f : (colourEdges L k 0).Carrier → ℂ, IsSupBelow (colourEdges L k 0) f ρ →
      initialField f ∈ nearIdentityFields L k 0 ε := by
  set ε₀ := min (ε / 4) (1 / 2) with hε₀
  have hp : 0 < ε₀ := lt_min (by positivity) (by norm_num)
  have hc : ContinuousAt (fun X : ComplexMatrix2 => ComplexMatrix2.matExp (Complex.I • X)) 0 :=
    ContinuousAt.comp (g := NormedSpace.exp) (f := fun X : ComplexMatrix2 => Complex.I • X)
      (NormedSpace.exp_analytic (𝕂 := ℂ) (Complex.I • (0 : ComplexMatrix2))).continuousAt
      (continuous_const_smul _).continuousAt
  obtain ⟨η, hη, H⟩ := Metric.continuousAt_iff.1 hc ε₀ hp
  have h0 : ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2)) = 1 := by
    rw [smul_zero]
    exact NormedSpace.exp_zero
  have key : ∀ X : ComplexMatrix2, ‖X‖ < η →
      ‖ComplexMatrix2.matExp (Complex.I • X) - 1‖ < ε₀ := fun X hX => by
    have := H (x := X) (by simpa [dist_eq_norm] using hX)
    rwa [h0, dist_eq_norm] at this
  refine ⟨η / 3, by positivity, fun f ⟨r, hr, hb⟩ => ⟨initialField_mem hA hL f, fun b => ?_⟩⟩
  have hbound : ∀ {b' : Edge L k 0}, b'.IsPositivelyOriented →
      ‖ComplexMatrix2.matExp (Complex.I • edgeForm f b') - 1‖ < ε₀ := fun hb' =>
    key _ ((norm_edgeForm_le f hb hb').trans_lt (by linarith))
  by_cases hbp : b.IsPositivelyOriented
  · rw [initialField_of_pos f hbp]
    exact (hbound hbp).trans_le ((min_le_left _ _).trans (by linarith))
  · have hrv := (pos_or_opposite_pos b).resolve_left hbp
    rw [initialField_of_not_pos f hbp]
    have h1 := inv_sub_one_le (matExp_mem hA hL f hrv) (min_le_right (ε / 4) (1 / 2))
      (hbound hrv).le
    have h2 : 2 * ε₀ < ε := by
      have := min_le_left (ε / 4) (1 / 2 : ℝ)
      linarith
    exact h1.trans_lt h2
private theorem meanIterate_near (hN : NormalizedMeanNearIdentity) (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) :
    ∀ m, m ≤ k → ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ f : (colourEdges L k 0).Carrier → ℂ, IsSupBelow (colourEdges L k 0) f ρ →
        meanIterate (initialField f) m ∈ nearIdentityFields L k m ε := by
  intro m
  induction m with
  | zero => exact fun _ ε hε => initialField_near hA hL hε
  | succ m ih =>
    intro hm ε hε
    obtain ⟨δ, hδ, H⟩ := nextMeanIterate_near hN hL hε
    obtain ⟨ρ, hρ, h⟩ := ih (by omega) δ hδ
    exact ⟨ρ, hρ, fun f hf => H k m (by omega) _ (h f hf)⟩
private theorem exists_uniform_radius (hN : NormalizedMeanNearIdentity)
    (hA : Tower.LeftChartFields.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {δ : ℝ} (hδ : 0 < δ) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ m, m ≤ k →
      ∀ f : (colourEdges L k 0).Carrier → ℂ, IsSupBelow (colourEdges L k 0) f ρ →
        meanIterate (initialField f) m ∈ nearIdentityFields L k m δ := by
  have main : ∀ q, q ≤ k → ∃ ρ : ℝ, 0 < ρ ∧ ∀ m, m ≤ q →
      ∀ f : (colourEdges L k 0).Carrier → ℂ, IsSupBelow (colourEdges L k 0) f ρ →
        meanIterate (initialField f) m ∈ nearIdentityFields L k m δ := by
    intro q
    induction q with
    | zero =>
      intro _
      obtain ⟨ρ, hρ, h⟩ := meanIterate_near (k := k) hN hA hL 0 (Nat.zero_le _) δ hδ
      refine ⟨ρ, hρ, fun m hm f hf => ?_⟩
      obtain rfl : m = 0 := by omega
      exact h f hf
    | succ q ih =>
      intro hq
      obtain ⟨ρ₁, h₁, H₁⟩ := ih (by omega)
      obtain ⟨ρ₂, h₂, H₂⟩ := meanIterate_near (k := k) hN hA hL (q + 1) hq δ hδ
      refine ⟨min ρ₁ ρ₂, lt_min h₁ h₂, fun m hm f hf => ?_⟩
      obtain ⟨r, hr, hb⟩ := hf
      by_cases e : m = q + 1
      · subst e
        exact H₂ f ⟨r, hr.trans_le (min_le_right _ _), hb⟩
      · exact H₁ m (by omega) f ⟨r, hr.trans_le (min_le_left _ _), hb⟩
  exact main k le_rfl
end InitialField
section SingleLattice
variable {a : ℝ} {f : AmbientSpace → AmbientSpace}
private theorem coe_vertexImage (hM : Tower.FullSpace.MapsSublatticeOnto a f)
    (x : InfiniteLattice.LatticePoint a) :
    ((Tower.FullSpace.vertexImage f x : InfiniteLattice.LatticePoint a) : AmbientSpace) = f x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_space_vertexImage <;> assumption
private theorem apply_vertexPreimage (hM : Tower.FullSpace.MapsSublatticeOnto a f)
    (x : InfiniteLattice.LatticePoint a) :
    f (Tower.FullSpace.vertexPreimage f x : InfiniteLattice.LatticePoint a) = x := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingInvariance.vertexPreimage_spec <;> assumption
private theorem vertexPreimage_vertexImage (hM : Tower.FullSpace.MapsSublatticeOnto a f)
    (hi : Function.Injective f) (x : InfiniteLattice.LatticePoint a) :
    Tower.FullSpace.vertexPreimage f (Tower.FullSpace.vertexImage f x) = x :=
  Subtype.ext (hi ((apply_vertexPreimage hM _).trans (coe_vertexImage hM x)))
private theorem edgeImage_ends (hM : Tower.FullSpace.MapsSublatticeOnto a f)
    (hB : Tower.FullSpace.MapsLinksOnto a f) (b : InfiniteLattice.Link a) :
    (Tower.FullSpace.edgeImage f b).initial = Tower.FullSpace.vertexImage f b.initial ∧
      (Tower.FullSpace.edgeImage f b).terminal = Tower.FullSpace.vertexImage f b.terminal := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_endpoints <;> assumption
private theorem edgePreimage_ends (hM : Tower.FullSpace.MapsSublatticeOnto a f)
    (hB : Tower.FullSpace.MapsLinksOnto a f) (hi : Function.Injective f)
    (b : InfiniteLattice.Link a) :
    (Tower.FullSpace.edgePreimage f b).initial = Tower.FullSpace.vertexPreimage f b.initial ∧
      (Tower.FullSpace.edgePreimage f b).terminal =
        Tower.FullSpace.vertexPreimage f b.terminal := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgePreimage_endpoints <;> assumption
private theorem edgeImage_edgePreimage (hM : Tower.FullSpace.MapsSublatticeOnto a f)
    (hB : Tower.FullSpace.MapsLinksOnto a f) (hi : Function.Injective f)
    (b : InfiniteLattice.Link a) :
    Tower.FullSpace.edgeImage f (Tower.FullSpace.edgePreimage f b) = b := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_edgePreimage <;> assumption
private theorem edgePreimage_edgeImage (hM : Tower.FullSpace.MapsSublatticeOnto a f)
    (hB : Tower.FullSpace.MapsLinksOnto a f) (hi : Function.Injective f)
    (b : InfiniteLattice.Link a) :
    Tower.FullSpace.edgePreimage f (Tower.FullSpace.edgeImage f b) = b := by
  obtain ⟨t, h⟩ := edgeImage_ends hM hB b
  obtain ⟨t', h'⟩ := edgePreimage_ends hM hB hi (Tower.FullSpace.edgeImage f b)
  refine InfiniteLattice.Link.ext ?_ ?_
  · rw [t', t, vertexPreimage_vertexImage hM hi]
  · rw [h', h, vertexPreimage_vertexImage hM hi]
private theorem edgeImage_opposite (hM : Tower.FullSpace.MapsSublatticeOnto a f)
    (hB : Tower.FullSpace.MapsLinksOnto a f) (b : InfiniteLattice.Link a) :
    Tower.FullSpace.edgeImage f b.opposite = (Tower.FullSpace.edgeImage f b).opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_opposite <;> assumption
end SingleLattice
private structure ShiftFacts (L k : ℕ) (f : AmbientSpace → AmbientSpace) : Prop where
  sublattice : ∀ i ≤ k, Tower.FullSpace.MapsSublatticeOnto (meshAt L k i) f
  links : ∀ i ≤ k, Tower.FullSpace.MapsLinksOnto (meshAt L k i) f
  inj : Function.Injective f
  isom : Tower.FullSpace.IsDistancePreserving f
  add : ∀ p q : AmbientSpace, f (p + q) = f p + q
section Shifts
variable {L k m : ℕ} {f : AmbientSpace → AmbientSpace}
private theorem intShift_shiftFacts (hZ : Tower.BlockPathContourPivotStatement)
    (hTr : Tower.Translations.TranslationProperties) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (n : Fin 4 → ℤ) : ShiftFacts L k (intShift n) := by
  have hT := (hTr L hL k k le_rfl).2.2.2.1 n
  have hCt := ((hZ L hL k 0 k hk (Nat.zero_le _) le_rfl).2.2.2.2.2.2 hk).1
  have hMk : Tower.FullSpace.MapsSublatticeOnto (meshAt L k k) (intShift n) := hT.2.1 k le_rfl
  have hv : castVec n ∈ (InfiniteLattice.latticeSubgroup (meshAt L k k) : Set AmbientSpace) := by
    have h0 : intShift n 0 ∈ intShift n '' (InfiniteLattice.latticeSubgroup (meshAt L k k) :
        Set AmbientSpace) := ⟨0, (InfiniteLattice.latticeSubgroup _).zero_mem, rfl⟩
    rw [show intShift n '' (InfiniteLattice.latticeSubgroup (meshAt L k k) :
      Set AmbientSpace) = InfiniteLattice.latticeSubgroup (meshAt L k k) from hMk] at h0
    simpa [intShift] using h0
  exact { sublattice := fun i hi => hT.2.1 i hi
          links := fun i hi => (hCt.mapsSublatticeAndLinks ⟨castVec n, hv⟩ i hi).2
          inj := hT.2.2.1.injective
          isom := hT.1
          add := fun p q => by
            show p + q + castVec n = p + castVec n + q
            abel }
private theorem castVec_neg (n : Fin 4 → ℤ) : castVec (-n) = -castVec n := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.castVec_neg <;> assumption
section ShiftedEdges
variable (n : Fin 4 → ℤ) (T : ShiftFacts L k (intShift n)) (hm : m ≤ k)
  (hB : FullLatticeOverTorus.ShiftSurjectiveOnEdges L k m n)
  (hB' : FullLatticeOverTorus.ShiftSurjectiveOnEdges L k m (-n))
include T hm hB in
private theorem shiftEdge_val (c : PosEdge L k m) :
    (shiftEdge n c).1 = Tower.FullSpace.edgeImage (intShift n) c.1 := by
  have hM := T.sublattice m hm
  obtain ⟨t, h⟩ := edgeImage_ends hM (T.links m hm) c.1
  refine InfiniteLattice.Link.ext ?_ ?_
  · rw [t]
    apply Subtype.ext
    rw [coe_vertexImage hM]
    exact (hB.2 c).1
  · rw [h]
    apply Subtype.ext
    rw [coe_vertexImage hM]
    exact (hB.2 c).2
include T hm hB hB' in
private theorem shiftEdge_shiftEdge_neg (c : PosEdge L k m) :
    shiftEdge n (shiftEdge (-n) c) = c := by
  apply Subtype.ext
  apply InfiniteLattice.Link.ext
  · apply Subtype.ext
    rw [(hB.2 _).1, (hB'.2 _).1, castVec_neg]
    simp
  · apply Subtype.ext
    rw [(hB.2 _).2, (hB'.2 _).2, castVec_neg]
    simp
include T hm hB hB' in
private theorem edgePreimage_of_pos (b : PosEdge L k m) :
    Tower.FullSpace.edgePreimage (intShift n) b.1 = (shiftEdge (-n) b).1 := by
  have h1 := shiftEdge_val n T hm hB (shiftEdge (-n) b)
  rw [shiftEdge_shiftEdge_neg n T hm hB hB'] at h1
  rw [h1, edgePreimage_edgeImage (T.sublattice m hm) (T.links m hm) T.inj]
end ShiftedEdges
private theorem initialField_shiftField (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (n : Fin 4 → ℤ) (T : ShiftFacts L k (intShift n))
    (hB : FullLatticeOverTorus.ShiftSurjectiveOnEdges L k 0 n)
    (hB' : FullLatticeOverTorus.ShiftSurjectiveOnEdges L k 0 (-n))
    (ζ : (colourEdges L k 0).Carrier → ℂ) :
    initialField (shiftField (colourEdges L k 0) n ζ) = pushField (intShift n) (initialField ζ) := by
  have ha := meshAt_pos hL k 0
  have hk0 : 0 ≤ k := Nat.zero_le _
  have hF : ∀ (b : Edge L k 0) (h : b.IsPositivelyOriented),
      edgeForm (shiftField (colourEdges L k 0) n ζ) b =
        edgeForm ζ (shiftEdge (-n) ⟨b, h⟩).1 := by
    intro b h
    rw [edgeForm_of_pos _ h, edgeForm_of_pos _ (shiftEdge (-n) ⟨b, h⟩).2]
    rfl
  funext b
  by_cases h : b.IsPositivelyOriented
  · have hi : Tower.FullSpace.edgePreimage (intShift n) b = (shiftEdge (-n) ⟨b, h⟩).1 :=
      edgePreimage_of_pos n T hk0 hB hB' ⟨b, h⟩
    simp only [pushField]
    rw [hi, initialField_of_pos _ h, initialField_of_pos _ (shiftEdge _ _).2, hF b h]
  · have hr : b.opposite.IsPositivelyOriented := (pos_or_opposite_pos b).resolve_left h
    have hi : Tower.FullSpace.edgePreimage (intShift n) b =
        (shiftEdge (-n) ⟨b.opposite, hr⟩).1.opposite := by
      have h1 := edgePreimage_of_pos n T hk0 hB hB' ⟨b.opposite, hr⟩
      have h2 := edgeImage_edgePreimage (T.sublattice 0 hk0) (T.links 0 hk0) T.inj b
      have h3 := edgeImage_opposite (T.sublattice 0 hk0) (T.links 0 hk0)
        (Tower.FullSpace.edgePreimage (intShift n) b)
      have h4 : Tower.FullSpace.edgePreimage (intShift n) b.opposite =
          (Tower.FullSpace.edgePreimage (intShift n) b).opposite := by
        have := edgePreimage_edgeImage (T.sublattice 0 hk0) (T.links 0 hk0) T.inj
          (Tower.FullSpace.edgePreimage (intShift n) b).opposite
        rw [h3, h2] at this
        exact this
      rw [← h1, h4]
      rfl
    have h2 : ¬ ((shiftEdge (-n) ⟨b.opposite, hr⟩).1.opposite).IsPositivelyOriented :=
      not_pos_opposite ha (shiftEdge _ _).2
    simp only [pushField]
    rw [hi, initialField_of_not_pos _ h, initialField_of_not_pos _ h2, hF _ hr]
    rfl
end Shifts
section FiniteValues
variable {F : PeriodicData} {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S)
private theorem isOpen_openPolydisk {N : ℕ} (ρ : ℝ) :
    IsOpen (openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
private theorem fieldExtend_add (w w' : Coordinates.ComplexCoordinates l) :
    fieldExtend e (w + w') = fieldExtend e w + fieldExtend e w' := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.fieldExtend_add <;> assumption
private theorem fieldExtend_smul (c : ℂ) (w : Coordinates.ComplexCoordinates l) :
    fieldExtend e (c • w) = c • fieldExtend e w := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.fieldExtend_smul <;> assumption
private theorem isSupBelow_fieldExtend {ρ : ℝ} (hρ : 0 < ρ) {w : Coordinates.ComplexCoordinates l}
    (hw : w ∈ openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ) :
    IsSupBelow F (fieldExtend e w) ρ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.isSupBelow_fieldExtend <;> assumption
end FiniteValues
private structure Inputs : Prop where
  hN : NormalizedMeanNearIdentity
  hZ : Tower.BlockPathContourPivotStatement
  hA : Tower.LeftChartFields.Claim
  hTr : Tower.Translations.TranslationProperties
  hP : FullLatticeOverTorus.FullLatticeOverTorusClaim
private structure Setting (L k : ℕ) (δ ρ : ℝ) : Prop where
  G : Inputs
  hL : Conventions.IsAdmissibleBlockingFactor L
  hk : 1 ≤ k
  F : StepProperties L k δ
  hδ : 0 < δ
  hρ : 0 < ρ
  small : ∀ m, m ≤ k → ∀ f : (colourEdges L k 0).Carrier → ℂ,
    IsSupBelow (colourEdges L k 0) f ρ → meanIterate (initialField f) m ∈ nearIdentityFields L k m δ
section Iterates
variable {L k : ℕ} {δ ρ : ℝ}
private theorem analyticAt_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x) (hu : IsUnit (Matrix.det (f x))) :
    AnalyticAt ℂ (fun y => (f y)⁻¹) x := by
  have e : (fun y => (f y)⁻¹) = Ring.inverse ∘ f := by
    funext y
    simp [Matrix.nonsing_inv_eq_ringInverse]
  have hu' : IsUnit (f x) := (Matrix.isUnit_iff_isUnit_det _).2 hu
  obtain ⟨u, hu2⟩ := hu'
  rw [e]
  exact AnalyticAt.comp (by rw [← hu2]; exact analyticAt_inverse (𝕜 := ℂ) u) hf
abbrev _root_.YangMills.SharedProofs.p7089 := @analyticAt_inv
private def edgeFormCLM {S : Set (colourEdges L k 0).Carrier} {l : ℕ} (e : Fin l ≃ S)
    (b : Edge L k 0) : Coordinates.ComplexCoordinates l →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => edgeForm (fieldExtend e w) b
      map_add' := fun w w' => by simp only [fieldExtend_add, edgeForm_add, Pi.add_apply]
      map_smul' := fun c w => by
        simp only [fieldExtend_smul, edgeForm_smul, Pi.smul_apply, RingHom.id_apply] }
private theorem matExp_edgeForm_analytic {S : Set (colourEdges L k 0).Carrier} {l : ℕ}
    (e : Fin l ≃ S) (b : Edge L k 0) (p : Coordinates.ComplexCoordinates l) :
    AnalyticAt ℂ (fun w => ComplexMatrix2.matExp (Complex.I • edgeForm (fieldExtend e w) b)) p := by
  let m : Coordinates.ComplexCoordinates l →L[ℂ] ComplexMatrix2 :=
    (Complex.I • ContinuousLinearMap.id ℂ ComplexMatrix2).comp (edgeFormCLM e b)
  exact AnalyticAt.comp (g := NormedSpace.exp) (f := m)
    (NormedSpace.exp_analytic (𝕂 := ℂ) (m p)) (m.analyticAt _)
private theorem meanIterate_analytic (C : Setting L k δ ρ) {S : Set (colourEdges L k 0).Carrier}
    {l : ℕ} (e : Fin l ≃ S) : ∀ m, m ≤ k →
      ∀ p ∈ openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ, ∀ b,
        AnalyticAt ℂ (fun w => meanIterate (initialField (fieldExtend e w)) m b) p := by
  intro m
  induction m with
  | zero =>
    intro _ p _ b
    by_cases hb : b.IsPositivelyOriented
    · exact (matExp_edgeForm_analytic e b p).congr
        (Eventually.of_forall fun w => (initialField_of_pos _ hb).symm)
    · have hr := (pos_or_opposite_pos b).resolve_left hb
      have hu : IsUnit (Matrix.det
          (ComplexMatrix2.matExp (Complex.I • edgeForm (fieldExtend e p) b.opposite))) := by
        have e' : Matrix.det
            (ComplexMatrix2.matExp (Complex.I • edgeForm (fieldExtend e p) b.opposite)) = 1 :=
          matExp_mem C.G.hA C.hL _ hr
        rw [e']
        exact isUnit_one
      exact (analyticAt_inv (matExp_edgeForm_analytic e b.opposite p) hu).congr
        (Eventually.of_forall fun w => (initialField_of_not_pos _ hb).symm)
  | succ m ih =>
    intro hm p hp
    have hev : ∀ᶠ w in 𝓝 p, meanIterate (initialField (fieldExtend e w)) m ∈
        nearIdentityFields L k m δ := by
      filter_upwards [(isOpen_openPolydisk ρ).mem_nhds hp] with w hw
      exact C.small m (by omega) _ (isSupBelow_fieldExtend e C.hρ hw)
    exact (C.F.analytic m (by omega) l _ p (ih (by omega) p hp) hev).1
private theorem meanIterate_local (C : Setting L k δ ρ) : ∀ m, m ≤ k → ∀ (b : Edge L k m)
    (f f' : (colourEdges L k 0).Carrier → ℂ), IsSupBelow (colourEdges L k 0) f ρ →
    IsSupBelow (colourEdges L k 0) f' ρ →
    (∀ κ : (colourEdges L k 0).Carrier,
      ‖((κ.2.1.initial : Vertex L k 0) : AmbientSpace) - (b.initial : AmbientSpace)‖ ≤
          3 * (m : ℝ) + 3 →
        f κ = f' κ) →
    meanIterate (initialField f) m b = meanIterate (initialField f') m b := by
  intro m
  induction m with
  | zero =>
    intro _ b f f' _ _ h
    have hpos : ∀ {b' : Edge L k 0}, b'.IsPositivelyOriented →
        ‖(b'.initial : AmbientSpace) - (b.initial : AmbientSpace)‖ ≤ 3 →
          edgeForm f b' = edgeForm f' b' := fun hb' hd => by
      rw [edgeForm_of_pos f hb', edgeForm_of_pos f' hb']
      exact Finset.sum_congr rfl fun a _ => by
        rw [h (a, ⟨_, hb'⟩) (by simpa using hd)]
    by_cases hb : b.IsPositivelyOriented
    · show initialField f b = initialField f' b
      rw [initialField_of_pos f hb, initialField_of_pos f' hb, hpos hb (by simp)]
    · have hr := (pos_or_opposite_pos b).resolve_left hb
      show initialField f b = initialField f' b
      rw [initialField_of_not_pos f hb, initialField_of_not_pos f' hb, hpos hr]
      have := edge_length_le_one C.hL (Nat.zero_le k) b
      show ‖(b.terminal : AmbientSpace) - (b.initial : AmbientSpace)‖ ≤ 3
      linarith
  | succ m ih =>
    intro hm c f f' hf hf' h
    have hm' : m < k := by omega
    have hV := C.small m hm'.le f hf
    have hV' := C.small m hm'.le f' hf'
    have key : ∀ c₀ : Edge L k (m + 1), c₀.IsPositivelyOriented →
        ‖(c₀.initial : AmbientSpace) - (c.initial : AmbientSpace)‖ ≤ 1 →
        normalizedMean (meanIterate (initialField f) m) c₀ =
          normalizedMean (meanIterate (initialField f') m) c₀ := by
      intro c₀ hc₀ hd
      refine ((C.F.forms m hm' _ hV).2.2.2 c₀ hc₀ _ hV' fun b hb => ?_).2.1
      refine ih hm'.le b f f' hf hf' fun κ hκ => h κ ?_
      have h1 := dist_initial_of_mem_doubleCube C.G.hZ C.hL hm' hc₀ hb.1
      have h2 : ‖((κ.2.1.initial : Vertex L k 0) : AmbientSpace) - (c.initial : AmbientSpace)‖ ≤
          ‖((κ.2.1.initial : Vertex L k 0) : AmbientSpace) - (b.initial : AmbientSpace)‖ +
            (‖(b.initial : AmbientSpace) - (c₀.initial : AmbientSpace)‖ +
              ‖(c₀.initial : AmbientSpace) - (c.initial : AmbientSpace)‖) := by
        have e : ((κ.2.1.initial : Vertex L k 0) : AmbientSpace) - (c.initial : AmbientSpace) =
            (((κ.2.1.initial : Vertex L k 0) : AmbientSpace) - (b.initial : AmbientSpace)) +
              (((b.initial : AmbientSpace) - (c₀.initial : AmbientSpace)) +
                ((c₀.initial : AmbientSpace) - (c.initial : AmbientSpace))) := by
          abel
        rw [e]
        exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      push_cast
      linarith
    show nextMeanIterate (meanIterate (initialField f) m) c =
      nextMeanIterate (meanIterate (initialField f') m) c
    unfold nextMeanIterate
    by_cases hc : c.IsPositivelyOriented
    · rw [if_pos hc, if_pos hc]
      exact key c hc (by simp)
    · rw [if_neg hc, if_neg hc, key c.opposite ((pos_or_opposite_pos c).resolve_left hc)
        (edge_length_le_one C.hL (by omega) c)]
private theorem meanIterate_shiftField (C : Setting L k δ ρ) (n : Fin 4 → ℤ) : ∀ m, m ≤ k →
    ∀ f : (colourEdges L k 0).Carrier → ℂ, IsSupBelow (colourEdges L k 0) f ρ →
      meanIterate (initialField (shiftField (colourEdges L k 0) n f)) m =
        pushField (intShift n) (meanIterate (initialField f) m) := by
  intro m
  induction m with
  | zero =>
    intro _ f _
    have hP := C.G.hP L C.hL k 0 (Nat.zero_le _) 1 one_pos
    exact initialField_shiftField C.hL C.hk n (intShift_shiftFacts C.G.hZ C.G.hTr C.hL C.hk n)
      (hP.2.2.1 n).2.1 (hP.2.2.1 (-n)).2.1 f
  | succ m ih =>
    intro hm f hf
    show nextMeanIterate (meanIterate (initialField (shiftField (colourEdges L k 0) n f)) m) = _
    rw [ih (by omega) f hf]
    exact (C.F.shift m (by omega) n _ (C.small m (by omega) f hf)).1
end Iterates
section CompactFields
variable {L k : ℕ} {δ ρ : ℝ}
private theorem pauliFamily_mem_hermitianTraceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
private theorem edgeForm_mem_edgeFormSpace (hL : Conventions.IsAdmissibleBlockingFactor L)
    {f : (colourEdges L k 0).Carrier → ℂ} (hf : ∀ κ, (f κ).im = 0) :
    edgeForm f ∈ edgeFormSpace (meshAt L k 0) := by
  refine ⟨fun b hb => ?_, edgeForm_opposite hL f⟩
  rw [edgeForm_of_pos f hb]
  refine Submodule.sum_mem _ fun a _ => ?_
  have e : f (a, ⟨b, hb⟩) = (((f (a, ⟨b, hb⟩)).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simpa using hf (a, ⟨b, hb⟩))
  rw [e, ← real_smul_eq_ofReal_smul]
  exact Submodule.smul_mem _ _ (pauliFamily_mem_hermitianTraceless a)
private theorem inv_mem_specialUnitary {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem initialField_compact (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {f : (colourEdges L k 0).Carrier → ℂ}
    (hf : ∀ κ, (f κ).im = 0) (b : Edge L k 0) :
    initialField f b ∈ PeriodicLattice.compactGaugeGroup := by
  have hone : (1 : Edge L k 0 → ComplexMatrix2) ∈
      Tower.FullSpace.fieldsValuedIn L k 0 PeriodicLattice.compactGaugeGroup :=
    ⟨fun b => ComplexMatrix2.specialUnitary.one_mem, fun b => by simp⟩
  have hgp : ∀ b' : Edge L k 0, b'.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • edgeForm f b') ∈ PeriodicLattice.compactGaugeGroup :=
    fun b' hb => by
      have h := (((hA.2.2 L k 0 hL (Nat.zero_le _)).2.1.1).1 1 hone (edgeForm f)
        (edgeForm_mem_edgeFormSpace hL hf) ⟨b', hb⟩).1 1
      have h' : ComplexMatrix2.matExp (Complex.I • (((1 : ℝ) : ℂ) • edgeForm f b')) *
          (1 : ComplexMatrix2) ∈ PeriodicLattice.compactGaugeGroup := h
      rwa [Complex.ofReal_one, one_smul, mul_one] at h'
  by_cases hb : b.IsPositivelyOriented
  · rw [initialField_of_pos f hb]
    exact hgp b hb
  · rw [initialField_of_not_pos f hb]
    exact inv_mem_specialUnitary (hgp _ ((pos_or_opposite_pos b).resolve_left hb))
private theorem meanIterate_compact (C : Setting L k δ ρ) {f : (colourEdges L k 0).Carrier → ℂ}
    (hb : IsSupBelow (colourEdges L k 0) f ρ) (hf : ∀ κ, (f κ).im = 0) :
    ∀ m, m ≤ k → ∀ b, meanIterate (initialField f) m b ∈ PeriodicLattice.compactGaugeGroup := by
  intro m
  induction m with
  | zero => exact fun _ b => initialField_compact C.G.hA C.hL hf b
  | succ m ih =>
    intro hm
    exact (C.F.compact m (by omega) _ (C.small m (by omega) f hb) (ih (by omega))).1
end CompactFields
end FieldIterates
open FieldIterates in
theorem fieldIteratesNearIdentity_holds (hN : NormalizedMeanNearIdentity)
    (hAn : MeanStepAnalytic) (hF : MeanStepOnForms)
    (hT : MeanStepShiftCovariant) (hR : MeanStepAtCompactFields)
    (hS : Tower.SmoothingNearIdentity)
    (hZ : Tower.BlockPathContourPivotStatement)
    (hA : Tower.LeftChartFields.Claim)
    (hTr : Tower.Translations.TranslationProperties)
    (hP : FullLatticeOverTorus.FullLatticeOverTorusClaim) :
    FieldIteratesNearIdentity := by
  intro L hL
  obtain ⟨δ₀, h₀, H⟩ := exists_stepProperties hAn hF hT hR hS hL
  refine ⟨δ₀, h₀, fun δ hδ hle k hk => ?_⟩
  obtain ⟨ρ, hρ, hsm⟩ := exists_uniform_radius (k := k) hN hA hL hδ
  have C : Setting L k δ ρ := ⟨⟨hN, hZ, hA, hTr, hP⟩, hL, hk, H δ hle k, hδ, hρ, hsm⟩
  exact ⟨ρ, hρ, hsm, fun S l e => meanIterate_analytic C e, meanIterate_local C,
    fun n => meanIterate_shiftField C n, fun f hb hf => meanIterate_compact C hb hf⟩
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
