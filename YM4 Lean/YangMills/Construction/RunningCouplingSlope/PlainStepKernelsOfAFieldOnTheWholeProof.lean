import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.Towers.TheThreeKernelsAreRealAtRealConfigurationsProof
import YangMills.Construction.RunningCouplingSlope.PlainIteratesOfAFieldOnTheWholeProof
import YangMills.Construction.RunningCouplingSlope.PlainStepKernelsOfAFieldOnTheWhole
import YangMills.Construction.Towers.IteratesAreHolomorphicInTheFormAtTheSideInfinityProof
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.TheMapsOfOneStepKeepRealFunctions
import YangMills.Construction.Towers.TheResponseOperatorsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
namespace KernelLocality
open YangMills.Construction.Matrices YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
section Kernels
variable {N N' : Type}
private def basisFn (ι : N) : N → ℂ := open Classical in fun x => if x = ι then 1 else 0
private theorem basisFn_self (ι : N) : basisFn ι ι = 1 := by simp [basisFn]
private theorem basisFn_of_ne {ι x : N} (h : x ≠ ι) : basisFn ι x = 0 := by simp [basisFn, h]
private theorem kernel_eq_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) (ι' : N') (ι : N) : T ι' ι = M (basisFn ι) ι' := by apply _root_.YangMills.Construction.Tower.FreeOperators.kernel_eq_apply_indicator <;> assumption
private structure IsRowLocal (M : (N → ℂ) → N' → ℂ) (R : N' → Set N) : Prop where
  add : ∀ f g, M (f + g) = M f + M g
  smul : ∀ (w : ℂ) f, M (w • f) = w • M f
  standingConstraints : ∀ ι', (R ι').Finite
  reads : ∀ f ι', (∀ ι ∈ R ι', f ι = 0) → M f ι' = 0
private def basisKernel (M : (N → ℂ) → N' → ℂ) : KernelMatrix N N' :=
  fun ι' ι => M (basisFn ι) ι'
namespace IsRowLocal
variable {M : (N → ℂ) → N' → ℂ} {R : N' → Set N}
private theorem basisKernel_eq_zero (h : IsRowLocal M R) {ι : N} {ι' : N'} (hι : ι ∉ R ι') :
    basisKernel M ι' ι = 0 := by
  refine h.reads _ _ fun ι₂ h₂ => ?_
  refine basisFn_of_ne ?_
  rintro rfl
  exact hι h₂
private theorem rowFinite (h : IsRowLocal M R) : RowFinite (basisKernel M) := fun ι' =>
  (h.standingConstraints ι').subset fun ι hι => by
    by_contra h'
    exact hι (h.basisKernel_eq_zero h')
private theorem applySummable {T : KernelMatrix N N'} (hT : RowFinite T) (f : N → ℂ) :
    ApplySummable T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applySummable_of_rowFinite <;> assumption
private theorem represents (h : IsRowLocal M R) : Represents (basisKernel M) M := by
  classical
  intro f
  refine ⟨applySummable h.rowFinite f, ?_⟩
  funext ι'
  let Ml : (N → ℂ) →ₗ[ℂ] (N' → ℂ) := ⟨⟨M, h.add⟩, h.smul⟩
  let F : Finset N := (h.standingConstraints ι').toFinset
  let g : N → ℂ := ∑ ι ∈ F, f ι • basisFn ι
  have hg : ∀ ι ∈ R ι', (f - g) ι = 0 := by
    intro ι hι
    have hF : ι ∈ F := (h.standingConstraints ι').mem_toFinset.2 hι
    have : g ι = f ι := by
      simp only [g, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single ι]
      · simp [basisFn_self]
      · intro b _ hb
        simp [basisFn_of_ne hb.symm]
      · exact fun h' => absurd hF h'
    simp [this]
  have e1 : Ml (f - g) ι' = 0 := h.reads _ _ hg
  have e2 : M f ι' = Ml g ι' := by
    have : Ml f ι' - Ml g ι' = 0 := by
      rw [map_sub] at e1
      simpa using e1
    exact sub_eq_zero.1 this
  have e3 : Ml g ι' = ∑ ι ∈ F, basisKernel M ι' ι * f ι := by
    simp only [g, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [mul_comm]
    rfl
  rw [e2, e3]
  unfold applyKernel
  refine tsum_eq_sum fun ι hι => ?_
  rw [h.basisKernel_eq_zero fun h' => hι ((h.standingConstraints ι').mem_toFinset.2 h'), zero_mul]
private theorem kernelOfMap_spec (h : IsRowLocal M R) :
    Represents (kernelOfMap M) M ∧ RowFinite (kernelOfMap M) ∧
      ∀ ι' ι, kernelOfMap M ι' ι = M (basisFn ι) ι' := by
  have hg : Represents (kernelOfMap M) M :=
    Classical.epsilon_spec (p := fun T => Represents T M) ⟨_, h.represents⟩
  have he : ∀ ι' ι, kernelOfMap M ι' ι = M (basisFn ι) ι' := kernel_eq_of_represents hg
  refine ⟨hg, fun ι' => (h.standingConstraints ι').subset fun ι hι => ?_, he⟩
  by_contra h'
  apply hι
  rw [he]
  exact h.basisKernel_eq_zero h'
end IsRowLocal
end Kernels
section Coefficients
private def coeffLinear (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
  map_add' X Y := by
    fin_cases a <;> simp <;> ring
  map_smul' c X := by
    fin_cases a <;> simp <;> ring
private def coeffCLM (a : Fin 3) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (coeffLinear a)
private theorem pauliCoeff_eq_coeffCLM (a : Fin 3) {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.traceless) : pauliCoeff a X = coeffCLM a X := by
  unfold pauliCoeff
  rw [dif_pos h]
  rfl
private theorem pauliFamily_mem (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem real_smul_eq_ofReal_smul (x : ℝ) (X : ComplexMatrix2) : x • X = (x : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
private theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
private theorem ofPauliCoeffs_add {σ : Type} (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (c + c') = ofPauliCoeffs c + ofPauliCoeffs c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_add <;> assumption
private theorem ofPauliCoeffs_smul {σ : Type} (w : ℂ) (c : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (w • c) = w • ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_smul <;> assumption
end Coefficients
section Forms
variable {L k i : ℕ}
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k m : ℕ) :
    0 < meshAt L k m := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private theorem isPos_or_opposite_isPos {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
private theorem not_opposite_isPos {a : ℝ} (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
private def colourForm (ζ : (colourEdges L k i).Carrier → ℂ) : FullSpace.Edge L k i → ComplexMatrix2 :=
  (FullSpace.edgePauliCoordinates L k i).ofCoeffs ζ
private theorem colourForm_of_pos (ζ : (colourEdges L k i).Carrier → ℂ) {b : FullSpace.Edge L k i}
    (h : b.IsPositivelyOriented) :
    colourForm ζ b = ∑ a, ζ (a, ⟨b, h⟩) • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.DeltaSharedProofs.p500947 <;> assumption
private theorem colourForm_of_not_pos (ζ : (colourEdges L k i).Carrier → ℂ)
    {b : FullSpace.Edge L k i} (h : ¬ b.IsPositivelyOriented) :
    colourForm ζ b = -colourForm ζ b.opposite := by apply _root_.YangMills.DeltaSharedProofs.p500478 <;> assumption
private theorem colourForm_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ζ : (colourEdges L k i).Carrier → ℂ) (b : FullSpace.Edge L k i) :
    colourForm ζ b.opposite = -colourForm ζ b := by apply _root_.YangMills.DeltaSharedProofs.p501817 <;> assumption
private theorem colourForm_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ζ : (colourEdges L k i).Carrier → ℂ) :
    colourForm ζ ∈ FullSpace.complexEdgeForms (meshAt L k i) := by apply _root_.YangMills.DeltaSharedProofs.p502175 <;> assumption
private theorem colourForm_add (ζ ζ' : (colourEdges L k i).Carrier → ℂ) :
    colourForm (ζ + ζ') = colourForm ζ + colourForm ζ' := by apply _root_.YangMills.DeltaSharedProofs.p502563 <;> assumption
private theorem colourForm_smul (c : ℂ) (ζ : (colourEdges L k i).Carrier → ℂ) :
    colourForm (c • ζ) = c • colourForm ζ := by apply _root_.YangMills.DeltaSharedProofs.p501730 <;> assumption
private theorem colourForm_eqOn (ζ ζ' : (colourEdges L k i).Carrier → ℂ)
    {S : Set (FullSpace.Edge L k i)} (hS : ∀ b ∈ S, b.opposite ∈ S)
    (h : ∀ b ∈ S, ∀ (hb : b.IsPositivelyOriented) (a : Fin 3),
      ζ (a, ⟨b, hb⟩) = ζ' (a, ⟨b, hb⟩)) :
    EqOn (colourForm ζ) (colourForm ζ') S := by
  have hp : ∀ b ∈ S, b.IsPositivelyOriented → colourForm ζ b = colourForm ζ' b := by
    intro b hbS hb
    simp only [colourForm_of_pos _ hb, h b hbS hb]
  intro b hbS
  by_cases hb : b.IsPositivelyOriented
  · exact hp b hbS hb
  · have hr : b.opposite.IsPositivelyOriented := (isPos_or_opposite_isPos b).resolve_left hb
    rw [colourForm_of_not_pos _ hb, colourForm_of_not_pos _ hb, hp _ (hS b hbS) hr]
end Forms
section Distances
variable {L k : ℕ}
private theorem euclidNormVec_le {x : AmbientSpace} {r : ℝ} (h : ‖x‖ ≤ r) :
    euclidNormVec x ≤ 2 * r := by
  have hr : 0 ≤ r := (norm_nonneg _).trans h
  have hc : ∀ μ, x μ ^ 2 ≤ r ^ 2 := fun μ => by
    have h1 : |x μ| ≤ r := (norm_le_pi_norm x μ).trans h
    exact sq_le_sq' (by linarith [(abs_le.1 h1).1]) (abs_le.1 h1).2
  unfold euclidNormVec
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ μ, x μ ^ 2 ≤ ∑ _μ : Fin 4, r ^ 2 := Finset.sum_le_sum fun μ _ => hc μ
    _ = (2 * r) ^ 2 := by
        simp
        ring
private theorem norm_sub_le_of_mem_doubleCube (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hm : m < k)
    {c : FullSpace.Edge L k (m + 1)} (hc : c.IsPositivelyOriented) {x : AmbientSpace}
    (hx : x ∈ FullSpace.doubleCube L (meshAt L k m) c) :
    ‖x - (c.initial : AmbientSpace)‖ ≤ 3 / 2 := by apply _root_.YangMills.SharedProofs.p114653 <;> assumption
end Distances
section Small
variable {L k : ℕ}
private theorem nearIdentityFields_mono {m : ℕ} {δ δ' : ℝ} (h : δ ≤ δ') :
    nearIdentityFields L k m δ ⊆ nearIdentityFields L k m δ' :=
  fun _ hV => ⟨hV.1, fun b => (hV.2 b).trans_le h⟩
private abbrev expField (f : (colourEdges L k 0).Carrier → ℂ) : FullSpace.Edge L k 0 → ComplexMatrix2 :=
  FullSpace.BackgroundJets.gaugeFieldOfForm L k f
end Small
section Facts
private structure OneStepFacts (L k : ℕ) (δ : ℝ) : Prop where
  analytic : ∀ m : ℕ, m < k → ∀ (l : ℕ)
      (W : Coordinates.ComplexCoordinates l → FullSpace.Edge L k m → ComplexMatrix2)
      (p : Coordinates.ComplexCoordinates l), (∀ b, AnalyticAt ℂ (fun w => W w b) p) →
      (∀ᶠ w in 𝓝 p, W w ∈ nearIdentityFields L k m δ) →
      (∀ c, AnalyticAt ℂ (fun w => nextMeanIterate (W w) c) p) ∧
      (∀ c : FullSpace.Edge L k (m + 1), c.IsPositivelyOriented →
        AnalyticAt ℂ (fun w => (meanRadius (W w) c)⁻¹) p) ∧
      (∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m), ∀ c,
        AnalyticAt ℂ (fun w => meanCovariantStep (W w) B c) p) ∧
      ∀ (y : FullSpace.Vertex L k (m + 1)) (x : FullSpace.Vertex L k m),
        x ∈ FullSpace.cubeVertices L (meshAt L k m) y →
        AnalyticAt ℂ (fun w => FullSpace.complexContourMean L (W w) y x) p
  forms : ∀ m : ℕ, m < k → ∀ V ∈ nearIdentityFields L k m δ,
      (∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m),
        meanCovariantStep V B ∈ FullSpace.complexEdgeForms (meshAt L k (m + 1))) ∧
      (∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m),
        ∀ B' ∈ FullSpace.complexEdgeForms (meshAt L k m), ∀ w : ℂ,
          meanCovariantStep V (w • B + B') =
            w • meanCovariantStep V B + meanCovariantStep V B') ∧
      (∀ c : FullSpace.Edge L k (m + 1), c.IsPositivelyOriented →
        ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m),
        (∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k m) c, B b = 0) →
          meanCovariantStep V B c = 0) ∧
      ∀ c : FullSpace.Edge L k (m + 1), c.IsPositivelyOriented →
        ∀ V' ∈ nearIdentityFields L k m δ,
        (∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k m) c, V b = V' b) →
          meanRadius V c = meanRadius V' c ∧ normalizedMean V c = normalizedMean V' c ∧
          (∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m),
            meanCovariantStep V B c = meanCovariantStep V' B c) ∧
          ∀ y : FullSpace.Vertex L k (m + 1), (y = c.initial ∨ y = c.terminal) →
            ∀ x ∈ FullSpace.cubeVertices L (meshAt L k m) y,
              FullSpace.complexContourMean L V y x = FullSpace.complexContourMean L V' y x
  transl : ∀ m : ℕ, m < k → ∀ n : Fin 4 → ℤ, ∀ V ∈ nearIdentityFields L k m δ,
      nextMeanIterate (FullSpace.pushField (intShift n) V) =
          FullSpace.pushField (intShift n) (nextMeanIterate V) ∧
      ∀ c : FullSpace.Edge L k (m + 1), c.IsPositivelyOriented →
        meanRadius (FullSpace.pushField (intShift n) V) (FullSpace.edgeImage (intShift n) c) =
            meanRadius V c ∧
        ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m),
          meanCovariantStep (FullSpace.pushField (intShift n) V)
              (FullSpace.isometryOnTangent (intShift n) V B)
              (FullSpace.edgeImage (intShift n) c) =
            meanCovariantStep V B c
  real : ∀ m : ℕ, m < k → ∀ V ∈ nearIdentityFields L k m δ,
      (∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) →
      (∀ c, nextMeanIterate V c ∈ PeriodicLattice.compactGaugeGroup) ∧
      (∀ c : FullSpace.Edge L k (m + 1), c.IsPositivelyOriented → (meanRadius V c).im = 0) ∧
      ∀ B ∈ FullSpace.edgeFormSpace (meshAt L k m), ∀ c,
        meanCovariantStep V B c ∈ ComplexMatrix2.hermitianTraceless
  radius : δ ≤ polydiscRadius L
private theorem exists_oneStepFacts (hAn : MeanStepAnalytic)
    (hF : MeanStepOnForms) (hT : MeanStepShiftCovariant)
    (hR : MeanStepAtCompactFields)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ ≤ δ₀ → ∀ k : ℕ, OneStepFacts L k δ := by
  obtain ⟨δ₂, h₂, H₂⟩ := hAn L hL
  obtain ⟨δ₃, h₃, H₃⟩ := hF L hL
  obtain ⟨δ₄, h₄, H₄⟩ := hT L hL
  obtain ⟨δ₅, h₅, H₅⟩ := hR L hL
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  refine ⟨min (min δ₂ δ₃) (min (min δ₄ δ₅) (polydiscRadius L)),
    lt_min (lt_min h₂ h₃) (lt_min (lt_min h₄ h₅) hρ), fun δ hδ k => ?_⟩
  have l₂ : δ ≤ δ₂ := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have l₃ : δ ≤ δ₃ := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have l₄ : δ ≤ δ₄ := hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have l₅ : δ ≤ δ₅ := hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
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
end Facts
section OneLattice
variable {a : ℝ} {f : AmbientSpace → AmbientSpace}
private theorem coe_vertexImage (hM : FullSpace.MapsSublatticeOnto a f)
    (x : InfiniteLattice.LatticePoint a) :
    ((FullSpace.vertexImage f x : InfiniteLattice.LatticePoint a) : AmbientSpace) = f x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_space_vertexImage <;> assumption
private theorem apply_vertexPreimage (hM : FullSpace.MapsSublatticeOnto a f)
    (x : InfiniteLattice.LatticePoint a) :
    f (FullSpace.vertexPreimage f x : InfiniteLattice.LatticePoint a) = x := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingInvariance.vertexPreimage_spec <;> assumption
private theorem vertexImage_vertexPreimage (hM : FullSpace.MapsSublatticeOnto a f)
    (x : InfiniteLattice.LatticePoint a) :
    FullSpace.vertexImage f (FullSpace.vertexPreimage f x) = x :=
  Subtype.ext ((coe_vertexImage hM _).trans (apply_vertexPreimage hM x))
private theorem vertexPreimage_vertexImage (hM : FullSpace.MapsSublatticeOnto a f)
    (hi : Function.Injective f) (x : InfiniteLattice.LatticePoint a) :
    FullSpace.vertexPreimage f (FullSpace.vertexImage f x) = x :=
  Subtype.ext (hi ((apply_vertexPreimage hM _).trans (coe_vertexImage hM x)))
private theorem edgeImage_spec (hM : FullSpace.MapsSublatticeOnto a f)
    (hB : FullSpace.MapsLinksOnto a f) (b : InfiniteLattice.Link a) :
    (FullSpace.edgeImage f b).initial = FullSpace.vertexImage f b.initial ∧
      (FullSpace.edgeImage f b).terminal = FullSpace.vertexImage f b.terminal := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_endpoints <;> assumption
private theorem edgePreimage_spec (hM : FullSpace.MapsSublatticeOnto a f)
    (hB : FullSpace.MapsLinksOnto a f) (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    (FullSpace.edgePreimage f b).initial = FullSpace.vertexPreimage f b.initial ∧
      (FullSpace.edgePreimage f b).terminal = FullSpace.vertexPreimage f b.terminal := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgePreimage_endpoints <;> assumption
private theorem edgePreimage_edgeImage (hM : FullSpace.MapsSublatticeOnto a f)
    (hB : FullSpace.MapsLinksOnto a f) (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    FullSpace.edgePreimage f (FullSpace.edgeImage f b) = b := by
  obtain ⟨t, h⟩ := edgeImage_spec hM hB b
  obtain ⟨t', h'⟩ := edgePreimage_spec hM hB hi (FullSpace.edgeImage f b)
  refine InfiniteLattice.Link.ext ?_ ?_
  · rw [t', t, vertexPreimage_vertexImage hM hi]
  · rw [h', h, vertexPreimage_vertexImage hM hi]
end OneLattice
private structure TranslationData (L k : ℕ) (f : AmbientSpace → AmbientSpace) : Prop where
  lattice : ∀ i ≤ k, FullSpace.MapsSublatticeOnto (meshAt L k i) f
  bonds : ∀ i ≤ k, FullSpace.MapsLinksOnto (meshAt L k i) f
  inj : Function.Injective f
  isom : FullSpace.IsDistancePreserving f
  add : ∀ p q : AmbientSpace, f (p + q) = f p + q
section Translations
variable {L k j : ℕ} {f : AmbientSpace → AmbientSpace}
open YangMills.Construction.FullLatticeOverTorus (ShiftSurjectiveOnEdges ShiftSurjectiveOnVertices)
private theorem cubeVertices_bijOn (hM : FullSpace.MapsSublatticeOnto (meshAt L k j) f)
    (hi : Function.Injective f)
    (hZ : ∀ y : FullSpace.Vertex L k (j + 1), f '' FullSpace.cube L (meshAt L k j) y =
      FullSpace.cube L (meshAt L k j) (FullSpace.vertexImage f y))
    (y : FullSpace.Vertex L k (j + 1)) :
    BijOn (FullSpace.vertexImage f : FullSpace.Vertex L k j → FullSpace.Vertex L k j)
      (FullSpace.cubeVertices L (meshAt L k j) y)
      (FullSpace.cubeVertices L (meshAt L k j) (FullSpace.vertexImage f y)) := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.cubeVertices_bijOn <;> assumption
private theorem cube_image (hB : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (T : TranslationData L k f) (y : FullSpace.Vertex L k (j + 1)) :
    f '' FullSpace.cube L (meshAt L k j) y =
      FullSpace.cube L (meshAt L k j) (FullSpace.vertexImage f y) :=
  (hB L k (j + 1) hL (by omega) (by omega) (by omega)).2.2.2.2 f T.isom
    (T.lattice _ (by omega)) y
private theorem intShift_data (hZ : BlockPathContourPivotStatement)
    (hTr : Translations.TranslationProperties) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (n : Fin 4 → ℤ) : TranslationData L k (intShift n) := by
  have hT := (hTr L hL k k le_rfl).2.2.2.1 n
  have hCt := ((hZ L hL k 0 k hk (Nat.zero_le _) le_rfl).2.2.2.2.2.2 hk).1
  have hMk : FullSpace.MapsSublatticeOnto (meshAt L k k) (intShift n) := hT.2.1 k le_rfl
  have hv : castVec n ∈ (InfiniteLattice.latticeSubgroup (meshAt L k k) : Set AmbientSpace) := by
    have h0 : intShift n 0 ∈ intShift n '' (InfiniteLattice.latticeSubgroup (meshAt L k k) :
        Set AmbientSpace) := ⟨0, (InfiniteLattice.latticeSubgroup _).zero_mem, rfl⟩
    rw [show intShift n '' (InfiniteLattice.latticeSubgroup (meshAt L k k) :
      Set AmbientSpace) = InfiniteLattice.latticeSubgroup (meshAt L k k) from hMk] at h0
    simpa [intShift] using h0
  exact { lattice := fun i hi => hT.2.1 i hi
          bonds := fun i hi => (hCt.mapsSublatticeAndLinks ⟨castVec n, hv⟩ i hi).2
          inj := hT.2.2.1.injective
          isom := hT.1
          add := fun p q => by
            show p + q + castVec n = p + castVec n + q
            abel }
private theorem castVec_neg (n : Fin 4 → ℤ) : castVec (-n) = -castVec n := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.castVec_neg <;> assumption
section Shifts
variable (n : Fin 4 → ℤ) (T : TranslationData L k (intShift n)) (hj : j ≤ k)
  (hB : ShiftSurjectiveOnEdges L k j n) (hB' : ShiftSurjectiveOnEdges L k j (-n))
include T hj hB in
private theorem shiftEdge_val (c : PosEdge L k j) :
    (shiftEdge n c).1 = FullSpace.edgeImage (intShift n) c.1 := by
  have hM := T.lattice j hj
  obtain ⟨t, h⟩ := edgeImage_spec hM (T.bonds j hj) c.1
  refine InfiniteLattice.Link.ext ?_ ?_
  · rw [t]
    apply Subtype.ext
    rw [coe_vertexImage hM]
    exact (hB.2 c).1
  · rw [h]
    apply Subtype.ext
    rw [coe_vertexImage hM]
    exact (hB.2 c).2
include T hj hB hB' in
private theorem shiftEdge_neg_shiftEdge (c : PosEdge L k j) :
    shiftEdge (-n) (shiftEdge n c) = c := by
  apply Subtype.ext
  apply InfiniteLattice.Link.ext
  · apply Subtype.ext
    rw [(hB'.2 _).1, (hB.2 _).1, castVec_neg]
    simp
  · apply Subtype.ext
    rw [(hB'.2 _).2, (hB.2 _).2, castVec_neg]
    simp
include T hj hB hB' in
private theorem shiftEdge_shiftEdge_neg (c : PosEdge L k j) :
    shiftEdge n (shiftEdge (-n) c) = c := by
  apply Subtype.ext
  apply InfiniteLattice.Link.ext
  · apply Subtype.ext
    rw [(hB.2 _).1, (hB'.2 _).1, castVec_neg]
    simp
  · apply Subtype.ext
    rw [(hB.2 _).2, (hB'.2 _).2, castVec_neg]
    simp
include T hj hB hB' in
private theorem edgePreimage_of_pos (b : PosEdge L k j) :
    FullSpace.edgePreimage (intShift n) b.1 = (shiftEdge (-n) b).1 := by
  have h1 := shiftEdge_val n T hj hB (shiftEdge (-n) b)
  rw [shiftEdge_shiftEdge_neg n T hj hB hB'] at h1
  rw [h1, edgePreimage_edgeImage (T.lattice j hj) (T.bonds j hj) T.inj]
end Shifts
private theorem basisFn_map {N : Type} {s s' : N → N} (h : ∀ x, s' (s x) = x)
    (h' : ∀ x, s (s' x) = x) (ι x : N) : basisFn (s ι) x = basisFn ι (s' x) := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.basisFun_comp <;> assumption
private theorem isometryOnTangent_apply {a : ℝ} (f : AmbientSpace → AmbientSpace)
    (U B : InfiniteLattice.Link a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) (hi : (FullSpace.edgePreimage f b).IsPositivelyOriented) :
    FullSpace.isometryOnTangent f U B b = B (FullSpace.edgePreimage f b) := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.isometryOnTangent_apply_of_pos <;> assumption
private theorem colourForm_basisFn_translate (n : Fin 4 → ℤ) (T : TranslationData L k (intShift n))
    (hj : j ≤ k) (hB : ShiftSurjectiveOnEdges L k j n) (hB' : ShiftSurjectiveOnEdges L k j (-n))
    (U : FullSpace.Edge L k j → ComplexMatrix2) (ι : (colourEdges L k j).Carrier) :
    colourForm (basisFn ((colourEdges L k j).translate n ι)) =
      FullSpace.isometryOnTangent (intShift n) U (colourForm (basisFn ι)) := by
  have hinv : ∀ x : (colourEdges L k j).Carrier,
      (colourEdges L k j).translate (-n) ((colourEdges L k j).translate n x) = x := fun x =>
    Prod.ext rfl (shiftEdge_neg_shiftEdge n T hj hB hB' x.2)
  have hinv' : ∀ x : (colourEdges L k j).Carrier,
      (colourEdges L k j).translate n ((colourEdges L k j).translate (-n) x) = x := fun x =>
    Prod.ext rfl (shiftEdge_shiftEdge_neg n T hj hB hB' x.2)
  have hp : ∀ (b : FullSpace.Edge L k j), b.IsPositivelyOriented →
      colourForm (basisFn ((colourEdges L k j).translate n ι)) b =
        FullSpace.isometryOnTangent (intShift n) U (colourForm (basisFn ι)) b := by
    intro b h
    have hi : FullSpace.edgePreimage (intShift n) b = (shiftEdge (-n) ⟨b, h⟩).1 :=
      edgePreimage_of_pos n T hj hB hB' ⟨b, h⟩
    have hi' : (FullSpace.edgePreimage (intShift n) b).IsPositivelyOriented := by
      rw [hi]
      exact (shiftEdge _ _).2
    rw [isometryOnTangent_apply _ _ _ h hi', hi, colourForm_of_pos _ h,
      colourForm_of_pos _ (shiftEdge (-n) ⟨b, h⟩).2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [basisFn_map hinv hinv' ι (a, ⟨b, h⟩)]
    rfl
  funext b
  by_cases h : b.IsPositivelyOriented
  · exact hp b h
  · have hr : b.opposite.IsPositivelyOriented := (isPos_or_opposite_isPos b).resolve_left h
    rw [colourForm_of_not_pos _ h, hp _ hr]
    simp only [FullSpace.isometryOnTangent, FullSpace.extendOddly, if_neg h, if_pos hr]
end Translations
section Values
variable {F : PeriodicData} {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S)
private theorem isOpen_openPolydisk {N : ℕ} (ρ : ℝ) :
    IsOpen (openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
private theorem isSupBelow_fieldExtend {ρ : ℝ} (hρ : 0 < ρ) {z : Coordinates.ComplexCoordinates l}
    (hz : z ∈ openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ) :
    IsSupBelow F (fieldExtend e z) ρ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.isSupBelow_fieldExtend <;> assumption
private theorem fieldValues_mem_openPolydisk {ρ : ℝ} {ζ : F.Carrier → ℂ} (h : IsSupBelow F ζ ρ) :
    fieldValues e ζ ∈ openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.fieldValues_mem_openPolydisk <;> assumption
private theorem fieldExtend_fieldValues (ζ : F.Carrier → ℂ) {κ : F.Carrier} (hκ : κ ∈ S) :
    fieldExtend e (fieldValues e ζ) κ = ζ κ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.fieldExtend_fieldValues <;> assumption
private theorem isSupBelow_shiftField {ζ : F.Carrier → ℂ} {r : ℝ} (h : IsSupBelow F ζ r)
    (n : Fin 4 → ℤ) : IsSupBelow F (shiftField F n ζ) r := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.isSupBelow_shiftField <;> assumption
private theorem isHolomorphicIn_of_analyticAt {N N' : ℕ} {U : Set (Coordinates.ComplexCoordinates N)}
    {φ : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'} (hU : IsOpen U)
    (h : ∀ w ∈ U, AnalyticAt ℂ φ w) : Coordinates.ComplexCoordinates.IsHolomorphicIn U φ := by apply _root_.YangMills.Construction.Tower.FullSpace.IterHolomorphy.isHolomorphicIn_of_analyticAt <;> assumption
private theorem isLocalWith_of_entries {I I' : PeriodicData}
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    {ρ R : ℝ} (hρ : 0 < ρ) (hfin : ∀ y, (nearIndices F y R).Finite)
    (far : ∀ ζ, IsSupBelow F ζ ρ → ∀ ι' ι,
      ¬ euclidNormVec (I.pos ι - I'.pos ι') ≤ R → T ζ ι' ι = 0)
    (an : ∀ ι' ι (l : ℕ) (e : Fin l ≃ nearIndices F (I'.pos ι') R),
      ∀ p ∈ openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ,
        AnalyticAt ℂ (fun z => T (fieldExtend e z) ι' ι) p)
    (rd : ∀ ι' ι ζ ζ', IsSupBelow F ζ ρ → IsSupBelow F ζ' ρ →
      (∀ κ ∈ nearIndices F (I'.pos ι') R, ζ κ = ζ' κ) → T ζ ι' ι = T ζ' ι' ι)
    (cov : ∀ ζ, IsSupBelow F ζ ρ → ∀ (n : Fin 4 → ℤ) ι' ι,
      T (shiftField F n ζ) (I'.translate n ι') (I.translate n ι) = T ζ ι' ι) :
    IsLocalWith F I I' T ρ R where
  radius_pos := hρ
  vanish_far := far
  holo_entry := fun ι' ι => by
    have : Finite (nearIndices F (I'.pos ι') R) := (hfin _).to_subtype
    let e : Fin (Nat.card (nearIndices F (I'.pos ι') R)) ≃
        nearIndices F (I'.pos ι') R := (Finite.equivFin _).symm
    refine ⟨_, e, fun z => T (fieldExtend e z) ι' ι, ?_, fun ζ hζ => ?_⟩
    · refine isHolomorphicIn_of_analyticAt (isOpen_openPolydisk ρ) fun w hw => ?_
      exact analyticAt_pi_iff.2 fun _ => an ι' ι _ e w hw
    · exact rd ι' ι ζ _ hζ (isSupBelow_fieldExtend e hρ (fieldValues_mem_openPolydisk e hζ))
        fun κ hκ => (fieldExtend_fieldValues e ζ hκ).symm
  shift_covariant := cov
end Values
private structure Inputs : Prop where
  hZ : BlockPathContourPivotStatement
  hBk : BlockStructure
  hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity
  hPd : DoubleBlockPolydisc.PolydiscsHold
  hLin : FullSpace.CovariantStepComplexLinear
  hH : FullSpace.ComplexSmoothingEquivariance.Statement
  hTr : Translations.TranslationProperties
  hP : FullLatticeOverTorus.FullLatticeOverTorusClaim
  hV : ComplexMeanLiesInComplexGaugeGroup
  hRl : FullSpace.RealityOfOneStep.Statement
private structure Setting (L k : ℕ) (δ ρ : ℝ) : Prop where
  G : Inputs
  hL : Conventions.IsAdmissibleBlockingFactor L
  hk : 1 ≤ k
  F : OneStepFacts L k δ
  hδ : 0 < δ
  hρ : 0 < ρ
  I : FieldIterateProperties L k δ ρ
section Iterates
variable {L k : ℕ} {δ ρ : ℝ}
private theorem Setting.small (C : Setting L k δ ρ) : ∀ j, j ≤ k →
    ∀ f : (colourEdges L k 0).Carrier → ℂ,
    IsSupBelow (colourEdges L k 0) f ρ → meanIterate (expField f) j ∈ nearIdentityFields L k j δ :=
  C.I.mem_nearIdentity
private theorem iterate_analyticAt (C : Setting L k δ ρ) {S : Set (colourEdges L k 0).Carrier}
    {l : ℕ} (e : Fin l ≃ S) : ∀ j, j ≤ k →
    ∀ p ∈ openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ, ∀ b,
      AnalyticAt ℂ (fun z => meanIterate (expField (fieldExtend e z)) j b) p :=
  C.I.analyticAt S l e
private theorem iterate_local (C : Setting L k δ ρ) : ∀ j, j ≤ k → ∀ (b : FullSpace.Edge L k j)
    (f f' : (colourEdges L k 0).Carrier → ℂ), IsSupBelow (colourEdges L k 0) f ρ →
    IsSupBelow (colourEdges L k 0) f' ρ →
    (∀ κ : (colourEdges L k 0).Carrier,
      ‖((κ.2.1.initial : FullSpace.Vertex L k 0) : AmbientSpace) - (b.initial : AmbientSpace)‖ ≤
        3 * (j : ℝ) + 3 → f κ = f' κ) →
    meanIterate (expField f) j b = meanIterate (expField f') j b :=
  C.I.local_dependence
private theorem iterate_shift (C : Setting L k δ ρ) (n : Fin 4 → ℤ) : ∀ j, j ≤ k →
    ∀ f : (colourEdges L k 0).Carrier → ℂ, IsSupBelow (colourEdges L k 0) f ρ →
      meanIterate (expField (shiftField (colourEdges L k 0) n f)) j =
        FullSpace.pushField (intShift n) (meanIterate (expField f) j) :=
  C.I.shift_eq n
private theorem analyticAt_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x) (hu : IsUnit (Matrix.det (f x))) :
    AnalyticAt ℂ (fun y => (f y)⁻¹) x := by apply _root_.YangMills.SharedProofs.p7089 <;> assumption
end Iterates
section OneStep
variable {L k j : ℕ} {δ ρ : ℝ}
private theorem colourForm_zero : colourForm (0 : (colourEdges L k j).Carrier → ℂ) = 0 := by
  have h := colourForm_smul (L := L) (k := k) (i := j) 0 (0 : (colourEdges L k j).Carrier → ℂ)
  simpa using h
private def stepCoeffMap (V : FullSpace.Edge L k j → ComplexMatrix2) :
    ((colourEdges L k j).Carrier → ℂ) → (colourEdges L k (j + 1)).Carrier → ℂ :=
  PauliComponentsOfSymmetricKernel.mapOnCoeffs (FullSpace.edgePauliCoordinates L k j) (FullSpace.edgePauliCoordinates L k (j + 1))
    fun B => (L : ℝ)⁻¹ • meanCovariantStep V B
private theorem stepCoeffMap_eq (C : Setting L k δ ρ) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityFields L k j δ) (f : (colourEdges L k j).Carrier → ℂ)
    (ι' : (colourEdges L k (j + 1)).Carrier) :
    stepCoeffMap V f ι' = coeffCLM ι'.1
      ((((L : ℝ)⁻¹ : ℝ) : ℂ) • meanCovariantStep V (colourForm f) ι'.2.1) := by
  have hm := ((C.F.forms j hj V hV).1 _ (colourForm_mem C.hL f)).1 ι'.2.1 ι'.2.2
  show pauliCoeff ι'.1 (((L : ℝ)⁻¹ • meanCovariantStep V (colourForm f)) ι'.2.1) = _
  rw [Pi.smul_apply, real_smul_eq_ofReal_smul]
  exact pauliCoeff_eq_coeffCLM _ (Submodule.smul_mem _ _ hm)
private theorem step_add (C : Setting L k δ ρ) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityFields L k j δ) {B B' : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j))
    (hB' : B' ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    meanCovariantStep V (B + B') = meanCovariantStep V B + meanCovariantStep V B' := by
  have h := (C.F.forms j hj V hV).2.1 B hB B' hB' 1
  simpa only [one_smul] using h
private theorem step_smul (C : Setting L k δ ρ) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityFields L k j δ) {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j)) (w : ℂ)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    meanCovariantStep V (w • B) c = w • meanCovariantStep V B c := by
  have h := congrFun ((C.F.forms j hj V hV).2.1 B hB 0 (Submodule.zero_mem _) w) c
  have h0 := (C.F.forms j hj V hV).2.2.1 c hc 0 (Submodule.zero_mem _) fun _ _ => rfl
  simpa [h0] using h
private def stepRows (ι' : (colourEdges L k (j + 1)).Carrier) :
    Set (colourEdges L k j).Carrier :=
  {ι | ι.2.1 ∈ FullSpace.doubleCubeLinks L (meshAt L k j) ι'.2.1}
private theorem step_isRowLocal (C : Setting L k δ ρ) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityFields L k j δ) : IsRowLocal (stepCoeffMap V) stepRows where
  add f g := by
    funext ι'
    simp only [Pi.add_apply, stepCoeffMap_eq C hj hV, colourForm_add,
      step_add C hj hV (colourForm_mem C.hL f) (colourForm_mem C.hL g), smul_add, map_add]
  smul w f := by
    funext ι'
    simp only [Pi.smul_apply, stepCoeffMap_eq C hj hV, colourForm_smul,
      step_smul C hj hV (colourForm_mem C.hL f) w ι'.2.2, smul_eq_mul]
    rw [smul_comm, map_smul, smul_eq_mul]
  standingConstraints ι' := by
    have hfin := ((C.G.hPd L C.hL k j hj).2 ι'.2.1 ι'.2.2).finite_open.finite
    exact ((Set.finite_univ (α := Fin 3)).prod
      (hfin.preimage Subtype.val_injective.injOn)).subset fun ι hι => ⟨mem_univ _, hι⟩
  reads f ι' h := by
    have he : EqOn (colourForm f) (colourForm 0)
        (FullSpace.doubleCubeLinks L (meshAt L k j) ι'.2.1) :=
      colourForm_eqOn f 0 (fun b hb => ⟨hb.2, hb.1⟩) fun b hb hp a => h (a, ⟨b, hp⟩) hb
    rw [stepCoeffMap_eq C hj hV, (C.F.forms j hj V hV).2.2.1 ι'.2.1 ι'.2.2 _
      (colourForm_mem C.hL f) fun b hb => by rw [he hb, colourForm_zero]; rfl]
    simp
private theorem step_spec (C : Setting L k δ ρ) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityFields L k j δ) :
    Represents (kernelOfMap (stepCoeffMap V)) (stepCoeffMap V) ∧
      RowFinite (kernelOfMap (stepCoeffMap V)) ∧
      ∀ ι' ι, kernelOfMap (stepCoeffMap V) ι' ι = stepCoeffMap V (basisFn ι) ι' :=
  (step_isRowLocal C hj hV).kernelOfMap_spec
private theorem step_entry (C : Setting L k δ ρ) (hj : j < k)
    {f : (colourEdges L k 0).Carrier → ℂ} (hf : IsSupBelow (colourEdges L k 0) f ρ)
    (ι' : (colourEdges L k (j + 1)).Carrier) (ι : (colourEdges L k j).Carrier) :
    meanStepKernel L k (expField f) j ι' ι = coeffCLM ι'.1 ((((L : ℝ)⁻¹ : ℝ) : ℂ) •
      meanCovariantStep (meanIterate (expField f) j) (colourForm (basisFn ι)) ι'.2.1) := by
  have hV := C.small j hj.le f hf
  exact ((step_spec C hj hV).2.2 ι' ι).trans (stepCoeffMap_eq C hj hV _ ι')
private def radiusWindow (k : ℕ) : ℝ := 2 * (3 * (k : ℝ) + 5)
private theorem radiusWindow_nonneg (k : ℕ) : 0 ≤ radiusWindow k := by
  unfold radiusWindow
  positivity
private theorem nearIndices_finite (C : Setting L k δ ρ) (y : AmbientSpace) {R : ℝ} (hR : 0 ≤ R) :
    (nearIndices (colourEdges L k 0) y R).Finite := by
  have hP := (C.G.hP L C.hL k 0 (Nat.zero_le _) 1 one_pos).2.2.2.1
  have hb : Bornology.IsBounded {x : AmbientSpace | euclidNormVec (x - y) ≤ R} := by
    refine (Metric.isBounded_closedBall (x := y) (r := R)).subset fun x hx => ?_
    refine Metric.mem_closedBall.2 ((dist_pi_le_iff hR).2 fun μ => ?_)
    refine le_trans ?_ hx
    rw [Real.dist_eq]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun ν => (x - y) ν ^ 2) (fun ν _ => sq_nonneg _)
      (Finset.mem_univ μ)
  exact ((Set.finite_univ (α := Fin 3)).prod (hP _ hb).2.1).subset fun ι hι => ⟨mem_univ _, hι⟩
private theorem iterate_local_window (C : Setting L k δ ρ) (hj : j < k)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {f f' : (colourEdges L k 0).Carrier → ℂ} (hf : IsSupBelow (colourEdges L k 0) f ρ)
    (hf' : IsSupBelow (colourEdges L k 0) f' ρ)
    (h : ∀ κ ∈ nearIndices (colourEdges L k 0) (c.initial : AmbientSpace) (radiusWindow k),
      f κ = f' κ) :
    ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c,
      meanIterate (expField f) j b = meanIterate (expField f') j b := by
  intro b hb
  refine iterate_local C j hj.le b f f' hf hf' fun κ hκ => h κ ?_
  have h1 := norm_sub_le_of_mem_doubleCube C.G.hZ C.hL hj hc hb.1
  have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
  have h2 : ‖((κ.2.1.initial : FullSpace.Vertex L k 0) : AmbientSpace) -
      (c.initial : AmbientSpace)‖ ≤ 3 * (k : ℝ) + 5 := by
    have e : ((κ.2.1.initial : FullSpace.Vertex L k 0) : AmbientSpace) -
        (c.initial : AmbientSpace) =
        (((κ.2.1.initial : FullSpace.Vertex L k 0) : AmbientSpace) - (b.initial : AmbientSpace)) +
          ((b.initial : AmbientSpace) - (c.initial : AmbientSpace)) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    linarith
  exact euclidNormVec_le h2
private theorem step_isLocal (C : Setting L k δ ρ) (hj : j < k) :
    IsLocalWith (colourEdges L k 0) (colourEdges L k j) (colourEdges L k (j + 1))
      (fun f => meanStepKernel L k (expField f) j) ρ (radiusWindow k) := by
  refine isLocalWith_of_entries C.hρ (fun y => nearIndices_finite C y (radiusWindow_nonneg k))
    ?_ ?_ ?_ ?_
  · intro f hf ι' ι hfar
    have hV := C.small j hj.le f hf
    have hnot : ι ∉ stepRows ι' := fun hι => hfar (by
      have h1 := norm_sub_le_of_mem_doubleCube C.G.hZ C.hL hj ι'.2.2 hι.1
      have h2 := euclidNormVec_le h1
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      unfold radiusWindow
      refine h2.trans ?_
      linarith)
    have h0 := (step_isRowLocal C hj hV).basisKernel_eq_zero hnot
    exact ((step_spec C hj hV).2.2 ι' ι).trans h0
  · intro ι' ι l e p hp
    have hW := iterate_analyticAt C e j hj.le p hp
    have hev : ∀ᶠ z in 𝓝 p, meanIterate (expField (fieldExtend e z)) j ∈
        nearIdentityFields L k j δ := by
      filter_upwards [(isOpen_openPolydisk ρ).mem_nhds hp] with z hz
      exact C.small j hj.le _ (isSupBelow_fieldExtend e C.hρ hz)
    have hA := (C.F.analytic j hj l _ p hW hev).2.2.1 _ (colourForm_mem C.hL (basisFn ι)) ι'.2.1
    have hB : AnalyticAt ℂ (fun z => coeffCLM ι'.1 ((((L : ℝ)⁻¹ : ℝ) : ℂ) •
        meanCovariantStep (meanIterate (expField (fieldExtend e z)) j) (colourForm (basisFn ι))
          ι'.2.1)) p :=
      ((coeffCLM ι'.1).analyticAt _).comp (analyticAt_const.fun_smul hA)
    refine hB.congr ?_
    filter_upwards [(isOpen_openPolydisk ρ).mem_nhds hp] with z hz
    exact (step_entry C hj (isSupBelow_fieldExtend e C.hρ hz) ι' ι).symm
  · intro ι' ι f f' hf hf' he
    beta_reduce
    rw [step_entry C hj hf, step_entry C hj hf']
    have hV := C.small j hj.le f hf
    have hV' := C.small j hj.le f' hf'
    rw [((C.F.forms j hj _ hV).2.2.2 ι'.2.1 ι'.2.2 _ hV'
      (iterate_local_window C hj ι'.2.2 hf hf' he)).2.2.1 _ (colourForm_mem C.hL (basisFn ι))]
  · intro f hf n ι' ι
    beta_reduce
    have hP := C.G.hP L C.hL k j hj.le 1 one_pos
    have hP1 := C.G.hP L C.hL k (j + 1) (by omega) 1 one_pos
    have T := intShift_data C.G.hZ C.G.hTr C.hL C.hk n
    have hf₂ := isSupBelow_shiftField hf n
    have hV := C.small j hj.le f hf
    rw [step_entry C hj hf₂, step_entry C hj hf, iterate_shift C n j hj.le f hf,
      colourForm_basisFn_translate n T hj.le (hP.2.2.1 n).2.1 (hP.2.2.1 (-n)).2.1
        (meanIterate (expField f) j) ι]
    show coeffCLM ι'.1 (_ • meanCovariantStep _ _ (shiftEdge n ι'.2).1) = _
    rw [shiftEdge_val n T (by omega) (hP1.2.2.1 n).2.1 ι'.2,
      ((C.F.transl j hj n _ hV).2 ι'.2.1 ι'.2.2).2 _ (colourForm_mem C.hL (basisFn ι))]
end OneStep
section Sites
variable {L k j : ℕ} {δ ρ : ℝ}
private theorem translate_injective (C : Setting L k δ ρ) (hj : j ≤ k) (n : Fin 4 → ℤ)
    {ι' ι : (colourEdges L k j).Carrier}
    (h : (colourEdges L k j).translate n ι' = (colourEdges L k j).translate n ι) : ι' = ι := by
  have hP := C.G.hP L C.hL k j hj 1 one_pos
  have T := intShift_data C.G.hZ C.G.hTr C.hL C.hk n
  have hinv : ∀ x : (colourEdges L k j).Carrier,
      (colourEdges L k j).translate (-n) ((colourEdges L k j).translate n x) = x := fun x =>
    Prod.ext rfl (shiftEdge_neg_shiftEdge n T hj (hP.2.2.1 n).2.1
      (hP.2.2.1 (-n)).2.1 x.2)
  rw [← hinv ι', h, hinv]
private theorem invRadiusDiag_self (U : FullSpace.Edge L k 0 → ComplexMatrix2) (j : ℕ)
    (ι : Fin 3 × FullSpace.PositiveEdge (meshAt L k (j + 1))) :
    invRadiusDiag U j ι ι = (meanRadius (meanIterate U j) ι.2.1)⁻¹ := by
  simp [invRadiusDiag]
private theorem invRadiusDiag_of_ne (U : FullSpace.Edge L k 0 → ComplexMatrix2) (j : ℕ)
    {ι' ι : Fin 3 × FullSpace.PositiveEdge (meshAt L k (j + 1))} (h : ι' ≠ ι) :
    invRadiusDiag U j ι' ι = 0 := by
  simp [invRadiusDiag, h]
private theorem radius_isLocal (C : Setting L k δ ρ) (hj : j < k) :
    IsLocalWith (colourEdges L k 0) (colourEdges L k (j + 1))
      (colourEdges L k (j + 1)) (fun f => invRadiusDiag (expField f) j) ρ (radiusWindow k) := by
  classical
  refine isLocalWith_of_entries C.hρ (fun y => nearIndices_finite C y (radiusWindow_nonneg k))
    ?_ ?_ ?_ ?_
  · intro f hf ι' ι hfar
    have hne : ι' ≠ ι := by
      rintro rfl
      apply hfar
      have h0 : euclidNormVec ((colourEdges L k (j + 1)).pos ι' -
          (colourEdges L k (j + 1)).pos ι') = 0 := by
        simp [euclidNormVec]
      rw [h0]
      exact radiusWindow_nonneg k
    exact invRadiusDiag_of_ne _ j hne
  · intro ι' ι l e p hp
    by_cases hi : ι' = ι
    · subst hi
      have hW := iterate_analyticAt C e j hj.le p hp
      have hev : ∀ᶠ z in 𝓝 p, meanIterate (expField (fieldExtend e z)) j ∈
          nearIdentityFields L k j δ := by
        filter_upwards [(isOpen_openPolydisk ρ).mem_nhds hp] with z hz
        exact C.small j hj.le _ (isSupBelow_fieldExtend e C.hρ hz)
      exact ((C.F.analytic j hj l _ p hW hev).2.1 ι'.2.1 ι'.2.2).congr
        (Eventually.of_forall fun z => (invRadiusDiag_self _ j ι').symm)
    · exact (analyticAt_const (v := (0 : ℂ))).congr
        (Eventually.of_forall fun z => (invRadiusDiag_of_ne _ j hi).symm)
  · intro ι' ι f f' hf hf' he
    by_cases hi : ι' = ι
    · subst hi
      refine (invRadiusDiag_self _ j ι').trans (Eq.trans ?_ (invRadiusDiag_self _ j ι').symm)
      rw [((C.F.forms j hj _ (C.small j hj.le f hf)).2.2.2 ι'.2.1 ι'.2.2 _
        (C.small j hj.le f' hf') (iterate_local_window C hj ι'.2.2 hf hf' he)).1]
    · exact (invRadiusDiag_of_ne _ j hi).trans (invRadiusDiag_of_ne _ j hi).symm
  · intro f hf n ι' ι
    have hP1 := C.G.hP L C.hL k (j + 1) (by omega) 1 one_pos
    have T := intShift_data C.G.hZ C.G.hTr C.hL C.hk n
    by_cases hi : ι' = ι
    · subst hi
      refine (invRadiusDiag_self _ j _).trans (Eq.trans ?_ (invRadiusDiag_self _ j ι').symm)
      rw [iterate_shift C n j hj.le f hf]
      show (meanRadius _ (shiftEdge n ι'.2).1)⁻¹ = _
      rw [shiftEdge_val n T (by omega) (hP1.2.2.1 n).2.1 ι'.2,
        ((C.F.transl j hj n _ (C.small j hj.le f hf)).2 ι'.2.1 ι'.2.2).1]
    · exact (invRadiusDiag_of_ne _ j fun h => hi (translate_injective C (by omega) n h)).trans
        (invRadiusDiag_of_ne _ j hi).symm
private theorem cubeVertices_finite (L : ℕ) {a : ℝ} (a' : ℝ) (y : InfiniteLattice.LatticePoint a) :
    (FullSpace.cubeVertices L a' y : Set (InfiniteLattice.LatticePoint a')).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.cubeVertices_finite <;> assumption
private def vertexCoeffMap (V : FullSpace.Edge L k j → ComplexMatrix2) :
    ((colourVertices L k j).Carrier → ℂ) → (colourVertices L k (j + 1)).Carrier → ℂ :=
  PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L k j))
    (vertexCoordinate (FullSpace.Vertex L k (j + 1))) (FullSpace.adjointCubeAverage V)
private theorem mem_smallComplexFields (C : Setting L k δ ρ)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityFields L k j δ) : V ∈ FullSpace.smallComplexFields L k j :=
  ⟨hV.1, fun b => (hV.2 b).trans_le C.F.radius⟩
private theorem vertexCoeffMap_eq (C : Setting L k δ ρ) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityFields L k j δ) (f : (colourVertices L k j).Carrier → ℂ)
    (ι' : (colourVertices L k (j + 1)).Carrier) :
    vertexCoeffMap V f ι' =
      coeffCLM ι'.1 (FullSpace.adjointCubeAverage V (ofPauliCoeffs f) ι'.2) := by
  have hm := ((C.G.hLin L C.hL k j hj V (mem_smallComplexFields C hV)).2.2.1 _
    (ofPauliCoeffs_mem f)).2 ι'.2
  exact pauliCoeff_eq_coeffCLM _ hm
private theorem adjointCubeAverage_eq_zero {V : FullSpace.Edge L k j → ComplexMatrix2}
    {l : FullSpace.Vertex L k j → ComplexMatrix2} {y : FullSpace.Vertex L k (j + 1)}
    (h : ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) y, l x = 0) :
    FullSpace.adjointCubeAverage V l y = 0 := by
  unfold FullSpace.adjointCubeAverage
  have : ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) y,
      ComplexMatrix2.conjugateBy (FullSpace.complexContourMean L V y x) (l x) = 0 := fun x hx => by
    rw [h x hx]
    simp [ComplexMatrix2.conjugateBy]
  rw [finsum_mem_congr rfl this]
  simp
private def vertexRows (ι' : (colourVertices L k (j + 1)).Carrier) :
    Set (colourVertices L k j).Carrier :=
  {ι | ι.2 ∈ FullSpace.cubeVertices L (meshAt L k j) ι'.2}
private theorem vertex_isRowLocal (C : Setting L k δ ρ) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityFields L k j δ) : IsRowLocal (vertexCoeffMap V) vertexRows where
  add f g := by
    funext ι'
    have h := ((C.G.hLin L C.hL k j hj V (mem_smallComplexFields C hV)).2.2.2 _ _
      (ofPauliCoeffs_mem f) (ofPauliCoeffs_mem g) 1).2
    rw [one_smul, one_smul] at h
    rw [Pi.add_apply, vertexCoeffMap_eq C hj hV, vertexCoeffMap_eq C hj hV,
      vertexCoeffMap_eq C hj hV,
      show (ofPauliCoeffs (f + g) : FullSpace.Vertex L k j → ComplexMatrix2) =
        ofPauliCoeffs f + ofPauliCoeffs g from ofPauliCoeffs_add f g, h, Pi.add_apply, map_add]
  smul w f := by
    funext ι'
    have h0 : ∀ x, (0 : FullSpace.Vertex L k j → ComplexMatrix2) x ∈ ComplexMatrix2.traceless :=
      fun _ => ComplexMatrix2.traceless.zero_mem
    have h := ((C.G.hLin L C.hL k j hj V (mem_smallComplexFields C hV)).2.2.2 _ _
      (ofPauliCoeffs_mem f) h0 w).2
    have hz : FullSpace.adjointCubeAverage V (0 : FullSpace.Vertex L k j → ComplexMatrix2) ι'.2 = 0 :=
      adjointCubeAverage_eq_zero fun _ _ => rfl
    have e : (ofPauliCoeffs (w • f) : FullSpace.Vertex L k j → ComplexMatrix2) =
        w • ofPauliCoeffs f + (0 : FullSpace.Vertex L k j → ComplexMatrix2) := by
      rw [add_zero]
      exact ofPauliCoeffs_smul w f
    rw [Pi.smul_apply, vertexCoeffMap_eq C hj hV, vertexCoeffMap_eq C hj hV, e, h, Pi.add_apply,
      hz, add_zero, Pi.smul_apply, map_smul]
  standingConstraints ι' := ((Set.finite_univ (α := Fin 3)).prod
    (cubeVertices_finite L (meshAt L k j) ι'.2)).subset fun ι hι => ⟨mem_univ _, hι⟩
  reads f ι' h := by
    rw [vertexCoeffMap_eq C hj hV, adjointCubeAverage_eq_zero fun x hx => ?_]
    · simp
    · simp only [ofPauliCoeffs]
      exact Finset.sum_eq_zero fun a _ => by rw [h (a, x) hx, zero_smul]
private theorem vertex_spec (C : Setting L k δ ρ) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityFields L k j δ) :
    Represents (kernelOfMap (vertexCoeffMap V)) (vertexCoeffMap V) ∧
      RowFinite (kernelOfMap (vertexCoeffMap V)) ∧
      ∀ ι' ι, kernelOfMap (vertexCoeffMap V) ι' ι = vertexCoeffMap V (basisFn ι) ι' :=
  (vertex_isRowLocal C hj hV).kernelOfMap_spec
private theorem vertex_entry (C : Setting L k δ ρ) (hj : j < k)
    {f : (colourEdges L k 0).Carrier → ℂ} (hf : IsSupBelow (colourEdges L k 0) f ρ)
    (ι' : (colourVertices L k (j + 1)).Carrier) (ι : (colourVertices L k j).Carrier) :
    meanVertexStepKernel L k (expField f) j ι' ι = coeffCLM ι'.1
      (FullSpace.adjointCubeAverage (meanIterate (expField f) j)
        (ofPauliCoeffs (basisFn ι)) ι'.2) := by
  have hV := C.small j hj.le f hf
  exact ((vertex_spec C hj hV).2.2 ι' ι).trans (vertexCoeffMap_eq C hj hV _ ι')
private theorem forwardFrom_isPos (y : FullSpace.Vertex L k (j + 1)) :
    (InfiniteLattice.Link.forwardFrom y 0 : FullSpace.Edge L k (j + 1)).IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.forwardFrom_positive <;> assumption
private theorem contourMean_mem (C : Setting L k δ ρ) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityFields L k j δ) (y : FullSpace.Vertex L k (j + 1))
    {x : FullSpace.Vertex L k j} (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y) :
    FullSpace.complexContourMean L V y x ∈ PeriodicLattice.complexGaugeGroup := by
  have hc := forwardFrom_isPos (k := k) (j := j) y
  have hP : V ∈ FullSpace.nearIdentityPolydisc L k j (polydiscRadius L)
      (InfiniteLattice.Link.forwardFrom y 0) :=
    ⟨⟨fun b _ => hV.1.1 b, fun b _ => hV.1.2 b⟩, fun b _ => (hV.2 b).trans_le C.F.radius⟩
  exact ((C.G.hV.2 L k (j + 1) C.hL (by omega) (by omega)).2 _ V hc
    (((C.G.hS.1 L C.hL).2.2.fullSpace k j hj _ hc).subset_complexDomain hP)).1 y (Or.inl rfl) x hx
private theorem adjointCubeAverage_shift (C : Setting L k δ ρ) (hj : j < k) (n : Fin 4 → ℤ)
    {V : FullSpace.Edge L k j → ComplexMatrix2} (hV : V ∈ nearIdentityFields L k j δ)
    (l : FullSpace.Vertex L k j → ComplexMatrix2) (y : FullSpace.Vertex L k (j + 1)) :
    FullSpace.adjointCubeAverage (FullSpace.pushField (intShift n) V)
        (FullSpace.pushSiteFunction (intShift n) l) (FullSpace.vertexImage (intShift n) y) =
      FullSpace.adjointCubeAverage V l y := by
  have T := intShift_data C.G.hZ C.G.hTr C.hL C.hk n
  have hMj := T.lattice j hj.le
  have hM1 := T.lattice (j + 1) (by omega)
  unfold FullSpace.adjointCubeAverage
  congr 1
  symm
  refine finsum_mem_eq_of_bijOn _
    (cubeVertices_bijOn hMj T.inj (cube_image C.G.hBk C.hL hj T) y) fun x hx => ?_
  have hc := forwardFrom_isPos (k := k) (j := j) y
  have hP : V ∈ FullSpace.nearIdentityPolydisc L k j (polydiscRadius L)
      (InfiniteLattice.Link.forwardFrom y 0) :=
    ⟨⟨fun b _ => hV.1.1 b, fun b _ => hV.1.2 b⟩, fun b _ => (hV.2 b).trans_le C.F.radius⟩
  have h := (C.G.hH L C.hL k j hj _ T.isom hM1 _ hc V hP).1 y (Or.inl rfl) x hx
  rw [h]
  show _ = ComplexMatrix2.conjugateBy _
    (l (FullSpace.vertexPreimage (intShift n) (FullSpace.vertexImage (intShift n) x)))
  rw [vertexPreimage_vertexImage hMj T.inj]
private theorem ofPauliCoeffs_basisFn_translate (C : Setting L k δ ρ) (hj : j ≤ k) (n : Fin 4 → ℤ)
    (ι : (colourVertices L k j).Carrier) :
    ofPauliCoeffs (basisFn ((colourVertices L k j).translate n ι)) =
      FullSpace.pushSiteFunction (intShift n) (ofPauliCoeffs (basisFn ι)) := by
  have T := intShift_data C.G.hZ C.G.hTr C.hL C.hk n
  have hM := T.lattice j hj
  let s : (colourVertices L k j).Carrier → (colourVertices L k j).Carrier :=
    fun κ => (κ.1, FullSpace.vertexImage (intShift n) κ.2)
  let s' : (colourVertices L k j).Carrier → (colourVertices L k j).Carrier :=
    fun κ => (κ.1, FullSpace.vertexPreimage (intShift n) κ.2)
  have h1 : ∀ x, s' (s x) = x := fun x => Prod.ext rfl (vertexPreimage_vertexImage hM T.inj x.2)
  have h2 : ∀ x, s (s' x) = x := fun x => Prod.ext rfl (vertexImage_vertexPreimage hM x.2)
  funext x
  simp only [ofPauliCoeffs, FullSpace.pushSiteFunction]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e := basisFn_map h1 h2 ι (a, x)
  exact congrArg (fun w : ℂ => w • ComplexMatrix2.pauliFamily a) e
private theorem vertex_isLocal (C : Setting L k δ ρ) (hj : j < k) :
    IsLocalWith (colourEdges L k 0) (colourVertices L k j) (colourVertices L k (j + 1))
      (fun f => meanVertexStepKernel L k (expField f) j) ρ (radiusWindow k) := by
  refine isLocalWith_of_entries C.hρ (fun y => nearIndices_finite C y (radiusWindow_nonneg k))
    ?_ ?_ ?_ ?_
  · intro f hf ι' ι hfar
    have hV := C.small j hj.le f hf
    have hnot : ι ∉ vertexRows ι' := fun hι => hfar (by
      have h1 := norm_sub_le_of_mem_doubleCube C.G.hZ C.hL hj
        (forwardFrom_isPos (k := k) (j := j) ι'.2) (x := (ι.2 : AmbientSpace)) (Or.inl hι)
      have h2 := euclidNormVec_le h1
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      unfold radiusWindow
      refine h2.trans ?_
      linarith)
    have h0 := (vertex_isRowLocal C hj hV).basisKernel_eq_zero hnot
    exact ((vertex_spec C hj hV).2.2 ι' ι).trans h0
  · intro ι' ι l e p hp
    have hW := iterate_analyticAt C e j hj.le p hp
    have hev : ∀ᶠ z in 𝓝 p, meanIterate (expField (fieldExtend e z)) j ∈
        nearIdentityFields L k j δ := by
      filter_upwards [(isOpen_openPolydisk ρ).mem_nhds hp] with z hz
      exact C.small j hj.le _ (isSupBelow_fieldExtend e C.hρ hz)
    have hA := (C.F.analytic j hj l _ p hW hev).2.2.2 ι'.2
    have hfin := cubeVertices_finite L (meshAt L k j) ι'.2
    have hS : AnalyticAt ℂ (fun z => ∑ x ∈ hfin.toFinset,
        ComplexMatrix2.conjugateBy
          (FullSpace.complexContourMean L (meanIterate (expField (fieldExtend e z)) j) ι'.2 x)
          (ofPauliCoeffs (basisFn ι) x)) p :=
      Finset.analyticAt_fun_sum _ fun x hx => by
        have hx' := hfin.mem_toFinset.1 hx
        have hu : IsUnit (Matrix.det
            (FullSpace.complexContourMean L (meanIterate (expField (fieldExtend e p)) j)
              ι'.2 x)) := by
          have e' : Matrix.det
              (FullSpace.complexContourMean L (meanIterate (expField (fieldExtend e p)) j)
                ι'.2 x) = 1 :=
            contourMean_mem C hj hev.self_of_nhds ι'.2 hx'
          rw [e']
          exact isUnit_one
        exact ((hA x hx').fun_mul analyticAt_const).fun_mul (analyticAt_inv (hA x hx') hu)
    have hB : AnalyticAt ℂ (fun z => coeffCLM ι'.1 (PeriodicLattice.inverseFourthPowerWeight L •
        ∑ x ∈ hfin.toFinset, ComplexMatrix2.conjugateBy
          (FullSpace.complexContourMean L (meanIterate (expField (fieldExtend e z)) j) ι'.2 x)
          (ofPauliCoeffs (basisFn ι) x))) p :=
      ((coeffCLM ι'.1).analyticAt _).comp (analyticAt_const.fun_smul hS)
    refine hB.congr ?_
    filter_upwards [(isOpen_openPolydisk ρ).mem_nhds hp] with z hz
    rw [vertex_entry C hj (isSupBelow_fieldExtend e C.hρ hz) ι' ι]
    unfold FullSpace.adjointCubeAverage
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  · intro ι' ι f f' hf hf' he
    beta_reduce
    rw [vertex_entry C hj hf, vertex_entry C hj hf']
    unfold FullSpace.adjointCubeAverage
    refine congrArg (coeffCLM ι'.1)
      (congrArg (PeriodicLattice.inverseFourthPowerWeight L • ·)
      (finsum_mem_congr rfl fun x hx => ?_))
    have hc := forwardFrom_isPos (k := k) (j := j) ι'.2
    rw [((C.F.forms j hj _ (C.small j hj.le f hf)).2.2.2 _ hc _ (C.small j hj.le f' hf')
      (iterate_local_window C hj hc hf hf' he)).2.2.2 ι'.2 (Or.inl rfl) x hx]
  · intro f hf n ι' ι
    beta_reduce
    have hf₂ := isSupBelow_shiftField hf n
    have hV := C.small j hj.le f hf
    rw [vertex_entry C hj hf₂, vertex_entry C hj hf, iterate_shift C n j hj.le f hf,
      ofPauliCoeffs_basisFn_translate C hj.le n ι]
    show coeffCLM ι'.1 (FullSpace.adjointCubeAverage _ _
      (FullSpace.vertexImage (intShift n) ι'.2)) = _
    rw [adjointCubeAverage_shift C hj n hV]
end Sites
section Real
variable {L k j : ℕ} {δ ρ : ℝ}
private theorem realCombination_mem {x : Fin 3 → ℂ} (hx : ∀ a, (x a).im = 0) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.ResponseOperators.sum_smul_pauliFamily_mem_hermitianTraceless <;> assumption
private theorem basisFn_im {N : Type} (ι x : N) : (basisFn ι x).im = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.RealKernels.basisVec_im <;> assumption
private theorem colourForm_basisFn_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ι : (colourEdges L k j).Carrier) :
    colourForm (basisFn ι) ∈ FullSpace.edgeFormSpace (meshAt L k j) := by
  refine ⟨fun b hb => ?_, colourForm_opposite hL _⟩
  rw [colourForm_of_pos _ hb]
  exact realCombination_mem fun a => basisFn_im _ _
private theorem coeffCLM_im (a : Fin 3) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) : (coeffCLM a X).im = 0 := by
  obtain ⟨hh, -⟩ := hX
  have e10 : X 1 0 = star (X 0 1) := by
    have := congrFun (congrFun hh 1) 0
    simpa [Matrix.conjTranspose_apply] using this
  have e00 : X 0 0 = star (X 0 0) := by
    have := congrFun (congrFun hh 0) 0
    simpa [Matrix.conjTranspose_apply] using this
  have hv : coeffCLM a X =
      ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a := rfl
  rw [hv]
  set w := X 0 1 with hw
  fin_cases a
  · show ((w + X 1 0) / 2).im = 0
    rw [e10]
    have h : w + star w = ((2 * w.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
      ring
    rw [h]
    simp
  · show ((X 1 0 - w) / (2 * Complex.I)).im = 0
    rw [e10]
    have h : star w - w = ((-(2 * w.im) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
      ring
    have h2 : ((-(2 * w.im) : ℝ) : ℂ) * Complex.I / (2 * Complex.I) = ((-w.im : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [h, h2, Complex.ofReal_im]
  · show (X 0 0).im = 0
    have := congrArg Complex.im e00
    simp at this
    linarith
private theorem ofReal_smul_mem (x : ℝ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    (x : ℂ) • X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_smul_mem_hermitianTraceless <;> assumption
private theorem step_im (C : Setting L k δ ρ) (hj : j < k)
    {f : (colourEdges L k 0).Carrier → ℂ} (hf : IsSupBelow (colourEdges L k 0) f ρ)
    (hr : ∀ κ, (f κ).im = 0) (ι' : (colourEdges L k (j + 1)).Carrier)
    (ι : (colourEdges L k j).Carrier) : (meanStepKernel L k (expField f) j ι' ι).im = 0 := by
  rw [step_entry C hj hf]
  exact coeffCLM_im _ (ofReal_smul_mem _ ((C.F.real j hj _ (C.small j hj.le f hf)
    (C.I.mem_compact f hf hr j hj.le)).2.2 _ (colourForm_basisFn_mem C.hL ι) _))
private theorem radius_im (C : Setting L k δ ρ) (hj : j < k)
    {f : (colourEdges L k 0).Carrier → ℂ} (hf : IsSupBelow (colourEdges L k 0) f ρ)
    (hr : ∀ κ, (f κ).im = 0) (ι' ι : (colourEdges L k (j + 1)).Carrier) :
    (invRadiusDiag (expField f) j ι' ι).im = 0 := by
  by_cases hi : ι' = ι
  · subst hi
    have e := invRadiusDiag_self (expField f) j ι'
    have h := (C.F.real j hj _ (C.small j hj.le f hf)
      (C.I.mem_compact f hf hr j hj.le)).2.1 ι'.2.1 ι'.2.2
    refine (congrArg Complex.im e).trans ?_
    rw [Complex.inv_im, h]
    simp
  · have e := invRadiusDiag_of_ne (expField f) j hi
    exact (congrArg Complex.im e).trans rfl
private theorem vertex_im (C : Setting L k δ ρ) (hj : j < k)
    {f : (colourEdges L k 0).Carrier → ℂ} (hf : IsSupBelow (colourEdges L k 0) f ρ)
    (hr : ∀ κ, (f κ).im = 0) (ι' : (colourVertices L k (j + 1)).Carrier)
    (ι : (colourVertices L k j).Carrier) :
    (meanVertexStepKernel L k (expField f) j ι' ι).im = 0 := by
  rw [vertex_entry C hj hf]
  have hV := C.small j hj.le f hf
  have hcf : meanIterate (expField f) j ∈ FullSpace.fieldSpace L k j :=
    ⟨C.I.mem_compact f hf hr j hj.le, hV.1.2⟩
  have hl : ofPauliCoeffs (basisFn ι) ∈ FullSpace.vertexFunctionSpace (meshAt L k j) :=
    fun x _ => realCombination_mem fun a => basisFn_im _ _
  have h := (C.G.hRl L C.hL k j hj _ (mem_smallComplexFields C hV) hcf).2.2.2.2 _ hl
  exact coeffCLM_im _ (h _ (mem_univ _))
end Real
end KernelLocality
open KernelLocality YangMills.Construction.Tower YangMills.Construction.Tower.FullSpace
  YangMills.Construction.PeriodicOperators in
theorem meanStepKernelsAreLocal_holds (hI : FieldIteratesNearIdentity)
    (hAn : MeanStepAnalytic) (hF : MeanStepOnForms)
    (hT : MeanStepShiftCovariant) (hR : MeanStepAtCompactFields)
    (hZ : BlockPathContourPivotStatement)
    (hBk : BlockStructure)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hPd : DoubleBlockPolydisc.PolydiscsHold)
    (hLin : CovariantStepComplexLinear)
    (hH : ComplexSmoothingEquivariance.Statement)
    (hTr : Translations.TranslationProperties)
    (hP : FullLatticeOverTorus.FullLatticeOverTorusClaim)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hRl : RealityOfOneStep.Statement) :
    MeanStepKernelsAreLocal := by
  intro L hL k hk
  obtain ⟨δ₀, h₀, H⟩ := exists_oneStepFacts hAn hF hT hR hS hL
  obtain ⟨δ₁, h₁, HI⟩ := hI L hL
  obtain ⟨ρ, hρ, I⟩ := HI (min δ₀ δ₁) (lt_min h₀ h₁) (min_le_right _ _) k hk
  have C : Setting L k (min δ₀ δ₁) ρ :=
    ⟨⟨hZ, hBk, hS, hPd, hLin, hH, hTr, hP, hV, hRl⟩, hL, hk, H _ (min_le_left _ _) k,
      lt_min h₀ h₁, hρ, I⟩
  refine ⟨fun j hj => ⟨⟨ρ, radiusWindow k, step_isLocal C hj⟩,
    ⟨ρ, radiusWindow k, radius_isLocal C hj⟩, ⟨ρ, radiusWindow k, vertex_isLocal C hj⟩⟩,
    ρ, hρ, fun f hf j hj => ⟨?_, fun hr =>
      ⟨step_im C hj hf hr, radius_im C hj hf hr, vertex_im C hj hf hr⟩⟩⟩
  have hW := C.small j hj.le f hf
  refine ⟨(step_spec C hj hW).2.1, (step_spec C hj hW).1, (vertex_spec C hj hW).2.1,
    (vertex_spec C hj hW).1, (C.F.forms j hj _ hW).1, fun B hB w c hc =>
      step_smul C hj hW hB w hc, fun l hl y =>
      ((hLin L hL k j hj _ (mem_smallComplexFields C hW)).2.2.1 l hl).2 y⟩
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
