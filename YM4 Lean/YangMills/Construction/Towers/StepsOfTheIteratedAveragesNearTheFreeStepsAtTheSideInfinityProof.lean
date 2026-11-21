import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.OneLoop.PauliMatrixComputations
import YangMills.Construction.Towers.BoundsOfTheIteratedAveragesOnASideProof
import YangMills.Construction.Towers.NormOfTheColourCoefficients
import YangMills.Construction.Towers.SiteAverageOnTheWholeProof
import YangMills.Construction.Towers.StepKernelsNearTheTrivialConfigurationAtTheSideInfinity
import YangMills.Construction.Towers.StepsOfTheIteratedAveragesNearTheFreeStepsAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IterStepsNearFree
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.StepKernels
  (singleLinkForm positiveDoubleCubeLinks StepKernelsAt IsBoundedTracelessEndo)
open YangMills.Construction.Tower.FullSpace.StepKernelsNearIdentity (NearIdentityBounds)
theorem tsum_colour_place_le {σ : Type} (g : Fin 3 × σ → ℝ) (S : Set σ) (m : ℕ) (M : ℝ)
    (hM : 0 ≤ M) (hS : S.encard ≤ m) (hzero : ∀ a x, x ∉ S → g (a, x) = 0)
    (hg : ∀ p, g p ≤ M) :
    Summable g ∧ ∑' p, g p ≤ 3 * m * M := by
  classical
  have hfin : S.Finite := Set.finite_of_encard_le_coe hS
  have hsum : HasSum g (∑ p ∈ (Finset.univ ×ˢ hfin.toFinset : Finset (Fin 3 × σ)), g p) :=
    hasSum_sum_of_ne_finset_zero fun p hp => by
      obtain ⟨a, x⟩ := p
      refine hzero a x fun hx => hp ?_
      simp [hx]
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq]
  have hm : hfin.toFinset.card ≤ m := by
    have h := hS
    rw [hfin.encard_eq_coe_toFinset_card] at h
    exact_mod_cast h
  have hcard : (((Finset.univ ×ˢ hfin.toFinset : Finset (Fin 3 × σ))).card : ℝ) ≤ 3 * m := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast
    have : (hfin.toFinset.card : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  calc ∑ p ∈ (Finset.univ ×ˢ hfin.toFinset : Finset (Fin 3 × σ)), g p
      ≤ ∑ _p ∈ (Finset.univ ×ˢ hfin.toFinset : Finset (Fin 3 × σ)), M :=
        Finset.sum_le_sum fun p _ => hg p
    _ = ((Finset.univ ×ˢ hfin.toFinset : Finset (Fin 3 × σ))).card * M := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * m * M := mul_le_mul_of_nonneg_right hcard hM
theorem schurTest_of_finite_support (hSchur : SchurTest.Holds) {σ σ' : Type}
    (T : Fin 3 × σ' → Fin 3 × σ → ℂ) (w : Fin 3 × σ → ℝ) (w' : Fin 3 × σ' → ℝ)
    (a a' M C : ℝ) (p q : ℕ) (S : σ' → Set σ) (ha : 0 < a) (ha' : 0 < a') (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hw : ∀ ι, w ι = a) (hw' : ∀ ι', w' ι' = a')
    (hzero : ∀ u' y u x, x ∉ S y → T (u', y) (u, x) = 0)
    (hbound : ∀ ι' ι, ‖T ι' ι‖ ≤ M)
    (hrow : ∀ y, (S y).encard ≤ p) (hcol : ∀ x, {y | x ∈ S y}.encard ≤ q)
    (hprod : a' * ((3 * p * M) * (3 * q * M)) ≤ C ^ 2 * a) :
    (∀ f, NormSummable w f →
      (∀ ι', ApplySummableAt T f ι') ∧ NormSummable w' (applyKernel T f)) ∧
    ∀ E : Set (Fin 3 × σ → ℂ), OpNormSummable w w' E (applyKernel T) ∧
      wOpNorm w w' E (applyKernel T) ≤ ENNReal.ofReal C := by
  refine hSchur.1 _ _ T w w' a a' (3 * p * M) (3 * q * M) C ha ha' hC hw hw' ?_ ?_ hprod
  · rintro ⟨u', y⟩
    exact tsum_colour_place_le (fun ι => ‖T (u', y) ι‖) (S y) p M hM (hrow y)
      (fun u x hx => by simp [hzero u' y u x hx]) (fun ι => hbound _ ι)
  · rintro ⟨u, x⟩
    exact tsum_colour_place_le (fun ι' => ‖T ι' (u, x)‖) {y | x ∈ S y} q M hM (hcol x)
      (fun u' y hy => by simp [hzero u' y u x hy]) (fun ι' => hbound ι' _)
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliFamily_mem_hermitianTraceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
theorem operatorNorm_pauliFamily (a : Fin 3) :
    ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily a) = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.norm_pauliFamily <;> assumption
theorem norm_pauliCoeff_le (hNorm : PauliCoefficientNorm.Claim) (a : Fin 3)
    (X : ComplexMatrix2) : ‖pauliCoeff a X‖ ≤ ComplexMatrix2.operatorNorm X := by
  by_cases hX : X ∈ ComplexMatrix2.traceless
  · have h2 := (hNorm.2.1.1 ⟨X, hX⟩).1
    refine le_trans ?_ h2
    show ‖pauliCoeff a X‖ ≤ pauliNorm X
    unfold pauliNorm
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun u => ‖pauliCoeff u X‖ ^ 2)
      (fun u _ => by positivity) (Finset.mem_univ a)
  · have : pauliCoeff a X = 0 := by
      unfold pauliCoeff
      rw [dif_neg hX]
    rw [this, norm_zero]
    exact norm_nonneg X
section Elementary
variable {σ : Type}
theorem ofPauliCoeffs_single_same [DecidableEq (Fin 3 × σ)] (u : Fin 3) (x : σ) :
    ofPauliCoeffs (Pi.single (u, x) (1 : ℂ) : Fin 3 × σ → ℂ) x = ComplexMatrix2.pauliFamily u := by apply _root_.YangMills.Construction.Tower.FullVertexSmoothing.ofPauliCoeffs_single_self <;> assumption
theorem ofPauliCoeffs_single_of_ne [DecidableEq (Fin 3 × σ)] (u : Fin 3) {x x' : σ}
    (h : x' ≠ x) : ofPauliCoeffs (Pi.single (u, x) (1 : ℂ) : Fin 3 × σ → ℂ) x' = 0 := by apply _root_.YangMills.Construction.Tower.FullVertexSmoothing.ofPauliCoeffs_single_of_ne <;> assumption
theorem finsum_mem_eq_of_support_single {S : Set σ} {x : σ} (hx : x ∈ S)
    {g : σ → ComplexMatrix2} (h : ∀ x', x' ≠ x → g x' = 0) : ∑ᶠ x' ∈ S, g x' = g x := by apply _root_.YangMills.Construction.Tower.FullVertexSmoothing.finsum_mem_eq_of_mem <;> assumption
theorem finsum_mem_eq_zero_of_support_single {S : Set σ} {x : σ} (hx : x ∉ S)
    {g : σ → ComplexMatrix2} (h : ∀ x', x' ≠ x → g x' = 0) : ∑ᶠ x' ∈ S, g x' = 0 := by apply _root_.YangMills.Construction.Tower.FullVertexSmoothing.finsum_mem_eq_zero_of_not_mem <;> assumption
end Elementary
section Forms
variable {a : ℝ}
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (e : InfiniteLattice.Link a) : extendOddly f e.opposite = -extendOddly f e := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem singleLinkForm_apply_of_pos {e e' : InfiniteLattice.Link a}
    (he' : e'.IsPositivelyOriented) (X : ComplexMatrix2) :
    singleLinkForm e X e' = open Classical in if e' = e then X else 0 := by
  classical
  simp only [singleLinkForm, extendOddly, if_pos he']
theorem singleLinkForm_mem_complexEdgeForms (ha : 0 < a) (e : InfiniteLattice.Link a)
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    singleLinkForm e X ∈ complexEdgeForms a := by
  classical
  refine ⟨fun e' he' => ?_, fun e' => extendOddly_opposite ha _ e'⟩
  rw [singleLinkForm_apply_of_pos he']
  split_ifs
  · exact hX
  · exact ComplexMatrix2.traceless.zero_mem
theorem singleLinkForm_mem_edgeFormSpace (ha : 0 < a) (e : InfiniteLattice.Link a)
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    singleLinkForm e X ∈ edgeFormSpace a := by
  classical
  refine ⟨fun e' he' => ?_, fun e' => extendOddly_opposite ha _ e'⟩
  rw [singleLinkForm_apply_of_pos he']
  split_ifs
  · exact hX
  · exact ComplexMatrix2.hermitianTraceless.zero_mem
theorem extendOddly_single_eq_singleLinkForm (inst : DecidableEq (Fin 3 × PositiveEdge a))
    (u : Fin 3) (e : PositiveEdge a) :
    (open Classical in extendOddly fun e' : InfiniteLattice.Link a =>
      if h : e'.IsPositivelyOriented then
        ofPauliCoeffs (Pi.single (u, e) (1 : ℂ) : Fin 3 × PositiveEdge a → ℂ) ⟨e', h⟩
      else 0) = singleLinkForm e.1 (ComplexMatrix2.pauliFamily u) := by
  classical
  unfold singleLinkForm
  congr 1
  funext e'
  by_cases h : e'.IsPositivelyOriented
  · rw [dif_pos h]
    by_cases hee : e' = e.1
    · rw [if_pos hee]
      have : (⟨e', h⟩ : PositiveEdge a) = e := Subtype.ext hee
      rw [this, ofPauliCoeffs_single_same]
    · rw [if_neg hee]
      exact ofPauliCoeffs_single_of_ne u fun h' => hee (congrArg Subtype.val h')
  · have hne : ¬e' = e.1 := fun h' => h (by rw [h']; exact e.2)
    rw [dif_neg h, if_neg hne]
end Forms
variable {L k j : ℕ}
theorem edgeStepKernel_apply (V : Edge L k j → ComplexMatrix2) (u' u : Fin 3)
    (c : PositiveEdge (meshAt L k (j + 1))) (e : PositiveEdge (meshAt L k j)) :
    edgeStepKernel L k j V (u', c) (u, e) =
      pauliCoeff u' (((L : ℝ)⁻¹ •
        (covariantSmoothingDeriv V (singleLinkForm e.1 (ComplexMatrix2.pauliFamily u)) -
          crossingSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
            (singleLinkForm e.1 (ComplexMatrix2.pauliFamily u)))) c.1) := by
  unfold edgeStepKernel PauliComponentsOfSymmetricKernel.kernelOfBasisImages PauliComponentsOfSymmetricKernel.mapOnCoeffs
  exact congrArg (fun B : InfiniteLattice.Link (meshAt L k j) → ComplexMatrix2 =>
    pauliCoeff u' (((L : ℝ)⁻¹ • (covariantSmoothingDeriv V B -
      crossingSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j) B)) c.1))
    (extendOddly_single_eq_singleLinkForm _ u e)
theorem covariantSmoothingDeriv_singleLinkForm_eq_zero {V : Edge L k j → ComplexMatrix2}
    {c : Edge L k (j + 1)} (ha : 0 < meshAt L k j) (h : StepKernelsAt V c) {e : Edge L k j}
    (he : e ∉ positiveDoubleCubeLinks c) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    covariantSmoothingDeriv V (singleLinkForm e X) c = 0 := by
  classical
  rw [h.sum_eq_finsum _ (singleLinkForm_mem_complexEdgeForms ha e hX)]
  refine finsum_eq_zero_of_forall_eq_zero fun e' => ?_
  by_cases he' : e' ∈ positiveDoubleCubeLinks c
  · have hne : ¬e' = e := fun h' => he (by rw [← h']; exact he')
    have hval : singleLinkForm e X e' = 0 := by
      rw [singleLinkForm_apply_of_pos he'.2, if_neg hne]
    rw [hval]
    obtain ⟨T, hT, -⟩ := h.kernel_bound e' he'
    have h0 := hT 0
    have h1 : covariantSmoothingDeriv V (singleLinkForm e' 0) c = 0 := by
      simpa using h0.symm
    simp [he', h1]
  · simp [he']
theorem operatorNorm_real_smul (r : ℝ) (D : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (r • D) = |r| * ComplexMatrix2.operatorNorm D := by apply _root_.YangMills.Construction.Tower.IteratedMeanBounds.operatorNorm_real_smul <;> assumption
theorem pauliCoeff_zero (hNorm : PauliCoefficientNorm.Claim) (u : Fin 3) :
    pauliCoeff u (0 : ComplexMatrix2) = 0 := by
  have h := norm_pauliCoeff_le hNorm u 0
  have h0 : ComplexMatrix2.operatorNorm (0 : ComplexMatrix2) = 0 := norm_zero
  rw [h0] at h
  exact norm_le_zero_iff.1 h
theorem smoothingDifference_apply_of_mem (inst : DecidableEq (Fin 3 × Vertex L k j))
    (V : Edge L k j → ComplexMatrix2) (u : Fin 3) (y : Vertex L k (j + 1)) (x : Vertex L k j)
    (hx : x ∈ cubeVertices L (meshAt L k j) y) :
    (adjointCubeAverage V (ofPauliCoeffs (Pi.single (u, x) (1 : ℂ))) -
      vertexSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
        (ofPauliCoeffs (Pi.single (u, x) (1 : ℂ)))) y =
      PeriodicLattice.inverseFourthPowerWeight L •
        (ComplexMatrix2.conjugateBy (complexContourMean L V y x) (ComplexMatrix2.pauliFamily u) -
          ComplexMatrix2.pauliFamily u) := by
  show adjointCubeAverage V _ y - vertexSmoothing L _ y = _
  unfold adjointCubeAverage vertexSmoothing
  rw [finsum_mem_eq_of_support_single hx fun x' h => by
      rw [ofPauliCoeffs_single_of_ne u h]
      simp [ComplexMatrix2.conjugateBy],
    finsum_mem_eq_of_support_single hx fun x' h => ofPauliCoeffs_single_of_ne u h,
    ofPauliCoeffs_single_same, smul_sub]
theorem smoothingDifference_apply_of_not_mem (inst : DecidableEq (Fin 3 × Vertex L k j))
    (V : Edge L k j → ComplexMatrix2) (u : Fin 3) (y : Vertex L k (j + 1)) (x : Vertex L k j)
    (hx : x ∉ cubeVertices L (meshAt L k j) y) :
    (adjointCubeAverage V (ofPauliCoeffs (Pi.single (u, x) (1 : ℂ))) -
      vertexSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
        (ofPauliCoeffs (Pi.single (u, x) (1 : ℂ)))) y = 0 := by
  show adjointCubeAverage V _ y - vertexSmoothing L _ y = _
  unfold adjointCubeAverage vertexSmoothing
  rw [finsum_mem_eq_zero_of_support_single hx fun x' h => by
      rw [ofPauliCoeffs_single_of_ne u h]
      simp [ComplexMatrix2.conjugateBy],
    finsum_mem_eq_zero_of_support_single hx fun x' h => ofPauliCoeffs_single_of_ne u h, sub_self]
theorem vertexStepKernel_apply_of_mem (V : Edge L k j → ComplexMatrix2) (u' u : Fin 3)
    (y : Vertex L k (j + 1)) (x : Vertex L k j)
    (hx : x ∈ cubeVertices L (meshAt L k j) y) :
    vertexStepKernel L k j V (u', y) (u, x) =
      pauliCoeff u' (PeriodicLattice.inverseFourthPowerWeight L •
        (ComplexMatrix2.conjugateBy (complexContourMean L V y x) (ComplexMatrix2.pauliFamily u) -
          ComplexMatrix2.pauliFamily u)) := by
  unfold vertexStepKernel PauliComponentsOfSymmetricKernel.kernelOfBasisImages PauliComponentsOfSymmetricKernel.mapOnCoeffs
  exact congrArg (pauliCoeff u') (smoothingDifference_apply_of_mem _ V u y x hx)
theorem vertexStepKernel_apply_of_not_mem (V : Edge L k j → ComplexMatrix2) (u' u : Fin 3)
    (y : Vertex L k (j + 1)) (x : Vertex L k j)
    (hx : x ∉ cubeVertices L (meshAt L k j) y) :
    vertexStepKernel L k j V (u', y) (u, x) = pauliCoeff u' 0 := by
  unfold vertexStepKernel PauliComponentsOfSymmetricKernel.kernelOfBasisImages PauliComponentsOfSymmetricKernel.mapOnCoeffs
  exact congrArg (pauliCoeff u') (smoothingDifference_apply_of_not_mem _ V u y x hx)
theorem bound_holds (hSchur : SchurTest.Holds) (hCubes : BlockPathContourPivotStatement)
    (hNorm : PauliCoefficientNorm.Claim) (hKer : StepKernels.StepKernelBounds)
    (hNear : StepKernelsNearIdentity.Claim) (hOne : SmoothingStepAtOne) : Bound := by
  classical
  intro L hL k j hj V hV hsmall s hs
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have hmesh : ∀ i, 0 < meshAt L k i := fun i => zpow_pos hLr _
  have hscale : meshAt L k (j + 1) = (L : ℝ) * meshAt L k j := by
    unfold meshAt
    rw [show ((j + 1 : ℕ) : ℤ) - (k : ℤ) = 1 + ((j : ℤ) - (k : ℤ)) by push_cast; ring,
      zpow_add₀ hLr.ne', zpow_one]
  have hs0 : 0 ≤ s := (norm_nonneg _).trans (hs (InfiniteLattice.Link.forwardFrom 0 0))
  have hρ : 0 < polydiscRadius L := by
    have h1 := hsmall (InfiniteLattice.Link.forwardFrom 0 0)
    have h2 : 0 ≤ ComplexMatrix2.operatorNorm (V (InfiniteLattice.Link.forwardFrom 0 0) - 1) :=
      norm_nonneg _
    linarith
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = 1280 * (polydiscRadius L)⁻¹ ^ 2 * s := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    positivity
  have hC : smoothingStepConstant L * s = (12 * (L : ℝ) ^ 3 + 2) * (2 * κ) := by
    unfold smoothingStepConstant
    rw [hκ]
    ring
  have hC0 : 0 ≤ smoothingStepConstant L * s := by
    rw [hC]
    positivity
  have hnearV : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented → NearIdentityBounds V c s :=
    fun c hcp => hNear L hL k j hj c hcp V hV hsmall s fun e _ => hs e
  have hkerV : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented → StepKernelsAt V c :=
    fun c hcp => hKer L hL k j hj c hcp V hV fun e => by
      have := hsmall e
      linarith
  have hone : (fun _ => (1 : ComplexMatrix2)) ∈
      fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    ⟨fun _ => by simp [PeriodicLattice.complexGaugeGroup, ComplexMatrix2.unitDeterminant],
      fun _ => by simp⟩
  have hker1 : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      StepKernelsAt (fun _ : Edge L k j => (1 : ComplexMatrix2)) c :=
    fun c hcp => hKer L hL k j hj c hcp _ hone fun _ => by
      have h0 : ComplexMatrix2.operatorNorm ((1 : ComplexMatrix2) - 1) = 0 := by
        rw [sub_self]
        exact norm_zero
      rw [h0]
      positivity
  have hk : 1 ≤ k := by omega
  constructor
  · have hAdj : AdjacentCubesBounds L k 1 (j + 1) :=
      (hCubes L hL k 1 (j + 1) hk (by omega) (by omega)).2.2.2.2.2.1
    have hentry : ∀ (u' u : Fin 3) (c : PositiveEdge (meshAt L k (j + 1)))
        (e : PositiveEdge (meshAt L k j)),
        edgeStepKernel L k j V (u', c) (u, e) =
          pauliCoeff u' ((L : ℝ)⁻¹ •
            (covariantSmoothingDeriv V (singleLinkForm e.1 (ComplexMatrix2.pauliFamily u)) c.1 -
              covariantSmoothingDeriv (fun _ : Edge L k j => (1 : ComplexMatrix2))
                (singleLinkForm e.1 (ComplexMatrix2.pauliFamily u)) c.1)) := by
      intro u' u c e
      rw [edgeStepKernel_apply, ← ((hOne L hL k j hj).1 _
        (singleLinkForm_mem_edgeFormSpace (hmesh j) e.1
          (pauliFamily_mem_hermitianTraceless u))).2.2]
      rfl
    obtain ⟨M, hM⟩ : ∃ M, M = (L : ℝ)⁻¹ * κ := ⟨_, rfl⟩
    have hM0 : 0 ≤ M := by
      rw [hM]
      positivity
    have hLM : (L : ℝ) * M = κ := by
      rw [hM, ← mul_assoc, mul_inv_cancel₀ hLr.ne', one_mul]
    have hzero : ∀ (u' : Fin 3) (c : PositiveEdge (meshAt L k (j + 1))) (u : Fin 3)
        (e : PositiveEdge (meshAt L k j)),
        e ∉ {e : PositiveEdge (meshAt L k j) | e.1 ∈ positiveDoubleCubeLinks c.1} →
        edgeStepKernel L k j V (u', c) (u, e) = 0 := by
      intro u' c u e he
      rw [hentry, covariantSmoothingDeriv_singleLinkForm_eq_zero (hmesh j) (hkerV c.1 c.2) he
          (pauliFamily_mem_traceless u),
        covariantSmoothingDeriv_singleLinkForm_eq_zero (hmesh j) (hker1 c.1 c.2) he
          (pauliFamily_mem_traceless u),
        sub_self, smul_zero, pauliCoeff_zero hNorm]
    have hbound : ∀ (ι' : Fin 3 × PositiveEdge (meshAt L k (j + 1)))
        (ι : Fin 3 × PositiveEdge (meshAt L k j)),
        ‖edgeStepKernel L k j V ι' ι‖ ≤ M := by
      rintro ⟨u', c⟩ ⟨u, e⟩
      by_cases he : e.1 ∈ positiveDoubleCubeLinks c.1
      · rw [hentry]
        refine (norm_pauliCoeff_le hNorm u' _).trans ?_
        rw [operatorNorm_real_smul, abs_of_nonneg (by positivity), hM]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := (hnearV c.1 c.2).kernel_le e.1 he
          ⟨ComplexMatrix2.pauliFamily u, pauliFamily_mem_traceless u⟩
        rw [show ComplexMatrix2.operatorNorm
            ((⟨ComplexMatrix2.pauliFamily u, pauliFamily_mem_traceless u⟩ :
              ↥ComplexMatrix2.traceless) : ComplexMatrix2) = 1 from
          operatorNorm_pauliFamily u, mul_one] at h
        rw [hκ]
        exact h
      · rw [hzero u' c u e he, norm_zero]
        exact hM0
    have hrow : ∀ c : PositiveEdge (meshAt L k (j + 1)),
        {e : PositiveEdge (meshAt L k j) | e.1 ∈ positiveDoubleCubeLinks c.1}.encard ≤
          ((8 * L ^ (4 * 1) : ℕ) : ℕ∞) := by
      intro c
      rw [← Subtype.val_injective.encard_image]
      refine (Set.encard_le_encard ?_).trans (hAdj.bonds_encard_le c.1 c.2)
      rintro _ ⟨e, he, rfl⟩
      exact ⟨e.2, he.1.1, he.1.2⟩
    have hcol : ∀ e : PositiveEdge (meshAt L k j),
        {c : PositiveEdge (meshAt L k (j + 1)) |
          e ∈ {e : PositiveEdge (meshAt L k j) | e.1 ∈ positiveDoubleCubeLinks c.1}}.encard ≤
          ((8 : ℕ) : ℕ∞) := by
      intro e
      rw [← Subtype.val_injective.encard_image]
      refine (Set.encard_le_encard ?_).trans (hAdj.encard_le_eight e.1)
      rintro _ ⟨c, he, rfl⟩
      exact ⟨c.2, he.1.1, he.1.2⟩
    have hprod : meshAt L k (j + 1) ^ 4 *
        ((3 * ((8 * L ^ (4 * 1) : ℕ) : ℝ) * M) * (3 * ((8 : ℕ) : ℝ) * M)) ≤
          (smoothingStepConstant L * s) ^ 2 * meshAt L k j ^ 4 := by
      have hrw : meshAt L k (j + 1) ^ 4 *
          ((3 * ((8 * L ^ (4 * 1) : ℕ) : ℝ) * M) * (3 * ((8 : ℕ) : ℝ) * M)) =
            (576 * (L : ℝ) ^ 6 * κ ^ 2) * meshAt L k j ^ 4 := by
        rw [hscale, ← hLM]
        push_cast
        ring
      rw [hrw]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (hmesh j).le 4)
      rw [hC]
      have h1 : 24 * (L : ℝ) ^ 3 * κ ≤ (12 * (L : ℝ) ^ 3 + 2) * (2 * κ) := by
        nlinarith
      calc 576 * (L : ℝ) ^ 6 * κ ^ 2 = (24 * (L : ℝ) ^ 3 * κ) ^ 2 := by ring
        _ ≤ ((12 * (L : ℝ) ^ 3 + 2) * (2 * κ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
    have key := schurTest_of_finite_support (σ := PositiveEdge (meshAt L k j))
      (σ' := PositiveEdge (meshAt L k (j + 1))) hSchur
      (edgeStepKernel L k j V) (colourEdges L k j).weightOf
      (colourEdges L k (j + 1)).weightOf (meshAt L k j ^ 4)
      (meshAt L k (j + 1) ^ 4) M (smoothingStepConstant L * s) (8 * L ^ (4 * 1)) 8
      (fun c => {e | e.1 ∈ positiveDoubleCubeLinks c.1})
      (pow_pos (hmesh j) 4) (pow_pos (hmesh (j + 1)) 4) hC0 hM0 (fun _ => rfl) (fun _ => rfl)
      (fun u' c u e he => hzero u' c u e he) hbound hrow hcol hprod
    exact ⟨fun f hf => key.1 f hf, (key.2 _).1, (key.2 _).2⟩
  · have hPart : RefinedCubesPartition L k 1 (j + 1) :=
      (hCubes L hL k 1 (j + 1) hk (by omega) (by omega)).2.1
    have hsub : ∀ y : Vertex L k (j + 1),
        cubeOfOrder L (meshAt L k j) 1 y ⊆
          (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set InfiniteLattice.AmbientSpace) :=
      hPart.subset_sublattice
    have hnc : ∀ y : Vertex L k (j + 1),
        (cubeOfOrder L (meshAt L k j) 1 y).ncard = L ^ (4 * 1) := hPart.ncard_eq
    have hex : ∀ x : Vertex L k j, ∃! y : Vertex L k (j + 1),
        (x : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k j) 1 y :=
      hPart.existsUnique_mem
    have himg : ∀ y : Vertex L k (j + 1),
        Subtype.val '' cubeVertices L (meshAt L k j) y = cubeOfOrder L (meshAt L k j) 1 y := by
      intro y
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hp
        exact ⟨⟨p, hsub y hp⟩, hp, rfl⟩
    have hcard : ∀ y : Vertex L k (j + 1), (cubeVertices L (meshAt L k j) y).ncard = L ^ 4 := by
      intro y
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg y, hnc y]
    have hfin : ∀ y : Vertex L k (j + 1), (cubeVertices L (meshAt L k j) y).Finite := by
      intro y
      refine Set.finite_of_ncard_pos ?_
      rw [hcard y]
      positivity
    have hW : 0 < (L : ℝ) ^ (-4 : ℤ) := zpow_pos hLr _
    have hLW : (L : ℝ) ^ 4 * (L : ℝ) ^ (-4 : ℤ) = 1 := by
      rw [show (-4 : ℤ) = -((4 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
      exact mul_inv_cancel₀ (pow_ne_zero _ hLr.ne')
    obtain ⟨M, hM⟩ : ∃ M, M = (L : ℝ) ^ (-4 : ℤ) * κ := ⟨_, rfl⟩
    have hM0 : 0 ≤ M := by
      rw [hM]
      positivity
    have hLM : (L : ℝ) ^ 4 * M = κ := by
      rw [hM, ← mul_assoc, hLW, one_mul]
    have hzero : ∀ (u' : Fin 3) (y : Vertex L k (j + 1)) (u : Fin 3) (x : Vertex L k j),
        x ∉ cubeVertices L (meshAt L k j) y →
        vertexStepKernel L k j V (u', y) (u, x) = 0 := by
      intro u' y u x hx
      rw [vertexStepKernel_apply_of_not_mem V u' u y x hx, pauliCoeff_zero hNorm]
    have hbound : ∀ (ι' : Fin 3 × Vertex L k (j + 1)) (ι : Fin 3 × Vertex L k j),
        ‖vertexStepKernel L k j V ι' ι‖ ≤ M := by
      rintro ⟨u', y⟩ ⟨u, x⟩
      by_cases hx : x ∈ cubeVertices L (meshAt L k j) y
      · rw [vertexStepKernel_apply_of_mem V u' u y x hx]
        refine (norm_pauliCoeff_le hNorm u' _).trans ?_
        have hw : ‖PeriodicLattice.inverseFourthPowerWeight L‖ = (L : ℝ) ^ (-4 : ℤ) := by
          unfold PeriodicLattice.inverseFourthPowerWeight
          rw [Complex.norm_real, Real.norm_of_nonneg hW.le]
        show ‖PeriodicLattice.inverseFourthPowerWeight L • _‖ ≤ M
        rw [norm_smul, hw, hM]
        refine mul_le_mul_of_nonneg_left ?_ hW.le
        have hcp : (InfiniteLattice.Link.forwardFrom y 0).IsPositivelyOriented :=
          ⟨0, by
            show y + InfiniteLattice.axisStep _ 0 - y = InfiniteLattice.axisStep _ 0
            abel⟩
        have h := (hnearV _ hcp).conj_le y (Or.inl rfl) x hx
          ⟨ComplexMatrix2.pauliFamily u, pauliFamily_mem_traceless u⟩
        rw [show ComplexMatrix2.operatorNorm
            ((⟨ComplexMatrix2.pauliFamily u, pauliFamily_mem_traceless u⟩ :
              ↥ComplexMatrix2.traceless) : ComplexMatrix2) = 1 from
          operatorNorm_pauliFamily u, mul_one] at h
        rw [hκ]
        exact h
      · rw [hzero u' y u x hx, norm_zero]
        exact hM0
    have hrow : ∀ y : Vertex L k (j + 1),
        (cubeVertices L (meshAt L k j) y).encard ≤ ((L ^ 4 : ℕ) : ℕ∞) := by
      intro y
      rw [← (hfin y).cast_ncard_eq, hcard y]
    have hcol : ∀ x : Vertex L k j,
        {y : Vertex L k (j + 1) | x ∈ cubeVertices L (meshAt L k j) y}.encard ≤
          ((1 : ℕ) : ℕ∞) := by
      intro x
      obtain ⟨y₀, -, huniq⟩ := hex x
      rw [Nat.cast_one, Set.encard_le_one_iff]
      intro y y' hy hy'
      rw [huniq y hy, huniq y' hy']
    have hprod : meshAt L k (j + 1) ^ 4 *
        ((3 * ((L ^ 4 : ℕ) : ℝ) * M) * (3 * ((1 : ℕ) : ℝ) * M)) ≤
          (smoothingStepConstant L * s) ^ 2 * meshAt L k j ^ 4 := by
      have hrw : meshAt L k (j + 1) ^ 4 *
          ((3 * ((L ^ 4 : ℕ) : ℝ) * M) * (3 * ((1 : ℕ) : ℝ) * M)) =
            (9 * κ ^ 2) * meshAt L k j ^ 4 := by
        rw [hscale, ← hLM]
        push_cast
        ring
      rw [hrw]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (hmesh j).le 4)
      rw [hC]
      have h1 : 3 * κ ≤ (12 * (L : ℝ) ^ 3 + 2) * (2 * κ) := by
        have : 0 ≤ (L : ℝ) ^ 3 * κ := by positivity
        nlinarith
      calc 9 * κ ^ 2 = (3 * κ) ^ 2 := by ring
        _ ≤ ((12 * (L : ℝ) ^ 3 + 2) * (2 * κ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
    have key := schurTest_of_finite_support (σ := Vertex L k j) (σ' := Vertex L k (j + 1)) hSchur
      (vertexStepKernel L k j V) (colourVertices L k j).weightOf
      (colourVertices L k (j + 1)).weightOf (meshAt L k j ^ 4)
      (meshAt L k (j + 1) ^ 4) M (smoothingStepConstant L * s) (L ^ 4) 1
      (fun y => cubeVertices L (meshAt L k j) y)
      (pow_pos (hmesh j) 4) (pow_pos (hmesh (j + 1)) 4) hC0 hM0 (fun _ => rfl) (fun _ => rfl)
      (fun u' y u x hx => hzero u' y u x hx) hbound hrow hcol hprod
    exact ⟨fun f hf => key.1 f hf, (key.2 _).1, (key.2 _).2⟩
end YangMills.Construction.Tower.FullSpace.IterStepsNearFree
end
