import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.ComplexAnalysis.MontelSeveralVariables
import YangMills.Construction.EuclideanFunctionals.VectorsOfPlatesAndTheProductFormula
import YangMills.Construction.RotationInvariance.OneFunctionOnAllTubesProof
import YangMills.Construction.RotationInvariance.RadialBumpsExistAndMollifyInC1
import YangMills.Construction.RotationInvariance.SmearingOfPlatesByRadialBumps
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set Topology
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube
open Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
namespace EuclideanFunctionals.PlaneKernelProps
theorem continuous_embedPlane : Continuous embedPlane := by apply _root_.YangMills.Construction.ForwardTube.ProductIntegralDetermination.continuous_embedPlane <;> assumption
theorem continuous_embed_successiveDifferences (q : ℕ) :
    Continuous fun y : Fin (q + 1) → RealPlane => embedPlaneTuple (successiveDifferences y) :=
  continuous_pi fun _ => continuous_embedPlane.comp ((continuous_apply _).sub (continuous_apply _))
theorem continuous_pairTupleEquiv (p : ℕ) : Continuous (pairTupleEquiv p) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.continuous_pairTupleEquiv <;> assumption
theorem isOpen_pairTupleEquiv_image {p : ℕ} {O : Set (Fin p → ℂ × ℂ)} (hO : IsOpen O) :
    IsOpen (pairTupleEquiv p '' O) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeUnionHarmonicsProof.isOpen_image_pairTupleEquiv <;> assumption
theorem scalarEquiv_apply (c : ℂ) (i : Fin 1) : scalarEquiv c i = c := by apply _root_.YangMills.DeltaSharedProofs.p23888 <;> assumption
theorem scalarEquiv_comp {X : Type*} (f : X → ℂ) :
    scalarEquiv ∘ f = fun x _ => f x := by
  funext x i
  exact scalarEquiv_apply _ _
variable {p : ℕ} {U U' : Set (Fin p → ℂ × ℂ)} {f g : (Fin p → ℂ × ℂ) → ℂ}
theorem holomorphicOnTuples_continuousOn (h : HolomorphicOnTuples U f) : ContinuousOn f U := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicRotationCovariance.continuousOn_of_holomorphicOnTuples <;> assumption
theorem holomorphicOnTuples_mono (h : HolomorphicOnTuples U f) (hU' : IsOpen U') (hs : U' ⊆ U) :
    HolomorphicOnTuples U' f :=
  ⟨isOpen_pairTupleEquiv_image hU', h.2.1.mono (image_mono hs),
    fun a ha j => h.2.2 a (image_mono hs ha) j⟩
theorem holomorphicOnTuples_sub (hf : HolomorphicOnTuples U f) (hg : HolomorphicOnTuples U g) :
    HolomorphicOnTuples U fun v => f v - g v := by apply _root_.YangMills.Construction.EuclideanFunctionals.UnionKernel.holomorphicOnTuples_sub <;> assumption
theorem isHolomorphicIn_of_locally {N N' : ℕ} {W : Set (Coordinates.ComplexCoordinates N)}
    (hW : IsOpen W) {F : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (h : ∀ w ∈ W, ∃ (V : Set (Coordinates.ComplexCoordinates N))
      (G : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'),
      w ∈ V ∧ Coordinates.ComplexCoordinates.IsHolomorphicIn V G ∧ ∀ z ∈ V, F z = G z) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn W F := by
  refine ⟨hW, fun w hw => ?_, fun a ha j => ?_⟩
  · obtain ⟨V, G, hwV, hG, hFG⟩ := h w hw
    have hVn : V ∈ 𝓝 w := hG.1.mem_nhds hwV
    have hcont : ContinuousAt G w := hG.2.1.continuousAt hVn
    have heq : F =ᶠ[𝓝 w] G := by
      filter_upwards [hVn] with z hz using hFG z hz
    exact (hcont.congr heq.symm).continuousWithinAt
  · obtain ⟨V, G, haV, hG, hFG⟩ := h a ha
    have hcont : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈ V := by
      apply hcont.continuousAt.eventually_mem
      simpa using hG.1.mem_nhds haV
    filter_upwards [hG.2.2 a haV j, hnear.eventually_nhds] with ζ hd hz
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hz] with ζ' hζ' using hFG _ hζ'
theorem holomorphicOnTuples_of_locally (hU : IsOpen U)
    (h : ∀ a ∈ U, ∃ (V : Set (Fin p → ℂ × ℂ)) (G : (Fin p → ℂ × ℂ) → ℂ), IsOpen V ∧ a ∈ V ∧
      HolomorphicOnTuples V G ∧ ∀ v ∈ V, f v = G v) :
    HolomorphicOnTuples U f := by
  refine isHolomorphicIn_of_locally (isOpen_pairTupleEquiv_image hU) ?_
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨V, G, -, haV, hG, hfG⟩ := h a ha
  refine ⟨pairTupleEquiv p '' V, scalarEquiv ∘ G ∘ (pairTupleEquiv p).symm,
    mem_image_of_mem _ haV, hG, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  simp [hfG v hv]
theorem montel_holomorphicOnTuples (hM : ComplexAnalysis.MontelSeveralVariables) (hp : 1 ≤ p)
    (hU : IsOpen U) (F : ℕ → (Fin p → ℂ × ℂ) → ℂ) (hF : ∀ j, HolomorphicOnTuples U (F j))
    {B : ℝ} (hB : ∀ j, ∀ v ∈ U, ‖F j v‖ ≤ B) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ G : (Fin p → ℂ × ℂ) → ℂ, HolomorphicOnTuples U G ∧
      ∀ C : Set (Fin p → ℂ × ℂ), C ⊆ U → IsCompact C →
        TendstoUniformlyOn (fun l => F (ψ l)) G atTop C := by
  have hhol : ∀ j, 1 ≤ j → Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
      (pairTupleEquiv p '' U) fun z _ => F j ((pairTupleEquiv p).symm z) := by
    intro j _
    have h := hF j
    have h' : Coordinates.ComplexCoordinates.IsHolomorphicIn (pairTupleEquiv p '' U)
      (scalarEquiv ∘ (F j ∘ (pairTupleEquiv p).symm)) := h
    rwa [scalarEquiv_comp] at h'
  obtain ⟨ψ, hψ, -, g, hg, hu⟩ := hM (p * 2) (by omega) (pairTupleEquiv p '' U)
    (isOpen_pairTupleEquiv_image hU) (fun j z => F j ((pairTupleEquiv p).symm z)) hhol
    ⟨B, fun j _ z hz => by
      obtain ⟨v, hv, rfl⟩ := hz
      simpa using hB j v hv⟩
  refine ⟨ψ, hψ, fun v => g (pairTupleEquiv p v), ?_, fun C hC hCc => ?_⟩
  · show Coordinates.ComplexCoordinates.IsHolomorphicIn _
      (scalarEquiv ∘ ((fun v => g (pairTupleEquiv p v)) ∘ (pairTupleEquiv p).symm))
    rw [scalarEquiv_comp]
    simpa using hg
  · have h := (hu (pairTupleEquiv p '' C) (image_mono hC)
      (hCc.image (continuous_pairTupleEquiv p))).comp (pairTupleEquiv p)
    rw [(pairTupleEquiv p).injective.preimage_image] at h
    simpa [Function.comp_def] using h
section Integrals
variable {n : ℕ} {α : Fin n → RealPlane → ℂ}
theorem isCompact_pi_tsupport (hs : ∀ i, HasCompactSupport (α i)) :
    IsCompact (Set.univ.pi fun i => tsupport (α i)) :=
  isCompact_univ_pi fun i => hs i
theorem integrable_profileIntegrand (hc : ∀ i, Continuous (α i))
    (hs : ∀ i, HasCompactSupport (α i)) {F : (Fin n → RealPlane) → ℂ}
    (hF : ContinuousOn F (Set.univ.pi fun i => tsupport (α i))) :
    Integrable (profileIntegrand α F) := by apply _root_.YangMills.Construction.EuclideanFunctionals.AngleFunctionOnPencil.integrable_profileIntegrand <;> assumption
theorem profileIntegral_sub (hc : ∀ i, Continuous (α i))
    (hs : ∀ i, HasCompactSupport (α i)) {F G : (Fin n → RealPlane) → ℂ}
    (hF : ContinuousOn F (Set.univ.pi fun i => tsupport (α i)))
    (hG : ContinuousOn G (Set.univ.pi fun i => tsupport (α i))) :
    profileIntegral α (fun y => F y - G y) =
      profileIntegral α F - profileIntegral α G := by
  unfold profileIntegral
  rw [← integral_sub (integrable_profileIntegrand hc hs hF) (integrable_profileIntegrand hc hs hG)]
  congr 1
  funext y
  by_cases hy : y ∈ Set.univ.pi fun i => tsupport (α i)
  · simp [profileIntegrand, indicator_of_mem hy, mul_sub]
  · simp [profileIntegrand, indicator_of_notMem hy]
theorem profileIntegral_congr {F G : (Fin n → RealPlane) → ℂ}
    (h : ∀ y ∈ Set.univ.pi (fun i => tsupport (α i)), F y = G y) :
    profileIntegral α F = profileIntegral α G := by
  unfold profileIntegral
  congr 1
  funext y
  by_cases hy : y ∈ Set.univ.pi fun i => tsupport (α i)
  · simp [profileIntegrand, indicator_of_mem hy, h y hy]
  · simp [profileIntegrand, indicator_of_notMem hy]
end Integrals
section OneLength
variable {m : SharpScale} {S : ConnFamily} {q : ℕ}
def IsKernelAtLength (S : ConnFamily) (φ : Fin (q + 1) → realLabels) (η : ℝ)
    (K : (Fin q → ℂ × ℂ) → ℂ) : Prop :=
  ∀ b : Fin (q + 1) → RealPlane → ℂ, (∀ i, b i ∈ complexProfiles) → TimeSeparated η b →
    centeredFnAtProducts S b φ = differenceIntegral b K
theorem timeSeparated_mono {n : ℕ} {η η' : ℝ} (h : η' ≤ η) {b : Fin n → RealPlane → ℂ}
    (hb : TimeSeparated η b) : TimeSeparated η' b :=
  ⟨hb.1, hb.2.1, hb.2.2.1, fun i hi => lt_of_le_of_lt h (hb.2.2.2 i hi)⟩
theorem eq_of_isKernelAtLength (hD : HolomorphicDifferences.determinedByProductIntegrals)
    (hq : 1 ≤ q) (φ : Fin (q + 1) → realLabels) {η : ℝ} (hη : 0 ≤ η) {D : Set (Fin q → ℂ × ℂ)}
    (hDo : IsOpen D) (hDc : IsConnected D)
    (hU : ∀ v ∈ realTuplesTimeAbove q η, complexifyRealTuple v ∈ D)
    {K K' : (Fin q → ℂ × ℂ) → ℂ} (hK : HolomorphicOnTuples D K)
    (hK' : HolomorphicOnTuples D K') (hd : IsKernelAtLength S φ η K)
    (hd' : IsKernelAtLength S φ η K') : ∀ v ∈ D, K v = K' v := by
  obtain ⟨hA, hB⟩ := hD (q + 1) (by omega) η hη
  have hfull := (hB D (fun v => K v - K' v) hDo hDc hU (holomorphicOnTuples_sub hK hK')).1 ?_
  · intro v hv
    exact sub_eq_zero.1 (hfull v hv)
  · intro b hb
    have hprof : ∀ i, complexifyProfiles b i ∈ complexProfiles := fun i =>
      ⟨Complex.ofRealCLM.contDiff.comp ((hb.1 i).of_le (by exact_mod_cast le_top)), hb.2.2.1 i⟩
    have hcont : ∀ L : (Fin q → ℂ × ℂ) → ℂ, HolomorphicOnTuples D L →
        ContinuousOn (fun y : Fin (q + 1) → RealPlane => L (embedPlaneTuple (successiveDifferences y)))
          (Set.univ.pi fun i => tsupport (complexifyProfiles b i)) := fun L hL =>
      (holomorphicOnTuples_continuousOn hL).comp
        (continuous_embed_successiveDifferences q).continuousOn
        fun y hy => hU _ (hA _ hb.2 y fun i => hy i (mem_univ i))
    have e1 := hd _ hprof hb.2
    have e2 := hd' _ hprof hb.2
    have e3 := profileIntegral_sub (fun i => (hprof i).1.continuous) (fun i => (hprof i).2)
      (hcont K hK) (hcont K' hK')
    show profileIntegral _
      (fun y : Fin (q + 1) → RealPlane => K (embedPlaneTuple (successiveDifferences y)) -
        K' (embedPlaneTuple (successiveDifferences y))) = 0
    rw [e3]
    exact sub_eq_zero.2 (e1.symm.trans e2)
def kernelBound (d : PlaneDataWithAperture m S) (φ : Fin (q + 1) → realLabels) (η : ℝ) : ℝ :=
  (∏ i, d.base.labelConst (φ i)) *
    RealPower.rpowPos η (-(d.base.expo * ((q + 1 : ℕ) : ℝ)))
variable (d : PlaneDataWithAperture m S) (φ : Fin (q + 1) → realLabels)
theorem mollifiedKernel_holomorphic_bound (hP : PlateVectorsProduct.Holds) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) {δ : ℕ+ → RealPlane → ℝ} (hδ : d.IsRadialMollifier η δ) (j : ℕ+) :
    HolomorphicOnTuples (shiftedForwardTubePow q η)
        (d.mollifiedKernel η δ (fun i => (φ i : RealPlane → ℝ)) j) ∧
      ∀ v ∈ shiftedForwardTubePow q η,
        ‖d.mollifiedKernel η δ (fun i => (φ i : RealPlane → ℝ)) j v‖ ≤ kernelBound d φ η := by
  classical
  let C : (RealPlane → ℝ) → ℝ := fun f =>
    if h : f ∈ realLabels then d.base.labelConst ⟨f, h⟩ else 0
  have hC : ∀ f ∈ realLabels, ProductBoundWith d.base.sigma d.base.expo_pos
      d.base.frac_mem f (C f) := by
    intro f hf
    simp only [C, dif_pos hf]
    exact d.base.boundWith_labelConst ⟨f, hf⟩
  have hPF := (hP m S d.base.sigma d.base.expo d.base.frac
    d.base.expo_pos d.base.frac_mem C d.base.productBoundWithExponent hC
    d.base.cone η hη0 hη1).2 q (fun _ => ofRealFun (δ j))
    (fun i => (φ i : RealPlane → ℝ))
    (fun a => ⟨(φ a).2, (hδ.ofRealFun_mem hη0 j).1, (hδ.ofRealFun_mem hη0 j).2⟩)
  refine ⟨hPF.1, fun v hv => (hPF.2.1 v hv).trans (le_of_eq ?_)⟩
  have hnorm : profileL1Norm (ofRealFun (δ j)) = 1 := by
    unfold profileL1Norm
    rw [← hδ.integral_eq_one j]
    congr 1
    funext y
    simp [ofRealFun, abs_of_nonneg (hδ.nonneg j y)]
  have hCφ : ∀ a, C (φ a : RealPlane → ℝ) = d.base.labelConst (φ a) := by
    intro a
    simp only [C, dif_pos (φ a).2]
  unfold PlateVectorsProduct.plateFactorProduct kernelBound
  simp only [hnorm, mul_one, hCφ]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [RealPower.rpowPos, if_pos hη0]
  rw [← Real.exp_nat_mul]
  congr 1
  ring
theorem exists_common_ball_radius {n : ℕ} {A : Fin n → Set R4} (hA : ∀ i, IsCompact (A i)) :
    ∃ R : ℝ, 0 < R ∧ ∀ l, ∃ x, A l ⊆ TestFunctions.closedBallR4 x R := by
  have hcont : Continuous fun x : R4 => TorusMetric.euclidNormVec (x - 0) := by
    unfold TorusMetric.euclidNormVec
    fun_prop
  choose C hC using fun i => (hA i).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨1 + ∑ i, |C i|, by positivity, fun l => ⟨0, fun x hx => ?_⟩⟩
  have h1 := hC l x hx
  have h2 : |C l| ≤ ∑ i, |C i| :=
    Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ l)
  have h3 := le_abs_self (C l)
  have h4 := le_abs_self (TorusMetric.euclidNormVec (x - 0))
  rw [Real.norm_eq_abs] at h1
  show TorusMetric.euclidNormVec (x - 0) ≤ _
  linarith
theorem isKernelAtLength_of_tendsto (hS : PlateSmearing.PlateSmearingStatement)
    (hMol : RadialMollifiers.ExistAndConvergeC1)
    (hMom : Moments.MomentBoundsTheorem)
    (hR : TranslationRules.TranslationAndMotionFacts) (hq : 1 ≤ q)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {δ : ℕ+ → RealPlane → ℝ}
    (hδ : d.IsRadialMollifier η δ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    {G : (Fin q → ℂ × ℂ) → ℂ} {B : ℝ}
    (hcont : ∀ j, ContinuousOn (d.mollifiedKernel η δ (fun i => (φ i : RealPlane → ℝ)) j)
      (shiftedForwardTubePow q η))
    (hB : ∀ j, ∀ v ∈ shiftedForwardTubePow q η,
      ‖d.mollifiedKernel η δ (fun i => (φ i : RealPlane → ℝ)) j v‖ ≤ B)
    (hconv : ∀ v ∈ shiftedForwardTubePow q η,
      Tendsto (fun l => d.mollifiedKernel η δ (fun i => (φ i : RealPlane → ℝ))
        (ψ l).succPNat v) atTop (𝓝 (G v))) :
    IsKernelAtLength S φ η G := by
  intro b hb hgap
  obtain ⟨⟨A, hAc, hAd, hAs⟩, hidx⟩ := hS m S d q hq (fun i => (φ i : RealPlane → ℝ))
    (fun i => (φ i).2) η hη0 hη1 δ hδ b hb hgap
  obtain ⟨R, hRpos, hball⟩ := exists_common_ball_radius hAc
  have hsep : Moments.SeparatedInBalls A R (η / 2) :=
    ⟨hball, hAd⟩
  have hent : Moments.EntriesSupportedIn A fun i => productFunction (b i) (φ i) :=
    fun l => ⟨(hR.2.2.1 (b l) (hb l) (φ l) (φ l).2).1, (hAs l).1⟩
  have hmc := (hMom m S d.base.sigma (q + 1) (by omega) R (η / 2) hRpos (by positivity)
    A hsep _ _ hent hent).2.2.1
  have hlim := hmc (fun k => PlateSmearing.mollifiedProducts b δ
      (fun i => (φ i : RealPlane → ℝ)) k.succPNat)
    (fun k _ l => ⟨(hR.2.2.1 _ ((hidx k.succPNat).1 l) (φ l) (φ l).2).1, (hAs l).2 _⟩)
    (fun l => ((hMol m S d η ⟨hη0, hη1⟩).2 δ hδ (b l) (hb l) (φ l) (φ l).2).2)
  have hV : ∀ y ∈ Set.univ.pi (fun i => tsupport (b i)),
      embedPlaneTuple (successiveDifferences y) ∈ shiftedForwardTubePow q η := fun y hy =>
    (hidx 1).2.2.1 y fun i => hy i (mem_univ i)
  have hcompact := isCompact_pi_tsupport hgap.2.1
  have hprodc : Continuous fun y : Fin (q + 1) → RealPlane => ∏ i, b i (y i) :=
    continuous_finsetProd _ fun i _ => (hgap.1 i).comp (continuous_apply i)
  have hbound : Integrable ((Set.univ.pi fun i => tsupport (b i)).indicator
      fun y => ‖∏ i, b i (y i)‖ * B) := by
    have hon : IntegrableOn (fun y : Fin (q + 1) → RealPlane => ‖∏ i, b i (y i)‖ * B)
        (Set.univ.pi fun i => tsupport (b i)) :=
      ((hprodc.norm.mul continuous_const).continuousOn).integrableOn_compact hcompact
    exact hon.integrable_indicator hcompact.measurableSet
  have hint : Tendsto (fun l => differenceIntegral b
      (d.mollifiedKernel η δ (fun i => (φ i : RealPlane → ℝ)) (ψ l).succPNat)) atTop
      (𝓝 (differenceIntegral b G)) := by
    refine tendsto_integral_of_dominated_convergence _ (fun l => ?_) hbound (fun l => ?_) ?_
    · exact (integrable_profileIntegrand hgap.1 hgap.2.1
        (((hcont _).comp (continuous_embed_successiveDifferences q).continuousOn hV))).aestronglyMeasurable
    · refine Eventually.of_forall fun y => ?_
      by_cases hy : y ∈ Set.univ.pi fun i => tsupport (b i)
      · simp only [profileIntegrand, indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hB _ _ (hV y hy)) (norm_nonneg _)
      · simp [profileIntegrand, indicator_of_notMem hy]
    · refine Eventually.of_forall fun y => ?_
      by_cases hy : y ∈ Set.univ.pi fun i => tsupport (b i)
      · simp only [profileIntegrand, indicator_of_mem hy]
        exact (hconv _ (hV y hy)).const_mul _
      · simp [profileIntegrand, indicator_of_notMem hy]
  have hlim' := (hlim.comp hψ.tendsto_atTop).congr (fun l => (hidx (ψ l).succPNat).2.2.2)
  exact tendsto_nhds_unique hlim' hint
theorem exists_convergent_subseq (hM : ComplexAnalysis.MontelSeveralVariables)
    (hP : PlateVectorsProduct.Holds)
    (hS : PlateSmearing.PlateSmearingStatement)
    (hMol : RadialMollifiers.ExistAndConvergeC1)
    (hMom : Moments.MomentBoundsTheorem)
    (hR : TranslationRules.TranslationAndMotionFacts)
    (hT : ShiftedTubeCoords.Holds) (hq : 1 ≤ q)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {δ : ℕ+ → RealPlane → ℝ}
    (hδ : d.IsRadialMollifier η δ) {ψ₀ : ℕ → ℕ} (hψ₀ : StrictMono ψ₀) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ G : (Fin q → ℂ × ℂ) → ℂ,
      HolomorphicOnTuples (shiftedForwardTubePow q η) G ∧ IsKernelAtLength S φ η G ∧
      (∀ v ∈ shiftedForwardTubePow q η, ‖G v‖ ≤ kernelBound d φ η) ∧
      ∀ C : Set (Fin q → ℂ × ℂ), C ⊆ shiftedForwardTubePow q η → IsCompact C →
        TendstoUniformlyOn (fun l => d.mollifiedKernel η δ (fun i => (φ i : RealPlane → ℝ))
          (ψ₀ (ψ l)).succPNat) G atTop C := by
  have hfacts := fun j => mollifiedKernel_holomorphic_bound d φ hP hη0 hη1 hδ j
  have hopen : IsOpen (shiftedForwardTubePow q η) := (hT q hq η hη0 hη1).1.2.1
  obtain ⟨ψ, hψ, G, hG, hu⟩ := montel_holomorphicOnTuples hM (by omega) hopen
    (fun j => d.mollifiedKernel η δ (fun i => (φ i : RealPlane → ℝ)) (ψ₀ j).succPNat)
    (fun j => (hfacts _).1) (fun j => (hfacts _).2)
  have hconv : ∀ v ∈ shiftedForwardTubePow q η,
      Tendsto (fun l => d.mollifiedKernel η δ (fun i => (φ i : RealPlane → ℝ))
        (ψ₀ (ψ l)).succPNat v) atTop (𝓝 (G v)) := fun v hv =>
    (hu {v} (singleton_subset_iff.2 hv) isCompact_singleton).tendsto_at (mem_singleton v)
  refine ⟨ψ, hψ, G, hG, ?_, fun v hv => ?_, hu⟩
  · exact isKernelAtLength_of_tendsto d φ hS hMol hMom hR hq hη0 hη1 hδ (hψ₀.comp hψ)
      (fun j => holomorphicOnTuples_continuousOn (hfacts j).1)
      (fun j => (hfacts j).2) hconv
  · exact le_of_tendsto (hconv v hv).norm (Eventually.of_forall fun l => (hfacts _).2 v hv)
theorem shiftedForwardTubePow_props (hT : ShiftedTubeCoords.Holds) (hq : 1 ≤ q)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    IsOpen (shiftedForwardTubePow q η) ∧ IsConnected (shiftedForwardTubePow q η) ∧
      ∀ v ∈ realTuplesTimeAbove q η,
        complexifyRealTuple v ∈ shiftedForwardTubePow q η := by
  obtain ⟨ha, -, hc, -⟩ := hT q hq η hη0 hη1
  have hU : ∀ v ∈ realTuplesTimeAbove q η,
      complexifyRealTuple v ∈ shiftedForwardTubePow q η := by
    intro v hv
    have hmem : embedPlaneTuple v ∈
        embedPlaneTuple '' {y : Fin q → RealPlane | ∀ i, y i 0 > η / 2} :=
      mem_image_of_mem _ fun i => by
        have := hv i
        linarith
    rw [← hc.1] at hmem
    exact hmem.1
  have hne : (shiftedForwardTubePow q η).Nonempty := by
    refine ⟨_, hU (fun _ => EuclideanSpace.single 0 (η + 1)) fun i => ?_⟩
    simp
  exact ⟨ha.2.1, ⟨hne, ha.2.2.1.isPreconnected⟩, hU⟩
theorem forwardTubePow_props (hT : ShiftedTubeCoords.Holds) (hq : 1 ≤ q) :
    IsOpen (forwardTubePow q) ∧ IsConnected (forwardTubePow q) ∧
      ∀ v ∈ realTuplesTimeAbove q 0, complexifyRealTuple v ∈ forwardTubePow q := by
  obtain ⟨ha, -, hc, -⟩ := hT q hq 1 one_pos le_rfl
  have hU : ∀ v ∈ realTuplesTimeAbove q 0, complexifyRealTuple v ∈ forwardTubePow q := by
    intro v hv
    have hmem : embedPlaneTuple v ∈ embedPlaneTuple '' {y : Fin q → RealPlane | ∀ i, y i 0 > 0} :=
      mem_image_of_mem _ hv
    rw [← hc.2.1] at hmem
    exact hmem.1
  have hne : (forwardTubePow q).Nonempty := by
    refine ⟨_, hU (fun _ => EuclideanSpace.single 0 1) fun i => ?_⟩
    simp
  exact ⟨ha.2.2.2.1, ⟨hne, ha.2.2.2.2.isPreconnected⟩, hU⟩
theorem exists_kernelAtLength (hM : ComplexAnalysis.MontelSeveralVariables)
    (hP : PlateVectorsProduct.Holds)
    (hS : PlateSmearing.PlateSmearingStatement)
    (hMol : RadialMollifiers.ExistAndConvergeC1)
    (hMom : Moments.MomentBoundsTheorem)
    (hR : TranslationRules.TranslationAndMotionFacts)
    (hT : ShiftedTubeCoords.Holds)
    (hD : HolomorphicDifferences.determinedByProductIntegrals) (hq : 1 ≤ q)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ K : (Fin q → ℂ × ℂ) → ℂ,
      HolomorphicOnTuples (shiftedForwardTubePow q η) K ∧ IsKernelAtLength S φ η K ∧
      (∀ v ∈ shiftedForwardTubePow q η, ‖K v‖ ≤ kernelBound d φ η) ∧
      ∀ δ : ℕ+ → RealPlane → ℝ, d.IsRadialMollifier η δ →
        ∀ C : Set (Fin q → ℂ × ℂ), IsCompact C → C ⊆ shiftedForwardTubePow q η →
          TendstoUniformlyOn (d.mollifiedKernel η δ fun i => (φ i : RealPlane → ℝ)) K atTop C := by
  obtain ⟨δ₀, hδ₀⟩ := (hMol m S d η ⟨hη0, hη1⟩).1
  obtain ⟨-, -, K, hK, hKd, hKb, -⟩ :=
    exists_convergent_subseq d φ hM hP hS hMol hMom hR hT hq hη0 hη1 hδ₀ strictMono_id
  obtain ⟨hVo, hVc, hVU⟩ := shiftedForwardTubePow_props (q := q) hT hq hη0 hη1
  refine ⟨K, hK, hKd, hKb, fun δ hδ C hC hCV => ?_⟩
  by_contra hnot
  rw [Metric.tendstoUniformlyOn_iff] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hfreq⟩ := hnot
  have hfreq' : ∃ᶠ k : ℕ in atTop, ∃ x ∈ C, ε ≤
      dist (K x) (d.mollifiedKernel η δ (fun i => (φ i : RealPlane → ℝ)) k.succPNat x) := by
    rw [Filter.frequently_atTop] at hfreq ⊢
    intro a
    obtain ⟨j, hj, hjP⟩ := hfreq a.succPNat
    refine ⟨j.natPred, ?_, ?_⟩
    · have h1 : a + 1 ≤ (j : ℕ) := by
        have := PNat.coe_le_coe _ _ |>.2 hj
        simpa using this
      have h2 : j.natPred + 1 = (j : ℕ) := PNat.natPred_add_one j
      omega
    · rw [PNat.succPNat_natPred]
      exact hjP
  obtain ⟨ψ₀, hψ₀, hP₀⟩ := Filter.extraction_of_frequently_atTop hfreq'
  obtain ⟨ψ, -, G, hG, hGd, -, hGu⟩ :=
    exists_convergent_subseq d φ hM hP hS hMol hMom hR hT hq hη0 hη1 hδ hψ₀
  have hKG := eq_of_isKernelAtLength hD hq φ hη0.le hVo hVc hVU hK hG hKd hGd
  have hev := (Metric.tendstoUniformlyOn_iff.1 (hGu C hCV hC)) ε hε
  obtain ⟨l, hl⟩ := hev.exists
  obtain ⟨x, hx, hxε⟩ := hP₀ (ψ l)
  have := hl x hx
  rw [← hKG x (hCV hx)] at this
  exact absurd this (not_lt.2 hxε)
end OneLength
section Ordered
variable {n : ℕ}
theorem image_inner_rotatedDirection_zero (A : Set RealPlane) :
    (fun y => inner ℝ (rotatedDirection rightAngleZero) y) '' A =
      (fun y : RealPlane => y 0) '' A := by
  rw [rotatedDirection_rightAngleZero]
  congr 1
  funext y
  rw [inner_eq_coord_sum]
  simp [RealPlane.unitX]
theorem supInner_rightAngleZero (A : Set RealPlane) :
    supInner (rotatedDirection rightAngleZero) A = maxTime A := by
  unfold supInner maxTime
  rw [image_inner_rotatedDirection_zero]
theorem infInner_rightAngleZero (A : Set RealPlane) :
    infInner (rotatedDirection rightAngleZero) A = minTime A := by
  unfold infInner minTime
  rw [image_inner_rotatedDirection_zero]
theorem funsTimeSeparated_of_timeSeparated {b : Fin n → RealPlane → ℂ} (hb : TimeSeparated 0 b) :
    FunsTimeSeparated b := by
  refine ⟨hb.2.1, hb.2.2.1, fun i => (hb.2.1 i).isCompact, fun i => ?_, fun i hi => ?_⟩
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (hb.2.2.1 i)
    exact ⟨x, subset_tsupport _ hx⟩
  · rw [supInner_rightAngleZero, infInner_rightAngleZero]
    have := hb.2.2.2 i hi
    linarith
theorem exists_timeSeparated_of_funsTimeSeparated {q : ℕ} {α : Fin (q + 1) → RealPlane → ℂ}
    (hα : ∀ i, α i ∈ complexProfiles) (h : FunsTimeSeparated α) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ TimeSeparated η α := by
  obtain ⟨hs, hne, -, -, hord⟩ := h
  have hgap : ∀ i : Fin q, 0 < minTime (tsupport (α ⟨i + 1, by omega⟩)) -
      maxTime (tsupport (α ⟨i, by omega⟩)) := by
    intro i
    have := hord i (by omega)
    rw [supInner_rightAngleZero, infInner_rightAngleZero] at this
    linarith
  have h1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i : Fin q, η < minTime (tsupport (α ⟨i + 1, by omega⟩)) -
      maxTime (tsupport (α ⟨i, by omega⟩)) :=
    Filter.eventually_all.2 fun i => mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (hgap i))
  have h2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
  obtain ⟨η, ⟨h3, h4⟩, h5⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  refine ⟨η, h5, h4.le, fun i => (hα i).1.continuous, hs, hne, fun i hi => ?_⟩
  exact h3 ⟨i, by omega⟩
end Ordered
section AllLengths
variable {m : SharpScale} {S : ConnFamily} {q : ℕ}
theorem isKernelAtLength_zero {φ : Fin (q + 1) → realLabels} {K : (Fin q → ℂ × ℂ) → ℂ}
    (hK : IsPlaneKernel S φ K) : IsKernelAtLength S φ 0 K :=
  fun b hb hg => hK.integral_eq b hb (funsTimeSeparated_of_timeSeparated hg)
variable (d : PlaneDataWithAperture m S) (φ : Fin (q + 1) → realLabels)
theorem exists_planeKernel_limit (hM : ComplexAnalysis.MontelSeveralVariables)
    (hP : PlateVectorsProduct.Holds)
    (hS : PlateSmearing.PlateSmearingStatement)
    (hMol : RadialMollifiers.ExistAndConvergeC1)
    (hMom : Moments.MomentBoundsTheorem)
    (hR : TranslationRules.TranslationAndMotionFacts)
    (hT : ShiftedTubeCoords.Holds)
    (hD : HolomorphicDifferences.determinedByProductIntegrals) (hq : 1 ≤ q) :
    ∃ K₀ : (Fin q → ℂ × ℂ) → ℂ, IsPlaneKernel S φ K₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        (∀ v ∈ shiftedForwardTubePow q η, ‖K₀ v‖ ≤ kernelBound d φ η) ∧
        ∀ δ : ℕ+ → RealPlane → ℝ, d.IsRadialMollifier η δ →
          ∀ C : Set (Fin q → ℂ × ℂ), IsCompact C → C ⊆ shiftedForwardTubePow q η →
            TendstoUniformlyOn (d.mollifiedKernel η δ fun i => (φ i : RealPlane → ℝ)) K₀
              atTop C := by
  have hex := fun (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1) =>
    exists_kernelAtLength d φ hM hP hS hMol hMom hR hT hD hq h0 h1
  choose! Kf hKh hKd hKb hKc using hex
  have hnest : ∀ η' η : ℝ, 0 < η' → η' ≤ η → η ≤ 1 → ∀ v ∈ shiftedForwardTubePow q η,
      Kf η' v = Kf η v := by
    intro η' η h0 hle h1 v hv
    have h0' : 0 < η := h0.trans_le hle
    obtain ⟨hVo, hVc, hVU⟩ := shiftedForwardTubePow_props (q := q) hT hq h0' h1
    have hsub : shiftedForwardTubePow q η ⊆ shiftedForwardTubePow q η' :=
      ((hT q hq η h0' h1).2.1.1 η' h0 hle).1
    have hd' : IsKernelAtLength S φ η (Kf η') := fun b hb hg =>
      hKd η' h0 (hle.trans h1) b hb (timeSeparated_mono hle hg)
    exact eq_of_isKernelAtLength hD hq φ h0'.le hVo hVc hVU
      (holomorphicOnTuples_mono (hKh η' h0 (hle.trans h1)) hVo hsub) (hKh η h0' h1) hd'
      (hKd η h0' h1) v hv
  have hmargin : ∀ v ∈ forwardTubePow q,
      tubeMargin v ∈ Set.Ioc (0 : ℝ) 1 ∧ v ∈ shiftedForwardTubePow q (tubeMargin v) :=
    (hT q hq 1 one_pos le_rfl).2.1.2
  have hsubT : ∀ η : ℝ, 0 < η → η ≤ 1 → shiftedForwardTubePow q η ⊆ forwardTubePow q :=
    fun η h0 h1 => ((hT q hq η h0 h1).2.1.1 η h0 le_rfl).2
  have hagree : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ v ∈ shiftedForwardTubePow q η,
      Kf (tubeMargin v) v = Kf η v := by
    intro η h0 h1 v hv
    obtain ⟨⟨hm0, hm1⟩, hmv⟩ := hmargin v (hsubT η h0 h1 hv)
    rcases le_total (tubeMargin v) η with h | h
    · exact hnest _ _ hm0 h h1 v hv
    · exact (hnest _ _ h0 h hm1 v hmv).symm
  obtain ⟨hTo, -, -⟩ := forwardTubePow_props (q := q) hT hq
  refine ⟨fun v => Kf (tubeMargin v) v, ⟨?_, ?_⟩, fun η h0 h1 => ⟨fun v hv => ?_, ?_⟩⟩
  · refine holomorphicOnTuples_of_locally hTo fun a ha => ?_
    obtain ⟨⟨hm0, hm1⟩, hmv⟩ := hmargin a ha
    exact ⟨shiftedForwardTubePow q (tubeMargin a), Kf (tubeMargin a),
      (shiftedForwardTubePow_props hT hq hm0 hm1).1, hmv, hKh _ hm0 hm1,
      fun v hv => hagree _ hm0 hm1 v hv⟩
  · intro α hα hord
    obtain ⟨η, h0, h1, hg⟩ := exists_timeSeparated_of_funsTimeSeparated hα hord
    rw [hKd η h0 h1 α hα hg]
    refine profileIntegral_congr fun y hy => (hagree η h0 h1 _ ?_).symm
    exact (shiftedForwardTubePow_props hT hq h0 h1).2.2 _
      (((hD (q + 1) (by omega) η h0.le).1 α hg y fun i => hy i (mem_univ i)))
  · show ‖Kf (tubeMargin v) v‖ ≤ _
    rw [hagree η h0 h1 v hv]
    exact hKb η h0 h1 v hv
  · intro δ hδ C hC hCV
    exact (hKc η h0 h1 δ hδ C hC hCV).congr_right fun v hv => (hagree η h0 h1 v (hCV hv)).symm
include d in
theorem productFunction_supp_pairwise_disjoint (hS : PlateSmearing.PlateSmearingStatement)
    (hMol : RadialMollifiers.ExistAndConvergeC1) (hq : 1 ≤ q) {η : ℝ} (h0 : 0 < η)
    (h1 : η ≤ 1) {b : Fin (q + 1) → RealPlane → ℂ} (hb : ∀ i, b i ∈ complexProfiles)
    (hg : TimeSeparated η b) :
    Pairwise fun k l => Disjoint (supp (productFunction (b k) (φ k)))
      (supp (productFunction (b l) (φ l))) := by
  obtain ⟨δ, hδ⟩ := (hMol m S d η ⟨h0, h1⟩).1
  obtain ⟨⟨A, -, hAd, hAs⟩, -⟩ := hS m S d q hq (fun i => (φ i : RealPlane → ℝ))
    (fun i => (φ i).2) η h0 h1 δ hδ b hb hg
  intro k l hkl
  refine Set.disjoint_left.2 fun x hxk hxl => ?_
  have hle : Euclidean.euclidSetDist (A k) (A l) ≤ 0 := by
    unfold Euclidean.euclidSetDist
    refine (iInf₂_le x ((hAs k).1 hxk)).trans ((iInf₂_le x ((hAs l).1 hxl)).trans ?_)
    simp [Euclidean.euclidNorm]
  have h2 := (hAd hkl).trans hle
  have h3 : (0 : ENNReal) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (by positivity)
  exact absurd h2 (not_le.2 h3)
include d in
theorem centeredFn_im_eq_zero (hS : PlateSmearing.PlateSmearingStatement)
    (hMol : RadialMollifiers.ExistAndConvergeC1)
    (hR : TranslationRules.TranslationAndMotionFacts)
    (hE : RealTuples.realFunctionTuples) (hTS : TupleRules.TupleSpanActionRules)
    (hq : 1 ≤ q) {b : Fin (q + 1) → RealPlane → ℝ} (hb : SmoothTimeSeparated 0 b)
    (hprof : ∀ i, complexifyProfiles b i ∈ complexProfiles) :
    (centeredFnAtProducts S (complexifyProfiles b) φ).im = 0 := by
  obtain ⟨η, h0, h1, hg⟩ :=
    exists_timeSeparated_of_funsTimeSeparated hprof (funsTimeSeparated_of_timeSeparated hb.2)
  have hdis := productFunction_supp_pairwise_disjoint d φ hS hMol hq h0 h1 hprof hg
  have hreal : ∀ l, IsRealValued (productFunction (complexifyProfiles b l) (φ l)) := by
    intro l x
    simp [productFunction, complexifyProfiles]
  unfold centeredFnAtProducts complexTuple
  rw [if_pos hreal]
  have hparts := fun l => hTS.1 m 1 1 _ (hR.2.2.1 _ (hprof l) (φ l) (φ l).2).1
  have hmem : ∀ l, (fun x => (productFunction (complexifyProfiles b l) (φ l) x).re) ∈
      C1c ℝ := fun l => (hparts l).1
  have hsub : ∀ l, supp (fun x => (productFunction (complexifyProfiles b l) (φ l) x).re) ⊆
      supp (productFunction (complexifyProfiles b l) (φ l)) := fun l =>
    subset_union_left.trans (hparts l).2.2.1
  have hsep := ((hE m S d).2.2 (q + 1) (by omega)
    (fun l x => (productFunction (complexifyProfiles b l) (φ l) x).re) hmem
    fun k l hkl => (hdis hkl).mono (hsub k) (hsub l)).1
  rw [((hE m S d).2.1 _ (Set.mem_iUnion.2 ⟨q + 1, hsep⟩)).1]
  exact Complex.ofReal_im _
include d in
theorem im_eq_zero_at_real (hS : PlateSmearing.PlateSmearingStatement)
    (hMol : RadialMollifiers.ExistAndConvergeC1)
    (hR : TranslationRules.TranslationAndMotionFacts)
    (hE : RealTuples.realFunctionTuples) (hTS : TupleRules.TupleSpanActionRules)
    (hT : ShiftedTubeCoords.Holds)
    (hD : HolomorphicDifferences.determinedByProductIntegrals) (hq : 1 ≤ q)
    {K : (Fin q → ℂ × ℂ) → ℂ} (hK : IsPlaneKernel S φ K) :
    ∀ v ∈ realTuplesTimeAbove q 0, (K (complexifyRealTuple v)).im = 0 := by
  obtain ⟨hTo, hTc, hTU⟩ := forwardTubePow_props (q := q) hT hq
  refine ((hD (q + 1) (by omega) 0 le_rfl).2 (forwardTubePow q) K hTo hTc hTU hK.holomorphic).2 ?_
  intro b hb
  have hprof : ∀ i, complexifyProfiles b i ∈ complexProfiles := fun i =>
    ⟨Complex.ofRealCLM.contDiff.comp ((hb.1 i).of_le (by exact_mod_cast le_top)), hb.2.2.1 i⟩
  have e := isKernelAtLength_zero hK _ hprof hb.2
  have hr := centeredFn_im_eq_zero d φ hS hMol hR hE hTS hq hb hprof
  rw [e] at hr
  exact hr
end AllLengths
section Frames
theorem rotate_rotate_neg (t : ℝ) (y : RealPlane) :
    RealPlane.rotate t (RealPlane.rotate (-t) y) = y := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.rotate_rotate_neg <;> assumption
theorem rotate_neg_rotate (t : ℝ) (y : RealPlane) :
    RealPlane.rotate (-t) (RealPlane.rotate t y) = y := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.rotate_neg_rotate <;> assumption
def rotateIsometry (t : ℝ) : RealPlane ≃ₗᵢ[ℝ] RealPlane where
  toFun := RealPlane.rotate t
  invFun := RealPlane.rotate (-t)
  left_inv := rotate_neg_rotate t
  right_inv := rotate_rotate_neg t
  map_add' x y := by
    ext i
    fin_cases i <;> simp [RealPlane.rotate] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [RealPlane.rotate] <;> ring
  norm_map' y := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    have h := Real.sin_sq_add_cos_sq t
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    simp [RealPlane.rotate]
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * h
theorem rotateIsometry_apply (t : ℝ) (y : RealPlane) :
    rotateIsometry t y = RealPlane.rotate t y := rfl
theorem complexBoost_zero (v : ℂ × ℂ) : complexBoost 0 v = v := by
  simpa [complexBoost] using ofLightConeCoords_lightConePlus_lightConeMinus v
theorem complexBoost_add (z : ℂ) (x y : ℂ × ℂ) :
    complexBoost z (x + y) = complexBoost z x + complexBoost z y := by
  simp only [complexBoost, ofLightConeCoords, lightConePlus, lightConeMinus, Prod.fst_add,
    Prod.snd_add, Prod.mk_add_mk]
  congr 1 <;> ring
theorem complexBoost_smul (z c : ℂ) (x : ℂ × ℂ) :
    complexBoost z (c • x) = c • complexBoost z x := by
  simp only [complexBoost, ofLightConeCoords, lightConePlus, lightConeMinus, Prod.smul_fst,
    Prod.smul_snd, Prod.smul_mk, smul_eq_mul]
  congr 1 <;> ring
theorem pairTupleEquiv_add {p : ℕ} (x y : Fin p → ℂ × ℂ) :
    pairTupleEquiv p (x + y) = pairTupleEquiv p x + pairTupleEquiv p y := by apply _root_.YangMills.Construction.EuclideanFunctionals.UnionKernel.pairTupleEquiv_add <;> assumption
theorem pairTupleEquiv_smul {p : ℕ} (c : ℂ) (x : Fin p → ℂ × ℂ) :
    pairTupleEquiv p (c • x) = c • pairTupleEquiv p x := by apply _root_.YangMills.Construction.EuclideanFunctionals.UnionKernel.pairTupleEquiv_smul <;> assumption
def pairTupleLinearEquiv (p : ℕ) : (Fin p → ℂ × ℂ) ≃ₗ[ℂ] Coordinates.ComplexCoordinates (p * 2) :=
  { pairTupleEquiv p with
    map_add' := pairTupleEquiv_add
    map_smul' := pairTupleEquiv_smul }
def unrotateLinear (υ : rightAngleMultiples) (q : ℕ) :
    (Fin q → ℂ × ℂ) →ₗ[ℂ] (Fin q → ℂ × ℂ) where
  toFun := unrotate υ
  map_add' _ _ := funext fun _ => complexBoost_add _ _ _
  map_smul' _ _ := funext fun _ => complexBoost_smul _ _ _
variable {q : ℕ}
theorem mem_rotatedTubePow_iff (hF : TubeFrameStripSectorPencilFacts)
    (υ : rightAngleMultiples) (v : Fin q → ℂ × ℂ) :
    v ∈ rotatedTubePow υ q ↔ unrotate υ v ∈ forwardTubePow q := by
  obtain ⟨-, ⟨-, -, -, -, hG, -⟩, -⟩ := hF
  constructor
  · intro hv i _
    obtain ⟨u, hu, huv⟩ := hv i (mem_univ i)
    show complexBoost _ (v i) ∈ forwardTube
    rw [← huv, hG]
    simpa [complexBoost_zero] using hu
  · intro hv i _
    refine ⟨_, hv i (mem_univ i), ?_⟩
    show complexBoost _ (complexBoost _ (v i)) = v i
    rw [hG]
    simp [complexBoost_zero]
theorem holomorphicOnTuples_unrotate (hF : TubeFrameStripSectorPencilFacts)
    (hPS : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hT : ShiftedTubeCoords.Holds) (hq : 1 ≤ q)
    {K : (Fin q → ℂ × ℂ) → ℂ} (hK : HolomorphicOnTuples (forwardTubePow q) K)
    (υ : rightAngleMultiples) :
    HolomorphicOnTuples (rotatedTubePow υ q) fun v => K (unrotate υ v) := by
  obtain ⟨hTo, -, -⟩ := forwardTubePow_props (q := q) hT hq
  let L : Coordinates.ComplexCoordinates (q * 2) →ₗ[ℂ] Coordinates.ComplexCoordinates (q * 2) :=
    (pairTupleLinearEquiv q).toLinearMap ∘ₗ unrotateLinear υ q ∘ₗ
      (pairTupleLinearEquiv q).symm.toLinearMap
  let Lc : Coordinates.ComplexCoordinates (q * 2) →L[ℂ] Coordinates.ComplexCoordinates (q * 2) :=
    LinearMap.toContinuousLinearMap L
  have hLc : ∀ z, Lc z = pairTupleEquiv q (unrotate υ ((pairTupleEquiv q).symm z)) :=
    fun z => rfl
  have hO' : IsOpen (rotatedTubePow υ q) := by
    have h : rotatedTubePow υ q = unrotate υ ⁻¹' forwardTubePow q := by
      ext v
      exact mem_rotatedTubePow_iff hF υ v
    rw [h]
    exact hTo.preimage (unrotateLinear υ q).continuous_of_finiteDimensional
  have hg : Coordinates.ComplexCoordinates.IsHolomorphicIn
      (pairTupleEquiv q '' rotatedTubePow υ q) Lc :=
    ⟨isOpen_pairTupleEquiv_image hO', Lc.continuous.continuousOn, fun a _ j =>
      Eventually.of_forall fun ζ => Lc.differentiableAt.comp ζ
        ((differentiableAt_const a).add (differentiableAt_id.smul_const _))⟩
  have hmaps : MapsTo Lc (pairTupleEquiv q '' rotatedTubePow υ q)
      (pairTupleEquiv q '' forwardTubePow q) := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨unrotate υ v, (mem_rotatedTubePow_iff hF υ v).1 hv, ?_⟩
    rw [hLc, Equiv.symm_apply_apply]
  have hcomp := ((hPS.1 (q * 2) (pairTupleEquiv q '' forwardTubePow q)
    (isOpen_pairTupleEquiv_image hTo)).1 1 _ hK).2.2.2.1 (q * 2) _ Lc hg hmaps
  show Coordinates.ComplexCoordinates.IsHolomorphicIn _ (scalarEquiv ∘
    (fun v => K (unrotate υ v)) ∘ (pairTupleEquiv q).symm)
  convert hcomp using 1
  funext z
  simp [hLc]
end Frames
section FrameIdentity
variable {m : SharpScale} {S : ConnFamily} {q : ℕ}
variable (d : PlaneDataWithAperture m S) (φ : Fin (q + 1) → realLabels)
include d in
theorem integral_identity_rotated (hF : TubeFrameStripSectorPencilFacts)
    (hS : PlateSmearing.PlateSmearingStatement)
    (hMol : RadialMollifiers.ExistAndConvergeC1)
    (hR : TranslationRules.TranslationAndMotionFacts)
    (hI : MomentSymmetry.ReductionHolds)
    (hTS : TupleRules.TupleSpanActionRules)
    (hMot : ProductMotions.MotionFacts) (hq : 1 ≤ q)
    {K : (Fin q → ℂ × ℂ) → ℂ} (hK : IsPlaneKernel S φ K) (υ : rightAngleMultiples)
    {α : Fin (q + 1) → RealPlane → ℂ} (hα : ∀ i, α i ∈ complexProfiles)
    (hord : FunsDirectionSeparated υ α) :
    centeredFnAtProducts S α φ =
      differenceIntegral α fun v => K (unrotate υ v) := by
  obtain ⟨-, ⟨-, -, -, hReal, -, -⟩, -⟩ := hF
  obtain ⟨k, hk⟩ := υ.2
  let β : Fin (q + 1) → RealPlane → ℂ := fun i => α i ∘ RealPlane.rotate υ
  have hβ : ∀ i, β i ∈ complexProfiles := fun i => by
    have h := (hR.2.1 (α i) (hα i) (φ i) (φ i).2 0 (-(υ : ℝ))).2.2.2.2.1
    rwa [neg_neg] at h
  have hmem : ∀ i y, y ∈ tsupport (β i) ↔ RealPlane.rotate υ y ∈ tsupport (α i) := by
    intro i y
    have h := tsupport_comp_eq_preimage (α i) (rotateIsometry (υ : ℝ)).toHomeomorph
    have h' : tsupport (β i) = RealPlane.rotate υ ⁻¹' tsupport (α i) := h
    rw [h']
    rfl
  have himg : ∀ i, (fun y => inner ℝ (rotatedDirection rightAngleZero) y) '' tsupport (β i) =
      (fun y => inner ℝ (rotatedDirection υ) y) '' tsupport (α i) := by
    intro i
    ext c
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨RealPlane.rotate υ y, (hmem i y).1 hy, ?_⟩
      show inner ℝ (rotatedDirection υ) (RealPlane.rotate υ y) =
        inner ℝ (rotatedDirection rightAngleZero) y
      rw [rotatedDirection_eq_rotate_unitX υ, rotatedDirection_rightAngleZero]
      exact (rotateIsometry (υ : ℝ)).inner_map_map _ _
    · rintro ⟨z, hz, rfl⟩
      refine ⟨RealPlane.rotate (-(υ : ℝ)) z, (hmem i _).2 ?_, ?_⟩
      · rwa [rotate_rotate_neg]
      · show inner ℝ (rotatedDirection rightAngleZero) (RealPlane.rotate (-(υ : ℝ)) z) =
          inner ℝ (rotatedDirection υ) z
        rw [rotatedDirection_eq_rotate_unitX υ, rotatedDirection_rightAngleZero]
        have h := (rotateIsometry (υ : ℝ)).inner_map_map RealPlane.unitX
          (RealPlane.rotate (-(υ : ℝ)) z)
        rw [rotateIsometry_apply, rotateIsometry_apply, rotate_rotate_neg] at h
        exact h.symm
  have hβord : FunsTimeSeparated β := by
    refine ⟨fun i => (hβ i).2, fun i h => ?_, fun i => (hβ i).2.isCompact, fun i => ?_,
      fun i hi => ?_⟩
    · apply hord.2.1 i
      funext y
      have h' := congrFun h (RealPlane.rotate (-(υ : ℝ)) y)
      simpa [β, rotate_rotate_neg] using h'
    · obtain ⟨z, hz⟩ := hord.2.2.2.1 i
      exact ⟨RealPlane.rotate (-(υ : ℝ)) z, (hmem i _).2 (by
        rwa [rotate_rotate_neg])⟩
    · unfold supInner infInner
      rw [himg, himg]
      exact hord.2.2.2.2 i hi
  obtain ⟨η, h0, h1, hg⟩ := exists_timeSeparated_of_funsTimeSeparated hβ hβord
  have hentries : ComplexComponents fun i => productFunction (β i) (φ i) :=
    ⟨by omega, fun l => (hR.2.2.1 _ (hβ l) (φ l) (φ l).2).1,
      productFunction_supp_pairwise_disjoint d φ hS hMol hq h0 h1 hβ hg⟩
  have hw : rotateMotion (υ : ℝ) ∈ hyperoctahedral := by
    rw [hk]
    exact hMot.2.1 k
  have hon := (hTS.2.2.2.2.2.2.2.1 Set.univ isOpen_univ (rotateMotion (υ : ℝ)) (q + 1) _
    hentries fun _ => subset_univ _).2.2.2.2.2.2.1
  have hinv := ((hI m S d.base.sigma).2.1
    (complexTuple fun i => productFunction (β i) (φ i))).2 _ hw
  have hfun : ∀ l, (rotateMotion (υ : ℝ)).actFn (productFunction (β l) (φ l)) =
      productFunction (α l) (φ l) := by
    intro l
    rw [(hR.2.1 (β l) (hβ l) (φ l) (φ l).2 0 (υ : ℝ)).2.1]
    congr 1
    funext y
    simp [β, rotate_rotate_neg]
  have hσ : centeredFnAtProducts S α φ = centeredFnAtProducts S β φ := by
    unfold centeredFnAtProducts
    rw [← hinv, hon]
    exact congrArg _ (congrArg _ (funext fun l => (hfun l).symm))
  rw [hσ, hK.integral_eq β hβ hβord]
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : Fin (q + 1) =>
        (rotateIsometry (-(υ : ℝ))).toHomeomorph.toMeasurableEquiv)
      (volume : Measure (Fin (q + 1) → RealPlane)) volume := by
    rw [volume_pi]
    exact measurePreserving_pi (fun _ => volume) (fun _ => volume)
      fun _ => (rotateIsometry (-(υ : ℝ))).measurePreserving
  unfold differenceIntegral profileIntegral
  rw [← hmp.integral_comp']
  congr 1
  funext y
  have hT : ∀ i, (MeasurableEquiv.piCongrRight (fun _ : Fin (q + 1) =>
      (rotateIsometry (-(υ : ℝ))).toHomeomorph.toMeasurableEquiv) y) i =
      RealPlane.rotate (-(υ : ℝ)) (y i) := fun i => rfl
  have hiff : (MeasurableEquiv.piCongrRight (fun _ : Fin (q + 1) =>
      (rotateIsometry (-(υ : ℝ))).toHomeomorph.toMeasurableEquiv) y) ∈
        (Set.univ.pi fun i => tsupport (β i)) ↔ y ∈ Set.univ.pi fun i => tsupport (α i) := by
    simp only [Set.mem_univ_pi, hmem, hT, rotate_rotate_neg]
  have hdiff : embedPlaneTuple (successiveDifferences
      (MeasurableEquiv.piCongrRight (fun _ : Fin (q + 1) =>
        (rotateIsometry (-(υ : ℝ))).toHomeomorph.toMeasurableEquiv) y)) =
      unrotate υ (embedPlaneTuple (successiveDifferences y)) := by
    funext i
    show embedPlane (RealPlane.rotate (-(υ : ℝ)) _ - RealPlane.rotate (-(υ : ℝ)) _) =
      complexBoost (((-(υ : ℝ)) : ℝ) : ℂ) (embedPlane (_ - _))
    rw [hReal, ← rotateIsometry_apply, ← rotateIsometry_apply, ← rotateIsometry_apply, map_sub]
  by_cases hy : y ∈ Set.univ.pi fun i => tsupport (α i)
  · have hy' := hiff.2 hy
    simp only [profileIntegrand, indicator_of_mem hy, indicator_of_mem hy', hdiff]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [β, hT, rotate_rotate_neg]
  · have hy' := mt hiff.1 hy
    simp only [profileIntegrand, indicator_of_notMem hy, indicator_of_notMem hy']
end FrameIdentity
theorem holds_of_cited (hM : ComplexAnalysis.MontelSeveralVariables)
    (hP : PlateVectorsProduct.Holds)
    (hS : PlateSmearing.PlateSmearingStatement)
    (hMol : RadialMollifiers.ExistAndConvergeC1)
    (hMom : Moments.MomentBoundsTheorem)
    (hR : TranslationRules.TranslationAndMotionFacts)
    (hT : ShiftedTubeCoords.Holds)
    (hD : HolomorphicDifferences.determinedByProductIntegrals)
    (hE : RealTuples.realFunctionTuples)
    (hTS : TupleRules.TupleSpanActionRules)
    (hF : TubeFrameStripSectorPencilFacts)
    (hPS : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hI : MomentSymmetry.ReductionHolds)
    (hMot : ProductMotions.MotionFacts) : Holds := by
  intro m S d q hq φ
  obtain ⟨K₀, hK₀, hprops⟩ := exists_planeKernel_limit d φ hM hP hS hMol hMom hR hT hD hq
  have hspec : IsPlaneKernel S φ (planeKernel S φ) :=
    Classical.epsilon_spec (p := IsPlaneKernel S φ) ⟨K₀, hK₀⟩
  obtain ⟨hTo, hTc, hTU⟩ := forwardTubePow_props (q := q) hT hq
  have huniq : ∀ K : (Fin q → ℂ × ℂ) → ℂ, IsPlaneKernel S φ K →
      ∀ v ∈ forwardTubePow q, K v = planeKernel S φ v := fun K hK =>
    eq_of_isKernelAtLength hD hq φ le_rfl hTo hTc hTU hK.holomorphic hspec.holomorphic
      (isKernelAtLength_zero hK) (isKernelAtLength_zero hspec)
  have hsubT : ∀ η : ℝ, 0 < η → η ≤ 1 → shiftedForwardTubePow q η ⊆ forwardTubePow q :=
    fun η h0 h1 => ((hT q hq η h0 h1).2.1.1 η h0 le_rfl).2
  refine ⟨hspec, huniq, fun v hv => ?_, ⟨?_, fun v hv => ?_⟩, fun η h0 h1 δ hδ C hC hCV => ?_,
    fun υ => ⟨fun v hv => (mem_rotatedTubePow_iff hF υ v).1 hv,
      holomorphicOnTuples_unrotate hF hPS hT hq hspec.holomorphic υ, fun α hα hord =>
      integral_identity_rotated d φ hF hS hMol hR hI hTS hMot hq hspec υ hα hord⟩⟩
  · obtain ⟨⟨hm0, hm1⟩, hmv⟩ := (hT q hq 1 one_pos le_rfl).2.1.2 v hv
    rw [← huniq K₀ hK₀ v hv]
    exact (hprops _ hm0 hm1).1 v hmv
  · exact (hT q hq 1 one_pos le_rfl).2.2.1.2.1
  · rw [(hT q hq 1 one_pos le_rfl).2.2.1.2.1] at hv
    obtain ⟨y, hy, rfl⟩ := hv
    exact im_eq_zero_at_real d φ hS hMol hR hE hTS hT hD hq hspec y hy
  · exact ((hprops η h0 h1).2 δ hδ C hC hCV).congr_right
      fun v hv => huniq K₀ hK₀ v (hsubT η h0 h1 (hCV hv))
end EuclideanFunctionals.PlaneKernelProps
end YangMills.Construction
end
