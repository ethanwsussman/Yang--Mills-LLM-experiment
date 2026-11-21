import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStatesProof
import YangMills.Construction.Continuum.FlatFunctionsTensorsOfSubTuplesAndSmoothTuples
import YangMills.Construction.Continuum.IsometriesOfFourSpaceAndOfATorusReflectionsAndInducedMaps
import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayerProof
import YangMills.Construction.InfiniteLattice.DataOfADiagonalPictureProof
import YangMills.Construction.LinearAlgebra.InnerProductMinorsReflectionDeterminantProof
import YangMills.Construction.PassageToTheLimit.MovingAMirrorIsTranslatingTheImageProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Continuum.GroupOfHypercubicMotionsAndTheIsometriesItInducesOnTheTori
import YangMills.Construction.Continuum.IsometriesAndModuliOnFourSpace
import YangMills.Construction.Continuum.NeighbourhoodsAdmissibleFamiliesAndMembersOfTheClasses
import YangMills.Construction.GrowingTori.TranslationsIsometriesAndMirrorsOfFourSpaceProof
import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpacesProof
import YangMills.Construction.TwoPoints.TranslatePairingIsAnalyticNearAPointProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal Topology
open Matrix
noncomputable section
namespace YangMills.Construction.TorusTransport.MotionFacts
open TestFunctions TorusMetric
section Maps
variable {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
theorem contDiff_orthoAffine (S : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ)
    {n : WithTop ℕ∞} : ContDiff ℝ n (orthoAffine S v) := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.contDiff_orthoAffine <;> assumption
theorem contDiff_of_motion (hs : IsEuclideanMotion s) {n : WithTop ℕ∞} : ContDiff ℝ n s := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.contDiff_of_isEuclideanMotion <;> assumption
theorem continuous_of_motion (hs : IsEuclideanMotion s) : Continuous s := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.continuous_of_isEuclideanMotion <;> assumption
def motionHomeomorph (hs : IsEuclideanMotion s) : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toEquiv := hs.toPerm
  continuous_toFun := continuous_of_motion hs
  continuous_invFun := continuous_of_motion hs.symm
theorem motion_apply_symm (hs : IsEuclideanMotion s) (y : Fin 4 → ℝ) :
    s (hs.toPerm.symm y) = y :=
  hs.toPerm.apply_symm_apply y
theorem comp_symm_comp {β : Type*} (hs : IsEuclideanMotion s) (g : (Fin 4 → ℝ) → β) :
    (g ∘ hs.toPerm.symm) ∘ s = g := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.comp_symm_comp_motion <;> assumption
theorem euclidNormVec_map_sub (hs : IsEuclideanMotion s) (x y : Fin 4 → ℝ) :
    euclidNormVec (s x - s y) = euclidNormVec (x - y) := by apply _root_.YangMills.Construction.TorusTransport.IsEuclideanMotion.isDistancePreserving <;> assumption
theorem tsupport_comp_motion {E : Type*} [Zero E] (hs : IsEuclideanMotion s)
    (h : (Fin 4 → ℝ) → E) : tsupport (h ∘ s) = s ⁻¹' tsupport h :=
  tsupport_comp_eq_preimage h (motionHomeomorph hs)
theorem isCompact_preimage_motion (hs : IsEuclideanMotion s) {K : Set (Fin 4 → ℝ)}
    (hK : IsCompact K) : IsCompact (s ⁻¹' K) :=
  (motionHomeomorph hs).isCompact_preimage.mpr hK
theorem preimage_symm_preimage (hs : IsEuclideanMotion s) (A : Set (Fin 4 → ℝ)) :
    hs.toPerm.symm ⁻¹' (s ⁻¹' A) = A := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.preimage_symm_preimage <;> assumption
theorem ennSupNorm_comp {E : Type*} [Norm E] (hs : IsEuclideanMotion s)
    (h : (Fin 4 → ℝ) → E) : ennSupNorm (h ∘ s) = ennSupNorm h :=
  hs.bijective.surjective.iSup_comp fun u => ENNReal.ofReal ‖h u‖
theorem iSup₂_comp_motion {α : Type*} [CompleteLattice α] (hs : IsEuclideanMotion s)
    (g : (Fin 4 → ℝ) → (Fin 4 → ℝ) → α) :
    ⨆ (u : Fin 4 → ℝ) (v : Fin 4 → ℝ), g (s u) (s v) = ⨆ (u : Fin 4 → ℝ) (v : Fin 4 → ℝ), g u v := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.iSup₂_comp_motion <;> assumption
theorem ennLipConst_comp {E : Type*} [NormedAddCommGroup E] (hs : IsEuclideanMotion s)
    (h : (Fin 4 → ℝ) → E) :
    ennLipConst euclidDistR4 (h ∘ s) = ennLipConst euclidDistR4 h := by
  unfold ennLipConst
  rw [← iSup₂_comp_motion hs fun u v => ⨆ _ : u ≠ v, ENNReal.ofReal (‖h u - h v‖ / euclidDistR4 u v)]
  refine iSup_congr fun u => iSup_congr fun v => ?_
  have e : euclidDistR4 (s u) (s v) = euclidDistR4 u v := euclidNormVec_map_sub hs u v
  simp only [Function.comp, hs.bijective.injective.ne_iff, e]
theorem setDist_preimage (D : TransportData) (hs : IsEuclideanMotion s) (A B : Set (Fin 4 → ℝ)) :
    Domain.euclidean.setDist D (s ⁻¹' A) (s ⁻¹' B) = Domain.euclidean.setDist D A B := by
  rw [Domain.setDist_euclidean, Domain.setDist_euclidean]
  apply le_antisymm
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
    obtain ⟨a', rfl⟩ := hs.bijective.surjective a
    obtain ⟨b', rfl⟩ := hs.bijective.surjective b
    refine iInf₂_le_of_le a' ha (iInf₂_le_of_le b' hb ?_)
    rw [euclidNormVec_map_sub hs]
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
    refine iInf₂_le_of_le (s a) ha (iInf₂_le_of_le (s b) hb ?_)
    rw [euclidNormVec_map_sub hs]
theorem compInvariance (D : TransportData) (hs : IsEuclideanMotion s)
    (h : ComplexFun (Fin 4 → ℝ)) : CompInvariance D s h := by
  have hlip : Domain.euclidean.lipConst D (h ∘ s) = Domain.euclidean.lipConst D h :=
    ennLipConst_comp hs h
  refine ⟨tsupport_comp_motion hs h, ennSupNorm_comp hs h, hlip, ?_, ?_, ?_⟩
  · unfold Domain.ennSharpNorm
    rw [hlip]
    exact congrArg (fun t => max t _) (ennSupNorm_comp hs h)
  · intro hc
    exact (show ContDiff ℝ 1 h from hc).comp (contDiff_of_motion hs)
  · intro hc
    exact hc.comp (contDiff_of_motion hs)
theorem hasCompactSupportIn_comp {E : Type*} [Zero E] (hs : IsEuclideanMotion s)
    {h : (Fin 4 → ℝ) → E} {A : Set (Fin 4 → ℝ)} (hA : HasCompactSupportIn h A) :
    HasCompactSupportIn (h ∘ s) (s ⁻¹' A) := by
  rw [HasCompactSupportIn, tsupport_comp_motion hs]
  exact ⟨isCompact_preimage_motion hs hA.1, Set.preimage_mono hA.2⟩
theorem comp_mem_lipschitzSupportedIn (hs : IsEuclideanMotion s) {A : Set (Fin 4 → ℝ)}
    {h : RealFun (Fin 4 → ℝ)} (hh : h ∈ lipschitzSupportedIn A) :
    h ∘ s ∈ lipschitzSupportedIn (s ⁻¹' A) := by
  refine ⟨?_, hasCompactSupportIn_comp hs hh.2⟩
  unfold LipConstFinite
  rw [ennLipConst_comp hs]
  exact hh.1
theorem comp_mem_c1SupportedIn (hs : IsEuclideanMotion s) {A : Set (Fin 4 → ℝ)}
    {h : RealFun (Fin 4 → ℝ)} (hh : h ∈ c1SupportedIn A) :
    h ∘ s ∈ c1SupportedIn (s ⁻¹' A) :=
  ⟨(show ContDiff ℝ 1 h from hh.1).comp (contDiff_of_motion hs), hasCompactSupportIn_comp hs hh.2⟩
theorem image_pi_familyComp (V : Set (Fin 4 → ℝ) → Set (RealFun (Fin 4 → ℝ)))
    (hV : ∀ {t : (Fin 4 → ℝ) → Fin 4 → ℝ}, IsEuclideanMotion t →
      ∀ {A : Set (Fin 4 → ℝ)} {h : RealFun (Fin 4 → ℝ)}, h ∈ V A → h ∘ t ∈ V (t ⁻¹' A))
    (hs : IsEuclideanMotion s) {q : ℕ+} (A : Fin q → Set (Fin 4 → ℝ)) :
    (fun h : Fin q → RealFun (Fin 4 → ℝ) => familyComp h s) ''
        Set.univ.pi (fun l => V (A l)) = Set.univ.pi (fun l => V (s ⁻¹' A l)) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩ l -
    exact hV hs (hh l (Set.mem_univ l))
  · intro hg
    refine ⟨fun l => g l ∘ hs.toPerm.symm, fun l _ => ?_, ?_⟩
    · have := hV hs.symm (hg l (Set.mem_univ l))
      rwa [preimage_symm_preimage] at this
    · funext l
      exact comp_symm_comp hs (g l)
theorem isAdmissibleSets_preimage (D : TransportData) (hs : IsEuclideanMotion s) {q : ℕ+}
    {d R : ℝ} (hd : 0 < d) (hR : 0 < R) {A : Fin q → Set (Fin 4 → ℝ)}
    (hA : IsAdmissibleSets D d R hd hR A) :
    IsAdmissibleSets D d R hd hR (fun l => s ⁻¹' A l) := by
  refine ⟨fun l => ?_, fun l k hlk => ?_⟩
  · obtain ⟨x, hx⟩ := hA.1 l
    refine ⟨hs.toPerm.symm x, fun y hy => ?_⟩
    have h₁ : euclidNormVec (s y - x) ≤ R := hx hy
    have h₂ := euclidNormVec_map_sub hs y (hs.toPerm.symm x)
    rw [motion_apply_symm hs] at h₂
    change euclidNormVec (y - hs.toPerm.symm x) ≤ R
    rwa [← h₂]
  · rw [setDist_preimage D hs]
    exact hA.2 l k hlk
theorem familyComp_mem_sepC1Families (D : TransportData) (hs : IsEuclideanMotion s) {n : ℕ+}
    {h : Domain.euclidean.FnFamily D n ℝ} (hh : h ∈ Domain.euclidean.sepC1Families D n) :
    (familyComp h s : Domain.euclidean.FnFamily D n ℝ) ∈ Domain.euclidean.sepC1Families D n := by
  refine ⟨⟨fun i => ?_, fun i => ?_, fun i k hik => ?_⟩, fun i => ?_⟩
  · have e : Domain.euclidean.lipConst D (h i ∘ s) = Domain.euclidean.lipConst D (h i) :=
      ennLipConst_comp hs (h i)
    change Domain.euclidean.lipConst D (h i ∘ s) < ⊤
    rw [e]
    exact hh.1.lipschitzOn i
  · change IsCompact (tsupport (h i ∘ s))
    rw [tsupport_comp_motion hs]
    exact isCompact_preimage_motion hs (hh.1.isCompact_support i)
  · change Disjoint (tsupport (h i ∘ s)) (tsupport (h k ∘ s))
    rw [tsupport_comp_motion hs, tsupport_comp_motion hs]
    exact (hh.1.pairwise_disjoint i k hik).preimage s
  · exact (show ContDiff ℝ 1 (h i) from hh.2 i).comp (contDiff_of_motion hs)
theorem sepFamiliesInvariance (D : TransportData) (hs : IsEuclideanMotion s) (n : ℕ+) :
    SepFamiliesInvariance D s n := by
  refine ⟨?_, fun hn h hh => ⟨familyComp_mem_sepC1Families D hs hh, ?_⟩⟩
  · ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact familyComp_mem_sepC1Families D hs hh
    · intro hg
      refine ⟨familyComp g hs.toPerm.symm, familyComp_mem_sepC1Families D hs.symm hg, ?_⟩
      funext i
      exact comp_symm_comp hs (g i)
  · refine Finset.inf'_congr _ rfl fun p _ => ?_
    change Domain.euclidean.setDist D (tsupport (h p.1 ∘ s)) (tsupport (h p.2 ∘ s)) =
      Domain.euclidean.setDist D (tsupport (h p.1)) (tsupport (h p.2))
    rw [tsupport_comp_motion hs, tsupport_comp_motion hs, setDist_preimage D hs]
end Maps
theorem motionInvariance (D : TransportData) : MotionInvariance D := fun _ hs =>
  ⟨fun h _ _ => compInvariance D hs h,
    fun _ _ _ hd hR A hA => ⟨isAdmissibleSets_preimage D hs hd hR hA,
      image_pi_familyComp _ (fun ht _ _ hh => comp_mem_lipschitzSupportedIn ht hh) hs A,
      image_pi_familyComp _ (fun ht _ _ hh => comp_mem_c1SupportedIn ht hh) hs A⟩,
    fun n => sepFamiliesInvariance D hs n⟩
theorem tsupport_toComplex_eq (f : RealFun (Fin 4 → ℝ)) : tsupport f.toComplex = tsupport f := by apply _root_.YangMills.Construction.FlatTensors.tsupport_ofReal_comp <;> assumption
theorem mem_realC1Compact_iff (f : RealFun (Fin 4 → ℝ)) :
    f ∈ realC1Compact ↔ ContDiff ℝ 1 f ∧ IsCompact (tsupport f) := by
  change (ContDiff ℝ 1 f.toComplex ∧ IsCompact (tsupport f.toComplex)) ↔ _
  rw [tsupport_toComplex_eq]
  refine and_congr_left fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have h₁ : ContDiff ℝ 1 (Complex.reCLM ∘ f.toComplex) := Complex.reCLM.contDiff.comp h
    have e : Complex.reCLM ∘ f.toComplex = f := by
      funext x
      simp [RealFun.toComplex]
    rwa [e] at h₁
  · exact Complex.ofRealCLM.contDiff.comp h
theorem partialDerivR4_eq_fderiv {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ}
    (hf : DifferentiableAt ℝ f x) (μ : Fin 4) :
    partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ 1) := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.C1Banach.partialDerivR4_eq_fderiv <;> assumption
theorem clm_apply_eq_sum (L : (Fin 4 → ℝ) →L[ℝ] ℝ) (y : Fin 4 → ℝ) :
    L y = ∑ ν, y ν * L (Pi.single ν 1) := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusC1Facts.clm_apply_eq_sum_basis <;> assumption
theorem gradR4_comp_orthoAffine {f : RealFun (Fin 4 → ℝ)} (hf : ContDiff ℝ 1 f)
    (S : Matrix (Fin 4) (Fin 4) ℝ) (v x : Fin 4 → ℝ) :
    gradR4 (f ∘ orthoAffine S v) x = Sᵀ *ᵥ gradR4 f (orthoAffine S v x) := by
  have hd : ∀ y, DifferentiableAt ℝ f y := fun y => (hf.differentiable one_ne_zero) y
  have hm : HasFDerivAt (orthoAffine S v)
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin S)) x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin S)).hasFDerivAt.add_const v
  have hc := (hd (orthoAffine S v x)).hasFDerivAt.comp x hm
  funext μ
  have hdc : DifferentiableAt ℝ (f ∘ orthoAffine S v) x := hc.differentiableAt
  change partialDerivR4 μ (f ∘ orthoAffine S v) x = _
  rw [partialDerivR4_eq_fderiv hdc, hc.fderiv]
  change fderiv ℝ f (orthoAffine S v x) (S *ᵥ Pi.single μ 1) = _
  rw [clm_apply_eq_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, gradR4]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [partialDerivR4_eq_fderiv (hd _)]
  simp [Pi.single_apply]
theorem transpose_mem_orthogonalGroup {S : Matrix (Fin 4) (Fin 4) ℝ}
    (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ) :
    Sᵀ ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.orth_transpose_mem <;> assumption
theorem gradNorm_comp (D : TransportData) {f : RealFun (Fin 4 → ℝ)} (hf : ContDiff ℝ 1 f)
    {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) :
    Domain.euclidean.gradNorm D (f ∘ s) = Domain.euclidean.gradNorm D f ∘ s := by
  obtain ⟨S, hS, v, rfl⟩ := hs
  funext x
  rw [Function.comp, gradNorm_euclidean_eq, gradNorm_euclidean_eq, gradR4_comp_orthoAffine hf]
  exact euclidNorm_mulVec (transpose_mem_orthogonalGroup hS) _
theorem gradSupNorm_comp (D : TransportData) {f : RealFun (Fin 4 → ℝ)} (hf : ContDiff ℝ 1 f)
    {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) :
    Domain.euclidean.gradSupNorm D (f ∘ s) = Domain.euclidean.gradSupNorm D f := by
  unfold Domain.gradSupNorm
  rw [gradNorm_comp D hf hs]
  exact ennSupNorm_comp hs _
theorem gradOscillation_comp (f g : realC1Compact)
    {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) (e : g.1 = f.1 ∘ s) (δ : ℝ≥0) :
    gradOscillation g δ = gradOscillation f δ := by
  have hf : ContDiff ℝ 1 f.1 := ((mem_realC1Compact_iff f.1).mp f.2).1
  unfold gradOscillation
  rw [← iSup₂_comp_motion hs fun x y => ⨆ _ : euclidNorm (x - y) ≤ δ,
    ENNReal.ofReal (euclidNorm (gradR4 f.1 x - gradR4 f.1 y))]
  refine iSup_congr fun x => iSup_congr fun y => ?_
  obtain ⟨S, hS, v, rfl⟩ := id hs
  have e₁ : euclidNorm (orthoAffine S v x - orthoAffine S v y) = euclidNorm (x - y) :=
    euclidNormVec_map_sub hs x y
  have e₂ : euclidNorm (gradR4 g.1 x - gradR4 g.1 y) =
      euclidNorm (gradR4 f.1 (orthoAffine S v x) - gradR4 f.1 (orthoAffine S v y)) := by
    rw [e, gradR4_comp_orthoAffine hf, gradR4_comp_orthoAffine hf, ← Matrix.mulVec_sub]
    exact euclidNorm_mulVec (transpose_mem_orthogonalGroup hS) _
  rw [e₁, e₂]
theorem translationModulus_comp_motion (D : TransportData) (f g : realC1Compact)
    {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) (e : g.1 = f.1 ∘ s) :
    D.translationModulus g = D.translationModulus f := by
  have hf : ContDiff ℝ 1 f.1 := ((mem_realC1Compact_iff f.1).mp f.2).1
  funext δ
  unfold TransportData.translationModulus
  rw [gradOscillation_comp f g hs e, e, gradSupNorm_comp D hf hs]
theorem translateFn_eq_comp {β : Type*} (D : TransportData) (a : Fin 4 → ℝ)
    (h : (Fin 4 → ℝ) → β) :
    Domain.euclidean.translateFn D a h = h ∘ orthoAffine 1 (-a) := by
  funext x
  change h (x - a) = h (orthoAffine 1 (-a) x)
  simp [orthoAffine, sub_eq_add_neg]
theorem gradR4_translateFn (D : TransportData) {f : RealFun (Fin 4 → ℝ)} (hf : ContDiff ℝ 1 f)
    (a x : Fin 4 → ℝ) :
    gradR4 (Domain.euclidean.translateFn D a f) x = gradR4 f (x - a) := by
  rw [translateFn_eq_comp, gradR4_comp_orthoAffine hf]
  simp [orthoAffine, sub_eq_add_neg]
theorem isEuclideanMotion_translation (a : Fin 4 → ℝ) : IsEuclideanMotion (orthoAffine 1 (-a)) :=
  ⟨1, one_mem _, -a, rfl⟩
theorem gradR4_sub {g₁ g₂ : RealFun (Fin 4 → ℝ)} (h₁ : ContDiff ℝ 1 g₁)
    (h₂ : ContDiff ℝ 1 g₂) (x : Fin 4 → ℝ) :
    gradR4 (g₁ - g₂) x = gradR4 g₁ x - gradR4 g₂ x := by
  have d₁ : DifferentiableAt ℝ g₁ x := (h₁.differentiable one_ne_zero) x
  have d₂ : DifferentiableAt ℝ g₂ x := (h₂.differentiable one_ne_zero) x
  have hs : HasFDerivAt (g₁ - g₂) (fderiv ℝ g₁ x - fderiv ℝ g₂ x) x :=
    d₁.hasFDerivAt.sub d₂.hasFDerivAt
  funext μ
  change partialDerivR4 μ (g₁ - g₂) x = partialDerivR4 μ g₁ x - partialDerivR4 μ g₂ x
  rw [partialDerivR4_eq_fderiv hs.differentiableAt, partialDerivR4_eq_fderiv d₁,
    partialDerivR4_eq_fderiv d₂, hs.fderiv]
  rfl
theorem tsupport_sub_subset_union (g₁ g₂ : RealFun (Fin 4 → ℝ)) :
    tsupport (g₁ - g₂) ⊆ tsupport g₁ ∪ tsupport g₂ := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.tsupport_sub_subset <;> assumption
theorem comp_mem_realC1Compact {f : RealFun (Fin 4 → ℝ)} (hf : f ∈ realC1Compact)
    {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) :
    f ∘ s ∈ realC1Compact := by
  obtain ⟨h₁, h₂⟩ := (mem_realC1Compact_iff f).mp hf
  refine (mem_realC1Compact_iff _).mpr ⟨h₁.comp (contDiff_of_motion hs), ?_⟩
  rw [tsupport_comp_motion hs]
  exact isCompact_preimage_motion hs h₂
theorem translateFn_sub_mem (D : TransportData) {f : RealFun (Fin 4 → ℝ)}
    (hf : f ∈ realC1Compact) (a b : Fin 4 → ℝ) :
    Domain.euclidean.translateFn D a f - Domain.euclidean.translateFn D b f ∈ realC1Compact := by
  rw [translateFn_eq_comp, translateFn_eq_comp]
  obtain ⟨ca, ka⟩ := (mem_realC1Compact_iff _).mp
    (comp_mem_realC1Compact hf (isEuclideanMotion_translation a))
  obtain ⟨cb, kb⟩ := (mem_realC1Compact_iff _).mp
    (comp_mem_realC1Compact hf (isEuclideanMotion_translation b))
  exact (mem_realC1Compact_iff _).mpr ⟨ca.sub cb,
    (ka.union kb).of_isClosed_subset (isClosed_tsupport _) (tsupport_sub_subset_union _ _)⟩
theorem euclidNorm_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNorm v := Real.sqrt_nonneg _
theorem euclidNorm_neg (v : Fin 4 → ℝ) : euclidNorm (-v) = euclidNorm v := by
  simp [euclidNorm, euclidNormVec]
theorem norm_le_euclidNorm (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNorm v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem euclidNorm_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNorm v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
theorem gradOscillation_mono (f : realC1Compact) :
    Monotone (gradOscillation f) := fun _ _ hδ =>
  iSup₂_le fun x y => iSup_le fun h =>
    le_iSup₂_of_le x y (le_iSup_of_le (h.trans (NNReal.coe_le_coe.mpr hδ)) le_rfl)
theorem translationModulus_monotone (D : TransportData) (f : realC1Compact) :
    Monotone (D.translationModulus f) := fun _ _ hδ => by
  unfold TransportData.translationModulus
  refine max_le_max ?_ ?_
  · gcongr
  · have := gradOscillation_mono f hδ
    gcongr
theorem continuous_gradR4 {f : RealFun (Fin 4 → ℝ)} (hf : ContDiff ℝ 1 f) :
    Continuous (gradR4 f) := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.continuous_gradR4 <;> assumption
theorem tendsto_gradOscillation_zero (f : realC1Compact) :
    Filter.Tendsto (gradOscillation f) (𝓝 0) (𝓝 0) := by
  obtain ⟨hc, hk⟩ := (mem_realC1Compact_iff f.1).mp f.2
  have hd : ∀ y, DifferentiableAt ℝ f.1 y := fun y => (hc.differentiable one_ne_zero) y
  have hsupp : HasCompactSupport (gradR4 f.1) := by
    refine HasCompactSupport.intro hk fun x hx => ?_
    have h₀ : fderiv ℝ f.1 x = 0 := by
      by_contra hne
      exact hx (support_fderiv_subset ℝ hne)
    funext μ
    change partialDerivR4 μ f.1 x = 0
    rw [partialDerivR4_eq_fderiv (hd x), h₀]
    rfl
  have huc := hsupp.uniformContinuous_of_continuous (continuous_gradR4 hc)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hr : (0 : ℝ) < r := by exact_mod_cast hr0
  obtain ⟨δ₀, hδ₀, H⟩ := Metric.uniformContinuous_iff.mp huc (r / 2) (by positivity)
  filter_upwards [Iio_mem_nhds (Real.toNNReal_pos.mpr hδ₀)] with δ hδ
  have hδ' : (δ : ℝ) < δ₀ := Real.lt_toNNReal_iff_coe_lt.mp hδ
  refine le_trans (iSup₂_le fun x y => iSup_le fun hxy => ?_) hrε.le
  have hdist : dist x y < δ₀ := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt ((norm_le_euclidNorm _).trans hxy) hδ'
  have h₁ := H hdist
  rw [dist_eq_norm] at h₁
  have h₂ := euclidNorm_le_two_mul_norm (gradR4 f.1 x - gradR4 f.1 y)
  have h₃ : euclidNorm (gradR4 f.1 x - gradR4 f.1 y) ≤ r := by linarith
  calc ENNReal.ofReal (euclidNorm (gradR4 f.1 x - gradR4 f.1 y))
      ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal h₃
    _ = r := ENNReal.ofReal_coe_nnreal
theorem tendsto_translationModulus_zero (D : TransportData)
    (hN : SupportFacts.AllSupportFacts) (f : realC1Compact) :
    Filter.Tendsto (D.translationModulus f) (𝓝 0) (𝓝 0) := by
  have hfin := ((hN D).2.2.2.2.1 f.1 f.2).1
  have h₁ : Filter.Tendsto
      (fun δ : ℝ≥0 => Domain.euclidean.gradSupNorm D f.1 * (δ : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
    have hco : Filter.Tendsto (fun δ : ℝ≥0 => (δ : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
      simpa using (ENNReal.continuous_coe.tendsto (0 : ℝ≥0))
    simpa using ENNReal.Tendsto.const_mul hco (Or.inr hfin.ne)
  have h₂ : Filter.Tendsto
      (fun δ : ℝ≥0 => ENNReal.ofReal (40 * D.M) * gradOscillation f δ) (𝓝 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (40 * D.M))
      (tendsto_gradOscillation_zero f) (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at h
  have h₃ := h₁.max h₂
  rw [max_self] at h₃
  exact h₃
theorem ennSharpNorm_translateFn_sub_le (D : TransportData)
    (hN : SupportFacts.AllSupportFacts) (f : realC1Compact) (a b : Fin 4 → ℝ) :
    Domain.euclidean.ennSharpNorm D
        (Domain.euclidean.translateFn D a f.1 - Domain.euclidean.translateFn D b f.1) ≤
      D.translationModulus f (Real.toNNReal (euclidNorm (a - b))) := by
  obtain ⟨hc, -⟩ := (mem_realC1Compact_iff f.1).mp f.2
  have hd := (hN D).2.2.2.2.1
  have hfd := hd f.1 f.2
  have hm := translateFn_sub_mem D f.2 a b
  have hδ : ((Real.toNNReal (euclidNorm (a - b)) : ℝ≥0) : ℝ) = euclidNorm (a - b) :=
    Real.coe_toNNReal _ (euclidNorm_nonneg _)
  refine max_le_max ?_ ?_
  · refine iSup_le fun x => ?_
    have h₁ := hfd.2.1 (x - a) (x - b)
    have e : x - a - (x - b) = -(a - b) := by abel
    rw [e, euclidNorm_neg] at h₁
    calc ENNReal.ofReal ‖(Domain.euclidean.translateFn D a f.1 -
          Domain.euclidean.translateFn D b f.1) x‖
        ≤ ENNReal.ofReal ((Domain.euclidean.gradSupNorm D f.1).toReal *
            euclidNorm (a - b)) := ENNReal.ofReal_le_ofReal h₁
      _ = _ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfd.1.ne]
        rfl
  · have h₂ : Domain.euclidean.gradSupNorm D (Domain.euclidean.translateFn D a f.1 -
        Domain.euclidean.translateFn D b f.1) ≤
        gradOscillation f (Real.toNNReal (euclidNorm (a - b))) := by
      refine iSup_le fun x => ?_
      have ca : ContDiff ℝ 1 (Domain.euclidean.translateFn D a f.1) := by
        rw [translateFn_eq_comp]
        exact hc.comp (contDiff_orthoAffine _ _)
      have cb : ContDiff ℝ 1 (Domain.euclidean.translateFn D b f.1) := by
        rw [translateFn_eq_comp]
        exact hc.comp (contDiff_orthoAffine _ _)
      rw [gradNorm_euclidean_eq, gradR4_sub ca cb, gradR4_translateFn D hc,
        gradR4_translateFn D hc, Real.norm_of_nonneg (euclidNorm_nonneg _)]
      have e : x - b - (x - a) = a - b := by abel
      have e' : gradR4 f.1 (x - a) - gradR4 f.1 (x - b) =
          -(gradR4 f.1 (x - b) - gradR4 f.1 (x - a)) := by abel
      rw [e', euclidNorm_neg]
      exact le_iSup₂_of_le (x - b) (x - a) (le_iSup_of_le (by rw [e, hδ]) le_rfl)
    have h₃ := (hd _ hm).2.2.trans h₂
    gcongr
theorem translationModulusProps (D : TransportData) (hN : SupportFacts.AllSupportFacts) :
    TranslationModulusProps D := fun f =>
  ⟨translationModulus_monotone D f, tendsto_translationModulus_zero D hN f,
    ennSharpNorm_translateFn_sub_le D hN f,
    fun _ hs => ⟨comp_mem_realC1Compact f.2 hs,
      translationModulus_comp_motion D f ⟨_, comp_mem_realC1Compact f.2 hs⟩ hs rfl⟩⟩
theorem basisVec_self (μ : Fin 4) : basisVec μ μ = 1 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.basisVector_apply_self <;> assumption
theorem basisVec_of_ne {μ ν : Fin 4} (h : ν ≠ μ) : basisVec μ ν = 0 := by
  simp [basisVec, PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
theorem hyperplaneReflect_eq_add_smul (μ : Fin 4) (c c' : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflect μ c' x = hyperplaneReflect μ c x + (2 * (c' - c)) • basisVec μ := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.hyperplaneReflect_eq_add_smul <;> assumption
theorem hyperplaneReflect_sub_smul (μ : Fin 4) (c t : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflect μ c (x - t • basisVec μ) = hyperplaneReflect μ c x + t • basisVec μ := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.hyperplaneReflect_sub_smul <;> assumption
theorem hyperplaneReflect_involutive_apply (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflect μ c (hyperplaneReflect μ c x) = x := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.hyperplaneReflect_hyperplaneReflect <;> assumption
theorem comp_hyperplaneReflect_eq {β : Type*} (D : TransportData) (μ : Fin 4) (c c' : ℝ)
    (f : (Fin 4 → ℝ) → β) :
    f ∘ hyperplaneReflect μ c' =
      Domain.euclidean.translateFn D ((2 * (c' - c)) • basisVec μ) (f ∘ hyperplaneReflect μ c) := by
  funext x
  change f (hyperplaneReflect μ c' x) =
    f (hyperplaneReflect μ c (x - (2 * (c' - c)) • basisVec μ))
  rw [hyperplaneReflect_sub_smul, hyperplaneReflect_eq_add_smul μ c c']
theorem isEuclideanMotion_of_mem (hG : AffineGroup.AffineGroupOnTori) (D : TransportData)
    {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (h : s ∈ affineHyperoctahedral) : IsEuclideanMotion s := by
  obtain ⟨S, hS, v, e, -⟩ := ((hG D).2.1.1 s).mp h
  exact ⟨S, hS, v, e⟩
theorem euclidNorm_smul_basisVec (t : ℝ) (μ : Fin 4) :
    euclidNorm (t • basisVec μ) = |t| := by apply _root_.YangMills.Construction.LimitSpaces.MirrorTranslation.euclidNormVec_smul_stdBasisVec <;> assumption
theorem parallelReflect (D : TransportData) (hG : AffineGroup.AffineGroupOnTori)
    (hN : SupportFacts.AllSupportFacts) : ParallelReflect D := by
  intro μ c c'
  refine ⟨fun f => ⟨comp_hyperplaneReflect_eq D μ c c' f, ?_⟩, fun f => ?_⟩
  · have hr := isEuclideanMotion_of_mem hG D (hyperplaneReflect_mem_affineHyperoctahedral μ c')
    change tsupport (f ∘ hyperplaneReflect μ c') = _ '' (_ '' tsupport f)
    rw [tsupport_comp_motion hr]
    ext y
    constructor
    · intro hy
      refine ⟨_, ⟨hyperplaneReflect μ c' y, hy, rfl⟩, ?_⟩
      rw [translationEquiv_apply, ← hyperplaneReflect_eq_add_smul,
        hyperplaneReflect_involutive_apply]
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      rw [translationEquiv_apply, ← hyperplaneReflect_eq_add_smul]
      change hyperplaneReflect μ c' (hyperplaneReflect μ c' k) ∈ tsupport f
      rwa [hyperplaneReflect_involutive_apply]
  · have hr := isEuclideanMotion_of_mem hG D (hyperplaneReflect_mem_affineHyperoctahedral μ c)
    have hb := ennSharpNorm_translateFn_sub_le D hN
      ⟨f.1 ∘ hyperplaneReflect μ c, comp_mem_realC1Compact f.2 hr⟩
      ((2 * (c' - c)) • basisVec μ) 0
    have e : Domain.euclidean.translateFn D ((2 * (c' - c)) • basisVec μ)
          (f.1 ∘ hyperplaneReflect μ c) -
          Domain.euclidean.translateFn D 0 (f.1 ∘ hyperplaneReflect μ c) =
        f.1 ∘ hyperplaneReflect μ c' - f.1 ∘ hyperplaneReflect μ c := by
      rw [← comp_hyperplaneReflect_eq]
      congr 1
      funext x
      change (f.1 ∘ hyperplaneReflect μ c) (x - 0) = _
      rw [sub_zero]
    have em := translationModulus_comp_motion D f
      ⟨f.1 ∘ hyperplaneReflect μ c, comp_mem_realC1Compact f.2 hr⟩ hr rfl
    rw [em, sub_zero, euclidNorm_smul_basisVec, abs_mul, abs_two] at hb
    change Domain.euclidean.ennSharpNorm D (Domain.euclidean.translateFn D _
      (f.1 ∘ hyperplaneReflect μ c) -
        Domain.euclidean.translateFn D 0 (f.1 ∘ hyperplaneReflect μ c)) ≤ _ at hb
    rwa [e] at hb
theorem basisVec_dotProduct (μ : Fin 4) (x : Fin 4 → ℝ) : basisVec μ ⬝ᵥ x = x μ := by apply _root_.YangMills.Construction.InfiniteLattice.BoxQuotient.coordVec_dotProduct <;> assumption
theorem dotProduct_self_eq_one {n : Fin 4 → ℝ} (hn : euclidNorm n = 1) : n ⬝ᵥ n = 1 := by apply _root_.YangMills.DeltaSharedProofs.p3944 <;> assumption
theorem reflectAcross_zero_sub (n x b : Fin 4 → ℝ) :
    reflectAcross n 0 (x - b) = reflectAcross n 0 x - reflectAcross n 0 b := by
  funext ν
  simp only [reflectAcross, scalarProd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct_sub]
  ring
theorem reflectTranslateCommute (D : TransportData) {n : Fin 4 → ℝ} (hn : euclidNorm n = 1)
    (f : ComplexFun (Fin 4 → ℝ)) (b : Fin 4 → ℝ) (c : ℝ) :
    ReflectTranslateCommute D n f b c := by
  refine ⟨?_, ?_⟩
  · funext x
    change f (reflectAcross n 0 (x - b)) = f (reflectAcross n 0 x - reflectAcross n 0 b)
    rw [reflectAcross_zero_sub]
  · funext x
    change f (reflectAcross n c (x - -(c • n))) = f (reflectAcross n 0 x - -(c • n))
    congr 1
    have e : n ⬝ᵥ (x + c • n) = n ⬝ᵥ x + c := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_self_eq_one hn]
      simp
    rw [sub_neg_eq_add, sub_neg_eq_add]
    funext ν
    simp only [reflectAcross, scalarProd, e, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
theorem timeReflect_sub_of_coord_eq_zero {x b : Fin 4 → ℝ} (hb : b 3 = 0) :
    timeReflect (x - b) = timeReflect x - b := by
  funext ν
  by_cases h : ν = 3
  · subst h
    simp only [timeReflect, Pi.sub_apply, hyperplaneReflect_apply_self, hb]
    ring
  · simp only [timeReflect, Pi.sub_apply, hyperplaneReflect_apply_of_ne h]
theorem timeReflect_add_smul (x : Fin 4 → ℝ) (t : ℝ) :
    timeReflect (x + t • basisVec 3) = timeReflect x - t • basisVec 3 := by
  funext ν
  by_cases h : ν = 3
  · subst h
    simp only [timeReflect, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      hyperplaneReflect_apply_self, basisVec_self]
    ring
  · simp only [timeReflect, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      hyperplaneReflect_apply_of_ne h, basisVec_of_ne h]
    ring
theorem inv_sqrt_two_mul_inv_sqrt_two : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by apply _root_.YangMills.Construction.TwoPoints.ShiftPairingLocallyAnalytic.inv_sqrt_two_mul_self <;> assumption
theorem exists_hyperoctahedral_eq_reflectAcross {n : Fin 4 → ℝ} (hn : IsRootDirection n) :
    ∃ w : hyperoctahedral, ⇑w.1 = reflectAcross n 0 := by
  have ht := inv_sqrt_two_mul_inv_sqrt_two
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, lam, hlt, rfl | rfl⟩
  · refine ⟨coordNegation μ, ?_⟩
    rw [coe_coordNegation]
    funext x ν
    simp only [reflectAcross, scalarProd, basisVec_dotProduct, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    by_cases h : ν = μ
    · subst h
      rw [hyperplaneReflect_apply_self, basisVec_self]
      ring
    · rw [hyperplaneReflect_apply_of_ne h, basisVec_of_ne h]
      ring
  · have hne : μ ≠ lam := hlt.ne
    refine ⟨⟨TorusLifts.signedCoordinateEquiv (Equiv.swap μ lam)
      (fun ν => if ν = μ ∨ ν = lam then -1 else 1), ⟨_, _, rfl⟩⟩, ?_⟩
    funext x ν
    change TorusLifts.signedCoordinateEquiv _ _ x ν = _
    rw [signedCoordinateEquiv_apply]
    simp only [reflectAcross, scalarProd, smul_dotProduct, add_dotProduct,
      basisVec_dotProduct, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    by_cases h₁ : ν = μ
    · subst h₁
      rw [Equiv.swap_apply_left, basisVec_self, basisVec_of_ne hne]
      simp only [true_or, if_true, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      linear_combination (2 * (x ν + x lam)) * ht
    · by_cases h₂ : ν = lam
      · subst h₂
        rw [Equiv.swap_apply_right, basisVec_self, basisVec_of_ne h₁]
        simp only [or_true, if_true, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
        linear_combination (2 * (x μ + x ν)) * ht
      · rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂, basisVec_of_ne h₁, basisVec_of_ne h₂]
        simp [h₁, h₂]
  · have hne : μ ≠ lam := hlt.ne
    refine ⟨⟨TorusLifts.signedCoordinateEquiv (Equiv.swap μ lam) 1, ⟨_, _, rfl⟩⟩, ?_⟩
    funext x ν
    change TorusLifts.signedCoordinateEquiv _ _ x ν = _
    rw [signedCoordinateEquiv_apply]
    simp only [reflectAcross, scalarProd, smul_dotProduct, sub_dotProduct,
      basisVec_dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply,
      Units.val_one, Int.cast_one, one_mul]
    by_cases h₁ : ν = μ
    · subst h₁
      rw [Equiv.swap_apply_left, basisVec_self, basisVec_of_ne hne]
      linear_combination (2 * (x ν - x lam)) * ht
    · by_cases h₂ : ν = lam
      · subst h₂
        rw [Equiv.swap_apply_right, basisVec_self, basisVec_of_ne h₁]
        linear_combination (-(2 * (x μ - x ν))) * ht
      · rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂, basisVec_of_ne h₁, basisVec_of_ne h₂]
        simp
theorem hyperplaneReflectProps (D : TransportData) : HyperplaneReflectProps D := by
  refine ⟨fun n hn f b c => reflectTranslateCommute D hn f b c, fun f t => ?_, fun f b hb => ?_,
    fun n _ h => exists_hyperoctahedral_eq_reflectAcross h⟩
  · funext x
    change f (timeReflect (x - -(t • basisVec 3))) = f (timeReflect x - t • basisVec 3)
    rw [sub_neg_eq_add, timeReflect_add_smul]
  · have hb' : b 3 = 0 := by
      have e : basisVec 3 ⬝ᵥ b = 0 := by rwa [dotProduct_comm]
      rwa [basisVec_dotProduct] at e
    funext x
    change f (timeReflect (x - b)) = f (timeReflect x - b)
    rw [timeReflect_sub_of_coord_eq_zero hb']
theorem halfSpaceNormalize_apply (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) (ν : Fin 4) :
    halfSpaceNormalize μ c x ν = (x - c • basisVec μ) (Equiv.swap μ 3 ν) :=
  swapLast_apply μ ν _
theorem halfSpaceTimeReflect : HalfSpaceTimeReflect := by
  intro μ c
  refine ⟨⟨swapLast μ, -(swapLast μ).1 (c • basisVec μ), funext fun x => ?_⟩, ?_, ?_⟩
  · have e := map_sub (hyperoctahedralLinear (swapLast μ)) x (c • basisVec μ)
    simp only [coe_hyperoctahedralLinear] at e
    change (swapLast μ).1 (x - c • basisVec μ) = (swapLast μ).1 x + _
    rw [e, sub_eq_add_neg]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 0 < halfSpaceNormalize μ c x 3
      rw [halfSpaceNormalize_apply, Equiv.swap_apply_right]
      have hx' : c < x μ := hx
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVec_self]
      linarith
    · intro hy
      have hy' : 0 < y 3 := hy
      refine ⟨fun ν => y (Equiv.swap μ 3 ν) + c * basisVec μ ν, ?_, ?_⟩
      · change c < y (Equiv.swap μ 3 μ) + c * basisVec μ μ
        rw [Equiv.swap_apply_left, basisVec_self]
        linarith
      · funext ν
        rw [halfSpaceNormalize_apply]
        simp
  · funext x ν
    simp only [Function.comp]
    rw [halfSpaceNormalize_apply]
    by_cases h : ν = 3
    · subst h
      have e : timeReflect (halfSpaceNormalize μ c x) 3 = 2 * 0 - halfSpaceNormalize μ c x 3 :=
        hyperplaneReflect_apply_self 3 0 _
      rw [e, halfSpaceNormalize_apply, Equiv.swap_apply_right]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVec_self,
        hyperplaneReflect_apply_self]
      ring
    · have e : timeReflect (halfSpaceNormalize μ c x) ν = halfSpaceNormalize μ c x ν :=
        hyperplaneReflect_apply_of_ne h 0 _
      rw [e, halfSpaceNormalize_apply]
      have hne : Equiv.swap μ 3 ν ≠ μ := fun h' => h (by
        have := congrArg (Equiv.swap μ 3) h'
        simpa using this)
      simp only [Pi.sub_apply, hyperplaneReflect_apply_of_ne hne]
theorem statement_holds (hG : AffineGroup.AffineGroupOnTori)
    (hN : SupportFacts.AllSupportFacts) : Statement :=
  fun D => ⟨motionInvariance D, translationModulusProps D hN, parallelReflect D hG hN,
    hyperplaneReflectProps D, halfSpaceTimeReflect⟩
end YangMills.Construction.TorusTransport.MotionFacts
end
