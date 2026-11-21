import YangMills.Construction.Continuum.IsometriesOfFourSpaceAndOfATorusReflectionsAndInducedMaps
import YangMills.Construction.InfiniteLattice.DataOfADiagonalPictureProof
import YangMills.Construction.PassageToTheLimit.MovingAMirrorIsTranslatingTheImageProof
import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpacesProof
import YangMills.Construction.Continuum.NormsBallsDistancesAndSupportsInFourSpace
import YangMills.Construction.GrowingTori.IsometriesMirrorsAndAdicPointsAlongGrowingTori
import YangMills.Construction.GrowingTori.TranslationsIsometriesAndMirrorsOfFourSpace
import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1OnOneTorusProof
import YangMills.Construction.ReflectionPositivity.ModulusOfAFunctionOfClassC1TendsToZero
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotionsProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal ContDiff Topology
open Matrix
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient (ScaleParam compactC1 vecLength
  gradOsc gradSup smoothModulus normSharp)
open YangMills.Construction.TorusTransport (IsEuclideanMotion hyperoctahedral orthoAffine
  hyperplaneReflect timeReflect familyComp basisVec)
noncomputable section
namespace YangMills.Construction.ToriLimits.EuclideanSymmetryFacts
def signedPermMatrix (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν => if π μ = ν then ((ε μ : ℤ) : ℝ) else 0
theorem signedPermMatrix_mulVec (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ) (x : Fin 4 → ℝ) :
    signedPermMatrix π ε *ᵥ x = TorusLifts.signedCoordinateEquiv π ε x := by
  funext μ
  rw [TorusTransport.signedCoordinateEquiv_apply]
  simp [signedPermMatrix, Matrix.mulVec, dotProduct, ite_mul]
theorem intUnit_cast_mul_self (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]
theorem signedPermMatrix_mem_orthogonalGroup (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ) :
    signedPermMatrix π ε ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext μ ν
  simp only [Matrix.mul_apply, Matrix.transpose_apply, signedPermMatrix, ite_mul, mul_ite, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.one_apply]
  by_cases h : μ = ν
  · subst h
    simp [intUnit_cast_mul_self]
  · have h' : ¬π ν = π μ := fun e => h (π.injective e).symm
    simp [h]
theorem isEuclideanMotion_of_mem_affineHyperoctahedral {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hs : s ∈ TorusTransport.affineHyperoctahedral) : IsEuclideanMotion s := by
  obtain ⟨⟨_, π, ε, rfl⟩, v, rfl⟩ := hs
  refine ⟨signedPermMatrix π ε, signedPermMatrix_mem_orthogonalGroup π ε, v, funext fun x => ?_⟩
  rw [orthoAffine, signedPermMatrix_mulVec]
  rfl
theorem isEuclideanMotion_hyperplaneReflect (μ : Fin 4) (c : ℝ) :
    IsEuclideanMotion (hyperplaneReflect μ c) :=
  isEuclideanMotion_of_mem_affineHyperoctahedral
    (TorusTransport.hyperplaneReflect_mem_affineHyperoctahedral μ c)
section
variable {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
theorem contDiff_orthoAffine (S : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ)
    {n : WithTop ℕ∞} : ContDiff ℝ n (orthoAffine S v) :=
  ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin S)).contDiff).add contDiff_const
theorem contDiff_of_isEuclideanMotion (hs : IsEuclideanMotion s) {n : WithTop ℕ∞} :
    ContDiff ℝ n s := by
  obtain ⟨S, -, v, rfl⟩ := hs
  exact contDiff_orthoAffine S v
theorem continuous_of_isEuclideanMotion (hs : IsEuclideanMotion s) : Continuous s :=
  (contDiff_of_isEuclideanMotion hs (n := 0)).continuous
def motionToHomeomorph (hs : IsEuclideanMotion s) : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toEquiv := hs.toPerm
  continuous_toFun := continuous_of_isEuclideanMotion hs
  continuous_invFun := continuous_of_isEuclideanMotion hs.symm
theorem motion_apply_symm (hs : IsEuclideanMotion s) (y : Fin 4 → ℝ) :
    s (hs.toPerm.symm y) = y :=
  hs.toPerm.apply_symm_apply y
theorem motion_symm_apply (hs : IsEuclideanMotion s) (x : Fin 4 → ℝ) :
    hs.toPerm.symm (s x) = x :=
  hs.toPerm.symm_apply_apply x
theorem comp_symm_comp_motion {β : Type*} (hs : IsEuclideanMotion s) (g : (Fin 4 → ℝ) → β) :
    (g ∘ hs.toPerm.symm) ∘ s = g := by
  funext x
  exact congrArg g (motion_symm_apply hs x)
theorem motion_dist_eq (hs : IsEuclideanMotion s) (x y : Fin 4 → ℝ) :
    euclidNormVec (s x - s y) = euclidNormVec (x - y) := by apply _root_.YangMills.Construction.TorusTransport.IsEuclideanMotion.isDistancePreserving <;> assumption
theorem fnSupport_comp_motion {Z : Type*} [Zero Z] (hs : IsEuclideanMotion s)
    (h : (Fin 4 → ℝ) → Z) : fnSupport (h ∘ s) = s ⁻¹' fnSupport h :=
  tsupport_comp_eq_preimage h (motionToHomeomorph hs)
theorem isCompact_preimage_motion (hs : IsEuclideanMotion s) {K : Set (Fin 4 → ℝ)}
    (hK : IsCompact K) : IsCompact (s ⁻¹' K) :=
  (motionToHomeomorph hs).isCompact_preimage.mpr hK
theorem preimage_symm_preimage (hs : IsEuclideanMotion s) (A : Set (Fin 4 → ℝ)) :
    hs.toPerm.symm ⁻¹' (s ⁻¹' A) = A := by
  ext y
  simp only [Set.mem_preimage]
  rw [motion_apply_symm hs]
theorem iSup₂_comp_motion {α : Type*} [CompleteLattice α] (hs : IsEuclideanMotion s)
    (g : (Fin 4 → ℝ) → (Fin 4 → ℝ) → α) :
    ⨆ (u : Fin 4 → ℝ) (v : Fin 4 → ℝ), g (s u) (s v) = ⨆ (u : Fin 4 → ℝ) (v : Fin 4 → ℝ), g u v := by
  have hsurj := hs.bijective.surjective
  rw [← hsurj.iSup_comp fun u => ⨆ v, g u v]
  exact iSup_congr fun u => hsurj.iSup_comp fun v => g (s u) v
theorem uniformNorm_comp_motion (hs : IsEuclideanMotion s) (h : RealFn) :
    TestFunctions.uniformNorm (h ∘ s) = TestFunctions.uniformNorm h :=
  hs.bijective.surjective.iSup_comp fun u => ‖h u‖
theorem lipConst_comp_motion (hs : IsEuclideanMotion s) (h : RealFn) :
    lipConst (h ∘ s) = lipConst h := by
  refine congrArg sInf (Set.ext fun C => and_congr_right fun _ => ?_)
  constructor
  · intro H x y
    have e := H (hs.toPerm.symm x) (hs.toPerm.symm y)
    simp only [Function.comp, motion_apply_symm hs] at e
    have e' : TestFunctions.euclidDistR4 (hs.toPerm.symm x) (hs.toPerm.symm y) =
        TestFunctions.euclidDistR4 x y := by
      have := motion_dist_eq hs (hs.toPerm.symm x) (hs.toPerm.symm y)
      rw [motion_apply_symm hs, motion_apply_symm hs] at this
      exact this.symm
    rwa [e'] at e
  · intro H x y
    have e := H (s x) (s y)
    have e' : TestFunctions.euclidDistR4 (s x) (s y) = TestFunctions.euclidDistR4 x y :=
      motion_dist_eq hs x y
    rwa [e'] at e
theorem normSharp_comp_motion (D : ReflectionPositivity.AxisMirror.MirrorData) (M : ScaleParam)
    (hs : IsEuclideanMotion s) (h : RealFn) :
    normSharp D M .euclidean (h ∘ s) = normSharp D M .euclidean h := by
  change max (TestFunctions.uniformNorm (h ∘ s)) (40 * (M : ℝ) * lipConst (h ∘ s)) =
    max (TestFunctions.uniformNorm h) (40 * (M : ℝ) * lipConst h)
  rw [uniformNorm_comp_motion hs, lipConst_comp_motion hs]
theorem infDist_preimage_motion (hs : IsEuclideanMotion s) (A B : Set (Fin 4 → ℝ)) :
    infDist (s ⁻¹' A) (s ⁻¹' B) = infDist A B := by
  apply le_antisymm
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
    obtain ⟨a', rfl⟩ := hs.bijective.surjective a
    obtain ⟨b', rfl⟩ := hs.bijective.surjective b
    refine iInf₂_le_of_le a' ha (iInf₂_le_of_le b' hb ?_)
    rw [motion_dist_eq hs]
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
    refine iInf₂_le_of_le (s a) ha (iInf₂_le_of_le (s b) hb ?_)
    rw [motion_dist_eq hs]
theorem comp_mem_c1SuppIn (σ : Conventions.StandingParameters) (hs : IsEuclideanMotion s)
    {A : Set (Fin 4 → ℝ)} {h : RealFn} (hh : h ∈ c1SuppIn σ A) :
    h ∘ s ∈ c1SuppIn σ (s ⁻¹' A) := by
  obtain ⟨h₁, h₂, h₃⟩ := (mem_c1SuppIn_iff σ A h).1 hh
  refine (mem_c1SuppIn_iff σ _ _).2 ⟨h₁.comp (contDiff_of_isEuclideanMotion hs), ?_, ?_⟩
  · rw [fnSupport_comp_motion hs]
    exact isCompact_preimage_motion hs h₂
  · rw [fnSupport_comp_motion hs]
    exact Set.preimage_mono h₃
theorem image_familyComp_pi_c1SuppIn (σ : Conventions.StandingParameters)
    (hs : IsEuclideanMotion s) {q : ℕ} (A : Fin q → Set (Fin 4 → ℝ)) :
    (fun h : Fin q → RealFn => familyComp h s) ''
        Set.univ.pi (fun l => c1SuppIn σ (A l)) =
      Set.univ.pi (fun l => c1SuppIn σ (s ⁻¹' A l)) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩ l -
    exact comp_mem_c1SuppIn σ hs (hh l (Set.mem_univ l))
  · intro hg
    refine ⟨fun l => g l ∘ hs.toPerm.symm, fun l _ => ?_, ?_⟩
    · have := comp_mem_c1SuppIn σ hs.symm (hg l (Set.mem_univ l))
      rwa [preimage_symm_preimage] at this
    · funext l
      exact comp_symm_comp_motion hs (g l)
theorem admissibleSets_preimage (hs : IsEuclideanMotion s) {q : ℕ} (hq : 1 ≤ q) {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) {A : Fin q → Set (Fin 4 → ℝ)}
    (hA : AdmissibleSets hq d R hd hR A) :
    AdmissibleSets hq d R hd hR (fun l => s ⁻¹' A l) := by
  refine ⟨fun l => ?_, fun l k hlk => ?_⟩
  · obtain ⟨x, hx⟩ := hA.1 l
    refine ⟨hs.toPerm.symm x, fun y hy => ?_⟩
    have h₁ : euclidNormVec (s y - x) ≤ R := hx hy
    have h₂ := motion_dist_eq hs y (hs.toPerm.symm x)
    rw [motion_apply_symm hs] at h₂
    change euclidNormVec (y - hs.toPerm.symm x) ≤ R
    rwa [← h₂]
  · rw [infDist_preimage_motion hs]
    exact hA.2 l k hlk
theorem familyComp_mem_sepTuplesR4 (σ : Conventions.StandingParameters) (hs : IsEuclideanMotion s)
    {n : ℕ} {h : Fin n → RealFn} (hh : h ∈ sepTuplesR4 σ n) :
    familyComp h s ∈ sepTuplesR4 σ n := by
  obtain ⟨h₁, h₂, h₃⟩ := (mem_sepTuplesR4_iff σ h).1 hh
  refine (mem_sepTuplesR4_iff σ _).2 ⟨fun i => (h₁ i).comp (contDiff_of_isEuclideanMotion hs),
    fun i => ?_, fun i k hik => ?_⟩
  · change IsCompact (fnSupport (h i ∘ s))
    rw [fnSupport_comp_motion hs]
    exact isCompact_preimage_motion hs (h₂ i)
  · change Disjoint (fnSupport (h i ∘ s)) (fnSupport (h k ∘ s))
    rw [fnSupport_comp_motion hs, fnSupport_comp_motion hs]
    exact (h₃ i k hik).preimage s
theorem lipschitzR4_of_contDiff {f : RealFn} (h₁ : ContDiff ℝ 1 f)
    (h₂ : IsCompact (fnSupport f)) : LipschitzR4 f := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) h₂ h₁ one_ne_zero
  refine ⟨C, C.2, fun x y => ?_⟩
  have h := hC.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at h
  exact h.trans
    (mul_le_mul_of_nonneg_left (SeparatedTuplesR4.norm_le_euclidNormVec _) C.2)
theorem isSepLipTuple_of_mem (σ : Conventions.StandingParameters) {n : ℕ}
    {h : Fin n → RealFn} (hh : h ∈ sepTuplesR4 σ n) :
    IsSepLipTuple h := by
  obtain ⟨h₁, h₂, h₃⟩ := (mem_sepTuplesR4_iff σ h).1 hh
  exact ⟨fun i => lipschitzR4_of_contDiff (h₁ i) (h₂ i), h₂, h₃⟩
end
abbrev fnGrad (f : RealFn) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ReflectionPositivity.AxisMirror.Ambient.gradR4 f x
theorem vecLength_eq_euclidNormVec (v : Fin 4 → ℝ) : vecLength v = euclidNormVec v := by
  simp [vecLength, euclidNormVec, Real.norm_eq_abs, sq_abs]
theorem partialDerivR4_eq_fderiv {f : RealFn} {x : Fin 4 → ℝ}
    (hf : DifferentiableAt ℝ f x) (μ : Fin 4) :
    TestFunctions.partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ 1) := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.C1Banach.partialDerivR4_eq_fderiv <;> assumption
theorem clm_apply_eq_sum_single (L : (Fin 4 → ℝ) →L[ℝ] ℝ) (y : Fin 4 → ℝ) :
    L y = ∑ ν, y ν * L (Pi.single ν 1) := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusC1Facts.clm_apply_eq_sum_basis <;> assumption
theorem fderiv_apply_eq_sum_fnGrad {g : RealFn} {p : Fin 4 → ℝ}
    (hg : DifferentiableAt ℝ g p) (u : Fin 4 → ℝ) :
    fderiv ℝ g p u = ∑ ν, u ν * fnGrad g p ν := by
  rw [clm_apply_eq_sum_single]
  refine Finset.sum_congr rfl fun ν _ => ?_
  change _ = u ν * TestFunctions.partialDerivR4 ν g p
  rw [partialDerivR4_eq_fderiv hg]
theorem fnGrad_comp_orthoAffine {f : RealFn} (hf : ContDiff ℝ 1 f)
    (S : Matrix (Fin 4) (Fin 4) ℝ) (v x : Fin 4 → ℝ) :
    fnGrad (f ∘ orthoAffine S v) x = Sᵀ *ᵥ fnGrad f (orthoAffine S v x) := by
  have hd : ∀ y, DifferentiableAt ℝ f y := fun y => (hf.differentiable one_ne_zero) y
  have hm : HasFDerivAt (orthoAffine S v)
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin S)) x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin S)).hasFDerivAt.add_const v
  have hc := (hd (orthoAffine S v x)).hasFDerivAt.comp x hm
  funext μ
  have hdc : DifferentiableAt ℝ (f ∘ orthoAffine S v) x := hc.differentiableAt
  change TestFunctions.partialDerivR4 μ (f ∘ orthoAffine S v) x = _
  rw [partialDerivR4_eq_fderiv hdc, hc.fderiv]
  change fderiv ℝ f (orthoAffine S v x) (S *ᵥ Pi.single μ 1) = _
  rw [clm_apply_eq_sum_single]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun ν _ => ?_
  change _ = _ * TestFunctions.partialDerivR4 ν f (orthoAffine S v x)
  rw [partialDerivR4_eq_fderiv (hd _)]
  simp [Pi.single_apply]
theorem transpose_mem_orthogonalGroup {S : Matrix (Fin 4) (Fin 4) ℝ}
    (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ) :
    Sᵀ ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.orth_transpose_mem <;> assumption
theorem fnGrad_sub {g₁ g₂ : RealFn} (h₁ : ContDiff ℝ 1 g₁)
    (h₂ : ContDiff ℝ 1 g₂) (x : Fin 4 → ℝ) :
    fnGrad (g₁ - g₂) x = fnGrad g₁ x - fnGrad g₂ x := by
  have d₁ : DifferentiableAt ℝ g₁ x := (h₁.differentiable one_ne_zero) x
  have d₂ : DifferentiableAt ℝ g₂ x := (h₂.differentiable one_ne_zero) x
  have hs : HasFDerivAt (g₁ - g₂) (fderiv ℝ g₁ x - fderiv ℝ g₂ x) x :=
    d₁.hasFDerivAt.sub d₂.hasFDerivAt
  funext μ
  change TestFunctions.partialDerivR4 μ (g₁ - g₂) x =
    TestFunctions.partialDerivR4 μ g₁ x - TestFunctions.partialDerivR4 μ g₂ x
  rw [partialDerivR4_eq_fderiv hs.differentiableAt, partialDerivR4_eq_fderiv d₁,
    partialDerivR4_eq_fderiv d₂, hs.fderiv]
  rfl
theorem translate_eq_comp_orthoAffine {β : Type*} (a : Fin 4 → ℝ) (h : (Fin 4 → ℝ) → β) :
    (fun x => h (x - a)) = h ∘ orthoAffine 1 (-a) := by
  funext x
  change h (x - a) = h (orthoAffine 1 (-a) x)
  simp [orthoAffine, sub_eq_add_neg]
theorem fnGrad_translate {f : RealFn} (hf : ContDiff ℝ 1 f) (a x : Fin 4 → ℝ) :
    fnGrad (fun y => f (y - a)) x = fnGrad f (x - a) := by
  rw [translate_eq_comp_orthoAffine, fnGrad_comp_orthoAffine hf]
  simp [orthoAffine, sub_eq_add_neg]
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem abs_sum_mul_le_euclidNormVec (u w : Fin 4 → ℝ) :
    |∑ ν, u ν * w ν| ≤ euclidNormVec u * euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.abs_inner_le_euclidNormVec_mul <;> assumption
theorem abs_sub_le_of_fnGrad_le {g : RealFn} (hg : ContDiff ℝ 1 g) {G : ℝ}
    (hG : ∀ x, euclidNormVec (fnGrad g x) ≤ G) (x y : Fin 4 → ℝ) :
    |g x - g y| ≤ G * euclidNormVec (x - y) := by
  have hd : ∀ p, DifferentiableAt ℝ g p := fun p => (hg.differentiable one_ne_zero) p
  obtain ⟨u, hu⟩ : ∃ u, u = x - y := ⟨_, rfl⟩
  rw [← hu]
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => y + t • u) u t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const u).const_add y
  have hφ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => g (y + t • u)) (fderiv ℝ g (y + t • u) u) t :=
    fun t => (hd _).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hb : ∀ t : ℝ, ‖fderiv ℝ g (y + t • u) u‖ ≤ G * euclidNormVec u := fun t => by
    rw [Real.norm_eq_abs, fderiv_apply_eq_sum_fnGrad (hd _)]
    refine (abs_sum_mul_le_euclidNormVec _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hG _) (Real.sqrt_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun t : ℝ => g (y + t • u)) (fun t _ => (hφ t).hasDerivWithinAt) (fun t _ => hb t)
  have e₁ : y + u = x := by simp [hu]
  simpa [e₁, Real.norm_eq_abs] using h
section
variable {D : ReflectionPositivity.AxisMirror.MirrorData} {F G : RealFn}
theorem mem_compactC1_iff (f : RealFn) :
    f ∈ compactC1 D ℝ .euclidean ↔ ContDiff ℝ 1 f ∧ IsCompact (fnSupport f) := by
  rw [← FourSpace.C1c_eq_compactC1 D]
  exact Iff.rfl
theorem comp_motion_mem_compactC1 {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hF : F ∈ compactC1 D ℝ .euclidean) (hs : IsEuclideanMotion s) :
    F ∘ s ∈ compactC1 D ℝ .euclidean := by
  obtain ⟨h₁, h₂⟩ := (mem_compactC1_iff F).1 hF
  refine (mem_compactC1_iff _).2 ⟨h₁.comp (contDiff_of_isEuclideanMotion hs), ?_⟩
  rw [fnSupport_comp_motion hs]
  exact isCompact_preimage_motion hs h₂
theorem contDiff_of_mem_compactC1 (hF : F ∈ compactC1 D ℝ .euclidean) : ContDiff ℝ 1 F :=
  ((mem_compactC1_iff F).1 hF).1
theorem gradSup_comp_motion {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hF : F ∈ compactC1 D ℝ .euclidean) (hG : G ∈ compactC1 D ℝ .euclidean)
    (hs : IsEuclideanMotion s) (e : G = F ∘ s) :
    gradSup (⟨G, hG⟩ : compactC1 D ℝ .euclidean) =
      gradSup (⟨F, hF⟩ : compactC1 D ℝ .euclidean) := by
  have hf := contDiff_of_mem_compactC1 hF
  change (⨆ x : Fin 4 → ℝ, ENNReal.ofReal (vecLength (fnGrad G x))) =
    ⨆ x : Fin 4 → ℝ, ENNReal.ofReal (vecLength (fnGrad F x))
  rw [← hs.bijective.surjective.iSup_comp
    fun x => ENNReal.ofReal (vecLength (fnGrad F x))]
  refine iSup_congr fun x => ?_
  obtain ⟨S, hS, v, rfl⟩ := id hs
  rw [vecLength_eq_euclidNormVec, vecLength_eq_euclidNormVec, e, fnGrad_comp_orthoAffine hf]
  exact congrArg _ (TorusTransport.euclidNorm_mulVec (transpose_mem_orthogonalGroup hS) _)
theorem gradOsc_comp_motion {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hF : F ∈ compactC1 D ℝ .euclidean) (hG : G ∈ compactC1 D ℝ .euclidean)
    (hs : IsEuclideanMotion s) (e : G = F ∘ s) (δ : ℝ≥0) :
    gradOsc (⟨G, hG⟩ : compactC1 D ℝ .euclidean) δ =
      gradOsc (⟨F, hF⟩ : compactC1 D ℝ .euclidean) δ := by
  have hf := contDiff_of_mem_compactC1 hF
  change (⨆ (x : Fin 4 → ℝ) (y : Fin 4 → ℝ) (_ : euclidNormVec (x - y) ≤ δ),
      ENNReal.ofReal (vecLength (fnGrad G x - fnGrad G y))) =
    ⨆ (x : Fin 4 → ℝ) (y : Fin 4 → ℝ) (_ : euclidNormVec (x - y) ≤ δ),
      ENNReal.ofReal (vecLength (fnGrad F x - fnGrad F y))
  rw [← iSup₂_comp_motion hs fun x y => ⨆ _ : euclidNormVec (x - y) ≤ δ,
    ENNReal.ofReal (vecLength (fnGrad F x - fnGrad F y))]
  refine iSup_congr fun x => iSup_congr fun y => ?_
  have e₁ : euclidNormVec (s x - s y) = euclidNormVec (x - y) := motion_dist_eq hs x y
  obtain ⟨S, hS, v, rfl⟩ := id hs
  have e₂ : euclidNormVec (fnGrad G x - fnGrad G y) =
      euclidNormVec (fnGrad F (orthoAffine S v x) - fnGrad F (orthoAffine S v y)) := by
    rw [e, fnGrad_comp_orthoAffine hf, fnGrad_comp_orthoAffine hf, ← Matrix.mulVec_sub]
    exact TorusTransport.euclidNorm_mulVec (transpose_mem_orthogonalGroup hS) _
  rw [e₁, vecLength_eq_euclidNormVec, vecLength_eq_euclidNormVec, e₂]
theorem smoothModulus_comp_motion {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (M : ScaleParam)
    (hF : F ∈ compactC1 D ℝ .euclidean) (hG : G ∈ compactC1 D ℝ .euclidean)
    (hs : IsEuclideanMotion s) (e : G = F ∘ s) :
    smoothModulus M (⟨G, hG⟩ : compactC1 D ℝ .euclidean) =
      smoothModulus M (⟨F, hF⟩ : compactC1 D ℝ .euclidean) := by
  funext δ
  unfold smoothModulus
  rw [gradSup_comp_motion hF hG hs e, gradOsc_comp_motion hF hG hs e]
theorem gradOsc_monotone (f : compactC1 D ℝ .euclidean) :
    Monotone (gradOsc f) := fun _ _ hδ =>
  iSup₂_le fun x y => iSup_le fun h =>
    le_iSup₂_of_le x y (le_iSup_of_le (h.trans (NNReal.coe_le_coe.mpr hδ)) le_rfl)
variable (hT : ReflectionPositivity.AxisMirror.Ambient.SmoothModulusVanishes.Claim)
include hT
theorem gradOsc_lt_top (M : ScaleParam) (f : compactC1 D ℝ .euclidean)
    (δ : ℝ≥0) : gradOsc f δ < ⊤ :=
  ((hT D ℝ .euclidean M f).2.1 δ).1.trans_lt ((hT D ℝ .euclidean M f).2.1 δ).2
theorem smoothModulus_monotone (M : ScaleParam) (f : compactC1 D ℝ .euclidean) :
    Monotone (smoothModulus M f) := fun δ₁ δ₂ hδ => by
  refine max_le_max ?_ ?_
  · exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hδ) ENNReal.toReal_nonneg
  · refine mul_le_mul_of_nonneg_left ?_ ?_
    · exact ENNReal.toReal_mono (gradOsc_lt_top hT M f δ₂).ne
        (gradOsc_monotone f hδ)
    · have := M.2
      have h₁ : (1 : ℝ) ≤ (M : ℝ) := this
      linarith
theorem normSharp_translate_sub_le (M : ScaleParam) (hF : F ∈ compactC1 D ℝ .euclidean)
    (a b : Fin 4 → ℝ) :
    normSharp D M .euclidean ((fun x => F (x - a)) - fun x => F (x - b)) ≤
      smoothModulus M (⟨F, hF⟩ : compactC1 D ℝ .euclidean)
        (euclidNormVec (a - b)).toNNReal := by
  have hc := contDiff_of_mem_compactC1 hF
  obtain ⟨δ, hδd⟩ : ∃ δ, δ = (euclidNormVec (a - b)).toNNReal := ⟨_, rfl⟩
  rw [← hδd]
  have hδ : (δ : ℝ) = euclidNormVec (a - b) := by
    rw [hδd]
    exact Real.coe_toNNReal _ (Real.sqrt_nonneg _)
  have hGfin := (hT D ℝ .euclidean M ⟨F, hF⟩).1
  have hOfin := gradOsc_lt_top hT M ⟨F, hF⟩ δ
  have hgf : ∀ x, euclidNormVec (fnGrad F x) ≤
      (gradSup (⟨F, hF⟩ : compactC1 D ℝ .euclidean)).toReal := fun x => by
    rw [← vecLength_eq_euclidNormVec]
    refine (ENNReal.ofReal_le_iff_le_toReal hGfin.ne).1 ?_
    exact le_iSup (fun x : Fin 4 → ℝ => ENNReal.ofReal (vecLength (fnGrad F x))) x
  have ca : ContDiff ℝ 1 (fun x => F (x - a)) := by
    rw [translate_eq_comp_orthoAffine]
    exact hc.comp (contDiff_orthoAffine _ _)
  have cb : ContDiff ℝ 1 (fun x => F (x - b)) := by
    rw [translate_eq_comp_orthoAffine]
    exact hc.comp (contDiff_orthoAffine _ _)
  have hgg : ∀ x, euclidNormVec (fnGrad ((fun x => F (x - a)) - fun x => F (x - b)) x) ≤
      (gradOsc (⟨F, hF⟩ : compactC1 D ℝ .euclidean) δ).toReal := fun x => by
    rw [fnGrad_sub ca cb, fnGrad_translate hc, fnGrad_translate hc, ← vecLength_eq_euclidNormVec]
    refine (ENNReal.ofReal_le_iff_le_toReal hOfin.ne).1 ?_
    have hxy : euclidNormVec ((x - a) - (x - b)) ≤ δ := by
      have e : (x - a) - (x - b) = -(a - b) := by abel
      rw [e, hδ, euclidNormVec_neg]
    exact le_iSup₂_of_le (f := fun (u v : Fin 4 → ℝ) => ⨆ _ : euclidNormVec (u - v) ≤ δ,
      ENNReal.ofReal (vecLength (fnGrad F u - fnGrad F v))) (x - a) (x - b)
      (le_iSup_of_le hxy le_rfl)
  refine max_le_max ?_ (mul_le_mul_of_nonneg_left ?_ ?_)
  · refine ciSup_le fun x => ?_
    have h₁ := abs_sub_le_of_fnGrad_le hc hgf (x - a) (x - b)
    have e : (x - a) - (x - b) = -(a - b) := by abel
    rw [e, euclidNormVec_neg, ← hδ] at h₁
    exact h₁
  · refine csInf_le ⟨0, fun C hC => hC.1⟩ ⟨ENNReal.toReal_nonneg, fun x y => ?_⟩
    exact abs_sub_le_of_fnGrad_le (ca.sub cb) hgg x y
  · have h₁ : (1 : ℝ) ≤ (M : ℝ) := M.2
    linarith
end
theorem basisVec_self (μ : Fin 4) : basisVec μ μ = 1 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.basisVector_apply_self <;> assumption
theorem basisVec_of_ne {μ ν : Fin 4} (h : ν ≠ μ) : basisVec μ ν = 0 := by
  simp [basisVec, PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
theorem hyperplaneReflect_eq_add_smul (μ : Fin 4) (c c' : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflect μ c' x = hyperplaneReflect μ c x + (2 * (c' - c)) • basisVec μ := by
  simp only [hyperplaneReflect]
  rw [add_assoc, ← add_smul]
  congr 2
  ring
theorem hyperplaneReflect_sub_smul (μ : Fin 4) (c t : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflect μ c (x - t • basisVec μ) = hyperplaneReflect μ c x + t • basisVec μ := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      TorusTransport.hyperplaneReflect_apply_self, basisVec_self]
    ring
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      TorusTransport.hyperplaneReflect_apply_of_ne h, basisVec_of_ne h]
    ring
theorem hyperplaneReflect_hyperplaneReflect (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflect μ c (hyperplaneReflect μ c x) = x := by
  funext ν
  by_cases h : ν = μ
  · subst h
    rw [TorusTransport.hyperplaneReflect_apply_self, TorusTransport.hyperplaneReflect_apply_self]
    ring
  · rw [TorusTransport.hyperplaneReflect_apply_of_ne h,
      TorusTransport.hyperplaneReflect_apply_of_ne h]
theorem comp_hyperplaneReflect_eq_translate {β : Type*} (μ : Fin 4) (c c' : ℝ)
    (h : (Fin 4 → ℝ) → β) :
    h ∘ hyperplaneReflect μ c' =
      fun x => (h ∘ hyperplaneReflect μ c) (x - (2 * (c' - c)) • basisVec μ) := by
  funext x
  change h (hyperplaneReflect μ c' x) =
    h (hyperplaneReflect μ c (x - (2 * (c' - c)) • basisVec μ))
  rw [hyperplaneReflect_sub_smul, hyperplaneReflect_eq_add_smul μ c c']
theorem euclidNormVec_smul_basisVec (t : ℝ) (μ : Fin 4) :
    euclidNormVec (t • basisVec μ) = |t| := by apply _root_.YangMills.Construction.LimitSpaces.MirrorTranslation.euclidNormVec_smul_stdBasisVec <;> assumption
theorem parallelReflectTranslate_holds (D : ReflectionPositivity.AxisMirror.MirrorData)
    (M : ScaleParam) (μ : Fin 4) (c c' : ℝ) : ParallelReflectTranslate D M μ c c' := by
  intro Z _ h
  refine ⟨comp_hyperplaneReflect_eq_translate μ c c' h, ?_⟩
  rw [fnSupport_comp_motion (isEuclideanMotion_hyperplaneReflect μ c')]
  ext y
  constructor
  · intro hy
    refine ⟨_, ⟨hyperplaneReflect μ c' y, hy, rfl⟩, ?_⟩
    change hyperplaneReflect μ c (hyperplaneReflect μ c' y) + _ = y
    rw [← hyperplaneReflect_eq_add_smul, hyperplaneReflect_hyperplaneReflect]
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    change hyperplaneReflect μ c k + (2 * (c' - c)) • basisVec μ ∈
      hyperplaneReflect μ c' ⁻¹' fnSupport h
    rw [← hyperplaneReflect_eq_add_smul]
    change hyperplaneReflect μ c' (hyperplaneReflect μ c' k) ∈ fnSupport h
    rwa [hyperplaneReflect_hyperplaneReflect]
theorem normSharp_parallel_reflect_sub_le {D : ReflectionPositivity.AxisMirror.MirrorData}
    (hT : ReflectionPositivity.AxisMirror.Ambient.SmoothModulusVanishes.Claim) (M : ScaleParam)
    {F : RealFn} (hF : F ∈ compactC1 D ℝ .euclidean) (μ : Fin 4) (c c' : ℝ) :
    normSharp D M .euclidean (F ∘ hyperplaneReflect μ c' - F ∘ hyperplaneReflect μ c) ≤
      smoothModulus M (⟨F, hF⟩ : compactC1 D ℝ .euclidean) (2 * |c' - c|).toNNReal := by
  have hr := isEuclideanMotion_hyperplaneReflect μ c
  have hG := comp_motion_mem_compactC1 hF hr
  have hb := normSharp_translate_sub_le hT M hG ((2 * (c' - c)) • basisVec μ) 0
  have e : (fun x => (F ∘ hyperplaneReflect μ c) (x - (2 * (c' - c)) • basisVec μ)) -
      (fun x => (F ∘ hyperplaneReflect μ c) (x - 0)) =
        F ∘ hyperplaneReflect μ c' - F ∘ hyperplaneReflect μ c := by
    have e₀ : (fun x => (F ∘ hyperplaneReflect μ c) (x - 0)) = F ∘ hyperplaneReflect μ c := by
      funext x
      rw [sub_zero]
    rw [← comp_hyperplaneReflect_eq_translate, e₀]
  rw [e, smoothModulus_comp_motion M hF hG hr rfl, sub_zero, euclidNormVec_smul_basisVec,
    abs_mul, abs_two] at hb
  exact hb
theorem swapWithTime_apply (μ ν : Fin 4) (x : Fin 4 → ℝ) :
    swapWithTime μ x ν = x (Equiv.swap μ 3 ν) :=
  rfl
theorem toTimeMirrorMotion_apply (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) (ν : Fin 4) :
    toTimeMirrorMotion μ c x ν = (x - c • basisVec μ) (Equiv.swap μ 3 ν) :=
  rfl
theorem toTimeMirrorMotion_apply_three (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    toTimeMirrorMotion μ c x 3 = x μ - c := by
  rw [toTimeMirrorMotion_apply, Equiv.swap_apply_right]
  simp [basisVec_self]
theorem toTimeMirrorMotion_comp_hyperplaneReflect (μ : Fin 4) (c : ℝ) :
    toTimeMirrorMotion μ c ∘ hyperplaneReflect μ c = timeReflect ∘ toTimeMirrorMotion μ c := by
  funext x ν
  simp only [Function.comp]
  by_cases h : ν = 3
  · subst h
    have e : timeReflect (toTimeMirrorMotion μ c x) 3 = 2 * 0 - toTimeMirrorMotion μ c x 3 :=
      TorusTransport.hyperplaneReflect_apply_self 3 0 _
    rw [e, toTimeMirrorMotion_apply_three, toTimeMirrorMotion_apply_three,
      TorusTransport.hyperplaneReflect_apply_self]
    ring
  · have e : timeReflect (toTimeMirrorMotion μ c x) ν = toTimeMirrorMotion μ c x ν :=
      TorusTransport.hyperplaneReflect_apply_of_ne h 0 _
    rw [e, toTimeMirrorMotion_apply, toTimeMirrorMotion_apply]
    have hne : Equiv.swap μ 3 ν ≠ μ := fun h' => h (by
      have := congrArg (Equiv.swap μ 3) h'
      simpa using this)
    simp only [Pi.sub_apply, TorusTransport.hyperplaneReflect_apply_of_ne hne]
theorem conjugatesToTimeReflect_holds (μ : Fin 4) (c : ℝ) :
    ConjugatesToTimeReflect μ c := by
  refine ⟨⟨Equiv.swap μ 3, 1, Equiv.ext fun x => funext fun ν => ?_⟩,
    ⟨Equiv.swap μ 3, 1, -(swapWithTime μ (c • basisVec μ)), fun x => funext fun ν => ?_⟩,
    ?_, toTimeMirrorMotion_comp_hyperplaneReflect μ c, ?_⟩
  · rw [TorusTransport.signedCoordinateEquiv_apply, swapWithTime_apply]
    simp
  · rw [toTimeMirrorMotion_apply]
    simp [PeriodicLattice.CutoffTorus.signedPermEuclidean, swapWithTime_apply, sub_eq_add_neg]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : c < x μ := hx
      change 0 < toTimeMirrorMotion μ c x 3
      rw [toTimeMirrorMotion_apply_three]
      linarith
    · intro hy
      have hy' : 0 < y 3 := hy
      refine ⟨(toTimeMirrorMotion μ c).symm y, ?_, Equiv.apply_symm_apply _ y⟩
      have h := toTimeMirrorMotion_apply_three μ c ((toTimeMirrorMotion μ c).symm y)
      rw [Equiv.apply_symm_apply] at h
      change c < (toTimeMirrorMotion μ c).symm y μ
      linarith
  · funext y
    apply (toTimeMirrorMotion μ c).injective
    have h := congrFun (toTimeMirrorMotion_comp_hyperplaneReflect μ c)
      ((toTimeMirrorMotion μ c).symm y)
    simp only [Function.comp, Equiv.apply_symm_apply] at h ⊢
    exact h
theorem orthoAffineIsIsometry_holds (D : ReflectionPositivity.AxisMirror.MirrorData)
    {S : Matrix (Fin 4) (Fin 4) ℝ} (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    OrthoAffineIsIsometry D S v :=
  ⟨(TorusTransport.isEuclideanMotion_orthoAffine hS v).toPerm, rfl,
    GrowingTori.isDistIsometry_toPerm D.toStandingParameters _⟩
theorem orthoAffinePreservesLipschitz_holds (D : ReflectionPositivity.AxisMirror.MirrorData)
    (M : ScaleParam) {S : Matrix (Fin 4) (Fin 4) ℝ} (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ)
    (v : Fin 4 → ℝ) : OrthoAffinePreservesLipschitz D M S v := by
  have hs := TorusTransport.isEuclideanMotion_orthoAffine hS v
  intro h _ _
  exact ⟨fnSupport_comp_motion hs h, uniformNorm_comp_motion hs h, lipConst_comp_motion hs h,
    normSharp_comp_motion D M hs h, fun hc => hc.comp (contDiff_of_isEuclideanMotion hs),
    fun hc => hc.comp (contDiff_of_isEuclideanMotion hs)⟩
theorem orthoAffinePreservesAdmissible_holds (D : ReflectionPositivity.AxisMirror.MirrorData)
    {S : Matrix (Fin 4) (Fin 4) ℝ} (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    OrthoAffinePreservesAdmissible D S v := by
  have hs := TorusTransport.isEuclideanMotion_orthoAffine hS v
  intro q hq d R hd hR A hA
  exact ⟨admissibleSets_preimage hs hq hd hR hA,
    image_familyComp_pi_c1SuppIn D.toStandingParameters hs A⟩
theorem orthoAffinePreservesSepTuples_holds (D : ReflectionPositivity.AxisMirror.MirrorData)
    {S : Matrix (Fin 4) (Fin 4) ℝ} (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    OrthoAffinePreservesSepTuples D S v := by
  have hs := TorusTransport.isEuclideanMotion_orthoAffine hS v
  refine ⟨fun n => ?_, fun n hn h hh => ?_⟩
  · ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact familyComp_mem_sepTuplesR4 _ hs hh
    · intro hg
      refine ⟨familyComp g hs.toPerm.symm, familyComp_mem_sepTuplesR4 _ hs.symm hg, ?_⟩
      funext i
      exact comp_symm_comp_motion hs (g i)
  · refine ⟨isSepLipTuple_of_mem _ hh,
      isSepLipTuple_of_mem _ (familyComp_mem_sepTuplesR4 _ hs hh), ?_⟩
    refine iInf_congr fun i => iInf_congr fun k => iInf_congr fun _ => ?_
    change infDist (fnSupport (h i ∘ orthoAffine S v)) (fnSupport (h k ∘ orthoAffine S v)) = _
    rw [fnSupport_comp_motion hs, fnSupport_comp_motion hs, infDist_preimage_motion hs]
theorem statement_of_smoothModulusVanishes
    (hT : ReflectionPositivity.AxisMirror.Ambient.SmoothModulusVanishes.Claim) : Statement := by
  intro D M
  refine ⟨fun f => ⟨⟨smoothModulus_monotone hT M f, ?_⟩, ⟨fun a b => ?_, fun δ => rfl⟩,
      fun S hS v => ?_, fun μ c c' => ?_⟩,
    fun s hs => ?_,
    fun S hS v => ⟨orthoAffineIsIsometry_holds D hS v, orthoAffinePreservesLipschitz_holds D M hS v,
      orthoAffinePreservesAdmissible_holds D hS v, orthoAffinePreservesSepTuples_holds D hS v⟩,
    parallelReflectTranslate_holds D M, conjugatesToTimeReflect_holds⟩
  · exact (hT D ℝ .euclidean M f).2.2.2.mono_left nhdsWithin_le_nhds
  · exact normSharp_translate_sub_le hT M f.2 a b
  · have hs := TorusTransport.isEuclideanMotion_orthoAffine hS v
    exact ⟨comp_motion_mem_compactC1 f.2 hs,
      smoothModulus_comp_motion M f.2 (comp_motion_mem_compactC1 f.2 hs) hs rfl⟩
  · exact normSharp_parallel_reflect_sub_le hT M f.2 μ c c'
  · exact isEuclideanMotion_of_mem_affineHyperoctahedral
      ((GrowingTori.mem_euclideanMotions_iff_mem_affineHyperoctahedral s).1 hs)
end YangMills.Construction.ToriLimits.EuclideanSymmetryFacts
end
