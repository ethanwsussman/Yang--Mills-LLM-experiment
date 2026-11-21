import YangMills.Construction.EuclideanFunctionals.RulesOfMotionsConcatenationAndComplexEntriesProof
import YangMills.Construction.EuclideanFunctionals.SupportsIsometriesAndConcatenationProof
import YangMills.Construction.ComplexAnalysis.HolomorphicAndRealAnalyticFacts
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.EuclideanFunctionals.CalculusOfEnergyAndMomentumInMatrixElementsProof
import YangMills.Construction.EuclideanFunctionals.ConeConditionOfAReconstructionInThreeFormsAndTheCalculusOverThePyramid
import YangMills.Construction.EuclideanFunctionals.TuplesAboveAHeightTheRestrictionsAgreeProof
import YangMills.Construction.EuclideanFunctionals.TuplesSpansAndActionsProof
import YangMills.Construction.RotationInvariance.AnalyticityAlongTangentialMoves
import YangMills.Construction.RotationInvariance.MomentsAndConnectedFunctionsUnderAnOrthogonalMap
import YangMills.Construction.RotationInvariance.WhatAnOrthogonalMapPreserves
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror RealPlane
namespace EuclideanFunctionals.TangentialAnalyticity
theorem supp_eq_tsupport {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) : supp f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem continuous_motion (r : EuclidMotion) : Continuous fun x : R4 => r x :=
  (LinearMap.continuous_of_finiteDimensional r.lin).add continuous_const
def motionHomeomorph (r : EuclidMotion) : R4 ≃ₜ R4 where
  toEquiv := r.toPerm
  continuous_toFun := continuous_motion r
  continuous_invFun := continuous_motion r⁻¹
theorem supp_actFn {𝕜 : Type*} [RCLike 𝕜] (r : EuclidMotion) (f : R4 → 𝕜) :
    supp (r.actFn f) = (fun x => r x) '' supp f := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionMulRules.supp_actFn <;> assumption
theorem actFn_mem_C1c {𝕜 : Type*} [RCLike 𝕜] (r : EuclidMotion) {f : R4 → 𝕜}
    (hf : f ∈ C1c 𝕜) : r.actFn f ∈ C1c 𝕜 := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionProofs.actFn_mem_C1c <;> assumption
theorem actList_mem_sepIn (r : EuclidMotion) {O : Set R4} {X : FnList}
    (hX : X ∈ sepIn O) : r.actList X ∈ sepIn ((fun x => r x) '' O) := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionProofs.actList_mem_sepIn <;> assumption
theorem actFree_toFree (r : EuclidMotion) {X : FnList} (hX : X ∈ sepAll) :
    r.actFree (toFree X) = toFree (r.actList X) :=
  liftLin_toFree _ ⟨X, hX⟩
theorem actFree_mem_finCombIn (r : EuclidMotion) {O : Set R4} {F : FreeSep}
    (hF : F ∈ finCombIn O) : r.actFree F ∈ finCombIn ((fun x => r x) '' O) := by
  rw [finCombIn_eq_freeSpanIn] at hF ⊢
  have hle : freeSpanIn O ≤ (freeSpanIn ((fun x => r x) '' O)).comap r.actFree := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨X, hX, rfl⟩
    refine Submodule.mem_comap.2 ?_
    rw [actFree_toFree r hX.1]
    exact Submodule.subset_span ⟨_, actList_mem_sepIn r hX, rfl⟩
  exact hle hF
theorem finCombIn_mono {O O' : Set R4} (h : O ⊆ O') :
    finCombIn O ≤ finCombIn O' := by apply _root_.YangMills.Construction.EuclideanFunctionals.HeightTuples.finCombIn_mono <;> assumption
theorem actFn_mul {α : Type*} (r r' : EuclidMotion) (f : R4 → α) :
    (r * r').actFn f = r.actFn (r'.actFn f) := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionProofs.actFn_mul <;> assumption
theorem actFree_actFree (r r' : EuclidMotion) (F : FreeSep) :
    r.actFree (r'.actFree F) = (r * r').actFree F := by
  have h : r.actFree ∘ₗ r'.actFree = (r * r').actFree := by
    refine freeBasis.ext fun X => ?_
    rw [freeBasis_apply, LinearMap.comp_apply, actFree_toFree r' X.2, actFree_toFree _ X.2]
    have hX := (actList_mem_sepIn r' (O := Set.univ)
      ⟨X.2, fun _ _ => Set.subset_univ _⟩).1
    rw [actFree_toFree r hX]
    congr 1
    simp only [EuclidMotion.actList, List.map_map]
    exact List.map_congr_left fun f _ => (actFn_mul r r' f).symm
  exact LinearMap.congr_fun h F
theorem actFree_one (F : FreeSep) : (1 : EuclidMotion).actFree F = F := by apply _root_.YangMills.Construction.EuclideanFunctionals.one_actFree <;> assumption
theorem transl_mul_transl (a b : R4) :
    EuclidMotion.transl a * EuclidMotion.transl b = EuclidMotion.transl (a + b) :=
  EuclidMotion.ext_of_apply fun x => by
    rw [EuclidMotion.mul_apply, EuclidMotion.transl_apply, EuclidMotion.transl_apply,
      EuclidMotion.transl_apply]
    abel
theorem freeConj_mem_finCombIn {O : Set R4} {F : FreeSep} (hF : F ∈ finCombIn O) :
    freeConj F ∈ finCombIn O := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionMulRules.freeConj_mem_finCombIn <;> assumption
theorem freeConj_freeConj (F : FreeSep) : freeConj (freeConj F) = F := by
  ext X
  simp [freeConj]
def timeFlipMatrix : Matrix.orthogonalGroup (Fin 4) ℝ :=
  ⟨Matrix.diagonal ![1, 1, 1, -1], by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.mul_apply]⟩
theorem timeFlip_eq_ofOrthogonalMatrix : timeFlip = EuclidMotion.ofOrthogonalMatrix timeFlipMatrix :=
  EuclidMotion.ext_of_apply fun x => by
    rw [EuclidMotion.ofOrthogonalMatrix_apply, timeFlip_apply]
    funext i
    fin_cases i <;>
      simp [timeFlipMatrix, Matrix.mulVec_diagonal, PeriodicLattice.coordVec] <;> ring
theorem timeFlip_mul_self : timeFlip * timeFlip = 1 := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionProofs.timeFlip_mul_self <;> assumption
def swapMatrix (μ ν : Fin 4) : Matrix.orthogonalGroup (Fin 4) ℝ :=
  ⟨(Equiv.swap μ ν).permMatrix ℝ, by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩
theorem swapMotion_apply (μ ν : Fin 4) (x : R4) (i : Fin 4) :
    EuclidMotion.ofOrthogonalMatrix (swapMatrix μ ν) x i = x (Equiv.swap μ ν i) := by
  rw [EuclidMotion.ofOrthogonalMatrix_apply]
  simp [swapMatrix, Matrix.permMatrix_mulVec]
theorem swapMotion_mem_hyperoctahedral (μ ν : Fin 4) :
    EuclidMotion.ofOrthogonalMatrix (swapMatrix μ ν) ∈ hyperoctahedral := by
  refine ⟨(Equiv.swap μ ν, fun _ => 1), EuclidMotion.ext_of_apply fun x => ?_⟩
  rw [ofSignedFrame_apply]
  funext i
  rw [swapMotion_apply]
  simp [PeriodicLattice.SignedFrame.actOnVector]
theorem toFree_mem_finCombIn {O : Set R4} {X : FnList} (hX : X ∈ sepIn O) :
    toFree X ∈ finCombIn O := by apply _root_.YangMills.Construction.EuclideanFunctionals.TupleRules.toFree_mem_finCombIn <;> assumption
theorem ofFn_mem_sepIn {O : Set R4} {k : ℕ} (h : Fin k → R4 → ℂ)
    (hh : h ∈ disjointComplexTuples k) (hO : ∀ l, supp (h l) ⊆ O) (g : Fin k → R4 → ℝ)
    (hg : ∀ l, g l ∈ C1c ℝ) (hs : ∀ l, supp (g l) ⊆ supp (h l)) :
    List.ofFn g ∈ sepIn O := by
  refine ⟨Set.mem_iUnion.2 ⟨k, List.length_ofFn, ?_, ?_⟩, ?_⟩
  · intro f hf
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact hg l
  · refine List.pairwise_ofFn.2 fun i j hij => ?_
    exact (hh.2 hij.ne).mono (hs i) (hs j)
  · intro f hf
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact (hs l).trans (hO l)
theorem complexTuple_mem_finCombIn (hSharp : SharpNormC1.Main)
    (m : SharpScale) {O : Set R4} {k : ℕ} (h : Fin k → R4 → ℂ)
    (hh : h ∈ disjointComplexTuples k) (hO : ∀ l, supp (h l) ⊆ O) :
    complexTuple h ∈ finCombIn O := by
  have hp := fun l => (hSharp.2 m).2.1 (h l) (hh.1 l)
  unfold complexTuple
  split_ifs with hr
  · refine toFree_mem_finCombIn (ofFn_mem_sepIn h hh hO _ (fun l => (hp l).1) ?_)
    exact fun l => Set.subset_union_left.trans (hp l).2.2.1
  · refine Submodule.sum_mem _ fun ε _ => Submodule.smul_mem _ _ ?_
    refine toFree_mem_finCombIn (ofFn_mem_sepIn h hh hO _ (fun l => ?_) fun l => ?_)
    · by_cases he : ε l = 0
      · simpa [reOrImPart, he] using (hp l).1
      · simpa [reOrImPart, he] using (hp l).2.1
    · by_cases he : ε l = 0
      · simpa [reOrImPart, he] using Set.subset_union_left.trans (hp l).2.2.1
      · simpa [reOrImPart, he] using Set.subset_union_right.trans (hp l).2.2.1
section Pyramid
open MeasureTheory BorelSpectral SpectralPoint
def pyramidExpKernel (T : ℝ) (q : Fin 3 → ℝ) (z : ℂ) (p : EMPoints) : ℂ :=
  Set.indicator SpectralPoint.pyramid.1
    (fun p => Complex.exp (-(T : ℂ) * (SpectralPoint.energyOf p : ℂ) + Complex.I * (z * (SpectralPoint.dot3 q (SpectralPoint.momentumOf p) : ℂ)))) p
theorem norm_pyramidExpKernel_le {T : ℝ} {q : Fin 3 → ℝ} {z : ℂ}
    (hz : |z.im| * ∑ j, |q j| < T) (p : EMPoints) : ‖pyramidExpKernel T q z p‖ ≤ 1 := by
  unfold pyramidExpKernel
  by_cases hp : p ∈ SpectralPoint.pyramid.1
  · rw [Set.indicator_of_mem hp, Complex.norm_exp, Real.exp_le_one_iff]
    have hE : 0 ≤ SpectralPoint.energyOf p := (abs_nonneg _).trans (hp 0)
    have hD : |SpectralPoint.dot3 q (SpectralPoint.momentumOf p)| ≤ (∑ j, |q j|) * SpectralPoint.energyOf p := by
      unfold SpectralPoint.dot3
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hp j) (abs_nonneg _)
    have hre : (-(T : ℂ) * (SpectralPoint.energyOf p : ℂ) + Complex.I * (z * (SpectralPoint.dot3 q (SpectralPoint.momentumOf p) : ℂ))).re =
        -T * SpectralPoint.energyOf p - z.im * SpectralPoint.dot3 q (SpectralPoint.momentumOf p) := by
      simp
      ring
    rw [hre]
    have h1 : -(z.im * SpectralPoint.dot3 q (SpectralPoint.momentumOf p)) ≤ |z.im| * |SpectralPoint.dot3 q (SpectralPoint.momentumOf p)| := by
      rw [← abs_mul]
      exact neg_le_abs _
    have h2 : |z.im| * |SpectralPoint.dot3 q (SpectralPoint.momentumOf p)| ≤ |z.im| * ((∑ j, |q j|) * SpectralPoint.energyOf p) :=
      mul_le_mul_of_nonneg_left hD (abs_nonneg _)
    have h3 : |z.im| * (∑ j, |q j|) * SpectralPoint.energyOf p ≤ T * SpectralPoint.energyOf p :=
      mul_le_mul_of_nonneg_right hz.le hE
    nlinarith
  · rw [Set.indicator_of_notMem hp]
    simp
theorem measurable_pyramidExpKernel (T : ℝ) (q : Fin 3 → ℝ) (O : Set ℂ) :
    Measurable fun p : O × EMPoints => pyramidExpKernel T q p.1 p.2 := by
  have hm : Measurable fun p : O × EMPoints =>
      Complex.exp (-(T : ℂ) * (SpectralPoint.energyOf p.2 : ℂ) +
        Complex.I * ((p.1 : ℂ) * (SpectralPoint.dot3 q (SpectralPoint.momentumOf p.2) : ℂ))) := by
    refine Complex.measurable_exp.comp (Measurable.add ?_ ?_)
    · exact measurable_const.mul (Complex.measurable_ofReal.comp (SpectralPoint.measurable_energyOf.comp measurable_snd))
    · refine measurable_const.mul (Measurable.mul ?_ ?_)
      · exact measurable_subtype_coe.comp measurable_fst
      · exact Complex.measurable_ofReal.comp ((SpectralPoint.measurable_dot3_momentumOf q).comp measurable_snd)
  have hs : MeasurableSet {p : O × EMPoints | p.2 ∈ SpectralPoint.pyramid.1} := measurable_snd SpectralPoint.pyramid.2
  have he : (fun p : O × EMPoints => pyramidExpKernel T q p.1 p.2) =
      Set.indicator {p : O × EMPoints | p.2 ∈ SpectralPoint.pyramid.1} fun p =>
        Complex.exp (-(T : ℂ) * (SpectralPoint.energyOf p.2 : ℂ) +
          Complex.I * ((p.1 : ℂ) * (SpectralPoint.dot3 q (SpectralPoint.momentumOf p.2) : ℂ))) := by
    funext p
    by_cases hp : p.2 ∈ SpectralPoint.pyramid.1
    · rw [Set.indicator_of_mem (show p ∈ {p : O × EMPoints | p.2 ∈ SpectralPoint.pyramid.1} from hp)]
      exact Set.indicator_of_mem hp _
    · rw [Set.indicator_of_notMem (show p ∉ {p : O × EMPoints | p.2 ∈ SpectralPoint.pyramid.1} from hp)]
      exact Set.indicator_of_notMem hp _
  rw [he]
  exact hm.indicator hs
theorem differentiable_pyramidExpKernel (T : ℝ) (q : Fin 3 → ℝ) (p : EMPoints) :
    Differentiable ℂ fun z => pyramidExpKernel T q z p := by
  unfold pyramidExpKernel
  by_cases hp : p ∈ SpectralPoint.pyramid.1
  · simp only [Set.indicator_of_mem hp]
    fun_prop
  · simp only [Set.indicator_of_notMem hp]
    exact differentiable_const _
theorem isOpen_stripOf (δ s : ℝ) : IsOpen (stripOf δ s) :=
  isOpen_lt ((continuous_abs.comp Complex.continuous_im).mul continuous_const) continuous_const
theorem zeroExtend_kernel_eq {T : ℝ} {q : Fin 3 → ℝ} (r : ℝ) {p : EMPoints}
    (hp : p ∈ SpectralPoint.pyramid.1) :
    zeroExtend SpectralPoint.nonnegEnergy.1 (laplaceFourierKernel T (spatialEmbed (r • q))) p =
      pyramidExpKernel T q r p := by
  have hE : p ∈ SpectralPoint.nonnegEnergy.1 := (abs_nonneg _).trans (hp 0)
  unfold pyramidExpKernel
  rw [Set.indicator_of_mem hp]
  simp only [zeroExtend, dif_pos hE, laplaceFourierKernel, dotR4_spatialEmbed]
  congr 2
  have : SpectralPoint.dot3 (r • q) (SpectralPoint.momentumOf p) = r * SpectralPoint.dot3 q (SpectralPoint.momentumOf p) := by
    simp [SpectralPoint.dot3, Finset.mul_sum, mul_assoc]
  rw [this]
  push_cast
  rfl
theorem measurable_zeroExtend_kernel (T : ℝ) (v : R4) :
    Measurable (zeroExtend SpectralPoint.nonnegEnergy.1 (laplaceFourierKernel T v)) := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.measurable_zeroExtend_kernel <;> assumption
theorem norm_zeroExtend_kernel_le {T : ℝ} (hT : 0 ≤ T) (q : Fin 3 → ℝ) (p : EMPoints) :
    ‖zeroExtend SpectralPoint.nonnegEnergy.1 (laplaceFourierKernel T (spatialEmbed q)) p‖ ≤ 1 := by
  by_cases hE : p ∈ SpectralPoint.nonnegEnergy.1
  · simp only [zeroExtend, dif_pos hE, laplaceFourierKernel]
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hE' : 0 ≤ SpectralPoint.energyOf p := hE
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith
  · simp [zeroExtend, dif_neg hE]
variable {c : SharpScale} {S : ConnFamily}
theorem spectralMeasureAt_compl_pyramid (σ : EuclidFunctionalWithRecon c S)
    (hc : σ.jointMeasure.IsCarriedBy SpectralPoint.pyramid) (ψ : σ.space) :
    σ.spectralMeasureAt ψ SpectralPoint.pyramid.1ᶜ = 0 := by
  have h := σ.jointMeasure.diagMeasure_apply ψ ⟨SpectralPoint.pyramid.1ᶜ, SpectralPoint.pyramid.2.compl⟩
  have h0 : σ.jointMeasure.toFun ⟨SpectralPoint.pyramid.1ᶜ, SpectralPoint.pyramid.2.compl⟩ = 0 := hc
  rw [h0] at h
  simpa [EuclidFunctionalWithRecon.spectralMeasureAt] using h
theorem exists_holomorphic_extension
    (hCalc : HamMomMatrixCalculus)
    (hOne : ComplexAnalysis.HolomorphicAndRealAnalyticFacts)
    (σ : EuclidFunctionalWithRecon c S)
    (hc : σ.jointMeasure.IsCarriedBy SpectralPoint.pyramid) (φ ψ : σ.space) (δ : ℝ) (hδ : 0 < δ)
    (q : Fin 3 → ℝ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (stripOf δ (∑ j, |q j|)) ∧ ∀ r : ℝ,
      G r = BorelComplexMeasures.integralOf (σ.pairSpectralMeasure φ ψ)
        (zeroExtend SpectralPoint.nonnegEnergy.1
          (laplaceFourierKernel (δ + δ) (spatialEmbed (r • q)))) := by
  obtain ⟨-, hcomb, -⟩ := hCalc c S σ φ ψ
  obtain ⟨-, hfin, hint, -, -⟩ := hcomb
  set T : ℝ := δ + δ with hT
  refine ⟨fun z => (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4, (Complex.I ^ k)⁻¹ *
    ∫ p, pyramidExpKernel T q z p ∂σ.spectralMeasureAt (φ + Complex.I ^ k • ψ), ?_, fun r => ?_⟩
  · refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.fun_sum fun k hk => DifferentiableOn.const_mul ?_ _
    have := hfin k hk
    refine hOne.1 (↥EMPoints) _ (stripOf δ (∑ j, |q j|)) (pyramidExpKernel T q) (isOpen_stripOf _ _)
      ⟨1, fun z hz p => norm_pyramidExpKernel_le ?_ p⟩ (measurable_pyramidExpKernel T q _)
      fun p => (differentiable_pyramidExpKernel T q p).differentiableOn
    have hz' : |z.im| * ∑ j, |q j| < 2 * δ := hz
    rw [hT]
    linarith
  · rw [hint _ (measurable_zeroExtend_kernel _ _)
      ⟨1, norm_zeroExtend_kernel_le (by positivity) _⟩]
    beta_reduce
    refine congrArg ((1 / 4 : ℂ) * ·) (Finset.sum_congr rfl fun k _ =>
      congrArg ((Complex.I ^ k)⁻¹ * ·) ?_)
    refine integral_congr_ae ?_
    have hnull := spectralMeasureAt_compl_pyramid σ hc (φ + Complex.I ^ k • ψ)
    have hae : ∀ᵐ p ∂σ.spectralMeasureAt (φ + Complex.I ^ k • ψ), p ∈ SpectralPoint.pyramid.1 :=
      measure_eq_zero_iff_ae_notMem.1 hnull |>.mono fun p hp => by simpa using hp
    filter_upwards [hae] with p hp
    exact (zeroExtend_kernel_eq r hp).symm
end Pyramid
section MatrixElement
variable {c : SharpScale} {S : ConnFamily}
theorem spatialEmbed_mem_spatialVecs (v : Fin 3 → ℝ) : SpectralPoint.spatialEmbed v ∈ spatialVecs := by apply _root_.YangMills.Construction.EuclideanFunctionals.HamMomMatrixCalculusProof.spatialEmbed_mem_spatialVecs <;> assumption
open BorelSpectral
theorem transl_apply_three (v x : R4) :
    EuclidMotion.transl v x 3 = x 3 + v 3 := by
  rw [EuclidMotion.transl_apply]
  rfl
theorem actFree_transl_neg_cancel (t : ℝ) (F : FreeSep) :
    (EuclidMotion.transl (t • timeVec)).actFree ((EuclidMotion.transl ((-t) • timeVec)).actFree F) = F := by
  rw [actFree_actFree, transl_mul_transl, neg_smul, add_neg_cancel]
  have h1 : EuclidMotion.transl 0 = 1 :=
    EuclidMotion.ext_of_apply fun x => by
      rw [EuclidMotion.transl_apply, EuclidMotion.one_apply, add_zero]
  rw [h1, actFree_one]
theorem classOrZero_of_mem {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (cl : finCombIn upperHalf →ₗ[ℂ] ℋ) {F : FreeSep}
    (hF : F ∈ finCombIn upperHalf) : readClass cl F = cl ⟨F, hF⟩ := by
  simp [readClass, hF]
theorem cls_eq_heatSemigroup (σ : EuclidFunctionalWithRecon c S) {δ : ℝ} (hδ : 0 < δ)
    {G : FreeSep} (hG : G ∈ finCombIn upperHalf)
    (hGd : (EuclidMotion.transl ((-δ) • timeVec)).actFree G ∈ finCombIn upperHalf) :
    σ.recon.cls ⟨G, hG⟩ =
      σ.heatSemigroup δ (σ.recon.cls ⟨_, hGd⟩) := by
  have h := σ.recon.expHam_cls δ hδ.le ⟨_, hGd⟩
  simp only [actFree_transl_neg_cancel] at h
  rw [classOrZero_of_mem _ hG] at h
  exact h.symm
theorem exists_vectors_matrixElement
    (hCalc : HamMomMatrixCalculus)
    (hConj : ∀ F : FreeSep, freeConj (timeFlip.actFree F) = timeFlip.actFree (freeConj F))
    (σ : EuclidFunctionalWithRecon c S) {δ : ℝ} (hδ : 0 < δ) {A' B' : FreeSep}
    (hA' : A' ∈ finCombIn {x | x 3 < -δ}) (hB' : B' ∈ finCombIn {x | δ < x 3}) :
    ∃ φ ψ : σ.space, ∀ v : Fin 3 → ℝ,
      centeredFnFree S
          (freeMul A' ((EuclidMotion.transl (SpectralPoint.spatialEmbed v)).actFree B')) =
        BorelComplexMeasures.integralOf (σ.pairSpectralMeasure φ ψ)
          (zeroExtend SpectralPoint.nonnegEnergy.1
            (SpectralPoint.laplaceFourierKernel (δ + δ) (SpectralPoint.spatialEmbed v))) := by
  have hup : {x : R4 | δ < x 3} ⊆ upperHalf := fun x hx =>
    lt_trans hδ hx
  set F : FreeSep := timeFlip.actFree (freeConj A') with hFdef
  have hF : F ∈ finCombIn {x | δ < x 3} := by
    refine finCombIn_mono ?_ (actFree_mem_finCombIn timeFlip (freeConj_mem_finCombIn hA'))
    rintro _ ⟨x, hx, rfl⟩
    have h3 := (spatialProj_timeFlip x).2
    change δ < timeFlip x 3
    rw [h3]
    have hx' : x 3 < -δ := hx
    linarith
  have hFF : timeFlip.actFree (freeConj F) = A' := by
    rw [hFdef, hConj, freeConj_freeConj, actFree_actFree, timeFlip_mul_self, actFree_one]
  have hdown : ∀ {G : FreeSep}, G ∈ finCombIn {x | δ < x 3} →
      (EuclidMotion.transl ((-δ) • timeVec)).actFree G ∈ finCombIn upperHalf := by
    intro G hG
    refine finCombIn_mono ?_ (actFree_mem_finCombIn _ hG)
    rintro _ ⟨x, hx, rfl⟩
    change 0 < EuclidMotion.transl ((-δ) • timeVec) x 3
    rw [transl_apply_three]
    have hx' : δ < x 3 := hx
    simp [PeriodicLattice.coordVec]
    linarith
  set cl := σ.recon.cls with hcl
  have hFp := finCombIn_mono hup hF
  have hBp := finCombIn_mono hup hB'
  have hFd := hdown hF
  have hBd := hdown hB'
  refine ⟨cl ⟨_, hFd⟩, cl ⟨_, hBd⟩, fun v => ?_⟩
  set φ := cl ⟨_, hFd⟩ with hφ
  set ψ := cl ⟨_, hBd⟩ with hψ
  set vec := SpectralPoint.spatialEmbed v with hvec
  set G : FreeSep := (EuclidMotion.transl vec).actFree B' with hGdef
  have hG : G ∈ finCombIn upperHalf := by
    refine finCombIn_mono ?_ (actFree_mem_finCombIn (EuclidMotion.transl vec) hB')
    rintro _ ⟨x, hx, rfl⟩
    change 0 < EuclidMotion.transl vec x 3
    have hv3 : vec 3 = 0 := spatialEmbed_mem_spatialVecs v
    rw [transl_apply_three, hv3, add_zero]
    exact lt_trans hδ hx
  have hcF := cls_eq_heatSemigroup σ hδ hFp hFd
  have hcB := cls_eq_heatSemigroup σ hδ hBp hBd
  have hU : σ.spatialShiftOp v (cl ⟨B', hBp⟩) = cl ⟨G, hG⟩ :=
    (σ.recon.transl_cls vec (spatialEmbed_mem_spatialVecs v) ⟨B', hBp⟩).trans
      (classOrZero_of_mem _ hG)
  obtain ⟨hsa, -, hee, hcomm, -⟩ := (hCalc c S σ φ ψ).2.2 δ hδ.le δ hδ.le v
  obtain ⟨-, -, -, -, hint⟩ := (hCalc c S σ φ ψ).2.2 (δ + δ) (by positivity) 0 le_rfl v
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa
  have hUe : σ.spatialShiftOp v (σ.heatSemigroup δ ψ) =
      σ.heatSemigroup δ (σ.spatialShiftOp v ψ) :=
    (ContinuousLinearMap.ext_iff.1 hcomm ψ).symm
  have hee' : σ.heatSemigroup δ (σ.heatSemigroup δ (σ.spatialShiftOp v ψ)) =
      σ.heatSemigroup (δ + δ) (σ.spatialShiftOp v ψ) :=
    ContinuousLinearMap.ext_iff.1 hee _
  have hform : centeredFnFree S (freeMul A' G) = osForm S F G := by
    rw [osForm, hFF]
  rw [hform, ← hint, ← σ.recon.inner_cls ⟨F, hFp⟩ ⟨G, hG⟩, ← hU]
  change inner ℂ (cl ⟨F, hFp⟩) (σ.spatialShiftOp v (cl ⟨B', hBp⟩)) = _
  rw [hcF, hcB]
  change inner ℂ (σ.heatSemigroup δ φ) (σ.spatialShiftOp v (σ.heatSemigroup δ ψ)) = _
  rw [hUe]
  refine (hsym _ _).trans ?_
  rw [← hee']
  rfl
end MatrixElement
section Preliminaries
open Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
theorem scalarEquiv_image (O : Set ℂ) :
    scalarEquiv '' O = {z : Coordinates.ComplexCoordinates 1 | z 0 ∈ O} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    refine ⟨z 0, hz, ?_⟩
    funext i
    rw [Subsingleton.elim i 0]
    rfl
theorem holomorphicOnComplex_of_differentiableOn {O : Set ℂ} (hO : IsOpen O) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G O) : ForwardTube.HolomorphicOnComplex O G := by
  have hev : Continuous fun z : Coordinates.ComplexCoordinates 1 => z 0 := continuous_apply 0
  unfold ForwardTube.HolomorphicOnComplex Coordinates.ComplexCoordinates.IsHolomorphicVia
  rw [scalarEquiv_image]
  refine ⟨hO.preimage hev, ?_, fun a ha j => ?_⟩
  · refine continuousOn_pi.2 fun i => ?_
    exact hG.continuousOn.comp hev.continuousOn fun z hz => hz
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have hb : (Coordinates.ComplexCoordinates.stdBasisVector (0 : Fin 1) : Coordinates.ComplexCoordinates 1) 0 = 1 := by
      simp [Coordinates.ComplexCoordinates.stdBasisVector]
    have hline : Continuous fun ζ : ℂ => a 0 + ζ := by fun_prop
    have hopen : ∀ᶠ ζ in nhds (0 : ℂ), a 0 + ζ ∈ O :=
      hline.continuousAt.eventually_mem (hO.mem_nhds (by simpa using ha))
    filter_upwards [hopen] with ζ hζ
    refine differentiableAt_pi.2 fun i => ?_
    have he : (fun ζ' : ℂ => ((scalarEquiv ∘ G ∘ scalarEquiv.symm)
        (a + ζ' • Coordinates.ComplexCoordinates.stdBasisVector (0 : Fin 1))) i) =
        fun ζ' => G (a 0 + ζ') := by
      funext ζ'
      simp [scalarEquiv, hb, Equiv.funUnique]
    rw [he]
    exact ((hG (a 0 + ζ) hζ).differentiableAt (hO.mem_nhds hζ)).comp ζ (by fun_prop)
theorem isRealAnalyticOnReal_of_extension
    (hHolo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set ℂ} (hO : IsOpen O) (hR : ∀ r : ℝ, (r : ℂ) ∈ O) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G O) {f : ℝ → ℂ} (hf : ∀ r : ℝ, G r = f r) :
    IsRealAnalyticOnReal f := by
  have hh := holomorphicOnComplex_of_differentiableOn hO hG
  have hopen : IsOpen (scalarEquiv '' O) := hh.1
  have hra := (((hHolo.1 1 _ hopen).1 1 _ hh).2.2.2.2)
  have hreal : ∀ z ∈ Coordinates.ComplexCoordinates.realLocus 1, z 0 = (((z 0).re : ℝ) : ℂ) := fun z hz =>
    Complex.ext rfl (by simpa using hz 0)
  have hset : scalarEquiv '' O ∩ Coordinates.ComplexCoordinates.realLocus 1 =
      Coordinates.ComplexCoordinates.realLocus 1 := by
    refine Set.inter_eq_right.2 fun z hz => ?_
    rw [scalarEquiv_image]
    change z 0 ∈ O
    rw [hreal z hz]
    exact hR _
  rw [hset] at hra
  refine ⟨hra.1, fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := hra.2 a ha
  refine ⟨c, ?_⟩
  filter_upwards [hc, self_mem_nhdsWithin] with z hz hzr
  convert hz using 1
  funext i
  change f (z 0).re = G (z 0)
  rw [hreal z hzr, hf]
  simp
end Preliminaries
theorem holds
    (hIso : OrthogonalInvariance.Holds)
    (hMom : OrthogonalInvariance.OrthogonalMapStatement)
    (hCalc : HamMomMatrixCalculus)
    (hOne : ComplexAnalysis.HolomorphicAndRealAnalyticFacts)
    (hInv : MomentSymmetry.ReductionHolds)
    (hCone : EuclidFunctionalWithRecon.ConeForms.Holds)
    (hSharp : SharpNormC1.Main)
    (hHolo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) : Holds := by
  intro m S σ hcone μ c δ hδ p p' _ _ a ha b hb hAs hBs u hu
  obtain ⟨-, -, -, -, -, -, hImages, hConc, hAct, -, -⟩ := hIso
  have hVal := (hMom m S σ 1).2.2.2.2.2.2
  have hsets : Disjoint {x : R4 | x μ < c - δ} {x : R4 | c + δ < x μ} :=
    Set.disjoint_left.2 fun x h1 h2 => by
      have h1' : x μ < c - δ := h1
      have h2' : c + δ < x μ := h2
      linarith
  have hmove : ∀ (r : ℝ) (k : Fin p'),
      supp ((EuclidMotion.transl (r • u)).actFn (b k)) ⊆ {x | c + δ < x μ} := by
    intro r k
    rw [supp_actFn]
    rintro _ ⟨x, hx, rfl⟩
    change c + δ < EuclidMotion.transl (r • u) x μ
    rw [EuclidMotion.transl_apply]
    have hx' : c + δ < x μ := hBs k hx
    simpa [hu] using hx'
  have hA : ∀ r : ℝ, MulIsAppendedTuple S a b u r := by
    intro r
    obtain ⟨-, -, hbm, hEq⟩ := hImages 1 (r • u) p' b hb
    have hd : ∀ l k, Disjoint (supp (a l))
        (supp ((EuclidMotion.transl (r • u)).actFn (b k))) := fun l k =>
      hsets.mono (hAs l) (hmove r k)
    have h := hConc p p' a _ ha hbm hd
    refine ⟨?_, h.2.1, ?_⟩
    · rw [translatedTuple, hEq]
      exact h.1
    · rw [valueAlongShift, translatedTuple, hEq]
      exact hVal p p' a ha _ hbm hd
  set Q := swapMatrix μ 3 with hQ
  set w := EuclidMotion.ofOrthogonalMatrix Q with hw
  have hwc : ∀ x : R4, w x 3 = x μ := fun x => by
    rw [hw, hQ, swapMotion_apply, Equiv.swap_apply_right]
  set T := EuclidMotion.transl ((-c) • timeVec) with hT
  have hTc : ∀ x : R4, T x 3 = x 3 - c := fun x => by
    rw [hT, transl_apply_three]
    simp [PeriodicLattice.coordVec]
    ring
  have hAin := complexTuple_mem_finCombIn hSharp m a ha hAs
  have hBin := complexTuple_mem_finCombIn hSharp m b hb hBs
  set tA := complexTuple a with htA
  set tB := complexTuple b with htB
  have hA' : T.actFree (w.actFree tA) ∈ finCombIn {x | x 3 < -δ} := by
    refine finCombIn_mono ?_
      (actFree_mem_finCombIn T (actFree_mem_finCombIn w hAin))
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change T (w x) 3 < -δ
    rw [hTc, hwc]
    have hx' : x μ < c - δ := hx
    linarith
  have hB' : T.actFree (w.actFree tB) ∈ finCombIn {x | δ < x 3} := by
    refine finCombIn_mono ?_
      (actFree_mem_finCombIn T (actFree_mem_finCombIn w hBin))
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change δ < T (w x) 3
    rw [hTc, hwc]
    have hx' : c + δ < x μ := hx
    linarith
  have hConj : ∀ F : FreeSep, freeConj (timeFlip.actFree F) = timeFlip.actFree (freeConj F) := by
    intro F
    rw [timeFlip_eq_ofOrthogonalMatrix]
    exact (hAct timeFlipMatrix 1 0 F F).2.1
  obtain ⟨φ, ψ, hval⟩ := exists_vectors_matrixElement hCalc hConj σ hδ hA' hB'
  set q : Fin 3 → ℝ := fun j => w u j.castSucc with hq
  have hcar := (hCone σ).2.1.1 ((hCone σ).1.1 hcone)
  obtain ⟨G, hGd, hGr⟩ := exists_holomorphic_extension hCalc hOne σ hcar φ ψ δ hδ q
  have hw3 : w u 3 = 0 := by rw [hwc, hu]
  have hsum : ∑ j, |q j| = tangentialNorm μ u := by
    have h1 : ∑ i, |w u i| = ∑ j, |q j| + |w u (Fin.last 3)| :=
      Fin.sum_univ_castSucc fun i => |w u i|
    have h2 : ∑ i, |w u i| = ∑ i, |u i| := by
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
        (Equiv.sum_comp (Equiv.swap μ 3) fun i => |u i|)
      rw [hw, hQ, swapMotion_apply]
    have h3 : |w u (Fin.last 3)| = 0 := by
      change |w u 3| = 0
      rw [hw3, abs_zero]
    have h4 : tangentialNorm μ u = ∑ i, |u i| :=
      Finset.sum_erase _ (by rw [hu, abs_zero])
    rw [h4, ← h2, h1, h3, add_zero]
  rw [hsum] at hGd
  have hvec : ∀ r : ℝ, SpectralPoint.spatialEmbed (r • q) = w (r • u) := by
    intro r
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change (Fin.snoc (α := fun _ => ℝ) (r • q) 0 : R4) (Fin.last 3) = w (r • u) 3
      rw [Fin.snoc_last, hwc]
      simp [hu]
    · change (Fin.snoc (α := fun _ => ℝ) (r • q) 0 : R4) j.castSucc = w (r • u) j.castSucc
      rw [Fin.snoc_castSucc]
      simp only [hq, Pi.smul_apply, smul_eq_mul, hw, hQ, swapMotion_apply]
  have hInvar := (hInv m S σ).2.1
  have hkey : ∀ r : ℝ, G r = valueAlongShift S a b u r := by
    intro r
    rw [hGr r, ← hval (r • q), hvec r]
    set M := (EuclidMotion.transl (r • u)).actFree tB with hM
    have hdef : MulDefined tA M := (hA r).1
    obtain ⟨hd1, -, e1, -⟩ := (hAct Q Q ((-c) • timeVec) tA M).2.2.2.2 hdef
    obtain ⟨-, -, -, e2⟩ := (hAct Q Q ((-c) • timeVec) (w.actFree tA) (w.actFree M)).2.2.2.2 hd1
    obtain ⟨-, -, -, e3, -⟩ := hAct Q Q (r • u) tB tB
    have e1' : w.actFree (freeMul tA M) = freeMul (w.actFree tA) (w.actFree M) := e1
    have e2' : T.actFree (freeMul (w.actFree tA) (w.actFree M)) =
        freeMul (T.actFree (w.actFree tA)) (T.actFree (w.actFree M)) := e2
    have e3' : w.actFree M = (EuclidMotion.transl (w (r • u))).actFree (w.actFree tB) := e3
    have hcomm : T * EuclidMotion.transl (w (r • u)) = EuclidMotion.transl (w (r • u)) * T := by
      rw [hT, transl_mul_transl, transl_mul_transl, add_comm]
    have hwM : T.actFree (w.actFree M) =
        (EuclidMotion.transl (w (r • u))).actFree (T.actFree (w.actFree tB)) := by
      rw [e3', actFree_actFree T, actFree_actFree (EuclidMotion.transl (w (r • u))) T, hcomm]
    have hv : valueAlongShift S a b u r = centeredFnFree S (freeMul tA M) := rfl
    have s1 := (hInvar (freeMul (w.actFree tA) (w.actFree M))).1 ((-c) • timeVec)
    have s2 := (hInvar (freeMul tA M)).2 w (swapMotion_mem_hyperoctahedral μ 3)
    rw [hv, ← hwM, ← e2']
    exact s1.trans ((congrArg _ e1').symm.trans s2)
  have hRstrip : ∀ r : ℝ, (r : ℂ) ∈ stripOf δ (tangentialNorm μ u) := fun r => by
    change |((r : ℂ)).im| * _ < 2 * δ
    simp [hδ]
  refine ⟨hA, ⟨G, holomorphicOnComplex_of_differentiableOn (isOpen_stripOf _ _) hGd, hkey⟩, ?_,
    isRealAnalyticOnReal_of_extension hHolo (isOpen_stripOf _ _) hRstrip hGd hkey⟩
  intro h0
  have h00 : tangentialNorm μ u = 0 := by
    simp [tangentialNorm, h0]
  rw [h00]
  ext r
  simp [stripOf, hδ]
end EuclideanFunctionals.TangentialAnalyticity
end YangMills.Construction
