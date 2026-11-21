import YangMills.Construction.EuclideanFunctionals.ConeConditionOfAReconstructionInThreeFormsAndTheCalculusOverThePyramid
import YangMills.Construction.EuclideanFunctionals.FirstFactsOnAReconstruction
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.EuclidFunctionalWithRecon.ConeForms
open SpectralPoint
open BorelSpectral
open HilbertSpaceBasics (ofBounded)
open BorelCalculus (IsBoundedFn conjFn)
open SpectralTheorem (spectralIntegralOp)
def swapMotion (j : Fin 3) : timeStabilizer :=
  ⟨ofSignedFrame (Equiv.swap 0 j.castSucc, fun _ => 1), ⟨⟨_, rfl⟩, by
    rw [ofSignedFrame_apply]
    funext μ
    fin_cases j <;> fin_cases μ <;>
      simp [PeriodicLattice.SignedFrame.actOnVector, PeriodicLattice.coordVec, Equiv.swap_apply_def]⟩⟩
theorem swapMotion_apply (j : Fin 3) (x : R4) (μ : Fin 4) :
    (swapMotion j : EuclidMotion) x μ = x (Equiv.swap 0 j.castSucc μ) := by
  change ofSignedFrame _ x μ = _
  rw [ofSignedFrame_apply]
  simp [PeriodicLattice.SignedFrame.actOnVector]
theorem energyOf_rotPoint (w : timeStabilizer) (p : EMPoints) :
    SpectralPoint.energyOf (rotPoint w p) = SpectralPoint.energyOf p := rfl
theorem momentumOf_rotPoint_swap (j k : Fin 3) (p : EMPoints) :
    SpectralPoint.momentumOf (rotPoint (swapMotion j) p) k = SpectralPoint.momentumOf p (Equiv.swap 0 j k) := by
  have hk : SpectralPoint.momentumOf (rotPoint (swapMotion j) p) k =
      (swapMotion j : EuclidMotion) (spatialEmbed (SpectralPoint.momentumOf p)) k.castSucc := rfl
  rw [hk, swapMotion_apply]
  fin_cases j <;> fin_cases k <;>
    simp [spatialEmbed, Equiv.swap_apply_def, Fin.snoc]
  all_goals rfl
theorem rotPoint_swap_rotPoint_swap (j : Fin 3) (p : EMPoints) :
    rotPoint (swapMotion j) (rotPoint (swapMotion j) p) = p := by
  refine Subtype.ext (funext fun i => ?_)
  refine Fin.cases ?_ (fun k => ?_) i
  · exact energyOf_rotPoint _ _ |>.trans (energyOf_rotPoint _ p)
  · change SpectralPoint.momentumOf _ k = SpectralPoint.momentumOf p k
    rw [momentumOf_rotPoint_swap, momentumOf_rotPoint_swap, Equiv.swap_apply_self]
theorem dot3_basisVec (j : Fin 3) (q : Fin 3 → ℝ) : dot3 (basisVec j) q = q j := by
  simp [dot3, basisVec, Pi.single_apply]
theorem mem_belowAbsMomentum_basisVec (j : Fin 3) (p : EMPoints) :
    p ∈ (belowAbsMomentum (basisVec j)).1 ↔ SpectralPoint.energyOf p < |SpectralPoint.momentumOf p j| := by
  change SpectralPoint.energyOf p < |dot3 (basisVec j) (SpectralPoint.momentumOf p)| ↔ _
  rw [dot3_basisVec]
theorem image_rotPoint_swap_belowAbsMomentum (j : Fin 3) :
    rotPoint (swapMotion j) '' (belowAbsMomentum (basisVec 0)).1 =
      (belowAbsMomentum (basisVec j)).1 := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_belowAbsMomentum_basisVec, energyOf_rotPoint, momentumOf_rotPoint_swap,
      Equiv.swap_apply_right]
    exact (mem_belowAbsMomentum_basisVec 0 x).1 hx
  · intro hp
    refine ⟨rotPoint (swapMotion j) p, ?_, rotPoint_swap_rotPoint_swap j p⟩
    rw [mem_belowAbsMomentum_basisVec, energyOf_rotPoint, momentumOf_rotPoint_swap,
      Equiv.swap_apply_left]
    exact (mem_belowAbsMomentum_basisVec j p).1 hp
variable {c : SharpScale} {S : ConnFamily}
theorem hamGeAbsMomentum_of_coneCondition (hFacts : ReconstructionBasicFacts)
    (σ : EuclidFunctionalWithRecon c S) (h : σ.ConeCondition) (j : Fin 3) :
    σ.HamGeAbsMomentum j := by
  have hσ := hFacts c S σ σ.space σ.recon
  rw [withRecon_self] at hσ
  obtain ⟨-, -, -, -, -, -, -, hc, -⟩ := hσ
  obtain ⟨hm, he⟩ := hc (swapMotion j) (belowAbsMomentum (basisVec 0))
  have hset : (⟨rotPoint (swapMotion j) '' (belowAbsMomentum (basisVec 0)).1, hm⟩ :
      BorelSubsets EMPoints) = belowAbsMomentum (basisVec j) :=
    Subtype.ext (image_rotPoint_swap_belowAbsMomentum j)
  rw [hset] at he
  have h0 : σ.jointMeasure (belowAbsMomentum (basisVec 0)) = 0 := h
  refine ContinuousLinearMap.coe_injective ?_
  rw [← he, SpectralMeasure.unitaryPushforward, h0]
  ext ψ
  simp
theorem compl_pyramid_eq_iUnion :
    (pyramid.1)ᶜ = ⋃ j : Fin 3, (belowAbsMomentum (basisVec j)).1 := by
  ext p
  simp only [mem_compl_iff, mem_iUnion, mem_belowAbsMomentum_basisVec]
  change (¬ ∀ j : Fin 3, |SpectralPoint.momentumOf p j| ≤ SpectralPoint.energyOf p) ↔ _
  simp only [not_forall, not_le]
theorem isCarriedBy_pyramid (hCalc : SpectralMeasureCalculus.CalculusTheorem)
    (σ : EuclidFunctionalWithRecon c S)
    (h : ∀ j : Fin 3, σ.HamGeAbsMomentum j) :
    σ.jointMeasure.IsCarriedBy pyramid := by
  obtain ⟨hM, -⟩ := hCalc σ.space 4 _ σ.jointMeasure
  have hU := hM.value_iUnion (Fin 3) (fun j => belowAbsMomentum (basisVec j)) h
  have hset : (⟨(pyramid.1)ᶜ, pyramid.2.compl⟩ : BorelSubsets EMPoints) =
      ⟨⋃ j : Fin 3, (belowAbsMomentum (basisVec j)).1,
        MeasurableSet.iUnion fun j => (belowAbsMomentum (basisVec j)).2⟩ :=
    Subtype.ext compl_pyramid_eq_iUnion
  change σ.jointMeasure _ = 0
  rw [hset]
  exact hU
theorem hamGeAbsMomentum_of_isCarriedBy (σ : EuclidFunctionalWithRecon c S)
    (h : σ.jointMeasure.IsCarriedBy pyramid) (j : Fin 3) :
    σ.HamGeAbsMomentum j := by
  have hi := σ.jointMeasure.map_inter (belowAbsMomentum (basisVec j))
    ⟨(pyramid.1)ᶜ, pyramid.2.compl⟩
  have hset : (⟨(belowAbsMomentum (basisVec j)).1 ∩ (pyramid.1)ᶜ,
      (belowAbsMomentum (basisVec j)).2.inter pyramid.2.compl⟩ : BorelSubsets EMPoints) =
      belowAbsMomentum (basisVec j) := by
    refine Subtype.ext (inter_eq_left.2 ?_)
    rw [compl_pyramid_eq_iUnion]
    exact subset_iUnion (fun k : Fin 3 => (belowAbsMomentum (basisVec k)).1) j
  have hz : σ.jointMeasure ⟨(pyramid.1)ᶜ, pyramid.2.compl⟩ = 0 := h
  change σ.jointMeasure.toFun _ = _ at hi
  rw [hset] at hi
  change σ.jointMeasure _ = 0
  exact hi.trans (by rw [hz, mul_zero])
theorem zeroExtend_pyramid_coe (f : pyramid.1 → ℂ) (p : pyramid.1) :
    zeroExtend pyramid.1 f p = f p := by
  simp [zeroExtend]
theorem measurable_zeroExtend_pyramid {f : pyramid.1 → ℂ} (hf : Measurable f) :
    Measurable (zeroExtend pyramid.1 f) :=
  measurable_zeroExtend pyramid.2 hf
theorem isBoundedFn_zeroExtend_pyramid {f : pyramid.1 → ℂ} (hf : IsBoundedFn f) :
    IsBoundedFn (zeroExtend pyramid.1 f) := by
  obtain ⟨b, hb⟩ := hf
  refine ⟨max b 0, fun y => ?_⟩
  by_cases hy : y ∈ pyramid.1
  · simpa [zeroExtend, hy] using Or.inl (hb ⟨y, hy⟩)
  · simp [zeroExtend, hy]
theorem zeroExtend_pyramid_add (f g : pyramid.1 → ℂ) :
    zeroExtend pyramid.1 (f + g) = zeroExtend pyramid.1 f + zeroExtend pyramid.1 g := by
  funext y
  by_cases hy : y ∈ pyramid.1 <;> simp [zeroExtend, hy]
theorem zeroExtend_pyramid_smul (a : ℂ) (f : pyramid.1 → ℂ) :
    zeroExtend pyramid.1 (a • f) = a • zeroExtend pyramid.1 f := by
  funext y
  by_cases hy : y ∈ pyramid.1 <;> simp [zeroExtend, hy]
theorem zeroExtend_pyramid_mul (f g : pyramid.1 → ℂ) :
    zeroExtend pyramid.1 (f * g) = zeroExtend pyramid.1 f * zeroExtend pyramid.1 g := by
  funext y
  by_cases hy : y ∈ pyramid.1 <;> simp [zeroExtend, hy]
theorem zeroExtend_pyramid_conjFn (f : pyramid.1 → ℂ) :
    zeroExtend pyramid.1 (conjFn f) =
      conjFn (zeroExtend pyramid.1 f) := by
  funext y
  by_cases hy : y ∈ pyramid.1 <;> simp [zeroExtend, conjFn, hy]
theorem holds_of (hCalc : SpectralMeasureCalculus.CalculusTheorem)
    (hFacts : ReconstructionBasicFacts) : Holds := by
  intro c S σ
  obtain ⟨-, hB, hA, -⟩ := hCalc σ.space 4 _ σ.jointMeasure
  refine ⟨⟨hamGeAbsMomentum_of_coneCondition hFacts σ, fun h => h 0⟩,
    ⟨isCarriedBy_pyramid hCalc σ, hamGeAbsMomentum_of_isCarriedBy σ⟩,
    fun _ _ hC => ⟨fun f hf hb => ⟨?_, ?_, ?_⟩, fun f g hf hbf hg hbg => ⟨?_, fun a => ?_, ?_⟩⟩⟩
  · have hm := measurable_zeroExtend_pyramid hf
    have hbd := isBoundedFn_zeroExtend_pyramid hb
    obtain ⟨hdom, hval⟩ := hA.isIntegralOf _ hm
    obtain ⟨hU, hV⟩ := hA.of_bounded _ hm hbd
    refine LinearPMap.ext ?_ ?_
    · refine Submodule.ext fun ψ => ?_
      have : ψ ∈ σ.jointMeasure.integralDom (zeroExtend pyramid.1 f) := by
        rw [hU]
        exact mem_univ ψ
      exact iff_of_true ((hdom ψ).2 this) Submodule.mem_top
    · intro x hx _
      exact (hval ⟨x, hx⟩).trans (hV x)
  · have h := hB.norm_le _ pyramid (measurable_zeroExtend_pyramid hf) (isBoundedFn_zeroExtend_pyramid hb) hC
    simp only [zeroExtend_pyramid_coe] at h
    exact h
  · intro φ ψ
    change ⟪φ, σ.jointMeasure.integralOp _ ψ⟫_ℂ =
      ⟪σ.jointMeasure.integralOp (zeroExtend pyramid.1 (conjFn f)) φ, ψ⟫_ℂ
    rw [zeroExtend_pyramid_conjFn, hB.conjugate _ (measurable_zeroExtend_pyramid hf) (isBoundedFn_zeroExtend_pyramid hb),
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  · change σ.jointMeasure.integralOp _ = _
    rw [zeroExtend_pyramid_add]
    exact hB.add _ _ (measurable_zeroExtend_pyramid hf) (isBoundedFn_zeroExtend_pyramid hbf)
      (measurable_zeroExtend_pyramid hg) (isBoundedFn_zeroExtend_pyramid hbg)
  · change σ.jointMeasure.integralOp _ = _
    rw [zeroExtend_pyramid_smul]
    exact hB.smul a _ (measurable_zeroExtend_pyramid hf) (isBoundedFn_zeroExtend_pyramid hbf)
  · change σ.jointMeasure.integralOp _ = _
    rw [zeroExtend_pyramid_mul]
    exact hB.mul _ _ (measurable_zeroExtend_pyramid hf) (isBoundedFn_zeroExtend_pyramid hbf)
      (measurable_zeroExtend_pyramid hg) (isBoundedFn_zeroExtend_pyramid hbg)
end YangMills.Construction.EuclideanFunctionals.EuclidFunctionalWithRecon.ConeForms
