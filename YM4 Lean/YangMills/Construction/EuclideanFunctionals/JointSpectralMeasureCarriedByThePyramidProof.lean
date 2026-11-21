import YangMills.Construction.EuclideanFunctionals.FirstFactsOnAReconstruction
import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureCarriedByThePyramid
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.EuclidFunctionalWithRecon.CarriedByPyramid
open YangMills.Construction.BorelSpectral
open SpectralPoint
def swapFirstAxis (j : Fin 3) : timeStabilizer :=
  ⟨ofSignedFrame (Equiv.swap 0 j.castSucc, fun _ => 1), ⟨⟨_, rfl⟩, by
    rw [ofSignedFrame_apply]
    funext μ
    fin_cases j <;> fin_cases μ <;>
      simp [PeriodicLattice.SignedFrame.actOnVector, PeriodicLattice.coordVec, Equiv.swap_apply_def]⟩⟩
theorem swapFirstAxis_apply (j : Fin 3) (x : R4) (μ : Fin 4) :
    (swapFirstAxis j : EuclidMotion) x μ = x (Equiv.swap 0 j.castSucc μ) := by
  change ofSignedFrame _ x μ = _
  rw [ofSignedFrame_apply]
  simp [PeriodicLattice.SignedFrame.actOnVector]
theorem energyOf_rotPoint_swap (j : Fin 3) (p : EMPoints) :
    SpectralPoint.energyOf (rotPoint (swapFirstAxis j) p) = SpectralPoint.energyOf p :=
  rfl
theorem momentumOf_rotPoint_swap (j k : Fin 3) (p : EMPoints) :
    SpectralPoint.momentumOf (rotPoint (swapFirstAxis j) p) k = SpectralPoint.momentumOf p (Equiv.swap 0 j k) := by
  have hk : SpectralPoint.momentumOf (rotPoint (swapFirstAxis j) p) k =
      (swapFirstAxis j : EuclidMotion) (spatialEmbed (SpectralPoint.momentumOf p)) k.castSucc := by
    simp [SpectralPoint.momentumOf, rotPoint, rotSpatial]
  rw [hk, swapFirstAxis_apply]
  have hs : Equiv.swap (0 : Fin 4) j.castSucc k.castSucc = (Equiv.swap 0 j k).castSucc := by
    fin_cases j <;> fin_cases k <;> simp [Equiv.swap_apply_def]
  rw [hs]
  simp [spatialEmbed]
theorem rotPoint_swap_rotPoint_swap (j : Fin 3) (p : EMPoints) :
    rotPoint (swapFirstAxis j) (rotPoint (swapFirstAxis j) p) = p := by
  refine Subtype.ext (funext fun i => ?_)
  refine Fin.cases ?_ (fun k => ?_) i
  · exact energyOf_rotPoint_swap j _ |>.trans (energyOf_rotPoint_swap j p)
  · change SpectralPoint.momentumOf _ k = SpectralPoint.momentumOf p k
    rw [momentumOf_rotPoint_swap, momentumOf_rotPoint_swap, Equiv.swap_apply_self]
theorem image_ltAbsMomentumSet_zero (j : Fin 3) :
    rotPoint (swapFirstAxis j) '' (ltAbsMomentumSet 0).1 =
      (ltAbsMomentumSet j).1 := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    change SpectralPoint.energyOf _ < |SpectralPoint.momentumOf _ j|
    rw [energyOf_rotPoint_swap, momentumOf_rotPoint_swap, Equiv.swap_apply_right]
    exact hx
  · intro hp
    refine ⟨rotPoint (swapFirstAxis j) p, ?_, rotPoint_swap_rotPoint_swap j p⟩
    change SpectralPoint.energyOf _ < |SpectralPoint.momentumOf _ 0|
    rw [energyOf_rotPoint_swap, momentumOf_rotPoint_swap, Equiv.swap_apply_left]
    exact hp
theorem belowAbsMomentum_basisVec (j : Fin 3) :
    belowAbsMomentum (basisVec j) = ltAbsMomentumSet j := by
  refine Subtype.ext ?_
  ext p
  simp [belowAbsMomentum, ltAbsMomentumSet, dot3, basisVec, Pi.single_apply]
variable {c : SharpScale} {S : ConnFamily}
theorem jointMeasure_ltAbsMomentumSet_eq_zero (hFacts : ReconstructionBasicFacts)
    (σ : EuclidFunctionalWithRecon c S) (h : σ.ConeCondition) (j : Fin 3) :
    σ.jointMeasure (ltAbsMomentumSet j) = 0 := by
  have hc : σ.RotationCovariance := (hFacts c S σ σ.space σ.recon).2.2.2.2
  obtain ⟨-, -, -, hcov, -, -⟩ := hc
  obtain ⟨hm, he⟩ := hcov (swapFirstAxis j) (ltAbsMomentumSet 0)
  have hset : (⟨rotPoint (swapFirstAxis j) '' (ltAbsMomentumSet 0).1, hm⟩ :
      BorelSubsets EMPoints) = ltAbsMomentumSet j :=
    Subtype.ext (image_ltAbsMomentumSet_zero j)
  rw [hset] at he
  have h0 : σ.jointMeasure (ltAbsMomentumSet 0) = 0 := by
    rw [← belowAbsMomentum_basisVec]
    exact h
  refine ContinuousLinearMap.coe_injective ?_
  rw [← he]
  ext ψ
  simp [SpectralMeasure.unitaryPushforward, h0]
theorem isCarriedBy_pyramid (σ : EuclidFunctionalWithRecon c S)
    (h : ∀ j : Fin 3, σ.jointMeasure (ltAbsMomentumSet j) = 0) :
    σ.jointMeasure.IsCarriedBy pyramid := by
  have hset : (pyramid.1)ᶜ = ⋃ j : Fin 3, (ltAbsMomentumSet j).1 := by
    ext p
    simp [pyramid, ltAbsMomentumSet]
  refine ContinuousLinearMap.ext fun ψ => ?_
  have hnull : σ.jointMeasure.diagMeasure ψ (pyramid.1)ᶜ = 0 := by
    rw [hset]
    refine measure_iUnion_null fun j => ?_
    rw [SpectralMeasure.diagMeasure_apply, h j]
    simp
  have hval := σ.jointMeasure.diagMeasure_apply ψ ⟨(pyramid.1)ᶜ, pyramid.2.compl⟩
  rw [show σ.jointMeasure.diagMeasure ψ
      ((⟨(pyramid.1)ᶜ, pyramid.2.compl⟩ : BorelSubsets EMPoints).1) = 0 from hnull] at hval
  have hle : ‖σ.jointMeasure ⟨(pyramid.1)ᶜ, pyramid.2.compl⟩ ψ‖ ^ 2 ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hval.symm
  have hz : ‖σ.jointMeasure ⟨(pyramid.1)ᶜ, pyramid.2.compl⟩ ψ‖ = 0 := by
    nlinarith [norm_nonneg (σ.jointMeasure ⟨(pyramid.1)ᶜ, pyramid.2.compl⟩ ψ)]
  simpa using hz
theorem energyOf_nonneg_of_mem_pyramid {p : EMPoints} (hp : p ∈ pyramid.1) :
    0 ≤ SpectralPoint.energyOf p :=
  (abs_nonneg _).trans (hp 0)
theorem abs_dot3_le {p : EMPoints} (hp : p ∈ pyramid.1) (u : Fin 3 → ℝ) :
    |dot3 u (SpectralPoint.momentumOf p)| ≤ SpectralPoint.energyOf p * ∑ j, |u j| := by
  unfold dot3
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hp j) (abs_nonneg _)
theorem re_laplaceExponent (p : EMPoints) (z : Fin 4 → ℂ) :
    (-(z 3 * (SpectralPoint.energyOf p : ℂ)) + Complex.I * ∑ j : Fin 3, z j.castSucc * (SpectralPoint.momentumOf p j : ℂ)).re =
      -(SpectralPoint.energyOf p * (z 3).re) - ∑ j : Fin 3, SpectralPoint.momentumOf p j * (z j.castSucc).im := by
  rw [Complex.add_re, Complex.neg_re, Complex.I_mul_re, Complex.im_sum, Complex.mul_re]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add]
  have : ∑ j : Fin 3, (z j.castSucc).im * SpectralPoint.momentumOf p j =
      ∑ j : Fin 3, SpectralPoint.momentumOf p j * (z j.castSucc).im :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [this]
  ring
theorem statement_holds (hFacts : ReconstructionBasicFacts) : statement := by
  intro c S σ h
  have ha := jointMeasure_ltAbsMomentumSet_eq_zero hFacts σ h
  refine ⟨fun j => ⟨?_, ha j⟩, isCarriedBy_pyramid σ ha, fun p hp u => abs_dot3_le hp u, ?_⟩
  · change σ.jointMeasure (belowAbsMomentum (basisVec j)) = 0
    rw [belowAbsMomentum_basisVec]
    exact ha j
  · intro p hp z
    refine ⟨?_, ?_, fun hz => ?_⟩
    · rw [Complex.norm_exp, re_laplaceExponent]
    · refine Real.exp_le_exp.mpr ?_
      have hd := abs_dot3_le hp fun j => (z j.castSucc).im
      have hn := neg_abs_le (dot3 (fun j => (z j.castSucc).im) (SpectralPoint.momentumOf p))
      have hs : dot3 (fun j => (z j.castSucc).im) (SpectralPoint.momentumOf p) =
          ∑ j : Fin 3, SpectralPoint.momentumOf p j * (z j.castSucc).im :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hs] at hn hd
      nlinarith
    · refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ SpectralPoint.energyOf p * ((z 3).re - ∑ j : Fin 3, |(z j.castSucc).im|) :=
        mul_nonneg (energyOf_nonneg_of_mem_pyramid hp) (sub_nonneg.mpr hz)
      linarith
end YangMills.Construction.EuclideanFunctionals.EuclidFunctionalWithRecon.CarriedByPyramid
