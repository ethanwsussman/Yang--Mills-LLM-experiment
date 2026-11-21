import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import Mathlib
import YangMills.Construction.SummableBoundsOfTheFlow.EntriesOfTheLevelsOnTwoToriProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.MomentMethod
def bareMaxwellFormStatement : Prop :=
  ∀ (a : ℝ) (L m : ℕ) [NeZero m] (A A' : TorusFields.TorusBond m → ℝ),
    WeightedResponses.maxwellForm a L 0 A A' =
      ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m)),
        WeightedResponses.curl A p * WeightedResponses.curl A' p
end YangMills.Construction.MomentMethod
end

noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.MomentMethod
open TorusFields WeightedResponses BlockAverages
section Calculus
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
private theorem iteratedFDeriv_two_comp_clm {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (ι : G →L[ℝ] E) (v : Fin 2 → G) :
    iteratedFDeriv ℝ 2 (fun s => f (ι s)) 0 v = fderiv ℝ (fderiv ℝ f) 0 (ι (v 0)) (ι (v 1)) := by
  obtain ⟨U, hU, hfU⟩ : ∃ U ∈ 𝓝 (0 : E), ContDiffOn ℝ 2 f U := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.1 hU
  have hfV := hfU.mono hVU
  have hpre : IsOpen (ι ⁻¹' V) := hVo.preimage ι.continuous
  have hpre0 : (0 : G) ∈ ι ⁻¹' V := by simpa using hV0
  have hcomp := ι.iteratedFDerivWithin_comp_right hfV hVo.uniqueDiffOn hpre.uniqueDiffOn hpre0 (i := 2) le_rfl
  have hwithin₁ := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f ∘ ι) (F := ℝ) 2 hpre hpre0
  have hwithin₂ := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) (F := ℝ) 2 hVo hV0
  have hfun : iteratedFDeriv ℝ 2 (fun s => f (ι s)) 0 = iteratedFDeriv ℝ 2 (f ∘ ι) 0 := rfl
  rw [hfun, ← hwithin₁, hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, hwithin₂,
    iteratedFDeriv_two_apply]
abbrev _root_.YangMills.SharedProofs.p5330 := @iteratedFDeriv_two_comp_clm
private theorem sum_basis_bilinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) (u w : ι → ℝ) :
    ∑ i, ∑ j, u i * B (Pi.single i 1) (Pi.single j 1) * w j = B u w := by
  have hexp : ∀ u : ι → ℝ, u = ∑ i, u i • (Pi.single i (1 : ℝ) : ι → ℝ) := fun u => by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  calc ∑ i, ∑ j, u i * B (Pi.single i 1) (Pi.single j 1) * w j
      = B (∑ i, u i • (Pi.single i (1 : ℝ) : ι → ℝ)) (∑ i, w i • (Pi.single i (1 : ℝ) : ι → ℝ)) := by
        simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
          smul_eq_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = B u w := by rw [← hexp u, ← hexp w]
abbrev _root_.YangMills.SharedProofs.p21054 := @sum_basis_bilinear
end Calculus
section AbelianFields
private theorem expUnit_add_smul (s t : ℝ) :
    expUnit ((s + t) • unitGenerator) = expUnit (s • unitGenerator) * expUnit (t • unitGenerator) := by
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ _
  apply Subtype.ext
  have hcomm : Commute (((s • unitGenerator : imaginaryQuaternions)) : ℍ[ℝ])
      (((t • unitGenerator : imaginaryQuaternions)) : ℍ[ℝ]) := by
    simp only [Submodule.coe_smul]
    exact ((Commute.refl _).smul_left s).smul_right t
  have hsum : (((s + t) • unitGenerator : imaginaryQuaternions) : ℍ[ℝ]) =
      ((s • unitGenerator : imaginaryQuaternions) : ℍ[ℝ]) + ((t • unitGenerator : imaginaryQuaternions) : ℍ[ℝ]) := by
    simp [add_smul]
  simp only [expUnit, Submonoid.coe_mul]
  rw [hsum, NormedSpace.exp_add_of_commute hcomm]
abbrev _root_.YangMills.SharedProofs.p21518 := @expUnit_add_smul
private theorem expUnit_smul_inv (s : ℝ) :
    (expUnit (s • unitGenerator))⁻¹ = expUnit ((-s) • unitGenerator) := by apply _root_.YangMills.SharedProofs.p1618 <;> assumption
private theorem re_expUnit_smul (s : ℝ) :
    ((expUnit (s • unitGenerator) : UnitQuaternion) : ℍ[ℝ]).re = Real.cos s := by apply _root_.YangMills.SharedProofs.p36152 <;> assumption
variable {n : ℕ}
private def abelianField (θ : TorusBond n → ℝ) : TorusField n := fun x i => expUnit (θ (x, i) • unitGenerator)
private theorem holonomy_abelianField (θ : TorusBond n → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    holonomy (abelianField θ) x μ ν = expUnit (curl θ (x, μ, ν) • unitGenerator) := by
  simp only [holonomy, abelianField, curl]
  rw [expUnit_smul_inv, expUnit_smul_inv, ← expUnit_add_smul, ← expUnit_add_smul, ← expUnit_add_smul]
  congr 2
private theorem plaquetteEnergy_abelianField (θ : TorusBond n → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    plaquetteEnergy (abelianField θ) x μ ν = 1 - Real.cos (curl θ (x, μ, ν)) := by
  rw [plaquetteEnergy, holonomy_abelianField, re_expUnit_smul]
private theorem maxwellKernel_eq_fderiv [NeZero n] (β : ℝ) (L k : ℕ)
    (hdiff : ContDiffAt ℝ 2 (fun θ : TorusBond n → ℝ => actionAtLevel β L k Finset.univ (abelianField θ)) 0)
    (b b' : TorusBond n) :
    maxwellKernel β L k b b' =
      fderiv ℝ (fderiv ℝ fun θ : TorusBond n → ℝ => actionAtLevel β L k Finset.univ (abelianField θ)) 0
        (Pi.single b 1) (Pi.single b' 1) := by
  let ι : (Fin 2 → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
    (ContinuousLinearMap.proj 0).smulRight (Pi.single b 1) +
      (ContinuousLinearMap.proj 1).smulRight (Pi.single b' 1)
  have hite : ∀ (c : TorusBond n) (x : TorusSite n) (i : Fin 4) (s : ℝ),
      (if c = (x, i) then s • unitGenerator else (0 : imaginaryQuaternions)) =
      (s * (Pi.single c (1 : ℝ) : TorusBond n → ℝ) (x, i)) • unitGenerator := by
    intro c x i s
    by_cases hc : c = (x, i)
    · rw [if_pos hc, hc]
      simp
    · rw [if_neg hc, Pi.single_eq_of_ne (Ne.symm hc)]
      simp
  have hfun : (fun θ : Fin 2 → ℝ => actionAtLevel β L k Finset.univ
      (perturb ![b, b'] ![unitGenerator, unitGenerator] θ (trivialField n))) =
      fun θ => (fun θ : TorusBond n → ℝ => actionAtLevel β L k Finset.univ (abelianField θ)) (ι θ) := by
    funext θ
    show actionAtLevel β L k Finset.univ _ = actionAtLevel β L k Finset.univ _
    congr 1
    funext x i
    have hsum : (∑ l : Fin 2, if (![b, b'] : Fin 2 → TorusBond n) l = (x, i) then
        θ l • (![unitGenerator, unitGenerator] : Fin 2 → imaginaryQuaternions) l
        else 0) = (ι θ (x, i)) • unitGenerator := by
      rw [Fin.sum_univ_two]
      show (if b = (x, i) then θ 0 • unitGenerator else (0 : imaginaryQuaternions)) +
        (if b' = (x, i) then θ 1 • unitGenerator else (0 : imaginaryQuaternions)) = _
      rw [hite, hite, ← add_smul]
      simp [ι]
    show expUnit _ * 1 = expUnit _
    rw [mul_one, hsum]
  unfold maxwellKernel mixedDeriv
  rw [hfun, iteratedFDeriv_two_comp_clm hdiff ι]
  simp [ι]
private def curlCLM (p : TorusPlaquette n) : (TorusBond n → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) (p.1, p.2.1) +
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) (p.1 + TorusFields.unitStep n p.2.1, p.2.2) -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) (p.1 + TorusFields.unitStep n p.2.2, p.2.1) -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) (p.1, p.2.2)
private theorem curlCLM_apply (p : TorusPlaquette n) (θ : TorusBond n → ℝ) : curlCLM p θ = curl θ p := rfl
end AbelianFields
theorem bareMaxwellForm_holds : bareMaxwellFormStatement := by
  intro β L n _ u w
  classical
  set P := plaquettesIn (Finset.univ : Finset (TorusSite n)) with hP
  set S : (TorusBond n → ℝ) → ℝ := fun θ => actionAtLevel β L 0 Finset.univ (abelianField θ) with hS
  have hSsum : S = fun θ => ∑ p ∈ P, (1 - Real.cos (curlCLM p θ)) := by
    funext θ
    show TorusFields.wilsonAction Finset.univ (abelianField θ) = _
    unfold TorusFields.wilsonAction
    exact Finset.sum_congr rfl fun p _ => plaquetteEnergy_abelianField θ p.1 p.2.1 p.2.2
  have hdiff : ContDiffAt ℝ 2 S 0 := by
    rw [hSsum]
    refine ContDiff.contDiffAt (ContDiff.sum fun p _ => ?_)
    exact contDiff_const.sub (curlCLM p).contDiff.cos
  have hfirst : ∀ θ, HasFDerivAt S (∑ p ∈ P, Real.sin (curlCLM p θ) • curlCLM p) θ := by
    intro θ
    rw [hSsum]
    refine (HasFDerivAt.fun_sum fun p _ => ?_)
    have hcos := ((curlCLM p).hasFDerivAt (x := θ)).cos
    have hsub := (hasFDerivAt_const (1 : ℝ) θ).fun_sub hcos
    have hsub' : HasFDerivAt (fun i => 1 - Real.cos (curlCLM p i))
        (-(-Real.sin (curlCLM p θ) • curlCLM p)) θ := by
      simpa using hsub
    have hneg : Real.sin (curlCLM p θ) • curlCLM p = -(-Real.sin (curlCLM p θ) • curlCLM p) := by
      ext v
      simp
    rw [hneg]
    exact hsub'
  have hfderiv : fderiv ℝ S = fun θ => ∑ p ∈ P, Real.sin (curlCLM p θ) • curlCLM p :=
    funext fun θ => (hfirst θ).fderiv
  have hsecond : HasFDerivAt (fderiv ℝ S) (∑ p ∈ P, (curlCLM p).smulRight (curlCLM p)) 0 := by
    rw [hfderiv]
    refine (HasFDerivAt.fun_sum fun p _ => ?_)
    have hsin := (((curlCLM p).hasFDerivAt (x := (0 : TorusBond n → ℝ))).sin).smul_const (curlCLM p)
    simpa using hsin
  have hbil := sum_basis_bilinear (fderiv ℝ (fderiv ℝ S) 0) u w
  unfold maxwellForm
  simp only [maxwellKernel_eq_fderiv β L 0 hdiff]
  refine hbil.trans ?_
  rw [hsecond.fderiv]
  simp [curlCLM_apply, _root_.sum_apply]
end YangMills.Construction.MomentMethod
end
