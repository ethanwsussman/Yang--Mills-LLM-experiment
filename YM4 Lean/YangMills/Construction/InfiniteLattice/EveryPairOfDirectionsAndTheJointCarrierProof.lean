import YangMills.Construction.EnergyMomentum.ArcoshCurveChord
import YangMills.Construction.InfiniteLattice.EveryPairOfDirectionsAndTheJointCarrier
import YangMills.Construction.InfiniteLattice.LinkPictureAndSitePicture
import YangMills.Construction.JointSpectrum.BorelCalculusApplications
import YangMills.Construction.JointSpectrum.BorelFunctionalCalculus
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace ENNReal ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction
open OneLoopNotation ComplexHilbert
open JointSpectrum JointSpectrum.SpectralIntegral FamilyPolynomials
namespace LatticeConventions.DirectionPairsSupport
open InfiniteLattice (GaugeField IsShiftInvariant)
section SpectralFunctions
variable {𝒦 : Type} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
  {J : Type} [Fintype J] [Nonempty J]
def coneFunction (α : J) (p : SpectralDomain J) : ℝ :=
  (1 - (p.1 : ℝ)) ^ 2 - (p.1 : ℝ) * ‖1 - (p.2 α : ℂ)‖ ^ 2
omit [Fintype J] [Nonempty J] in
theorem continuous_circleCoord (α : J) :
    Continuous fun p : SpectralDomain J => ((p.2 α : Circle) : ℂ) := by
  fun_prop
omit [Fintype J] [Nonempty J] in
theorem continuous_coneFunction (α : J) : Continuous (coneFunction α) := by
  unfold coneFunction
  fun_prop
omit [Fintype J] [Nonempty J] in
theorem abs_coneFunction_le_five (α : J) (p : SpectralDomain J) : |coneFunction α p| ≤ 5 := by
  have ht₀ : (0 : ℝ) ≤ p.1 := p.1.2.1
  have ht₁ : (p.1 : ℝ) ≤ 1 := p.1.2.2
  have hn : ‖1 - (p.2 α : ℂ)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_one, Circle.norm_coe]
    norm_num
  have hn₀ : 0 ≤ ‖1 - (p.2 α : ℂ)‖ := norm_nonneg _
  have hsq : ‖1 - (p.2 α : ℂ)‖ ^ 2 ≤ 4 := by nlinarith
  have hm : (p.1 : ℝ) * ‖1 - (p.2 α : ℂ)‖ ^ 2 ≤ 4 := by nlinarith [sq_nonneg ‖1 - (p.2 α : ℂ)‖]
  have hm₀ : 0 ≤ (p.1 : ℝ) * ‖1 - (p.2 α : ℂ)‖ ^ 2 := by positivity
  unfold coneFunction
  rw [abs_le]
  constructor <;> nlinarith
structure RepresentsOp (S : CommutingFamily 𝒦 J) (f : SpectralDomain J → ℂ)
    (C : 𝒦 →L[ℂ] 𝒦) : Prop where
  measurable : Measurable f
  domain_eq_univ : integralDomain S f = univ
  integral_eq : spectralIntegral S f = ⇑C
theorem RepresentsOp.add_smul (hcalc : BorelCalculus.BorelCalculusStatement)
    {S : CommutingFamily 𝒦 J} {f g : SpectralDomain J → ℂ} {C D : 𝒦 →L[ℂ] 𝒦}
    (hf : RepresentsOp S f C) (hg : RepresentsOp S g D) (c : ℂ) :
    RepresentsOp S (f + c • g) (C + c • D) := by
  obtain ⟨-, -, -, h₄, -⟩ := hcalc 𝒦 J S
  have hmem : ∀ ψ, ψ ∈ integralDomain S (f + c • g) ∧
      spectralIntegral S (f + c • g) ψ = spectralIntegral S f ψ + c • spectralIntegral S g ψ :=
    fun ψ => h₄ f g hf.measurable hg.measurable c ψ (hf.domain_eq_univ ▸ mem_univ ψ)
      (hg.domain_eq_univ ▸ mem_univ ψ)
  refine ⟨hf.measurable.add (hg.measurable.const_smul c), eq_univ_of_forall fun ψ => (hmem ψ).1, ?_⟩
  funext ψ
  rw [(hmem ψ).2, hf.integral_eq, hg.integral_eq]
  rfl
omit [Nonempty J] in
theorem continuous_spectralMonomial (n : ℕ) (y : J → ℤ) :
    Continuous (spectralMonomial n y : SpectralDomain J → ℂ) := by
  have h₁ : Continuous fun p : SpectralDomain J => ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  unfold spectralMonomial torusMonomial
  refine (h₁.pow n).mul (continuous_finsetProd _ fun α _ => ?_)
  exact (continuous_circleCoord α).zpow₀ (y α) fun p => Or.inl (Circle.coe_ne_zero _)
theorem representsOp_spectralMonomial (hcalc : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily 𝒦 J) (n : ℕ) (y : J → ℤ) :
    RepresentsOp S (spectralMonomial n y) (familyMonomial S n y) := by
  obtain ⟨-, -, h₃, -⟩ := hcalc 𝒦 J S
  exact ⟨(continuous_spectralMonomial n y).measurable, (h₃ n y).1, (h₃ n y).2⟩
theorem unitaryMonomial_zero (S : CommutingFamily 𝒦 J) : S.unitaryMonomial 0 = 1 := by
  unfold CommutingFamily.unitaryMonomial
  have h₁ : Finset.univ.noncommProd (fun α => S.B α ^ (0 : J → ℤ) α)
      (fun α _ α' _ _ => S.commute_zpow_unitary 0 α α') = 1 :=
    Finset.noncommProd_induction _ _ _ (fun u => u = 1)
      (fun a b ha hb => by rw [ha, hb, one_mul]) rfl (fun α _ => by simp)
  rw [h₁]
  rfl
omit [Fintype J] [Nonempty J] in
theorem noncommProd_eq_of_eq_one_of_ne {G : Type*} [Monoid G] (f : J → G) (α : J)
    (hf : ∀ β, β ≠ α → f β = 1) (t : Finset J) (comm) (hα : α ∈ t) :
    t.noncommProd f comm = f α := by
  classical
  have key : ∀ (s : Finset J) (c), α ∉ s → s.noncommProd f c = 1 := fun s c h =>
    Finset.noncommProd_induction _ _ _ (fun u => u = 1)
      (fun a b ha hb => by rw [ha, hb, one_mul]) rfl
      (fun β hβ => hf β fun e => h (e ▸ hβ))
  obtain ⟨s, hs, rfl⟩ : ∃ s, α ∉ s ∧ t = insert α s :=
    ⟨t.erase α, Finset.notMem_erase α t, (Finset.insert_erase hα).symm⟩
  rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hs, key _ _ hs, mul_one]
theorem unitaryMonomial_single [DecidableEq J] (S : CommutingFamily 𝒦 J) (α : J) (k : ℤ) :
    S.unitaryMonomial (Pi.single α k) = ((S.B α ^ k : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦) := by
  have h₁ : Finset.univ.noncommProd (fun β => S.B β ^ (Pi.single α k : J → ℤ) β)
      (fun β _ β' _ _ => S.commute_zpow_unitary (Pi.single α k) β β') = S.B α ^ k := by
    refine (noncommProd_eq_of_eq_one_of_ne _ α (fun β hβ => by simp [Pi.single_eq_of_ne hβ]) _ _
      (Finset.mem_univ α)).trans ?_
    simp
  exact congrArg Subtype.val h₁
omit [Nonempty J] in
theorem torusMonomial_single [DecidableEq J] (ζ : J → Circle) (α : J) (k : ℤ) :
    torusMonomial ζ (Pi.single α k) = (ζ α : ℂ) ^ k := by
  unfold torusMonomial
  rw [Fintype.prod_eq_single α fun β hβ => by rw [Pi.single_eq_of_ne hβ, zpow_zero]]
  rw [Pi.single_eq_same]
omit [Nonempty J] in
theorem coneFunction_eq_monomials [DecidableEq J] (α : J) :
    (fun p => ((coneFunction α p : ℝ) : ℂ)) =
      spectralMonomial 0 (0 : J → ℤ) + (-4 : ℂ) • spectralMonomial 1 (0 : J → ℤ)
        + (1 : ℂ) • spectralMonomial 2 (0 : J → ℤ)
        + (1 : ℂ) • spectralMonomial 1 (Pi.single α 1)
        + (1 : ℂ) • spectralMonomial 1 (Pi.single α (-1)) := by
  funext p
  set ζ : ℂ := (p.2 α : ℂ) with hζ
  have h₁ : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj', hζ, Circle.norm_coe]
    simp
  have h₂ : (((‖1 - ζ‖ ^ 2 : ℝ)) : ℂ) = (1 - ζ) * conj (1 - ζ) := by
    rw [Complex.mul_conj']
    push_cast
    rfl
  have h₃ : ζ⁻¹ = conj ζ := by
    rw [hζ, ← Circle.coe_inv, Circle.coe_inv_eq_conj]
  have h₀ : torusMonomial p.2 (0 : J → ℤ) = 1 := by simp [torusMonomial]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, spectralMonomial, torusMonomial_single, h₀,
    coneFunction]
  rw [← hζ, zpow_neg_one, zpow_one, h₃]
  push_cast at h₂ ⊢
  rw [h₂, map_sub, map_one]
  linear_combination (-((p.1 : ℝ) : ℂ)) * h₁
theorem representsOp_coneFunction (hcalc : BorelCalculus.BorelCalculusStatement)
    (S : CommutingFamily 𝒦 J) (α : J) :
    RepresentsOp S (fun p => ((coneFunction α p : ℝ) : ℂ))
      ((1 - S.A) ^ 2 -
        S.A * ((2 : ℂ) • (1 : 𝒦 →L[ℂ] 𝒦) - (S.B α : 𝒦 →L[ℂ] 𝒦) - star (S.B α : 𝒦 →L[ℂ] 𝒦))) := by
  classical
  have hr := ((((representsOp_spectralMonomial hcalc S 0 0).add_smul hcalc
    (representsOp_spectralMonomial hcalc S 1 0) (-4)).add_smul hcalc
    (representsOp_spectralMonomial hcalc S 2 0) 1).add_smul hcalc
    (representsOp_spectralMonomial hcalc S 1 (Pi.single α 1)) 1).add_smul hcalc
    (representsOp_spectralMonomial hcalc S 1 (Pi.single α (-1))) 1
  rw [← coneFunction_eq_monomials] at hr
  have hinv : ((S.B α ^ (-1 : ℤ) : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦) =
      star (S.B α : 𝒦 →L[ℂ] 𝒦) := by
    rw [zpow_neg_one]
    rfl
  have hone : ((S.B α ^ (1 : ℤ) : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦) = (S.B α : 𝒦 →L[ℂ] 𝒦) := by
    rw [zpow_one]
  have hop : familyMonomial S 0 0 + (-4 : ℂ) • familyMonomial S 1 0 +
      (1 : ℂ) • familyMonomial S 2 0 + (1 : ℂ) • familyMonomial S 1 (Pi.single α 1) +
      (1 : ℂ) • familyMonomial S 1 (Pi.single α (-1)) =
      (1 - S.A) ^ 2 -
        S.A * ((2 : ℂ) • (1 : 𝒦 →L[ℂ] 𝒦) - (S.B α : 𝒦 →L[ℂ] 𝒦) - star (S.B α : 𝒦 →L[ℂ] 𝒦)) := by
    simp only [familyMonomial, unitaryMonomial_zero, unitaryMonomial_single, hinv, hone, pow_zero,
      pow_one, mul_one, pow_two, mul_sub, sub_mul, one_mul, mul_smul_comm]
    module
  rwa [hop] at hr
theorem measure_coneFunction_neg_eq_zero (hcalc : BorelCalculus.BorelCalculusStatement)
    (huses : CalculusApplications.CalculusApplicationsStatement) (S : CommutingFamily 𝒦 J) (α : J)
    {T U : 𝒦 →L[ℂ] 𝒦} (hA : S.A = T) (hB : (S.B α : 𝒦 →L[ℂ] 𝒦) = U)
    (h : OpGE ((idOp 𝒦 - T) ^ 2)
      (T * ((2 : ℂ) • idOp 𝒦 - U - ContinuousLinearMap.adjoint U))) :
    jointSpectralMeasure S {p | coneFunction α p < 0} = 0 := by
  subst hA hB
  obtain ⟨ha, -⟩ := huses 𝒦 J S
  obtain ⟨C, hC, -, hiff⟩ := ha (coneFunction α) (continuous_coneFunction α).measurable
    ⟨5, abs_coneFunction_le_five α⟩
  have hCD := DFunLike.coe_injective (hC.trans (representsOp_coneFunction hcalc S α).integral_eq)
  apply hiff.mp
  rw [hCD]
  exact sub_nonneg.mpr (le_of_opLE h)
end SpectralFunctions
section SiteSide
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
theorem opLE_of_re_nonneg {B B' : BddOp H} (hB : IsSymmetricOp B)
    (hB' : IsSymmetricOp B') (h : ∀ ψ, 0 ≤ (⟪ψ, (B' - B) ψ⟫_ℂ).re) : OpLE B B' := by
  refine ⟨hB, hB', fun ψ => Complex.le_def.mpr ⟨?_, ?_⟩⟩
  · have := h ψ
    rw [sub_apply, inner_sub_right, Complex.sub_re] at this
    linarith
  · rw [hB.inner_self_apply_im_eq_zero, hB'.inner_self_apply_im_eq_zero]
theorem cone_transfer_of_intertwiner (T U : BddOp H) (T' U' : BddOp H')
    (hT : IsSymmetricOp T) (hU : U ∈ unitary (H →L[ℂ] H)) (hTU : Commute T U)
    (hU' : U' ∈ unitary (H' →L[ℂ] H'))
    (hcone : OpGE ((idOp H' - T') ^ 2)
      (T' * ((2 : ℂ) • idOp H' - U' - ContinuousLinearMap.adjoint U')))
    (W : H' →L[ℂ] H) (hWT : W.comp T' = T.comp W) (hWU : W.comp U' = U.comp W)
    (K : Submodule ℂ H) (hK : ∀ χ, χ ∈ K ↔ T χ = 0)
    (W₀ : H' →ₗ[ℂ] ↥Kᗮ) (hW₀ : ∀ ψ, (W₀ ψ : H) = W ψ)
    (hun : IsUnitaryMap W₀) :
    OpGE ((idOp H - T) ^ 2)
      (T * ((2 : ℂ) • idOp H - U - ContinuousLinearMap.adjoint U)) := by
  have hTs : IsSelfAdjoint T := (isSymmetricOp_iff T).mp hT
  have hUsU : star U * U = 1 := (Unitary.mem_iff.mp hU).1
  have hU'U's : U' * star U' = 1 := (Unitary.mem_iff.mp hU').2
  have hTUs : Commute T (star U) := by
    have := hTU.star_star
    rwa [hTs.star_eq] at this
  set X : BddOp H := (2 : ℂ) • idOp H - U - ContinuousLinearMap.adjoint U
    with hX
  have hXstar : star X = X := by
    rw [hX, ← ContinuousLinearMap.star_eq_adjoint]
    simp only [star_sub, star_smul, star_star]
    have h₂ : star (idOp H) = idOp H := star_one _
    rw [h₂]
    simp only [Complex.star_def, map_ofNat]
    abel
  have hcomX : Commute T X := by
    rw [hX, ← ContinuousLinearMap.star_eq_adjoint]
    refine (Commute.sub_right ?_ hTU).sub_right hTUs
    exact Commute.smul_right (Commute.one_right T) 2
  have hleft : IsSymmetricOp (T * X) := by
    rw [isSymmetricOp_iff]
    change star (T * X) = T * X
    rw [star_mul, hXstar, hTs.star_eq]
    exact hcomX.eq.symm
  have hright : IsSymmetricOp ((idOp H - T) ^ 2) := by
    rw [isSymmetricOp_iff]
    exact ((IsSelfAdjoint.one _).sub hTs).pow 2
  refine opLE_of_re_nonneg hleft hright fun ψ => ?_
  set D' : BddOp H' := (idOp H' - T') ^ 2 -
    T' * ((2 : ℂ) • idOp H' - U' - ContinuousLinearMap.adjoint U') with hD'
  have hD'pos : ∀ φ, 0 ≤ (⟪φ, D' φ⟫_ℂ).re := fun φ => by
    have h := (Complex.le_def.mp (hcone.le φ)).1
    rw [hD', sub_apply, inner_sub_right, Complex.sub_re]
    linarith
  have hWTφ : ∀ φ, W (T' φ) = T (W φ) := fun φ => congrArg (fun Z : H' →L[ℂ] H => Z φ) hWT
  have hWUφ : ∀ φ, W (U' φ) = U (W φ) := fun φ => congrArg (fun Z : H' →L[ℂ] H => Z φ) hWU
  have hWUsφ : ∀ φ, W (ContinuousLinearMap.adjoint U' φ) = ContinuousLinearMap.adjoint U (W φ) := by
    intro φ
    rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint]
    have e₁ : star U (U (W (star U' φ))) = W (star U' φ) :=
      congrArg (fun Z : H →L[ℂ] H => Z (W (star U' φ))) hUsU
    have e₂ : U' (star U' φ) = φ := congrArg (fun Z : H' →L[ℂ] H' => Z φ) hU'U's
    rw [← e₁, ← hWUφ, e₂]
  have hDW : ∀ φ, ((idOp H - T) ^ 2 - T * X) (W φ) = W (D' φ) := by
    intro φ
    simp only [hD', hX, pow_two, sub_apply, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul,
      hWTφ, hWUφ, hWUsφ]
  have hKclosed : IsClosed (K : Set H) := by
    have : (K : Set H) = T ⁻¹' {0} := by
      ext x
      exact hK x
    rw [this]
    exact isClosed_singleton.preimage T.continuous
  have : CompleteSpace K := hKclosed.completeSpace_coe
  obtain ⟨ψ₀, hψ₀, ψ₁, hψ₁, rfl⟩ := K.exists_add_mem_mem_orthogonal ψ
  obtain ⟨φ, hφ⟩ := hun.onto ⟨ψ₁, hψ₁⟩
  have hψ₁W : ψ₁ = W φ := by
    rw [← hW₀, hφ]
  have hTψ₀ : T ψ₀ = 0 := (hK ψ₀).mp hψ₀
  have hDψ₀ : ((idOp H - T) ^ 2 - T * X) ψ₀ = ψ₀ := by
    have h₁ : (T * X) ψ₀ = 0 := by
      rw [hcomX.eq]
      change X (T ψ₀) = 0
      rw [hTψ₀, map_zero]
    rw [sub_apply, h₁, sub_zero, pow_two]
    change (idOp H - T) ((idOp H - T) ψ₀) = ψ₀
    simp [hTψ₀]
  have hrange : ∀ χ, W χ ∈ Kᗮ := fun χ => by
    rw [← hW₀]
    exact (W₀ χ).2
  have horth : ∀ χ, ⟪ψ₀, W χ⟫_ℂ = 0 := fun χ =>
    (Submodule.mem_orthogonal K _).mp (hrange χ) ψ₀ hψ₀
  have horth' : ∀ χ, ⟪W χ, ψ₀⟫_ℂ = 0 := fun χ => by
    rw [← inner_conj_symm, horth, map_zero]
  have hiso : ∀ χ χ', ⟪W χ, W χ'⟫_ℂ = ⟪χ, χ'⟫_ℂ := fun χ χ' => by
    rw [← hW₀, ← hW₀, ← Submodule.coe_inner]
    exact (⟨W₀, hun.isometric⟩ : H' →ₗᵢ[ℂ] ↥Kᗮ).inner_map_map χ χ'
  rw [map_add, hDψ₀, hψ₁W, hDW, inner_add_left, inner_add_right, inner_add_right, horth, horth',
    hiso]
  simp only [zero_add, add_zero, Complex.add_re]
  have h₀ : 0 ≤ (⟪ψ₀, ψ₀⟫_ℂ).re := inner_self_nonneg (𝕜 := ℂ)
  have := hD'pos φ
  linarith
end SiteSide
section Supports
variable {μ : Direction}
theorem energyOfTime_toReal {t : unitInterval} (ht : 0 < (t : ℝ)) :
    (energyOfTime t).toReal = -Real.log (t : ℝ) := by
  have h₀ : 0 ≤ -Real.log (t : ℝ) := neg_nonneg.mpr (Real.log_nonpos ht.le t.2.2)
  unfold energyOfTime
  rw [if_neg ht.ne', ENNReal.toReal_ofReal h₀]
theorem exp_I_mul_momentumAngle (ζ : TransverseDirection μ → Circle) (l : TransverseDirection μ) :
    Complex.exp (Complex.I * (momentumAngle ζ l : ℂ)) = (ζ l : ℂ) := by
  have h := Complex.norm_mul_exp_arg_mul_I (ζ l : ℂ)
  rw [Circle.norm_coe] at h
  simpa [momentumAngle, principalArg, mul_comm] using h
theorem cosh_add_cos_iff (hcurve : EnergyMomentum.ArcoshCurve.Statement)
    (p : SpectralDomain (TransverseDirection μ)) (ht : 0 < (p.1 : ℝ)) (l : TransverseDirection μ) :
    (2 ≤ Real.cosh (energyOfTime p.1).toReal + Real.cos (momentumAngle p.2 l) ↔
      0 ≤ coneFunction l p) ∧
    (2 ≤ Real.cosh (energyOfTime p.1).toReal + Real.cos (momentumAngle p.2 l) →
      EnergyMomentum.chordSlopeConstant * |momentumAngle p.2 l| ≤ (energyOfTime p.1).toReal) := by
  obtain ⟨-, hEq, -⟩ := hcurve
  have h := hEq (p.1 : ℝ) ⟨ht, p.1.2.2⟩ (momentumAngle p.2 l)
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  dsimp only at h
  rw [exp_I_mul_momentumAngle] at h
  obtain ⟨-, h₁, h₂, -, -, -, h₃, -⟩ := h
  rw [energyOfTime_toReal ht]
  refine ⟨?_, h₃⟩
  rw [coneFunction, sub_nonneg]
  exact (h₁.trans h₂).symm
theorem coshCosRegion_eq (hcurve : EnergyMomentum.ArcoshCurve.Statement) :
    coshCosRegion μ = {p | 0 < (p.1 : ℝ)} ∩ ⋂ l, {p | 0 ≤ coneFunction l p} := by
  ext p
  simp only [coshCosRegion, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  refine and_congr_right fun ht => forall_congr' fun l => (cosh_add_cos_iff hcurve p ht l).1
theorem measurableSet_coshCosRegion (hcurve : EnergyMomentum.ArcoshCurve.Statement) :
    MeasurableSet (coshCosRegion μ) := by
  rw [coshCosRegion_eq hcurve]
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun l => ?_)
  · exact measurableSet_lt measurable_const
      (continuous_subtype_val.comp continuous_fst).measurable
  · exact measurableSet_le measurable_const (continuous_coneFunction l).measurable
theorem measurableSet_zeroTimeSet : MeasurableSet (zeroTimeSet μ) :=
  measurableSet_eq_fun (continuous_subtype_val.comp continuous_fst).measurable measurable_const
theorem coshCosRegion_subset_linearConeRegion (hcurve : EnergyMomentum.ArcoshCurve.Statement) :
    coshCosRegion μ ⊆ linearConeRegion μ := by
  rintro p ⟨ht, hp⟩
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    fun l => |momentumAngle p.2 l|
  have h := (cosh_add_cos_iff hcurve p ht l).2 (hp l)
  have hE : energyOfTime p.1 = ENNReal.ofReal (energyOfTime p.1).toReal := by
    unfold energyOfTime
    rw [if_neg ht.ne', ENNReal.toReal_ofReal (neg_nonneg.mpr (Real.log_nonpos ht.le p.1.2.2))]
  change ENNReal.ofReal (EnergyMomentum.chordSlopeConstant * supAngle p.2) ≤ energyOfTime p.1
  rw [hE, supAngle, hl]
  exact ENNReal.ofReal_le_ofReal h
theorem compl_coshCosRegion_union_zeroTimeSet (hcurve : EnergyMomentum.ArcoshCurve.Statement) :
    (coshCosRegion μ ∪ zeroTimeSet μ)ᶜ =
      ⋃₀ range fun l : TransverseDirection μ => {p | coneFunction l p < 0} := by
  ext p
  simp only [sUnion_range, mem_iUnion, mem_compl_iff, mem_union, mem_ofPred_eq, not_or]
  constructor
  · rintro ⟨h₁, h₂⟩
    have ht : 0 < (p.1 : ℝ) := lt_of_le_of_ne p.1.2.1 (Ne.symm h₂)
    rw [coshCosRegion_eq hcurve] at h₁
    simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq, not_and, not_forall, not_le] at h₁
    exact h₁ ht
  · rintro ⟨l, hl⟩
    have ht : (p.1 : ℝ) ≠ 0 := by
      intro h
      simp [coneFunction, h] at hl
      linarith [sq_nonneg (1 : ℝ)]
    refine ⟨fun h => ?_, ht⟩
    rw [coshCosRegion_eq hcurve] at h
    exact absurd (mem_iInter.mp h.2 l) (not_le.mpr hl)
theorem compl_coshCosRegion (hcurve : EnergyMomentum.ArcoshCurve.Statement) :
    (coshCosRegion μ)ᶜ =
      ⋃₀ insert {p | (p.1 : ℝ) = 0}
        (range fun l : TransverseDirection μ => {p | coneFunction l p < 0}) := by
  rw [sUnion_insert, ← compl_coshCosRegion_union_zeroTimeSet hcurve]
  ext p
  constructor
  · intro h
    by_cases h₀ : (p.1 : ℝ) = 0
    · exact Or.inl h₀
    · refine Or.inr ?_
      rintro (h₁ | h₂)
      · exact h h₁
      · exact h₀ h₂
  · rintro (h₀ | h₁) hc
    · exact hc.1.ne' h₀
    · exact h₁ (Or.inl hc)
end Supports
section MainResults
variable (a : Spacing) {ν : Measure (GaugeField (a : ℝ))} [IsProbabilityMeasure ν]
theorem isAdmissibleState_of_pairConditions {μ lam : Direction} {hne : μ ≠ lam}
    (h : PairConditions hne ν) : LinkFrame.IsAdmissibleState a μ ν :=
  ⟨h.1, h.2.1⟩
theorem pairConditions_of_reflectionPositive {μ lam : Direction} (hne : μ ≠ lam)
    (hti : IsShiftInvariant ν) (hrp : IsReflectionPositiveAtEveryMirror ν) :
    PairConditions hne ν :=
  ⟨hti, fun _ => hrp _ _, fun _ => hrp _ _⟩
theorem site_cone_opGE (hcone : LinkConeInequality)
    (hls : LinkSiteComparison.Statement)
    (hmatrix : CoordinatePictureOperators)
    {μ lam : Direction} (hne : μ ≠ lam) (h : PairConditions hne ν) :
    OpGE
      ((idOp (SiteFrame.SiteHilbertSpace a μ ν) - SiteFrame.transferOperator a μ ν) ^ 2)
      (SiteFrame.transferOperator a μ ν *
        ((2 : ℂ) • idOp (SiteFrame.SiteHilbertSpace a μ ν)
          - SiteFrame.transverseShift a μ ν ⟨lam, hne.symm⟩
          - ContinuousLinearMap.adjoint (SiteFrame.transverseShift a μ ν ⟨lam, hne.symm⟩))) := by
  have hst := isAdmissibleState_of_pairConditions a h
  obtain ⟨-, hL, hS⟩ := hmatrix a μ ν hst
  obtain ⟨-, ⟨-, -, -, ⟨W₀, hW₀, hun⟩, hWT, hWU⟩, -⟩ := hls a μ ν hst
  have hLs := LinkFrame.TransferMatrixElements.isCommutingFamilyData hL
  have hSs := SiteFrame.TransferMatrixElements.isCommutingFamilyData hS
  exact cone_transfer_of_intertwiner _ _ _ _ hSs.isSymmetric
    (mem_unitary_of_isUnitaryMap (hSs.unitary _)) (hSs.commute_T_U _)
    (mem_unitary_of_isUnitaryMap (hLs.unitary _)) (hcone a μ lam hne ν h).1
    _ hWT (hWU _)
    (LinearMap.ker (SiteFrame.transferOperator a μ ν :
      SiteFrame.SiteHilbertSpace a μ ν →ₗ[ℂ] SiteFrame.SiteHilbertSpace a μ ν))
    (fun _ => Iff.rfl) W₀ hW₀ hun
theorem siteConeInequality_of_pairConditions (hcone : LinkConeInequality)
    (hls : LinkSiteComparison.Statement)
    (hmatrix : CoordinatePictureOperators)
    (hcalc : BorelCalculus.BorelCalculusStatement)
    (huses : CalculusApplications.CalculusApplicationsStatement)
    {μ lam : Direction} (hne : μ ≠ lam) (h : PairConditions hne ν) :
    SiteConeInequality a hne ν := by
  have habove := site_cone_opGE a hcone hls hmatrix hne h
  refine ⟨habove, ?_, ?_⟩
  · have hset : coneInteriorOf (SingleTransverse (μ := μ) ⟨lam, hne.symm⟩) =
        {p | 0 ≤ coneFunction default p} := by
      ext p
      simp only [coneInteriorOf, mem_ofPred_eq, coneFunction, ge_iff_le, sub_nonneg]
    rw [hset]
    exact measurableSet_le measurable_const (continuous_coneFunction _).measurable
  · have hst := isAdmissibleState_of_pairConditions a h
    obtain ⟨-, -, hS⟩ := hmatrix a μ ν hst
    have hop := SiteFrame.TransferMatrixElements.singleShiftFamily_ops hS
      (⟨lam, hne.symm⟩ : TransverseDirection μ)
    have hnull := measure_coneFunction_neg_eq_zero hcalc huses
      (SiteFrame.singleShiftFamily a μ ν ⟨lam, hne.symm⟩) default hop.1 (hop.2 default) habove
    have hset : (coneInteriorOf (SingleTransverse (μ := μ) ⟨lam, hne.symm⟩))ᶜ =
        {p | coneFunction default p < 0} := by
      ext p
      simp only [coneInteriorOf, mem_compl_iff, mem_ofPred_eq, coneFunction, ge_iff_le, not_le,
        sub_neg]
    rw [hset]
    exact hnull
theorem jointSupport_of_reflectionPositive (hcone : LinkConeInequality)
    (hls : LinkSiteComparison.Statement)
    (hmatrix : CoordinatePictureOperators)
    (hcalc : BorelCalculus.BorelCalculusStatement)
    (huses : CalculusApplications.CalculusApplicationsStatement)
    (hcurve : EnergyMomentum.ArcoshCurve.Statement)
    (hti : IsShiftInvariant ν) (hrp : IsReflectionPositiveAtEveryMirror ν)
    (μ : Direction) : JointSupport a μ ν := by
  have hst : LinkFrame.IsAdmissibleState a μ ν := ⟨hti, fun _ => hrp _ _⟩
  obtain ⟨-, hL, hS⟩ := hmatrix a μ ν hst
  obtain ⟨-, -, hinj⟩ := hls a μ ν hst
  have hopL := LinkFrame.TransferMatrixElements.allShiftsFamily_ops hL
  have hopS := SiteFrame.TransferMatrixElements.allShiftsFamily_ops hS
  have hnullL : ∀ l : TransverseDirection μ,
      jointSpectralMeasure (LinkFrame.allShiftsFamily a μ ν) {p | coneFunction l p < 0} = 0 :=
    fun l => measure_coneFunction_neg_eq_zero hcalc huses _ l hopL.1 (hopL.2 l)
      (hcone a μ l.1 l.2.symm ν (pairConditions_of_reflectionPositive a l.2.symm hti hrp)).1
  have hnullS : ∀ l : TransverseDirection μ,
      jointSpectralMeasure (SiteFrame.allShiftsFamily a μ ν) {p | coneFunction l p < 0} = 0 :=
    fun l => measure_coneFunction_neg_eq_zero hcalc huses _ l hopS.1 (hopS.2 l)
      (site_cone_opGE a hcone hls hmatrix l.2.symm
        (pairConditions_of_reflectionPositive a l.2.symm hti hrp))
  have hmeas : ∀ l : TransverseDirection μ,
      MeasurableSet {p : SpectralDomain (TransverseDirection μ) | coneFunction l p < 0} :=
    fun l => measurableSet_lt (continuous_coneFunction l).measurable measurable_const
  have hzero : jointSpectralMeasure (LinkFrame.allShiftsFamily a μ ν)
      {p | (p.1 : ℝ) = 0} = 0 := by
    obtain ⟨-, -, ⟨P, hP, -, hrange⟩, -⟩ := huses _ _ (LinkFrame.allShiftsFamily a μ ν)
    rw [← hP]
    funext ψ
    have hmem : P ψ ∈ LatticeBasics.nullSet (LinkFrame.allShiftsFamily a μ ν).A := by
      rw [← hrange]
      exact mem_range_self ψ
    have hk : LinkFrame.transferOperator a μ ν (P ψ) = 0 := by
      have : (LinkFrame.allShiftsFamily a μ ν).A (P ψ) = 0 := hmem
      rwa [hopL.1] at this
    have hk' : P ψ ∈ linearKer (LinkFrame.transferOperator a μ ν :
        LinkFrame.LinkHilbertSpace a μ ν →ₗ[ℂ] LinkFrame.LinkHilbertSpace a μ ν) := hk
    rw [hinj] at hk'
    exact hk'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hunionL, -⟩ :=
    hcalc _ _ (LinkFrame.allShiftsFamily a μ ν)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hunionS, -⟩ :=
    hcalc _ _ (SiteFrame.allShiftsFamily a μ ν)
  refine ⟨⟨measurableSet_coshCosRegion hcurve, ?_⟩, coshCosRegion_subset_linearConeRegion hcurve,
    ⟨(measurableSet_coshCosRegion hcurve).union measurableSet_zeroTimeSet, ?_⟩, ?_⟩
  · change jointSpectralMeasure (LinkFrame.allShiftsFamily a μ ν) (coshCosRegion μ)ᶜ = 0
    rw [compl_coshCosRegion hcurve]
    refine (hunionL _ ((countable_range _).insert _) ?_).2
    rintro T (rfl | ⟨l, rfl⟩)
    · exact ⟨measurableSet_zeroTimeSet, hzero⟩
    · exact ⟨hmeas l, hnullL l⟩
  · change jointSpectralMeasure (SiteFrame.allShiftsFamily a μ ν)
      (coshCosRegion μ ∪ zeroTimeSet μ)ᶜ = 0
    rw [compl_coshCosRegion_union_zeroTimeSet hcurve]
    refine (hunionS _ (countable_range _) ?_).2
    rintro T ⟨l, rfl⟩
    exact ⟨hmeas l, hnullS l⟩
  · intro p hp
    have hp' : (p.1 : ℝ) = 0 := hp
    simp [energyOfTime, hp']
end MainResults
theorem pairwiseConeAndJointSupport_holds (hcone : LinkConeInequality)
    (hls : LinkSiteComparison.Statement)
    (hmatrix : CoordinatePictureOperators)
    (hcalc : BorelCalculus.BorelCalculusStatement)
    (huses : CalculusApplications.CalculusApplicationsStatement)
    (hcurve : EnergyMomentum.ArcoshCurve.Statement) : PairwiseConeAndJointSupport :=
  ⟨⟨hcone, fun a _ _ hne _ _ h =>
      siteConeInequality_of_pairConditions a hcone hls hmatrix hcalc huses hne h⟩,
    fun a _ _ hti hrp μ =>
      jointSupport_of_reflectionPositive a hcone hls hmatrix hcalc huses hcurve hti hrp μ⟩
end LatticeConventions.DirectionPairsSupport
end YangMills.Construction
end
