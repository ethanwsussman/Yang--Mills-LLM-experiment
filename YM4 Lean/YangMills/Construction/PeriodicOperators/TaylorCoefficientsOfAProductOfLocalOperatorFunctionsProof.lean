import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunctionProof
import YangMills.Construction.PeriodicOperators.ProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfAProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsReadOnALargerSetOfIndices
import Mathlib
set_option autoImplicit false
open Set Filter Topology Asymptotics
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LeibnizRuleProof
open TorusMetric (euclidNormVec)
open Coordinates (ComplexCoordinates)
open Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
section SecondOrder
variable {n : ℕ}
theorem linearForm_isBigO_norm (φ : ComplexCoordinates n →ₗ[ℂ] ℂ) :
    (fun w => φ w) =O[𝓝 0] fun w : ComplexCoordinates n => ‖w‖ :=
  ((LinearMap.toContinuousLinearMap φ).isBigO_id (𝓝 0)).norm_right
theorem bilinearDiag_isBigO_sq (β : ComplexCoordinates n →ₗ[ℂ] ComplexCoordinates n →ₗ[ℂ] ℂ) :
    (fun w => β w w) =O[𝓝 0] fun w : ComplexCoordinates n => ‖w‖ ^ 2 := by
  let B : ComplexCoordinates n →L[ℂ] ComplexCoordinates n →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (ComplexCoordinates n →ₗ[ℂ] ℂ) ≃ₗ[ℂ] ComplexCoordinates n →L[ℂ] ℂ).toLinearMap ∘ₗ β)
  refine IsBigO.of_bound ‖B‖ (Eventually.of_forall fun w => ?_)
  have hw : β w w = B w w := rfl
  rw [hw, norm_pow, norm_norm]
  calc ‖B w w‖ ≤ ‖B‖ * ‖w‖ * ‖w‖ := B.le_opNorm₂ w w
    _ = ‖B‖ * ‖w‖ ^ 2 := by ring
theorem norm_pow_succ_isBigO (k : ℕ) :
    (fun w : ComplexCoordinates n => ‖w‖ ^ (k + 1)) =O[𝓝 0]
      fun w : ComplexCoordinates n => ‖w‖ ^ k := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ComplexCoordinates n) one_pos] with w hw
  have hw1 : ‖w‖ ≤ 1 := (mem_ball_zero_iff.1 hw).le
  rw [norm_pow, norm_pow, norm_norm, one_mul, pow_succ]
  exact mul_le_of_le_one_right (by positivity) hw1
def symmTensor (φ ψ : ComplexCoordinates n →ₗ[ℂ] ℂ) :
    ComplexCoordinates n →ₗ[ℂ] ComplexCoordinates n →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun w w' => φ w * ψ w' + ψ w * φ w')
    (fun w v w' => by simp only [map_add]; ring)
    (fun c w w' => by simp only [map_smul, smul_eq_mul]; ring)
    (fun w w' v => by simp only [map_add]; ring)
    (fun c w w' => by simp only [map_smul, smul_eq_mul]; ring)
@[simp] theorem symmTensor_apply (φ ψ : ComplexCoordinates n →ₗ[ℂ] ℂ) (w w' : ComplexCoordinates n) :
    symmTensor φ ψ w w' = φ w * ψ w' + ψ w * φ w' := rfl
variable {f g : ComplexCoordinates n → ℂ} {φ ψ : ComplexCoordinates n →ₗ[ℂ] ℂ}
  {β γ : ComplexCoordinates n →ₗ[ℂ] ComplexCoordinates n →ₗ[ℂ] ℂ}
theorem secondOrder_congr (he : f =ᶠ[𝓝 0] g) (hf : IsSecondOrderExpansion f φ β) :
    IsSecondOrderExpansion g φ β := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.secondOrder_congr <;> assumption
theorem secondOrder_add (hf : IsSecondOrderExpansion f φ β) (hg : IsSecondOrderExpansion g ψ γ) :
    IsSecondOrderExpansion (fun w => f w + g w) (φ + ψ) (β + γ) := by
  refine ⟨fun w w' => ?_, (hf.2.add hg.2).congr_left fun w => ?_⟩
  · simp only [LinearMap.add_apply, hf.1 w w', hg.1 w w']
  · simp only [LinearMap.add_apply]
    ring
theorem secondOrder_sum {α : Type} (s : Finset α) {h : α → ComplexCoordinates n → ℂ}
    {p : α → ComplexCoordinates n →ₗ[ℂ] ℂ}
    {b : α → ComplexCoordinates n →ₗ[ℂ] ComplexCoordinates n →ₗ[ℂ] ℂ}
    (hh : ∀ a ∈ s, IsSecondOrderExpansion (h a) (p a) (b a)) :
    IsSecondOrderExpansion (fun w => ∑ a ∈ s, h a w) (∑ a ∈ s, p a) (∑ a ∈ s, b a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun w w' => by simp, ?_⟩
    simpa using isBigO_zero (fun w : ComplexCoordinates n => ‖w‖ ^ 3) (𝓝 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact secondOrder_add (hh a (Finset.mem_insert_self a s))
      (ih fun c hc => hh c (Finset.mem_insert_of_mem hc))
theorem secondOrder_mul (hf : IsSecondOrderExpansion f φ β) (hg : IsSecondOrderExpansion g ψ γ) :
    IsSecondOrderExpansion (fun w => f w * g w) (f 0 • ψ + g 0 • φ)
      (f 0 • γ + g 0 • β + symmTensor φ ψ) := by
  refine ⟨fun w w' => ?_, ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, symmTensor_apply, hf.1 w w', hg.1 w w']
    ring
  · have hrf := hf.2
    have hrg := hg.2
    have hφ := linearForm_isBigO_norm φ
    have hψ := linearForm_isBigO_norm ψ
    have hu : (fun w => (1 / 2 : ℂ) * β w w + (f w - (f 0 + φ w + (1 / 2 : ℂ) * β w w)))
        =O[𝓝 0] fun w : ComplexCoordinates n => ‖w‖ ^ 2 :=
      ((bilinearDiag_isBigO_sq β).const_mul_left _).add (hrf.trans (norm_pow_succ_isBigO 2))
    have hv : (fun w => (1 / 2 : ℂ) * γ w w + (g w - (g 0 + ψ w + (1 / 2 : ℂ) * γ w w)))
        =O[𝓝 0] fun w : ComplexCoordinates n => ‖w‖ ^ 2 :=
      ((bilinearDiag_isBigO_sq γ).const_mul_left _).add (hrg.trans (norm_pow_succ_isBigO 2))
    have hv1 : (fun w => (1 / 2 : ℂ) * γ w w + (g w - (g 0 + ψ w + (1 / 2 : ℂ) * γ w w)))
        =O[𝓝 0] fun w : ComplexCoordinates n => ‖w‖ ^ 1 :=
      hv.trans (norm_pow_succ_isBigO 1)
    have h3 := (hφ.mul hv).congr_right (g₂ := fun w : ComplexCoordinates n => ‖w‖ ^ 3)
      fun w => by ring
    have h4 := (hu.mul hψ).congr_right (g₂ := fun w : ComplexCoordinates n => ‖w‖ ^ 3)
      fun w => by ring
    have h5 := (hu.mul hv1).congr_right (g₂ := fun w : ComplexCoordinates n => ‖w‖ ^ 3)
      fun w => by ring
    refine ((((hrg.const_mul_left (f 0)).add (hrf.const_mul_left (g 0))).add h3).add h4 |>.add
      h5).congr_left fun w => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, symmTensor_apply, smul_eq_mul]
    ring
end SecondOrder
section Extension
variable {F : PeriodicData}
theorem norm_fieldExtend_le {S : Set F.Carrier} {n : ℕ} (e : Fin n ≃ S) (w : ComplexCoordinates n)
    (κ : F.Carrier) : ‖fieldExtend e w κ‖ ≤ ‖w‖ := by apply _root_.YangMills.Construction.PeriodicOperators.LocalTorusMatrices.norm_fieldExtend_le <;> assumption
theorem fieldExtend_zero {S : Set F.Carrier} {n : ℕ} (e : Fin n ≃ S) :
    fieldExtend e (0 : ComplexCoordinates n) = 0 := by
  funext κ
  have hinj : Function.Injective fun j => ((e j : S) : F.Carrier) :=
    Subtype.val_injective.comp e.injective
  by_cases h : ∃ j, ((e j : S) : F.Carrier) = κ
  · obtain ⟨j, rfl⟩ := h
    exact hinj.extend_apply _ 0 j
  · exact Function.extend_apply' _ _ _ h
end Extension
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem leibnizRule (hSup : CoeffsOnSuperset.Claim)
    (hTay : LocalOpFunTaylor.Claim)
    (hPar : ParameterIndependence.Claim)
    (hComp : OpFunComp.LocalClosed)
    (hRange : CovariantFiniteRange.Claim) : LeibnizRule.Claim := by
  intro F I I' I'' hF hI hI' hI'' T S hT hS ζ ζ'
  obtain ⟨ρT, RT₀, hT₀⟩ := id hT
  obtain ⟨ρS, RS₀, hS₀⟩ := id hS
  obtain ⟨ρP, RP₀, hP₀⟩ := hComp F I I' I'' hF hI hI' hI'' T S hT hS
  obtain ⟨RT, hRT⟩ : ∃ RT, RT = max RT₀ 0 := ⟨_, rfl⟩
  obtain ⟨RS, hRS⟩ : ∃ RS, RS = max RS₀ 0 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = max RP₀ (RT + RS) := ⟨_, rfl⟩
  have hRS0 : 0 ≤ RS := hRS ▸ le_max_right _ _
  have hRge : RT + RS ≤ R := hR ▸ le_max_right _ _
  have hTm : IsLocalWith F I I' T ρT RT :=
    (hPar F I I' hF hI hI' T ρT RT₀ ρT RT₀ hT₀ hT₀).1.1 ρT RT hT₀.radius_pos le_rfl
      (hRT ▸ le_max_left _ _)
  have hSm : IsLocalWith F I'' I S ρS RS :=
    (hPar F I'' I hF hI'' hI S ρS RS₀ ρS RS₀ hS₀ hS₀).1.1 ρS RS hS₀.radius_pos le_rfl
      (hRS ▸ le_max_left _ _)
  have hPm : IsLocalWith F I'' I' (opFunComp T S) ρP R :=
    (hPar F I'' I' hF hI'' hI' _ ρP RP₀ ρP RP₀ hP₀ hP₀).1.1 ρP R hP₀.radius_pos le_rfl
      (hR ▸ le_max_left _ _)
  have key : ∀ (ι' : I'.Carrier) (ι'' : I''.Carrier),
      coeffOne F I'' I' (opFunComp T S) ζ ι' ι'' =
          compKernel (coeffOne F I I' T ζ) (coeffZero F I'' I S) ι' ι'' +
            compKernel (coeffZero F I I' T) (coeffOne F I'' I S ζ) ι' ι'' ∧
        coeffTwo F I'' I' (opFunComp T S) ζ ζ' ι' ι'' =
          compKernel (coeffTwo F I I' T ζ ζ') (coeffZero F I'' I S) ι' ι'' +
            compKernel (coeffZero F I I' T) (coeffTwo F I'' I S ζ ζ') ι' ι'' +
            compKernel (coeffOne F I I' T ζ) (coeffOne F I'' I S ζ') ι' ι'' +
            compKernel (coeffOne F I I' T ζ') (coeffOne F I'' I S ζ) ι' ι'' := by
    intro ι' ι''
    have hAfin : (nearIndices F (I'.pos ι') R).Finite := (hRange.1 F hF).1 _ _
    have := hAfin.fintype
    obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (Fin n ≃ nearIndices F (I'.pos ι') R) :=
      ⟨_, ⟨(Fintype.equivFin _).symm⟩⟩
    have hMfin : (nearIndices I (I'.pos ι') RT).Finite := (hRange.1 I hI).1 _ _
    obtain ⟨M, hM⟩ : ∃ M : Finset I.Carrier, ∀ ι, ι ∈ M ↔
        euclidNormVec (I.pos ι - I'.pos ι') ≤ RT :=
      ⟨hMfin.toFinset, fun ι => by simp [nearIndices]⟩
    have hsubT : nearIndices F (I'.pos ι') RT ⊆ nearIndices F (I'.pos ι') R :=
      fun κ (hκ : euclidNormVec _ ≤ RT) =>
        show euclidNormVec _ ≤ R by linarith
    have hsubS : ∀ ι ∈ M, nearIndices F (I.pos ι) RS ⊆ nearIndices F (I'.pos ι') R := by
      intro ι hι κ (hκ : euclidNormVec _ ≤ RS)
      show euclidNormVec _ ≤ R
      have h1 := euclidNormVec_add_le (F.pos κ - I.pos ι) (I.pos ι - I'.pos ι')
      rw [sub_add_sub_cancel] at h1
      have h2 := (hM ι).1 hι
      linarith
    have hTf := fun ι => hSup F I I' hF hI hI' T ρT RT hTm ι' ι _ n e hsubT
    choose p b hp1 hp2 hp3 using hTf
    have hSf := fun (ι : I.Carrier) (hι : ι ∈ M) =>
      hSup F I'' I hF hI'' hI S ρS RS hSm ι ι'' _ n e (hsubS ι hι)
    choose! q c hq1 hq2 hq3 using hSf
    have hexp := secondOrder_sum M fun ι hι => secondOrder_mul (hp1 ι) (hq1 ι hι)
    have hnear : (fun w => ∑ ι ∈ M, entryFun T ι' ι e w * entryFun S ι ι'' e w)
        =ᶠ[𝓝 0] entryFun (opFunComp T S) ι' ι'' e := by
      filter_upwards [Metric.ball_mem_nhds (0 : ComplexCoordinates n) hTm.radius_pos] with w hw
      have hb : IsSupBelow F (fieldExtend e w) ρT :=
        ⟨‖w‖, mem_ball_zero_iff.1 hw, norm_fieldExtend_le e w⟩
      show _ = ∑' ι, T (fieldExtend e w) ι' ι * S (fieldExtend e w) ι ι''
      rw [tsum_eq_sum (s := M)]
      · rfl
      · intro ι hι
        rw [hTm.vanish_far _ hb ι' ι (fun h => hι ((hM ι).2 h)), zero_mul]
    have hexp' := secondOrder_congr hnear hexp
    have hnum := (hPar F I'' I' hF hI'' hI' _ ρP R ρP R hPm hPm).2.1.1 ζ ζ' ι' ι''
    have hfirst := hnum.1.2.2 ρP R hPm n e _ _ hexp'
    have hsecond := hnum.2.2.2 ρP R hPm n e _ _ hexp'
    have hvan : ∀ (ξ ξ' : F.Carrier → ℂ) (ι : I.Carrier), ι ∉ M →
        coeffZero F I I' T ι' ι = 0 ∧ coeffOne F I I' T ξ ι' ι = 0 ∧
          coeffTwo F I I' T ξ ξ' ι' ι = 0 := fun ξ ξ' ι hι =>
      (hTay F I I' hF hI hI' T ρT RT hTm ξ ξ' ι' ι 0).2.1.2 fun h => hι ((hM ι).2 h)
    have hT0 : ∀ ι, entryFun T ι' ι e 0 = coeffZero F I I' T ι' ι := fun ι => by
      show T (fieldExtend e 0) ι' ι = T 0 ι' ι
      rw [fieldExtend_zero]
    have hS0 : ∀ ι, entryFun S ι ι'' e 0 = coeffZero F I'' I S ι ι'' := fun ι => by
      show S (fieldExtend e 0) ι ι'' = S 0 ι ι''
      rw [fieldExtend_zero]
    have hk : ∀ (X : I'.Carrier → I.Carrier → ℂ) (Y : I.Carrier → I''.Carrier → ℂ),
        (∀ ι, ι ∉ M → X ι' ι = 0) →
        compKernel X Y ι' ι'' = ∑ ι ∈ M, X ι' ι * Y ι ι'' := fun X Y hX =>
      tsum_eq_sum fun ι hι => by rw [hX ι hι, zero_mul]
    constructor
    · rw [hk _ _ fun ι hι => (hvan ζ ζ' ι hι).2.1, hk _ _ fun ι hι => (hvan ζ ζ' ι hι).1,
        ← Finset.sum_add_distrib, ← hfirst]
      simp only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun ι hι => ?_
      rw [hT0, hS0, hp2, hq2 ι hι]
      ring
    · rw [hk _ _ fun ι hι => (hvan ζ ζ' ι hι).2.2, hk _ _ fun ι hι => (hvan ζ ζ' ι hι).1,
        hk _ _ fun ι hι => (hvan ζ ζ' ι hι).2.1, hk _ _ fun ι hι => (hvan ζ' ζ ι hι).2.1,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← hsecond]
      simp only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        symmTensor_apply]
      refine Finset.sum_congr rfl fun ι hι => ?_
      rw [hT0, hS0, hp2, hp2, hp3, hq2 ι hι, hq2 ι hι, hq3 ι hι]
      ring
  exact ⟨funext fun ι' => funext fun ι'' => (key ι' ι'').1,
    funext fun ι' => funext fun ι'' => (key ι' ι'').2⟩
end YangMills.Construction.PeriodicOperators.LeibnizRuleProof
end
