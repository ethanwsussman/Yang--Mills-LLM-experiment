import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.NormOfTheColourCoefficients
import YangMills.Construction.Towers.PlaquettesAndSumsOfATowerProof
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAndTheTwoDeterminants
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.TheBackgroundKernelAtZeroProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.HessianDeterminants
open Set Filter
open scoped Topology
open Matrices
section MatrixFacts
theorem conj_fullTrace (X : ComplexMatrix2) :
    (starRingEnd ℂ) (ComplexMatrix2.fullTrace X) = ComplexMatrix2.fullTrace X.conjTranspose := by
  simp [ComplexMatrix2.fullTrace, Matrix.trace, Fin.sum_univ_two]
theorem im_eq_zero_of_conj_eq {c : ℂ} (h : (starRingEnd ℂ) c = c) : c.im = 0 :=
  Complex.conj_eq_iff_im.mp h
theorem conjTranspose_eq_self_of_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.hermitianTraceless) :
    X.conjTranspose = X := h.1.symm
theorem fullTrace_mul_hermitian_im {X Y : ComplexMatrix2} (hX : X.conjTranspose = X)
    (hY : Y.conjTranspose = Y) : (ComplexMatrix2.fullTrace (X * Y)).im = 0 := by
  apply im_eq_zero_of_conj_eq
  rw [conj_fullTrace, Matrix.conjTranspose_mul, hX, hY]
  exact Matrix.trace_mul_comm _ _
theorem fullTrace_mul_skewHermitian_im {X Y : ComplexMatrix2} (hX : X.conjTranspose = -X)
    (hY : Y.conjTranspose = -Y) : (ComplexMatrix2.fullTrace (X * Y)).im = 0 := by
  apply im_eq_zero_of_conj_eq
  rw [conj_fullTrace, Matrix.conjTranspose_mul, hX, hY, neg_mul_neg]
  exact Matrix.trace_mul_comm _ _
theorem inv_eq_conjTranspose_of_mem {W : ComplexMatrix2} (h : W ∈ ComplexMatrix2.specialUnitary) :
    W⁻¹ = W.conjTranspose := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_eq_conjTranspose_of_mem_specialUnitary <;> assumption
theorem det_eq_one_of_mem {W : ComplexMatrix2} (h : W ∈ ComplexMatrix2.specialUnitary) : W.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.mp h).2
theorem fullTrace_im_of_mem_specialUnitary {W : ComplexMatrix2}
    (h : W ∈ ComplexMatrix2.specialUnitary) : (ComplexMatrix2.fullTrace W).im = 0 := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.fullTrace_im_eq_zero_of_mem_specialUnitary <;> assumption
theorem inv_mem_specialUnitary {W : ComplexMatrix2} (h : W ∈ ComplexMatrix2.specialUnitary) :
    W⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem neg_mem_hermitianTraceless {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.hermitianTraceless) :
    -X ∈ ComplexMatrix2.hermitianTraceless := ComplexMatrix2.hermitianTraceless.neg_mem h
end MatrixFacts
section RealSecondDerivExpr
open FaceTermDerivatives
theorem sum_mem_hermitianTraceless {Y : Fin 4 → ComplexMatrix2}
    (hY : ∀ i, Y i ∈ ComplexMatrix2.hermitianTraceless) :
    (∑ i, Y i) ∈ ComplexMatrix2.hermitianTraceless :=
  ComplexMatrix2.hermitianTraceless.sum_mem fun i _ => hY i
theorem commutatorSum_conjTranspose {Y : Fin 4 → ComplexMatrix2}
    (hY : ∀ i, Y i ∈ ComplexMatrix2.hermitianTraceless) :
    (commutatorSum Y).conjTranspose = -commutatorSum Y := by
  simp only [commutatorSum, Matrix.conjTranspose_sum, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, conjTranspose_eq_self_of_mem (hY _), ← Finset.sum_neg_distrib, neg_sub]
theorem secondDerivExpr_im {Y : Fin 4 → ComplexMatrix2} {W : ComplexMatrix2}
    (hY : ∀ i, Y i ∈ ComplexMatrix2.hermitianTraceless) (hW : W ∈ ComplexMatrix2.specialUnitary) :
    (secondDerivExpr Y W).im = 0 := by
  have h1 : (ComplexMatrix2.fullTrace W).im = 0 := fullTrace_im_of_mem_specialUnitary hW
  have hS := conjTranspose_eq_self_of_mem (sum_mem_hermitianTraceless hY)
  have h2 : (ComplexMatrix2.fullTrace ((∑ i, Y i) * ∑ i, Y i)).im = 0 :=
    fullTrace_mul_hermitian_im hS hS
  have hE : (W - W⁻¹).conjTranspose = -(W - W⁻¹) := by
    have hi : W⁻¹.conjTranspose = W := by
      rw [inv_eq_conjTranspose_of_mem hW, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.conjTranspose_sub, hi, inv_eq_conjTranspose_of_mem hW, neg_sub]
  have h3 : (ComplexMatrix2.fullTrace (commutatorSum Y * (W - W⁻¹))).im = 0 :=
    fullTrace_mul_skewHermitian_im (commutatorSum_conjTranspose hY) hE
  simp only [secondDerivExpr, ComplexMatrix2.halfTrace]
  generalize ComplexMatrix2.fullTrace W = a at h1
  generalize ComplexMatrix2.fullTrace ((∑ i, Y i) * ∑ i, Y i) = b at h2
  generalize ComplexMatrix2.fullTrace (commutatorSum Y * (W - W⁻¹)) = c at h3
  have e1 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [e2, e1]
  simp [Complex.add_im, Complex.mul_im, h1, h2, h3]
theorem transportSign_smul_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (i : Fin 4) : transportSign i • X ∈ ComplexMatrix2.hermitianTraceless := by
  fin_cases i
  all_goals simp [transportSign, hX, neg_mem_hermitianTraceless hX]
theorem finsum_im_eq_zero {ι : Type*} (f : ι → ℂ) (h : ∀ i, (f i).im = 0) :
    (∑ᶠ i, f i).im = 0 := by
  have e : f = fun i => (((f i).re : ℝ) : ℂ) := by
    funext i
    exact Complex.ext (by simp) (by simp [h i])
  rw [e]
  have := AddMonoidHom.map_finsum_of_injective (Complex.ofRealHom.toAddMonoidHom)
    Complex.ofReal_injective (fun i => (f i).re)
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Complex.ofRealHom_eq_coe] at this
  rw [← this]
  simp
end RealSecondDerivExpr
section Polarization
open HessianKernel
variable {α : Type}
theorem apply_eq_polarization {𝒮 : Set (α → ComplexMatrix2)}
    {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsSymmBilinearOn 𝒮 Q) {B B' : α → ComplexMatrix2} (hB : B ∈ 𝒮) (hB' : B' ∈ 𝒮)
    (hS : B + B' ∈ 𝒮) :
    Q B B' = (1 / 2) * (Q (B + B') (B + B') - Q B B - Q B' B') := by
  have h1 := (hQ 1 B hB B' hB' (B + B') hS).1
  have h2 := (hQ 1 B hB B' hB' B hB).2.1
  have h3 := (hQ 1 B hB B' hB' B' hB').2.1
  have h4 := (hQ 1 B hB B' hB' B' hB').2.2
  simp only [one_smul, one_mul] at h1 h2 h3
  rw [h1, h2, h3, ← h4]
  ring
end Polarization
section PairingFacts
variable {ι : Type}
theorem traceFinsumPairing_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.traceFinsumPairing_comm <;> assumption
theorem halfTrace_mul_im {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    (ComplexMatrix2.halfTrace (X * Y)).im = 0 := by apply _root_.YangMills.Construction.Tower.FaceSums.halfTrace_mul_im <;> assumption
theorem traceFinsumPairing_im {f g : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless)
    (hg : ∀ i, g i ∈ ComplexMatrix2.hermitianTraceless) :
    (traceFinsumPairing f g).im = 0 :=
  finsum_im_eq_zero _ fun i => halfTrace_mul_im (hf i) (hg i)
theorem halfTrace_mul_self_re_nonneg {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (ComplexMatrix2.halfTrace (X * X)).re := by apply _root_.YangMills.SharedProofs.p2980 <;> assumption
theorem eq_zero_of_halfTrace_mul_self {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (h : (ComplexMatrix2.halfTrace (X * X)).re = 0) : X = 0 := by apply _root_.YangMills.Construction.Tower.FaceSums.eq_zero_of_halfTrace_mul_self_re <;> assumption
section FiniteIndex
variable [Finite ι]
omit [Finite ι] in
theorem traceFinsumPairing_eq_sum [Fintype ι] (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = ∑ i, ComplexMatrix2.halfTrace (f i * g i) :=
  finsum_eq_sum_of_fintype _
theorem traceFinsumPairing_add_right (f g h : ι → ComplexMatrix2) :
    traceFinsumPairing f (g + h) = traceFinsumPairing f g + traceFinsumPairing f h := by
  have := Fintype.ofFinite ι
  simp only [traceFinsumPairing_eq_sum, Pi.add_apply, mul_add, ComplexMatrix2.halfTrace,
    ComplexMatrix2.fullTrace, Matrix.trace_add, Finset.sum_add_distrib, ← Finset.mul_sum]
theorem traceFinsumPairing_smul_right (c : ℂ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f (c • g) = c * traceFinsumPairing f g := by
  have := Fintype.ofFinite ι
  simp only [traceFinsumPairing_eq_sum, Pi.smul_apply, Matrix.mul_smul, ComplexMatrix2.halfTrace,
    ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
theorem traceFinsumPairing_add_left (f g h : ι → ComplexMatrix2) :
    traceFinsumPairing (f + g) h = traceFinsumPairing f h + traceFinsumPairing g h := by
  rw [traceFinsumPairing_comm, traceFinsumPairing_add_right, traceFinsumPairing_comm h f,
    traceFinsumPairing_comm h g]
theorem traceFinsumPairing_smul_left (c : ℂ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (c • f) g = c * traceFinsumPairing f g := by
  rw [traceFinsumPairing_comm, traceFinsumPairing_smul_right, traceFinsumPairing_comm g f]
theorem traceFinsumPairing_self_re_nonneg {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (traceFinsumPairing f f).re := by
  have := Fintype.ofFinite ι
  rw [traceFinsumPairing_eq_sum, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => halfTrace_mul_self_re_nonneg (hf i)
theorem eq_zero_of_traceFinsumPairing_self {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless)
    (h : (traceFinsumPairing f f).re = 0) : f = 0 := by
  have := Fintype.ofFinite ι
  rw [traceFinsumPairing_eq_sum, Complex.re_sum] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => halfTrace_mul_self_re_nonneg (hf i)).mp h
  funext i
  exact eq_zero_of_halfTrace_mul_self (hf i) (this i (Finset.mem_univ i))
end FiniteIndex
def hermPart (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def skewHermPart (X : ComplexMatrix2) : ComplexMatrix2 := (-Complex.I / 2) • (X - X.conjTranspose)
theorem hermPart_add_I_smul_skewHermPart (X : ComplexMatrix2) :
    hermPart X + Complex.I • skewHermPart X = X := by
  simp only [hermPart, skewHermPart, smul_smul]
  have : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    have := Complex.I_mul_I
    linear_combination (-1 / 2 : ℂ) * this
  rw [this, ← smul_add]
  have h2 : X + X.conjTranspose + (X - X.conjTranspose) = (2 : ℂ) • X := by
    rw [two_smul]; abel
  rw [h2, smul_smul]
  norm_num
theorem fullTrace_conjTranspose_of_traceless {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.fullTrace X.conjTranspose = 0 := by apply _root_.YangMills.Construction.Tower.RescaledTrivialStepsProof.fullTrace_conjTranspose_of_traceless <;> assumption
theorem hermPart_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    hermPart X ∈ ComplexMatrix2.hermitianTraceless := by
  have t : ComplexMatrix2.fullTrace X = 0 := hX
  refine ⟨?_, ?_⟩
  · simp only [hermPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm X.conjTranspose X]
    simp
  · simp only [hermPart, ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_add]
    have t' := fullTrace_conjTranspose_of_traceless hX
    simp only [ComplexMatrix2.fullTrace] at t t'
    rw [t, t']
    simp
theorem skewHermPart_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    skewHermPart X ∈ ComplexMatrix2.hermitianTraceless := by
  have t : ComplexMatrix2.fullTrace X = 0 := hX
  refine ⟨?_, ?_⟩
  · simp only [skewHermPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    have : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      simp [Complex.conj_I]
      ring
    rw [this, neg_smul, ← smul_neg, neg_sub]
  · simp only [skewHermPart, ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sub]
    have t' := fullTrace_conjTranspose_of_traceless hX
    simp only [ComplexMatrix2.fullTrace] at t t'
    rw [t, t']
    simp
theorem hermPart_neg (X : ComplexMatrix2) : hermPart (-X) = -hermPart X := by
  simp only [hermPart, Matrix.conjTranspose_neg, ← neg_add, smul_neg]
theorem skewHermPart_neg (X : ComplexMatrix2) : skewHermPart (-X) = -skewHermPart X := by
  simp only [skewHermPart, Matrix.conjTranspose_neg, ← smul_neg]
  congr 1
  abel
theorem mem_of_skewHermPart_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (h : skewHermPart X = 0) : X ∈ ComplexMatrix2.hermitianTraceless := by
  have := hermPart_add_I_smul_skewHermPart X
  rw [h, smul_zero, add_zero] at this
  rw [← this]
  exact hermPart_mem hX
variable [Finite ι]
theorem forall_mem_of_pairing_skewHermPart_im {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.traceless)
    (h : (traceFinsumPairing (fun i => skewHermPart (f i)) f).im = 0) :
    ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless := by
  set r : ι → ComplexMatrix2 := fun i => hermPart (f i) with hr
  set s : ι → ComplexMatrix2 := fun i => skewHermPart (f i) with hs
  have hrm : ∀ i, r i ∈ ComplexMatrix2.hermitianTraceless := fun i => hermPart_mem (hf i)
  have hsm : ∀ i, s i ∈ ComplexMatrix2.hermitianTraceless := fun i => skewHermPart_mem (hf i)
  have e : f = r + Complex.I • s := by
    funext i
    exact (hermPart_add_I_smul_skewHermPart (f i)).symm
  have e2 : traceFinsumPairing s f = traceFinsumPairing s r + Complex.I * traceFinsumPairing s s := by
    conv_lhs => rw [e]
    rw [traceFinsumPairing_add_right, traceFinsumPairing_smul_right]
  rw [e2] at h
  have i1 := traceFinsumPairing_im hsm hrm
  have i2 := traceFinsumPairing_im hsm hsm
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, i1, i2] at h
  have z : s = 0 := eq_zero_of_traceFinsumPairing_self hsm (by linarith)
  intro i
  exact mem_of_skewHermPart_eq_zero (hf i) (congrFun z i)
theorem eq_zero_of_pairing_parts {f : ι → ComplexMatrix2} (hf : ∀ i, f i ∈ ComplexMatrix2.traceless)
    (h1 : traceFinsumPairing (fun i => hermPart (f i)) f = 0)
    (h2 : traceFinsumPairing (fun i => skewHermPart (f i)) f = 0) : f = 0 := by
  set r : ι → ComplexMatrix2 := fun i => hermPart (f i) with hr
  set s : ι → ComplexMatrix2 := fun i => skewHermPart (f i) with hs
  have hrm : ∀ i, r i ∈ ComplexMatrix2.hermitianTraceless := fun i => hermPart_mem (hf i)
  have hsm : ∀ i, s i ∈ ComplexMatrix2.hermitianTraceless := fun i => skewHermPart_mem (hf i)
  have e : f = r + Complex.I • s := by
    funext i
    exact (hermPart_add_I_smul_skewHermPart (f i)).symm
  have e1 : traceFinsumPairing r f = traceFinsumPairing r r + Complex.I * traceFinsumPairing r s := by
    conv_lhs => rw [e]
    rw [traceFinsumPairing_add_right, traceFinsumPairing_smul_right]
  have e2 : traceFinsumPairing s f = traceFinsumPairing s r + Complex.I * traceFinsumPairing s s := by
    conv_lhs => rw [e]
    rw [traceFinsumPairing_add_right, traceFinsumPairing_smul_right]
  rw [e1] at h1
  rw [e2] at h2
  have i1 := traceFinsumPairing_im hrm hsm
  have i2 := traceFinsumPairing_im hsm hsm
  have i3 := traceFinsumPairing_im hsm hrm
  have a1 := congrArg Complex.re h1
  have a2 := congrArg Complex.im h2
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, i1, Complex.zero_re]
    at a1
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, i2, i3, Complex.zero_im]
    at a2
  have z1 : r = 0 := eq_zero_of_traceFinsumPairing_self hrm (by linarith)
  have z2 : s = 0 := eq_zero_of_traceFinsumPairing_self hsm (by linarith)
  rw [e, z1, z2]
  simp
end PairingFacts
section Determinants
open Massive
variable {ι : Type}
structure IsRealInnerProductOn (V : Submodule ℝ (ι → ComplexMatrix2))
    (Q : (ι → ComplexMatrix2) → (ι → ComplexMatrix2) → ℂ) : Prop where
  map_add_left : ∀ f g h : V, Q (f + g : ι → ComplexMatrix2) h = Q f h + Q g h
  map_smul_left : ∀ (c : ℝ) (f g : V), Q (c • (f : ι → ComplexMatrix2)) g = c * Q f g
  comm : ∀ f g : V, Q f g = Q g f
  im_eq_zero : ∀ f g : V, (Q f g).im = 0
  re_pos : ∀ f : V, f ≠ 0 → 0 < (Q f f).re
variable {V : Submodule ℝ (ι → ComplexMatrix2)} {Q : (ι → ComplexMatrix2) → (ι → ComplexMatrix2) → ℂ}
def IsRealInnerProductOn.toBilinForm (hQ : IsRealInnerProductOn V Q) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun f g => (Q f g).re)
    (fun f g h => by
      have := hQ.map_add_left f g h
      simp only [Submodule.coe_add, this, Complex.add_re])
    (fun c f g => by
      have := hQ.map_smul_left c f g
      simp only [Submodule.coe_smul, this, Complex.re_ofReal_mul, smul_eq_mul])
    (fun f g h => by
      have e1 := hQ.comm f (g + h)
      have e2 := hQ.map_add_left g h f
      have e3 := hQ.comm g f
      have e4 := hQ.comm h f
      simp only [Submodule.coe_add] at e1 ⊢
      rw [e1, e2, Complex.add_re, e3, e4])
    (fun c f g => by
      have e1 := hQ.comm f (c • g)
      have e2 := hQ.map_smul_left c g f
      have e3 := hQ.comm g f
      simp only [Submodule.coe_smul] at e1 ⊢
      rw [e1, e2, Complex.re_ofReal_mul, e3, smul_eq_mul])
theorem IsRealInnerProductOn.toBilinForm_apply (hQ : IsRealInnerProductOn V Q) (f g : V) :
    hQ.toBilinForm f g = (Q f g).re := rfl
theorem det_pos_of_forall_re_pos [FiniteDimensional ℝ V] (hQ : IsRealInnerProductOn V Q)
    (T : V →ₗ[ℝ] V) (hT : ∀ f : V, f ≠ 0 → 0 < (Q (T f) f).re) : 0 < LinearMap.det T := by
  by_contra hneg
  rw [not_lt] at hneg
  let S : ℝ → V →ₗ[ℝ] V := fun t => t • T + (1 - t) • LinearMap.id
  let b := Module.finBasis ℝ V
  let M := LinearMap.toMatrix b b T
  have hS : ∀ t, LinearMap.det (S t) = (t • M + (1 - t) • (1 : Matrix _ _ ℝ)).det := by
    intro t
    rw [← LinearMap.det_toMatrix b]
    congr 1
    simp only [S, map_add, map_smul, LinearMap.toMatrix_id, M]
  have hc : Continuous fun t : ℝ => LinearMap.det (S t) := by
    simp only [hS]
    fun_prop
  have h0 : LinearMap.det (S 0) = 1 := by simp [S]
  have h1 : LinearMap.det (S 1) = LinearMap.det T := by simp [S]
  have hivt : (0 : ℝ) ∈ Set.Icc (LinearMap.det (S 1)) (LinearMap.det (S 0)) := by
    rw [h0, h1]
    exact ⟨hneg, zero_le_one⟩
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' (zero_le_one) hc.continuousOn hivt
  have hker := LinearMap.bot_lt_ker_of_det_eq_zero hz
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker.ne'
  have hz2 : S t f = 0 := hf
  have e : (hQ.toBilinForm (S t f)) f = t * (Q (T f) f).re + (1 - t) * (Q f f).re := by
    simp [S, map_add, LinearMap.add_apply, hQ.toBilinForm_apply]
  rw [hz2, map_zero, LinearMap.zero_apply] at e
  have p1 := hT f hf0
  have p2 := hQ.re_pos f hf0
  rcases ht with ⟨t0, t1⟩
  rcases eq_or_lt_of_le t0 with h | h
  · subst h
    simp at e
    linarith
  · have : 0 < t * (Q (T f) f).re := by positivity
    have : 0 ≤ (1 - t) * (Q f f).re := mul_nonneg (by linarith) p2.le
    linarith
theorem restrictToSubmodule_eq {T : (ι → ComplexMatrix2) → ι → ComplexMatrix2} (T' : V →ₗ[ℝ] V)
    (h : ∀ f : V, (T' f : ι → ComplexMatrix2) = T f) : restrictToSubmodule V T = T' := by
  have hs : ∀ f : V, (restrictToSubmodule V T f : ι → ComplexMatrix2) = T f :=
    Classical.epsilon_spec (p := fun T'' : V →ₗ[ℝ] V => ∀ f : V, (T'' f : ι → ComplexMatrix2) = T f)
      ⟨T', h⟩
  ext1 f
  exact Subtype.ext ((hs f).trans (h f).symm)
theorem shiftedDetOn_eq {T : (ι → ComplexMatrix2) → ι → ComplexMatrix2} (T' : V →ₗ[ℝ] V)
    (h : ∀ f : V, (T' f : ι → ComplexMatrix2) = T f) (z : ℝ) :
    shiftedDetOn V T z = LinearMap.det (T' + z • LinearMap.id) := by
  rw [shiftedDetOn, restrictToSubmodule_eq (T' + z • LinearMap.id)]
  intro f
  simp [h f]
theorem shiftedDetOn_pos [FiniteDimensional ℝ V] (hQ : IsRealInnerProductOn V Q)
    {T : (ι → ComplexMatrix2) → ι → ComplexMatrix2} (T' : V →ₗ[ℝ] V)
    (h : ∀ f : V, (T' f : ι → ComplexMatrix2) = T f)
    (hT : ∀ f : V, 0 ≤ (Q (T f) f).re) {z : ℝ} (hz : 0 < z) :
    0 < shiftedDetOn V T z := by
  rw [shiftedDetOn_eq T' h]
  apply det_pos_of_forall_re_pos hQ
  intro f hf
  have e : (((T' + z • (LinearMap.id : V →ₗ[ℝ] V)) f : V) : ι → ComplexMatrix2) =
      (T' f : ι → ComplexMatrix2) + z • (f : ι → ComplexMatrix2) := by
    simp
  have e2 := hQ.map_add_left (T' f) (z • f) f
  have e3 := hQ.map_smul_left z f f
  simp only [Submodule.coe_smul] at e2
  rw [e, e2, e3, Complex.add_re, Complex.re_ofReal_mul, h]
  have := hT f
  have := hQ.re_pos f hf
  have : 0 < z * (Q f f).re := by positivity
  linarith
theorem eventually_shiftedDetOn_pos [FiniteDimensional ℝ V] (hQ : IsRealInnerProductOn V Q)
    {X : Type} [TopologicalSpace X] {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ D)
    {T : X → (ι → ComplexMatrix2) → ι → ComplexMatrix2}
    (hT : ∀ x ∈ D, ∃ T' : V →ₗ[ℝ] V, ∀ f : V, (T' f : ι → ComplexMatrix2) = T x f)
    (hpos : ∀ f : V, 0 ≤ (Q (T x₀ f) f).re)
    (hc : ∀ f g : V, ContinuousWithinAt (fun x => (Q f (T x g)).re) D x₀) {z : ℝ} (hz : 0 < z) :
    ∀ᶠ x in 𝓝[D] x₀, 0 < shiftedDetOn V (T x) z := by
  let b := Module.finBasis ℝ V
  let B := hQ.toBilinForm
  let G := LinearMap.BilinForm.toMatrix b B
  have hnd : B.Nondegenerate := by
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · by_contra h0
      have := hQ.re_pos f h0
      have h2 : B f f = 0 := hf f
      rw [hQ.toBilinForm_apply] at h2
      linarith
    · by_contra h0
      have := hQ.re_pos f h0
      have h2 : B f f = 0 := hf f
      rw [hQ.toBilinForm_apply] at h2
      linarith
  have hG : G.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  let N : X → Matrix _ _ ℝ := fun x => Matrix.of fun i j =>
    (Q (b i) (T x (b j))).re + z * (Q (b i) (b j)).re
  have hN : ContinuousWithinAt N D x₀ := by
    refine continuousWithinAt_pi.mpr fun i => continuousWithinAt_pi.mpr fun j => ?_
    exact (hc (b i) (b j)).add continuousWithinAt_const
  have hdet : ContinuousWithinAt (fun x => (N x).det / G.det) D x₀ :=
    ((Continuous.matrix_det continuous_id).continuousAt.comp_continuousWithinAt hN).div_const _
  have hrel : ∀ x ∈ D, shiftedDetOn V (T x) z = (N x).det / G.det := by
    intro x hx
    obtain ⟨T', hT'⟩ := hT x hx
    rw [shiftedDetOn_eq T' hT']
    have hm : N x = G * LinearMap.toMatrix b b (T' + z • LinearMap.id) := by
      rw [← LinearMap.BilinForm.toMatrix_compRight]
      ext i j
      simp only [N, Matrix.of_apply, LinearMap.BilinForm.toMatrix_apply,
        LinearMap.BilinForm.compRight_apply, B, hQ.toBilinForm_apply]
      have e1 := hQ.comm (b i) (T' (b j))
      have e2 := hQ.comm (b i) ((T' + z • (LinearMap.id : V →ₗ[ℝ] V)) (b j))
      have e3 : (((T' + z • (LinearMap.id : V →ₗ[ℝ] V)) (b j) : V) : ι → ComplexMatrix2) =
          (T' (b j) : ι → ComplexMatrix2) + z • (b j : ι → ComplexMatrix2) := by simp
      have e4 := hQ.map_add_left (T' (b j)) (z • b j) (b i)
      have e5 := hQ.map_smul_left z (b j) (b i)
      have e6 := hQ.comm (b j) (b i)
      simp only [Submodule.coe_smul] at e4
      rw [e2, e3, e4, e5, Complex.add_re, Complex.re_ofReal_mul, e6, ← e1, hT']
    rw [hm, Matrix.det_mul, LinearMap.det_toMatrix, mul_comm, mul_div_assoc, div_self hG, mul_one]
  have h0 : 0 < (N x₀).det / G.det := by
    rw [← hrel x₀ hx₀]
    obtain ⟨T', hT'⟩ := hT x₀ hx₀
    exact shiftedDetOn_pos hQ T' hT' hpos hz
  have hev := hdet.eventually (lt_mem_nhds h0)
  filter_upwards [hev, self_mem_nhdsWithin] with x h1 h2
  rw [hrel x h2]
  exact h1
end Determinants
section RealityOnTorus
open FaceTermDerivatives HessianKernel
variable {L n k j : ℕ}
theorem mem_traceless_of_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.hermitianTraceless) :
    X ∈ ComplexMatrix2.traceless := h.2
theorem edgeForm_apply_mem {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (b : Edge L n k j) : B b ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.edgeForm_apply_mem <;> assumption
theorem mem_complexEdgeForms_of_mem {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) : B ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
theorem compact_field_mem_complex {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.compactGaugeGroup) :
    U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
theorem field_apply_mem {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.compactGaugeGroup) (b : Edge L n k j) :
    U b ∈ ComplexMatrix2.specialUnitary := hU.1 b (mem_univ b)
theorem plaquetteHolonomy_mem {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.compactGaugeGroup) (p : Face L n k j) :
    PeriodicLattice.plaquetteHolonomy U p ∈ ComplexMatrix2.specialUnitary := by
  refine Submonoid.list_prod_mem _ fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  exact field_apply_mem hU b
theorem faceTransports_mem {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.compactGaugeGroup) (p : Face L n k j)
    (i : Fin 4) : faceTransports U p i ∈ ComplexMatrix2.specialUnitary := by
  have h := field_apply_mem hU
  fin_cases i
  · exact Submonoid.one_mem _
  · exact h _
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (h _) (h _)) (inv_mem_specialUnitary (h _))
  · exact plaquetteHolonomy_mem hU p
theorem transportedForm_mem {U B : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.compactGaugeGroup) (hB : B ∈ edgeFormSpace L n k j)
    (p : Face L n k j) (i : Fin 4) :
    transportedForm U B p i ∈ ComplexMatrix2.hermitianTraceless :=
  transportSign_smul_mem (ComplexMatrix2.conjugateBy_mem_hermitianTraceless
    (faceTransports_mem hU p i) _ (edgeForm_apply_mem hB _)) i
theorem complexActionHessian_diag_im (hP : FaceTermDerivatives.HoldsOnPeriodicLevel L n k j)
    {U B : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.compactGaugeGroup) (hB : B ∈ edgeFormSpace L n k j) :
    (complexActionHessian U B B).im = 0 := by
  rw [← ((hP B (mem_complexEdgeForms_of_mem hB)).1 U (compact_field_mem_complex hU)).2.1]
  exact finsum_im_eq_zero _ fun p =>
    secondDerivExpr_im (transportedForm_mem hU hB p) (plaquetteHolonomy_mem hU p)
theorem complexActionHessian_im (hP : FaceTermDerivatives.HoldsOnPeriodicLevel L n k j)
    (hA : HessianKernel.HoldsOnTorus L n k j)
    {U B B' : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.compactGaugeGroup) (hB : B ∈ edgeFormSpace L n k j)
    (hB' : B' ∈ edgeFormSpace L n k j) : (complexActionHessian U B B').im = 0 := by
  have hQ := (hA U (compact_field_mem_complex hU)).1
  rw [apply_eq_polarization hQ (mem_complexEdgeForms_of_mem hB) (mem_complexEdgeForms_of_mem hB')
    (mem_complexEdgeForms_of_mem ((edgeFormSpace L n k j).add_mem hB hB'))]
  have e1 := complexActionHessian_diag_im hP hU ((edgeFormSpace L n k j).add_mem hB hB')
  have e2 := complexActionHessian_diag_im hP hU hB
  have e3 := complexActionHessian_diag_im hP hU hB'
  have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  simp [Complex.mul_im, e1, e2, e3]
theorem hessianSymmRealOnTorus (hP : FaceTermDerivatives.HoldsOnPeriodicLevel L n k j)
    (hA : HessianKernel.HoldsOnTorus L n k j) :
    HessianSymmRealOnTorus L n k j :=
  ⟨fun U hU => (hA U hU).1, fun _ hU _ hB _ hB' => complexActionHessian_im hP hA hU hB hB'⟩
end RealityOnTorus
section RealityOnFullSpace
open FaceTermDerivatives HessianKernel
variable {L k j : ℕ}
theorem fullSpace_edgeForm_apply_mem {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L k j)) (b : FullSpace.Edge L k j) :
    B b ∈ ComplexMatrix2.hermitianTraceless := by
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · exact hB.1 b ⟨μ, h⟩
  · have hp : b.opposite.IsPositivelyOriented := ⟨μ, by
      change b.initial - b.terminal = _
      rw [← neg_sub, h, neg_neg]⟩
    have h1 := hB.1 _ hp
    rw [hB.2 b] at h1
    simpa using neg_mem_hermitianTraceless h1
theorem fullSpace_mem_complexEdgeForms_of_mem {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L k j)) :
    B ∈ FullSpace.complexEdgeForms (meshAt L k j) :=
  ⟨fun b hb => mem_traceless_of_mem (hB.1 b hb), hB.2⟩
theorem fullSpace_compact_field_mem_complex {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup) :
    U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
  ⟨fun b => det_eq_one_of_mem (hU.1 b), hU.2⟩
theorem fullSpace_faceVariable_mem {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup)
    (p : FullSpace.Face L k j) : FullSpace.faceVariable U p ∈ ComplexMatrix2.specialUnitary := by
  refine Submonoid.list_prod_mem _ fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  exact hU.1 b
theorem fullSpace_faceTransports_mem {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup)
    (p : FullSpace.Face L k j) (i : Fin 4) :
    FullSpace.faceTransports U p i ∈ ComplexMatrix2.specialUnitary := by
  have h := hU.1
  fin_cases i
  · exact Submonoid.one_mem _
  · exact h _
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (h _) (h _)) (inv_mem_specialUnitary (h _))
  · exact fullSpace_faceVariable_mem hU p
theorem fullSpace_transportedForm_mem {U B : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup)
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L k j)) (p : FullSpace.Face L k j) (i : Fin 4) :
    FullSpace.transportedForm U B p i ∈ ComplexMatrix2.hermitianTraceless :=
  transportSign_smul_mem (ComplexMatrix2.conjugateBy_mem_hermitianTraceless
    (fullSpace_faceTransports_mem hU p i) _ (fullSpace_edgeForm_apply_mem hB _)) i
theorem fullSpace_complexActionHessian_diag_im (hP : HoldsOnFullSpaceLevel L k j)
    {U B : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup)
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L k j)) (hf : FullSpace.HasFiniteEdgeSupport B) :
    (FullSpace.complexActionHessian U B B).im = 0 := by
  rw [← (((hP B (fullSpace_mem_complexEdgeForms_of_mem hB)).2 hf).1 U
    (fullSpace_compact_field_mem_complex hU)).1]
  exact finsum_im_eq_zero _ fun p => secondDerivExpr_im (fullSpace_transportedForm_mem hU hB p)
    (fullSpace_faceVariable_mem hU p)
theorem fullSpace_hasFiniteEdgeSupport_add {B B' : FullSpace.Edge L k j → ComplexMatrix2}
    (hf : FullSpace.HasFiniteEdgeSupport B) (hf' : FullSpace.HasFiniteEdgeSupport B') :
    FullSpace.HasFiniteEdgeSupport (B + B') := by
  refine (hf.union hf').subset ?_
  rintro b ⟨hb, h⟩
  by_cases h1 : B b = 0
  · refine Or.inr ⟨hb, fun h2 => h ?_⟩
    simp [h1, h2]
  · exact Or.inl ⟨hb, h1⟩
theorem hessianSymmRealOnFullSpace (hP : HoldsOnFullSpaceLevel L k j)
    (hA : HessianKernel.HoldsOnFullSpace L k j) :
    HessianSymmRealOnFullSpace L k j := by
  refine ⟨fun U hU => (hA U hU).1, ?_⟩
  intro U hU B hB hf B' hB' hf'
  have hQ := (hA U (fullSpace_compact_field_mem_complex hU)).1
  have hS := (FullSpace.edgeFormSpace (meshAt L k j)).add_mem hB hB'
  have hfS := fullSpace_hasFiniteEdgeSupport_add hf hf'
  rw [apply_eq_polarization hQ ⟨fullSpace_mem_complexEdgeForms_of_mem hB, hf⟩
    ⟨fullSpace_mem_complexEdgeForms_of_mem hB', hf'⟩ ⟨fullSpace_mem_complexEdgeForms_of_mem hS, hfS⟩]
  have e1 := fullSpace_complexActionHessian_diag_im hP hU hS hfS
  have e2 := fullSpace_complexActionHessian_diag_im hP hU hB hf
  have e3 := fullSpace_complexActionHessian_diag_im hP hU hB' hf'
  have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  simp [Complex.mul_im, e1, e2, e3]
end RealityOnFullSpace
section TorusTransposes
open PairedFunctionSpace (linearOfValues transposeOfValues)
open HessianKernel CovDiffTransposes
theorem real_smul_eq_complex_smul {ι : Type} (c : ℝ) (f : ι → ComplexMatrix2) :
    c • f = (c : ℂ) • f := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
theorem vertex_apply_mem {σ : Type} {l : σ → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.hermitianTracelessFunctions σ) (x : σ) :
    l x ∈ ComplexMatrix2.hermitianTraceless :=
  (Submodule.mem_pi.mp hl) x (mem_univ x)
theorem vertex_apply_mem_traceless {σ : Type} {l : σ → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.tracelessFunctions σ) (x : σ) : l x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.PauliCoefficientNorm.apply_mem_traceless <;> assumption
theorem mem_hermitianTracelessFunctions {σ : Type} {l : σ → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) :
    l ∈ GroupLieProduct.hermitianTracelessFunctions σ :=
  Submodule.mem_pi.mpr fun x _ => hl x
theorem mem_tracelessFunctions {σ : Type} {l : σ → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    l ∈ GroupLieProduct.tracelessFunctions σ :=
  Submodule.mem_pi.mpr fun x _ => hl x
theorem mem_tracelessFunctions_of_mem {σ : Type} {l : σ → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.hermitianTracelessFunctions σ) :
    l ∈ GroupLieProduct.tracelessFunctions σ :=
  mem_tracelessFunctions fun x => mem_traceless_of_mem (vertex_apply_mem hl x)
variable {L n : ℕ}
def covDiffTranspose (U : Edge L n 0 0 → ComplexMatrix2) :
    (Edge L n 0 0 → ComplexMatrix2) → Vertex L n 0 0 → ComplexMatrix2 :=
  transposeOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U)
theorem gaugeLaplacian_eq (U : Edge L n 0 0 → ComplexMatrix2) (l : Vertex L n 0 0 → ComplexMatrix2) :
    gaugeLaplacian U l = covDiffTranspose U (covDiff U l) := rfl
theorem massiveHessian_eq (U B : Edge L n 0 0 → ComplexMatrix2) :
    massiveHessian U B =
      complexHessianOperator U B + covDiff U (covDiffTranspose U B) := rfl
theorem edgeFormPairing_comm (B B' : Edge L n 0 0 → ComplexMatrix2) :
    edgeFormPairing B B' = edgeFormPairing B' B :=
  traceFinsumPairing_comm _ _
theorem eq_zero_of_positive_edges {Z : Edge L n 0 0 → ComplexMatrix2}
    (hZ : ∀ b, Z b.opposite = -Z b)
    (h : ∀ b : Edge L n 0 0, b.IsPositivelyOriented → Z b = 0) : Z = 0 := by
  funext b
  obtain ⟨μ, h1 | h1⟩ := b.isNeighbour
  · exact h b ⟨μ, h1⟩
  · have hp : b.opposite.IsPositivelyOriented := ⟨μ, by
      change b.source - b.target = _
      rw [← neg_sub, h1, neg_neg]⟩
    have h2 := h _ hp
    rw [hZ b] at h2
    simpa using h2
variable [Finite (Vertex L n 0 0)]
instance instFiniteEdge : Finite (Edge L n 0 0) :=
  Finite.of_injective (fun b : Edge L n 0 0 => (b.source, b.target)) (by
    rintro ⟨t, h, _⟩ ⟨t', h', _⟩ e
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl)
theorem edgeFormPairing_add_right (f g h : Edge L n 0 0 → ComplexMatrix2) :
    edgeFormPairing f (g + h) = edgeFormPairing f g + edgeFormPairing f h :=
  traceFinsumPairing_add_right _ _ _
theorem edgeFormPairing_smul_right (c : ℂ) (f g : Edge L n 0 0 → ComplexMatrix2) :
    edgeFormPairing f (c • g) = c * edgeFormPairing f g :=
  traceFinsumPairing_smul_right _ _ _
theorem edgeFormPairing_add_left (f g h : Edge L n 0 0 → ComplexMatrix2) :
    edgeFormPairing (f + g) h = edgeFormPairing f h + edgeFormPairing g h :=
  traceFinsumPairing_add_left _ _ _
theorem edgeFormPairing_smul_left (c : ℂ) (f g : Edge L n 0 0 → ComplexMatrix2) :
    edgeFormPairing (c • f) g = c * edgeFormPairing f g :=
  traceFinsumPairing_smul_left _ _ _
theorem vertexInnerProduct :
    IsRealInnerProductOn (vertexFunctionSpace L n 0 0) (traceFinsumPairing (ι := Vertex L n 0 0)) where
  map_add_left f g h := traceFinsumPairing_add_left _ _ _
  map_smul_left c f g := by rw [real_smul_eq_complex_smul, traceFinsumPairing_smul_left]
  comm f g := traceFinsumPairing_comm _ _
  im_eq_zero f g := traceFinsumPairing_im (vertex_apply_mem f.2) (vertex_apply_mem g.2)
  re_pos f hf := by
    refine lt_of_le_of_ne (traceFinsumPairing_self_re_nonneg (vertex_apply_mem f.2)) fun h => hf ?_
    exact Subtype.ext (eq_zero_of_traceFinsumPairing_self (vertex_apply_mem f.2) h.symm)
theorem edgeInnerProduct :
    IsRealInnerProductOn (edgeFormSpace L n 0 0) (edgeFormPairing (L := L) (m := n) (k := 0) (j := 0)) where
  map_add_left f g h := edgeFormPairing_add_left _ _ _
  map_smul_left c f g := by rw [real_smul_eq_complex_smul, edgeFormPairing_smul_left]
  comm f g := edgeFormPairing_comm _ _
  im_eq_zero f g := traceFinsumPairing_im (fun b => edgeForm_apply_mem f.2 b.1)
    (fun b => edgeForm_apply_mem g.2 b.1)
  re_pos f hf := by
    have hm : ∀ b : PositiveEdge L n 0 0,
        restrictToPositiveEdges (f : Edge L n 0 0 → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless :=
      fun b => edgeForm_apply_mem f.2 b.1
    refine lt_of_le_of_ne (traceFinsumPairing_self_re_nonneg hm) fun h => hf ?_
    have h0 := eq_zero_of_traceFinsumPairing_self hm h.symm
    refine Subtype.ext (eq_zero_of_positive_edges f.2.2 fun b hb => ?_)
    exact congrFun h0 ⟨b, hb⟩
structure TransposePairFacts (S S' : PairedFunctionSpace)
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2) : Prop where
  transpose_mem_complex : ∀ g ∈ S'.complexSubmodule, transposeOfValues S S' m g ∈ S.complexSubmodule
  pair_transpose : ∀ g ∈ S'.complexSubmodule, ∀ f ∈ S.complexSubmodule, S.IsFinitelySupported f →
    S.pair (transposeOfValues S S' m g) f = S'.pair g (m f)
  apply_mem_complex : ∀ f ∈ S.complexSubmodule, m f ∈ S'.complexSubmodule
  apply_add : ∀ f ∈ S.complexSubmodule, ∀ f' ∈ S.complexSubmodule, m (f + f') = m f + m f'
  apply_smul : ∀ (c : ℂ), ∀ f ∈ S.complexSubmodule, m (c • f) = c • m f
  transpose_apply_add : ∀ g ∈ S'.complexSubmodule, ∀ g' ∈ S'.complexSubmodule,
    transposeOfValues S S' m (g + g') =
      transposeOfValues S S' m g + transposeOfValues S S' m g'
  transpose_apply_smul : ∀ (c : ℂ), ∀ g ∈ S'.complexSubmodule,
    transposeOfValues S S' m (c • g) = c • transposeOfValues S S' m g
theorem transposePairFacts {S S' : PairedFunctionSpace}
    {m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2}
    (hlin : ∀ f : S.complexSubmodule, (linearOfValues S S' m f : S'.index → ComplexMatrix2) = m f.1)
    (htr : PairedFunctionSpace.IsTransposeMap (linearOfValues S S' m)
      (PairedFunctionSpace.transposeMap (linearOfValues S S' m))) : TransposePairFacts S S' m := by
  have hv : ∀ (g : S'.index → ComplexMatrix2) (hg : g ∈ S'.complexSubmodule),
      transposeOfValues S S' m g =
        (PairedFunctionSpace.transposeMap (linearOfValues S S' m) ⟨g, hg⟩ : S.complexSubmodule).1 :=
    fun g hg => dif_pos hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [hv g hg]
    exact Subtype.property _
  · intro g hg f hf hs
    rw [hv g hg, ← hlin ⟨f, hf⟩]
    exact htr ⟨g, hg⟩ ⟨f, hf⟩ hs
  · intro f hf
    rw [show m f = _ from (hlin ⟨f, hf⟩).symm]
    exact Subtype.property _
  · intro f hf f' hf'
    have e := congrArg Subtype.val
      (map_add (linearOfValues S S' m) (⟨f, hf⟩ : S.complexSubmodule) ⟨f', hf'⟩)
    rw [Submodule.coe_add, hlin, hlin, hlin] at e
    exact e
  · intro c f hf
    have e := congrArg Subtype.val
      (map_smul (linearOfValues S S' m) c (⟨f, hf⟩ : S.complexSubmodule))
    rw [Submodule.coe_smul, hlin, hlin] at e
    exact e
  · intro g hg g' hg'
    rw [hv _ (S'.complexSubmodule.add_mem hg hg'), hv _ hg, hv _ hg']
    exact congrArg Subtype.val
      (map_add (PairedFunctionSpace.transposeMap (linearOfValues S S' m))
        (⟨g, hg⟩ : S'.complexSubmodule) ⟨g', hg'⟩)
  · intro c g hg
    rw [hv _ (S'.complexSubmodule.smul_mem c hg), hv _ hg]
    exact congrArg Subtype.val
      (map_smul (PairedFunctionSpace.transposeMap (linearOfValues S S' m)) c
        (⟨g, hg⟩ : S'.complexSubmodule))
omit [Finite (Vertex L n 0 0)] in
theorem covDiff_transposePairFacts (hX : CovDiffTransposes.OnTorus L n 0 0)
    {U : Edge L n 0 0 → ComplexMatrix2} (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup) :
    TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U) :=
  transposePairFacts (hX U hU).covDiff.coe_linear (hX U hU).covDiff.isTranspose
end TorusTransposes
section RealOperators
open HessianKernel CovDiffTransposes
open PairedFunctionSpace (linearOfValues transposeOfValues)
variable {L n : ℕ}
theorem skewHermPart_edgeForm_mem {Z : Edge L n 0 0 → ComplexMatrix2}
    (hZ : Z ∈ complexEdgeForms L n 0 0) :
    (fun b => skewHermPart (Z b)) ∈ edgeFormSpace L n 0 0 :=
  ⟨fun b hb => skewHermPart_mem (hZ.1 b hb), fun b => by simp only [hZ.2 b, skewHermPart_neg]⟩
theorem hermPart_edgeForm_mem {Z : Edge L n 0 0 → ComplexMatrix2}
    (hZ : Z ∈ complexEdgeForms L n 0 0) :
    (fun b => hermPart (Z b)) ∈ edgeFormSpace L n 0 0 :=
  ⟨fun b hb => hermPart_mem (hZ.1 b hb), fun b => by simp only [hZ.2 b, hermPart_neg]⟩
theorem covDiff_apply_of_positive (U : Edge L n 0 0 → ComplexMatrix2)
    (l : Vertex L n 0 0 → ComplexMatrix2) {b : Edge L n 0 0} (hb : b.IsPositivelyOriented) :
    covDiff U l b = ComplexMatrix2.conjugateBy (U b) (l b.target) - l b.source := by
  simp [covDiff, extendOddly, if_pos hb]
theorem covDiff_mem {U : Edge L n 0 0 → ComplexMatrix2}
    (hF : TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U))
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) {l : Vertex L n 0 0 → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace L n 0 0) : covDiff U l ∈ edgeFormSpace L n 0 0 := by
  have hc : covDiff U l ∈ complexEdgeForms L n 0 0 :=
    hF.apply_mem_complex l (mem_tracelessFunctions_of_mem hl)
  refine ⟨fun b hb => ?_, hc.2⟩
  rw [covDiff_apply_of_positive U l hb]
  exact ComplexMatrix2.hermitianTraceless.sub_mem
    (ComplexMatrix2.conjugateBy_mem_hermitianTraceless (field_apply_mem hU b) _
      (vertex_apply_mem hl _))
    (vertex_apply_mem hl _)
variable [Finite (Vertex L n 0 0)]
theorem pair_covDiffTranspose {U : Edge L n 0 0 → ComplexMatrix2}
    (hF : TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U))
    {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0)
    {l : Vertex L n 0 0 → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0)) :
    traceFinsumPairing (covDiffTranspose U B) l = edgeFormPairing B (covDiff U l) :=
  hF.pair_transpose B hB l hl (Set.toFinite _)
theorem covDiffTranspose_mem {U : Edge L n 0 0 → ComplexMatrix2}
    (hF : TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U))
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) {B : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n 0 0) : covDiffTranspose U B ∈ vertexFunctionSpace L n 0 0 := by
  have hc : covDiffTranspose U B ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0) :=
    hF.transpose_mem_complex B (mem_complexEdgeForms_of_mem hB)
  have hv := vertex_apply_mem_traceless hc
  refine mem_hermitianTracelessFunctions (forall_mem_of_pairing_skewHermPart_im hv ?_)
  have hs : (fun x => skewHermPart (covDiffTranspose U B x)) ∈ vertexFunctionSpace L n 0 0 :=
    mem_hermitianTracelessFunctions fun x => skewHermPart_mem (hv x)
  rw [traceFinsumPairing_comm,
    pair_covDiffTranspose hF (mem_complexEdgeForms_of_mem hB) (mem_tracelessFunctions_of_mem hs)]
  have hd := covDiff_mem hF hU hs
  exact traceFinsumPairing_im (fun b => edgeForm_apply_mem hB b.1) (fun b => edgeForm_apply_mem hd b.1)
structure HessianOperatorFacts (U : Edge L n 0 0 → ComplexMatrix2) : Prop where
  isSymmBilinear : IsSymmBilinearOn (complexEdgeForms L n 0 0 : Set (Edge L n 0 0 → ComplexMatrix2))
    (complexActionHessian U)
  operator_mem_complex : ∀ B ∈ complexEdgeForms L n 0 0,
    complexHessianOperator U B ∈ complexEdgeForms L n 0 0
  pairing_operator : ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
    edgeFormPairing B (complexHessianOperator U B') = complexActionHessian U B B'
omit [Finite (Vertex L n 0 0)] in
theorem hessianOperatorFacts (hA : HessianKernel.HoldsOnTorus L n 0 0)
    (hX : CovDiffTransposes.OnTorus L n 0 0)
    {U : Edge L n 0 0 → ComplexMatrix2} (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup) :
    HessianOperatorFacts U :=
  ⟨(hA U hU).1, fun B hB => ((hX U hU).operator_mem B hB).2.1, (hA U hU).2.2.2.2.1⟩
theorem complexHessianOperator_mem (hP : FaceTermDerivatives.HoldsOnPeriodicLevel L n 0 0)
    (hA : HessianKernel.HoldsOnTorus L n 0 0)
    {U : Edge L n 0 0 → ComplexMatrix2} (hK : HessianOperatorFacts U)
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) {B : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n 0 0) : complexHessianOperator U B ∈ edgeFormSpace L n 0 0 := by
  have hc := hK.operator_mem_complex B (mem_complexEdgeForms_of_mem hB)
  have hv : ∀ b : PositiveEdge L n 0 0,
      restrictToPositiveEdges (complexHessianOperator U B) b ∈ ComplexMatrix2.traceless :=
    fun b => hc.1 b.1 b.2
  have hE := skewHermPart_edgeForm_mem hc
  have h := forall_mem_of_pairing_skewHermPart_im hv (by
    have e : traceFinsumPairing
        (fun i => skewHermPart (restrictToPositiveEdges (complexHessianOperator U B) i))
        (restrictToPositiveEdges (complexHessianOperator U B)) =
        edgeFormPairing (fun b => skewHermPart (complexHessianOperator U B b))
          (complexHessianOperator U B) := rfl
    rw [e, hK.pairing_operator _ (mem_complexEdgeForms_of_mem hE) _ (mem_complexEdgeForms_of_mem hB)]
    exact complexActionHessian_im hP hA hU hE hB)
  exact ⟨fun b hb => h ⟨b, hb⟩, hc.2⟩
theorem complexEdgeForm_eq_zero_of_pairings {Z : Edge L n 0 0 → ComplexMatrix2}
    (hZ : Z ∈ complexEdgeForms L n 0 0)
    (hz : ∀ E ∈ complexEdgeForms L n 0 0, edgeFormPairing E Z = 0) : Z = 0 := by
  have hv : ∀ b : PositiveEdge L n 0 0, restrictToPositiveEdges Z b ∈ ComplexMatrix2.traceless :=
    fun b => hZ.1 b.1 b.2
  have a1 : traceFinsumPairing (fun i => hermPart (restrictToPositiveEdges Z i))
      (restrictToPositiveEdges Z) = 0 :=
    hz (fun b => hermPart (Z b)) (mem_complexEdgeForms_of_mem (hermPart_edgeForm_mem hZ))
  have a2 : traceFinsumPairing (fun i => skewHermPart (restrictToPositiveEdges Z i))
      (restrictToPositiveEdges Z) = 0 :=
    hz (fun b => skewHermPart (Z b)) (mem_complexEdgeForms_of_mem (skewHermPart_edgeForm_mem hZ))
  have h0 := eq_zero_of_pairing_parts hv a1 a2
  exact eq_zero_of_positive_edges hZ.2 fun b hb => congrFun h0 ⟨b, hb⟩
theorem complexEdgeForm_eq_of_pairings {X Y : Edge L n 0 0 → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n 0 0) (hY : Y ∈ complexEdgeForms L n 0 0)
    (h : ∀ E ∈ complexEdgeForms L n 0 0, edgeFormPairing E X = edgeFormPairing E Y) : X = Y := by
  have hZ : X + (-1 : ℂ) • Y ∈ complexEdgeForms L n 0 0 :=
    (complexEdgeForms L n 0 0).add_mem hX ((complexEdgeForms L n 0 0).smul_mem _ hY)
  have h1 := complexEdgeForm_eq_zero_of_pairings hZ fun E hE => by
    rw [edgeFormPairing_add_right, edgeFormPairing_smul_right, h E hE]
    ring
  have h2 : X + -Y = 0 := by
    rw [← h1]
    congr 1
    rw [neg_one_smul]
  exact add_neg_eq_zero.mp h2
theorem complexHessianOperator_smul_add {U : Edge L n 0 0 → ComplexMatrix2}
    (hK : HessianOperatorFacts U) (c : ℂ)
    {B B' : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0)
    (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexHessianOperator U (c • B + B') =
      c • complexHessianOperator U B + complexHessianOperator U B' := by
  have hS : c • B + B' ∈ complexEdgeForms L n 0 0 :=
    (complexEdgeForms L n 0 0).add_mem ((complexEdgeForms L n 0 0).smul_mem c hB) hB'
  refine complexEdgeForm_eq_of_pairings (hK.operator_mem_complex _ hS)
    ((complexEdgeForms L n 0 0).add_mem
      ((complexEdgeForms L n 0 0).smul_mem c (hK.operator_mem_complex _ hB))
      (hK.operator_mem_complex _ hB')) ?_
  intro E hE
  rw [edgeFormPairing_add_right, edgeFormPairing_smul_right, hK.pairing_operator E hE _ hS,
    hK.pairing_operator E hE _ hB, hK.pairing_operator E hE _ hB']
  exact (hK.isSymmBilinear c B hB B' hB' E hE).2.1
theorem complexHessianOperator_add {U : Edge L n 0 0 → ComplexMatrix2} (hK : HessianOperatorFacts U)
    {B B' : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0)
    (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexHessianOperator U (B + B') =
      complexHessianOperator U B + complexHessianOperator U B' := by
  simpa using complexHessianOperator_smul_add hK 1 hB hB'
theorem complexHessianOperator_smul {U : Edge L n 0 0 → ComplexMatrix2} (hK : HessianOperatorFacts U)
    (c : ℂ) {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0) :
    complexHessianOperator U (c • B) = c • complexHessianOperator U B := by
  have h0 : (0 : Edge L n 0 0 → ComplexMatrix2) ∈ complexEdgeForms L n 0 0 :=
    (complexEdgeForms L n 0 0).zero_mem
  have hz : complexHessianOperator U (0 : Edge L n 0 0 → ComplexMatrix2) = 0 := by
    have := complexHessianOperator_add hK h0 h0
    simpa using this
  simpa [hz] using complexHessianOperator_smul_add hK c hB h0
theorem exists_linear_gaugeLaplacian {U : Edge L n 0 0 → ComplexMatrix2}
    (hF : TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U))
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) :
    ∃ T' : vertexFunctionSpace L n 0 0 →ₗ[ℝ] vertexFunctionSpace L n 0 0,
      ∀ f : vertexFunctionSpace L n 0 0,
        (T' f : Vertex L n 0 0 → ComplexMatrix2) = gaugeLaplacian U f := by
  have hm : ∀ f : vertexFunctionSpace L n 0 0, gaugeLaplacian U f ∈ vertexFunctionSpace L n 0 0 :=
    fun f => covDiffTranspose_mem hF hU (covDiff_mem hF hU f.2)
  have hmc : ∀ f : vertexFunctionSpace L n 0 0, covDiff U f ∈ complexEdgeForms L n 0 0 := fun f =>
    mem_complexEdgeForms_of_mem (covDiff_mem hF hU f.2)
  refine ⟨{ toFun := fun f => ⟨gaugeLaplacian U f, hm f⟩, map_add' := ?_, map_smul' := ?_ },
    fun f => rfl⟩
  · intro f g
    apply Subtype.ext
    change gaugeLaplacian U (f + g : Vertex L n 0 0 → ComplexMatrix2) =
      gaugeLaplacian U f + gaugeLaplacian U g
    have e1 : covDiff U (f + g : Vertex L n 0 0 → ComplexMatrix2) =
        covDiff U f + covDiff U g :=
      hF.apply_add _ (mem_tracelessFunctions_of_mem f.2) _ (mem_tracelessFunctions_of_mem g.2)
    rw [gaugeLaplacian_eq, e1]
    exact hF.transpose_apply_add _ (hmc f) _ (hmc g)
  · intro c f
    apply Subtype.ext
    change gaugeLaplacian U (c • (f : Vertex L n 0 0 → ComplexMatrix2)) = c • gaugeLaplacian U f
    have e1 : covDiff U ((c : ℂ) • (f : Vertex L n 0 0 → ComplexMatrix2)) =
        (c : ℂ) • covDiff U f := hF.apply_smul _ _ (mem_tracelessFunctions_of_mem f.2)
    rw [real_smul_eq_complex_smul, real_smul_eq_complex_smul, gaugeLaplacian_eq, e1]
    exact hF.transpose_apply_smul _ _ (hmc f)
theorem exists_linear_massiveHessian (hP : FaceTermDerivatives.HoldsOnPeriodicLevel L n 0 0)
    (hA : HessianKernel.HoldsOnTorus L n 0 0) {U : Edge L n 0 0 → ComplexMatrix2}
    (hF : TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U))
    (hK : HessianOperatorFacts U) (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) :
    ∃ T' : edgeFormSpace L n 0 0 →ₗ[ℝ] edgeFormSpace L n 0 0,
      ∀ f : edgeFormSpace L n 0 0, (T' f : Edge L n 0 0 → ComplexMatrix2) = massiveHessian U f := by
  have hm : ∀ f : edgeFormSpace L n 0 0, massiveHessian U f ∈ edgeFormSpace L n 0 0 := fun f =>
    (edgeFormSpace L n 0 0).add_mem (complexHessianOperator_mem hP hA hK hU f.2)
      (covDiff_mem hF hU (covDiffTranspose_mem hF hU f.2))
  have hc : ∀ f : edgeFormSpace L n 0 0, (f : Edge L n 0 0 → ComplexMatrix2) ∈ complexEdgeForms L n 0 0 :=
    fun f => mem_complexEdgeForms_of_mem f.2
  have ht : ∀ f : edgeFormSpace L n 0 0, covDiffTranspose U f ∈
      GroupLieProduct.tracelessFunctions (Vertex L n 0 0) := fun f =>
    hF.transpose_mem_complex _ (hc f)
  refine ⟨{ toFun := fun f => ⟨massiveHessian U f, hm f⟩, map_add' := ?_, map_smul' := ?_ },
    fun f => rfl⟩
  · intro f g
    apply Subtype.ext
    change massiveHessian U (f + g : Edge L n 0 0 → ComplexMatrix2) =
      massiveHessian U f + massiveHessian U g
    simp only [massiveHessian_eq]
    rw [complexHessianOperator_add hK (hc f) (hc g)]
    have e1 : covDiffTranspose U (f + g : Edge L n 0 0 → ComplexMatrix2) =
        covDiffTranspose U f + covDiffTranspose U g :=
      hF.transpose_apply_add _ (hc f) _ (hc g)
    have e2 : covDiff U (covDiffTranspose U f + covDiffTranspose U g) =
        covDiff U (covDiffTranspose U f) + covDiff U (covDiffTranspose U g) :=
      hF.apply_add _ (ht f) _ (ht g)
    rw [e1, e2]
    abel
  · intro c f
    apply Subtype.ext
    change massiveHessian U (c • (f : Edge L n 0 0 → ComplexMatrix2)) = c • massiveHessian U f
    simp only [massiveHessian_eq]
    rw [real_smul_eq_complex_smul, real_smul_eq_complex_smul, complexHessianOperator_smul hK _ (hc f)]
    have e1 : covDiffTranspose U ((c : ℂ) • (f : Edge L n 0 0 → ComplexMatrix2)) =
        (c : ℂ) • covDiffTranspose U f := hF.transpose_apply_smul _ _ (hc f)
    have e2 : covDiff U ((c : ℂ) • covDiffTranspose U f) =
        (c : ℂ) • covDiff U (covDiffTranspose U f) :=
      hF.apply_smul _ _ (ht f)
    rw [e1, e2, smul_add]
theorem pairing_massiveHessian {U : Edge L n 0 0 → ComplexMatrix2}
    (hF : TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U))
    (hK : HessianOperatorFacts U) {f g : Edge L n 0 0 → ComplexMatrix2}
    (hf : f ∈ complexEdgeForms L n 0 0) (hg : g ∈ complexEdgeForms L n 0 0) :
    edgeFormPairing f (massiveHessian U g) = complexActionHessian U f g +
      traceFinsumPairing (covDiffTranspose U f) (covDiffTranspose U g) := by
  have ht : covDiffTranspose U g ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0) :=
    hF.transpose_mem_complex g hg
  rw [massiveHessian_eq, edgeFormPairing_add_right, hK.pairing_operator f hf g hg,
    pair_covDiffTranspose hF hf ht]
theorem gaugeLaplacian_symm {U : Edge L n 0 0 → ComplexMatrix2}
    (hF : TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U))
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) (f g : vertexFunctionSpace L n 0 0) :
    traceFinsumPairing (gaugeLaplacian U f) (g : Vertex L n 0 0 → ComplexMatrix2) =
      traceFinsumPairing (f : Vertex L n 0 0 → ComplexMatrix2) (gaugeLaplacian U g) := by
  have hf := mem_complexEdgeForms_of_mem (covDiff_mem hF hU f.2)
  have hg := mem_complexEdgeForms_of_mem (covDiff_mem hF hU g.2)
  rw [traceFinsumPairing_comm (f : Vertex L n 0 0 → ComplexMatrix2), gaugeLaplacian_eq,
    gaugeLaplacian_eq, pair_covDiffTranspose hF hf (mem_tracelessFunctions_of_mem g.2),
    pair_covDiffTranspose hF hg (mem_tracelessFunctions_of_mem f.2), edgeFormPairing_comm]
theorem gaugeLaplacian_re_nonneg {U : Edge L n 0 0 → ComplexMatrix2}
    (hF : TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U))
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) (f : vertexFunctionSpace L n 0 0) :
    0 ≤ (traceFinsumPairing (gaugeLaplacian U f) (f : Vertex L n 0 0 → ComplexMatrix2)).re := by
  have hd := covDiff_mem hF hU f.2
  rw [gaugeLaplacian_eq, pair_covDiffTranspose hF (mem_complexEdgeForms_of_mem hd)
    (mem_tracelessFunctions_of_mem f.2)]
  exact traceFinsumPairing_self_re_nonneg fun b => edgeForm_apply_mem hd b.1
theorem massiveHessian_symm {U : Edge L n 0 0 → ComplexMatrix2}
    (hF : TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U))
    (hK : HessianOperatorFacts U) (f g : edgeFormSpace L n 0 0) :
    edgeFormPairing (massiveHessian U f) (g : Edge L n 0 0 → ComplexMatrix2) =
      edgeFormPairing (f : Edge L n 0 0 → ComplexMatrix2) (massiveHessian U g) := by
  have hf := mem_complexEdgeForms_of_mem f.2
  have hg := mem_complexEdgeForms_of_mem g.2
  rw [edgeFormPairing_comm, pairing_massiveHessian hF hK hg hf, pairing_massiveHessian hF hK hf hg,
    (hK.isSymmBilinear 0 _ hf _ hf _ hg).2.2, traceFinsumPairing_comm]
omit [Finite (Vertex L n 0 0)] in
theorem edgeCoboundary_mem {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0)
    (p : Face L n 0 0) : edgeCoboundary B p ∈ ComplexMatrix2.hermitianTraceless := by
  simp only [edgeCoboundary]
  have h := edgeForm_apply_mem hB
  exact ComplexMatrix2.hermitianTraceless.sub_mem (ComplexMatrix2.hermitianTraceless.sub_mem
    (ComplexMatrix2.hermitianTraceless.add_mem (h _) (h _)) (h _)) (h _)
end RealOperators
section ContinuityNearIdentity
open HessianKernel FaceTermDerivatives
theorem continuousAt_matrix_inv {X : Type} [TopologicalSpace X] {c : X → ComplexMatrix2} {x : X}
    (hc : ContinuousAt c x) (hd : (c x).det ≠ 0) : ContinuousAt (fun u => (c u)⁻¹) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  have h1 : ContinuousAt (fun u => (c u).det) x :=
    (continuous_id.matrix_det).continuousAt.comp hc
  have h2 : ContinuousAt (fun u => (c u).adjugate) x :=
    (continuous_id.matrix_adjugate).continuousAt.comp hc
  exact (h1.inv₀ hd).smul h2
theorem continuousAt_conjugateBy {X : Type} [TopologicalSpace X] {c : X → ComplexMatrix2} {x : X}
    (hc : ContinuousAt c x) (hd : (c x).det ≠ 0) (A : ComplexMatrix2) :
    ContinuousAt (fun u => ComplexMatrix2.conjugateBy (c u) A) x := by
  simp only [ComplexMatrix2.conjugateBy]
  exact (hc.mul continuousAt_const).mul (continuousAt_matrix_inv hc hd)
theorem continuousAt_fullTrace {X : Type} [TopologicalSpace X] {c : X → ComplexMatrix2} {x : X}
    (hc : ContinuousAt c x) : ContinuousAt (fun u => ComplexMatrix2.fullTrace (c u)) x :=
  (continuous_id.matrix_trace).continuousAt.comp hc
theorem continuousAt_secondDerivExpr {X : Type} [TopologicalSpace X]
    {Y : X → Fin 4 → ComplexMatrix2} {W : X → ComplexMatrix2} {x : X}
    (hY : ∀ i, ContinuousAt (fun u => Y u i) x) (hW : ContinuousAt W x)
    (hd : (W x).det ≠ 0) :
    ContinuousAt (fun u => secondDerivExpr (Y u) (W u)) x := by
  have hS : ContinuousAt (fun u => ∑ i, Y u i) x :=
    tendsto_finsetSum _ fun i _ => hY i
  have hC : ContinuousAt (fun u => commutatorSum (Y u)) x := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun m _ => ?_
    exact ((hY i).mul (hY m)).sub ((hY m).mul (hY i))
  simp only [secondDerivExpr, ComplexMatrix2.halfTrace]
  refine ContinuousAt.add ?_ ?_
  · exact (continuousAt_const.mul (continuousAt_fullTrace hW)).mul
      (continuousAt_const.mul (continuousAt_fullTrace (hS.mul hS)))
  · exact continuousAt_const.mul
      (continuousAt_fullTrace (hC.mul (hW.sub (continuousAt_matrix_inv hW hd))))
variable {L n : ℕ}
abbrev identityField (L n : ℕ) : Edge L n 0 0 → ComplexMatrix2 := fun _ => 1
theorem identityField_mem :
    identityField L n ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup :=
  ⟨fun _ _ => Submonoid.one_mem _, fun _ _ => by simp⟩
theorem continuousAt_field_apply (b : Edge L n 0 0) :
    ContinuousAt (fun U : Edge L n 0 0 → ComplexMatrix2 => U b) (identityField L n) :=
  (continuous_apply b).continuousAt
theorem continuousAt_plaquetteHolonomy (p : Face L n 0 0) :
    ContinuousAt (fun U : Edge L n 0 0 → ComplexMatrix2 => PeriodicLattice.plaquetteHolonomy U p)
      (identityField L n) := by
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil]
  exact (continuousAt_field_apply _).mul ((continuousAt_field_apply _).mul
    ((continuousAt_field_apply _).mul ((continuousAt_field_apply _).mul continuousAt_const)))
theorem plaquetteHolonomy_identityField (p : Face L n 0 0) :
    PeriodicLattice.plaquetteHolonomy (identityField L n) p = 1 := by
  simp [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds]
theorem continuousAt_faceTransports (p : Face L n 0 0) (i : Fin 4) :
    ContinuousAt (fun U : Edge L n 0 0 → ComplexMatrix2 => faceTransports U p i)
      (identityField L n) := by
  fin_cases i
  · exact continuousAt_const
  · exact continuousAt_field_apply _
  · exact ((continuousAt_field_apply _).mul (continuousAt_field_apply _)).mul
      (continuousAt_matrix_inv (continuousAt_field_apply _) (by simp))
  · exact continuousAt_plaquetteHolonomy p
theorem faceTransports_identityField (p : Face L n 0 0) (i : Fin 4) :
    faceTransports (identityField L n) p i = 1 := by
  fin_cases i
  · rfl
  · rfl
  · simp [faceTransports]
  · exact plaquetteHolonomy_identityField p
theorem continuousAt_transportedForm (B : Edge L n 0 0 → ComplexMatrix2) (p : Face L n 0 0)
    (i : Fin 4) :
    ContinuousAt (fun U : Edge L n 0 0 → ComplexMatrix2 => transportedForm U B p i)
      (identityField L n) :=
  (continuousAt_conjugateBy (continuousAt_faceTransports p i)
    (by rw [faceTransports_identityField]; simp) _).const_smul (transportSign i)
theorem continuousAt_diag_sum [Finite (Face L n 0 0)] (B : Edge L n 0 0 → ComplexMatrix2) :
    ContinuousAt (fun U : Edge L n 0 0 → ComplexMatrix2 => ∑ᶠ p : Face L n 0 0,
      secondDerivExpr (transportedForm U B p) (PeriodicLattice.plaquetteHolonomy U p))
      (identityField L n) := by
  have := Fintype.ofFinite (Face L n 0 0)
  simp only [finsum_eq_sum_of_fintype]
  refine tendsto_finsetSum _ fun p _ => ?_
  exact continuousAt_secondDerivExpr (fun i => continuousAt_transportedForm B p i)
    (continuousAt_plaquetteHolonomy p) (by rw [plaquetteHolonomy_identityField]; simp)
theorem continuousAt_pairing_covDiff [Finite (Vertex L n 0 0)] (f : Edge L n 0 0 → ComplexMatrix2)
    (l : Vertex L n 0 0 → ComplexMatrix2) :
    ContinuousAt (fun U : Edge L n 0 0 → ComplexMatrix2 => edgeFormPairing f (covDiff U l))
      (identityField L n) := by
  have := Fintype.ofFinite (PositiveEdge L n 0 0)
  simp only [edgeFormPairing, traceFinsumPairing_eq_sum, restrictToPositiveEdges,
    ComplexMatrix2.halfTrace]
  refine tendsto_finsetSum _ fun b _ => ?_
  refine continuousAt_const.mul (continuousAt_fullTrace (continuousAt_const.mul ?_))
  simp only [covDiff_apply_of_positive _ _ b.2]
  exact (continuousAt_conjugateBy (continuousAt_field_apply _) (by simp) _).sub continuousAt_const
theorem halfTrace_mul_eq_sum_pauli {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (X * Y) = ∑ a, ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily a) *
      ComplexMatrix2.halfTrace (Y * ComplexMatrix2.pauliFamily a) := by
  have tX : X 0 0 + X 1 1 = 0 := by
    have : ComplexMatrix2.fullTrace X = 0 := hX
    simpa [ComplexMatrix2.fullTrace, Matrix.trace, Fin.sum_univ_two] using this
  have tY : Y 0 0 + Y 1 1 = 0 := by
    have : ComplexMatrix2.fullTrace Y = 0 := hY
    simpa [ComplexMatrix2.fullTrace, Matrix.trace, Fin.sum_univ_two] using this
  have x1 : X 1 1 = -X 0 0 := by linear_combination tX
  have y1 : Y 1 1 = -Y 0 0 := by linear_combination tY
  simp only [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
    OneLoop.pauliZ, Fin.sum_univ_three, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, x1, y1]
  simp
  have hI := Complex.I_mul_I
  ring_nf
  simp only [Complex.I_sq]
  ring
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
open Classical in
def singlePauli (x : Vertex L n 0 0) (a : Fin 3) : Vertex L n 0 0 → ComplexMatrix2 :=
  fun y => if y = x then ComplexMatrix2.pauliFamily a else 0
theorem singlePauli_mem (x : Vertex L n 0 0) (a : Fin 3) :
    singlePauli x a ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0) := by
  refine mem_tracelessFunctions fun y => ?_
  by_cases h : y = x
  · simp only [singlePauli, if_pos h]
    exact pauliFamily_mem_traceless a
  · simp only [singlePauli, if_neg h]
    exact ComplexMatrix2.traceless.zero_mem
theorem pairing_singlePauli (l : Vertex L n 0 0 → ComplexMatrix2) (x : Vertex L n 0 0) (a : Fin 3) :
    traceFinsumPairing l (singlePauli x a) =
      ComplexMatrix2.halfTrace (l x * ComplexMatrix2.pauliFamily a) := by
  rw [traceFinsumPairing, finsum_eq_single _ x]
  · simp [singlePauli]
  · intro y hy
    simp [singlePauli, hy]
variable [Finite (Vertex L n 0 0)]
theorem pairing_covDiffTranspose_eq_sum [Fintype (Vertex L n 0 0)] {U : Edge L n 0 0 → ComplexMatrix2}
    (hF : TransposePairFacts (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0) (covDiff U))
    {f g : Edge L n 0 0 → ComplexMatrix2} (hf : f ∈ complexEdgeForms L n 0 0)
    (hg : g ∈ complexEdgeForms L n 0 0) :
    traceFinsumPairing (covDiffTranspose U f) (covDiffTranspose U g) =
      ∑ x : Vertex L n 0 0, ∑ a, edgeFormPairing f (covDiff U (singlePauli x a)) *
        edgeFormPairing g (covDiff U (singlePauli x a)) := by
  have tf : covDiffTranspose U f ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0) :=
    hF.transpose_mem_complex f hf
  have tg : covDiffTranspose U g ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0) :=
    hF.transpose_mem_complex g hg
  rw [traceFinsumPairing_eq_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [halfTrace_mul_eq_sum_pauli (vertex_apply_mem_traceless tf x) (vertex_apply_mem_traceless tg x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← pair_covDiffTranspose hF hf (singlePauli_mem x a),
    ← pair_covDiffTranspose hF hg (singlePauli_mem x a), pairing_singlePauli, pairing_singlePauli]
theorem continuousWithinAt_pairing_massiveHessian [Finite (Face L n 0 0)]
    (hP : FaceTermDerivatives.HoldsOnPeriodicLevel L n 0 0)
    (hA : HessianKernel.HoldsOnTorus L n 0 0)
    (hX : CovDiffTransposes.OnTorus L n 0 0)
    (f g : edgeFormSpace L n 0 0) :
    ContinuousWithinAt
      (fun U => (edgeFormPairing (f : Edge L n 0 0 → ComplexMatrix2) (massiveHessian U g)).re)
      (fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) (identityField L n) := by
  have := Fintype.ofFinite (Vertex L n 0 0)
  have hf := mem_complexEdgeForms_of_mem f.2
  have hg := mem_complexEdgeForms_of_mem g.2
  have hS : (f + g : Edge L n 0 0 → ComplexMatrix2) ∈ edgeFormSpace L n 0 0 :=
    (edgeFormSpace L n 0 0).add_mem f.2 g.2
  let d : (Edge L n 0 0 → ComplexMatrix2) → (Edge L n 0 0 → ComplexMatrix2) → ℂ := fun B U =>
    ∑ᶠ p : Face L n 0 0,
      secondDerivExpr (transportedForm U B p) (PeriodicLattice.plaquetteHolonomy U p)
  let F : (Edge L n 0 0 → ComplexMatrix2) → ℂ := fun U =>
    (1 / 2) * (d (f + g : Edge L n 0 0 → ComplexMatrix2) U - d f U - d g U) +
      ∑ x : Vertex L n 0 0, ∑ a,
        edgeFormPairing (f : Edge L n 0 0 → ComplexMatrix2) (covDiff U (singlePauli x a)) *
        edgeFormPairing (g : Edge L n 0 0 → ComplexMatrix2) (covDiff U (singlePauli x a))
  have hc : ContinuousAt F (identityField L n) := by
    refine ContinuousAt.add (continuousAt_const.mul
      (((continuousAt_diag_sum _).sub (continuousAt_diag_sum _)).sub (continuousAt_diag_sum _))) ?_
    refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun a _ => ?_
    exact (continuousAt_pairing_covDiff _ _).mul (continuousAt_pairing_covDiff _ _)
  have hval : ∀ U ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup,
      edgeFormPairing (f : Edge L n 0 0 → ComplexMatrix2) (massiveHessian U g) = F U := by
    intro U hU
    have hUc := compact_field_mem_complex hU
    have hF := covDiff_transposePairFacts hX hUc
    have hK := hessianOperatorFacts hA hX hUc
    have hd : ∀ B ∈ edgeFormSpace L n 0 0, d B U = complexActionHessian U B B :=
      fun B hB => ((hP B (mem_complexEdgeForms_of_mem hB)).1 U hUc).2.1
    simp only [F]
    rw [pairing_massiveHessian hF hK hf hg, pairing_covDiffTranspose_eq_sum hF hf hg, hd _ f.2,
      hd _ g.2, hd _ hS,
      apply_eq_polarization hK.isSymmBilinear hf hg (mem_complexEdgeForms_of_mem hS)]
  have hw : ContinuousWithinAt (fun U => (F U).re)
      (fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup) (identityField L n) :=
    (Complex.continuous_re.continuousAt.comp hc).continuousWithinAt
  exact hw.congr (fun U hU => by rw [hval U hU]) (by rw [hval _ identityField_mem])
theorem massiveHessian_identityField_re_nonneg [Finite (Face L n 0 0)]
    (hP : FaceTermDerivatives.HoldsOnPeriodicLevel L n 0 0)
    (hA : HessianKernel.HoldsOnTorus L n 0 0)
    (hX : CovDiffTransposes.OnTorus L n 0 0)
    (f : edgeFormSpace L n 0 0) :
    0 ≤ (edgeFormPairing (massiveHessian (identityField L n) f)
      (f : Edge L n 0 0 → ComplexMatrix2)).re := by
  have hU := identityField_mem (L := L) (n := n)
  have hUc := compact_field_mem_complex hU
  have hF := covDiff_transposePairFacts hX hUc
  have hK := hessianOperatorFacts hA hX hUc
  have hf := mem_complexEdgeForms_of_mem f.2
  have ht := covDiffTranspose_mem hF hU f.2
  rw [edgeFormPairing_comm, pairing_massiveHessian hF hK hf hf, (hP f hf).2, Complex.add_re]
  exact add_nonneg (traceFinsumPairing_self_re_nonneg (edgeCoboundary_mem f.2))
    (traceFinsumPairing_self_re_nonneg (vertex_apply_mem ht))
instance instFiniteDimensionalVertexFunctions : FiniteDimensional ℝ (vertexFunctionSpace L n 0 0) :=
  FiniteDimensional.finiteDimensional_submodule _
instance instFiniteDimensionalEdgeForms : FiniteDimensional ℝ (edgeFormSpace L n 0 0) :=
  FiniteDimensional.finiteDimensional_submodule _
theorem positiveDeterminantsOnTorus [Finite (Face L n 0 0)]
    (hP : FaceTermDerivatives.HoldsOnPeriodicLevel L n 0 0)
    (hA : HessianKernel.HoldsOnTorus L n 0 0)
    (hX : CovDiffTransposes.OnTorus L n 0 0)
    {z : ℝ} (hz : 0 < z) : PositiveDeterminantsOnTorus L n z := by
  refine ⟨fun U hU => ?_, ?_⟩
  · have hUc := compact_field_mem_complex hU
    have hF := covDiff_transposePairFacts hX hUc
    have hK := hessianOperatorFacts hA hX hUc
    obtain ⟨T, hT⟩ := exists_linear_gaugeLaplacian hF hU
    exact ⟨⟨⟨T, hT⟩, gaugeLaplacian_symm hF hU⟩,
      ⟨exists_linear_massiveHessian hP hA hF hK hU, massiveHessian_symm hF hK⟩,
      shiftedDetOn_pos vertexInnerProduct T hT (gaugeLaplacian_re_nonneg hF hU) hz⟩
  · refine eventually_shiftedDetOn_pos (T := massiveHessian) edgeInnerProduct identityField_mem
      ?_ ?_ ?_ hz
    · intro U hU
      have hUc := compact_field_mem_complex hU
      exact exists_linear_massiveHessian hP hA (covDiff_transposePairFacts hX hUc)
        (hessianOperatorFacts hA hX hUc) hU
    · exact massiveHessian_identityField_re_nonneg hP hA hX
    · exact continuousWithinAt_pairing_massiveHessian hP hA hX
end ContinuityNearIdentity
theorem hessianSymmAndDetsPositive (hA : HessianKernel.KernelProperties)
    (hP : FaceTermDerivatives.Statement)
    (hX : CovDiffTransposes.Claim)
    (hE : FaceSums.FacesAndPairings) : HessianSymmAndDetsPositive := by
  intro L hL
  refine ⟨fun k j hj => ⟨fun n hn => ?_, ?_⟩, fun z hz n hn => ?_⟩
  · exact hessianSymmRealOnTorus ((hP L hL k j hj).1 n hn) ((hA L hL k j hj).1 n hn)
  · exact hessianSymmRealOnFullSpace (hP L hL k j hj).2 (hA L hL k j hj).2
  · have h := (hE L hL 0 0 le_rfl).1 n hn
    have fs : Finite (Vertex L n 0 0) := Set.finite_univ_iff.mp (h.2.1 univ).2.1
    have fp : Finite (Face L n 0 0) := Set.finite_univ_iff.mp (h.2.2.2 univ).2.1
    exact positiveDeterminantsOnTorus ((hP L hL 0 0 le_rfl).1 n hn) ((hA L hL 0 0 le_rfl).1 n hn)
      ((hX L hL 0 0 le_rfl).1 n hn) hz
end YangMills.Construction.Tower.HessianDeterminants
end
