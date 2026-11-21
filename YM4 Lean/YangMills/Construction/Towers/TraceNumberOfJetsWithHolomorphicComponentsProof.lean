import YangMills.Construction.ComplexAnalysis.BoxIntegralHolomorphic
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import YangMills.Construction.PeriodicOperators.ProductOfLocalOperatorFunctionsProof
import YangMills.Construction.Towers.SumsProductsAndTransposesOfJetsWithHolomorphicComponentsProof
import YangMills.Construction.Towers.TraceNumberOfJetsWithHolomorphicComponents
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.JetTraceHolomorphy
open Coordinates
open PeriodicOperators
open ScaledOperatorFunctions
theorem isHolomorphicIn_scalar_iff {N : ℕ} {O : Set (ComplexCoordinates N)}
    {g : ComplexCoordinates N → ℂ} :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O (fun x _ => g x) ↔
      IsOpen O ∧ ContinuousOn g O ∧ ∀ a ∈ O, ∀ j : Fin N, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ (fun ζ : ℂ => g (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.PeriodicOperators.OpFunComp.isHolomorphicIn_scalar_iff <;> assumption
theorem isHolomorphicIn_sum {N : ℕ} {ι : Type} [Fintype ι] {O : Set (ComplexCoordinates N)}
    (hO : IsOpen O) {f : ι → ComplexCoordinates N → ℂ}
    (h : ∀ c, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => f c x) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => ∑ c, f c x := by
  refine isHolomorphicIn_scalar_iff.2 ⟨hO, continuousOn_finsetSum _ fun c _ =>
    (isHolomorphicIn_scalar_iff.1 (h c)).2.1, fun a ha j => ?_⟩
  have hall : ∀ᶠ ζ in 𝓝 (0 : ℂ), ∀ c, DifferentiableAt ℂ
      (fun ζ : ℂ => f c (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ :=
    eventually_all.2 fun c => (isHolomorphicIn_scalar_iff.1 (h c)).2.2 a ha j
  filter_upwards [hall] with ζ hζ
  exact DifferentiableAt.fun_sum fun c _ => hζ c
theorem isHolomorphicIn_const_mul {N : ℕ} {O : Set (ComplexCoordinates N)} (z : ℂ)
    {g : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => g x) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => z * g x := by
  obtain ⟨hO, hc, hd⟩ := isHolomorphicIn_scalar_iff.1 h
  refine isHolomorphicIn_scalar_iff.2 ⟨hO, continuousOn_const.mul hc, fun a ha j => ?_⟩
  filter_upwards [hd a ha j] with ζ hζ
  exact hζ.const_mul z
theorem trace_eq_sum_linearMapEntry {J : Type} [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J → ℂ)) :
    LinearMap.trace ℂ (J → ℂ) M = ∑ c, linearMapEntry M c c := by apply _root_.YangMills.SharedProofs.p9894 <;> assumption
theorem splitCoords_appendCoords (x y : ComplexCoordinates 4) :
    splitCoords (n := 4) (n' := 4) (appendCoords x y) = (x, y) := by apply _root_.YangMills.Construction.Tower.FullSpace.JetClosure.splitCoords_appendCoords <;> assumption
theorem continuous_appendCoords_left (y : ComplexCoordinates 4) :
    Continuous fun x : ComplexCoordinates 4 => appendCoords (n := 4) (n' := 4) x y := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [appendCoords, Fin.append_left]
    exact continuous_apply i
  · simp only [appendCoords, Fin.append_right]
    exact continuous_const
theorem continuous_appendCoords_right (x : ComplexCoordinates 4) :
    Continuous fun y : ComplexCoordinates 4 => appendCoords (n := 4) (n' := 4) x y := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [appendCoords, Fin.append_left]
    exact continuous_const
  · simp only [appendCoords, Fin.append_right]
    exact continuous_apply i
theorem appendCoords_add_smul_stdBasisVector (κ a : ComplexCoordinates 4) (ζ : ℂ) (j : Fin 4) :
    appendCoords (n := 4) (n' := 4) κ (a + ζ • ComplexCoordinates.stdBasisVector j) =
      appendCoords κ a + ζ • ComplexCoordinates.stdBasisVector (Fin.natAdd 4 j) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have hne : Fin.castAdd 4 i ≠ Fin.natAdd 4 j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp only [appendCoords, Pi.add_apply, Pi.smul_apply, Fin.append_left,
      ComplexCoordinates.stdBasisVector, smul_eq_mul]
    rw [Pi.single_eq_of_ne hne, mul_zero, add_zero]
  · simp only [appendCoords, Pi.add_apply, Pi.smul_apply, Fin.append_right,
      ComplexCoordinates.stdBasisVector, smul_eq_mul]
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · have hne : Fin.natAdd 4 i ≠ Fin.natAdd 4 j := by
        intro e
        apply h
        have := congrArg Fin.val e
        simp at this
        exact Fin.ext this
      rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne hne]
theorem isHolomorphicIn_slice {U : Set (ComplexCoordinates (4 + 4))}
    {f : ComplexCoordinates (4 + 4) → ℂ}
    (hf : ComplexCoordinates.IsHolomorphicIn (N' := 1) U fun x _ => f x)
    {P : Set (ComplexCoordinates 4)} (hP : IsOpen P) (κ : ComplexCoordinates 4)
    (hU : ∀ p ∈ P, appendCoords (n := 4) (n' := 4) κ p ∈ U) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => f (appendCoords κ p) := by
  obtain ⟨-, hc, hd⟩ := isHolomorphicIn_scalar_iff.1 hf
  refine isHolomorphicIn_scalar_iff.2 ⟨hP, hc.comp (continuous_appendCoords_right κ).continuousOn hU,
    fun a ha j => ?_⟩
  filter_upwards [hd _ (hU a ha) (Fin.natAdd 4 j)] with ζ hζ
  simpa only [appendCoords_add_smul_stdBasisVector] using hζ
theorem sqrtOf_div_self_le_one (w : ℝ) : RealPower.sqrtOf (w / w) ≤ 1 := by
  by_cases hw : w = 0
  · simp [hw, RealPower.sqrtOf]
  · simp [div_self hw, RealPower.sqrtOf, RealPower.rpowPos]
theorem claim_holds (hBox : ComplexAnalysis.BoxIntegralHolomorphicInParameter)
    (hNorm : HomNorm.Claim) : Claim := by
  intro δ _ P hP _ I hI T hT hsup
  have : Finite I.UnitQuot := hI.finite_quot
  have : Fintype I.UnitQuot := Fintype.ofFinite I.UnitQuot
  obtain ⟨W, -, hWR, hW⟩ := hT.open11
  have hW' : HolomorphicOnEntrywise quotHomEntries (appendSet (n := 4) (n' := 4) W)
      ((fun q : ComplexCoordinates 4 × ComplexCoordinates 4 => (T q.2).f11 q.1) ∘ splitCoords) := hW
  obtain ⟨-, hU, hent⟩ := hW'
  let F : ComplexCoordinates (4 + 4) → ℂ := fun z =>
    ∑ c, linearMapEntry ((T (splitCoords (n := 4) (n' := 4) z).2).f11
      (splitCoords (n := 4) (n' := 4) z).1) c c
  have hF : ComplexCoordinates.IsHolomorphicIn (N' := 1) (appendSet (n := 4) (n' := 4) W)
      fun z _ => F z := isHolomorphicIn_sum hU fun c => hent (c, c)
  let γ : (Fin 4 → ℝ) → ComplexCoordinates 4 → ℂ := fun t p =>
    LinearMap.trace ℂ (I.UnitQuot → ℂ) ((T p).f11 (toComplexVec t))
  have hγ : ∀ t p, γ t p = F (appendCoords (toComplexVec t) p) := by
    intro t p
    simp only [γ, F, splitCoords_appendCoords]
    exact trace_eq_sum_linearMapEntry _
  have hreal : ∀ t : Fin 4 → ℝ, toComplexVec t ∈ realDualPoints := by
    intro t j
    simp [toComplexVec]
  have hmem : ∀ t, ∀ p ∈ P, appendCoords (n := 4) (n' := 4) (toComplexVec t) p ∈
      appendSet (n := 4) (n' := 4) W :=
    fun t p hp => ⟨(toComplexVec t, p), hWR p hp _ (hreal t), rfl⟩
  have hNormEntries := (hNorm I I hI hI).2.2.2.1
  set B : ℝ≥0∞ := ⨆ p ∈ P, JetQuad.jetNorm δ p (T p) with hB
  have hnorm : ∀ t, ∀ p ∈ P, (quotHomNorm ((T p).f11 (toComplexVec t))).toReal ≤ B.toReal := by
    intro t p hp
    refine ENNReal.toReal_mono hsup.ne ?_
    calc quotHomNorm ((T p).f11 (toComplexVec t))
        ≤ ⨆ κ ∈ realDualPoints, quotHomNorm ((T p).f11 κ) :=
          le_iSup₂ (f := fun κ (_ : κ ∈ realDualPoints) => quotHomNorm ((T p).f11 κ)) _ (hreal t)
      _ ≤ JetQuad.jetNorm δ p (T p) := by
          unfold JetQuad.jetNorm
          exact le_add_self
      _ ≤ B := le_iSup₂ (f := fun p (_ : p ∈ P) => JetQuad.jetNorm δ p (T p)) p hp
  have hbound : ∀ t ∈ Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), ∀ p ∈ P,
      ‖γ t p‖ ≤ (Fintype.card I.UnitQuot : ℝ) * B.toReal := by
    intro t _ p hp
    have hsum : γ t p = ∑ c, linearMapEntry ((T p).f11 (toComplexVec t)) c c :=
      trace_eq_sum_linearMapEntry _
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    have hone : ∀ c ∈ (Finset.univ : Finset I.UnitQuot),
        ‖linearMapEntry ((T p).f11 (toComplexVec t)) c c‖ ≤ B.toReal := by
      intro c _
      refine (hNormEntries _ c c).trans ?_
      calc _ ≤ (quotHomNorm ((T p).f11 (toComplexVec t))).toReal * 1 :=
            mul_le_mul_of_nonneg_left (sqrtOf_div_self_le_one _) ENNReal.toReal_nonneg
        _ ≤ B.toReal := by simpa using hnorm t p hp
    simpa using Finset.sum_le_card_nsmul _ _ _ hone
  have hcont : ∀ p ∈ P, ContinuousOn (fun t => γ t p)
      (Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) := by
    intro p hp
    have hcv : Continuous (toComplexVec : (Fin 4 → ℝ) → Fin 4 → ℂ) :=
      continuous_pi fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
    have hpair : Continuous fun t : Fin 4 → ℝ =>
        appendCoords (n := 4) (n' := 4) (toComplexVec t) p :=
      (continuous_appendCoords_left p).comp hcv
    have := (isHolomorphicIn_scalar_iff.1 hF).2.1.comp hpair.continuousOn
      (s := Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) fun t _ => hmem t p hp
    exact this.congr fun t _ => hγ t p
  have hhol : ∀ t ∈ Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi),
      ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => γ t p := by
    intro t _
    have := isHolomorphicIn_slice hF hP (toComplexVec t) fun p hp => hmem t p hp
    simpa only [hγ] using this
  have hint := (hBox 4 4 (by norm_num) (by norm_num) (fun _ => -Real.pi) (fun _ => Real.pi)
    (fun _ => by linarith [Real.pi_pos]) P hP γ ⟨_, hbound⟩ hcont hhol).2
  exact isHolomorphicIn_const_mul _ hint
end YangMills.Construction.Tower.FullSpace.JetTraceHolomorphy
end
