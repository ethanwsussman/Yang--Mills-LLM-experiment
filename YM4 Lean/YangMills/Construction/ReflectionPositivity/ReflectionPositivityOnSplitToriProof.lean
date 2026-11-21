import YangMills.Construction.ReflectionPositivity.CrossingIntegralIsAReflectedSeriesAtALinkMirror
import YangMills.Construction.ReflectionPositivity.CrossingIntegralIsAReflectedSeriesAtAnIntegerPosition
import YangMills.Construction.ReflectionPositivity.FormIsASquareOfAReflectedSeries
import YangMills.Construction.ReflectionPositivity.IntegralOverTheTwoHalvesFactorsProof
import YangMills.Construction.ReflectionPositivity.PullBacksOnASplitTorus
import YangMills.Construction.ReflectionPositivity.ReflectionPositivityOnSplitTori
import YangMills.Construction.ReflectionPositivity.ReflectionPreservesThePerturbedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace SplitTorusPositivity
open PeriodSublattice NormalFamilies
theorem level_int_or_half_int {v : AmbientSpace} (hv : v ∈ normalSet) {t : ℝ}
    (ht : IsAllowedLevel 1 v t) :
    (∃ k : ℤ, t = (k : ℝ)) ∨ ∃ k : ℤ, t = (k : ℝ) + 1 / 2 := by apply _root_.YangMills.Construction.InfiniteLattice.HalvesFactorizationProof.level_int_or_half <;> assumption
section SquareForm
variable {Y : Type} [MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
theorem integrable_conj_mul_of_bdd {f g : Y → ℂ} (hf : Measurable f) (hg : Measurable g) {A B : ℝ}
    (hA : ∀ y, ‖f y‖ ≤ A) (hB : ∀ y, ‖g y‖ ≤ B) :
    Integrable (fun y => conj (f y) * g y) μ := by
  refine Integrable.of_bound
    ((Complex.continuous_conj.measurable.comp hf).mul hg).aestronglyMeasurable (A * B)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (hA y) (hB y) (norm_nonneg _) ((norm_nonneg _).trans (hA y))
omit [IsFiniteMeasure μ] in
theorem integral_conj_mul_symm (f g : Y → ℂ) :
    ∫ y, conj (f y) * g y ∂μ = conj (∫ y, conj (g y) * f y ∂μ) := by
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mul_comm]
omit [IsFiniteMeasure μ] in
theorem integral_conj_mul_self_nonneg (f : Y → ℂ) : 0 ≤ ∫ y, conj (f y) * f y ∂μ := by
  have h : (fun y => conj (f y) * f y) = fun y => ((‖f y‖ ^ 2 : ℝ) : ℂ) := by
    funext y
    rw [Complex.conj_mul']
    push_cast
    rfl
  rw [h, integral_complex_ofReal]
  exact Complex.zero_le_real.2 (integral_nonneg fun y => by positivity)
end SquareForm
variable {Λ : PeriodSublattice 1}
theorem exp_mem_plusAlgebra {v : AmbientSpace} {z : ℤ} {t : ℝ} {V : Λ.QuotientField → ℝ}
    (hV : (fun U => (V U : ℂ)) ∈ Λ.plusAlgebra v z t) :
    (fun U => ((Real.exp (V U) : ℝ) : ℂ)) ∈ Λ.plusAlgebra v z t := by
  obtain ⟨hm, ⟨M, hM⟩, hd⟩ := (Λ.mem_boundedAlgebra).1 hV
  have hVm : Measurable V := by
    have := Complex.measurable_re.comp hm
    simpa [Function.comp_def] using this
  refine (Λ.mem_boundedAlgebra).2 ⟨?_, ⟨Real.exp M, fun U => ?_⟩, fun U U' h => ?_⟩
  · exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp hVm)
  · have h1 : V U ≤ M := by
      have := hM U
      rw [Complex.norm_real] at this
      exact (le_abs_self _).trans this
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 h1
  · have := hd U U' h
    have h2 : V U = V U' := Complex.ofReal_injective this
    simp only [h2]
end SplitTorusPositivity
open SplitTorusPositivity NormalFamilies
theorem splitTorusReflectionPositivity_holds
    (hPull : SplitTorusPullbacks)
    (hTwo : TwoLevelsOfOneReflection)
    (hSq : ReflectionPairingIsIntegralSquare)
    (hInt : CrossingIntegralReflectionSeriesInteger)
    (hHalf : CrossingIntegralReflectionSeriesHalfInteger)
    (hPert : PerturbedReflMeasureInvariant) :
    SplitTorusReflectionPositivity := by
  intro β hβ Λ v hv z hs t ht L
  obtain ⟨hθ, hAll, -⟩ := hPull β hβ Λ v hv z hs
  obtain ⟨-, -, -, -, hInv⟩ := hθ t ht
  have hLf : IsClassIsometry v L.reflectSymmetry.toFun :=
    isClassIsometry_reflectAcross ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hW⟩ := hAll _ hLf
  obtain ⟨hz, hRest⟩ := hTwo Λ v hv z t ht hs
  obtain ⟨-, -, -, -, -, -, -, hMinus, -⟩ := hRest
  have hSer : Λ.HasReflectionSeries z L
      (Λ.integrateOut (Λ.crossingLinks v z t)
        fun U => (Λ.splitFaceWeight β v z t U : ℂ))
      (Real.exp (β * (Λ.numSplitPlaquettes v z t : ℝ))) := by
    rcases level_int_or_half_int hv ht with h | h
    · exact hInt β hβ Λ v hv z hs t ht h
    · exact hHalf β hβ Λ v hv z hs t ht h
  obtain ⟨Y, mY, ν, Φ, hFin, hMeas, hBdd, hRep⟩ := hSq β hβ Λ v hv z hs t ht _ hSer
  have hRep' : ∀ F ∈ Λ.plusAlgebra v z t, ∀ G ∈ Λ.plusAlgebra v z t,
      ∃ f g : ↥(Λ.plusAlgebra v z t), f.1 = F ∧ g.1 = G ∧
        Λ.reflectionPairing β L G F = ∫ y, conj (Φ g y) * Φ f y ∂ν :=
    fun F hF G hG => ⟨⟨F, hF⟩, ⟨G, hG⟩, rfl, rfl, hRep ⟨F, hF⟩ ⟨G, hG⟩⟩
  have hIntg : ∀ f g : ↥(Λ.plusAlgebra v z t),
      Integrable (fun y => conj (Φ g y) * Φ f y) ν :=
    fun f g => integrable_conj_mul_of_bdd (hMeas g) (hMeas f) (hBdd g) (hBdd f)
  have hLin : ∀ (f g h : ↥(Λ.plusAlgebra v z t)) (w : ℂ),
      Λ.reflectionPairing β L g.1 (w • f.1 + h.1) =
        w * Λ.reflectionPairing β L g.1 f.1 + Λ.reflectionPairing β L g.1 h.1 := by
    intro f g h w
    have e := hRep (w • f + h) g
    have hCoe : ((w • f + h : ↥(Λ.plusAlgebra v z t)) : Λ.QuotientField → ℂ) =
        w • f.1 + h.1 := rfl
    rw [hCoe] at e
    rw [e, hRep f g, hRep h g, ← integral_const_mul, ← integral_add
      ((hIntg f g).const_mul w) (hIntg h g)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hHerm : ∀ F ∈ Λ.plusAlgebra v z t, ∀ G ∈ Λ.plusAlgebra v z t,
      Λ.reflectionPairing β L G F = conj (Λ.reflectionPairing β L F G) := by
    intro F hF G hG
    rw [hRep ⟨F, hF⟩ ⟨G, hG⟩, hRep ⟨G, hG⟩ ⟨F, hF⟩]
    exact integral_conj_mul_symm _ _
  have hPos : ∀ F ∈ Λ.plusAlgebra v z t, 0 ≤ Λ.reflectionPairing β L F F := by
    intro F hF
    rw [hRep ⟨F, hF⟩ ⟨F, hF⟩]
    exact integral_conj_mul_self_nonneg _
  refine ⟨hW, ⟨Y, mY, ν, Φ, hFin, hMeas, hBdd, fun F G => hRep F G⟩, ?_, hHerm, hPos,
    hSer, ?_⟩
  · intro F hF G hG H hH w
    refine ⟨hLin ⟨F, hF⟩ ⟨G, hG⟩ ⟨H, hH⟩ w, ?_⟩
    have hMem : w • F + H ∈ Λ.plusAlgebra v z t :=
      add_mem (Subalgebra.smul_mem _ hF w) hH
    have h1 : Λ.reflectionPairing β L G (w • F + H) =
        w * Λ.reflectionPairing β L G F + Λ.reflectionPairing β L G H :=
      hLin ⟨F, hF⟩ ⟨G, hG⟩ ⟨H, hH⟩ w
    rw [hHerm G hG _ hMem, h1, map_add, map_mul, ← hHerm G hG F hF, ← hHerm G hG H hH]
  · intro V hV
    obtain ⟨hProb, hPres⟩ := hPert β hβ Λ v hv z hs t ht V hV
    have hUp : ∀ F ∈ Λ.plusAlgebra v z t,
        0 ≤ ∫ U, Λ.conjReflect L F U * F U *
          (Λ.perturbedReflWeight β L V U : ℂ) ∂Λ.quotientHaar := by
      intro F hF
      have hG := Subalgebra.mul_mem _ hF (exp_mem_plusAlgebra hV)
      have h := hPos _ hG
      have hEq : Λ.reflectionPairing β L
          (F * fun U => ((Real.exp (V U) : ℝ) : ℂ)) (F * fun U => ((Real.exp (V U) : ℝ) : ℂ)) =
          ∫ U, Λ.conjReflect L F U * F U *
            (Λ.perturbedReflWeight β L V U : ℂ) ∂Λ.quotientHaar := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        simp only [PeriodSublattice.conjReflect, PeriodSublattice.compPullback,
          PeriodSublattice.perturbedReflWeight, Pi.mul_apply, map_mul, Complex.conj_ofReal,
          Real.exp_add, Complex.ofReal_mul]
        ring
      rwa [hEq] at h
    refine ⟨hProb, hPres, ?_⟩
    rintro F (hF | hF)
    · exact hUp F hF
    · have hF' : Λ.conjReflect L F ∈ Λ.plusAlgebra v z t := by
        have : Λ.conjReflect L F ∈
            Λ.conjReflect L '' (Λ.minusAlgebra v z t : Set (Λ.QuotientField → ℂ)) :=
          Set.mem_image_of_mem _ hF
        rw [hMinus] at this
        exact this
      have hBB : Λ.IsBoundedBorelFn F := ⟨hF.1, hF.2.1⟩
      have h := hUp _ hF'
      rw [hInv F hBB] at h
      have hEq : ∫ U, F U * Λ.conjReflect L F U *
            (Λ.perturbedReflWeight β L V U : ℂ) ∂Λ.quotientHaar =
          ∫ U, Λ.conjReflect L F U * F U *
            (Λ.perturbedReflWeight β L V U : ℂ) ∂Λ.quotientHaar :=
        integral_congr_ae (Filter.Eventually.of_forall fun U => by
          simp only [mul_comm (F U)])
      rwa [hEq] at h
end YangMills.Construction.InfiniteLattice
