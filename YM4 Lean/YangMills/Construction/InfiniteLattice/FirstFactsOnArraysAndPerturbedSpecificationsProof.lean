import YangMills.Construction.InfiniteLattice.ContinuousFunctionsOfFinitelyManyBondsAndPlaquetteEnergies
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.FactsOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.FirstFactsOnArraysAndPerturbedSpecifications
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
theorem LinkWindow.glue_agree_of_agree_outside (W : LinkWindow 1) (V : W.Assignments)
    {U U' : GaugeField 1} {M : Set (Link 1)} (h : ∀ b ∈ M, b ∉ W.links → U b = U' b) :
    ∀ b ∈ M, W.glue one_pos V U b = W.glue one_pos V U' b := by
  intro b hb
  by_cases hin : b ∈ W.links
  · simp [LinkWindow.glue, hin]
  · by_cases hopp : b.opposite ∈ W.links
    · simp [LinkWindow.glue, hin, hopp]
    · simp [LinkWindow.glue, hin, hopp, h b hb hin]
theorem continuous_complex_measurable_borel {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Continuous f) : Measurable[borel X] f := by
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  exact hf.measurable
theorem LocalObservableArray.tiltedKernel_mem_continuousLocal (A : LocalObservableArray) {β t : ℝ}
    (W : LinkWindow 1)
    (hE : (fun U => (A.windowEnergy β t W U : ℂ)) ∈ continuousLocalFunctions 1)
    (hZ : ∀ U : GaugeField 1, 0 < A.windowPartition β t W U)
    (hGlue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (hLoc : LocalFunctionProperties 1)
    (hInt : FiniteHaarIntegralsBounded 1)
    (hFun : ContinuousLocalAndFaceEnergies.Statement)
    {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) :
    A.tiltedKernel β t W F ∈ continuousLocalFunctions 1 := by
  have hEc : Continuous fun U => A.windowEnergy β t W U :=
    Complex.continuous_re.comp hE.2.2
  obtain ⟨CF, hCF⟩ := hF.1.2
  obtain ⟨CE, hCE⟩ := hE.1.2
  let g : W.Assignments × GaugeField 1 → GaugeField 1 := fun q => W.glue one_pos q.1 q.2
  let w : W.Assignments × GaugeField 1 → ℂ :=
    fun q => (Real.exp (-A.windowEnergy β t W (g q)) : ℂ)
  let Φ : W.Assignments × GaugeField 1 → ℂ := fun q => F (g q) * w q
  have hw : Continuous w :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (hEc.comp hGlue).neg)
  have hΦ : Continuous Φ := (hF.2.2.comp hGlue).mul hw
  have hwle : ∀ q, ‖w q‖ ≤ Real.exp CE := by
    intro q
    have h₂ := hCE (g q)
    rw [Complex.norm_real, Real.norm_eq_abs] at h₂
    simp only [w]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (A.windowEnergy β t W (g q))])
  have hΦle : ∀ q, ‖Φ q‖ ≤ CF * Real.exp CE := by
    intro q
    have h₁ := hCF (g q)
    simp only [Φ]
    rw [norm_mul]
    exact mul_le_mul h₁ (hwle q) (norm_nonneg _) (le_trans (norm_nonneg _) h₁)
  have hnum : Continuous fun U => ∫ V, Φ (V, U) ∂W.haarProd :=
    (hInt W.links Φ (continuous_complex_measurable_borel hΦ) ⟨_, hΦle⟩).2.2 hΦ
  have hden : Continuous fun U => ∫ V, w (V, U) ∂W.haarProd :=
    (hInt W.links w (continuous_complex_measurable_borel hw) ⟨_, hwle⟩).2.2 hw
  have hden_eq : ∀ U, ∫ V, w (V, U) ∂W.haarProd = (A.windowPartition β t W U : ℂ) := fun U =>
    integral_complex_ofReal
  have hcont : Continuous (A.tiltedKernel β t W F) := by
    have hquot : A.tiltedKernel β t W F =
        fun U => (∫ V, Φ (V, U) ∂W.haarProd) / ∫ V, w (V, U) ∂W.haarProd := by
      funext U
      rw [hden_eq]
      rfl
    rw [hquot]
    refine hnum.div hden fun U => ?_
    rw [hden_eq]
    exact Complex.ofReal_ne_zero.mpr (hZ U).ne'
  obtain ⟨hFdep, hFset, hFfin, -⟩ := hLoc.2.2.2.2.2.2.2 F hF.1 hF.2.1
  obtain ⟨hEdep, hEset, hEfin, -⟩ := hLoc.2.2.2.2.2.2.2 _ hE.1 hE.2.1
  let N : Set (Link 1) := (observableSupport F ∪
    observableSupport fun U => (A.windowEnergy β t W U : ℂ)) \ (W.links : Set (Link 1))
  have hNset : IsLinkSet N := fun b hb => hb.1.elim (fun h => hFset h) fun h => hEset h
  have hNfin : N.Finite := (hFfin.union hEfin).subset sdiff_subset
  have hdep : DependsOnlyOn N (A.tiltedKernel β t W F) := by
    intro U U' hUU
    have hout : ∀ b ∈ observableSupport F ∪
        observableSupport (fun U => (A.windowEnergy β t W U : ℂ)), b ∉ W.links → U b = U' b :=
      fun b hb hbW => hUU b ⟨hb, hbW⟩
    have hagree := fun V : W.Assignments => W.glue_agree_of_agree_outside V hout
    have hFV : ∀ V : W.Assignments, F (W.glue one_pos V U) = F (W.glue one_pos V U') := fun V =>
      hFdep _ _ fun b hb => hagree V b (Or.inl hb)
    have hEV : ∀ V : W.Assignments, A.windowEnergy β t W (W.glue one_pos V U) =
        A.windowEnergy β t W (W.glue one_pos V U') := fun V =>
      Complex.ofReal_injective (hEdep _ _ fun b hb => hagree V b (Or.inr hb))
    simp only [LocalObservableArray.tiltedKernel, LocalObservableArray.windowPartition, hFV, hEV]
  exact (hFun.1 N hNset hNfin _ hcont hdep).1
theorem basicTiltedKernelFacts_holds
    (hTori : ToriArraysAndTiltedMeasuresFacts)
    (hElem : ElementaryLatticeFacts)
    (hFun : ContinuousLocalAndFaceEnergies.Statement) :
    BasicTiltedKernelFacts := by
  intro β hβ A W t
  obtain ⟨-, hArr, -, -⟩ := hTori β hβ
  obtain ⟨hSupp, hDef, -⟩ := hArr A t
  obtain ⟨hConf, -, -, hLoc, -, -, -, -, hInt⟩ :=
    hElem 1 β one_pos hβ
  exact ⟨hSupp.finite_labelsTouching W, hDef.tiltedKernel_zero W, hDef.tiltedGibbsClass_zero,
    fun F hF => A.tiltedKernel_mem_continuousLocal W (hDef.windowEnergy_mem W)
      (hDef.windowPartition_pos W) (hConf.2.2 W) hLoc hInt hFun hF⟩
end YangMills.Construction.InfiniteLattice
