import YangMills.Construction.InfiniteLattice.GibbsStatesReadThroughKernelsAndSymmetries
import YangMills.Construction.InfiniteLattice.GroupOfTheLatticeIsometriesAndItsAction
import YangMills.Construction.InfiniteLattice.InvarianceOfAMeasureUnderAMotion
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAreConvexAndWeaklyCompact
import YangMills.Construction.InfiniteLattice.ThreePropertiesOfTheWilsonKernel
import YangMills.Construction.InfiniteLattice.TopologyAndDensityOnTheConfigurationsOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open LatticePhases
namespace InfiniteLattice.PeriodicGibbsConvexCompact
def toProbMeasure {a : ℝ} (ν : Measure (GaugeField a)) (h : IsProbabilityMeasure ν) :
    ProbMeasure (GaugeField a) :=
  (⟨ν, h⟩ : ProbabilityMeasure (GaugeField a))
theorem continuous_eval {X : Type*} [MeasurableSpace X] [TopologicalSpace X] (G : C(X, ℂ)) :
    Continuous fun μ : ProbMeasure X => μ.eval G :=
  continuous_iInf_dom (i := G) continuous_induced_dom
theorem integrable_of_bounded {a : ℝ} {G : GaugeField a → ℂ} (hG : IsBoundedObservable G)
    (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ] : Integrable G μ := by apply _root_.YangMills.Construction.LatticeConventions.CoarseStepFivePoint.integrable_of_isBoundedObservable <;> assumption
theorem integral_convexCombo {a : ℝ} {G : GaugeField a → ℂ} (hG : IsBoundedObservable G)
    (μ₁ μ₂ : Measure (GaugeField a)) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    ∫ x, G x ∂(ENNReal.ofReal s • μ₁ + ENNReal.ofReal (1 - s) • μ₂) =
      s • ∫ x, G x ∂μ₁ + (1 - s) • ∫ x, G x ∂μ₂ := by
  have hs₂ : 0 ≤ 1 - s := by linarith
  rw [integral_add_measure
    ((integrable_of_bounded hG μ₁).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_of_bounded hG μ₂).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hs₀,
    ENNReal.toReal_ofReal hs₂]
theorem isProbabilityMeasure_convexCombo {a : ℝ} (μ₁ μ₂ : Measure (GaugeField a))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    IsProbabilityMeasure (ENNReal.ofReal s • μ₁ + ENNReal.ofReal (1 - s) • μ₂) := by
  have hs₂ : 0 ≤ 1 - s := by linarith
  refine ⟨?_⟩
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hs₀ hs₂]
  simp
def SatisfiesInvarianceEquations (S : Setup) (μ : ProbMeasure (GaugeField S.mesh)) : Prop :=
  (∀ W : OrientedLinkSet S.mesh, ∀ F ∈ continuousLocalFunctions S.mesh,
      μ.eval (W.heatBath S.β F) = μ.eval F) ∧
    ∀ v : LatticePoint S.mesh, ∀ F ∈ continuousLocalFunctions S.mesh,
      μ.eval (latticeMotionAct (shiftMotion v) F) = μ.eval F
theorem mem_periodicGibbsSet_iff (hGK : GibbsKernelsAndSymmetries.Assertion)
    (S : Setup) (μ : Measure (GaugeField S.mesh)) :
    μ ∈ periodicGibbsSet S.L S.K S.β ↔ IsGibbs S.β μ ∧ IsShiftInvariant μ := by
  constructor
  · intro h
    exact ⟨h.1, ((hGK S S.β S.β_pos).2.1 (toProbMeasure μ h.1.1) h).2.1⟩
  · rintro ⟨hgibbs, hshift⟩
    exact ⟨hgibbs, ⊤, inferInstance, fun v _ => hshift v⟩
theorem mem_iff_satisfiesInvarianceEquations (hGK : GibbsKernelsAndSymmetries.Assertion)
    (hTD : TopologyDensityHolds)
    (hMI : MotionInvariance.Holds)
    (S : Setup) (μ : ProbMeasure (GaugeField S.mesh)) :
    μ.toMeasure ∈ periodicGibbsSet S.L S.K S.β ↔ SatisfiesInvarianceEquations S μ := by
  rw [mem_periodicGibbsSet_iff hGK]
  have hkern := (hGK S S.β S.β_pos).1 μ
  constructor
  · rintro ⟨hgibbs, hshift⟩
    exact ⟨hkern.mp hgibbs, fun v F hF => hshift v F hF.1⟩
  · rintro ⟨hheat, hshift⟩
    refine ⟨hkern.mpr hheat, fun v => ?_⟩
    have hdense : ∀ G : C(GaugeField S.mesh, ℂ), ∀ ε : ℝ, 0 < ε →
        ∃ F ∈ {F : C(GaugeField S.mesh, ℂ) | ⇑F ∈ continuousLocalFunctions S.mesh},
          uniformSup (⇑G - ⇑F) < ε := by
      intro G ε hε
      obtain ⟨H, hH, hlt⟩ := (hTD S).dense_local.2 G G.continuous ε hε
      exact ⟨⟨H, hH.2.2⟩, hH, hlt⟩
    exact ((hMI S (shiftMotion v) μ).2.1 _ hdense).mpr fun F hF => hshift v F hF
theorem isClosed_satisfiesInvarianceEquations (hWK : WilsonKernelProperties.Statement)
    (S : Setup) :
    IsClosed {μ : ProbMeasure (GaugeField S.mesh) | SatisfiesInvarianceEquations S μ} := by
  simp only [SatisfiesInvarianceEquations, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter
    (isClosed_iInter fun W => isClosed_iInter fun F => isClosed_iInter fun hF => ?_)
    (isClosed_iInter fun v => isClosed_iInter fun F => isClosed_iInter fun hF => ?_)
  · obtain ⟨-, ⟨-, -, hheat⟩, -, -⟩ := hWK S W S.β S.β S.β_pos S.β_pos F hF
    exact isClosed_eq (continuous_eval ⟨_, hheat.2.2⟩) (continuous_eval ⟨F, hF.2.2⟩)
  · have hcont : Continuous (latticeMotionAct (shiftMotion v) F) :=
      hF.2.2.comp (continuous_latticeMotionField (shiftMotion v))
    exact isClosed_eq (continuous_eval ⟨_, hcont⟩) (continuous_eval ⟨F, hF.2.2⟩)
theorem convexCombo_mem (hGK : GibbsKernelsAndSymmetries.Assertion)
    (hWK : WilsonKernelProperties.Statement) (S : Setup)
    {μ₁ μ₂ : Measure (GaugeField S.mesh)}
    (hμ₁ : μ₁ ∈ periodicGibbsSet S.L S.K S.β) (hμ₂ : μ₂ ∈ periodicGibbsSet S.L S.K S.β)
    {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    ENNReal.ofReal s • μ₁ + ENNReal.ofReal (1 - s) • μ₂ ∈
      periodicGibbsSet S.L S.K S.β := by
  obtain ⟨hg₁, hi₁⟩ := (mem_periodicGibbsSet_iff hGK S μ₁).mp hμ₁
  obtain ⟨hg₂, hi₂⟩ := (mem_periodicGibbsSet_iff hGK S μ₂).mp hμ₂
  have := hg₁.1
  have := hg₂.1
  have hprob := isProbabilityMeasure_convexCombo μ₁ μ₂ hs₀ hs₁
  have hkern := (hGK S S.β S.β_pos).1
  refine (mem_periodicGibbsSet_iff hGK S _).mpr ⟨?_, fun v A hA => ?_⟩
  · refine (hkern (toProbMeasure _ hprob)).mpr fun W F hF => ?_
    obtain ⟨-, ⟨-, -, hheat⟩, -, -⟩ := hWK S W S.β S.β S.β_pos S.β_pos F hF
    have e₁ : ∫ x, W.heatBath S.β F x ∂μ₁ = ∫ x, F x ∂μ₁ :=
      (hkern (toProbMeasure μ₁ hg₁.1)).mp hg₁ W F hF
    have e₂ : ∫ x, W.heatBath S.β F x ∂μ₂ = ∫ x, F x ∂μ₂ :=
      (hkern (toProbMeasure μ₂ hg₂.1)).mp hg₂ W F hF
    show ∫ x, W.heatBath S.β F x ∂(ENNReal.ofReal s • μ₁ + ENNReal.ofReal (1 - s) • μ₂) =
      ∫ x, F x ∂(ENNReal.ofReal s • μ₁ + ENNReal.ofReal (1 - s) • μ₂)
    rw [integral_convexCombo hheat.1 μ₁ μ₂ hs₀ hs₁, integral_convexCombo hF.1 μ₁ μ₂ hs₀ hs₁,
      e₁, e₂]
  · have hmoved : IsBoundedObservable (latticeMotionAct (shiftMotion v) A) :=
      hA.latticeMotionAct (shiftMotion v)
    have e₁ : ∫ x, latticeMotionAct (shiftMotion v) A x ∂μ₁ = ∫ x, A x ∂μ₁ := hi₁ v A hA
    have e₂ : ∫ x, latticeMotionAct (shiftMotion v) A x ∂μ₂ = ∫ x, A x ∂μ₂ := hi₂ v A hA
    show ∫ x, latticeMotionAct (shiftMotion v) A x
        ∂(ENNReal.ofReal s • μ₁ + ENNReal.ofReal (1 - s) • μ₂) =
      ∫ x, A x ∂(ENNReal.ofReal s • μ₁ + ENNReal.ofReal (1 - s) • μ₂)
    rw [integral_convexCombo hmoved μ₁ μ₂ hs₀ hs₁, integral_convexCombo hA μ₁ μ₂ hs₀ hs₁,
      e₁, e₂]
theorem statement_holds (hGK : GibbsKernelsAndSymmetries.Assertion)
    (hTD : TopologyDensityHolds)
    (hMI : MotionInvariance.Holds)
    (hWK : WilsonKernelProperties.Statement) : PeriodicGibbsConvexCompact.Statement := by
  intro S
  refine ⟨?_, (hGK S S.β S.β_pos).2.2.2, ?_, ?_⟩
  · ext μ
    exact mem_periodicGibbsSet_iff hGK S μ
  · intro μ₁ hμ₁ μ₂ hμ₂ s hs₀ hs₁
    exact convexCombo_mem hGK hWK S hμ₁ hμ₂ hs₀ hs₁
  · have := (hTD S).compact_prob
    have hset : {μ : ProbMeasure (GaugeField S.mesh) |
        μ.toMeasure ∈ periodicGibbsSet S.L S.K S.β} =
        {μ | SatisfiesInvarianceEquations S μ} := by
      ext μ
      exact mem_iff_satisfiesInvarianceEquations hGK hTD hMI S μ
    rw [hset]
    exact (isClosed_satisfiesInvarianceEquations hWK S).isCompact
end InfiniteLattice.PeriodicGibbsConvexCompact
end YangMills.Construction
end
