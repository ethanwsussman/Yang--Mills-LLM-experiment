import YangMills.Construction.InfiniteLattice.InvarianceOfAMeasureUnderAMotion
import YangMills.Construction.InfiniteLattice.InvarianceOfStatesUnderIsometriesOfACutoffLatticeProof
import YangMills.Construction.InfiniteLattice.TopologyAndDensityOnTheConfigurationsOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.InfiniteLattice
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.LatticePhases.MotionInvariance
variable {a : ℝ}
def pushforward (m : latticeMotions a) (μ : ProbMeasure (GaugeField a)) :
    ProbMeasure (GaugeField a) :=
  (⟨μ.toMeasure.map (latticeMotionField m),
    Measure.isProbabilityMeasure_map
      (continuous_latticeMotionField m).aemeasurable⟩ : ProbabilityMeasure (GaugeField a))
theorem eval_pushforward (m : latticeMotions a) (μ : ProbMeasure (GaugeField a))
    {f : GaugeField a → ℂ} (hf : Measurable f) :
    (pushforward m μ).eval f = μ.eval (latticeMotionAct m f) :=
  integral_map (continuous_latticeMotionField m).aemeasurable hf.aestronglyMeasurable
theorem isBoundedObservable_of_continuous [CompactSpace (GaugeField a)]
    {f : GaugeField a → ℂ} (hf : Continuous f) : IsBoundedObservable f := by apply _root_.YangMills.Construction.CutoffLatticeStates.MotionInvariance.isBoundedObservable_of_continuous <;> assumption
theorem uniformSup_sub_self {X : Type*} (g : X → ℂ) : uniformSup (g - g) = 0 := by
  simp [uniformSup]
theorem isUniformlyDenseIn_continuous :
    IsUniformlyDenseIn {f : GaugeField a → ℂ | Continuous f} {f | Continuous f} :=
  ⟨subset_rfl, fun f hf ε hε => ⟨f, hf, by rwa [uniformSup_sub_self]⟩⟩
variable {S : Setup}
theorem pushforward_eq_of_symmetric (h : TopologyDensity S) (m : latticeMotions S.mesh)
    (μ : ProbMeasure (GaugeField S.mesh))
    (hs : IsSymmetricUnder μ.toMeasure (latticeMotionSymmetry m)) : pushforward m μ = μ := by
  have := h.compact
  refine h.ext_of_dense _ isUniformlyDenseIn_continuous _ _ fun f hf => ?_
  rw [eval_pushforward m μ (Continuous.measurable hf)]
  exact hs f (isBoundedObservable_of_continuous hf)
theorem pushforwardExistsUnique_holds (h : TopologyDensity S)
    (m : latticeMotions S.mesh) (μ : ProbMeasure (GaugeField S.mesh)) :
    PushforwardExistsUnique m μ := by
  have := h.compact
  refine ExistsUnique.intro (pushforward m μ) (fun f hf => eval_pushforward m μ hf.1) ?_
  intro ν hν
  refine h.ext_of_dense _ isUniformlyDenseIn_continuous _ _ fun f hf => ?_
  rw [hν f (isBoundedObservable_of_continuous hf), eval_pushforward m μ (Continuous.measurable hf)]
theorem invarianceCheckedOnDense_holds (h : TopologyDensity S)
    (m : latticeMotions S.mesh) (μ : ProbMeasure (GaugeField S.mesh)) :
    InvarianceCheckedOnDense m μ := by
  have := h.compact
  intro D hD
  constructor
  · intro hs f _
    exact hs f (isBoundedObservable_of_continuous f.continuous)
  · intro hD'
    have hdense : IsUniformlyDenseIn
        ((fun f : C(GaugeField S.mesh, ℂ) => (f : GaugeField S.mesh → ℂ)) '' D)
        {f | Continuous f} := by
      refine ⟨?_, fun f hf ε hε => ?_⟩
      · rintro _ ⟨f, -, rfl⟩
        exact f.continuous
      · obtain ⟨g, hg, hlt⟩ := hD ⟨f, hf⟩ ε hε
        exact ⟨g, ⟨g, hg, rfl⟩, hlt⟩
    have hpush : pushforward m μ = μ := by
      refine h.ext_of_dense _ hdense _ _ ?_
      rintro _ ⟨f, hf, rfl⟩
      rw [eval_pushforward m μ f.continuous.measurable]
      exact hD' f hf
    intro f hf
    have hv := eval_pushforward m μ hf.1
    rw [hpush] at hv
    exact hv.symm
theorem invarianceExtendsToBorel_holds (h : TopologyDensity S)
    (m : latticeMotions S.mesh) (μ : ProbMeasure (GaugeField S.mesh)) :
    InvarianceExtendsToBorel m μ := by
  intro hs
  have hc := continuous_latticeMotionField m
  have hm : μ.toMeasure.map (latticeMotionField m) = μ.toMeasure :=
    congrArg ProbMeasure.toMeasure (pushforward_eq_of_symmetric h m μ hs)
  refine ⟨fun g hg => ?_, fun g hg _ => ?_, fun g g' _ _ hae => ?_⟩
  · have hv := lintegral_map hg hc.measurable (μ := μ.toMeasure)
    rw [hm] at hv
    exact hv.symm
  · have hv := integral_map (μ := μ.toMeasure) hc.aemeasurable hg.aestronglyMeasurable
    rw [hm] at hv
    exact hv.symm
  · rw [ProbMeasure.holdsAS_iff] at hae ⊢
    have hmap : ∀ᵐ A ∂(μ.toMeasure.map (latticeMotionField m)), g A = g' A := by
      rw [hm]
      exact hae
    exact ae_of_ae_map hc.aemeasurable hmap
theorem invarianceClosedUnderLimits_holds (h : TopologyDensity S)
    (m : latticeMotions S.mesh) (μ : ProbMeasure (GaugeField S.mesh)) :
    InvarianceClosedUnderLimits m μ := by
  have := h.compact
  intro μs hμs hlim
  rw [ProbMeasure.tendsto_iff_eval] at hlim
  refine (invarianceCheckedOnDense_holds h m μ Set.univ ?_).mpr ?_
  · intro g ε hε
    exact ⟨g, Set.mem_univ g, by rwa [uniformSup_sub_self]⟩
  · intro f _
    have hmf : Continuous (latticeMotionAct m (f : GaugeField S.mesh → ℂ)) :=
      f.continuous.comp (continuous_latticeMotionField m)
    have h1 : Tendsto (fun n => (μs n).eval (latticeMotionAct m (f : GaugeField S.mesh → ℂ)))
        atTop (𝓝 (μ.eval (latticeMotionAct m (f : GaugeField S.mesh → ℂ)))) :=
      hlim ⟨_, hmf⟩
    have heq : ∀ n, (μs n).eval (latticeMotionAct m (f : GaugeField S.mesh → ℂ)) =
        (μs n).eval f := fun n => hμs n f (isBoundedObservable_of_continuous f.continuous)
    exact tendsto_nhds_unique (h1.congr heq) (hlim f)
theorem holds_of_topologyDensity (h : TopologyDensityHolds) : Holds := fun S m μ =>
  ⟨pushforwardExistsUnique_holds (h S) m μ, invarianceCheckedOnDense_holds (h S) m μ,
    invarianceExtendsToBorel_holds (h S) m μ, invarianceClosedUnderLimits_holds (h S) m μ⟩
end YangMills.Construction.LatticePhases.MotionInvariance
end
