import YangMills.Construction.InfiniteLattice.DilationToSpacingOneProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def inverseScaling (ha : 0 < a) : AmbientSpace ≃ AmbientSpace where
  toFun x := a⁻¹ • x
  invFun x := a • x
  left_inv x := smul_inv_smul₀ ha.ne' x
  right_inv x := inv_smul_smul₀ ha.ne' x
def pointOfUnit (a : ℝ) : LatticePoint 1 →+ LatticePoint a :=
  AddMonoidHom.mk' (fun x => ⟨a • (x : AmbientSpace), by
    obtain ⟨n, hn⟩ := x.2
    exact ⟨n, fun μ => by simp [hn μ, mul_comm]⟩⟩)
    (fun x y => Subtype.ext (by simp [smul_add]))
def pointToUnit (ha : 0 < a) : LatticePoint a →+ LatticePoint 1 :=
  AddMonoidHom.mk' (fun x => ⟨inverseScaling ha x, by
    obtain ⟨n, hn⟩ := x.2
    refine ⟨n, fun μ => ?_⟩
    have h : a⁻¹ * ((n μ : ℝ) * a) = (n μ : ℝ) * 1 := by field_simp
    simpa [inverseScaling, hn μ] using h⟩)
    (fun x y => Subtype.ext (by simp [inverseScaling, smul_add]))
theorem pointOfUnit_axisStep (a : ℝ) (μ : Fin 4) :
    pointOfUnit a (axisStep 1 μ) = axisStep a μ := by
  refine Subtype.ext (funext fun ν => ?_)
  by_cases h : ν = μ
  · subst h
    simp [pointOfUnit, axisStep]
  · simp [pointOfUnit, axisStep, Pi.single_eq_of_ne h]
theorem pointToUnit_axisStep (ha : 0 < a) (μ : Fin 4) :
    pointToUnit ha (axisStep a μ) = axisStep 1 μ := by
  refine Subtype.ext (funext fun ν => ?_)
  by_cases h : ν = μ
  · subst h
    simp [pointToUnit, inverseScaling, axisStep, ha.ne']
  · simp [pointToUnit, inverseScaling, axisStep, Pi.single_eq_of_ne h]
def linkOfUnit (a : ℝ) (b : Link 1) : Link a where
  initial := pointOfUnit a b.initial
  terminal := pointOfUnit a b.terminal
  isAdjacent := by
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · exact ⟨μ, Or.inl (by rw [← map_sub, h, pointOfUnit_axisStep])⟩
    · exact ⟨μ, Or.inr (by rw [← map_sub, h, map_neg, pointOfUnit_axisStep])⟩
def linkToUnit (ha : 0 < a) (b : Link a) : Link 1 where
  initial := pointToUnit ha b.initial
  terminal := pointToUnit ha b.terminal
  isAdjacent := by
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · exact ⟨μ, Or.inl (by rw [← map_sub, h, pointToUnit_axisStep])⟩
    · exact ⟨μ, Or.inr (by rw [← map_sub, h, map_neg, pointToUnit_axisStep])⟩
def gaugeFieldRescale (a : ℝ) (U : GaugeField a) : GaugeField 1 :=
  ⟨fun b => U (linkOfUnit a b), fun b => U.2 (linkOfUnit a b)⟩
def gaugeFieldUnrescale (ha : 0 < a) (V : GaugeField 1) : GaugeField a :=
  ⟨fun b => V (linkToUnit ha b), fun b => V.2 (linkToUnit ha b)⟩
theorem continuous_gaugeFieldRescale (a : ℝ) :
    Continuous (gaugeFieldRescale a) := by
  refine continuous_induced_rng.2 (continuous_pi fun b => ?_)
  exact (continuous_apply (linkOfUnit a b)).comp continuous_induced_dom
def pullToUnit {E : Type*} (ha : 0 < a) (F : GaugeField a → E) : GaugeField 1 → E :=
  F ∘ gaugeFieldUnrescale ha
def pushToUnit (ν : Measure (GaugeField a)) : Measure (GaugeField 1) :=
  ν.map (gaugeFieldRescale a)
theorem isProbabilityMeasure_pushToUnit (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (pushToUnit ν) :=
  Measure.isProbabilityMeasure_map
    (continuous_gaugeFieldRescale a).measurable.aemeasurable
def GaugeFieldProbability.toUnit (ν : GaugeFieldProbability a) :
    GaugeFieldProbability 1 :=
  ⟨pushToUnit ν.1, haveI := ν.2; isProbabilityMeasure_pushToUnit ν.1⟩
theorem euclidNormVec_smul (c : ℝ) (v : AmbientSpace) :
    TorusMetric.euclidNormVec (c • v) = |c| * TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.UnitSpacing.euclidNormVec_smul <;> assumption
def LatticeSymmetry.toUnit (ha : 0 < a) (r : LatticeSymmetry a) : LatticeSymmetry 1 where
  toFun := inverseScaling ha ∘ r.toFun ∘ (inverseScaling ha).symm
  preservesDist x y := by
    have hr := r.preservesDist ((inverseScaling ha).symm x) ((inverseScaling ha).symm y)
    have h₁ : (inverseScaling ha).symm x - (inverseScaling ha).symm y = a • (x - y) :=
      (smul_sub a x y).symm
    have h₂ : (inverseScaling ha ∘ r.toFun ∘ (inverseScaling ha).symm) x -
        (inverseScaling ha ∘ r.toFun ∘ (inverseScaling ha).symm) y =
        a⁻¹ • (r.toFun ((inverseScaling ha).symm x) - r.toFun ((inverseScaling ha).symm y)) :=
      (smul_sub a⁻¹ _ _).symm
    rw [h₂, euclidNormVec_smul, hr, h₁, euclidNormVec_smul, abs_inv, abs_of_pos ha,
      inv_mul_cancel_left₀ ha.ne']
  image_eq := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h : r.toFun (a • x) ∈ r.toFun '' (latticeSubgroup a : Set AmbientSpace) :=
        ⟨a • x, (pointOfUnit a ⟨x, hx⟩).2, rfl⟩
      rw [r.image_eq] at h
      exact (pointToUnit ha ⟨_, h⟩).2
    · intro hy
      have h : a • y ∈ r.toFun '' (latticeSubgroup a : Set AmbientSpace) := by
        rw [r.image_eq]
        exact (pointOfUnit a ⟨y, hy⟩).2
      obtain ⟨z, hz, hzy⟩ := h
      refine ⟨inverseScaling ha z, (pointToUnit ha ⟨z, hz⟩).2, ?_⟩
      change inverseScaling ha (r.toFun ((inverseScaling ha).symm (inverseScaling ha z))) = y
      rw [Equiv.symm_apply_apply, hzy]
      exact inv_smul_smul₀ ha.ne' y
end YangMills.Construction.InfiniteLattice
