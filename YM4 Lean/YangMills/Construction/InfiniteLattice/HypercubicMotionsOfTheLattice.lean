import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.AxialGauges
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def basisVector (κ : Fin 4) : AmbientSpace := Pi.single κ 1
def hypercubicGroup : Set (AmbientSpace →ₗ[ℝ] AmbientSpace) :=
  {w | ∃ σ : Equiv.Perm (Fin 4), ∀ κ,
    w (basisVector κ) = basisVector (σ κ) ∨ w (basisVector κ) = -basisVector (σ κ)}
def frameLinearMap (r : PeriodicLattice.SignedFrame) : AmbientSpace →ₗ[ℝ] AmbientSpace where
  toFun := r.actOnVector
  map_add' x y := by
    funext μ
    simp [PeriodicLattice.SignedFrame.actOnVector, mul_add]
  map_smul' c x := by
    funext μ
    simp [PeriodicLattice.SignedFrame.actOnVector]
    ring
theorem exists_frameLinearMap_eq_of_mem_hypercubicGroup {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hypercubicGroup) :
    ∃ r : PeriodicLattice.SignedFrame, w = frameLinearMap r := by
  classical
  obtain ⟨σ, h⟩ := hw
  have hs : ∀ κ, ∃ u : ℤˣ, w (basisVector κ) = ((u : ℤ) : ℝ) • basisVector (σ κ) := by
    intro κ
    rcases h κ with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  choose u hu using hs
  refine ⟨(σ⁻¹, fun μ => u (σ⁻¹ μ)), LinearMap.ext fun x => ?_⟩
  have hx : x = ∑ κ, x κ • basisVector κ := by
    funext ν
    simp [basisVector, Finset.sum_apply, Pi.single_apply]
  funext μ
  have hsum : w x = ∑ κ, x κ • (((u κ : ℤ) : ℝ) • basisVector (σ κ)) := by
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, hu]
  rw [hsum, Finset.sum_apply, Finset.sum_eq_single (σ⁻¹ μ)]
  · simp [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, basisVector, mul_comm]
  · intro κ _ hκ
    have : σ κ ≠ μ := fun hc => hκ (by simp [← hc])
    simp [basisVector, Pi.single_eq_of_ne' this]
  · simp
theorem frameLinearMap_mem_hypercubicGroup (r : PeriodicLattice.SignedFrame) :
    frameLinearMap r ∈ hypercubicGroup := by
  classical
  refine ⟨r.1⁻¹, fun κ => ?_⟩
  rcases Int.units_eq_one_or (r.2 (r.1⁻¹ κ)) with h | h
  · left
    funext μ
    by_cases hμ : r.1 μ = κ
    · subst hμ
      simp_all [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, basisVector]
    · have : μ ≠ r.1.symm κ := fun hc => hμ (by simp [hc])
      simp [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, basisVector, hμ, this]
  · right
    funext μ
    by_cases hμ : r.1 μ = κ
    · subst hμ
      simp_all [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, basisVector]
    · have : μ ≠ r.1.symm κ := fun hc => hμ (by simp [hc])
      simp [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, basisVector, hμ, this]
def latticeMotions (a : ℝ) : Set (AmbientSpace → AmbientSpace) :=
  {r | ∃ w ∈ hypercubicGroup, ∃ v ∈ latticeSubgroup a, ∀ x, r x = w x + v}
def latticeMotionMul (r t : AmbientSpace → AmbientSpace) : AmbientSpace → AmbientSpace := r ∘ t
def coordinateReflection (μ : Fin 4) (c : ℝ) (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (x μ - c)) • basisVector μ
def coordinateSignFlip (μ : Fin 4) : AmbientSpace →ₗ[ℝ] AmbientSpace where
  toFun x := fun ν => if ν = μ then -x ν else x ν
  map_add' x y := by
    funext ν
    by_cases h : ν = μ <;> simp [h, add_comm]
  map_smul' c x := by
    funext ν
    by_cases h : ν = μ <;> simp [h]
theorem coordinateSignFlip_mem_hypercubicGroup (μ : Fin 4) :
    coordinateSignFlip μ ∈ hypercubicGroup := by
  refine ⟨1, fun κ => ?_⟩
  by_cases h : κ = μ
  · subst h
    right
    funext ν
    by_cases hν : ν = κ
    · subst hν
      simp [coordinateSignFlip, basisVector]
    · simp [coordinateSignFlip, basisVector, hν]
  · left
    funext ν
    by_cases hν : ν = μ
    · subst hν
      have : ν ≠ κ := fun hc => h hc.symm
      simp [coordinateSignFlip, basisVector, Pi.single_eq_of_ne this]
    · simp [coordinateSignFlip, basisVector, hν]
theorem coordinateReflection_eq_signFlip_add (μ : Fin 4) (c : ℝ) (x : AmbientSpace) :
    coordinateReflection μ c x = coordinateSignFlip μ x + (2 * c) • basisVector μ := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [coordinateReflection, coordinateSignFlip, basisVector]
    ring
  · simp [coordinateReflection, coordinateSignFlip, basisVector, h]
namespace LatticeMotion
theorem euclidNormVec_sub {r : AmbientSpace → AmbientSpace} (hr : r ∈ latticeMotions a)
    (x y : AmbientSpace) :
    TorusMetric.euclidNormVec (r x - r y) = TorusMetric.euclidNormVec (x - y) := by
  obtain ⟨w, hw, v, -, h⟩ := hr
  obtain ⟨f, rfl⟩ := exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
  have hsq : ∀ μ, (r x - r y) μ ^ 2 = (x - y) (f.1 μ) ^ 2 := by
    intro μ
    rcases Int.units_eq_one_or (f.2 μ) with hs | hs <;>
      simp [h, frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, hs] <;> ring
  rw [TorusMetric.euclidNormVec, TorusMetric.euclidNormVec]
  congr 1
  rw [Finset.sum_congr rfl fun μ _ => hsq μ]
  exact Equiv.sum_comp f.1 fun ν => (x - y) ν ^ 2
theorem image_latticeSubgroup {r : AmbientSpace → AmbientSpace} (hr : r ∈ latticeMotions a) :
    r '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a := by
  obtain ⟨w, hw, v, hv, h⟩ := hr
  obtain ⟨f, rfl⟩ := exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
  ext y
  constructor
  · rintro ⟨x, ⟨n, hn⟩, rfl⟩
    rw [h]
    refine add_mem (⟨fun μ => (f.2 μ : ℤ) * n (f.1 μ), fun μ => ?_⟩ : _ ∈ latticeSubgroup a) hv
    simp [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, hn, mul_assoc]
  · intro hy
    obtain ⟨n, hn⟩ := sub_mem hy hv
    have hunit : ∀ μ, ((f.2 μ : ℤ) : ℝ) * ((f.2 μ : ℤ) : ℝ) = 1 := fun μ => by
      rcases Int.units_eq_one_or (f.2 μ) with hs | hs <;> simp [hs]
    refine ⟨fun κ => ((f.2 (f.1.symm κ) : ℤ) : ℝ) * (n (f.1.symm κ) * a),
      ⟨fun κ => (f.2 (f.1.symm κ) : ℤ) * n (f.1.symm κ), fun κ => by simp [mul_assoc]⟩, ?_⟩
    rw [h]
    funext μ
    have h1 := hn μ
    have h2 : y μ - v μ = (n μ : ℝ) * a := h1
    simp only [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.add_apply, Equiv.symm_apply_apply]
    rw [← mul_assoc, hunit, one_mul, ← h2]
    ring
end LatticeMotion
def latticeMotionSymmetry (r : latticeMotions a) : LatticeSymmetry a where
  toFun := r.1
  preservesDist := LatticeMotion.euclidNormVec_sub r.2
  image_eq := LatticeMotion.image_latticeSubgroup r.2
def latticeMotionField (r : latticeMotions a) (U : GaugeField a) : GaugeField a :=
  (latticeMotionSymmetry r).pullbackField U
def latticeMotionAct {E : Type*} (r : latticeMotions a) (F : GaugeField a → E) :
    GaugeField a → E :=
  (latticeMotionSymmetry r).actOn F
theorem continuous_latticeMotionField (r : latticeMotions a) :
    Continuous (latticeMotionField r) := by
  refine Continuous.subtype_mk (continuous_pi fun b => ?_) _
  exact (continuous_apply _).comp continuous_subtype_val
theorem IsBoundedObservable.latticeMotionAct {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (r : latticeMotions a) : IsBoundedObservable (latticeMotionAct r F) := by
  obtain ⟨hm, C, hC⟩ := hF
  exact ⟨hm.comp (continuous_latticeMotionField r).measurable, C, fun U => hC _⟩
def IsLatticeMotionInvariant (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (r : latticeMotions a) : Prop :=
  ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    ∫ U, latticeMotionAct r F U ∂ν = ∫ U, F U ∂ν
end YangMills.Construction.InfiniteLattice
