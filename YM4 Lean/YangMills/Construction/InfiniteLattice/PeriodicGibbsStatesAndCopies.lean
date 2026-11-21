import YangMills.Construction.Lattice.ImagesOfBondsAndPlaquettesUnderLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a c lam : ℝ}
def pointScale (lam : ℝ) (hc : c = lam * a) (x : LatticePoint a) : LatticePoint c :=
  ⟨lam • (x : AmbientSpace), by
    obtain ⟨n, hn⟩ := x.2
    exact ⟨n, fun μ => by
      simp only [Pi.smul_apply, smul_eq_mul, hn μ, hc]
      ring⟩⟩
theorem pointScale_sub (hc : c = lam * a) (x y : LatticePoint a) :
    pointScale lam hc (x - y) = pointScale lam hc x - pointScale lam hc y :=
  Subtype.ext (smul_sub lam (x : AmbientSpace) y)
theorem pointScale_neg (hc : c = lam * a) (x : LatticePoint a) :
    pointScale lam hc (-x) = -pointScale lam hc x :=
  Subtype.ext (smul_neg lam (x : AmbientSpace))
theorem pointScale_axisStep (hc : c = lam * a) (μ : Fin 4) :
    pointScale lam hc (axisStep a μ) = axisStep c μ := by
  refine Subtype.ext (funext fun ν => ?_)
  by_cases h : ν = μ
  · subst h
    simp [pointScale, axisStep, hc]
  · simp [pointScale, axisStep, Pi.single_eq_of_ne h]
def linkScale (lam : ℝ) (hc : c = lam * a) (l : Link a) : Link c where
  initial := pointScale lam hc l.initial
  terminal := pointScale lam hc l.terminal
  isAdjacent := by
    obtain ⟨μ, h | h⟩ := l.isAdjacent
    · exact ⟨μ, Or.inl (by rw [← pointScale_sub, h, pointScale_axisStep])⟩
    · exact ⟨μ, Or.inr (by rw [← pointScale_sub, h, pointScale_neg, pointScale_axisStep])⟩
theorem linkScale_opposite (hc : c = lam * a) (l : Link a) :
    linkScale lam hc l.opposite = (linkScale lam hc l).opposite := rfl
theorem spacing_eq_inv_mul (hlam : 0 < lam) (hc : c = lam * a) : a = lam⁻¹ * c := by
  rw [hc, inv_mul_cancel_left₀ hlam.ne']
theorem linkScale_inv_linkScale (hlam : 0 < lam) (hc : c = lam * a) (l : Link a) :
    linkScale lam⁻¹ (spacing_eq_inv_mul hlam hc) (linkScale lam hc l) = l := by
  apply Link.ext <;> refine Subtype.ext ?_ <;>
    simp [linkScale, pointScale, smul_smul, inv_mul_cancel₀ hlam.ne']
theorem linkScale_linkScale_inv (hlam : 0 < lam) (hc : c = lam * a) (l : Link c) :
    linkScale lam hc (linkScale lam⁻¹ (spacing_eq_inv_mul hlam hc) l) = l := by
  apply Link.ext <;> refine Subtype.ext ?_ <;>
    simp [linkScale, pointScale, smul_smul, mul_inv_cancel₀ hlam.ne']
def plaquetteScale (lam : ℝ) (hc : c = lam * a) (p : ElementaryPlaquette a) :
    ElementaryPlaquette c where
  corner := pointScale lam hc p.corner
  lowAxis := p.lowAxis
  highAxis := p.highAxis
  lowAxis_lt_highAxis := p.lowAxis_lt_highAxis
namespace ElementaryPlaquette
theorem corner_mem_cornerSet (p : ElementaryPlaquette a) : p.corner ∈ p.cornerSet :=
  mem_insert _ _
private theorem sum_single_coord (μ : Fin 4) (t : ℝ) :
    ∑ ν, (Pi.single μ t : AmbientSpace) ν = t := by
  simp [Finset.sum_pi_single']
theorem coordSum_corner_lt (ha : 0 < a) (p : ElementaryPlaquette a) {y : LatticePoint a}
    (hy : y ∈ p.cornerSet) (hne : y ≠ p.corner) :
    ∑ μ, (p.corner : AmbientSpace) μ < ∑ μ, (y : AmbientSpace) μ := by
  simp only [cornerSet, mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  all_goals
    simp only [AddSubgroup.coe_add, axisStep, Pi.add_apply, Finset.sum_add_distrib,
      sum_single_coord]
    linarith
theorem exists_coord_ne_iff (ha : 0 < a) (p : ElementaryPlaquette a) (ν : Fin 4) :
    (∃ y ∈ p.cornerSet, ∃ z ∈ p.cornerSet, (y : AmbientSpace) ν ≠ (z : AmbientSpace) ν) ↔
      ν = p.lowAxis ∨ ν = p.highAxis := by
  constructor
  · rintro ⟨y, hy, z, hz, h⟩
    by_contra hν
    replace hν := not_or.mp hν
    have key : ∀ w ∈ p.cornerSet, (w : AmbientSpace) ν = (p.corner : AmbientSpace) ν := by
      intro w hw
      simp only [cornerSet, mem_insert_iff, mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl <;>
        simp [axisStep, Pi.single_eq_of_ne hν.1, Pi.single_eq_of_ne hν.2]
    exact h (by rw [key y hy, key z hz])
  · rintro (rfl | rfl)
    · refine ⟨p.corner + axisStep a p.lowAxis, by simp [cornerSet], p.corner,
        p.corner_mem_cornerSet, ?_⟩
      simp [axisStep, ha.ne']
    · refine ⟨p.corner + axisStep a p.highAxis, by simp [cornerSet], p.corner,
        p.corner_mem_cornerSet, ?_⟩
      simp [axisStep, ha.ne']
theorem cornerSet_injective (ha : 0 < a) : Function.Injective (cornerSet (a := a)) := by
  intro p q h
  have hcorner : p.corner = q.corner := by
    by_contra hne
    have h₁ := q.coordSum_corner_lt ha (by rw [← h]; exact p.corner_mem_cornerSet) hne
    have h₂ := p.coordSum_corner_lt ha (by rw [h]; exact q.corner_mem_cornerSet) (Ne.symm hne)
    exact lt_asymm h₁ h₂
  have hν : ∀ ν, (ν = p.lowAxis ∨ ν = p.highAxis) ↔ (ν = q.lowAxis ∨ ν = q.highAxis) :=
    fun ν => by
      rw [← p.exists_coord_ne_iff ha, ← q.exists_coord_ne_iff ha, h]
  have h₁ := (hν p.lowAxis).1 (Or.inl rfl)
  have h₂ := (hν p.highAxis).1 (Or.inr rfl)
  have h₃ := (hν q.lowAxis).2 (Or.inl rfl)
  have h₄ := (hν q.highAxis).2 (Or.inr rfl)
  have hp := p.lowAxis_lt_highAxis
  have hq := q.lowAxis_lt_highAxis
  simp only [Fin.ext_iff, Fin.lt_def] at h₁ h₂ h₃ h₄ hp hq
  exact ElementaryPlaquette.ext hcorner (Fin.ext (by omega)) (Fin.ext (by omega))
end ElementaryPlaquette
def gaugeFieldScale (hlam : 0 < lam) (hc : c = lam * a) (U : GaugeField a) : GaugeField c :=
  ⟨fun l => U (linkScale lam⁻¹ (spacing_eq_inv_mul hlam hc) l),
    fun l => U.2 (linkScale lam⁻¹ (spacing_eq_inv_mul hlam hc) l)⟩
theorem gaugeFieldScale_linkScale (hlam : 0 < lam) (hc : c = lam * a) (U : GaugeField a)
    (l : Link a) : gaugeFieldScale hlam hc U (linkScale lam hc l) = U l :=
  congrArg U.1 (linkScale_inv_linkScale hlam hc l)
theorem continuous_gaugeFieldScale (hlam : 0 < lam) (hc : c = lam * a) :
    Continuous (gaugeFieldScale (a := a) hlam hc) := by
  have hval : Continuous fun U : GaugeField a =>
      (U.1 : Link a → YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary) :=
    continuous_subtype_val
  exact Continuous.subtype_mk
    (f := fun U : GaugeField a => fun l => U.1 (linkScale lam⁻¹ (spacing_eq_inv_mul hlam hc) l))
    (continuous_pi fun l => (continuous_apply _).comp hval) fun U => (gaugeFieldScale hlam hc U).2
theorem measurable_gaugeFieldScale (hlam : 0 < lam) (hc : c = lam * a) :
    Measurable (gaugeFieldScale (a := a) hlam hc) :=
  (continuous_gaugeFieldScale hlam hc).measurable
def scaledState (hlam : 0 < lam) (hc : c = lam * a) (ν : Measure (GaugeField a)) :
    Measure (GaugeField c) :=
  ν.map (gaugeFieldScale hlam hc)
instance isProbabilityMeasure_scaledState (hlam : 0 < lam) (hc : c = lam * a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (scaledState hlam hc ν) :=
  Measure.isProbabilityMeasure_map (measurable_gaugeFieldScale hlam hc).aemeasurable
end YangMills.Construction.InfiniteLattice
