import YangMills.Construction.InfiniteLattice.PlaquetteFunctionAndActionOfTheIsometriesProof
import YangMills.Construction.InfiniteLattice.BondsPlaquettesCircuitsAndConfigurationsOfTheLatticeOfACutoffProof
import YangMills.Construction.InfiniteLattice.EightLoopsRoundAPlaquette
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace InfiniteLattice
namespace PlaquetteLoops
theorem re_fullTrace_mul_comm (a b : ComplexMatrix2.specialUnitary) :
    (ComplexMatrix2.fullTrace ((a * b : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
      (ComplexMatrix2.fullTrace ((b * a : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re := by
  have hab : ((a * b : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      (a : ComplexMatrix2) * (b : ComplexMatrix2) := rfl
  have hba : ((b * a : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      (b : ComplexMatrix2) * (a : ComplexMatrix2) := rfl
  rw [hab, hba, ComplexMatrix2.fullTrace, Matrix.trace_mul_comm]
theorem re_fullTrace_inv (g : ComplexMatrix2.specialUnitary) :
    (ComplexMatrix2.fullTrace ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
      (ComplexMatrix2.fullTrace (g : ComplexMatrix2)).re := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.re_fullTrace_inv <;> assumption
def reTraceProd4 (a b c d : ComplexMatrix2.specialUnitary) : ℝ :=
  (ComplexMatrix2.fullTrace ((a * b * c * d : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re
theorem reTraceProd4_rotate (a b c d : ComplexMatrix2.specialUnitary) :
    reTraceProd4 b c d a = reTraceProd4 a b c d := by apply _root_.YangMills.Construction.InfiniteLattice.FaceEnergyAndMotions.reTraceLoop_rotate <;> assumption
theorem reTraceProd4_reverse (a b c d : ComplexMatrix2.specialUnitary) :
    reTraceProd4 d⁻¹ c⁻¹ b⁻¹ a⁻¹ = reTraceProd4 a b c d := by apply _root_.YangMills.Construction.InfiniteLattice.FaceEnergyAndMotions.reTraceLoop_reverse <;> assumption
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cyclic_or_reverse_of_fin4 : ∀ i j k l : Fin 4, (∀ m, m = i ∨ m = j ∨ m = k ∨ m = l) →
    j ≠ i + 2 → k ≠ j + 2 → l ≠ k + 2 → i ≠ l + 2 →
    (i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 3 ∧ l = 0) ∨
    (i = 2 ∧ j = 3 ∧ k = 0 ∧ l = 1) ∨ (i = 3 ∧ j = 0 ∧ k = 1 ∧ l = 2) ∨
    (i = 0 ∧ j = 3 ∧ k = 2 ∧ l = 1) ∨ (i = 1 ∧ j = 0 ∧ k = 3 ∧ l = 2) ∨
    (i = 2 ∧ j = 1 ∧ k = 0 ∧ l = 3) ∨ (i = 3 ∧ j = 2 ∧ k = 1 ∧ l = 0) := by
  decide +kernel
def IsNeighbour (x y : LatticePoint 1) : Prop :=
  ∃ μ : Fin 4, y - x = axisStep 1 μ ∨ y - x = -axisStep 1 μ
theorem IsNeighbour.symm {x y : LatticePoint 1} (h : IsNeighbour x y) : IsNeighbour y x := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr (by rw [← h]; abel)⟩
  · exact ⟨μ, Or.inl (by rw [← neg_eq_iff_eq_neg.mpr h]; abel)⟩
open Classical in
def linkValue (U : GaugeField 1) (x y : LatticePoint 1) : ComplexMatrix2.specialUnitary :=
  if h : IsNeighbour x y then U ⟨x, y, h⟩ else 1
theorem linkValue_of_isNeighbour (U : GaugeField 1) {x y : LatticePoint 1} (h : IsNeighbour x y) :
    linkValue U x y = U ⟨x, y, h⟩ :=
  dif_pos h
theorem linkValue_swap (U : GaugeField 1) (x y : LatticePoint 1) :
    linkValue U y x = (linkValue U x y)⁻¹ := by
  by_cases h : IsNeighbour x y
  · rw [linkValue_of_isNeighbour U h.symm, linkValue_of_isNeighbour U h]
    exact U.2 ⟨x, y, h⟩
  · have h' : ¬ IsNeighbour y x := fun k => h k.symm
    simp [linkValue, h, h']
theorem linkValue_of_unitDistance (U : GaugeField 1) (x y : LatticePoint 1)
    (h : TorusMetric.euclidNormVec ((x : AmbientSpace) - (y : AmbientSpace)) = 1) :
    U (linkOfUnitDistance x y h) = linkValue U x y :=
  (linkValue_of_isNeighbour U (linkOfUnitDistance x y h).isAdjacent).symm
def vertex (p : ElementaryPlaquette 1) : Fin 4 → LatticePoint 1 :=
  ![p.corner, p.corner + axisStep 1 p.lowAxis, p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis,
    p.corner + axisStep 1 p.highAxis]
theorem range_vertex (p : ElementaryPlaquette 1) : range (vertex p) = p.cornerSet := by
  ext y
  simp [vertex, ElementaryPlaquette.cornerSet]
  tauto
theorem coe_axisStep (μ ν : Fin 4) :
    ((axisStep 1 μ : LatticePoint 1) : AmbientSpace) ν = if ν = μ then 1 else 0 := by
  simp [axisStep, Pi.single_apply]
theorem vertex_injective (p : ElementaryPlaquette 1) : Function.Injective (vertex p) := by
  have hne : p.lowAxis ≠ p.highAxis := ne_of_lt p.lowAxis_lt_highAxis
  intro i j h
  have h₁ := congrFun (congrArg Subtype.val h) p.lowAxis
  have h₂ := congrFun (congrArg Subtype.val h) p.highAxis
  fin_cases i <;> fin_cases j <;>
    simp [vertex, coe_axisStep, hne, hne.symm] at h₁ h₂ ⊢
theorem not_isNeighbour_opposite (p : ElementaryPlaquette 1) (i : Fin 4) :
    ¬ IsNeighbour (vertex p i) (vertex p (i + 2)) := by
  have hne : p.lowAxis ≠ p.highAxis := ne_of_lt p.lowAxis_lt_highAxis
  rintro ⟨μ, h⟩
  have key : ∀ d : LatticePoint 1, (d : AmbientSpace) p.lowAxis ≠ 0 →
      (d : AmbientSpace) p.highAxis ≠ 0 → d ≠ axisStep 1 μ ∧ d ≠ -axisStep 1 μ := by
    intro d h₁ h₂
    have hμ : p.lowAxis ≠ μ ∨ p.highAxis ≠ μ := by
      by_cases hl : p.lowAxis = μ
      · exact Or.inr fun h => hne (hl.trans h.symm)
      · exact Or.inl hl
    constructor
    · rintro rfl
      rcases hμ with hμ | hμ
      · exact h₁ (by simp [coe_axisStep, hμ])
      · exact h₂ (by simp [coe_axisStep, hμ])
    · rintro rfl
      rcases hμ with hμ | hμ
      · exact h₁ (by simp [coe_axisStep, hμ])
      · exact h₂ (by simp [coe_axisStep, hμ])
  have hd := key (vertex p (i + 2) - vertex p i)
    (by fin_cases i <;> simp [vertex, coe_axisStep, hne])
    (by fin_cases i <;> simp [vertex, coe_axisStep, hne.symm])
  rcases h with h | h
  · exact hd.1 h
  · exact hd.2 h
theorem faceHolonomy_eq_prod (U : GaugeField 1) (p : ElementaryPlaquette 1) :
    faceHolonomy U p = linkValue U (vertex p 0) (vertex p 1) *
      linkValue U (vertex p 1) (vertex p 2) * linkValue U (vertex p 2) (vertex p 3) *
        linkValue U (vertex p 3) (vertex p 0) := by
  have e₂ : vertex p 2 = p.corner + axisStep 1 p.highAxis + axisStep 1 p.lowAxis := by
    change p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis = _
    abel
  have e₃ : vertex p 3 = p.corner + axisStep 1 p.highAxis := rfl
  have f₁ : linkValue U (vertex p 0) (vertex p 1) = U (Link.forwardFrom p.corner p.lowAxis) :=
    linkValue_of_isNeighbour U (Link.forwardFrom p.corner p.lowAxis).isAdjacent
  have f₂ : linkValue U (vertex p 1) (vertex p 2) =
      U (Link.forwardFrom (p.corner + axisStep 1 p.lowAxis) p.highAxis) :=
    linkValue_of_isNeighbour U (Link.forwardFrom (p.corner + axisStep 1 p.lowAxis) p.highAxis).isAdjacent
  have f₃ : linkValue U (vertex p 3) (vertex p 2) =
      U (Link.forwardFrom (p.corner + axisStep 1 p.highAxis) p.lowAxis) := by
    rw [e₂, e₃]
    exact linkValue_of_isNeighbour U
      (Link.forwardFrom (p.corner + axisStep 1 p.highAxis) p.lowAxis).isAdjacent
  have f₄ : linkValue U (vertex p 0) (vertex p 3) = U (Link.forwardFrom p.corner p.highAxis) :=
    linkValue_of_isNeighbour U (Link.forwardFrom p.corner p.highAxis).isAdjacent
  rw [linkValue_swap U (vertex p 3) (vertex p 2), linkValue_swap U (vertex p 0) (vertex p 3), f₁,
    f₂, f₃, f₄]
  rfl
theorem reTraceProd4_of_closedPath (U : GaugeField 1) (p : ElementaryPlaquette 1)
    {y₁ y₂ y₃ y₄ : LatticePoint 1}
    (hy : ({y₁, y₂, y₃, y₄} : Set (LatticePoint 1)) = p.cornerSet)
    (h₁₂ : IsNeighbour y₁ y₂) (h₂₃ : IsNeighbour y₂ y₃) (h₃₄ : IsNeighbour y₃ y₄)
    (h₄₁ : IsNeighbour y₄ y₁) :
    reTraceProd4 (linkValue U y₁ y₂) (linkValue U y₂ y₃) (linkValue U y₃ y₄) (linkValue U y₄ y₁) =
      (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re := by
  have hr := range_vertex p
  have hc := vertex_injective p
  have hn := not_isNeighbour_opposite p
  obtain ⟨i₁, rfl⟩ : y₁ ∈ range (vertex p) := hr ▸ hy ▸ (by simp)
  obtain ⟨i₂, rfl⟩ : y₂ ∈ range (vertex p) := hr ▸ hy ▸ (by simp)
  obtain ⟨i₃, rfl⟩ : y₃ ∈ range (vertex p) := hr ▸ hy ▸ (by simp)
  obtain ⟨i₄, rfl⟩ : y₄ ∈ range (vertex p) := hr ▸ hy ▸ (by simp)
  have hs : ∀ k, k = i₁ ∨ k = i₂ ∨ k = i₃ ∨ k = i₄ := fun k => by
    have h : vertex p k ∈ p.cornerSet := hr ▸ mem_range_self k
    rw [← hy] at h
    simpa [hc.eq_iff] using h
  have n₁ : i₂ ≠ i₁ + 2 := fun h => hn i₁ (h ▸ h₁₂)
  have n₂ : i₃ ≠ i₂ + 2 := fun h => hn i₂ (h ▸ h₂₃)
  have n₃ : i₄ ≠ i₃ + 2 := fun h => hn i₃ (h ▸ h₃₄)
  have n₄ : i₁ ≠ i₄ + 2 := fun h => hn i₄ (h ▸ h₄₁)
  have e₀ := linkValue_swap U (vertex p 0) (vertex p 1)
  have e₁ := linkValue_swap U (vertex p 1) (vertex p 2)
  have e₂ := linkValue_swap U (vertex p 2) (vertex p 3)
  have e₃ := linkValue_swap U (vertex p 3) (vertex p 0)
  have r₀ : reTraceProd4 (linkValue U (vertex p 0) (vertex p 1))
      (linkValue U (vertex p 1) (vertex p 2))
      (linkValue U (vertex p 2) (vertex p 3)) (linkValue U (vertex p 3) (vertex p 0)) =
      (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re := by
    rw [faceHolonomy_eq_prod, reTraceProd4]
  have r₁ := (reTraceProd4_rotate (linkValue U (vertex p 0) (vertex p 1))
    (linkValue U (vertex p 1) (vertex p 2)) (linkValue U (vertex p 2) (vertex p 3))
    (linkValue U (vertex p 3) (vertex p 0))).trans r₀
  have r₂ := (reTraceProd4_rotate (linkValue U (vertex p 1) (vertex p 2))
    (linkValue U (vertex p 2) (vertex p 3)) (linkValue U (vertex p 3) (vertex p 0))
    (linkValue U (vertex p 0) (vertex p 1))).trans r₁
  have r₃ := (reTraceProd4_rotate (linkValue U (vertex p 2) (vertex p 3))
    (linkValue U (vertex p 3) (vertex p 0)) (linkValue U (vertex p 0) (vertex p 1))
    (linkValue U (vertex p 1) (vertex p 2))).trans r₂
  rcases cyclic_or_reverse_of_fin4 i₁ i₂ i₃ i₄ hs n₁ n₂ n₃ n₄ with
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact r₀
  · exact r₁
  · exact r₂
  · exact r₃
  · rw [e₃, e₂, e₁, e₀]
    exact (reTraceProd4_reverse _ _ _ _).trans r₀
  · rw [e₀, e₃, e₂, e₁]
    exact (reTraceProd4_reverse _ _ _ _).trans r₁
  · rw [e₁, e₀, e₃, e₂]
    exact (reTraceProd4_reverse _ _ _ _).trans r₂
  · rw [e₂, e₁, e₀, e₃]
    exact (reTraceProd4_reverse _ _ _ _).trans r₃
end PlaquetteLoops
open PlaquetteLoops in
theorem plaquetteLoopTraces_of_unitaryLogarithm
    (hlog : ComplexMatrix2.UnitaryLogarithmProperties) : PlaquetteLoopTraces := by
  refine ⟨?_, re_fullTrace_mul_comm, re_fullTrace_inv, fun p U => ?_⟩
  · intro p y₁ y₂ y₃ y₄ hy h₁₂ h₂₃ h₃₄ h₄₁ U
    have key := reTraceProd4_of_closedPath U p hy (linkOfUnitDistance y₁ y₂ h₁₂).isAdjacent
      (linkOfUnitDistance y₂ y₃ h₂₃).isAdjacent (linkOfUnitDistance y₃ y₄ h₃₄).isAdjacent
      (linkOfUnitDistance y₄ y₁ h₄₁).isAdjacent
    rw [linkValue_of_unitDistance U y₁ y₂ h₁₂, linkValue_of_unitDistance U y₂ y₃ h₂₃,
      linkValue_of_unitDistance U y₃ y₄ h₃₄, linkValue_of_unitDistance U y₄ y₁ h₄₁]
    exact key
  · obtain ⟨t, ⟨h₁, h₂⟩, ht⟩ := (hlog.2.1 _ (faceHolonomy U p).2).1
    have hre : ((1 / 2 : ℂ) * ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re =
        (t : ℂ).re :=
      congrArg Complex.re ht
    have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [e, Complex.re_ofReal_mul, Complex.ofReal_re] at hre
    unfold faceEnergy
    constructor <;> linarith
end InfiniteLattice
end YangMills.Construction
