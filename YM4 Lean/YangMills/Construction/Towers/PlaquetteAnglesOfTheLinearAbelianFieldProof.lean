import YangMills.Construction.Towers.PlaquetteAnglesOfTheLinearAbelianField
import YangMills.Construction.Towers.PlaquettesOfABondProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LinearFieldPlaquetteAngles
open AbelianFieldFacts
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ ν : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ν) : μ = ν := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
theorem linearAbelianAngle_forwardEdge {a : ℝ} (ha : a ≠ 0) (x : InfiniteLattice.LatticePoint a)
    (μ : Fin 4) :
    FullSpace.linearAbelianAngle (FullSpace.forwardEdge x μ) =
      if μ = 1 then (x : InfiniteLattice.AmbientSpace) 0 else 0 := by
  have hd : (FullSpace.forwardEdge x μ).1.terminal - (FullSpace.forwardEdge x μ).1.initial =
      InfiniteLattice.axisStep a μ := by
    simp [FullSpace.forwardEdge, InfiniteLattice.Link.forwardFrom]
  have ht : (FullSpace.forwardEdge x μ).1.initial = x := rfl
  unfold FullSpace.linearAbelianAngle
  simp only [hd]
  simp only [ht]
  by_cases h : μ = 1
  · subst h
    simp
  · have hne : ¬ InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a 1 :=
      fun e => h (axisStep_injective ha e)
    simp [hne, h]
theorem coord_zero_add_axisStep {a : ℝ} (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    ((x + InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) :
      InfiniteLattice.AmbientSpace) 0 =
      (x : InfiniteLattice.AmbientSpace) 0 + if μ = 0 then a else 0 := by
  by_cases h : μ = 0
  · subst h
    simp [InfiniteLattice.axisStep]
  · simp [InfiniteLattice.axisStep, h]
theorem edgeDifference_linearAbelianAngle {a : ℝ} (ha : a ≠ 0)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    FullSpace.edgeDifference (FullSpace.linearAbelianAngle (a := a)) p =
      if p.lowAxis = 0 ∧ p.highAxis = 1 then a else 0 := by
  obtain ⟨x, μ, ν, hμν⟩ := p
  simp only [FullSpace.edgeDifference, linearAbelianAngle_forwardEdge ha, coord_zero_add_axisStep]
  revert hμν
  fin_cases μ <;> fin_cases ν <;> simp
theorem claim_holds : Claim := by
  intro L _ f p
  have ha : meshAt L 0 0 = 1 := by simp [meshAt]
  have hd := edgeDifference_linearAbelianAngle (a := meshAt L 0 0) (by rw [ha]; exact one_ne_zero) p
  have hf : FullSpace.faceAngle (fun b => f * FullSpace.linearAbelianAngle b) p =
      f * FullSpace.edgeDifference FullSpace.linearAbelianAngle p := by
    simp only [FullSpace.faceAngle, FullSpace.edgeDifference]
    ring
  rw [hf, hd]
  split_ifs
  · rw [ha, mul_one]
  · rw [mul_zero]
end YangMills.Construction.Tower.LinearFieldPlaquetteAngles
end
