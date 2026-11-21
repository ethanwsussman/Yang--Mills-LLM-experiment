import YangMills.Construction.SummableBoundsOfTheFlow.DerivativeInTheTopAlongASegment
import YangMills.Construction.SummableBoundsOfTheFlow.MeanNearANumber
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfADerivativeOfAnExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.TopDerivativesOfASmoothFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Cumulants
variable {F : BlockFrame}
namespace MeanFieldDerivNearValue
theorem cellSupDist_le_cellSetDiameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ Interpolation.cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
theorem bondSpan_le_cellSetDiameter {P : Finset F.Cell} {Y : F.Cell} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} (hY : Y ∈ P)
    (hc : ∀ l, (c l).1 ∈ P) : bondSpan Y c ≤ Interpolation.cellSetDiameter P := by
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · exact cellSupDist_le_cellSetDiameter hY (hc l)
  · exact cellSupDist_le_cellSetDiameter (hc l) (hc l')
end MeanFieldDerivNearValue
open MeanFieldDerivNearValue in
theorem meanFieldDerivNearValue_holds (hTD : Estimates.fieldDerivRegularityStatement)
    (hSeg : Estimates.fieldDerivAlongSegmentStatement) (hMN : Estimates.ExpectationNearConstant) :
    meanFieldDerivNearValueStatement := by
  classical
  intro F star a ρA m ρ κ Cg ε₃ W₀ N₀ M₂ t p Φ h V Y hρ hκ hCg hε₃ ht hW₀ hN₀ hM₂ hrow Fm hgrad hmom hW hcard k c X hk hX
  have TD := hTD F ρ V
  set S := (sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y with hSdef
  set H := cellExpansionInField star a ρA m h Y with hH
  have hHS : H = fun η V' => ∑ y ∈ S, centredExpansion star a ρA m h y η V' := rfl
  have hHJ : Estimates.JointlyContDiffOnBalls ρ V H := fun j c' X' η hη => by
    rw [hHS]
    exact ContDiffAt.sum fun y _ => hrow y j c' X' η hη
  have hk3 : k ≤ 3 := by omega
  have hzero : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ ≤ ρ := fun b => by simpa using hρ.le
  have hsumAt : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      Estimates.fieldDeriv H V c X η = ∑ y ∈ S, Estimates.fieldDeriv (centredExpansion star a ρA m h y) V c X η :=
    fun η hη => by
    rw [hHS]
    exact TD.sum _ S (fun y => centredExpansion star a ρA m h y) k c X η (fun y _ => hrow y) hk3 hη
  set D : ↥(chordBonds (finiteCells F)) → ℝ := fun b => ∑ y ∈ S, Cg * ε₃ *
    Real.exp (-(2 ^ 7 * κ * Interpolation.cellSetDiameter (insert (enclosingCell y)
      (Interpolation.chordBondCells ![b] ∪ Interpolation.topBondCells c)))) with hD
  have hD0 : ∀ b, 0 ≤ D b := fun b =>
    Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg hCg hε₃) (Real.exp_pos _).le
  have hnice : IsBoundedContinuousOn ↥(chordBonds (finiteCells F)) ρ (Estimates.fieldDeriv H V c X) := by
    obtain ⟨B, hB⟩ := TD.bounded H k c X hHJ hk3
    exact ⟨TD.continuousOn H k c X hHJ hk3, B, fun η hη => hB η fun b => (hη b).le⟩
  have hclose : ∀ η ∈ openPolyball ↥(chordBonds (finiteCells F)) ρ,
      |Estimates.fieldDeriv H V c X η - Estimates.fieldDeriv H V c X 0| ≤ ∑ b, ‖η b‖ * D b := fun η hη => by
    have hη' : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
    rw [hsumAt η hη', hsumAt 0 hzero, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hy : ∀ y ∈ S, |Estimates.fieldDeriv (centredExpansion star a ρA m h y) V c X η -
        Estimates.fieldDeriv (centredExpansion star a ρA m h y) V c X 0| ≤
        ∑ b, ‖η b‖ * (Cg * ε₃ *
          Real.exp (-(2 ^ 7 * κ * Interpolation.cellSetDiameter (insert (enclosingCell y)
            (Interpolation.chordBondCells ![b] ∪ Interpolation.topBondCells c))))) :=
      fun y _ => hSeg F ρ V _ k c X _ η (hrow y) hk
        (fun ζ hζ b v hv => hgrad y ζ b v k c X hζ hv hk hX) hη'
    refine (Finset.sum_le_sum hy).trans (le_of_eq ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hD, Finset.mul_sum]
  have hmain := hMN ↥(chordBonds (finiteCells F)) ρ p Φ (Estimates.fieldDeriv H V c X) D
    (Estimates.fieldDeriv H V c X 0) t M₂ hρ ht Fm hnice hD0 hclose hmom
  set E := Real.exp (-(2 ^ 6 * κ * (bondSpan Y c : ℝ))) with hE
  have hpair : ∀ (y : F.Site F.depth) (b : ↥(chordBonds (finiteCells F))), y ∈ S →
      Real.exp (-(2 ^ 7 * κ * Interpolation.cellSetDiameter (insert (enclosingCell y)
        (Interpolation.chordBondCells ![b] ∪ Interpolation.topBondCells c)))) ≤
        E * Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) := fun y b hy => by
    have hyY : enclosingCell y = Y := (Finset.mem_filter.mp hy).2
    set P := insert (enclosingCell y) (Interpolation.chordBondCells ![b] ∪ Interpolation.topBondCells c) with hP
    have hYP : Y ∈ P := by
      rw [hP, hyY]
      exact Finset.mem_insert_self _ _
    have hcP : ∀ l, (c l).1 ∈ P := fun l =>
      Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩))
    have hbP : enclosingCell b.1.1 ∈ P :=
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩))
    have h1 : (bondSpan Y c : ℝ) ≤ (Interpolation.cellSetDiameter P : ℝ) := by
      exact_mod_cast bondSpan_le_cellSetDiameter hYP hcP
    have h2 : (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ (Interpolation.cellSetDiameter P : ℝ) := by
      exact_mod_cast cellSupDist_le_cellSetDiameter hbP hYP
    rw [hE, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hsum : ∑ b, D b ≤ N₀ * (Cg * ε₃) * W₀ * E := by
    rw [hD, Finset.sum_comm]
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hCe : 0 ≤ Cg * ε₃ := mul_nonneg hCg hε₃
    have hy : ∀ y ∈ S, ∑ b : ↥(chordBonds (finiteCells F)), Cg * ε₃ *
        Real.exp (-(2 ^ 7 * κ * Interpolation.cellSetDiameter (insert (enclosingCell y)
          (Interpolation.chordBondCells ![b] ∪ Interpolation.topBondCells c)))) ≤
        Cg * ε₃ * (E * W₀) := fun y hy => by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hCe
      refine (Finset.sum_le_sum fun b _ => hpair y b hy).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hW hE0
    refine (Finset.sum_le_sum hy).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have : 0 ≤ Cg * ε₃ * (E * W₀) := by positivity
    calc (S.card : ℝ) * (Cg * ε₃ * (E * W₀)) ≤ N₀ * (Cg * ε₃ * (E * W₀)) :=
          mul_le_mul_of_nonneg_right hcard this
      _ = N₀ * (Cg * ε₃) * W₀ * E := by ring
  have hT0 : 0 ≤ t / 2 + M₂ / (2 * t) := by positivity
  have hEle : E ≤ Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
    refine Real.exp_le_exp.mpr ?_
    have h0 : (0 : ℝ) ≤ (bondSpan Y c : ℝ) := Nat.cast_nonneg _
    have : κ / 2 ^ 6 * (bondSpan Y c : ℝ) ≤ 2 ^ 6 * κ * (bondSpan Y c : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ h0
      norm_num
      linarith
    linarith
  have hK0 : 0 ≤ N₀ * (Cg * ε₃) * W₀ := by positivity
  calc |ballExpectation (cutoffFactor ρ p) Φ (Estimates.fieldDeriv H V c X) - Estimates.fieldDeriv H V c X 0|
      ≤ (∑ b, D b) * (t / 2 + M₂ / (2 * t)) := hmain
    _ ≤ N₀ * (Cg * ε₃) * W₀ * E * (t / 2 + M₂ / (2 * t)) := mul_le_mul_of_nonneg_right hsum hT0
    _ = N₀ * (Cg * ε₃) * W₀ * (t / 2 + M₂ / (2 * t)) * E := by ring
    _ ≤ N₀ * (Cg * ε₃) * W₀ * (t / 2 + M₂ / (2 * t)) * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) :=
      mul_le_mul_of_nonneg_left hEle (mul_nonneg hK0 hT0)
end Cumulants
end YangMills.Construction
end
