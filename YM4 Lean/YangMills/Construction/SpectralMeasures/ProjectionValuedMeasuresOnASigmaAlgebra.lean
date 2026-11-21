import YangMills.Construction.HilbertSpaces.ComplexHilbertSpaceDefs
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralMeasures
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert
abbrev MeasSet (X : Type) [MeasurableSpace X] : Type := {Y : Set X // MeasurableSet Y}
def IsCountablyAdditive {X : Type} [MeasurableSpace X] (m : MeasSet X → ℂ) : Prop :=
  ∀ Y : ℕ → MeasSet X, Pairwise (fun k l => Disjoint (Y k).1 (Y l).1) →
    HasSum (fun k => m (Y k)) (m ⟨⋃ k, (Y k).1, MeasurableSet.iUnion fun k => (Y k).2⟩)
section Spaces
variable {X X' H H' : Type} [MeasurableSpace X] [MeasurableSpace X']
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
def diagForm (E : MeasSet X → BddOp H) (v : H) (Y : MeasSet X) : ℂ :=
  ⟪v, E Y v⟫_ℂ
structure IsPVM (E : MeasSet X → BddOp H) : Prop where
  isOrthProj : ∀ Y, IsOrthProj (E Y)
  map_univ : E ⟨Set.univ, MeasurableSet.univ⟩ = idOp H
  map_inter : ∀ Y Y', E ⟨Y.1 ∩ Y'.1, Y.2.inter Y'.2⟩ = E Y * E Y'
  countablyAdditive : ∀ v, IsCountablyAdditive (diagForm E v)
variable (X H) in
structure PVM where
  toFun : MeasSet X → BddOp H
  isPVM : IsPVM toFun
namespace PVM
instance : CoeFun (PVM X H) (fun _ => MeasSet X → BddOp H) :=
  ⟨toFun⟩

variable (E : PVM X H)
theorem diagForm_eq_norm_sq (v : H) (Y : MeasSet X) :
    diagForm E v Y = ((‖E Y v‖ ^ 2 : ℝ) : ℂ) := by
  have hP := E.isPVM.isOrthProj Y
  have hidem : E Y (E Y v) = E Y v := by
    have h₁ : (E Y ^ 2) v = E Y v := by rw [hP.idempotent]
    rw [pow_two] at h₁
    exact h₁
  have h₂ : ⟪v, E Y v⟫_ℂ = ⟪E Y v, E Y v⟫_ℂ := by
    rw [← hP.selfAdjoint v (E Y v), hidem]
  rw [diagForm, h₂, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem diagForm_re_nonneg (v : H) (Y : MeasSet X) :
    0 ≤ (diagForm E v Y).re := by
  rw [diagForm_eq_norm_sq, Complex.ofReal_re]
  positivity
theorem diagForm_empty (v : H) :
    diagForm E v ⟨∅, MeasurableSet.empty⟩ = 0 := by
  have hs := E.isPVM.countablyAdditive v (fun _ => ⟨∅, MeasurableSet.empty⟩)
    (fun _ _ _ => disjoint_bot_left)
  exact tendsto_const_nhds_iff.mp hs.summable.tendsto_atTop_zero
def diagMeasure (v : H) : Measure X :=
  Measure.ofMeasurable (fun Y hY => ENNReal.ofReal (diagForm E v ⟨Y, hY⟩).re)
    (by
      show ENNReal.ofReal (diagForm E v ⟨∅, MeasurableSet.empty⟩).re = 0
      rw [diagForm_empty]
      simp)
    (by
      intro f hf hd
      have hs := E.isPVM.countablyAdditive v (fun k => ⟨f k, hf k⟩) hd
      have hr := Complex.hasSum_re hs
      rw [← hr.tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg (fun _ => diagForm_re_nonneg E v _) hr.summable)
theorem diagMeasure_apply (v : H) (Y : MeasSet X) :
    E.diagMeasure v Y.1 = ENNReal.ofReal (diagForm E v Y).re :=
  Measure.ofMeasurable_apply Y.1 Y.2
instance (v : H) : IsFiniteMeasure (E.diagMeasure v) :=
  ⟨by
    have h₁ := E.diagMeasure_apply v ⟨Set.univ, MeasurableSet.univ⟩
    exact h₁ ▸ ENNReal.ofReal_lt_top⟩
theorem diagMeasure_real (v : H) (Y : MeasSet X) :
    (((E.diagMeasure v).real Y.1 : ℝ) : ℂ) = diagForm E v Y := by
  rw [Measure.real, E.diagMeasure_apply, ENNReal.toReal_ofReal (diagForm_re_nonneg E v Y),
    diagForm_eq_norm_sq, Complex.ofReal_re]
end PVM
def IsBddMeasurable (f : X → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
namespace PVM
variable (E : PVM X H)
def IsBddIntegral (f : X → ℂ) (B : BddOp H) : Prop :=
  ∀ v, ⟪v, B v⟫_ℂ = ∫ x, f x ∂(E.diagMeasure v)
def bddIntegral (f : X → ℂ) : BddOp H :=
  Classical.epsilon (E.IsBddIntegral f)
theorem isBddIntegral_bddIntegral {f : X → ℂ} (h : ∃ B, E.IsBddIntegral f B) :
    E.IsBddIntegral f (E.bddIntegral f) :=
  Classical.epsilon_spec h
end PVM
namespace PVM
variable (E : PVM X H)
def pushforward (κ : X → X') (hκ : Measurable κ) (Y' : MeasSet X') : BddOp H :=
  E ⟨κ ⁻¹' Y'.1, hκ Y'.2⟩
end PVM
def unitaryToBdd {W : H →ₗ[ℂ] H'} (hW : IsUnitaryMap W) : BddOpBetween H H' :=
  W.mkContinuous 1 fun v => by rw [one_mul, hW.isometric v]
def unitaryInvToBdd {W : H →ₗ[ℂ] H'} (hW : IsUnitaryMap W) :
    BddOpBetween H' H :=
  (hW.toLinearEquiv.symm : H' →ₗ[ℂ] H).mkContinuous 1 fun w => by
    have h₁ : W ((hW.toLinearEquiv.symm : H' →ₗ[ℂ] H) w) = w :=
      hW.toLinearEquiv.apply_symm_apply w
    have h₂ := hW.isometric ((hW.toLinearEquiv.symm : H' →ₗ[ℂ] H) w)
    rw [h₁] at h₂
    rw [one_mul, h₂]
namespace PVM
variable (E : PVM X H)
def conj {W : H →ₗ[ℂ] H'} (hW : IsUnitaryMap W) (Y : MeasSet X) :
    BddOp H' :=
  unitaryToBdd hW ∘L E Y ∘L unitaryInvToBdd hW
theorem conj_apply {W : H →ₗ[ℂ] H'} (hW : IsUnitaryMap W) (Y : MeasSet X)
    (v : H) : E.conj hW Y (W v) = W (E Y v) := by
  have h₁ : unitaryInvToBdd hW (W v) = v :=
    hW.toLinearEquiv.symm_apply_apply v
  change unitaryToBdd hW (E Y (unitaryInvToBdd hW (W v))) = W (E Y v)
  rw [h₁]
  rfl
end PVM
end Spaces
end YangMills.Construction.SpectralMeasures
