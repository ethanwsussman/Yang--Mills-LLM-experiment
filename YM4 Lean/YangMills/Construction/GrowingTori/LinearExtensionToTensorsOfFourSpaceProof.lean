import YangMills.Construction.GrowingTori.LinearExtensionToTensorsOfFourSpace
import YangMills.Construction.GrowingTori.SubFamiliesNeighbourhoodsAndTheSeparation
import YangMills.Construction.TorusOrFourSpace.LinearExtensionToTensors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriLimits.TensorExtension
open PeriodicSpace
theorem holds_of_tensorExtension (hExtension : Kind.TensorExtension.Claim)
    (hGaps : SubfamiliesAndGaps.Statement) : Holds := by
  intro D Y q hq Ψ hΨ
  have hset : Kind.sepC1Tuples Y Kind.euclidean q =
      sepTuplesR4 D.toStandingParameters q :=
    (hGaps.2.2.2.2.1 Y).2.2.2 D.toStandingParameters |>.2 q hq
  have hmem : ∀ f : Fin q → RealFn,
      f ∈ Kind.sepC1Tuples Y Kind.euclidean q ↔
        f ∈ TestTupleClass.sep.members D.toStandingParameters q := fun f => by
    rw [hset]
    rfl
  let Ψ' : Kind.sepC1Tuples Y Kind.euclidean q → ℝ :=
    fun f => Ψ ⟨f.1, (hmem f.1).1 f.2⟩
  have hΨ' : Kind.IsMultilinearOn Y Kind.euclidean
      (Kind.sepC1Tuples Y Kind.euclidean q) Ψ' := by
    intro i h h' hagree
    let g : TestTupleClass.sep.members D.toStandingParameters q := ⟨h.1, (hmem h.1).1 h.2⟩
    let g' : TestTupleClass.sep.members D.toStandingParameters q := ⟨h'.1, (hmem h'.1).1 h'.2⟩
    constructor
    · intro hSum
      have e : Function.update g.1 i ((1 : ℝ) • g.1 i + (1 : ℝ) • g'.1 i) =
          Function.update h.1 i (h.1 i + h'.1 i) := by
        simp only [one_smul]
        rfl
      have hm : Function.update g.1 i ((1 : ℝ) • g.1 i + (1 : ℝ) • g'.1 i) ∈
          TestTupleClass.sep.members D.toStandingParameters q := by
        rw [e]
        exact (hmem _).1 hSum
      have key := hΨ i g g' hagree 1 1 hm
      have hval : Ψ' ⟨_, hSum⟩ = Ψ ⟨_, hm⟩ := congrArg Ψ (Subtype.ext e.symm)
      refine hval.trans (key.trans ?_)
      simp [Ψ', g, g']
    · intro α hScaled
      have e : Function.update g.1 i (α • g.1 i + (0 : ℝ) • g.1 i) =
          Function.update h.1 i (α • h.1 i) := by
        simp only [zero_smul, add_zero]
        rfl
      have hm : Function.update g.1 i (α • g.1 i + (0 : ℝ) • g.1 i) ∈
          TestTupleClass.sep.members D.toStandingParameters q := by
        rw [e]
        exact (hmem _).1 hScaled
      have key := hΨ i g g (fun _ _ => rfl) α 0 hm
      have hval : Ψ' ⟨_, hScaled⟩ = Ψ ⟨_, hm⟩ := congrArg Ψ (Subtype.ext e.symm)
      refine hval.trans (key.trans ?_)
      simp [Ψ', g]
  obtain ⟨hRelations, T₀, hT₀, hT₀unique⟩ := (hExtension Y Kind.euclidean).1 q hq Ψ' hΨ'
  refine ⟨?_, ?_⟩
  · intro B _ c X hsum
    let e := Fintype.equivFin B
    have hrel := hRelations (Fintype.card B)
      (fun k => ⟨(X (e.symm k)).1, (hmem _).2 (X (e.symm k)).2⟩) (fun k => c (e.symm k))
      ((Equiv.sum_comp e.symm fun b => c b • realTensor Y (X b).1).trans hsum)
    exact (Equiv.sum_comp e.symm fun b => c b * ((Ψ (X b) : ℝ) : ℂ)).symm.trans hrel
  · have hspan := sepTensorSpanOn_univ Y q
    let e := LinearEquiv.ofEq _ _ hspan
    have hin : ∀ X : TestTupleClass.sep.members D.toStandingParameters q,
        realTensor Y X.1 ∈ sepTensorSpanOn Y q Set.univ := fun X => by
      rw [hspan]
      exact Kind.tensorFn_mem_sepTensorSpan Y Kind.euclidean ⟨X.1, (hmem _).2 X.2⟩
    refine ⟨T₀ ∘ₗ e.toLinearMap, fun X => ⟨hin X, ?_⟩, fun T hT => ?_⟩
    · exact hT₀ ⟨X.1, (hmem _).2 X.2⟩
    · have hT' : T ∘ₗ e.symm.toLinearMap = T₀ := by
        refine hT₀unique _ fun f => ?_
        obtain ⟨hX, hval⟩ := hT ⟨f.1, (hmem _).1 f.2⟩
        exact hval
      rw [← hT']
      ext x
      simp
end YangMills.Construction.ToriLimits.TensorExtension
end
