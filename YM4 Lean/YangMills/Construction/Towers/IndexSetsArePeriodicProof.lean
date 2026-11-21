import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.Towers.IndexSetsArePeriodic
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.PeriodicityProof
open PeriodicOperators
theorem ofSingle_isPeriodic_reweight {W : Type} {s : (Fin 4 → ℤ) → W → W}
    {x : W → InfiniteLattice.AmbientSpace} {w w' : ℝ}
    (h : IsPeriodic (PeriodicData.ofSingle W s x w)) (hw : 0 < w') :
    IsPeriodic (PeriodicData.ofSingle W s x w') where
  translate_zero := h.translate_zero
  translate_add := h.translate_add
  free := h.free
  finite_quot := h.finite_quot
  pos_translate := h.pos_translate
  finite_components := h.finite_components
  componentOf_translate := h.componentOf_translate
  weight_pos := fun _ => hw
theorem ofSingle_isPeriodic_of_coloured {W : Type} {s : (Fin 4 → ℤ) → W → W}
    {x : W → InfiniteLattice.AmbientSpace} {w w' : ℝ}
    (h : IsPeriodic (PeriodicData.ofSingle (Fin 3 × W) (fun m i => (i.1, s m i.2))
      (fun i => x i.2) w)) (hw : 0 < w') :
    IsPeriodic (PeriodicData.ofSingle W s x w') where
  translate_zero := fun σ => congrArg Prod.snd (h.translate_zero ((0 : Fin 3), σ))
  translate_add := fun m m' σ => congrArg Prod.snd (h.translate_add m m' ((0 : Fin 3), σ))
  free := fun m σ e => h.free m ((0 : Fin 3), σ) (Prod.ext rfl e)
  finite_quot := by
    have := h.finite_quot
    let q : (PeriodicData.ofSingle (Fin 3 × W) (fun m i => (i.1, s m i.2)) (fun i => x i.2) w).UnitQuot →
        (PeriodicData.ofSingle W s x w').UnitQuot :=
      Quot.lift (fun i => (PeriodicData.ofSingle W s x w').mkQuot 1 i.2) (by
        rintro i _ ⟨m, rfl⟩
        exact Quot.sound ⟨m, rfl⟩)
    refine Finite.of_surjective q fun c => ?_
    induction c using Quot.ind with
    | mk σ => exact ⟨Quot.mk _ ((0 : Fin 3), σ), rfl⟩
  pos_translate := fun m σ => h.pos_translate m ((0 : Fin 3), σ)
  finite_components := h.finite_components
  componentOf_translate := fun _ _ => rfl
  weight_pos := fun _ => hw
theorem component_isPeriodic (h : TowerIndexSets.Claim) (L : ℕ)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) (P : Component k) :
    IsPeriodic (P.toPeriodicData L) := by
  obtain ⟨j, hj, kind, col, w, hw⟩ := P
  obtain ⟨hS, hB, hP⟩ := h L hL k j hj
  cases kind <;> cases col
  · exact ofSingle_isPeriodic_of_coloured hS hw
  · exact ofSingle_isPeriodic_reweight hS hw
  · exact ofSingle_isPeriodic_of_coloured hB hw
  · exact ofSingle_isPeriodic_reweight hB hw
  · exact ofSingle_isPeriodic_of_coloured hP hw
  · exact ofSingle_isPeriodic_reweight hP hw
def slotEquivComponent {k : ℕ} (L : ℕ) (I : WeightedIndexSet k) :
    I.Slot ≃ (I.toPeriodicData L).Component where
  toFun := fun p => ⟨p, ()⟩
  invFun := fun q => q.1
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
theorem indexSetPeriodicity_holds (h : TowerIndexSets.Claim) : IndexSetPeriodicity.Statement :=
  fun L hL k =>
  ⟨component_isPeriodic h L hL k, fun I =>
    ⟨by
      have := I.finite_slot
      exact IsPeriodic.sigma fun p => component_isPeriodic h L hL k (I.comp p),
      slotEquivComponent L I, fun _ => rfl, fun _ => rfl⟩⟩
end YangMills.Construction.LocalKernels.PeriodicityProof
end
