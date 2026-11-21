import YangMills.Construction.VolumeTransfer.LatticeSymmetriesAndInvariantMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.VolumeTransfer
open InfiniteLattice (AmbientSpace refinedLattice refinedSpacing RefinedGaugeField)
namespace LatticeGeometry
variable {L K : ℕ}
theorem diagSign_add (s : Fin 4 → ℤˣ) (p q : AmbientSpace) :
    diagSign s (p + q) = diagSign s p + diagSign s q := by
  funext i
  simp only [Pi.add_apply, diagSign_apply]
  ring
theorem diagSign_neg (s : Fin 4 → ℤˣ) (p : AmbientSpace) : diagSign s (-p) = -diagSign s p := by
  funext i
  simp only [Pi.neg_apply, diagSign_apply]
  ring
theorem diagSign_sub (s : Fin 4 → ℤˣ) (p q : AmbientSpace) :
    diagSign s (p - q) = diagSign s p - diagSign s q := by
  rw [sub_eq_add_neg, diagSign_add, diagSign_neg, ← sub_eq_add_neg]
theorem diagSign_mem_latticeSubgroup {a : ℝ} (s : Fin 4 → ℤˣ) {p : AmbientSpace}
    (hp : p ∈ InfiniteLattice.latticeSubgroup a) :
    diagSign s p ∈ InfiniteLattice.latticeSubgroup a := by
  obtain ⟨k, hk⟩ := hp
  refine ⟨fun i => ((s i : ℤˣ) : ℤ) * k i, fun i => ?_⟩
  rw [diagSign_apply, hk i]
  push_cast
  ring
theorem diagSign_axisStep (a : ℝ) (s : Fin 4 → ℤˣ) (i : Fin 4) :
    diagSign s (InfiniteLattice.axisStep a i : AmbientSpace) =
        (InfiniteLattice.axisStep a i : AmbientSpace) ∨
      diagSign s (InfiniteLattice.axisStep a i : AmbientSpace) =
        -(InfiniteLattice.axisStep a i : AmbientSpace) := by
  have hs : (InfiniteLattice.axisStep a i : AmbientSpace) = Pi.single i a := rfl
  rw [hs]
  rcases Int.units_eq_one_or (s i) with h | h
  · left
    funext j
    rw [diagSign_apply]
    by_cases hj : j = i
    · subst hj
      simp [h]
    · simp [Pi.single_eq_of_ne hj]
  · right
    funext j
    rw [diagSign_apply]
    by_cases hj : j = i
    · subst hj
      simp [h]
    · simp [Pi.single_eq_of_ne hj]
theorem exists_link_image_diagSign_add {a : ℝ} (s : Fin 4 → ℤˣ) {v : AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup a) (e : InfiniteLattice.Link a) :
    ∃ e' : InfiniteLattice.Link a,
      (e'.initial : AmbientSpace) = diagSign s (e.initial : AmbientSpace) + v ∧
        (e'.terminal : AmbientSpace) = diagSign s (e.terminal : AmbientSpace) + v := by
  have hmem : ∀ p : InfiniteLattice.LatticePoint a,
      diagSign s (p : AmbientSpace) + v ∈ InfiniteLattice.latticeSubgroup a :=
    fun p => add_mem (diagSign_mem_latticeSubgroup s p.2) hv
  obtain ⟨i, h⟩ := e.isAdjacent
  have hd : diagSign s (e.terminal : AmbientSpace) + v - (diagSign s (e.initial : AmbientSpace) + v) =
      diagSign s ((e.terminal - e.initial : InfiniteLattice.LatticePoint a) : AmbientSpace) := by
    rw [AddSubgroup.coe_sub, diagSign_sub]
    abel
  refine ⟨⟨⟨_, hmem e.initial⟩, ⟨_, hmem e.terminal⟩, i, ?_⟩, rfl, rfl⟩
  rcases h with h | h <;> rcases diagSign_axisStep a s i with h' | h'
  · left
    apply Subtype.ext
    rw [AddSubgroup.coe_sub]
    rw [hd, h, h']
  · right
    apply Subtype.ext
    rw [AddSubgroup.coe_sub]
    rw [hd, h, h']
    rfl
  · right
    apply Subtype.ext
    rw [AddSubgroup.coe_sub]
    rw [hd, h, AddSubgroup.coe_neg, diagSign_neg, h']
  · left
    apply Subtype.ext
    rw [AddSubgroup.coe_sub]
    rw [hd, h, AddSubgroup.coe_neg, diagSign_neg, h', neg_neg]
theorem IsReflectionTranslation.mapsLinks_euclidean {f : AmbientSpace → AmbientSpace}
    (hf : (euclidean L K).IsReflectionTranslation f) : (euclidean L K).MapsLinks f := by
  obtain ⟨s, v, hv, hform⟩ := hf
  intro e
  obtain ⟨e', h₁, h₂⟩ := exists_link_image_diagSign_add s hv e
  exact ⟨e', h₁.trans (hform _).symm, h₂.trans (hform _).symm⟩
theorem torusProjHom_axisStep (m : ℕ) (i : Fin 4) :
    TorusCovering.torusProjHom (PeriodicLattice.torusSide L m)
        (InfiniteLattice.axisStep (refinedSpacing L K) i : AmbientSpace) =
      (PeriodicLattice.unitStep L m (K : ℤ) i : PeriodicLattice.FourTorus L m) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [TorusCovering.torusProjHom_apply, TorusMetric.torusProj, InfiniteLattice.axisStep,
      PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
  · simp [TorusCovering.torusProjHom_apply, TorusMetric.torusProj, InfiniteLattice.axisStep,
      PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hj]
theorem exists_periodicBond_of_link (m : ℕ) (e : InfiniteLattice.Link (refinedSpacing L K)) :
    ∃ e' : PeriodicLattice.Bond L m (K : ℤ),
      (e'.source : PeriodicLattice.FourTorus L m) =
          TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (e.initial : AmbientSpace) ∧
        (e'.target : PeriodicLattice.FourTorus L m) =
          TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (e.terminal : AmbientSpace) := by
  have hmem : ∀ p : InfiniteLattice.LatticePoint (refinedSpacing L K),
      TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (p : AmbientSpace) ∈
        PeriodicLattice.sublattice L m (K : ℤ) := by
    rintro ⟨p, k, hk⟩
    exact ⟨k, fun i => congrArg (fun r : ℝ => (r : AddCircle (PeriodicLattice.torusSide L m))) (hk i)⟩
  obtain ⟨i, h⟩ := e.isAdjacent
  have hd : TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (e.terminal : AmbientSpace) -
      TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (e.initial : AmbientSpace) =
        TorusCovering.torusProjHom (PeriodicLattice.torusSide L m)
          ((e.terminal - e.initial : InfiniteLattice.LatticePoint (refinedSpacing L K)) :
            AmbientSpace) := by
    rw [AddSubgroup.coe_sub, map_sub]
  refine ⟨⟨⟨_, hmem e.initial⟩, ⟨_, hmem e.terminal⟩, i, ?_⟩, rfl, rfl⟩
  rcases h with h | h
  · left
    apply Subtype.ext
    rw [AddSubgroup.coe_sub]
    rw [hd, h, torusProjHom_axisStep]
  · right
    apply Subtype.ext
    rw [AddSubgroup.coe_sub]
    rw [hd, h, AddSubgroup.coe_neg, map_neg, torusProjHom_axisStep]
    rfl
theorem exists_link_of_periodicBond {m : ℕ} (e : PeriodicLattice.Bond L m (K : ℤ)) :
    ∃ e' : InfiniteLattice.Link (refinedSpacing L K),
      TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (e'.initial : AmbientSpace) =
          (e.source : PeriodicLattice.FourTorus L m) ∧
        TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (e'.terminal : AmbientSpace) =
          (e.target : PeriodicLattice.FourTorus L m) := by
  obtain ⟨k, hk⟩ := e.source.2
  let p : InfiniteLattice.LatticePoint (refinedSpacing L K) :=
    ⟨fun i => (k i : ℝ) * PeriodicLattice.meshSize L (K : ℤ), k, fun _ => rfl⟩
  have hp : TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (p : AmbientSpace) =
      (e.source : PeriodicLattice.FourTorus L m) := by
    funext i
    exact (hk i).symm
  obtain ⟨i, h | h⟩ := e.isNeighbour
  · refine ⟨InfiniteLattice.Link.forwardFrom p i, hp, ?_⟩
    have h' := congrArg (Subtype.val) h
    rw [AddSubgroup.coe_sub] at h'
    change TorusCovering.torusProjHom (PeriodicLattice.torusSide L m)
      ((p : AmbientSpace) + (InfiniteLattice.axisStep (refinedSpacing L K) i : AmbientSpace)) = _
    rw [map_add, hp, torusProjHom_axisStep, ← h']
    abel
  · refine ⟨⟨p, p - InfiniteLattice.axisStep (refinedSpacing L K) i, i, Or.inr (by abel)⟩, hp, ?_⟩
    have h' := congrArg (Subtype.val) h
    rw [AddSubgroup.coe_sub, AddSubgroup.coe_neg] at h'
    change TorusCovering.torusProjHom (PeriodicLattice.torusSide L m)
      ((p : AmbientSpace) - (InfiniteLattice.axisStep (refinedSpacing L K) i : AmbientSpace)) = _
    rw [map_sub, hp, torusProjHom_axisStep, sub_eq_add_neg, ← h']
    abel
theorem IsReflectionTranslation.mapsLinks_periodic {m : ℕ}
    {f : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m}
    (hf : (periodic L m K).IsReflectionTranslation f) : (periodic L m K).MapsLinks f := by
  obtain ⟨s, v, hv, hform⟩ := hf
  intro e
  obtain ⟨c, hc₁, hc₂⟩ := exists_link_of_periodicBond e
  obtain ⟨c', h₁, h₂⟩ := exists_link_image_diagSign_add s hv c
  obtain ⟨e', h₃, h₄⟩ := exists_periodicBond_of_link m c'
  refine ⟨e', ?_, ?_⟩
  · change (e'.source : PeriodicLattice.FourTorus L m) = f (e.source : PeriodicLattice.FourTorus L m)
    rw [h₃, h₁, ← hc₁]
    exact (hform _).symm
  · change (e'.target : PeriodicLattice.FourTorus L m) = f (e.target : PeriodicLattice.FourTorus L m)
    rw [h₄, h₂, ← hc₂]
    exact (hform _).symm
end LatticeGeometry
def IsInvariantUnderReflectionTranslation {L K : ℕ} (μ : Measure (RefinedGaugeField L K))
    [IsProbabilityMeasure μ] {f : AmbientSpace → AmbientSpace}
    (hf : (LatticeGeometry.euclidean L K).IsReflectionTranslation f) : Prop :=
  IsInvariantUnderLinkMap μ (LatticeGeometry.IsReflectionTranslation.mapsLinks_euclidean hf)
end YangMills.Construction.VolumeTransfer
end
