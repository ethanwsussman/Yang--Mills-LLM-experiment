import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def Link.IsWithin {a : ℝ} (e : Link a) (S : Set AmbientSpace) : Prop :=
  (e.initial : AmbientSpace) ∈ S ∧ (e.terminal : AmbientSpace) ∈ S
theorem mem_linksWithin_iff_isWithin {a : ℝ} (e : Link a) (S : Set AmbientSpace) :
    e ∈ linksWithin S ↔ e.IsWithin S :=
  Iff.rfl
def unitRegionObservables (S : Set AmbientSpace) : Set (GaugeField (1 : ℝ) → ℂ) :=
  regionObservables 1 S
def closedHalfSpace (μ : Fin 4) : Set AmbientSpace := {x | 0 ≤ x μ}
theorem regionSigma_mono {a : ℝ} {S T : Set AmbientSpace} (h : S ⊆ T) :
    (regionSigma S : MeasurableSpace (GaugeField a)) ≤ regionSigma T :=
  biSup_mono fun _ he => ⟨h he.1, h he.2⟩
theorem IsBoundedObservable.add {a : ℝ} {f g : GaugeField a → ℂ} (hf : IsBoundedObservable f)
    (hg : IsBoundedObservable g) : IsBoundedObservable (f + g) := by
  obtain ⟨mf, C, hC⟩ := hf
  obtain ⟨mg, D, hD⟩ := hg
  exact ⟨mf.add mg, C + D, fun U => (norm_add_le _ _).trans (add_le_add (hC U) (hD U))⟩
theorem IsBoundedObservable.const_smul {a : ℝ} {f : GaugeField a → ℂ}
    (hf : IsBoundedObservable f) (c : ℂ) : IsBoundedObservable (c • f) := by
  obtain ⟨mf, C, hC⟩ := hf
  refine ⟨mf.const_smul c, ‖c‖ * C, fun U => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hC U) (norm_nonneg c)
theorem IsLocalObservable.add {a : ℝ} {f g : GaugeField a → ℂ} (hf : IsLocalObservable f)
    (hg : IsLocalObservable g) : IsLocalObservable (f + g) := by
  obtain ⟨S, bS, mS⟩ := hf
  obtain ⟨T, bT, mT⟩ := hg
  refine ⟨S ∪ T, bS.union bT, ?_⟩
  exact (mS.mono (regionSigma_mono Set.subset_union_left) le_rfl).add
    (mT.mono (regionSigma_mono Set.subset_union_right) le_rfl)
def halfSpaceLocalObservables (μ : Fin 4) : Submodule ℂ (GaugeField (1 : ℝ) → ℂ) where
  carrier := {f | f ∈ unitRegionObservables (closedHalfSpace μ) ∧ IsLocalObservable f}
  add_mem' := by
    rintro f g ⟨⟨of, mf⟩, lf⟩ ⟨⟨og, mg⟩, lg⟩
    exact ⟨⟨of.add og, Measurable.add mf mg⟩, lf.add lg⟩
  zero_mem' :=
    ⟨⟨⟨measurable_const, 0, fun _ => by simp⟩, measurable_const⟩,
      ∅, Bornology.isBounded_empty, measurable_const⟩
  smul_mem' := by
    rintro c f ⟨⟨of, mf⟩, S, bS, mS⟩
    exact ⟨⟨of.const_smul c, Measurable.const_smul mf c⟩, S, bS, Measurable.const_smul mS c⟩
theorem mem_halfSpaceLocalObservables_iff (μ : Fin 4) (f : GaugeField (1 : ℝ) → ℂ) :
    f ∈ halfSpaceLocalObservables μ ↔
      f ∈ unitRegionObservables (closedHalfSpace μ) ∧ IsLocalObservable f :=
  Iff.rfl
end YangMills.Construction.InfiniteLattice
