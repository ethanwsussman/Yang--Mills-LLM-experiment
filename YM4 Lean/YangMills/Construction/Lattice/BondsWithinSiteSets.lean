import YangMills.Construction.Lattice.GaugeConfigurations
import YangMills.Construction.Lattice.LieFieldsOnBondSets
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ} {j : ℤ}
def Bond.LiesIn (b : Bond L m j) (Z : Set (Site L m j)) : Prop := b.source ∈ Z ∧ b.target ∈ Z
def Plaquette.LiesIn (p : Plaquette L m j) (Z : Set (Site L m j)) : Prop := p.vertices ⊆ Z
theorem Plaquette.LiesIn.boundaryBonds_liesIn {p : Plaquette L m j} {Z : Set (Site L m j)}
    (h : p.LiesIn Z) : ∀ b ∈ p.boundaryBonds, b.LiesIn Z := by
  have h₀ : p.origin ∈ Z := h (by simp [Plaquette.vertices])
  have h₁ : p.origin + unitStep L m j p.firstAxis ∈ Z := h (by simp [Plaquette.vertices])
  have h₂ : p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis ∈ Z :=
    h (by simp [Plaquette.vertices])
  have h₃ : p.origin + unitStep L m j p.secondAxis ∈ Z := h (by simp [Plaquette.vertices])
  intro b hb
  simp only [Plaquette.boundaryBonds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨h₀, h₁⟩
  · exact ⟨h₁, h₂⟩
  · refine ⟨?_, h₃⟩
    change p.origin + unitStep L m j p.secondAxis + unitStep L m j p.firstAxis ∈ Z
    rwa [add_right_comm]
  · exact ⟨h₃, h₀⟩
variable {K i : ℕ}
def bondsWithin (Z : Set (SiteAtLevel L m K i)) : SymmetricBondSet L m K i where
  bonds := {b | b.LiesIn Z}
  opposite_mem := fun _ hb => ⟨hb.2, hb.1⟩
abbrev IsGaugeFieldWithin (Z : Set (SiteAtLevel L m K i))
    (W : BondAtLevel L m K i → ComplexMatrix2) : Prop :=
  IsGaugeField compactGaugeGroup (bondsWithin Z).bonds W
abbrev LieBondFieldWithin (Z : Set (SiteAtLevel L m K i)) : Type := LieBondField (bondsWithin Z)
def maxPlaquetteDeviation (Z : Set (SiteAtLevel L m K i))
    (W : BondAtLevel L m K i → ComplexMatrix2) : ℝ :=
  sSup ((fun p : PlaquetteAtLevel L m K i =>
    ComplexMatrix2.operatorNorm (plaquetteHolonomy W p - 1)) '' {p | p.LiesIn Z})
theorem maxPlaquetteDeviation_congr {Z : Set (SiteAtLevel L m K i)}
    {W W' : BondAtLevel L m K i → ComplexMatrix2}
    (h : ∀ b ∈ (bondsWithin Z).bonds, W b = W' b) :
    maxPlaquetteDeviation Z W = maxPlaquetteDeviation Z W' := by
  refine congrArg sSup (Set.image_congr fun p hp => ?_)
  have hb : p.boundaryBonds.map W = p.boundaryBonds.map W' :=
    List.map_congr_left fun b hb => h b (Plaquette.LiesIn.boundaryBonds_liesIn hp b hb)
  simp only [plaquetteHolonomy, pathHolonomy, hb]
theorem conjugateBy_mem_traceless (V : ComplexMatrix2) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V A ∈ ComplexMatrix2.traceless := by
  have h : ComplexMatrix2.fullTrace A = 0 := hA
  change ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy V A) = 0
  by_cases hV : IsUnit V.det
  · rw [ComplexMatrix2.fullTrace, ComplexMatrix2.conjugateBy, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hV, Matrix.one_mul]
    exact h
  · simp [ComplexMatrix2.fullTrace, ComplexMatrix2.conjugateBy,
      Matrix.nonsing_inv_apply_not_isUnit _ hV]
end YangMills.Construction.PeriodicLattice
