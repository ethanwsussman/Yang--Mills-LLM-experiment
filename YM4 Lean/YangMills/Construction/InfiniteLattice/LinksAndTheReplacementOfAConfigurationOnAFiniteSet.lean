import YangMills.Construction.InfiniteLattice.KernelsOfFiniteSetsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set
open GibbsAtFixedSpacing
namespace InfiniteLattice
variable {a : ℝ}
private def coordTotal (x : LatticePoint a) : ℝ := ∑ μ, (x : AmbientSpace) μ
private theorem coordTotal_add (x y : LatticePoint a) :
    coordTotal (x + y) = coordTotal x + coordTotal y := by
  simp [coordTotal, Finset.sum_add_distrib]
private theorem coordTotal_axisStep (μ : Fin 4) : coordTotal (axisStep a μ) = a := by
  simp [coordTotal, axisStep]
theorem mem_edgesOf_iff_mem_edges (ha : 0 < a) (p : ElementaryPlaquette a) (b : Link a) :
    b ∈ edgesOf p ↔ b ∈ p.edges := by
  constructor
  · rintro ⟨hb, hi, ht⟩
    obtain ⟨κ, hκ⟩ := mem_positiveLinks_iff.mp hb
    have hs : coordTotal b.terminal = coordTotal b.initial + a := by
      rw [show b.terminal = b.initial + axisStep a κ by rw [← hκ]; abel, coordTotal_add,
        coordTotal_axisStep]
    simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff] at hi ht
    simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false]
    rcases hi with hi | hi | hi | hi <;> rcases ht with ht | ht | ht | ht <;>
      rw [hi, ht] at hs <;>
      (try simp only [coordTotal_add, coordTotal_axisStep] at hs)
    all_goals first
      | (exfalso; linarith)
      | exact Or.inl (Link.ext hi ht)
      | exact Or.inr (Or.inl (Link.ext hi ht))
      | exact Or.inr (Or.inr (Or.inl (Link.ext hi (ht.trans (add_right_comm _ _ _)))))
      | exact Or.inr (Or.inr (Or.inr (Link.ext hi ht)))
  · intro hb
    simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;>
      refine ⟨⟨_, _, rfl⟩, ?_, ?_⟩ <;>
      simp [ElementaryPlaquette.cornerSet, Link.forwardFrom, add_right_comm]
theorem mem_plaquettesTouching_iff (ha : 0 < a) (L : Finset (Link a)) (p : ElementaryPlaquette a) :
    p ∈ plaquettesTouching L ↔ ∃ b ∈ p.edges, b ∈ L ∨ b.opposite ∈ L := by
  simp only [plaquettesTouching, mem_ofPred_eq, mem_edgesOf_iff_mem_edges ha]
section Overwrite
variable {S : Set (Link a)} (h : HasNoOppositePairs S) (V : LinkVariables S)
  (U : GaugeField a)
theorem overwriteLinks_apply_of_mem (b : S) : overwriteLinks h V U b = V b :=
  dif_pos b.2
theorem overwriteLinks_apply_opposite (b : S) :
    overwriteLinks h V U (b : Link a).opposite = (V b)⁻¹ := by
  have h₁ : (overwriteLinks h V U) (b : Link a).opposite = (overwriteLinks h V U b)⁻¹ :=
    (overwriteLinks h V U).2 b
  rw [h₁, overwriteLinks_apply_of_mem]
theorem overwriteLinks_apply_of_not_mem {b : Link a} (hb : b ∉ S) (hr : b.opposite ∉ S) :
    overwriteLinks h V U b = U b :=
  (dif_neg hb).trans (dif_neg hr)
end Overwrite
def complementLinks (L : Finset (Link a)) : Set (Link a) :=
  positiveLinkSet a \ (L : Set (Link a))
abbrev ComplementVariables (L : Finset (Link a)) : Type := LinkVariables (complementLinks L)
def complementValues (L : Finset (Link a)) (U : GaugeField a) : ComplementVariables L :=
  restrictField U (complementLinks L)
@[reducible] def complementSigma (L : Finset (Link a)) : MeasurableSpace (GaugeField a) :=
  linkSigma (complementLinks L)
end InfiniteLattice
end YangMills.Construction
