import YangMills.Construction.InfiniteLattice.LatticeOfACutoffAndTheVariablesOfASetOfBonds
import YangMills.Construction.InfiniteLattice.PlaquettesOfTheLatticeOfACutoff
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.CutoffLinks
open YangMills.Construction.InfiniteLattice
namespace CutoffData
structure CutoffWindow (d : CutoffData) where
  links : Set (Link d.spacing)
  finite : links.Finite
  subset_links : links ⊆ d.links
namespace CutoffWindow
variable {d : CutoffData} (W : d.CutoffWindow)
def faces : Set (ElementaryPlaquette d.spacing) := {p | ∃ b ∈ W.links, ContainsLink p b}
def faceCount : ℕ := W.faces.ncard
def rim : Set (Link d.spacing) := {b | (∃ p ∈ W.faces, ContainsLink p b) ∧ b ∉ W.links}
theorem rim_subset_links : W.rim ⊆ d.links := by
  rintro b ⟨⟨p, -, hb⟩, -⟩
  simp only [ContainsLink, ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
end CutoffWindow
end CutoffData
end YangMills.Construction.CutoffLinks
