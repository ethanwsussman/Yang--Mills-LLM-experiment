import YangMills.Construction.HoleBesideASecondHole.HolesAtGrowingScales
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace Holes
open Classical in
def LinkComponentProperties : Prop :=
  ∀ (F : BlockFrame) (h : Finset (Finset (F.Site F.depth))),
    (∀ (r : ℕ) (l : Finset (F.Site F.depth)), l ∈ h → l ∈ linkComponent r h l) ∧
    (∀ (r : ℕ) (l l' : Finset (F.Site F.depth)), l' ∈ linkComponent r h l →
      linkComponent r h l' = linkComponent r h l) ∧
    (∀ (r r' : ℕ) (l : Finset (F.Site F.depth)), r ≤ r' → linkComponent r h l ⊆ linkComponent r' h l) ∧
    (∀ (r r' : ℕ) (k : Finset (Finset (F.Site F.depth))), r ≤ r' → k ∈ linkComponents r' h →
      componentsWithin r h k = k.image (linkComponent r h)) ∧
    ∀ (J₀ I : ℕ) (k : Finset (Finset (F.Site F.depth))), 1 ≤ J₀ → k ∈ linkComponents (holeScale J₀ I) h →
      I + 1 ≤ ((Finset.range I).filter (IsStableIndex J₀ h k)).card + k.card
end Holes
end YangMills.Construction
end
