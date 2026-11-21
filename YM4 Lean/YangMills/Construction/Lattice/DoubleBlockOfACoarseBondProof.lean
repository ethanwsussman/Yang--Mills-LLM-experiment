import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.CountsOfTheBondsOfDoubleBlocks
import YangMills.Construction.Lattice.DoubleBlockOfACoarseBond
import YangMills.Construction.Lattice.PivotOfBond
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Conventions
namespace PeriodicLattice.CoarseBondDoubleBlock
theorem statement_holds (hPart : BlockPartition.Properties)
    (hPiv : PivotOfEveryBond)
    (hDouble : DoubleBlockStructure.Statement)
    (hCounts : DoubleBlockBondCounts) :
    CoarseBondDoubleBlock.Statement := by
  intro L m K k c μ hc
  have hpos : c.IsPositivelyOriented := hc.isPositivelyOriented
  obtain ⟨hL, hK, hm, hk, -⟩ := hc
  have hj : -(m : ℤ) ≤ levelDepth K (k + 1) := by
    simp only [levelDepth]
    omega
  obtain ⟨-, hparts, -, -, -⟩ := hPart L m hL hm (levelDepth K (k + 1)) 1 0 hj
  have hself := hparts.1
  have hdisj := hparts.2.2.1
  have huniq : ∀ (y y' : SiteAtLevel L m K (k + 1)) (x : FourTorus L m),
      x ∈ unitBlock y → x ∈ unitBlock y' → y = y' := by
    intro y y' x hx hx'
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) hx hx'
  let s : StandingParameters := ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩
  have hpiv : ∀ c' : BondAtLevel L m K (k + 1), PivotProperties c' := fun c' => hPiv s k hk c'
  have hends : ∀ c' : BondAtLevel L m K (k + 1),
      ((pivot c' : BondAtLevel L m K k).source : FourTorus L m) ∈ unitBlock c'.source ∧
        ((pivot c' : BondAtLevel L m K k).target : FourTorus L m) ∈ unitBlock c'.target :=
    fun c' => (hpiv c').isPivot.1
  have hapart : ∀ c' : BondAtLevel L m K (k + 1), c'.source ≠ c'.target := by
    intro c' heq
    have hempty := (hDouble L m K k hL hm hk c').1.1
    have hmem : (c'.source : FourTorus L m) ∈ unitBlock c'.source ∩ unitBlock c'.target :=
      ⟨hself _, heq ▸ hself _⟩
    rw [hempty] at hmem
    exact hmem
  refine ⟨(hCounts L hL m K k hm hk).2.1 c hpos, ?_, ?_, ?_, ?_⟩
  · exact (hpiv c).isPositivelyOriented_iff.mpr hpos
  · exact ⟨Or.inl (hends c).1, Or.inr (hends c).2⟩
  · intro c' hc'
    have hwhere : ∀ x : FourTorus L m, ∀ y : SiteAtLevel L m K (k + 1), x ∈ unitBlock y →
        x ∈ bondDoubleBlock c → y = c.source ∨ y = c.target := by
      intro x y hy hx
      rcases hx with hx | hx
      · exact Or.inl (huniq _ _ x hy hx)
      · exact Or.inr (huniq _ _ x hy hx)
    have hs := hwhere _ _ (hends c').1 hc'.1
    have ht := hwhere _ _ (hends c').2 hc'.2
    have hne := hapart c'
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact absurd (hs.trans ht.symm) hne
    · exact Or.inl (Bond.ext hs ht)
    · exact Or.inr (Bond.ext hs ht)
    · exact absurd (hs.trans ht.symm) hne
  · intro b y hsrc htgt c' hb
    subst hb
    exact hapart c' ((huniq _ _ _ (hends c').1 hsrc).trans
      (huniq _ _ _ (hends c').2 htgt).symm)
end PeriodicLattice.CoarseBondDoubleBlock
end YangMills.Construction
