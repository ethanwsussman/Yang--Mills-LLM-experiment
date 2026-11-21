import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K n : ℕ}
namespace ComplexAverageLocality
theorem pathHolonomy_congr {j : ℤ} {W W' : Bond L m j → Matrices.ComplexMatrix2}
    {Γ : List (Bond L m j)} (h : ∀ b ∈ Γ, W b = W' b) :
    pathHolonomy W Γ = pathHolonomy W' Γ := by
  simp only [pathHolonomy, List.map_congr_left h]
end ComplexAverageLocality
open ComplexAverageLocality in
theorem complexAverageIsLocal_of_blockPaths (hP : BlockPaths.Statement) :
    ComplexAverageIsLocal := by
  intro L m K n hodd hL hm hn c hc
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨hy, hcμ⟩ := hP L m K hodd hL hm n hn
  obtain ⟨hD, -, -, hS, hPaths⟩ := hcμ c μ hμ
  obtain ⟨-, -, -, hI, htr, -⟩ := hD
  have hzero : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
    intro ν
    have h2 : 0 ≤ centreToFaceSteps L := by
      unfold centreToFaceSteps
      have : (13 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
      omega
    simpa using h2
  have hsrc : c.source.toSublattice (levelDepth K n) ∈ sitesInBlock (levelDepth K n) c.source := by
    have himg := (hy c.source).1.1.2
    have : ((offsetSite (c.source.toSublattice (levelDepth K n)) 0 :
        Site L m (levelDepth K n)) : FourTorus L m) ∈ unitBlock c.source := by
      rw [← himg]
      exact ⟨0, hzero, rfl⟩
    simpa [sitesInBlock, offsetSite] using this
  have htgt : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
    intro x hx
    rw [htr x hx, ← hI]
    exact ⟨x, hx, rfl⟩
  have hval : ∀ W W' : BondAtLevel L m K n → Matrices.ComplexMatrix2,
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), W b = W' b) →
      ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
        ∀ x ∈ sitesInBlock (levelDepth K n) y,
          contourHolonomies W y x = contourHolonomies W' y x := by
    intro W W' h y hy' x hx
    funext σ
    exact pathHolonomy_congr fun b hb => h b ((hPaths.1 y hy' x hx).1 _ ⟨σ, rfl⟩ b hb)
  have hcross : ∀ W W' : BondAtLevel L m K n → Matrices.ComplexMatrix2,
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), W b = W' b) →
      ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
        pathHolonomy W (crossingPath c x) = pathHolonomy W' (crossingPath c x) :=
    fun W W' h x hx => pathHolonomy_congr fun b hb => h b (hPaths.2 x hx b hb)
  have htransport : ∀ W W' : BondAtLevel L m K n → Matrices.ComplexMatrix2,
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), W b = W' b) →
      parallelTransport W c = parallelTransport W' c := by
    intro W W' h
    unfold parallelTransport
    rw [hS.2.1]
    exact hcross W W' h _ hsrc
  have helem : ∀ W W' : BondAtLevel L m K n → Matrices.ComplexMatrix2,
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), W b = W' b) →
      ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
        complexCrossingDefect W c x = complexCrossingDefect W' c x := by
    intro W W' h x hx
    unfold complexCrossingDefect complexMeanContourHolonomy
    rw [hval W W' h c.source (Or.inl rfl) x hx,
      hval W W' h c.target (Or.inr rfl) (shiftAcross c x) (htgt x hx), hcross W W' h x hx,
      htransport W W' h]
  have hmem : ∀ W W' : BondAtLevel L m K n → Matrices.ComplexMatrix2,
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), W b = W' b) →
      W ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)) →
        W' ∈ (complexAveragingDomainNearOne c :
          Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)) := by
    rintro W W' h ⟨⟨⟨hg, hr⟩, ht, hh⟩, hs⟩
    refine ⟨⟨⟨fun b hb => h b hb ▸ hg b hb, fun b hb => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩,
      fun x hx => ?_⟩
    · have hb' : b.opposite ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) :=
        ⟨hb.2, hb.1⟩
      rw [← h b hb, ← h _ hb']
      exact hr b hb
    · rw [← hval W W' h c.source (Or.inl rfl) x hx]
      exact ht x hx
    · rw [← hval W W' h c.target (Or.inr rfl) x hx]
      exact hh x hx
    · rw [← helem W W' h x hx]
      exact hs x hx
  refine ⟨fun W W' h => ⟨hmem W W' h, hmem W' W fun b hb => (h b hb).symm⟩, fun W W' h => ?_⟩
  unfold complexBlockAverageOnPositive
  rw [htransport W W' h, finsum_mem_congr rfl fun x hx => by rw [helem W W' h x hx]]
end PeriodicLattice
end YangMills.Construction
