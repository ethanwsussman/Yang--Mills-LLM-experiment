import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.CountsOfTheBondsOfDoubleBlocks
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.DoubleBlockBondCounts
theorem doubleBlockBondCounts_holds (hPart : BlockPartition.Properties) :
    PeriodicLattice.DoubleBlockBondCounts := by
  intro L hL m K n hm hn
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hdepth : -(m : ℤ) ≤ levelDepth K (n + 1) := by
    simp only [levelDepth]
    omega
  obtain ⟨hpts, hpart, -, -, -⟩ := hPart L m hL hm (levelDepth K (n + 1)) 1 0 hdepth
  have hdisj := hpart.2.2.1
  refine ⟨SeparatedSequences.BaseParameters.site_finite hLpos m _, ?_, ?_⟩
  · intro c _
    have hblk : ∀ y : SiteAtLevel L m K (n + 1),
        ({x : SiteAtLevel L m K n | (x : FourTorus L m) ∈ unitBlock y}).encard ≤ ((L ^ 4 : ℕ) : ℕ∞) := by
      intro y
      have hcard : (unitBlock y).ncard = L ^ 4 := by
        simpa using (hpts y).2.2
      have hfin : (unitBlock y).Finite :=
        Set.finite_of_ncard_pos (by rw [hcard]; positivity)
      calc ({x : SiteAtLevel L m K n | (x : FourTorus L m) ∈ unitBlock y}).encard
          ≤ (unitBlock y).encard :=
            Set.encard_le_encard_of_injOn (f := Subtype.val) (fun x hx => hx)
              Subtype.val_injective.injOn
        _ = ((L ^ 4 : ℕ) : ℕ∞) := by rw [← hfin.cast_ncard_eq, hcard]
    set S : Set (SiteAtLevel L m K n) := {x | (x : FourTorus L m) ∈ bondDoubleBlock c} with hS
    have hScard : S.encard ≤ ((L ^ 4 : ℕ) : ℕ∞) + ((L ^ 4 : ℕ) : ℕ∞) := by
      have hunion : S = {x : SiteAtLevel L m K n | (x : FourTorus L m) ∈ unitBlock c.source} ∪
          {x : SiteAtLevel L m K n | (x : FourTorus L m) ∈ unitBlock c.target} := rfl
      rw [hunion]
      exact (Set.encard_union_le _ _).trans (add_le_add (hblk _) (hblk _))
    have hsub : {b : BondAtLevel L m K n | b ∈ (doubleBlockSymmetricSet c).bonds ∧ b.IsPositivelyOriented} ⊆
        (fun p : SiteAtLevel L m K n × Fin 4 => Bond.forwardFrom p.1 p.2) '' (S ×ˢ (univ : Set (Fin 4))) := by
      rintro b ⟨hb, μ, hμ⟩
      refine ⟨(b.source, μ), ⟨hb.1, mem_univ _⟩, ?_⟩
      apply Bond.ext
      · rfl
      · change b.source + unitStep L m (levelDepth K n) μ = b.target
        rw [← hμ]
        abel
    calc {b : BondAtLevel L m K n | b ∈ (doubleBlockSymmetricSet c).bonds ∧ b.IsPositivelyOriented}.encard
        ≤ ((fun p : SiteAtLevel L m K n × Fin 4 => Bond.forwardFrom p.1 p.2) ''
            (S ×ˢ (univ : Set (Fin 4)))).encard := Set.encard_le_encard hsub
      _ ≤ (S ×ˢ (univ : Set (Fin 4))).encard := Set.encard_image_le _ _
      _ = S.encard * (univ : Set (Fin 4)).encard := Set.encard_prod
      _ ≤ (((L ^ 4 : ℕ) : ℕ∞) + ((L ^ 4 : ℕ) : ℕ∞)) * 4 := by
            have : (univ : Set (Fin 4)).encard = 4 := by simp [Set.encard_univ]
            rw [this]
            gcongr
      _ = ((8 * L ^ 4 : ℕ) : ℕ∞) := by
            push_cast
            ring
  · intro b
    by_cases hex : ∃ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented ∧ b ∈ (doubleBlockSymmetricSet c).bonds
    · obtain ⟨c₀, -, hb₀⟩ := hex
      obtain ⟨y, hy⟩ : ∃ y : SiteAtLevel L m K (n + 1), (b.source : FourTorus L m) ∈ unitBlock y := by
        rcases hb₀.1 with h | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      have huniq : ∀ y' : SiteAtLevel L m K (n + 1), (b.source : FourTorus L m) ∈ unitBlock y' → y' = y := by
        intro y' hy'
        by_contra hne
        exact Set.disjoint_left.mp (hdisj hne) hy' hy
      have hsub : {c : BondAtLevel L m K (n + 1) | c.IsPositivelyOriented ∧ b ∈ (doubleBlockSymmetricSet c).bonds} ⊆
          (fun p : Fin 4 × Bool =>
            if p.2 then Bond.forwardFrom y p.1
            else Bond.forwardFrom (y - unitStep L m (levelDepth K (n + 1)) p.1) p.1) ''
            (univ : Set (Fin 4 × Bool)) := by
        rintro c ⟨⟨μ, hμ⟩, hb⟩
        rcases hb.1 with h | h
        · have hsrc : c.source = y := huniq _ h
          refine ⟨(μ, true), mem_univ _, ?_⟩
          apply Bond.ext
          · exact hsrc.symm
          · change y + unitStep L m (levelDepth K (n + 1)) μ = c.target
            rw [← hsrc, ← hμ]
            abel
        · have htgt : c.target = y := huniq _ h
          refine ⟨(μ, false), mem_univ _, ?_⟩
          apply Bond.ext
          · change y - unitStep L m (levelDepth K (n + 1)) μ = c.source
            rw [← htgt, ← hμ]
            abel
          · change y - unitStep L m (levelDepth K (n + 1)) μ + unitStep L m (levelDepth K (n + 1)) μ = c.target
            rw [htgt]
            abel
      calc {c : BondAtLevel L m K (n + 1) | c.IsPositivelyOriented ∧ b ∈ (doubleBlockSymmetricSet c).bonds}.encard
          ≤ _ := Set.encard_le_encard hsub
        _ ≤ (univ : Set (Fin 4 × Bool)).encard := Set.encard_image_le _ _
        _ = 8 := by simp [Set.encard_univ]
    · have hemp :
          {c : BondAtLevel L m K (n + 1) | c.IsPositivelyOriented ∧ b ∈ (doubleBlockSymmetricSet c).bonds} = ∅ :=
        Set.eq_empty_of_forall_notMem fun c hc => hex ⟨c, hc⟩
      rw [hemp]
      simp
end YangMills.Construction.PeriodicLattice.DoubleBlockBondCounts
end
