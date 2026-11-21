import YangMills.Construction.CellOfTheFlow.TheLowerWindowLiesInTheHull
import YangMills.Construction.SixteenPointsOnASmallTorus.SizeOfACopyProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings WeightedResponses
private theorem supDist_comm {n : ℕ} (x y : TorusSite n) : supDist x y = supDist y x := by apply _root_.YangMills.SharedProofs.p9265 <;> assumption
private theorem chainConnected_swap {n r : ℕ} {Y : Finset (TorusSite n)} {a b : TorusSite n}
    (h : ChainConnected r Y a b) : ChainConnected r Y b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    exact Relation.ReflTransGen.head ⟨hs.2.1, hs.1, by rw [supDist_comm]; exact hs.2.2⟩ ih
private theorem chainConnected_mono {n r : ℕ} {Y Y' : Finset (TorusSite n)} (hY : Y ⊆ Y')
    {a b : TorusSite n} (h : ChainConnected r Y a b) : ChainConnected r Y' a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail ⟨hY hs.1, hY hs.2.1, hs.2.2⟩
private theorem thickening_mono {n : ℕ} [NeZero n] (m : ℕ) {X X' : Finset (TorusSite n)} (h : X ⊆ X') :
    thickening m X ⊆ thickening m X' := by
  intro z hz
  simp only [thickening, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  obtain ⟨x, hx, hd⟩ := hz
  exact ⟨x, h hx, hd⟩
private theorem coreBlocks_mono {n L : ℕ} [NeZero n] [NeZero L] (r : ℕ)
    {θ θ' : Finset (TorusSite (n * L))} (h : θ ⊆ θ') : coreBlocks L r θ ⊆ coreBlocks L r θ' := by
  intro y hy
  simp only [coreBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  obtain ⟨z, hz⟩ := hy
  obtain ⟨h₁, h₂⟩ := Finset.mem_inter.1 hz
  exact ⟨z, Finset.mem_inter.2 ⟨h₁, thickening_mono _ h h₂⟩⟩
abbrev _root_.YangMills.SharedProofs.p23923 := @coreBlocks_mono
open Classical in
private theorem meeting_components_mono {n : ℕ} [NeZero n] (ρ : ℕ) {X X' A : Finset (TorusSite n)}
    (h : X ⊆ X') :
    ((chainComponents ρ X).filter fun K => (K ∩ A).Nonempty).biUnion id ⊆
      ((chainComponents ρ X').filter fun K => (K ∩ A).Nonempty).biUnion id := by
  intro x hx
  simp only [Finset.mem_biUnion, Finset.mem_filter, id] at hx ⊢
  obtain ⟨K, ⟨hK, z, hz⟩, hxK⟩ := hx
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hK
  obtain ⟨hzK, hzA⟩ := Finset.mem_inter.1 hz
  obtain ⟨hzX, hyz⟩ := Finset.mem_filter.1 hzK
  obtain ⟨hxX, hyx⟩ := Finset.mem_filter.1 hxK
  refine ⟨X'.filter (ChainConnected ρ X' x), ⟨Finset.mem_image.2 ⟨x, h hxX, rfl⟩, z, ?_⟩, ?_⟩
  · exact Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨h hzX,
      chainConnected_mono h ((chainConnected_swap hyx).trans hyz)⟩, hzA⟩
  · exact Finset.mem_filter.2 ⟨h hxX, Relation.ReflTransGen.refl⟩
private theorem lowerZone_subset_storedBlocks {ℓ : StepParameters} (T : StageTower ℓ) (k s : ℕ) {m : ℕ}
    [NeZero m] (C : Finset (TorusSite m)) (bad : Finset (TorusBond (m * ℓ.side)))
    {Ym Y : Finset (TorusSite (m * ℓ.side))} (c : Finset (TorusSite m)) (h : Ym ⊆ Y) :
    lowerZone T k s C bad Ym c ⊆ storedBlocks ℓ.side (T.stage s).toStepSetup.range bad Y C := by
  classical
  have hX : windowSeeds ℓ.side bad Ym C (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c)) ⊆
      bad.image Prod.fst ∪ Y ∪ sitesInBlocks ℓ.side C := by
    intro x hx
    have hx' := (Finset.mem_inter.1 hx).1
    simp only [Finset.mem_union] at hx' ⊢
    rcases hx' with (hx' | hx') | hx'
    · exact Or.inl (Or.inl hx')
    · exact Or.inl (Or.inr (h hx'))
    · exact Or.inr hx'
  intro y hy
  have hy' := (Finset.mem_inter.1 hy).1
  refine Finset.mem_union.2 ((Finset.mem_union.1 hy').imp id fun hc => ?_)
  exact coreBlocks_mono _ (meeting_components_mono _ hX) hc
private theorem lowerHull_subset_stageHull {ℓ : StepParameters} (T : StageTower ℓ) (k : ℕ) :
    ∀ (s m : ℕ) [NeZero m] (u : MarkedSample ℓ s m) (c : Finset (TorusSite m)),
      lowerHull T k s m u c ⊆ stageHull T s m u := by
  intro s
  induction s with
  | zero =>
    intro m _ u c
    exact Finset.inter_subset_left
  | succ s ih =>
    intro m _ u c
    exact thickening_mono _
      (lowerZone_subset_storedBlocks T k s _ _ c (ih (m * ℓ.side) u.1 (sitesInBlocks ℓ.side c)))
theorem lowerHullSubsetStageHull : lowerHullSubsetStageHullStatement := by
  intro ℓ T k
  exact ⟨fun s m _ u c => lowerHull_subset_stageHull T k s m u c, fun s m _ u c =>
    lowerZone_subset_storedBlocks T k s _ _ c
      (lowerHull_subset_stageHull T k s (m * ℓ.side) u.1 (sitesInBlocks ℓ.side c))⟩
end YangMills.Construction.CellWindows
end
