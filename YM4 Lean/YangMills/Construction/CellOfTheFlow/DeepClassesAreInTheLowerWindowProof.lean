import YangMills.Construction.CellOfTheFlow.ACellIsRareProof
import YangMills.Construction.CellOfTheFlow.DeepClassesAreInTheLowerWindow
import YangMills.Construction.CellOfTheFlow.TheLowerWindowLiesInTheHull
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAFamily
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps TorusBalls StepSettings WeightedResponses BlockPlaces ClusterExpansionOfAStep
section Geometry
private theorem interiorAtDepth_anti {N : ℕ} [NeZero N] {a b : ℕ} (h : a ≤ b) (c : Finset (TorusSite N)) :
    interiorAtDepth b c ⊆ interiorAtDepth a c := by apply _root_.YangMills.SharedProofs.p56231 <;> assumption
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem mem_interior_of_parentBlock_mem {D : ℕ} {c : Finset (TorusSite n)} {w : TorusSite (n * L)}
    (hw : parentBlock L w ∈ interiorAtDepth D c) :
    w ∈ interiorAtDepth (L * (D - 1)) (sitesInBlocks L c) := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hw
  refine Finset.mem_filter.mpr ⟨mem_sitesInBlocks.mpr h1, fun v hv => ?_⟩
  have hv' : parentBlock L v ∉ c := fun h => hv (mem_sitesInBlocks.mpr h)
  have h3 := (h2 _ hv').trans (supDist_parentBlock_le_div_add_one L w v)
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have h4 : D - 1 ≤ supDist w v / L := by
    generalize supDist w v / L = q at h3
    omega
  rw [mul_comm]
  exact (Nat.le_div_iff_mul_le hL).mp h4
private theorem sum_blockOffset_eq_sum_sitesInBlocks {M : Type} [AddCommMonoid M] (y : TorusSite n)
    (f : TorusSite (n * L) → M) :
    ∑ o : BlockOffset L, f (blockSite y o) = ∑ z ∈ sitesInBlocks L {y}, f z := by
  classical
  refine Finset.sum_bij' (fun o _ => blockSite y o) (fun z _ => siteOffset z) ?_ ?_ ?_ ?_ ?_
  · intro o _
    exact mem_sitesInBlocks.mpr (by simp [parentBlock_blockSite])
  · intro z _
    exact Finset.mem_univ _
  · intro o _
    exact FamilyZones.siteOffset_blockSite y o
  · intro z hz
    have hb : parentBlock L z = y := by simpa using mem_sitesInBlocks.mp hz
    show blockSite y (siteOffset z) = z
    rw [← hb]
    exact BlockZones.blockSite_parentBlock_siteOffset z
  · intro o _
    rfl
variable {r r' : ℕ} {bad : Finset (TorusBond (n * L))} {Yt Ym : Finset (TorusSite (n * L))}
  {C X : Finset (TorusSite n)}
private theorem mem_coarseHull_of_mem_storedBlocks {z : TorusSite n} (hz : z ∈ storedBlocks L r bad Yt C) :
    z ∈ coarseHull L r r' bad Yt C :=
  (mem_thickening _ _ _).mpr ⟨z, hz, by simp [supDist_self]⟩
private theorem parentBlock_mem_storedBlocks_of_attached {u : TorusSite (n * L)}
    (hu : u ∈ attachedSites L r bad Yt C) :
    parentBlock L u ∈ storedBlocks L r bad Yt C := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.parentBlock_mem_storedBlocks <;> assumption
private theorem mem_component_of_supDist_le (hX : X ∈ chainComponents r' (coarseHull L r r' bad Yt C))
    {a b : TorusSite n} (ha : a ∈ X) (hb : b ∈ coarseHull L r r' bad Yt C) (h : supDist a b ≤ r') : b ∈ X :=
  mem_of_chainConnected_of_mem_chainComponents hX ha hb
    (chainConnected_of_supDist_le (subset_of_mem_chainComponents hX ha) hb h)
private theorem parentBlock_mem_of_attached_component (hc : 10 * r / L + 1 ≤ r')
    (hX : X ∈ chainComponents r' (coarseHull L r r' bad Yt C))
    {θ : Finset (TorusSite (n * L))} (hθ : θ ∈ chainComponents (10 * r) (clusterSites (L := L) bad Yt C))
    (hatt : (θ ∩ sitesInBlocks L C).Nonempty) {w₀ : TorusSite (n * L)} (hw₀ : w₀ ∈ θ)
    (hb : parentBlock L w₀ ∈ X) :
    ∀ w ∈ θ, parentBlock L w ∈ X := by
  have key : ∀ v, ChainConnected (10 * r) (clusterSites (L := L) bad Yt C) w₀ v →
      v ∈ θ ∧ parentBlock L v ∈ X := by
    intro v hv
    induction hv with
    | refl => exact ⟨hw₀, hb⟩
    | @tail a v _ hs ih =>
      have hvθ : v ∈ θ := mem_of_chainConnected_of_mem_chainComponents hθ ih.1 hs.2.1
        (chainConnected_of_supDist_le hs.1 hs.2.1 hs.2.2)
      refine ⟨hvθ, mem_component_of_supDist_le hX ih.2
        (mem_coarseHull_of_mem_storedBlocks (parentBlock_mem_storedBlocks_of_attached
          ((mem_attachedSites_iff r bad Yt C).mpr ⟨θ, hθ, hvθ, hatt⟩))) ?_⟩
      have h1 := supDist_parentBlock_le_div_add_one L a v
      have h2 : supDist a v / L ≤ 10 * r / L := Nat.div_le_div_right hs.2.2
      omega
  exact fun w hw => (key w (chainConnected_of_mem_chainComponents hθ hw₀ hw)).2
private theorem exists_component_of_mem_coreBlocks (hc : 10 * r / L + 1 ≤ r')
    (hX : X ∈ chainComponents r' (coarseHull L r r' bad Yt C))
    {y : TorusSite n} (hyX : y ∈ X) (hy : y ∈ coreBlocks L r (attachedSites L r bad Yt C)) :
    ∃ θ ∈ chainComponents (10 * r) (clusterSites (L := L) bad Yt C), (θ ∩ sitesInBlocks L C).Nonempty ∧
      (∀ w ∈ θ, parentBlock L w ∈ X) ∧ ∃ u ∈ θ, ∃ p, parentBlock L p = y ∧ supDist p u ≤ 4 * r := by
  classical
  obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hy).2
  obtain ⟨hp1, hp2⟩ := Finset.mem_inter.mp hp
  have hpy : parentBlock L p = y := by simpa using mem_sitesInBlocks.mp hp1
  obtain ⟨u, hu, hpu⟩ := (mem_thickening _ _ _).mp hp2
  obtain ⟨θ, hθ, huθ, hatt⟩ := (mem_attachedSites_iff r bad Yt C).mp hu
  have hbu : parentBlock L u ∈ X := by
    refine mem_component_of_supDist_le hX hyX
      (mem_coarseHull_of_mem_storedBlocks (parentBlock_mem_storedBlocks_of_attached hu)) ?_
    rw [← hpy]
    have h1 := supDist_parentBlock_le_div_add_one L p u
    have h2 : supDist p u / L ≤ 10 * r / L := Nat.div_le_div_right (by omega)
    omega
  exact ⟨θ, hθ, hatt, parentBlock_mem_of_attached_component hc hX hθ hatt huθ hbu, u, huθ, p, hpy, hpu⟩
private theorem exists_component_of_mem_clusterSites (hc : 10 * r / L + 1 ≤ r') (hL : L + 4 * r ≤ 10 * r)
    (hX : X ∈ chainComponents r' (coarseHull L r r' bad Yt C)) {y : TorusSite n} (hyX : y ∈ X)
    (hyZ : y ∈ storedBlocks L r bad Yt C) {z : TorusSite (n * L)} (hzb : parentBlock L z = y)
    (hzS : z ∈ clusterSites (L := L) bad Yt C) :
    ∃ θ ∈ chainComponents (10 * r) (clusterSites (L := L) bad Yt C), (θ ∩ sitesInBlocks L C).Nonempty ∧
      (∀ w ∈ θ, parentBlock L w ∈ X) ∧ z ∈ θ := by
  classical
  rcases Finset.mem_union.mp hyZ with hC | hcore
  · obtain ⟨θ, hθ, hz⟩ := exists_mem_chainComponents (r := 10 * r) hzS
    have hzC : z ∈ sitesInBlocks L C := mem_sitesInBlocks.mpr (hzb ▸ hC)
    have hatt : (θ ∩ sitesInBlocks L C).Nonempty := ⟨z, Finset.mem_inter.mpr ⟨hz, hzC⟩⟩
    exact ⟨θ, hθ, hatt, parentBlock_mem_of_attached_component hc hX hθ hatt hz (hzb ▸ hyX), hz⟩
  · obtain ⟨θ, hθ, hatt, hb, u, hu, p, hp, hpu⟩ := exists_component_of_mem_coreBlocks hc hX hyX hcore
    have h1 : supDist z p ≤ L := supDist_le_of_parentBlock_eq (hzb.trans hp.symm)
    have h2 : supDist u z ≤ 10 * r := by
      rw [supDist_comm]
      have := supDist_triangle z p u
      omega
    exact ⟨θ, hθ, hatt, hb, mem_of_chainConnected_of_mem_chainComponents hθ hu hzS
      (chainConnected_of_supDist_le (subset_of_mem_chainComponents hθ hu) hzS h2)⟩
private theorem component_subset_of_meets {θ : Finset (TorusSite (n * L))}
    (hθ : θ ∈ chainComponents (10 * r) (clusterSites (L := L) bad Yt C)) {w : TorusSite (n * L)} (hw : w ∈ θ)
    {K : Finset (TorusSite (n * L))} (hK : K ∈ chainComponents r Yt) (hwK : w ∈ K) : K ⊆ θ := by
  classical
  have hup : ∀ a, a ∈ Yt → a ∈ clusterSites (L := L) bad Yt C := fun a ha =>
    Finset.mem_union_left _ (Finset.mem_union_right _ ha)
  intro v hv
  have key : ∀ v, ChainConnected r Yt w v → ChainConnected (10 * r) (clusterSites (L := L) bad Yt C) w v := by
    intro v hv
    induction hv with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.tail ⟨hup _ hs.1, hup _ hs.2.1, by have := hs.2.2; omega⟩
  exact mem_of_chainConnected_of_mem_chainComponents hθ hw (hup _ (subset_of_mem_chainComponents hK hv))
    (key v (chainConnected_of_mem_chainComponents hK hwK hv))
private theorem subset_lowerAttached {c : Finset (TorusSite n)} {ρ D : ℕ} (hXd : X ⊆ interiorAtDepth D c)
    (hρ : ρ ≤ D)
    (hYm : ∀ K ∈ chainComponents r Yt, K ⊆ interiorAtDepth (L * (D - 1)) (sitesInBlocks L c) → K ⊆ Ym)
    {θ : Finset (TorusSite (n * L))} (hθ : θ ∈ chainComponents (10 * r) (clusterSites (L := L) bad Yt C))
    (hatt : (θ ∩ sitesInBlocks L C).Nonempty) (hb : ∀ w ∈ θ, parentBlock L w ∈ X) :
    θ ⊆ lowerAttached L r (windowSeeds L bad Ym C (sitesInBlocks L (interiorAtDepth ρ c)))
      (sitesInBlocks L C) := by
  classical
  have hsub : θ ⊆ windowSeeds L bad Ym C (sitesInBlocks L (interiorAtDepth ρ c)) := by
    intro w hw
    have hwS := subset_of_mem_chainComponents hθ hw
    refine Finset.mem_inter.mpr ⟨?_, mem_sitesInBlocks.mpr (interiorAtDepth_anti hρ c (hXd (hb w hw)))⟩
    simp only [Finset.mem_union] at hwS ⊢
    rcases hwS with (h1 | h2) | h3
    · exact Or.inl (Or.inl h1)
    · obtain ⟨K, hK, hwK⟩ := exists_mem_chainComponents (r := r) h2
      refine Or.inl (Or.inr (hYm K hK (fun v hv => ?_) hwK))
      exact mem_interior_of_parentBlock_mem (hXd (hb v (component_subset_of_meets hθ hw hK hwK hv)))
    · exact Or.inr h3
  obtain ⟨x₀, hx₀⟩ := hatt
  obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx₀
  obtain ⟨K, hK, hxK⟩ := exists_mem_chainComponents (r := 10 * r) (hsub hx₁)
  have key : ∀ v, ChainConnected (10 * r) (clusterSites (L := L) bad Yt C) x₀ v →
      v ∈ θ ∧ ChainConnected (10 * r) (windowSeeds L bad Ym C (sitesInBlocks L (interiorAtDepth ρ c))) x₀ v := by
    intro v hv
    induction hv with
    | refl => exact ⟨hx₁, Relation.ReflTransGen.refl⟩
    | @tail a v _ hs ih =>
      have hvθ : v ∈ θ := mem_of_chainConnected_of_mem_chainComponents hθ ih.1 hs.2.1
        (chainConnected_of_supDist_le hs.1 hs.2.1 hs.2.2)
      exact ⟨hvθ, ih.2.tail ⟨hsub ih.1, hsub hvθ, hs.2.2⟩⟩
  intro w hw
  simp only [lowerAttached, Finset.mem_biUnion, Finset.mem_filter, id]
  exact ⟨K, ⟨hK, ⟨x₀, Finset.mem_inter.mpr ⟨hxK, hx₂⟩⟩⟩,
    mem_of_chainConnected_of_mem_chainComponents hK hxK (hsub hw)
      (key w (chainConnected_of_mem_chainComponents hθ hx₁ hw)).2⟩
private theorem mem_lowerZone_of_deep {c : Finset (TorusSite n)} {ρ D : ℕ} (hc : 10 * r / L + 1 ≤ r')
    (hX : X ∈ chainComponents r' (coarseHull L r r' bad Yt C)) (hXd : X ⊆ interiorAtDepth D c) (hρ : ρ ≤ D)
    (hYm : ∀ K ∈ chainComponents r Yt, K ⊆ interiorAtDepth (L * (D - 1)) (sitesInBlocks L c) → K ⊆ Ym)
    {y : TorusSite n} (hyX : y ∈ X) (hyZ : y ∈ storedBlocks L r bad Yt C) :
    y ∈ windowZone L r (lowerAttached L r (windowSeeds L bad Ym C (sitesInBlocks L (interiorAtDepth ρ c)))
      (sitesInBlocks L C)) C (interiorAtDepth ρ c) := by
  classical
  refine Finset.mem_inter.mpr ⟨?_, interiorAtDepth_anti hρ c (hXd hyX)⟩
  rcases Finset.mem_union.mp hyZ with hC | hcore
  · exact Finset.mem_union_left _ hC
  · obtain ⟨θ, hθ, hatt, hb, u, hu, p, hp, hpu⟩ := exists_component_of_mem_coreBlocks hc hX hyX hcore
    refine Finset.mem_union_right _ ?_
    simp only [coreBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p, Finset.mem_inter.mpr ⟨mem_sitesInBlocks.mpr (by simp [hp]),
      (mem_thickening _ _ _).mpr ⟨u, subset_lowerAttached hXd hρ hYm hθ hatt hb hu, hpu⟩⟩⟩
private theorem component_subset_interior {c : Finset (TorusSite n)} {D : ℕ} (hc : 10 * r / L + 1 ≤ r')
    (hL : L + 4 * r ≤ 10 * r) (hX : X ∈ chainComponents r' (coarseHull L r r' bad Yt C))
    (hXd : X ⊆ interiorAtDepth D c) {y : TorusSite n} (hyX : y ∈ X) (hyZ : y ∈ storedBlocks L r bad Yt C)
    {z : TorusSite (n * L)} (hzb : parentBlock L z = y) (hz : z ∈ Yt) {K : Finset (TorusSite (n * L))}
    (hK : K ∈ chainComponents r Yt) (hzK : z ∈ K) :
    K ⊆ interiorAtDepth (L * (D - 1)) (sitesInBlocks L c) := by
  obtain ⟨θ, hθ, -, hb, hzθ⟩ := exists_component_of_mem_clusterSites hc hL hX hyX hyZ hzb
    (Finset.mem_union_left _ (Finset.mem_union_right _ hz))
  intro v hv
  exact mem_interior_of_parentBlock_mem (hXd (hb v (component_subset_of_meets hθ hzθ hK hzK hv)))
end Geometry
section Tower
variable {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (k : ℕ)
private theorem lowerScore_of_not_mem (s₀ s₁ : ℝ) : ∀ (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n)
    (c : Finset (TorusSite n)) (y : TorusSite n), y ∉ lowerHull T k s n u c → lowerScore T k s₀ s₁ s n u c y = 0
  | 0, n, _, u, c, y, h => by rw [lowerScore, if_neg h]
  | s + 1, n, _, u, c, y, h => by rw [lowerScore, if_neg h]
private theorem siteMajorant_of_not_mem (s₀ s₁ : ℝ) (t n : ℕ) [NeZero n] (u : MarkedSample ℓ t n)
    {y : TorusSite n} (h : y ∉ stageHull T t n u) : siteMajorant T s₀ s₁ t n u y = 0 := by
  unfold siteMajorant siteScore
  exact dif_neg h
private theorem siteMajorant_zero_of_mem (s₀ s₁ : ℝ) (n : ℕ) [NeZero n] (u : MarkedSample ℓ 0 n)
    {y : TorusSite n} (h : y ∈ stageHull T 0 n u) : siteMajorant T s₀ s₁ 0 n u y = s₀ := by
  have h' : y ∈ (stageState T 0 n u).2.1 := h
  unfold siteMajorant siteScore
  rw [dif_pos h']
  rfl
private theorem siteMajorant_succ_of_not_stored (s₀ s₁ : ℝ) (s n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + 1) n)
    {y : TorusSite n} (hy : y ∈ stageHull T (s + 1) n u)
    (hZ : y ∉ storedBlocks ℓ.side (stageRange T s) u.2.2.2 (stageState T s (n * ℓ.side) u.1).2.1
      (hotCoreSites (T.stage s).toStepSetup u.2.2.1)) :
    siteMajorant T s₀ s₁ (s + 1) n u y = s₁ := by
  classical
  have hy' : y ∈ (stageState T (s + 1) n u).2.1 := hy
  unfold siteMajorant siteScore
  rw [dif_pos hy']
  show coarseLabelScore s₁ (labelMajorant T s₀ s₁ s)
    (if (y : TorusSite n) ∈ storedBlocks ℓ.side (stageRange T s) u.2.2.2 (stageState T s (n * ℓ.side) u.1).2.1
        (hotCoreSites (T.stage s).toStepSetup u.2.2.1) then _ else Sum.inl ()) = s₁
  rw [if_neg hZ]
  rfl
private theorem siteMajorant_succ_of_stored (s₀ s₁ : ℝ) (s n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + 1) n)
    {y : TorusSite n} (hy : y ∈ stageHull T (s + 1) n u)
    (hZ : y ∈ storedBlocks ℓ.side (stageRange T s) u.2.2.2 (stageState T s (n * ℓ.side) u.1).2.1
      (hotCoreSites (T.stage s).toStepSetup u.2.2.1)) :
    siteMajorant T s₀ s₁ (s + 1) n u y =
      s₁ + ∑ z ∈ sitesInBlocks ℓ.side {y}, siteMajorant T s₀ s₁ s (n * ℓ.side) u.1 z := by
  classical
  rw [← sum_blockOffset_eq_sum_sitesInBlocks y (fun z => siteMajorant T s₀ s₁ s (n * ℓ.side) u.1 z)]
  have hy' : y ∈ (stageState T (s + 1) n u).2.1 := hy
  unfold siteMajorant siteScore
  rw [dif_pos hy']
  show coarseLabelScore s₁ (labelMajorant T s₀ s₁ s)
    (if (y : TorusSite n) ∈ storedBlocks ℓ.side (stageRange T s) u.2.2.2 (stageState T s (n * ℓ.side) u.1).2.1
        (hotCoreSites (T.stage s).toStepSetup u.2.2.1) then
      Sum.inr (blockConfigAt (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1)
        (storedBlocks ℓ.side (stageRange T s) u.2.2.2 (stageState T s (n * ℓ.side) u.1).2.1
          (hotCoreSites (T.stage s).toStepSetup u.2.2.1))
        (stageState T s (n * ℓ.side) u.1).1 (stageState T s (n * ℓ.side) u.1).2.1
        (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1 y) else Sum.inl ()) = _
  rw [if_pos hZ]
  show s₁ + _ = s₁ + _
  congr 1
  refine Finset.sum_congr rfl fun o _ => ?_
  simp only [blockConfigAt]
  by_cases h : (blockSite y o : TorusSite (n * ℓ.side)) ∈ (stageState T s (n * ℓ.side) u.1).2.1
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]
    rfl
private theorem deep_components_in_lowerHull
    (hc : ∀ j < k, 10 * stageRange T j / ℓ.side + 1 ≤ stageRange T (j + 1))
    (hL : ∀ j < k, ℓ.side + 4 * stageRange T j ≤ 10 * stageRange T j)
    (hρ : ∀ s d, s + d + 1 = k → blockDepth T k s ≤ componentDepth T k d)
    (hbot : 4 * stageRange T 0 ≤ componentDepth T k k)
    (hW : lowerHullSubsetStageHullStatement) :
    ∀ (s d : ℕ), s + d = k → ∀ (m : ℕ) [NeZero m] (u : MarkedSample ℓ s m) (c : Finset (TorusSite m)),
      ∀ X ∈ chainComponents (stageRange T s) (stageHull T s m u), X ⊆ interiorAtDepth (componentDepth T k d) c →
        X ⊆ lowerHull T k s m u c ∧
          ∀ s₀ s₁ : ℝ, ∀ z ∈ X, lowerScore T k s₀ s₁ s m u c z = siteMajorant T s₀ s₁ s m u z := by
  classical
  intro s
  induction s with
  | zero =>
    intro d hd m _ u c X hX hXd
    have hdk : d = k := by omega
    subst hdk
    have hin : X ⊆ lowerHull T d 0 m u c := fun v hv =>
      Finset.mem_inter.mpr ⟨subset_of_mem_chainComponents hX hv, interiorAtDepth_anti hbot c (hXd hv)⟩
    refine ⟨hin, fun s₀ s₁ z hz => ?_⟩
    rw [lowerScore, if_pos (hin hz)]
    exact (siteMajorant_zero_of_mem T s₀ s₁ m u (subset_of_mem_chainComponents hX hz)).symm
  | succ s ih =>
    intro d hd m _ u c X hX hXd
    have IH := ih (d + 1) (by omega) (m * ℓ.side) u.1 (sitesInBlocks ℓ.side c)
    have hs : s < k := by omega
    have hX' : X ∈ chainComponents (stageRange T (s + 1)) (coarseHull ℓ.side (stageRange T s)
      (stageRange T (s + 1)) u.2.2.2 (stageState T s (m * ℓ.side) u.1).2.1
      (hotCoreSites (T.stage s).toStepSetup u.2.2.1)) := hX
    have hYm : ∀ K ∈ chainComponents (stageRange T s) (stageState T s (m * ℓ.side) u.1).2.1,
        K ⊆ interiorAtDepth (ℓ.side * (componentDepth T k d - 1)) (sitesInBlocks ℓ.side c) →
        K ⊆ lowerHull T k s (m * ℓ.side) u.1 (sitesInBlocks ℓ.side c) := fun K h1 h2 => (IH K h1 h2).1
    have hzone : ∀ y ∈ X, y ∈ storedBlocks ℓ.side (stageRange T s) u.2.2.2
        (stageState T s (m * ℓ.side) u.1).2.1 (hotCoreSites (T.stage s).toStepSetup u.2.2.1) →
        y ∈ lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
          (lowerHull T k s (m * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c := fun y hyX hyZ =>
      mem_lowerZone_of_deep (hc s hs) hX' hXd (hρ s d (by omega)) hYm hyX hyZ
    have hin : X ⊆ lowerHull T k (s + 1) m u c := by
      intro v hv
      obtain ⟨z, hz, hvz⟩ := (mem_thickening _ _ _).mp (subset_of_mem_chainComponents hX' hv)
      have hzX : z ∈ X := mem_component_of_supDist_le hX' hv (mem_coarseHull_of_mem_storedBlocks hz)
        (hvz.trans (Nat.div_le_self _ _))
      rw [lowerHull]
      exact (mem_thickening _ _ _).mpr ⟨z, hzone z hzX hz, hvz⟩
    refine ⟨hin, fun s₀ s₁ y hy => ?_⟩
    have hyH : y ∈ stageHull T (s + 1) m u := subset_of_mem_chainComponents hX hy
    rw [lowerScore, if_pos (hin hy)]
    by_cases hZ : y ∈ storedBlocks ℓ.side (stageRange T s) u.2.2.2 (stageState T s (m * ℓ.side) u.1).2.1
        (hotCoreSites (T.stage s).toStepSetup u.2.2.1)
    · rw [if_pos (hzone y hy hZ), siteMajorant_succ_of_stored T s₀ s₁ s m u hyH hZ]
      congr 1
      refine Finset.sum_congr rfl fun z hz => ?_
      have hzb : parentBlock ℓ.side z = y := by simpa using mem_sitesInBlocks.mp hz
      by_cases hzY : z ∈ (stageState T s (m * ℓ.side) u.1).2.1
      · obtain ⟨K, hK, hzK⟩ := exists_mem_chainComponents (r := stageRange T s) hzY
        exact (IH K hK (component_subset_interior (hc s hs) (hL s hs) hX' hXd hy hZ hzb hzY hK hzK)).2
          s₀ s₁ z hzK
      · rw [siteMajorant_of_not_mem T s₀ s₁ s (m * ℓ.side) u.1 hzY]
        refine lowerScore_of_not_mem T k s₀ s₁ s (m * ℓ.side) u.1 _ z fun h => hzY ?_
        exact (hW ℓ T k).1 s (m * ℓ.side) u.1 _ h
    · have hZ' : y ∉ lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
          (lowerHull T k s (m * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c := fun h =>
        hZ ((hW ℓ T k).2 s m u c h)
      rw [if_neg hZ', siteMajorant_succ_of_not_stored T s₀ s₁ s m u hyH hZ, add_zero]
end Tower
section Numbers
variable {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (k : ℕ)
private theorem componentDepth_ge (hr : 1 ≤ stageRange T k) :
    ∀ d, 14 * stageRange T k * ℓ.side ^ d + 2 ≤ componentDepth T k d := by
  have hL : 2 ≤ ℓ.side := T.two_le_side
  intro d
  induction d with
  | zero =>
    show 14 * stageRange T k * ℓ.side ^ 0 + 2 ≤ 2 ^ 4 * stageRange T k
    simp only [pow_zero, mul_one]
    omega
  | succ d ih =>
    show 14 * stageRange T k * ℓ.side ^ (d + 1) + 2 ≤ ℓ.side * (componentDepth T k d - 1)
    have h1 : 14 * stageRange T k * ℓ.side ^ d + 1 ≤ componentDepth T k d - 1 := by omega
    calc 14 * stageRange T k * ℓ.side ^ (d + 1) + 2 ≤ ℓ.side * (14 * stageRange T k * ℓ.side ^ d + 1) := by
          rw [pow_succ]
          nlinarith
      _ ≤ ℓ.side * (componentDepth T k d - 1) := Nat.mul_le_mul_left _ h1
private theorem stageRange_le_add (hstep : ∀ j < k, stageRange T j ≤ stageRange T (j + 1) + 1) :
    ∀ i j, j + i = k → stageRange T j ≤ stageRange T k + i := by
  intro i
  induction i with
  | zero =>
    intro j hj
    have : j = k := by omega
    subst this
    omega
  | succ i ih =>
    intro j hj
    have h1 := ih (j + 1) (by omega)
    have h2 := hstep j (by omega)
    omega
private theorem four_mul_add_le {r P d : ℕ} (hr : 1 ≤ r) (hP : d + 1 ≤ P) : 4 * (r + d) ≤ 14 * r * P + 2 := by
  have h1 : (d + 1) * r ≤ P * r := Nat.mul_le_mul_right _ hP
  have h2 : r + d ≤ (d + 1) * r := by nlinarith
  nlinarith
private theorem poly_le_sixteen_pow (d : ℕ) : (2 * d + 3) * (d + 8) ≤ 28 * 16 ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [pow_succ]
    nlinarith
private theorem mul_le_of_poly_le {r P d : ℕ} (hr : 2 ≤ r) (hP : (2 * d + 3) * (d + 8) ≤ 28 * P) :
    (r + d + 1) * (d + 8) ≤ 14 * r * P := by
  have h1 : 2 * (r + d + 1) ≤ r * (2 * d + 3) := by nlinarith
  have h2 : 2 * ((r + d + 1) * (d + 8)) ≤ r * (2 * d + 3) * (d + 8) := by
    calc 2 * ((r + d + 1) * (d + 8)) = 2 * (r + d + 1) * (d + 8) := by ring
      _ ≤ r * (2 * d + 3) * (d + 8) := Nat.mul_le_mul_right _ h1
  have h3 : r * ((2 * d + 3) * (d + 8)) ≤ r * (28 * P) := Nat.mul_le_mul_left _ hP
  nlinarith
private theorem ceilDiv_le_succ (a L : ℕ) (hL : 1 ≤ L) : ceilDiv a L ≤ a + 1 := by
  unfold ceilDiv
  refine Nat.div_le_of_le_mul ?_
  have h1 : a + L - 1 ≤ a + L := Nat.sub_le _ _
  nlinarith
private theorem le_clusterRange {L : ℕ} {x : ℝ} (h : (L : ℝ) ^ 100 ≤ x) : L ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
end Numbers
theorem deepComponentsInLowerHull (hS : windowDepthBoundStatement)
    (hW : lowerHullSubsetStageHullStatement) : deepComponentsInLowerHullStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt, H⟩ := hS a ha
  refine ⟨max L₀ 16, rt₀, hrt, fun L hodd hL Tb hTa hTL hDr hrtb => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hodd (le_trans (le_max_left _ _) hL) Tb hTa hTL hDr hrtb
  refine ⟨max y₀ ((L : ℝ) ^ 100), fun y hy hret hrow => ?_⟩
  have hsz := Hy y (le_trans (le_max_left _ _) hy) hret hrow
  intro T β k hrun s d hsd m _ u G κ _ X hX hXd
  have hL16 : 16 ≤ (Tb.stepParameters y).side := by
    show 16 ≤ Tb.side
    rw [hTL]
    exact le_trans (le_max_right _ _) hL
  have hfloor : ∀ j ≤ k, (Tb.stepParameters y).side ≤ stageRange T j := by
    intro j hj
    have h1 : y ≤ (T.stage j).coupling := (hrun.onFamily.onFamily j hj).le_coupling
    have h2 : (L : ℝ) ^ 100 ≤ (T.stage j).coupling := (le_trans (le_max_right _ _) hy).trans h1
    have h3 : L ≤ stageRange T j := le_clusterRange h2
    have h4 : (Tb.stepParameters y).side = L := hTL
    omega
  have hstep : ∀ j < k, stageRange T j ≤ stageRange T (j + 1) + 1 := fun j hj =>
    (hrun.onFamily.onFamily j hj.le).isStep.2.2
  have hrk := hfloor k le_rfl
  have hc : ∀ j < k, 10 * stageRange T j / (Tb.stepParameters y).side + 1 ≤ stageRange T (j + 1) := by
    intro j hj
    have h1 := hfloor j hj.le
    have h2 := hstep j hj
    have h3 : 10 * stageRange T j / (Tb.stepParameters y).side ≤ 10 * stageRange T j / 16 :=
      Nat.div_le_div_left hL16 (by norm_num)
    omega
  have hLr : ∀ j < k, (Tb.stepParameters y).side + 4 * stageRange T j ≤ 10 * stageRange T j := by
    intro j hj
    have h1 := hfloor j hj.le
    omega
  have hr1 : 1 ≤ stageRange T k := by omega
  have hpow : ∀ d, d + 1 ≤ (Tb.stepParameters y).side ^ d := fun d => Nat.lt_pow_self (by omega)
  have hρ : ∀ s d, s + d + 1 = k → blockDepth T k s ≤ componentDepth T k d := by
    intro s d hsd
    have hcd := componentDepth_ge T k hr1 d
    refine max_le ?_ ?_
    · have h1 := stageRange_le_add T k hstep d (s + 1) (by omega)
      have h2 := four_mul_add_le hr1 (hpow d)
      omega
    · have h1 := stageRange_le_add T k hstep (d + 1) s (by omega)
      have h2 := (hsz T β k hrun).1 s (by omega)
      have h3 : ((k : ℝ) - s) = (d : ℝ) + 1 := by
        have : (k : ℝ) = (s : ℝ) + d + 1 := by exact_mod_cast hsd.symm
        rw [this]
        ring
      have h4 : (windowDepth T k s : ℝ) ≤ ((stageRange T s * (d + 8) : ℕ) : ℝ) := by
        refine h2.trans ?_
        rw [h3]
        push_cast
        have h5 : (2⁻¹ : ℝ) ^ 20 * ((d : ℝ) + 1) ≤ (d : ℝ) + 1 := by
          have : (2⁻¹ : ℝ) ^ 20 ≤ 1 := by norm_num
          have h6 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
          nlinarith
        have h7 : (0 : ℝ) ≤ stageRange T s := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) h7
      have h8 : windowDepth T k s ≤ stageRange T s * (d + 8) := by exact_mod_cast h4
      have h9 : stageRange T s * (d + 8) ≤ (stageRange T k + d + 1) * (d + 8) :=
        Nat.mul_le_mul_right _ (by omega)
      have h10 : (16 : ℕ) ^ d ≤ (Tb.stepParameters y).side ^ d := Nat.pow_le_pow_left hL16 d
      have h11 := mul_le_of_poly_le (r := stageRange T k) (P := (Tb.stepParameters y).side ^ d) (d := d)
        (by omega) ((poly_le_sixteen_pow d).trans (Nat.mul_le_mul_left _ h10))
      have h12 := ceilDiv_le_succ (windowDepth T k s) (Tb.stepParameters y).side (by omega)
      omega
  have hbot : 4 * stageRange T 0 ≤ componentDepth T k k := by
    have h1 := stageRange_le_add T k hstep k 0 (by omega)
    have h2 := four_mul_add_le hr1 (hpow k)
    have h3 := componentDepth_ge T k hr1 k
    omega
  have := deep_components_in_lowerHull T k hc hLr hρ hbot hW s d hsd m u (G.cell m κ) X hX hXd
  exact this
end YangMills.Construction.CellWindows
end
