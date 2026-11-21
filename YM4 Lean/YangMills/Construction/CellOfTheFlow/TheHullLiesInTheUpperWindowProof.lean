import YangMills.Construction.CellOfTheFlow.AFalseSiteHoldsALongClassProof
import YangMills.Construction.CellOfTheFlow.TheHullLiesInTheUpperWindow
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsAboveABox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps TorusBalls StepSettings WeightedResponses
section Geometry
variable {n : ℕ} [NeZero n]
private theorem mem_interiorAtDepth {m : ℕ} {c : Finset (TorusSite n)} {v : TorusSite n} :
    v ∈ interiorAtDepth m c ↔ v ∈ c ∧ ∀ w, w ∉ c → m ≤ supDist v w := by
  classical
  simp [interiorAtDepth]
private theorem mem_sitesInBlocks {L : ℕ} [NeZero L] {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.CongruentBoxes.mem_sitesInBlocks <;> assumption
private theorem mem_interiorAtDepth_of_supDist_add_le {m p : ℕ} {c : Finset (TorusSite n)} {z y : TorusSite n}
    (hz : z ∈ interiorAtDepth m c) (hp : 0 < p) (hzy : supDist z y + p ≤ m) : y ∈ interiorAtDepth p c := by
  obtain ⟨_, hd⟩ := mem_interiorAtDepth.mp hz
  refine mem_interiorAtDepth.mpr ⟨?_, fun w hw => ?_⟩
  · by_contra hy
    have := hd y hy
    omega
  · have h1 := hd w hw
    have h2 := supDist_triangle z y w
    omega
private theorem le_mul_ceilDiv (a L : ℕ) (hL : 0 < L) : a ≤ L * ceilDiv a L := by apply _root_.YangMills.SharedProofs.p15502 <;> assumption
private theorem sitesInBlocks_interior_subset {L h ρ : ℕ} [NeZero L] {c : Finset (TorusSite n)}
    (hρ : ceilDiv h L + 1 ≤ ρ) :
    sitesInBlocks L (interiorAtDepth ρ c) ⊆ interiorAtDepth h (sitesInBlocks L c) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  intro x hx
  obtain ⟨hc, hd⟩ := mem_interiorAtDepth.mp (mem_sitesInBlocks.mp hx)
  refine mem_interiorAtDepth.mpr ⟨mem_sitesInBlocks.mpr hc, fun w hw => ?_⟩
  have h1 := hd (parentBlock L w) fun hb => hw (mem_sitesInBlocks.mpr hb)
  have h2 := supDist_parentBlock_le_div_add_one L x w
  have h3 : ceilDiv h L ≤ supDist x w / L := by omega
  have h4 := le_mul_ceilDiv h L hL
  have h5 := Nat.mul_le_mul_left L h3
  have h6 := Nat.mul_div_le (supDist x w) L
  omega
private theorem supDist_parentBlock_le_ceilDiv {L r g : ℕ} [NeZero L] (hg : r ≠ 0 → 4 * r < g)
    {a u : TorusSite (n * L)} (hau : supDist a u ≤ 4 * r) :
    supDist (parentBlock L a) (parentBlock L u) ≤ ceilDiv g L := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain ⟨e, he, hb⟩ := exists_offset_of_supDist a u
    have h0 : e = 0 := by
      funext i
      have := hb i
      exact Int.natAbs_eq_zero.mp (by omega)
    have : u = a := by
      rw [he, h0]
      funext i
      simp [siteOfInt]
    rw [this, supDist_self]
    exact Nat.zero_le _
  · have h1 := supDist_parentBlock_le_div_add_one L a u
    have h2 := hg (by omega)
    have h3 : supDist a u / L < ceilDiv g L := by
      have h4 := le_mul_ceilDiv g L hL
      have h5 := Nat.mul_div_le (supDist a u) L
      exact Nat.lt_of_mul_lt_mul_left (a := L) (by omega)
    omega
private theorem exists_component_reaching {s : ℕ} {X Xp LC Rw : Finset (TorusSite n)}
    (hX : ∀ p ∈ X, p ∈ Rw → p ∈ Xp) {p q : TorusSite n} (hpq : ChainConnected s X p q) (hq : q ∈ LC)
    (hp : p ∈ Xp) :
    ∃ K ∈ chainComponents s Xp, p ∈ K ∧
      ((∃ x ∈ K, x ∈ LC) ∨ ∃ a ∈ K, ∃ b, b ∉ Rw ∧ supDist a b ≤ s) := by
  classical
  induction hpq using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨K, hK, hpK⟩ := exists_mem_chainComponents (r := s) hp
    exact ⟨K, hK, hpK, Or.inl ⟨_, hpK, hq⟩⟩
  | @head a b hs _ ih =>
    obtain ⟨K₀, hK₀, haK₀⟩ := exists_mem_chainComponents (r := s) hp
    by_cases hb : b ∈ Rw
    · obtain ⟨K, hK, hbK, hm⟩ := ih (hX b hs.2.1 hb)
      exact ⟨K, hK, mem_of_chainConnected_of_mem_chainComponents hK hbK hp
        (chainConnected_of_supDist_le (hX b hs.2.1 hb) hp (by rw [supDist_comm]; exact hs.2.2)), hm⟩
    · exact ⟨K₀, hK₀, haK₀, Or.inr ⟨a, haK₀, b, hb, hs.2.2⟩⟩
private theorem mem_windowZone_of_mem_storedBlocks {L r h ρ g : ℕ} [NeZero L]
    {bad : Finset (TorusBond (n * L))} {Yt Yw : Finset (TorusSite (n * L))} {C c : Finset (TorusSite n)}
    (hρ : ceilDiv h L + 1 ≤ ρ) (hg : r ≠ 0 → 4 * r < g)
    (hY : Yt ∩ interiorAtDepth h (sitesInBlocks L c) ⊆ Yw) {z : TorusSite n}
    (hz : z ∈ storedBlocks L r bad Yt C) (hd : z ∈ interiorAtDepth (ρ + ceilDiv g L) c) :
    z ∈ windowZone L r
      (upperAttached L r (windowSeeds L bad Yw C (sitesInBlocks L (interiorAtDepth ρ c)))
        (sitesInBlocks L C) (sitesInBlocks L (interiorAtDepth ρ c))) C (interiorAtDepth ρ c) := by
  classical
  have hzρ : z ∈ interiorAtDepth ρ c := by
    obtain ⟨hc, hw⟩ := mem_interiorAtDepth.mp hd
    exact mem_interiorAtDepth.mpr ⟨hc, fun w hwc => by have := hw w hwc; omega⟩
  unfold windowZone
  refine Finset.mem_inter.mpr ⟨?_, hzρ⟩
  unfold storedBlocks at hz
  rcases Finset.mem_union.mp hz with hC | hcore
  · exact Finset.mem_union_left _ hC
  refine Finset.mem_union_right _ ?_
  unfold coreBlocks at hcore ⊢
  obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hcore).2
  obtain ⟨haz, haw⟩ := Finset.mem_inter.mp ha
  obtain ⟨u, hu, hau⟩ := (mem_thickening _ _ _).mp haw
  have hblock : parentBlock L a = z := by simpa using mem_sitesInBlocks.mp haz
  unfold attachedSites at hu
  obtain ⟨K, hKf, huK⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨hK, hKC⟩ := Finset.mem_filter.mp hKf
  obtain ⟨w, hw⟩ := hKC
  obtain ⟨hwK, hwC⟩ := Finset.mem_inter.mp hw
  have hnear : supDist z (parentBlock L u) ≤ ceilDiv g L := hblock ▸ supDist_parentBlock_le_ceilDiv hg hau
  have hρ0 : 0 < ρ := by omega
  have huR : u ∈ sitesInBlocks L (interiorAtDepth ρ c) :=
    mem_sitesInBlocks.mpr (mem_interiorAtDepth_of_supDist_add_le hd hρ0 (by omega))
  have hX : ∀ p ∈ bad.image Prod.fst ∪ Yt ∪ sitesInBlocks L C, p ∈ sitesInBlocks L (interiorAtDepth ρ c) →
      p ∈ windowSeeds L bad Yw C (sitesInBlocks L (interiorAtDepth ρ c)) := by
    intro p hp hpR
    unfold windowSeeds
    refine Finset.mem_inter.mpr ⟨?_, hpR⟩
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (hY (Finset.mem_inter.mpr ⟨hp, sitesInBlocks_interior_subset hρ hpR⟩)))
    · exact Finset.mem_union_right _ hp
  have huX : u ∈ bad.image Prod.fst ∪ Yt ∪ sitesInBlocks L C := subset_of_mem_chainComponents hK huK
  obtain ⟨K', hK', huK', hm⟩ :=
    exists_component_reaching hX (chainConnected_of_mem_chainComponents hK huK hwK) hwC (hX u huX huR)
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, Finset.mem_inter.mpr ⟨haz, ?_⟩⟩⟩
  refine (mem_thickening _ _ _).mpr ⟨u, ?_, hau⟩
  unfold upperAttached
  refine Finset.mem_biUnion.mpr ⟨K', Finset.mem_filter.mpr ⟨hK', ?_⟩, huK'⟩
  rcases hm with ⟨x, hxK, hxC⟩ | hm
  · exact Or.inl ⟨x, Finset.mem_inter.mpr ⟨hxK, hxC⟩⟩
  · exact Or.inr hm
end Geometry
variable {ℓ : StepParameters}
private theorem stageHull_inter_subset_upperHull_of_le (T : StageTower ℓ) (k : ℕ) :
    ∀ s : ℕ, s ≤ k → ∀ (n : ℕ) [NeZero n] (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)),
    stageHull T s n u ∩ interiorAtDepth (windowDepth T k s) c ⊆ upperHull T k s n u c := by
  intro s
  induction s with
  | zero =>
    intro _ n _ u c v hv
    exact hv
  | succ s ih =>
    intro hs n _ u c v hv
    obtain ⟨hvY, hvd⟩ := Finset.mem_inter.mp hv
    have hvY' : v ∈ thickening (stageRange T (s + 1) / 2)
        (storedBlocks ℓ.side (stageRange T s) u.2.2.2 (stageHull T s (n * ℓ.side) u.1)
          (hotCoreSites (T.stage s).toStepSetup u.2.2.1)) := hvY
    obtain ⟨z, hz, hvz⟩ := (mem_thickening _ _ _).mp hvY'
    have hρ : ceilDiv (windowDepth T k s) ℓ.side + 1 ≤ blockDepth T k s := le_max_right _ _
    have hg : stageRange T s ≠ 0 → 4 * stageRange T s < windowLength T k s := by
      intro hr
      have h1 : 1 ≤ k - s := by omega
      have h2 : 2 ^ 12 * stageRange T s * 1 ≤ 2 ^ 12 * stageRange T s * (k - s) :=
        Nat.mul_le_mul_left _ h1
      unfold windowLength
      omega
    have hdepth : windowDepth T k (s + 1) =
        blockDepth T k s + ceilDiv (windowLength T k s) ℓ.side + stageRange T (s + 1) := rfl
    have hzd : z ∈ interiorAtDepth (blockDepth T k s + ceilDiv (windowLength T k s) ℓ.side) c := by
      refine mem_interiorAtDepth_of_supDist_add_le hvd (by omega) ?_
      omega
    refine Finset.mem_inter.mpr ⟨hvd, (mem_thickening _ _ _).mpr ⟨z, ?_, hvz⟩⟩
    exact mem_windowZone_of_mem_storedBlocks hρ hg (ih (by omega) (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) hz hzd
theorem stageHull_inter_subset_upperHull : stageHullInterSubsetUpperHullStatement := by
  intro a _
  refine ⟨1, fun _ => 1, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ _ _
  refine ⟨0, ?_⟩
  intro y _ _ _ T β k _ s hs m _ u G κ _
  exact stageHull_inter_subset_upperHull_of_le T k s hs m u _
end YangMills.Construction.CellWindows
end
