import YangMills.Construction.CellOfTheFlow.LongClassesHaveManyUnitsProof
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.HullsInEveryVolume.OneStepDownFromAHull
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusFields TorusLumps TorusBlocks TorusBalls RenormalizationStepParameters StepReturn StepFloors WeightedResponses
section Geometry
variable {n : ℕ} [NeZero n]
private theorem mem_box_iff (z q : TorusSite n) (m : ℕ) : q ∈ box z m ↔ _root_.YangMills.Construction.TorusFields.supDist q z ≤ m := by
  classical
  unfold box
  rw [mem_thickening]
  simp
abbrev _root_.YangMills.SharedProofs.p104074 := @mem_box_iff
private theorem mem_plaquettesIn {S : Finset (TorusSite n)} {p : TorusPlaquette n} :
    p ∈ plaquettesIn S ↔ p.2.1 < p.2.2 ∧ ∀ q ∈ plaquetteVertices p.1 p.2.1 p.2.2, q ∈ S := by apply _root_.YangMills.Construction.TorusLumps.mem_plaquettesIn_iff_forall_vertex <;> assumption
private theorem containsHotPlaquette_of_near {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible)
    (hLn : ℓ.side ∣ n) {V : TorusField n} {z s : TorusSite n} {m : ℕ}
    (hs : s ∈ torusHotSites ℓ V) (hd : _root_.YangMills.Construction.TorusFields.supDist z s + 2 ^ 15 + 8 ≤ m) :
    ContainsHotPlaquette ℓ V (box z m) := by
  classical
  obtain ⟨l, hl, hsl⟩ := mem_torusHotSites_iff.mp hs
  obtain ⟨x, μ, ν, hlt, hσ, c, hc, rfl⟩ := (mem_torusHotLumps_iff ℓ hfit hLn V l).mp hl
  refine ⟨(x, μ, ν), mem_plaquettesIn.mpr ⟨hlt, fun q hq => ?_⟩, hσ⟩
  rw [mem_box_iff]
  have h1 := _root_.YangMills.Construction.TorusLumps.supDist_lt_of_mem_torusHotLumps hfit hLn hl hsl (mem_torusLumpOf_self c)
  have h2 := _root_.YangMills.Construction.TorusLumps.supDist_le_four_of_mem_plaquetteVertices (x, μ, ν) hc hq
  have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle q c z
  have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle c s z
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm q c] at h3
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm c s, _root_.YangMills.Construction.TorusFields.supDist_comm s z] at h4
  omega
private theorem exists_mem_near_threshold {ρ : ℕ} {Y : Finset (TorusSite n)} {p q : TorusSite n}
    (hp : p ∈ Y) (hj : ChainConnected ρ Y p q) (D : ℕ) (hD : D ≤ _root_.YangMills.Construction.TorusFields.supDist p q) :
    ∃ a ∈ Y, D ≤ _root_.YangMills.Construction.TorusFields.supDist p a ∧ _root_.YangMills.Construction.TorusFields.supDist p a ≤ D + ρ := by apply _root_.YangMills.SharedProofs.p3024 <;> assumption
end Geometry
private theorem coarseHull_site_descends {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible) {n : ℕ}
    [NeZero n] (hLn : ℓ.side ∣ n) {r r' : ℕ}
    (hr : 1 ≤ r) (hrr : r ≤ r' + 1) (hr' : 2 ^ 20 ≤ r') (bad : Finset (TorusBond (n * ℓ.side)))
    (Yt : Finset (TorusSite (n * ℓ.side))) (V : TorusField n) (z : TorusSite n)
    (hz : z ∈ coarseHull ℓ.side r r' bad Yt (thickening (2 * r') (torusHotSites ℓ V))) :
    ContainsHotPlaquette ℓ V (box z (4 * r')) ∨
      (∃ b ∈ bad, parentBlock ℓ.side b.1 ∈ box z (4 * r')) ∨
      ∃ S : Finset (TorusSite (n * ℓ.side)), S.card = treeBranching ℓ.side ∧ S ⊆ Yt ∧
        (∀ a ∈ S, parentBlock ℓ.side a ∈ box z (2 * r')) ∧ Separated (40 * r) S := by
  classical
  by_cases hH : ContainsHotPlaquette ℓ V (box z (4 * r'))
  · exact Or.inl hH
  by_cases hB : ∃ b ∈ bad, parentBlock ℓ.side b.1 ∈ box z (4 * r')
  · exact Or.inr (Or.inl hB)
  refine Or.inr (Or.inr ?_)
  have hL16 : 2 ^ 16 ≤ ℓ.side := hfit.L_ge
  have hodd : Odd ℓ.side := hfit.L_odd
  set C := thickening (2 * r') (torusHotSites ℓ V) with hC
  have hot_far : ∀ s ∈ torusHotSites ℓ V, 4 * r' < _root_.YangMills.Construction.TorusFields.supDist z s + 2 ^ 15 + 8 := by
    intro s hs
    by_contra hcon
    exact hH (containsHotPlaquette_of_near hfit hLn hs (by omega))
  have off_C : ∀ y : TorusSite n, y ∈ C → 2 * r' < _root_.YangMills.Construction.TorusFields.supDist z y + 2 ^ 15 + 8 := by
    intro y hy
    obtain ⟨s, hs, hys⟩ := (mem_thickening _ _ _).mp hy
    have h1 := hot_far s hs
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z y s
    omega
  obtain ⟨y₀, hy₀, hzy₀⟩ := (mem_thickening _ _ _).mp hz
  have hstored := Finset.mem_union.mp hy₀
  rcases hstored with hyC | hycore
  · have := off_C y₀ hyC
    omega
  obtain ⟨f, hf⟩ := (Finset.mem_filter.mp hycore).2
  obtain ⟨hfb, hfw⟩ := Finset.mem_inter.mp hf
  have hfy : parentBlock ℓ.side f = y₀ := by
    simpa [sitesInBlocks] using hfb
  obtain ⟨p, hpθ, hfp⟩ := (mem_thickening _ _ _).mp hfw
  obtain ⟨X, hXf, hpX⟩ := Finset.mem_biUnion.mp hpθ
  obtain ⟨hX, hXC⟩ := Finset.mem_filter.mp hXf
  obtain ⟨c, hcI⟩ := hXC
  obtain ⟨hcX, hcC⟩ := Finset.mem_inter.mp hcI
  have hcb : parentBlock ℓ.side c ∈ C := by
    simpa [sitesInBlocks] using hcC
  set Y := bad.image Prod.fst ∪ Yt ∪ sitesInBlocks ℓ.side C with hY
  have hXcl : X ∈ chainComponents (10 * r) Y := hX
  have hpc : ChainConnected (10 * r) Y p c := chainConnected_of_mem_chainComponents hXcl hpX hcX
  have hpY : p ∈ Y := subset_of_mem_chainComponents hXcl hpX
  have dL : ∀ a : ℕ, a / ℓ.side ≤ a / 2 ^ 16 := fun a => Nat.div_le_div_left hL16 (by norm_num)
  have e1 : _root_.YangMills.Construction.TorusFields.supDist y₀ (parentBlock ℓ.side p) ≤ 4 * r / 2 ^ 16 + 1 := by
    have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one ℓ.side f p
    rw [hfy] at h1
    have h2 : _root_.YangMills.Construction.TorusFields.supDist f p / ℓ.side ≤ 4 * r / ℓ.side := Nat.div_le_div_right hfp
    have h3 := dL (4 * r)
    omega
  have e2 : _root_.YangMills.Construction.TorusFields.supDist z (parentBlock ℓ.side p) ≤ r' / 2 + (4 * r / 2 ^ 16 + 1) := by
    have := _root_.YangMills.Construction.TorusFields.supDist_triangle z y₀ (parentBlock ℓ.side p)
    omega
  have e3 : r + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side p) (parentBlock ℓ.side c) := by
    have h1 := off_C _ hcb
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z (parentBlock ℓ.side p) (parentBlock ℓ.side c)
    omega
  have e4 : ℓ.side * r ≤ _root_.YangMills.Construction.TorusFields.supDist p c := by
    have h1 := mul_supDist_parentBlock_le hodd p c
    have h2 : ℓ.side * (r + 1) ≤ ℓ.side * _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side p) (parentBlock ℓ.side c) :=
      Nat.mul_le_mul_left _ e3
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  have hk : 100 * treeBranching ℓ.side ≤ ℓ.side := by
    unfold treeBranching
    omega
  have pick : ∀ i : Fin (treeBranching ℓ.side), ∃ a, a ∈ Yt ∧ parentBlock ℓ.side a ∈ box z (2 * r') ∧
      50 * r * (i : ℕ) ≤ _root_.YangMills.Construction.TorusFields.supDist p a ∧ _root_.YangMills.Construction.TorusFields.supDist p a ≤ 50 * r * (i : ℕ) + 10 * r := by
    intro i
    have hi : 100 * (i : ℕ) ≤ ℓ.side := by
      have := i.2
      omega
    have hD2 : 2 * (50 * r * (i : ℕ)) ≤ ℓ.side * r := by
      calc 2 * (50 * r * (i : ℕ)) = (100 * (i : ℕ)) * r := by ring
        _ ≤ ℓ.side * r := Nat.mul_le_mul_right _ hi
    have hLr : 2 ^ 16 * r ≤ ℓ.side * r := Nat.mul_le_mul_right _ hL16
    obtain ⟨a, haY, ha1, ha2⟩ := exists_mem_near_threshold hpY hpc (50 * r * (i : ℕ)) (by omega)
    have hbl : _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side p) (parentBlock ℓ.side a) ≤ r + 1 := by
      have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one ℓ.side p a
      have h2 : _root_.YangMills.Construction.TorusFields.supDist p a / ℓ.side ≤ r := by
        apply Nat.div_le_of_le_mul
        omega
      omega
    have hza : _root_.YangMills.Construction.TorusFields.supDist z (parentBlock ℓ.side a) ≤ r' / 2 + (4 * r / 2 ^ 16 + 1) + (r + 1) := by
      have := _root_.YangMills.Construction.TorusFields.supDist_triangle z (parentBlock ℓ.side p) (parentBlock ℓ.side a)
      omega
    have hnC : parentBlock ℓ.side a ∉ C := fun hc => by
      have := off_C _ hc
      omega
    have hnb : a ∉ bad.image Prod.fst := fun hb => by
      obtain ⟨b, hb', rfl⟩ := Finset.mem_image.mp hb
      exact hB ⟨b, hb', (mem_box_iff _ _ _).mpr (by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; omega)⟩
    have hnS : a ∉ sitesInBlocks ℓ.side C := fun hs => hnC (by simpa [sitesInBlocks] using hs)
    have haYt : a ∈ Yt := by
      rcases Finset.mem_union.mp haY with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact absurd h hnb
        · exact h
      · exact absurd h hnS
    exact ⟨a, haYt, (mem_box_iff _ _ _).mpr (by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; omega), ha1, ha2⟩
  choose a haYt hab ha1 ha2 using pick
  have hfar : ∀ i j : Fin (treeBranching ℓ.side), i < j → 40 * r ≤ _root_.YangMills.Construction.TorusFields.supDist (a i) (a j) := by
    intro i j hij
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle p (a i) (a j)
    have h2 := ha1 j
    have h3 := ha2 i
    have hij' : (i : ℕ) + 1 ≤ (j : ℕ) := hij
    have h4 : 50 * r * ((i : ℕ) + 1) ≤ 50 * r * (j : ℕ) := Nat.mul_le_mul_left _ hij'
    rw [Nat.mul_add, Nat.mul_one] at h4
    omega
  have hfar' : ∀ i j : Fin (treeBranching ℓ.side), i ≠ j → 40 * r ≤ _root_.YangMills.Construction.TorusFields.supDist (a i) (a j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hfar i j h
    · rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      exact hfar j i h
  have hinj : Function.Injective a := by
    intro i j hij
    by_contra hne
    have := hfar' i j hne
    rw [hij, _root_.YangMills.Construction.TorusFields.supDist_self] at this
    omega
  refine ⟨Finset.univ.image a, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact haYt i
  · intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact hab i
  · intro q hq q' hq' hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq'
    exact hfar' i j fun h => hne (by rw [h])
private theorem hasExpansion_next_of_returns {ℓ : TorusLumps.StepParameters} (hR : ExpansionReturnsAt ℓ)
    {t : ℕ} {x : ℝ} {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem couplingFlow_above_until_crossing {Tb : ParameterAssignment} (hB : 1 ≤ Tb.B) {y g β : ℝ} {K : ℕ}
    (hret : ExpansionReturnsAt (Tb.stepParameters y))
    (hW : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    (hp : FlowCrossing Tb y g β K) :
    (∀ j ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1) ∧
      ∀ j < K, |(couplingFlow (Tb.stepParameters y) β (j + 1)).1 -
        (couplingFlow (Tb.stepParameters y) β j).1| ≤ 2 * Tb.B := by
  have hΞ : windowUpper (Tb.stepParameters y) g = (g ^ 2)⁻¹ + 2 * Tb.B := rfl
  have hfl := hp.le_inv_sq
  have hab := hp.upper_le
  obtain ⟨-, hlow⟩ := hp.isFirst
  rw [hΞ] at hab hlow
  have hlow' : ∀ j < K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 := fun j hj => by
    have := hlow j hj
    linarith
  have hrow : ∀ j ≤ K, HasExpansion (Tb.stepParameters y) j (couplingFlow (Tb.stepParameters y) β j).1
      (couplingFlow (Tb.stepParameters y) β j).2 := by
    intro j
    induction j with
    | zero => exact fun _ => hW β (by linarith)
    | succ j ih =>
      intro hj
      exact (hasExpansion_next_of_returns hret (hlow' j (by omega)) (ih (by omega))).1
  have hstep : ∀ j < K, |(couplingFlow (Tb.stepParameters y) β (j + 1)).1 -
      (couplingFlow (Tb.stepParameters y) β j).1| ≤ 2 * Tb.B :=
    fun j hj => (hasExpansion_next_of_returns hret (hlow' j hj) (hrow j hj.le)).2
  refine ⟨fun j hj => ?_, hstep⟩
  rcases Nat.lt_or_ge j K with h | h
  · exact hlow' j h
  · have hjK : j = K := le_antisymm hj h
    subst hjK
    cases j with
    | zero =>
      have : (couplingFlow (Tb.stepParameters y) β 0).1 = β := rfl
      rw [this]
      linarith
    | succ k =>
      have h1 := abs_le.mp (hstep k (Nat.lt_succ_self k))
      have h2 := hlow k (Nat.lt_succ_self k)
      linarith [h1.1]
private theorem side_dvd_of_hullChainAtLevel {Tb : ParameterAssignment} {y g β : ℝ} {K m u n : ℕ}
    {T : StageTower (Tb.stepParameters y)} (hfit : (Tb.stepParameters y).Admissible)
    (h : HullChainAtLevel Tb y g β K m T u n) : (Tb.stepParameters y).side ∣ n := by
  have hL : (Tb.stepParameters y).side = Tb.side := rfl
  have hL16 : 2 ^ 16 ≤ Tb.side := hfit.L_ge
  have hn₀ : 4096 ≤ Tb.n₀ := hfit.n₀_ge
  have hvol := h.chain.volume_le
  have hm : m ≠ 0 := by
    rintro rfl
    have : 2 ^ 16 * 1 ≤ Tb.side * Tb.n₀ := Nat.mul_le_mul hL16 (by omega)
    simp only [pow_zero, mul_one] at hvol
    omega
  rw [hL, h.side_eq]
  unfold torusSideAtLevel
  rw [fineSide_eq]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) _) _
theorem unitOrSeparatedChildren_of_eventuallyFloorConditions (hF : EventuallyFloorConditions) :
    UnitOrSeparatedChildren := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L _ _ Tb _ _ hD _ _ _ _ => ⟨0, fun Kr _ _ _ _ _ => ?_⟩⟩
  obtain ⟨y₂, hy₂⟩ := hF Tb hD (2 ^ 20) 1 (by norm_num) one_pos
  refine ⟨max Tb.floorMin y₂, fun y hy hret hW g β K m T u n _ hA w z hz => ?_⟩
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y (le_trans (le_max_left _ _) hy)
  have hyy : y₂ ≤ y := le_trans (le_max_right _ _) hy
  have hLn := side_dvd_of_hullChainAtLevel hfit hA
  obtain ⟨hfl, hst⟩ := couplingFlow_above_until_crossing hD.B_ge hret hW hA.chain.toFlowCrossing
  have hlev : ∀ j ≤ K, stageRange T j = clusterRange (couplingFlow (Tb.stepParameters y) β j).1 :=
    fun j hj => by
      unfold stageRange
      rw [hA.chain.follows j (by omega)]
  have hbig : ∀ j ≤ K, 2 ^ 20 ≤ stageRange T j := fun j hj => by
    rw [hlev j hj]
    have h6 := (hy₂ _ (le_trans hyy (hfl j hj))).range_ge
    exact_mod_cast h6
  cases u with
  | zero =>
    left
    left
    have hb := hbig 0 (Nat.zero_le _)
    have hz' : z ∈ thickening (2 * stageRange T 0) (torusHotSites (Tb.stepParameters y) w) := hz
    obtain ⟨s, hs, hzs⟩ := (mem_thickening _ _ _).mp hz'
    exact containsHotPlaquette_of_near hfit hLn hs (by omega)
  | succ u =>
    have hu : u < K := hA.le
    have hb := hbig (u + 1) hA.le
    have hb0 := hbig u hu.le
    have hrr : stageRange T u ≤ stageRange T (u + 1) + 1 := by
      rw [hlev u hu.le, hlev (u + 1) hA.le]
      exact ((hy₂ _ (le_trans hyy (hfl u hu.le))).stable_nearby.2 _ (hst u hu)).2.2.1
    have hz' : z ∈ coarseHull (Tb.stepParameters y).side (stageRange T u) (stageRange T (u + 1)) w.2.2.2
        (hullSet T u (n * (Tb.stepParameters y).side) w.1)
        (thickening (2 * stageRange T (u + 1)) (torusHotSites (Tb.stepParameters y) w.2.2.1)) := hz
    rcases coarseHull_site_descends hfit hLn (by omega) hrr hb _ _ _ z hz' with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
end YangMills.Construction.HullTrees
end
