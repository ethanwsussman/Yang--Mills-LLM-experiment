import YangMills.Construction.CellOfTheFlow.LongClassesHaveManyUnits
import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.TorusBalls YangMills.Construction.WeightedResponses YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings
section Points
variable {N : ℕ} [NeZero N]
private theorem exists_supDist_near (s : ℕ) (K : Finset (TorusSite N)) {y z : TorusSite N} (hy : y ∈ K)
    (hj : ChainConnected s K y z) : ∀ t, t ≤ _root_.YangMills.Construction.TorusFields.supDist y z → ∃ w ∈ K, t ≤ _root_.YangMills.Construction.TorusFields.supDist y w ∧ _root_.YangMills.Construction.TorusFields.supDist y w ≤ t + s := by
  unfold ChainConnected at hj
  induction hj with
  | refl =>
    intro t ht
    have h0 := _root_.YangMills.Construction.TorusFields.supDist_self y
    exact ⟨y, hy, ht, by omega⟩
  | @tail b c _ step ih =>
    intro t ht
    by_cases h : t ≤ _root_.YangMills.Construction.TorusFields.supDist y b
    · exact ih t h
    · obtain ⟨_, hc, hbc⟩ := step
      have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle y b c
      exact ⟨c, hc, ht, by omega⟩
abbrev _root_.YangMills.SharedProofs.p3024 := @exists_supDist_near
private theorem exists_separated_subset (s D M : ℕ) (K : Finset (TorusSite N)) {y z : TorusSite N} (hy : y ∈ K)
    (hj : ChainConnected s K y z) (hM : (M - 1) * (D + s + 1) ≤ _root_.YangMills.Construction.TorusFields.supDist y z) :
    ∃ P : Finset (TorusSite N), P.card = M ∧ P ⊆ K ∧ ∀ u ∈ P, ∀ v ∈ P, u ≠ v → D < _root_.YangMills.Construction.TorusFields.supDist u v := by
  classical
  have h : ∀ i : ℕ, i < M →
      ∃ w ∈ K, i * (D + s + 1) ≤ _root_.YangMills.Construction.TorusFields.supDist y w ∧ _root_.YangMills.Construction.TorusFields.supDist y w ≤ i * (D + s + 1) + s := by
    intro i hi
    exact exists_supDist_near s K hy hj _ (le_trans (Nat.mul_le_mul_right _ (by omega)) hM)
  choose! w hwK hlo hhi using h
  have hsep : ∀ i j, i < j → j < M → D < _root_.YangMills.Construction.TorusFields.supDist (w i) (w j) := by
    intro i j hij hjM
    have h1 := hhi i (by omega)
    have h2 := hlo j hjM
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle y (w i) (w j)
    have h4 : (i + 1) * (D + s + 1) ≤ j * (D + s + 1) := Nat.mul_le_mul_right _ hij
    have h5 : (i + 1) * (D + s + 1) = i * (D + s + 1) + (D + s + 1) := by ring
    omega
  have hne : ∀ i j, i < M → j < M → i ≠ j → D < _root_.YangMills.Construction.TorusFields.supDist (w i) (w j) := by
    intro i j hi hj' hij
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact hsep i j h' hj'
    · rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      exact hsep j i h' hi
  refine ⟨(Finset.range M).image w, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj' hij
    by_contra hc
    have h1 := hne i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj') hc
    rw [hij, _root_.YangMills.Construction.TorusFields.supDist_self] at h1
    omega
  · intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact hwK i (Finset.mem_range.mp hi)
  · intro u hu v hv huv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj', rfl⟩ := Finset.mem_image.mp hv
    exact hne i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj') fun h => huv (by rw [h])
end Points
section Units
variable {n : ℕ} [NeZero n] (L : ℕ) [NeZero L]
private theorem card_le_supportUnitCount_of_separated {r : ℕ} (hL : L ≤ 8 * r) (θ : ClusterSupport L n)
    (Q : Finset (TorusSite (n * L))) (hQ : Q ⊆ clusterSupportSites L θ)
    (hsep : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → 8 * r < _root_.YangMills.Construction.TorusFields.supDist u v) : Q.card ≤ supportUnitCount L r θ := by
  classical
  have hmem : ballCoverNumber (4 * r) θ.2 ∈
      {k | ∃ C : Finset (TorusSite (n * L)), C.card = k ∧ θ.2 ⊆ thickening (4 * r) C} := by
    unfold ballCoverNumber
    exact Nat.sInf_mem ⟨θ.2.card, θ.2, rfl, fun z hz =>
      (mem_thickening _ _ _).mpr ⟨z, hz, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩⟩
  obtain ⟨C, hC, hcov⟩ := hmem
  have hcentre : ∀ w ∈ θ.2, ∃ c ∈ C, _root_.YangMills.Construction.TorusFields.supDist w c ≤ 4 * r :=
    fun w hw => (mem_thickening _ _ _).mp (hcov hw)
  choose! c hcC hcd using hcentre
  let f : TorusSite (n * L) → TorusSite n ⊕ TorusSite (n * L) := fun w =>
    if w ∈ θ.1.image Prod.fst then Sum.inl (parentBlock L w) else Sum.inr (c w)
  have hsite : ∀ w ∈ Q, w ∉ θ.1.image Prod.fst → w ∈ θ.2 := by
    intro w hw hn
    have := hQ hw
    unfold clusterSupportSites at this
    rcases Finset.mem_union.mp this with h | h
    · exact absurd h hn
    · exact h
  have hmaps : ∀ w ∈ Q, f w ∈ (θ.1.image fun b => parentBlock L b.1).disjSum C := by
    intro w hw
    by_cases h : w ∈ θ.1.image Prod.fst
    · simp only [f, if_pos h]
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
      exact Finset.inl_mem_disjSum.mpr (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    · simp only [f, if_neg h]
      exact Finset.inr_mem_disjSum.mpr (hcC w (hsite w hw h))
  have hinj : Set.InjOn f Q := by
    intro u hu v hv huv
    by_contra hne
    have hd := hsep u hu v hv hne
    by_cases h1 : u ∈ θ.1.image Prod.fst <;> by_cases h2 : v ∈ θ.1.image Prod.fst
    · simp only [f, if_pos h1, if_pos h2, Sum.inl.injEq] at huv
      have := _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq L huv
      omega
    · simp only [f, if_pos h1, if_neg h2, reduceCtorEq] at huv
    · simp only [f, if_neg h1, if_pos h2, reduceCtorEq] at huv
    · simp only [f, if_neg h1, if_neg h2, Sum.inr.injEq] at huv
      have e1 := hcd u (hsite u hu h1)
      have e2 := hcd v (hsite v hv h2)
      have e3 := _root_.YangMills.Construction.TorusFields.supDist_triangle u (c u) v
      rw [huv, _root_.YangMills.Construction.TorusFields.supDist_comm (c v) v] at e3
      rw [huv] at e1
      omega
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_disjSum] at hcard
  unfold supportUnitCount badBlockCount
  omega
private theorem le_supDist_sitesInBlocks (hL : 2 ≤ L) {c c' : Finset (TorusSite n)} {A : ℕ}
    (h : ∀ x ∈ c, ∀ x' ∈ c', A + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist x x') :
    ∀ u ∈ sitesInBlocks L c, ∀ u' ∈ sitesInBlocks L c', L * A + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist u u' := by
  intro u hu u' hu'
  have h1 := h _ (Finset.mem_filter.mp hu).2 _ (Finset.mem_filter.mp hu').2
  have h2 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one L u u'
  have h3 : A + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist u u' / L := by omega
  have h4 : (A + 1) * L ≤ _root_.YangMills.Construction.TorusFields.supDist u u' := (Nat.le_div_iff_mul_le (by omega)).mp h3
  have h5 : (A + 1) * L = L * A + L := by ring
  omega
end Units
private theorem le_supDist_cellBelow (L : ℕ) [NeZero L] (hL : 2 ≤ L) : ∀ (d n : ℕ) [NeZero n]
    (c c' : Finset (TorusSite n)) (A : ℕ), (∀ x ∈ c, ∀ x' ∈ c', A + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist x x') →
    ∀ u ∈ cellBelow L d n c, ∀ u' ∈ cellBelow L d n c', L ^ d * A + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist u u'
  | 0, n, _, c, c', A, h => by
    intro u hu u' hu'
    have h1 : A + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist (n := n) u u' := h u hu u' hu'
    rw [pow_zero, one_mul]
    exact h1
  | d + 1, n, _, c, c', A, h => by
    intro u hu u' hu'
    have h1 := le_supDist_cellBelow L hL d (n * L) (sitesInBlocks L c) (sitesInBlocks L c') (L * A)
      (le_supDist_sitesInBlocks L hL h) u hu u' hu'
    have h2 : L ^ (d + 1) * A = L ^ d * (L * A) := by ring
    rw [h2]
    exact h1
private theorem le_supDist_cells_of_same_parity (G : CellGrid) {n : ℕ} [NeZero n] (hs : 0 < G.side)
    (hd : 2 * G.side ∣ n) {κ κ₁ κ₂ : Fin 4 → ℤ} (h₁ : κ₁ ∈ G.sameParityIndices n κ)
    (h₂ : κ₂ ∈ G.sameParityIndices n κ) (hne : κ₁ ≠ κ₂) :
    ∀ x ∈ G.cell n κ₁, ∀ x' ∈ G.cell n κ₂, G.side + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist x x' := by
  classical
  intro x hx x' hx'
  obtain ⟨p, hp⟩ := hd
  have hn0 : n ≠ 0 := NeZero.ne n
  have hq : n / G.side = 2 * p := by
    rw [hp]
    exact Nat.div_eq_of_eq_mul_right hs (by ring)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have m₁ := Finset.mem_filter.mp h₁
  have m₂ := Finset.mem_filter.mp h₂
  have b₁ := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp m₁.1 i)
  have b₂ := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp m₂.1 i)
  rw [hq] at b₁ b₂
  obtain ⟨a₁, ha₁⟩ := m₁.2 i
  obtain ⟨a₂, ha₂⟩ := m₂.2 i
  obtain ⟨h, hh, rfl⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨h', hh', rfl⟩ := (Finset.mem_filter.mp hx').2
  set z : ℤ := (G.side : ℤ) * (κ₁ i - κ₂ i) + (h i - h' i) with hz
  have hval : (siteOfInt (fun i => G.offset i + (G.side : ℤ) * κ₁ i + h i) : TorusSite n) i -
      (siteOfInt (fun i => G.offset i + (G.side : ℤ) * κ₂ i + h' i) : TorusSite n) i = ((z : ℤ) : ZMod n) := by
    simp only [siteOfInt, hz]
    push_cast
    ring
  have hle : (((siteOfInt (fun i => G.offset i + (G.side : ℤ) * κ₁ i + h i) : TorusSite n) i -
      (siteOfInt (fun i => G.offset i + (G.side : ℤ) * κ₂ i + h' i) : TorusSite n) i).valMinAbs).natAbs ≤
      _root_.YangMills.Construction.TorusFields.supDist (siteOfInt (fun i => G.offset i + (G.side : ℤ) * κ₁ i + h i) : TorusSite n)
        (siteOfInt (fun i => G.offset i + (G.side : ℤ) * κ₂ i + h' i) : TorusSite n) :=
    Finset.le_sup (f := fun i => (((siteOfInt (fun i => G.offset i + (G.side : ℤ) * κ₁ i + h i) : TorusSite n) i -
      (siteOfInt (fun i => G.offset i + (G.side : ℤ) * κ₂ i + h' i) : TorusSite n) i).valMinAbs).natAbs)
      (Finset.mem_univ i)
  rw [hval] at hle
  refine le_trans ?_ hle
  set v : ℤ := ((z : ℤ) : ZMod n).valMinAbs with hv
  have hcast : ((v : ℤ) : ZMod n) = ((z : ℤ) : ZMod n) := ZMod.coe_valMinAbs _
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
  have hnz : (n : ℤ) = 2 * (G.side : ℤ) * (p : ℤ) := by rw [hp]; push_cast; ring
  set m : ℤ := a₁ - a₂ with hm
  have hdiff : κ₁ i - κ₂ i = 2 * m := by rw [hm]; linarith
  have hm0 : m ≠ 0 := by
    intro h0
    apply hi
    rw [h0] at hdiff
    linarith
  have hmp : |m| < (p : ℤ) := by
    rw [abs_lt]
    push_cast at b₁ b₂
    constructor <;> linarith [b₁.1, b₁.2, b₂.1, b₂.2]
  set u : ℤ := m - (p : ℤ) * t with hu
  have hu0 : u ≠ 0 := by
    intro h0
    have hdvd : (p : ℤ) ∣ m := ⟨t, by rw [hu] at h0; linarith⟩
    exact hm0 (Int.eq_zero_of_abs_lt_dvd hdvd hmp)
  have hvu : v = 2 * (G.side : ℤ) * u + (h i - h' i) := by
    have e1 : z - v = (n : ℤ) * t := ht
    have e2 : z = (G.side : ℤ) * (2 * m) + (h i - h' i) := by rw [hz, hdiff]
    rw [hnz] at e1
    rw [hu]
    linear_combination e2 - e1
  have c₁ := hh i
  have c₂ := hh' i
  rcases lt_or_gt_of_ne hu0 with hneg | hpos
  · have e3 : (G.side : ℤ) * u ≤ -(G.side : ℤ) := by nlinarith
    have e4 : v ≤ -((G.side : ℤ) + 1) := by linarith [c₁.1, c₁.2, c₂.1, c₂.2]
    omega
  · have e3 : (G.side : ℤ) ≤ (G.side : ℤ) * u := by nlinarith
    have e4 : (G.side : ℤ) + 1 ≤ v := by linarith [c₁.1, c₁.2, c₂.1, c₂.2]
    omega
private theorem le_clusterRange_of_pow_le {L : ℕ} {x : ℝ} (h : (L : ℝ) ^ 100 ≤ x) : L ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem mul_card_le_supportUnitCount (L : ℕ) [NeZero L] (hL : 2 ≤ L) (r rk d e ρ : ℕ) (hLr : L ≤ r)
    (hrk : 1 ≤ rk) (hrr : r ≤ rk + (d + 1)) (G : CellGrid) (κ : Fin 4 → ℤ) (S : Finset (Fin 4 → ℤ))
    (θ : ClusterSupport L (fineSide L d (2 * L ^ e))) (hside : G.side = baseCellSide L rk)
    (hle : 2 * G.side ≤ 2 * L ^ e) (hS : S ⊆ G.sameParityIndices (2 * L ^ e) κ)
    (hlong : ∀ κ' ∈ S, IsLongWithin L r (2 ^ 12 * r * (d + 1)) θ
      (sitesInBlocks L (interiorAtDepth ρ (cellBelow L d (2 * L ^ e) (G.cell (2 * L ^ e) κ'))))) :
    100 * (d + 1) * S.card ≤ supportUnitCount L r θ := by
  classical
  have hr1 : 1 ≤ r := by omega
  have hs0 : 0 < G.side := by
    rw [hside]
    exact pow_pos (by omega) _
  have hsk : 2 ^ 7 * rk ≤ G.side := by
    rw [hside]
    exact Nat.le_pow_clog (by omega) _
  have hfit : 2 * G.side ∣ 2 * L ^ e := by
    refine Nat.mul_dvd_mul_left 2 ?_
    have h1 : G.side ≤ L ^ e := by omega
    rw [hside] at h1 ⊢
    exact pow_dvd_pow L ((Nat.pow_le_pow_iff_right (by omega)).mp h1)
  have hP : ∀ κ' ∈ S, ∃ P : Finset (TorusSite (fineSide L d (2 * L ^ e) * L)), P.card = 100 * (d + 1) ∧
      (∀ u ∈ P, u ∈ clusterSupportSites L θ ∧
        u ∈ sitesInBlocks L (interiorAtDepth ρ (cellBelow L d (2 * L ^ e) (G.cell (2 * L ^ e) κ')))) ∧
      ∀ u ∈ P, ∀ v ∈ P, u ≠ v → 8 * r < _root_.YangMills.Construction.TorusFields.supDist u v := by
    intro κ' hκ'
    obtain ⟨K, hKs, hKne, hKj, hKg⟩ := hlong κ' hκ'
    obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_eq_sup K hKne fun y => K.sup fun z => _root_.YangMills.Construction.TorusFields.supDist y z
    obtain ⟨z, hz, hz'⟩ := Finset.exists_mem_eq_sup K hKne fun z => _root_.YangMills.Construction.TorusFields.supDist y z
    have hdiam : siteDiameter K = _root_.YangMills.Construction.TorusFields.supDist y z := by
      unfold siteDiameter
      rw [hy', hz']
    rw [hdiam] at hKg
    have hM : (100 * (d + 1) - 1) * (8 * r + 10 * r + 1) ≤ _root_.YangMills.Construction.TorusFields.supDist y z := by
      have h1 : (100 * (d + 1) - 1) * (8 * r + 10 * r + 1) ≤ (100 * (d + 1)) * (19 * r) :=
        Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    obtain ⟨P, hPc, hPK, hPd⟩ :=
      exists_separated_subset (10 * r) (8 * r) (100 * (d + 1)) K hy (hKj y hy z hz) hM
    refine ⟨P, hPc, fun u hu => ?_, hPd⟩
    exact Finset.mem_inter.mp (hKs (hPK hu))
  choose! P hPc hPs hPd using hP
  have hfar : ∀ κ₁ ∈ S, ∀ κ₂ ∈ S, κ₁ ≠ κ₂ → ∀ u ∈ P κ₁, ∀ v ∈ P κ₂, 8 * r < _root_.YangMills.Construction.TorusFields.supDist u v := by
    intro κ₁ h₁ κ₂ h₂ hne u hu v hv
    have hA : ∀ x ∈ G.cell (2 * L ^ e) κ₁, ∀ x' ∈ G.cell (2 * L ^ e) κ₂, (G.side - 1) + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist x x' := by
      intro x hx x' hx'
      have := le_supDist_cells_of_same_parity G hs0 hfit (hS h₁) (hS h₂) hne x hx x' hx'
      omega
    have hB := le_supDist_cellBelow L hL d (2 * L ^ e) _ _ (G.side - 1) hA
    have hC : ∀ x ∈ interiorAtDepth ρ (cellBelow L d (2 * L ^ e) (G.cell (2 * L ^ e) κ₁)),
        ∀ x' ∈ interiorAtDepth ρ (cellBelow L d (2 * L ^ e) (G.cell (2 * L ^ e) κ₂)),
        L ^ d * (G.side - 1) + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist x x' :=
      fun x hx x' hx' => hB x (Finset.mem_filter.mp hx).1 x' (Finset.mem_filter.mp hx').1
    have hD := le_supDist_sitesInBlocks L hL hC u (hPs κ₁ h₁ u hu).2 v (hPs κ₂ h₂ v hv).2
    have hpow : d + 2 ≤ L ^ (d + 1) :=
      (Nat.lt_two_pow_self (n := d + 1)).trans_le (Nat.pow_le_pow_left hL _)
    have hW : L * (L ^ d * (G.side - 1)) = L ^ (d + 1) * (G.side - 1) := by ring
    have hA1 : 127 * rk ≤ G.side - 1 := by omega
    have hW2 : (d + 2) * (127 * rk) ≤ L ^ (d + 1) * (G.side - 1) := Nat.mul_le_mul hpow hA1
    have hW3 : (d + 2) * 127 ≤ (d + 2) * (127 * rk) := Nat.mul_le_mul_left _ (by omega)
    have hW4 : 2 * (127 * rk) ≤ (d + 2) * (127 * rk) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hdisj : ∀ κ₁ ∈ S, ∀ κ₂ ∈ S, κ₁ ≠ κ₂ → Disjoint (P κ₁) (P κ₂) := by
    intro κ₁ h₁ κ₂ h₂ hne
    refine Finset.disjoint_left.mpr fun u hu hv => ?_
    have := hfar κ₁ h₁ κ₂ h₂ hne u hu u hv
    rw [_root_.YangMills.Construction.TorusFields.supDist_self] at this
    omega
  have hcard : (S.biUnion P).card = 100 * (d + 1) * S.card := by
    rw [Finset.card_biUnion fun a ha b hb hab => hdisj a ha b hb hab,
      Finset.sum_congr rfl fun κ' hκ' => hPc κ' hκ', Finset.sum_const, smul_eq_mul]
    ring
  rw [← hcard]
  refine card_le_supportUnitCount_of_separated L (by omega) θ _ ?_ ?_
  · intro u hu
    obtain ⟨κ', hκ', huP⟩ := Finset.mem_biUnion.mp hu
    exact (hPs κ' hκ' u huP).1
  · intro u hu v hv huv
    obtain ⟨κ₁, h₁, huP⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨κ₂, h₂, hvP⟩ := Finset.mem_biUnion.mp hv
    by_cases hκ : κ₁ = κ₂
    · subst hκ
      exact hPd κ₁ h₁ u huP v hvP huv
    · exact hfar κ₁ h₁ κ₂ h₂ hκ u huP v hvP
theorem longSupportUnitCount : longSupportUnitCountStatement := by
  intro a _
  refine ⟨2, fun _ => 1, fun _ => one_pos, fun L _ _ Tb _ _ hD _ => ⟨(Tb.side : ℝ) ^ 100, fun y hy _ _ => ?_⟩⟩
  intro T β j d hrun e G κ S θ hside hle hS hlong
  have hL : 2 ≤ (Tb.stepParameters y).side := le_trans (by norm_num) hD.L_ge
  have hon := hrun.onFamily.onFamily
  have hrange : ∀ i ≤ j + 1 + d, (Tb.stepParameters y).side ≤ stageRange T i := fun i hi =>
    le_clusterRange_of_pow_le (hy.trans (hon i hi).le_coupling)
  have hstep : ∀ i ≤ j + 1 + d, stageRange T i ≤ stageRange T (i + 1) + 1 := fun i hi =>
    (hon i hi).isStep.2.2
  have hdown : ∀ m ≤ d + 1, stageRange T j ≤ stageRange T (j + m) + m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hstep (j + m) (by omega)
      have h3 : j + (m + 1) = j + m + 1 := by ring
      rw [h3]
      omega
  have hjk : j + (d + 1) = j + 1 + d := by ring
  have hrr := hdown (d + 1) le_rfl
  rw [hjk] at hrr
  have hrk := hrange (j + 1 + d) le_rfl
  have hw : windowLength T (j + 1 + d) j = 2 ^ 12 * stageRange T j * (d + 1) := by
    unfold windowLength
    congr 1
    omega
  refine mul_card_le_supportUnitCount (Tb.stepParameters y).side hL (stageRange T j) (stageRange T (j + 1 + d)) d e
    (blockDepth T (j + 1 + d) j) (hrange j (by omega)) (by omega) hrr G κ S θ hside hle hS ?_
  intro κ' hκ'
  have := hlong κ' hκ'
  rwa [hw] at this
end YangMills.Construction.CellWindows
end
