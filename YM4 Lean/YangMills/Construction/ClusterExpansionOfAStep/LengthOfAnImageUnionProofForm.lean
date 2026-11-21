import YangMills.Construction.ClusterExpansionOfAStep.NearSitesOfAClassProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open TorusFields
namespace ImageUnionLength
variable {n : ℕ}
theorem supDist_parentBlock_le_div_add_one [NeZero n] (L : ℕ) [NeZero L] (x x' : TorusSite (n * L)) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock L x) (parentBlock L x') ≤ _root_.YangMills.Construction.TorusFields.supDist x x' / L + 1 := by apply _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one <;> assumption
theorem exists_chainConnected_supDist_mem_Ico {m : ℕ} [NeZero m] {s : ℕ} (hs : 0 < s)
    {Y : Finset (TorusSite m)} {u v : TorusSite m}
    (h : ChainConnected s Y u v) (a : ℕ) (ha : a ≤ _root_.YangMills.Construction.TorusFields.supDist u v) :
    ∃ p, ChainConnected s Y u p ∧ a ≤ _root_.YangMills.Construction.TorusFields.supDist u p ∧ _root_.YangMills.Construction.TorusFields.supDist u p < a + s := by
  induction h with
  | refl =>
    refine ⟨u, Relation.ReflTransGen.refl, ha, ?_⟩
    rw [_root_.YangMills.Construction.TorusFields.supDist_self]
    omega
  | @tail b c hb hst ih =>
    by_cases h1 : a ≤ _root_.YangMills.Construction.TorusFields.supDist u b
    · exact ih h1
    · refine ⟨c, hb.tail hst, ha, ?_⟩
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle u b c
      omega
theorem exists_separated_net [NeZero n] (d : ℕ) (A : Finset (TorusSite n)) :
    ∃ B ⊆ A, (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → d < _root_.YangMills.Construction.TorusFields.supDist b b') ∧ ∀ a ∈ A, ∃ b ∈ B, _root_.YangMills.Construction.TorusFields.supDist a b ≤ d := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, subset_rfl, by simp, by simp⟩
  | insert a A _ ih =>
    obtain ⟨B, hBA, hsep, hcov⟩ := ih
    by_cases h : ∃ b ∈ B, _root_.YangMills.Construction.TorusFields.supDist a b ≤ d
    · refine ⟨B, hBA.trans (Finset.subset_insert _ _), hsep, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with hx | hx
      · rw [hx]
        exact h
      · exact hcov x hx
    · push Not at h
      refine ⟨insert a B, Finset.insert_subset_insert _ hBA, ?_, ?_⟩
      · intro b hb b' hb' hne
        rcases Finset.mem_insert.mp hb with hb | hb <;> rcases Finset.mem_insert.mp hb' with hb' | hb'
        · exact absurd (hb.trans hb'.symm) hne
        · rw [hb]
          exact h _ hb'
        · rw [hb', _root_.YangMills.Construction.TorusFields.supDist_comm]
          exact h _ hb
        · exact hsep _ hb _ hb' hne
      · intro x hx
        rcases Finset.mem_insert.mp hx with hx | hx
        · exact ⟨x, Finset.mem_insert.mpr (Or.inl hx), by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
        · obtain ⟨b, hb, hxb⟩ := hcov x hx
          exact ⟨b, Finset.mem_insert_of_mem hb, hxb⟩
theorem ballCoverNumber_le_card [NeZero n] {m : ℕ} {X C : Finset (TorusSite n)} (h : X ⊆ thickening m C) :
    ballCoverNumber m X ≤ C.card :=
  Nat.sInf_le ⟨C, rfl, h⟩
theorem exists_card_eq_ballCoverNumber [NeZero n] (m : ℕ) (X : Finset (TorusSite n)) :
    ∃ C : Finset (TorusSite n), C.card = ballCoverNumber m X ∧ X ⊆ thickening m C := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.exists_cover_card_eq_ballCoverNumber <;> assumption
theorem excessLength_le_card [NeZero n] (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (r : ℕ) (X : Finset (TorusSite n))
    (V : TorusField n) (D : Finset (TorusSite n))
    (h : ∀ y ∈ X, (∃ l ∈ torusHotLumps ℓ V, l ⊆ X ∧ _root_.YangMills.Construction.TorusFields.supDist y (lumpCenter l) ≤ 4 * r) ∨
      y ∈ thickening (4 * r) D) :
    excessLength ℓ r X V ≤ D.card := by
  classical
  unfold excessLength
  refine ballCoverNumber_le_card fun y hy => ?_
  obtain ⟨hyX, hyn⟩ := Finset.mem_sdiff.mp hy
  rcases h y hyX with ⟨l, hl, hlX, hd⟩ | h'
  · exact absurd ((mem_thickening _ _ _).mpr ⟨lumpCenter l,
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hl, hlX⟩), hd⟩) hyn
  · exact h'
theorem exists_cover_card_le_add_excessLength [NeZero n] (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (r : ℕ)
    (U : Finset (TorusSite n)) (W : TorusField n)
    (H : Finset (Finset (TorusSite n))) (hH : ∀ l ∈ torusHotLumps ℓ W, l ⊆ U → l ∈ H) :
    ∃ M : Finset (TorusSite n), M.card ≤ H.card + excessLength ℓ r U W ∧ U ⊆ thickening (4 * r) M := by
  classical
  unfold excessLength
  obtain ⟨D, hDcard, hD⟩ := exists_card_eq_ballCoverNumber (4 * r)
    (U \ thickening (4 * r) (((torusHotLumps ℓ W).filter (· ⊆ U)).image lumpCenter))
  refine ⟨H.image lumpCenter ∪ D, ?_, fun p hp => ?_⟩
  · rw [← hDcard]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right Finset.card_image_le _)
  · by_cases hpm : p ∈ thickening (4 * r) (((torusHotLumps ℓ W).filter (· ⊆ U)).image lumpCenter)
    · obtain ⟨c, hc, hpc⟩ := (mem_thickening _ _ _).mp hpm
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hl1, hl2⟩ := Finset.mem_filter.mp hl
      exact (mem_thickening _ _ _).mpr ⟨lumpCenter l,
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hH l hl1 hl2)), hpc⟩
    · obtain ⟨c, hc, hpc⟩ := (mem_thickening _ _ _).mp (hD (Finset.mem_sdiff.mpr ⟨hp, hpm⟩))
      exact (mem_thickening _ _ _).mpr ⟨c, Finset.mem_union_right _ hc, hpc⟩
theorem supDist_lumpCenter_le [NeZero n] {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    {V : TorusField n} {l : Finset (TorusSite n)} (hl : l ∈ torusHotLumps ℓ V) {y : TorusSite n} (hy : y ∈ l) :
    _root_.YangMills.Construction.TorusFields.supDist y (lumpCenter l) ≤ 2 ^ 14 := by
  obtain ⟨_, _, _, _, _, u, _, hlu⟩ := (mem_torusHotLumps_iff ℓ hfit hLn V l).mp hl
  have hm : ∃ m : TorusSite n, ∀ y ∈ l, _root_.YangMills.Construction.TorusFields.supDist y m ≤ 2 ^ 14 := by
    rw [hlu]
    exact exists_centre_of_torusLumpOf hfit hLn u
  unfold lumpCenter
  rw [dif_pos hm]
  exact hm.choose_spec y hy
theorem card_mul_le_of_long_chains [NeZero n] (L : ℕ) [NeZero L] {r r' m : ℕ} (hr : 1 ≤ r)
    (hclose : (2 * (L * r' + 10 * r) + 8 * r) / L + 1 ≤ 3 * r') (hm : 20 * r * m ≤ L * r')
    {G Cn : Finset (TorusSite (n * L))} {B : Finset (TorusSite n)} (u : TorusSite n → TorusSite (n * L))
    (hsep : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → 3 * r' < _root_.YangMills.Construction.TorusFields.supDist b b')
    (hblock : ∀ b ∈ B, parentBlock L (u b) = b)
    (hend : ∀ b ∈ B, ∃ v, ChainConnected (10 * r) G (u b) v ∧ L * r' + 10 * r ≤ _root_.YangMills.Construction.TorusFields.supDist (u b) v)
    (hcov : ∀ b ∈ B, ∀ p, ChainConnected (10 * r) G (u b) p → _root_.YangMills.Construction.TorusFields.supDist (u b) p < L * r' + 10 * r →
      p ∈ thickening (4 * r) Cn) :
    B.card * (m + 1) ≤ Cn.card := by
  classical
  have hpick : ∀ b ∈ B, ∀ j ≤ m, ∃ c ∈ Cn, ∃ p, _root_.YangMills.Construction.TorusFields.supDist p c ≤ 4 * r ∧ 20 * r * j ≤ _root_.YangMills.Construction.TorusFields.supDist (u b) p ∧
      _root_.YangMills.Construction.TorusFields.supDist (u b) p < 20 * r * j + 10 * r := by
    intro b hb j hj
    obtain ⟨v, hv, hd⟩ := hend b hb
    have hjm : 20 * r * j ≤ 20 * r * m := Nat.mul_le_mul_left _ hj
    obtain ⟨p, hp, h1, h2⟩ := exists_chainConnected_supDist_mem_Ico (by omega) hv (20 * r * j) (by omega)
    obtain ⟨c, hc, hpc⟩ := (mem_thickening _ _ _).mp (hcov b hb p hp (by omega))
    exact ⟨c, hc, p, hpc, h1, h2⟩
  choose! c hc p hpc hlo hhi using hpick
  have hlt : ∀ b ∈ B, ∀ j j', j ≤ m → j' ≤ m → j < j' → c b j ≠ c b j' := by
    intro b hb j j' hj hj' hjj heq
    have h1 := hpc b hb j hj
    have h2 := hpc b hb j' hj'
    rw [← heq] at h2
    have h3 := hhi b hb j hj
    have h4 := hlo b hb j' hj'
    have h5 : 20 * r * (j + 1) ≤ 20 * r * j' := Nat.mul_le_mul_left _ hjj
    have h6 : 20 * r * (j + 1) = 20 * r * j + 20 * r := by ring
    have h7 := _root_.YangMills.Construction.TorusFields.supDist_triangle (u b) (p b j) (p b j')
    have h8 := _root_.YangMills.Construction.TorusFields.supDist_triangle (p b j) (c b j) (p b j')
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm (c b j) (p b j')] at h8
    omega
  have hcard : (B ×ˢ Finset.range (m + 1)).card ≤ Cn.card := by
    refine Finset.card_le_card_of_injOn (fun x => c x.1 x.2) ?_ ?_
    · rintro ⟨b, j⟩ hx
      obtain ⟨hb, hj⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hx)
      exact hc b hb j (by simpa [Nat.lt_succ_iff] using hj)
    · rintro ⟨b, j⟩ hx ⟨b', j'⟩ hx' heq
      obtain ⟨hb, hj⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hx)
      obtain ⟨hb', hj'⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hx')
      have hjm : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
      have hjm' : j' ≤ m := by simpa [Nat.lt_succ_iff] using hj'
      have heq' : c b j = c b' j' := heq
      by_cases hbb : b = b'
      · subst hbb
        rcases lt_trichotomy j j' with h | h | h
        · exact absurd heq' (hlt b hb j j' hjm hjm' h)
        · rw [h]
        · exact absurd heq'.symm (hlt b hb j' j hjm' hjm h)
      · exfalso
        have h1 := hpc b hb j hjm
        have h2 := hpc b' hb' j' hjm'
        rw [← heq'] at h2
        have h3 := hhi b hb j hjm
        have h4 := hhi b' hb' j' hjm'
        have h5 : 20 * r * j ≤ 20 * r * m := Nat.mul_le_mul_left _ hjm
        have h6 : 20 * r * j' ≤ 20 * r * m := Nat.mul_le_mul_left _ hjm'
        have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (u b) (p b j) (u b')
        have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (p b j) (c b j) (u b')
        have t3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (c b j) (p b' j') (u b')
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm (c b j) (p b' j'), _root_.YangMills.Construction.TorusFields.supDist_comm (p b' j') (u b')] at t3
        have hd : _root_.YangMills.Construction.TorusFields.supDist (u b) (u b') ≤ 2 * (L * r' + 10 * r) + 8 * r := by omega
        have hbl := _root_.YangMills.Construction.TorusLumps.ImageUnionLength.supDist_parentBlock_le_div_add_one L (u b) (u b')
        rw [hblock b hb, hblock b' hb'] at hbl
        have hdiv := Nat.div_le_div_right (c := L) hd
        have := hsep b hb b' hb' hbb
        omega
  simpa [Finset.card_product] using hcard
theorem excessLength_biUnion_le (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hfit : ℓ.Admissible) {r r' : ℕ} (hr1 : 1 ≤ r)
    (hrr : r ≤ r' + 1) (hr' : 2 ^ 16 ≤ r')
    {n : ℕ} [NeZero n] (hLn : ℓ.side ∣ n) (V : TorusField n) (W : TorusField (n * ℓ.side))
    (bad : Finset (TorusBond (n * ℓ.side)))
    (Yt : Finset (TorusSite (n * ℓ.side))) (P : Finset (Finset (TorusSite n)))
    (hP : P ⊆ chainComponents r' (coarseHull ℓ.side r r' bad Yt (thickening (2 * r') (torusHotSites ℓ V))))
    (H : Finset (Finset (TorusSite (n * ℓ.side))))
    (hH : ∀ l ∈ torusHotLumps ℓ W,
      l ⊆ attachedInBlocks ℓ.side r bad Yt (thickening (2 * r') (torusHotSites ℓ V)) (P.biUnion id) → l ∈ H) :
    ∃ b : ℕ, excessLength ℓ r' (P.biUnion id) V ≤
        (badBlocksOff ℓ.side bad (thickening (2 * r') (torusHotSites ℓ V))
          (attachedInBlocks ℓ.side r bad Yt (thickening (2 * r') (torusHotSites ℓ V)) (P.biUnion id))).card + b ∧
      b * ℓ.side ≤ 40 * (H.card + excessLength ℓ r (componentsWithin ℓ.side r Yt
        (attachedInBlocks ℓ.side r bad Yt (thickening (2 * r') (torusHotSites ℓ V)) (P.biUnion id))) W) := by
  classical
  set C := thickening (2 * r') (torusHotSites ℓ V) with hC
  set Y' := coarseHull ℓ.side r r' bad Yt C with hY'
  set X := P.biUnion id with hX
  set Z := storedBlocks ℓ.side r bad Yt C with hZ
  set A := attachedSites ℓ.side r bad Yt C with hA
  set K := attachedInBlocks ℓ.side r bad Yt C X with hK
  set G := bad.image Prod.fst ∪ Yt ∪ sitesInBlocks ℓ.side C with hG
  set Bd := badBlocksOff ℓ.side bad C K with hBd
  set U := componentsWithin ℓ.side r Yt K with hU
  have hLbig : 2 ^ 16 ≤ ℓ.side := hfit.L_ge
  have hLpos : 0 < ℓ.side := by omega
  have hdiv : ∀ d, d / ℓ.side ≤ d / 65536 := fun d => Nat.div_le_div_left (by omega) (by norm_num)
  have hZY : Z ⊆ Y' := fun z hz => (mem_thickening _ _ _).mpr ⟨z, hz, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
  have hCZ : C ⊆ Z := Finset.subset_union_left
  have hsub : thickening (2 * r') (torusHotSites ℓ V) ⊆ Y' := hCZ.trans hZY
  have hsmall : ∀ d, d ≤ 10 * r → d / ℓ.side + 1 ≤ r' := by
    intro d hd
    have h1 := hdiv d
    omega
  have hclosed : ∀ {a b : TorusSite n}, a ∈ X → b ∈ Y' → ChainConnected r' Y' a b → b ∈ X := by
    intro a b ha hb hj
    obtain ⟨Xc, hXc, haXc⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨Xc, hXc, mem_of_chainConnected_of_mem_chainComponents (hP hXc) haXc hb hj⟩
  have hAZ : ∀ v ∈ A, parentBlock ℓ.side v ∈ Z := by
    intro v hv
    refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, ?_⟩)
    refine Finset.mem_inter.mpr ⟨?_, (mem_thickening _ _ _).mpr ⟨v, hv, ?_⟩⟩
    · simp [sitesInBlocks]
    · rw [_root_.YangMills.Construction.TorusFields.supDist_self]
      omega
  have hAG : ∀ {v}, v ∈ A → v ∈ G := by
    intro v hv
    obtain ⟨Ac, hAc, hvAc⟩ := Finset.mem_biUnion.mp hv
    exact subset_of_mem_chainComponents (Finset.mem_filter.mp hAc).1 hvAc
  have hchain : ∀ u ∈ A, ∀ v, ChainConnected (10 * r) G u v →
      v ∈ A ∧ ChainConnected r' Y' (parentBlock ℓ.side u) (parentBlock ℓ.side v) := by
    intro u hu v huv
    obtain ⟨Ac, hAc, huAc⟩ := Finset.mem_biUnion.mp hu
    have hAcl := (Finset.mem_filter.mp hAc).1
    induction huv with
    | refl => exact ⟨hu, Relation.ReflTransGen.refl⟩
    | tail hab hs ih =>
      obtain ⟨ihA, ihJ⟩ := ih
      have hw := mem_of_chainConnected_of_mem_chainComponents hAcl huAc hs.2.1 (Relation.ReflTransGen.tail hab hs)
      have hwA : _ ∈ A := Finset.mem_biUnion.mpr ⟨Ac, hAc, hw⟩
      refine ⟨hwA, ihJ.trans (chainConnected_of_supDist_le (hZY (hAZ _ ihA)) (hZY (hAZ _ hwA)) ?_)⟩
      exact (_root_.YangMills.Construction.TorusLumps.ImageUnionLength.supDist_parentBlock_le_div_add_one ℓ.side _ _).trans (hsmall _ hs.2.2)
  have hlump : ∀ c ∈ C, c ∈ X →
      ∃ l ∈ torusHotLumps ℓ V, l ⊆ X ∧ _root_.YangMills.Construction.TorusFields.supDist c (lumpCenter l) ≤ 2 * r' + 2 ^ 14 := by
    intro c hcC hcX
    obtain ⟨s, hs, hcs⟩ := (mem_thickening _ _ _).mp hcC
    obtain ⟨l, hl, hsl⟩ := mem_torusHotSites_iff.mp hs
    have hj : ChainConnected r' Y' s c := chainConnected_of_supDist_le_two_mul (P := ℓ) (U := V) hsub hs hcs
    have hsY : s ∈ Y' := hsub ((mem_thickening _ _ _).mpr ⟨s, hs, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
    have hsX : s ∈ X := hclosed hcX hsY (chainConnected_symm hj)
    obtain ⟨Xc, hXc, hsXc⟩ := Finset.mem_biUnion.mp hsX
    have hlXc : l ⊆ Xc := subset_of_mem_torusHotLumps_of_mem hfit hLn hr' hsub (hP hXc) hl hsl hsXc
    refine ⟨l, hl, fun w hw => Finset.mem_biUnion.mpr ⟨Xc, hXc, hlXc hw⟩, ?_⟩
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle c s (lumpCenter l)
    have h2 := _root_.YangMills.Construction.TorusLumps.ImageUnionLength.supDist_lumpCenter_le hfit hLn hl hsl
    omega
  let Near : TorusSite n → Prop := fun z =>
    (∃ l ∈ torusHotLumps ℓ V, l ⊆ X ∧ _root_.YangMills.Construction.TorusFields.supDist z (lumpCenter l) ≤ 4 * r' - r' / 2) ∨
      ∃ b ∈ Bd, _root_.YangMills.Construction.TorusFields.supDist z b ≤ 4 * r' - r' / 2
  have hcore : ∀ z ∈ Z, z ∈ X → ¬ Near z →
      ∃ u ∈ A, parentBlock ℓ.side u ∈ X ∧ _root_.YangMills.Construction.TorusFields.supDist z (parentBlock ℓ.side u) ≤ 4 * r / 65536 + 1 := by
    intro z hzZ hzX hn
    rcases Finset.mem_union.mp hzZ with hzC | hzc
    · exfalso
      obtain ⟨l, hl, hlX, hd⟩ := hlump z hzC hzX
      exact hn (Or.inl ⟨l, hl, hlX, by omega⟩)
    · obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hzc).2
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      have hbx : parentBlock ℓ.side x = z := by simpa [sitesInBlocks] using hx1
      obtain ⟨a, ha, hxa⟩ := (mem_thickening _ _ _).mp hx2
      have hzb : _root_.YangMills.Construction.TorusFields.supDist z (parentBlock ℓ.side a) ≤ 4 * r / 65536 + 1 := by
        rw [← hbx]
        have h1 := _root_.YangMills.Construction.TorusLumps.ImageUnionLength.supDist_parentBlock_le_div_add_one ℓ.side x a
        have h2 := Nat.div_le_div_right (c := ℓ.side) hxa
        have h3 := hdiv (4 * r)
        omega
      have haX : parentBlock ℓ.side a ∈ X := hclosed hzX (hZY (hAZ a ha))
        (chainConnected_of_supDist_le (hZY hzZ) (hZY (hAZ a ha)) (by omega))
      exact ⟨a, ha, haX, hzb⟩
  have hfar : ∀ z u, ¬ Near z → u ∈ A → parentBlock ℓ.side u ∈ X →
      _root_.YangMills.Construction.TorusFields.supDist z (parentBlock ℓ.side u) ≤ 4 * r / 65536 + 1 → ∀ p, ChainConnected (10 * r) G u p →
      _root_.YangMills.Construction.TorusFields.supDist u p < ℓ.side * r' + 10 * r →
      p ∉ sitesInBlocks ℓ.side C ∧ p ∉ bad.image Prod.fst ∧ p ∈ A ∧ parentBlock ℓ.side p ∈ X := by
    intro z u hz hu hbX hzb p hj hd
    obtain ⟨hpA, hpJ⟩ := hchain u hu p hj
    have hpX : parentBlock ℓ.side p ∈ X := hclosed hbX (hZY (hAZ p hpA)) hpJ
    have hbp : _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side u) (parentBlock ℓ.side p) ≤ r' + 10 * r / 65536 + 1 := by
      have h1 := _root_.YangMills.Construction.TorusLumps.ImageUnionLength.supDist_parentBlock_le_div_add_one ℓ.side u p
      have h2 := Nat.div_le_div_right (c := ℓ.side) hd.le
      rw [Nat.mul_add_div hLpos] at h2
      have h3 := hdiv (10 * r)
      omega
    have hzp := _root_.YangMills.Construction.TorusFields.supDist_triangle z (parentBlock ℓ.side u) (parentBlock ℓ.side p)
    have hpC : p ∉ sitesInBlocks ℓ.side C := by
      intro hpc
      have hbc : parentBlock ℓ.side p ∈ C := by simpa [sitesInBlocks] using hpc
      obtain ⟨l, hl, hlX, hd2⟩ := hlump _ hbc hpX
      refine hz (Or.inl ⟨l, hl, hlX, ?_⟩)
      have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle z (parentBlock ℓ.side p) (lumpCenter l)
      omega
    refine ⟨hpC, fun hpb => hz (Or.inr ⟨parentBlock ℓ.side p, ?_, by omega⟩), hpA, hpX⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr
      ⟨p, Finset.mem_inter.mpr ⟨hpb, Finset.mem_inter.mpr ⟨hpA, ?_⟩⟩, rfl⟩, ?_⟩
    · simpa [sitesInBlocks] using hpX
    · intro hc
      exact hpC (by simpa [sitesInBlocks] using hc)
  let A₀ : Finset (TorusSite n) := Finset.univ.filter fun b =>
    ∃ z u, ¬ Near z ∧ u ∈ A ∧ parentBlock ℓ.side u = b ∧ b ∈ X ∧ _root_.YangMills.Construction.TorusFields.supDist z b ≤ 4 * r / 65536 + 1
  obtain ⟨B, hBA, hsep, hBcov⟩ := exists_separated_net (3 * r') A₀
  have hlen : excessLength ℓ r' X V ≤ (Bd ∪ B).card := by
    refine excessLength_le_card ℓ r' X V _ fun y hy => ?_
    have hyY : y ∈ Y' := by
      obtain ⟨Xc, hXc, hyXc⟩ := Finset.mem_biUnion.mp hy
      exact subset_of_mem_chainComponents (hP hXc) hyXc
    obtain ⟨z, hzZ, hyz⟩ := (mem_thickening _ _ _).mp hyY
    have hzX : z ∈ X := hclosed hy (hZY hzZ) (chainConnected_of_supDist_le hyY (hZY hzZ) (by omega))
    by_cases hn : Near z
    · rcases hn with ⟨l, hl, hlX, hd⟩ | ⟨b, hb, hd⟩
      · refine Or.inl ⟨l, hl, hlX, ?_⟩
        have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle y z (lumpCenter l)
        omega
      · refine Or.inr ((mem_thickening _ _ _).mpr ⟨b, Finset.mem_union_left _ hb, ?_⟩)
        have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle y z b
        omega
    · obtain ⟨u, hu, hbX, hzb⟩ := hcore z hzZ hzX hn
      have hmem : parentBlock ℓ.side u ∈ A₀ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, u, hn, hu, rfl, hbX, hzb⟩
      obtain ⟨b, hb, hbd⟩ := hBcov _ hmem
      refine Or.inr ((mem_thickening _ _ _).mpr ⟨b, Finset.mem_union_right _ hb, ?_⟩)
      have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle y z b
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z (parentBlock ℓ.side u) b
      omega
  have hpick : ∀ b ∈ B, ∃ u z, ¬ Near z ∧ u ∈ A ∧ parentBlock ℓ.side u = b ∧ b ∈ X ∧
      _root_.YangMills.Construction.TorusFields.supDist z b ≤ 4 * r / 65536 + 1 := by
    intro b hb
    obtain ⟨z, u, h⟩ := (Finset.mem_filter.mp (hBA hb)).2
    exact ⟨u, z, h⟩
  choose! u zz hn huA hub hbX hzb using hpick
  have hUK : U ⊆ K := by
    intro p hp
    obtain ⟨Xc, hXc, hpXc⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hXc).2 hpXc
  obtain ⟨M, hMcard, hMcov⟩ :=
    exists_cover_card_le_add_excessLength ℓ r U W H fun l hl hlU => hH l hl (hlU.trans hUK)
  set m := ℓ.side * r' / (20 * r) with hmdef
  have hr20 : 0 < 20 * r := by omega
  have hm : 20 * r * m ≤ ℓ.side * r' := Nat.mul_div_le _ _
  have hm1 : ℓ.side * r' < 20 * r * (m + 1) := Nat.lt_mul_div_succ _ hr20
  have hclose : (2 * (ℓ.side * r' + 10 * r) + 8 * r) / ℓ.side + 1 ≤ 3 * r' := by
    have e : 2 * (ℓ.side * r' + 10 * r) + 8 * r = ℓ.side * (2 * r') + 28 * r := by ring
    rw [e, Nat.mul_add_div hLpos]
    have h1 := hdiv (28 * r)
    omega
  have hcount : B.card * (m + 1) ≤ M.card := by
    refine card_mul_le_of_long_chains ℓ.side hr1 hclose hm (G := G) u hsep hub ?_ ?_
    · intro b hb
      have huA' := huA b hb
      obtain ⟨Ac, hAc, huAc⟩ := Finset.mem_biUnion.mp huA'
      obtain ⟨hAcl, c, hc⟩ := Finset.mem_filter.mp hAc
      obtain ⟨hcAc, hcC⟩ := Finset.mem_inter.mp hc
      have hj : ChainConnected (10 * r) G (u b) c := chainConnected_of_mem_chainComponents hAcl huAc hcAc
      refine ⟨c, hj, ?_⟩
      by_contra hlt
      have hlt' : _root_.YangMills.Construction.TorusFields.supDist (u b) c < ℓ.side * r' + 10 * r := not_le.mp hlt
      have hbX' : parentBlock ℓ.side (u b) ∈ X := by rw [hub b hb]; exact hbX b hb
      have hzb' : supDist (zz b) (parentBlock ℓ.side (u b)) ≤ 4 * r / 65536 + 1 := by
        rw [hub b hb]
        exact hzb b hb
      exact (hfar _ _ (hn b hb) huA' hbX' hzb' c hj hlt').1 hcC
    · intro b hb p hj hd
      have hbX' : parentBlock ℓ.side (u b) ∈ X := by rw [hub b hb]; exact hbX b hb
      have hzb' : supDist (zz b) (parentBlock ℓ.side (u b)) ≤ 4 * r / 65536 + 1 := by
        rw [hub b hb]
        exact hzb b hb
      obtain ⟨hpC, hpb, hpA, hpX⟩ := hfar _ _ (hn b hb) (huA b hb) hbX' hzb' p hj hd
      have hpYt : p ∈ Yt := by
        rcases Finset.mem_union.mp (hAG hpA) with h1 | h1
        · rcases Finset.mem_union.mp h1 with h2 | h2
          · exact absurd h2 hpb
          · exact h2
        · exact absurd h1 hpC
      obtain ⟨Xc, hXc, hpXc⟩ := exists_mem_chainComponents (r := r) hpYt
      have hYG : ∀ {w}, w ∈ Yt → w ∈ G := fun h => Finset.mem_union_left _ (Finset.mem_union_right _ h)
      have hXK : Xc ⊆ K := by
        intro w hw
        have hjw : ChainConnected r Yt p w := chainConnected_of_mem_chainComponents hXc hpXc hw
        have hstep : ∀ a c, (a ∈ Yt ∧ c ∈ Yt ∧ _root_.YangMills.Construction.TorusFields.supDist a c ≤ r) →
            (a ∈ G ∧ c ∈ G ∧ _root_.YangMills.Construction.TorusFields.supDist a c ≤ 10 * r) :=
          fun a c hac => ⟨hYG hac.1, hYG hac.2.1, by have := hac.2.2; omega⟩
        have hjG : ChainConnected (10 * r) G p w := Relation.ReflTransGen.mono hstep _ _ hjw
        obtain ⟨hwA, hwJ⟩ := hchain p hpA w hjG
        refine Finset.mem_inter.mpr ⟨hwA, ?_⟩
        have hwX := hclosed hpX (hZY (hAZ w hwA)) hwJ
        simpa [sitesInBlocks] using hwX
      have hpU : p ∈ U := Finset.mem_biUnion.mpr ⟨Xc, Finset.mem_filter.mpr ⟨hXc, hXK⟩, hpXc⟩
      exact hMcov hpU
  have hL40 : ℓ.side ≤ 40 * (m + 1) := by
    by_contra hc
    have hc' : 40 * (m + 1) ≤ ℓ.side := by omega
    have h1 : (20 * r) * (m + 1) ≤ (40 * r') * (m + 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (40 * (m + 1)) * r' ≤ ℓ.side * r' := Nat.mul_le_mul_right _ hc'
    have h3 : (40 * r') * (m + 1) = (40 * (m + 1)) * r' := by ring
    omega
  refine ⟨B.card, hlen.trans (Finset.card_union_le _ _), ?_⟩
  calc B.card * ℓ.side ≤ B.card * (40 * (m + 1)) := Nat.mul_le_mul_left _ hL40
    _ = 40 * (B.card * (m + 1)) := by ring
    _ ≤ 40 * M.card := Nat.mul_le_mul_left _ hcount
    _ ≤ 40 * (H.card + excessLength ℓ r U W) := Nat.mul_le_mul_left _ hMcard
theorem real_le_add_div_mul {a d b h v L : ℕ} (hL : 0 < L) (h1 : a ≤ d + b) (h2 : b * L ≤ 40 * (h + v)) :
    (a : ℝ) ≤ (d : ℝ) + 40 / (L : ℝ) * ((h : ℝ) + (v : ℝ)) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have h1' : (a : ℝ) ≤ (d : ℝ) + (b : ℝ) := by exact_mod_cast h1
  have h2' : (b : ℝ) * L ≤ 40 * ((h : ℝ) + (v : ℝ)) := by exact_mod_cast h2
  have h3 : (b : ℝ) ≤ 40 / (L : ℝ) * ((h : ℝ) + (v : ℝ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hLr]
    exact h2'
  linarith
end ImageUnionLength
theorem imageUnionLengthBound_holds : ImageUnionLengthBound := by
  classical
  intro ℓ hfit r r' hr1 hrr hr' n _ hLn V W bad Yt P hP
  have hLpos : 0 < ℓ.side := by
    have := hfit.L_ge
    omega
  obtain ⟨b, h1, h2⟩ := ImageUnionLength.excessLength_biUnion_le ℓ hfit hr1 hrr hr' hLn V W bad Yt P hP
    ((torusHotLumps ℓ W).filter
      (· ⊆ attachedInBlocks ℓ.side r bad Yt (thickening (2 * r') (torusHotSites ℓ V)) (P.biUnion id)))
    fun l hl hlK => Finset.mem_filter.mpr ⟨hl, hlK⟩
  convert ImageUnionLength.real_le_add_div_mul hLpos h1 h2
end YangMills.Construction.TorusLumps
end
