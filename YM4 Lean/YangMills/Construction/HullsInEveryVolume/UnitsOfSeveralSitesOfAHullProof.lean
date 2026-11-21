import YangMills.Construction.HullsInEveryVolume.SetsOfCentresOfATree
import YangMills.Construction.HullsInEveryVolume.TreeOfAHullProof
import YangMills.Construction.HullsInEveryVolume.UnitsOfSeveralSitesOfAHull
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HullTrees
open TorusLumps TorusFields TorusBalls RenormalizationStepParameters StepReturn WeightedResponses
private def ancestorSite (L : ℕ) : (j n : ℕ) → TorusSite (fineSide L j n) → TorusSite n
  | 0, _, z => z
  | j + 1, n, z => parentBlock L (ancestorSite L j (n * L) z)
private theorem sum_levelWeight_le_one (u : ℕ) : ∑ j ∈ Finset.range (u + 1), levelWeight j ≤ 1 := by apply _root_.YangMills.SharedProofs.p12137 <;> assumption
private theorem exists_depth_with_share (u mm : ℕ) (hmm : 1 ≤ mm) (f : Fin mm → ℕ) (hf : ∀ i, f i ≤ u) :
    ∃ j ≤ u, levelWeight j * (mm : ℝ) ≤ ((Finset.univ.filter fun i => f i = j).card : ℝ) := by
  by_contra hc
  push Not at hc
  have hcard : mm = ∑ j ∈ Finset.range (u + 1), (Finset.univ.filter fun i => f i = j).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin mm)))
      (t := Finset.range (u + 1)) (f := f) (fun i _ => by
        have := hf i
        simp only [Finset.coe_range, Set.mem_Iio]
        omega)
    simpa using h
  have hcast : (mm : ℝ) = ∑ j ∈ Finset.range (u + 1), ((Finset.univ.filter fun i => f i = j).card : ℝ) := by
    exact_mod_cast hcard
  have hlt : (mm : ℝ) < ∑ j ∈ Finset.range (u + 1), levelWeight j * (mm : ℝ) := by
    calc (mm : ℝ) = ∑ j ∈ Finset.range (u + 1), ((Finset.univ.filter fun i => f i = j).card : ℝ) := hcast
      _ < ∑ j ∈ Finset.range (u + 1), levelWeight j * (mm : ℝ) :=
        Finset.sum_lt_sum_of_nonempty (by simp) fun j hj => hc j (by
          have := Finset.mem_range.1 hj
          omega)
  have hle : ∑ j ∈ Finset.range (u + 1), levelWeight j * (mm : ℝ) ≤ (mm : ℝ) := by
    rw [← Finset.sum_mul]
    nlinarith [sum_levelWeight_le_one u]
  linarith
open Classical in
private def unionsOfChoices {X : Type} {mm : ℕ} (G : Fin mm → Finset (Finset X)) (M N : ℕ) :
    Finset (Finset X) :=
  ((Finset.powersetCard M (Finset.univ : Finset (Fin mm))).biUnion fun I =>
    (I.pi fun i => G i).image fun f => I.attach.biUnion fun i => f i.1 i.2).filter fun S => S.card = N
private theorem card_of_mem_unionsOfChoices {X : Type} {mm : ℕ} {G : Fin mm → Finset (Finset X)} {M N : ℕ}
    {S : Finset X} (h : S ∈ unionsOfChoices G M N) : S.card = N := by
  classical
  exact (Finset.mem_filter.1 h).2
open Classical in
private theorem card_unionsOfChoices_le {X : Type} {mm : ℕ} (G : Fin mm → Finset (Finset X)) (M N : ℕ)
    (E : ℝ) (hE : 0 ≤ E) (hG : ∀ i, ((G i).card : ℝ) ≤ E) :
    ((unionsOfChoices G M N).card : ℝ) ≤ 2 ^ mm * E ^ M := by
  have h1 : (unionsOfChoices G M N).card ≤
      ∑ I ∈ Finset.powersetCard M (Finset.univ : Finset (Fin mm)), ∏ i ∈ I, (G i).card := by
    refine (Finset.card_filter_le _ _).trans (Finset.card_biUnion_le.trans ?_)
    refine Finset.sum_le_sum fun I _ => Finset.card_image_le.trans ?_
    rw [Finset.card_pi]
  have h2 : ∀ I ∈ Finset.powersetCard M (Finset.univ : Finset (Fin mm)),
      ((∏ i ∈ I, (G i).card : ℕ) : ℝ) ≤ E ^ M := by
    intro I hI
    have hc := (Finset.mem_powersetCard.1 hI).2
    push_cast
    calc ∏ i ∈ I, ((G i).card : ℝ) ≤ ∏ _i ∈ I, E :=
          Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => hG i
      _ = E ^ M := by rw [Finset.prod_const, hc]
  have h3 : ((Finset.powersetCard M (Finset.univ : Finset (Fin mm))).card : ℝ) ≤ 2 ^ mm := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.choose_le_two_pow _ _
  calc ((unionsOfChoices G M N).card : ℝ)
      ≤ ((∑ I ∈ Finset.powersetCard M (Finset.univ : Finset (Fin mm)), ∏ i ∈ I, (G i).card : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ∑ I ∈ Finset.powersetCard M (Finset.univ : Finset (Fin mm)), ((∏ i ∈ I, (G i).card : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ _I ∈ Finset.powersetCard M (Finset.univ : Finset (Fin mm)), E ^ M :=
        Finset.sum_le_sum h2
    _ = ((Finset.powersetCard M (Finset.univ : Finset (Fin mm))).card : ℝ) * E ^ M := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ mm * E ^ M := mul_le_mul_of_nonneg_right h3 (by positivity)
open Classical in
private theorem exists_mem_unionsOfChoices {X : Type} {mm : ℕ} (G : Fin mm → Finset (Finset X)) (M N₀ : ℕ)
    (I : Finset (Fin mm)) (hI : I.card = M) (S : Fin mm → Finset X) (hS : ∀ i ∈ I, S i ∈ G i)
    (hc : ∀ i ∈ I, (S i).card = N₀) (hd : ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → ∀ a ∈ S i, a ∉ S i') :
    ∃ U ∈ unionsOfChoices G M (N₀ * M), ∀ a, a ∈ U ↔ ∃ i ∈ I, a ∈ S i := by
  have hmem : ∀ a, a ∈ I.attach.biUnion (fun i => S i.1) ↔ ∃ i ∈ I, a ∈ S i := by
    intro a
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨i, hi, ha⟩
      exact ⟨i, hi, ha⟩
    · rintro ⟨i, hi, ha⟩
      exact ⟨i, hi, ha⟩
  have hcard : (I.attach.biUnion fun i => S i.1).card = N₀ * M := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl fun i _ => hc i.1 i.2, Finset.sum_const, Finset.card_attach, hI, smul_eq_mul,
        mul_comm]
    · intro i _ i' _ hne
      refine Finset.disjoint_left.2 fun a ha ha' => hd i.1 i.2 i'.1 i'.2 (fun e => hne (Subtype.ext e)) a ha ha'
  refine ⟨I.attach.biUnion fun i => S i.1, ?_, hmem⟩
  refine Finset.mem_filter.2 ⟨?_, hcard⟩
  refine Finset.mem_biUnion.2 ⟨I, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hI⟩, ?_⟩
  exact Finset.mem_image.2 ⟨fun i _ => S i, Finset.mem_pi.2 fun i hi => hS i hi, rfl⟩
variable {ℓ : StepParameters}
private theorem unitsAtDepth_iff_forall_singleton (T : StageTower ℓ) (j : ℕ) :
    ∀ (u n : ℕ) [NeZero n] (w : MarkedSample ℓ u n)
    (S : Finset (TorusSite (fineSide ℓ.side j n))), j ≤ u →
    (UnitsAtDepth T j u n w S ↔ ∀ z ∈ S, UnitsAtDepth T j u n w {z}) := by
  induction j with
  | zero =>
    intro u n _ w S _
    simp only [UnitsAtDepth]
    constructor
    · intro h z hz z' hz'
      rw [Finset.mem_singleton.1 hz']
      exact h z hz
    · intro h z hz
      exact h z hz z (Finset.mem_singleton_self z)
  | succ j ih =>
    intro u n _ w S hj
    cases u with
    | zero => omega
    | succ u =>
      simp only [UnitsAtDepth]
      exact ih u (n * ℓ.side) w.1 S (by omega)
private theorem unitsAtDepth_leafSites (T : StageTower ℓ) (k : ℕ) {u n : ℕ} (tr : SiteTree ℓ.side u n) :
    ∀ [NeZero n] (w : MarkedSample ℓ u n), tr.Embeds T k w →
    ∀ j ≤ u, UnitsAtDepth T j u n w (tr.leafSites j) := by
  induction tr with
  | @leaf u n y =>
    intro _ w hh j hj
    cases j with
    | zero =>
      have h2 : HullTrees.IsUnit T u n w y := by
        simp only [SiteTree.Embeds] at hh
        exact hh.2
      simp only [UnitsAtDepth]
      intro z hz
      rw [Finset.mem_singleton.1 hz]
      exact h2
    | succ j =>
      refine (unitsAtDepth_iff_forall_singleton T _ _ _ w _ hj).2 fun z hz => ?_
      exact absurd hz (Finset.notMem_empty _)
  | @node u n y k' kids ih =>
    intro _ w hh j hj
    cases j with
    | zero =>
      refine (unitsAtDepth_iff_forall_singleton T _ _ _ w _ hj).2 fun z hz => ?_
      exact absurd hz (Finset.notMem_empty _)
    | succ j =>
      simp only [SiteTree.Embeds] at hh
      obtain ⟨_, _, _, _, h5⟩ := hh
      show UnitsAtDepth T j u (n * ℓ.side) w.1 ((SiteTree.node y k' kids).leafSites (j + 1))
      refine (unitsAtDepth_iff_forall_singleton T _ _ _ w.1 _ (by omega)).2 fun z hz => ?_
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
      exact (unitsAtDepth_iff_forall_singleton T _ _ _ w.1 _ (by omega)).1 (ih i w.1 (h5 i) j (by omega)) z hi
private theorem supDist_ancestorSite_root_le (T : StageTower ℓ) (hL : 8 ≤ ℓ.side) (k : ℕ) {u n : ℕ}
    (tr : SiteTree ℓ.side u n) :
    ∀ [NeZero n] (w : MarkedSample ℓ u n), tr.Embeds T k w →
    (∀ v ≤ u, 1 ≤ stageRange T v) → (∀ v < u, stageRange T v ≤ 2 * stageRange T (v + 1)) →
    ∀ j, ∀ z ∈ tr.leafSites j, supDist (ancestorSite ℓ.side j n z) tr.root ≤ 4 * stageRange T u := by
  induction tr with
  | @leaf u n y =>
    intro _ w hh hpos hstep j z hz
    cases j with
    | zero =>
      have hz' : z = y := Finset.mem_singleton.1 hz
      rw [hz']
      exact (supDist_self y).le.trans (Nat.zero_le _)
    | succ j => exact absurd hz (Finset.notMem_empty _)
  | @node u n y k' kids ih =>
    intro _ w hh hpos hstep j z hz
    cases j with
    | zero => exact absurd hz (Finset.notMem_empty _)
    | succ j =>
      simp only [SiteTree.Embeds] at hh
      obtain ⟨_, _, h3, _, h5⟩ := hh
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
      have a := ih i w.1 (h5 i) (fun v hv => hpos v (by omega)) (fun v hv => hstep v (by omega)) j z hi
      have b : supDist (parentBlock ℓ.side (kids i).root) y ≤ 2 * stageRange T (u + 1) := by
        have h := h3 i
        simp only [box, thickening, Finset.mem_filter, Finset.mem_singleton, exists_eq_left] at h
        exact h.2
      have c := supDist_parentBlock_le_div_add_one ℓ.side (ancestorSite ℓ.side j (n * ℓ.side) z) (kids i).root
      have d := supDist_triangle (parentBlock ℓ.side (ancestorSite ℓ.side j (n * ℓ.side) z))
        (parentBlock ℓ.side (kids i).root) y
      have r1 := hpos (u + 1) le_rfl
      have r2 := hstep u (by omega)
      have e : supDist (ancestorSite ℓ.side j (n * ℓ.side) z) (kids i).root / ℓ.side ≤ stageRange T (u + 1) := by
        apply Nat.div_le_of_le_mul
        nlinarith
      show supDist (parentBlock ℓ.side (ancestorSite ℓ.side j (n * ℓ.side) z)) y ≤ 4 * stageRange T (u + 1)
      omega
private theorem le_supDist_of_ancestorSite (T : StageTower ℓ) (hL : 8 ≤ ℓ.side) (j : ℕ) :
    ∀ (u n : ℕ) [NeZero n], j ≤ u →
    (∀ v ≤ u, 1 ≤ stageRange T v) → (∀ v < u, stageRange T v ≤ 2 * stageRange T (v + 1)) →
    ∀ a b : TorusSite (fineSide ℓ.side j n),
      32 * stageRange T u ≤ supDist (ancestorSite ℓ.side j n a) (ancestorSite ℓ.side j n b) →
      32 * stageRange T (u - j) ≤ supDist a b := by
  induction j with
  | zero =>
    intro u n _ _ _ _ a b h
    exact h
  | succ j ih =>
    intro u n _ hj hpos hstep a b h
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    have e : v + 1 - (j + 1) = v - j := by omega
    rw [e]
    refine ih v (n * ℓ.side) (by omega) (fun t ht => hpos t (by omega)) (fun t ht => hstep t (by omega)) a b ?_
    have c := supDist_parentBlock_le_div_add_one ℓ.side (ancestorSite ℓ.side j (n * ℓ.side) a)
      (ancestorSite ℓ.side j (n * ℓ.side) b)
    have h' : 32 * stageRange T (v + 1) ≤
        supDist (parentBlock ℓ.side (ancestorSite ℓ.side j (n * ℓ.side) a))
          (parentBlock ℓ.side (ancestorSite ℓ.side j (n * ℓ.side) b)) := h
    have r1 := hpos (v + 1) le_rfl
    have r2 := hstep v (by omega)
    have e1 : 31 * stageRange T (v + 1) ≤
        supDist (ancestorSite ℓ.side j (n * ℓ.side) a) (ancestorSite ℓ.side j (n * ℓ.side) b) / ℓ.side := by
      omega
    have e2 := (Nat.le_div_iff_mul_le (by omega)).1 e1
    nlinarith
private theorem one_le_clusterRange {x : ℝ} (hx : 0 < x) : 1 ≤ clusterRange x :=
  Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx _)
private theorem clusterRange_le_two_mul {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 < x') (h : x ≤ 2 * x') :
    clusterRange x ≤ 2 * clusterRange x' := by
  unfold clusterRange
  apply Nat.ceil_le.2
  push_cast
  have h1 : x ^ ((1 : ℝ) / 100) ≤ (2 * x') ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow hx h (by norm_num)
  have h2 : (2 * x') ^ ((1 : ℝ) / 100) = 2 ^ ((1 : ℝ) / 100) * x' ^ ((1 : ℝ) / 100) :=
    Real.mul_rpow (by norm_num) hx'.le
  have h3 : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h4 := Nat.le_ceil (x' ^ ((1 : ℝ) / 100))
  have h5 : 0 ≤ x' ^ ((1 : ℝ) / 100) := Real.rpow_nonneg hx'.le _
  nlinarith
private theorem hasExpansion_expansionCoupling (hret : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hr : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem couplingFlow_ge_and_hasExpansion (Tb : ParameterAssignment) {y g β : ℝ} {K : ℕ}
    (hp : FlowCrossing Tb y g β K) (hB : 0 ≤ Tb.B) (hret : ExpansionReturnsAt (Tb.stepParameters y))
    (hrow : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β)) (t : ℕ) :
    t ≤ K → y ≤ (couplingFlow (Tb.stepParameters y) β t).1 ∧
      HasExpansion (Tb.stepParameters y) t (couplingFlow (Tb.stepParameters y) β t).1
        (couplingFlow (Tb.stepParameters y) β t).2 := by
  induction t with
  | zero =>
    intro _
    have h1 := hp.le_inv_sq
    have h2 : (g ^ 2)⁻¹ + 2 * Tb.B ≤ β := hp.upper_le
    have h3 : y ≤ β := by linarith
    exact ⟨h3, hrow β h3⟩
  | succ t ih =>
    intro ht
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨h3, h4⟩ := hasExpansion_expansionCoupling hret (ℓ := Tb.stepParameters y) h1 h2
    refine ⟨?_, h3⟩
    have h5 : (g ^ 2)⁻¹ + 2 * Tb.B < (couplingFlow (Tb.stepParameters y) β t).1 := hp.isFirst.2 t (by omega)
    have h6 := abs_le.1 h4
    have h7 := hp.le_inv_sq
    have h8 : -(2 * Tb.B) ≤ expansionCoupling (Tb.stepParameters y) t (couplingFlow (Tb.stepParameters y) β t).1
        (couplingFlow (Tb.stepParameters y) β t).2 - (couplingFlow (Tb.stepParameters y) β t).1 := h6.1
    show y ≤ expansionCoupling (Tb.stepParameters y) t (couplingFlow (Tb.stepParameters y) β t).1
      (couplingFlow (Tb.stepParameters y) β t).2
    linarith
theorem unitsOfSeparatedHullSites_holds (h₁ : HullSiteTreeExists) (h₂ : FewLeafSiteFamilies) :
    UnitsOfSeparatedHullSites := by
  obtain ⟨C₁, hS⟩ := h₂
  refine ⟨C₁, ?_⟩
  intro a ha
  obtain ⟨L₁, rt₁, D₁, hrt₁, hT⟩ := h₁ a ha
  obtain ⟨L₂, rt₂, D₂, hrt₂, hS⟩ := hS a ha
  refine ⟨max L₁ L₂, fun c => min (rt₁ c) (rt₂ c), max D₁ D₂, fun c => lt_min (hrt₁ c) (hrt₂ c), ?_⟩
  intro L hodd hL Tb hTa hTL hD hC hOn hrt hCd
  obtain ⟨M₁, hT⟩ := hT L hodd (le_trans (le_max_left _ _) hL) Tb hTa hTL hD hC hOn
    (le_trans hrt (min_le_left _ _)) (le_trans (le_max_left _ _) hCd)
  obtain ⟨M₂, hS⟩ := hS L hodd (le_trans (le_max_right _ _) hL) Tb hTa hTL hD hC hOn
    (le_trans hrt (min_le_right _ _)) (le_trans (le_max_right _ _) hCd)
  refine ⟨max M₁ M₂, ?_⟩
  intro Kr hM hη hN hF hR
  obtain ⟨y₁, hT⟩ := hT Kr (le_trans (le_max_left _ _) hM) hη hN hF hR
  obtain ⟨y₂, hS⟩ := hS Kr (le_trans (le_max_right _ _) hM) hη hN hF hR
  refine ⟨max (max y₁ y₂) (2 * Tb.B + 1), ?_⟩
  intro y hy hret hrow
  have hT := hT y (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy) hret hrow
  have hS := hS y (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy) hret hrow
  intro g β K m T u n _ hA mm hmm
  obtain ⟨F', hF'⟩ := hS g β K m T u n hA
  have hp : FlowCrossing Tb y g β K := hA.chain.toCrossingVolume.toFlowCrossing
  have hB1 : 1 ≤ Tb.B := hD.B_ge
  have hy3 : 2 * Tb.B + 1 ≤ y := le_trans (le_max_right _ _) hy
  have hL8 : 8 ≤ (Tb.stepParameters y).side := by
    have h := hD.L_ge
    have e : (Tb.stepParameters y).side = Tb.side := rfl
    rw [e]
    norm_num at h
    omega
  have hl := hA.le
  have hrun := fun t ht => couplingFlow_ge_and_hasExpansion Tb hp (by linarith) hret hrow t ht
  have hpos : ∀ v ≤ u, 1 ≤ stageRange T v := fun v hv => by
    have h1 := (hrun v (hv.trans hl)).1
    have e := hA.chain.follows v (by omega)
    show 1 ≤ clusterRange (T.stage v).coupling
    rw [e]
    exact one_le_clusterRange (by linarith)
  have hstep : ∀ v < u, stageRange T v ≤ 2 * stageRange T (v + 1) := fun v hv => by
    obtain ⟨h1, h2⟩ := hrun v (by omega)
    have h3 := (hrun (v + 1) (by omega)).1
    have h4 := (hasExpansion_expansionCoupling hret (ℓ := Tb.stepParameters y) h1 h2).2
    have e1 := hA.chain.follows v (by omega)
    have e2 := hA.chain.follows (v + 1) (by omega)
    show clusterRange (T.stage v).coupling ≤ 2 * clusterRange (T.stage (v + 1)).coupling
    rw [e1, e2]
    have h5 : |(couplingFlow (Tb.stepParameters y) β (v + 1)).1 - (couplingFlow (Tb.stepParameters y) β v).1|
        ≤ 2 * Tb.B := h4
    have h6 := abs_le.1 h5
    exact clusterRange_le_two_mul (by linarith) (by linarith) (by linarith [h6.1])
  refine ⟨fun ys j => unionsOfChoices (fun i => F' (ys i) j) ⌈levelWeight j * (mm : ℝ)⌉₊
    (minLeafCountScaled (Tb.stepParameters y).side j mm), ?_⟩
  intro ys hsep
  refine ⟨fun j hj => ⟨?_, fun S hS' => card_of_mem_unionsOfChoices hS'⟩, fun w hw => ?_⟩
  · refine (card_unionsOfChoices_le (fun i => F' (ys i) j) _ _ _ (Real.exp_pos _).le
      fun i => (hF' (ys i) j hj).1).trans (le_of_eq ?_)
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [minLeafCountScaled]
    push_cast
    ring
  · have trees := fun i => hT g β K m T u n hA w (ys i) (hw i)
    choose tr hroot hhang _ hdepth hleaf using trees
    choose f hfu hfs using hdepth
    obtain ⟨j, hj, hJ⟩ := exists_depth_with_share u mm hmm f hfu
    have hsets : ∀ i, f i = j → ∃ S ∈ F' (ys i) j, S ⊆ (tr i).leafSites j := fun i hi =>
      (hF' (ys i) j hj).2.2 w (tr i) (hroot i) (hhang i) (hi ▸ hfs i)
    choose! S hSF hSsub using hsets
    obtain ⟨I, hIJ, hIc⟩ := Finset.exists_subset_card_eq (Nat.ceil_le.2 hJ)
    have hIj : ∀ i ∈ I, f i = j := fun i hi => (Finset.mem_filter.1 (hIJ hi)).2
    have hu1 : 1 ≤ stageRange T (u - j) := hpos _ (by omega)
    have far : ∀ i i', i ≠ i' → ∀ a ∈ (tr i).leafSites j, ∀ b ∈ (tr i').leafSites j,
        32 * stageRange T (u - j) ≤ supDist a b := by
      intro i i' hne a ha b hb
      refine le_supDist_of_ancestorSite T hL8 j u n hj hpos hstep a b ?_
      have r1 := supDist_ancestorSite_root_le T hL8 _ (tr i) w (hhang i) hpos hstep j a ha
      have r2 := supDist_ancestorSite_root_le T hL8 _ (tr i') w (hhang i') hpos hstep j b hb
      rw [hroot i] at r1
      rw [hroot i'] at r2
      have d0 := hsep i i' hne
      have d1 := supDist_triangle (ys i) (ancestorSite (Tb.stepParameters y).side j n a) (ys i')
      have d2 := supDist_triangle (ancestorSite (Tb.stepParameters y).side j n a)
        (ancestorSite (Tb.stepParameters y).side j n b) (ys i')
      have d3 := supDist_comm (ys i) (ancestorSite (Tb.stepParameters y).side j n a)
      omega
    obtain ⟨U, hU, hUm⟩ := exists_mem_unionsOfChoices (fun i => F' (ys i) j) _
      (minLeafCount (Tb.stepParameters y).side j) I hIc S
      (fun i hi => hSF i (hIj i hi)) (fun i hi => (hF' (ys i) j hj).2.1 _ (hSF i (hIj i hi)))
      (fun i hi i' hi' hne a ha ha' => by
        have h := far i i' hne a (hSsub i (hIj i hi) ha) a (hSsub i' (hIj i' hi') ha')
        rw [supDist_self] at h
        omega)
    refine ⟨j, hj, U, hU, ?_, ?_⟩
    · refine (unitsAtDepth_iff_forall_singleton T _ _ _ w _ hj).2 fun z hz => ?_
      obtain ⟨i, hi, hz'⟩ := (hUm z).1 hz
      exact (unitsAtDepth_iff_forall_singleton T _ _ _ w _ hj).1
        (unitsAtDepth_leafSites T _ (tr i) w (hhang i) j hj) z (hSsub i (hIj i hi) hz')
    · intro a ha b hb hne
      obtain ⟨i, hi, ha'⟩ := (hUm a).1 ha
      obtain ⟨i', hi', hb'⟩ := (hUm b).1 hb
      have ma := hSsub i (hIj i hi) ha'
      have mb := hSsub i' (hIj i' hi') hb'
      by_cases e : i = i'
      · subst e
        exact (hleaf i j hj).2 a ma b mb hne
      · have := far i i' e a ma b mb
        omega
end YangMills.Construction.HullTrees
end
