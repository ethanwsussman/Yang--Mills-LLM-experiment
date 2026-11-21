import YangMills.Construction.CellOfTheFlow.FreeClassesGivenTheState
import YangMills.Construction.CellOfTheFlow.LongClassesAreRare
import YangMills.Construction.CellOfTheFlow.LongClassesHaveManyUnits
import YangMills.Construction.CellOfTheFlow.SupportsAboutABlockAreFew
import YangMills.Construction.ClusterExpansionOfAStep.ClustersHaveClassSupportsProof
import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.FourPointCondition.LawsAtALevelOfTheWindowProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepReturn WeightedResponses ResponseInTheExpansion
private theorem measure_inter_forall_exists_le_aux {Ω ι Sp : Type} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω)
    (Γ : Ω → Finset Sp) (z b : Sp → ℝ) (w : ℝ) (long : ι → Sp → Prop) (cands : ι → Finset Sp)
    (S : Finset ι) (hz : ∀ θ, 0 ≤ z θ) (hb : ∀ θ, 0 ≤ b θ)
    (free : ∀ Θ : Finset Sp, μ (A ∩ {v | Θ ⊆ Γ v}) ≤ ENNReal.ofReal (∏ θ ∈ Θ, z θ) * μ A)
    (hc : ∀ i ∈ S, ∀ θ, long i θ → θ ∈ cands i)
    (price : ∀ (S' : Finset ι) (θ : Sp), S' ⊆ S → (∀ i ∈ S', long i θ) →
      z θ ≤ b θ * Real.exp (-(w * S'.card)))
    (sum1 : ∀ i ∈ S, ∑ θ ∈ cands i, b θ ≤ 1) (n : ℕ) :
    ∀ (S' : Finset ι), S'.card = n → S' ⊆ S → ∀ Θ : Finset Sp, (∀ θ ∈ Θ, ∀ i ∈ S', ¬ long i θ) →
      μ (A ∩ {v | Θ ⊆ Γ v} ∩ {v | ∀ i ∈ S', ∃ θ ∈ Γ v, long i θ}) ≤
        ENNReal.ofReal ((∏ θ ∈ Θ, z θ) * Real.exp (-(w * S'.card))) * μ A := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S' hn hS Θ hΘ
    have hP : 0 ≤ ∏ θ ∈ Θ, z θ := Finset.prod_nonneg fun θ _ => hz θ
    rcases S'.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · have h0 : (((∅ : Finset ι).card : ℕ) : ℝ) = 0 := by simp
      rw [h0, mul_zero, neg_zero, Real.exp_zero, mul_one]
      exact (measure_mono Set.inter_subset_left).trans (free Θ)
    · set E : ℝ := (∏ θ ∈ Θ, z θ) * Real.exp (-(w * S'.card)) with hE
      have hE0 : 0 ≤ E := mul_nonneg hP (Real.exp_pos _).le
      have hcover : A ∩ {v | Θ ⊆ Γ v} ∩ {v | ∀ i ∈ S', ∃ θ ∈ Γ v, long i θ} ⊆
          ⋃ θ ∈ (cands i).filter (long i), (A ∩ {v | insert θ Θ ⊆ Γ v} ∩
            {v | ∀ i' ∈ S'.filter (fun i' => ¬ long i' θ), ∃ θ' ∈ Γ v, long i' θ'}) := by
        rintro v ⟨⟨hA, hΘv⟩, hall⟩
        obtain ⟨θ, hθ, hl⟩ := hall i hi
        refine Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hc i (hS hi) θ hl, hl⟩)) ?_
        refine ⟨⟨hA, ?_⟩, fun i' hi' => hall i' (Finset.mem_filter.mp hi').1⟩
        exact Finset.insert_subset hθ hΘv
      have hterm : ∀ θ ∈ (cands i).filter (long i), μ (A ∩ {v | insert θ Θ ⊆ Γ v} ∩
            {v | ∀ i' ∈ S'.filter (fun i' => ¬ long i' θ), ∃ θ' ∈ Γ v, long i' θ'}) ≤
          ENNReal.ofReal (b θ * E) * μ A := by
        intro θ hθ
        have hl : long i θ := (Finset.mem_filter.mp hθ).2
        have hnot : θ ∉ Θ := fun h => hΘ θ h i hi hl
        have hsub : S'.filter (fun i' => ¬ long i' θ) ⊂ S' := by
          refine Finset.filter_ssubset.mpr ⟨i, hi, ?_⟩
          simpa using hl
        have hlt : (S'.filter (fun i' => ¬ long i' θ)).card < n := hn ▸ Finset.card_lt_card hsub
        have key := ih _ hlt (S'.filter (fun i' => ¬ long i' θ)) rfl (hsub.subset.trans hS) (insert θ Θ)
          (by
            intro θ' hθ' i' hi'
            rcases Finset.mem_insert.mp hθ' with rfl | h
            · exact (Finset.mem_filter.mp hi').2
            · exact hΘ θ' h i' (Finset.mem_filter.mp hi').1)
        refine key.trans ?_
        refine mul_le_mul_left ?_ _
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.prod_insert hnot]
        have hstr := price (S'.filter (long · θ)) θ ((Finset.filter_subset _ _).trans hS)
          (fun i' hi' => (Finset.mem_filter.mp hi').2)
        have hcard : ((S'.filter (long · θ)).card : ℝ) + ((S'.filter (fun i' => ¬ long i' θ)).card : ℝ) =
            (S'.card : ℝ) := by
          exact_mod_cast Finset.card_filter_add_card_filter_not (s := S') (long · θ)
        have hexp : Real.exp (-(w * ((S'.filter (long · θ)).card : ℝ))) *
            Real.exp (-(w * ((S'.filter (fun i' => ¬ long i' θ)).card : ℝ))) = Real.exp (-(w * S'.card)) := by
          rw [← Real.exp_add, ← hcard]
          congr 1
          ring
        calc z θ * (∏ θ ∈ Θ, z θ) * Real.exp (-(w * ((S'.filter (fun i' => ¬ long i' θ)).card : ℝ)))
            ≤ (b θ * Real.exp (-(w * ((S'.filter (long · θ)).card : ℝ)))) * (∏ θ ∈ Θ, z θ) *
                Real.exp (-(w * ((S'.filter (fun i' => ¬ long i' θ)).card : ℝ))) := by
              gcongr
          _ = b θ * E := by
              rw [hE, ← hexp]
              ring
      calc μ (A ∩ {v | Θ ⊆ Γ v} ∩ {v | ∀ i ∈ S', ∃ θ ∈ Γ v, long i θ})
          ≤ μ (⋃ θ ∈ (cands i).filter (long i), (A ∩ {v | insert θ Θ ⊆ Γ v} ∩
            {v | ∀ i' ∈ S'.filter (fun i' => ¬ long i' θ), ∃ θ' ∈ Γ v, long i' θ'})) := measure_mono hcover
        _ ≤ ∑ θ ∈ (cands i).filter (long i), μ (A ∩ {v | insert θ Θ ⊆ Γ v} ∩
            {v | ∀ i' ∈ S'.filter (fun i' => ¬ long i' θ), ∃ θ' ∈ Γ v, long i' θ'}) :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ θ ∈ (cands i).filter (long i), ENNReal.ofReal (b θ * E) * μ A := Finset.sum_le_sum hterm
        _ = ENNReal.ofReal (∑ θ ∈ (cands i).filter (long i), b θ * E) * μ A := by
            rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun θ _ => mul_nonneg (hb θ) hE0]
        _ ≤ ENNReal.ofReal E * μ A := by
            refine mul_le_mul_left ?_ _
            apply ENNReal.ofReal_le_ofReal
            rw [← Finset.sum_mul]
            have h1 : ∑ θ ∈ (cands i).filter (long i), b θ ≤ 1 :=
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun θ _ _ => hb θ).trans
                (sum1 i (hS hi))
            nlinarith
private theorem measure_inter_forall_exists_le {Ω ι Sp : Type} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω)
    (Γ : Ω → Finset Sp) (z b : Sp → ℝ) (w : ℝ) (long : ι → Sp → Prop) (cands : ι → Finset Sp)
    (S : Finset ι) (hz : ∀ θ, 0 ≤ z θ) (hb : ∀ θ, 0 ≤ b θ)
    (free : ∀ Θ : Finset Sp, μ (A ∩ {v | Θ ⊆ Γ v}) ≤ ENNReal.ofReal (∏ θ ∈ Θ, z θ) * μ A)
    (hc : ∀ i ∈ S, ∀ θ, long i θ → θ ∈ cands i)
    (price : ∀ (S' : Finset ι) (θ : Sp), S' ⊆ S → (∀ i ∈ S', long i θ) →
      z θ ≤ b θ * Real.exp (-(w * S'.card)))
    (sum1 : ∀ i ∈ S, ∑ θ ∈ cands i, b θ ≤ 1) :
    μ (A ∩ {v | ∀ i ∈ S, ∃ θ ∈ Γ v, long i θ}) ≤ ENNReal.ofReal (Real.exp (-(w * S.card))) * μ A := by
  classical
  have h := measure_inter_forall_exists_le_aux μ A Γ z b w long cands S hz hb free hc price sum1 S.card S rfl
    subset_rfl ∅ (by simp)
  simp only [Finset.prod_empty, one_mul] at h
  refine (measure_mono ?_).trans h
  rintro v ⟨hA, hall⟩
  exact ⟨⟨hA, by simp⟩, hall⟩
private theorem sum_biUnion_le_sum_sum {α β : Type} [DecidableEq β] (s : Finset α) (t : α → Finset β)
    (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h1 := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have h2 : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
    linarith
abbrev _root_.YangMills.SharedProofs.p62010 := @sum_biUnion_le_sum_sum
section Counts
variable {n : ℕ} [NeZero n]
private theorem mem_sitesInBlocks {L : ℕ} [NeZero L] {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.CongruentBoxes.mem_sitesInBlocks <;> assumption
private theorem card_cell_le (G : CellGrid) (κ : Fin 4 → ℤ) : (G.cell n κ).card ≤ G.side ^ 4 := by
  classical
  have hsub : G.cell n κ ⊆ (Fintype.piFinset fun _ : Fin 4 => Finset.Ico (0 : ℤ) (G.side : ℤ)).image
      fun h : Fin 4 → ℤ => (siteOfInt (fun i => G.offset i + (G.side : ℤ) * κ i + h i) : TorusSite n) := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_image.mpr ⟨h, Fintype.mem_piFinset.mpr fun i => ?_, rfl⟩
    exact Finset.mem_Ico.mpr (hh i)
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Fintype.card_piFinset]
private theorem card_sitesInBlocks_le (L : ℕ) [NeZero L] (S : Finset (TorusSite n)) :
    (sitesInBlocks L S).card ≤ (2 * L + 1) ^ 4 * S.card := by
  classical
  have hsub : sitesInBlocks L S ⊆ S.biUnion fun Y => sitesInBlocks L {Y} := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨parentBlock L x, mem_sitesInBlocks.mp hx, mem_sitesInBlocks.mpr (by simp)⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ Y ∈ S, (sitesInBlocks L {Y}).card ≤ ∑ _Y ∈ S, (2 * L + 1) ^ 4 :=
        Finset.sum_le_sum fun Y _ => TorusCounting.card_sitesInBlocks_singleton_le Y
    _ = (2 * L + 1) ^ 4 * S.card := by simp [mul_comm]
end Counts
private theorem card_cellBelow_le (L : ℕ) [NeZero L] (d : ℕ) : ∀ (n : ℕ) [NeZero n] (c : Finset (TorusSite n)),
    (cellBelow L d n c).card ≤ ((2 * L + 1) ^ 4) ^ d * c.card := by
  induction d with
  | zero =>
    intro n _ c
    show c.card ≤ ((2 * L + 1) ^ 4) ^ 0 * c.card
    rw [pow_zero, one_mul]
  | succ d ih =>
    intro n _ c
    have h := ih (n * L) (sitesInBlocks L c)
    have h' := card_sitesInBlocks_le L c
    calc (cellBelow L (d + 1) n c).card = (cellBelow L d (n * L) (sitesInBlocks L c)).card := rfl
      _ ≤ ((2 * L + 1) ^ 4) ^ d * (sitesInBlocks L c).card := h
      _ ≤ ((2 * L + 1) ^ 4) ^ d * ((2 * L + 1) ^ 4 * c.card) := Nat.mul_le_mul_left _ h'
      _ = ((2 * L + 1) ^ 4) ^ (d + 1) * c.card := by ring
section Supports
variable {n : ℕ} [NeZero n]
private theorem chainConnected_within_component {r : ℕ} {Y X : Finset (TorusSite n)}
    (hX : X ∈ chainComponents r Y) {z z' : TorusSite n}
    (hz : z ∈ X) (h : ChainConnected r Y z z') : ChainConnected r X z z' := by apply _root_.YangMills.Construction.TorusLumps.ClusterSupports.chainConnected_within_component <;> assumption
private theorem isClusterSupport_of_mem_freeSupports (R : StepSetup) (C : Finset (TorusSite n))
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (θ : ClusterSupport R.params.side n) (h : θ ∈ freeSupports R C bad Yt) :
    IsClusterSupport R.params.side R.range θ := by
  classical
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp h
  obtain ⟨hXc, hXb⟩ := Finset.mem_filter.mp hX
  have hcl : X ∈ chainComponents (10 * R.range)
      (bad.image Prod.fst ∪ Yt ∪ sitesInBlocks R.params.side C) := hXc
  have hsites : clusterSupportSites R.params.side (supportOfComponent R.params.side bad Yt X) = X := by
    ext u
    simp only [clusterSupportSites, supportOfComponent, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_inter]
    constructor
    · rintro (⟨b', ⟨_, hb'⟩, rfl⟩ | ⟨_, hu⟩)
      · exact hb'
      · exact hu
    · intro hu
      have huY := subset_of_mem_chainComponents hcl hu
      rcases Finset.mem_union.mp huY with h1 | h1
      · rcases Finset.mem_union.mp h1 with h2 | h2
        · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp h2
          exact Or.inl ⟨b', ⟨hb', hu⟩, rfl⟩
        · exact Or.inr ⟨h2, hu⟩
      · exact absurd ⟨u, Finset.mem_inter.mpr ⟨hu, h1⟩⟩ hXb
  have hne : X.Nonempty := by
    obtain ⟨y, hy, rfl⟩ := mem_chainComponents.mp hcl
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, Relation.ReflTransGen.refl⟩⟩
  refine ⟨by rw [hsites]; exact hne, ?_⟩
  rw [hsites]
  intro y hy z hz
  exact chainConnected_within_component hcl hy (chainConnected_of_mem_chainComponents hcl hy hz)
end Supports
private theorem lt_of_hasLongSupport {ℓ : StepParameters} (T : StageTower ℓ) (k j : ℕ) : ∀ (s n : ℕ) [NeZero n]
    (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)), HasLongSupport T k j s n u c → j < s := by
  intro s
  induction s with
  | zero => intro n _ u c h; exact h.elim
  | succ s ih =>
    intro n _ u c h
    rcases h with ⟨rfl, _⟩ | h
    · exact Nat.lt_succ_self _
    · exact (ih _ _ _ h).trans (Nat.lt_succ_self _)
section Numbers
private theorem clusterRange_le {x : ℝ} (hx : 1 ≤ x) : (clusterRange x : ℝ) ≤ x + 1 := by
  have h0 : 0 ≤ x ^ ((1 : ℝ) / 100) := Real.rpow_nonneg (by linarith) _
  have h1 : x ^ ((1 : ℝ) / 100) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  rw [Real.rpow_one] at h1
  have h2 := Nat.ceil_lt_add_one h0
  simp only [clusterRange]
  linarith
abbrev _root_.YangMills.SharedProofs.p37996 := @clusterRange_le
private theorem le_clusterRange {x M : ℝ} (hM : 0 ≤ M) (h : M ^ 100 ≤ x) : M ≤ (clusterRange x : ℝ) := by
  have h1 : (M ^ 100) ^ ((1 : ℝ) / 100) ≤ x ^ ((1 : ℝ) / 100) :=
    Real.rpow_le_rpow (pow_nonneg hM _) h (by norm_num)
  have h2 : (M ^ 100) ^ ((1 : ℝ) / 100) = M := by
    have h3 : ((1 : ℝ) / 100) = (((100 : ℕ) : ℝ))⁻¹ := by norm_num
    rw [h3]
    exact Real.pow_rpow_inv_natCast hM (by norm_num)
  rw [h2] at h1
  exact h1.trans (Nat.le_ceil _)
private theorem le_baseCellSide (L r : ℕ) (hL : 1 < L) : 2 ^ 7 * r ≤ baseCellSide L r :=
  Nat.le_pow_clog hL _
private theorem baseCellSide_le (L r : ℕ) (hL : 1 < L) (hr : 1 ≤ r) : baseCellSide L r ≤ 2 ^ 7 * r * L := by
  have h1 : 1 < 2 ^ 7 * r := by omega
  have h2 := Nat.pow_pred_clog_lt_self hL h1
  have h3 : 0 < Nat.clog L (2 ^ 7 * r) := Nat.clog_pos hL (by omega)
  obtain ⟨c, hc⟩ : ∃ c, Nat.clog L (2 ^ 7 * r) = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h3).symm⟩
  rw [hc] at h2
  simp only [Nat.pred_succ] at h2
  show L ^ Nat.clog L (2 ^ 7 * r) ≤ _
  rw [hc, pow_succ]
  exact Nat.mul_le_mul_right _ h2.le
private theorem exists_threshold_log_le (c B N M : ℝ) (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ y : ℝ, ∀ x, y ≤ x → 1 ≤ x ∧ M ≤ x ∧ N + 4 * Real.log (x + 2 * B + 1) ≤ 700 * c * x := by
  refine ⟨max 1 (max M ((N + 4 * c * (2 * B + 1) - 4 - 4 * Real.log c) / (696 * c))), fun x hx => ?_⟩
  have h1 : 1 ≤ x := (le_max_left _ _).trans hx
  have h2 : M ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have h3 : (N + 4 * c * (2 * B + 1) - 4 - 4 * Real.log c) / (696 * c) ≤ x :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  refine ⟨h1, h2, ?_⟩
  have hP : 0 < x + 2 * B + 1 := by linarith
  have h4 := Real.log_le_sub_one_of_pos (mul_pos hc hP)
  rw [Real.log_mul hc.ne' hP.ne'] at h4
  rw [div_le_iff₀ (by positivity)] at h3
  nlinarith
private theorem card_mul_exp_le_one {c x P : ℝ} {L side d : ℕ} (hL : 1 ≤ L) (hP : 1 ≤ P)
    (hside : (side : ℝ) ≤ 2 ^ 7 * L * (P * ((d : ℝ) + 1)))
    (h : 41 + 8 * Real.log L + 4 * Real.log P ≤ 700 * c * x) :
    ((((2 * L + 1) ^ 4) ^ d * side ^ 4 : ℕ) : ℝ) *
      (2 * Real.exp (-(7 * c * x * ((100 * (d + 1) : ℕ) : ℝ)))) ≤ 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hP0 : 0 < P := by linarith
  have lL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have lP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have e2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have e3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have ed : (d : ℝ) + 1 ≤ Real.exp d := Real.add_one_le_exp _
  have eL : (L : ℝ) = Real.exp (Real.log L) := (Real.exp_log hL0).symm
  have eP : P = Real.exp (Real.log P) := (Real.exp_log hP0).symm
  have b1 : (2 * (L : ℝ) + 1) ≤ Real.exp (2 + Real.log L) := by
    rw [Real.exp_add, ← eL]
    nlinarith
  have b2 : (side : ℝ) ≤ Real.exp (7 + Real.log L + Real.log P + d) := by
    have e7 : (2 : ℝ) ^ 7 ≤ Real.exp 7 := by
      have : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      gcongr
    refine hside.trans ?_
    rw [Real.exp_add, Real.exp_add, Real.exp_add, ← eL, ← eP]
    have hm : (2 : ℝ) ^ 7 * L * (P * ((d : ℝ) + 1)) = ((2 : ℝ) ^ 7 * L * P) * ((d : ℝ) + 1) := by ring
    rw [hm]
    gcongr
  have b3 : ((((2 * L + 1) ^ 4) ^ d * side ^ 4 : ℕ) : ℝ) ≤
      Real.exp (4 * (d : ℝ) * (2 + Real.log L)) * Real.exp (4 * (7 + Real.log L + Real.log P + d)) := by
    push_cast
    have p1 : ((2 * (L : ℝ) + 1) ^ 4) ^ d ≤ Real.exp (4 * (d : ℝ) * (2 + Real.log L)) := by
      have : Real.exp (4 * (d : ℝ) * (2 + Real.log L)) = (Real.exp (2 + Real.log L) ^ 4) ^ d := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [this]
      gcongr
    have p2 : (side : ℝ) ^ 4 ≤ Real.exp (4 * (7 + Real.log L + Real.log P + d)) := by
      have : Real.exp (4 * (7 + Real.log L + Real.log P + d)) =
          Real.exp (7 + Real.log L + Real.log P + d) ^ 4 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [this]
      gcongr
    exact mul_le_mul p1 p2 (by positivity) (Real.exp_pos _).le
  have hE : 1 + 4 * (d : ℝ) * (2 + Real.log L) + 4 * (7 + Real.log L + Real.log P + d) ≤
      7 * c * x * ((100 * (d + 1) : ℕ) : ℝ) := by
    push_cast
    have m1 : 0 ≤ (d : ℝ) * Real.log L := mul_nonneg hd lL
    have m2 : 0 ≤ (d : ℝ) * Real.log P := mul_nonneg hd lP
    have m3 : ((d : ℝ) + 1) * (41 + 8 * Real.log L + 4 * Real.log P) ≤ ((d : ℝ) + 1) * (700 * c * x) :=
      mul_le_mul_of_nonneg_left h (by linarith)
    nlinarith
  calc ((((2 * L + 1) ^ 4) ^ d * side ^ 4 : ℕ) : ℝ) *
        (2 * Real.exp (-(7 * c * x * ((100 * (d + 1) : ℕ) : ℝ))))
      ≤ (Real.exp (4 * (d : ℝ) * (2 + Real.log L)) * Real.exp (4 * (7 + Real.log L + Real.log P + d))) *
        (Real.exp 1 * Real.exp (-(7 * c * x * ((100 * (d + 1) : ℕ) : ℝ)))) := by
        gcongr
    _ = Real.exp (1 + 4 * (d : ℝ) * (2 + Real.log L) + 4 * (7 + Real.log L + Real.log P + d) -
          7 * c * x * ((100 * (d + 1) : ℕ) : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
end Numbers
section Flow
private theorem abs_couplingFlow_succ_sub_le (ℓ : StepParameters) (hR : ExpansionReturnsAt ℓ) (β : ℝ)
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (t : ℕ)
    (hy : ∀ i ≤ t, ℓ.y₁ ≤ (couplingFlow ℓ β i).1) :
    |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p4489 <;> assumption
end Flow
open Classical in
theorem longSupportsConditionalBound (hF : freeSupportsConditionalBoundStatement)
    (hS : sqrtClusterWeightTailAtBlockStatement) (hU : longSupportUnitCountStatement) :
    longSupportsConditionalBoundStatement := by
  intro a ha
  obtain ⟨L₁, t₁, ht₁, h₁⟩ := hF a ha
  obtain ⟨L₂, t₂, ht₂, h₂⟩ := hS a ha
  obtain ⟨L₃, t₃, ht₃, h₃⟩ := hU a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (t₁ c) (min (t₂ c) (t₃ c)),
    fun c => lt_min (ht₁ c) (lt_min (ht₂ c) (ht₃ c)), ?_⟩
  intro L hodd hL Tb hTa hTL hD hrt
  obtain ⟨y₁, hy₁⟩ := h₁ L hodd ((le_max_left _ _).trans hL) Tb hTa hTL hD (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, hy₂⟩ := h₂ L hodd (((le_max_left _ _).trans (le_max_right _ _)).trans hL) Tb hTa hTL hD
    (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y₃, hy₃⟩ := h₃ L hodd (((le_max_right _ _).trans (le_max_right _ _)).trans hL) Tb hTa hTL hD
    (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hκ₁ : 0 < Tb.κ₁ := lt_min (by have := hD.κ_pos; positivity)
    (by have := hD.cE_pos; have := hD.σ_pos; positivity)
  have hch : 0 < Tb.gasRate := by
    have h1 := hD.cE_pos
    have h2 := hD.κ_pos
    have h3 := hD.σ_pos
    have h4 : 0 < min Tb.cE (min (Tb.κ * Tb.threshold ^ 2) (Tb.κ₁ * Tb.threshold ^ 2)) :=
      lt_min h1 (lt_min (by positivity) (by positivity))
    simp only [ParameterAssignment.gasRate]
    positivity
  obtain ⟨y₄, hy₄⟩ := exists_threshold_log_le Tb.gasRate Tb.B (41 + 8 * Real.log Tb.side)
    (((Tb.side * Tb.n₀ : ℕ) : ℝ) ^ 100) hch (by linarith [hD.B_ge])
  refine ⟨max (max y₁ y₂) (max y₃ y₄), fun y hy hR hW => ?_⟩
  have F := hy₁ y ((le_max_left _ _).trans ((le_max_left _ _).trans hy)) hR hW
  have Su := hy₂ y ((le_max_right _ _).trans ((le_max_left _ _).trans hy)) hR hW
  have U := hy₃ y ((le_max_left _ _).trans ((le_max_right _ _).trans hy)) hR hW
  have hfl : ∀ x, y ≤ x → 1 ≤ x ∧ (((Tb.side * Tb.n₀ : ℕ) : ℝ) ^ 100) ≤ x ∧
      41 + 8 * Real.log Tb.side + 4 * Real.log (x + 2 * Tb.B + 1) ≤ 700 * Tb.gasRate * x :=
    fun x hx => hy₄ x (((le_max_right _ _).trans ((le_max_right _ _).trans hy)).trans hx)
  intro T β j d hrun e G κ S hside hle hSt A hA
  have hL1 : 1 < Tb.side := by
    have h := hD.L_ge
    have h' : (1 : ℕ) < 2 ^ 40 := by norm_num
    omega
  have hxs : ∀ i ≤ j + 1 + d, y ≤ (T.stage i).coupling :=
    fun i hi => (hrun.onFamily.onFamily i hi).le_coupling
  have hxr : ∀ i ≤ j + 1 + d + 1, (T.stage i).coupling = (couplingFlow (Tb.stepParameters y) β i).1 :=
    hrun.onFamily.coupling_eq
  have hβ : y ≤ β := by
    have h1 := hxs 0 (Nat.zero_le _)
    rw [hxr 0 (Nat.zero_le _)] at h1
    exact h1
  have hy0 : HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β) := hW β hβ
  have hmove : ∀ i, i + 1 ≤ j + 1 + d →
      |(T.stage (i + 1)).coupling - (T.stage i).coupling| ≤ 2 * Tb.B := by
    intro i hi
    rw [hxr (i + 1) (by omega), hxr i (by omega)]
    refine abs_couplingFlow_succ_sub_le (Tb.stepParameters y) hR β hy0 i fun i' hi' => ?_
    have h1 := hxs i' (by omega)
    rw [hxr i' (by omega)] at h1
    exact h1
  have hup : ∀ i, i ≤ d →
      (T.stage (j + 1 + i)).coupling ≤ (T.stage j).coupling + 2 * Tb.B * ((i : ℝ) + 1) := by
    intro i
    induction i with
    | zero =>
      intro _
      have h1 := (abs_le.mp (hmove j (by omega))).2
      have h2 : (T.stage (j + 1 + 0)).coupling = (T.stage (j + 1)).coupling := rfl
      rw [h2]
      push_cast
      linarith
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := (abs_le.mp (hmove (j + 1 + i) (by omega))).2
      have h3 : (T.stage (j + 1 + (i + 1))).coupling = (T.stage (j + 1 + i + 1)).coupling := rfl
      rw [h3]
      push_cast
      linarith
  obtain ⟨hj1, _, hjN⟩ := hfl _ (hxs j (by omega))
  obtain ⟨hk1, hkM, _⟩ := hfl _ (hxs (j + 1 + d) le_rfl)
  have hx0 : 0 < (T.stage j).coupling := by linarith
  have hB0 : 0 ≤ Tb.B := by linarith [hD.B_ge]
  have hr_ge : Tb.side * Tb.n₀ ≤ stageRange T (j + 1 + d) := by
    have h1 := le_clusterRange (Nat.cast_nonneg _) hkM
    exact_mod_cast h1
  have hn₀ : 4096 ≤ Tb.n₀ := hD.n₀_ge
  have hr1 : 1 ≤ stageRange T (j + 1 + d) :=
    le_trans (Nat.mul_pos (by omega) (by omega)) hr_ge
  have hcs : baseCellSide Tb.side (stageRange T (j + 1 + d)) ≤ Tb.side ^ e := by
    have h1 : G.side = baseCellSide Tb.side (stageRange T (j + 1 + d)) := hside
    have h2 : 2 * G.side ≤ 2 * Tb.side ^ e := hle
    omega
  have hLe : 2 ^ 7 * stageRange T (j + 1 + d) ≤ Tb.side ^ e := (le_baseCellSide _ _ hL1).trans hcs
  have hblock : IsBlockTorusSide (Tb.stepParameters y)
      (fineSide (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e)) := by
    rw [fineSide_eq]
    have he : e ≠ 0 := by
      rintro rfl
      simp only [pow_zero] at hLe
      omega
    have hLd : 1 ≤ Tb.side ^ d := Nat.one_le_pow _ _ (by omega)
    refine ⟨?_, ?_⟩
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ he) _) _
    · have h1 : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ e * Tb.side ^ d := by
        have h2 : Tb.side ^ e ≤ Tb.side ^ e * Tb.side ^ d := Nat.le_mul_of_pos_right _ (by omega)
        have h3 : 2 * Tb.side ^ e * Tb.side ^ d = 2 * (Tb.side ^ e * Tb.side ^ d) := by ring
        omega
      exact h1
  have hrun' : IsTowerAtParametersMeasurable Tb y T β (j + 1) :=
    ⟨⟨hrun.onFamily.startsAtWilson, fun i hi => hrun.onFamily.coupling_eq i (by omega),
      fun i hi => hrun.onFamily.onFamily i (by omega)⟩, hrun.measurable⟩
  have key := measure_inter_forall_exists_le
    (markedSampleLaw T β (j + 1) (fineSide (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e))) A
    (freeSupportsAt T j (fineSide (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e)))
    (fun θ => clusterWeight (Tb.stepParameters y).side Tb.gasRate (T.stage j).coupling (stageRange T j) θ)
    (fun θ => Real.sqrt (clusterWeight (Tb.stepParameters y).side Tb.gasRate (T.stage j).coupling
      (stageRange T j) θ))
    (8 * Tb.gasRate * (T.stage j).coupling * (100 * ((d : ℝ) + 1)))
    (fun κ' θ => IsClusterSupport (Tb.stepParameters y).side (stageRange T j) θ ∧
      IsLongWithin (Tb.stepParameters y).side (stageRange T j) (windowLength T (j + 1 + d) j) θ
        (sitesInBlocks (Tb.stepParameters y).side (interiorAtDepth (blockDepth T (j + 1 + d) j)
          (cellBelow (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e)
            (G.cell (2 * (Tb.stepParameters y).side ^ e) κ')))))
    (fun κ' => (cellBelow (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e)
        (G.cell (2 * (Tb.stepParameters y).side ^ e) κ')).biUnion fun Y =>
      (supportsAtBlock (Tb.stepParameters y).side (stageRange T j) Y).filter
        fun θ => 100 * (d + 1) ≤ supportUnitCount (Tb.stepParameters y).side (stageRange T j) θ)
    S (fun θ => (Real.exp_pos _).le) (fun θ => Real.sqrt_nonneg _)
    (fun Θ => F T β j hrun' _ hblock Θ A hA) ?_ ?_ ?_
  · refine (measure_mono ?_).trans key
    rintro v ⟨hv, hl⟩
    refine ⟨hv, fun κ' hκ' => ?_⟩
    rcases hl κ' hκ' with ⟨_, θ, hθ, hlong⟩ | h
    · exact ⟨θ, hθ, isClusterSupport_of_mem_freeSupports (T.stage j).toStepSetup _ _ _ θ hθ, hlong⟩
    · exact absurd (lt_of_hasLongSupport T _ j _ _ _ _ h) (lt_irrefl _)
  · rintro κ' hκ' θ ⟨hcl, hlong⟩
    have hlong' := hlong
    obtain ⟨K, hK, ⟨u, hu⟩, _, _⟩ := hlong
    obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp (hK hu)
    have hY := mem_sitesInBlocks.mp hu2
    refine Finset.mem_biUnion.mpr ⟨parentBlock (Tb.stepParameters y).side u, (Finset.mem_filter.mp hY).1,
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl, ?_⟩, ?_⟩⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, Finset.mem_inter.mpr
        ⟨mem_sitesInBlocks.mpr (Finset.mem_singleton_self _), (mem_thickening _ _ _).mpr ⟨u, hu1, ?_⟩⟩⟩
      rw [supDist_self]
      exact Nat.zero_le _
    · have h1 := U T β j d hrun e G κ {κ'} θ hside hle (Finset.singleton_subset_iff.mpr (hSt hκ'))
        (fun κ'' h => by rw [Finset.mem_singleton.mp h]; exact hlong')
      simpa using h1
  · rintro S' θ hsub hl
    have hn := U T β j d hrun e G κ S' θ hside hle (hsub.trans hSt) (fun κ' h => (hl κ' h).2)
    have hn' : (100 * ((d : ℝ) + 1)) * (S'.card : ℝ) ≤
        (supportUnitCount (Tb.stepParameters y).side (stageRange T j) θ : ℝ) := by exact_mod_cast hn
    simp only [clusterWeight]
    rw [← Real.exp_half, ← Real.exp_add, Real.exp_le_exp]
    have h1 : 0 < 8 * Tb.gasRate * (T.stage j).coupling := by positivity
    have h2 := mul_le_mul_of_nonneg_left hn' h1.le
    nlinarith
  · intro κ' _
    have hcard : (cellBelow (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e)
        (G.cell (2 * (Tb.stepParameters y).side ^ e) κ')).card ≤
        ((2 * (Tb.stepParameters y).side + 1) ^ 4) ^ d * G.side ^ 4 :=
      (card_cellBelow_le _ _ _ _).trans (Nat.mul_le_mul_left _ (card_cell_le G κ'))
    have hsd : (G.side : ℝ) ≤ 2 ^ 7 * ((Tb.stepParameters y).side : ℝ) *
        (((T.stage j).coupling + 2 * Tb.B + 1) * ((d : ℝ) + 1)) := by
      have h1 : G.side ≤ 2 ^ 7 * stageRange T (j + 1 + d) * Tb.side :=
        (le_of_eq hside).trans (baseCellSide_le _ _ hL1 hr1)
      have h2 : (stageRange T (j + 1 + d) : ℝ) ≤ (T.stage (j + 1 + d)).coupling + 1 := clusterRange_le hk1
      have h3 := hup d le_rfl
      have h4 : (G.side : ℝ) ≤ 2 ^ 7 * (stageRange T (j + 1 + d) : ℝ) * (Tb.side : ℝ) := by
        exact_mod_cast h1
      have h5 : (stageRange T (j + 1 + d) : ℝ) ≤ ((T.stage j).coupling + 2 * Tb.B + 1) * ((d : ℝ) + 1) := by
        have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith
      have hLp : (0 : ℝ) ≤ (Tb.side : ℝ) := Nat.cast_nonneg _
      calc (G.side : ℝ) ≤ 2 ^ 7 * (stageRange T (j + 1 + d) : ℝ) * (Tb.side : ℝ) := h4
        _ ≤ 2 ^ 7 * (((T.stage j).coupling + 2 * Tb.B + 1) * ((d : ℝ) + 1)) * (Tb.side : ℝ) := by gcongr
        _ = _ := by
          show _ = 2 ^ 7 * (Tb.side : ℝ) * (((T.stage j).coupling + 2 * Tb.B + 1) * ((d : ℝ) + 1))
          ring
    calc _ ≤ _ := sum_biUnion_le_sum_sum _ _ _ fun _ => Real.sqrt_nonneg _
      _ ≤ ∑ _Y ∈ cellBelow (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e)
            (G.cell (2 * (Tb.stepParameters y).side ^ e) κ'),
            2 * Real.exp (-(7 * Tb.gasRate * (T.stage j).coupling * ((100 * (d + 1) : ℕ) : ℝ))) :=
          Finset.sum_le_sum fun Y _ => Su (T.stage j).coupling (hxs j (by omega)) _ Y (100 * (d + 1))
      _ = ((cellBelow (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e)
            (G.cell (2 * (Tb.stepParameters y).side ^ e) κ')).card : ℝ) *
            (2 * Real.exp (-(7 * Tb.gasRate * (T.stage j).coupling * ((100 * (d + 1) : ℕ) : ℝ)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((((2 * (Tb.stepParameters y).side + 1) ^ 4) ^ d * G.side ^ 4 : ℕ) : ℝ) *
            (2 * Real.exp (-(7 * Tb.gasRate * (T.stage j).coupling * ((100 * (d + 1) : ℕ) : ℝ)))) := by
          refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ ≤ 1 := card_mul_exp_le_one (by have := hL1; exact le_of_lt this) (by linarith) hsd hjN
end YangMills.Construction.CellWindows
end
