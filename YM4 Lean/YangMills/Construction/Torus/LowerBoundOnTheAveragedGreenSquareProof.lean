import YangMills.Construction.Torus.ChangeOfDomainAndBoundaryConditionsProof
import YangMills.Construction.Weighted.BlockBumpFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
open GivenChainGeneral
namespace AvgGreenSqLowerBound
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
instance instFintypeBareSite (D : TorusData) : Fintype D.BareSite :=
  @Fintype.ofFinite _ D.bareSite_finite
theorem bond_finite (D : TorusData) : Finite D.Bond := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bond_finite <;> assumption
instance instFintypeBond (D : TorusData) : Fintype D.Bond :=
  @Fintype.ofFinite _ (bond_finite D)
theorem finsum_mem_eq_sum_indicator {α : Type*} [Fintype α] (s : Set α) (f : α → ℝ) :
    ∑ᶠ a ∈ s, f a = ∑ a, s.indicator f a := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
open Classical in
theorem finsum_mem_eq_sum_if {α : Type*} [Fintype α] (s : Set α) (f : α → ℝ) :
    ∑ᶠ a ∈ s, f a = ∑ a, if a ∈ s then f a else 0 := by
  rw [finsum_mem_eq_sum_indicator]
  exact Finset.sum_congr rfl fun a _ => indicator_apply s f a
theorem avgWeight_pos_and_le_one (L n : ℕ) :
    0 < avgWeight L n ∧ avgWeight L n ≤ 1 := by
  induction n with
  | zero => simp [avgWeight]
  | succ n ih =>
    cases n with
    | zero => simp [avgWeight]
    | succ m =>
      have e : avgWeight L (m + 1 + 1) = avgWeight L (m + 1) /
          (((L : ℝ) ^ 2)⁻¹ + avgWeight L (m + 1)) := rfl
      have hc : 0 ≤ ((L : ℝ) ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
      rw [e]
      have hd : 0 < ((L : ℝ) ^ 2)⁻¹ + avgWeight L (m + 1) := by linarith [ih.1]
      exact ⟨div_pos ih.1 hd, (div_le_one hd).2 (by linarith)⟩
theorem sum_if_sum_mul {α ι : Type*} [Fintype α] [Fintype ι] (P : α → Prop) [DecidablePred P]
    (c : ι → ℝ) (t : ι → α → ℝ) :
    (∑ a, if P a then ∑ i, c i * t i a else 0) = ∑ i, c i * ∑ a, if P a then t i a else 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : P a <;> simp [h]
theorem abs_smul_sum_mul_le_sqrt {ι : Type*} [Fintype ι] {k : ℝ} (hk : 0 ≤ k) (p q : ι → ℝ) :
    |k * ∑ i, p i * q i| ≤
      Real.sqrt (k * ∑ i, p i ^ 2) * Real.sqrt (k * ∑ i, q i ^ 2) := by
  have hp : 0 ≤ k * ∑ i, p i ^ 2 := mul_nonneg hk (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [← Real.sqrt_mul hp]
  refine Real.abs_le_sqrt ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p q
  calc (k * ∑ i, p i * q i) ^ 2 = k ^ 2 * (∑ i, p i * q i) ^ 2 := by ring
    _ ≤ k ^ 2 * ((∑ i, p i ^ 2) * ∑ i, q i ^ 2) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by ring
theorem le_sq_mul_of_le_mul_sqrt {P U C : ℝ} (hP : 0 ≤ P) (hU : 0 ≤ U)
    (h : P ≤ C * Real.sqrt P * Real.sqrt U) : P ≤ C ^ 2 * U := by
  rcases hP.eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · have hs : 0 < Real.sqrt P := Real.sqrt_pos.2 h0
    have h1 : Real.sqrt P ≤ C * Real.sqrt U := by
      have h2 : Real.sqrt P * Real.sqrt P ≤ (C * Real.sqrt U) * Real.sqrt P := by
        rw [Real.mul_self_sqrt hP]
        linarith
      exact le_of_mul_le_mul_right h2 hs
    have h3 := pow_le_pow_left₀ hs.le h1 2
    rw [Real.sq_sqrt hP, mul_pow, Real.sq_sqrt hU] at h3
    exact h3
section Bonds
variable {D : TorusData}
theorem bondGrad_sum {ι : Type*} [Fintype ι] (c : ι → ℝ) (t : ι → D.BareSite → ℝ)
    (e : D.Bond) :
    TorusData.bondGrad (fun x => ∑ i, c i * t i x) e =
      ∑ i, c i * TorusData.bondGrad (t i) e := by
  simp only [TorusData.bondGrad, TorusData.bondDiff]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
open Classical in
theorem bareLaplacian_eq_sum (g : D.BareSite → ℝ) (x : D.BareSite) :
    TorusData.bareLaplacian g x = (D.scale 0)⁻¹ *
      ((∑ e : D.Bond, if e.target = x then TorusData.bondGrad g e else 0) -
        ∑ e : D.Bond, if e.source = x then TorusData.bondGrad g e else 0) := by
  unfold TorusData.bareLaplacian
  rw [finsum_mem_eq_sum_if, finsum_mem_eq_sum_if]
  congr 2
  · refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : e.target = x
    · rw [if_pos (show e ∈ {e : D.Bond | e.target = x} from h), if_pos h]
    · rw [if_neg (show e ∉ {e : D.Bond | e.target = x} from h), if_neg h]
  · refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : e.source = x
    · rw [if_pos (show e ∈ {e : D.Bond | e.source = x} from h), if_pos h]
    · rw [if_neg (show e ∉ {e : D.Bond | e.source = x} from h), if_neg h]
theorem bareLaplacian_sum {ι : Type*} [Fintype ι] (c : ι → ℝ) (t : ι → D.BareSite → ℝ)
    (x : D.BareSite) :
    TorusData.bareLaplacian (fun x' => ∑ i, c i * t i x') x =
      ∑ i, c i * TorusData.bareLaplacian (t i) x := by
  classical
  simp only [bareLaplacian_eq_sum, bondGrad_sum]
  rw [sum_if_sum_mul, sum_if_sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem sum_bondGrad_mul_eq (f g : D.BareSite → ℝ) :
    ∑ e : D.Bond, TorusData.bondGrad f e * TorusData.bondGrad g e =
      ∑ x, f x * TorusData.bareLaplacian g x := by
  classical
  have h1 : ∀ p : D.Bond → D.BareSite,
      (∑ x, f x * ∑ e : D.Bond, if p e = x then TorusData.bondGrad g e else 0) =
        ∑ e : D.Bond, f (p e) * TorusData.bondGrad g e := by
    intro p
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [mul_ite]
  have h2 : ∑ x, f x * TorusData.bareLaplacian g x = (D.scale 0)⁻¹ *
      ((∑ x, f x * ∑ e : D.Bond, if e.target = x then TorusData.bondGrad g e else 0) -
        ∑ x, f x * ∑ e : D.Bond, if e.source = x then TorusData.bondGrad g e else 0) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [bareLaplacian_eq_sum]
    ring
  rw [h2, h1 fun e => e.target, h1 fun e => e.source, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [TorusData.bondGrad, TorusData.bondDiff]
  ring
open Classical in
def oppositeEnd (x : D.BareSite) (e : D.Bond) : D.BareSite :=
  if e.source = x then e.target else e.source
open Classical in
def closedNbhd (x : D.BareSite) : Finset D.BareSite :=
  insert x ((Finset.univ.filter fun e : D.Bond => e ∈ TorusData.bondsAtSite x).image (oppositeEnd x))
theorem card_closedNbhd_le (hbonds : ∀ x : D.BareSite, (TorusData.bondsAtSite x).ncard = 2 * 4)
    (x : D.BareSite) : (closedNbhd x).card ≤ 9 := by
  classical
  have h1 : (Finset.univ.filter fun e : D.Bond => e ∈ TorusData.bondsAtSite x).card = 8 := by
    have h2 := hbonds x
    rw [← Set.ncard_coe_finset]
    have h3 : ((Finset.univ.filter fun e : D.Bond => e ∈ TorusData.bondsAtSite x : Finset D.Bond) :
        Set D.Bond) = TorusData.bondsAtSite x := by
      ext e
      simp
    rw [h3, h2]
  unfold closedNbhd
  refine (Finset.card_insert_le _ _).trans ?_
  have := Finset.card_image_le
    (s := Finset.univ.filter fun e : D.Bond => e ∈ TorusData.bondsAtSite x) (f := oppositeEnd x)
  omega
theorem self_mem_closedNbhd (x : D.BareSite) : x ∈ closedNbhd x :=
  Finset.mem_insert_self _ _
theorem mem_closedNbhd_of_adjacent {x x' : D.BareSite} (h : TorusData.Adjacent x x') :
    x' ∈ closedNbhd x := by
  classical
  obtain ⟨e, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨e, ?_, ?_⟩)
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl h1⟩
    · simp [oppositeEnd, h1, h2]
  · by_cases h3 : e.source = x
    · have : x' = x := h1.symm.trans h3
      rw [this]
      exact self_mem_closedNbhd x
    · refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨e, ?_, ?_⟩)
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr h2⟩
      · unfold oppositeEnd
        rw [if_neg h3]
        exact h1
theorem adjacent_symm {x x' : D.BareSite} (h : TorusData.Adjacent x x') :
    TorusData.Adjacent x' x := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, h.symm⟩
end Bonds
section Blocks
variable {D : TorusData} (B : SeparatedChain D)
theorem siteScale_pos (y : D.Space) : 0 < B.siteScale y := scale_pos D _
theorem bareInner_congr {f f' g g' : D.BareSite → ℝ}
    (h : ∀ x ∈ D.bareSites (B.stage 0), f x * f' x = g x * g' x) :
    B.bareInner f f' = B.bareInner g g' := by apply _root_.YangMills.Construction.Weighted.AdmissibleOp.bareInner_congr <;> assumption
theorem bareInner_eq_sum {f : D.BareSite → ℝ}
    (hf : ∀ x, x ∉ D.bareSites (B.stage 0) → f x = 0) (g : D.BareSite → ℝ) :
    B.bareInner f g = D.scale 0 ^ 4 * ∑ x, f x * g x := by
  classical
  unfold SeparatedChain.bareInner
  rw [finsum_mem_eq_sum_if]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x ∈ D.bareSites (B.stage 0)
  · rw [if_pos h]
  · rw [if_neg h, hf x h, zero_mul]
theorem bareInner_self_eq_sum {f : D.BareSite → ℝ}
    (hf : ∀ x, x ∉ D.bareSites (B.stage 0) → f x = 0) :
    B.bareInner f f = D.scale 0 ^ 4 * ∑ x, f x ^ 2 := by
  rw [bareInner_eq_sum B hf]
  simp only [pow_two]
theorem bareInner_self_nonneg (f : D.BareSite → ℝ) : 0 ≤ B.bareInner f f := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bareInner_self_nonneg <;> assumption
theorem block_subset_bareSites (hb : BlockPartition B) {y : D.Space} (hy : y ∈ B.allSites) :
    B.block y ⊆ D.bareSites (B.stage 0) := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.block_subset_bareSites <;> assumption
theorem block_subset_bareSites_of_mem (hb : BlockPartition B) {W : Set D.Space}
    (hW : B.IsBlockUnion W) {y : D.Space} (hy : y ∈ B.sitesIn W) :
    B.block y ⊆ D.bareSites W := by
  obtain ⟨Y, -, hY, rfl⟩ := hW
  have h := hb.sitesIn_iUnion Y hY
  rw [← h] at hy
  intro x hx
  exact mem_iUnion₂.2 ⟨y, hy, hx⟩
theorem bareLaplacian_eq_zero_of_not_mem {y : D.Space} {φ : D.BareSite → ℝ}
    (hφ : ∀ x, x ∉ B.block y → φ x = 0) {x : D.BareSite} (hx : x ∉ B.thickenedBlock y) :
    TorusData.bareLaplacian φ x = 0 := by
  classical
  have hxb : x ∉ B.block y := fun h => hx (Or.inl h)
  have hn : ∀ e : D.Bond, e.target = x ∨ e.source = x → TorusData.bondGrad φ e = 0 := by
    intro e hex
    have h1 : φ e.target = 0 := by
      rcases hex with h | h
      · rw [h]
        exact hφ x hxb
      · exact hφ _ fun ht => hx (Or.inr ⟨e.target, ht, e, Or.inr ⟨h, rfl⟩⟩)
    have h2 : φ e.source = 0 := by
      rcases hex with h | h
      · exact hφ _ fun ht => hx (Or.inr ⟨e.source, ht, e, Or.inl ⟨rfl, h⟩⟩)
      · rw [h]
        exact hφ x hxb
    simp [TorusData.bondGrad, TorusData.bondDiff, h1, h2]
  rw [bareLaplacian_eq_sum, Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero, mul_zero]
  · intro e _
    split_ifs with h
    · exact hn e (Or.inr h)
    · rfl
  · intro e _
    split_ifs with h
    · exact hn e (Or.inl h)
    · rfl
theorem exists_of_mem_thickenedBlock {x : D.BareSite} {y : D.Space}
    (h : x ∈ B.thickenedBlock y) :
    ∃ x' ∈ B.block y, x' ∈ closedNbhd x ∧ x ∈ closedNbhd x' := by
  rcases h with h | ⟨x₀, h₀, hj⟩
  · exact ⟨x, h, self_mem_closedNbhd x, self_mem_closedNbhd x⟩
  · exact ⟨x₀, h₀, mem_closedNbhd_of_adjacent (adjacent_symm hj), mem_closedNbhd_of_adjacent hj⟩
open Classical in
theorem card_thickenedBlock_le (hb : BlockPartition B) (y : D.Space) :
    (Finset.univ.filter fun x => x ∈ B.thickenedBlock y).card ≤
      9 * (Finset.univ.filter fun x => x ∈ B.block y).card := by
  have hsub : (Finset.univ.filter fun x => x ∈ B.thickenedBlock y) ⊆
      (Finset.univ.filter fun x => x ∈ B.block y).biUnion closedNbhd := by
    intro x hx
    obtain ⟨x', h1, -, h3⟩ := exists_of_mem_thickenedBlock B (Finset.mem_filter.1 hx).2
    exact Finset.mem_biUnion.2 ⟨x', Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩, h3⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [mul_comm]
  exact Finset.card_biUnion_le_card_mul _ _ 9 fun x _ => card_closedNbhd_le hb.card_bondsAtSite x
variable [Fintype ↥B.allSites]
theorem layerInner_eq_sum (w w' : B.LayerFn) :
    B.layerInner w w' = ∑ y : ↥B.allSites, B.siteScale y ^ 4 * (w y * w' y) :=
  finsum_eq_sum_of_fintype _
theorem layerInner_self_nonneg (w : B.LayerFn) : 0 ≤ B.layerInner w w := by
  rw [layerInner_eq_sum]
  exact Finset.sum_nonneg fun y _ =>
    mul_nonneg (pow_pos (siteScale_pos B y) 4).le (mul_self_nonneg _)
open Classical in
theorem card_sites_thickened_le (hb : BlockPartition B) (x : D.BareSite) :
    (Finset.univ.filter fun y : ↥B.allSites => x ∈ B.thickenedBlock y).card ≤ 9 := by
  have h : ∀ y : ↥B.allSites, ∃ x', x ∈ B.thickenedBlock y →
      x' ∈ B.block y ∧ x' ∈ closedNbhd x := by
    intro y
    by_cases hy : x ∈ B.thickenedBlock y
    · obtain ⟨x', h1, h2, -⟩ := exists_of_mem_thickenedBlock B hy
      exact ⟨x', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨x, fun h => absurd h hy⟩
  choose g hg using h
  refine (Finset.card_le_card_of_injOn g ?_ ?_).trans (card_closedNbhd_le hb.card_bondsAtSite x)
  · intro y hy
    exact (hg y (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2).2
  · intro y hy y' hy' he
    by_contra hne
    have hd := hb.block_pairwise_disjoint y y.2 y' y'.2 fun h => hne (Subtype.ext h)
    have h1 := (hg y (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2).1
    have h2 := (hg y' (Finset.mem_filter.1 (Finset.mem_coe.1 hy')).2).1
    rw [← he] at h2
    exact Set.disjoint_left.1 hd h1 h2
open Classical in
theorem scale_pow_mul_card_block (hb : BlockPartition B) (hav : B.AvgRelations)
    (y : ↥B.allSites) :
    D.scale 0 ^ 4 * ((Finset.univ.filter fun x => x ∈ B.block y).card : ℝ) =
      B.siteScale y ^ 4 := by
  have h := hav.2.2.2.1 y
  unfold SeparatedChain.bareSpaceNorm at h
  rw [Real.sq_sqrt (bareInner_self_nonneg B _)] at h
  have hf : ∀ x, x ∉ D.bareSites (B.stage 0) → B.blockIndicator y x = 0 := fun x hx =>
    indicator_of_notMem (fun h' => hx (block_subset_bareSites B hb y.2 h')) _
  rw [← h, bareInner_eq_sum B hf]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ B.block y <;> simp [SeparatedChain.blockIndicator, hx]
open Classical in
theorem sum_sq_bareLaplacian_combo_le (hb : BlockPartition B) (hav : B.AvgRelations)
    {φ : ↥B.allSites → D.BareSite → ℝ} (hφ : ∀ y : ↥B.allSites, B.IsBlockBump y (φ y))
    (c : ↥B.allSites → ℝ) :
    D.scale 0 ^ 4 * ∑ x, (∑ y, c y * TorusData.bareLaplacian (φ y) x) ^ 2 ≤
      (9 * testLaplacianConst 4) ^ 2 * ∑ y, c y ^ 2 := by
  have hk : 0 ≤ D.scale 0 ^ 4 := (pow_pos (scale_pos D 0) 4).le
  set C := testLaplacianConst 4 with hC
  let t : ↥B.allSites → ℝ := fun y => c y ^ 2 * (C * (B.siteScale y ^ 2)⁻¹) ^ 2
  have ht : ∀ y, 0 ≤ t y := fun y => by positivity
  have hpt : ∀ x, (∑ y, c y * TorusData.bareLaplacian (φ y) x) ^ 2 ≤
      9 * ∑ y : ↥B.allSites, if x ∈ B.thickenedBlock y then t y else 0 := by
    intro x
    set s := Finset.univ.filter fun y : ↥B.allSites => x ∈ B.thickenedBlock y with hs
    have h1 : ∑ y, c y * TorusData.bareLaplacian (φ y) x =
        ∑ y ∈ s, c y * TorusData.bareLaplacian (φ y) x := by
      rw [hs, Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases h : x ∈ B.thickenedBlock y
      · rw [if_pos h]
      · rw [if_neg h, bareLaplacian_eq_zero_of_not_mem B (hφ y).vanishes_of_not_mem h, mul_zero]
    rw [h1, ← Finset.sum_filter]
    have h2 := sq_sum_le_card_mul_sum_sq (s := s)
      (f := fun y => c y * TorusData.bareLaplacian (φ y) x)
    have h3 : ∑ y ∈ s, (c y * TorusData.bareLaplacian (φ y) x) ^ 2 ≤ ∑ y ∈ s, t y :=
      Finset.sum_le_sum fun y _ => by
        rw [mul_pow]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [← sq_abs (TorusData.bareLaplacian (φ y) x)]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hφ y).abs_laplacian_le x) 2
    have h5 : (s.card : ℝ) ≤ 9 := by exact_mod_cast card_sites_thickened_le B hb x
    have h6 : 0 ≤ ∑ y ∈ s, t y := Finset.sum_nonneg fun y _ => ht y
    calc (∑ y ∈ s, c y * TorusData.bareLaplacian (φ y) x) ^ 2
        ≤ (s.card : ℝ) * ∑ y ∈ s, (c y * TorusData.bareLaplacian (φ y) x) ^ 2 := h2
      _ ≤ (s.card : ℝ) * ∑ y ∈ s, t y := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
      _ ≤ 9 * ∑ y ∈ s, t y := mul_le_mul_of_nonneg_right h5 h6
  have hsum : ∑ x, (∑ y, c y * TorusData.bareLaplacian (φ y) x) ^ 2 ≤
      9 * ∑ y : ↥B.allSites,
        ((Finset.univ.filter fun x => x ∈ B.thickenedBlock y).card : ℝ) * t y := by
    calc ∑ x, (∑ y, c y * TorusData.bareLaplacian (φ y) x) ^ 2
        ≤ ∑ x, 9 * ∑ y : ↥B.allSites, (if x ∈ B.thickenedBlock y then t y else 0) :=
          Finset.sum_le_sum fun x _ => hpt x
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hterm : ∀ y : ↥B.allSites, D.scale 0 ^ 4 *
      (((Finset.univ.filter fun x => x ∈ B.thickenedBlock y).card : ℝ) * t y) ≤
        9 * (C ^ 2 * c y ^ 2) := by
    intro y
    have h1 : ((Finset.univ.filter fun x => x ∈ B.thickenedBlock y).card : ℝ) ≤
        9 * ((Finset.univ.filter fun x => x ∈ B.block y).card : ℝ) := by
      exact_mod_cast card_thickenedBlock_le B hb y
    have h2 := scale_pow_mul_card_block B hb hav y
    have hξ : B.siteScale y ≠ 0 := (siteScale_pos B y).ne'
    calc D.scale 0 ^ 4 *
          (((Finset.univ.filter fun x => x ∈ B.thickenedBlock y).card : ℝ) * t y)
        ≤ D.scale 0 ^ 4 *
          ((9 * ((Finset.univ.filter fun x => x ∈ B.block y).card : ℝ)) * t y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (ht y)) hk
      _ = 9 * ((D.scale 0 ^ 4 *
          ((Finset.univ.filter fun x => x ∈ B.block y).card : ℝ)) * t y) := by ring
      _ = 9 * (B.siteScale y ^ 4 * t y) := by rw [h2]
      _ = 9 * (C ^ 2 * c y ^ 2) := by
          simp only [t]
          field_simp
  calc D.scale 0 ^ 4 * ∑ x, (∑ y, c y * TorusData.bareLaplacian (φ y) x) ^ 2
      ≤ D.scale 0 ^ 4 * (9 * ∑ y : ↥B.allSites,
          ((Finset.univ.filter fun x => x ∈ B.thickenedBlock y).card : ℝ) * t y) :=
        mul_le_mul_of_nonneg_left hsum hk
    _ = 9 * ∑ y : ↥B.allSites, D.scale 0 ^ 4 *
          (((Finset.univ.filter fun x => x ∈ B.thickenedBlock y).card : ℝ) * t y) := by
        rw [mul_left_comm, Finset.mul_sum]
    _ ≤ 9 * ∑ y, 9 * (C ^ 2 * c y ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hterm y) (by norm_num)
    _ = (9 * C) ^ 2 * ∑ y, c y ^ 2 := by
        simp only [← Finset.mul_sum]
        ring
theorem layerInner_avgOp_le (hav : B.AvgRelations) (v : ↥B.bareSpace) :
    B.layerInner (B.avgOp v) (B.avgOp v) ≤ B.bareInner v v := by
  set w := B.avgOp v with hw
  set t := B.avgOpAdjoint w with ht
  have h1 : B.layerInner w w = B.bareInner v t := hav.1 v w
  have h4 : B.avgOp t = w := by
    have := LinearMap.congr_fun hav.2.2.1 w
    simpa using this
  have h2 : B.layerInner w w = B.bareInner t t := by
    have h3 := hav.1 t w
    rwa [h4] at h3
  have hP := layerInner_self_nonneg B w
  have hv := bareInner_self_nonneg B (v : D.BareSite → ℝ)
  have hcs : |B.bareInner v t| ≤
      Real.sqrt (B.bareInner v v) * Real.sqrt (B.bareInner t t) := by
    rw [bareInner_eq_sum B v.2, bareInner_self_eq_sum B v.2, bareInner_self_eq_sum B t.2]
    exact abs_smul_sum_mul_le_sqrt (pow_pos (scale_pos D 0) 4).le _ _
  have h5 : B.layerInner w w ≤
      1 * Real.sqrt (B.layerInner w w) * Real.sqrt (B.bareInner v v) := by
    rw [one_mul, mul_comm]
    calc B.layerInner w w = B.bareInner v t := h1
      _ ≤ |B.bareInner v t| := le_abs_self _
      _ ≤ _ := by rw [h2]; exact hcs
  have h6 := le_sq_mul_of_le_mul_sqrt hP hv h5
  simpa using h6
end Blocks
section Pairs
variable {D : TorusData} (B : SeparatedChain D)
theorem bareInner_comm (f f' : D.BareSite → ℝ) : B.bareInner f f' = B.bareInner f' f := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.bareInner_comm <;> assumption
theorem bareInner_add_left (f f' g : D.BareSite → ℝ) :
    B.bareInner (f + f') g = B.bareInner f g + B.bareInner f' g := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bareInner_add_left <;> assumption
theorem bareInner_smul_left (c : ℝ) (f g : D.BareSite → ℝ) :
    B.bareInner (c • f) g = c * B.bareInner f g := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bareInner_smul_left <;> assumption
def innerBilin (W : Set D.Space) : LinearMap.BilinForm ℝ ↥(B.bareSpaceOn W) :=
  LinearMap.mk₂ ℝ (fun f g => B.bareInner f g)
    (fun f f' g => by
      simpa only [Submodule.coe_add] using bareInner_add_left B f f' g)
    (fun c f g => by
      simp only [Submodule.coe_smul, smul_eq_mul]
      exact bareInner_smul_left B c f g)
    (fun f g g' => by
      simp only [Submodule.coe_add]
      rw [bareInner_comm, bareInner_add_left, bareInner_comm B g, bareInner_comm B g'])
    (fun c f g => by
      simp only [Submodule.coe_smul]
      rw [bareInner_comm, bareInner_smul_left, bareInner_comm B g, smul_eq_mul])
theorem admissibleForm_admissibleGreen (hfin : B.allSites.Finite) {W : Set D.Space}
    {𝔟 : Set D.Bond} (hu : IsUnit (B.admissibleOp W 𝔟)) (v h : ↥(B.bareSpaceOn W)) :
    B.admissibleForm W 𝔟 v (B.admissibleGreen W 𝔟 h) = B.bareInner v h := by apply _root_.YangMills.Construction.Weighted.DomainChange.admissibleForm_green_right <;> assumption
theorem layerEval_of_mem {y : D.Space} (hy : y ∈ B.allSites) (w : B.LayerFn) :
    B.layerEval w y = w ⟨y, hy⟩ := dif_pos hy
theorem block_average_bump (hb : BlockPartition B)
    {φ : ↥B.allSites → D.BareSite → ℝ} (hφ : ∀ y : ↥B.allSites, B.IsBlockBump y (φ y))
    (y y' : ↥B.allSites) :
    ((D.L : ℝ) ^ (B.level y' * 4))⁻¹ * ∑ᶠ x ∈ B.block y', φ y x =
      if y = y' then 1 else 0 := by
  have hL : (D.L : ℝ) ≠ 0 := by
    have := D.blocking.three_le_factor
    have h0 : D.L ≠ 0 := by omega
    exact_mod_cast h0
  by_cases h : y = y'
  · subst h
    rw [(hφ y).sum_eq, if_pos rfl]
    exact inv_mul_cancel₀ (pow_ne_zero _ hL)
  · have h0 : ∀ x ∈ B.block y', φ y x = 0 := fun x hx =>
      (hφ y).vanishes_of_not_mem x fun hx' => Set.disjoint_left.1
        (hb.block_pairwise_disjoint y y.2 y' y'.2 fun e => h (Subtype.ext e)) hx' hx
    rw [finsum_mem_congr rfl h0, if_neg h]
    simp
variable [Fintype ↥B.allSites]
theorem finsum_mem_eq_sum_allSites {S : Set D.Space} (hS : S ⊆ B.allSites) (F : D.Space → ℝ)
    (h : ∀ y : ↥B.allSites, (y : D.Space) ∉ S → F y = 0) :
    ∑ᶠ y ∈ S, F y = ∑ y : ↥B.allSites, F y := by
  rw [← finsum_eq_sum_of_fintype (fun y : ↥B.allSites => F y),
    finsum_set_coe_eq_finsum_mem B.allSites (f := F), finsum_mem_def, finsum_mem_def]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy, indicator_of_mem (hS hy)]
  · rw [indicator_of_notMem hy]
    by_cases hy' : y ∈ B.allSites
    · rw [indicator_of_mem hy', h ⟨y, hy'⟩ hy]
    · rw [indicator_of_notMem hy']
theorem scale_weighted_le_green_sq (hb : BlockPartition B) (hav : B.AvgRelations)
    {φ : ↥B.allSites → D.BareSite → ℝ} (hφ : ∀ y : ↥B.allSites, B.IsBlockBump y (φ y))
    {W : Set D.Space} {𝔟 : Set D.Bond} (hW : B.IsBlockUnion W)
    (hu : IsUnit (B.admissibleOp W 𝔟)) {X : Set ↥B.allSites}
    (hXW : ∀ y ∈ X, (y : D.Space) ∈ B.sitesIn W)
    (hXb : ∀ y ∈ X, B.blockBondSet (y : D.Space) ⊆ 𝔟)
    (ω : B.LayerFn) (hω : ∀ y, y ∉ X → ω y = 0) :
    lowerBoundConst 4 * ∑ y : ↥B.allSites, B.siteScale y ^ 8 * ω y ^ 2 ≤
      B.bareInner
        (B.admissibleGreen W 𝔟 (B.restrictBare W (B.avgOpAdjoint ω)))
        (B.admissibleGreen W 𝔟 (B.restrictBare W (B.avgOpAdjoint ω))) := by
  classical
  have hfin : B.allSites.Finite := toFinite _
  have hk : 0 ≤ D.scale 0 ^ 4 := (pow_pos (scale_pos D 0) 4).le
  set Q : ℝ := ∑ y : ↥B.allSites, B.siteScale y ^ 8 * ω y ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun y _ => by positivity
  let c : ↥B.allSites → ℝ := fun y => B.siteScale y ^ 4 * ω y
  have hcX : ∀ y, y ∉ X → c y = 0 := fun y hy => by
    simp only [c]
    rw [hω y hy, mul_zero]
  have hcQ : ∑ y, c y ^ 2 = Q := by
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [c]
    ring
  let ψf : D.BareSite → ℝ := fun x => ∑ y, c y * φ y x
  have hψ0 : ∀ x, x ∉ D.bareSites (B.stage 0) → ψf x = 0 := fun x hx =>
    Finset.sum_eq_zero fun y _ => by
      rw [(hφ y).vanishes_of_not_mem x (fun h => hx (block_subset_bareSites B hb y.2 h)), mul_zero]
  have hψW : ∀ x, x ∉ D.bareSites W → ψf x = 0 := fun x hx =>
    Finset.sum_eq_zero fun y _ => by
      by_cases hy : y ∈ X
      · rw [(hφ y).vanishes_of_not_mem x
          (fun h => hx (block_subset_bareSites_of_mem B hb hW (hXW y hy) h)), mul_zero]
      · rw [hcX y hy, zero_mul]
  let ψ : ↥(B.bareSpaceOn W) := ⟨ψf, hψ0, hψW⟩
  set f := B.restrictBare W (B.avgOpAdjoint ω) with hf
  set u := B.admissibleGreen W 𝔟 f with hu'
  have hQψ : ∀ y', B.avgOp (B.bareSpaceOnIncl W ψ) y' = c y' := by
    intro y'
    change ((D.L : ℝ) ^ (B.level y' * 4))⁻¹ * ∑ᶠ x ∈ B.block y', ψf x = c y'
    rw [finsum_mem_eq_sum_if]
    simp only [ψf]
    rw [sum_if_sum_mul (fun x => x ∈ B.block y') c φ, Finset.mul_sum]
    have h1 : ∀ y, ((D.L : ℝ) ^ (B.level y' * 4))⁻¹ *
        (c y * ∑ x, if x ∈ B.block y' then φ y x else 0) = c y * if y = y' then 1 else 0 := by
      intro y
      rw [mul_left_comm, ← finsum_mem_eq_sum_if, block_average_bump B hb hφ y y']
    simp only [h1]
    simp
  have hprod : B.bareInner ψf f = Q := by
    have h1 : B.bareInner ψf f = B.bareInner ψf (B.avgOpAdjoint ω) :=
      bareInner_congr B fun x _ => by
        by_cases hx : x ∈ D.bareSites W
        · have h2 : (f : D.BareSite → ℝ) x = (B.avgOpAdjoint ω : D.BareSite → ℝ) x :=
            indicator_of_mem hx _
          rw [h2]
        · rw [hψW x hx, zero_mul, zero_mul]
    rw [h1]
    have h2 : B.layerInner (B.avgOp (B.bareSpaceOnIncl W ψ)) ω =
        B.bareInner ψf (B.avgOpAdjoint ω) := hav.1 (B.bareSpaceOnIncl W ψ) ω
    rw [← h2, layerInner_eq_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hQψ y]
    simp only [c]
    ring
  have hgrad : ∀ e, e ∉ 𝔟 → TorusData.bondGrad ψf e = 0 := by
    intro e hen
    simp only [ψf]
    rw [bondGrad_sum]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : y ∈ X
    · have hne : e ∉ B.blockBondSet y := fun h => hen (hXb y hy h)
      have h1 : e.source ∉ B.block y := fun h => hne (mem_iUnion₂.2 ⟨e.source, h, Or.inl rfl⟩)
      have h2 : e.target ∉ B.block y := fun h => hne (mem_iUnion₂.2 ⟨e.target, h, Or.inr rfl⟩)
      simp [TorusData.bondGrad, TorusData.bondDiff, (hφ y).vanishes_of_not_mem _ h1,
        (hφ y).vanishes_of_not_mem _ h2]
    · rw [hcX y hy, zero_mul]
  set q : ↥B.allSites → ℝ := B.avgOp (B.bareSpaceOnIncl W u) with hq
  have hsplit : B.admissibleForm W 𝔟 ψ u =
      D.scale 0 ^ 4 * ∑ x, (u : D.BareSite → ℝ) x * TorusData.bareLaplacian ψf x +
        ∑ y : ↥B.allSites, avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
          (c y * q y) := by
    unfold SeparatedChain.admissibleForm
    congr 1
    · congr 1
      rw [finsum_mem_eq_sum_if, ← sum_bondGrad_mul_eq]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e ∈ 𝔟
      · rw [if_pos he, mul_comm]
      · rw [if_neg he]
        have : TorusData.bondGrad ψf e = 0 := hgrad e he
        rw [this, mul_zero]
    · rw [finsum_mem_eq_sum_allSites B (fun y hy => hy.1)]
      · refine Finset.sum_congr rfl fun y _ => ?_
        rw [layerEval_of_mem B y.2, layerEval_of_mem B y.2]
        simp only [Subtype.coe_eta]
        rw [hQψ y]
      · intro y hy
        have hyX : y ∉ X := fun h => hy (hXW y h)
        rw [layerEval_of_mem B y.2]
        simp only [Subtype.coe_eta]
        rw [hQψ y, hcX y hyX]
        simp
  have hQeq : Q = D.scale 0 ^ 4 * ∑ x, (u : D.BareSite → ℝ) x * TorusData.bareLaplacian ψf x +
      ∑ y : ↥B.allSites, avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
        (c y * q y) := by
    rw [← hsplit, hu', admissibleForm_admissibleGreen B hfin hu]
    exact hprod.symm
  set U : ℝ := B.bareInner u u with hU
  have hU0 : 0 ≤ U := bareInner_self_nonneg B _
  have hC : 0 ≤ testLaplacianConst 4 := by
    unfold testLaplacianConst
    positivity
  have hT1 : |D.scale 0 ^ 4 *
      ∑ x, (u : D.BareSite → ℝ) x * TorusData.bareLaplacian ψf x| ≤
        9 * testLaplacianConst 4 * Real.sqrt Q * Real.sqrt U := by
    have h1 := abs_smul_sum_mul_le_sqrt hk (u : D.BareSite → ℝ) (TorusData.bareLaplacian ψf)
    have hu0 : ∀ x, x ∉ D.bareSites (B.stage 0) → (u : D.BareSite → ℝ) x = 0 := u.2.1
    rw [← bareInner_self_eq_sum B hu0] at h1
    have h2 : D.scale 0 ^ 4 * ∑ x, TorusData.bareLaplacian ψf x ^ 2 ≤
        (9 * testLaplacianConst 4) ^ 2 * Q := by
      have h3 := sum_sq_bareLaplacian_combo_le B hb hav hφ c
      rw [hcQ] at h3
      have h4 : ∀ x, TorusData.bareLaplacian ψf x =
          ∑ y, c y * TorusData.bareLaplacian (φ y) x := fun x => bareLaplacian_sum c φ x
      simp only [h4]
      exact h3
    have h5 : Real.sqrt (D.scale 0 ^ 4 * ∑ x, TorusData.bareLaplacian ψf x ^ 2) ≤
        9 * testLaplacianConst 4 * Real.sqrt Q := by
      refine (Real.sqrt_le_sqrt h2).trans_eq ?_
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    calc _ ≤ _ := h1
      _ ≤ Real.sqrt U * (9 * testLaplacianConst 4 * Real.sqrt Q) :=
          mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hT2 : |∑ y : ↥B.allSites, avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
      (c y * q y)| ≤ 1 * Real.sqrt Q * Real.sqrt U := by
    have h1 := abs_smul_sum_mul_le_sqrt zero_le_one c
      (fun y => avgWeight D.L (B.level y) * B.siteScale y ^ 2 * q y)
    have e1 : ∑ y : ↥B.allSites, avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
        (c y * q y) = 1 * ∑ y, c y *
          (avgWeight D.L (B.level y) * B.siteScale y ^ 2 * q y) := by
      rw [one_mul]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [e1]
    rw [one_mul (∑ y, c y ^ 2), hcQ] at h1
    have h2 : ∑ y : ↥B.allSites,
        (avgWeight D.L (B.level y) * B.siteScale y ^ 2 * q y) ^ 2 ≤ U := by
      refine le_trans ?_ (layerInner_avgOp_le B hav (B.bareSpaceOnIncl W u))
      rw [layerInner_eq_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      obtain ⟨ha0, ha1⟩ := avgWeight_pos_and_le_one D.L (B.level y)
      have ha : avgWeight D.L (B.level y) ^ 2 ≤ 1 := by nlinarith
      have h3 : 0 ≤ (B.siteScale y ^ 2 * q y) ^ 2 := sq_nonneg _
      calc (avgWeight D.L (B.level y) * B.siteScale y ^ 2 * q y) ^ 2
          = avgWeight D.L (B.level y) ^ 2 * (B.siteScale y ^ 2 * q y) ^ 2 := by ring
        _ ≤ 1 * (B.siteScale y ^ 2 * q y) ^ 2 := mul_le_mul_of_nonneg_right ha h3
        _ = _ := by ring
    rw [one_mul (Real.sqrt Q)]
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by rw [one_mul]; exact h2))
      (Real.sqrt_nonneg _))
  have hbound : Q ≤ (9 * testLaplacianConst 4 + 1) * Real.sqrt Q * Real.sqrt U := by
    calc Q ≤ _ := le_of_eq hQeq
      _ ≤ |D.scale 0 ^ 4 * ∑ x, (u : D.BareSite → ℝ) x * TorusData.bareLaplacian ψf x| +
          |∑ y : ↥B.allSites, avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
            (c y * q y)| := add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ 9 * testLaplacianConst 4 * Real.sqrt Q * Real.sqrt U +
          1 * Real.sqrt Q * Real.sqrt U := add_le_add hT1 hT2
      _ = _ := by ring
  have hfinal := le_sq_mul_of_le_mul_sqrt hQ0 hU0 hbound
  have hbase : lowerBoundBaseConst 4 = 9 * testLaplacianConst 4 + 1 := by
    unfold lowerBoundBaseConst
    norm_num
  have hpos : 0 < lowerBoundBaseConst 4 ^ 2 := by
    rw [hbase]
    positivity
  unfold lowerBoundConst
  rw [inv_mul_le_iff₀ hpos, hbase]
  exact hfinal
end Pairs
section Conclusions
variable {D : TorusData} (B : SeparatedChain D)
theorem scaleOnLayer_pow_apply (n : ℕ) (w : B.LayerFn) (y : ↥B.allSites) :
    (((B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ n) w) y =
      B.siteScale y ^ n * w y := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    change B.siteScale y ^ n * (B.siteScale y * w y) = _
    ring
variable [Fintype ↥B.allSites]
theorem layerSpaceNorm_scale_sq_sq (w : B.LayerFn) :
    B.layerSpaceNorm (((B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 2) w) ^ 2 =
      ∑ y : ↥B.allSites, B.siteScale y ^ 8 * w y ^ 2 := by
  unfold SeparatedChain.layerSpaceNorm
  rw [Real.sq_sqrt (layerInner_self_nonneg B _), layerInner_eq_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [scaleOnLayer_pow_apply]
  ring
theorem admissibleAvgGreenSq_bound (hb : BlockPartition B) (hav : B.AvgRelations)
    {φ : ↥B.allSites → D.BareSite → ℝ} (hφ : ∀ y : ↥B.allSites, B.IsBlockBump y (φ y))
    {W : Set D.Space} {𝔟 : Set D.Bond} (hadm : B.IsAdmissiblePair W 𝔟)
    (hop : B.PairOperatorFacts W 𝔟) {X : Set ↥B.allSites}
    (hXW : ∀ y ∈ X, (y : D.Space) ∈ B.sitesIn W)
    (hXb : ∀ y ∈ X, B.blockBondSet (y : D.Space) ⊆ 𝔟) :
    B.AdmissibleAvgGreenSqLowerBoundOn W 𝔟 X (lowerBoundConst 4) := by
  intro ω hω
  have hk := scale_weighted_le_green_sq B hb hav hφ hadm.1 hop.1 hXW hXb ω hω
  rw [layerSpaceNorm_scale_sq_sq]
  have hcut : ((B.restrictToBlocks W ω : ↥(B.layerSpaceOn W)) : B.LayerFn) = ω := by
    funext y
    by_cases hy : (y : D.Space) ∈ B.sitesIn W
    · exact indicator_of_mem (s := {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}) hy ω
    · have h1 : y ∉ X := fun h => hy (hXW y h)
      rw [hω y h1]
      exact indicator_of_notMem (s := {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}) hy ω
  have h4 := hop.2.2.2.1 (B.restrictToBlocks W ω) (B.restrictToBlocks W ω)
  rw [hcut] at h4
  have hext : B.extendByZeroFromBlocks W (B.admissibleAvgGreenSq W 𝔟) ω =
      (B.admissibleAvgGreenSq W 𝔟 (B.restrictToBlocks W ω) : B.LayerFn) := rfl
  rw [hext, h4]
  exact hk
omit [Fintype ↥B.allSites] in
theorem restrictBare_avgOpAdjoint_eq_sum (hb : BlockPartition B) (hav : B.AvgRelations)
    {W : Set D.Space} {X : Set ↥B.allSites} [Fintype ↥X]
    (ω : B.LayerFn) (hω : ∀ y, y ∉ X → ω y = 0) :
    B.restrictBare W (B.avgOpAdjoint ω) =
      ∑ y : ↥X, ω y • B.blockIndicatorIn W y := by
  classical
  apply Subtype.ext
  funext x
  have hRv : ((∑ y : ↥X, ω y • B.blockIndicatorIn W y : ↥(B.bareSpaceOn W)) :
      D.BareSite → ℝ) x = ∑ y : ↥X, ω y * (B.blockIndicatorIn W y : D.BareSite → ℝ) x := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hL : ((B.restrictBare W (B.avgOpAdjoint ω) : ↥(B.bareSpaceOn W)) :
      D.BareSite → ℝ) x =
        (D.bareSites W).indicator (B.avgOpAdjoint ω : D.BareSite → ℝ) x := rfl
  rw [hRv, hL]
  by_cases hx : x ∈ D.bareSites (B.stage 0) ∩ D.bareSites W
  · have hex : ∃ y, y ∈ B.allSites ∧ x ∈ B.block y := by
      have h1 := hx.1
      rw [← hb.iUnion_block] at h1
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 h1
      exact ⟨y, hy, hxy⟩
    obtain ⟨hc1, hc2⟩ : B.blockCenter x ∈ B.allSites ∧ x ∈ B.block (B.blockCenter x) :=
      Classical.epsilon_spec hex
    set yc : ↥B.allSites := ⟨B.blockCenter x, hc1⟩ with hyc
    have hne : ∀ y : ↥X, (y : ↥B.allSites) ≠ yc →
        (B.blockIndicatorIn W y : D.BareSite → ℝ) x = 0 := by
      intro y hy
      have hnot : x ∉ B.block ((y : ↥B.allSites) : D.Space) := fun h =>
        Set.disjoint_left.1 (hb.block_pairwise_disjoint _ (y : ↥B.allSites).2 _ hc1
          fun e => hy (Subtype.ext e)) h hc2
      change (D.bareSites (B.stage 0) ∩ D.bareSites W).indicator
        (B.blockIndicator ((y : ↥B.allSites) : D.Space)) x = 0
      rw [indicator_of_mem hx]
      exact indicator_of_notMem hnot _
    rw [indicator_of_mem hx.2, hav.2.1 ω x hx.1, layerEval_of_mem B hc1]
    by_cases hX : yc ∈ X
    · rw [Finset.sum_eq_single (⟨yc, hX⟩ : ↥X)]
      · have h1 : (B.blockIndicatorIn W ((⟨yc, hX⟩ : ↥X) : ↥B.allSites) : D.BareSite → ℝ) x = 1 := by
          change (D.bareSites (B.stage 0) ∩ D.bareSites W).indicator
            (B.blockIndicator (B.blockCenter x)) x = 1
          rw [indicator_of_mem hx]
          exact indicator_of_mem hc2 _
        rw [h1, mul_one]
      · intro y _ hy
        rw [hne y fun e => hy (Subtype.ext e), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hω yc hX]
      refine (Finset.sum_eq_zero fun y _ => ?_).symm
      rw [hne y fun e => hX (e ▸ y.2), mul_zero]
  · refine Eq.trans ?_ (Finset.sum_eq_zero fun y _ => ?_).symm
    · by_cases hxW : x ∈ D.bareSites W
      · have hx0 : x ∉ D.bareSites (B.stage 0) := fun h => hx ⟨h, hxW⟩
        rw [indicator_of_mem hxW]
        exact (B.avgOpAdjoint ω).2 x hx0
      · exact indicator_of_notMem hxW _
    · have : (B.blockIndicatorIn W y : D.BareSite → ℝ) x = 0 := indicator_of_notMem hx _
      rw [this, mul_zero]
theorem admissibleScaledMatrix_bound (hb : BlockPartition B) (hav : B.AvgRelations)
    {φ : ↥B.allSites → D.BareSite → ℝ} (hφ : ∀ y : ↥B.allSites, B.IsBlockBump y (φ y))
    {W : Set D.Space} {𝔟 : Set D.Bond} (hadm : B.IsAdmissiblePair W 𝔟)
    (hop : B.PairOperatorFacts W 𝔟) {X : Set ↥B.allSites}
    (hXW : ∀ y ∈ X, (y : D.Space) ∈ B.sitesIn W)
    (hXb : ∀ y ∈ X, B.blockBondSet (y : D.Space) ⊆ 𝔟) :
    B.QuadFormLowerBoundOn X (B.admissibleScaledMatrix W 𝔟) (lowerBoundConst 4) := by
  classical
  intro v
  let ω : B.LayerFn := fun y =>
    if h : y ∈ X then v ⟨y, h⟩ * B.siteScale y ^ (-4 : ℤ) else 0
  have hω : ∀ y, y ∉ X → ω y = 0 := fun y h => dif_neg h
  have hωX : ∀ y : ↥X, ω y = v y * B.siteScale (y : ↥B.allSites) ^ (-4 : ℤ) := fun y =>
    dif_pos y.2
  have hk := scale_weighted_le_green_sq B hb hav hφ hadm.1 hop.1 hXW hXb ω hω
  have hLeft : ∑ y : ↥B.allSites, B.siteScale y ^ 8 * ω y ^ 2 = ∑ᶠ y : ↥X, v y ^ 2 := by
    rw [finsum_eq_sum_of_fintype]
    have h1 : ∑ y : ↥B.allSites, B.siteScale y ^ 8 * ω y ^ 2 =
        ∑ y ∈ Finset.univ.filter (· ∈ X), B.siteScale y ^ 8 * ω y ^ 2 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : y ∈ X
      · rw [if_pos hy]
      · rw [if_neg hy, hω y hy]
        simp
    rw [h1, Finset.sum_subtype (p := (· ∈ X)) (Finset.univ.filter (· ∈ X)) (fun y => by simp)
      (fun y : ↥B.allSites => B.siteScale y ^ 8 * ω y ^ 2)]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h2 := hωX y
    have h3 : B.siteScale (y : ↥B.allSites) ≠ 0 := (siteScale_pos B _).ne'
    change B.siteScale (y : ↥B.allSites) ^ 8 * ω y ^ 2 = _
    rw [h2, zpow_neg, mul_pow]
    have h4 : B.siteScale (y : ↥B.allSites) ^ (4 : ℤ) =
        B.siteScale (y : ↥B.allSites) ^ 4 := by norm_cast
    rw [h4]
    field_simp
  let g : ↥X → ↥(B.bareSpaceOn W) := fun y =>
    B.admissibleGreen W 𝔟 (B.blockIndicatorIn W (y : ↥B.allSites))
  have hG : B.admissibleGreen W 𝔟 (B.restrictBare W (B.avgOpAdjoint ω)) =
      ∑ y : ↥X, ω y • g y := by
    rw [restrictBare_avgOpAdjoint_eq_sum B hb hav ω hω, map_sum]
    exact Finset.sum_congr rfl fun y _ => map_smul _ _ _
  have hRight : ∑ᶠ y : ↥X, ∑ᶠ y' : ↥X, v y * B.admissibleScaledMatrix W 𝔟 y y' * v y' =
      B.bareInner (∑ y : ↥X, ω y • g y : ↥(B.bareSpaceOn W))
        (∑ y : ↥X, ω y • g y : ↥(B.bareSpaceOn W)) := by
    have hbil : ∀ a b : ↥(B.bareSpaceOn W), B.bareInner a b = innerBilin B W a b :=
      fun _ _ => rfl
    rw [hbil, LinearMap.BilinForm.sum_left, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [LinearMap.BilinForm.sum_right, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      hop.2.2.2.2.2 y y' (hXW y y.2) (hXW y' y'.2), hωX, hωX]
    change _ = _ * (_ * B.bareInner (g y) (g y'))
    simp only [g]
    ring
  rw [← hLeft, hRight, ← hG]
  exact hk
end Conclusions
end AvgGreenSqLowerBound
open AvgGreenSqLowerBound in
theorem avgGreenSqLowerBound_holds
    (hop : AvgAndMatrixFacts)
    (hpair : AdmissiblePairOperators)
    (hset : GivenChainGeneralFacts)
    (htest : BlockBumpsExist) :
    AvgGreenSqLowerBoundStatement := by
  intro D B h0
  let G : GivenChain := ⟨D, B, h0⟩
  have hb : BlockPartition B := (hset G).2.2.2.2.1
  have hlc : ShellsAndCubes B := (hset G).2.2.1
  have hav : B.AvgRelations := (hop G).1
  have hp := hpair G
  have hne : ∀ y : ↥B.allSites, ∃ x : D.BareSite, x ∈ B.block y := fun y =>
    hb.block_nonempty y y.2
  choose pt hpt using hne
  have hinj : Function.Injective pt := by
    intro y y' h
    by_contra hyy
    have hd := hb.block_pairwise_disjoint y y.2 y' y'.2 fun e => hyy (Subtype.ext e)
    have h1 := hpt y
    rw [h] at h1
    exact Set.disjoint_left.1 hd h1 (hpt y')
  have hfinite : Finite ↥B.allSites := by
    have := D.bareSite_finite
    exact Finite.of_injective pt hinj
  let _ : Fintype ↥B.allSites := Fintype.ofFinite _
  have htf : ∀ y : ↥B.allSites, ∃ φ : D.BareSite → ℝ, B.IsBlockBump y φ := fun y =>
    htest G y y.2
  choose φ hφ using htf
  obtain ⟨hadm, -, -, -, -, -, -, -, hT⟩ := hp.2
  have hop0 := hp.1 _ _ hadm
  have hall : ∀ y : ↥B.allSites, (y : D.Space) ∈ B.sitesIn (B.stage 0) := by
    intro y
    have h := hb.sitesIn_iUnion B.allSites subset_rfl
    rw [hlc.iUnion_siteCube_eq] at h
    rw [← h]
    exact y.2
  have hbonds : ∀ y : ↥B.allSites, B.blockBondSet (y : D.Space) ⊆ B.initialBonds := by
    intro y e he
    obtain ⟨x, hx, hex⟩ := mem_iUnion₂.1 he
    have hx0 := block_subset_bareSites B hb y.2 hx
    rcases hex with h | h
    · exact Or.inl (h ▸ hx0)
    · exact Or.inr (h ▸ hx0)
  have hbound : B.AvgGreenSqDominatesScaleFourth (lowerBoundConst 4) := by
    intro ω
    have h1 := admissibleAvgGreenSq_bound B hb hav hφ hadm hop0 (X := Set.univ)
      (fun y _ => hall y) (fun y _ => hbonds y) ω (fun y h => absurd (mem_univ y) h)
    have hcut : ((B.restrictToBlocks (B.stage 0) ω : ↥(B.layerSpaceOn (B.stage 0))) :
        B.LayerFn) = ω := by
      funext y
      exact indicator_of_mem
        (s := {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn (B.stage 0)}) (hall y) ω
    have h2 : B.extendByZeroFromBlocks (B.stage 0) (B.admissibleAvgGreenSq (B.stage 0)
        B.initialBonds) ω = B.avgGreenSq ω := by
      have h3 := hT (B.restrictToBlocks (B.stage 0) ω)
      rw [hcut] at h3
      exact h3
    rw [h2, layerSpaceNorm_scale_sq_sq] at h1
    refine le_trans (le_of_eq ?_) h1
    congr 1
    rw [layerInner_eq_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [scaleOnLayer_pow_apply]
    ring
  refine ⟨fun W 𝔟 X hadm' hXW hXb => ?_, hbound, ?_⟩
  · have hop' := hp.1 W 𝔟 hadm'
    exact ⟨admissibleAvgGreenSq_bound B hb hav hφ hadm' hop' hXW hXb,
      admissibleScaledMatrix_bound B hb hav hφ hadm' hop' hXW hXb⟩
  · have hγ : 0 < lowerBoundConst 4 := by
      have hC : 0 ≤ testLaplacianConst 4 := by
        unfold testLaplacianConst
        positivity
      unfold lowerBoundConst lowerBoundBaseConst
      positivity
    have hker : Function.Injective (B.avgGreenSq : Module.End ℝ B.LayerFn) := by
      refine (injective_iff_map_eq_zero _).2 fun ω hω => ?_
      have h1 := hbound ω
      rw [hω, layerInner_eq_sum, layerInner_eq_sum] at h1
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
      have h2 : 0 ≤ ∑ y : ↥B.allSites, B.siteScale y ^ 4 * (ω y *
          (((B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 4) ω) y) :=
        Finset.sum_nonneg fun y _ => by
          rw [scaleOnLayer_pow_apply]
          have h3 : 0 < B.siteScale y := siteScale_pos B y
          have : B.siteScale y ^ 4 * (ω y * (B.siteScale y ^ 4 * ω y)) =
              (B.siteScale y ^ 4 * ω y) ^ 2 := by ring
          rw [this]
          exact sq_nonneg _
      have h3 : ∑ y : ↥B.allSites, B.siteScale y ^ 4 * (ω y *
          (((B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 4) ω) y) = 0 := by
        have h4 := mul_nonneg hγ.le h2
        have h5 : lowerBoundConst 4 * ∑ y : ↥B.allSites, B.siteScale y ^ 4 * (ω y *
            (((B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 4) ω) y) = 0 :=
          le_antisymm h1 h4
        exact (mul_eq_zero.1 h5).resolve_left hγ.ne'
      have h6 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => by
        rw [scaleOnLayer_pow_apply]
        have : B.siteScale y ^ 4 * (ω y * (B.siteScale y ^ 4 * ω y)) =
            (B.siteScale y ^ 4 * ω y) ^ 2 := by ring
        rw [this]
        exact sq_nonneg _).1 h3
      funext y
      have h7 := h6 y (Finset.mem_univ _)
      rw [scaleOnLayer_pow_apply] at h7
      have h8 : B.siteScale y ≠ 0 := (siteScale_pos B y).ne'
      have h9 : (B.siteScale y ^ 4 * ω y) ^ 2 = 0 := by
        rw [← h7]
        ring
      have h10 := pow_eq_zero_iff (two_ne_zero) |>.1 h9
      exact (mul_eq_zero.1 h10).resolve_left (pow_ne_zero _ h8)
    have hsurj := LinearMap.injective_iff_surjective.1 hker
    exact (Module.End.isUnit_iff _).2 ⟨hker, hsurj⟩
end YangMills.Construction.Weighted
end
