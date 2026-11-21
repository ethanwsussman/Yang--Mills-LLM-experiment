import YangMills.Construction.Dirichlet.WeightRecursionBounds
import YangMills.Construction.Torus.BoundsOnTheWeightedDistanceProof
import YangMills.Construction.Torus.CoercivityAndWeightedBoundsOfAnAdmissiblePair
import YangMills.Construction.Weighted.BoxPoincare
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace CoercivityProof
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
instance instFintypeBareSite (D : TorusData) : Fintype D.BareSite :=
  @Fintype.ofFinite _ D.bareSite_finite
theorem bond_finite (D : TorusData) : Finite D.Bond := by
  have := D.bareSite_finite
  refine Finite.of_injective (fun b : D.Bond => (b.source, b.target)) fun b b' h => ?_
  exact TorusData.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
instance instFintypeBond (D : TorusData) : Fintype D.Bond :=
  @Fintype.ofFinite _ (bond_finite D)
theorem finsum_mem_eq_sum_indicator {α : Type*} [Fintype α] (s : Set α) (f : α → ℝ) :
    ∑ᶠ x ∈ s, f x = ∑ x, s.indicator f x := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
theorem finsum_mem_nonneg_of_forall {α : Type*} [Fintype α] (s : Set α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ ∑ᶠ x ∈ s, f x := by
  rw [finsum_mem_eq_sum_indicator]
  exact Finset.sum_nonneg fun x _ => indicator_nonneg (fun y _ => hf y) x
theorem finsum_mem_mono_of_subset {α : Type*} [Fintype α] {s s' : Set α} (h : s ⊆ s')
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : ∑ᶠ x ∈ s, f x ≤ ∑ᶠ x ∈ s', f x := by
  rw [finsum_mem_eq_sum_indicator, finsum_mem_eq_sum_indicator]
  exact Finset.sum_le_sum fun x _ => indicator_le_indicator_of_subset h hf x
theorem fintype_sum_eq_finsum_mem {α : Type*} [Fintype α] (s : Set α) {f : α → ℝ}
    (hf : ∀ x, x ∉ s → f x = 0) : ∑ x, f x = ∑ᶠ x ∈ s, f x := by
  rw [finsum_mem_eq_sum_indicator]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, hf x hx]
def bondDir {D : TorusData} (b : D.Bond) : Fin 4 := Classical.choose b.isPositive
theorem bondDir_spec {D : TorusData} (b : D.Bond) :
    (b.target : D.Space) - (b.source : D.Space) = D.unitStep (bondDir b) :=
  Classical.choose_spec b.isPositive
theorem source_dir_injective {D : TorusData} :
    Function.Injective fun b : D.Bond => (b.source, bondDir b) := by
  intro b b' h
  have h1 : b.source = b'.source := congrArg Prod.fst h
  have h2 : bondDir b = bondDir b' := congrArg Prod.snd h
  refine TorusData.Bond.ext h1 (Subtype.ext ?_)
  have e1 := bondDir_spec b
  have e2 := bondDir_spec b'
  rw [← h2, ← h1] at e2
  have := e1.trans e2.symm
  exact sub_left_injective this
theorem target_dir_injective {D : TorusData} :
    Function.Injective fun b : D.Bond => (b.target, bondDir b) := by
  intro b b' h
  have h1 : b.target = b'.target := congrArg Prod.fst h
  have h2 : bondDir b = bondDir b' := congrArg Prod.snd h
  refine TorusData.Bond.ext (Subtype.ext ?_) h1
  have e1 := bondDir_spec b
  have e2 := bondDir_spec b'
  rw [← h2, ← h1] at e2
  have := e1.trans e2.symm
  exact sub_right_injective this
theorem sum_endpoint_le {D : TorusData} (e : D.Bond → D.BareSite)
    (hinj : Function.Injective fun b : D.Bond => (e b, bondDir b))
    (S : Finset D.Bond) {p : D.BareSite → ℝ} (hp : ∀ x, 0 ≤ p x) :
    ∑ b ∈ S, p (e b) ≤ 4 * ∑ x, p x := by
  classical
  have h1 : ∑ b ∈ S, p (e b) =
      ∑ z ∈ S.image (fun b => (e b, bondDir b)), p z.1 := by
    rw [Finset.sum_image fun a _ b _ h => hinj h]
  have h2 : ∑ z ∈ S.image (fun b => (e b, bondDir b)), p z.1 ≤
      ∑ z : D.BareSite × Fin 4, p z.1 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hp _
  rw [h1]
  refine h2.trans_eq ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp
theorem siteNorm_sq {D : TorusData} (E : Set D.BareSite) (f : D.BareSite → ℝ) :
    TorusData.siteNorm E f ^ 2 = D.scale 0 ^ 4 * ∑ᶠ x ∈ E, f x ^ 2 := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.siteNorm_sq_eq <;> assumption
theorem bondNorm_sq {D : TorusData} (S : Set D.Bond) (A : D.Bond → ℝ) :
    TorusData.bondNorm S A ^ 2 = D.scale 0 ^ 4 * ∑ᶠ b ∈ S, A b ^ 2 :=
  Real.sq_sqrt (mul_nonneg (pow_pos (scale_pos D 0) 4).le
    (finsum_mem_nonneg_of_forall S fun _ => sq_nonneg _))
theorem siteNorm_nonneg {D : TorusData} (E : Set D.BareSite) (f : D.BareSite → ℝ) :
    0 ≤ TorusData.siteNorm E f := Real.sqrt_nonneg _
theorem bondNorm_nonneg {D : TorusData} (S : Set D.Bond) (A : D.Bond → ℝ) :
    0 ≤ TorusData.bondNorm S A := Real.sqrt_nonneg _
theorem bondNorm_mono {D : TorusData} {S S' : Set D.Bond} (h : S ⊆ S') (A : D.Bond → ℝ) :
    TorusData.bondNorm S A ≤ TorusData.bondNorm S' A :=
  Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (finsum_mem_mono_of_subset h fun _ => sq_nonneg _) (pow_pos (scale_pos D 0) 4).le)
theorem siteNorm_le_mul {D : TorusData} {E : Set D.BareSite} {f g : D.BareSite → ℝ} {τ : ℝ}
    (hτ : 0 ≤ τ) (h : ∀ x ∈ E, |f x| ≤ τ * |g x|) :
    TorusData.siteNorm E f ≤ τ * TorusData.siteNorm E g := by
  have hc : 0 ≤ D.scale 0 ^ 4 := (pow_pos (scale_pos D 0) 4).le
  unfold TorusData.siteNorm
  have hs : τ * Real.sqrt (D.scale 0 ^ 4 * ∑ᶠ x ∈ E, g x ^ 2) =
      Real.sqrt (τ ^ 2 * (D.scale 0 ^ 4 * ∑ᶠ x ∈ E, g x ^ 2)) := by
    rw [Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ]
  rw [hs]
  refine Real.sqrt_le_sqrt ?_
  rw [finsum_mem_eq_sum_indicator, finsum_mem_eq_sum_indicator, mul_left_comm,
    Finset.mul_sum (a := τ ^ 2)]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) hc
  by_cases hx : x ∈ E
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    have := h x hx
    have h2 : |f x| ^ 2 ≤ (τ * |g x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    rwa [sq_abs, mul_pow, sq_abs] at h2
  · simp [indicator_of_notMem hx]
theorem bondNorm_le_of_le_add {D : TorusData} {S : Set D.Bond} {A P Q : D.Bond → ℝ} {s : ℝ}
    (hs : 0 ≤ s) (h : ∀ b ∈ S, |A b| ≤ s * (P b + Q b)) :
    TorusData.bondNorm S A ≤ s * (TorusData.bondNorm S P + TorusData.bondNorm S Q) := by
  classical
  have hc : 0 ≤ D.scale 0 ^ 4 := (pow_pos (scale_pos D 0) 4).le
  set c : ℝ := D.scale 0 ^ 4 with hcdef
  set Sf : Finset D.Bond := Finset.univ.filter (· ∈ S) with hSf
  have hsum : ∀ r : D.Bond → ℝ, ∑ᶠ b ∈ S, r b = ∑ b ∈ Sf, r b := by
    intro r
    rw [finsum_mem_eq_sum_indicator, hSf, Finset.sum_filter]
    exact Finset.sum_congr rfl fun b _ => by simp [indicator]
  have hP2 : TorusData.bondNorm S P ^ 2 = c * ∑ b ∈ Sf, P b ^ 2 := by
    rw [bondNorm_sq, hsum]
  have hQ2 : TorusData.bondNorm S Q ^ 2 = c * ∑ b ∈ Sf, Q b ^ 2 := by
    rw [bondNorm_sq, hsum]
  have hcs : ∑ b ∈ Sf, P b * Q b ≤
      Real.sqrt (∑ b ∈ Sf, P b ^ 2) * Real.sqrt (∑ b ∈ Sf, Q b ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hPQ : c * ∑ b ∈ Sf, P b * Q b ≤ TorusData.bondNorm S P * TorusData.bondNorm S Q := by
    have e1 : TorusData.bondNorm S P = Real.sqrt c * Real.sqrt (∑ b ∈ Sf, P b ^ 2) := by
      unfold TorusData.bondNorm
      rw [Real.sqrt_mul hc, hsum]
    have e2 : TorusData.bondNorm S Q = Real.sqrt c * Real.sqrt (∑ b ∈ Sf, Q b ^ 2) := by
      unfold TorusData.bondNorm
      rw [Real.sqrt_mul hc, hsum]
    have e3 : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
    rw [e1, e2]
    calc c * ∑ b ∈ Sf, P b * Q b
        ≤ c * (Real.sqrt (∑ b ∈ Sf, P b ^ 2) * Real.sqrt (∑ b ∈ Sf, Q b ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs hc
      _ = _ := by
          nth_rewrite 1 [← e3]
          ring
  have hnP := bondNorm_nonneg S P
  have hnQ := bondNorm_nonneg S Q
  have hbound : TorusData.bondNorm S A ^ 2 ≤
      (s * (TorusData.bondNorm S P + TorusData.bondNorm S Q)) ^ 2 := by
    have hA : ∑ b ∈ Sf, A b ^ 2 ≤ ∑ b ∈ Sf, s ^ 2 * (P b ^ 2 + 2 * (P b * Q b) + Q b ^ 2) := by
      refine Finset.sum_le_sum fun b hb => ?_
      have h1 := h b (Finset.mem_filter.1 hb).2
      have h2 : |A b| ^ 2 ≤ (s * (P b + Q b)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at h2
      nlinarith
    rw [bondNorm_sq, hsum]
    have e : ∑ b ∈ Sf, s ^ 2 * (P b ^ 2 + 2 * (P b * Q b) + Q b ^ 2) =
        s ^ 2 * (∑ b ∈ Sf, P b ^ 2 + 2 * ∑ b ∈ Sf, P b * Q b + ∑ b ∈ Sf, Q b ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    rw [e] at hA
    have h3 : c * ∑ b ∈ Sf, A b ^ 2 ≤
        c * (s ^ 2 * (∑ b ∈ Sf, P b ^ 2 + 2 * ∑ b ∈ Sf, P b * Q b + ∑ b ∈ Sf, Q b ^ 2)) :=
      mul_le_mul_of_nonneg_left hA hc
    have h4 : c * (s ^ 2 * (∑ b ∈ Sf, P b ^ 2 + 2 * ∑ b ∈ Sf, P b * Q b + ∑ b ∈ Sf, Q b ^ 2)) =
        s ^ 2 * (c * ∑ b ∈ Sf, P b ^ 2 + 2 * (c * ∑ b ∈ Sf, P b * Q b) +
          c * ∑ b ∈ Sf, Q b ^ 2) := by ring
    rw [h4, ← hP2, ← hQ2] at h3
    refine h3.trans ?_
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    have : TorusData.bondNorm S P ^ 2 + 2 * (c * ∑ b ∈ Sf, P b * Q b) +
        TorusData.bondNorm S Q ^ 2 ≤ (TorusData.bondNorm S P + TorusData.bondNorm S Q) ^ 2 := by
      nlinarith
    calc _ ≤ s ^ 2 * (TorusData.bondNorm S P + TorusData.bondNorm S Q) ^ 2 :=
          mul_le_mul_of_nonneg_left this hs2
      _ = _ := by ring
  exact (sq_le_sq₀ (bondNorm_nonneg S A) (mul_nonneg hs (add_nonneg hnP hnQ))).1 hbound
end CoercivityProof
namespace CoercivityProof
variable {D : TorusData} (B : SeparatedChain D)
open GivenChainGeneral
theorem block_subset_stage (hb : BlockPartition B) {y : D.Space} (hy : y ∈ B.allSites) :
    B.block y ⊆ D.bareSites (B.stage 0) := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.block_subset_bareSites <;> assumption
theorem blockCenter_eq (hb : BlockPartition B) {y : D.Space} (hy : y ∈ B.allSites)
    {x : D.BareSite} (hx : x ∈ B.block y) : B.blockCenter x = y := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.blockCenter_eq <;> assumption
theorem bareScale_eq (hb : BlockPartition B) {y : D.Space} (hy : y ∈ B.allSites)
    {x : D.BareSite} (hx : x ∈ B.block y) : B.bareScale x = B.siteScale y := by
  unfold SeparatedChain.bareScale
  rw [blockCenter_eq B hb hy hx]
theorem bareScale_pos (x : D.BareSite) : 0 < B.bareScale x := scale_pos D _
theorem siteScale_pos (y : D.Space) : 0 < B.siteScale y := scale_pos D _
theorem finite_allSites (hb : BlockPartition B) : B.allSites.Finite := by
  have := D.bareSite_finite
  refine (finite_range B.blockCenter).subset fun y hy => ?_
  obtain ⟨x, hx⟩ := hb.block_nonempty y hy
  exact ⟨x, blockCenter_eq B hb hy hx⟩
theorem finite_sitesIn (hfin : B.allSites.Finite) (W : Set D.Space) :
    (B.sitesIn W).Finite :=
  hfin.subset fun _ hy => hy.1
theorem bareSites_eq_iUnion_block (hb : BlockPartition B) {W : Set D.Space}
    (hW : B.IsBlockUnion W) : D.bareSites W = ⋃ y ∈ B.sitesIn W, B.block y := by
  obtain ⟨Y, -, hY, rfl⟩ := hW
  rw [← hb.sitesIn_iUnion Y hY]
  exact hb.bareSites_iUnion Y hY
theorem bareSites_subset_stage (hb : BlockPartition B) {W : Set D.Space}
    (hW : B.IsBlockUnion W) : D.bareSites W ⊆ D.bareSites (B.stage 0) := by
  rw [bareSites_eq_iUnion_block B hb hW]
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
  exact block_subset_stage B hb hy.1 hxy
theorem finsum_bareSites_eq_blocks (hb : BlockPartition B) {W : Set D.Space}
    (hW : B.IsBlockUnion W) (g : D.BareSite → ℝ) :
    ∑ᶠ x ∈ D.bareSites W, g x = ∑ᶠ y ∈ B.sitesIn W, ∑ᶠ x ∈ B.block y, g x := by
  rw [bareSites_eq_iUnion_block B hb hW]
  exact finsum_mem_biUnion
    (fun y hy y' hy' hne => hb.block_pairwise_disjoint y hy.1 y' hy'.1 hne)
    (finite_sitesIn B (finite_allSites B hb) W) (fun _ _ => toFinite _)
theorem bareInner_self_nonneg (f : D.BareSite → ℝ) : 0 ≤ B.bareInner f f :=
  mul_nonneg (pow_pos (scale_pos D 0) 4).le
    (finsum_mem_nonneg_of_forall _ fun x => mul_self_nonneg (f x))
theorem bareSpaceNorm_sq (f : D.BareSite → ℝ) : B.bareSpaceNorm f ^ 2 = B.bareInner f f :=
  Real.sq_sqrt (bareInner_self_nonneg B f)
theorem bareSpaceNorm_sq_eq_sum {g : D.BareSite → ℝ}
    (hg : ∀ x, x ∉ D.bareSites (B.stage 0) → g x = 0) :
    B.bareSpaceNorm g ^ 2 = D.scale 0 ^ 4 * ∑ x, g x ^ 2 := by
  rw [bareSpaceNorm_sq]
  unfold SeparatedChain.bareInner
  congr 1
  rw [fintype_sum_eq_finsum_mem (D.bareSites (B.stage 0)) (f := fun x => g x ^ 2)
    (fun x hx => by simp [hg x hx])]
  exact finsum_mem_congr rfl fun x _ => (pow_two _).symm
theorem bareInner_comm (f f' : D.BareSite → ℝ) : B.bareInner f f' = B.bareInner f' f := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.bareInner_comm <;> assumption
theorem bareInner_add_left (f f' g : D.BareSite → ℝ) :
    B.bareInner (f + f') g = B.bareInner f g + B.bareInner f' g := by
  unfold SeparatedChain.bareInner
  rw [← mul_add]
  congr 1
  simp only [finsum_mem_eq_sum_indicator, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ D.bareSites (B.stage 0) <;> simp [hx, add_mul]
theorem bareInner_smul_left (c : ℝ) (f g : D.BareSite → ℝ) :
    B.bareInner (c • f) g = c * B.bareInner f g := by
  unfold SeparatedChain.bareInner
  rw [mul_left_comm]
  congr 1
  simp only [finsum_mem_eq_sum_indicator, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ D.bareSites (B.stage 0) <;> simp [hx, mul_assoc]
theorem bareInner_le (f g : D.BareSite → ℝ) :
    B.bareInner f g ≤ B.bareSpaceNorm f * B.bareSpaceNorm g := by
  classical
  have hc : 0 ≤ D.scale 0 ^ 4 := (pow_pos (scale_pos D 0) 4).le
  set c : ℝ := D.scale 0 ^ 4 with hcdef
  set Sf : Finset D.BareSite := Finset.univ.filter (· ∈ D.bareSites (B.stage 0)) with hSf
  have hsum : ∀ r : D.BareSite → ℝ, ∑ᶠ x ∈ D.bareSites (B.stage 0), r x = ∑ x ∈ Sf, r x := by
    intro r
    rw [finsum_mem_eq_sum_indicator, hSf, Finset.sum_filter]
    exact Finset.sum_congr rfl fun b _ => by simp [indicator]
  have hn : ∀ r : D.BareSite → ℝ,
      B.bareSpaceNorm r = Real.sqrt c * Real.sqrt (∑ x ∈ Sf, r x ^ 2) := by
    intro r
    unfold SeparatedChain.bareSpaceNorm SeparatedChain.bareInner
    rw [Real.sqrt_mul hc, hsum]
    simp only [pow_two]
  have e3 : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
  unfold SeparatedChain.bareInner
  rw [hsum, hn f, hn g]
  calc c * ∑ x ∈ Sf, f x * g x
      ≤ c * (Real.sqrt (∑ x ∈ Sf, f x ^ 2) * Real.sqrt (∑ x ∈ Sf, g x ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hc
    _ = _ := by
        nth_rewrite 1 [← e3]
        ring
theorem bareSpaceNorm_le_mul {f g : D.BareSite → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (h : ∀ x ∈ D.bareSites (B.stage 0), |f x| ≤ τ * |g x|) :
    B.bareSpaceNorm f ≤ τ * B.bareSpaceNorm g := by
  have e : ∀ r : D.BareSite → ℝ,
      B.bareSpaceNorm r = TorusData.siteNorm (D.bareSites (B.stage 0)) r := by
    intro r
    unfold SeparatedChain.bareSpaceNorm SeparatedChain.bareInner TorusData.siteNorm
    simp only [pow_two]
  rw [e f, e g]
  exact siteNorm_le_mul hτ h
theorem siteNorm_block_le (hb : BlockPartition B) {y : D.Space} (hy : y ∈ B.allSites)
    (f : D.BareSite → ℝ) : TorusData.siteNorm (B.block y) f ≤ B.bareSpaceNorm f := by
  unfold SeparatedChain.bareSpaceNorm SeparatedChain.bareInner TorusData.siteNorm
  refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ (pow_pos (scale_pos D 0) 4).le)
  simp only [← pow_two]
  exact finsum_mem_mono_of_subset (block_subset_stage B hb hy) fun _ => sq_nonneg _
theorem bondGrad_add (f f' : D.BareSite → ℝ) (b : D.Bond) :
    TorusData.bondGrad (f + f') b = TorusData.bondGrad f b + TorusData.bondGrad f' b := by
  simp only [TorusData.bondGrad, TorusData.bondDiff, Pi.add_apply]
  ring
theorem bondGrad_smul (c : ℝ) (f : D.BareSite → ℝ) (b : D.Bond) :
    TorusData.bondGrad (c • f) b = c * TorusData.bondGrad f b := by
  simp only [TorusData.bondGrad, TorusData.bondDiff, Pi.smul_apply, smul_eq_mul]
  ring
theorem admissibleForm_eq_sum (hfin : B.allSites.Finite) (W : Set D.Space) (𝔟 : Set D.Bond)
    (f f' : ↥(B.bareSpaceOn W)) :
    B.admissibleForm W 𝔟 f f' =
      D.scale 0 ^ 4 * ∑ b ∈ (toFinite 𝔟).toFinset,
          TorusData.bondGrad (f : D.BareSite → ℝ) b * TorusData.bondGrad (f' : D.BareSite → ℝ) b +
        ∑ y ∈ (finite_sitesIn B hfin W).toFinset,
          avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
            (B.layerEval (B.avgOp (B.bareSpaceOnIncl W f)) y *
              B.layerEval (B.avgOp (B.bareSpaceOnIncl W f')) y) := by
  unfold SeparatedChain.admissibleForm
  rw [finsum_mem_eq_finite_toFinset_sum _ (toFinite 𝔟),
    finsum_mem_eq_finite_toFinset_sum _ (finite_sitesIn B hfin W)]
theorem admissibleForm_comm (W : Set D.Space) (𝔟 : Set D.Bond) (f f' : ↥(B.bareSpaceOn W)) :
    B.admissibleForm W 𝔟 f f' = B.admissibleForm W 𝔟 f' f := by
  unfold SeparatedChain.admissibleForm
  congr 1
  · congr 1
    exact finsum_mem_congr rfl fun b _ => mul_comm _ _
  · exact finsum_mem_congr rfl fun y _ => by ring
theorem admissibleForm_add_left (hfin : B.allSites.Finite) (W : Set D.Space) (𝔟 : Set D.Bond)
    (f f' g : ↥(B.bareSpaceOn W)) :
    B.admissibleForm W 𝔟 (f + f') g = B.admissibleForm W 𝔟 f g + B.admissibleForm W 𝔟 f' g := by
  simp only [admissibleForm_eq_sum B hfin, map_add, Submodule.coe_add, bondGrad_add, add_mul,
    Finset.sum_add_distrib, mul_add, Pi.add_apply]
  ring
theorem admissibleForm_smul_left (hfin : B.allSites.Finite) (W : Set D.Space) (𝔟 : Set D.Bond)
    (c : ℝ) (f g : ↥(B.bareSpaceOn W)) :
    B.admissibleForm W 𝔟 (c • f) g = c * B.admissibleForm W 𝔟 f g := by
  simp only [admissibleForm_eq_sum B hfin, map_smul, Submodule.coe_smul, bondGrad_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [mul_add]
  congr 1
  · rw [mul_left_comm, Finset.mul_sum (a := c)]
    congr 1
    exact Finset.sum_congr rfl fun b _ => by ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
def admissibleBilin (hfin : B.allSites.Finite) (W : Set D.Space) (𝔟 : Set D.Bond) :
    LinearMap.BilinForm ℝ ↥(B.bareSpaceOn W) :=
  LinearMap.mk₂ ℝ (B.admissibleForm W 𝔟) (admissibleForm_add_left B hfin W 𝔟)
    (fun c f g => by rw [admissibleForm_smul_left B hfin, smul_eq_mul])
    (fun f g g' => by
      rw [admissibleForm_comm B W 𝔟 f, admissibleForm_add_left B hfin,
        admissibleForm_comm B W 𝔟 g, admissibleForm_comm B W 𝔟 g'])
    (fun c f g => by
      rw [admissibleForm_comm B W 𝔟 f, admissibleForm_smul_left B hfin,
        admissibleForm_comm B W 𝔟 g, smul_eq_mul])
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
theorem eq_zero_of_bareInner_self {f : D.BareSite → ℝ}
    (hf : ∀ x, x ∉ D.bareSites (B.stage 0) → f x = 0) (h : B.bareInner f f = 0) : f = 0 := by
  have h2 := bareSpaceNorm_sq_eq_sum B hf
  rw [bareSpaceNorm_sq, h] at h2
  have hc : D.scale 0 ^ 4 ≠ 0 := (pow_pos (scale_pos D 0) 4).ne'
  have h0 := (mul_eq_zero.1 h2.symm).resolve_left hc
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => sq_nonneg (f x)).1 h0
  funext x
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (h1 x (Finset.mem_univ _))
theorem innerBilin_nondegenerate (W : Set D.Space) : (innerBilin B W).Nondegenerate := by
  have key : ∀ f : ↥(B.bareSpaceOn W), B.bareInner f f = 0 → f = 0 := fun f h =>
    Subtype.ext (eq_zero_of_bareInner_self B f.2.1 h)
  exact ⟨fun f h => key f (h f), fun f h => key f (h f)⟩
theorem exists_admissibleFormOp (hfin : B.allSites.Finite) (W : Set D.Space) (𝔟 : Set D.Bond) :
    ∃ T, B.IsAdmissibleFormOp W 𝔟 T := by
  have := D.bareSite_finite
  have hT : ∀ f g : ↥(B.bareSpaceOn W), B.bareInner
      (LinearMap.BilinForm.symmCompOfNondegenerate (admissibleBilin B hfin W 𝔟) (innerBilin B W)
        (innerBilin_nondegenerate B W) f : ↥(B.bareSpaceOn W)) g =
      B.admissibleForm W 𝔟 f g := fun f g =>
    LinearMap.BilinForm.symmCompOfNondegenerate_left_apply (admissibleBilin B hfin W 𝔟)
      (innerBilin_nondegenerate B W) g f
  refine ⟨LinearMap.BilinForm.symmCompOfNondegenerate (admissibleBilin B hfin W 𝔟)
    (innerBilin B W) (innerBilin_nondegenerate B W), fun f g => ?_, fun f g => ?_⟩
  · rw [hT, bareInner_comm, hT, admissibleForm_comm]
  · rw [bareInner_comm, hT, admissibleForm_comm]
theorem admissibleOp_spec (hfin : B.allSites.Finite) (W : Set D.Space) (𝔟 : Set D.Bond) :
    B.IsAdmissibleFormOp W 𝔟 (B.admissibleOp W 𝔟) :=
  Classical.epsilon_spec (exists_admissibleFormOp B hfin W 𝔟)
def mulOp (m : D.BareSite → ℝ) : ↥B.bareSpace →ₗ[ℝ] ↥B.bareSpace where
  toFun f := ⟨fun x => m x * (f : D.BareSite → ℝ) x, fun x hx => by
    have h : (f : D.BareSite → ℝ) x = 0 := f.2 x hx
    simp [h]⟩
  map_add' f g := by
    ext x
    simp [mul_add]
  map_smul' c f := by
    ext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem mulOp_apply (m : D.BareSite → ℝ) (f : ↥B.bareSpace) (x : D.BareSite) :
    (mulOp B m f : D.BareSite → ℝ) x = m x * (f : D.BareSite → ℝ) x := rfl
theorem inverse_scaleOnBare_apply (u : ↥B.bareSpace) :
    (Ring.inverse B.scaleOnBare u : ↥B.bareSpace) =
      mulOp B (fun x => (B.bareScale x)⁻¹) u := by
  have hne : ∀ x, B.bareScale x ≠ 0 := fun x => (scale_pos D _).ne'
  have h1 : (B.scaleOnBare : Module.End ℝ ↥B.bareSpace) *
      mulOp B (fun x => (B.bareScale x)⁻¹) = 1 := by
    ext f x
    change B.bareScale x * ((B.bareScale x)⁻¹ * (f : D.BareSite → ℝ) x) =
      (f : D.BareSite → ℝ) x
    rw [mul_inv_cancel_left₀ (hne x)]
  have h2 : mulOp B (fun x => (B.bareScale x)⁻¹) *
      (B.scaleOnBare : Module.End ℝ ↥B.bareSpace) = 1 := by
    ext f x
    change (B.bareScale x)⁻¹ * (B.bareScale x * (f : D.BareSite → ℝ) x) =
      (f : D.BareSite → ℝ) x
    rw [inv_mul_cancel_left₀ (hne x)]
  have h3 := Ring.inverse_unit (⟨B.scaleOnBare, _, h1, h2⟩ : (Module.End ℝ ↥B.bareSpace)ˣ)
  exact congrArg (fun T : Module.End ℝ ↥B.bareSpace => T u) h3
theorem invScaleNorm_eq (u : ↥B.bareSpace) :
    B.invScaleNorm u =
      B.bareSpaceNorm (fun x => (B.bareScale x)⁻¹ * (u : D.BareSite → ℝ) x) := by
  unfold SeparatedChain.invScaleNorm
  rw [inverse_scaleOnBare_apply]
  rfl
theorem weightedDistance_symm (x x' : D.Space) :
    B.weightedDistance x x' = B.weightedDistance x' x := by apply _root_.YangMills.Construction.Weighted.DistBounds.weightedDistance_comm <;> assumption
theorem layerEval_of_mem {y : D.Space} (hy : y ∈ B.allSites) (w : B.LayerFn) :
    B.layerEval w y = w ⟨y, hy⟩ := dif_pos hy
end CoercivityProof
namespace CoercivityProof
variable {D : TorusData} (B : SeparatedChain D)
open GivenChainGeneral
theorem mem_centredIntVectors_iff {N : ℝ} {M : ℕ} (hM : N = 2 * (M : ℝ) + 1) (k : Fin 4 → ℤ) :
    k ∈ Torus.centredIntVectors 4 N ↔ k ∈ integerBox M := by
  have h : (N - 1) / 2 = (M : ℝ) := by
    rw [hM]
    ring
  simp only [Torus.centredIntVectors, mem_ofPred_eq, integerBox, Fintype.mem_piFinset,
    Finset.mem_Icc, h]
  refine forall_congr' fun μ => ?_
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
theorem mem_layerSites_level {y : D.Space} (hy : y ∈ B.allSites) :
    y ∈ B.layerSites (B.level y) := by
  obtain ⟨n, -, hn⟩ := mem_iUnion₂.1 hy
  exact Nat.sInf_mem (s := {n | y ∈ B.layerSites n}) ⟨n, hn⟩
theorem exists_torusProj_eq {y : D.Space} {n : ℕ} (hy : y ∈ B.layerSites n) :
    ∃ z : Fin 4 → ℝ, Torus.torusProj 4 D.side z = y := by
  obtain ⟨k, hk⟩ := hy.1
  exact ⟨_, hk.symm⟩
theorem finsum_bondGrad_sq (S : Set D.Bond) (f : D.BareSite → ℝ) :
    ∑ᶠ b ∈ S, TorusData.bondGrad f b ^ 2 =
      (D.scale 0 ^ 2)⁻¹ * ∑ᶠ b ∈ S, TorusData.bondDiff f b ^ 2 := by
  rw [finsum_mem_eq_sum_indicator, finsum_mem_eq_sum_indicator, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b ∈ S
  · rw [indicator_of_mem hb, indicator_of_mem hb]
    simp only [TorusData.bondGrad]
    rw [mul_pow, inv_pow]
  · simp [indicator_of_notMem hb]
theorem block_poincare_ineq (hP : BoxPoincareInequality) (hb : BlockPartition B)
    (hblock : ∀ n, ∀ y ∈ B.layerSites n, ∀ z : Fin 4 → ℝ, Torus.torusProj 4 D.side z = y →
      SiteBlockGrid B n y z)
    {y : D.Space} (hy : y ∈ B.allSites) (f : D.BareSite → ℝ) (m : ℝ)
    (hm : m = ((D.L : ℝ) ^ (B.level y * 4))⁻¹ * ∑ᶠ x ∈ B.block y, f x) :
    (B.siteScale y ^ 2)⁻¹ * TorusData.siteNorm (B.block y) (fun x => f x - m) ^ 2 ≤
      TorusData.bondNorm (TorusData.bondsWithin (B.block y)) (TorusData.bondGrad f) ^ 2 := by
  classical
  set n : ℕ := B.level y with hn
  obtain ⟨z, hz⟩ := exists_torusProj_eq B (mem_layerSites_level B hy)
  have hB := hblock n y (mem_layerSites_level B hy) z hz
  have hodd : Odd (D.L ^ n) := D.blocking.factor_odd.pow
  obtain ⟨M, hM⟩ := hodd
  have hMr : (D.L : ℝ) ^ n = 2 * (M : ℝ) + 1 := by exact_mod_cast hM
  set box := integerBox M with hbox
  have hmem := mem_centredIntVectors_iff (N := (D.L : ℝ) ^ n) hMr
  have : Nonempty D.BareSite := by
    obtain ⟨x, -⟩ := hb.block_nonempty y hy
    exact ⟨x⟩
  have hex : ∀ k, k ∈ box → ∃ x : D.BareSite, x ∈ B.block y ∧
      (x : D.Space) = Torus.gridImage D.side (D.scale 0) z k := by
    intro k hk
    have h1 : Torus.gridImage D.side (D.scale 0) z k ∈ (Subtype.val '' B.block y) := by
      rw [← hB.isGrid.image_eq]
      exact mem_image_of_mem _ ((hmem k).2 hk)
    obtain ⟨x, hx, e⟩ := h1
    exact ⟨x, hx, e⟩
  choose! φ hφ1 hφ2 using hex
  have hinj : ∀ k ∈ box, ∀ k' ∈ box, φ k = φ k' → k = k' := by
    intro k hk k' hk' h
    refine hB.isGrid.injOn ((hmem k).2 hk) ((hmem k').2 hk') ?_
    rw [← hφ2 k hk, ← hφ2 k' hk', h]
  have hsurj : ∀ x ∈ B.block y, ∃ k ∈ box, φ k = x := by
    intro x hx
    have h1 : (x : D.Space) ∈ (Subtype.val '' B.block y) := mem_image_of_mem _ hx
    rw [← hB.isGrid.image_eq] at h1
    obtain ⟨k, hk, e⟩ := h1
    have hk' := (hmem k).1 hk
    exact ⟨k, hk', Subtype.ext ((hφ2 k hk').trans e)⟩
  have hset : B.block y = ↑(box.image φ) := by
    ext x
    simp only [Finset.coe_image, mem_image, Finset.mem_coe]
    constructor
    · intro hx
      exact hsurj x hx
    · rintro ⟨k, hk, rfl⟩
      exact hφ1 k hk
  have hsum : ∀ h : D.BareSite → ℝ, ∑ᶠ x ∈ B.block y, h x = ∑ k ∈ box, h (φ k) := by
    intro h
    rw [hset, finsum_mem_coe_finset, Finset.sum_image fun a ha b hb' e => hinj a ha b hb' e]
  set g : (Fin 4 → ℤ) → ℝ := fun k => f (φ k) with hg
  have hmean : m = ((2 * (M : ℝ) + 1) ^ 4)⁻¹ * ∑ k ∈ box, g k := by
    rw [hm, hsum f, ← hMr, pow_mul]
  have hmain := hP M g m hmean
  set T : Finset (Fin 4 × (Fin 4 → ℤ)) :=
    ((Finset.univ : Finset (Fin 4)) ×ˢ box).filter
      (fun p => p.2 + Pi.single p.1 1 ∈ box) with hT
  have hTsum : ∑ μ : Fin 4, ∑ k ∈ box.filter (fun k => k + Pi.single μ 1 ∈ box),
      (g (k + Pi.single μ 1) - g k) ^ 2 =
      ∑ p ∈ T, (g (p.2 + Pi.single p.1 1) - g p.2) ^ 2 := by
    rw [hT, Finset.sum_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_filter _ _
  have hbond : ∀ p ∈ T, ∃ b : D.Bond,
      (b.source = φ p.2 ∧ b.target = φ (p.2 + Pi.single p.1 1)) ∨
        (b.source = φ (p.2 + Pi.single p.1 1) ∧ b.target = φ p.2) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    have hk := (Finset.mem_product.1 hp1).2
    exact (hB.adjacent_iff p.2 ((hmem _).2 hk) _ ((hmem _).2 hp2) (φ p.2) _ (hφ2 _ hk)
      (hφ2 _ hp2)).2 ⟨p.1, Or.inl rfl⟩
  have hEb : ∑ p ∈ T, (g (p.2 + Pi.single p.1 1) - g p.2) ^ 2 ≤
      ∑ᶠ b ∈ TorusData.bondsWithin (B.block y), TorusData.bondDiff f b ^ 2 := by
    rcases isEmpty_or_nonempty D.Bond with hE | hE
    · have hTe : T = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
        obtain ⟨b, -⟩ := hbond p hp
        exact hE.false b
      rw [hTe, Finset.sum_empty]
      exact finsum_mem_nonneg_of_forall _ fun _ => sq_nonneg _
    · choose! ψ hψ using hbond
      have hval : ∀ p ∈ T, (g (p.2 + Pi.single p.1 1) - g p.2) ^ 2 =
          TorusData.bondDiff f (ψ p) ^ 2 := by
        intro p hp
        unfold TorusData.bondDiff
        rcases hψ p hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2]
          simp only [hg]
          ring
      have hψinj : ∀ p ∈ T, ∀ p' ∈ T, ψ p = ψ p' → p = p' := by
        intro p hp p' hp' e
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
        obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hp'
        have hk := (Finset.mem_product.1 hp1).2
        have hk' := (Finset.mem_product.1 hq1).2
        have hsingle : ∀ μ ν : Fin 4, (Pi.single μ 1 : Fin 4 → ℤ) = Pi.single ν 1 → μ = ν := by
          intro μ ν h
          by_contra hne
          have := congrFun h μ
          simp [hne] at this
        have key : p.2 = p'.2 ∧ p.2 + Pi.single p.1 1 = p'.2 + Pi.single p'.1 1 := by
          rcases hψ p hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hψ p' hp' with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [e] at h1 h2
            exact ⟨hinj _ hk _ hk' (h1.symm.trans h3), hinj _ hp2 _ hq2 (h2.symm.trans h4)⟩
          · exfalso
            rw [e] at h1 h2
            have e1 := hinj _ hk _ hq2 (h1.symm.trans h3)
            have e2 := hinj _ hp2 _ hk' (h2.symm.trans h4)
            have e3 : (Pi.single p.1 1 : Fin 4 → ℤ) + Pi.single p'.1 1 = 0 := by
              have : p.2 + Pi.single p.1 1 + Pi.single p'.1 1 = p.2 := by
                rw [e2, ← e1]
              exact add_left_cancel (a := p.2) (by rw [← add_assoc, this, add_zero])
            have := congrFun e3 p.1
            simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at this
            have h5 : (Pi.single p'.1 1 : Fin 4 → ℤ) p.1 = 0 ∨
                (Pi.single p'.1 1 : Fin 4 → ℤ) p.1 = 1 := by
              by_cases hh : p.1 = p'.1
              · right
                rw [hh, Pi.single_eq_same]
              · left
                exact Pi.single_eq_of_ne hh _
            rcases h5 with h5 | h5 <;> rw [h5] at this <;> omega
          · exfalso
            rw [e] at h1 h2
            have e1 := hinj _ hp2 _ hk' (h1.symm.trans h3)
            have e2 := hinj _ hk _ hq2 (h2.symm.trans h4)
            have e3 : (Pi.single p.1 1 : Fin 4 → ℤ) + Pi.single p'.1 1 = 0 := by
              have : p.2 + Pi.single p.1 1 + Pi.single p'.1 1 = p.2 := by
                rw [e1, ← e2]
              exact add_left_cancel (a := p.2) (by rw [← add_assoc, this, add_zero])
            have := congrFun e3 p.1
            simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at this
            have h5 : (Pi.single p'.1 1 : Fin 4 → ℤ) p.1 = 0 ∨
                (Pi.single p'.1 1 : Fin 4 → ℤ) p.1 = 1 := by
              by_cases hh : p.1 = p'.1
              · right
                rw [hh, Pi.single_eq_same]
              · left
                exact Pi.single_eq_of_ne hh _
            rcases h5 with h5 | h5 <;> rw [h5] at this <;> omega
          · rw [e] at h1 h2
            exact ⟨hinj _ hk _ hk' (h2.symm.trans h4), hinj _ hp2 _ hq2 (h1.symm.trans h3)⟩
        obtain ⟨k1, k2⟩ := key
        have h6 : (Pi.single p.1 1 : Fin 4 → ℤ) = Pi.single p'.1 1 := by
          rw [k1] at k2
          exact add_left_cancel k2
        exact Prod.ext (hsingle _ _ h6) k1
      have hin : ∀ p ∈ T, ψ p ∈ TorusData.bondsWithin (B.block y) := by
        intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
        have hk := (Finset.mem_product.1 hp1).2
        rcases hψ p hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1 ▸ hφ1 _ hk, h2 ▸ hφ1 _ hp2⟩
        · exact ⟨h1 ▸ hφ1 _ hp2, h2 ▸ hφ1 _ hk⟩
      rw [Finset.sum_congr rfl hval, finsum_mem_eq_sum_indicator]
      have h1 : ∑ p ∈ T, TorusData.bondDiff f (ψ p) ^ 2 =
          ∑ b ∈ T.image ψ, (TorusData.bondsWithin (B.block y)).indicator
            (fun b => TorusData.bondDiff f b ^ 2) b := by
        rw [Finset.sum_image fun a ha b hb' e => hψinj a ha b hb' e]
        exact Finset.sum_congr rfl fun p hp =>
          (indicator_of_mem (hin p hp) (fun b => TorusData.bondDiff f b ^ 2)).symm
      rw [h1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ =>
        indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hξ0 : 0 < D.scale 0 := scale_pos D 0
  have hc : 0 < D.scale 0 ^ 4 := pow_pos hξ0 4
  have hξy : B.siteScale y = (2 * (M : ℝ) + 1) * D.scale 0 := by
    change D.scale n = _
    simp only [TorusData.scale, pow_zero, one_mul]
    rw [hMr]
  rw [siteNorm_sq, bondNorm_sq, finsum_bondGrad_sq, hsum (fun x => (f x - m) ^ 2)]
  set A : ℝ := ∑ k ∈ box, (f (φ k) - m) ^ 2 with hA
  set Eb : ℝ := ∑ᶠ b ∈ TorusData.bondsWithin (B.block y), TorusData.bondDiff f b ^ 2 with hEbdef
  have hAE : A ≤ (2 * (M : ℝ) + 1) ^ 2 * Eb := by
    refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    rw [hTsum]
    exact hEb
  rw [hξy]
  have : (((2 * (M : ℝ) + 1) * D.scale 0) ^ 2)⁻¹ * (D.scale 0 ^ 4 * A) ≤
      (((2 * (M : ℝ) + 1) * D.scale 0) ^ 2)⁻¹ *
        (D.scale 0 ^ 4 * ((2 * (M : ℝ) + 1) ^ 2 * Eb)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAE hc.le) (by positivity)
  refine this.trans_eq ?_
  field_simp
end CoercivityProof
namespace CoercivityProof
theorem coercivityConst_bounds {L : ℕ} (h3 : 3 ≤ L) :
    8 / 9 ≤ coercivityConst L ∧ coercivityConst L ≤ 1 := by
  have hL : (3 : ℝ) ≤ L := by exact_mod_cast h3
  have h9 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hpos : 0 < ((L : ℝ) ^ 2)⁻¹ := inv_pos.2 (by linarith)
  have hle : ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 9 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) h9
  unfold coercivityConst
  constructor <;> linarith
theorem avgWeight_bounds (hW : Dirichlet.WeightRecursionBounds) {L : ℕ} (h3 : 3 ≤ L)
    (hodd : Odd L) (n : ℕ) :
    coercivityConst L ≤ avgWeight L n ∧ avgWeight L n ≤ 1 := by
  have h1 : (L : ℝ) ^ (-2 : ℤ) = ((L : ℝ) ^ 2)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hrec : ∀ n : ℕ, 1 ≤ n → avgWeight L (n + 1) =
      avgWeight L n / ((L : ℝ) ^ (-2 : ℤ) + avgWeight L n) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [h1]
    rfl
  have h := (hW L h3 hodd (avgWeight L) rfl rfl hrec).2 n
  rw [h1] at h
  exact ⟨h.1.le, h.2⟩
variable {D : TorusData} (B : SeparatedChain D)
open GivenChainGeneral
theorem invScaleNorm_sq_eq_sum {W : Set D.Space} (f : ↥(B.bareSpaceOn W)) :
    B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 =
      D.scale 0 ^ 4 * ∑ x, ((B.bareScale x)⁻¹ * (f : D.BareSite → ℝ) x) ^ 2 := by
  rw [invScaleNorm_eq, bareSpaceNorm_sq_eq_sum]
  · rfl
  · intro x hx
    have h : (f : D.BareSite → ℝ) x = 0 := f.2.1 x hx
    change (B.bareScale x)⁻¹ * (f : D.BareSite → ℝ) x = 0
    rw [h, mul_zero]
theorem invScaleNorm_sq_eq_blocks (hb : BlockPartition B) (hfin : B.allSites.Finite)
    {W : Set D.Space} (hU : B.IsBlockUnion W) (f : ↥(B.bareSpaceOn W)) :
    B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 =
      ∑ y ∈ (finite_sitesIn B hfin W).toFinset,
        (B.siteScale y ^ 2)⁻¹ * TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) ^ 2 := by
  rw [invScaleNorm_sq_eq_sum,
    fintype_sum_eq_finsum_mem (D.bareSites W)
      (f := fun x => ((B.bareScale x)⁻¹ * (f : D.BareSite → ℝ) x) ^ 2)
      (fun x hx => by
        have h : (f : D.BareSite → ℝ) x = 0 := f.2.2 x hx
        simp [h]),
    finsum_bareSites_eq_blocks B hb hU, finsum_mem_eq_finite_toFinset_sum _ (finite_sitesIn B hfin W),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy' : y ∈ B.allSites := ((finite_sitesIn B hfin W).mem_toFinset.1 hy).1
  have h : ∑ᶠ x ∈ B.block y, ((B.bareScale x)⁻¹ * (f : D.BareSite → ℝ) x) ^ 2 =
      (B.siteScale y ^ 2)⁻¹ * ∑ᶠ x ∈ B.block y, (f : D.BareSite → ℝ) x ^ 2 := by
    rw [finsum_mem_eq_sum_indicator, finsum_mem_eq_sum_indicator, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ B.block y
    · rw [indicator_of_mem hx, indicator_of_mem hx, bareScale_eq B hb hy' hx, mul_pow,
        inv_pow]
    · simp [indicator_of_notMem hx]
  rw [h, siteNorm_sq]
  ring
theorem sum_block_bonds_le (hb : BlockPartition B) (hfin : B.allSites.Finite)
    {W : Set D.Space} {𝔟 : Set D.Bond} (hU : B.IsBlockUnion W)
    (hin : TorusData.bondsWithin (D.bareSites W) ⊆ 𝔟) (r : D.Bond → ℝ) (hr : ∀ b, 0 ≤ r b) :
    D.scale 0 ^ 4 * ∑ y ∈ (finite_sitesIn B hfin W).toFinset,
        ∑ᶠ b ∈ TorusData.bondsWithin (B.block y), r b ≤
      D.scale 0 ^ 4 * ∑ᶠ b ∈ 𝔟, r b := by
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos (scale_pos D 0) 4).le
  have h1 : ∑ᶠ b ∈ ⋃ y ∈ B.sitesIn W, TorusData.bondsWithin (B.block y), r b =
      ∑ᶠ y ∈ B.sitesIn W, ∑ᶠ b ∈ TorusData.bondsWithin (B.block y), r b :=
    finsum_mem_biUnion
      (fun y hy y' hy' hne => Set.disjoint_left.2 fun b h1 h2 =>
        Set.disjoint_left.1 (hb.block_pairwise_disjoint y hy.1 y' hy'.1 hne) h1.1 h2.1)
      (finite_sitesIn B hfin W) (fun _ _ => toFinite _)
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_sitesIn B hfin W)] at h1
  rw [← h1]
  refine finsum_mem_mono_of_subset (fun b hbm => ?_) hr
  obtain ⟨y, hy, hby⟩ := mem_iUnion₂.1 hbm
  refine hin ⟨?_, ?_⟩
  · rw [bareSites_eq_iUnion_block B hb hU]
    exact mem_iUnion₂.2 ⟨y, hy, hby.1⟩
  · rw [bareSites_eq_iUnion_block B hb hU]
    exact mem_iUnion₂.2 ⟨y, hy, hby.2⟩
theorem bondNorm_grad_sq_le_form (hfin : B.allSites.Finite)
    (hwt : ∀ n, coercivityConst D.L ≤ avgWeight D.L n ∧ avgWeight D.L n ≤ 1)
    (W : Set D.Space) (𝔟 : Set D.Bond) (f : ↥(B.bareSpaceOn W)) :
    TorusData.bondNorm 𝔟 (TorusData.bondGrad (f : D.BareSite → ℝ)) ^ 2 ≤
      B.admissibleForm W 𝔟 f f := by
  have hc := coercivityConst_bounds D.blocking.three_le_factor
  rw [admissibleForm_eq_sum B hfin, bondNorm_sq, finsum_mem_eq_finite_toFinset_sum _ (toFinite 𝔟)]
  have h2 : 0 ≤ ∑ y ∈ (finite_sitesIn B hfin W).toFinset,
      avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
        (B.layerEval (B.avgOp (B.bareSpaceOnIncl W f)) y *
          B.layerEval (B.avgOp (B.bareSpaceOnIncl W f)) y) := by
    refine Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg ?_ (sq_nonneg _))
      (mul_self_nonneg _)
    linarith [(hwt (B.level y)).1]
  have h3 : ∑ b ∈ (toFinite 𝔟).toFinset, TorusData.bondGrad (f : D.BareSite → ℝ) b ^ 2 =
      ∑ b ∈ (toFinite 𝔟).toFinset,
        TorusData.bondGrad (f : D.BareSite → ℝ) b * TorusData.bondGrad (f : D.BareSite → ℝ) b :=
    Finset.sum_congr rfl fun b _ => pow_two _
  rw [h3]
  linarith
theorem form_coercive (hb : BlockPartition B) (hfin : B.allSites.Finite)
    (hav : B.AvgRelations)
    (hpoin : ∀ y ∈ B.allSites, ∀ (f : D.BareSite → ℝ) (m : ℝ),
      m = ((D.L : ℝ) ^ (B.level y * 4))⁻¹ * ∑ᶠ x ∈ B.block y, f x →
      (B.siteScale y ^ 2)⁻¹ * TorusData.siteNorm (B.block y) (fun x => f x - m) ^ 2 ≤
        TorusData.bondNorm (TorusData.bondsWithin (B.block y)) (TorusData.bondGrad f) ^ 2)
    (hwt : ∀ n, coercivityConst D.L ≤ avgWeight D.L n ∧ avgWeight D.L n ≤ 1)
    {W : Set D.Space} {𝔟 : Set D.Bond} (hU : B.IsBlockUnion W)
    (hin : TorusData.bondsWithin (D.bareSites W) ⊆ 𝔟) (f : ↥(B.bareSpaceOn W)) :
    coercivityConst D.L * B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 ≤
      B.admissibleForm W 𝔟 f f := by
  have hc := coercivityConst_bounds D.blocking.three_le_factor
  set Λ := (finite_sitesIn B hfin W).toFinset with hΛ
  have hterm : ∀ y ∈ Λ,
      coercivityConst D.L * ((B.siteScale y ^ 2)⁻¹ *
          TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) ^ 2) ≤
        D.scale 0 ^ 4 * (∑ᶠ b ∈ TorusData.bondsWithin (B.block y),
            TorusData.bondGrad (f : D.BareSite → ℝ) b ^ 2) +
          avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
            (B.layerEval (B.avgOp (B.bareSpaceOnIncl W f)) y *
              B.layerEval (B.avgOp (B.bareSpaceOnIncl W f)) y) := by
    intro y hy
    have hy' : y ∈ B.allSites := ((finite_sitesIn B hfin W).mem_toFinset.1 hy).1
    rw [layerEval_of_mem B hy']
    set q : ℝ := B.avgOp (B.bareSpaceOnIncl W f) ⟨y, hy'⟩ with hq
    have hsplit := hav.2.2.2.2.2 (B.bareSpaceOnIncl W f) ⟨y, hy'⟩
    have hP := hpoin y hy' (f : D.BareSite → ℝ) q rfl
    rw [bondNorm_sq] at hP
    have hsplit' : TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) ^ 2 =
        TorusData.siteNorm (B.block y) (fun x => (f : D.BareSite → ℝ) x - q) ^ 2 +
          B.siteScale y ^ 4 * q ^ 2 := hsplit
    rw [hsplit']
    have hξ : 0 < B.siteScale y := siteScale_pos B y
    set Pn := TorusData.siteNorm (B.block y) (fun x => (f : D.BareSite → ℝ) x - q) ^ 2 with hPn
    have hPnn : 0 ≤ Pn := sq_nonneg _
    have hi : 0 ≤ (B.siteScale y ^ 2)⁻¹ * Pn := mul_nonneg (by positivity) hPnn
    have e1 : (B.siteScale y ^ 2)⁻¹ * (Pn + B.siteScale y ^ 4 * q ^ 2) =
        (B.siteScale y ^ 2)⁻¹ * Pn + B.siteScale y ^ 2 * q ^ 2 := by
      field_simp
    rw [e1]
    have h1 : coercivityConst D.L * ((B.siteScale y ^ 2)⁻¹ * Pn) ≤
        (B.siteScale y ^ 2)⁻¹ * Pn :=
      mul_le_of_le_one_left hi hc.2
    have h2 : coercivityConst D.L * (B.siteScale y ^ 2 * q ^ 2) ≤
        avgWeight D.L (B.level y) * (B.siteScale y ^ 2 * q ^ 2) :=
      mul_le_mul_of_nonneg_right (hwt _).1 (by positivity)
    have e2 : avgWeight D.L (B.level y) * B.siteScale y ^ 2 * (q * q) =
        avgWeight D.L (B.level y) * (B.siteScale y ^ 2 * q ^ 2) := by ring
    rw [e2, mul_add]
    linarith
  rw [invScaleNorm_sq_eq_blocks B hb hfin hU, Finset.mul_sum, admissibleForm_eq_sum B hfin]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add ?_ le_rfl
  have h3 := sum_block_bonds_le B hb hfin hU hin
    (fun b => TorusData.bondGrad (f : D.BareSite → ℝ) b ^ 2) fun _ => sq_nonneg _
  refine h3.trans_eq ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (toFinite 𝔟)]
  congr 1
  exact Finset.sum_congr rfl fun b _ => pow_two _
theorem invScaleNorm_sq_pos {W : Set D.Space} (f : ↥(B.bareSpaceOn W)) (hf : f ≠ 0) :
    0 < B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 := by
  rw [invScaleNorm_sq_eq_sum]
  have hx : ∃ x, (f : D.BareSite → ℝ) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  obtain ⟨x, hx⟩ := hx
  refine mul_pos (pow_pos (scale_pos D 0) 4) (Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨x, Finset.mem_univ _, ?_⟩)
  have := (bareScale_pos B x).ne'
  positivity
end CoercivityProof
namespace CoercivityProof
theorem exp_add_exp_neg_sub_two_le {s : ℝ} (hs : |s| ≤ 1) :
    Real.exp s + Real.exp (-s) - 2 ≤ 2 * s ^ 2 := by
  have h1 := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hs)).2
  have h2 := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le (x := -s) (by rwa [abs_neg]))).2
  rw [neg_sq] at h2
  linarith
theorem exp_add_exp_neg_sub_two_nonneg (s : ℝ) : 0 ≤ Real.exp s + Real.exp (-s) - 2 := by
  have h1 := Real.add_one_le_exp s
  have h2 := Real.add_one_le_exp (-s)
  linarith
theorem abs_exp_sub_one_le_of_abs_le {s t : ℝ} (hs : |s| ≤ t) :
    |Real.exp s - 1| ≤ Real.exp t - 1 := by
  obtain ⟨h1, h2⟩ := abs_le.1 hs
  rw [abs_le]
  have h3 := Real.exp_le_exp.2 h2
  have h4 := Real.exp_le_exp.2 h1
  have h5 := exp_add_exp_neg_sub_two_nonneg t
  constructor <;> linarith
theorem conj_diff_mul_eq (lp lm tp tm : ℝ) :
    (Real.exp tp * lp - Real.exp tm * lm) * (Real.exp (-tp) * lp - Real.exp (-tm) * lm) =
      (lp - lm) ^ 2 - lp * lm * (Real.exp (tp - tm) + Real.exp (-(tp - tm)) - 2) := by
  have h1 : Real.exp tp * Real.exp (-tp) = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp tm * Real.exp (-tm) = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : Real.exp (tp - tm) = Real.exp tp * Real.exp (-tm) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have h4 : Real.exp (-(tp - tm)) = Real.exp tm * Real.exp (-tp) := by
    rw [neg_sub, sub_eq_add_neg, Real.exp_add]
  rw [h3, h4]
  linear_combination lp ^ 2 * h1 + lm ^ 2 * h2
theorem greenDecayRate_four_eq (L : ℕ) : greenDecayRate 4 L = 1 / (80 * (L : ℝ)) := by
  unfold greenDecayRate
  push_cast
  ring_nf
theorem greenDecayRate_bounds {L : ℕ} (h3 : 3 ≤ L) :
    0 < greenDecayRate 4 L ∧ greenDecayRate 4 L ≤ 1 ∧ 4 * greenDecayRate 4 L ≤ 1 / 60 := by
  have hL : (3 : ℝ) ≤ L := by exact_mod_cast h3
  rw [greenDecayRate_four_eq]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    linarith
  · rw [show 4 * (1 / (80 * (L : ℝ))) = 1 / (20 * (L : ℝ)) by field_simp; ring]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
theorem small_constants_le {L : ℕ} (h3 : 3 ≤ L) :
    8 * (greenDecayRate 4 L ^ 2 * (L : ℝ) ^ 2) + (Real.exp (4 * greenDecayRate 4 L) - 1) ≤
      coercivityConst L / 4 := by
  have hL : (3 : ℝ) ≤ L := by exact_mod_cast h3
  have h1 : 8 * (greenDecayRate 4 L ^ 2 * (L : ℝ) ^ 2) = 1 / 800 := by
    rw [greenDecayRate_four_eq]
    field_simp
    norm_num
  have h2 : Real.exp (4 * greenDecayRate 4 L) ≤ 60 / 59 := by
    have h4 : Real.exp (4 * greenDecayRate 4 L) ≤ Real.exp (1 / 60) :=
      Real.exp_le_exp.2 (greenDecayRate_bounds h3).2.2
    have h5 : (59 : ℝ) / 60 ≤ Real.exp (-(1 / 60)) := by
      have := Real.add_one_le_exp (-(1 / 60 : ℝ))
      linarith
    have h6 : Real.exp (1 / 60) * Real.exp (-(1 / 60)) = 1 := by
      rw [← Real.exp_add]
      simp
    have h7 : 0 < Real.exp (1 / 60) := Real.exp_pos _
    have h8 : Real.exp (1 / 60) * (59 / 60) ≤ 1 := by
      calc _ ≤ Real.exp (1 / 60) * Real.exp (-(1 / 60)) :=
            mul_le_mul_of_nonneg_left h5 h7.le
        _ = 1 := h6
    have h9 : Real.exp (1 / 60) ≤ 60 / 59 := by linarith
    exact h4.trans h9
  have hc := (coercivityConst_bounds h3).1
  rw [h1]
  linarith
variable {D : TorusData} (B : SeparatedChain D)
open GivenChainGeneral
theorem abs_weight_sub_le_on_bond (hshort : B.BlocksAndBondsShort) {θ : D.Space → ℝ}
    (hLip : B.IsWeightedLipschitz θ) {b : D.Bond}
    (ht : b.source ∈ D.bareSites (B.stage 0)) (hh : b.target ∈ D.bareSites (B.stage 0)) :
    |θ (b.target : D.Space) - θ (b.source : D.Space)| ≤ greenDecayRate 4 D.L ∧
      |θ (b.target : D.Space) - θ (b.source : D.Space)| ≤
        greenDecayRate 4 D.L * ((D.L : ℝ) * D.scale 0 * (B.bareScale b.target)⁻¹) ∧
      |θ (b.target : D.Space) - θ (b.source : D.Space)| ≤
        greenDecayRate 4 D.L * ((D.L : ℝ) * D.scale 0 * (B.bareScale b.source)⁻¹) := by
  have hj : TorusData.Adjacent b.target b.source := ⟨b, Or.inr ⟨rfl, rfl⟩⟩
  have hj' : TorusData.Adjacent b.source b.target := ⟨b, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, h1, h2⟩ := hshort.2 b.target b.source hh ht hj
  obtain ⟨-, -, h3⟩ := hshort.2 b.source b.target ht hh hj'
  have hε := (greenDecayRate_bounds D.blocking.three_le_factor).1
  have hl := hLip b.target b.source
  have hmid : 1 / 2 * D.scale 0 * ((B.bareScale b.source)⁻¹ + (B.bareScale b.target)⁻¹) =
      1 / 2 * D.scale 0 * ((B.bareScale b.target)⁻¹ + (B.bareScale b.source)⁻¹) := by
    ring
  rw [hmid] at h3
  have hd1 := h1.trans (h2.trans (min_le_left _ _))
  have hd2 := h1.trans (h2.trans (min_le_right _ _))
  have hd3 := h1.trans (h3.trans (min_le_right _ _))
  refine ⟨hl.trans ?_, hl.trans (mul_le_mul_of_nonneg_left hd2 hε.le),
    hl.trans (mul_le_mul_of_nonneg_left hd3 hε.le)⟩
  calc _ ≤ greenDecayRate 4 D.L * 1 := mul_le_mul_of_nonneg_left hd1 hε.le
    _ = _ := mul_one _
theorem mulOnBare_apply (W : Set D.Space) (g : D.Space → ℝ)
    (f : ↥(B.bareSpaceOn W)) (x : D.BareSite) :
    (B.mulOnBare W g f : D.BareSite → ℝ) x = g (x : D.Space) * (f : D.BareSite → ℝ) x := rfl
theorem bond_term_le (hshort : B.BlocksAndBondsShort) {θ : D.Space → ℝ}
    (hLip : B.IsWeightedLipschitz θ) {W : Set D.Space}
    (hsub : D.bareSites W ⊆ D.bareSites (B.stage 0))
    (f : ↥(B.bareSpaceOn W)) (b : D.Bond) :
    TorusData.bondGrad (f : D.BareSite → ℝ) b * TorusData.bondGrad (f : D.BareSite → ℝ) b -
        greenDecayRate 4 D.L ^ 2 * (D.L : ℝ) ^ 2 *
          (((B.bareScale b.target)⁻¹ * (f : D.BareSite → ℝ) b.target) ^ 2 +
            ((B.bareScale b.source)⁻¹ * (f : D.BareSite → ℝ) b.source) ^ 2) ≤
      TorusData.bondGrad (B.mulOnBare W (fun x => Real.exp (θ x)) f : D.BareSite → ℝ) b *
        TorusData.bondGrad (B.mulOnBare W (fun x => Real.exp (-θ x)) f : D.BareSite → ℝ)
          b := by
  have hξ0 : 0 < D.scale 0 := scale_pos D 0
  simp only [TorusData.bondGrad, TorusData.bondDiff, mulOnBare_apply]
  set s : ℝ := (D.scale 0)⁻¹ with hs
  set lp : ℝ := (f : D.BareSite → ℝ) b.target with hlp
  set lm : ℝ := (f : D.BareSite → ℝ) b.source with hlm
  set tp : ℝ := θ (b.target : D.Space) with htp
  set tm : ℝ := θ (b.source : D.Space) with htm
  set ip : ℝ := (B.bareScale b.target)⁻¹ with hip
  set im : ℝ := (B.bareScale b.source)⁻¹ with him
  set ε : ℝ := greenDecayRate 4 D.L with hε
  have hprod := conj_diff_mul_eq lp lm tp tm
  have e : s * (Real.exp tp * lp - Real.exp tm * lm) *
      (s * (Real.exp (-tp) * lp - Real.exp (-tm) * lm)) =
      s ^ 2 * ((lp - lm) ^ 2 - lp * lm * (Real.exp (tp - tm) + Real.exp (-(tp - tm)) - 2)) := by
    rw [← hprod]
    ring
  rw [e]
  have hT : 0 ≤ ε ^ 2 * (D.L : ℝ) ^ 2 * ((ip * lp) ^ 2 + (im * lm) ^ 2) := by positivity
  by_cases hboth : b.target ∈ D.bareSites W ∧ b.source ∈ D.bareSites W
  · obtain ⟨h1, h2, h3⟩ := abs_weight_sub_le_on_bond B hshort hLip (hsub hboth.2) (hsub hboth.1)
    change |tp - tm| ≤ ε at h1
    change |tp - tm| ≤ ε * ((D.L : ℝ) * D.scale 0 * ip) at h2
    change |tp - tm| ≤ ε * ((D.L : ℝ) * D.scale 0 * im) at h3
    have hε1 : ε ≤ 1 := (greenDecayRate_bounds D.blocking.three_le_factor).2.1
    set C : ℝ := Real.exp (tp - tm) + Real.exp (-(tp - tm)) - 2 with hC
    have hC0 : 0 ≤ C := exp_add_exp_neg_sub_two_nonneg _
    have hC1 : C ≤ 2 * (tp - tm) ^ 2 := exp_add_exp_neg_sub_two_le (h1.trans hε1)
    have hmul : lp * lm ≤ (lp ^ 2 + lm ^ 2) / 2 := by nlinarith [sq_nonneg (lp - lm)]
    have hA : lp * lm * C ≤ (lp ^ 2 + lm ^ 2) * (tp - tm) ^ 2 := by
      calc lp * lm * C ≤ (lp ^ 2 + lm ^ 2) / 2 * C := mul_le_mul_of_nonneg_right hmul hC0
        _ ≤ (lp ^ 2 + lm ^ 2) / 2 * (2 * (tp - tm) ^ 2) :=
            mul_le_mul_of_nonneg_left hC1 (by positivity)
        _ = _ := by ring
    have hsq : ∀ u : ℝ, |tp - tm| ≤ u → (tp - tm) ^ 2 ≤ u ^ 2 := fun u hu => by
      rw [← sq_abs (tp - tm)]
      exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    have hB1 : lp ^ 2 * (tp - tm) ^ 2 ≤ lp ^ 2 * (ε * ((D.L : ℝ) * D.scale 0 * ip)) ^ 2 :=
      mul_le_mul_of_nonneg_left (hsq _ h2) (sq_nonneg _)
    have hB2 : lm ^ 2 * (tp - tm) ^ 2 ≤ lm ^ 2 * (ε * ((D.L : ℝ) * D.scale 0 * im)) ^ 2 :=
      mul_le_mul_of_nonneg_left (hsq _ h3) (sq_nonneg _)
    have hs2 : s ^ 2 * D.scale 0 ^ 2 = 1 := by
      rw [hs, inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero 2 hξ0.ne')
    have hfin : s ^ 2 * (lp * lm * C) ≤
        ε ^ 2 * (D.L : ℝ) ^ 2 * ((ip * lp) ^ 2 + (im * lm) ^ 2) := by
      have h5 : lp * lm * C ≤ D.scale 0 ^ 2 *
          (ε ^ 2 * (D.L : ℝ) ^ 2 * ((ip * lp) ^ 2 + (im * lm) ^ 2)) := by
        calc lp * lm * C ≤ lp ^ 2 * (tp - tm) ^ 2 + lm ^ 2 * (tp - tm) ^ 2 := by linarith
          _ ≤ lp ^ 2 * (ε * ((D.L : ℝ) * D.scale 0 * ip)) ^ 2 +
                lm ^ 2 * (ε * ((D.L : ℝ) * D.scale 0 * im)) ^ 2 := add_le_add hB1 hB2
          _ = _ := by ring
      calc s ^ 2 * (lp * lm * C) ≤ s ^ 2 * (D.scale 0 ^ 2 *
            (ε ^ 2 * (D.L : ℝ) ^ 2 * ((ip * lp) ^ 2 + (im * lm) ^ 2))) :=
            mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
        _ = (s ^ 2 * D.scale 0 ^ 2) *
            (ε ^ 2 * (D.L : ℝ) ^ 2 * ((ip * lp) ^ 2 + (im * lm) ^ 2)) := by ring
        _ = _ := by rw [hs2, one_mul]
    nlinarith
  · have hzero : lp * lm = 0 := by
      by_cases h1 : b.target ∈ D.bareSites W
      · have h2 : b.source ∉ D.bareSites W := fun h => hboth ⟨h1, h⟩
        have : lm = 0 := f.2.2 _ h2
        rw [this, mul_zero]
      · have : lp = 0 := f.2.2 _ h1
        rw [this, zero_mul]
    rw [hzero, zero_mul, sub_zero]
    have : s * (lp - lm) * (s * (lp - lm)) = s ^ 2 * (lp - lm) ^ 2 := by ring
    rw [this]
    linarith
theorem site_term_le (hav : B.AvgRelations) (hshort : B.BlocksAndBondsShort)
    {θ : D.Space → ℝ} (hLip : B.IsWeightedLipschitz θ) {W : Set D.Space}
    (f : ↥(B.bareSpaceOn W)) {y : D.Space} (hy : y ∈ B.allSites) :
    B.avgOp (B.bareSpaceOnIncl W f) ⟨y, hy⟩ ^ 2 -
        (Real.exp (4 * greenDecayRate 4 D.L) - 1) *
          ((B.siteScale y ^ 2)⁻¹ * TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ)) ^ 2 ≤
      B.avgOp (B.bareSpaceOnIncl W
          (B.mulOnBare W (fun x => Real.exp (θ x)) f)) ⟨y, hy⟩ *
        B.avgOp (B.bareSpaceOnIncl W
          (B.mulOnBare W (fun x => Real.exp (-θ x)) f)) ⟨y, hy⟩ := by
  set ε : ℝ := greenDecayRate 4 D.L with hεdef
  have hε := (greenDecayRate_bounds D.blocking.three_le_factor).1
  set F : ↥B.bareSpace := B.bareSpaceOnIncl W f with hF
  set Y : ↥B.allSites := ⟨y, hy⟩ with hY
  set t : ℝ := θ y with ht
  set gp : ↥B.bareSpace := mulOp B (fun x => Real.exp (θ (x : D.Space) - t) - 1) F
    with hgp
  set gm : ↥B.bareSpace := mulOp B (fun x => Real.exp (-(θ (x : D.Space) - t)) - 1) F
    with hgm
  have e1 : B.bareSpaceOnIncl W (B.mulOnBare W (fun x => Real.exp (θ x)) f) =
      Real.exp t • (F + gp) := by
    refine Subtype.ext (funext fun x => ?_)
    change Real.exp (θ (x : D.Space)) * (f : D.BareSite → ℝ) x =
      Real.exp t * ((f : D.BareSite → ℝ) x +
        (Real.exp (θ (x : D.Space) - t) - 1) * (f : D.BareSite → ℝ) x)
    have : Real.exp (θ (x : D.Space)) = Real.exp t * Real.exp (θ (x : D.Space) - t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [this]
    ring
  have e2 : B.bareSpaceOnIncl W (B.mulOnBare W (fun x => Real.exp (-θ x)) f) =
      Real.exp (-t) • (F + gm) := by
    refine Subtype.ext (funext fun x => ?_)
    change Real.exp (-θ (x : D.Space)) * (f : D.BareSite → ℝ) x =
      Real.exp (-t) * ((f : D.BareSite → ℝ) x +
        (Real.exp (-(θ (x : D.Space) - t)) - 1) * (f : D.BareSite → ℝ) x)
    have : Real.exp (-θ (x : D.Space)) = Real.exp (-t) * Real.exp (-(θ (x : D.Space) - t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [this]
    ring
  rw [e1, e2, map_smul, map_smul, map_add, map_add]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  set q : ℝ := B.avgOp F Y with hq
  set rp : ℝ := B.avgOp gp Y with hrp
  set rm : ℝ := B.avgOp gm Y with hrm
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have e3 : Real.exp t * (q + rp) * (Real.exp (-t) * (q + rm)) = (q + rp) * (q + rm) := by
    calc _ = (Real.exp t * Real.exp (-t)) * ((q + rp) * (q + rm)) := by ring
      _ = _ := by rw [hexp, one_mul]
  rw [e3]
  set κ : ℝ := Real.exp (2 * ε) - 1 with hκ
  have hκ0 : 0 ≤ κ := by
    have := Real.add_one_le_exp (2 * ε)
    rw [hκ]
    linarith
  have hz : (B.siteScale y : ℝ) ^ (-2 : ℤ) = (B.siteScale y ^ 2)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  set P : ℝ := (B.siteScale y ^ 2)⁻¹ * TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ)
    with hP
  have hP0 : 0 ≤ P := mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (siteNorm_nonneg _ _)
  have hq1 : |q| ≤ P := by
    have := hav.2.2.2.2.1 F Y
    rw [show ((Y : D.Space)) = y from rfl, hz] at this
    exact this
  have hclose : ∀ x ∈ B.block y, |θ (x : D.Space) - t| ≤ 2 * ε := by
    intro x hx
    have h1 := hLip (x : D.Space) y
    have h2 := hshort.1 y hy x hx
    have h3 : ε * B.weightedDistance (x : D.Space) y ≤ ε * (1 / 2 * 4) :=
      mul_le_mul_of_nonneg_left h2 hε.le
    have h4 : ε * (1 / 2 * 4) = 2 * ε := by ring
    exact h1.trans (h3.trans h4.le)
  have hr : ∀ (w : ↥B.bareSpace) (m : D.BareSite → ℝ), w = mulOp B m F →
      (∀ x ∈ B.block y, |m x| ≤ κ) → |B.avgOp w Y| ≤ κ * P := by
    intro w m hw hm
    have h1 := hav.2.2.2.2.1 w Y
    rw [show ((Y : D.Space)) = y from rfl, hz] at h1
    have h2 : TorusData.siteNorm (B.block y) (w : D.BareSite → ℝ) ≤
        κ * TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) := by
      refine siteNorm_le_mul hκ0 fun x hx => ?_
      rw [hw, mulOp_apply, abs_mul]
      exact mul_le_mul_of_nonneg_right (hm x hx) (abs_nonneg _)
    refine h1.trans ?_
    calc _ ≤ (B.siteScale y ^ 2)⁻¹ * (κ * TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 (sq_nonneg _))
      _ = _ := by rw [hP]; ring
  have hrp1 : |rp| ≤ κ * P := hr gp _ rfl fun x hx => abs_exp_sub_one_le_of_abs_le (hclose x hx)
  have hrm1 : |rm| ≤ κ * P := hr gm _ rfl fun x hx =>
    abs_exp_sub_one_le_of_abs_le (by rw [abs_neg]; exact hclose x hx)
  have hK : Real.exp (4 * ε) - 1 = 2 * κ + κ ^ 2 := by
    have : Real.exp (4 * ε) = Real.exp (2 * ε) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [this, hκ]
    ring
  rw [hK]
  have a1 : -(P * (κ * P)) ≤ q * rp := by
    have h : |q * rp| ≤ P * (κ * P) := by
      rw [abs_mul]
      exact mul_le_mul hq1 hrp1 (abs_nonneg _) hP0
    exact (neg_le_neg h).trans (neg_abs_le _)
  have a2 : -(P * (κ * P)) ≤ q * rm := by
    have h : |q * rm| ≤ P * (κ * P) := by
      rw [abs_mul]
      exact mul_le_mul hq1 hrm1 (abs_nonneg _) hP0
    exact (neg_le_neg h).trans (neg_abs_le _)
  have a3 : -((κ * P) * (κ * P)) ≤ rp * rm := by
    have h : |rp * rm| ≤ (κ * P) * (κ * P) := by
      rw [abs_mul]
      exact mul_le_mul hrp1 hrm1 (abs_nonneg _) (mul_nonneg hκ0 hP0)
    exact (neg_le_neg h).trans (neg_abs_le _)
  nlinarith
theorem form_sub_le_conj_form (hb : BlockPartition B) (hfin : B.allSites.Finite)
    (hav : B.AvgRelations) (hshort : B.BlocksAndBondsShort)
    (hwt : ∀ n, coercivityConst D.L ≤ avgWeight D.L n ∧ avgWeight D.L n ≤ 1)
    {θ : D.Space → ℝ} (hLip : B.IsWeightedLipschitz θ) {W : Set D.Space}
    {𝔟 : Set D.Bond} (hU : B.IsBlockUnion W) (f : ↥(B.bareSpaceOn W)) :
    B.admissibleForm W 𝔟 f f -
        coercivityConst D.L / 4 * B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 ≤
      B.admissibleForm W 𝔟 (B.mulOnBare W (fun x => Real.exp (θ x)) f)
        (B.mulOnBare W (fun x => Real.exp (-θ x)) f) := by
  classical
  have h3 := D.blocking.three_le_factor
  have hc := coercivityConst_bounds h3
  have hsub := bareSites_subset_stage B hb hU
  have hξ0 : 0 < D.scale 0 ^ 4 := pow_pos (scale_pos D 0) 4
  set N2 : ℝ := B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 with hN2
  have hN0 : 0 ≤ N2 := sq_nonneg _
  set ε : ℝ := greenDecayRate 4 D.L with hε
  set K : ℝ := Real.exp (4 * ε) - 1 with hK
  have hK0 : 0 ≤ K := by
    have := Real.add_one_le_exp (4 * ε)
    have he := (greenDecayRate_bounds h3).1
    rw [hK]
    linarith
  set T : D.BareSite → ℝ := fun x => ((B.bareScale x)⁻¹ * (f : D.BareSite → ℝ) x) ^ 2 with hT
  have hTn : ∀ x, 0 ≤ T x := fun x => sq_nonneg _
  have hN2T : N2 = D.scale 0 ^ 4 * ∑ x, T x := invScaleNorm_sq_eq_sum B f
  set Sb := (toFinite 𝔟).toFinset with hSb
  have hbond : D.scale 0 ^ 4 * ∑ b ∈ Sb,
        TorusData.bondGrad (f : D.BareSite → ℝ) b * TorusData.bondGrad (f : D.BareSite → ℝ) b -
        8 * (ε ^ 2 * (D.L : ℝ) ^ 2) * N2 ≤
      D.scale 0 ^ 4 * ∑ b ∈ Sb,
        TorusData.bondGrad (B.mulOnBare W (fun x => Real.exp (θ x)) f : D.BareSite → ℝ) b *
        TorusData.bondGrad (B.mulOnBare W (fun x => Real.exp (-θ x)) f : D.BareSite → ℝ) b
        := by
    have h1 := Finset.sum_le_sum (s := Sb) fun b _ => bond_term_le B hshort hLip hsub f b
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib] at h1
    have h2 : ∑ b ∈ Sb, T b.target ≤ 4 * ∑ x, T x := sum_endpoint_le _ target_dir_injective Sb hTn
    have h4 : ∑ b ∈ Sb, T b.source ≤ 4 * ∑ x, T x := sum_endpoint_le _ source_dir_injective Sb hTn
    have h5 : ε ^ 2 * (D.L : ℝ) ^ 2 * (∑ b ∈ Sb, T b.target + ∑ b ∈ Sb, T b.source) ≤
        ε ^ 2 * (D.L : ℝ) ^ 2 * (8 * ∑ x, T x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h6 := mul_le_mul_of_nonneg_left h1 hξ0.le
    have h7 := mul_le_mul_of_nonneg_left h5 hξ0.le
    rw [hN2T]
    rw [mul_sub] at h6
    calc _ = D.scale 0 ^ 4 * ∑ b ∈ Sb,
            TorusData.bondGrad (f : D.BareSite → ℝ) b * TorusData.bondGrad (f : D.BareSite → ℝ) b -
          D.scale 0 ^ 4 * (ε ^ 2 * (D.L : ℝ) ^ 2 * (8 * ∑ x, T x)) := by ring
      _ ≤ _ := by linarith
  set Λ := (finite_sitesIn B hfin W).toFinset with hΛ
  have hsite : ∑ y ∈ Λ, avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
        (B.layerEval (B.avgOp (B.bareSpaceOnIncl W f)) y *
          B.layerEval (B.avgOp (B.bareSpaceOnIncl W f)) y) - K * N2 ≤
      ∑ y ∈ Λ, avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
        (B.layerEval (B.avgOp (B.bareSpaceOnIncl W
            (B.mulOnBare W (fun x => Real.exp (θ x)) f))) y *
          B.layerEval (B.avgOp (B.bareSpaceOnIncl W
            (B.mulOnBare W (fun x => Real.exp (-θ x)) f))) y) := by
    rw [invScaleNorm_sq_eq_blocks B hb hfin hU] at hN2
    rw [hN2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun y hy => ?_
    have hy' : y ∈ B.allSites := ((finite_sitesIn B hfin W).mem_toFinset.1 hy).1
    simp only [layerEval_of_mem B hy']
    have h1 := site_term_le B hav hshort hLip f hy'
    have ha := hwt (B.level y)
    have ha0 : 0 ≤ avgWeight D.L (B.level y) := by linarith
    have hξ := siteScale_pos B y
    set a : ℝ := avgWeight D.L (B.level y) with hadef
    set ξ : ℝ := B.siteScale y with hξdef
    set n : ℝ := TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) with hn
    set q : ℝ := B.avgOp (B.bareSpaceOnIncl W f) ⟨y, hy'⟩ with hq
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg ha0 (sq_nonneg ξ))
    refine le_trans ?_ h2
    rw [mul_sub]
    have e1 : a * ξ ^ 2 * (K * ((ξ ^ 2)⁻¹ * n) ^ 2) = a * (K * ((ξ ^ 2)⁻¹ * n ^ 2)) := by
      field_simp
    rw [e1]
    have e2 : a * (K * ((ξ ^ 2)⁻¹ * n ^ 2)) ≤ K * ((ξ ^ 2)⁻¹ * n ^ 2) :=
      mul_le_of_le_one_left (mul_nonneg hK0 (by positivity)) ha.2
    have e3 : a * ξ ^ 2 * (q * q) = a * ξ ^ 2 * q ^ 2 := by ring
    rw [e3]
    linarith
  have hnum := small_constants_le h3
  have hnum' : (8 * (ε ^ 2 * (D.L : ℝ) ^ 2) + K) * N2 ≤ coercivityConst D.L / 4 * N2 :=
    mul_le_mul_of_nonneg_right hnum hN0
  rw [admissibleForm_eq_sum B hfin, admissibleForm_eq_sum B hfin]
  linarith
theorem conj_lower_bound (hb : BlockPartition B) (hfin : B.allSites.Finite)
    (hav : B.AvgRelations) (hshort : B.BlocksAndBondsShort)
    (hwt : ∀ n, coercivityConst D.L ≤ avgWeight D.L n ∧ avgWeight D.L n ≤ 1)
    {θ : D.Space → ℝ} (hLip : B.IsWeightedLipschitz θ) {W : Set D.Space}
    {𝔟 : Set D.Bond} (hU : B.IsBlockUnion W)
    (hco : ∀ f : ↥(B.bareSpaceOn W),
      coercivityConst D.L * B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 ≤
        B.admissibleForm W 𝔟 f f) (f : ↥(B.bareSpaceOn W)) :
    1 / 2 * TorusData.bondNorm 𝔟 (TorusData.bondGrad (f : D.BareSite → ℝ)) ^ 2 +
        1 / 4 * coercivityConst D.L *
          B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 ≤
      B.bareInner f (B.conjAdmissibleOp W 𝔟 θ f) := by
  have e : B.bareInner f (B.conjAdmissibleOp W 𝔟 θ f) =
      B.admissibleForm W 𝔟 (B.mulOnBare W (fun x => Real.exp (θ x)) f)
        (B.mulOnBare W (fun x => Real.exp (-θ x)) f) := by
    rw [← (admissibleOp_spec B hfin W 𝔟).2]
    unfold SeparatedChain.bareInner
    congr 1
    refine finsum_mem_congr rfl fun x _ => ?_
    change (f : D.BareSite → ℝ) x * (Real.exp (θ (x : D.Space)) *
        (B.admissibleOp W 𝔟 (B.mulOnBare W (fun x => Real.exp (-θ x)) f) :
          D.BareSite → ℝ) x) =
      Real.exp (θ (x : D.Space)) * (f : D.BareSite → ℝ) x *
        (B.admissibleOp W 𝔟 (B.mulOnBare W (fun x => Real.exp (-θ x)) f) :
          D.BareSite → ℝ) x
    ring
  rw [e]
  have h1 := form_sub_le_conj_form (𝔟 := 𝔟) B hb hfin hav hshort hwt hLip hU f
  have h2 := hco f
  have h3 := bondNorm_grad_sq_le_form B hfin hwt W 𝔟 f
  linarith
end CoercivityProof
namespace CoercivityProof
variable {D : TorusData} (B : SeparatedChain D)
open GivenChainGeneral
theorem stage_zero_nonempty {W : Set D.Space} (hU : B.IsBlockUnion W) :
    (B.stage 0).Nonempty := by
  obtain ⟨Y, ⟨y, hy⟩, hY, -⟩ := hU
  obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.1 (hY hy)
  have hn' : n ≤ D.top := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  have h1 : (B.stage n).Nonempty := by
    have h2 : y ∈ B.layer n := hyn.2
    unfold SeparatedChain.layer at h2
    by_cases h3 : n < D.top
    · rw [if_pos h3] at h2
      obtain ⟨x, hx⟩ := closure_nonempty_iff.1 ⟨y, h2⟩
      exact ⟨x, hx.1⟩
    · rw [if_neg h3, if_pos (le_antisymm hn' (not_lt.1 h3))] at h2
      exact ⟨y, h2⟩
  clear hyn hn
  induction n with
  | zero => exact h1
  | succ k ih =>
    obtain ⟨x, hx⟩ := h1
    exact ih (by omega) ⟨x, B.decreasing k (by omega) hx⟩
theorem admissibleOp_isUnit {W : Set D.Space} {𝔟 : Set D.Bond}
    (hpos : ∀ f : ↥(B.bareSpaceOn W), f ≠ 0 →
      0 < B.bareInner f (B.admissibleOp W 𝔟 f)) : IsUnit (B.admissibleOp W 𝔟) := by
  have := D.bareSite_finite
  have hinj : Function.Injective (B.admissibleOp W 𝔟) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hne
    have h1 := hpos f hne
    rw [hf] at h1
    have h2 : B.bareInner f ((0 : ↥(B.bareSpaceOn W)) : D.BareSite → ℝ) = 0 := by
      unfold SeparatedChain.bareInner
      simp
    exact h1.ne' h2
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  exact (Module.End.isUnit_iff _).2 ⟨hinj, hsurj⟩
theorem mulOnBare_exp_cancel (W : Set D.Space) (θ : D.Space → ℝ) :
    B.mulOnBare W (fun x => Real.exp (θ x)) *
        B.mulOnBare W (fun x => Real.exp (-θ x)) = 1 ∧
      B.mulOnBare W (fun x => Real.exp (-θ x)) *
        B.mulOnBare W (fun x => Real.exp (θ x)) = 1 := by
  constructor
  · ext f x
    change Real.exp (θ (x : D.Space)) * (Real.exp (-θ (x : D.Space)) * (f : D.BareSite → ℝ) x) =
      (f : D.BareSite → ℝ) x
    rw [← mul_assoc, ← Real.exp_add]
    simp
  · ext f x
    change Real.exp (-θ (x : D.Space)) * (Real.exp (θ (x : D.Space)) * (f : D.BareSite → ℝ) x) =
      (f : D.BareSite → ℝ) x
    rw [← mul_assoc, ← Real.exp_add]
    simp
theorem conjOp_mul_conjGreen {W : Set D.Space} {𝔟 : Set D.Bond}
    (hu : IsUnit (B.admissibleOp W 𝔟)) (θ : D.Space → ℝ) :
    B.conjAdmissibleOp W 𝔟 θ * B.conjAdmissibleGreen W 𝔟 θ = 1 := by
  obtain ⟨h1, h2⟩ := mulOnBare_exp_cancel B W θ
  have h3 : B.admissibleOp W 𝔟 * B.admissibleGreen W 𝔟 = 1 := Ring.mul_inverse_cancel _ hu
  unfold SeparatedChain.conjAdmissibleOp SeparatedChain.conjAdmissibleGreen
  set E := B.mulOnBare W (fun x => Real.exp (θ x))
  set E' := B.mulOnBare W (fun x => Real.exp (-θ x))
  set A := B.admissibleOp W 𝔟
  set G := B.admissibleGreen W 𝔟
  calc E * A * E' * (E * G * E') = E * (A * ((E' * E) * (G * E'))) := by
        simp only [mul_assoc]
    _ = E * (A * (G * E')) := by rw [h2, one_mul]
    _ = E * ((A * G) * E') := by simp only [mul_assoc]
    _ = E * E' := by rw [h3, one_mul]
    _ = 1 := h1
theorem bareInner_le_scaleNorm (v f : ↥B.bareSpace) :
    B.bareInner v f ≤ B.invScaleNorm v * B.scaleNorm f := by
  have h1 := bareInner_le B (fun x => (B.bareScale x)⁻¹ * (v : D.BareSite → ℝ) x)
    (fun x => B.bareScale x * (f : D.BareSite → ℝ) x)
  have e : B.bareInner (fun x => (B.bareScale x)⁻¹ * (v : D.BareSite → ℝ) x)
      (fun x => B.bareScale x * (f : D.BareSite → ℝ) x) = B.bareInner v f := by
    unfold SeparatedChain.bareInner
    congr 1
    refine finsum_mem_congr rfl fun x _ => ?_
    have := (bareScale_pos B x).ne'
    field_simp
  rw [e] at h1
  rw [invScaleNorm_eq]
  exact h1
theorem bounds_of_quadratic_le {c p t w : ℝ} (hc : 0 < c) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (h : 1 / 2 * w ^ 2 + 1 / 4 * c * p ^ 2 ≤ p * t) :
    p ≤ 4 / c * t ∧ w ≤ Real.sqrt (8 / c) * t := by
  have h1 : p ≤ 4 / c * t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    rcases hp.eq_or_lt with h0 | h0
    · rw [← h0]
      nlinarith
    · have h2 : 1 / 4 * c * p ≤ t := by
        by_contra hh
        have hh' := not_le.1 hh
        nlinarith [mul_pos h0 (sub_pos.2 hh'), sq_nonneg w]
      nlinarith
  refine ⟨h1, ?_⟩
  have h3 : w ^ 2 ≤ 8 / c * t ^ 2 := by
    have h4 : p * t ≤ 4 / c * t * t := mul_le_mul_of_nonneg_right h1 ht
    have h5 : 0 ≤ 1 / 4 * c * p ^ 2 := by positivity
    have h6 : 8 / c * t ^ 2 = 2 * (4 / c * t * t) := by ring
    rw [h6]
    linarith
  have h7 : Real.sqrt (8 / c) * t = Real.sqrt (8 / c * t ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ht]
  rw [h7]
  exact Real.le_sqrt_of_sq_le h3
theorem scaleNorm_nonneg (u : ↥B.bareSpace) : 0 ≤ B.scaleNorm u := Real.sqrt_nonneg _
theorem invScaleNorm_nonneg (u : ↥B.bareSpace) : 0 ≤ B.invScaleNorm u :=
  Real.sqrt_nonneg _
theorem conj_bounds (hb : BlockPartition B) (hfin : B.allSites.Finite)
    (hav : B.AvgRelations) (hshort : B.BlocksAndBondsShort)
    (hwt : ∀ n, coercivityConst D.L ≤ avgWeight D.L n ∧ avgWeight D.L n ≤ 1)
    {θ : D.Space → ℝ} (hLip : B.IsWeightedLipschitz θ) {W : Set D.Space}
    {𝔟 : Set D.Bond} (hU : B.IsBlockUnion W)
    (hco : ∀ f : ↥(B.bareSpaceOn W),
      coercivityConst D.L * B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 ≤
        B.admissibleForm W 𝔟 f f)
    (hu : IsUnit (B.admissibleOp W 𝔟)) : B.ConjAdmissibleBounds W 𝔟 θ := by
  refine ⟨conj_lower_bound B hb hfin hav hshort hwt hLip hU hco, fun f => ?_⟩
  have hc := coercivityConst_bounds D.blocking.three_le_factor
  have hc0 : 0 < coercivityConst D.L := by linarith [hc.1]
  set v : ↥(B.bareSpaceOn W) := B.conjAdmissibleGreen W 𝔟 θ f with hv
  have h1 := conj_lower_bound B hb hfin hav hshort hwt hLip hU hco v
  have h2 : B.conjAdmissibleOp W 𝔟 θ v = f := by
    have := conjOp_mul_conjGreen B hu θ
    rw [hv, ← Module.End.mul_apply, this, Module.End.one_apply]
  rw [h2] at h1
  have h3 := bareInner_le_scaleNorm B (B.bareSpaceOnIncl W v) (B.bareSpaceOnIncl W f)
  have h4 : 1 / 2 * TorusData.bondNorm 𝔟 (TorusData.bondGrad (v : D.BareSite → ℝ)) ^ 2 +
      1 / 4 * coercivityConst D.L * B.invScaleNorm (B.bareSpaceOnIncl W v) ^ 2 ≤
      B.invScaleNorm (B.bareSpaceOnIncl W v) * B.scaleNorm (B.bareSpaceOnIncl W f) := h1.trans h3
  exact bounds_of_quadratic_le hc0 (invScaleNorm_nonneg B _) (scaleNorm_nonneg B _) h4
theorem bondGrad_le_of_conj (hshort : B.BlocksAndBondsShort) {θ : D.Space → ℝ}
    (hLip : B.IsWeightedLipschitz θ) {W : Set D.Space}
    (hsub : D.bareSites W ⊆ D.bareSites (B.stage 0)) {u v : ↥(B.bareSpaceOn W)}
    (huv : ∀ x : D.BareSite, (v : D.BareSite → ℝ) x =
      Real.exp (θ (x : D.Space)) * (u : D.BareSite → ℝ) x)
    {m : ℝ} {b : D.Bond}
    (hH : b.target ∈ D.bareSites (B.stage 0) → m ≤ θ (b.target : D.Space))
    (hT : b.source ∈ D.bareSites (B.stage 0) → m ≤ θ (b.source : D.Space)) :
    |TorusData.bondGrad (u : D.BareSite → ℝ) b| ≤ Real.exp (-m) *
      (|TorusData.bondGrad (v : D.BareSite → ℝ) b| +
        2 * greenDecayRate 4 D.L * (D.L : ℝ) *
          |(B.bareScale b.target)⁻¹ * (v : D.BareSite → ℝ) b.target|) := by
  have hξ0 : 0 < D.scale 0 := scale_pos D 0
  have hε := greenDecayRate_bounds D.blocking.three_le_factor
  have hLn : (0 : ℝ) ≤ D.L := Nat.cast_nonneg _
  have hu' : ∀ x : D.BareSite, (u : D.BareSite → ℝ) x =
      Real.exp (-θ (x : D.Space)) * (v : D.BareSite → ℝ) x := by
    intro x
    rw [huv x, ← mul_assoc, ← Real.exp_add]
    simp
  simp only [TorusData.bondGrad, TorusData.bondDiff]
  set s : ℝ := (D.scale 0)⁻¹ with hs
  have hs0 : 0 < s := inv_pos.2 hξ0
  set vp : ℝ := (v : D.BareSite → ℝ) b.target with hvp
  set vm : ℝ := (v : D.BareSite → ℝ) b.source with hvm
  set tp : ℝ := θ (b.target : D.Space) with htp
  set tm : ℝ := θ (b.source : D.Space) with htm
  set Q : ℝ := 2 * greenDecayRate 4 D.L * (D.L : ℝ) * |(B.bareScale b.target)⁻¹ * vp| with hQ
  have hQ0 : 0 ≤ Q :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε.1.le) hLn) (abs_nonneg _)
  have hup : (u : D.BareSite → ℝ) b.target = Real.exp (-tp) * vp := hu' _
  have hum : (u : D.BareSite → ℝ) b.source = Real.exp (-tm) * vm := hu' _
  rw [hup, hum]
  have hexp0 : ∀ a : ℝ, m ≤ a → Real.exp (-a) ≤ Real.exp (-m) := fun a ha =>
    Real.exp_le_exp.2 (by linarith)
  by_cases h1 : b.target ∈ D.bareSites W <;> by_cases h2 : b.source ∈ D.bareSites W
  · obtain ⟨g1, g2, -⟩ := abs_weight_sub_le_on_bond B hshort hLip (hsub h2) (hsub h1)
    change |tp - tm| ≤ greenDecayRate 4 D.L at g1
    change |tp - tm| ≤ greenDecayRate 4 D.L * ((D.L : ℝ) * D.scale 0 *
      (B.bareScale b.target)⁻¹) at g2
    have habs : |tm - tp| = |tp - tm| := abs_sub_comm _ _
    have g3 : |Real.exp (tm - tp) - 1| ≤ 2 * |tm - tp| :=
      Real.abs_exp_sub_one_le (by rw [habs]; exact g1.trans hε.2.1)
    have e : s * (Real.exp (-tp) * vp - Real.exp (-tm) * vm) =
        Real.exp (-tm) * (s * (vp - vm) + s * (Real.exp (tm - tp) - 1) * vp) := by
      have : Real.exp (-tp) = Real.exp (-tm) * Real.exp (tm - tp) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [this]
      ring
    rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hi : 0 < B.bareScale b.target := bareScale_pos B _
    have g4 : |s * (Real.exp (tm - tp) - 1) * vp| ≤ Q := by
      rw [abs_mul, abs_mul, abs_of_pos hs0]
      have g5 : |Real.exp (tm - tp) - 1| ≤ 2 * (greenDecayRate 4 D.L * ((D.L : ℝ) * D.scale 0 *
          (B.bareScale b.target)⁻¹)) := by
        refine g3.trans ?_
        rw [habs]
        linarith
      have g6 : s * |Real.exp (tm - tp) - 1| * |vp| ≤ s * (2 * (greenDecayRate 4 D.L *
          ((D.L : ℝ) * D.scale 0 * (B.bareScale b.target)⁻¹))) * |vp| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left g5 hs0.le) (abs_nonneg _)
      refine g6.trans_eq ?_
      rw [hQ, abs_mul, abs_of_pos (inv_pos.2 hi)]
      have : s * D.scale 0 = 1 := inv_mul_cancel₀ hξ0.ne'
      calc _ = (s * D.scale 0) * (2 * greenDecayRate 4 D.L * (D.L : ℝ) *
            ((B.bareScale b.target)⁻¹ * |vp|)) := by ring
        _ = _ := by rw [this, one_mul]
    have g7 := abs_add_le (s * (vp - vm)) (s * (Real.exp (tm - tp) - 1) * vp)
    have g8 : |s * (vp - vm) + s * (Real.exp (tm - tp) - 1) * vp| ≤ |s * (vp - vm)| + Q := by
      linarith
    exact mul_le_mul (hexp0 _ (hT (hsub h2))) g8 (abs_nonneg _) (Real.exp_pos _).le
  · have hz : vm = 0 := v.2.2 _ h2
    rw [hz] at *
    have e : s * (Real.exp (-tp) * vp - Real.exp (-tm) * 0) =
        Real.exp (-tp) * (s * (vp - 0)) := by ring
    rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hexp0 _ (hH (hsub h1))) ?_ (abs_nonneg _) (Real.exp_pos _).le
    linarith
  · have hz : vp = 0 := v.2.2 _ h1
    have e : s * (Real.exp (-tp) * vp - Real.exp (-tm) * vm) =
        Real.exp (-tm) * (s * (vp - vm)) := by
      rw [hz]
      ring
    rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hexp0 _ (hT (hsub h2))) ?_ (abs_nonneg _) (Real.exp_pos _).le
    linarith
  · have hz1 : vp = 0 := v.2.2 _ h1
    have hz2 : vm = 0 := v.2.2 _ h2
    have e : s * (Real.exp (-tp) * vp - Real.exp (-tm) * vm) = 0 := by
      rw [hz1, hz2]
      ring
    rw [e, abs_zero]
    exact mul_nonneg (Real.exp_pos _).le (add_nonneg (abs_nonneg _) hQ0)
theorem bondNorm_target_term_le {W : Set D.Space} (S : Set D.Bond) (v : ↥(B.bareSpaceOn W))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    TorusData.bondNorm S (fun b => τ *
        |(B.bareScale b.target)⁻¹ * (v : D.BareSite → ℝ) b.target|) ≤
      2 * τ * B.invScaleNorm (B.bareSpaceOnIncl W v) := by
  classical
  have hc : 0 ≤ D.scale 0 ^ 4 := (pow_pos (scale_pos D 0) 4).le
  refine (sq_le_sq₀ (bondNorm_nonneg _ _)
    (mul_nonneg (by positivity) (invScaleNorm_nonneg B _))).1 ?_
  rw [bondNorm_sq, mul_pow, invScaleNorm_sq_eq_sum]
  set T : D.BareSite → ℝ := fun x => ((B.bareScale x)⁻¹ * (v : D.BareSite → ℝ) x) ^ 2 with hT
  have h1 : ∑ᶠ b ∈ S, (τ * |(B.bareScale b.target)⁻¹ * (v : D.BareSite → ℝ) b.target|) ^ 2 =
      τ ^ 2 * ∑ b ∈ Finset.univ.filter (· ∈ S), T b.target := by
    rw [finsum_mem_eq_sum_indicator, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hbS : b ∈ S
    · rw [indicator_of_mem hbS, if_pos hbS, mul_pow, sq_abs]
    · rw [indicator_of_notMem hbS, if_neg hbS, mul_zero]
  rw [h1]
  have h2 : ∑ b ∈ Finset.univ.filter (· ∈ S), T b.target ≤ 4 * ∑ x, T x :=
    sum_endpoint_le _ target_dir_injective _ fun _ => sq_nonneg _
  calc D.scale 0 ^ 4 * (τ ^ 2 * ∑ b ∈ Finset.univ.filter (· ∈ S), T b.target)
      ≤ D.scale 0 ^ 4 * (τ ^ 2 * (4 * ∑ x, T x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) hc
    _ = _ := by ring
theorem bondNorm_abs (S : Set D.Bond) (A : D.Bond → ℝ) :
    TorusData.bondNorm S (fun b => |A b|) = TorusData.bondNorm S A := by
  unfold TorusData.bondNorm
  simp only [sq_abs]
theorem decay_arith {ε c L r a g p w T X : ℝ} (hε : 0 < ε) (hc : 0 < c) (hL : 0 ≤ L)
    (hp0 : 0 ≤ p) (ha : a ≤ Real.exp (-(ε * (r - 2))) * p)
    (hg : g ≤ Real.exp (-(ε * (r - 3))) * (w + 4 * ε * L * p))
    (hp : p ≤ 4 / c * T) (hw : w ≤ Real.sqrt (8 / c) * T)
    (hT : T ≤ Real.exp (2 * ε) * X) :
    a + g ≤ Real.exp (ε * 5) * (4 / c + Real.sqrt (8 / c) + 8 * ε * L * 2 / c) * X *
      Real.exp (-(ε * r)) := by
  set R : ℝ := Real.exp (-(ε * r)) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have e2 : Real.exp (-(ε * (r - 2))) = R * Real.exp (2 * ε) := by
    rw [hR, ← Real.exp_add]
    congr 1
    ring
  have e3 : Real.exp (-(ε * (r - 3))) = R * Real.exp (3 * ε) := by
    rw [hR, ← Real.exp_add]
    congr 1
    ring
  have e5 : Real.exp (ε * 5) = Real.exp (3 * ε) * Real.exp (2 * ε) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h23 : Real.exp (2 * ε) ≤ Real.exp (3 * ε) := Real.exp_le_exp.2 (by linarith)
  set s : ℝ := Real.sqrt (8 / c) with hs
  have h1 : a ≤ R * Real.exp (3 * ε) * (4 / c * T) := by
    refine ha.trans ?_
    rw [e2]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h23 hR0.le) hp hp0 (by positivity)
  have h2 : g ≤ R * Real.exp (3 * ε) * (s * T + 4 * ε * L * (4 / c * T)) := by
    refine hg.trans ?_
    rw [e3]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : 4 * ε * L * p ≤ 4 * ε * L * (4 / c * T) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    linarith
  have h3 : a + g ≤ R * Real.exp (3 * ε) * ((4 / c + s + 8 * ε * L * 2 / c) * T) := by
    have e : 4 / c * T + (s * T + 4 * ε * L * (4 / c * T)) =
        (4 / c + s + 8 * ε * L * 2 / c) * T := by
      field_simp
      ring
    rw [← e, mul_add]
    linarith
  refine h3.trans ?_
  have h4 : 0 ≤ 4 / c + s + 8 * ε * L * 2 / c := by positivity
  have h5 : (4 / c + s + 8 * ε * L * 2 / c) * T ≤
      (4 / c + s + 8 * ε * L * 2 / c) * (Real.exp (2 * ε) * X) :=
    mul_le_mul_of_nonneg_left hT h4
  calc _ ≤ R * Real.exp (3 * ε) * ((4 / c + s + 8 * ε * L * 2 / c) * (Real.exp (2 * ε) * X)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := by
        rw [e5]
        ring
theorem admissibleGreen_decay (hb : BlockPartition B) (hfin : B.allSites.Finite)
    (hav : B.AvgRelations) (hshort : B.BlocksAndBondsShort)
    (hwt : ∀ n, coercivityConst D.L ≤ avgWeight D.L n ∧ avgWeight D.L n ≤ 1)
    (htri : ∀ x x' x'' : D.Space, B.weightedDistance x x'' ≤
      B.weightedDistance x x' + B.weightedDistance x' x'')
    {W : Set D.Space} {𝔟 : Set D.Bond} (hU : B.IsBlockUnion W)
    (hco : ∀ f : ↥(B.bareSpaceOn W),
      coercivityConst D.L * B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 ≤
        B.admissibleForm W 𝔟 f f)
    (hu : IsUnit (B.admissibleOp W 𝔟)) : B.AdmissibleGreenDecay W 𝔟 := by
  intro y' hy' f hf y'' hy''
  have h3 := D.blocking.three_le_factor
  have hc := coercivityConst_bounds h3
  have hc0 : 0 < coercivityConst D.L := by linarith [hc.1]
  have hεb := greenDecayRate_bounds h3
  have hsub := bareSites_subset_stage B hb hU
  set ε : ℝ := greenDecayRate 4 D.L with hε
  have hε0 : 0 < ε := hεb.1
  have hy'A : y' ∈ B.allSites := hy'.1
  have hcomm := weightedDistance_symm B
  set θ : D.Space → ℝ := fun x => ε * B.weightedDistance x y' with hθ
  have hLip : B.IsWeightedLipschitz θ := by
    intro x x'
    have h1 := htri x x' y'
    have h2 := htri x' x y'
    rw [hcomm x' x] at h2
    change |ε * B.weightedDistance x y' - ε * B.weightedDistance x' y'| ≤
      ε * B.weightedDistance x x'
    rw [← mul_sub, abs_mul, abs_of_pos hε0]
    refine mul_le_mul_of_nonneg_left ?_ hε0.le
    rw [abs_le]
    constructor <;> linarith
  have hblockW : B.block y' ⊆ D.bareSites W := by
    rw [bareSites_eq_iUnion_block B hb hU]
    exact fun x hx => mem_iUnion₂.2 ⟨y', hy', hx⟩
  set fW : ↥(B.bareSpaceOn W) := B.restrictBare W f with hfW
  have hfW' : ∀ x, (fW : D.BareSite → ℝ) x = (f : D.BareSite → ℝ) x := by
    intro x
    change (D.bareSites W).indicator (f : D.BareSite → ℝ) x = _
    by_cases hx : x ∈ D.bareSites W
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hf x fun h => hx (hblockW h)]
  set u : ↥(B.bareSpaceOn W) := B.admissibleGreen W 𝔟 fW with hu'
  set E := B.mulOnBare W (fun x => Real.exp (θ x)) with hE
  set E' := B.mulOnBare W (fun x => Real.exp (-θ x)) with hE'
  obtain ⟨-, hcancel⟩ := mulOnBare_exp_cancel B W θ
  set h : ↥(B.bareSpaceOn W) := E fW with hh
  set v : ↥(B.bareSpaceOn W) := E u with hv
  have hvG : B.conjAdmissibleGreen W 𝔟 θ h = v := by
    have e1 : E' h = fW := by
      rw [hh, ← Module.End.mul_apply, hcancel, Module.End.one_apply]
    change E (B.admissibleGreen W 𝔟 (E' h)) = v
    rw [e1]
  have hb2 := (conj_bounds B hb hfin hav hshort hwt hLip hU hco hu).2 h
  rw [hvG] at hb2
  obtain ⟨hp, hw⟩ := hb2
  set p : ℝ := B.invScaleNorm (B.bareSpaceOnIncl W v) with hpdef
  set w : ℝ := TorusData.bondNorm 𝔟 (TorusData.bondGrad (v : D.BareSite → ℝ)) with hwdef
  set Tn : ℝ := B.scaleNorm (B.bareSpaceOnIncl W h) with hTn
  have hp0 : 0 ≤ p := invScaleNorm_nonneg B _
  have hξ' : 0 < B.siteScale y' := siteScale_pos B y'
  have hξ'' : 0 < B.siteScale y'' := siteScale_pos B y''
  have hTnle : Tn ≤ Real.exp (2 * ε) * (B.siteScale y' * B.bareSpaceNorm f) := by
    have e : Tn = B.bareSpaceNorm (fun x => B.bareScale x *
        (Real.exp (θ (x : D.Space)) * (fW : D.BareSite → ℝ) x)) := rfl
    rw [e, ← mul_assoc]
    refine bareSpaceNorm_le_mul B (by positivity) fun x _ => ?_
    rw [hfW' x]
    by_cases hx : x ∈ B.block y'
    · rw [bareScale_eq B hb hy'A hx, abs_mul, abs_mul, abs_of_pos hξ',
        abs_of_pos (Real.exp_pos _)]
      have h1 : θ (x : D.Space) ≤ 2 * ε := by
        have h2 := hshort.1 y' hy'A x hx
        change ε * B.weightedDistance (x : D.Space) y' ≤ _
        have h4 := mul_le_mul_of_nonneg_left h2 hε0.le
        linarith
      have h2 := Real.exp_le_exp.2 h1
      calc B.siteScale y' * (Real.exp (θ (x : D.Space)) * |(f : D.BareSite → ℝ) x|)
          ≤ B.siteScale y' * (Real.exp (2 * ε) * |(f : D.BareSite → ℝ) x|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) hξ'.le
        _ = _ := by ring
    · rw [hf x hx]
      simp
  set r : ℝ := B.weightedDistance y'' y' with hr
  have hlow1 : ∀ x ∈ B.block y'', ε * (r - 2) ≤ θ (x : D.Space) := by
    intro x hx
    have h1 := hshort.1 y'' hy'' x hx
    have h2 := htri y'' (x : D.Space) y'
    rw [hcomm y'' (x : D.Space)] at h2
    change _ ≤ ε * B.weightedDistance (x : D.Space) y'
    refine mul_le_mul_of_nonneg_left ?_ hε0.le
    linarith
  have hlow2 : ∀ x ∈ B.block y'', ∀ x' : D.BareSite, x' ∈ D.bareSites (B.stage 0) →
      TorusData.Adjacent x x' → ε * (r - 3) ≤ θ (x' : D.Space) := by
    intro x hx x' hx' hj
    have h1 := hshort.1 y'' hy'' x hx
    have h2 := htri y'' (x : D.Space) y'
    rw [hcomm y'' (x : D.Space)] at h2
    have h3 := htri (x : D.Space) (x' : D.Space) y'
    obtain ⟨-, h4, h5⟩ := hshort.2 x x' (block_subset_stage B hb hy'' hx) hx' hj
    have h6 := h4.trans (h5.trans (min_le_left _ _))
    change _ ≤ ε * B.weightedDistance (x' : D.Space) y'
    refine mul_le_mul_of_nonneg_left ?_ hε0.le
    linarith
  have huv : ∀ x : D.BareSite, (v : D.BareSite → ℝ) x =
      Real.exp (θ (x : D.Space)) * (u : D.BareSite → ℝ) x := fun x => rfl
  set a : ℝ := TorusData.siteNorm (B.block y'')
    (fun x => (B.bareScale x)⁻¹ * (u : D.BareSite → ℝ) x) with ha
  have hnorm_eq : B.localAdmissibleNorm (B.admissibleGreenExt W 𝔟 f) 𝔟 y'' =
      Real.sqrt (a ^ 2 + TorusData.bondNorm (𝔟 ∩ B.blockBondSet y'')
        (TorusData.bondGrad (u : D.BareSite → ℝ)) ^ 2) := by
    unfold SeparatedChain.localAdmissibleNorm
    rw [inverse_scaleOnBare_apply]
    rfl
  set g : ℝ := TorusData.bondNorm (𝔟 ∩ B.blockBondSet y'')
    (TorusData.bondGrad (u : D.BareSite → ℝ)) with hg
  have ha0 : 0 ≤ a := siteNorm_nonneg _ _
  have hg0 : 0 ≤ g := bondNorm_nonneg _ _
  have hale : a ≤ Real.exp (-(ε * (r - 2))) * p := by
    have h1 : a ≤ Real.exp (-(ε * (r - 2))) * TorusData.siteNorm (B.block y'')
        (fun x => (B.bareScale x)⁻¹ * (v : D.BareSite → ℝ) x) := by
      refine siteNorm_le_mul (Real.exp_pos _).le fun x hx => ?_
      have e : (B.bareScale x)⁻¹ * (Real.exp (θ (x : D.Space)) * (u : D.BareSite → ℝ) x) =
          Real.exp (θ (x : D.Space)) * ((B.bareScale x)⁻¹ * (u : D.BareSite → ℝ) x) := by
        ring
      have hval : |(B.bareScale x)⁻¹ * (v : D.BareSite → ℝ) x| =
          Real.exp (θ (x : D.Space)) * |(B.bareScale x)⁻¹ * (u : D.BareSite → ℝ) x| := by
        rw [huv x, e, abs_mul, abs_of_pos (Real.exp_pos (θ (x : D.Space)))]
      change |(B.bareScale x)⁻¹ * (u : D.BareSite → ℝ) x| ≤ Real.exp (-(ε * (r - 2))) *
        |(B.bareScale x)⁻¹ * (v : D.BareSite → ℝ) x|
      rw [hval, ← mul_assoc]
      have h2 : 1 ≤ Real.exp (-(ε * (r - 2))) * Real.exp (θ (x : D.Space)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith [hlow1 x hx])
      exact le_mul_of_one_le_left (abs_nonneg _) h2
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    rw [hpdef, invScaleNorm_eq]
    exact siteNorm_block_le B hb hy'' _
  have hgle : g ≤ Real.exp (-(ε * (r - 3))) * (w + 4 * ε * (D.L : ℝ) * p) := by
    have hbound : ∀ b ∈ 𝔟 ∩ B.blockBondSet y'', |TorusData.bondGrad (u : D.BareSite → ℝ) b| ≤
        Real.exp (-(ε * (r - 3))) * (|TorusData.bondGrad (v : D.BareSite → ℝ) b| +
          2 * ε * (D.L : ℝ) * |(B.bareScale b.target)⁻¹ * (v : D.BareSite → ℝ) b.target|) := by
      intro b hbm
      obtain ⟨x, hx, hbx⟩ := mem_iUnion₂.1 hbm.2
      have hxm : ε * (r - 3) ≤ θ (x : D.Space) := by
        have := hlow1 x hx
        nlinarith
      refine bondGrad_le_of_conj B hshort hLip hsub huv (fun hh' => ?_) (fun ht' => ?_)
      · rcases hbx with hbx | hbx
        · exact hlow2 x hx _ hh' ⟨b, Or.inl ⟨hbx, rfl⟩⟩
        · rw [hbx]
          exact hxm
      · rcases hbx with hbx | hbx
        · rw [hbx]
          exact hxm
        · exact hlow2 x hx _ ht' ⟨b, Or.inr ⟨rfl, hbx⟩⟩
    have h1 := bondNorm_le_of_le_add (Real.exp_pos (-(ε * (r - 3)))).le hbound
    refine h1.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Real.exp_pos _).le)
    · rw [bondNorm_abs]
      exact bondNorm_mono inter_subset_left _
    · have := bondNorm_target_term_le B (𝔟 ∩ B.blockBondSet y'') v (τ := 2 * ε * (D.L : ℝ))
        (by positivity)
      refine this.trans_eq ?_
      ring
  have hfinal := decay_arith (L := (D.L : ℝ)) hε0 hc0 (Nat.cast_nonneg _) hp0 hale hgle hp
    hw hTnle
  have hC : weightedBoundConst 4 D.L = Real.exp (ε * 5) * (4 / coercivityConst D.L +
      Real.sqrt (8 / coercivityConst D.L) + 8 * ε * (D.L : ℝ) * 2 / coercivityConst D.L) := by
    unfold weightedBoundConst
    have h4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
      rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h4]
    norm_num
    rw [← hε]
  have hsqrt : Real.sqrt (a ^ 2 + g ^ 2) ≤ a + g :=
    Real.sqrt_le_iff.2 ⟨add_nonneg ha0 hg0, by nlinarith⟩
  have hlocal : Real.sqrt (a ^ 2 + g ^ 2) ≤ weightedBoundConst 4 D.L * B.siteScale y' *
      Real.exp (-(ε * r)) * B.bareSpaceNorm f := by
    refine hsqrt.trans (hfinal.trans_eq ?_)
    rw [hC]
    ring
  refine ⟨by rw [hnorm_eq]; exact hlocal, ?_⟩
  have h1 : TorusData.siteNorm (B.block y'') (B.admissibleGreenExt W 𝔟 f : D.BareSite → ℝ) ≤
      B.siteScale y'' * a := by
    refine siteNorm_le_mul hξ''.le fun x hx => ?_
    change |(u : D.BareSite → ℝ) x| ≤ _
    rw [abs_mul, abs_of_pos (inv_pos.2 (bareScale_pos B x)),
      bareScale_eq B hb hy'' hx, ← mul_assoc, mul_inv_cancel₀ hξ''.ne', one_mul]
  have h2 : a ≤ Real.sqrt (a ^ 2 + g ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  calc _ ≤ B.siteScale y'' * a := h1
    _ ≤ B.siteScale y'' * (weightedBoundConst 4 D.L * B.siteScale y' *
          Real.exp (-(ε * r)) * B.bareSpaceNorm f) :=
        mul_le_mul_of_nonneg_left (h2.trans hlocal) hξ''.le
    _ = _ := by ring
end CoercivityProof
open GivenChainGeneral in
theorem coercivityWeightedBounds_holds
    (hS : GivenChainGeneralFacts)
    (hAv : AvgAndMatrixFacts)
    (hBd : WeightedDistBounds)
    (hW : Dirichlet.WeightRecursionBounds)
    (hP : BoxPoincareInequality) :
    CoercivityWeightedBounds := by
  intro D B W 𝔟 hA
  have hU := hA.1
  set G : GivenChain := ⟨D, B, CoercivityProof.stage_zero_nonempty B hU⟩ with hG
  obtain ⟨-, -, -, hblock, hb, htri⟩ := hS G
  have hav : B.AvgRelations := (hAv G).1
  have hshort : B.BlocksAndBondsShort := (hBd G).2.2.2.1
  have hfin := CoercivityProof.finite_allSites B hb
  have hwt := CoercivityProof.avgWeight_bounds hW
    D.blocking.three_le_factor D.blocking.factor_odd
  have hc := CoercivityProof.coercivityConst_bounds D.blocking.three_le_factor
  have hco : ∀ f : ↥(B.bareSpaceOn W),
      coercivityConst D.L * B.invScaleNorm (B.bareSpaceOnIncl W f) ^ 2 ≤
        B.admissibleForm W 𝔟 f f := fun f =>
    CoercivityProof.form_coercive B hb hfin hav
      (fun y hy f m hm =>
        CoercivityProof.block_poincare_ineq B hP hb hblock hy f m hm)
      hwt hU hA.2.1 f
  have hspec := CoercivityProof.admissibleOp_spec B hfin W 𝔟
  have hpos : ∀ f : ↥(B.bareSpaceOn W), f ≠ 0 →
      0 < B.bareInner f (B.admissibleOp W 𝔟 f) := by
    intro f hf
    rw [hspec.2]
    have h1 := CoercivityProof.invScaleNorm_sq_pos B f hf
    have h2 : 0 < coercivityConst D.L := by linarith [hc.1]
    exact lt_of_lt_of_le (mul_pos h2 h1) (hco f)
  have hu := CoercivityProof.admissibleOp_isUnit B hpos
  exact ⟨⟨hco, hspec.1, hpos⟩,
    fun θ hθ => CoercivityProof.conj_bounds B hb hfin hav hshort hwt hθ hU hco hu,
    CoercivityProof.admissibleGreen_decay B hb hfin hav hshort hwt htri hU hco hu⟩
end YangMills.Construction.Weighted
