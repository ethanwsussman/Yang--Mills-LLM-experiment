import YangMills.Construction.Torus.WeightedLengthsAndLocalLipschitzNumbersProof
import YangMills.Construction.Weighted.LayerCutoffConstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
namespace SiteSumProof
section Exponentials
open Finset
theorem sum_exp_neg_le_of_nonneg (a c t : ℝ) (ha : 0 < a) (hc : 0 < c) (T : Finset ℤ)
    (hT : ∀ k ∈ T, 0 ≤ t + c * k) :
    ∑ k ∈ T, Real.exp (-a * (t + c * k)) ≤ 1 + 1 / (a * c) := by
  set p : ℝ := a * c with hp
  have hp0 : 0 < p := mul_pos ha hc
  set q : ℝ := Real.exp (-p) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hp0)
  set m : ℤ := ⌈-t / c⌉ with hm
  have hbase : 0 ≤ t + c * m := by
    have e1 : -t / c ≤ (m : ℝ) := Int.le_ceil _
    rw [div_le_iff₀ hc] at e1
    nlinarith
  have hmk : ∀ k ∈ T, m ≤ k := fun k hk => by
    refine Int.ceil_le.mpr ?_
    rw [div_le_iff₀ hc]
    nlinarith [hT k hk]
  have hbound : ∀ k ∈ T, Real.exp (-a * (t + c * k)) ≤ q ^ (k - m).toNat := by
    intro k hk
    have e2 : (((k - m).toNat : ℤ) : ℝ) = (k : ℝ) - m := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr (hmk k hk))]
      push_cast
      ring
    have e3 : (((k - m).toNat : ℕ) : ℝ) = (k : ℝ) - m := (Int.cast_natCast _).symm.trans e2
    rw [hq, ← Real.exp_nat_mul, e3, Real.exp_le_exp, hp]
    nlinarith [mul_nonneg ha.le hbase]
  have hinj : Set.InjOn (fun k : ℤ => (k - m).toNat) (T : Set ℤ) := by
    intro x hx y hy hxy
    have := hmk x hx
    have := hmk y hy
    simp only at hxy
    omega
  have hgeom : ∑ k ∈ T, q ^ (k - m).toNat ≤ (1 - q)⁻¹ := by
    rw [← Finset.sum_image (f := fun n : ℕ => q ^ n) hinj, ← tsum_geometric_of_lt_one hq0 hq1]
    exact (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun _ _ => pow_nonneg hq0 _)
  have hkey : q * (1 + p) ≤ 1 := by
    have e4 : q * Real.exp p = 1 := by
      rw [hq, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [Real.add_one_le_exp p, mul_le_mul_of_nonneg_left
      (show 1 + p ≤ Real.exp p by linarith [Real.add_one_le_exp p]) hq0]
  have hinv : (1 - q)⁻¹ ≤ 1 + 1 / p := by
    have hpos : 0 < 1 - q := by linarith
    rw [inv_le_comm₀ hpos (by positivity)]
    have e5 : (1 + 1 / p)⁻¹ = p / (1 + p) := by
      field_simp
      ring
    rw [e5, div_le_iff₀ (by positivity)]
    nlinarith
  exact ((Finset.sum_le_sum hbound).trans hgeom).trans hinv
theorem sum_exp_neg_abs_le (a c t : ℝ) (ha : 0 < a) (hc : 0 < c) (T : Finset ℤ) :
    ∑ k ∈ T, Real.exp (-a * |c * k - t|) ≤ 2 + 2 / (a * c) := by
  rw [← Finset.sum_filter_add_sum_filter_not T (fun k : ℤ => 0 ≤ c * k - t)]
  have hup : ∑ k ∈ T.filter (fun k : ℤ => 0 ≤ c * k - t), Real.exp (-a * |c * k - t|) ≤
      1 + 1 / (a * c) := by
    have hb := sum_exp_neg_le_of_nonneg a c (-t) ha hc (T.filter (fun k : ℤ => 0 ≤ c * k - t))
      (fun k hk => by linarith [(Finset.mem_filter.mp hk).2])
    refine (Eq.le ?_).trans hb
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [abs_of_nonneg (Finset.mem_filter.mp hk).2]
    ring_nf
  have hdown : ∑ k ∈ T.filter (fun k : ℤ => ¬ 0 ≤ c * k - t), Real.exp (-a * |c * k - t|) ≤
      1 + 1 / (a * c) := by
    have hb := sum_exp_neg_le_of_nonneg a c t ha hc
      ((T.filter (fun k : ℤ => ¬ 0 ≤ c * k - t)).image fun k => -k) (by
        intro k hk
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
        have hj' := (Finset.mem_filter.mp hj).2
        push_cast
        linarith)
    rw [Finset.sum_image (fun x _ y _ hxy => neg_injective hxy)] at hb
    refine (Eq.le ?_).trans hb
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [abs_of_neg (not_le.mp (Finset.mem_filter.mp hk).2)]
    push_cast
    ring_nf
  have htwo : 2 / (a * c) = 1 / (a * c) + 1 / (a * c) := by ring
  linarith
theorem sum_linear_mul_exp_le_eight (P : ℕ) :
    ∑ p ∈ range P, (2 * (p : ℝ) + 1) * Real.exp (-((p - 1 : ℕ) : ℝ)) ≤ 8 := by
  set w : ℕ → ℝ := fun p => (2 * (p : ℝ) + 1) * Real.exp (-((p - 1 : ℕ) : ℝ)) with hw
  have hw0 : ∀ p, 0 ≤ w p := fun p => by positivity
  set ρ : ℝ := 10 / 27 with hρ
  have hdecay : ∀ m : ℕ, Real.exp (-(m : ℝ)) ≤ ρ ^ m := by
    intro m
    have he : Real.exp (-1) ≤ ρ := by
      rw [Real.exp_neg, hρ, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have he9 := Real.exp_one_gt_d9
      norm_num at he9 ⊢
      linarith
    have hpow : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [hpow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le he m
  set V : ℕ → ℝ := fun m => (54 / 17 * (m : ℝ) + 1917 / 289) * ρ ^ m with hV
  have hV0 : ∀ m, 0 ≤ V m := fun m => by positivity
  have htel : ∀ N : ℕ, ∑ p ∈ range (N + 2), w p ≤ 4 + V 1 - V (N + 1) := by
    intro N
    induction N with
    | zero =>
      simp [Finset.sum_range_succ, hw]
      norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hnext : w (N + 2) ≤ (2 * ((N : ℝ) + 1) + 3) * ρ ^ (N + 1) := by
        have e1 : ((N + 2 - 1 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) := by
          congr 1
        simp only [hw]
        rw [e1]
        have e2 := hdecay (N + 1)
        push_cast
        have e3 : 2 * ((N : ℝ) + 2) + 1 = 2 * ((N : ℝ) + 1) + 3 := by ring
        rw [e3]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using e2
      have hdiff : V (N + 1) - V (N + 1 + 1) = (2 * ((N : ℝ) + 1) + 3) * ρ ^ (N + 1) := by
        simp only [hV, hρ]
        push_cast
        rw [pow_succ (10 / 27 : ℝ) (N + 1)]
        ring
      linarith
  have hV1 : V 1 = 1050 / 289 := by
    simp only [hV, hρ]
    norm_num
  have hall : ∑ p ∈ range (P + 2), w p ≤ 8 := by
    have e4 := htel P
    have e5 := hV0 (P + 1)
    rw [hV1] at *
    linarith
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (by omega)) (fun p _ _ => hw0 p)).trans hall
theorem pow_mul_exp_neg_le (x b : ℝ) (hx : 1 ≤ x) (hb : 4 * Real.log x + 1 ≤ b) (n : ℕ) :
    x ^ (4 * n) * Real.exp (-b * ((n - 1 : ℕ) : ℝ)) ≤
      x ^ 4 * Real.exp (-((n - 1 : ℕ) : ℝ)) := by
  have hx0 : 0 < x := by linarith
  rcases n with _ | k
  · simp
    exact one_le_pow₀ hx
  · have hk : ((k + 1 - 1 : ℕ) : ℝ) = k := by simp
    rw [hk]
    have hsplit : x ^ (4 * (k + 1)) = x ^ 4 * Real.exp (4 * Real.log x * k) := by
      have hlog : Real.exp (4 * Real.log x * k) = x ^ (4 * k) := by
        rw [show 4 * Real.log x * (k : ℝ) = ((4 * k : ℕ) : ℝ) * Real.log x by push_cast; ring]
        rw [Real.exp_nat_mul, Real.exp_log hx0]
      rw [hlog, ← pow_add]
      congr 1
      ring
    rw [hsplit, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    nlinarith
theorem sum_sum_Icc_le (i N : ℕ) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ i' ∈ range (N + 1), ∑ n ∈ Icc (max i i') N, f (n - min i i') ≤
      ∑ p ∈ range (N + 1), (2 * (p : ℝ) + 1) * f p := by
  rw [Finset.sum_sigma']
  set Q := (range (N + 1)).sigma fun i' => Icc (max i i') N with hQ
  set d : (Σ _ : ℕ, ℕ) → ℕ := fun z => z.2 - min i z.1 with hd
  have hd_mem : ∀ z ∈ Q, d z ∈ range (N + 1) := by
    intro z hz
    have hz2 := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hz).2).2
    simp only [hd, Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hd_mem]
  refine Finset.sum_le_sum fun p _ => ?_
  have hfib : ∀ z ∈ Q.filter (fun z => d z = p), f (z.2 - min i z.1) = f p := by
    intro z hz
    have hzp := (Finset.mem_filter.mp hz).2
    simp only [hd] at hzp
    rw [hzp]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hf p)
  have hcount : (Q.filter (fun z => d z = p)).card ≤ (Finset.Icc (-(p : ℤ)) p).card := by
    apply Finset.card_le_card_of_injOn (fun z => (z.1 : ℤ) - i)
    · intro z hz
      have hz' := Finset.mem_coe.mp hz
      have hzQ := (Finset.mem_filter.mp hz').1
      have hzp := (Finset.mem_filter.mp hz').2
      have hz1 := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hzQ).2).1
      simp only [hd] at hzp
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    · intro z hz z' hz' hzz
      have hzQ := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).1
      have hzp := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
      have hzQ' := (Finset.mem_filter.mp (Finset.mem_coe.mp hz')).1
      have hzp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hz')).2
      have hv := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hzQ).2).1
      have hv' := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hzQ').2).1
      simp only [hd] at hzp hzp'
      simp only at hzz
      obtain ⟨u, v⟩ := z
      obtain ⟨u', v'⟩ := z'
      simp only at hzp hzp' hv hv' hzz
      have hu : u = u' := by omega
      subst hu
      have hvv : v = v' := by omega
      subst hvv
      rfl
  have hIcc : (Finset.Icc (-(p : ℤ)) p).card = 2 * p + 1 := by
    rw [Int.card_Icc]
    omega
  exact_mod_cast hcount.trans hIcc.le
end Exponentials
open Set Filter Topology YangMills.Construction.TorusMetric
open scoped ENNReal
section Basics
variable {D : TorusData}
theorem scale_pos (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem one_le_L : (1 : ℝ) ≤ D.L := by apply _root_.YangMills.Construction.Weighted.DistBounds.one_le_L <;> assumption
theorem gap_mul_block_pos : 0 < (D.gapNumber : ℝ) * (D.blockNumber : ℝ) := by apply _root_.YangMills.Construction.Weighted.LocalComparison.gapNumber_mul_blockNumber_pos <;> assumption
variable (B : SeparatedChain D)
theorem stage_antitone {m m' : ℕ} (h : m ≤ m') (h' : m' ≤ D.top) :
    B.stage m' ⊆ B.stage m := by apply _root_.YangMills.Construction.Weighted.CubeGeometry.Layers.stage_anti <;> assumption
theorem layer_eq_closure_of_lt {n : ℕ} (h : n < D.top) :
    B.layer n = closure (B.stage n \ B.stage (n + 1)) := if_pos h
theorem layer_top_eq : B.layer D.top = B.stage D.top := by
  unfold SeparatedChain.layer
  simp
theorem layer_eq_empty_of_gt {n : ℕ} (h : D.top < n) : B.layer n = ∅ := by apply _root_.YangMills.Construction.Weighted.CubeGeometry.Layers.layer_eq_empty <;> assumption
theorem le_top_of_mem_layer {n : ℕ} {x : D.Space} (hx : x ∈ B.layer n) : n ≤ D.top := by
  by_contra h
  rw [layer_eq_empty_of_gt B (by omega)] at hx
  exact hx
theorem stage_zero_nonempty_of_mem_layer {n : ℕ} {x : D.Space} (hx : x ∈ B.layer n) :
    (B.stage 0).Nonempty := by
  have hn := le_top_of_mem_layer B hx
  rcases lt_or_eq_of_le hn with h | h
  · rw [layer_eq_closure_of_lt B h] at hx
    obtain ⟨z, hz, -⟩ := closure_nonempty_iff.mp ⟨x, hx⟩
    exact ⟨z, stage_antitone B (Nat.zero_le n) hn hz⟩
  · subst h
    rw [layer_top_eq] at hx
    exact ⟨x, stage_antitone B (Nat.zero_le _) le_rfl hx⟩
theorem exists_layer_of_mem_stage {z : D.Space} (d : ℕ) :
    ∀ a : ℕ, a + d = D.top → z ∈ B.stage a → ∃ m, a ≤ m ∧ m ≤ D.top ∧ z ∈ B.layer m := by
  induction d with
  | zero =>
    intro a ha hz
    have : a = D.top := by omega
    subst this
    exact ⟨D.top, le_rfl, le_rfl, by rw [layer_top_eq]; exact hz⟩
  | succ d ih =>
    intro a ha hz
    by_cases h : z ∈ B.stage (a + 1)
    · obtain ⟨m, h1, h2, h3⟩ := ih (a + 1) (by omega) h
      exact ⟨m, by omega, h2, h3⟩
    · refine ⟨a, le_rfl, by omega, ?_⟩
      rw [layer_eq_closure_of_lt B (by omega)]
      exact subset_closure ⟨hz, h⟩
theorem weightedLength_nonneg (Γ : List LiftedSegment) : 0 ≤ B.weightedLength Γ := by apply _root_.YangMills.Construction.Weighted.DistBounds.weightedLength_nonneg <;> assumption
theorem continuous_pointAt (S : ℝ) (s : LiftedSegment) : Continuous (s.pointAt S) := by apply _root_.YangMills.Construction.Weighted.WeightedLengthProof.continuous_pointAt <;> assumption
theorem exists_torusProj_eq {S : ℝ} (x : Torus4 S) : ∃ v, torusProj S v = x := by apply _root_.YangMills.Construction.Weighted.DistBounds.torusProj_surjective <;> assumption
theorem exists_treeGraph_through (x x' : D.Space) : ∃ Γ : List LiftedSegment,
    IsTreeGraph D.side Γ ∧ x ∈ segmentsSupport D.side Γ ∧ x' ∈ segmentsSupport D.side Γ := by apply _root_.YangMills.Construction.Weighted.DistanceAvgPairMatrixNormProof.exists_tree_joining <;> assumption
theorem weightedDistance_nonneg (x x' : D.Space) : 0 ≤ B.weightedDistance x x' := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.weightedDistance_nonneg <;> assumption
theorem weightedDistance_le_weightedLength {Γ : List LiftedSegment} {x x' : D.Space}
    (hΓ : IsTreeGraph D.side Γ)
    (hx : x ∈ segmentsSupport D.side Γ) (hx' : x' ∈ segmentsSupport D.side Γ) :
    B.weightedDistance x x' ≤ B.weightedLength Γ := by
  unfold SeparatedChain.weightedDistance
  refine csInf_le ⟨0, ?_⟩ ⟨Γ, hΓ, hx, hx', rfl⟩
  rintro _ ⟨Γ', -, -, -, rfl⟩
  exact weightedLength_nonneg B Γ'
theorem le_weightedDistance {r : ℝ} {x x' : D.Space}
    (h : ∀ Γ : List LiftedSegment, IsTreeGraph D.side Γ → x ∈ segmentsSupport D.side Γ →
      x' ∈ segmentsSupport D.side Γ → r ≤ B.weightedLength Γ) :
    r ≤ B.weightedDistance x x' := by
  unfold SeparatedChain.weightedDistance
  obtain ⟨Γ, h1, h2, h3⟩ := exists_treeGraph_through x x'
  refine le_csInf ⟨_, Γ, h1, h2, h3, rfl⟩ ?_
  rintro _ ⟨Γ', h1', h2', h3', rfl⟩
  exact h Γ' h1' h2' h3'
end Basics
section Distance
variable {S : ℝ}
theorem torusSupNorm_eq_norm (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem torusSupNorm_sub_comm (x y : Torus4 S) :
    torusSupNorm (x - y) = torusSupNorm (y - x) := by apply _root_.YangMills.Construction.Weighted.LayerCutoff.torusSupNorm_sub_comm <;> assumption
theorem setSupDist_singleton (z : Torus4 S) (A : Set (Torus4 S)) :
    setSupDist {z} A = ⨅ a ∈ A, ENNReal.ofReal (torusSupNorm (z - a)) := by
  unfold setSupDist
  simp
def supDistTo (A : Set (Torus4 S)) (z : Torus4 S) : ℝ := (setSupDist {z} A).toReal
theorem setSupDist_singleton_ne_top {A : Set (Torus4 S)} (hA : A.Nonempty)
    (z : Torus4 S) : setSupDist {z} A ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hA
  rw [setSupDist_singleton]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf₂_le a ha)
theorem supDistTo_of_mem {A : Set (Torus4 S)} {z : Torus4 S} (hz : z ∈ A) :
    supDistTo A z = 0 := by apply _root_.YangMills.Construction.Weighted.LayerCutoff.distInftyToSet_eq_zero_of_mem <;> assumption
theorem le_supDistTo {A E : Set (Torus4 S)} (hA : A.Nonempty) {c : ℝ}
    (hc : ENNReal.ofReal c ≤ setSupDist A E) {w : Torus4 S} (hw : w ∈ E) :
    c ≤ supDistTo A w := by
  have h : ENNReal.ofReal c ≤ setSupDist {w} A := by
    rw [setSupDist_singleton]
    refine le_iInf₂ fun a ha => ?_
    rw [torusSupNorm_sub_comm]
    refine hc.trans ?_
    unfold setSupDist
    exact (iInf₂_le a ha).trans (iInf₂_le w hw)
  exact (ENNReal.ofReal_le_iff_le_toReal (setSupDist_singleton_ne_top hA w)).mp h
theorem continuous_of_lipschitzL1 {f : Torus4 S → ℝ} (h : LipschitzL1 f) :
    Continuous f := by apply _root_.YangMills.Construction.Weighted.LayerCutoff.continuous_of_lipschitzL1 <;> assumption
theorem lipschitzL1_min {f : Torus4 S → ℝ} (h : LipschitzL1 f) (ρ : ℝ) :
    LipschitzL1 fun z => min (f z) ρ := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun x x' => ?_⟩
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simpa using hC x x'
theorem lipschitzL1_add {f₁ f₂ : Torus4 S → ℝ} (h₁ : LipschitzL1 f₁)
    (h₂ : LipschitzL1 f₂) {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) :
    LipschitzL1 fun z => s₁ * f₁ z + s₂ * f₂ z := by
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  refine ⟨Real.toNNReal s₁ * K₁ + Real.toNNReal s₂ * K₂, fun u v => ?_⟩
  have hsplit : s₁ * f₁ v + s₂ * f₂ v - (s₁ * f₁ u + s₂ * f₂ u) =
      s₁ * (f₁ v - f₁ u) + s₂ * (f₂ v - f₂ u) := by ring
  have b₁ := mul_le_mul_of_nonneg_left (hK₁ u v) hs₁
  have b₂ := mul_le_mul_of_nonneg_left (hK₂ u v) hs₂
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hs₁, abs_of_nonneg hs₂]
  push_cast
  rw [Real.coe_toNNReal s₁ hs₁, Real.coe_toNNReal s₂ hs₂]
  nlinarith
end Distance
section Layers
variable (hl : WeightedLengthAndLip)
  (hb : WeightedDistBounds)
  (hs : GivenChainGeneralFacts)
  (G : GivenChain)
include hl in
theorem localLip_eq_zero {f : G.data.Space → ℝ} (hf : LipschitzL1 f) {x : G.data.Space}
    (h : ∀ᶠ z in 𝓝 x, f z = f x) : localLip f x = 0 :=
  ((hl G).2.2.2.2 f f hf hf 0 0 0 le_rfl le_rfl le_rfl x).2.2.2 h
include hl in
theorem localLip_truncDist_eq_zero (X E : Set G.data.Space) (hA : (closure Xᶜ).Nonempty)
    {ρ : ℝ} (hgap : ENNReal.ofReal ρ < setSupDist (closure Xᶜ) E) {z : G.data.Space}
    (hz : z ∉ closure (X \ E)) :
    localLip (fun w => min (supDistTo (closure Xᶜ) w) ρ) z = 0 := by
  have hd : LipschitzL1LipLeOne (supDistTo (closure Xᶜ)) := (hl G).2.2.1 _ hA
  have hc : Continuous (supDistTo (closure Xᶜ)) := continuous_of_lipschitzL1 hd.1
  have hg := lipschitzL1_min hd.1 ρ
  by_cases h1 : z ∈ interior (closure Xᶜ)
  · apply localLip_eq_zero hl G hg
    have e : ∀ v ∈ interior (closure Xᶜ), supDistTo (closure Xᶜ) v = 0 :=
      fun v hv => supDistTo_of_mem (interior_subset hv)
    filter_upwards [isOpen_interior.mem_nhds h1] with w hw
    rw [e w hw, e z h1]
  by_cases h2 : ρ < supDistTo (closure Xᶜ) z
  · apply localLip_eq_zero hl G hg
    filter_upwards [(hc.tendsto z).eventually (lt_mem_nhds h2)] with w hw
    rw [min_eq_right hw.le, min_eq_right h2.le]
  exfalso
  apply hz
  obtain ⟨c, -, hc1, hc2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hgap
  have hc0 : ρ < c := by
    by_contra hcon
    exact absurd hc1 (not_lt.mpr (ENNReal.ofReal_le_ofReal (not_lt.mp hcon)))
  have hU : IsOpen {w | supDistTo (closure Xᶜ) w < c} := isOpen_lt hc continuous_const
  have hzU : z ∈ {w | supDistTo (closure Xᶜ) w < c} := lt_of_le_of_lt (not_lt.mp h2) hc0
  have hUE : ∀ w ∈ E, c ≤ supDistTo (closure Xᶜ) w := fun w hw => le_supDistTo hA hc2.le hw
  rw [mem_closure_iff_nhds]
  intro V hV
  have hV' : V ∩ {w | supDistTo (closure Xᶜ) w < c} ∈ 𝓝 z := inter_mem hV (hU.mem_nhds hzU)
  have hns : ¬ (V ∩ {w | supDistTo (closure Xᶜ) w < c} ⊆ closure Xᶜ) := fun hsub =>
    h1 (mem_interior_iff_mem_nhds.mpr (mem_of_superset hV' hsub))
  obtain ⟨w, hw, hwA⟩ := not_subset.mp hns
  refine ⟨w, hw.1, ?_, ?_⟩
  · by_contra hwX
    exact hwA (subset_closure hwX)
  · intro hwE
    exact absurd hw.2 (not_lt.mpr (hUE w hwE))
include hl in
theorem localLip_sum_le (J : Finset ℕ) (φ : ℕ → G.data.Space → ℝ) (w : ℕ → ℝ)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hφ : ∀ i ∈ J, LipschitzL1 (φ i)) (z : G.data.Space) :
    LipschitzL1 (fun u => ∑ i ∈ J, w i * φ i u) ∧
      localLip (fun u => ∑ i ∈ J, w i * φ i u) z ≤
        ∑ i ∈ J, ENNReal.ofReal (w i) * localLip (φ i) z := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    have hconst : LipschitzL1 (fun _ : G.data.Space => (0 : ℝ)) := ⟨0, by simp⟩
    simp only [Finset.sum_empty]
    exact ⟨hconst, (localLip_eq_zero hl G hconst (Eventually.of_forall fun _ => rfl)).le⟩
  | insert b J hbJ ih =>
    have hwb := hw b (Finset.mem_insert_self b J)
    have hφb := hφ b (Finset.mem_insert_self b J)
    obtain ⟨hrest, hrest'⟩ := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
      (fun i hi => hφ i (Finset.mem_insert_of_mem hi))
    have hfun : (fun u => ∑ i ∈ insert b J, w i * φ i u) =
        fun u => w b * φ b u + 1 * ∑ i ∈ J, w i * φ i u := by
      funext u
      rw [Finset.sum_insert hbJ, one_mul]
    rw [hfun, Finset.sum_insert hbJ]
    refine ⟨lipschitzL1_add hφb hrest hwb zero_le_one, ?_⟩
    refine ((hl G).2.2.2.2 (φ b) _ hφb hrest (w b) 1 0 hwb zero_le_one le_rfl z).1.trans ?_
    rw [ENNReal.ofReal_one, one_mul]
    gcongr
include hl hb hs in
theorem weightedDistance_ge_of_layer_gap {m m' : ℕ} (hmm : m + 2 ≤ m') {y y' : G.data.Space}
    (hy : y ∈ G.chain.layer m) (hy' : y' ∈ G.chain.layer m') :
    (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) * ((m' : ℝ) - m - 1) ≤
        G.chain.weightedDistance y y' ∧
      (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) * ((m' : ℝ) - m - 1) ≤
        G.chain.weightedDistance y' y := by
  classical
  have hfacts := (hs G).2.2.1
  have hm' : m' ≤ G.data.top := le_top_of_mem_layer _ hy'
  have hm : m ≤ G.data.top := by omega
  let Rg : ℝ := (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ)
  have hRg : 0 < Rg := gap_mul_block_pos
  let Y : ℕ → Set G.data.Space := fun k => closure (G.chain.stage k)ᶜ
  let trunc : ℕ → G.data.Space → ℝ := fun k u => min (supDistTo (Y k) u) (Rg * G.data.scale k)
  have hinY : ∀ k, m < k → y ∈ Y k := fun k hk =>
    hfacts.closedComplement_mono (m + 1) k hk (hfacts.layer_subset_diff m hm hy).2
  have hinStage : ∀ k, k < m' → y' ∈ G.chain.stage (k + 1) := fun k hk =>
    stage_antitone _ (by omega) hm' (hfacts.layer_subset_diff m' hm' hy').1
  have hsep : ∀ k, k < m' →
      ENNReal.ofReal (Rg * G.data.scale k) < setSupDist (Y k) (G.chain.stage (k + 1)) :=
    fun k hk => G.chain.separated k (by omega)
  have hYne : ∀ k, m < k → (Y k).Nonempty := fun k hk => ⟨y, hinY k hk⟩
  have hcap : ∀ k, 0 ≤ Rg * G.data.scale k := fun k => (mul_pos hRg (scale_pos k)).le
  have hdist : ∀ k, m < k → LipschitzL1LipLeOne (supDistTo (Y k)) :=
    fun k hk => (hl G).2.2.1 _ (hYne k hk)
  have htruncL : ∀ k ∈ Finset.Ioo m m', LipschitzL1 (trunc k) := fun k hk =>
    lipschitzL1_min (hdist k (Finset.mem_Ioo.mp hk).1).1 _
  have hcoef : ∀ k ∈ Finset.Ioo m m', 0 ≤ (G.data.scale k)⁻¹ := fun k _ =>
    inv_nonneg.mpr (scale_pos k).le
  let F : G.data.Space → ℝ := fun u => ∑ k ∈ Finset.Ioo m m', (G.data.scale k)⁻¹ * trunc k u
  have hFL : LipschitzL1 F := (localLip_sum_le hl G _ trunc _ hcoef htruncL y).1
  have hFlip : ∀ z, localLip F z ≤
      ENNReal.ofReal (1 * G.chain.weightDensity z) := by
    intro z
    refine (localLip_sum_le hl G _ trunc _ hcoef htruncL z).2.trans ?_
    have hpiece : ∀ k ∈ Finset.Ioo m m',
        ENNReal.ofReal (G.data.scale k)⁻¹ * localLip (trunc k) z ≤
          ENNReal.ofReal ((G.data.scale k)⁻¹ *
            (G.chain.layer k).indicator (fun _ => (1 : ℝ)) z) := by
      intro k hk
      have hk' := Finset.mem_Ioo.mp hk
      by_cases hzk : z ∈ G.chain.layer k
      · rw [indicator_of_mem hzk, mul_one]
        have hone : localLip (trunc k) z ≤ 1 :=
          ((hl G).2.2.2.2 (supDistTo (Y k)) (supDistTo (Y k)) (hdist k hk'.1).1
            (hdist k hk'.1).1 0 0 (Rg * G.data.scale k) le_rfl le_rfl (hcap k) z).2.1.trans
            ((hdist k hk'.1).2 z)
        calc ENNReal.ofReal (G.data.scale k)⁻¹ * localLip (trunc k) z
            ≤ ENNReal.ofReal (G.data.scale k)⁻¹ * 1 := by gcongr
          _ = ENNReal.ofReal (G.data.scale k)⁻¹ := mul_one _
      · have hzc : z ∉ closure (G.chain.stage k \ G.chain.stage (k + 1)) := by
          rwa [layer_eq_closure_of_lt _ (by omega)] at hzk
        have hzero : localLip (trunc k) z = 0 :=
          localLip_truncDist_eq_zero hl G _ _ (hYne k hk'.1) (hsep k hk'.2) hzc
        rw [hzero, mul_zero]
        exact bot_le
    refine (Finset.sum_le_sum hpiece).trans ?_
    have hnn : ∀ k ∈ Finset.Icc 1 G.data.top, 0 ≤ (G.data.scale k)⁻¹ *
        (G.chain.layer k).indicator (fun _ => (1 : ℝ)) z := fun k _ =>
      mul_nonneg (inv_nonneg.mpr (scale_pos k).le) (indicator_nonneg (fun _ _ => zero_le_one) _)
    have hIoo : Finset.Ioo m m' ⊆ Finset.Icc 1 G.data.top := by
      intro k hk
      have hk' := Finset.mem_Ioo.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [← ENNReal.ofReal_sum_of_nonneg fun k hk => hnn k (hIoo hk)]
    apply ENNReal.ofReal_le_ofReal
    rw [one_mul]
    unfold SeparatedChain.weightDensity
    have hbase : 0 ≤ (G.data.scale 0)⁻¹ *
        (G.chain.stage 1)ᶜ.indicator (fun _ => (1 : ℝ)) z :=
      mul_nonneg (inv_nonneg.mpr (scale_pos 0).le) (indicator_nonneg (fun _ _ => zero_le_one) _)
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg hIoo fun k hk _ => hnn k hk
    linarith
  have hF0 : F y = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hd0 : supDistTo (Y k) y = 0 := supDistTo_of_mem (hinY k (Finset.mem_Ioo.mp hk).1)
    simp only [trunc]
    rw [hd0, min_eq_left (hcap k), mul_zero]
  have hF1 : F y' = Rg * ((m' : ℝ) - m - 1) := by
    have hconst : ∀ k ∈ Finset.Ioo m m', (G.data.scale k)⁻¹ * trunc k y' = Rg := by
      intro k hk
      have hk' := Finset.mem_Ioo.mp hk
      have hfar : Rg * G.data.scale k ≤ supDistTo (Y k) y' :=
        le_supDistTo (hYne k hk'.1) (hsep k hk'.2).le (hinStage k hk'.2)
      simp only [trunc]
      rw [min_eq_right hfar]
      have hne := (scale_pos (D := G.data) k).ne'
      field_simp
    simp only [F]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul]
    have hcast : ((m' - m - 1 : ℕ) : ℝ) = (m' : ℝ) - m - 1 := by
      have hnat : m' = (m' - m - 1) + m + 1 := by omega
      have hreal : (m' : ℝ) = ((m' - m - 1 : ℕ) : ℝ) + m + 1 := by exact_mod_cast hnat
      linarith
    rw [hcast]
    ring
  have hcomp := ((hb G).1 F hFL).2 1 zero_le_one hFlip
  have hfwd := hcomp y y'
  have hbwd := hcomp y' y
  rw [one_mul] at hfwd hbwd
  rw [hF0, hF1] at hfwd hbwd
  have hlow : Rg * ((m' : ℝ) - m - 1) ≤ |Rg * ((m' : ℝ) - m - 1)| := le_abs_self _
  constructor
  · refine hlow.trans ?_
    simpa using hfwd
  · refine hlow.trans ?_
    simpa using hbwd
include hl hb hs in
theorem weightedDistance_layers_ge (p q : ℕ) {u v : G.data.Space}
    (hu : u ∈ G.chain.layer p) (hv : v ∈ G.chain.layer q) :
    (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) * max (|(p : ℝ) - (q : ℝ)| - 1) 0 ≤
      G.chain.weightedDistance u v := by
  rcases le_or_gt (p + 2) q with hpq | hpq
  · have hgap := (weightedDistance_ge_of_layer_gap hl hb hs G hpq hu hv).1
    have hpq' : (p : ℝ) + 2 ≤ q := by exact_mod_cast hpq
    have habs : |(p : ℝ) - (q : ℝ)| = (q : ℝ) - p := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [habs, max_eq_left (by linarith)]
    linarith
  rcases le_or_gt (q + 2) p with hqp | hqp
  · have hgap := (weightedDistance_ge_of_layer_gap hl hb hs G hqp hv hu).2
    have hqp' : (q : ℝ) + 2 ≤ p := by exact_mod_cast hqp
    have habs : |(p : ℝ) - (q : ℝ)| = (p : ℝ) - q := abs_of_nonneg (by linarith)
    rw [habs, max_eq_left (by linarith)]
    linarith
  have hp1 : (p : ℝ) ≤ q + 1 := by exact_mod_cast (show p ≤ q + 1 by omega)
  have hq1 : (q : ℝ) ≤ p + 1 := by exact_mod_cast (show q ≤ p + 1 by omega)
  have habs : |(p : ℝ) - (q : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [max_eq_right (by linarith), mul_zero]
  exact weightedDistance_nonneg _ _ _
end Layers
section Sites
variable {D : TorusData} (B : SeparatedChain D)
def siteLevel (y : D.Space) : ℕ := sInf {n | y ∈ B.layerSites n}
theorem siteLevel_spec {y : D.Space} (hy : y ∈ B.allSites) :
    y ∈ B.layerSites (siteLevel B y) ∧ siteLevel B y ≤ D.top ∧
      B.siteScale y = D.scale (siteLevel B y) := by
  have hne : {n | y ∈ B.layerSites n}.Nonempty := by
    obtain ⟨n, -, hn⟩ : ∃ n, n ∈ Finset.range (D.top + 1) ∧ y ∈ B.layerSites n := by
      simpa [SeparatedChain.allSites] using hy
    exact ⟨n, hn⟩
  have hm : y ∈ B.layerSites (siteLevel B y) := Nat.sInf_mem hne
  exact ⟨hm, le_top_of_mem_layer B hm.2, rfl⟩
end Sites
section ScaleRatio
variable (hl : WeightedLengthAndLip)
  (hb : WeightedDistBounds)
  (hs : GivenChainGeneralFacts)
  (G : GivenChain)
include hl hb hs in
theorem siteScale_div_rpow_le (t : ℝ) {u u' : G.data.Space} (hu : u ∈ G.chain.allSites)
    (hu' : u' ∈ G.chain.allSites) :
    (G.chain.siteScale u / G.chain.siteScale u') ^ t ≤
      (G.data.L : ℝ) ^ |t| *
        Real.exp (|t| * G.data.scaleRatioRate * G.chain.weightedDistance u u') := by
  obtain ⟨hmem, -, hsc⟩ := siteLevel_spec G.chain hu
  obtain ⟨hmem', -, hsc'⟩ := siteLevel_spec G.chain hu'
  set a := siteLevel G.chain u
  set a' := siteLevel G.chain u'
  have hlay := weightedDistance_layers_ge hl hb hs G a a' hmem.2 hmem'.2
  have hL1 : (1 : ℝ) ≤ G.data.L := one_le_L
  have hL0 : (0 : ℝ) < G.data.L := by linarith
  set lg := Real.log (G.data.L : ℝ) with hlg
  have hlg0 : 0 ≤ lg := Real.log_nonneg hL1
  have hGB := gap_mul_block_pos (D := G.data)
  set GB := (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) with hGBdef
  set δ := G.chain.weightedDistance u u' with hδ
  set e := max (|(a : ℝ) - (a' : ℝ)| - 1) 0 with he
  have hquot : G.chain.siteScale u / G.chain.siteScale u' =
      Real.exp (((a : ℝ) - a') * lg) := by
    have hpow : ∀ k : ℕ, ((G.data.L : ℝ)) ^ k = Real.exp ((k : ℝ) * lg) := by
      intro k
      rw [Real.exp_nat_mul, hlg, Real.exp_log hL0]
    rw [hsc, hsc', sub_mul, Real.exp_sub, ← hpow, ← hpow]
    unfold TorusData.scale
    have hne := G.data.bareSpacing_pos.ne'
    field_simp
  rw [hquot, ← Real.exp_mul, Real.rpow_def_of_pos hL0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hrate : lg * e ≤ G.data.scaleRatioRate * δ := by
    unfold TorusData.scaleRatioRate
    rw [← hlg, ← hGBdef, div_mul_eq_mul_div, le_div_iff₀ hGB]
    have hmul := mul_le_mul_of_nonneg_left hlay hlg0
    nlinarith
  have hgap : |(a : ℝ) - a'| ≤ 1 + e := by
    have hmax := le_max_left (|(a : ℝ) - (a' : ℝ)| - 1) 0
    linarith
  have ht0 := abs_nonneg t
  have hsgn : ((a : ℝ) - a') * lg * t ≤ |(a : ℝ) - a'| * lg * |t| := by
    have hprod : ((a : ℝ) - a') * t ≤ |(a : ℝ) - a'| * |t| := by
      rw [← abs_mul]
      exact le_abs_self _
    nlinarith
  have hgap' : |(a : ℝ) - a'| * lg * |t| ≤ (1 + e) * lg * |t| := by
    have hmul := mul_le_mul_of_nonneg_right hgap (mul_nonneg hlg0 ht0)
    nlinarith
  have hrate' : lg * e * |t| ≤ G.data.scaleRatioRate * δ * |t| :=
    mul_le_mul_of_nonneg_right hrate ht0
  nlinarith
end ScaleRatio
section Lattice
theorem side_eq_int_mul_scale (D : TorusData) {i : ℕ} (hi : i ≤ D.top) :
    ∃ N : ℤ, D.side = N * D.scale i := by
  obtain ⟨k, -, hS⟩ := D.side_multiple
  refine ⟨2 * k * D.blockNumber * (D.L : ℤ) ^ (D.top - i), ?_⟩
  rw [hS]
  unfold TorusData.scale
  have e : (D.L : ℝ) ^ D.top = (D.L : ℝ) ^ (D.top - i) * (D.L : ℝ) ^ i := by
    rw [← pow_add]
    congr 1
    omega
  rw [e]
  push_cast
  ring
theorem exists_lattice_rep_abs_eq_norm {S h : ℝ} {M : ℤ} (hSM : S = M * h) (j₀ : ℤ) (x : ℝ) :
    ∃ k : ℤ, ((h * (k : ℝ) : ℝ) : AddCircle S) = ((h * (j₀ : ℝ) : ℝ) : AddCircle S) ∧
      |h * (k : ℝ) - x| = ‖((h * (j₀ : ℝ) - x : ℝ) : AddCircle S)‖ := by
  obtain ⟨w, hw, hw'⟩ := exists_coe_eq_abs_eq_norm ((h * (j₀ : ℝ) - x : ℝ) : AddCircle S)
  have hdiff : ((w - (h * (j₀ : ℝ) - x) : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_sub, hw, sub_self]
  obtain ⟨r, hr⟩ := (AddCircle.coe_eq_zero_iff S).mp hdiff
  rw [zsmul_eq_mul] at hr
  have hper : (((r : ℝ) * S : ℝ) : AddCircle S) = 0 :=
    (AddCircle.coe_eq_zero_iff S).mpr ⟨r, by simp⟩
  have hshift : h * ((j₀ + r * M : ℤ) : ℝ) = h * (j₀ : ℝ) + (r : ℝ) * S := by
    rw [hSM]
    push_cast
    ring
  refine ⟨j₀ + r * M, ?_, ?_⟩
  · rw [hshift, AddCircle.coe_add, hper, add_zero]
  · have hval : h * ((j₀ + r * M : ℤ) : ℝ) - x = w := by
      have hrS : (r : ℝ) * S = h * ((r : ℝ) * M) := by
        rw [hSM]
        ring
      push_cast
      linarith
    rw [hval, hw']
theorem sum_prod_le_pow {α : Type*} (A : Finset α) (ι : α → Fin 4 → ℤ)
    (hι : Set.InjOn ι A) (w : Fin 4 → ℤ → ℝ) (hw : ∀ μ m, 0 ≤ w μ m) {C : ℝ}
    (hC : ∀ μ (T : Finset ℤ), ∑ m ∈ T, w μ m ≤ C) :
    ∑ a ∈ A, ∏ μ, w μ (ι a μ) ≤ C ^ 4 := by
  classical
  let proj : Fin 4 → Finset ℤ := fun μ => A.image fun a => ι a μ
  have hbox : A.image ι ⊆ Fintype.piFinset proj := by
    intro k hk
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
    exact Fintype.mem_piFinset.mpr fun μ => Finset.mem_image_of_mem _ hb
  have hre : ∑ a ∈ A, ∏ μ, w μ (ι a μ) = ∑ k ∈ A.image ι, ∏ μ, w μ (k μ) :=
    (Finset.sum_image (f := fun k => ∏ μ, w μ (k μ)) hι).symm
  have hext : ∑ k ∈ A.image ι, ∏ μ, w μ (k μ) ≤ ∑ k ∈ Fintype.piFinset proj, ∏ μ, w μ (k μ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hbox fun _ _ _ =>
      Finset.prod_nonneg fun _ _ => hw _ _
  have hfac : ∑ k ∈ Fintype.piFinset proj, ∏ μ, w μ (k μ) = ∏ μ, ∑ m ∈ proj μ, w μ m :=
    (Finset.prod_univ_sum proj w).symm
  have hbound : ∏ μ, ∑ m ∈ proj μ, w μ m ≤ ∏ _μ : Fin 4, C :=
    Finset.prod_le_prod (fun μ _ => Finset.sum_nonneg fun _ _ => hw _ _)
      fun μ _ => hC μ (proj μ)
  rw [hre]
  refine hext.trans ?_
  rw [hfac]
  refine hbound.trans ?_
  simp
theorem exists_lattice_lift_l1 (D : TorusData) {i : ℕ} (hi : i ≤ D.top) {x y : D.Space}
    (hx : x ∈ D.latticeAt (D.scale i)) {v : Fin 4 → ℝ} (hv : torusProj D.side v = y) :
    ∃ k : Fin 4 → ℤ, torusProj D.side (fun μ => D.scale i * (k μ : ℝ)) = x ∧
      ∑ μ, |D.scale i * (k μ : ℝ) - v μ| = torusL1Norm (x - y) := by
  obtain ⟨N, hN⟩ := side_eq_int_mul_scale D hi
  obtain ⟨k₀, hk₀⟩ := hx
  choose k hk1 hk2 using fun μ => exists_lattice_rep_abs_eq_norm hN (k₀ μ) (v μ)
  refine ⟨k, ?_, ?_⟩
  · rw [hk₀]
    funext μ
    exact hk1 μ
  · rw [torusL1Norm_eq_sum_norm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hk2 μ, hk₀, ← hv]
    congr 1
theorem sum_exp_lattice_le {α : Type*} (D : TorusData) (F : Finset α) (φ : α → D.Space)
    (hφ : Set.InjOn φ F) {i : ℕ} (hi : i ≤ D.top)
    (hlat : ∀ a ∈ F, φ a ∈ D.latticeAt (D.scale i)) (y : D.Space) {β : ℝ}
    (hβ : 0 < β) :
    ∑ a ∈ F, Real.exp (-β * torusL1Norm (φ a - y)) ≤ (2 + 2 / (β * D.scale i)) ^ 4 := by
  classical
  obtain ⟨v, hv⟩ := exists_torusProj_eq y
  have hσ0 : 0 < D.scale i := scale_pos i
  have key : ∀ a ∈ F, ∃ k : Fin 4 → ℤ, torusProj D.side (fun μ => D.scale i * (k μ : ℝ)) = φ a ∧
      ∑ μ, |D.scale i * (k μ : ℝ) - v μ| = torusL1Norm (φ a - y) :=
    fun a ha => exists_lattice_lift_l1 D hi (hlat a ha) hv
  choose! kk hk1 hk2 using key
  have hinj : Set.InjOn kk F := by
    intro a ha b hb hab
    apply hφ ha hb
    rw [← hk1 a ha, ← hk1 b hb, hab]
  have h1 : ∀ a ∈ F, Real.exp (-β * torusL1Norm (φ a - y)) =
      ∏ μ, Real.exp (-β * |D.scale i * (kk a μ : ℝ) - v μ|) := by
    intro a ha
    rw [← hk2 a ha, Finset.mul_sum, Real.exp_sum]
  rw [Finset.sum_congr rfl h1]
  exact sum_prod_le_pow F kk hinj (fun μ m => Real.exp (-β * |D.scale i * (m : ℝ) - v μ|))
    (fun _ _ => (Real.exp_pos _).le) fun μ T => sum_exp_neg_abs_le β _ (v μ) hβ hσ0 T
end Lattice
theorem isClosed_segmentsSupport (D : TorusData) (Γ : List LiftedSegment) :
    IsClosed (segmentsSupport D.side Γ) := by
  unfold segmentsSupport
  refine Set.Finite.isClosed_biUnion (List.finite_toSet Γ) fun s _ => ?_
  exact (isCompact_Icc.image (continuous_pointAt _ s)).isClosed
theorem natSub_le_max_abs (i k : ℕ) : ((k - i - 1 : ℕ) : ℝ) ≤ max (|(i : ℝ) - k| - 1) 0 := by
  rcases Nat.lt_or_ge i k with hik | hik
  · have hcast : ((k - i - 1 : ℕ) : ℝ) = (k : ℝ) - i - 1 := by
      have hk : k = (k - i - 1) + i + 1 := by omega
      have hk' : (k : ℝ) = ((k - i - 1 : ℕ) : ℝ) + i + 1 := by exact_mod_cast hk
      linarith
    rw [hcast]
    refine le_max_of_le_left ?_
    linarith [neg_le_abs ((i : ℝ) - k)]
  · rw [show k - i - 1 = 0 by omega]
    simp
section SumsOverSites
variable (hl : WeightedLengthAndLip)
  (hb : WeightedDistBounds)
  (hs : GivenChainGeneralFacts)
  (G : GivenChain)
include hl hb in
theorem l1_le_weightedLength (n : ℕ) {Γ : List LiftedSegment} (hΓ : IsTreeGraph G.data.side Γ)
    {y y' : G.data.Space} (hy : y ∈ segmentsSupport G.data.side Γ)
    (hy' : y' ∈ segmentsSupport G.data.side Γ)
    (havoid : ∀ z ∈ segmentsSupport G.data.side Γ, z ∉ G.chain.stage (n + 1)) :
    (G.data.scale n)⁻¹ * torusL1Norm (y' - y) ≤ G.chain.weightedLength Γ := by
  have hf := (hl G).2.2.2.1 y
  have h1 := ((hb G).1 _ hf.1).1 Γ y y' hΓ hy hy'
  have h2 := ((hl G).1 Γ).1
  have hξ : 0 < G.data.scale n := scale_pos n
  have hfloor := (hb G).2.1
  have h3 : setLIntegralL1 (segmentsSupport G.data.side Γ)
        (localLip fun z : G.data.Space => torusL1Norm (z - y)) ≤
      ENNReal.ofReal (G.data.scale n) * setLIntegralL1 (segmentsSupport G.data.side Γ)
        (fun x => ENNReal.ofReal (G.chain.weightDensity x)) := by
    unfold setLIntegralL1
    rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.setLIntegral_mono' (isClosed_segmentsSupport G.data Γ).measurableSet
      fun x hx => ?_
    refine (hf.2 x).trans ?_
    rw [← ENNReal.ofReal_mul hξ.le, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h4 := hfloor n x (havoid x hx)
    calc (1 : ℝ) = G.data.scale n * (G.data.scale n)⁻¹ := (mul_inv_cancel₀ hξ.ne').symm
      _ ≤ G.data.scale n * G.chain.weightDensity x := by gcongr
  have h5 : ENNReal.ofReal |torusL1Norm (y - y) - torusL1Norm (y' - y)| ≤
      ENNReal.ofReal (G.data.scale n * G.chain.weightedLength Γ) := by
    refine h1.trans (h3.trans ?_)
    rw [ENNReal.ofReal_mul hξ.le]
    gcongr
  have h0 : torusL1Norm (y - y) = 0 := by
    rw [torusL1Norm_eq_sum_norm]
    simp
  rw [h0, zero_sub, abs_neg] at h5
  have h6 : |torusL1Norm (y' - y)| ≤ G.data.scale n * G.chain.weightedLength Γ :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hξ.le (weightedLength_nonneg _ _))).mp h5
  rw [inv_mul_le_iff₀ hξ]
  exact (le_abs_self _).trans h6
include hl hb hs in
theorem exists_level_le_weightedLength {j j' : ℕ} {y y' : G.data.Space}
    (hy : y ∈ G.chain.layer j) (hy' : y' ∈ G.chain.layer j') {Γ : List LiftedSegment}
    (hΓ : IsTreeGraph G.data.side Γ)
    (hyΓ : y ∈ segmentsSupport G.data.side Γ) (hy'Γ : y' ∈ segmentsSupport G.data.side Γ) :
    ∃ n ∈ Finset.Icc (max j j') G.data.top,
      1 / 2 * ((G.data.scale n)⁻¹ * torusL1Norm (y' - y)) +
          1 / 2 * ((G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) *
            ((n - min j j' - 1 : ℕ) : ℝ)) ≤
        G.chain.weightedLength Γ := by
  classical
  have hjtop := le_top_of_mem_layer _ hy
  have hj'top := le_top_of_mem_layer _ hy'
  let met := (Finset.range (G.data.top + 1)).filter
    fun l => (segmentsSupport G.data.side Γ ∩ G.chain.layer l).Nonempty
  have hjmet : j ∈ met := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), y, hyΓ, hy⟩
  have hj'met : j' ∈ met := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), y', hy'Γ, hy'⟩
  let hi := met.max' ⟨j, hjmet⟩
  have hhi : hi ∈ met := met.max'_mem _
  have hjhi : j ≤ hi := met.le_max' _ hjmet
  have hj'hi : j' ≤ hi := met.le_max' _ hj'met
  obtain ⟨hhir, w, hwΓ, hwL⟩ := Finset.mem_filter.mp hhi
  have hhitop : hi ≤ G.data.top := by
    have hlt := Finset.mem_range.mp hhir
    omega
  have hmiss : ∀ z ∈ segmentsSupport G.data.side Γ, z ∉ G.chain.stage (hi + 1) := by
    intro z hz hzs
    rcases le_or_gt (hi + 1) G.data.top with hle | hlt
    · obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
      obtain ⟨l, hl1, hl2, hl3⟩ := exists_layer_of_mem_stage G.chain r (hi + 1) hr.symm hzs
      have hlmet : l ∈ met := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), z, hz, hl3⟩
      have hlhi := met.le_max' _ hlmet
      omega
    · rw [G.chain.empty_above (hi + 1) hlt] at hzs
      exact hzs
  have hl1 := l1_le_weightedLength hl hb G hi hΓ hyΓ hy'Γ hmiss
  have hlayers : (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) *
      ((hi - min j j' - 1 : ℕ) : ℝ) ≤ G.chain.weightedLength Γ := by
    have hpos := (gap_mul_block_pos (D := G.data)).le
    rcases le_total j j' with hjj | hjj
    · rw [min_eq_left hjj]
      have hd1 := weightedDistance_layers_ge hl hb hs G j hi hy hwL
      have hd2 := weightedDistance_le_weightedLength G.chain hΓ hyΓ hwΓ
      have hd3 := mul_le_mul_of_nonneg_left (natSub_le_max_abs j hi) hpos
      linarith
    · rw [min_eq_right hjj]
      have hd1 := weightedDistance_layers_ge hl hb hs G j' hi hy' hwL
      have hd2 := weightedDistance_le_weightedLength G.chain hΓ hy'Γ hwΓ
      have hd3 := mul_le_mul_of_nonneg_left (natSub_le_max_abs j' hi) hpos
      linarith
  exact ⟨hi, Finset.mem_Icc.mpr ⟨max_le hjhi hj'hi, hhitop⟩, by linarith⟩
include hl hb hs in
theorem exists_level_le_weightedDistance {j j' : ℕ} {y y' : G.data.Space}
    (hy : y ∈ G.chain.layer j) (hy' : y' ∈ G.chain.layer j') :
    ∃ n ∈ Finset.Icc (max j j') G.data.top,
      1 / 2 * ((G.data.scale n)⁻¹ * torusL1Norm (y' - y)) +
          1 / 2 * ((G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) *
            ((n - min j j' - 1 : ℕ) : ℝ)) ≤
        G.chain.weightedDistance y y' := by
  have hne : (Finset.Icc (max j j') G.data.top).Nonempty :=
    ⟨max j j', Finset.mem_Icc.mpr ⟨le_rfl, max_le (le_top_of_mem_layer _ hy)
      (le_top_of_mem_layer _ hy')⟩⟩
  obtain ⟨n₀, hn₀, hmin⟩ := Finset.exists_min_image _ (fun n =>
    1 / 2 * ((G.data.scale n)⁻¹ * torusL1Norm (y' - y)) +
      1 / 2 * ((G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) *
        ((n - min j j' - 1 : ℕ) : ℝ))) hne
  refine ⟨n₀, hn₀, le_weightedDistance _ fun Γ h1 h2 h3 => ?_⟩
  obtain ⟨n, hn, hle⟩ := exists_level_le_weightedLength hl hb hs G hy hy' h1 h2 h3
  exact (hmin n hn).trans hle
include hl hb hs in
theorem sum_exp_weightedDistance_le {κ : ℝ} (hκ : 0 < κ)
    (hfloor : latticeSumRadius 4 G.data.L κ ≤
      (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ))
    (o : ↥G.chain.allSites) (A : Finset ↥G.chain.allSites) :
    ∑ o' ∈ A, Real.exp (-κ * G.chain.weightedDistance o o') ≤
      latticeSumConst 4 G.data.L κ := by
  classical
  have hL1 : (1 : ℝ) ≤ G.data.L := one_le_L
  set Rg := (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) with hRg
  set ν : ℝ := 1 / 2 * κ * Rg with hν
  have hνlog : 4 * Real.log (G.data.L : ℝ) + 1 ≤ ν := by
    unfold latticeSumRadius at hfloor
    rw [div_le_iff₀ hκ] at hfloor
    push_cast at hfloor
    rw [hν]
    linarith
  let lev : ↥G.chain.allSites → ℕ := fun s => siteLevel G.chain s.1
  have hlev : ∀ s, s.1 ∈ G.chain.layerSites (lev s) ∧ lev s ≤ G.data.top :=
    fun s => ⟨(siteLevel_spec G.chain s.2).1, (siteLevel_spec G.chain s.2).2.1⟩
  let j₀ := lev o
  let rate : ℕ → ℝ := fun l => 1 / 2 * κ * (G.data.scale l)⁻¹
  have hrate : ∀ l, 0 < rate l := fun l => by
    have hsc := scale_pos (D := G.data) l
    simp only [rate]
    positivity
  let Ex : ℕ → ↥G.chain.allSites → ℝ := fun l s =>
    Real.exp (-(rate l) * torusL1Norm (s.1 - o.1))
  let Gap : ℕ → ℕ → ℝ := fun l i => Real.exp (-ν * ((l - i - 1 : ℕ) : ℝ))
  let Tot : ↥G.chain.allSites → ℝ := fun s =>
    ∑ l ∈ Finset.Icc (max j₀ (lev s)) G.data.top, Ex l s * Gap l (min j₀ (lev s))
  have hpt : ∀ s : ↥G.chain.allSites,
      Real.exp (-κ * G.chain.weightedDistance o s) ≤ Tot s := by
    intro s
    obtain ⟨l, hl', hlen⟩ := exists_level_le_weightedDistance hl hb hs G (hlev o).1.2 (hlev s).1.2
    rw [← hRg] at hlen
    refine le_trans ?_ (Finset.single_le_sum (f := fun l => Ex l s * Gap l (min j₀ (lev s)))
      (fun _ _ => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le) hl')
    simp only [Ex, Gap]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hlen hκ.le
    simp only [rate]
    rw [hν]
    linarith
  set Cst : ℝ := (2 + 4 / κ) ^ 4 with hCst
  have hCst0 : 0 ≤ Cst := by positivity
  let Wt : ℕ → ℝ := fun p => Real.exp (-((p - 1 : ℕ) : ℝ))
  have hWt : ∀ p, 0 ≤ Wt p := fun p => (Real.exp_pos _).le
  have hlevel : ∀ r ∈ Finset.range (G.data.top + 1),
      ∑ s ∈ A.filter (fun s => lev s = r), Tot s ≤
        ∑ l ∈ Finset.Icc (max j₀ r) G.data.top,
          Cst * (G.data.L : ℝ) ^ 4 * Wt (l - min j₀ r) := by
    intro r hr
    have hrtop : r ≤ G.data.top := by
      have hlt := Finset.mem_range.mp hr
      omega
    have hsplit : ∑ s ∈ A.filter (fun s => lev s = r), Tot s =
        ∑ l ∈ Finset.Icc (max j₀ r) G.data.top,
          (∑ s ∈ A.filter (fun s => lev s = r), Ex l s) * Gap l (min j₀ r) := by
      have hrow : ∀ s ∈ A.filter (fun s => lev s = r), Tot s =
          ∑ l ∈ Finset.Icc (max j₀ r) G.data.top, Ex l s * Gap l (min j₀ r) := by
        intro s hs'
        have hsr := (Finset.mem_filter.mp hs').2
        simp only [Tot]
        rw [hsr]
      rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => (Finset.sum_mul _ _ _).symm
    rw [hsplit]
    refine Finset.sum_le_sum fun l hl'' => ?_
    have hl3 := Finset.mem_Icc.mp hl''
    have hrl : r ≤ l := (le_max_right j₀ r).trans hl3.1
    have hlat := sum_exp_lattice_le G.data (A.filter (fun s => lev s = r)) Subtype.val
      Subtype.val_injective.injOn hrtop
      (fun s hs' => by
        have hsr := (Finset.mem_filter.mp hs').2
        have hsite := (hlev s).1.1
        rw [hsr] at hsite
        exact hsite) o.1 (hrate l)
    set Pw : ℝ := (G.data.L : ℝ) ^ (l - r) with hPw
    have hPw1 : 1 ≤ Pw := one_le_pow₀ hL1
    have hratio : 2 / (rate l * G.data.scale r) = 4 / κ * Pw := by
      have hsc : G.data.scale l = Pw * G.data.scale r := by
        unfold TorusData.scale
        rw [hPw, ← mul_assoc, ← pow_add]
        congr 2
        omega
      have hne := (scale_pos (D := G.data) r).ne'
      have hPne : Pw ≠ 0 := by positivity
      simp only [rate]
      rw [hsc]
      field_simp
      ring
    have hfour : (2 + 2 / (rate l * G.data.scale r)) ^ 4 ≤
        Cst * (G.data.L : ℝ) ^ (4 * (l - r)) := by
      rw [hratio, hCst, mul_comm 4 (l - r), pow_mul, ← hPw, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have hk4 : 0 ≤ 4 / κ := by positivity
      nlinarith
    set p₀ := l - min j₀ r with hp₀
    have hmono : (G.data.L : ℝ) ^ (4 * (l - r)) ≤ (G.data.L : ℝ) ^ (4 * p₀) :=
      pow_le_pow_right₀ hL1 (by omega)
    have hdecay := pow_mul_exp_neg_le (G.data.L : ℝ) ν hL1 hνlog p₀
    have hGap : 0 ≤ Gap l (min j₀ r) := (Real.exp_pos _).le
    calc (∑ s ∈ A.filter (fun s => lev s = r), Ex l s) * Gap l (min j₀ r)
        ≤ (Cst * (G.data.L : ℝ) ^ (4 * p₀)) * Gap l (min j₀ r) := by
          apply mul_le_mul_of_nonneg_right _ hGap
          exact hlat.trans (hfour.trans (mul_le_mul_of_nonneg_left hmono hCst0))
      _ = Cst * ((G.data.L : ℝ) ^ (4 * p₀) * Real.exp (-ν * ((p₀ - 1 : ℕ) : ℝ))) := by
          simp only [Gap]
          rw [mul_assoc]
      _ ≤ Cst * ((G.data.L : ℝ) ^ 4 * Wt p₀) := mul_le_mul_of_nonneg_left hdecay hCst0
      _ = Cst * (G.data.L : ℝ) ^ 4 * Wt p₀ := by ring
  have hCL : 0 ≤ Cst * (G.data.L : ℝ) ^ 4 := by positivity
  have hfib : ∑ s ∈ A, Tot s =
      ∑ r ∈ Finset.range (G.data.top + 1), ∑ s ∈ A.filter (fun s => lev s = r), Tot s :=
    (Finset.sum_fiberwise_of_maps_to
      (fun s _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hlev s).2)) _).symm
  have hpull : ∑ r ∈ Finset.range (G.data.top + 1), ∑ l ∈ Finset.Icc (max j₀ r) G.data.top,
        Cst * (G.data.L : ℝ) ^ 4 * Wt (l - min j₀ r) =
      Cst * (G.data.L : ℝ) ^ 4 * ∑ r ∈ Finset.range (G.data.top + 1),
        ∑ l ∈ Finset.Icc (max j₀ r) G.data.top, Wt (l - min j₀ r) := by
    simp only [Finset.mul_sum]
  have hend : Cst * (G.data.L : ℝ) ^ 4 * 8 = latticeSumConst 4 G.data.L κ := by
    unfold latticeSumConst
    rw [hCst]
    ring
  refine (Finset.sum_le_sum fun s _ => hpt s).trans ?_
  rw [hfib]
  refine (Finset.sum_le_sum hlevel).trans ?_
  rw [hpull, ← hend]
  refine mul_le_mul_of_nonneg_left ?_ hCL
  exact (sum_sum_Icc_le j₀ G.data.top Wt hWt).trans (sum_linear_mul_exp_le_eight _)
end SumsOverSites
theorem finsum_le_of_forall_finset {α : Type*} (g : α → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ F : Finset α, ∑ a ∈ F, g a ≤ M) : ∑ᶠ a, g a ≤ M := by
  rcases (Function.support g).finite_or_infinite with hfin | hinf
  · rw [finsum_eq_sum _ hfin]
    exact hF _
  · rw [finsum_of_infinite_support hinf]
    exact hM
end SiteSumProof
theorem chainSiteSumBounds_holds
    (hgen : GivenChainGeneralFacts)
    (hlen : WeightedLengthAndLip)
    (hdist : WeightedDistBounds) :
    ChainSiteSumBounds := by
  intro Dt Bc
  have hL : (1 : ℝ) ≤ Dt.L := SiteSumProof.one_le_L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro κ₁ hκ₁ κ₂ hκ₂ hle
    have hκ₁' : (0 : ℝ) < κ₁ := hκ₁
    have hκ₂' : (0 : ℝ) < κ₂ := hκ₂
    unfold latticeSumConst
    gcongr
  · intro κ₁ hκ₁ κ₂ hκ₂ hle
    have hκ₁' : (0 : ℝ) < κ₁ := hκ₁
    unfold latticeSumRadius
    exact div_le_div_of_nonneg_left (by positivity) hκ₁' hle
  · intro p q u hu v hv
    exact SiteSumProof.weightedDistance_layers_ge hlen hdist hgen
      ⟨Dt, Bc, SiteSumProof.stage_zero_nonempty_of_mem_layer Bc hu⟩ p q hu hv
  · intro t u hu v hv
    exact SiteSumProof.siteScale_div_rpow_le hlen hdist hgen
      ⟨Dt, Bc, SiteSumProof.stage_zero_nonempty_of_mem_layer Bc
        (SiteSumProof.siteLevel_spec Bc hu).1.2⟩ t hu hv
  · intro κ hκ hfloor
    have hK : 0 ≤ latticeSumConst 4 Dt.L κ := by
      unfold latticeSumConst
      positivity
    have hbound : ∀ (u : ↥Bc.allSites) (A : Finset ↥Bc.allSites),
        ∑ v ∈ A, Real.exp (-κ * Bc.weightedDistance u v) ≤ latticeSumConst 4 Dt.L κ :=
      fun u A => SiteSumProof.sum_exp_weightedDistance_le hlen hdist hgen
        ⟨Dt, Bc, SiteSumProof.stage_zero_nonempty_of_mem_layer Bc
          (SiteSumProof.siteLevel_spec Bc u.2).1.2⟩ hκ hfloor u A
    refine ⟨fun u => SiteSumProof.finsum_le_of_forall_finset _ hK (hbound u), fun u v => ?_⟩
    have hexp : 0 < Real.exp (-κ * Bc.weightedDistance u v) := Real.exp_pos _
    refine SiteSumProof.finsum_le_of_forall_finset _ (mul_nonneg hK hexp.le) fun A => ?_
    have htri := (hgen ⟨Dt, Bc, SiteSumProof.stage_zero_nonempty_of_mem_layer Bc
      (SiteSumProof.siteLevel_spec Bc u.2).1.2⟩).2.2.2.2.2
    have hterm : ∀ w ∈ A, Real.exp (-(2 * κ) * Bc.weightedDistance u w) *
          Real.exp (-(2 * κ) * Bc.weightedDistance w v) ≤
        Real.exp (-κ * Bc.weightedDistance u v) * Real.exp (-κ * Bc.weightedDistance u w) := by
      intro w _
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have htw : Bc.weightedDistance u v ≤
          Bc.weightedDistance u w + Bc.weightedDistance w v := htri u w v
      have hwv := SiteSumProof.weightedDistance_nonneg Bc w.1 v.1
      nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, mul_comm (latticeSumConst 4 Dt.L κ)]
    exact mul_le_mul_of_nonneg_left (hbound u A) hexp.le
end YangMills.Construction.Weighted
