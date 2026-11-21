import YangMills.Construction.Continuum.ConsistencyOfTheLocalFunctionalsProof
import YangMills.Construction.Continuum.ConstantOfTheExtensionIsOfFactorialTypeProof
import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.Continuum.FirstFactsOnSmoothTestFunctionsAndTuplesProof
import YangMills.Construction.Continuum.OneClassOfTuplesAndOneNotionOfMultilinearityProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Matrix
noncomputable section
namespace YangMills.Construction.ConfigSpace
open SmoothMaps TestFunctions Bumps ShellPieces
namespace LocalPairingBounds
open LocalPairingProps
variable {n : ℕ}
theorem mem_closedBox_iff {a y : Fin 4 → ℝ} {s : ℝ} :
    y ∈ ShellPieces.closedBox a s ↔ ∀ c, |y c - a c| ≤ s / 2 := by apply _root_.YangMills.SharedProofs.p5872 <;> assumption
theorem closedBox_eq_pi (a : Fin 4 → ℝ) (s : ℝ) :
    ShellPieces.closedBox a s = Set.pi univ (fun c => Icc (a c - s / 2) (a c + s / 2)) := by
  ext y
  rw [mem_closedBox_iff]
  simp only [Set.mem_pi, mem_univ, forall_true_left, mem_Icc, abs_le]
  constructor
  · intro h c
    have := h c
    constructor <;> linarith [this.1, this.2]
  · intro h c
    have := h c
    constructor <;> linarith [this.1, this.2]
theorem isCompact_closedBox (a : Fin 4 → ℝ) (s : ℝ) : IsCompact (ShellPieces.closedBox a s) := by
  rw [closedBox_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc
theorem cylinderSet_eq_pi (S : Fin n → Set (Fin 4 → ℝ)) : cylinderSet S = Set.pi univ S := by apply _root_.YangMills.Construction.ConfigSpace.TupleFacts.cylinderSet_eq_univ_pi <;> assumption
theorem isCompact_cylinderSet {S : Fin n → Set (Fin 4 → ℝ)} (h : ∀ i, IsCompact (S i)) :
    IsCompact (cylinderSet S) := by
  rw [cylinderSet_eq_pi]
  exact isCompact_univ_pi h
theorem tsupport_subset_of_vanishing {X E : Type*} [TopologicalSpace X] [Zero E] {f : X → E}
    {K : Set X} (hK : IsClosed K) (h : ∀ x, x ∉ K → f x = 0) : tsupport f ⊆ K := by
  refine closure_minimal (fun x hx => ?_) hK
  by_contra hxK
  exact hx (h x hxK)
section Boxes
variable (Q : PointSystem n)
theorem isCompact_outerBox (i : Fin n) : IsCompact (Q.outerBox i) := isCompact_closedBox _ _
theorem isCompact_midBox (i : Fin n) : IsCompact (Q.midBox i) := isCompact_closedBox _ _
theorem midBox_subset_outerBox (i : Fin n) : Q.midBox i ⊆ Q.outerBox i := by
  intro y hy
  unfold PointSystem.midBox at hy
  unfold PointSystem.outerBox
  rw [mem_closedBox_iff] at hy ⊢
  intro c
  have := hy c
  have := Q.scale_pos
  linarith
theorem outerBox_subset_ball (i : Fin n) : Q.outerBox i ⊆ closedBallR4 (Q.base i) 1 := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.outerBox_subset_closedBallR4 <;> assumption
end Boxes
theorem setDistR4_anti {A A' B B' : Set (Fin 4 → ℝ)} (hA : A ⊆ A') (hB : B ⊆ B') :
    setDistR4 A' B' ≤ setDistR4 A B :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb => iInf₂_le_of_le a (hA ha) (iInf₂_le b (hB hb))
theorem disjoint_of_setDistR4_pos {A B : Set (Fin 4 → ℝ)} (h : 0 < setDistR4 A B) :
    Disjoint A B := by apply _root_.YangMills.Construction.TestSpaces.UnifiedSeparatedTuples.disjoint_of_setDistR4_pos <;> assumption
theorem boxGap_le (Q : PointSystem n) {i i' : Fin n} (h : i ≠ i') :
    Q.boxGap ≤ setDistR4 (Q.outerBox i) (Q.outerBox i') :=
  iInf_le_of_le i (iInf_le_of_le i' (iInf_le _ h))
theorem finite_multiIndex_order_le (ν : ℕ) : Finite {α : MultiIndex n // α.order ≤ ν} := by apply _root_.YangMills.Construction.ConfigSpace.FourierDecay.finite_order_le <;> assumption
theorem le_scaledSupNorm {ν : ℕ} {m : ℝ} (Ψ : Config n → ℂ) (α : MultiIndex n) (h : α.order ≤ ν) :
    m ^ α.order * uniformNorm (iteratedPartial α Ψ) ≤ scaledSupNorm ν m Ψ := by
  have := finite_multiIndex_order_le (n := n) ν
  exact le_ciSup (f := fun α : {α : MultiIndex n // α.order ≤ ν} =>
    m ^ α.1.order * uniformNorm (iteratedPartial α.1 Ψ)) (Set.finite_range _).bddAbove ⟨α, h⟩
theorem uniformNorm_nonneg {X : Type*} (f : X → ℂ) : 0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem scaledSupNorm_nonneg (ν : ℕ) {m : ℝ} (hm : 0 ≤ m) (Ψ : Config n → ℂ) :
    0 ≤ scaledSupNorm ν m Ψ :=
  Real.iSup_nonneg fun _ => mul_nonneg (pow_nonneg hm _) (uniformNorm_nonneg _)
section Linear
variable {Q : PointSystem n} {T : smoothRealTupleSet n → ℝ} {c : ℝ} {a : ℕ} {G : ℝ}
theorem isClosed_cylinder_midBox (Q : PointSystem n) : IsClosed (cylinderSet Q.midBox) :=
  (isCompact_cylinderSet (isCompact_midBox Q)).isClosed
theorem eq_zero_of_not_mem_cylinder {Φ : Config n → ℂ} (hΦ : Φ ∈ Q.supportedClass) {x : Config n}
    (hx : x ∉ cylinderSet Q.midBox) : Φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hΦ.2 h)
theorem add_mem_supportedClass {Φ Ψ : Config n → ℂ} (hΦ : Φ ∈ Q.supportedClass)
    (hΨ : Ψ ∈ Q.supportedClass) : Φ + Ψ ∈ Q.supportedClass := by
  refine ⟨hΦ.1.add hΨ.1, tsupport_subset_of_vanishing (isClosed_cylinder_midBox Q) fun x hx => ?_⟩
  simp [eq_zero_of_not_mem_cylinder hΦ hx, eq_zero_of_not_mem_cylinder hΨ hx]
theorem smul_mem_supportedClass (lam : ℂ) {Φ : Config n → ℂ} (hΦ : Φ ∈ Q.supportedClass) :
    lam • Φ ∈ Q.supportedClass := by
  refine ⟨contDiff_const.smul hΦ.1,
    tsupport_subset_of_vanishing (isClosed_cylinder_midBox Q) fun x hx => ?_⟩
  simp [eq_zero_of_not_mem_cylinder hΦ hx]
theorem zero_mem_supportedClass : (0 : Config n → ℂ) ∈ Q.supportedClass :=
  ⟨contDiff_const, tsupport_subset_of_vanishing (isClosed_cylinder_midBox Q) fun _ _ => rfl⟩
theorem supportedClass_isSubmodule (Q : PointSystem n) : SupportedClassIsSubmodule Q :=
  ⟨{ carrier := Q.supportedClass
     add_mem' := add_mem_supportedClass
     zero_mem' := zero_mem_supportedClass
     smul_mem' := smul_mem_supportedClass }, rfl⟩
theorem continuous_configDot_sub (ξ : Config n) (y : Config n) :
    Continuous fun x : Config n => configDot ξ (x - y) := by
  unfold configDot dotProduct
  fun_prop
theorem integrableOn_fourierIntegrand {Φ : Config n → ℂ} (hΦ : Φ ∈ Q.supportedClass)
    (ξ : Config n) :
    IntegrableOn
      (fun x => Φ x * Complex.exp (-(Complex.I * (configDot ξ (x - Q.base) : ℝ))))
      (cylinderSet Q.outerBox) := by
  apply ContinuousOn.integrableOn_compact (isCompact_cylinderSet (isCompact_outerBox Q))
  apply Continuous.continuousOn
  have h := continuous_configDot_sub ξ Q.base
  have hΦc : Continuous Φ := hΦ.1.continuous
  fun_prop
theorem fourierCoeff_add {Φ Ψ : Config n → ℂ} (hΦ : Φ ∈ Q.supportedClass)
    (hΨ : Ψ ∈ Q.supportedClass) (ξ : Config n) :
    Q.fourierCoeff (Φ + Ψ) ξ = Q.fourierCoeff Φ ξ + Q.fourierCoeff Ψ ξ := by
  unfold PointSystem.fourierCoeff
  rw [← mul_add, ← integral_add (integrableOn_fourierIntegrand hΦ ξ)
    (integrableOn_fourierIntegrand hΨ ξ)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [add_mul]
theorem fourierCoeff_smul (lam : ℂ) (Φ : Config n → ℂ) (ξ : Config n) :
    Q.fourierCoeff (lam • Φ) ξ = lam * Q.fourierCoeff Φ ξ := by
  unfold PointSystem.fourierCoeff
  have h : ∫ x in cylinderSet Q.outerBox, (lam • Φ) x *
        Complex.exp (-(Complex.I * (configDot ξ (x - Q.base) : ℝ))) =
      lam * ∫ x in cylinderSet Q.outerBox, Φ x *
        Complex.exp (-(Complex.I * (configDot ξ (x - Q.base) : ℝ))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [mul_assoc]
  rw [h]
  ring
theorem summable_pairingTerms {Φ : Config n → ℂ} (h : Q.CoeffCostSummable Φ c a G T) :
    Summable fun ξ : Q.freqLattice =>
      Q.fourierCoeff Φ ξ * complexifyAtModes T Q ξ := by
  refine Summable.of_norm (h.1.congr fun ξ => ?_)
  rw [norm_mul]
theorem localPairing_add (hcost : ∀ Φ ∈ Q.supportedClass, Q.CoeffCostSummable Φ c a G T)
    {Φ Ψ : Config n → ℂ} (hΦ : Φ ∈ Q.supportedClass) (hΨ : Ψ ∈ Q.supportedClass) :
    localPairing T Q (Φ + Ψ) = localPairing T Q Φ + localPairing T Q Ψ := by
  unfold localPairing
  rw [← (summable_pairingTerms (hcost Φ hΦ)).tsum_add (summable_pairingTerms (hcost Ψ hΨ))]
  refine tsum_congr fun ξ => ?_
  rw [fourierCoeff_add hΦ hΨ, add_mul]
theorem localPairing_smul (lam : ℂ) (Φ : Config n → ℂ) :
    localPairing T Q (lam • Φ) = lam * localPairing T Q Φ := by
  unfold localPairing
  rw [← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  rw [fourierCoeff_smul, mul_assoc]
theorem pairing_constant_le (hn : 1 ≤ n) {C : ℝ} (hC : 0 ≤ C) :
    (2 : ℝ) ^ (5 * n + 1) * (1 + 8 * (n : ℝ)) * (2 * C) ^ n ≤ (1152 * C) ^ n := by
  have h1 : (2 : ℝ) ^ (5 * n + 1) ≤ 64 ^ n := by
    have e1 : (2 : ℝ) ^ (5 * n + 1) = 2 * 32 ^ n := by
      rw [pow_succ, pow_mul]
      norm_num
      ring
    have e2 : (64 : ℝ) ^ n = 2 ^ n * 32 ^ n := by
      rw [← mul_pow]
      norm_num
    rw [e1, e2]
    have h2 : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have h2 : 1 + 8 * (n : ℝ) ≤ 9 ^ n := by
    have := one_add_mul_le_pow (a := (8 : ℝ)) (by norm_num) n
    norm_num at this
    linarith
  have e : (1152 * C) ^ n = 64 ^ n * 9 ^ n * (2 * C) ^ n := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    ring
  rw [e]
  gcongr
theorem two_le_modeConst (hb : GevreyBumpBounds) : 2 ≤ modeConst := by
  obtain ⟨-, -, -, -, ⟨-, -, h01, h1, -, -⟩, -⟩ := hb
  have hc : cubeBump 0 = 1 := h1 0 fun c => by norm_num
  have hbdd : BddAbove (Set.range fun y : Fin 4 → ℝ => ‖(cubeBump y : ℂ)‖) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, rfl⟩
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (h01 y).1]
    exact (h01 y).2
  have h3 : ‖((cubeBump 0 : ℝ) : ℂ)‖ = 1 := by
    rw [hc]
    simp
  have h2 : (1 : ℝ) ≤ uniformNorm fun y => (cubeBump y : ℂ) :=
    h3.symm.le.trans (le_ciSup hbdd 0)
  unfold modeConst
  exact le_max_of_le_left (by linarith)
theorem one_le_localConst (hb : GevreyBumpBounds) : 1 ≤ localConst := by apply _root_.YangMills.Construction.ExtensionConstants.one_le_localConst <;> assumption
theorem norm_localPairing_le (hb : GevreyBumpBounds) (hn : 1 ≤ n) (hG : 0 ≤ G)
    {Φ : Config n → ℂ} (hΦ : Q.CoeffCostSummable Φ c a G T) :
    ‖localPairing T Q Φ‖ ≤
      localConst ^ n * max 1 c ^ n * G * max 1 (Q.boxGap.toReal ^ (-(a : ℤ))) *
        Q.scale ^ (-(n : ℤ)) * scaledSupNorm (5 * n + 1) Q.scale Φ := by
  have hC : 0 ≤ modeConst := by linarith [two_le_modeConst hb]
  have hs := Q.scale_pos
  have hR : 0 ≤ max 1 c ^ n * G * max 1 (Q.boxGap.toReal ^ (-(a : ℤ))) *
      Q.scale ^ (-(n : ℤ)) * scaledSupNorm (5 * n + 1) Q.scale Φ := by
    have h1 : 0 ≤ max 1 c := le_max_of_le_left zero_le_one
    have h2 : 0 ≤ max 1 (Q.boxGap.toReal ^ (-(a : ℤ))) := le_max_of_le_left zero_le_one
    have h3 : 0 ≤ Q.scale ^ (-(n : ℤ)) := zpow_nonneg hs.le _
    have h4 := scaledSupNorm_nonneg (5 * n + 1) hs.le Φ
    positivity
  calc ‖localPairing T Q Φ‖
      ≤ ∑' ξ : Q.freqLattice, ‖Q.fourierCoeff Φ ξ * complexifyAtModes T Q ξ‖ :=
        norm_tsum_le_tsum_norm ((summable_pairingTerms hΦ).norm)
    _ = ∑' ξ : Q.freqLattice, ‖Q.fourierCoeff Φ ξ‖ * ‖complexifyAtModes T Q ξ‖ :=
        tsum_congr fun ξ => norm_mul _ _
    _ ≤ _ := hΦ.2
    _ = (2 ^ (5 * n + 1) * (1 + 8 * (n : ℝ)) * (2 * modeConst) ^ n) *
          (max 1 c ^ n * G * max 1 (Q.boxGap.toReal ^ (-(a : ℤ))) *
            Q.scale ^ (-(n : ℤ)) * scaledSupNorm (5 * n + 1) Q.scale Φ) := by
        unfold PointSystem.sepWeight
        ring
    _ ≤ (1152 * modeConst) ^ n *
          (max 1 c ^ n * G * max 1 (Q.boxGap.toReal ^ (-(a : ℤ))) *
            Q.scale ^ (-(n : ℤ)) * scaledSupNorm (5 * n + 1) Q.scale Φ) :=
        mul_le_mul_of_nonneg_right (pairing_constant_le hn hC) hR
    _ = _ := by
        unfold localConst
        ring
theorem localPairing_continuous (hb : GevreyBumpBounds) (hn : 1 ≤ n)
    (hG : 0 ≤ G) (hcost : ∀ Φ ∈ Q.supportedClass, Q.CoeffCostSummable Φ c a G T) :
    PairingContinuousInScaledNorm T Q := by
  intro Φ Φ' hΦ hΦ' hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set K : ℝ := localConst ^ n * max 1 c ^ n * G *
    max 1 (Q.boxGap.toReal ^ (-(a : ℤ))) * Q.scale ^ (-(n : ℤ)) with hK
  have hlim' : Tendsto (fun t => K * scaledSupNorm (5 * n + 1) Q.scale (Φ' t - Φ)) atTop (𝓝 0) := by
    simpa using hlim.const_mul K
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim'
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hneg : (-1 : ℂ) • Φ ∈ Q.supportedClass := smul_mem_supportedClass _ hΦ
  have hsub : Φ' t - Φ = Φ' t + (-1 : ℂ) • Φ := by
    simp [sub_eq_add_neg]
  have hmem : Φ' t - Φ ∈ Q.supportedClass := by
    rw [hsub]
    exact add_mem_supportedClass (hΦ' t ht) hneg
  have heq : localPairing T Q (Φ' t) - localPairing T Q Φ =
      localPairing T Q (Φ' t - Φ) := by
    rw [hsub, localPairing_add hcost (hΦ' t ht) hneg, localPairing_smul]
    ring
  rw [heq]
  exact norm_localPairing_le hb hn hG (hcost _ hmem)
end Linear
theorem tendsto_multilinear_of_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (M : MultilinearMap ℂ E ℂ)
    (p : ∀ i, E i → ℝ) (B : ℝ) (hB : ∀ w, ‖M w‖ ≤ B * ∏ i, p i (w i)) {l : Filter α}
    (u : α → ∀ i, E i) (v : ∀ i, E i) (hu : ∀ i, Tendsto (fun t => p i (u t i - v i)) l (𝓝 0)) :
    Tendsto (fun t => M (u t)) l (𝓝 (M v)) := by
  have hsplit : ∀ t, M (u t) = ∑ s : Finset ι, M (s.piecewise v (u t - v)) := by
    intro t
    rw [← M.map_add_univ]
    congr 1
    simp
  have hterm : ∀ s : Finset ι, Tendsto (fun t => M (s.piecewise v (u t - v))) l
      (𝓝 (if s = Finset.univ then M v else 0)) := by
    intro s
    by_cases hs : s = Finset.univ
    · subst hs
      simpa using tendsto_const_nhds
    · rw [if_neg hs]
      obtain ⟨i₀, hi₀⟩ : ∃ i, i ∉ s := by
        by_contra h
        push Not at h
        exact hs (Finset.eq_univ_iff_forall.mpr h)
      have hfac : ∀ i ∈ (Finset.univ : Finset ι),
          Tendsto (fun t => p i (s.piecewise v (u t - v) i)) l
            (𝓝 (if i ∈ s then p i (v i) else 0)) := by
        intro i _
        by_cases hi : i ∈ s
        · simpa [hi] using tendsto_const_nhds
        · simpa [hi] using hu i
      have hprod := tendsto_finsetProd _ hfac
      have hzero : ∏ i, (if i ∈ s then p i (v i) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])
      rw [hzero] at hprod
      have hbound := hprod.const_mul B
      rw [mul_zero] at hbound
      exact squeeze_zero_norm (fun t => hB _) hbound
  have hsum := tendsto_finsetSum _ fun s (_ : s ∈ Finset.univ) => hterm s
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  exact hsum.congr fun t => (hsplit t).symm
section Boxes
variable (Q : PointSystem n)
theorem isClosed_outerBox (i : Fin n) : IsClosed (Q.outerBox i) :=
  (isCompact_outerBox Q i).isClosed
def boxFunctions (i : Fin n) : Submodule ℂ ((Fin 4 → ℝ) → ℂ) where
  carrier := {ψ | ContDiff ℝ ∞ ψ ∧ tsupport ψ ⊆ Q.outerBox i}
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, tsupport_subset_of_vanishing (isClosed_outerBox Q i) fun x hx => ?_⟩
    have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hf.2 h)
    have h2 : g x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hg.2 h)
    simp [h1, h2]
  zero_mem' := ⟨contDiff_const, tsupport_subset_of_vanishing (isClosed_outerBox Q i) fun _ _ => rfl⟩
  smul_mem' := by
    intro lam f hf
    refine ⟨contDiff_const.smul hf.1, tsupport_subset_of_vanishing (isClosed_outerBox Q i)
      fun x hx => ?_⟩
    have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hf.2 h)
    simp [h1]
theorem disjoint_outerBoxes (hsep : Q.IsSeparated) {i i' : Fin n} (h : i ≠ i') :
    Disjoint (Q.outerBox i) (Q.outerBox i') :=
  disjoint_of_setDistR4_pos (lt_of_lt_of_le hsep (boxGap_le Q h))
theorem hasCompactSupport_of_mem_boxFunctions {i : Fin n} {ψ : (Fin 4 → ℝ) → ℂ}
    (h : ψ ∈ boxFunctions Q i) : HasCompactSupport ψ :=
  (isCompact_outerBox Q i).of_isClosed_subset (isClosed_tsupport _) h.2
theorem boxTuple_mem (hsep : Q.IsSeparated) (ψ : ∀ i, boxFunctions Q i) :
    (fun i => (ψ i).1) ∈ smoothComplexTupleSet n :=
  ⟨fun i => ⟨(ψ i).2.1, hasCompactSupport_of_mem_boxFunctions Q (ψ i).2⟩, fun i i' h =>
    (disjoint_outerBoxes Q hsep h).mono (ψ i).2.2 (ψ i').2.2⟩
def boxForm (T : smoothRealTupleSet n → ℝ) (hsep : Q.IsSeparated)
    (hm : IsComplexMultilinearSmooth (complexify T)) :
    MultilinearMap ℂ (fun i => boxFunctions Q i) ℂ where
  toFun ψ := complexify T ⟨fun i => (ψ i).1, boxTuple_mem Q hsep ψ⟩
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    refine (hm i ⟨_, boxTuple_mem Q hsep (Function.update m i x)⟩
      ⟨_, boxTuple_mem Q hsep (Function.update m i y)⟩ (fun k hk => ?_)).1
      ⟨_, boxTuple_mem Q hsep (Function.update m i (x + y))⟩ ?_
    · simp [Function.update_of_ne hk]
    · funext k
      by_cases hk : k = i
      · subst hk
        simp
      · simp [Function.update_of_ne hk]
  map_update_smul' := by
    intro inst m i lam x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    refine (hm i ⟨_, boxTuple_mem Q hsep (Function.update m i x)⟩
      ⟨_, boxTuple_mem Q hsep (Function.update m i x)⟩ (fun _ _ => rfl)).2 lam
      ⟨_, boxTuple_mem Q hsep (Function.update m i (lam • x))⟩ ?_
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Function.update_of_ne hk]
end Boxes
def gradMaxNorm (c : ℝ) (ψ : (Fin 4 → ℝ) → ℂ) : ℝ := max (uniformNorm ψ) (c * gradSupNorm ψ)
theorem boxForm_bound (hC : complexifyUniqueAndBounded) {c : ℝ} {a : ℕ}
    {G : ℝ} {T : smoothRealTupleSet n → ℝ} (hT : SeparatedBallBound c a G T) (Q : PointSystem n)
    (hsep : Q.IsSeparated) (hm : IsComplexMultilinearSmooth (complexify T)) :
    ∃ B : ℝ, ∀ w, ‖boxForm Q T hsep hm w‖ ≤ B * ∏ i, gradMaxNorm c (w i).1 := by
  have hne : min 1 Q.boxGap ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
  have hd : 0 < (min 1 Q.boxGap).toReal :=
    ENNReal.toReal_pos (lt_min one_pos hsep).ne' hne
  refine ⟨2 ^ n * G * max 1 ((min 1 Q.boxGap).toReal ^ (-(a : ℤ))), fun w => ?_⟩
  refine (hC n hT.1 T hT.2.2.2.1).2 c a G hT _ hd ⟨_, boxTuple_mem Q hsep w⟩ (fun i => ?_)
    (fun i i' h => ?_)
  · exact ⟨closedBallR4 (Q.base i) 1, 1, ⟨_, rfl⟩, le_rfl,
      (w i).2.2.trans (outerBox_subset_ball Q i)⟩
  · rw [ENNReal.ofReal_toReal hne]
    exact (min_le_right _ _).trans ((boxGap_le Q h).trans
      (setDistR4_anti (w i).2.2 (w i').2.2))
def liftOnePoint (ψ : (Fin 4 → ℝ) → ℂ) : Config 1 → ℂ := tensorProd fun _ : Fin 1 => ψ
theorem liftOnePoint_apply (ψ : (Fin 4 → ℝ) → ℂ) (x : Config 1) : liftOnePoint ψ x = ψ (x 0) := by
  simp [liftOnePoint, tensorProd]
def singlePointSystem (Q : PointSystem n) (i : Fin n) : PointSystem 1 :=
  ⟨fun _ => Q.base i, Q.scale, Q.scale_pos, Q.scale_le_half⟩
theorem liftOnePoint_mem_supportedClass (Q : PointSystem n) (i : Fin n) {ψ : (Fin 4 → ℝ) → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Q.midBox i) :
    liftOnePoint ψ ∈ (singlePointSystem Q i).supportedClass := by
  have e : liftOnePoint ψ = ψ ∘ fun x : Config 1 => x 0 := funext fun x => liftOnePoint_apply ψ x
  refine ⟨?_, tsupport_subset_of_vanishing (isClosed_cylinder_midBox _) fun x hx => ?_⟩
  · rw [e]
    exact hψ.comp (contDiff_apply ℝ (Fin 4 → ℝ) (0 : Fin 1))
  · rw [liftOnePoint_apply]
    refine image_eq_zero_of_notMem_tsupport fun h => hx fun j => ?_
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    exact hs h
theorem uniformNorm_comp_eval_zero (f : (Fin 4 → ℝ) → ℂ) :
    uniformNorm (fun x : Config 1 => f (x 0)) = uniformNorm f := by
  unfold uniformNorm
  exact Function.Surjective.iSup_comp (g := fun y => ‖f y‖)
    (f := fun x : Config 1 => x 0) (fun y => ⟨fun _ => y, rfl⟩)
theorem iteratedPartial_zero (g : Config 1 → ℂ) : iteratedPartial (0 : MultiIndex 1) g = g := by
  have h1 : List.finRange 1 = [0] := rfl
  have h4 : List.finRange 4 = [0, 1, 2, 3] := rfl
  simp [iteratedPartial, h1, h4]
theorem iteratedPartial_single (μ : Fin 4) (g : Config 1 → ℂ) :
    iteratedPartial (fun _ => Pi.single μ 1) g = coordPartial 0 μ g := by
  have h1 : List.finRange 1 = [0] := rfl
  have h4 : List.finRange 4 = [0, 1, 2, 3] := rfl
  fin_cases μ <;> simp [iteratedPartial, h1, h4]
theorem coordPartial_liftOnePoint (μ : Fin 4) (ψ : (Fin 4 → ℝ) → ℂ) (x : Config 1) :
    coordPartial 0 μ (liftOnePoint ψ) x = partialDerivR4 μ ψ (x 0) := by
  unfold coordPartial lineDeriv partialDerivR4
  congr 1
  funext t
  rw [liftOnePoint_apply]
  simp
theorem bddAbove_norm_partialDerivR4 {ψ : (Fin 4 → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (μ : Fin 4) :
    BddAbove (Set.range fun y => ‖partialDerivR4 μ ψ y‖) := by
  obtain ⟨C, hC⟩ := (hψ.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ))
  refine ⟨C * ‖(Pi.single μ 1 : Fin 4 → ℝ)‖, ?_⟩
  rintro _ ⟨y, rfl⟩
  have e : partialDerivR4 μ ψ y = fderiv ℝ ψ y (Pi.single μ 1) :=
    ((hψ.differentiable (by simp)) y).lineDeriv_eq_fderiv
  simp only
  rw [e]
  exact ((fderiv ℝ ψ y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _))
theorem gradMaxNorm_le {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) {ψ : (Fin 4 → ℝ) → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hcs : HasCompactSupport ψ) :
    gradMaxNorm c ψ ≤ (1 + 2 * c * m⁻¹) * scaledSupNorm 1 m (liftOnePoint ψ) := by
  set S := scaledSupNorm 1 m (liftOnePoint ψ) with hS
  have hS0 : 0 ≤ S := scaledSupNorm_nonneg 1 hm.le _
  have hsup : uniformNorm ψ ≤ S := by
    have h := le_scaledSupNorm (ν := 1) (m := m) (liftOnePoint ψ) 0 (by simp [MultiIndex.order])
    rw [iteratedPartial_zero] at h
    have e : liftOnePoint ψ = fun x : Config 1 => ψ (x 0) :=
      funext fun x => liftOnePoint_apply ψ x
    have h2 : uniformNorm (liftOnePoint ψ) = uniformNorm ψ := by
      rw [e]
      exact uniformNorm_comp_eval_zero ψ
    simpa [MultiIndex.order, h2] using h
  have hpart : ∀ μ y, ‖partialDerivR4 μ ψ y‖ ≤ m⁻¹ * S := by
    intro μ y
    have h := le_scaledSupNorm (ν := 1) (m := m) (liftOnePoint ψ) (fun _ => Pi.single μ 1)
      (by simp [MultiIndex.order])
    have hsize : MultiIndex.order (fun _ => Pi.single μ 1 : MultiIndex 1) = 1 := by
      simp [MultiIndex.order]
    rw [hsize, iteratedPartial_single, pow_one] at h
    have e : coordPartial 0 μ (liftOnePoint ψ) = fun x : Config 1 => partialDerivR4 μ ψ (x 0) :=
      funext fun x => coordPartial_liftOnePoint μ ψ x
    rw [e, uniformNorm_comp_eval_zero] at h
    have h3 : ‖partialDerivR4 μ ψ y‖ ≤ uniformNorm (partialDerivR4 μ ψ) :=
      le_ciSup (bddAbove_norm_partialDerivR4 hψ hcs μ) y
    rw [inv_mul_eq_div, le_div_iff₀ hm]
    calc ‖partialDerivR4 μ ψ y‖ * m ≤ uniformNorm (partialDerivR4 μ ψ) * m :=
          mul_le_mul_of_nonneg_right h3 hm.le
      _ = m * uniformNorm (partialDerivR4 μ ψ) := mul_comm _ _
      _ ≤ S := h
  have hgrad : gradSupNorm ψ ≤ 2 * (m⁻¹ * S) := by
    refine ciSup_le fun y => ?_
    unfold gradNorm
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have key : ∀ μ, ‖partialDerivR4 μ ψ y‖ ^ 2 ≤ (m⁻¹ * S) ^ 2 := fun μ =>
      pow_le_pow_left₀ (norm_nonneg _) (hpart μ y) 2
    rw [Fin.sum_univ_four]
    nlinarith [key 0, key 1, key 2, key 3]
  unfold gradMaxNorm
  have hcm : 0 ≤ 2 * c * m⁻¹ := by positivity
  refine max_le ?_ ?_
  · nlinarith [mul_nonneg hcm hS0]
  · have h1 : c * gradSupNorm ψ ≤ c * (2 * (m⁻¹ * S)) := mul_le_mul_of_nonneg_left hgrad hc
    nlinarith [h1]
theorem gradMaxNorm_neg (c : ℝ) (ψ : (Fin 4 → ℝ) → ℂ) : gradMaxNorm c (-ψ) = gradMaxNorm c ψ := by
  have h1 : uniformNorm (-ψ) = uniformNorm ψ := by
    simp [uniformNorm]
  have h2 : gradSupNorm (-ψ) = gradSupNorm ψ := by
    have : ∀ μ y, partialDerivR4 μ (-ψ) y = -partialDerivR4 μ ψ y := by
      intro μ y
      unfold partialDerivR4
      simp only [Pi.neg_apply]
      exact deriv.fun_neg
    simp [gradSupNorm, gradNorm, this]
  simp [gradMaxNorm, h1, h2]
def dualLattice (m : ℝ) : Set (Fin 4 → ℝ) :=
  {η | ∃ ζ : Fin 4 → ℤ, ∀ c, η c = Real.pi / m * ζ c}
def dualLatticeBox (m t : ℝ) : Set (Fin 4 → ℝ) := {η | η ∈ dualLattice m ∧ ∀ c, |η c| ≤ t}
theorem finite_dualLatticeBox {m : ℝ} (hm : 0 < m) (t : ℝ) : (dualLatticeBox m t).Finite := by
  have hpi := Real.pi_pos
  set N : ℤ := ⌈t * m / Real.pi⌉ with hN
  refine ((Set.finite_Icc (fun _ : Fin 4 => -N) (fun _ => N)).image
    (fun (ζ : Fin 4 → ℤ) (c : Fin 4) => Real.pi / m * (ζ c : ℝ))).subset ?_
  rintro η ⟨⟨ζ, hζ⟩, hη⟩
  refine ⟨ζ, ⟨fun c => ?_, fun c => ?_⟩, funext fun c => (hζ c).symm⟩
  all_goals
    have h1 := hη c
    rw [hζ c, abs_mul, abs_of_pos (div_pos hpi hm)] at h1
    have h2 : |(ζ c : ℝ)| ≤ t * m / Real.pi := by
      rw [le_div_iff₀ hpi]
      have : Real.pi / m * |(ζ c : ℝ)| * m = |(ζ c : ℝ)| * Real.pi := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right h1 hm.le]
    have h3 : t * m / Real.pi ≤ (N : ℝ) := Int.le_ceil _
    have h4 := abs_le.mp (h2.trans h3)
  · have : (-N : ℝ) ≤ ζ c := h4.1
    exact_mod_cast this
  · have : (ζ c : ℝ) ≤ N := h4.2
    exact_mod_cast this
theorem dualLatticeBox_mono (m : ℝ) {s t : ℝ} (h : s ≤ t) :
    dualLatticeBox m s ⊆ dualLatticeBox m t :=
  fun _ hη => ⟨hη.1, fun c => (hη.2 c).trans h⟩
theorem mem_freqLattice_iff (Q : PointSystem n) (ξ : Config n) :
    ξ ∈ Q.freqLattice ↔ ∀ i, ξ i ∈ dualLattice Q.scale := by
  constructor
  · rintro ⟨ζ, hζ⟩ i
    exact ⟨ζ i, hζ i⟩
  · intro h
    choose ζ hζ using h
    exact ⟨ζ, hζ⟩
theorem coordSupNorm_le_iff [Nonempty (Fin n)] (ξ : Config n) (t : ℝ) :
    coordSupNorm ξ ≤ t ↔ ∀ i c, |ξ i c| ≤ t := by
  unfold coordSupNorm
  constructor
  · intro h i c
    have h1 : |ξ i c| ≤ ⨆ c, |ξ i c| :=
      le_ciSup (f := fun c => |ξ i c|) (Set.finite_range _).bddAbove c
    have h2 : (⨆ c, |ξ i c|) ≤ ⨆ i, ⨆ c, |ξ i c| :=
      le_ciSup (f := fun i => ⨆ c, |ξ i c|) (Set.finite_range _).bddAbove i
    exact h1.trans (h2.trans h)
  · intro h
    exact ciSup_le fun i => ciSup_le fun c => h i c
theorem mem_freqsWithin_iff [Nonempty (Fin n)] (Q : PointSystem n) (t : ℝ) (ξ : Config n) :
    ξ ∈ Q.freqsWithin t ↔ ∀ i, ξ i ∈ dualLatticeBox Q.scale t := by
  unfold PointSystem.freqsWithin
  simp only [Set.mem_ofPred_eq]
  rw [mem_freqLattice_iff, coordSupNorm_le_iff]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
theorem integral_cylinderSet_prod (S : Fin n → Set (Fin 4 → ℝ)) (f : Fin n → (Fin 4 → ℝ) → ℂ) :
    ∫ x in cylinderSet S, ∏ i, f i (x i) = ∏ i, ∫ y in S i, f i y := by
  rw [cylinderSet_eq_pi, volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod f
def componentCoeff (Q : PointSystem n) (φ : FnTuple n) (i : Fin n) (η : Fin 4 → ℝ) : ℂ :=
  (((2 * Q.scale) ^ 4)⁻¹ : ℝ) * ∫ y in Q.outerBox i,
    φ i y * Complex.exp (-(Complex.I * ((η ⬝ᵥ (y - Q.base i) : ℝ))))
theorem fourierCoeff_tensorProd (Q : PointSystem n) (φ : FnTuple n) (ξ : Config n) :
    Q.fourierCoeff (tensorProd φ) ξ = ∏ i, componentCoeff Q φ i (ξ i) := by
  unfold PointSystem.fourierCoeff componentCoeff
  have hint : ∀ x : Config n, tensorProd φ x *
      Complex.exp (-(Complex.I * (configDot ξ (x - Q.base) : ℝ))) =
      ∏ i, (φ i (x i) * Complex.exp (-(Complex.I * ((ξ i ⬝ᵥ (x i - Q.base i) : ℝ))))) := by
    intro x
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 2
    simp only [configDot, Pi.sub_apply]
    push_cast
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  simp_rw [hint]
  rw [integral_cylinderSet_prod Q.outerBox
    (fun i y => φ i y * Complex.exp (-(Complex.I * ((ξ i ⬝ᵥ (y - Q.base i) : ℝ))))),
    Finset.prod_mul_distrib]
  congr 1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [inv_pow, ← pow_mul]
theorem singlePointSystem_fourierCoeff (Q : PointSystem n) (φ : FnTuple n) (i : Fin n)
    (η : Fin 4 → ℝ) :
    (singlePointSystem Q i).fourierCoeff (liftOnePoint (φ i)) (fun _ => η) =
      componentCoeff Q φ i η := by
  unfold liftOnePoint
  rw [fourierCoeff_tensorProd]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rfl
section Modes
variable {Q : PointSystem n}
theorem const_mem_freqLattice {η : Fin 4 → ℝ} (hη : η ∈ dualLattice Q.scale) :
    (fun _ => η) ∈ Q.freqLattice :=
  (mem_freqLattice_iff Q _).mpr fun _ => hη
theorem modeFun_mem_boxFunctions (hmodes : Q.ModesLocalCharacters) (i : Fin n) {η : Fin 4 → ℝ}
    (hη : η ∈ dualLattice Q.scale) : Q.modeFun i (fun _ => η) ∈ boxFunctions Q i :=
  ⟨(hmodes i _ (const_mem_freqLattice hη)).1.1, (hmodes i _ (const_mem_freqLattice hη)).2.1⟩
open scoped Classical in
def boxMode (hmodes : Q.ModesLocalCharacters) (i : Fin n) (η : Fin 4 → ℝ) :
    boxFunctions Q i :=
  if hη : η ∈ dualLattice Q.scale then
    ⟨Q.modeFun i (fun _ => η), modeFun_mem_boxFunctions hmodes i hη⟩
  else 0
theorem boxMode_coe (hmodes : Q.ModesLocalCharacters) (i : Fin n) {η : Fin 4 → ℝ}
    (hη : η ∈ dualLattice Q.scale) : (boxMode hmodes i η).1 = Q.modeFun i (fun _ => η) := by
  unfold boxMode
  rw [dif_pos hη]
def componentPartialSum (hmodes : Q.ModesLocalCharacters) (φ : FnTuple n) (i : Fin n)
    (t : ℝ) : boxFunctions Q i :=
  ∑ η ∈ (finite_dualLatticeBox Q.scale_pos t).toFinset, componentCoeff Q φ i η • boxMode hmodes i η
theorem singlePointSystem_truncatedSum (hmodes : Q.ModesLocalCharacters) (φ : FnTuple n)
    (i : Fin n) (t : ℝ) :
    (singlePointSystem Q i).truncatedSum (liftOnePoint (φ i)) t =
      liftOnePoint (componentPartialSum hmodes φ i t).1 := by
  funext x
  have himg : (singlePointSystem Q i).freqsWithin t =
      (fun (η : Fin 4 → ℝ) (_ : Fin 1) => η) '' dualLatticeBox Q.scale t := by
    ext ξ
    rw [mem_freqsWithin_iff]
    constructor
    · intro h
      refine ⟨ξ 0, h 0, funext fun j => ?_⟩
      rw [Subsingleton.elim j 0]
    · rintro ⟨η, hη, rfl⟩ _
      exact hη
  have hinj : Set.InjOn (fun (η : Fin 4 → ℝ) (_ : Fin 1) => η) (dualLatticeBox Q.scale t) :=
    fun a _ b _ h => congrFun h 0
  unfold PointSystem.truncatedSum
  rw [himg, finsum_mem_image hinj,
    finsum_mem_eq_finite_toFinset_sum _ (finite_dualLatticeBox Q.scale_pos t), liftOnePoint_apply]
  unfold componentPartialSum
  rw [Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun η hη => ?_
  have hη' : η ∈ dualLattice Q.scale := ((Set.Finite.mem_toFinset _).mp hη).1
  rw [singlePointSystem_fourierCoeff, Submodule.coe_smul, Pi.smul_apply, boxMode_coe hmodes i hη',
    smul_eq_mul]
  congr 1
  simp only [tensorProd, Finset.univ_unique, Finset.prod_singleton]
  rfl
end Modes
theorem pairingOnTensors_holds (hF : FourierExpansionAndModeCosts)
    (hC : complexifyUniqueAndBounded) (hFF : TupleFacts.BasicFacts)
    {c : ℝ} {a : ℕ} {G : ℝ} {T : smoothRealTupleSet n → ℝ} {Q : PointSystem n}
    (hT : SeparatedBallBound c a G T) (hsep : Q.IsSeparated) : PairingOnTensors T Q := by
  classical
  intro φ hsmooth hsupp
  have hn : 2 ≤ n := hT.1
  have hn1 : 1 ≤ n := by omega
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hc : 0 ≤ c := hT.2.1.le
  let v : ∀ i, boxFunctions Q i := fun i =>
    ⟨φ i, hsmooth i, (hsupp i).trans (midBox_subset_outerBox Q i)⟩
  have htuple : φ ∈ smoothComplexTupleSet n := boxTuple_mem Q hsep v
  have hten := (hFF n hn).2.1.1 φ htuple
  have hmem : tensorProd φ ∈ Q.supportedClass :=
    ⟨hten.1.1, hten.2.trans fun x hx i => hsupp i (hx i)⟩
  refine ⟨htuple, hmem, ?_⟩
  obtain ⟨-, hmodes, -, -, -, hcostall⟩ := hF n hn1 Q (tensorProd φ) hmem
  obtain ⟨hmodecost, hcost⟩ := hcostall hn hsep c a G T hT
  have hmult : IsComplexMultilinearSmooth (complexify T) := (hC n hn T hT.2.2.2.1).1.2.1
  obtain ⟨B, hB⟩ := boxForm_bound hC hT Q hsep hmult
  set M := boxForm Q T hsep hmult with hM
  let A : ℝ → Finset (Fin 4 → ℝ) := fun t => (finite_dualLatticeBox Q.scale_pos t).toFinset
  let u : ℝ → ∀ i, boxFunctions Q i := fun t i => componentPartialSum hmodes φ i t
  have hlim1 : Tendsto (fun t => M (u t)) atTop (𝓝 (M v)) := by
    refine tendsto_multilinear_of_bound M (fun _ w => gradMaxNorm c w.1) B hB u v fun i => ?_
    have hone := (hF 1 le_rfl (singlePointSystem Q i) (liftOnePoint (φ i))
      (liftOnePoint_mem_supportedClass Q i (hsmooth i) (hsupp i))).2.2.2.1.2 1
    have hK := hone.const_mul (1 + 2 * c * Q.scale⁻¹)
    rw [mul_zero] at hK
    refine squeeze_zero (fun t => ?_) (fun t => ?_) hK
    · exact le_max_of_le_left (uniformNorm_nonneg _)
    · have hd : ((u t i - v i : boxFunctions Q i) : (Fin 4 → ℝ) → ℂ) =
          -((v i - u t i : boxFunctions Q i) : (Fin 4 → ℝ) → ℂ) := by
        simp
      have hmemd := (v i - u t i : boxFunctions Q i).2
      simp only [hd, gradMaxNorm_neg]
      refine (gradMaxNorm_le hc Q.scale_pos hmemd.1
        (hasCompactSupport_of_mem_boxFunctions Q hmemd)).trans (le_of_eq ?_)
      congr 2
      funext x
      simp only [Pi.sub_apply, Submodule.coe_sub, liftOnePoint_apply]
      rw [singlePointSystem_truncatedSum hmodes φ i t, liftOnePoint_apply]
  have hMu : ∀ t, M (u t) = ∑ r ∈ Fintype.piFinset fun _ : Fin n => A t,
      Q.fourierCoeff (tensorProd φ) r * complexifyAtModes T Q r := by
    intro t
    have h := M.map_sum_finset (fun i η => componentCoeff Q φ i η • boxMode hmodes i η)
      (fun _ => A t)
    refine h.trans (Finset.sum_congr rfl fun r hr => ?_)
    rw [M.map_smul_univ, fourierCoeff_tensorProd, smul_eq_mul]
    congr 1
    have hri : ∀ i, r i ∈ dualLattice Q.scale := fun i =>
      ((Set.Finite.mem_toFinset _).mp (Fintype.mem_piFinset.mp hr i)).1
    have hr' : r ∈ Q.freqLattice := (mem_freqLattice_iff Q r).mpr hri
    unfold complexifyAtModes
    rw [dif_pos (hmodecost r hr').1]
    show complexify T ⟨_, _⟩ = _
    congr 2
    funext i
    rw [boxMode_coe hmodes i (hri i)]
    rfl
  let Fs : ℝ → Finset Q.freqLattice := fun t =>
    (Fintype.piFinset fun _ : Fin n => A t).subtype (· ∈ Q.freqLattice)
  have hmono : Monotone Fs := by
    intro s t hst ξ hξ
    simp only [Fs, Finset.mem_subtype, Fintype.mem_piFinset] at hξ ⊢
    intro i
    exact (Set.Finite.mem_toFinset _).mpr
      (dualLatticeBox_mono _ hst ((Set.Finite.mem_toFinset _).mp (hξ i)))
  have hevery : ∀ ξ : Q.freqLattice, ∃ t, ξ ∈ Fs t := by
    intro ξ
    refine ⟨coordSupNorm ξ.1, ?_⟩
    simp only [Fs, Finset.mem_subtype, Fintype.mem_piFinset]
    intro i
    refine (Set.Finite.mem_toFinset _).mpr ?_
    exact (mem_freqsWithin_iff Q _ ξ.1).mp ⟨ξ.2, le_rfl⟩ i
  have hFs := tendsto_atTop_finset_of_monotone hmono hevery
  have hlim2 : Tendsto (fun t => M (u t)) atTop (𝓝 (localPairing T Q (tensorProd φ))) := by
    have hs := (summable_pairingTerms hcost).hasSum
    have hcomp := Tendsto.comp hs hFs
    refine hcomp.congr fun t => ?_
    rw [hMu t]
    simp only [Function.comp_apply]
    exact Finset.sum_subtype_of_mem
      (fun r => Q.fourierCoeff (tensorProd φ) r * complexifyAtModes T Q r)
      (fun r hr => (mem_freqLattice_iff Q r).mpr fun i =>
        ((Set.Finite.mem_toFinset (finite_dualLatticeBox Q.scale_pos t)).mp
          (Fintype.mem_piFinset.mp hr i)).1)
  exact tendsto_nhds_unique hlim2 hlim1
theorem localPairingProperties_holds (hF : FourierExpansionAndModeCosts)
    (hC : complexifyUniqueAndBounded) (hFF : TupleFacts.BasicFacts)
    (hb : GevreyBumpBounds) : LocalPairingProperties := by
  intro n c a G T Q hT hsep
  have hn1 : 1 ≤ n := by
    have := hT.1
    omega
  have hcost : ∀ Φ ∈ Q.supportedClass, Q.CoeffCostSummable Φ c a G T := fun Φ hΦ =>
    ((hF n hn1 Q Φ hΦ).2.2.2.2.2 hT.1 hsep c a G T hT).2
  exact ⟨supportedClass_isSubmodule Q,
    ⟨fun Φ hΦ Ψ hΨ => localPairing_add hcost hΦ hΨ, fun lam Φ _ => localPairing_smul lam Φ⟩,
    one_le_localConst hb,
    fun Φ hΦ => norm_localPairing_le hb hn1 hT.2.2.1 (hcost Φ hΦ),
    localPairing_continuous hb hn1 hT.2.2.1 hcost, pairingOnTensors_holds hF hC hFF hT hsep⟩
end LocalPairingBounds
end YangMills.Construction.ConfigSpace
