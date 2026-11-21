import YangMills.Construction.Continuum.CoefficientsOfAFunctionOfASystemDecayProof
import YangMills.Construction.Continuum.ConsistencyOfTheLocalFunctionals
import YangMills.Construction.Continuum.FourierSeriesOfASystemAndTheCostOfAMode
import YangMills.Construction.Continuum.LocalFunctionalsLinearBoundedAndValueOnTensors
import YangMills.Construction.RealFunctions.GevreyBumpBounds
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ConfigSpace
open YangMills.Construction.TestFunctions YangMills.Construction.Bumps YangMills.Construction.ShellPieces
namespace LocalPairingConsistency
variable {n : ℕ}
private theorem mem_closedBox_iff (a y : Fin 4 → ℝ) (s : ℝ) :
    y ∈ closedBox a s ↔ ∀ c, |y c - a c| ≤ s / 2 := by
  unfold YangMills.Construction.ShellPieces.closedBox YangMills.Construction.EuclideanCoords.supCoord
  change (⨆ c, |(y - a) c|) ≤ s / 2 ↔ _
  constructor
  · intro h c
    exact (le_ciSup (f := fun c => |(y - a) c|) (Set.finite_range _).bddAbove c).trans h
  · intro h
    exact ciSup_le h
abbrev _root_.YangMills.SharedProofs.p5872 := @mem_closedBox_iff
private theorem closedBox_mono {a : Fin 4 → ℝ} {s s' : ℝ} (h : s ≤ s') :
    closedBox a s ⊆ closedBox a s' := by
  intro y hy
  rw [mem_closedBox_iff] at hy ⊢
  intro c
  linarith [hy c]
private theorem finite_multiIndex_le (ν : ℕ) : Finite {α : MultiIndex n // α.order ≤ ν} := by apply _root_.YangMills.Construction.ConfigSpace.FourierDecay.finite_order_le <;> assumption
private theorem scaledSupNorm_nonneg (ν : ℕ) {m : ℝ} (hm : 0 ≤ m) (Ψ : Config n → ℂ) :
    0 ≤ scaledSupNorm ν m Ψ :=
  Real.iSup_nonneg fun _ =>
    mul_nonneg (pow_nonneg hm _) (Real.iSup_nonneg fun _ => norm_nonneg _)
private theorem scaledSupNorm_le_of_scale_le (ν : ℕ) {s m : ℝ} (hs : 0 < s) (hsm : s ≤ m)
    (Ψ : Config n → ℂ) : scaledSupNorm ν m Ψ ≤ (m / s) ^ ν * scaledSupNorm ν s Ψ := by
  have := finite_multiIndex_le (n := n) ν
  have : Nonempty {α : MultiIndex n // α.order ≤ ν} :=
    ⟨⟨0, by simp [MultiIndex.order]⟩⟩
  refine ciSup_le fun α => ?_
  have hα := le_ciSup (f := fun α : {α : MultiIndex n // α.order ≤ ν} =>
    s ^ α.1.order * uniformNorm (iteratedPartial α.1 Ψ)) (Set.finite_range _).bddAbove α
  have hS : 0 ≤ uniformNorm (iteratedPartial α.1 Ψ) := Real.iSup_nonneg fun _ => norm_nonneg _
  have hr : 1 ≤ m / s := (one_le_div hs).2 hsm
  have hterm : 0 ≤ s ^ α.1.order * uniformNorm (iteratedPartial α.1 Ψ) :=
    mul_nonneg (pow_nonneg hs.le _) hS
  calc m ^ α.1.order * uniformNorm (iteratedPartial α.1 Ψ)
      = (m / s) ^ α.1.order * (s ^ α.1.order * uniformNorm (iteratedPartial α.1 Ψ)) := by
        rw [div_pow]
        field_simp
    _ ≤ (m / s) ^ ν * (s ^ α.1.order * uniformNorm (iteratedPartial α.1 Ψ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr α.2) hterm
    _ ≤ (m / s) ^ ν * scaledSupNorm ν s Ψ :=
        mul_le_mul_of_nonneg_left hα (pow_nonneg (by linarith) _)
private theorem map_finset_sum_of_linearOn (S : Submodule ℂ (Config n → ℂ)) (L : (Config n → ℂ) → ℂ)
    (hadd : ∀ Φ ∈ S, ∀ Ψ ∈ S, L (Φ + Ψ) = L Φ + L Ψ)
    (hsmul : ∀ (lam : ℂ), ∀ Φ ∈ S, L (lam • Φ) = lam * L Φ)
    {ι : Type*} (s : Finset ι) (w : ι → ℂ) (f : ι → Config n → ℂ) (hf : ∀ k ∈ s, f k ∈ S) :
    L (∑ k ∈ s, w k • f k) = ∑ k ∈ s, w k * L (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hsmul 0 0 S.zero_mem
    simpa using this
  | insert k s hk ih =>
    have hfs : ∀ j ∈ s, f j ∈ S := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hfk : f k ∈ S := hf k (Finset.mem_insert_self k s)
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      hadd _ (S.smul_mem _ hfk) _ (S.sum_mem fun j hj => S.smul_mem _ (hfs j hj)),
      hsmul _ _ hfk, ih hfs]
private theorem tendsto_of_sub_gauge (S : Submodule ℂ (Config n → ℂ)) (L : (Config n → ℂ) → ℂ)
    (gauge : (Config n → ℂ) → ℝ)
    (hadd : ∀ Φ ∈ S, ∀ Ψ ∈ S, L (Φ + Ψ) = L Φ + L Ψ)
    (hsmul : ∀ (lam : ℂ), ∀ Φ ∈ S, L (lam • Φ) = lam * L Φ)
    (hcont : ∀ (Φ : Config n → ℂ) (Φ' : ℝ → Config n → ℂ), Φ ∈ S → (∀ t, 0 < t → Φ' t ∈ S) →
      Tendsto (fun t => gauge (Φ' t - Φ)) atTop (𝓝 0) →
      Tendsto (fun t => L (Φ' t)) atTop (𝓝 (L Φ)))
    {Ψ : Config n → ℂ} (hΨ : Ψ ∈ S) {A : ℝ → Config n → ℂ} (hA : ∀ t, 0 < t → A t ∈ S)
    (hlim : Tendsto (fun t => gauge (Ψ - A t)) atTop (𝓝 0)) :
    Tendsto (fun t => L (A t)) atTop (𝓝 (L Ψ)) := by
  have hmem : ∀ t, 0 < t → Ψ + (Ψ + (-1 : ℂ) • A t) ∈ S := fun t ht =>
    S.add_mem hΨ (S.add_mem hΨ (S.smul_mem _ (hA t ht)))
  have hgauge : (fun t => gauge ((Ψ + (Ψ + (-1 : ℂ) • A t)) - Ψ)) =
      fun t => gauge (Ψ - A t) := by
    funext t
    congr 1
    rw [add_sub_cancel_left, neg_one_smul, sub_eq_add_neg]
  have h1 := hcont Ψ (fun t => Ψ + (Ψ + (-1 : ℂ) • A t)) hΨ hmem (by rw [hgauge]; exact hlim)
  have h2 : Tendsto (fun t => (2 : ℂ) * L Ψ - L (Ψ + (Ψ + (-1 : ℂ) • A t))) atTop
      (𝓝 ((2 : ℂ) * L Ψ - L Ψ)) := tendsto_const_nhds.sub h1
  have h3 : (2 : ℂ) * L Ψ - L Ψ = L Ψ := by ring
  rw [h3] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hAt := hA t ht
  rw [hadd _ hΨ _ (S.add_mem hΨ (S.smul_mem _ hAt)), hadd _ hΨ _ (S.smul_mem _ hAt),
    hsmul _ _ hAt]
  ring
private theorem pairing_eq_of_fine_system
    (hL : LocalPairingProps.LocalPairingProperties)
    (hF : FourierExpansionAndModeCosts)
    {c : ℝ} {a : ℕ} {G : ℝ} {T : smoothRealTupleSet n → ℝ}
    (hT : SeparatedBallBound c a G T) {Q Q' P : PointSystem n}
    (hQ : Q.IsSeparated) (hQ' : Q'.IsSeparated)
    (hs : P.scale ≤ Q.scale) (hs' : P.scale ≤ Q'.scale)
    (hc : ∀ i, P.outerBox i ⊆ Q.midBox i) (hc' : ∀ i, P.outerBox i ⊆ Q'.midBox i)
    {Ψ : Config n → ℂ} (hP : Ψ ∈ P.supportedClass) (h1 : Ψ ∈ Q.supportedClass)
    (h2 : Ψ ∈ Q'.supportedClass) :
    localPairing T Q Ψ = localPairing T Q' Ψ := by
  have hn : 1 ≤ n := le_trans (by norm_num) hT.1
  obtain ⟨-, hModes, -, hApprox, -, -⟩ := hF n hn P Ψ hP
  obtain ⟨⟨S, hS⟩, ⟨hadd, hsmul⟩, -, -, hcont, hval⟩ := hL n c a G T Q hT hQ
  obtain ⟨⟨S', hS'⟩, ⟨hadd', hsmul'⟩, -, -, hcont', hval'⟩ := hL n c a G T Q' hT hQ'
  have mem : ∀ Φ, Φ ∈ S ↔ Φ ∈ Q.supportedClass := fun Φ => by rw [← hS]; rfl
  have mem' : ∀ Φ, Φ ∈ S' ↔ Φ ∈ Q'.supportedClass := fun Φ => by rw [← hS']; rfl
  have htensor : ∀ ξ ∈ P.freqLattice, tensorProd (P.modeFamily ξ) ∈ S ∧
      tensorProd (P.modeFamily ξ) ∈ S' ∧
      localPairing T Q (tensorProd (P.modeFamily ξ)) =
        localPairing T Q' (tensorProd (P.modeFamily ξ)) := by
    intro ξ hξ
    have hsm : ∀ i, ContDiff ℝ ∞ (P.modeFamily ξ i) := fun i => (hModes i ξ hξ).1.1
    obtain ⟨h, ht, hv⟩ := hval (P.modeFamily ξ) hsm fun i => (hModes i ξ hξ).2.1.trans (hc i)
    obtain ⟨h', ht', hv'⟩ := hval' (P.modeFamily ξ) hsm fun i => (hModes i ξ hξ).2.1.trans (hc' i)
    exact ⟨(mem _).2 ht, (mem' _).2 ht', hv.trans hv'.symm⟩
  have hsum : ∀ t : ℝ, 0 < t → ∃ s : Finset (Config n), (∀ ξ ∈ s, ξ ∈ P.freqLattice) ∧
      P.truncatedSum Ψ t = ∑ ξ ∈ s, P.fourierCoeff Ψ ξ • tensorProd (P.modeFamily ξ) := by
    intro t ht
    have hfin := (hApprox.1 t ht).1
    refine ⟨hfin.toFinset, fun ξ hξ => ((hfin.mem_toFinset).1 hξ).1, ?_⟩
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    unfold PointSystem.truncatedSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hA : ∀ t : ℝ, 0 < t → P.truncatedSum Ψ t ∈ S := by
    intro t ht
    obtain ⟨s, hs0, he⟩ := hsum t ht
    rw [he]
    exact S.sum_mem fun ξ hξ => S.smul_mem _ (htensor ξ (hs0 ξ hξ)).1
  have hA' : ∀ t : ℝ, 0 < t → P.truncatedSum Ψ t ∈ S' := by
    intro t ht
    obtain ⟨s, hs0, he⟩ := hsum t ht
    rw [he]
    exact S'.sum_mem fun ξ hξ => S'.smul_mem _ (htensor ξ (hs0 ξ hξ)).2.1
  have hsame : ∀ t : ℝ, 0 < t →
      localPairing T Q (P.truncatedSum Ψ t) = localPairing T Q' (P.truncatedSum Ψ t) := by
    intro t ht
    obtain ⟨s, hs0, he⟩ := hsum t ht
    rw [he, map_finset_sum_of_linearOn S _
        (fun Φ hΦ Φ' hΦ' => hadd Φ ((mem _).1 hΦ) Φ' ((mem _).1 hΦ'))
        (fun lam Φ hΦ => hsmul lam Φ ((mem _).1 hΦ)) s _ _
        (fun ξ hξ => (htensor ξ (hs0 ξ hξ)).1),
      map_finset_sum_of_linearOn S' _
        (fun Φ hΦ Φ' hΦ' => hadd' Φ ((mem' _).1 hΦ) Φ' ((mem' _).1 hΦ'))
        (fun lam Φ hΦ => hsmul' lam Φ ((mem' _).1 hΦ)) s _ _
        (fun ξ hξ => (htensor ξ (hs0 ξ hξ)).2.1)]
    exact Finset.sum_congr rfl fun ξ hξ => by rw [(htensor ξ (hs0 ξ hξ)).2.2]
  have hgauge : ∀ {m : ℝ}, P.scale ≤ m →
      Tendsto (fun t => scaledSupNorm (5 * n + 1) m (Ψ - P.truncatedSum Ψ t)) atTop (𝓝 0) := by
    intro m hm
    have hm0 : 0 ≤ m := P.scale_pos.le.trans hm
    have hb := (hApprox.2 (5 * n + 1)).const_mul ((m / P.scale) ^ (5 * n + 1))
    rw [mul_zero] at hb
    exact squeeze_zero (fun t => scaledSupNorm_nonneg _ hm0 _)
      (fun t => scaledSupNorm_le_of_scale_le _ P.scale_pos hm _) hb
  have hlim := tendsto_of_sub_gauge S (localPairing T Q) (scaledSupNorm (5 * n + 1) Q.scale)
    (fun Φ hΦ Φ' hΦ' => hadd Φ ((mem _).1 hΦ) Φ' ((mem _).1 hΦ'))
    (fun lam Φ hΦ => hsmul lam Φ ((mem _).1 hΦ))
    (fun Φ Φ' hΦ hΦ' hl => hcont Φ Φ' ((mem _).1 hΦ) (fun t ht => (mem _).1 (hΦ' t ht)) hl)
    ((mem _).2 h1) hA (hgauge hs)
  have hlim' := tendsto_of_sub_gauge S' (localPairing T Q') (scaledSupNorm (5 * n + 1) Q'.scale)
    (fun Φ hΦ Φ' hΦ' => hadd' Φ ((mem' _).1 hΦ) Φ' ((mem' _).1 hΦ'))
    (fun lam Φ hΦ => hsmul' lam Φ ((mem' _).1 hΦ))
    (fun Φ Φ' hΦ hΦ' hl => hcont' Φ Φ' ((mem' _).1 hΦ) (fun t ht => (mem' _).1 (hΦ' t ht)) hl)
    ((mem' _).2 h2) hA' (hgauge hs')
  refine tendsto_nhds_unique hlim (hlim'.congr' ?_)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (hsame t ht).symm
private def bumpProduct (v : ℝ) (z : LatticePt n) (x : Config n) : ℝ :=
  ∏ i, ∏ c, mollifiedIndicator (x i c / v - z i c)
private def latticeWindow (N : ℕ) : Finset (LatticePt n) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N
private theorem sum_translates_eq_one (hB : Bumps.GevreyBumpBounds) {t : ℝ} {N : ℕ}
    (ht : |t| + 1 ≤ N) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) N, mollifiedIndicator (t - k) = 1 := by
  obtain ⟨-, -, -, ⟨-, -, hsupp, hsum⟩, -, -⟩ := hB
  have hz : ∀ k ∉ Finset.Icc (-(N : ℤ)) N, mollifiedIndicator (t - k) = 0 := by
    intro k hk
    by_contra hne
    apply hk
    have hmem := hsupp (subset_tsupport _ (Function.mem_support.2 hne))
    have habs := abs_le.1 (le_refl |t|)
    have h1 : -(N : ℝ) ≤ k := by linarith [hmem.2, habs.1]
    have h2 : (k : ℝ) ≤ N := by linarith [hmem.1, habs.2]
    rw [Finset.mem_Icc]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  exact (hasSum_sum_of_ne_finset_zero hz).unique (hsum t).1
private theorem sum_bumpProduct_eq_one (hB : Bumps.GevreyBumpBounds) {v : ℝ} {N : ℕ}
    {x : Config n} (hx : ∀ i c, |x i c / v| + 1 ≤ N) :
    ∑ z ∈ latticeWindow (n := n) N, bumpProduct v z x = 1 := by
  have h1 : ∀ i c, ∑ k ∈ Finset.Icc (-(N : ℤ)) N, mollifiedIndicator (x i c / v - k) = 1 :=
    fun i c => sum_translates_eq_one hB (hx i c)
  have h2 : ∀ i, ∑ w ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(N : ℤ)) N),
      ∏ c, mollifiedIndicator (x i c / v - w c) = 1 := by
    intro i
    have h := Finset.prod_univ_sum (fun _ : Fin 4 => Finset.Icc (-(N : ℤ)) N)
      (fun c k => mollifiedIndicator (x i c / v - k))
    rw [← h]
    exact Finset.prod_eq_one fun c _ => h1 i c
  have h3 := Finset.prod_univ_sum
    (fun _ : Fin n => Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(N : ℤ)) N))
    (fun i (w : Fin 4 → ℤ) => ∏ c, mollifiedIndicator (x i c / v - w c))
  unfold latticeWindow bumpProduct
  rw [← h3]
  exact Finset.prod_eq_one fun i _ => h2 i
private theorem near_of_bumpProduct_ne_zero (hB : Bumps.GevreyBumpBounds) {v : ℝ}
    (hv : 0 < v) {z : LatticePt n} {x : Config n} (h : bumpProduct v z x ≠ 0) (i : Fin n)
    (c : Fin 4) : |x i c - v * z i c| ≤ 3 / 4 * v := by
  obtain ⟨-, -, -, ⟨-, -, hsupp, -⟩, -, -⟩ := hB
  have hi := Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
  have hc := Finset.prod_ne_zero_iff.1 hi c (Finset.mem_univ c)
  have hmem := hsupp (subset_tsupport _ (Function.mem_support.2 hc))
  have heq : x i c - v * z i c = v * (x i c / v - z i c) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hv, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_le.2 ⟨by linarith [hmem.1], hmem.2⟩) hv.le
private theorem tsupport_bumpProduct_subset (hB : Bumps.GevreyBumpBounds) {v : ℝ}
    (hv : 0 < v) (z : LatticePt n) :
    tsupport (fun x : Config n => ((bumpProduct v z x : ℝ) : ℂ)) ⊆
      {x | ∀ i c, |x i c - v * z i c| ≤ 3 / 4 * v} := by
  refine closure_minimal ?_ ?_
  · intro x hx
    have : bumpProduct v z x ≠ 0 := fun h => hx (by simp [h])
    exact near_of_bumpProduct_ne_zero hB hv this
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun c =>
      isClosed_le (by fun_prop) continuous_const
private theorem contDiff_bumpProduct (hB : Bumps.GevreyBumpBounds) (v : ℝ)
    (z : LatticePt n) : ContDiff ℝ ∞ (fun x : Config n => ((bumpProduct v z x : ℝ) : ℂ)) := by
  obtain ⟨-, -, -, ⟨hsm, -⟩, -, -⟩ := hB
  have hsm' : ContDiff ℝ ∞ mollifiedIndicator := hsm
  have hb : ContDiff ℝ ∞ (fun x : Config n => bumpProduct v z x) := by
    unfold bumpProduct
    refine contDiff_prod fun i _ => contDiff_prod fun c _ => hsm'.comp ?_
    have hx : ContDiff ℝ ∞ (fun x : Config n => x i c) := by fun_prop
    exact (hx.div_const v).sub contDiff_const
  exact Complex.ofRealCLM.contDiff.comp hb
end LocalPairingConsistency
theorem LocalPairingConsistency.localPairingConsistent_of_bounds
    (hL : LocalPairingProps.LocalPairingProperties)
    (hF : FourierExpansionAndModeCosts)
    (hB : Bumps.GevreyBumpBounds) : LocalPairingConsistent := by
  intro n c a G T hT Q Q' hQ hQ' Φ hΦ hsupp
  have hm0 : 0 < min Q.scale Q'.scale := lt_min Q.scale_pos Q'.scale_pos
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = min Q.scale Q'.scale / 12 := ⟨_, rfl⟩
  have hv : 0 < v := by rw [hvdef]; positivity
  have hvQ : 12 * v ≤ Q.scale := by
    rw [hvdef]; linarith [min_le_left Q.scale Q'.scale]
  have hvQ' : 12 * v ≤ Q'.scale := by
    rw [hvdef]; linarith [min_le_right Q.scale Q'.scale]
  have hhalf : 2 * v ≤ 1 / 2 := by linarith [Q.scale_le_half]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ x ∈ cylinderSet Q.box, ∀ i c, |x i c / v| + 1 ≤ N := by
    obtain ⟨N, hN⟩ := exists_nat_ge ((∑ i, ∑ c, |Q.base i c| + Q.scale) / v + 1)
    refine ⟨N, fun x hx i c => ?_⟩
    have h1 := (LocalPairingConsistency.mem_closedBox_iff _ _ _).1 (hx i) c
    have h2 : |Q.base i c| ≤ ∑ c, |Q.base i c| :=
      Finset.single_le_sum (f := fun c => |Q.base i c|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ c)
    have h3 : ∑ c, |Q.base i c| ≤ ∑ i, ∑ c, |Q.base i c| :=
      Finset.single_le_sum (f := fun i => ∑ c, |Q.base i c|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h4 : |x i c| ≤ ∑ i, ∑ c, |Q.base i c| + Q.scale := by
      have := abs_sub_abs_le_abs_sub (x i c) (Q.base i c)
      have hh : |x i c - Q.base i c| ≤ Q.scale / 2 := h1
      linarith [Q.scale_pos]
    have h5 : |x i c / v| ≤ (∑ i, ∑ c, |Q.base i c| + Q.scale) / v := by
      rw [abs_div, abs_of_pos hv]
      exact div_le_div_of_nonneg_right h4 hv.le
    linarith
  obtain ⟨piece, hpiece⟩ : ∃ piece : LatticePt n → Config n → ℂ,
      piece = fun z x => ((LocalPairingConsistency.bumpProduct v z x : ℝ) : ℂ) * Φ x := ⟨_, rfl⟩
  have hsumΦ : Φ = ∑ z ∈ LocalPairingConsistency.latticeWindow (n := n) N, (1 : ℂ) • piece z := by
    funext x
    simp only [Finset.sum_apply, one_smul, hpiece]
    by_cases hx : x ∈ cylinderSet Q.box
    · have h1 := LocalPairingConsistency.sum_bumpProduct_eq_one hB (hN x hx)
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, h1]
      simp
    · have h0 : Φ x = 0 := by
        by_contra hne
        exact hx (hsupp (subset_tsupport _ (Function.mem_support.2 hne))).1
      simp [h0]
  have hsmooth : ∀ z, ContDiff ℝ ∞ (piece z) := fun z => by
    rw [hpiece]
    exact (LocalPairingConsistency.contDiff_bumpProduct hB v z).mul hΦ
  have hsub : ∀ z, tsupport (piece z) ⊆ tsupport Φ := fun z => by
    rw [hpiece]
    exact tsupport_mul_subset_right
  have hnear : ∀ z, ∀ x ∈ tsupport (piece z), ∀ i c, |x i c - v * z i c| ≤ 3 / 4 * v := by
    intro z x hx
    rw [hpiece] at hx
    exact LocalPairingConsistency.tsupport_bumpProduct_subset hB hv z
      (tsupport_mul_subset_left hx)
  have hmiddle : ∀ (R : PointSystem n), cylinderSet R.box ⊆ cylinderSet R.midBox := by
    intro R x hx i
    exact LocalPairingConsistency.closedBox_mono (by linarith [R.scale_pos]) (hx i)
  have hinclass : ∀ z, piece z ∈ Q.supportedClass ∧ piece z ∈ Q'.supportedClass := fun z =>
    ⟨⟨hsmooth z, ((hsub z).trans hsupp).trans (Set.inter_subset_left.trans (hmiddle Q))⟩,
      ⟨hsmooth z, ((hsub z).trans hsupp).trans (Set.inter_subset_right.trans (hmiddle Q'))⟩⟩
  have hone : ∀ z, localPairing T Q (piece z) = localPairing T Q' (piece z) := by
    intro z
    by_cases h0 : piece z = 0
    · have hq := (hL n c a G T Q hT hQ).2.1.2 0 (piece z) (hinclass z).1
      have hq' := (hL n c a G T Q' hT hQ').2.1.2 0 (piece z) (hinclass z).2
      rw [h0, zero_smul, zero_mul] at hq hq'
      rw [h0, hq, hq']
    · obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 h0
      have hx₀' : ((LocalPairingConsistency.bumpProduct v z x₀ : ℝ) : ℂ) * Φ x₀ ≠ 0 := by
        rw [hpiece] at hx₀
        simpa using hx₀
      have hb : LocalPairingConsistency.bumpProduct v z x₀ ≠ 0 := fun h =>
        hx₀' (by simp [h])
      have hΦ₀ : Φ x₀ ≠ 0 := fun h => hx₀' (by simp [h])
      have hnear₀ := LocalPairingConsistency.near_of_bumpProduct_ne_zero hB hv hb
      have hx₀s := hsupp (subset_tsupport _ (Function.mem_support.2 hΦ₀))
      let P : PointSystem n := ⟨fun i c => v * z i c, 2 * v, by positivity, hhalf⟩
      have hlarge : ∀ (R : PointSystem n), x₀ ∈ cylinderSet R.box → 12 * v ≤ R.scale →
          ∀ i, P.outerBox i ⊆ R.midBox i := by
        intro R hR hvR i y hy
        have hy' := (LocalPairingConsistency.mem_closedBox_iff _ _ _).1 hy
        refine (LocalPairingConsistency.mem_closedBox_iff _ _ _).2 fun c => ?_
        have h1 : |y c - v * z i c| ≤ 2 * (2 * v) / 2 := hy' c
        have h2 := hnear₀ i c
        have h3 : |x₀ i c - R.base i c| ≤ R.scale / 2 :=
          (LocalPairingConsistency.mem_closedBox_iff _ _ _).1 (hR i) c
        have h4 : y c - R.base i c =
            (y c - v * z i c) - (x₀ i c - v * z i c) + (x₀ i c - R.base i c) := by ring
        have h5 := abs_add_le ((y c - v * z i c) - (x₀ i c - v * z i c))
          (x₀ i c - R.base i c)
        have h6 := abs_sub (y c - v * z i c) (x₀ i c - v * z i c)
        rw [h4]
        linarith
      have hPmiddle : tsupport (piece z) ⊆ cylinderSet P.midBox := by
        intro x hx i
        refine (LocalPairingConsistency.mem_closedBox_iff _ _ _).2 fun c => ?_
        have h1 := hnear z x hx i c
        have h2 : (3 / 2 * (2 * v)) / 2 = 3 / 2 * v := by ring
        change |x i c - v * z i c| ≤ (3 / 2 * (2 * v)) / 2
        rw [h2]
        linarith
      exact LocalPairingConsistency.pairing_eq_of_fine_system hL hF hT hQ hQ'
        (P := P) (by change 2 * v ≤ _; linarith) (by change 2 * v ≤ _; linarith)
        (hlarge Q hx₀s.1 hvQ) (hlarge Q' hx₀s.2 hvQ')
        ⟨hsmooth z, hPmiddle⟩ (hinclass z).1 (hinclass z).2
  obtain ⟨⟨S, hS⟩, ⟨hadd, hsmul⟩, -⟩ := hL n c a G T Q hT hQ
  obtain ⟨⟨S', hS'⟩, ⟨hadd', hsmul'⟩, -⟩ := hL n c a G T Q' hT hQ'
  have mem : ∀ Φ, Φ ∈ S ↔ Φ ∈ Q.supportedClass := fun Φ => by rw [← hS]; rfl
  have mem' : ∀ Φ, Φ ∈ S' ↔ Φ ∈ Q'.supportedClass := fun Φ => by rw [← hS']; rfl
  rw [hsumΦ,
    LocalPairingConsistency.map_finset_sum_of_linearOn S _
      (fun Φ hΦ Φ' hΦ' => hadd Φ ((mem _).1 hΦ) Φ' ((mem _).1 hΦ'))
      (fun lam Φ hΦ => hsmul lam Φ ((mem _).1 hΦ)) _ _ _
      (fun z _ => (mem _).2 (hinclass z).1),
    LocalPairingConsistency.map_finset_sum_of_linearOn S' _
      (fun Φ hΦ Φ' hΦ' => hadd' Φ ((mem' _).1 hΦ) Φ' ((mem' _).1 hΦ'))
      (fun lam Φ hΦ => hsmul' lam Φ ((mem' _).1 hΦ)) _ _ _
      (fun z _ => (mem' _).2 (hinclass z).2)]
  exact Finset.sum_congr rfl fun z _ => by rw [hone z]
end YangMills.Construction.ConfigSpace
