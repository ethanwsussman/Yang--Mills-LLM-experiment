import YangMills.Construction.HilbertSpaces.LimitsSeriesIntegralsAndTheLogarithmOfBoundedOperatorsProof
import YangMills.Construction.Towers.DifferenceOfTheLogarithmicDensitiesAsAnIntegralProof
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory YangMills.Construction.OneLoopNotation YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.BoundedTraceProof
section Riemann
theorem sum_succ_sub_castSucc {E : Type} [AddCommGroup E] (n : ℕ) (f : Fin (n + 1) → E) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by apply _root_.YangMills.Construction.OperatorCalculus.sum_fin_succ_sub_castSucc <;> assumption
theorem norm_markedSum_sub_integral_le {g : ℝ → ℂ} {a b υ ε : ℝ} (hg : ContinuousOn g (Icc a b))
    (hu : ∀ w ∈ Icc a b, ∀ w' ∈ Icc a b, |w - w'| ≤ υ → ‖g w - g w'‖ ≤ ε)
    (P : MarkedPartition a b)
    (hmesh : ∀ i : Fin P.card, P.node i.succ - P.node i.castSucc ≤ υ) :
    ‖P.sum g - ∫ w in a..b, g w‖ ≤ ε * (b - a) := by
  have hmem : ∀ i, P.node i ∈ Icc a b := fun i =>
    ⟨P.node_zero.ge.trans (P.node_mono (Fin.zero_le i)),
      (P.node_mono (Fin.le_last i)).trans P.node_last.le⟩
  have hab : a ≤ b := (hmem 0).1.trans (hmem 0).2
  have hint : ∀ c ∈ Icc a b, ∀ d ∈ Icc a b, IntervalIntegrable g volume c d := fun c hc d hd =>
    (hg.intervalIntegrable_of_Icc hab).mono_set (by rw [uIcc_of_le hab]; exact uIcc_subset_Icc hc hd)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hpiece : ∀ i : Fin P.card,
      ‖(P.node i.succ - P.node i.castSucc) • g (P.sample i) -
          ((∫ w in a..P.node i.succ, g w) - ∫ w in a..P.node i.castSucc, g w)‖ ≤
        ε * (P.node i.succ - P.node i.castSucc) := by
    intro i
    have hc := hmem i.castSucc
    have hd := hmem i.succ
    have hcd : P.node i.castSucc ≤ P.node i.succ := P.node_mono Fin.castSucc_lt_succ.le
    have ht := P.sample_mem i
    have htm : P.sample i ∈ Icc a b := ⟨hc.1.trans ht.1, ht.2.trans hd.2⟩
    rw [intervalIntegral.integral_interval_sub_left (hint a ha _ hd) (hint a ha _ hc)]
    have e : (P.node i.succ - P.node i.castSucc) • g (P.sample i) -
        ∫ w in P.node i.castSucc..P.node i.succ, g w =
        ∫ w in P.node i.castSucc..P.node i.succ, (g (P.sample i) - g w) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint _ hc _ hd),
        intervalIntegral.integral_const]
    rw [e]
    have hb : ‖∫ w in P.node i.castSucc..P.node i.succ, (g (P.sample i) - g w)‖ ≤
        ε * |P.node i.succ - P.node i.castSucc| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun w hw => ?_
      rw [uIoc_of_le hcd] at hw
      refine hu _ htm w ⟨hc.1.trans hw.1.le, hw.2.trans hd.2⟩ ?_
      have := hmesh i
      rw [abs_le]
      constructor <;> linarith [hw.1, hw.2, ht.1, ht.2]
    rwa [abs_of_nonneg (sub_nonneg.2 hcd)] at hb
  have hI : ∫ w in a..b, g w = ∑ i : Fin P.card,
      ((∫ w in a..P.node i.succ, g w) - ∫ w in a..P.node i.castSucc, g w) := by
    rw [sum_succ_sub_castSucc P.card (fun i => ∫ w in a..P.node i, g w)]
    simp [P.node_last, P.node_zero]
  rw [hI, MarkedPartition.sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hpiece i).trans ?_)
  rw [← Finset.mul_sum, sum_succ_sub_castSucc P.card P.node, P.node_last, P.node_zero]
theorem exists_markedPartition_fineness_le {a b υ : ℝ} (hab : a < b) (hυ : 0 < υ) :
    ∃ P : MarkedPartition a b, 1 ≤ P.card ∧ StrictMono P.node ∧
      ∀ i : Fin P.card, P.node i.succ - P.node i.castSucc ≤ υ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / υ)
  have hd : 0 < b - a := sub_pos.2 hab
  have hN0 : (0 : ℝ) < N := (div_pos hd hυ).trans hN
  have hNn : 1 ≤ N := by exact_mod_cast hN0
  have hstep : 0 < (b - a) / N := div_pos hd hN0
  have hle : (b - a) / N ≤ υ := by
    rw [div_lt_iff₀ hυ] at hN
    rw [div_le_iff₀ hN0]
    linarith [mul_comm υ (N : ℝ)]
  have hmono : StrictMono fun i : Fin (N + 1) => a + ((i : ℕ) : ℝ) * ((b - a) / N) := by
    intro i j hij
    have h1 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    have h2 := mul_lt_mul_of_pos_right h1 hstep
    simp only
    linarith
  refine ⟨⟨N, fun i => a + ((i : ℕ) : ℝ) * ((b - a) / N),
    fun i => a + ((i.castSucc : Fin (N + 1)) : ℕ) * ((b - a) / N), hmono.monotone, by simp, ?_,
    fun i => ⟨le_rfl, hmono.monotone Fin.castSucc_lt_succ.le⟩⟩, hNn, hmono, fun i => ?_⟩
  · simp only [Fin.val_last]
    field_simp
    ring
  · simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    linarith
end Riemann
section Functional
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem continuousOn_of_normContinuousOn {T : ℝ → BddOp H} {m m' : ℝ}
    (h : NormContinuousOn T m m') : ContinuousOn T (Icc m m') := by apply _root_.YangMills.Construction.OperatorCalculus.continuousOn_of_normContinuousOn <;> assumption
theorem continuousOn_Ici_of_normContinuousOn {T : ℝ → BddOp H}
    (h : ∀ m : ℝ, 0 < m → NormContinuousOn T 0 m) : ContinuousOn T (Ici 0) := by apply _root_.YangMills.Construction.Tower.LocalFamilies.LogTraceDiff.continuousOn_Ici_of_normContinuousOn <;> assumption
theorem isBoundedLinearTrace_of_entries {I : Type} {S : Set I} (hS : S.Finite) {𝔑 : ℕ}
    (hc : S.ncard = 𝔑) (v : I → BddOp H → ℂ)
    (hadd : ∀ ι T T' (s : ℂ), v ι (T + s • T') = v ι T + s * v ι T')
    (hb : ∀ ι T, ‖v ι T‖ ≤ ‖T‖) (h1 : ∀ ι, v ι (ContinuousLinearMap.id ℂ H) = 1) :
    IsBoundedLinearTrace (fun T => ∑ᶠ ι ∈ S, v ι T) 𝔑 := by
  have e : ∀ T, ∑ᶠ ι ∈ S, v ι T = ∑ ι ∈ hS.toFinset, v ι T := fun T =>
    finsum_mem_eq_finite_toFinset_sum _ hS
  have hcard : hS.toFinset.card = 𝔑 := by rw [← hc, Set.ncard_eq_toFinset_card S hS]
  refine ⟨fun T T' s => ?_, fun T => ?_, ?_⟩
  · show ∑ᶠ ι ∈ S, v ι (T + s • T') = ∑ᶠ ι ∈ S, v ι T + s * ∑ᶠ ι ∈ S, v ι T'
    rw [e, e, e]
    simp only [hadd, Finset.sum_add_distrib, Finset.mul_sum]
  · show ‖∑ᶠ ι ∈ S, v ι T‖ ≤ (𝔑 : ℝ) * ‖T‖
    rw [e]
    calc ‖∑ ι ∈ hS.toFinset, v ι T‖ ≤ ∑ ι ∈ hS.toFinset, ‖v ι T‖ := norm_sum_le _ _
      _ ≤ ∑ _ι ∈ hS.toFinset, ‖T‖ := Finset.sum_le_sum fun ι _ => hb ι T
      _ = (𝔑 : ℝ) * ‖T‖ := by simp [hcard]
  · show ∑ᶠ ι ∈ S, v ι (ContinuousLinearMap.id ℂ H) = (𝔑 : ℂ)
    rw [e]
    simp only [h1]
    simp [hcard]
variable [CompleteSpace H]
omit [CompleteSpace H] in
theorem map_opIntegral (hE : CompactIntervalIntegral H)
    (τ : BddOp H →L[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ A, ‖τ A‖ ≤ C * ‖A‖)
    {T : ℝ → BddOp H} {m : ℝ} (hm : 0 < m) (hc : NormContinuousOn T 0 m) :
    τ (opIntegral T 0 m) = ∫ w in (0 : ℝ)..m, τ (T w) := by
  obtain ⟨-, -, hX, -⟩ := hE 0 m T hm hc
  have hg : ContinuousOn (fun w => τ (T w)) (Icc 0 m) :=
    τ.continuous.comp_continuousOn (continuousOn_of_normContinuousOn hc)
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hg
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨δ, hδ, hδe⟩ : ∃ δ : ℝ, 0 < δ ∧ (C + 1) * δ = ε :=
    ⟨ε / (C + 1), div_pos hε hC1, by field_simp⟩
  obtain ⟨υ₁, hυ₁, hR⟩ := hX δ hδ
  obtain ⟨υ₂, hυ₂, hv⟩ := Metric.uniformContinuousOn_iff.1 hu (δ / m) (div_pos hδ hm)
  obtain ⟨P, hP1, hPs, hPm⟩ := exists_markedPartition_fineness_le hm
    (lt_min hυ₁ (half_pos hυ₂))
  have hclose := hR (P.sum T)
    ⟨P, hP1, hPs, fun i => (hPm i).trans (min_le_left _ _), rfl⟩
  have hsum := norm_markedSum_sub_integral_le (g := fun w => τ (T w)) (υ := υ₂ / 2) (ε := δ / m) hg
    (fun w hw w' hw' hd => by
      have h1 := hv w hw w' hw' (by rw [Real.dist_eq]; linarith [half_lt_self hυ₂])
      rw [dist_eq_norm] at h1
      exact h1.le) P (fun i => (hPm i).trans (min_le_right _ _))
  rw [sub_zero, div_mul_cancel₀ _ hm.ne'] at hsum
  have hmap : τ (P.sum T) = P.sum fun w => τ (T w) := by
    simp only [MarkedPartition.sum, map_sum, ContinuousLinearMap.map_smul_of_tower]
  have hdiff : ‖τ (opIntegral T 0 m - P.sum T)‖ ≤ C * δ := by
    refine (hb _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rwa [norm_sub_rev]
  have hsplit : τ (opIntegral T 0 m) - ∫ w in (0 : ℝ)..m, τ (T w) =
      τ (opIntegral T 0 m - P.sum T) +
        ((P.sum fun w => τ (T w)) - ∫ w in (0 : ℝ)..m, τ (T w)) := by
    rw [map_sub, hmap]
    ring
  rw [hsplit, zero_add, ← hδe]
  refine (norm_add_le _ _).trans ?_
  linarith
omit [CompleteSpace H] in
theorem commutesWithIntegral_of_clm (hE : CompactIntervalIntegral H)
    (hF : HalfLineIntegral H) (τ : BddOp H →L[ℂ] ℂ) (𝔑 : ℕ)
    (hb : ∀ A, ‖τ A‖ ≤ (𝔑 : ℝ) * ‖A‖) : CommutesWithIntegral (fun A => τ A) 𝔑 := by
  intro T hc hl
  have hl' : IntegrableOnHalfLine (fun w => ‖T w‖) := by
    obtain ⟨l, h⟩ := hl
    exact ⟨l, by simpa only [abs_norm] using h⟩
  obtain ⟨X, hX, -⟩ := hF T hc hl'
  have hlim : TendstoInOpNorm atTop (fun m : ℝ => opIntegral T 0 m)
      (opIntegralIoi T) :=
    Classical.epsilon_spec
      (p := fun X => TendstoInOpNorm atTop (fun m : ℝ => opIntegral T 0 m) X)
      ⟨X, hX⟩
  have hint : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, τ (T w)) atTop
      (nhds (τ (opIntegralIoi T))) := by
    have h1 : Tendsto (fun y : ℝ => τ (opIntegral T 0 y)) atTop
        (nhds (τ (opIntegralIoi T))) :=
      (τ.continuous.tendsto _).comp hlim
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    exact map_opIntegral hE τ (Nat.cast_nonneg 𝔑) hb hy (hc y hy)
  have hspec : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, τ (T w)) atTop
      (nhds (complexIntegralIoi fun w => τ (T w))) :=
    Classical.epsilon_spec
      (p := fun c => Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, τ (T w)) atTop (nhds c)) ⟨_, hint⟩
  exact ⟨fun m hm => (hE 0 m T hm (hc m hm)).2.2.1, hlim,
    τ.continuous.comp_continuousOn (continuousOn_Ici_of_normContinuousOn hc),
    fun w _ => hb _, hspec, tendsto_nhds_unique hint hspec⟩
theorem and_commutesWithIntegral (hL : YangMills.Construction.OperatorCalculus.Calculus.Statement)
    {τ : BddOp H → ℂ} {𝔑 : ℕ} (h : IsBoundedLinearTrace τ 𝔑) :
    IsBoundedLinearTrace τ 𝔑 ∧ CommutesWithIntegral τ 𝔑 := by
  obtain ⟨-, -, -, -, hE, hF, -⟩ := hL H H
  obtain ⟨hadd, hb, -⟩ := id h
  have h0 : τ 0 = 0 := by
    have h1 := hb 0
    simpa using h1
  let τL : BddOp H →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := τ
      map_add' := fun A B => by
        have h1 := hadd A B 1
        simpa using h1
      map_smul' := fun s A => by
        have h1 := hadd 0 A s
        simpa [h0] using h1 } (𝔑 : ℝ) hb
  exact ⟨h, commutesWithIntegral_of_clm hE hF τL 𝔑 hb⟩
end Functional
theorem isBoundedLinearTrace_traceAt {J : Type} (hE : MatrixEntryProperties J)
    (position : J → InfiniteLattice.AmbientSpace) (x : InfiniteLattice.AmbientSpace)
    (hS : {ι | position ι = x}.Finite) {𝔑 : ℕ} (hc : {ι | position ι = x}.ncard = 𝔑) :
    IsBoundedLinearTrace (fun T => traceAt position T x) 𝔑 :=
  isBoundedLinearTrace_of_entries hS hc (fun ι T => matrixEntry T ι ι)
    (fun ι T T' s => by simp only [matrixEntry, _root_.add_apply, _root_.smul_apply]; rfl)
    (fun ι T => ((hE T).1 ι ι).2)
    (fun ι => by simp [matrixEntry, basisVec])
theorem isBoundedLinearTrace_vecTraceAt {L N' : ℕ} (x : FullSpace.Vertex L 0 0) :
    IsBoundedLinearTrace (fun T : BddOp (VectorL2 L N') => vecTraceAt T x) N' := by
  have hset : {ι : Fin N' × FullSpace.Vertex L 0 0 | ι.2 = x} =
      (fun l : Fin N' => (l, x)) '' Set.univ := by
    ext ⟨l, y⟩
    simp [eq_comm]
  have hinj : Function.Injective fun l : Fin N' => ((l, x) : Fin N' × FullSpace.Vertex L 0 0) :=
    fun l l' h => (Prod.ext_iff.1 h).1
  have hunit : ∀ ι : Fin N' × FullSpace.Vertex L 0 0, ‖vecDelta ι‖ = 1 := by
    intro ι
    simp [vecDelta, lp.norm_single]
  have hval : ∀ (w : VectorL2 L N') (ι : Fin N' × FullSpace.Vertex L 0 0),
      ‖vecCoord w ι‖ ≤ ‖w‖ := fun w ι =>
    (PiLp.norm_apply_le (w ι.2) ι.1).trans (lp.norm_apply_le_norm (by norm_num) w ι.2)
  refine isBoundedLinearTrace_of_entries (S := {ι : Fin N' × FullSpace.Vertex L 0 0 | ι.2 = x})
    (by rw [hset]; exact Set.finite_univ.image _) ?_
    (fun ι T => vecCoord (T (vecDelta ι)) ι) (fun ι T T' s => by
      simp only [vecCoord, _root_.add_apply, _root_.smul_apply]; rfl)
    (fun ι T => ?_) (fun ι => by simp [vecCoord, vecDelta])
  · rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_fin]
  · refine (hval _ ι).trans ((T.le_opNorm _).trans ?_)
    rw [hunit, mul_one]
theorem traceIsBoundedLinear_holds (hSpaces : UnitLatticeL2Statement)
    (hCalculus : YangMills.Construction.OperatorCalculus.Calculus.Statement) :
    TraceIsBoundedLinear := by
  intro L x
  obtain ⟨-, ⟨-, -, -, hSites, hSiteCoords, -⟩, ⟨-, -, -, hBonds, hBondCoords, -⟩⟩ := hSpaces.2 L
  refine ⟨and_commutesWithIntegral hCalculus ?_, and_commutesWithIntegral hCalculus ?_, fun N' _ =>
    and_commutesWithIntegral hCalculus (isBoundedLinearTrace_vecTraceAt x)⟩
  · refine isBoundedLinearTrace_traceAt hSiteCoords _ _ ?_ ?_
    · rw [(hSites.1 x).1]
      exact Set.finite_range _
    · rw [(hSites.1 x).1]
      exact (hSites.1 x).2
  · refine isBoundedLinearTrace_traceAt hBondCoords _ _ ?_ ?_
    · rw [(hBonds.1 x).1]
      exact Set.finite_range _
    · rw [(hBonds.1 x).1]
      exact (hBonds.1 x).2
end YangMills.Construction.Tower.AbelianFieldDensity.BoundedTraceProof
end
