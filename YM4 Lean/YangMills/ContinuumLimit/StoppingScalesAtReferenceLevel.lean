import YangMills.ContinuumLimit.ReferenceOnSmallTori
import YangMills.ContinuumLimit.StoppingLevel
import YangMills.ContinuumLimit.FirstPassageOfATunedPair
import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.ReferenceCalibration
open Construction

/-- A reference level bounded away from zero precludes a stop at the bare lattice.
The number of lattice steps left after stopping diverges in physical lattice units. -/
theorem stopping_scales_at_reference_level {ι : Type*} {l : Filter ι}
    (s : Conventions.StandingParameters) (K : ι → ℕ+) (β : ι → ℝ) (x : ι → ℕ → ℝ)
    {r B c : ℝ} (hr : 0 < r) (hlevel : ∀ᶠ j in l, r ≤ referenceResponse s.L s.m (K j) (β j))
    (hinit : ∀ j, x j 0 = β j) (hhot : Tendsto (fun j => x j (K j)) l atTop)
    (hstep : ∀ᶠ j in l, ∀ i < (K j : ℕ), x j (i+1) ≤ x j i + B)
    (hdrop : ∀ᶠ j in l, ∀ i ≤ (K j : ℕ), x j (K j) - c ≤ x j i) :
    ∃ (k : ι → ℕ) (A : ℝ), 1 ≤ A ∧ (∀ j, k j ≤ (K j : ℕ)) ∧
      Tendsto (fun j => (s.L:ℝ)^((K j:ℕ)-k j)) l atTop ∧
      ∀ᶠ j in l, let q := (s.L:ℝ)^((K j:ℕ)-k j)
        0 < k j ∧ q^92 ≤ x j (k j) ∧ x j (k j) ≤ A*q^92 := by
  classical
  have hL : 1 ≤ (s.L:ℝ) := by exact_mod_cast (show 1 ≤ s.L by have := s.isAdmissible.2; omega)
  have hbase : Tendsto (fun j => x j (K j) - c) l atTop := tendsto_atTop.2 fun d =>
    (hhot.eventually_ge_atTop (d+c)).mono fun j hj => by linarith
  have hβ : Tendsto β l atTop := tendsto_atTop_mono' l
    (hdrop.mono fun j hj => (hj 0 (Nat.zero_le _)).trans_eq (hinit j))
    hbase
  let ell := 2 * (s.L:ℝ)^(s.m:ℕ)
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hbig := SmallBox.small_side_excluded_at_reference_level s K β hβ hr hlevel ell
  have hsep : ∀ᶠ j in l, β j ^ (1/92:ℝ) < (s.L:ℝ)^(K j:ℕ) := by
    filter_upwards [hbig] with j hj
    apply lt_of_mul_lt_mul_left (a:=ell) _ hell.le
    simpa [ell,pow_add,mul_assoc] using hj
  let ok (j : ι) := 1 ≤ x j (K j) ∧ ∀ i < (K j : ℕ), x j (i+1) ≤ x j i + B
  have pick j (hj : ok j) := exists_reference_stopping_scale (L:=s.L) hj.1 hj.2
  let k (j : ι) : ℕ := if h : ok j then (pick j h).choose else 0
  let q (j : ι) := (s.L:ℝ)^((K j:ℕ)-k j)
  have hq j : 1 ≤ q j := one_le_pow₀ hL
  have hle j : k j ≤ (K j:ℕ) := by
    by_cases h : ok j
    · exact (dif_pos h : k j = _).trans_le (pick j h).choose_spec.1
    · simp [k,h]
  let A := (s.L:ℝ)^92 + |B| + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg B, pow_nonneg (show (0:ℝ) ≤ s.L by positivity) 92]
  have good : ∀ᶠ j in l, 0 < k j ∧ q j^92 ≤ x j (k j) ∧ x j (k j) ≤ A*q j^92 := by
    filter_upwards [hhot.eventually_ge_atTop 1,hstep,hsep] with j hj hst sep
    have hj' : ok j := ⟨hj,hst⟩
    have hx := (pick j hj').choose_spec.2
    have hk : k j = (pick j hj').choose := dif_pos hj'
    have hh : q j^92 ≤ x j (k j) ∧ (k j=0 ∨ x j (k j) < ((s.L:ℝ)*q j)^92+B) := by
      simpa only [q, hk] using hx
    have hn : k j ≠ 0 := by
      intro hz
      have hlow := hh.1
      simp only [q,hz,Nat.sub_zero,hinit] at hlow
      have hx := Real.rpow_le_rpow (by positivity) hlow (show (0:ℝ) ≤ 1/92 by norm_num)
      rw [← Real.rpow_natCast_mul (by positivity)] at hx
      norm_num at hx
      exact sep.not_ge hx
    refine ⟨Nat.pos_of_ne_zero hn, hh.1, ((hh.2.resolve_left hn).le).trans ?_⟩
    have hq1 : 1 ≤ q j ^ 92 := one_le_pow₀ (hq j)
    rw [mul_pow]
    dsimp only [A]
    nlinarith [le_abs_self B, mul_le_mul_of_nonneg_left hq1 (abs_nonneg B)]
  have hg : Tendsto (fun j => x j (k j)) l atTop :=
    tendsto_atTop_mono' l (hdrop.mono fun j hj => hj _ (hle j)) hbase
  refine ⟨k,A,hA,hle,?_,good⟩
  apply tendsto_atTop.2
  intro d
  filter_upwards [hg.eventually_gt_atTop (A*(max d 1)^92),good] with j hj hu
  by_contra! hd
  have hpow := pow_le_pow_left₀ (zero_le_one.trans (hq j)) (hd.le.trans (le_max_left d 1)) 92
  exact hj.not_ge (hu.2.2.trans (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hA)))

end YangMills.ReferenceCalibration
namespace YangMills.ReferenceCalibration
open Construction ContinuumLimit Construction.ResponseInTheExpansion
open Construction.TheStatementsProvedTogether

/-- Stopping levels for the actual Wilson roots on a single tuned RG table. Here
the terminal values are those of the total-density flow used for tuning. -/
theorem stopping_scales_on_tuned_flow {ι : Type*} {l : Filter ι}
    {T : RenormalizationStepParameters.ParameterAssignment} {y lam cr : ℝ}
    {Kr : WeightedResponses.ResponseParameters} (H : RunTable T y Kr lam cr) (M : ℕ+)
    (K : ι → ℕ+) (β P : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hlevel : ∀ᶠ j in l, r ≤ referenceResponse T.side M (K j) (β j))
    (ht : ∀ᶠ j in l, IsTunedAt T y (P j) (K j) (β j)) (hhot : Tendsto P l atTop) :
    ∃ (k : ι → ℕ) (A : ℝ), 1 ≤ A ∧ (∀ j, k j ≤ (K j : ℕ)) ∧
      Tendsto (fun j => T.side^((K j:ℕ)-k j)) l atTop ∧
      ∀ᶠ j in l, let q := ((T.side^((K j:ℕ)-k j) : ℕ):ℝ)
        let x := flowCouplings (T.stepParameters y) (β j) (k j)
        0 < k j ∧ FreeEnergies.CouplingsAboveFloor (T.stepParameters y) (β j) (k j) ∧
        q^92 ≤ x ∧ x ≤ A*q^92 := by
  have hL : Conventions.IsAdmissibleBlockingFactor T.side := ⟨H.adm.L_odd,(by have := H.adm.L_ge; omega)⟩
  let s : Conventions.StandingParameters := ⟨T.side,hL,1,M⟩
  let x (j : ι) (i : ℕ) := flowCouplings (T.stepParameters y) (β j) i
  have heq : ∀ᶠ j in l, P j = x j (K j) := ht.mono fun j hj =>
    hj.2.symm.trans ((total_flow_of_above_total expansion_gives_total_flow total_density_flow_unique H hj.1).2 _ le_rfl)
  have hprev := ht.mono fun j hj =>
    (above_iff_total expansion_gives_total_flow total_density_flow_unique H).mp hj.1
  have hbound (j : ι) (h : Above T y (β j) (K j)) (a b : ℕ)
      (hab : a ≤ b) (hb : b ≤ (K j:ℕ)) : x j b - cr ≤ x j a := by
    have h' := H.descent (β j) h.1 b (fun i hi => h.2 i (hi.trans_le hb)) a hab
    change lam * ((b:ℝ)-(a:ℝ))-cr ≤ x j a - x j b at h'
    have hn : 0 ≤ (b:ℝ)-(a:ℝ) := sub_nonneg.mpr (by exact_mod_cast hab)
    linarith [mul_nonneg H.lam_pos.le hn]
  have hstep : ∀ᶠ j in l, ∀ i < (K j:ℕ), x j (i+1) ≤ x j i + cr := by
    filter_upwards [hprev] with j hj i hi
    linarith [hbound j hj i (i+1) (Nat.le_succ i) (by omega)]
  have hdrop : ∀ᶠ j in l, ∀ i ≤ (K j:ℕ), x j (K j) - cr ≤ x j i :=
    hprev.mono fun j hj i hi => hbound j hj i _ hi le_rfl
  obtain ⟨k,A,hA,hk,hq,hgj⟩ := stopping_scales_at_reference_level s K β x hr hlevel
    (fun _ => rfl) (hhot.congr' heq) hstep hdrop
  refine ⟨k,A,hA,hk,?_,?_⟩
  · apply tendsto_atTop.2
    intro d
    filter_upwards [hq.eventually_ge_atTop (d:ℝ)] with j hj
    change (d:ℝ) ≤ (T.side:ℝ)^((K j:ℕ)-k j) at hj
    exact_mod_cast hj
  · filter_upwards [hgj,hprev,(hhot.congr' heq).eventually_ge_atTop y] with j hj hp hterm
    refine ⟨hj.1,?_,?_,?_⟩
    · intro i hi
      rcases lt_or_eq_of_le (hi.trans (hk j)) with h | rfl
      · exact hp.2 i h
      · exact hterm
    · change ((T.side^((K j:ℕ)-k j):ℕ):ℝ)^92 ≤ x j (k j)
      push_cast
      exact hj.2.1
    · change x j (k j) ≤ A*((T.side^((K j:ℕ)-k j):ℕ):ℝ)^92
      push_cast
      exact hj.2.2

theorem stopping_scales_on_tuned_flow_nat {ι : Type*} {l : Filter ι}
    {T : RenormalizationStepParameters.ParameterAssignment} {y lam cr : ℝ}
    {Kr : WeightedResponses.ResponseParameters} (H : RunTable T y Kr lam cr) (M : ℕ+)
    (K : ι → ℕ) (β P : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hK : ∀ᶠ j in l, 0 < K j) (hlevel : ∀ᶠ j in l, r ≤ referenceResponse T.side M (K j) (β j))
    (ht : ∀ᶠ j in l, IsTunedAt T y (P j) (K j) (β j)) (hhot : Tendsto P l atTop) :
    ∃ (k : ι → ℕ) (A : ℝ), 1 ≤ A ∧ (∀ j, k j ≤ (K j)) ∧
      Tendsto (fun j => T.side^((K j)-k j)) l atTop ∧
      ∀ᶠ j in l, let q := ((T.side^((K j)-k j) : ℕ):ℝ)
        let x := flowCouplings (T.stepParameters y) (β j) (k j)
        0 < k j ∧ FreeEnergies.CouplingsAboveFloor (T.stepParameters y) (β j) (k j) ∧
        q^92 ≤ x ∧ x ≤ A*q^92 := by
  let K' (j : ι) := (K j).toPNat'
  have he : ∀ᶠ j in l, (K' j:ℕ) = K j := hK.mono fun j hj => PNat.toPNat'_coe hj
  have hlevel' : ∀ᶠ j in l, r ≤ referenceResponse T.side M (K' j) (β j) := by
    filter_upwards [he,hlevel] with j ej hj; simpa [ej] using hj
  have ht' : ∀ᶠ j in l, IsTunedAt T y (P j) (K' j) (β j) := by
    filter_upwards [he,ht] with j ej hj; simpa [ej] using hj
  obtain ⟨k,A,hA,hk,hq,hgj⟩ := stopping_scales_on_tuned_flow H M K' β P hr hlevel' ht' hhot
  let k' (j : ι) := min (k j) (K j)
  have hek : ∀ᶠ j in l, k' j = k j := by
    filter_upwards [he] with j ej
    exact min_eq_left ((hk j).trans_eq ej)
  refine ⟨k',A,hA,fun j => min_le_right ..,hq.congr' ?_,?_⟩
  · filter_upwards [he,hek] with j hj ej; rw [ej,hj]
  · filter_upwards [he,hek,hgj] with j hj ej hg; simpa only [hj,ej] using hg

end YangMills.ReferenceCalibration
