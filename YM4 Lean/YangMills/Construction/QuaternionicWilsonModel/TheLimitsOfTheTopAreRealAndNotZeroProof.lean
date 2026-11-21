import YangMills.Construction.InfiniteLattice.MultilinearityOfTheConnectedCurvatureFunctions
import YangMills.Construction.QuaternionicWilsonModel.TheLimitsOfTheTopAreRealAndNotZero
import YangMills.Construction.Torus.GeometryTransportLiftAndDilationOfTestPairs
import YangMills.Construction.Torus.LipschitzTuplesWithDisjointSupportsOnATorus
import YangMills.Construction.TotalDensitiesGiveASystem.TheTopOfTheTrajectory
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero
theorem tendsto_pnat_coe_atTop {K : ℕ+ → ℕ+} (hK : Tendsto K atTop atTop) :
    Tendsto (fun j => (K j : ℕ)) atTop atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hK ⟨b + 1, by omega⟩).mono fun j hj => by
    have hb : b + 1 ≤ (K j : ℕ) := hj
    omega
theorem tendsto_atTop_of_coe {K : ℕ+ → ℕ+} (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop) :
    Tendsto K atTop atTop :=
  tendsto_atTop.2 fun b => (hK.eventually_ge_atTop (b : ℕ)).mono fun _ hj => hj
theorem tendsto_of_strictMono_pnat {φ : ℕ+ → ℕ+} (hφ : StrictMono φ) : Tendsto φ atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b, fun _ ha => ha.trans hφ.le_apply⟩
theorem log_inv_meshSize {L : ℕ} (hL : 0 < L) (K : ℕ) :
    Real.log (1 / PeriodicLattice.meshSize L (K : ℤ)) = K * Real.log L := by
  simp [PeriodicLattice.meshSize, Real.log_pow, zpow_neg]
theorem asymptoticFreedomSlope_pos : 0 < SystemsWithFiveBounds.asymptoticFreedomSlope := by
  unfold SystemsWithFiveBounds.asymptoticFreedomSlope
  positivity
section Couplings
variable {ℓ : TorusLumps.StepParameters} {Bs c₅ lam CT g : ℝ} {Nw : ℕ}
theorem tendsto_coupling_atTop (hL : 2 ≤ ℓ.side) (hc : TotalDensitySystem.CouplingConditions ℓ Bs c₅ lam Nw CT g)
    (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (hp : ∀ j, TotalDensitySystem.IsFirstPassagePair ℓ Bs g (K j) (β j))
    (hK : Tendsto K atTop atTop) : Tendsto β atTop atTop := by
  have hK' := tendsto_pnat_coe_atTop hK
  obtain ⟨δ, hδ, hb⟩ := hc.passage.asymptotically_free
  have hratio : Tendsto (fun j => β j / Real.log (1 / PeriodicLattice.meshSize ℓ.side (((K j : ℕ) : ℕ) : ℤ))) atTop
      (𝓝 SystemsWithFiveBounds.asymptoticFreedomSlope) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => hb _ _ (K j).2 (hp j)) (hδ.comp hK')
  have hlogL : 0 < Real.log ℓ.side := Real.log_pos (by exact_mod_cast (by omega : 1 < ℓ.side))
  have hden : Tendsto (fun j => Real.log (1 / PeriodicLattice.meshSize ℓ.side (((K j : ℕ) : ℕ) : ℤ))) atTop atTop := by
    have e : (fun j => Real.log (1 / PeriodicLattice.meshSize ℓ.side (((K j : ℕ) : ℕ) : ℤ))) =
        fun j => ((K j : ℕ) : ℝ) * Real.log ℓ.side := by
      funext j
      exact log_inv_meshSize (by omega) _
    rw [e]
    exact (tendsto_natCast_atTop_atTop.comp hK').atTop_mul_const hlogL
  refine (hden.atTop_mul_pos asymptoticFreedomSlope_pos hratio).congr' ?_
  filter_upwards [hden.eventually_gt_atTop 0] with j hj
  field_simp
theorem exists_firstPassagePairs (hc : TotalDensitySystem.CouplingConditions ℓ Bs c₅ lam Nw CT g) :
    ∃ (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, TotalDensitySystem.IsFirstPassagePair ℓ Bs g (K j) (β j)) ∧
      Tendsto K atTop atTop := by
  have hex : ∀ j : ℕ+, ∃ K : ℕ+, (j : ℕ) < (K : ℕ) ∧ ∃ β, TotalDensitySystem.IsFirstPassagePair ℓ Bs g K β :=
    fun j => by
      obtain ⟨K, h1, -, β, hβ⟩ := hc.passage.windows_recur j
      exact ⟨⟨K, by have := j.pos; omega⟩, h1, β, hβ⟩
  choose K hK hβ using hex
  choose β hβ using hβ
  refine ⟨K, β, hβ, tendsto_atTop.2 fun b => ?_⟩
  filter_upwards [eventually_ge_atTop b] with j hj
  exact (PNat.coe_le_coe _ _).1 ((PNat.coe_le_coe _ _).2 hj |>.trans (hK j).le)
end Couplings
theorem torusSide_mono {L : ℕ} (hL : 1 ≤ L) {a b : ℕ} (hab : a ≤ b) :
    PeriodicLattice.torusSide L a ≤ PeriodicLattice.torusSide L b := by
  unfold PeriodicLattice.torusSide
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 := pow_le_pow_right₀ h1 hab
  linarith
theorem eventually_lt_torusSide {L : ℕ} (hL : 2 ≤ L) {m : ℕ+ → ℕ+} (hm : Tendsto m atTop atTop) (b : ℝ) :
    ∀ᶠ j in atTop, b < PeriodicLattice.torusSide L (m j) := by
  have h1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have h2 : Tendsto (fun k : ℕ => (L : ℝ) ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt h1
  filter_upwards [(h2.comp (tendsto_pnat_coe_atTop hm)).eventually_gt_atTop b] with j hj
  have h3 : 0 < (L : ℝ) ^ ((m j : ℕ)) := by positivity
  have h4 : b < (L : ℝ) ^ ((m j : ℕ)) := hj
  unfold PeriodicLattice.torusSide
  linarith
theorem torusUrsellFunction_im_eq_zero (hMul : TorusCumulants.Multilinearity.claim)
    (s : Conventions.StandingParameters) {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 1 ≤ n) (h : Fin n → s.Torus → ℝ)
    (hb : ∀ i, TestFunctions.IsBoundedFun (h i)) :
    (PeriodicLattice.torusUrsellFunction s.L s.m s.K β h).im = 0 := by
  obtain ⟨hcum, hall⟩ := hMul
  obtain ⟨hprob, hrv, heq⟩ := (hall s β n hβ hn).1 h hb
  have := hprob
  have hr := (hcum _ (LatticeProbability.gibbsMeasureOn s β) n ⟨0, hn⟩ _ _ _ 1 0 hrv (hrv ⟨0, hn⟩) (hrv ⟨0, hn⟩)
    (by funext x; simp)).1
  show (TorusCumulants.cumulantFunctional s.L s.m s.K β h).im = 0
  rw [heq]
  exact hr
theorem isBoundedFun_of_isC1Torus {ℓ : ℝ} (hℓ : 0 < ℓ) {f : TorusMetric.Torus4 ℓ → ℝ}
    (hf : TestFunctions.IsC1Torus f) : TestFunctions.IsBoundedFun f := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  have hcont : Continuous (f ∘ TorusMetric.torusProj ℓ) := hf.continuous
  have hcpt : IsCompact (Set.pi univ fun _ : Fin 4 => Icc (0 : ℝ) ℓ) := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun x => ?_⟩
  have hx : ∀ μ, ∃ y ∈ Icc (0 : ℝ) ℓ, (y : AddCircle ℓ) = x μ := by
    intro μ
    have himg := AddCircle.coe_image_Icc_eq ℓ (0 : ℝ)
    rw [zero_add] at himg
    have hmem : x μ ∈ ((↑) : ℝ → AddCircle ℓ) '' Icc 0 ℓ := by rw [himg]; exact mem_univ _
    obtain ⟨y, hy, e⟩ := hmem
    exact ⟨y, hy, e⟩
  choose v hv hvx using hx
  have e : TorusMetric.torusProj ℓ v = x := funext hvx
  rw [← e]
  exact hC v fun μ _ => hv μ
theorem isBoundedFun_periodize {f : (Fin 4 → ℝ) → ℝ} {R C ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ : 2 * R < ℓ)
    (hR : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) (hC : ∀ x, ‖f x‖ ≤ C) (hC0 : 0 ≤ C) :
    TestFunctions.IsBoundedFun (TestFunctions.periodize ℓ f) := by
  refine ⟨C, fun x => ?_⟩
  show ‖TestFunctions.periodicSum ℓ f (TestFunctions.liftPoint x)‖ ≤ C
  unfold TestFunctions.periodicSum
  generalize TestFunctions.liftPoint x = v
  by_cases hex : ∃ k, f (v + TestFunctions.latticeTranslate ℓ k) ≠ 0
  · obtain ⟨k, hk⟩ := hex
    rw [tsum_eq_single k]
    · exact hC _
    · intro k' hk'
      by_contra hne
      apply hk'
      funext μ
      have a1 := abs_le.1 ((Real.norm_eq_abs _).symm.le.trans
        ((norm_le_pi_norm (v + TestFunctions.latticeTranslate ℓ k) μ).trans (hR _ hk)))
      have a2 := abs_le.1 ((Real.norm_eq_abs _).symm.le.trans
        ((norm_le_pi_norm (v + TestFunctions.latticeTranslate ℓ k') μ).trans (hR _ hne)))
      simp only [Pi.add_apply, TestFunctions.latticeTranslate] at a1 a2
      have h3 : |ℓ * ((k' μ : ℝ) - (k μ : ℝ))| ≤ 2 * R :=
        abs_le.2 ⟨by linarith [a1.1, a1.2, a2.1, a2.2], by linarith [a1.1, a1.2, a2.1, a2.2]⟩
      rw [abs_mul, abs_of_pos hℓ0] at h3
      have h4 : |(k' μ : ℝ) - (k μ : ℝ)| < 1 := by
        by_contra hh
        nlinarith
      have h5 : |k' μ - k μ| < 1 := by exact_mod_cast h4
      have h6 := Int.abs_lt_one_iff.1 h5
      omega
  · have h0 : ∀ k, f (v + TestFunctions.latticeTranslate ℓ k) = 0 := fun k => by
      by_contra hk
      exact hex ⟨k, hk⟩
    simp [h0, hC0]
theorem exists_radius_and_bound {f : (Fin 4 → ℝ) → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ R C : ℝ, 0 ≤ C ∧ (∀ x, f x ≠ 0 → ‖x‖ ≤ R) ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hs.norm
  obtain ⟨R, hR⟩ := (IsCompact.isBounded hs).subset_closedBall (0 : Fin 4 → ℝ)
  refine ⟨R, C, (norm_nonneg _).trans (hC ⟨0, rfl⟩), fun x hx => ?_, fun x => hC ⟨x, rfl⟩⟩
  exact mem_closedBall_zero_iff.1 (hR (subset_tsupport f hx))
section RealLimits
variable {ℓ : TorusLumps.StepParameters} {Bs c₅ lam CT g : ℝ} {Nw : ℕ}
theorem oneTorusValues_real (hMul : TorusCumulants.Multilinearity.claim)
    (hB : Conventions.IsAdmissibleBlockingFactor ℓ.side) (hL : 2 ≤ ℓ.side)
    (hc : TotalDensitySystem.CouplingConditions ℓ Bs c₅ lam Nw CT g) : OneTorusValuesReal ℓ Bs g := by
  intro m K β hp hK n hn X hC1 _ z hz
  have hβ := tendsto_coupling_atTop hL hc K β hp hK
  have hs : 0 < PeriodicLattice.torusSide ℓ.side m := by
    unfold PeriodicLattice.torusSide
    positivity
  have him : ∀ᶠ j in atTop, (PeriodicLattice.torusUrsellFunction ℓ.side m (K j) (β j) X).im = 0 := by
    filter_upwards [hβ.eventually_gt_atTop 0] with j hj
    exact torusUrsellFunction_im_eq_zero hMul ⟨ℓ.side, hB, K j, m⟩ hj (by omega) X fun i =>
      isBoundedFun_of_isC1Torus hs (hC1 i)
  exact tendsto_nhds_unique ((Complex.continuous_im.tendsto z).comp hz)
    (tendsto_const_nhds.congr' (him.mono fun j h => h.symm))
theorem growingToriValues_real (hMul : TorusCumulants.Multilinearity.claim)
    (hB : Conventions.IsAdmissibleBlockingFactor ℓ.side) (hL : 2 ≤ ℓ.side)
    (hc : TotalDensitySystem.CouplingConditions ℓ Bs c₅ lam Nw CT g) : GrowingToriValuesReal ℓ Bs g := by
  intro K m β hp hK hm n hn X z hz
  have hβ := tendsto_coupling_atTop hL hc K β hp hK
  have hb : ∀ i, ∃ R C : ℝ, 0 ≤ C ∧ (∀ x, X.1 i x ≠ 0 → ‖x‖ ≤ R) ∧ ∀ x, ‖X.1 i x‖ ≤ C := fun i =>
    exists_radius_and_bound (X.2.1 i).1.continuous (X.2.1 i).2.1
  choose R C hC0 hR hC using hb
  have hside : ∀ᶠ j in atTop, ∀ i, max 0 (2 * R i) < PeriodicLattice.torusSide ℓ.side (m j) :=
    eventually_all.2 fun i => eventually_lt_torusSide hL hm _
  have him : ∀ᶠ j in atTop, (PeriodicLattice.torusUrsellFunction ℓ.side (m j) (K j) (β j)
      (fun i => TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side (m j)) (X.1 i))).im = 0 := by
    filter_upwards [hβ.eventually_gt_atTop 0, hside] with j hj hsj
    exact torusUrsellFunction_im_eq_zero hMul ⟨ℓ.side, hB, K j, m j⟩ hj (by omega) _ fun i =>
      isBoundedFun_periodize (lt_of_le_of_lt (le_max_left _ _) (hsj i)) (lt_of_le_of_lt (le_max_right _ _) (hsj i))
        (hR i) (hC i) (hC0 i)
  exact tendsto_nhds_unique ((Complex.continuous_im.tendsto z).comp hz)
    (tendsto_const_nhds.congr' (him.mono fun j h => h.symm))
theorem existsSubseqFamilyOnTorus_holds (hLip : TorusLipschitzTuples.TorusLipschitzTupleFacts)
    (hMul : TorusCumulants.Multilinearity.claim) (hL : 2 ≤ ℓ.side)
    (hc : TotalDensitySystem.CouplingConditions ℓ Bs c₅ lam Nw CT g) : ExistsSubseqFamilyOnTorus ℓ Bs g := by
  intro s hs K β hp hK
  obtain ⟨L0, hB, K0, m0⟩ := s
  simp only at hs
  subst hs
  obtain ⟨φ, hφ, hlim⟩ := hc.torusLimits m0 K β hp hK
  have hKφ : Tendsto (fun j => K (φ j)) atTop atTop := hK.comp (tendsto_of_strictMono_pnat hφ)
  have hreal := oneTorusValues_real hMul hB hL hc
  let s : Conventions.StandingParameters := ⟨ℓ.side, hB, K0, m0⟩
  have key : ∀ (n : ℕ) (hn : 2 ≤ n) (X : AmbientPoints.separatedTuples s .torus n), ∃ z : ℝ,
      Tendsto (fun j => SchwingerFunctions.connectedSchwinger s.L s.m (K (φ j)) (β (φ j)) X.1) atTop
        (𝓝 (z : ℂ)) := by
    intro n hn X
    have hlist : TorusLipschitzTuples.componentList s X.1 ∈ ReflectionPositivity.TorusTuples.disjointC1Tuples s n := by
      rw [((hLip s).2.2.2.2.2.2.1 n (by omega)).2.1]
      exact ⟨X.1, X.2, rfl⟩
    obtain ⟨f, hf, hfe⟩ := (hLip s).2.2.2.1 n hn hlist
    have hfX : f = X.1 := List.ofFn_injective hfe
    rw [hfX] at hf
    have hU := hf
    rw [(hLip s).2.1 n hn] at hU
    simp only [mem_iUnion] at hU
    obtain ⟨d, hd, -, hdle⟩ := hU
    have hsupp := ((hLip s).2.2.1 n hn X.1 hf d hd).2 hdle
    have hC1 : ∀ i, TestFunctions.IsC1Torus (X.1 i) := fun i => (X.2.1 i).1
    obtain ⟨z, hz⟩ := hlim n hn X.1 hC1 ⟨d, hd, hsupp⟩
    have hz0 := hreal m0 (fun j => K (φ j)) (fun j => β (φ j)) (fun j => hp (φ j)) hKφ n hn X.1 hC1
      ⟨d, hd, hsupp⟩ z hz
    have hzz : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
    exact ⟨z.re, by rw [hzz]; exact hz⟩
  choose S hS using key
  exact ⟨φ, S, hφ, ⟨fun j => K (φ j), fun j => β (φ j), fun j => hp (φ j), hKφ, hS⟩, hS⟩
theorem existsSubseqFamilyAlongTori_holds (hMul : TorusCumulants.Multilinearity.claim)
    (hB : Conventions.IsAdmissibleBlockingFactor ℓ.side) (hL : 2 ≤ ℓ.side)
    (hc : TotalDensitySystem.CouplingConditions ℓ Bs c₅ lam Nw CT g) : ExistsSubseqFamilyAlongTori ℓ Bs g := by
  intro K m β hp hK hm
  obtain ⟨φ, hφ, hlim⟩ := hc.growingTorusLimits K m β hp hK hm
  have hsφ := tendsto_of_strictMono_pnat hφ
  have hreal := growingToriValues_real hMul hB hL hc
  have key : ∀ (n : ℕ) (_ : 2 ≤ n) (X : TestSpaces.SepTupleOfCard n), ∃ z : ℝ,
      Tendsto (fun j => PeriodicLattice.torusUrsellFunction ℓ.side (m (φ j)) (K (φ j)) (β (φ j))
        (fun i => TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side (m (φ j))) (X.1 i))) atTop
        (𝓝 (z : ℂ)) := by
    intro n hn X
    obtain ⟨z, hz⟩ := hlim n hn X
    have hz0 := hreal (fun j => K (φ j)) (fun j => m (φ j)) (fun j => β (φ j)) (fun j => hp (φ j))
      (hK.comp hsφ) (hm.comp hsφ) n hn X z hz
    have hzz : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
    exact ⟨z.re, by rw [hzz]; exact hz⟩
  choose S hS using key
  exact ⟨φ, S, hφ, ⟨fun j => K (φ j), fun j => m (φ j), fun j => β (φ j), fun j => hp (φ j), hK.comp hsφ,
    hm.comp hsφ, hS⟩, hS⟩
theorem isGrowingTorusLimit_of_volumeFirst (hL : 2 ≤ ℓ.side)
    (hc : TotalDensitySystem.CouplingConditions ℓ Bs c₅ lam Nw CT g)
    {Q : SystemsWithFiveBounds.PairSequence ℓ.side (TotalDensitySystem.IsFirstPassagePair ℓ Bs g)}
    {S : LimitTheorem.CumulantFamily} (hS : Q.Defines S) : TotalDensitySystem.IsGrowingTorusLimit ℓ Bs g S := by
  obtain ⟨cV, Cn, C, -, -, -, -, hvf, -⟩ := hc.constants
  obtain ⟨m, hm, hlim⟩ := (hvf Q S hS).1.large_sides fun j => ((j : ℕ) : ℝ)
  refine ⟨Q.cutoff, m, Q.coupling, Q.pair, tendsto_atTop_of_coe Q.tendsto_cutoff, ?_,
    fun n hn X => (hlim n hn X).2⟩
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (PeriodicLattice.torusSide ℓ.side (b : ℕ))
  filter_upwards [eventually_ge_atTop (⟨N + 1, by omega⟩ : ℕ+)] with j hj
  by_contra hlt
  have h1 : ((m j : ℕ)) ≤ (b : ℕ) := (PNat.coe_le_coe _ _).2 (not_le.1 hlt).le
  have h2 := torusSide_mono (by omega : 1 ≤ ℓ.side) h1
  have h3 : (N : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
    have h4 : N + 1 ≤ (j : ℕ) := hj
    exact_mod_cast h4
  have h5 := hm j
  linarith
theorem limitsRealAt_holds (hLip : TorusLipschitzTuples.TorusLipschitzTupleFacts)
    (hMul : TorusCumulants.Multilinearity.claim)
    (hB : Conventions.IsAdmissibleBlockingFactor ℓ.side) (hL : 2 ≤ ℓ.side)
    (hc : TotalDensitySystem.CouplingConditions ℓ Bs c₅ lam Nw CT g) : LimitsRealAt ℓ Bs g := by
  have hFT := existsSubseqFamilyOnTorus_holds hLip hMul hL hc
  have hFA := existsSubseqFamilyAlongTori_holds hMul hB hL hc
  obtain ⟨K, β, hp, hK⟩ := exists_firstPassagePairs hc
  obtain ⟨φ, S, -, hS, -⟩ := hFA K id β hp hK tendsto_id
  exact
    { real_onTorus := oneTorusValues_real hMul hB hL hc
      real_alongTori := growingToriValues_real hMul hB hL hc
      family_onTorus := hFT
      family_alongTori := hFA
      exists_params := fun m => ⟨⟨ℓ.side, hB, 1, m⟩, rfl, rfl⟩
      exists_torusLimit := fun s hs => by
        obtain ⟨φ', S', -, hS', -⟩ := hFT s hs K β hp hK
        exact ⟨S', hS'⟩
      exists_growingTorusLimit := ⟨S, hS⟩
      exists_volumeFirstLimit := hc.volumeFirstLimits.1
      volumeFirst_isGrowingTorusLimit := fun Q S' hQ => isGrowingTorusLimit_of_volumeFirst hL hc hQ
      exists_continuumLimit := ⟨S, Or.inl hS⟩ }
end RealLimits
theorem bddAbove_norm_of_isBoundedFun {Y : Type*} {f : Y → ℝ} (hf : TestFunctions.IsBoundedFun f) :
    BddAbove (range fun x => ‖f x‖) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
theorem uniformNorm_pos {Y : Type*} {f : Y → ℝ} (hb : BddAbove (range fun x => ‖f x‖)) (hne : ∃ y, f y ≠ 0) :
    0 < TestFunctions.uniformNorm f := by
  obtain ⟨y, hy⟩ := hne
  exact (norm_pos_iff.2 hy).trans_le (le_ciSup hb y)
theorem twoPointPrefactor_pos : 0 < SystemsWithFiveBounds.twoPointPrefactor := by
  unfold SystemsWithFiveBounds.twoPointPrefactor
  positivity
theorem pos_of_isInLimitInterval {Y : Type*} {ϑ d r : ℝ} (hϑ : 0 < ϑ) (hd0 : 0 < d) (hd1 : d < 1)
    {f : Fin 4 → Y → ℝ} (hprod : 0 < ∏ i, TestFunctions.uniformNorm (f i))
    (h : FourPointCondition.IsInLimitInterval ϑ d f r) : 0 < r := by
  have hlog : 0 < Real.log (1 / d) := Real.log_pos (by rw [lt_div_iff₀ hd0]; linarith)
  have hmin : 0 < min ϑ (TorusMeasure.omega4 * (16 : ℝ) ^ (-4 : ℤ)) := by
    refine lt_min hϑ ?_
    unfold TorusMeasure.omega4
    positivity
  have hfloor : 0 < FourPointCondition.fourPointLowerConst ϑ := by
    unfold FourPointCondition.fourPointLowerConst
    positivity
  have hdim : 0 < FourPointCondition.gaugeGroupDim := by
    unfold FourPointCondition.gaugeGroupDim
    norm_num [ParameterChoice.colorNumber]
  have hone : 0 < FourPointCondition.oneLoopCoeff := by
    unfold FourPointCondition.oneLoopCoeff
    positivity
  refine lt_of_lt_of_le ?_ h.1
  exact mul_pos (mul_pos (mul_pos (mul_pos hfloor hdim) (pow_pos (by positivity) 4)) (zpow_pos hlog _)) hprod
def linearGauge (s : ℕ) : ℝ := (s : ℝ) + 1
theorem linearGauge_isSubexpGrowth : RoomFunctions.IsSubexpGrowth linearGauge := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only [linearGauge]; linarith
  · intro s
    have h1 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    simp only [linearGauge]; linarith
  · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · have h := (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right _ (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
    refine h.congr fun s => ?_
    simp [linearGauge, Function.comp]
theorem valuesPositiveAt_holds {ℓ : TorusLumps.StepParameters} {Bs c₅ lam g ϑ d₀ d₄ d : ℝ} {room : ℕ → ℝ}
    {C : SystemsWithFiveBounds.LimitConstants}
    {ηBar εBar : ℝ → ℝ} {ζ : ℕ+ → ℝ → ℝ → ℝ} {K₀ : ℝ → ℕ}
    (hMul : TorusCumulants.Multilinearity.claim)
    (hGeom : TestFunctions.PairTransport.PairTransportStatement)
    (hside : ∀ (s : Conventions.StandingParameters) (d : ℝ), d ≤ 1 / 40 →
      40 * d ≤ PeriodicLattice.torusSide s.L s.m)
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1)
    (hcl : TotalDensitySystem.ShapeConditions ℓ Bs c₅ lam g ϑ room C d₀ ηBar εBar ζ K₀ d₄)
    (hmem : TopAux.NonemptyTestClasses.NonemptyOnEuclideanSpace d ϑ ∧
      ∀ s : Conventions.StandingParameters, 40 * d ≤ PeriodicLattice.torusSide s.L s.m →
        TopAux.NonemptyTestClasses.NonemptyOnTorus s d ϑ)
    (hd : d ∈ Ioc (0 : ℝ) d₄) : ValuesPositiveAt ℓ Bs g ϑ d := by
  have hdm := hcl.d₄_mem
  have hd₀ := hcl.twoPointLaw.cutoff_mem
  have hdd : d ∈ Ioc (0 : ℝ) d₀ := ⟨hd.1, hd.2.trans hdm.2⟩
  have hd40 : d ≤ 1 / 40 := hdd.2.trans hd₀.2
  have hd1 : d < 1 := by linarith
  have hlog : 0 < Real.log (1 / d) := Real.log_pos (by rw [lt_div_iff₀ hd.1]; linarith)
  have hbd : ∀ (s : Conventions.StandingParameters) (f : s.Torus → ℝ),
      TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus f → TestFunctions.IsBoundedFun f :=
    fun s f hf => (hMul.2 s 1 1 one_pos le_rfl).2.1.2 f hf
  refine ⟨hmem.1, fun s _ => hmem.2 s (hside s d hd40), ?_, ?_, ?_, ?_⟩
  · intro S hlim X hX
    exact (hcl.everyLimit S hlim).conditions.twoPoint_pos d hdd X hX
  · intro S hlim X hX
    refine pos_of_isInLimitInterval hϑ.1 hd.1 hd1 (f := X.1) ?_
      (hcl.fourPointInLimits.on_space S hlim d hd X hX)
    obtain ⟨⟨-, -, hpairs⟩, -⟩ := hX
    refine Finset.prod_pos fun i _ => ?_
    obtain ⟨j, hj⟩ : ∃ j : Fin 4, i ≠ j := ⟨i + 1, by fin_cases i <;> decide⟩
    obtain ⟨x₁, x₂, h1, -⟩ := hpairs i j hj
    exact uniformNorm_pos ((X.2.1 i).1.continuous.norm.bddAbove_range_of_hasCompactSupport (X.2.1 i).2.1.norm)
      h1.2.2.1
  · intro s S hs hlim X hX
    have h40 : 40 * d ≤ s.side := hside s d hd40
    obtain ⟨-, -, -, hker, -⟩ := (hGeom s d ϑ ⟨hd.1, hϑ⟩).2.2.1 h40 (X.1 0) (X.1 1) hX
    obtain ⟨η, hv, hlo, -⟩ := hcl.twoPointLawInLimits.on_torus s S hs hlim d hdd X hX
    obtain ⟨x₁, x₂, b1, b2, -⟩ := hX
    have hA : 0 < TestFunctions.uniformNorm (X.1 0) :=
      uniformNorm_pos (bddAbove_norm_of_isBoundedFun (hbd s _ b1.1)) b1.2.2.1
    have hA' : 0 < TestFunctions.uniformNorm (X.1 1) :=
      uniformNorm_pos (bddAbove_norm_of_isBoundedFun (hbd s _ b2.1)) b2.2.2.1
    have hfl : 0 < (10 : ℝ) ^ (-8 : ℤ) * ϑ ^ 2 * TestFunctions.uniformNorm (X.1 0) *
        TestFunctions.uniformNorm (X.1 1) :=
      mul_pos (mul_pos (mul_pos (zpow_pos (by norm_num) _) (pow_pos hϑ.1 2)) hA) hA'
    have hK := hfl.trans_le hker.1
    have hε : εBar d ∈ Icc (0 : ℝ) (1 / 2) := hcl.twoPointLaw.sharp_on_tori.εBar_mem 0 d hdd
    have hη := hcl.twoPointLaw.sharp_on_tori.ηBar_mem d hdd
    have hpos : 0 < 1 + η :=
      lt_of_lt_of_le (mul_pos (by linarith [hε.2]) (pow_pos (by linarith [hη.2]) 4)) hlo
    rw [hv]
    exact mul_pos (div_pos (mul_pos twoPointPrefactor_pos hK) (pow_pos hlog 2)) hpos
  · intro s S hs hlim X hX
    refine pos_of_isInLimitInterval hϑ.1 hd.1 hd1 (f := X.1) ?_
      (hcl.fourPointInLimits.on_torus s S hs hlim d hd X hX)
    obtain ⟨⟨-, -, hl, hpairs⟩, -⟩ := hX
    refine Finset.prod_pos fun i _ => ?_
    obtain ⟨j, hj⟩ : ∃ j : Fin 4, i ≠ j := ⟨i + 1, by fin_cases i <;> decide⟩
    obtain ⟨x₁, x₂, h1, -⟩ := hpairs i j hj
    exact uniformNorm_pos (bddAbove_norm_of_isBoundedFun (hbd s _ (hl i).1)) h1.2.2.1
theorem mainStatement_holds (hT : TotalDensities.TrajectoryTopStatement)
    (hCl : TopAux.NonemptyTestClasses.Statement)
    (hLip : TorusLipschitzTuples.TorusLipschitzTupleFacts)
    (hMul : TorusCumulants.Multilinearity.claim)
    (hGeom : TestFunctions.PairTransport.PairTransportStatement) : MainStatement := by
  obtain ⟨hside, ϑ₀, hϑ₀, hmem⟩ := hCl
  obtain ⟨J, Ls, hJ, h⟩ := hT
  refine ⟨ϑ₀, hϑ₀, J, Ls, hJ, fun L hodd hge => ?_⟩
  obtain ⟨ℓ, Bs, c₅, γ, Nw, CT, hL, hJ₀, hdat, hBs, hc₅, hγ, hCT, hNw, hall⟩ := h L hodd hge
  have h40 := hdat.side_ge
  have hL2 : 2 ≤ ℓ.side := by
    have h2 : (2 : ℕ) ≤ 2 ^ 40 := by norm_num
    omega
  have hB : Conventions.IsAdmissibleBlockingFactor ℓ.side := by
    have h13 : (13 : ℕ) ≤ 2 ^ 40 := by norm_num
    exact ⟨hdat.side_odd, by omega⟩
  refine ⟨ℓ, Bs, c₅, γ, Nw, CT, hL, hJ₀, hdat, hBs, hc₅, hγ, hCT, hNw, fun g hg =>
    ⟨hall g hg, limitsRealAt_holds hLip hMul hB hL2 (hall g hg), fun ϑ hϑ => ?_⟩⟩
  have hϑ1 : ϑ ∈ Ioc (0 : ℝ) 1 := ⟨hϑ.1, hϑ.2.trans hϑ₀.2⟩
  obtain ⟨cV, Cn, C, hC, -, -, -, -, hnum⟩ := (hall g hg).constants
  obtain ⟨-, hroom⟩ := hnum ϑ hϑ1
  obtain ⟨d₀, ηBar, εBar, ζ, K₀, d₄, hcl⟩ := hroom linearGauge linearGauge_isSubexpGrowth
  exact ⟨d₄, ⟨hcl.d₄_mem.1, hcl.d₄_mem.2.trans hcl.twoPointLaw.cutoff_mem.2⟩, fun d hd =>
    valuesPositiveAt_holds hMul hGeom hside hϑ1 hcl (hmem ϑ hϑ d hd.1) hd⟩
end YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero
end
