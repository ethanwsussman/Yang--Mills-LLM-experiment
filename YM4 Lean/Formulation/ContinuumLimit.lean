import YangMills.Construction.LimitTheorem.OsterwalderSchrader
import YangMills.Construction.TheStatementsProvedTogether.FromTheTopOfTheTrajectoryProof

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology ContDiff

namespace YangMills

open Construction

open Construction.LimitTheorem
open Construction.ConfigSpace (FlatSequence)
open Construction.LimitTheorem.ComponentConditions

private theorem mixture_schwinger {p : TorusLumps.StepParameters} {Bs g c₅ lam CT : ℝ}
    {Nw : ℕ}
    {Q : SystemsWithFiveBounds.PairSequence p.side (TotalDensitySystem.IsFirstPassagePair p Bs g)}
    {S : LimitTheorem.CumulantFamily} {A : SeparatedTuples.DecompositionData}
    (hc : TotalDensitySystem.CouplingConditions p Bs c₅ lam Nw CT g)
    (hS : Q.Defines S) (hA : A.IsCanonical (centredOf S)) :
    ∃ (C' : SystemsWithFiveBounds.LimitConstants) (T : FlatSequence),
      C'.Valid ∧ SystemsWithFiveBounds.HasSchwingerSequence (centredOf S) T ∧
      SystemsWithFiveBounds.SatisfiesGrowth T C'.schwartzOrder C'.schwartzPrefactor
        C'.schwartzBase C'.schwartzExp ∧
      ConfigSpace.IsEuclidInvariant T ∧ ConfigSpace.IsOSPositive T ∧
      ConfigSpace.IsPermSymmetric T ∧ ConfigSpace.IsReflectionReal T ∧ HasCumulants (centredOf S) S := by
  obtain ⟨_, _, C', hvalid, _, _, _, _, hs⟩ := hc.constants
  obtain ⟨_, _, _, _, _, _, shape⟩ := (hs 1 ⟨zero_lt_one, le_rfl⟩).2 _
    Assembled.exists_room_function_of_apex
  let hlim := (shape.ergodic Q S hS).limit
  obtain ⟨T, hT, hgrowth⟩ := hlim.conditions.growth
  obtain ⟨hpos, _⟩ := hlim.conditions.reconstruction.2.2
  have hbary (X : SeparatedTuples.SepTuple) :
      (∫ ξ, A.comp ξ X ∂A.law) = centredOf S X := by
    simpa [SeparatedTuples.iteratedLimitAtInfinity, SeparatedTuples.iterLimitValue,
      SeparatedTuples.shiftedJuxt] using hA.integral_comp_prod X []
  have hrot : IsO4InvariantFunctional (centredOf S) := by
    intro R X
    rw [← hbary, ← hbary X]
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => ((shape.ergodic Q S hS).components A hA ξ).symmetries.rotation_inv R X
  obtain ⟨he, hp, hs, hr⟩ := os_of_tuple_symmetries
    TheStatementsProvedTogether.schwinger_properties_transfer_schwartz
    TheStatementsProvedTogether.reflection_positive_of_functional_values hlim.distributions.1
    hlim.conditions.reconstruction.2.1 hrot hlim.symmetries.centred_symm hpos hT
  exact ⟨C', T, hvalid, hT, hgrowth, he, hp, hs, hr, hlim.conditions.cumulants_eq⟩

noncomputable section
/-- The SU(2) Wilson expectation of a product of centered smeared plaquette energies. -/
def su2_centeredMoment (L m K : ℕ) (β : ℝ) {n : ℕ}
    (X : TestSpaces.SepTupleOfCard n) : ℂ :=
  let f := SchwingerFunctions.periodizeAll L m X.1
  let obs := fun i U => PeriodicLattice.smearedObservable
    (fun x => (f i x : ℂ)) U
  PeriodicLattice.gibbsExpectation L m K β fun U =>
    ∏ i, (obs i U - PeriodicLattice.gibbsExpectation L m K β (obs i))

theorem su2_moments_tendsto {ι : Type*} {l : Filter ι} {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {m : ι → ℕ} {K : ι → ℕ+} {β : ι → ℝ}
    (hm : ∀ᶠ j in l, 0 < m j) (hβ : ∀ᶠ j in l, 0 < β j)
    {S : LimitTheorem.CumulantFamily}
    (hc : ∀ (n : ℕ) (hn : 2 ≤ n) (X : TestSpaces.SepTupleOfCard n),
      Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 L (m j) (K j) (β j) X.1)
        l (𝓝 (S n hn X : ℂ)))
    (n : ℕ) (X : TestSpaces.SepTupleOfCard n) :
    Tendsto (fun j => su2_centeredMoment L (m j) (K j) (β j) X) l
      (𝓝 (TestSpaces.centredOfCumulants S ⟨n,X⟩ : ℂ)) := by
  classical
  let F (B : Finset (Fin n)) : ℝ :=
    if h : 2 ≤ B.card then S B.card h (TestSpaces.sepRestrict X B) else 0
  have hsum : TestSpaces.centredOfCumulants S ⟨n,X⟩ =
      ∑ π ∈ SetPartition.singletonFree n, ∏ B ∈ π.parts, F B := by
    have e : TestSpaces.centredOfCumulants S ⟨n,X⟩ =
        ∑ P ∈ TestSpaces.partitionsNoSingletons (Fin n), ∏ B ∈ P, F B := by
      rw [TestSpaces.centredOfCumulants, ← Finset.sum_attach (TestSpaces.partitionsNoSingletons (Fin n))]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [← Finset.prod_attach P.1]
      refine Finset.prod_congr rfl fun B _ => ?_
      simp [F, TestSpaces.two_le_card_of_mem_partitionsNoSingletons P.2 B.2]
    rw [e, EntrywiseMultilinearity.partitionsAgree_holds.2 n, Finset.sum_image]
    exact fun _ _ _ _ eq => Finpartition.ext eq
  rw [hsum]
  push_cast
  let c (j : ι) (B : Finset (Fin n)) :=
    SchwingerFunctions.connectedSchwingerR4 L (m j) (K j) (β j) (TestSpaces.sepRestrict X B).1
  have lim : Tendsto (fun j => ∑ π ∈ SetPartition.singletonFree n, ∏ B ∈ π.parts, c j B)
      l (𝓝 (∑ π ∈ SetPartition.singletonFree n, ∏ B ∈ π.parts, (F B : ℂ))) := by
    refine tendsto_finsetSum _ fun π hπ => tendsto_finsetProd _ fun B hB => ?_
    have h2 := AmbientPoints.two_le_card_of_mem_singletonFree hπ hB
    simpa [F, h2] using hc B.card h2 (TestSpaces.sepRestrict X B)
  apply lim.congr'
  filter_upwards [hm, hβ] with j hmj hj
  let D : ConnectedFunctions.CouplingData := ⟨⟨L,hL,K j,⟨m j, hmj⟩⟩, β j,hj⟩
  exact (CumulantLimits.CentredMoments.centredMomentFn_ofRealTuple_eq_sum
    TheStatementsProvedTogether.connected_functions_centred_identity D
    (SchwingerFunctions.periodizeAll L (m j) X.1)).symm


/-- A property of Schwinger representatives that follows for every canonical component.
The extraction of cutoff and volume subsequences is independent of this choice. -/
def HoldsForComponents (P : SystemsWithFiveBounds.LimitConstants → FlatSequence → Prop) : Prop :=
  ∀ {M θ d : ℝ} {η : ℝ → ℝ} {D : SystemsWithFiveBounds.LimitConstants}
    {σ : SeparatedTuples.TupleFunctional},
    SystemsWithFiveBounds.ComponentProperties M θ d η D σ →
    ∃ T, SystemsWithFiveBounds.HasSchwingerSequence σ T ∧ P D T

theorem os_axioms_for_components : HoldsForComponents SystemsWithFiveBounds.OSAxioms := by
  intro M θ d η D σ hc
  obtain ⟨T, hT, _⟩ := hc.growth
  exact ⟨T, hT, hc.componentOS T hT⟩

/-- A prescribed sequence of inverse couplings has a nontrivial infinite-volume
continuum subsequence whenever it enters one fixed first-passage window cofinally. -/
theorem su2_continuum_limit_of_frequent_passage
    {P : SystemsWithFiveBounds.LimitConstants → FlatSequence → Prop} (hP : HoldsForComponents P)
    {p : TorusLumps.StepParameters} {Bs c₅ lam CT g : ℝ} {Nw : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor p.side)
    (hc : TotalDensitySystem.CouplingConditions p Bs c₅ lam Nw CT g)
    (K : ℕ → ℕ+) (β : ℕ → ℝ) (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop)
    (hβ : ∀ j, 0 < β j)
    (hp : ∃ᶠ j in atTop, TotalDensitySystem.IsFirstPassagePair p Bs g (K j) (β j)) :
    ∃ (φ : ℕ → ℕ) (m : ℕ → ℕ+) (ν : ∀ j, Measure (InfiniteLattice.GaugeField
          (PeriodicLattice.meshSize p.side ((K (φ j) : ℕ) : ℤ))))
        (S : CumulantFamily) (X₂ : TestSpaces.SepTupleOfCard 2) (X₄ : TestSpaces.SepTupleOfCard 4),
      StrictMono φ ∧ (∀ j, TotalDensitySystem.IsFirstPassagePair p Bs g (K (φ j)) (β (φ j))) ∧
      (∀ j, InfiniteLattice.IsInfiniteVolumeLimit p.side (K (φ j)) (β (φ j)) (ν j)) ∧
      Tendsto (fun j => PeriodicLattice.torusSide p.side (m j)) atTop atTop ∧
      Tendsto (fun j => β (φ j) / ((K (φ j) : ℝ) * Real.log p.side))
        atTop (𝓝 (11 / (3 * Real.pi ^ 2) : ℝ)) ∧
      (∀ n hn (X : TestSpaces.SepTupleOfCard n),
        (∀ᶠ j in atTop, SchwingerFunctions.IsR4TestFamily (PeriodicLattice.torusSide p.side (m j)) X.1) ∧
        Tendsto (fun j => InfiniteLattice.smearedEnergyCumulant (ν j) X.1) atTop (𝓝 (S n hn X : ℂ)) ∧
        Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 p.side (m j) (K (φ j)) (β (φ j)) X.1)
          atTop (𝓝 (S n hn X : ℂ))) ∧
      (∀ n (X : TestSpaces.SepTupleOfCard n), let z : ℂ := TestSpaces.centredOfCumulants S ⟨n,X⟩
        Tendsto (fun j => InfiniteLattice.centeredMoment (ν j) X.1) atTop (𝓝 z) ∧
        Tendsto (fun j => su2_centeredMoment p.side (m j) (K (φ j)) (β (φ j)) X) atTop (𝓝 z)) ∧
      (∀ i, ContDiff ℝ ∞ (X₂.1 i)) ∧ 0 < S 2 le_rfl X₂ ∧
      (∀ i, ContDiff ℝ ∞ (X₄.1 i)) ∧ 0 < S 4 (by decide) X₄ ∧
      (∃ (D : SystemsWithFiveBounds.LimitConstants) (T : FlatSequence),
        D.Valid ∧ SystemsWithFiveBounds.HasSchwingerSequence (centredOf S) T ∧
        SystemsWithFiveBounds.SatisfiesGrowth T D.schwartzOrder D.schwartzPrefactor D.schwartzBase D.schwartzExp ∧
        ConfigSpace.IsEuclidInvariant T ∧ ConfigSpace.IsOSPositive T ∧
        ConfigSpace.IsPermSymmetric T ∧ ConfigSpace.IsReflectionReal T ∧ HasCumulants (centredOf S) S) ∧
      ∃ (A : SeparatedTuples.DecompositionData) (D : SystemsWithFiveBounds.LimitConstants),
        D.Valid ∧ A.IsCanonical (centredOf S) ∧
        (∀ ξ, ∃ T : FlatSequence, SystemsWithFiveBounds.HasSchwingerSequence (A.comp ξ) T ∧
          P D T) ∧
        ∀ᵐ ξ ∂A.law, ModelSeams.IsNonGaussianOnSmoothQuadruple (A.comp ξ) := by
  obtain ⟨e, he, hpass⟩ := extraction_of_frequently_atTop hp
  have hL2 : 2 ≤ p.side := by have := hL.2; omega
  have hstate (j : ℕ+) := TheStatementsProvedTogether.torus_limit_sets_nonempty p.side (K (e j.val))
    hL (K (e j.val)).pos _ (hβ (e j.val))
  simp only [TheStatementsProvedTogether.torus_limits_eq_infinite_volume_limits _ _ _ hL2] at hstate
  choose ν hν using hstate
  let Q : SystemsWithFiveBounds.PairSequence p.side (TotalDensitySystem.IsFirstPassagePair p Bs g) :=
    ⟨fun j => K (e j.val), (hK.comp he.tendsto_atTop).comp tendsto_PNat_val_atTop_atTop,
      fun j => β (e j.val), fun j => hpass _, ν, hν⟩
  obtain ⟨ψ, hψ, S, hS⟩ := hc.volumeFirstLimits.2 Q
  let Q' := Q.subseq ψ hψ
  obtain ⟨_, _, C, hC, _, _, _, hv, hshape⟩ := hc.constants
  obtain ⟨hsides, ϑ, hϑ, hclasses⟩ := TheStatementsProvedTogether.testClasses_nonempty_all_scales
  have hϑ' : ϑ ∈ Ioc (0 : ℝ) ϑ := ⟨hϑ.1, le_rfl⟩
  obtain ⟨hNG, hroom⟩ := hshape ϑ hϑ
  obtain ⟨_, _, _, _, _, d, hsh⟩ := hroom _ Assembled.exists_room_function_of_apex
  have hd : d ∈ Ioc (0 : ℝ) d := ⟨hsh.d₄_mem.1, le_rfl⟩
  have hpos := QuaternionicWilsonModel.TopLimitsRealNonzero.valuesPositiveAt_holds
    TheStatementsProvedTogether.torusCumulant_multilinear TheStatementsProvedTogether.test_pair_transport_lift_dilation
    hsides hϑ hsh (hclasses ϑ hϑ' d hd.1) hd
  obtain ⟨⟨X₂, hX₂, hs₂⟩, X₄, hX₄, hs₄⟩ := hpos.nonempty_space
  have hlimS : TotalDensitySystem.IsContinuumLimit p Bs g S := Or.inr ⟨Q', hS⟩
  have hAss := hsh.ergodic Q' S hS
  obtain ⟨A, hA⟩ := hAss.decomposition.exists_canonical
  obtain ⟨m, hm, hlim⟩ := (hv Q' S hS).1.large_sides (fun j => ((Q'.cutoff j : ℕ) : ℝ))
  have hside : Tendsto (fun j => PeriodicLattice.torusSide p.side (m j)) atTop atTop :=
    tendsto_atTop_mono hm (tendsto_natCast_atTop_atTop.comp Q'.tendsto_cutoff)
  have hsucc : Tendsto Nat.succPNat atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ h => Nat.succ_le_succ h)
      (fun b => ⟨b.val, Nat.le_succ _⟩)
  obtain ⟨t, ht, hψt⟩ := strictMono_subseq_of_tendsto_atTop (hψ.comp hsucc)
  let i (j : ℕ) := (t j).succPNat
  have hi : Tendsto i atTop atTop := hsucc.comp ht.tendsto_atTop
  let φ (j : ℕ) := e (ψ (i j)).val
  have hmono : StrictMono φ := fun _ _ h => he (hψt h)
  obtain ⟨δ, hδ, herr⟩ := hc.passage.asymptotically_free
  have hratio : Tendsto (fun j => Q'.coupling j / Real.log (1 / PeriodicLattice.meshSize p.side
      ((Q'.cutoff j : ℕ) : ℤ))) atTop (𝓝 SystemsWithFiveBounds.asymptoticFreedomSlope) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => herr _ _ (Q'.cutoff j).pos (Q'.pair j))
      (hδ.comp Q'.tendsto_cutoff)
  have hslope : SystemsWithFiveBounds.asymptoticFreedomSlope = 11 / (3 * Real.pi ^ 2) := by
    unfold SystemsWithFiveBounds.asymptoticFreedomSlope
    field_simp
    ring
  refine ⟨φ, fun j => m (i j), fun j => Q'.state (i j), S, X₂, X₄, hmono, fun j => Q'.pair (i j),
    fun j => Q'.isLimit (i j), hside.comp hi, ?_, fun n hn X =>
      ⟨hi.eventually (hlim n hn X).1, (hS n hn X).comp hi, ((hlim n hn X).2).comp hi⟩,
    ?_, fun l => (hs₂ l).1, hpos.pair_pos_space S hlimS X₂ hX₂, fun l => (hs₄ l).1,
    hpos.quad_pos_space S hlimS X₄ hX₄, mixture_schwinger hc hS hA, A, C, hC, hA, ?_, ?_⟩
  · rw [hslope] at hratio
    apply (hratio.comp hi).congr
    intro j
    change β (φ j) / Real.log (1 / PeriodicLattice.meshSize p.side ((K (φ j) : ℕ) : ℤ)) = _
    rw [NonGaussianLimits.log_inv_meshSize (by omega : 0 < p.side)]
  · intro n X
    refine ⟨?_, su2_moments_tendsto hL (Eventually.of_forall fun j => (m (i j)).pos)
      (Eventually.of_forall fun j => hβ (φ j)) (fun n hn X => ((hlim n hn X).2).comp hi) n X⟩
    let s : Conventions.StandingParameters := ⟨p.side, hL, 1, 1⟩
    let f : AmbientPoints.separatedTuples s .euclidean n :=
      ⟨X.1, (AmbientPoints.mem_separatedTuples_r4_iff X.1).2 X.2⟩
    let T : AmbientPoints.TupleMapFamily s .euclidean := fun k hk u => S k hk (AmbientPoints.toR4Tuple u)
    have he := AmbientPoints.centredOfMaps_r4 T S (fun _ _ _ => rfl) f
    change Tendsto _ atTop (𝓝 ((TestSpaces.centredOfCumulants S ⟨n, AmbientPoints.toR4Tuple f⟩ : ℝ) : ℂ))
    rw [← he]
    apply (CumulantLimits.CentredMoments.tendsto_sum_singletonFree T
      (fun j k u => InfiniteLattice.smearedEnergyCumulant (Q'.state (i j)) u)
      (fun k hk u => (hS k hk (AmbientPoints.toR4Tuple u)).comp hi) f).congr
    intro j
    let st : Conventions.StandingParameters := ⟨p.side, hL, Q'.cutoff (i j), 1⟩
    have hid := (TheStatementsProvedTogether.gibbsState_centered_identity st _ (Q'.isLimit (i j)).1).2.2
      n f.1 (CumulantLimits.CentredMoments.apply_mem_compactTestFunctions f.2)
    exact (hid.trans (CumulantLimits.CentredMoments.ursellPartitionSum_eq_sum _ _)).symm
  · exact fun ξ => hP (hAss.components A hA ξ)
  · obtain ⟨X, hX, hsX⟩ := ((hclasses ϑ hϑ' 1 one_pos).1).2
    let Y (u : ℕ) : TestSpaces.SepTupleOfCard 4 :=
      ⟨TotalDensities.dyadicRescale u X.1, NonGaussianLimits.dyadicRescale_mem u X⟩
    have hng := (hv Q' S hS).2.ae_components A hA 4 (by decide) (by decide) X Y (fun _ => rfl)
    filter_upwards [hng] with ξ hξ
    obtain ⟨u, hu⟩ := (hξ.eventually (lt_mem_nhds (hNG.four_pos X hX))).exists
    refine ⟨Y u, fun k => (hsX k).1.comp (by fun_prop), fun hzero => ?_⟩
    rw [hzero, mul_zero] at hu
    exact (lt_irrefl _ hu)

/-- Continuum limit of the four-dimensional SU(2) Wilson model.

For each small first-passage coupling, one sequence of cutoffs and tori yields
convergence of all separated-test cumulants and centered moments. The limiting two-point function is
positive on a smooth pair. The centered moment functional extends to a Schwinger
sequence satisfying the OS conditions except possibly clustering. Each canonical component has
a Schwinger sequence satisfying all OS axioms, including clustering.
Almost every component has a nonzero smooth connected four-point function.
-/
theorem su2_continuum_limit :
    ∃ Lstar : ℕ, ∀ L : ℕ, Odd L → Lstar ≤ L →
      ∃ (p : TorusLumps.StepParameters) (Bs γ : ℝ),
        p.side = L ∧ TotalDensitySystem.IsUnitMeshStepParameters p ∧
        2 ≤ Bs ∧ γ ∈ Ioo (0 : ℝ) 1 ∧
        ∀ g ∈ Ioc (0 : ℝ) γ,
          ∃ (K m : ℕ+ → ℕ+) (β : ℕ+ → ℝ)
            (S : LimitTheorem.CumulantFamily) (X₂ : TestSpaces.SepTupleOfCard 2),
            (∀ j, TotalDensitySystem.IsFirstPassagePair p Bs g (K j) (β j)) ∧
            Tendsto (fun j => (K j : ℕ)) atTop atTop ∧
            Tendsto β atTop atTop ∧
            Tendsto (fun j => PeriodicLattice.torusSide L (m j)) atTop atTop ∧
            Tendsto (fun j => β j /
              Real.log (1 / PeriodicLattice.meshSize L ((K j : ℕ) : ℤ)))
              atTop (𝓝 (11 / (3 * Real.pi ^ 2) : ℝ)) ∧
            (∀ (n : ℕ) (hn : 2 ≤ n) (X : TestSpaces.SepTupleOfCard n),
              (∀ᶠ j in atTop,
                SchwingerFunctions.IsR4TestFamily (PeriodicLattice.torusSide L (m j)) X.1) ∧
              Tendsto (fun j =>
                SchwingerFunctions.connectedSchwingerR4 L (m j) (K j) (β j) X.1)
                atTop (𝓝 ((S n hn X : ℝ) : ℂ))) ∧
            (∀ (n : ℕ) (X : TestSpaces.SepTupleOfCard n),
              Tendsto (fun j => su2_centeredMoment L (m j) (K j) (β j) X) atTop
                (𝓝 (TestSpaces.centredOfCumulants S ⟨n, X⟩ : ℂ))) ∧
            (∀ i, ContDiff ℝ ∞ (X₂.1 i)) ∧ 0 < S 2 le_rfl X₂ ∧
            (∃ (D : SystemsWithFiveBounds.LimitConstants) (T : FlatSequence),
              D.Valid ∧ SystemsWithFiveBounds.HasSchwingerSequence (centredOf S) T ∧
              SystemsWithFiveBounds.SatisfiesGrowth T D.schwartzOrder D.schwartzPrefactor
                D.schwartzBase D.schwartzExp ∧
              ConfigSpace.IsEuclidInvariant T ∧ ConfigSpace.IsOSPositive T ∧
              ConfigSpace.IsPermSymmetric T ∧ ConfigSpace.IsReflectionReal T ∧ HasCumulants (centredOf S) S) ∧
            ∃ (A : SeparatedTuples.DecompositionData) (C : SystemsWithFiveBounds.LimitConstants),
              C.Valid ∧ A.IsCanonical (LimitTheorem.centredOf S) ∧
              (∀ ξ, ∃ T : ConfigSpace.FlatSequence,
                SystemsWithFiveBounds.HasSchwingerSequence (A.comp ξ) T ∧
                SystemsWithFiveBounds.OSAxioms C T) ∧
              ∀ᵐ ξ ∂A.law, ModelSeams.IsNonGaussianOnSmoothQuadruple (A.comp ξ) := by
  obtain ⟨_, Lstar, _, htop⟩ := TheStatementsProvedTogether.totalDensity_trajectory_top
  refine ⟨max Lstar 13, ?_⟩
  intro L hodd hlarge
  obtain ⟨p, Bs, c₅, γ, Nw, CT, hside, _, hunit, hBs, _, hγ, _, _, hg⟩ :=
    htop L hodd ((le_max_left ..).trans hlarge)
  subst L
  refine ⟨p, Bs, γ, rfl, hunit, hBs, hγ, ?_⟩
  intro g hgin
  let hc := hg g hgin
  obtain ⟨Q, _, _⟩ := hc.volumeFirstLimits.1
  let K (j : ℕ) := Q.cutoff j.succPNat
  let β (j : ℕ) := Q.coupling j.succPNat
  have hL : Conventions.IsAdmissibleBlockingFactor p.side := ⟨hodd, (le_max_right ..).trans hlarge⟩
  have hsucc : Tendsto Nat.succPNat atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ h => Nat.succ_le_succ h) (fun b => ⟨b.val, Nat.le_succ _⟩)
  have hK : Tendsto (fun j => (K j : ℕ)) atTop atTop := Q.tendsto_cutoff.comp hsucc
  have hβ (j : ℕ) : 0 < β j := by
    have h : g ^ (-2 : ℤ) + Bs ≤ β j := (Q.pair j.succPNat).2.1
    linarith [zpow_pos hgin.1 (-2 : ℤ)]
  obtain ⟨φ, m, _, S, X₂, _, hφ, hp, _, hm, hAF, hlim, hcent, hsm, hpos, _, _, hOS, hcomp⟩ :=
    su2_continuum_limit_of_frequent_passage os_axioms_for_components hL hc K β hK hβ (.of_forall fun j => Q.pair j.succPNat)
  have hpred := InfiniteLattice.PeriodicExtensions.tendsto_pnatNatPred_atTop
  have hKt := (hK.comp hφ.tendsto_atTop).comp hpred
  have hL2 : 2 ≤ p.side := by have := hL.2; omega
  refine ⟨fun j => K (φ j.natPred), fun j => m j.natPred, fun j => β (φ j.natPred), S, X₂,
    fun j => hp _, hKt, NonGaussianLimits.tendsto_coupling_atTop hL2 hc _ _ (fun j => hp _) hKt,
    hm.comp hpred, ?_, fun n hn X => ⟨hpred.eventually (hlim n hn X).1, ((hlim n hn X).2.2).comp hpred⟩,
    fun n X => ((hcent n X).2).comp hpred, hsm, hpos, hOS, hcomp⟩
  apply (hAF.comp hpred).congr
  intro j
  change β (φ j.natPred) / ((K (φ j.natPred) : ℝ) * Real.log p.side) =
    β (φ j.natPred) / Real.log (1 / PeriodicLattice.meshSize p.side ((K (φ j.natPred) : ℕ) : ℤ))
  rw [NonGaussianLimits.log_inv_meshSize (by omega : 0 < p.side)]


end
end YangMills
