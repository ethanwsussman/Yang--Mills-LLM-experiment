import YangMills.Construction.Continuum.CentredMomentsOfTheCumulantsAndOfTheirLimits
import YangMills.Construction.Continuum.MultilinearFunctionalsCoordinatewise
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import YangMills.Construction.ToriAtArbitraryCouplings.TheTransportToATorus
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfConnectedFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter MeasureTheory AmbientPoints
open scoped Topology
namespace CumulantLimits.CentredMoments
variable {n : ℕ}
theorem update_linComb_of_slotLinear {X : Type*} {R : Set (X → ℝ)} {c : (Fin n → X → ℝ) → ℂ}
    (hc : IsRealValuedAndSlotLinear R c) (hsmul : ∀ (a : ℝ) (h : X → ℝ), h ∈ R → a • h ∈ R)
    {f f' : Fin n → X → ℝ} (hf : ∀ k, f k ∈ R) (hf' : ∀ k, f' k ∈ R) {i : Fin n}
    (he : ∀ l, l ≠ i → f l = f' l) (a a' : ℝ) :
    c (Function.update f i (a • f i + a' • f' i)) = (a : ℂ) * c f + (a' : ℂ) * c f' := by
  have hu : Function.update f i (f' i) = f' := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · simp [Function.update_of_ne hl, he l hl]
  have h₁ := (hc f hf).2.1 i (a • f i) (a' • f' i) (hsmul a _ (hf i)) (hsmul a' _ (hf' i))
  have h₂ := (hc f hf).2.2 i (f i) a (hf i)
  have h₃ := (hc f hf).2.2 i (f' i) a' (hf' i)
  rw [h₁, h₂, h₃, hu, Function.update_eq_self]
theorem slotLinear_cumulantReal (X : ConnectedFunctions.CouplingData) {R : Set (X.Torus → ℝ)}
    (h : X.RealSymmMultilinearOn n R) :
    IsRealValuedAndSlotLinear R (X.cumulantReal (n := n)) := by
  have hr : ∀ f : Fin n → X.Torus → ℝ,
      X.connected (X.ofRealTuple f) = X.cumulantReal f :=
    fun f => X.connected_ofReal f
  obtain ⟨h₁, -, h₃, h₄⟩ := h
  intro f hf
  refine ⟨?_, fun i g g' hg hg' => ?_, fun i g a hg => ?_⟩
  · rw [← hr]
    exact h₁ f hf
  · simp only [← hr]
    exact h₃ f hf i g g' hg hg'
  · simp only [← hr]
    exact h₄ f hf i g a hg
theorem centredMomentFn_ofRealTuple_eq_sum
    (h : ConnectedFunctions.CentredIdentityAtAllFunctions)
    (X : ConnectedFunctions.CouplingData) (f : Fin n → X.Torus → ℝ) :
    X.centredMomentFn (X.ofRealTuple f) =
      ∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts,
        X.cumulantReal fun k => f (J.orderEmbOfFin rfl k) := by
  rw [(h X).2.2.1 n (X.ofRealTuple f) fun _ => Set.mem_univ _]
  exact Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ =>
    X.connected_ofReal _
theorem slotLinear_ursellFunction {a : ℝ} (ν : Measure (InfiniteLattice.GaugeField a))
    (h : InfiniteLattice.CenteredIdentity.UrsellIsRealSymmetricMultilinear ν n) :
    IsRealValuedAndSlotLinear InfiniteLattice.compactTestFunctions
      (InfiniteLattice.ursellFunction ν n) := by
  intro f hf
  have hup : ∀ (i : Fin n) (g : InfiniteLattice.AmbientSpace → ℝ),
      g ∈ InfiniteLattice.compactTestFunctions →
      ∀ k, Function.update f i g k ∈ InfiniteLattice.compactTestFunctions := by
    intro i g hg k
    by_cases hk : k = i
    · subst hk
      simpa using hg
    · simpa [Function.update_of_ne hk] using hf k
  refine ⟨(h f hf).1, fun i g g' hg hg' => ?_, fun i g a hg => ?_⟩
  · simpa using (h _ (hup i g hg)).2.2.1 i g' hg'
  · simpa using (h _ (hup i g hg)).2.2.2 i a
theorem ursellPartitionSum_eq_sum {a : ℝ} (ν : Measure (InfiniteLattice.GaugeField a))
    (f : Fin n → InfiniteLattice.AmbientSpace → ℝ) :
    InfiniteLattice.ursellPartitionSum ν f =
      ∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts,
        InfiniteLattice.smearedEnergyCumulant ν fun k => f (J.orderEmbOfFin rfl k) := by
  have hset : SetPartition.singletonFree n = SetPartition.nonSingletonPartitions n := by
    rw [SetPartition.singletonFree_eq_nonSingletonPartitions]
  rw [hset]
  rfl
theorem apply_mem_compactTestFunctions {s : Conventions.StandingParameters}
    {f : Fin n → Pt s .euclidean → ℝ}
    (hf : f ∈ separatedTuples s .euclidean n) (i : Fin n) :
    (f i : InfiniteLattice.AmbientSpace → ℝ) ∈ InfiniteLattice.compactTestFunctions := by
  have hcont : Continuous (fun x : Fin 4 → ℝ => f i x) :=
    ((isC1Fn_euclidean_iff (f i)).1 (hf.1 i).1).continuous
  have hsupp : HasCompactSupport (fun x : Fin 4 → ℝ => f i x) :=
    (((mem_separatedTuples_r4_iff f).1 hf).1 i).2.1
  exact ⟨hcont.measurable, hcont.bounded_above_of_compact_support hsupp, hsupp⟩
theorem tendsto_sum_singletonFree {ι : Type*} {l : Filter ι} {s : Conventions.StandingParameters}
    (S : TupleMapFamily s .euclidean) (c : ι → (k : ℕ) → (Fin k → Pt s .euclidean → ℝ) → ℂ)
    (hc : ∀ (k : ℕ) (hk : 2 ≤ k) (g : separatedTuples s .euclidean k),
      Tendsto (fun j => c j k g.1) l (𝓝 (S k hk g : ℂ)))
    (f : separatedTuples s .euclidean n) :
    Tendsto (fun j => ∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts,
        c j J.card fun k => f.1 (J.orderEmbOfFin rfl k)) l
      (𝓝 (moments S (toAllSeparated f) : ℂ)) := by
  have hm : ((moments S (toAllSeparated f) : ℝ) : ℂ) =
      ∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts,
        ((mapFamilyBlockFactor S f J : ℝ) : ℂ) := by
    change ((∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts,
      mapFamilyBlockFactor S f J : ℝ) : ℂ) = _
    push_cast
    rfl
  rw [hm]
  refine tendsto_finsetSum _ fun π hπ => tendsto_finsetProd _ fun J hJ => ?_
  have h2 : 2 ≤ J.card := two_le_card_of_mem_singletonFree hπ hJ
  rw [mapFamilyBlockFactor, dif_pos h2]
  exact hc J.card h2 (restrictSeparated f J)
theorem eq_add_of_tendsto_of_eventually {ι : Type*} {l : Filter ι} [l.NeBot] {u v w : ι → ℂ}
    {x y z a a' : ℝ}
    (hu : Tendsto u l (𝓝 (x : ℂ))) (hv : Tendsto v l (𝓝 (y : ℂ))) (hw : Tendsto w l (𝓝 (z : ℂ)))
    (h : ∀ᶠ j in l, u j = (a : ℂ) * v j + (a' : ℂ) * w j) : x = a * y + a' * z := by
  have h₁ : Tendsto (fun j => (a : ℂ) * v j + (a' : ℂ) * w j) l
      (𝓝 ((a : ℂ) * (y : ℂ) + (a' : ℂ) * (z : ℂ))) :=
    (hv.const_mul _).add (hw.const_mul _)
  have h₂ := tendsto_nhds_unique (hu.congr' h) h₁
  exact_mod_cast h₂
theorem exists_hasDiameterLE_of_isCompact {Y : Set (Fin 4 → ℝ)} (hY : IsCompact Y) :
    ∃ C : ℝ, ∀ r : ℝ, C ≤ r → TestFunctions.HasDiameterLE Y r := by
  obtain ⟨R, hR⟩ := hY.isBounded.exists_norm_le
  refine ⟨4 * R, fun r hr x hx y hy => ?_⟩
  have h₁ := SeparatedTuplesR4.euclidNormVec_le_two_mul_norm (x - y)
  have h₂ : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  linarith [hR x hx, hR y hy]
theorem torusTransport_linComb (ht : ToriAtArbitraryCouplings.TransportToTorus.Properties)
    (σ : ToriAtArbitraryCouplings.TorusSide) {f h : (Fin 4 → ℝ) → ℝ} (hf : HasCompactSupport f)
    (hh : HasCompactSupport h)
    (hd : TestFunctions.HasDiameterLE (tsupport f ∪ tsupport h) (σ.length / 2)) (a a' : ℝ) :
    σ.torusTransport (a • f + a' • h) = a • σ.torusTransport f + a' • σ.torusTransport h := by
  have hs : ∀ g : (Fin 4 → ℝ) → ℝ, σ.closedSupport .euclidean g = tsupport g := fun g =>
    SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
  have hc : ∀ g : (Fin 4 → ℝ) → ℝ, HasCompactSupport g → tsupport g ⊆ tsupport f ∪ tsupport h →
      σ.HasCompactSupportWithin (tsupport f ∪ tsupport h) g := fun g hg hsub => by
    refine ⟨?_, ?_⟩
    · rw [hs g]
      exact (SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) _).2 hg
    · rw [hs g]
      exact hsub
  exact ((ht σ _ hd).2 f h (hc f hf Set.subset_union_left) (hc h hh Set.subset_union_right)).1 a a'
variable {D : GrowingTori.GrowthParameters} {g : ℝ} {s : Conventions.StandingParameters}
theorem toral_centredMomentAt_eq
    (h₁ : ConnectedFunctions.CentredIdentityAtAllFunctions)
    (hg : 0 < g) (Q : ToralSequence D g) (j : ℕ+) (f : Fin n → Pt s .euclidean → ℝ) :
    Q.centredMomentAt hg j f =
      ∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts,
        Q.cumulant j fun k => f (J.orderEmbOfFin rfl k) := by
  refine (centredMomentFn_ofRealTuple_eq_sum h₁ (Q.couplingDataAt hg j) _).trans ?_
  exact Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => rfl
theorem gibbs_centredMomentAt_eq (h₂ : InfiniteLattice.CenteredIdentity.Statement)
    (Q : PeriodicGibbsSequence D g) (j : ℕ+) (f : separatedTuples s .euclidean n) :
    Q.centredMomentAt j f.1 =
      ∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts,
        Q.cumulant j fun k => f.1 (J.orderEmbOfFin rfl k) := by
  have hp : IsProbabilityMeasure (Q.measure j) := (Q.measure_mem j).1.1
  obtain ⟨-, -, hid⟩ := h₂ (D.standingParams (Q.passage j).K 1) (Q.measure j) hp
  exact (hid n f.1 (apply_mem_compactTestFunctions f.2)).trans (ursellPartitionSum_eq_sum _ _)
theorem isLinearInEachArgument_of_toral
    (h₁ : ConnectedFunctions.CentredIdentityAtAllFunctions)
    (ht : ToriAtArbitraryCouplings.TransportToTorus.Properties)
    (hg : 0 < g) (Q : ToralSequence D g) {S : TupleMapFamily s .euclidean}
    (hQ : Q.Defines S) (hn : 2 ≤ n) :
    EntrywiseMultilinearity.IsLinearInEachComponent (S n hn) := by
  intro i a a' h h' h'' hdiff hh''
  have hcf : HasCompactSupport (fun x : Fin 4 → ℝ => h.1 i x) :=
    (((mem_separatedTuples_r4_iff h.1).1 h.2).1 i).2.1
  have hcf' : HasCompactSupport (fun x : Fin 4 → ℝ => h'.1 i x) :=
    (((mem_separatedTuples_r4_iff h'.1).1 h'.2).1 i).2.1
  obtain ⟨C, hC⟩ := exists_hasDiameterLE_of_isCompact (hcf.isCompact.union hcf'.isCompact)
  have hside : ∀ᶠ j in (atTop : Filter ℕ+), 2 * C ≤ Q.side j :=
    Q.tendsto_side.eventually_ge_atTop (2 * C)
  refine eq_add_of_tendsto_of_eventually (hQ n hn h'') (hQ n hn h) (hQ n hn h')
    (hside.mono fun j hj => ?_)
  set X := Q.couplingDataAt hg j with hX
  let σ : ToriAtArbitraryCouplings.TorusSide := ⟨D.L, D.admissible.factor_admissible, Q.sideExponent j⟩
  have hd : TestFunctions.HasDiameterLE
      (tsupport (fun x : Fin 4 → ℝ => h.1 i x) ∪ tsupport (fun x : Fin 4 → ℝ => h'.1 i x))
      (σ.length / 2) :=
    hC _ (by change C ≤ Q.side j / 2; linarith)
  have hlin := torusTransport_linComb ht σ hcf hcf' hd a a'
  have htr : SchwingerFunctions.periodizeAll D.L (Q.sideExponent j) h''.1 =
      Function.update (SchwingerFunctions.periodizeAll D.L (Q.sideExponent j) h.1) i
        (a • SchwingerFunctions.periodizeAll D.L (Q.sideExponent j) h.1 i +
          a' • SchwingerFunctions.periodizeAll D.L (Q.sideExponent j) h'.1 i) := by
    funext l
    by_cases hl : l = i
    · subst hl
      rw [Function.update_self, hh'']
      change TestFunctions.periodize _ _ = _
      rw [EntrywiseMultilinearity.updateLinComb, Function.update_self]
      exact hlin
    · rw [Function.update_of_ne hl, hh'']
      change TestFunctions.periodize _ _ = TestFunctions.periodize _ _
      rw [EntrywiseMultilinearity.updateLinComb, Function.update_of_ne hl]
  have hlinear : IsRealValuedAndSlotLinear Set.univ (X.cumulantReal (n := n)) :=
    slotLinear_cumulantReal X ((h₁ X).2.1 n hn).1.1
  have := update_linComb_of_slotLinear hlinear (fun _ _ _ => Set.mem_univ _)
    (f := SchwingerFunctions.periodizeAll D.L (Q.sideExponent j) h.1)
    (f' := SchwingerFunctions.periodizeAll D.L (Q.sideExponent j) h'.1)
    (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) (i := i)
    (fun l hl => by
      change TestFunctions.periodize _ _ = TestFunctions.periodize _ _
      rw [hdiff.2.2 l hl]) a a'
  exact (congrArg X.cumulantReal htr).trans this
theorem isLinearInEachArgument_of_gibbs (h₂ : InfiniteLattice.CenteredIdentity.Statement)
    (Q : PeriodicGibbsSequence D g) {S : TupleMapFamily s .euclidean}
    (hQ : Q.Defines S) (hn : 2 ≤ n) :
    EntrywiseMultilinearity.IsLinearInEachComponent (S n hn) := by
  intro i a a' h h' h'' hdiff hh''
  refine eq_add_of_tendsto_of_eventually (hQ n hn h'') (hQ n hn h) (hQ n hn h')
    (Eventually.of_forall fun j => ?_)
  have hp : IsProbabilityMeasure (Q.measure j) := (Q.measure_mem j).1.1
  obtain ⟨⟨-, hF⟩, hlin, -⟩ := h₂ (D.standingParams (Q.passage j).K 1) (Q.measure j) hp
  obtain ⟨F, hF, -⟩ := hF
  have hsmul : ∀ (c : ℝ) (u : InfiniteLattice.AmbientSpace → ℝ),
      u ∈ InfiniteLattice.compactTestFunctions → c • u ∈ InfiniteLattice.compactTestFunctions := by
    intro c u hu
    rw [← hF] at hu ⊢
    exact F.smul_mem c hu
  have := update_linComb_of_slotLinear (slotLinear_ursellFunction (Q.measure j) (hlin n hn)) hsmul
    (f := h.1) (f' := h'.1) (apply_mem_compactTestFunctions h.2)
    (apply_mem_compactTestFunctions h'.2) (i := i)
    hdiff.2.2 a a'
  change InfiniteLattice.ursellFunction (Q.measure j) n h''.1 = _
  rw [hh'']
  exact this
theorem isConnectedFamily_of_isLinearInEachArgument (he : EntrywiseMultilinearity.Statement)
    {S : TupleMapFamily s .euclidean}
    (hS : ∀ (n : ℕ) (hn : 2 ≤ n), EntrywiseMultilinearity.IsLinearInEachComponent (S n hn)) :
    IsConnectedFamily S := by
  have hm : ∀ (n : ℕ) (hn : 2 ≤ n), IsTupleMultilinear (S n hn) := fun n hn =>
    (((he s).1 n (by omega)).2.1 _).2 (hS n hn)
  exact ⟨hm, ⟨S, hm⟩, rfl⟩
theorem centredMomentsAndTheirLimits_holds
    (h₁ : ConnectedFunctions.CentredIdentityAtAllFunctions)
    (h₂ : InfiniteLattice.CenteredIdentity.Statement)
    (h₃ : AmbientPoints.CentredOfConnectedFamilyProperties)
    (h₄ : EntrywiseMultilinearity.Statement)
    (h₅ : ToriAtArbitraryCouplings.TransportToTorus.Properties) : CentredMomentsAndTheirLimits := by
  refine ⟨fun X => ⟨fun n f _ => centredMomentFn_ofRealTuple_eq_sum h₁ X f, fun n hn => ?_⟩, ?_, ?_, ?_⟩
  · exact slotLinear_cumulantReal X (((h₁ X).2.2.2.2.1).2.1 n hn).1
  · intro s β _ ν hν
    obtain ⟨-, hlin, hid⟩ := h₂ s ν hν.1
    exact ⟨fun n f hf => (hid n f hf).trans rfl, fun n hn => slotLinear_ursellFunction ν (hlin n hn)⟩
  · intro D g hg s S
    refine ⟨fun Q hQ => ⟨fun n f => ?_, isConnectedFamily_of_isLinearInEachArgument h₄ fun n hn =>
      isLinearInEachArgument_of_toral h₁ h₅ hg Q hQ hn⟩,
      fun Q hQ => ⟨fun n f => ?_, isConnectedFamily_of_isLinearInEachArgument h₄ fun n hn =>
      isLinearInEachArgument_of_gibbs h₂ Q hQ hn⟩⟩
    · exact (tendsto_sum_singletonFree S (fun j k u => Q.cumulant j u)
        (fun k hk u => hQ k hk u) f).congr fun j =>
          (toral_centredMomentAt_eq h₁ hg Q j f.1).symm
    · exact (tendsto_sum_singletonFree S (fun j k u => Q.cumulant j u)
        (fun k hk u => hQ k hk u) f).congr fun j =>
          (gibbs_centredMomentAt_eq h₂ Q j f).symm
  · intro s S
    obtain ⟨-, -, hm, hf, -⟩ := h₃ s .euclidean S
    exact ⟨hm, hf⟩
end CumulantLimits.CentredMoments
end YangMills.Construction
end
