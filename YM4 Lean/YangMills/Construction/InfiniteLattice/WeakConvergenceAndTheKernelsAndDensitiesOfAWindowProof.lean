import YangMills.Construction.InfiniteLattice.KernelAndOperatorOfAWindowAtOneSpacing
import YangMills.Construction.InfiniteLattice.MetricForTheWeakTopologyOfRealTestsProof
import YangMills.Construction.InfiniteLattice.ObjectsOfAWindowOfTheLatticeOfACutoffAreFormed
import YangMills.Construction.InfiniteLattice.TorusConfigurationsAsPeriodicConfigurations
import YangMills.Construction.InfiniteLattice.WeakConvergenceAndTheKernelsAndDensitiesOfAWindow
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfExtensionsAreNonEmptyAndClosed
import YangMills.Construction.InfiniteLattice.WindowDensitiesAtOneSpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.WeakConvergence
open YangMills.Construction.InfiniteLattice YangMills.Construction.InfiniteLattice.PeriodicExtensions
section Sequences
variable {a : ℝ}
theorem abs_value_sub_value_le_norm [CompactSpace (GaugeField a)] (ν : RealWeakState a)
    (A B : C(GaugeField a, ℝ)) : |ν.value A - ν.value B| ≤ ‖A - B‖ := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicExtensions.RealWeakState.abs_value_sub_le_norm <;> assumption
theorem abs_value_sub_le_add_norm [CompactSpace (GaugeField a)] (μ ν : RealWeakState a)
    (A B : C(GaugeField a, ℝ)) :
    |μ.value A - ν.value A| ≤ |μ.value B - ν.value B| + 2 * ‖A - B‖ := by
  have h1 := abs_le.1 (abs_value_sub_value_le_norm μ A B)
  have h2 := abs_le.1 (abs_value_sub_value_le_norm ν A B)
  have h3 := abs_le.1 (le_refl |μ.value B - ν.value B|)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
theorem frequentlyClose_of_hasSubseqTendsto {μ : ℕ → RealWeakState a}
    {ν : RealWeakState a} (h : HasSubseqTendsto μ ν) : FrequentlyClose μ ν := by
  obtain ⟨φ, hφ, hc⟩ := h
  intro 𝒜 ε hε
  refine Nat.frequently_atTop_iff_infinite.1 ?_
  have hall : ∀ᶠ n in atTop, ∀ A ∈ 𝒜, |(μ (φ n)).value A - ν.value A| < ε :=
    (Filter.eventually_all_finset 𝒜).2 fun A _ => by
      filter_upwards [(Metric.tendsto_nhds.1 (hc A)) ε hε] with n hn
      rw [Real.dist_eq] at hn
      exact hn
  exact hφ.tendsto_atTop.frequently hall.frequently
theorem hasSubseqTendsto_of_frequentlyClose [CompactSpace (GaugeField a)]
    (F : ℕ+ → C(GaugeField a, ℝ))
    (hF : ∀ (H : C(GaugeField a, ℝ)) (ε : ℝ), 0 < ε → ∃ k, ‖H - F k‖ < ε)
    {μ : ℕ → RealWeakState a} {ν : RealWeakState a} (h : FrequentlyClose μ ν) :
    HasSubseqTendsto μ ν := by
  classical
  have hfreq : ∀ n : ℕ, ∃ᶠ k in atTop, ∀ r ∈ Finset.range (n + 1),
      |(μ k).value (F r.succPNat) - ν.value (F r.succPNat)| < 1 / ((n : ℝ) + 1) := fun n => by
    have hinf := h ((Finset.range (n + 1)).image fun r => F r.succPNat) (1 / ((n : ℝ) + 1))
      (by positivity)
    exact (Nat.frequently_atTop_iff_infinite.2 hinf).mono fun k hk r hr =>
      hk _ (Finset.mem_image_of_mem _ hr)
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_frequently hfreq
  refine ⟨φ, hφ, fun G => ?_⟩
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := hF G (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by positivity)
  refine ⟨max N k.natPred, fun n hn => ?_⟩
  have h1 := abs_value_sub_le_add_norm (μ (φ n)) ν G (F k)
  have h2 := hP n k.natPred
    (Finset.mem_range.2 (Nat.lt_succ_of_le ((le_max_right _ _).trans hn)))
  rw [PNat.succPNat_natPred] at h2
  have h3 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    have : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [Real.dist_eq]
  change |(μ (φ n)).value G - ν.value G| < ε
  linarith
theorem tendstoWeakly_congr_measure {ρ ρ' : ℕ → RealWeakState a} {ν : RealWeakState a}
    (h : ∀ n, (ρ n).measure = (ρ' n).measure) (hc : RealWeakState.TendstoWeakly ρ ν) :
    RealWeakState.TendstoWeakly ρ' ν := by
  intro F
  simpa only [h] using hc F
theorem tendstoWeakly_comp {ρ : ℕ → RealWeakState a} {ν : RealWeakState a}
    (hc : RealWeakState.TendstoWeakly ρ ν) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    RealWeakState.TendstoWeakly (ρ ∘ ψ) ν :=
  fun F => (hc F).comp hψ
end Sequences
section Window
variable {a : ℝ} (W : LinkWindow a)
theorem continuous_restrictRim : Continuous W.restrictRim :=
  continuous_pi fun b => (continuous_apply (b : Link a)).comp continuous_subtype_val
theorem continuous_stateDensity (ha : 0 < a) (β : ℝ) (ν : RealWeakState a)
    (hk : Continuous fun x : W.Assignments × LinkVariables W.rim =>
      W.rimKernel ha β x.1 x.2)
    (C : ℝ) (hb : ∀ V η, |W.rimKernel ha β V η| ≤ C) :
    Continuous (W.stateDensity ha β ν) := by
  have : SecondCountableTopology YangMills.Construction.Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology
      YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hV : ∀ U : GaugeField a, Continuous fun V : W.Assignments =>
      W.rimKernel ha β V (W.restrictRim U) := fun U => by
    have hc : Continuous fun V : W.Assignments =>
        ((V, W.restrictRim U) : W.Assignments × LinkVariables W.rim) :=
      continuous_id.prodMk continuous_const
    have h := hk.comp hc
    exact h
  have hU : ∀ V : W.Assignments, Continuous fun U : GaugeField a =>
      W.rimKernel ha β V (W.restrictRim U) := fun V => by
    have hc : Continuous fun U : GaugeField a =>
        ((V, W.restrictRim U) : W.Assignments × LinkVariables W.rim) :=
      continuous_const.prodMk (continuous_restrictRim W)
    have h := hk.comp hc
    exact h
  exact show Continuous fun V : W.Assignments =>
      ∫ U, W.rimKernel ha β V (W.restrictRim U) ∂ν.measure from
    continuous_of_dominated (bound := fun _ => C)
      (fun V => (hU V).aestronglyMeasurable)
      (fun V => ae_of_all _ fun U => by
        rw [Real.norm_eq_abs]
        exact hb V (W.restrictRim U))
      (integrable_const C) (ae_of_all _ hV)
end Window
section Sides
variable {L K : ℕ} {β : ℝ}
theorem torusSide_injective (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L)
    {m n : ℕ}
    (h : YangMills.Construction.PeriodicLattice.torusSide L m =
      YangMills.Construction.PeriodicLattice.torusSide L n) : m = n := by
  have hL2 : (1 : ℝ) < L := by
    have : 13 ≤ L := hL.2
    exact_mod_cast (by omega : 1 < L)
  have h' : (L : ℝ) ^ m = (L : ℝ) ^ n := by
    simpa [YangMills.Construction.PeriodicLattice.torusSide] using h
  exact pow_right_injective₀ (by linarith) hL2.ne' h'
theorem exists_isLiftedAlongSides
    (hprob : ∀ m : ℕ, 0 < m → IsProbabilityMeasure (liftedWilsonMeasure L m K β))
    (ℓ : ℕ → ℝ) (hℓ : ∀ i, 1 ≤ i → ℓ i ∈ YangMills.Construction.PeriodicLattice.torusSides L) :
    ∃ ρ, IsLiftedAlongSides L K β ℓ ρ := by
  have hex : ∀ i : ℕ,
      ∃ ρ : RealWeakState (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)),
      1 ≤ i → IsLiftedMeasureAtSide L K β (ℓ i) ρ := by
    intro i
    by_cases hi : 1 ≤ i
    · obtain ⟨m, hm, he⟩ := hℓ i hi
      exact ⟨⟨liftedWilsonMeasure L m K β, hprob m hm⟩, fun _ => ⟨m, hm, he, rfl⟩⟩
    · exact ⟨⟨liftedWilsonMeasure L 1 K β, hprob 1 one_pos⟩, fun h => absurd h hi⟩
  choose ρ hρ using hex
  exact ⟨ρ, hρ⟩
theorem mem_limitsOfLiftedMeasures_iff_hasSubseqTendsto
    (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L)
    (hEq : limitsOfLiftedMeasures L K β = subsequentialLimits L K β)
    {ρ : ℕ → RealWeakState (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ))}
    (hρ : IsLiftedAlongSides L K β
      (fun i => YangMills.Construction.PeriodicLattice.torusSide L i) ρ)
    (ν : RealWeakState (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ))) :
    ν ∈ limitsOfLiftedMeasures L K β ↔ HasSubseqTendsto ρ ν := by
  have hmeas : ∀ i, 1 ≤ i → (ρ i).measure = liftedWilsonMeasure L i K β := fun i hi => by
    obtain ⟨m, -, he, hr⟩ := hρ i hi
    have hm := torusSide_injective hL he
    subst hm
    exact hr
  rw [hEq]
  constructor
  · rintro ⟨i, ρ', hi, h1, h2, hc⟩
    exact ⟨i, hi, tendstoWeakly_congr_measure (fun n => (h2 n).trans (hmeas _ (h1 n)).symm) hc⟩
  · rintro ⟨φ, hφ, hc⟩
    have h1 : ∀ n, 1 ≤ φ (n + 1) := fun n => by
      have := hφ.le_apply (x := n + 1)
      omega
    exact ⟨fun n => φ (n + 1), fun n => ρ (φ (n + 1)), fun m n h => hφ (by omega), h1,
      fun n => hmeas _ (h1 n), tendstoWeakly_comp hc (tendsto_add_atTop_nat 1)⟩
theorem mem_limitsOfLiftedMeasures_of_subseq
    (hSeq : ∀ ν : RealWeakState (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)),
      IsLimitOfLiftedMeasures L K β ν ↔ ∃ ℓ ρ, IsLimitAlongSideSequence L K β ℓ ρ ν)
    {ℓ : ℕ → ℝ} (hℓ : SidesTendToInfinity L ℓ)
    {ρ : ℕ → RealWeakState (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ))}
    (hρ : IsLiftedAlongSides L K β ℓ ρ) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ν : RealWeakState (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ))}
    (hc : RealWeakState.TendstoWeakly (ρ ∘ φ) ν) :
    ν ∈ limitsOfLiftedMeasures L K β := by
  have h1 : ∀ n, 1 ≤ φ (n + 1) := fun n => by
    have := hφ.le_apply (x := n + 1)
    omega
  have hinj : Function.Injective fun n => φ (n + 1) := fun m n h => by
    have := hφ.injective h
    omega
  refine (hSeq ν).2 ⟨fun n => ℓ (φ (n + 1)), fun n => ρ (φ (n + 1)),
    ⟨fun i _ => hℓ.1 _ (h1 i), fun s => ?_⟩, fun i _ => hρ _ (h1 i),
    tendstoWeakly_comp hc (tendsto_add_atTop_nat 1)⟩
  refine ((hℓ.2 s).preimage hinj.injOn).subset ?_
  rintro i ⟨-, hs⟩
  exact ⟨h1 i, hs⟩
end Sides
theorem exists_hasSubseqTendsto
    (hCompact : EveryStateSequenceHasWeaklyConvergentSubsequence.Statement)
    (s : YangMills.Construction.Conventions.StandingParameters)
    (μ : ℕ → RealWeakState
      (YangMills.Construction.PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ))) :
    ∃ ν, HasSubseqTendsto μ ν := by
  obtain ⟨i, ν, hi, hc⟩ := hCompact s fun k => μ k
  have hs : Tendsto Nat.succPNat (atTop : Filter ℕ) atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun c hc => by
      rw [← PNat.coe_le_coe, Nat.succPNat_coe]
      omega⟩
  exact ⟨ν, fun n => i n.succPNat, fun m n h => hi (Nat.succPNat_strictMono h),
    fun F => (hc F).comp hs⟩
theorem weakConvergenceWindowStatement_holds
    (hSpace : GaugeFieldSpace.Statement)
    (hCompact : EveryStateSequenceHasWeaklyConvergentSubsequence.Statement)
    (hTor : LimitSetIsNonemptyClosed)
    (hSeq : SequentialLimitCharacterization)
    (hDens : YangMills.Construction.WindowDensities.Statement)
    (hOp : WindowKernelOperatorProperties)
    (hPer : TorusFieldsAsPeriodic.Statement)
    (hFormed : YangMills.Construction.CutoffLattice.WindowObjectsWellDefined) :
    WeakConvergenceWindowStatement := by
  intro L K hL hK β hβ ha
  let s : YangMills.Construction.Conventions.StandingParameters := ⟨L, hL, ⟨K, hK⟩, 1⟩
  let d : YangMills.Construction.CutoffLinks.CutoffData := ⟨s, β, hβ⟩
  have hP : GaugeFieldSpace.ProductStructure
      (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)) := (hSpace d).1
  obtain ⟨-, -, -, -, hCS, -⟩ := hP
  have hD : GaugeFieldSpace.ExistsDenseLocalSequence
      (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)) := (hSpace d).2.2.2.1
  obtain ⟨F, hF, -⟩ := hD
  have hF' : ∀ (H : C(GaugeField (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)), ℝ))
      (ε : ℝ), 0 < ε → ∃ k, ‖H - F k‖ < ε := fun H ε hε => by
    obtain ⟨k, hk⟩ := hF H ε hε
    exact ⟨k, by rwa [YangMills.Construction.CutoffLattice.supNorm_eq_norm] at hk⟩
  have hiff : ∀ (μ : ℕ → RealWeakState (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)))
      (ν : RealWeakState (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ))),
      FrequentlyClose μ ν ↔ HasSubseqTendsto μ ν := fun μ ν =>
    ⟨hasSubseqTendsto_of_frequentlyClose F hF', frequentlyClose_of_hasSubseqTendsto⟩
  have hprob : ∀ m : ℕ, 0 < m → IsProbabilityMeasure (liftedWilsonMeasure L m K β) :=
    fun m hm => (hPer ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ β hβ).2.2.1.1
  have hT : limitsOfLiftedMeasures L K β = subsequentialLimits L K β ∧
      (limitsOfLiftedMeasures L K β).Nonempty := ⟨(hTor s β hβ).1, (hTor s β hβ).2.1⟩
  have hW : TorusFieldsAsPeriodic.SubsequentialLimitsAreTorusLimits L K β :=
    (hPer s β hβ).2.2.2.1
  have hsub : ∀ μ : ℕ → RealWeakState (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)),
      ∃ ν, HasSubseqTendsto μ ν := exists_hasSubseqTendsto hCompact s
  refine ⟨hiff, ⟨?_, ?_, ?_⟩, hsub, ⟨hT.2, ?_⟩, fun W => ⟨?_, ?_⟩⟩
  · exact exists_isLiftedAlongSides hprob _ fun i hi => ⟨i, hi, rfl⟩
  · intro ρ hρ ν
    have h := mem_limitsOfLiftedMeasures_iff_hasSubseqTendsto hL hT.1 hρ ν
    exact ⟨h.trans (hiff ρ ν).symm, h⟩
  · intro μ
    constructor
    · intro h
      exact ⟨⟨μ, h.1⟩, (hW ⟨μ, h.1⟩).1.1 h, rfl⟩
    · rintro ⟨ν, hν, rfl⟩
      exact (hW ν).1.2 hν
  · intro ℓ hℓ
    refine ⟨exists_isLiftedAlongSides hprob ℓ hℓ.1, fun ρ hρ => ?_⟩
    obtain ⟨ν, φ, hφ, hc⟩ := hsub ρ
    exact ⟨ν, mem_limitsOfLiftedMeasures_of_subseq
      (fun ν => (hSeq L K hL hK β hβ ν).1) hℓ hρ hφ hc, φ, hφ, hc⟩
  · obtain ⟨⟨hk, hkb, hqb, hΔ⟩, -, -, -, -, -, -⟩ := hDens L K hL hK β hβ W
    obtain ⟨⟨hfin, -, hbd⟩, -⟩ := hFormed L K hL hK β hβ W
    refine ⟨hfin, hbd, hk, hkb, (hOp d W).1.1, fun ν => ⟨?_, hqb ν⟩,
      fun μ ν => (hΔ μ ν).trans_lt ENNReal.ofReal_lt_top⟩
    refine continuous_stateDensity W ha β ν hk (Real.exp (2 * β * W.faceCount)) fun V η => ?_
    rw [abs_of_nonneg ((Real.exp_pos _).le.trans (hkb V η).1)]
    exact (hkb V η).2
  · obtain ⟨⟨-, -, -, hΔ⟩, -, -, -, -, h6, -⟩ := hDens L K hL hK β hβ W
    intro μ ν hc
    have hq := h6 μ ν hc
    refine ⟨hq, ?_⟩
    have hup : Tendsto (fun i => ENNReal.ofReal (Real.exp (2 * β * W.faceCount) *
        YangMills.Construction.TestFunctions.uniformNorm fun V : W.Assignments =>
          W.stateDensity ha β (μ i) V - W.stateDensity ha β ν V)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (hq.const_mul (Real.exp (2 * β * W.faceCount)))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun _ => zero_le) fun i => ?_
    have hsym : (YangMills.Construction.TestFunctions.uniformNorm fun V : W.Assignments =>
        W.stateDensity ha β ν V - W.stateDensity ha β (μ i) V) =
        YangMills.Construction.TestFunctions.uniformNorm fun V : W.Assignments =>
          W.stateDensity ha β (μ i) V - W.stateDensity ha β ν V := by
      simp only [YangMills.Construction.TestFunctions.uniformNorm, norm_sub_rev]
    have := hΔ (μ i) ν
    rwa [hsym] at this
end YangMills.Construction.InfiniteLattice.WeakConvergence
