import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.InfiniteLattice.SumsIntegralsAndImageMeasuresOfTheStatesAreFormed
import YangMills.Construction.SourcesOnAFlow.MeanInAPeriodicExtension
import YangMills.Construction.SystemOfAdmissibleConstants.MeansAndValuesOfACellFunction
import YangMills.Construction.SystemOfAdmissibleConstants.OnePointBoundsFromTheInequality
import YangMills.Construction.SystemOfAdmissibleConstants.SizeOfAnObservableOnABall
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSide
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter YangMills.Construction.TestFunctions
open scoped Topology
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
open YangMills.Construction.ChessboardTori YangMills.Construction.ReflectedCopies YangMills.Construction.BoundsOnEverySide
open YangMills.Construction.InfiniteLattice (AmbientSpace GaugeField ElementaryPlaquette faceEnergy
  smearedEnergy periodicGibbsSet liftedWilsonMeasure IsBoundedBorelCompactlySupported IsPeriodicGibbs)
open YangMills.Construction.TorusMetric (euclidNormVec)
private theorem abs_apply_le_euclidNormVec (v : AmbientSpace) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem continuous_of_isLipschitzFor {f : AmbientSpace → ℝ} (hf : IsLipschitzFor euclidDistR4 f) :
    Continuous f := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_r4 <;> assumption
private theorem isBoundedBorelCompactlySupported_of_closedBall {f : AmbientSpace → ℝ} {x : AmbientSpace}
    {R : ℝ} (hR : 0 ≤ R)
    (hf : IsLipschitzFor euclidDistR4 f) (hs : tsupport f ⊆ closedBallR4 x R) :
    IsBoundedBorelCompactlySupported f := by
  have hc := continuous_of_isLipschitzFor hf
  have hcomp : HasCompactSupport f := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport f) ?_
    refine (Metric.isBounded_closedBall (x := x) (r := R)).subset fun y hy => ?_
    rw [Metric.mem_closedBall]
    refine (dist_pi_le_iff hR).mpr fun μ => ?_
    rw [Real.dist_eq]
    exact (abs_apply_le_euclidNormVec (y - x) μ).trans (hs hy)
  exact ⟨hc.measurable, hc.bounded_above_of_compact_support hcomp, hcomp⟩
private theorem smearedEnergy_facts {a : ℝ} (ha : 0 < a)
    (hForm : InfiniteLattice.WellDefinedStates.Statement)
    {g : AmbientSpace → ℝ} (hg : IsBoundedBorelCompactlySupported g) :
    {p : ElementaryPlaquette a | g p.center ≠ 0}.Finite ∧
      Measurable (smearedEnergy g : GaugeField a → ℝ) ∧
      ∃ C : ℝ, ∀ U : GaugeField a, |smearedEnergy g U| ≤ C := by
  obtain ⟨h, -, hobs, -⟩ := (hForm.1 a ha).2.2.1 g hg
  refine ⟨h, ?_, ?_⟩
  · have := Complex.measurable_re.comp hobs.1
    simpa [Function.comp_def] using this
  · obtain ⟨C, hC⟩ := hobs.2
    exact ⟨C, fun U => by simpa using hC U⟩
private theorem smearedEnergy_finset_sum {a : ℝ} {ι : Type*} (T : Finset ι) (g : ι → AmbientSpace → ℝ)
    {f : AmbientSpace → ℝ} (hf : ∀ x, f x = ∑ i ∈ T, g i x)
    (hfin : ∀ i ∈ T, {p : ElementaryPlaquette a | g i p.center ≠ 0}.Finite) (U : GaugeField a) :
    smearedEnergy f U = ∑ i ∈ T, smearedEnergy (g i) U := by
  have h := finsum_sum_comm T (fun (p : ElementaryPlaquette a) i => faceEnergy U p • g i p.center)
    (fun i hi => (hfin i hi).subset fun p hp h0 => hp (by simp [h0]))
  simp only [smearedEnergy]
  rw [← h]
  refine finsum_congr fun p => ?_
  rw [hf, Finset.smul_sum]
private def IsCutoffMeasure (L : ℕ) (K : ℕ+) (β : ℝ)
    (μ : Measure (GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))) : Prop :=
  μ ∈ periodicGibbsSet L K β ∨ ∃ m : ℕ+, μ = liftedWilsonMeasure L m K β
private theorem IsCutoffMeasure.isProbabilityMeasure {L : ℕ} {K : ℕ+} {β : ℝ}
    (hForm : InfiniteLattice.WellDefinedStates.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hβ : 0 < β)
    {μ : Measure (GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))}
    (h : IsCutoffMeasure L K β μ) : IsProbabilityMeasure μ := by
  rcases h with h | ⟨m, rfl⟩
  · have h' : IsPeriodicGibbs β μ := h
    exact h'.1.1
  · exact hForm.2.1 L K m hL K.pos m.pos β hβ
private theorem torusAverage_eq_integral (hForm : InfiniteLattice.WellDefinedStates.Statement)
    (D : ChessboardSetup) (m' : ℕ+) {h : AmbientSpace → ℝ} (hh : IsBoundedBorelCompactlySupported h) :
    torusAverage D m' (ReflectionsAndOneInsertion.complexSmeared D h) =
      ((∫ U, smearedEnergy h U ∂liftedWilsonMeasure D.L m' D.K D.β : ℝ) : ℂ) := by
  have hprob : IsProbabilityMeasure (liftedWilsonMeasure D.L m' D.K D.β) :=
    hForm.2.1 D.L D.K m' D.isAdmissible D.K.pos m'.pos D.β D.beta_pos
  have hae : AEMeasurable (InfiniteLattice.liftField D.L m' ((D.K : ℕ) : ℤ))
      (PeriodicLattice.wilsonGibbsMeasure D.L m' D.K D.β) := by
    by_contra hn
    have h0 : liftedWilsonMeasure D.L m' D.K D.β = 0 := Measure.map_of_not_aemeasurable hn
    exact IsProbabilityMeasure.ne_zero _ h0
  have hm := (smearedEnergy_facts (a := PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))
    (zpow_pos (by linarith [D.one_lt_factor]) _) hForm hh).2.1
  have e : (∫ U, smearedEnergy h U ∂liftedWilsonMeasure D.L m' D.K D.β) =
      ∫ U, smearedEnergy h (InfiniteLattice.liftField D.L m' ((D.K : ℕ) : ℤ) U)
        ∂PeriodicLattice.wilsonGibbsMeasure D.L m' D.K D.β :=
    integral_map hae hm.aestronglyMeasurable
  rw [e]
  exact integral_complex_ofReal
private theorem mean_near_constant_of_small_support
    (hMV : CellFunctionMeanBounds)
    (hForm : InfiniteLattice.WellDefinedStates.Statement)
    {L : ℕ} {K : ℕ+} {β A b : ℝ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hβ : 0 < β)
    (hK : 2 ≤ (K : ℕ)) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hI : CopyInequality ⟨⟨L, hL, K, 1⟩, β, hβ⟩ A b) (α : AmbientSpace) {p : AmbientSpace → ℝ}
    (hlip : IsLipschitzFor euclidDistR4 p) (hc : IsBoundedBorelCompactlySupported p)
    (hcube : ∀ x, p x ≠ 0 → ∀ μ, |x μ - α μ| < 1 / 16)
    (hball : ∀ x, p x ≠ 0 → x ∈ closedBallR4 α (1 / 8)) :
    ∃ κ : ℝ, ∀ μ, IsCutoffMeasure L K β μ →
      |(∫ U, smearedEnergy p U ∂μ) - κ| ≤ copyBound A b 1 (1 / 8) p := by
  set D : ChessboardSetup := ⟨⟨L, hL, K, 1⟩, β, hβ⟩ with hD
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hDa : D.mesh = (L : ℝ) ^ (-((K : ℕ) : ℤ)) := rfl
  have ha0 : 0 < D.mesh := D.mesh_pos
  have ha2 : D.mesh ≤ (L : ℝ) ^ (-2 : ℤ) := by
    rw [hDa]
    refine zpow_le_zpow_right₀ (by linarith) ?_
    have : (2 : ℤ) ≤ ((K : ℕ) : ℤ) := by exact_mod_cast hK
    omega
  have hL2 : (L : ℝ) ^ (-2 : ℤ) ≤ 1 / 169 := by
    have e : (L : ℝ) ^ (-2 : ℤ) = 1 / (L : ℝ) ^ 2 := by
      rw [zpow_neg, one_div]
      norm_cast
    rw [e]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  set i : Fin 4 → ℤ := fun μ => ⌊(α μ + 1 / 2) / D.mesh⌋ with hi
  set c : AmbientSpace := fun μ => D.mesh * ((i μ : ℝ) + 1 / 2) with hcdef
  have hclose : ∀ μ, |c μ - (α μ + 1 / 2)| ≤ D.mesh / 2 := by
    intro μ
    have h1 := Int.floor_le ((α μ + 1 / 2) / D.mesh)
    have h2 := Int.lt_floor_add_one ((α μ + 1 / 2) / D.mesh)
    have e : α μ + 1 / 2 = D.mesh * ((α μ + 1 / 2) / D.mesh) := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 ha0.le
    have h4 := mul_lt_mul_of_pos_left h2 ha0
    rw [← e] at h3 h4
    have e1 : c μ = D.mesh * (⌊(α μ + 1 / 2) / D.mesh⌋ : ℝ) + D.mesh / 2 := by
      simp only [hcdef, hi]
      ring
    rw [abs_le]
    constructor <;> linarith
  have hside : D.IsAdmissibleSide ((D.L : ℝ) ^ (0 : ℤ)) := by
    have := D.isAdmissibleSide_one ha2
    simpa using this
  set g : ReflectionGrid D := D.gridOfSide 0 hside c (fun μ => ⟨i μ, rfl⟩) with hg
  have hgs : g.cellSide = 1 := by
    simp [hg, ReflectionGrid.cellSide, ChessboardSetup.gridOfSide]
  have hgo : ∀ μ, g.origin μ = c μ := fun μ => rfl
  let cd : GridCell D := ⟨g, ReflectionGrid.hasAdmissibleSide_gridOfSide 0 hside c _, fun _ => -1⟩
  have hcs : cd.side = 1 := hgs
  have hst : SupportedInCell cd (1 / 8) p := by
    refine ⟨by norm_num, by rw [hcs]; norm_num, hlip, ⟨α, hball⟩, ?_, ?_⟩
    · intro x hx
      show ∀ μ, x μ - (g.origin μ + g.cellSide * ((-1 : ℤ) : ℝ)) ∈ Icc 0 g.cellSide
      intro μ
      have h1 := abs_lt.mp (hcube x hx μ)
      have h2 := abs_le.mp (hclose μ)
      rw [hgs, hgo]
      push_cast
      constructor <;> linarith
    · intro x hx z hz
      simp only [ReflectionGrid.walls, mem_iUnion] at hz
      obtain ⟨ν, k, hz⟩ := hz
      have hz' : z ν = g.origin ν + k * g.cellSide := hz
      rw [hgs, hgo] at hz'
      have h0 := abs_apply_le_euclidNormVec (x - z) ν
      have h1 := abs_lt.mp (hcube x hx ν)
      have h2 := abs_le.mp (hclose ν)
      refine le_trans ?_ h0
      have e : (x - z) ν = x ν - z ν := rfl
      rw [e, hz']
      rcases le_or_gt k (-1) with hk | hk
      · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast hk
        refine le_trans ?_ (le_abs_self _)
        linarith
      · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast (by omega : (0 : ℤ) ≤ k)
        refine le_trans ?_ (neg_le_abs _)
        linarith
  obtain ⟨κ, h1, h2, -⟩ := hMV D A b hA hb hI cd (1 / 8) p hst
  rw [hcs] at h1 h2
  refine ⟨κ, fun μ hμ => ?_⟩
  rcases hμ with hν | ⟨m, rfl⟩
  · exact h1 μ hν
  · have hs : 2 * (1 : ℝ) ≤ PeriodicLattice.torusSide D.L m := by
      have : (1 : ℝ) ≤ (L : ℝ) ^ (m : ℕ) := one_le_pow₀ (by linarith)
      show 2 * (1 : ℝ) ≤ 2 * (L : ℝ) ^ (m : ℕ)
      linarith
    have h3 := h2 m hs
    rw [torusAverage_eq_integral hForm D m hc, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h3
    exact h3
private theorem copySize_le {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    copySize A b 1 (1 / 8) ≤ A * Real.exp (3 * b) := by
  unfold copySize
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
  have hlog : TorusBound.logPos (1 / (1 / 8)) ≤ (2 : ℝ) ^ 20 := by
    unfold TorusBound.logPos
    refine max_le ?_ (by norm_num)
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 / 8) by norm_num)
    norm_num at this ⊢
    linarith
  have h0 : 0 ≤ TorusBound.logPos (1 / (1 / 8)) := le_max_right _ _
  have h2 : TorusBound.logPos (1 / (1 / 8)) ^ (1 / 20 : ℝ) ≤ 2 := by
    have e : (2 : ℝ) = ((2 : ℝ) ^ 20) ^ (1 / 20 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc _ ≤ ((2 : ℝ) ^ 20) ^ (1 / 20 : ℝ) := Real.rpow_le_rpow h0 hlog (by norm_num)
      _ = 2 := e.symm
  nlinarith
private theorem mean_diff_le_at_cutoff
    (hT : SystemOfAdmissibleConstants.hatPartitionOfUnity_prop) (hMV : CellFunctionMeanBounds)
    (hSize : SmearedObservableBound)
    (hForm : InfiniteLattice.WellDefinedStates.Statement)
    {L : ℕ} {K : ℕ+} {β A b M : ℝ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hβ : 0 < β)
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hM : 1 ≤ M)
    (hI : 2 ≤ (K : ℕ) → CopyInequality ⟨⟨L, hL, K, 1⟩, β, hβ⟩ A b)
    {μ μ' : Measure (GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))}
    (hμ : IsCutoffMeasure L K β μ) (hμ' : IsCutoffMeasure L K β μ')
    {R : ℝ} (hR : 0 < R) {f : AmbientSpace → ℝ} (hf : IsLipschitzFor euclidDistR4 f)
    (hx : ∃ x, tsupport f ⊆ closedBallR4 x R) :
    |(∫ U, smearedEnergy f U ∂μ) - ∫ U, smearedEnergy f U ∂μ'| ≤
      onePointBound L A b R * sharpNormR4 M f := by
  obtain ⟨x, hx⟩ := hx
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have ha : 0 < PeriodicLattice.meshSize L ((K : ℕ) : ℤ) := zpow_pos (by linarith) _
  have hP := hμ.isProbabilityMeasure hForm hL hβ
  have hP' := hμ'.isProbabilityMeasure hForm hL hβ
  have hfc := isBoundedBorelCompactlySupported_of_closedBall hR.le hf hx
  have hbd : IsBoundedFun f := hfc.2.1
  have hsup0 : 0 ≤ uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
  have hS0 : 0 ≤ sharpNormR4 M f := hsup0.trans (le_max_left _ _)
  have hR1 : (0 : ℝ) ≤ (1 + R) ^ 4 := by positivity
  by_cases hK : 2 ≤ (K : ℕ)
  · have hε : (0 : ℝ) < 1 / 16 := by norm_num
    obtain ⟨-, c2, c3, c4, -, c6, c7⟩ := hT.1 (1 / 16) hε
    obtain ⟨hfinS, hcard⟩ := c7 R hR f ⟨x, hx⟩
    set T := hfinS.toFinset with hTdef
    have hdec : ∀ y, f y = ∑ α ∈ T,
        (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) y := by
      intro y
      by_cases hy : f y = 0
      · simp [hy]
      · simp only []
        rw [← Finset.sum_mul]
        have h2 : ∑ᶠ α ∈ SystemOfAdmissibleConstants.scaledIntLattice (1 / 16),
            SystemOfAdmissibleConstants.hatFunction (1 / 16) α y = 1 := by
          rw [← finsum_set_coe_eq_finsum_mem]
          exact (c2 y).2
        have h3 : ∑ᶠ α ∈ SystemOfAdmissibleConstants.scaledIntLattice (1 / 16),
            SystemOfAdmissibleConstants.hatFunction (1 / 16) α y =
            ∑ α ∈ T, SystemOfAdmissibleConstants.hatFunction (1 / 16) α y := by
          refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
          ext α
          simp only [mem_inter_iff, Function.mem_support, hTdef, Finite.coe_toFinset, mem_ofPred_eq]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨⟨h1, y, mul_ne_zero h2 hy⟩, h2⟩
          · rintro ⟨⟨h1, -⟩, h2⟩
            exact ⟨h1, h2⟩
        rw [← h3, h2, one_mul]
    have hpiece : ∀ α, IsLipschitzFor euclidDistR4
        (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) ∧
        max (uniformNorm fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z)
          (2 * (1 / 16) * lipConstR4 fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z)
          ≤ 5 * sharpNormR4 M f :=
      c6 M hM (by norm_num) f hbd hf
    have hpc : ∀ α, IsBoundedBorelCompactlySupported
        (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) := by
      intro α
      refine isBoundedBorelCompactlySupported_of_closedBall (x := x) hR.le (hpiece α).1 ?_
      refine (closure_mono ?_).trans hx
      intro z hz
      exact fun h0 => hz (by simp [h0])
    have hfin : ∀ α ∈ T, {p : ElementaryPlaquette (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)) |
        (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) p.center ≠ 0}.Finite :=
      fun α _ => (smearedEnergy_facts ha hForm (hpc α)).1
    have hsum : ∀ ρ : Measure (GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))),
        IsProbabilityMeasure ρ → (∫ U, smearedEnergy f U ∂ρ) =
          ∑ α ∈ T, ∫ U, smearedEnergy
            (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) U ∂ρ := by
      intro ρ _
      rw [← integral_finsetSum]
      · exact integral_congr_ae (ae_of_all _ fun U => smearedEnergy_finset_sum T _ hdec hfin U)
      · intro α _
        obtain ⟨-, hm, C, hC⟩ := smearedEnergy_facts
          (a := PeriodicLattice.meshSize L ((K : ℕ) : ℤ)) ha hForm (hpc α)
        exact Integrable.of_bound hm.aestronglyMeasurable C
          (ae_of_all _ fun U => by simpa using hC U)
    have hq : ∀ α, copyBound A b 1 (1 / 8)
        (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) ≤
        A * Real.exp (3 * b) * (5 * sharpNormR4 M f) := by
      intro α
      have h1 := (hpiece α).2
      have hn0 : 0 ≤ radiusNorm (1 / 8)
          (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) :=
        (Real.iSup_nonneg fun _ => norm_nonneg _).trans (le_max_left _ _)
      have hn : radiusNorm (1 / 8)
          (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) ≤
          5 * sharpNormR4 M f := by
        have e : min (1 : ℝ) (1 / 8) = 2 * (1 / 16) := by norm_num
        unfold radiusNorm
        rw [e]
        exact h1
      exact mul_le_mul (copySize_le (by linarith) (by linarith)) hn hn0 (by positivity)
    have hone : ∀ α ∈ T, |(∫ U, smearedEnergy
        (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) U ∂μ) -
        ∫ U, smearedEnergy (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) U ∂μ'| ≤
        2 * (A * Real.exp (3 * b) * (5 * sharpNormR4 M f)) := by
      intro α _
      have hne : ∀ z, SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z ≠ 0 →
          SystemOfAdmissibleConstants.hatFunction (1 / 16) α z ≠ 0 :=
        fun z hz h0 => hz (by rw [h0, zero_mul])
      obtain ⟨κ, hκ⟩ := mean_near_constant_of_small_support hMV hForm hL hβ hK (by linarith)
        (by linarith) (hI hK) α
        (hpiece α).1 (hpc α) (fun z hz => c3 α z (hne z hz))
        (fun z hz => by
          have := c4 α (subset_tsupport _ (hne z hz))
          have e : (2 : ℝ) * (1 / 16) = 1 / 8 := by norm_num
          rwa [e] at this)
      have h1 := (hκ μ hμ).trans (hq α)
      have h2 := (hκ μ' hμ').trans (hq α)
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hcard' : (T.card : ℝ) ≤ 2 ^ 20 * (1 + R) ^ 4 := by
      have e : ({α | α ∈ SystemOfAdmissibleConstants.scaledIntLattice (1 / 16) ∧
          ∃ x, SystemOfAdmissibleConstants.hatFunction (1 / 16) α x * f x ≠ 0}.ncard : ℝ) = T.card := by
        rw [Set.ncard_eq_toFinset_card _ hfinS]
      rw [← e]
      refine hcard.trans ?_
      have h32 : 2 * R / (1 / 16) + 3 ≤ 32 * (1 + R) := by
        have : 2 * R / (1 / 16) = 32 * R := by ring
        rw [this]
        linarith
      calc (2 * R / (1 / 16) + 3) ^ 4 ≤ (32 * (1 + R)) ^ 4 :=
            pow_le_pow_left₀ (by positivity) h32 4
        _ = 2 ^ 20 * (1 + R) ^ 4 := by ring
    rw [hsum μ hP, hsum μ' hP', ← Finset.sum_sub_distrib]
    have hE : 0 < Real.exp (3 * b) := Real.exp_pos _
    have hA0 : 0 < A := by linarith
    calc _ ≤ ∑ α ∈ T, |(∫ U, smearedEnergy
            (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) U ∂μ) -
            ∫ U, smearedEnergy
              (fun z => SystemOfAdmissibleConstants.hatFunction (1 / 16) α z * f z) U ∂μ'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _α ∈ T, 2 * (A * Real.exp (3 * b) * (5 * sharpNormR4 M f)) := Finset.sum_le_sum hone
      _ = (T.card : ℝ) * (2 * (A * Real.exp (3 * b) * (5 * sharpNormR4 M f))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 ^ 20 * (1 + R) ^ 4) * (2 * (A * Real.exp (3 * b) * (5 * sharpNormR4 M f))) :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ = 10 * 2 ^ 20 * A * Real.exp (3 * b) * (1 + R) ^ 4 * sharpNormR4 M f := by ring
      _ ≤ transferConstant L A b * (1 + R) ^ 4 * sharpNormR4 M f :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hR1) hS0
  · have hK1 : (K : ℕ) = 1 := by have := K.pos; omega
    have hpt : ∀ U : GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)),
        ‖smearedEnergy f U‖ ≤
          12 * (2 * R / PeriodicLattice.meshSize L ((K : ℕ) : ℤ) + 1) ^ 4 * uniformNorm f :=
      fun U => by simpa using hSize.1 _ R ha hR f hbd ⟨x, hx⟩ U
    have hb1 : ∀ ρ : Measure (GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))),
        IsProbabilityMeasure ρ → |∫ U, smearedEnergy f U ∂ρ| ≤
          12 * (2 * R / PeriodicLattice.meshSize L ((K : ℕ) : ℤ) + 1) ^ 4 * uniformNorm f := by
      intro ρ _
      have := norm_integral_le_of_norm_le_const (μ := ρ) (ae_of_all _ hpt)
      simpa using this
    have hsp : PeriodicLattice.meshSize L ((K : ℕ) : ℤ) = 1 / (L : ℝ) := by
      show (L : ℝ) ^ (-((K : ℕ) : ℤ)) = _
      rw [hK1]
      simp
    have hL0 : (0 : ℝ) < L := by linarith
    have h2 : 2 * R / PeriodicLattice.meshSize L ((K : ℕ) : ℤ) + 1 ≤ 2 * L * (1 + R) := by
      rw [hsp]
      have e : 2 * R / (1 / (L : ℝ)) = 2 * R * L := by field_simp
      rw [e]
      nlinarith
    have h3 : (2 * R / PeriodicLattice.meshSize L ((K : ℕ) : ℤ) + 1) ^ 4 ≤ (2 * L * (1 + R)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h2 4
    have h4 := hb1 μ hP
    have h5 := hb1 μ' hP'
    have h6 : |(∫ U, smearedEnergy f U ∂μ) - ∫ U, smearedEnergy f U ∂μ'| ≤
        2 * (12 * (2 * R / PeriodicLattice.meshSize L ((K : ℕ) : ℤ) + 1) ^ 4 * uniformNorm f) := by
      have := abs_sub (∫ U, smearedEnergy f U ∂μ) (∫ U, smearedEnergy f U ∂μ')
      linarith
    refine h6.trans ?_
    calc _ ≤ 2 * (12 * (2 * L * (1 + R)) ^ 4 * uniformNorm f) := by gcongr
      _ = 384 * (L : ℝ) ^ 4 * (1 + R) ^ 4 * uniformNorm f := by ring
      _ ≤ transferConstant L A b * (1 + R) ^ 4 * sharpNormR4 M f := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) hR1)
            (le_max_left _ _) hsup0 ?_
          exact mul_nonneg ((by positivity : (0 : ℝ) ≤ 384 * (L : ℝ) ^ 4).trans (le_max_right _ _)) hR1
theorem onePointBoundsOfInequality_holds
    (h₁ : SystemOfAdmissibleConstants.hatPartitionOfUnity_prop) (h₂ : CellFunctionMeanBounds)
    (h₃ : SmearedObservableBound) (h₄ : PeriodicExtension.LiftedMeanEqTorusMean)
    (h₅ : InfiniteLattice.WellDefinedStates.Statement) :
    OnePointBoundsOfInequality := by
  intro L IsDatum A b M hL hpos hA hb hM hIn
  refine ⟨fun K β hd ν hν ν' hν' R hR f hf hx => ?_, fun K β hd ν hν m R hR _ f hf hx => ?_⟩
  · exact mean_diff_le_at_cutoff h₁ h₂ h₃ h₅ hL (hpos K β hd) hA hb hM
      (fun hK => hIn ⟨⟨L, hL, K, 1⟩, β, hpos K β hd⟩ rfl hK hd) (Or.inl hν) (Or.inl hν') hR hf hx
  · have hfc : IsBoundedBorelCompactlySupported f := by
      obtain ⟨x, hx⟩ := hx
      exact isBoundedBorelCompactlySupported_of_closedBall hR.le hf hx
    have e : torusMean L m K β f =
        ∫ U, smearedEnergy f U ∂liftedWilsonMeasure L m K β :=
      (h₄ L m K β hL m.pos (hpos K β hd) f hfc).symm
    rw [e]
    exact mean_diff_le_at_cutoff h₁ h₂ h₃ h₅ hL (hpos K β hd) hA hb hM
      (fun hK => hIn ⟨⟨L, hL, K, 1⟩, β, hpos K β hd⟩ rfl hK hd) (Or.inl hν)
      (Or.inr ⟨m, rfl⟩) hR hf hx
end YangMills.Construction.AdmissibleConstants
end
