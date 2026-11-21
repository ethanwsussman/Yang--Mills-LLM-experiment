import YangMills.Construction.PeriodicOperators.FunctionalDeterminesItsPolarisationSymbol
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunctionProof
import YangMills.Construction.Towers.TheBackgroundNumbersOnTheRealPolydisc
import YangMills.Construction.Towers.TheMassiveFamilyIsTempered
import YangMills.Construction.Towers.TheMassiveFunctionAsASumOfSymbols
import YangMills.Construction.Towers.TheMassiveFunctionAtTheMomentaOfTheTori
import YangMills.Construction.Towers.TheMassiveFunctionIsContinuousOnTheRealPolydisc
import Mathlib
set_option autoImplicit false
open Filter Topology Set
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.SymbolExpansion
open PeriodicOperators (toComplexVec dualLattice imStrip)
open PeriodicOperators.Tempered
open Tower.FullSpace.BackgroundJets
def roundTowardZero (x : ℝ) : ℤ := if 0 ≤ x then ⌊x⌋ else ⌈x⌉
theorem abs_roundTowardZero_le (x : ℝ) : |(roundTowardZero x : ℝ)| ≤ |x| := by
  unfold roundTowardZero
  split_ifs with h
  · have h0 : (0 : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.2 h
    rw [abs_of_nonneg h0, abs_of_nonneg h]
    exact Int.floor_le x
  · have hx : x < 0 := not_le.1 h
    have h0 : ((⌈x⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_le.2 (by simpa using hx.le)
    rw [abs_of_nonpos h0, abs_of_neg hx]
    exact neg_le_neg (Int.le_ceil x)
theorem abs_sub_roundTowardZero_le (x : ℝ) : |x - (roundTowardZero x : ℝ)| ≤ 1 := by
  unfold roundTowardZero
  split_ifs with h
  · rw [abs_le]
    constructor
    · linarith [Int.floor_le x, Int.lt_floor_add_one x]
    · linarith [Int.floor_le x, Int.lt_floor_add_one x]
  · rw [abs_le]
    constructor
    · linarith [Int.le_ceil x, Int.ceil_lt_add_one x]
    · linarith [Int.le_ceil x, Int.ceil_lt_add_one x]
def roundToGrid (a : ℝ) (p : InfiniteLattice.AmbientSpace) : InfiniteLattice.AmbientSpace :=
  fun μ => (roundTowardZero (p μ / a) : ℝ) * a
theorem abs_roundToGrid_le {a : ℝ} (ha : 0 < a) (p : InfiniteLattice.AmbientSpace) (μ : Fin 4) :
    |roundToGrid a p μ| ≤ |p μ| := by
  have h := abs_roundTowardZero_le (p μ / a)
  rw [abs_div, abs_of_pos ha, le_div_iff₀ ha] at h
  simpa [roundToGrid, abs_mul, abs_of_pos ha] using h
theorem abs_sub_roundToGrid_le {a : ℝ} (ha : 0 < a) (p : InfiniteLattice.AmbientSpace) (μ : Fin 4) :
    |roundToGrid a p μ - p μ| ≤ a := by
  have h := abs_sub_roundTowardZero_le (p μ / a)
  have e : roundToGrid a p μ - p μ = -((p μ / a - (roundTowardZero (p μ / a) : ℝ)) * a) := by
    simp only [roundToGrid]
    field_simp
    ring
  rw [e, abs_neg, abs_mul, abs_of_pos ha]
  nlinarith
def symbolSum (L k : ℕ) (z : ℝ) (μPlus μMinus : Fin 4) (p : InfiniteLattice.AmbientSpace) : ℂ :=
  (((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ *
    ∑ m ∈ PlaneWaves.freqBox L k, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      hessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z)) ρ σ
          (fun μ => ((finestMesh L k : ℝ) : ℂ) *
            PlaneWaves.shiftedFreq (toComplexVec p) m μ) *
        backgroundCoeff L k (toComplexVec p) μPlus ρ m *
        backgroundCoeff L k (-toComplexVec p) μMinus σ (-m)
theorem norm_toComplexVec_eq_abs (p : InfiniteLattice.AmbientSpace) (μ : Fin 4) :
    ‖toComplexVec p μ‖ = |p μ| := by
  simp [toComplexVec]
theorem toComplexVec_neg_eq (p : InfiniteLattice.AmbientSpace) :
    toComplexVec (-p) = -toComplexVec p := by
  funext μ
  simp [toComplexVec]
theorem finestMesh_pos_of_pos {L : ℕ} (hL : 0 < L) (k : ℕ) : 0 < finestMesh L k := by
  unfold finestMesh meshAt
  exact zpow_pos (by exact_mod_cast hL) _
theorem neg_mem_freqBox_of_mem {L k : ℕ} {m : Fin 4 → ℤ} (hm : m ∈ PlaneWaves.freqBox L k) :
    -m ∈ PlaneWaves.freqBox L k := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.neg_mem_freqBox <;> assumption
theorem continuousOn_symbolSum
    (h4 : BackgroundCoeffsOnRealPolydisc.Claim)
    (ht : Tempered.MassiveFamilyTempered)
    (hP : HessianSymbolDetermined.Claim)
    {L : ℕ} (hS : Conventions.IsAdmissibleBlockingFactor L) {k : ℕ} (hk : 1 ≤ k) {z : ℝ} (hz : 0 < z)
    (μPlus μMinus : Fin 4) :
    ContinuousOn (symbolSum L k z μPlus μMinus)
      {p | toComplexVec p ∈ momentumPolydisc (massWidth z)} := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hS.2
  have hη := finestMesh_pos_of_pos hL0 k
  have hz' : 0 < finestMesh L k ^ 2 * z := by positivity
  obtain ⟨hTemp, -⟩ := ht L hS _ hz'
  obtain ⟨-, δ, π, e, hc⟩ := id hTemp
  obtain ⟨-, P, hPP, -⟩ := hP L hS _ hTemp
  have hpol : IsHessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z))
      (hessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z))) :=
    Classical.epsilon_spec (p := IsHessianSymbol L _) ⟨P, hPP⟩
  obtain ⟨O, hO, hhol⟩ := hc.analytic
  have hsub : ∀ {p : InfiniteLattice.AmbientSpace},
      toComplexVec p ∈ momentumPolydisc (massWidth z) →
        toComplexVec p ∈ momentumPolydisc stripHalfWidth := fun h μ =>
    (h μ).trans (min_le_left _ _)
  have hreal : ∀ (m : Fin 4 → ℤ) (p : InfiniteLattice.AmbientSpace),
      (fun μ => ((finestMesh L k : ℝ) : ℂ) *
        PlaneWaves.shiftedFreq (toComplexVec p) m μ) ∈ imStrip δ := by
    intro m p μ
    have him : (((finestMesh L k : ℝ) : ℂ) *
        PlaneWaves.shiftedFreq (toComplexVec p) m μ).im = 0 := by
      simp [PlaneWaves.shiftedFreq, toComplexVec]
    rw [him, abs_zero]
    exact hc.delta_pos.le
  have hg : ∀ m : Fin 4 → ℤ, Continuous fun p : InfiniteLattice.AmbientSpace =>
      (fun μ => ((finestMesh L k : ℝ) : ℂ) *
        PlaneWaves.shiftedFreq (toComplexVec p) m μ) := by
    intro m
    refine continuous_pi fun μ => ?_
    simp only [PlaneWaves.shiftedFreq, toComplexVec]
    have : Continuous fun p : InfiniteLattice.AmbientSpace => p μ := continuous_apply μ
    fun_prop
  have hsym : ∀ (m : Fin 4 → ℤ) (ρ σ : Fin 4),
      ContinuousOn (fun p : InfiniteLattice.AmbientSpace =>
        hessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z)) ρ σ
          (fun μ => ((finestMesh L k : ℝ) : ℂ) *
            PlaneWaves.shiftedFreq (toComplexVec p) m μ))
        {p | toComplexVec p ∈ momentumPolydisc (massWidth z)} := by
    intro m ρ σ
    have hπ : ContinuousOn (π ρ σ) O := continuousOn_pi.1 (hhol ρ σ).1.2.1 0
    have hcomp := hπ.comp (hg m).continuousOn (s := {p | toComplexVec p ∈ momentumPolydisc (massWidth z)})
      (fun p _ => hO (hreal m p))
    exact hcomp.congr fun p _ => hpol δ π e hc ρ σ (hreal m p)
  have hb := (h4 L hS k hk).2
  unfold symbolSum
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun m hm =>
    continuousOn_finsetSum _ fun ρ _ => continuousOn_finsetSum _ fun σ _ => ?_)
  refine ((hsym m ρ σ).mul ((hb μPlus ρ m hm).mono fun p hp => hsub hp)).mul ?_
  have hneg := (hb μMinus σ (-m) (neg_mem_freqBox_of_mem hm)).comp
    (continuous_neg (G := InfiniteLattice.AmbientSpace)).continuousOn
    (s := {p | toComplexVec p ∈ momentumPolydisc (massWidth z)}) (fun p hp μ => by
      have h := hsub hp μ
      rw [norm_toComplexVec_eq_abs] at h
      rw [norm_toComplexVec_eq_abs, Pi.neg_apply, abs_neg]
      exact h)
  refine hneg.congr fun p _ => ?_
  simp only [Function.comp, toComplexVec_neg_eq]
theorem tendsto_gridStep {L : ℕ} (hL : 1 < L) :
    Tendsto (fun j : ℕ => 2 * Real.pi / ((2 * L ^ (j + 1) : ℕ) : ℝ)) atTop (𝓝 0) := by
  refine tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ?_)
  refine tendsto_atTop_mono (fun j => ?_) tendsto_id
  have h : j + 1 < L ^ (j + 1) := Nat.lt_pow_self hL
  simp only [id]
  omega
theorem massiveLogFnAsSymbolSum_holds (h8 : TorusMomenta.MassiveLogFnAtTorusMomenta)
    (h10 : ContinuousOnRealPolydisc.Claim)
    (h4 : BackgroundCoeffsOnRealPolydisc.Claim)
    (ht : Tempered.MassiveFamilyTempered)
    (hP : HessianSymbolDetermined.Claim) : MassiveLogFnAsSymbolSum := by
  intro L hS k hk z hz p hp μPlus μMinus
  have hL1 : 1 < L := lt_of_lt_of_le (by norm_num) hS.2
  have hL0 : 0 < L := by omega
  set a : ℕ → ℝ := fun j => 2 * Real.pi / ((2 * L ^ (j + 1) : ℕ) : ℝ) with ha
  have hapos : ∀ j, 0 < a j := by
    intro j
    have h0 : (0 : ℝ) < ((2 * L ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by norm_num) (pow_pos hL0 _)
    exact div_pos (by positivity) h0
  set q : ℕ → InfiniteLattice.AmbientSpace := fun j => roundToGrid (a j) p with hq
  have hqW : ∀ j, toComplexVec (q j) ∈ momentumPolydisc (massWidth z) := by
    intro j μ
    have h := hp μ
    rw [norm_toComplexVec_eq_abs] at h ⊢
    exact (abs_roundToGrid_le (hapos j) p μ).trans h
  have hqm : ∀ j, q j ∈ dualLattice (2 * L ^ (j + 1)) := fun j =>
    ⟨fun μ => roundTowardZero (p μ / a j), fun μ => rfl⟩
  have hqp : Tendsto q atTop (𝓝 p) := by
    refine tendsto_pi_nhds.2 fun μ => ?_
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (tendsto_gridStep hL1))
    rw [Real.dist_eq]
    exact abs_sub_roundToGrid_le (hapos j) p μ
  have hqW' : Tendsto q atTop
      (𝓝[{p | toComplexVec p ∈ momentumPolydisc (massWidth z)}] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hqp, Eventually.of_forall hqW⟩
  have hl := ((h10 L hS k hk z hz μPlus μMinus) p hp).tendsto.comp hqW'
  have hr := ((continuousOn_symbolSum h4 ht hP hS hk hz μPlus μMinus) p hp).tendsto.comp hqW'
  have heq : ∀ j, ((fun p : InfiniteLattice.AmbientSpace =>
      massiveLogFn L k (toComplexVec p) μPlus μMinus z) ∘ q) j =
        (symbolSum L k z μPlus μMinus ∘ q) j := fun j =>
    h8 L hS k hk z hz (j + 1) (Nat.succ_pos j) (q j) (hqm j) (hqW j) μPlus μMinus
  exact tendsto_nhds_unique (hl.congr heq) hr
end YangMills.Construction.Tower.MassiveOpFunctions.SymbolExpansion
end
