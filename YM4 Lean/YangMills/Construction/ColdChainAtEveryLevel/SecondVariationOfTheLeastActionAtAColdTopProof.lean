import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ColdChainAtEveryLevel.CriticalValueIsTheLeastAction
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheActionInTheChartProof
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheLeastActionAtAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.SliceNormAgainstTheForm
import YangMills.Construction.ColdChainAtEveryLevel.TotalUnderATurnedTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.BlockAverages.ColdTopSecondVariation
open BlockAverages.ChartCoordinates CoordinateSeminorms GaugeMap
variable {F : BlockFrame}
theorem second_deriv_comp_of_analyticAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Φ : E → ℝ) (s : ℝ → E) (hΦ : AnalyticAt ℝ Φ 0) (hs : AnalyticAt ℝ s 0) (h0 : s 0 = 0) :
    deriv (deriv (Φ ∘ s)) 0 =
      fderiv ℝ (fderiv ℝ Φ) 0 (deriv s 0) (deriv s 0) + fderiv ℝ Φ 0 (deriv (deriv s) 0) := by apply _root_.YangMills.Construction.ChartSecondVariation.deriv_deriv_comp_of_analyticAt <;> assumption
theorem deriv_comp_smul_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Φ : E → ℝ) (u : E) (hΦ : AnalyticAt ℝ Φ 0) :
    deriv (deriv fun τ : ℝ => Φ (τ • u)) 0 = fderiv ℝ (fderiv ℝ Φ) 0 u u ∧
      deriv (fun τ : ℝ => Φ (τ • u)) 0 = fderiv ℝ Φ 0 u := by apply _root_.YangMills.Construction.ChartSecondVariation.deriv_deriv_smul_line <;> assumption
theorem envelope_derivs {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Ψ : E × ℝ → ℝ) (e₀ : E) (e : ℝ → E) (hΨ : AnalyticAt ℝ Ψ (e₀, 0)) (he : AnalyticAt ℝ e 0)
    (h0 : e 0 = e₀) (hcrit : ∀ B : E, deriv (fun τ : ℝ => Ψ (e₀ + τ • B, 0)) 0 = 0) :
    AnalyticAt ℝ (fun τ => Ψ (e τ, τ)) 0 ∧
      deriv (fun τ => Ψ (e τ, τ)) 0 = deriv (fun τ => Ψ (e₀, τ)) 0 ∧
      deriv (deriv fun τ => Ψ (e τ, τ)) 0 = deriv (deriv fun τ => Ψ (e₀ + τ • deriv e 0, τ)) 0 := by
  let Φ : E × ℝ → ℝ := fun x => Ψ ((e₀, 0) + x)
  let s : ℝ → E × ℝ := fun τ => (e τ - e₀, τ)
  have hΦ : AnalyticAt ℝ Φ 0 := by
    have h1 : AnalyticAt ℝ Ψ ((fun x : E × ℝ => (e₀, (0 : ℝ)) + x) 0) := by simpa using hΨ
    exact h1.comp (by fun_prop)
  have hsa : AnalyticAt ℝ s 0 := (he.sub analyticAt_const).prod analyticAt_id
  have hs0 : s 0 = 0 := by simp [s, h0]
  have hfun : (fun τ => Ψ (e τ, τ)) = Φ ∘ s := by
    funext τ
    simp [Φ, s]
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), AnalyticAt ℝ e τ := he.eventually_analyticAt
  have hd1 : ∀ τ, AnalyticAt ℝ e τ → HasDerivAt s (deriv e τ, 1) τ := fun τ hτ =>
    (hτ.differentiableAt.hasDerivAt.sub_const e₀).prodMk (hasDerivAt_id τ)
  have hs' : deriv s 0 = (deriv e 0, 1) := (hd1 0 he).deriv
  have hs'' : deriv (deriv s) 0 = (deriv (deriv e) 0, 0) := by
    have h1 : deriv s =ᶠ[𝓝 0] fun τ => (deriv e τ, (1 : ℝ)) := by
      filter_upwards [hev] with τ hτ using (hd1 τ hτ).deriv
    rw [h1.deriv_eq]
    exact (he.deriv.differentiableAt.hasDerivAt.prodMk (hasDerivAt_const (0 : ℝ) (1 : ℝ))).deriv
  have hΦB : ∀ B : E, fderiv ℝ Φ 0 (B, 0) = 0 := by
    intro B
    have e1 : (fun τ : ℝ => Φ (τ • (B, (0 : ℝ)))) = fun τ : ℝ => Ψ (e₀ + τ • B, 0) := by
      funext τ
      simp [Φ]
    rw [← (deriv_comp_smul_line Φ (B, 0) hΦ).2, e1]
    exact hcrit B
  have hΦ' : AnalyticAt ℝ Φ (s 0) := by rw [hs0]; exact hΦ
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact hΦ'.comp hsa
  · rw [hfun]
    have h1 := fderiv_comp_deriv (0 : ℝ) hΦ'.differentiableAt hsa.differentiableAt
    rw [h1, hs0, hs']
    have e1 : ((deriv e 0, 1) : E × ℝ) = (deriv e 0, 0) + (0, 1) := by simp
    rw [e1, map_add, hΦB, zero_add, ← (deriv_comp_smul_line Φ (0, 1) hΦ).2]
    congr 1
    funext τ
    simp [Φ]
  · rw [hfun, second_deriv_comp_of_analyticAt Φ s hΦ hsa hs0, hs', hs'', hΦB, add_zero,
      ← (deriv_comp_smul_line Φ (deriv e 0, 1) hΦ).1]
    congr 2
    funext τ
    simp [Φ]
theorem deriv_mem_of_eventually_mem {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) (w : ℝ → E) (w' : E) (hd : HasDerivAt w w' 0) (hev : ∀ᶠ τ in 𝓝 (0 : ℝ), w τ ∈ P) :
    w' ∈ P := by
  have hc : IsClosed (P : Set E) := P.closed_of_finiteDimensional
  have h0 : w 0 ∈ P := hev.self_of_nhds
  have ht := hasDerivAt_iff_tendsto_slope.1 hd
  refine hc.mem_of_tendsto ht ?_
  have h1 : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), w τ ∈ P := hev.filter_mono nhdsWithin_le_nhds
  filter_upwards [h1] with τ hτ
  rw [slope_def_module]
  exact P.smul_mem _ (P.sub_mem hτ h0)
theorem inGaugeSlice_add_smul (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
    {u u' : F.Site 0 → Fin 4 → imaginaryQuaternions}
    (hu : InGaugeSlice S V R u) (hu' : InGaugeSlice S V R u') (t : ℝ) :
    InGaugeSlice S V R (fun x i => u x i + t • u' x i) := by
  intro s hs
  have h := gaugeMap_add_smul S V R (fun x i => (u x i : ℍ[ℝ])) (fun x i => (u' x i : ℍ[ℝ])) t s
  have e : (fun x i => ((u x i + t • u' x i : imaginaryQuaternions) : ℍ[ℝ])) =
      fun x i => (u x i : ℍ[ℝ]) + t • (u' x i : ℍ[ℝ]) := by
    funext x i
    simp
  show gaugeMap S V R (fun x i => ((u x i + t • u' x i : imaginaryQuaternions) : ℍ[ℝ])) s = 0
  rw [e, h, hu s hs, hu' s hs]
  simp
theorem inGaugeSlice_zero (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) :
    InGaugeSlice S V R (fun _ _ => 0) := by
  intro s _
  exact gaugeMap_zero S V R s
def sliceBondValues (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) :
    Submodule ℝ (↥(innerBonds S 0) → imaginaryQuaternions) where
  carrier := {w | ∃ u, InGaugeSlice S V R u ∧ ∀ b : ↥(innerBonds S 0), u b.1.1 b.1.2 = w b}
  add_mem' := by
    rintro w w' ⟨u, hu, h⟩ ⟨u', hu', h'⟩
    refine ⟨_, by simpa using inGaugeSlice_add_smul S V R hu hu' 1, fun b => ?_⟩
    simp [h b, h' b]
  zero_mem' := ⟨_, inGaugeSlice_zero S V R, fun _ => rfl⟩
  smul_mem' := by
    rintro t w ⟨u, hu, h⟩
    refine ⟨_, by simpa using inGaugeSlice_add_smul S V R (inGaugeSlice_zero S V R) hu t, fun b => ?_⟩
    simp [h b]
theorem chartValues_chartOfValues (S : Finset F.Cell) (U : ChainChart F) (e : ChartValues S) :
    chartValues S (chartOfValues S U e) = e := by
  refine Prod.ext ?_ ?_
  · funext b
    simp only [chartOfValues, chartValues]
    rw [dif_pos (show (b.1.1, b.1.2) ∈ innerBonds S 0 from b.2)]
  · funext j b
    simp only [chartOfValues, chartValues]
    rw [dif_pos j.2, dif_pos (show (b.1.1, b.1.2) ∈ innerBonds S (j.val + 1) from b.2)]
theorem chartOfValues_add_smul_agreeOn (S : Finset F.Cell) (U A : ChainChart F) (τ : ℝ) :
    ChartEqOnBonds S (chartOfValues S U (chartValues S U + τ • chartValues S A)) (chartMove U A τ) := by
  refine ⟨fun b hb => ?_, fun j hj b hb => ?_⟩
  · simp only [chartOfValues, chartValues, chartMove]
    rw [dif_pos (show (b.1, b.2) ∈ innerBonds S 0 from hb)]
    rfl
  · have hj' : j < F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    simp only [chartOfValues, chartValues, chartMove]
    rw [dif_pos hj', dif_pos (show (b.1, b.2) ∈ innerBonds S (j + 1) from hb)]
    rfl
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit])
theorem rotatedField_zero_smul (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    rotatedField (fun y i => (0 : ℝ) • v y i) V = V := by
  funext y i
  simp [rotatedField, expUnit_zero]
theorem analyticAt_chartOfValues_fine (S : Finset F.Cell) (U : ChainChart F) (e₀ : ChartValues S)
    {b : F.Site 0 × Fin 4} (hb : b ∈ innerBonds S 0) :
    AnalyticAt ℝ (fun e : ChartValues S => (chartOfValues S U e).fine b.1 b.2) e₀ := by
  have e : (fun e : ChartValues S => (chartOfValues S U e).fine b.1 b.2) = fun e => e.1 ⟨b, hb⟩ := by
    funext e
    simp only [chartOfValues]
    rw [dif_pos (show (b.1, b.2) ∈ innerBonds S 0 from hb)]
  rw [e]
  have h1 : AnalyticAt ℝ (fun e : ChartValues S => e.1) e₀ := analyticAt_fst
  exact (analyticAt_pi_iff.1 h1) ⟨b, hb⟩
theorem analyticAt_chartOfValues_coarse (S : Finset F.Cell) (U : ChainChart F) (e₀ : ChartValues S) {j : ℕ}
    (hj : j + 1 < F.top) {b : F.Site (j + 1) × Fin 4} (hb : b ∈ innerBonds S (j + 1)) :
    AnalyticAt ℝ (fun e : ChartValues S => (chartOfValues S U e).coarse j b.1 b.2) e₀ := by
  have hj' : j < F.depth := by
    have hn : F.top = F.depth + 1 := rfl
    omega
  have e : (fun e : ChartValues S => (chartOfValues S U e).coarse j b.1 b.2) =
      fun e => e.2 ⟨j, hj'⟩ ⟨b, hb⟩ := by
    funext e
    simp only [chartOfValues]
    rw [dif_pos hj', dif_pos (show (b.1, b.2) ∈ innerBonds S (j + 1) from hb)]
  rw [e]
  have h1 : AnalyticAt ℝ (fun e : ChartValues S => e.2) e₀ := analyticAt_snd
  have h2 := (analyticAt_pi_iff.1 h1) ⟨j, hj'⟩
  exact (analyticAt_pi_iff.1 h2) ⟨b, hb⟩
theorem derivs_minimalAction_of_curve (a : ℝ) (hodd : Odd F.blockSide) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (U : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (e : ℝ → ChartValues S)
    (hcrit : ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) V U A)
    (hΨ : AnalyticAt ℝ (fun x : ChartValues S × ℝ => chartAction a S (referenceFieldChain S V)
      (chartOfValues S U x.1) (rotatedField (fun y i => x.2 • v y i) V)) (chartValues S U, 0))
    (hea : AnalyticAt ℝ e 0) (he0 : e 0 = chartValues S U)
    (hval : ∀ᶠ τ : ℝ in 𝓝 0, minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V) =
      chartAction a S (referenceFieldChain S V) (chartOfValues S U (e τ)) (rotatedField (fun y i => τ • v y i) V))
    (hsl : ∀ᶠ τ : ℝ in 𝓝 0, (e τ).1 ∈ sliceBondValues S V (referenceFieldChain S V 0)) :
    ∃ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine ∧
      deriv (fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0 =
        deriv (fun τ : ℝ => chartAction a S (referenceFieldChain S V) U
          (rotatedField (fun y i => τ • v y i) V)) 0 ∧
      deriv (deriv fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0 =
        deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ)
          (rotatedField (fun y i => τ • v y i) V)) 0 := by
  have hlie : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
  set R := referenceFieldChain S V with hR
  let Ψ : ChartValues S × ℝ → ℝ := fun x => chartAction a S R (chartOfValues S U x.1)
    (rotatedField (fun y i => x.2 • v y i) V)
  let e₀ : ChartValues S := chartValues S U
  have hcr : ∀ Bv : ChartValues S, deriv (fun τ : ℝ => Ψ (e₀ + τ • Bv, 0)) 0 = 0 := by
    intro Bv
    have e1 : (fun τ : ℝ => Ψ (e₀ + τ • Bv, 0)) =
        fun τ : ℝ => chartAction a S R (chartMove U (chartOfValues S (zeroChart F) Bv) τ) V := by
      funext τ
      simp only [Ψ]
      rw [rotatedField_zero_smul]
      have h1 := chartOfValues_add_smul_agreeOn S U (chartOfValues S (zeroChart F) Bv) τ
      rw [chartValues_chartOfValues] at h1
      exact chartAction_congr hodd a R V h1
    rw [e1]
    exact (hcrit (chartOfValues S (zeroChart F) Bv)).deriv
  obtain ⟨-, hd1, hd2⟩ := envelope_derivs Ψ e₀ e hΨ hea he0 hcr
  have hf : (fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) =ᶠ[𝓝 0]
      fun τ => Ψ (e τ, τ) := hval
  have hmem : (deriv e 0).1 ∈ sliceBondValues S V (R 0) := by
    have h0 : HasDerivAt e (deriv e 0) 0 := hea.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun τ => (e τ).1) (deriv e 0).1 0 :=
      (ContinuousLinearMap.fst ℝ (↥(innerBonds S 0) → imaginaryQuaternions)
        ((j : Fin F.depth) → ↥(innerBonds S (j.val + 1)) → imaginaryQuaternions)).hasFDerivAt.comp_hasDerivAt 0 h0
    exact deriv_mem_of_eventually_mem _ _ _ h1 hsl
  obtain ⟨u₁, hu₁, hu₁e⟩ := hmem
  let A : ChainChart F := ⟨u₁, (chartOfValues S (zeroChart F) (deriv e 0)).coarse⟩
  have hreadA : chartValues S A = deriv e 0 := by
    refine Prod.ext (funext hu₁e) ?_
    funext j b
    have h1 := chartValues_chartOfValues S (zeroChart F) (deriv e 0)
    exact congrFun (congrFun (congrArg Prod.snd h1) j) b
  refine ⟨A, hu₁, ?_, ?_⟩
  · rw [hf.deriv_eq, hd1]
    congr 1
    funext τ
    simp only [Ψ, e₀, chartOfValues_chartValues]
  · rw [hf.deriv.deriv_eq, hd2]
    congr 2
    funext τ
    simp only [Ψ, e₀]
    have h1 := chartOfValues_add_smul_agreeOn S U A τ
    rw [hreadA] at h1
    exact chartAction_congr hodd a R _ h1
theorem derivs_minimalAction_of_rotatedChain (a θ del Ca rL r' CL s σV : ℝ) (Ck : ℕ → ℝ)
    (hodd : Odd F.blockSide) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (U : ChainChart F) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (hs : 0 < s) (hsV : s < σV) (hrL : 0 < r') (hcold : IsCold S F.top s V)
    (hcrit : ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) V U A)
    (hCV : ∀ (s' : ℝ) (v' : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s' → s' ≤ σV →
      IsCold S F.top s' V → (∀ y i, ‖v' y i‖ ≤ s') → ∀ U' : ChainChart F,
      IsCriticalChainOverTop a θ del Ca CL s' S V (rotatedField v' V) U' →
      minimalAction a S F.top (rotatedField v' V) =
        chartAction a S (referenceFieldChain S V) U' (rotatedField v' V))
    (hΨ : AnalyticAt ℝ (fun x : ChartValues S × ℝ => chartAction a S (referenceFieldChain S V)
      (chartOfValues S U x.1) (rotatedField (fun y i => x.2 • v y i) V)) (chartValues S U, 0))
    (k : ℕ) (hk : 1 ≤ k) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (T : (Fin k → ℝ) → ChainChart F) (hT : IsRotatedChain a θ del Ca rL r' CL s Ck S V c X U T)
    (ζ : ℝ → Fin k → ℝ) (W : ℝ) (hW0 : 0 < W) (hζ0 : ζ 0 = 0) (hζa : AnalyticAt ℝ ζ 0)
    (hζb : ∀ τ l, |ζ τ l| ≤ |τ| * W) (hvW : ∀ y i, ‖v y i‖ ≤ W)
    (hspread : ∀ τ, bondSpread c X (ζ τ) = fun y i => τ • v y i) :
    ∃ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine ∧
      deriv (fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0 =
        deriv (fun τ : ℝ => chartAction a S (referenceFieldChain S V) U
          (rotatedField (fun y i => τ • v y i) V)) 0 ∧
      deriv (deriv fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0 =
        deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ)
          (rotatedField (fun y i => τ • v y i) V)) 0 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hea : AnalyticAt ℝ (fun τ => chartValues S (T (ζ τ))) 0 := by
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun b => ?_)
      (analyticAt_pi_iff.2 fun j => analyticAt_pi_iff.2 fun b => ?_)
    · have h1 : AnalyticAt ℝ (fun ξ : Fin k → ℝ => (T ξ).fine b.1.1 b.1.2) (ζ 0) := by
        rw [hζ0]
        exact hT.analyticAt_fine b.1 b.2
      exact h1.comp hζa
    · have hj : j.val + 1 < F.top := by
        have hn : F.top = F.depth + 1 := rfl
        have := j.2
        omega
      have h1 : AnalyticAt ℝ (fun ξ : Fin k → ℝ => (T ξ).coarse j.val b.1.1 b.1.2) (ζ 0) := by
        rw [hζ0]
        exact hT.analyticAt_coarse j.val hj b.1 b.2
      exact h1.comp hζa
  have he0 : (fun τ => chartValues S (T (ζ τ))) 0 = chartValues S U := by
    show chartValues S (T (ζ 0)) = chartValues S U
    rw [hζ0]
    exact chartValues_congr hT.eq_at_zero
  have hcardpos : (0 : ℝ) < k := by linarith
  set ε : ℝ := min (r' / k) ((σV - s) / k) with hε
  have hε0 : 0 < ε := lt_min (div_pos hrL hcardpos) (div_pos (by linarith) hcardpos)
  have hsmall : ∀ᶠ τ : ℝ in 𝓝 0, |τ| * W < ε := by
    have h1 : Filter.Tendsto (fun τ : ℝ => |τ| * W) (𝓝 0) (𝓝 0) :=
      (continuous_abs.mul continuous_const).tendsto' 0 0 (by simp)
    exact h1.eventually (gt_mem_nhds hε0)
  refine derivs_minimalAction_of_curve a hodd S V U v _ hcrit hΨ hea he0 ?_ ?_
  · filter_upwards [hsmall] with τ hτ
    have h1 : |τ| * W < r' / k := hτ.trans_le (min_le_left _ _)
    have h2 : |τ| * W < (σV - s) / k := hτ.trans_le (min_le_right _ _)
    have h3 : k * (|τ| * W) < σV - s := by
      rw [lt_div_iff₀ hcardpos] at h2
      linarith
    have hσ0 : 0 ≤ |τ| * W := by positivity
    have hk0 : |τ| * W ≤ (k : ℝ) * (|τ| * W) := by nlinarith
    have hc := hT.critical (ζ τ) (|τ| * W) (hζb τ) h1
    have e1 : rotatedTop c X (ζ τ) V = rotatedField (fun y i => τ • v y i) V := by
      simp only [rotatedTop, hspread]
    rw [e1] at hc
    have hres := hCV (s + k * (|τ| * W)) (fun y i => τ • v y i) (by linarith) (by linarith)
      (fun p hp => (hcold p hp).trans_le (by linarith)) (fun y i => by
        rw [norm_smul, Real.norm_eq_abs]
        have h4 := mul_le_mul_of_nonneg_left (hvW y i) (abs_nonneg τ)
        linarith) _ hc
    show minimalAction a S F.top (rotatedField (fun y i => τ • v y i) V) = _
    rw [hres]
    exact (chartAction_congr hodd a _ _ (chartOfValues_agreeOn U (T (ζ τ)))).symm
  · filter_upwards [hsmall] with τ hτ
    refine ⟨(T (ζ τ)).fine, hT.mem_slice (ζ τ) fun l => ?_, fun b => rfl⟩
    exact (hζb τ l).trans_lt (hτ.trans_le (min_le_left _ _))
theorem derivs_minimalAction (a θ del Ca rL r' CL s σV : ℝ) (Ck : ℕ → ℝ) (hodd : Odd F.blockSide)
    (S : Finset F.Cell) (V : F.GaugeField F.top) (U : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (hs : 0 < s) (hsV : s < σV) (hrL : 0 < r') (hcold : IsCold S F.top s V)
    (hv : ∀ b, b ∉ innerBonds S F.top → v b.1 b.2 = 0) (b₀ : F.Site F.top × Fin 4) (hb₀ : v b₀.1 b₀.2 ≠ 0)
    (hcrit : ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) V U A)
    (hTs : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
      AreUnitVectors X →
      ∃ T : (Fin k → ℝ) → ChainChart F, IsRotatedChain a θ del Ca rL r' CL s Ck S V c X U T)
    (hCV : ∀ (s' : ℝ) (v' : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s' → s' ≤ σV →
      IsCold S F.top s' V → (∀ y i, ‖v' y i‖ ≤ s') → ∀ U' : ChainChart F,
      IsCriticalChainOverTop a θ del Ca CL s' S V (rotatedField v' V) U' →
      minimalAction a S F.top (rotatedField v' V) =
        chartAction a S (referenceFieldChain S V) U' (rotatedField v' V))
    (hΨ : AnalyticAt ℝ (fun x : ChartValues S × ℝ => chartAction a S (referenceFieldChain S V)
      (chartOfValues S U x.1) (rotatedField (fun y i => x.2 • v y i) V)) (chartValues S U, 0)) :
    ∃ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine ∧
      deriv (fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0 =
        deriv (fun τ : ℝ => chartAction a S (referenceFieldChain S V) U
          (rotatedField (fun y i => τ • v y i) V)) 0 ∧
      deriv (deriv fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0 =
        deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ)
          (rotatedField (fun y i => τ • v y i) V)) 0 := by
  classical
  set R := referenceFieldChain S V with hR
  have hb₀B : b₀ ∈ innerBonds S F.top := by
    by_contra h
    exact hb₀ (hv b₀ h)
  let B := innerBonds S F.top
  let q := B.equivFin
  let c : Fin B.card → F.Site F.top × Fin 4 := fun l => (q.symm l).1
  have hcB : ∀ l, c l ∈ B := fun l => (q.symm l).2
  have hcinj : Function.Injective c := Subtype.val_injective.comp q.symm.injective
  have hcsurj : ∀ b ∈ B, ∃ l, c l = b := fun b hb => ⟨q ⟨b, hb⟩, by simp [c]⟩
  have hk : 1 ≤ B.card := Finset.card_pos.2 ⟨b₀, hb₀B⟩
  have hn₀ : ‖v b₀.1 b₀.2‖ ≠ 0 := norm_ne_zero_iff.2 hb₀
  let X : Fin B.card → imaginaryQuaternions := fun l =>
    if ‖v (c l).1 (c l).2‖ = 0 then ‖v b₀.1 b₀.2‖⁻¹ • v b₀.1 b₀.2
    else ‖v (c l).1 (c l).2‖⁻¹ • v (c l).1 (c l).2
  have hX : AreUnitVectors X := by
    intro l
    simp only [X]
    split_ifs with h
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn₀]
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h]
  obtain ⟨T, hT⟩ := hTs B.card c X hk hX
  let ζ : ℝ → Fin B.card → ℝ := fun τ l => τ * ‖v (c l).1 (c l).2‖
  let W : ℝ := 1 + ∑ l, ‖v (c l).1 (c l).2‖
  have hW0 : 0 < W := by
    have : 0 ≤ ∑ l, ‖v (c l).1 (c l).2‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    simp only [W]
    linarith
  have hvW : ∀ y i, ‖v y i‖ ≤ W := by
    intro y i
    by_cases hb : (y, i) ∈ B
    · obtain ⟨l, hl⟩ := hcsurj _ hb
      have h1 : ‖v (c l).1 (c l).2‖ ≤ ∑ l, ‖v (c l).1 (c l).2‖ :=
        Finset.single_le_sum (f := fun l => ‖v (c l).1 (c l).2‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ l)
      rw [hl] at h1
      simp only [W]
      linarith
    · have : v y i = 0 := hv (y, i) hb
      rw [this, norm_zero]
      exact hW0.le
  have hζb : ∀ τ l, |ζ τ l| ≤ |τ| * W := by
    intro τ l
    simp only [ζ]
    rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hvW _ _) (abs_nonneg _)
  have hspread : ∀ τ, bondSpread c X (ζ τ) = fun y i => τ • v y i := by
    intro τ
    funext y i
    simp only [bondSpread]
    by_cases hb : (y, i) ∈ B
    · obtain ⟨l, hl⟩ := hcsurj _ hb
      rw [Finset.sum_eq_single l]
      · rw [if_pos hl]
        have h1 : v (c l).1 (c l).2 = v y i := by rw [hl]
        simp only [ζ, X, h1]
        split_ifs with h0
        · have : v y i = 0 := norm_eq_zero.1 h0
          simp [this]
        · rw [smul_smul, mul_assoc, mul_inv_cancel₀ h0, mul_one]
      · intro l' _ hne
        rw [if_neg]
        intro h
        exact hne (hcinj (h.trans hl.symm))
      · simp
    · rw [show v y i = 0 from hv (y, i) hb, smul_zero]
      refine Finset.sum_eq_zero fun l _ => if_neg fun h => hb ?_
      rw [← h]
      exact hcB l
  have hζ0 : ζ 0 = 0 := by
    funext l
    simp [ζ]
  have hζa : AnalyticAt ℝ ζ 0 := analyticAt_pi_iff.2 fun l => by
    show AnalyticAt ℝ (fun τ : ℝ => τ * ‖v (c l).1 (c l).2‖) 0
    fun_prop
  exact derivs_minimalAction_of_rotatedChain a θ del Ca rL r' CL s σV Ck hodd S V U v hs hsV hrL hcold hcrit
    hCV hΨ B.card hk c X T hT ζ W hW0 hζ0 hζa hζb hvW hspread
theorem pathHolonomyVariation_sub {j : ℕ} (X : F.GaugeField j) (v v' : F.Site j → Fin 4 → imaginaryQuaternions)
    (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomyVariation X v x l - pathHolonomyVariation X v' x l =
      pathHolonomyVariation X (fun x i => v x i - v' x i) x l := by apply _root_.YangMills.Construction.ChartSecondVariation.pathHolonomyVariation_sub <;> assumption
theorem sum_norm_variationCurl_sq_le {j : ℕ} (S : Finset F.Cell) (X : F.GaugeField j)
    (v : F.Site j → Fin 4 → imaginaryQuaternions) :
    ∑ p ∈ innerPlaquettes S j, ‖variationCurl X v p‖ ^ 2 ≤ 64 * ∑ b ∈ innerBonds S j, ‖v b.1 b.2‖ ^ 2 := by apply _root_.YangMills.Construction.ChartSecondVariation.sum_sq_norm_variationCurl_le <;> assumption
theorem second_variation_arith (a ca K Ce Cs2 Cd s E Cu M Nn N2 B Z Y f2 : ℝ) (ha : 0 < a) (hca : 0 < ca)
    (hK : K = 2 * Ce * (1 + 1 / a) + 128 / a) (hcaK : ca * K ≤ 1 / 4) (hCe : 0 < Ce) (hCs : 0 ≤ Cs2)
    (hCd : 0 ≤ Cd) (hs0 : 0 < s) (hs1 : s ≤ 1) (hE : E = Cu + a * M + a * Nn) (hCu : 0 ≤ Cu) (hM : 0 ≤ M)
    (hNn : 0 ≤ Nn) (hN2 : 0 ≤ N2) (hB : 0 ≤ B) (hd : E - Cd * s * (N2 + B) ≤ f2)
    (hsl : N2 ≤ Cs2 * (2 * E + 2 * a * B)) (he : Y ≤ Ce * (Cu + M) + Ce * s ^ 2 * N2)
    (hz : Z ≤ 2 * Y + 128 * Nn) (hm1 : 2 * Cd * Cs2 * s ≤ 1 / 2) (hm2 : 4 * ca * Ce * Cs2 * s ≤ 1 / 4) :
    ca * Z - (Cd * (2 * a * Cs2 + 1) + 4 * ca * Ce * Cs2 * a) * s * B ≤ f2 := by
  have hE0 : 0 ≤ E := by
    rw [hE]
    positivity
  have h1 : Cu + M ≤ (1 + 1 / a) * E := by
    have e : (1 + 1 / a) * E = Cu + M + (a * M + a * Nn + Cu / a + Nn) := by
      rw [hE]
      field_simp
      ring
    rw [e]
    have : 0 ≤ a * M + a * Nn + Cu / a + Nn := by positivity
    linarith
  have h2 : Nn ≤ E / a := by
    have e : E / a = Cu / a + M + Nn := by
      rw [hE]
      field_simp
    rw [e]
    have : 0 ≤ Cu / a + M := by positivity
    linarith
  have h3 : Z ≤ K * E + 2 * Ce * s ^ 2 * N2 := by
    have g1 : 2 * (Ce * (Cu + M)) ≤ 2 * Ce * ((1 + 1 / a) * E) := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * Ce)
      linarith
    have e : K * E = 2 * Ce * ((1 + 1 / a) * E) + 128 * (E / a) := by
      rw [hK]
      ring
    rw [e]
    linarith
  have h4 : ca * Z ≤ ca * K * E + ca * (2 * Ce * s ^ 2 * N2) := by
    have := mul_le_mul_of_nonneg_left h3 hca.le
    linarith
  have h5 : ca * K * E ≤ 1 / 4 * E := mul_le_mul_of_nonneg_right hcaK hE0
  have hss : s ^ 2 ≤ s := by nlinarith
  have h6 : ca * (2 * Ce * s ^ 2 * N2) ≤ 2 * ca * Ce * s * N2 := by
    have := mul_le_mul_of_nonneg_left hss (by positivity : 0 ≤ 2 * ca * Ce * N2)
    nlinarith
  have h7 : 2 * ca * Ce * s * N2 ≤ 2 * ca * Ce * s * (Cs2 * (2 * E + 2 * a * B)) :=
    mul_le_mul_of_nonneg_left hsl (by positivity)
  have h8 : 4 * ca * Ce * Cs2 * s * E ≤ 1 / 4 * E := mul_le_mul_of_nonneg_right hm2 hE0
  have h9 : Cd * s * N2 ≤ Cd * s * (Cs2 * (2 * E + 2 * a * B)) :=
    mul_le_mul_of_nonneg_left hsl (by positivity)
  have h10 : 2 * Cd * Cs2 * s * E ≤ 1 / 2 * E := mul_le_mul_of_nonneg_right hm1 hE0
  have e3 : (Cd * (2 * a * Cs2 + 1) + 4 * ca * Ce * Cs2 * a) * s * B =
      Cd * (2 * a * Cs2) * s * B + Cd * s * B + 4 * ca * Ce * Cs2 * a * s * B := by ring
  have e4 : Cd * s * (N2 + B) = Cd * s * N2 + Cd * s * B := by ring
  rw [e3]
  rw [e4] at hd
  linarith
theorem norm_pureComponent_le_norm (q : ℍ[ℝ]) : ‖pureComponent q‖ ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_pureComponent_le <;> assumption
theorem enclosingCell_mem_of_top (S : Finset F.Cell) {b : F.Site F.top × Fin 4} (hb : b ∈ innerBonds S F.top) :
    enclosingCell b.1 ∈ S := by
  have hx : b.1 ∈ sitesOfCells S F.top := (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
  obtain ⟨z, hz, hy⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨h, hh, he⟩ := Finset.mem_image.1 hy
  have h0 : h = 0 := by
    funext i
    have := Fintype.mem_piFinset.1 hh i
    simp at this
    simpa using this
  have hc : b.1 = z := by
    rw [← he, h0, siteOfCoords_zero, add_zero]
    exact cellCentre_top z
  have e : enclosingCell b.1 = b.1 := by
    unfold enclosingCell
    have : (fun i => (siteCoords b.1 i + ((F.blockSide : ℤ) ^ (F.top - F.top) - 1) / 2) /
        (F.blockSide : ℤ) ^ (F.top - F.top)) = siteCoords b.1 := by
      funext i
      simp
    rw [this]
    exact siteOfCoords_siteCoords b.1
  rw [e, hc]
  exact hz
theorem innerBonds_top_subset (S : Finset F.Cell) : innerBonds S F.top ⊆ bondsOver S S F.top := fun b hb => by
  classical
  unfold bondsOver
  exact Finset.mem_filter.2 ⟨hb, enclosingCell_mem_of_top S hb⟩
theorem sum_norm_sq_le_of_sub {ι : Type} (s₁ s₂ : Finset ι) (h : s₁ ⊆ s₂) (f g : ι → ℍ[ℝ]) (r : ι → ℝ)
    (hr : ∀ c, r c = ‖g c‖) :
    ∑ c ∈ s₁, ‖f c‖ ^ 2 ≤ 2 * ∑ c ∈ s₁, ‖f c - g c‖ ^ 2 + 2 * ∑ c ∈ s₂, r c ^ 2 := by
  have h1 : ∑ c ∈ s₁, ‖f c‖ ^ 2 ≤ ∑ c ∈ s₁, (2 * ‖f c - g c‖ ^ 2 + 2 * r c ^ 2) := by
    refine Finset.sum_le_sum fun c _ => ?_
    have h2 : ‖f c‖ ≤ ‖f c - g c‖ + ‖g c‖ := by
      have := norm_add_le (f c - g c) (g c)
      simpa using this
    have h3 : ‖f c‖ ^ 2 ≤ (‖f c - g c‖ + ‖g c‖) ^ 2 := by gcongr
    rw [hr]
    nlinarith [sq_nonneg (‖f c - g c‖ - ‖g c‖)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  have h4 : ∑ c ∈ s₁, r c ^ 2 ≤ ∑ c ∈ s₂, r c ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity
  linarith
theorem slice_norm_sq_arith (a Cs Cu M Nn P B N form : ℝ) (ha : 0 < a) (hCu : 0 ≤ Cu) (hM : 0 ≤ M)
    (hP0 : 0 ≤ P) (hN : 0 ≤ N) (hCs : 0 ≤ Cs) (hform : form = Cu + a * M + a * P) (hP : P ≤ 2 * Nn + 2 * B)
    (hsl : N ≤ Cs * Real.sqrt form) :
    N ^ 2 ≤ Cs ^ 2 * (2 * (Cu + a * M + a * Nn) + 2 * a * B) := by
  have hf0 : 0 ≤ form := by
    rw [hform]
    positivity
  have h1 : N ^ 2 ≤ (Cs * Real.sqrt form) ^ 2 := by gcongr
  rw [mul_pow, Real.sq_sqrt hf0] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [hform]
  have h2 := mul_le_mul_of_nonneg_left hP ha.le
  have h3 : 0 ≤ a * M := by positivity
  have e : a * (2 * Nn + 2 * B) = 2 * (a * Nn) + 2 * a * B := by ring
  rw [e] at h2
  linarith
theorem quadraticFormNormSq_unit (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) :
    quadraticFormNormSq a S R A (oneSiteWeights F) =
      ∑ q ∈ plaquettesOver S S 0, ‖linearizedCurl (R 0) A.fine q‖ ^ 2 +
      a * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2 +
      a * ∑ c ∈ bondsOver S S F.top, ‖linearPart R A F.top c.1 c.2‖ ^ 2 := by
  simp [quadraticFormNormSq, oneSiteWeights]
theorem sum_norm_variationCurl_sq_split {j : ℕ} (S : Finset F.Cell) (X : F.GaugeField j)
    (v ν : F.Site j → Fin 4 → imaginaryQuaternions) :
    ∑ p ∈ innerPlaquettes S j, ‖variationCurl X v p‖ ^ 2 ≤
      2 * ∑ p ∈ innerPlaquettes S j, ‖variationCurl X ν p‖ ^ 2 +
      128 * ∑ b ∈ innerBonds S j, ‖v b.1 b.2 - ν b.1 b.2‖ ^ 2 := by
  have h1 := sum_norm_variationCurl_sq_le S X fun x i => v x i - ν x i
  have h2 : ∑ p ∈ innerPlaquettes S j, ‖variationCurl X v p‖ ^ 2 ≤
      ∑ p ∈ innerPlaquettes S j, (2 * ‖variationCurl X ν p‖ ^ 2 +
        2 * ‖variationCurl X (fun x i => v x i - ν x i) p‖ ^ 2) := by
    refine Finset.sum_le_sum fun p _ => ?_
    have h3 : variationCurl X v p = variationCurl X ν p + variationCurl X (fun x i => v x i - ν x i) p := by
      have := pathHolonomyVariation_sub X v ν
        [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1
      simp only [variationCurl]
      rw [← this]
      abel
    rw [h3]
    have h4 := norm_add_le (variationCurl X ν p) (variationCurl X (fun x i => v x i - ν x i) p)
    have h5 : ‖variationCurl X ν p + variationCurl X (fun x i => v x i - ν x i) p‖ ^ 2 ≤
        (‖variationCurl X ν p‖ + ‖variationCurl X (fun x i => v x i - ν x i) p‖) ^ 2 := by gcongr
    nlinarith [sq_nonneg (‖variationCurl X ν p‖ - ‖variationCurl X (fun x i => v x i - ν x i) p‖)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
  linarith
theorem sum_norm_sub_topLevelAverage_sq_le (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2 - topLevelAverage R A b.1 b.2‖ ^ 2 ≤
      ∑ c ∈ bondsOver S S F.top, ‖linearPart R A F.top c.1 c.2 - (v c.1 c.2 : ℍ[ℝ])‖ ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun b _ => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (innerBonds_top_subset S) fun _ _ _ => by positivity)
  have e1 : ((v b.1 b.2 - topLevelAverage R A b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      pureComponent ((v b.1 b.2 : ℍ[ℝ]) - linearPart R A F.top b.1 b.2) := by
    rw [pureComponent_sub, pureComponent_of_re_eq_zero (v b.1 b.2).2]
    rfl
  have e2 : ‖v b.1 b.2 - topLevelAverage R A b.1 b.2‖ ≤
      ‖linearPart R A F.top b.1 b.2 - (v b.1 b.2 : ℍ[ℝ])‖ := by
    have h7 := norm_pureComponent_le_norm ((v b.1 b.2 : ℍ[ℝ]) - linearPart R A F.top b.1 b.2)
    rw [← e1, norm_sub_rev (v b.1 b.2 : ℍ[ℝ])] at h7
    exact h7
  gcongr
theorem second_variation_lower_of_direction (a ca K Ce Cs Cd s f2 : ℝ) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (A : ChainChart F) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (ha : 0 < a) (hca : 0 < ca)
    (hK : K = 2 * Ce * (1 + 1 / a) + 128 / a) (hcaK : ca * K ≤ 1 / 4) (hCe : 0 < Ce) (hCd : 0 ≤ Cd)
    (hCs : 0 ≤ Cs) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hsl : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ≤
      Cs * Real.sqrt (quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F)))
    (he : ∑ p ∈ innerPlaquettes S F.top,
        ‖variationCurl V (topLevelAverage (referenceFieldChain S V) A) p‖ ^ 2 ≤
      Ce * (∑ q ∈ plaquettesOver S S 0, ‖linearizedCurl (referenceFieldChain S V 0) A.fine q‖ ^ 2 +
          ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2) +
        Ce * s ^ 2 * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2)
    (hd : rotatedTopQuadraticForm a S (referenceFieldChain S V) A v - Cd * s *
        (weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2 +
          ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2) ≤ f2)
    (hm1 : 2 * Cd * Cs ^ 2 * s ≤ 1 / 2) (hm2 : 4 * ca * Ce * Cs ^ 2 * s ≤ 1 / 4) :
    ca * ∑ p ∈ innerPlaquettes S F.top, ‖variationCurl V v p‖ ^ 2 -
        (Cd * (2 * a * Cs ^ 2 + 1) + 4 * ca * Ce * Cs ^ 2 * a) * s *
          ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2 ≤ f2 := by
  have hP := sum_norm_sq_le_of_sub (bondsOver S S F.top) (innerBonds S F.top) (Finset.filter_subset _ _)
    (fun c => linearPart (referenceFieldChain S V) A F.top c.1 c.2) (fun c => (v c.1 c.2 : ℍ[ℝ]))
    (fun c => ‖v c.1 c.2‖) (fun _ => rfl)
  have hN := slice_norm_sq_arith a Cs _ _ _ _ _ _ _ ha (Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.sum_nonneg fun _ _ => by positivity) (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _) hCs
    (quadraticFormNormSq_unit a S (referenceFieldChain S V) A) hP hsl
  have hz := (sum_norm_variationCurl_sq_split S V v (topLevelAverage (referenceFieldChain S V) A)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (sum_norm_sub_topLevelAverage_sq_le S (referenceFieldChain S V) A v) (by norm_num)))
  exact second_variation_arith a ca K Ce (Cs ^ 2) Cd s _ _ _ _ _ _ _ _ f2 ha hca hK hcaK hCe
    (by positivity) hCd hs0 hs1 rfl (Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    (Finset.sum_nonneg fun _ _ => by positivity) hd hN he hz hm1 hm2
theorem supWeightedNorm_le_of_split (S : Finset F.Cell) (hL : 0 < F.blockSide) (del : ℝ) (R : F.FieldChain)
    (U Ulin Urest : ChainChart F) (b₁ b₂ : ℝ) (hsame : ChartEqOnBonds S U (chartSum Ulin Urest))
    (h : ∀ (y0 : F.Cell), _root_.YangMills.Construction.BlockAverages.weightedNorm S R Ulin (decayWeights F del 0 0 y0) ≤ b₁ ∧
      _root_.YangMills.Construction.BlockAverages.weightedNorm S R Urest (decayWeights F del 0 0 y0) ≤ b₂) :
    supWeightedNorm S del R U ≤ b₁ + b₂ := by
  refine supWeightedNorm_le _ _ _ _ _ fun y0 => ?_
  rw [_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_congr S R U _ _ hsame]
  have h1 := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_chartMove_le S R Ulin Urest 1 _ fun j x => (decayWeights_pos hL del 0 0 y0 j x).le
  rw [abs_one, one_mul] at h1
  exact h1.trans (add_le_add (h y0).1 (h y0).2)
theorem blockMisfit_le_of_cellMisfit (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (V : F.GaugeField F.top) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ z : F.Cell, cellMisfitSum S R U V F.depth 4 z ≤ b ^ 4) {c : F.Site F.top × Fin 4}
    (hc : c ∈ innerBonds S F.top) :
    normSubOne (chartBondMisfit R U V F.depth c) ≤ b := by
  classical
  have h1 := h (enclosingCell c.1)
  have hmem : c ∈ bondsOver S {enclosingCell c.1} (F.depth + 1) := by
    unfold bondsOver
    exact Finset.mem_filter.2 ⟨hc, Finset.mem_singleton_self _⟩
  have h2 : normSubOne (chartBondMisfit R U V F.depth c) ^ 4 ≤
      cellMisfitSum S R U V F.depth 4 (enclosingCell c.1) :=
    Finset.single_le_sum (f := fun c => normSubOne (chartBondMisfit R U V F.depth c) ^ 4)
      (fun _ _ => by positivity) hmem
  have h3 := h2.trans h1
  have h0 : 0 ≤ normSubOne (chartBondMisfit R U V F.depth c) := norm_nonneg _
  exact (pow_le_pow_iff_left₀ h0 hb (by norm_num)).1 h3
theorem second_variation_of_zero (a ca C s : ℝ) (hca : 0 < ca) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (h : ∀ b : F.Site F.top × Fin 4, v b.1 b.2 = 0) :
    ca * ∑ p ∈ innerPlaquettes S F.top, ‖variationCurl V v p‖ ^ 2 -
        C * s * ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2 ≤
        deriv (deriv fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0 ∧
      |deriv (fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0| ≤
        C * s * ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ := by
  have e0 : ∀ τ : ℝ, expRotatedField (fun x i => τ • v x i) V = V := by
    intro τ
    funext x i
    have : v x i = 0 := h (x, i)
    simp [expRotatedField, this, expUnit_zero]
  have e1 : (fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) =
      fun _ => minimalAction a S F.top V := by
    funext τ
    rw [e0]
  have hB : ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun b _ => by simp [h b]
  have hB1 : ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ = 0 :=
    Finset.sum_eq_zero fun b _ => by simp [h b]
  have hZ := sum_norm_variationCurl_sq_le S V v
  rw [hB, mul_zero] at hZ
  rw [e1, hB, hB1]
  simp only [deriv_const', deriv_const, abs_zero, mul_zero, sub_zero, le_refl, and_true]
  nlinarith
theorem second_variation_at_top (a ca K Ce Cs CD C θ del Ca rL r' CL s σV : ℝ) (Ck : ℕ → ℝ) (ha : 0 < a)
    (hca : 0 < ca) (hK : K = 2 * Ce * (1 + 1 / a) + 128 / a) (hcaK : ca * K ≤ 1 / 4) (hCe : 0 < Ce)
    (hCD : 0 < CD) (hCs : 0 ≤ Cs) (hCa : 0 < Ca) (hCL : 0 < CL) (hs0 : 0 < s) (hs1 : s ≤ 1) (hsV : s < σV)
    (hrL : 0 < r')
    (hm1 : 2 * (CD * (1 + Ca + CL)) * Cs ^ 2 * s ≤ 1 / 2) (hm2 : 4 * ca * Ce * Cs ^ 2 * s ≤ 1 / 4)
    (hC1 : (CD * (1 + Ca + CL)) * (2 * a * Cs ^ 2 + 1) + 4 * ca * Ce * Cs ^ 2 * a ≤ C) (hC2 : a * CL ≤ C)
    (hodd : Odd F.blockSide) (S : Finset F.Cell) (V : F.GaugeField F.top) (hcold : IsCold S F.top s V)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (hv : ∀ b, b ∉ innerBonds S F.top → v b.1 b.2 = 0)
    (b₀ : F.Site F.top × Fin 4) (hb₀ : v b₀.1 b₀.2 ≠ 0) (U : ChainChart F)
    (hU : IsSliceCriticalPoint a θ del Ca rL CL s S V U)
    (hLB : SliceCriticalPointLocalBounds a θ CL s S V U)
    (hTs : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
      AreUnitVectors X →
      ∃ T : (Fin k → ℝ) → ChainChart F, IsRotatedChain a θ del Ca rL r' CL s Ck S V c X U T)
    (hCV : ∀ (s' : ℝ) (v' : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s' → s' ≤ σV →
      IsCold S F.top s' V → (∀ y i, ‖v' y i‖ ≤ s') → ∀ U' : ChainChart F,
      IsCriticalChainOverTop a θ del Ca CL s' S V (rotatedField v' V) U' →
      minimalAction a S F.top (rotatedField v' V) =
        chartAction a S (referenceFieldChain S V) U' (rotatedField v' V))
    (hsl : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ≤
        Cs * Real.sqrt (quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F)))
    (hE : ∀ A : ChainChart F,
      ∑ p ∈ innerPlaquettes S F.top, ‖variationCurl V (topLevelAverage (referenceFieldChain S V) A) p‖ ^ 2 ≤
        Ce * (∑ q ∈ plaquettesOver S S 0, ‖linearizedCurl (referenceFieldChain S V 0) A.fine q‖ ^ 2 +
            ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2) +
          Ce * s ^ 2 * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2)
    (hΨ : AnalyticAt ℝ (fun x : ChartValues S × ℝ => chartAction a S (referenceFieldChain S V)
      (chartOfValues S U x.1) (rotatedField (fun y i => x.2 • v y i) V)) (chartValues S U, 0))
    (hu : supWeightedNorm S del (referenceFieldChain S V) U ≤ (Ca + CL) * s)
    (hD2 : ∀ A : ChainChart F,
      |deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ)
          (rotatedField (fun y i => τ • v y i) V)) 0 -
          rotatedTopQuadraticForm a S (referenceFieldChain S V) A v| ≤
        CD * (s + supWeightedNorm S del (referenceFieldChain S V) U) *
          (_root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2 +
            ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2))
    (hD1 : |deriv (fun τ : ℝ => chartAction a S (referenceFieldChain S V) U
        (rotatedField (fun y i => τ • v y i) V)) 0| ≤
      a * ∑ c ∈ innerBonds S F.top,
        normSubOne (chartBondMisfit (referenceFieldChain S V) U V F.depth c) * ‖v c.1 c.2‖) :
    ca * ∑ p ∈ innerPlaquettes S F.top, ‖variationCurl V v p‖ ^ 2 -
        C * s * ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2 ≤
        deriv (deriv fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0 ∧
      |deriv (fun τ : ℝ => minimalAction a S F.top (expRotatedField (fun x i => τ • v x i) V)) 0| ≤
        C * s * ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ := by
  obtain ⟨A, hA, e1, e2⟩ := derivs_minimalAction a θ del Ca rL r' CL s σV Ck hodd S V U v hs0 hsV hrL hcold
    hv b₀ hb₀ hU.critical hTs hCV hΨ
  rw [e1, e2]
  have hB0 : 0 ≤ ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hB1 : 0 ≤ ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  constructor
  · have hd : rotatedTopQuadraticForm a S (referenceFieldChain S V) A v - (CD * (1 + Ca + CL)) * s *
        (weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2 +
          ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2) ≤
        deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ)
          (rotatedField (fun y i => τ • v y i) V)) 0 := by
      have h1 := (abs_le.1 (hD2 A)).1
      have h2 : 0 ≤ _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2 +
          ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2 := by positivity
      have h3 : CD * (s + supWeightedNorm S del (referenceFieldChain S V) U) ≤ CD * (1 + Ca + CL) * s := by
        have : s + supWeightedNorm S del (referenceFieldChain S V) U ≤ (1 + Ca + CL) * s := by linarith
        have := mul_le_mul_of_nonneg_left this hCD.le
        linarith
      have h4 := mul_le_mul_of_nonneg_right h3 h2
      linarith
    have hres := second_variation_lower_of_direction a ca K Ce Cs (CD * (1 + Ca + CL)) s _ S V A v ha hca hK
      hcaK hCe (by positivity) hCs hs0 hs1 (hsl A hA) (hE A) hd hm1 hm2
    refine le_trans ?_ hres
    have h5 := mul_le_mul_of_nonneg_right hC1 (mul_nonneg hs0.le hB0)
    nlinarith
  · refine hD1.trans ?_
    have hm : ∀ c ∈ innerBonds S F.top,
        normSubOne (chartBondMisfit (referenceFieldChain S V) U V F.depth c) * ‖v c.1 c.2‖ ≤
        CL * s * ‖v c.1 c.2‖ := by
      intro c hc
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine blockMisfit_le_of_cellMisfit S _ U V (CL * s) (by positivity) (fun z => ?_) hc
      have h1 := (hLB.misfits_on_cells F.depth z (Nat.lt_succ_self _)).1
      have e : F.top - 1 - F.depth = 0 := by simp [BlockFrame.top]
      rw [e, pow_zero, mul_one] at h1
      exact h1
    have h6 := Finset.sum_le_sum hm
    rw [← Finset.mul_sum] at h6
    have h7 := mul_le_mul_of_nonneg_left h6 ha.le
    refine h7.trans ?_
    have h8 := mul_le_mul_of_nonneg_right hC2 (mul_nonneg hs0.le hB1)
    nlinarith
theorem two_mul_mul_le_half (x s : ℝ) (hx : 0 ≤ x) (hs0 : 0 < s) (hs : s ≤ 1 / (4 * x + 1)) :
    2 * x * s ≤ 1 / 2 := by
  have hp : 0 < 4 * x + 1 := by linarith
  rw [le_div_iff₀ hp] at hs
  nlinarith
set_option maxHeartbeats 2000000 in
theorem coldTopSecondVariation (hCC : rotatedCriticalChainsStatement)
    (hCVs : criticalValueEqMinimalActionStatement)
    (hSN : sliceNormFormBoundStatement) (hDs : rotatedTopActionStatement)
    (hEs : topAverageCurlBoundStatement) : coldTopSecondVariationStatement := by
  intro a ha
  obtain ⟨c₁, Cs, L1, hc₁, hCs, hSl⟩ := hSN a ha
  obtain ⟨Ce, hCe, LE, hEL⟩ := hEs
  obtain ⟨θ, del, Ca, hθ, hθ8, hdel, hdel8, hCa, LC, hCCL⟩ := hCC a ha
  obtain ⟨LV, hCVL⟩ := hCVs a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨LD, hDL⟩ := hDs a del ha hdel hdel8
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * Ce * (1 + 1 / a) + 128 / a := ⟨_, rfl⟩
  have hKp : 0 < K := by
    rw [hK]
    positivity
  obtain ⟨ca, hcaD⟩ : ∃ ca, ca = 1 / (4 * K) := ⟨_, rfl⟩
  have hca : 0 < ca := by
    rw [hcaD]
    positivity
  have hcaK : ca * K ≤ 1 / 4 := by
    rw [hcaD]
    have : 1 / (4 * K) * K = 1 / 4 := by
      field_simp
    rw [this]
  refine ⟨ca, hca, max (max L1 LE) (max LC (max LV LD)), fun L hodd hL => ?_⟩
  have hL1 : L1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLE : LE ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLC : LC ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLV : LV ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLD : LD ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  obtain ⟨cE, hcE, hEF⟩ := hEL L hodd hLE
  obtain ⟨rL, r', sL, CL, Ck, hrL, hr'0, hr'rL, hsL, hCL, -, hmain, -⟩ := hCCL L hodd hLC
  obtain ⟨σV, hσV, hCV⟩ := hCVL L hodd hLV CL hCL
  obtain ⟨cD, CD, hcD, hCD, hD⟩ := hDL L hodd hLD
  obtain ⟨Cd, hCdD⟩ : ∃ Cd, Cd = CD * (1 + Ca + CL) := ⟨_, rfl⟩
  have hCd : 0 < Cd := by
    rw [hCdD]
    positivity
  obtain ⟨x₁, hx₁⟩ : ∃ x, x = Cd * Cs ^ 2 := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x, x = 2 * ca * Ce * Cs ^ 2 * 2 := ⟨_, rfl⟩
  have hx₁0 : 0 ≤ x₁ := by
    rw [hx₁]
    positivity
  have hx₂0 : 0 ≤ x₂ := by
    rw [hx₂]
    positivity
  obtain ⟨C, hCdef⟩ : ∃ C, C = Cd * (2 * a * Cs ^ 2 + 1) + 4 * ca * Ce * Cs ^ 2 * a + a * CL + 1 :=
    ⟨_, rfl⟩
  have hn1 : 0 ≤ Cd * (2 * a * Cs ^ 2 + 1) + 4 * ca * Ce * Cs ^ 2 * a := by positivity
  have hn2 : 0 ≤ a * CL := by positivity
  have hCp : 0 < C := by
    rw [hCdef]
    linarith
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, σ₀ = min (min (min 1 c₁) (min cE sL)) (min (min (σV / 2) cD)
      (min (cD / (Ca + CL)) (min (1 / (4 * x₁ + 1)) (1 / (4 * x₂ + 1))))) := ⟨_, rfl⟩
  have hCaCL : 0 < Ca + CL := by positivity
  have hσ₀p : 0 < σ₀ := by
    rw [hσ₀]
    refine lt_min (lt_min (lt_min one_pos hc₁) (lt_min hcE hsL)) (lt_min (lt_min (by positivity) hcD)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  refine ⟨C, σ₀, hCp, hσ₀p, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsσ hcold v hv
  have hodd' : Odd F.blockSide := by rw [hFL]; exact hodd
  have hL0 : 0 < F.blockSide := hodd'.pos
  rw [hσ₀] at hsσ
  have g1 := le_min_iff.1 hsσ
  have g2 := le_min_iff.1 g1.1
  have g3 := le_min_iff.1 g1.2
  have g4 := le_min_iff.1 g2.1
  have g5 := le_min_iff.1 g2.2
  have g6 := le_min_iff.1 g3.1
  have g7 := le_min_iff.1 g3.2
  have g8 := le_min_iff.1 g7.2
  have hs1 : s ≤ 1 := g4.1
  have hsc₁ : s ≤ c₁ := g4.2
  have hscE : s ≤ cE := g5.1
  have hssL : s ≤ sL := g5.2
  have hsV : s < σV := by linarith [g6.1]
  have hscD : s ≤ cD := g6.2
  have hscD' : (Ca + CL) * s ≤ cD := by
    have := g7.1
    rw [le_div_iff₀ hCaCL] at this
    linarith
  by_cases hv0 : ∀ b : F.Site F.top × Fin 4, v b.1 b.2 = 0
  · exact second_variation_of_zero a ca C s hca S V v hv0
  push_neg at hv0
  obtain ⟨b₀, hb₀⟩ := hv0
  obtain ⟨U, hU, hLB, hTs⟩ := hmain F m S hFL hamb hm hreg s V hs hssL hcold
  have hu : supWeightedNorm S del (referenceFieldChain S V) U ≤ (Ca + CL) * s := by
    obtain ⟨Ulin, Urest, hsame, hsp⟩ := hU.split
    have := supWeightedNorm_le_of_split S hL0 del (referenceFieldChain S V) U Ulin Urest (Ca * s)
      (CL * s ^ 2) hsame fun y0 => hsp 0 y0 0 (Or.inr rfl)
    refine this.trans ?_
    have h2 : CL * s ^ 2 ≤ CL * s := by
      have : s ^ 2 ≤ s := by nlinarith
      exact mul_le_mul_of_nonneg_left this hCL.le
    linarith
  obtain ⟨hDa, hDU⟩ := hD F m S hFL hamb hm hreg s V hs hscD hcold v hv
  have hΨ := hDa (ChartValues S) (chartValues S U) (chartOfValues S U) (by
      rw [chartOfValues_chartValues]
      exact hu.trans hscD') (fun b hb => analyticAt_chartOfValues_fine S U _ hb)
    (fun j hj b hb => analyticAt_chartOfValues_coarse S U _ hj hb)
  obtain ⟨hD2, hD1⟩ := hDU U (hu.trans hscD')
  have hm1 : 2 * (CD * (1 + Ca + CL)) * Cs ^ 2 * s ≤ 1 / 2 := by
    have := two_mul_mul_le_half x₁ s hx₁0 hs g8.1
    rw [hx₁, hCdD] at this
    linarith
  have hm2 : 4 * ca * Ce * Cs ^ 2 * s ≤ 1 / 4 := by
    have := two_mul_mul_le_half x₂ s hx₂0 hs g8.2
    rw [hx₂] at this
    nlinarith
  have hsl : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ≤
        Cs * Real.sqrt (quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F)) := by
    intro A hA
    have h1 := hSl F m S hodd' (hFL ▸ hL1) hamb hm hreg s V hs hsc₁ hcold (fun _ => 0) 0 0 0
      (by norm_num) (by norm_num) (fun _ _ => by simp) A hA
    rwa [classWeight_zero] at h1
  have hEF' : ∀ A : ChainChart F, _ := fun A => hEF F m S hFL hamb hm hreg s V hs hscE hcold A
  have hC1 : (CD * (1 + Ca + CL)) * (2 * a * Cs ^ 2 + 1) + 4 * ca * Ce * Cs ^ 2 * a ≤ C := by
    rw [hCdef, ← hCdD]
    linarith
  have hC2 : a * CL ≤ C := by
    rw [hCdef]
    linarith
  exact second_variation_at_top a ca K Ce Cs CD C θ del Ca rL r' CL s σV Ck ha hca hK hcaK hCe hCD hCs.le
    hCa hCL hs hs1 hsV hr'0 hm1 hm2 hC1 hC2 hodd' S V hcold v hv b₀ hb₀ U hU hLB hTs
    (fun s' v' h1 h2 h3 h4 U' h5 => (hCV F m S hFL hamb hm hreg s' V v' h1 h2 h3 h4 U' h5).1)
    hsl hEF' hΨ hu hD2 hD1
end YangMills.Construction.BlockAverages.ColdTopSecondVariation
end
