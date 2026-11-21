import YangMills.Construction.ClusterExpansionOfAStep.AdmissionEqualInBoxes
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderAtAbelianFields
import YangMills.Construction.ColdStepAtMirrorFrames.ChainOfConstantCurvature
import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import Mathlib
import YangMills.Construction.ColdStepAtMirrorFrames.TopFamiliesReadOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.TopOfTheCurvedChainOnATorus
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
def secondOrderDensityStatement : Prop :=
  ∀ (L t n₀ : ℕ) (σ δ C : ℝ) (h : TopLevelFamily), Odd L → 0 < σ → 0 < δ → 0 < C →
    IsLocalDensity L t n₀ σ h → DerivDecay L t n₀ σ h (fun _ n => C / torusDecayFactor L δ n) →
    IsLocalOnTori L t n₀ σ (centredFamily h) (fun r => C / torusDecayFactor L δ r) →
    ∃ q : BondBilinearForm,
      (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform h L t n b b' X X') Filter.atTop
        (nhds (q b b' X X'))) ∧
      ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (l : ℕ) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
        ‖X‖ = 1 → μ < ν →
        IsLinearPotential (constantPlaneCurvature X μ ν) B →
        ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
            q e.1 e.2 (B e.1) (B e.2)) v ∧
          ∀ ε : ℝ, 0 < ε → ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ Y : (cubicTorusFrame L t n).Cell,
            |centredFamily h (cubicTorusFrame L t n) Y
                (constantCurvatureChain (cubicTorusFrame L t n) X μ ν l (t + 1)) -
              (2 * Real.pi * l / (n : ℝ) ^ 2) ^ 2 / 2 * v| ≤
              ε * (2 * Real.pi * l / (n : ℝ) ^ 2) ^ 2
end ColdStepAtMirrorFrames
end YangMills.Construction
end

noncomputable section
open scoped Topology Quaternion
open Filter
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields YangMills.Construction.LumpContours
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace SecondOrderAtConstantCurvature
def fiveBlockGrid : LumpGrid 81925 where
  lower o := (o + 8192) / 16385 * 16385 - 8192
  upper o := (o + 8192) / 16385 * 16385 + 8192
  mem_interval := by
    intro o ho
    have h := abs_le.mp ho
    norm_num at h ⊢
    omega
  interval_eq := by
    intro o o' ho h₁ h₂
    have h := abs_le.mp ho
    norm_num at h
    omega
  interval_length := by
    intro o ho
    norm_num
  lower_neg := by
    intro o ho
    have h := abs_le.mp ho
    norm_num at h
    omega
def topParameters (L : ℕ) (σ δ : ℝ) (N : ℕ) : StepParameters where
  coupling := 1
  side := 81925
  side_ne := ⟨by norm_num⟩
  grid := fiveBlockGrid
  baseDepth := 0
  threshold := σ
  κ := 1 / 8
  κ₁ := 1
  rt := δ * 2 ^ 10
  n₁ := (L : ℝ) ^ (1 / 640 : ℝ)
  E := 1
  E₃ := 1
  derivBound := 1
  n₀ := N
  y₁ := (2 ^ 16 : ℝ) ^ 100
  B := 1
theorem topParameters_admissible {L N : ℕ} {σ δ : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hδ : 0 < δ)
    (hN : 4096 ≤ N) : (topParameters L σ δ N).Admissible where
  a_ge := le_refl _
  L_odd := by show Odd 81925; decide
  L_ge := by show 2 ^ 16 ≤ 81925; norm_num
  σ_pos := hσ
  κ_pos := by show (0 : ℝ) < 1 / 8; norm_num
  κ_le := le_refl _
  κ₁_pos := zero_lt_one
  rt_pos := by show 0 < δ * 2 ^ 10; positivity
  n₁_pos := by
    show 0 < (L : ℝ) ^ (1 / 640 : ℝ)
    exact Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  E_pos := zero_lt_one
  E_ge := le_refl _
  depth_lt := by show 11 * 2 ^ 12 * 0 < 81925; norm_num
  E₃_pos := zero_lt_one
  B_pos := zero_lt_one
  Cder_ge := le_refl _
  n₀_ge := hN
  y₁_ge := by
    show (1 : ℝ) ≤ (2 ^ 16 : ℝ) ^ 100
    exact one_le_pow₀ (by norm_num)
  range_ge := by
    show 2 ^ 16 ≤ clusterRange ((2 ^ 16 : ℝ) ^ 100)
    have h : ((2 ^ 16 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 ^ 16 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    unfold clusterRange
    rw [h]
    have h' := Nat.le_ceil (2 ^ 16 : ℝ)
    exact_mod_cast h'
theorem topParameters_weight (L : ℕ) (σ δ : ℝ) (N m : ℕ) :
    (topParameters L σ δ N).weight m = torusDecayFactor L δ m := by
  have h : δ * 2 ^ 10 / 2 ^ 10 = δ := by field_simp
  simp only [StepParameters.weight, StepParameters.weightRate, topParameters, torusDecayFactor, h]
section Casts
variable {F : BlockFrame} {m j : ℕ}
theorem zmod_cast_cast {a b : ℕ} (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
theorem siteOfCoords_toTorusSite (hp : ∀ i, F.period j i = m) (y : F.Site j) :
    (siteOfCoords j fun k => (((toTorusSite m y k).cast : ℤ)) : F.Site j) = y := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfTorusSite_toTorusSite <;> assumption
theorem readAtLevel_restrictToTorus (hp : ∀ i, F.period j i = m) (W : F.GaugeField j) :
    readAtLevel F j (restrictToTorus m W) = W := by
  funext x i
  exact congrFun (congrArg W (siteOfCoords_toTorusSite hp x)) i
end Casts
theorem torusFrame_period_top (L t n : ℕ) (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.CongruentAdmission.torusFrame_period_succ <;> assumption
theorem centered_densityOfTopFamily (h : TopLevelFamily) (L t n : ℕ) (Y : (torusFrame L t n).Cell)
    (W : (torusFrame L t n).GaugeField (torusFrame L t n).top) :
    centered (densityOfTopFamily L t h) n (toTorusSite n Y) (restrictToTorus n W) =
      centredFamily h (torusFrame L t n) Y W := by
  have hY := siteOfCoords_toTorusSite (torusFrame_period_top L t n) Y
  have hW := readAtLevel_restrictToTorus (torusFrame_period_top L t n) W
  simp only [centered, densityOfTopFamily, centredFamily]
  rw [hY, hW]
  rfl
section ZeroFlux
variable {F : BlockFrame}
theorem expUnit_zero : expUnit 0 = 1 := Subtype.ext (by simp [expUnit])
theorem pathHolonomy_uniformField {j : ℕ} (l : List PathStep) (x : F.Site j) :
    pathHolonomy (uniformField F j) x l = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathHolonomy_one <;> assumption
theorem quaternionUnitPart_smul_one {c : ℝ} (hc : 0 < c) :
    quaternionUnitPart (c • (1 : ℍ[ℝ])) = 1 := by
  unfold quaternionUnitPart
  split_ifs with h
  · have hq := h.choose_spec.2
    have hn : ‖c • (1 : ℍ[ℝ])‖ = c := by simp [norm_smul, abs_of_pos hc]
    have hq' : c • (1 : ℍ[ℝ]) = c • (h.choose : ℍ[ℝ]) :=
      hq.trans (congrArg (· • (h.choose : ℍ[ℝ])) hn)
    have h1 := smul_right_injective ℍ[ℝ] hc.ne' hq'
    exact Subtype.ext h1.symm
  · rfl
theorem contourAverage_uniformField (hL : 0 < F.blockSide) {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ contourAverage (uniformField F j) c = c₀ • (1 : ℍ[ℝ]) := by
  have hne : (centredCube F.blockSide).Nonempty := by
    refine ⟨0, ?_⟩
    simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc, Pi.zero_apply]
    intro _
    omega
  refine ⟨1 / (24 * (F.blockSide : ℝ) ^ 4) *
    ((centredCube F.blockSide).card * Fintype.card (Equiv.Perm (Fin 4))), by positivity, ?_⟩
  simp only [contourAverage, pathHolonomy_uniformField, Finset.sum_const, Finset.card_univ,
    Submonoid.coe_one, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
theorem constantCurvatureField_zero (X : imaginaryQuaternions) (μ ν : Fin 4) :
    constantCurvatureField F X μ ν 0 = uniformField F 0 := by
  funext z i
  simp only [constantCurvatureField, uniformField]
  split_ifs <;> simp [expUnit_zero]
theorem constantCurvatureChain_zero (hL : 0 < F.blockSide) (X : imaginaryQuaternions) (μ ν : Fin 4) :
    ∀ j, constantCurvatureChain F X μ ν 0 j = uniformField F j
  | 0 => constantCurvatureField_zero X μ ν
  | j + 1 => by
    funext y i
    obtain ⟨c₀, h₀, hc⟩ := contourAverage_uniformField hL (j := j) (y, i)
    simp only [constantCurvatureChain]
    rw [constantCurvatureChain_zero hL X μ ν j, hc, quaternionUnitPart_smul_one h₀]
    rfl
end ZeroFlux
theorem hasPolynomialGrowth_of_linearPotential {Fm : Fin 4 → Fin 4 → imaginaryQuaternions}
    {B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions}
    (h : IsLinearPotential Fm B) : HasPolynomialGrowth B := by
  obtain ⟨A, e, hB, -⟩ := h
  refine ⟨∑ μ, (∑ ν, ‖A μ ν‖ + ‖e μ‖), 1, ?_⟩
  rintro ⟨x, μ⟩
  have hx : ∀ ν, |((x ν : ℤ) : ℝ)| ≤ offsetSupNorm x := by
    intro ν
    have h1 : (x ν).natAbs ≤ offsetSupNorm x :=
      Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ ν)
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast h1
  have hK : ∑ ν, ‖A μ ν‖ + ‖e μ‖ ≤ ∑ μ', (∑ ν, ‖A μ' ν‖ + ‖e μ'‖) :=
    Finset.single_le_sum (f := fun μ' => ∑ ν, ‖A μ' ν‖ + ‖e μ'‖)
      (fun _ _ => by positivity) (Finset.mem_univ μ)
  have h1 : ‖∑ ν, ((x ν : ℤ) : ℝ) • A μ ν‖ ≤ (offsetSupNorm x : ℝ) * ∑ ν, ‖A μ ν‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ν _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hx ν) (norm_nonneg _)
  have hA : 0 ≤ ∑ ν, ‖A μ ν‖ := by positivity
  have he : 0 ≤ ‖e μ‖ := norm_nonneg _
  show ‖B (x, μ)‖ ≤ _ * (1 + (offsetSupNorm x : ℝ)) ^ 1
  rw [hB, pow_one]
  calc ‖∑ ν, ((x ν : ℤ) : ℝ) • A μ ν + e μ‖
      ≤ (offsetSupNorm x : ℝ) * ∑ ν, ‖A μ ν‖ + ‖e μ‖ := (norm_add_le _ _).trans (by linarith)
    _ ≤ (∑ ν, ‖A μ ν‖ + ‖e μ‖) * (1 + (offsetSupNorm x : ℝ)) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (by linarith)
theorem planeUnitForm_antisymm {μ ν : Fin 4} (h : μ < ν) (i j : Fin 4) :
    planeUnitForm μ ν i j = - planeUnitForm μ ν j i := by
  have hne : μ ≠ ν := h.ne
  simp only [planeUnitForm]
  split_ifs <;> simp_all
theorem curvatureAlong_planeUnitForm (X : imaginaryQuaternions) (μ ν : Fin 4) :
    curvatureAlong X (planeUnitForm μ ν) = constantPlaneCurvature X μ ν := by
  funext a b
  simp only [curvatureAlong, planeUnitForm, constantPlaneCurvature]
  split_ifs
  · exact one_smul _ _
  · exact Subtype.ext (by
      show (-1 : ℝ) • (X : ℍ[ℝ]) = -(X : ℍ[ℝ])
      rw [neg_smul, one_smul])
  · exact zero_smul _ _
theorem eventually_flux_small {l : ℕ} (hl : 0 < l) {γ₀ : ℝ} (hγ₀ : 0 < γ₀) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < 2 * Real.pi * l / (n : ℝ) ^ 2 ∧ 2 * Real.pi * l / (n : ℝ) ^ 2 < γ₀ ∧
      2 * Real.pi * l / (n : ℝ) ^ 2 ≤ 1 ∧
      4 * Real.log (1 / (2 * Real.pi * l / (n : ℝ) ^ 2)) ^ 2 + 4 < n := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hc1 : 1 ≤ 2 * Real.pi * l := by
    nlinarith [Real.pi_gt_three]
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop
  have hγ : Tendsto (fun n : ℕ => 2 * Real.pi * l / (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  have h1 := hγ.eventually (gt_mem_nhds hγ₀)
  have h2 := hγ.eventually (gt_mem_nhds (zero_lt_one (α := ℝ)))
  have h3 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ 1 / 32 * x := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show (0 : ℝ) < 1 / 32 by norm_num)
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    simpa [abs_of_nonneg hx0, abs_of_nonneg (sq_nonneg (Real.log x))] using hx
  have h4 := tendsto_natCast_atTop_atTop.eventually h3
  filter_upwards [h1, h2, h4, eventually_ge_atTop 9] with n h1 h2 h4 hn
  have hn0 : 0 < n := by omega
  have hnr : (9 : ℝ) ≤ n := by exact_mod_cast hn
  have hg : 0 < 2 * Real.pi * l / (n : ℝ) ^ 2 := by positivity
  refine ⟨hn0, hg, h1, h2.le, ?_⟩
  have hlog : Real.log (1 / (2 * Real.pi * l / (n : ℝ) ^ 2)) =
      2 * Real.log n - Real.log (2 * Real.pi * l) := by
    have hc : (0 : ℝ) < 2 * Real.pi * l := by linarith
    rw [one_div_div, Real.log_div (by positivity) hc.ne', Real.log_pow]
    norm_num
  have hc0 : 0 ≤ Real.log (2 * Real.pi * l) := Real.log_nonneg hc1
  have hpos : 0 ≤ Real.log (1 / (2 * Real.pi * l / (n : ℝ) ^ 2)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hg]
    linarith
  have hle : Real.log (1 / (2 * Real.pi * l / (n : ℝ) ^ 2)) ≤ 2 * Real.log n := by
    rw [hlog]
    linarith
  have hsq' : Real.log (1 / (2 * Real.pi * l / (n : ℝ) ^ 2)) ^ 2 ≤ (2 * Real.log n) ^ 2 :=
    pow_le_pow_left₀ hpos hle 2
  nlinarith
end SecondOrderAtConstantCurvature
open SecondOrderAtConstantCurvature in
theorem secondOrderDensityStatement_holds (hS : SecondOrderAtAbelianFields)
    (hT : TopFamilyOnTori) (hC : ConstantCurvatureTopOnTorus) :
    secondOrderDensityStatement := by
  intro L t n₀ σ δ C h hL hσ hδ hC0 hD hDec hCmp
  have hLpos : 0 < L := hL.pos
  obtain ⟨N, hN⟩ : ∃ N, N = n₀ + 4096 := ⟨_, rfl⟩
  have hmono : ∀ F, IsCubicTopTorus L t N F → IsCubicTopTorus L t n₀ F := by
    rintro F ⟨h1, h2, n, h3, h4⟩
    exact ⟨h1, h2, n, h3, by omega⟩
  have hD' : IsLocalDensity L t N σ h :=
    ⟨fun F hF => hD.smooth F (hmono F hF), fun F hF => hD.gauge_invariant F (hmono F hF),
      fun F hF => hD.translation_invariant F (hmono F hF)⟩
  have hDec' : DerivDecay L t N σ h (fun _ n => C / torusDecayFactor L δ n) :=
    fun F hF => hDec F (hmono F hF)
  have hCmp' : IsLocalOnTori L t N σ (centredFamily h) (fun r => C / torusDecayFactor L δ r) :=
    fun F F' hF hF' => hCmp F F' (hmono F hF) (hmono F' hF')
  have hN0 : 0 < N := by omega
  obtain ⟨hT1, hT2, -, hT4, hT5⟩ := hT L t N σ h hN0
  obtain ⟨hsm, hga, htr⟩ := hT1 hD'
  have hT3 := (hT L t N σ (centredFamily h) hN0).2.2.1 _ hCmp'
  have hfam : IsCurvatureFamily (topParameters L σ δ N) C (densityOfTopFamily L t h) :=
    { smooth := fun n _ hn y W hW => hsm n hn y W hW
      gauge := fun n _ hn y g W hW => hga n hn y g W hW
      translation := fun n _ hn y u W hW => htr n hn y u W hW
      decay := by
        intro n _ hn y W hW k c X hk1 hk3 hX
        rw [topParameters_weight]
        exact hT2 _ hDec' n hn y W hW k c X hk1 hk3 hX
      local_density := by
        intro n n' _ _ hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
        rw [topParameters_weight]
        have e₁ : centered (densityOfTopFamily L t h) n y =
            densityOfTopFamily L t (centredFamily h) n y :=
          funext fun V => (hT4 n y V).symm
        have e₂ : centered (densityOfTopFamily L t h) n' y' =
            densityOfTopFamily L t (centredFamily h) n' y' :=
          funext fun V => (hT4 n' y' V).symm
        rw [e₁, e₂]
        exact hT3 n n' hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX }
  obtain ⟨hlim, -, -, hsum, -, -, hmain, -⟩ :=
    hS (topParameters L σ δ N) (topParameters_admissible hLpos hσ hδ (by omega)) C
      (densityOfTopFamily L t h) hfam
  refine ⟨secondDerivLimit (densityOfTopFamily L t h), ?_, ?_⟩
  · intro b b' X X'
    refine (hlim b b' X X').congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : NeZero n := ⟨hn.ne'⟩
    exact (hT5 n b b' X X').symm
  · intro X μ ν l B hX hμν hB
    have hB' : IsLinearPotential (curvatureAlong X (planeUnitForm μ ν)) B := by
      rw [curvatureAlong_planeUnitForm]
      exact hB
    have hG := hasPolynomialGrowth_of_linearPotential hB
    refine ⟨_, (hsum B B hG hG).hasSum, ?_⟩
    intro ε hε
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · refine ⟨0, fun n _ Y => ?_⟩
      have e : centredFamily h (cubicTorusFrame L t n) Y
          (uniformField (cubicTorusFrame L t n) (t + 1)) = 0 := sub_self _
      have hz : 2 * Real.pi * ((0 : ℕ) : ℝ) / (n : ℝ) ^ 2 = 0 := by simp
      rw [constantCurvatureChain_zero (F := cubicTorusFrame L t n) hLpos X μ ν (t + 1), e, hz]
      simp
    · obtain ⟨γ₀, hγ₀, hγ⟩ := hmain (planeUnitForm μ ν) (planeUnitForm_antisymm hμν) ε hε
      obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (eventually_flux_small hl hγ₀)
      refine ⟨n₁, fun n hn Y => ?_⟩
      obtain ⟨hn0, hg0, hg1, hg2, hg3⟩ := hn₁ n hn
      have : NeZero n := ⟨hn0.ne'⟩
      have hV := hC (cubicTorusFrame L t n) X μ ν n l hL (fun _ => rfl) hn0 hX hμν hg2
      have h1 := hγ _ hg0 hg1 n hg3 X _ B hX hV hB' (toTorusSite n Y)
      have e : centered (densityOfTopFamily L t h) n (toTorusSite n Y)
          (restrictToTorus n (constantCurvatureChain (cubicTorusFrame L t n) X μ ν l
            (cubicTorusFrame L t n).top)) =
          centredFamily h (cubicTorusFrame L t n) Y
            (constantCurvatureChain (cubicTorusFrame L t n) X μ ν l (t + 1)) :=
        centered_densityOfTopFamily h L t n Y _
      rw [e] at h1
      exact h1
end YangMills.Construction.ColdStepAtMirrorFrames
end
