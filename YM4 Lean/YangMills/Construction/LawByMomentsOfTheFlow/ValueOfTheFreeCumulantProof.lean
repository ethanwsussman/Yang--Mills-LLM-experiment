import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOfTheGaussianChain
import YangMills.Construction.LawByMomentsOfTheFlow.CumulantOfTheBottomCurvature
import YangMills.Construction.LawByMomentsOfTheFlow.LatticeNumberNearTheCyclicFormula
import YangMills.Construction.LawByMomentsOfTheFlow.TorusSumNearTheLatticeNumber
import YangMills.Construction.LawByMomentsOfTheFlow.ValueOfTheFreeCumulant
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheScale
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings WeightedResponses ResponseInTheExpansion BlockAverages LevelTestFunctions TestFunctions CyclicFormula
private theorem radius_nonneg_of_point {Λ : MomentParameters} (S : MomentPoint Λ) (i : Fin Λ.k) : 0 ≤ Λ.R := by
  obtain ⟨p, hp⟩ := S.supAdmissible.exists_ne_zero i
  have hp' : S.data.fn i _ ≠ 0 := hp
  have hx := subset_tsupport (S.data.fn i) (Function.mem_support.mpr hp')
  exact (abs_nonneg _).trans (S.supAdmissible.isSupTestFamily.abs_coord_le i _ hx 0)
private theorem cumulant_bounds_at_point {Λ : MomentParameters} (S : MomentPoint Λ) (CL CT : ℝ)
    (hCL : ∀ (φ : Fin Λ.k → EuclideanFourSpace → ℝ) (L s : ℕ), 1 ≤ L → IsSupTestFamily Λ.R Λ.d φ →
      |latticeCycleSum L s (⌈Λ.R * (L : ℝ) ^ s⌉₊ + 2) φ| ≤ CL ∧
      |latticeCycleSum L s (⌈Λ.R * (L : ℝ) ^ s⌉₊ + 2) φ - cyclicMomentFormula Λ.k φ| ≤ CL * (L : ℝ) ^ (-(s : ℝ)))
    (hCT : ∀ (L : ℕ) [NeZero L] (P : LevelData Λ.k), P.SupAdmissible L Λ.R Λ.d →
      |3 * (if Λ.k = 2 then 1 / 2 else 1) * ∑ σ ∈ unorientedCyclicOrders Λ.k, ∑ p : Fin Λ.k → OrientedPlaquette (fineSide L P.windowLevel (P.period L)),
          (∏ i, P.testWeight L i _ (p i).1) * ∏ c : Fin Λ.k, torusCurvatureProjection (p (σ c)) (p (σ (c + 1))) -
        latticeCycleSum L P.scaleLevel (⌈Λ.R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2) P.fn| ≤ CT * (L : ℝ) ^ (-(4 * ((P.windowLevel : ℝ) - (P.scaleLevel : ℝ)))))
    (X₀ : ℝ) (κ : ℝ)
    (hκ : κ = 3 * (if Λ.k = 2 then 1 / 2 else 1) * ∑ σ ∈ unorientedCyclicOrders Λ.k,
      ∑ p : Fin Λ.k → OrientedPlaquette (fineSide Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side)),
        (∏ i, S.weight i _ (p i).1) * ∏ c : Fin Λ.k, torusCurvatureProjection (p (σ c)) (p (σ (c + 1))))
    (hwin : X₀ ≤ S.scaleCoupling → (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) ≤ S.scaleCoupling⁻¹ ∧
      4 * (S.logIndex : ℝ) ≤ (S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ)) :
    |κ| ≤ |CL| + |CT| ∧
    |κ - S.latticeCycleSumAt S.data.scaleLevel| ≤ (|CL| + |CT|) * (Λ.stepParams.side : ℝ) ^ (-(4 * ((S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ)))) ∧
    (X₀ ≤ S.scaleCoupling → |κ - S.latticeCycleSumAt S.data.scaleLevel| ≤ (|CL| + |CT|) * S.scaleCoupling⁻¹) ∧
    |S.latticeCycleSumAt S.data.scaleLevel| ≤ |CL| + |CT| ∧
    |S.latticeCycleSumAt S.data.scaleLevel - S.cyclicLimit| ≤ (|CL| + |CT|) * (Λ.stepParams.side : ℝ) ^ (-(S.data.scaleLevel : ℝ)) := by
  have hL1 : 1 ≤ Λ.stepParams.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hL1' : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by exact_mod_cast hL1
  have hLpos : (0 : ℝ) < (Λ.stepParams.side : ℝ) := by linarith
  have hC0 : 0 ≤ |CL| + |CT| := by positivity
  obtain ⟨h1, h2⟩ := hCL S.data.fn Λ.stepParams.side S.data.scaleLevel hL1 S.supAdmissible.isSupTestFamily
  have h3 := hCT Λ.stepParams.side S.data S.supAdmissible
  have h3' : |κ - S.latticeCycleSumAt S.data.scaleLevel| ≤ CT * (Λ.stepParams.side : ℝ) ^ (-(4 * ((S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ)))) := by
    rw [hκ]; exact h3
  have h1' : |S.latticeCycleSumAt S.data.scaleLevel| ≤ CL := h1
  have h2' : |S.latticeCycleSumAt S.data.scaleLevel - S.cyclicLimit| ≤ CL * (Λ.stepParams.side : ℝ) ^ (-(S.data.scaleLevel : ℝ)) := h2
  have hsK : (S.data.scaleLevel : ℝ) ≤ (S.data.windowLevel : ℝ) := by exact_mod_cast S.supAdmissible.scaleLevel_le
  have hpow0 : 0 ≤ (Λ.stepParams.side : ℝ) ^ (-(4 * ((S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ)))) := (Real.rpow_pos_of_pos hLpos _).le
  have hpow1 : (Λ.stepParams.side : ℝ) ^ (-(4 * ((S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ)))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1' (by linarith)
  have hdiff : |κ - S.latticeCycleSumAt S.data.scaleLevel| ≤ (|CL| + |CT|) * (Λ.stepParams.side : ℝ) ^ (-(4 * ((S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ)))) := by
    refine h3'.trans (mul_le_mul_of_nonneg_right ?_ hpow0)
    have := le_abs_self CT
    have := abs_nonneg CL
    linarith
  have hgam : |S.latticeCycleSumAt S.data.scaleLevel| ≤ |CL| + |CT| := by
    have := le_abs_self CL
    have := abs_nonneg CT
    linarith
  refine ⟨?_, hdiff, ?_, hgam, ?_⟩
  · have h4 : |κ - S.latticeCycleSumAt S.data.scaleLevel| ≤ |CT| := by
      refine h3'.trans ?_
      calc CT * (Λ.stepParams.side : ℝ) ^ (-(4 * ((S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ))))
          ≤ |CT| * (Λ.stepParams.side : ℝ) ^ (-(4 * ((S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ)))) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hpow0
        _ ≤ |CT| * 1 := mul_le_mul_of_nonneg_left hpow1 (abs_nonneg _)
        _ = |CT| := mul_one _
    have h5 : |κ| ≤ |κ - S.latticeCycleSumAt S.data.scaleLevel| + |S.latticeCycleSumAt S.data.scaleLevel| := by
      simpa using abs_add_le (κ - S.latticeCycleSumAt S.data.scaleLevel) (S.latticeCycleSumAt S.data.scaleLevel)
    have := le_abs_self CL
    linarith
  · intro hX
    obtain ⟨hw1, hw2⟩ := hwin hX
    refine hdiff.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hL1' ?_) hw1
    have hN : (0 : ℝ) ≤ (S.logIndex : ℝ) := Nat.cast_nonneg _
    linarith
  · refine h2'.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hLpos _).le)
    have := le_abs_self CL
    have := abs_nonneg CT
    linarith
theorem freeCumulantValue_of_components (hB : baseCurvatureCumulantStatement)
    (hL : latticeCycleSumApproxStatement) (hT : torusCycleSumNearLatticeStatement)
    (hC : gaussianChainCoordinatesStatement) (hW : scaleWindowStatement) :
    freeCumulantValueStatement := by
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, H₁⟩ := hC a ha
  obtain ⟨L₂, rt₂, C₂, hrt₂, H₂⟩ := hW a ha
  refine ⟨max L₁ L₂, fun c => min (rt₁ c) (rt₂ c), max C₁ C₂, fun c => lt_min (hrt₁ c) (hrt₂ c), ?_⟩
  intro L hodd hLL Tb hTa hTL hD hCS hCH hrt hCder Kr hKr
  obtain ⟨y₁, Y₁⟩ := H₁ L hodd ((le_max_left _ _).trans hLL) Tb hTa hTL hD hCS hCH
    (hrt.trans (min_le_left _ _)) ((le_max_left _ _).trans hCder) Kr hKr
  obtain ⟨y₂, Y₂⟩ := H₂ L hodd ((le_max_right _ _).trans hLL) Tb hTa hTL hD hCS hCH
    (hrt.trans (min_le_right _ _)) ((le_max_right _ _).trans hCder) Kr hKr
  refine ⟨max y₁ y₂, ?_⟩
  intro y hy hRet hWil g hg hyg k _ hk2 hk8 R d hd
  obtain ⟨Ca, ca, Xa, -, -, Qa⟩ := Y₁ y ((le_max_left _ _).trans hy) hRet hWil g hg hyg k hk2 hk8 R d hd
  obtain ⟨Cb, cb, Xb, hcb, hyb, Qb⟩ := Y₂ y ((le_max_right _ _).trans hy) hRet hWil g hg hyg k hk2 hk8 R d hd
  by_cases hR0 : 0 ≤ R
  · obtain ⟨CL, hCL⟩ := hL k hk2 R d hR0 hd
    obtain ⟨CT, hCT⟩ := hT k hk2 R d hR0 hd
    refine ⟨fun _ => |CL| + |CT|, cb, Xb, hcb, hyb, ?_⟩
    intro S μ hμ
    have hcoord := ((Qa S S.data.windowLevel 0 rfl).2 μ hμ).1
    have hκ := hB _ _ S.data.windowLevel (S.data.period _) k hk2 (fun i => S.weight i _) μ hμ.isProbabilityMeasure hcoord
    have key := cumulant_bounds_at_point S CL CT hCL hCT Xb _ hκ (fun hX => by
      obtain ⟨w1, -, -, w4, w5, -⟩ := Qb S hX
      exact ⟨w1, w5.trans w4⟩)
    exact ⟨hκ, key.1, key.2.1, key.2.2.1, key.2.2.2.1, key.2.2.2.2⟩
  · refine ⟨fun _ => 0, cb, Xb, hcb, hyb, fun S => absurd (radius_nonneg_of_point S ⟨0, by show 0 < k; omega⟩) hR0⟩
end YangMills.Construction.MomentLaw
end
