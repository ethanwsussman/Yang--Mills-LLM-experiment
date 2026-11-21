import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdOrderAlongAField
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdOrderWithTwoFamilies
import Mathlib
import YangMills.Construction.SummableBoundsOfTheFlow.FieldOfTheTopInItsVariable
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.RestAlongAFieldHasItsSize
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.RimMomentsOfALaw
import YangMills.Construction.SummableBoundsOfTheFlow.ScoreOfAFieldHasItsSize
import YangMills.Construction.SummableBoundsOfTheFlow.SitesOfACellAreFew
import YangMills.Construction.SummableBoundsOfTheFlow.SizeFromSquareBoundsProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoToriProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlopesOfAFamilyLaw
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmallProof
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdDerivativeIsAMeanOverTheOrders
import YangMills.Construction.SummableBoundsOfTheFlow.TopDerivativesOfASmoothFunction
import YangMills.Construction.SummableBoundsOfTheFlow.WeightPartIsAdmittedProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames FamilyNorms Estimates BondIntegration TorusComparison
def expansionThirdDerivDecompAt (T : StepParameters) (Cz : ℕ → ℝ) : Prop :=
  ∀ (t : ℕ) (x s : ℝ) (φ h : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio h →
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → AreUnitVectors X →
    (∀ w X' : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X' (Th w X')) →
    ∃ (Ψ : StepVariable (finiteCells F) → ℝ)
      (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ)
      (z : Equiv.Perm (Fin 3) → ↥(chordBonds (finiteCells F)) → BondVector → BondVector)
      (Hs Rs : F.Site F.depth → Equiv.Perm (Fin 3) → StepVariable (finiteCells F) → ℝ),
      (∀ i, 2 ≤ F.extent i) ∧
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        Ψ η = familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V η) ∧
      IsUniformlyConvexDecaying T.ballRadius (x * T.chainParams.lam / 4) T.κ
        (fun b b' => (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ)) Ψ K ∧
      (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * T.chainParams.lam / 4) * ‖e‖) ∧
      (∀ π b, IsBoundedC1BondField (z π b) ∧
        (∀ v : BondVector, ‖v‖ < T.ballRadius → z π b v = imaginaryCoords
          (topVariationField Th s T.a T.chainParams.ρA (frameRadius x) (c (π 0)) (X (π 0)) b.1
            (toImaginary v) V)) ∧
        ContDiffOn ℝ 1 (fieldScore T.p Ψ b (z π b)) {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
        HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ Cz x T.κ
          (T.Cs * Real.sqrt x * Real.exp (-(2 ^ 6 * T.κ * bondDistToTopBond b (c (π 0)))))
          (fun b' => (cellSupDist (enclosingCell b'.1.1) (enclosingCell b.1.1) : ℝ))
          (fieldScore T.p Ψ b (z π b))) ∧
      ∀ y : F.Site F.depth,
        (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
          bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y η) V c X =
            (1 / 6) * ∑ π, ((∑ b, fieldDerivative b (z π b) (Hs y π) η) + Rs y π η)) ∧
        ∀ π, ContDiffOn ℝ 1 (Hs y π) {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
          ContDiffOn ℝ 1 (Rs y π) {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
          HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ Cz x T.κ
            (T.Cs * T.energyRatio * x ^ (-(1 / 2 : ℝ)) *
              Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) ![c (π 1), c (π 2)])))
            (bondDistToCell (enclosingCell y)) (Hs y π) ∧
          HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ Cz x T.κ
            (T.Cs * T.energyRatio * x ^ (-(1 / 2 : ℝ)) *
              Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) c)))
            (bondDistToCell (enclosingCell y)) (Rs y π)
def expansionThirdDerivDecompStatement : Prop :=
  ∃ Cz : StepParameters → ℕ → ℝ, (∀ U q, 0 ≤ Cz U q) ∧
    EventuallyInParameters fun T => expansionThirdDerivDecompAt T
      (Cz { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 })
end YangMills.Construction.Interpolation
end

set_option linter.unusedSectionVars false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open MeasureTheory ColdStepAtMirrorFrames Estimates BondIntegration IteratedDerivative
  TorusComparison FamilyNorms CellCounting SummableBounds ThirdDerivative
open BlockAverages hiding bondSpread
namespace Interpolation
namespace ExpansionThirdDeriv
section Laws
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
theorem radialWeightProd_eq_zero_of_not_mem {η : BondField ι} (hη : ¬ (∀ b, ‖η b‖ < ρ)) :
    radialWeightProd (cutoffFactor ρ p) η = 0 := by
  obtain ⟨c, hc⟩ := not_forall.1 hη
  refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
  unfold cutoffFactor
  rw [if_neg hc]
theorem ballDensity_eq_zero_of_not_mem {Φ : BondField ι → ℝ} {η : BondField ι} (hη : ¬ (∀ b, ‖η b‖ < ρ)) :
    ballDensity (cutoffFactor ρ p) Φ η = 0 := by apply _root_.YangMills.SharedProofs.p11780 <;> assumption
theorem ballDensity_congr {Φ₁ Φ₂ : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Φ₁ η = Φ₂ η) :
    ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂ := by
  funext η
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · unfold ballDensity
    rw [h η hη]
  · rw [ballDensity_eq_zero_of_not_mem hη, ballDensity_eq_zero_of_not_mem hη]
theorem ballExpectation_congr_density {Φ₁ Φ₂ : BondField ι → ℝ}
    (h : ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂) (f : BondField ι → ℝ) :
    ballExpectation (cutoffFactor ρ p) Φ₁ f = ballExpectation (cutoffFactor ρ p) Φ₂ f := by apply _root_.YangMills.SharedProofs.p53358 <;> assumption
theorem momentBound_of_ballDensity_eq {Φ₁ Φ₂ H : BondField ι → ℝ} {q : ℕ} {B : ℝ}
    (h : ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂)
    (hm : MomentBound (cutoffFactor ρ p) Φ₁ H q B) : MomentBound (cutoffFactor ρ p) Φ₂ H q B := by
  refine ⟨?_, ?_⟩
  · rw [← h]
    exact hm.1
  · rw [← ballExpectation_congr_density h]
    exact hm.2
theorem hasLocalSize_of_ballDensity_eq {Φ₁ Φ₂ H : BondField ι → ℝ} {Cq : ℕ → ℝ} {x κ a : ℝ} {dZ : ι → ℝ}
    (h : ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂)
    (hs : HasLocalSize ρ (cutoffFactor ρ p) Φ₁ Cq x κ a dZ H) : HasLocalSize ρ (cutoffFactor ρ p) Φ₂ Cq x κ a dZ H := by
  obtain ⟨h1, H₀, h2⟩ := hs
  exact ⟨h1, H₀, fun q hq => ⟨momentBound_of_ballDensity_eq h (h2 q hq).1,
    fun b => momentBound_of_ballDensity_eq h ((h2 q hq).2 b)⟩⟩
theorem momentBound_mono {r : ℝ → ℝ} {Φ H : BondField ι → ℝ} {q : ℕ} {a b : ℝ} (hab : |a| ≤ b)
    (h : MomentBound r Φ H q a) : MomentBound r Φ H q b := by
  refine ⟨h.1, h.2.trans ?_⟩
  calc a ^ q ≤ |a ^ q| := le_abs_self _
    _ = |a| ^ q := abs_pow _ _
    _ ≤ b ^ q := pow_le_pow_left₀ (abs_nonneg _) hab _
theorem hasLocalSize_mono {r : ℝ → ℝ} {Φ H : BondField ι → ℝ} {C₁ C₂ : ℕ → ℝ} {x κ h₁ h₂ : ℝ} {dZ : ι → ℝ} {ρ' : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h₁) (hhh : h₁ ≤ h₂) (hC : ∀ q, |C₁ q| ≤ C₂ q) (hs : HasLocalSize ρ' r Φ C₁ x κ h₁ dZ H) :
    HasLocalSize ρ' r Φ C₂ x κ h₂ dZ H := by
  obtain ⟨h1, H₀, h2⟩ := hs
  have hr : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  refine ⟨h1, H₀, fun q hq => ⟨momentBound_mono ?_ (h2 q hq).1, fun b => momentBound_mono ?_ ((h2 q hq).2 b)⟩⟩
  · rw [abs_mul, abs_of_nonneg hh]
    exact mul_le_mul (hC q) hhh hh ((abs_nonneg _).trans (hC q))
  · have hE := (Real.exp_pos (-(2 * κ * dZ b))).le
    have e : C₁ q * Real.sqrt x * h₁ * Real.exp (-(2 * κ * dZ b)) =
        C₁ q * (Real.sqrt x * h₁ * Real.exp (-(2 * κ * dZ b))) := by ring
    have e' : C₂ q * Real.sqrt x * h₂ * Real.exp (-(2 * κ * dZ b)) =
        C₂ q * (Real.sqrt x * h₂ * Real.exp (-(2 * κ * dZ b))) := by ring
    have h0 : 0 ≤ Real.sqrt x * h₁ * Real.exp (-(2 * κ * dZ b)) := mul_nonneg (mul_nonneg hr hh) hE
    rw [e, e', abs_mul, abs_of_nonneg h0]
    refine mul_le_mul (hC q) ?_ h0 ((abs_nonneg _).trans (hC q))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhh hr) hE
end Laws
section Extension
theorem exists_bounded_extension {g : BondVector → BondVector} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : ∀ v : BondVector, ‖v‖ < 2 * ρ → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) g v) :
    ∃ z : BondVector → BondVector, IsBoundedC1BondField z ∧ ∀ v : BondVector, ‖v‖ < ρ → z =ᶠ[𝓝 v] g := by
  let χ : ContDiffBump (0 : BondVector) := ⟨ρ, 3 * ρ / 2, hρ, by linarith⟩
  set z : BondVector → BondVector := fun v => χ v • g v with hz
  have hsupp : tsupport χ = Metric.closedBall (0 : BondVector) (3 * ρ / 2) := χ.tsupport_eq
  have hz2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) z := by
    refine contDiff_iff_contDiffAt.2 fun v => ?_
    by_cases hv : ‖v‖ < 2 * ρ
    · exact (χ.contDiff.contDiffAt).smul (hg v hv)
    · have hout : v ∉ tsupport χ := by
        rw [hsupp]
        simp only [Metric.mem_closedBall, dist_zero_right, not_le]
        linarith [not_lt.1 hv]
      have he : z =ᶠ[𝓝 v] fun _ => 0 := by
        have hO : (tsupport χ)ᶜ ∈ 𝓝 v := (isClosed_tsupport _).isOpen_compl.mem_nhds hout
        filter_upwards [hO] with w hw
        have : χ w = 0 := image_eq_zero_of_notMem_tsupport hw
        simp [hz, this]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hcs : HasCompactSupport z := by
    have h1 : HasCompactSupport (fun v => χ v) := χ.hasCompactSupport
    exact h1.smul_right
  have hb0 := hz2.continuous.bounded_above_of_compact_support hcs
  have hc1 : Continuous (fderiv ℝ z) := hz2.continuous_fderiv (by norm_num)
  have hb1 := hc1.bounded_above_of_compact_support (hcs.fderiv (𝕜 := ℝ))
  obtain ⟨C₀, h0⟩ := hb0
  obtain ⟨C₁, h1⟩ := hb1
  refine ⟨z, ⟨hz2.of_le (by norm_num), max C₀ C₁, fun v => (h0 v).trans (le_max_left _ _),
    fun v => (h1 v).trans (le_max_right _ _)⟩, fun v hv => ?_⟩
  have hO : IsOpen {w : BondVector | ‖w‖ < ρ} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hO.mem_nhds hv] with w hw
  have : χ w = 1 := χ.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt hw)
  simp [hz, this]
end Extension
section Cells
variable {F : BlockFrame}
theorem bondSpan_le_diameter {k : ℕ} {P : Finset F.Cell} {Y : F.Cell} {c : Fin k → F.Site F.top × Fin 4}
    (hY : Y ∈ P) (hc : ∀ l, (c l).1 ∈ P) : bondSpan Y c ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.bondSpan_le_cellSetDiameter <;> assumption
theorem diameter_le_two_mul (hD : SupDistCellComparison) {P : Finset F.Cell} {z : F.Cell} {n : ℕ}
    (h : ∀ u ∈ P, cellSupDist z u ≤ n) : cellSetDiameter P ≤ 2 * n := by
  have e : ∀ y w : F.Cell, siteSupDist y w = cellSupDist y w := fun _ _ => rfl
  have sym : ∀ u v : F.Cell, cellSupDist u v = cellSupDist v u := fun u v => by
    have := (hD.1 F F.top u v v).2.1
    simpa only [e] using this
  have tri : ∀ u v w : F.Cell, cellSupDist u w ≤ cellSupDist u v + cellSupDist v w := fun u v w => by
    have := (hD.1 F F.top u v w).2.2
    simpa only [e] using this
  change (P.sup fun u => P.sup fun v => cellSupDist u v) ≤ _
  refine Finset.sup_le fun u hu => Finset.sup_le fun v hv => ?_
  have a1 := h u hu
  have a2 := h v hv
  have a3 := tri u z v
  rw [sym u z] at a3
  omega
theorem exp_neg_listDist_le (hD : SupDistCellComparison) {κ κ₂ : ℝ} (hκ : 0 < κ) (hκ₂ : 2 ^ 9 * κ ≤ κ₂)
    {P : Finset F.Cell} {z : F.Cell} {n : ℕ} (h : ∀ u ∈ P, cellSupDist z u ≤ n) :
    Real.exp (-(κ₂ * n)) ≤ Real.exp (-(2 ^ 8 * κ * cellSetDiameter P)) := by
  refine Real.exp_le_exp.2 ?_
  have h1 : (cellSetDiameter P : ℝ) ≤ 2 * n := by exact_mod_cast diameter_le_two_mul hD h
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have a1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 ^ 8 * κ)
  have a2 := mul_le_mul_of_nonneg_right hκ₂ h0
  nlinarith
theorem cellSupDist_le_listDist_two (z : F.Cell) (c c' : F.Site F.top × Fin 4) :
    ∀ u ∈ ({z, c.1, c'.1} : Finset F.Cell), cellSupDist z u ≤
      bondListDistance z (Fin.cons c (fun _ : Fin 1 => c') : Fin 2 → F.Site F.top × Fin 4) := by
  intro u hu
  have hs : ∀ l : Fin 2, cellSupDist z ((Fin.cons c (fun _ : Fin 1 => c') : Fin 2 → F.Site F.top × Fin 4) l).1 ≤
      bondListDistance z (Fin.cons c (fun _ : Fin 1 => c') : Fin 2 → F.Site F.top × Fin 4) := fun l =>
    Finset.le_sup (f := fun l => cellSupDist z ((Fin.cons c (fun _ : Fin 1 => c') : Fin 2 → F.Site F.top × Fin 4) l).1) (Finset.mem_univ l)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · simp [cellSupDist]
  · simpa using hs 0
  · simpa using hs 1
theorem cellSupDist_le_listDist_three (z : F.Cell) (c : F.Site F.top × Fin 4) (c' : Fin 2 → F.Site F.top × Fin 4) :
    ∀ u ∈ ({z, c.1, (c' 0).1, (c' 1).1} : Finset F.Cell), cellSupDist z u ≤
      bondListDistance z (Fin.cons c c' : Fin 3 → F.Site F.top × Fin 4) := by
  intro u hu
  have hs : ∀ l : Fin 3, cellSupDist z ((Fin.cons c c' : Fin 3 → F.Site F.top × Fin 4) l).1 ≤
      bondListDistance z (Fin.cons c c' : Fin 3 → F.Site F.top × Fin 4) := fun l =>
    Finset.le_sup (f := fun l => cellSupDist z ((Fin.cons c c' : Fin 3 → F.Site F.top × Fin 4) l).1) (Finset.mem_univ l)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · simp [cellSupDist]
  · simpa using hs 0
  · simpa using hs (Fin.succ 0)
  · have := hs (Fin.succ 1)
    rw [Fin.cons_succ] at this
    exact this
end Cells
section Laws₂
variable {F : BlockFrame}
theorem extendByZero_id (ζ : StepVariable (finiteCells F)) :
    _root_.YangMills.Construction.Interpolation.extendByZero (id : ↥(chordBonds (finiteCells F)) → _) Finset.univ ζ = ζ := by apply _root_.YangMills.Construction.InterpolatedBirths.extendByZero_id <;> assumption
abbrev singleLaw (F : BlockFrame) (V : F.GaugeField F.top) (Ψ₀ : StepVariable (finiteCells F) → ℝ) :
    LawOnBondVariables ↥(chordBonds (finiteCells F)) := ⟨F, V, id, Finset.univ, Ψ₀⟩
theorem convexCombinationExponent_single (lam x : ℝ) (V : F.GaugeField F.top) (Ψ₀ : StepVariable (finiteCells F) → ℝ) :
    convexCombinationExponent lam x (fun _ : Fin 1 => (1 : ℝ)) (fun _ => singleLaw F V Ψ₀) = Ψ₀ := by
  funext ζ
  have h : (singleLaw F V Ψ₀).exponent lam x ζ = Ψ₀ ζ := by
    change Ψ₀ (_root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ ζ) + ∑ i ∈ Finset.univ \ Finset.univ, x * lam / 2 * ‖ζ i‖ ^ 2 = Ψ₀ ζ
    rw [extendByZero_id, Finset.sdiff_self]
    simp
  simp [convexCombinationExponent, h]
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem eventually_smallCurvature_bondSpread {k : ℕ} (hF : ∀ i, F.extent i ≠ 0) (s : ℝ) (V : F.GaugeField F.top)
    (hV : IsSmallCurvature s V) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.SharedProofs.p8866 <;> assumption
theorem contDiffAt_rotatedEval {ρ : ℝ} {V : F.GaugeField F.top} {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (hJ : JointlyContDiffOnBalls ρ V G) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0) :=
  ContDiffAt.comp (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
    (f := fun p : StepVariable (finiteCells F) × (Fin k → ℝ) => (p.2, p.1)) (η, 0) (hJ k c X η hη)
    (contDiff_snd.prodMk contDiff_fst).contDiffAt
theorem contDiffAt_slice {ρ : ℝ} {V : F.GaugeField F.top} {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (hJ : JointlyContDiffOnBalls ρ V G) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) 0 :=
  ContDiffAt.comp (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
    (f := fun τ : Fin k → ℝ => (τ, η)) 0 (hJ k c X η hη) (contDiff_id.prodMk contDiff_const).contDiffAt
theorem bondDeriv_three_eq_mean (hSym : ThirdDerivEqMeanOverOrders) (hMov : MovingFieldSecondDeriv)
    {ρ : ℝ} {V : F.GaugeField F.top} {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (Z : Equiv.Perm (Fin 3) → ↥(chordBonds (finiteCells F)) → F.GaugeField F.top → BondVector → BondVector)
    (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions) (η : StepVariable (finiteCells F))
    (hper : ∀ i, F.period F.top i ≠ 0)
    (hη : ∀ b, ‖η b‖ < ρ) (hopen : IsOpen {ζ : StepVariable (finiteCells F) | ∀ b, ‖ζ b‖ < ρ})
    (hJ : JointlyContDiffOnBalls ρ V G)
    (hZ : ∀ π b, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞)
      (fun r => Z π b (translateAlongPair V ![c (π 1), c (π 2)] ![X (π 1), X (π 2)] r) (η b)) 0)
    (hD : ∀ π : Equiv.Perm (Fin 3), ∀ᶠ r in 𝓝 (0 : Fin 2 → ℝ),
      bondDeriv (G η) (translateAlongPair V ![c (π 1), c (π 2)] ![X (π 1), X (π 2)] r) (fun _ : Fin 1 => c (π 0)) (fun _ => X (π 0)) =
        ∑ b, bondPartialDeriv (fun ζ => G ζ (translateAlongPair V ![c (π 1), c (π 2)] ![X (π 1), X (π 2)] r)) b η
          (Z π b (translateAlongPair V ![c (π 1), c (π 2)] ![X (π 1), X (π 2)] r) (η b))) :
    bondDeriv (G η) V c X = (1 / 6) * ∑ π : Equiv.Perm (Fin 3),
      ((∑ b, fieldDerivative b (Z π b V) (fun ζ => bondDeriv (G ζ) V ![c (π 1), c (π 2)] ![X (π 1), X (π 2)]) η) +
        movingFieldRemainder G (Z π) V ![c (π 1), c (π 2)] ![X (π 1), X (π 2)] η) := by
  have hηc : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
  rw [hSym F F.top (G η) V c X hper fun q c' X' => contDiffAt_slice hJ c' X' η hηc]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  refine hMov F V G (Z π) (fun W' => bondDeriv (G η) W' (fun _ : Fin 1 => c (π 0)) (fun _ => X (π 0))) _ _ η ?_ (hZ π) (hD π)
  filter_upwards [hopen.mem_nhds hη] with ζ hζ
  exact contDiffAt_rotatedEval hJ _ _ ζ fun b => (hζ b).le
end Laws₂
section Table
def ExpansionDerivBound (K : ℕ → ℝ) (r κ : ℝ) (L : ℕ) (C : ℝ) : Prop :=
  ∀ (F : BlockFrame) (n₀ m : ℕ) (σ s a ρA ρ : ℝ) (e : ℕ → ℝ) (f : LocalFamily)
    (V : F.GaugeField F.top) (y : F.Site F.depth),
    F.blockSide = L → IsLargeCubicTorus F → IsCubicTorusAbove L F.depth n₀ F → (∀ j, 0 ≤ e j) →
    HasBoundedDerivatives L F.depth n₀ σ (κ / 2 ^ 10) 3 e f →
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → IsSmallCurvature σ (interpolatedField s a ρA m V η)) →
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → ∀ x i, ¬ IsAxialTreeBond (x, i) →
      ‖interpolatedCoords s a ρA m V η x i‖ ≤ 1) →
    (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m d) V) →
    (∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4) (X' : Fin k' → imaginaryQuaternions),
      1 ≤ k' → AreUnitVectors X' →
      ‖bondDeriv (interpolatedFrame s a ρA m d) V c' X'‖ ≤
        K k' * Real.exp (-(r * bondListDistance (enclosingCell d.1) c'))) →
    JointlyContDiffOnBalls ρ V (fun ζ V' => interpolatedExpansion s a ρA m f y ζ V') ∧
    ∀ (η : StepVariable (finiteCells F)) (l k : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
      (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      (∀ b, ‖η b‖ ≤ ρ) → (∀ i, ‖u i‖ = 1) → AreUnitVectors X → 1 ≤ l + k → l + k ≤ 3 →
      |jointMixedDeriv (fun ζ V' => interpolatedExpansion s a ρA m f y ζ V') η V b u c X| ≤
        C * runningMax e (l + k) *
          Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert (enclosingCell y) (chordBondCells b ∪ topBondCells c))))
structure ExpansionParameterBounds (Cb : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ) (Wl : ℕ → ℝ → ℝ) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop where
  side_large : 2 ^ 40 ≤ T.L
  n₀_large : 64 ≤ T.n₀
  rate_le : 2 ^ 10 * T.κ ≤ T.chainParams.δ₂
  one_le_coupling : 1 ≤ T.coupling
  Ct_nonneg : 0 ≤ T.Ct
  σ_small : (T.Ct + 1) * T.σ ≤ 1 / 2
  slope_le : (Cb (rateParameters T) * T.E * Wl T.L T.κ) ^ 2 ≤ T.coupling
theorem eventually_expansionParameterBounds (Cb : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ) (Wl : ℕ → ℝ → ℝ) :
    EventuallyInParameters (ExpansionParameterBounds Cb Wl) := by
  intro a _
  refine ⟨2 ^ 40, fun L hL hL₀ c hc => ?_⟩
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨0, fun Ct hCt => ?_⟩
  refine ⟨c.δ₂ / 2 ^ 10, by positivity, fun κ hκ hκle => ?_⟩
  refine ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩
  refine ⟨0, fun nss _ => ?_⟩
  refine ⟨1 / (2 * (Ct + 1)), by positivity, fun σ hσ hσle p _ => ?_⟩
  refine ⟨0, fun Cs _ E _ => ?_⟩
  refine ⟨64, fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  refine ⟨max 1 ((Cb ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ * E * Wl L κ) ^ 2), fun y₁ hy₁ => ?_⟩
  refine ⟨hL₀, hn₀, ?_, (le_max_left _ _).trans hy₁, hCt, ?_, (le_max_right _ _).trans hy₁⟩
  · change 2 ^ 10 * κ ≤ c.δ₂
    have := mul_le_mul_of_nonneg_left hκle (by positivity : (0 : ℝ) ≤ 2 ^ 10)
    have e : (2 : ℝ) ^ 10 * (c.δ₂ / 2 ^ 10) = c.δ₂ := by ring
    linarith
  · change (Ct + 1) * σ ≤ 1 / 2
    have h1 : 0 < Ct + 1 := by linarith
    have := mul_le_mul_of_nonneg_left hσle h1.le
    have e : (Ct + 1) * (1 / (2 * (Ct + 1))) = 1 / 2 := by field_simp
    linarith
theorem runningMax_le_of_le_two {ε ε₃ : ℝ} (hε : 0 < ε) (n : ℕ) (hn : n ≤ 2) :
    runningMax (fun i => if i = 3 then ε₃ else ε) n ≤ ε := by
  obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  · simp [runningMax, hε.le]
  · simp [runningMax, hε.le]
  · simp [runningMax, hε.le]
theorem runningMax_le_of_le_three {ε ε₃ : ℝ} (hε : 0 < ε) (h3 : ε ≤ ε₃) (n : ℕ) (hn : n ≤ 3) :
    runningMax (fun i => if i = 3 then ε₃ else ε) n ≤ ε₃ := by
  obtain rfl | rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  · simp [runningMax, hε.le.trans h3]
  · simp [runningMax, hε.le, h3]
  · simp [runningMax, hε.le, h3]
  · simp [runningMax, hε.le, h3]
def TopVariationBound (M : ℝ) : Prop :=
  ∀ (F : BlockFrame) (s a ρA r CT : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions)
    (K : ℕ → ℝ) (b : F.Site F.depth × Fin 4) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (v : BondVector),
    (∀ i, F.period F.top i ≠ 0) → 0 ≤ r → (∀ k, 0 ≤ K k) → 0 ≤ CT →
    (∀ w : imaginaryQuaternions, ‖w‖ < Real.pi → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Th w) →
    (∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 3 → ‖iteratedFDeriv ℝ j Th w‖ ≤ CT) →
    IsBondAnalyticAt (interpolatedFrame s a ρA m b) V →
    (∀ (i : ℕ) (cs : Fin i → F.Site F.top × Fin 4) (Xs : Fin i → imaginaryQuaternions), 1 ≤ i → AreUnitVectors Xs →
      ‖bondDeriv (interpolatedFrame s a ρA m b) V cs Xs‖ ≤
        K i * Real.exp (-(r * bondListDistance (enclosingCell b.1) cs))) →
    ‖interpolatedFrame s a ρA m b V‖ + ‖v‖ < 1 → ‖X‖ = 1 →
    (∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions), k ≤ 2 → AreUnitVectors X' →
      ContDiffAt ℝ (k : WithTop ℕ∞)
        (fun τ : Fin k → ℝ => topVariationCoords Th s a ρA m c X b (leftTranslate (bondSpread c' X' τ) V) v) 0 ∧
      ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
        (fun v' => bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v') V c' X') v ∧
      ‖bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v) V c' X'‖ ≤ variationFieldConstant M CT K *
        Real.exp (-(r * bondListDistance (enclosingCell b.1) (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4))) ∧
      ‖fderiv ℝ (fun v' => bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v') V c' X') v‖ ≤
        variationFieldConstant M CT K *
          Real.exp (-(r * bondListDistance (enclosingCell b.1) (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4)))) ∧
    ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (topVariationCoords Th s a ρA m c X b V) v ∧
    ∀ e e' : BondVector, ‖fderiv ℝ (fun v' => fderiv ℝ (topVariationCoords Th s a ρA m c X b V) v' e') v e‖ ≤
      CT * Real.exp (-(r * cellSupDist (enclosingCell b.1) c.1)) * ‖e‖ * ‖e'‖
def FieldScoreBound (ρ : ℝ) (p : ℝ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (lam W W₀ : ℝ) (Cq : ℕ → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x κ C A u : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ) (b : ι)
    (w : ι → ℝ) (z : BondVector → BondVector),
    1 ≤ x → 0 ≤ κ → 0 ≤ A → 0 ≤ u → IsPseudoMetricOnBonds d → ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) Ψ →
    HasUniformlyConvexLaw ρ lam x κ C d Ψ → (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
    (∀ (j q N : ℕ) (b' : ι), 1 ≤ j → 1 ≤ q →
      Integrable (fun η => |iteratedDeriv j p ‖η b'‖| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) ∧
      ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b'‖| ^ q) ≤ Cr j q N * (x ^ N)⁻¹) →
    (∀ b', 0 ≤ w b') → ∑ b', w b' ≤ W₀ →
    (∀ (η : BondField ι) (e : BondVector), (∀ b, ‖η b‖ < ρ) →
      |bondPartialDeriv Ψ b η e| ≤ A * Real.sqrt x * (x * ∑ b', w b' * ‖η b'‖ ^ 2 + 1) * ‖e‖) →
    (∀ (η : BondField ι) (b' : ι) (e e' : BondVector), (∀ b, ‖η b‖ < ρ) →
      |secondDerivAlong Ψ η (bondVariation b e) (bondVariation b' e')| ≤
        A * x * Real.exp (-(2 * κ * d b' b)) * ‖e‖ * ‖e'‖) →
    (∀ v : BondVector, ‖v‖ < ρ → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) z v ∧ ‖z v‖ ≤ u ∧ ‖fderiv ℝ z v‖ ≤ u ∧
      ∀ e e' : BondVector, ‖fderiv ℝ (fun v' => fderiv ℝ z v' e') v e‖ ≤ u * ‖e‖ * ‖e'‖) →
    ContDiffOn ℝ 1 (fieldScore p Ψ b z) {η | ∀ b, ‖η b‖ < ρ} ∧
    HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ ((2 * A + 4) * Real.sqrt x * u) (fun b' => d b' b) (fieldScore p Ψ b z)
def CutoffMomentBound (ρ : ℝ) (p : ℝ → ℝ) (lam C W : ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ j q N : ℕ, 1 ≤ j → 1 ≤ q → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x κ : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ)
    (K : ι → ι → ℝ), 1 ≤ x → 0 ≤ κ → IsPseudoMetricOnBonds d → IsUniformlyConvexDecaying ρ (x * lam / 4) κ d Ψ K →
    (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
    (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ (b : ι) (e : BondVector),
      |bondPartialDeriv Ψ b η e| ≤ C * x * ‖e‖) →
    ∀ b : ι, Integrable (fun η => |iteratedDeriv j p ‖η b‖| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) ∧
      ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) ≤ Cr j q N * (x ^ N)⁻¹
end Table
section Core
variable {F : BlockFrame}
def topVariationFields (Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions) (s a ρA : ℝ)
    (m : ℕ) (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (π : Equiv.Perm (Fin 3)) (b : ↥(chordBonds (finiteCells F))) (V : F.GaugeField F.top) (v : BondVector) : BondVector :=
  topVariationCoords Th s a ρA m (c (π 0)) (X (π 0)) b.1 V v
theorem isOpen_ball_set (ρ : ℝ) : IsOpen {ζ : StepVariable (finiteCells F) | ∀ b, ‖ζ b‖ < ρ} := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.isOpen_bondBall <;> assumption
theorem isPseudoMetricOnBonds_cellSupDist (hD : SupDistCellComparison) :
    IsPseudoMetricOnBonds (fun b b' : ↥(chordBonds (finiteCells F)) =>
      (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ)) := by
  have eD : ∀ y w : F.Cell, siteSupDist y w = cellSupDist y w := fun _ _ => rfl
  refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
  · have := (hD.1 F F.top (enclosingCell b.1.1) (enclosingCell b.1.1) (enclosingCell b.1.1)).1
    rw [eD] at this
    simp [this]
  · have := (hD.1 F F.top (enclosingCell b.1.1) (enclosingCell b'.1.1) (enclosingCell b'.1.1)).2.1
    rw [eD, eD] at this
    exact_mod_cast this
  · have := (hD.1 F F.top (enclosingCell b.1.1) (enclosingCell b'.1.1) (enclosingCell b''.1.1)).2.2
    rw [eD, eD, eD] at this
    exact_mod_cast this
theorem card_bonds_in_cell_le {L : ℕ} (hLodd : Odd F.blockSide) (hs2 : ∀ i, 2 ≤ F.extent i) (hFL : F.blockSide = L)
    (hBd : cellBondsCardStatement) (z : F.Cell) :
    (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤ 4 * L ^ 4 + 1 := by
  have := hBd F hLodd hs2 z
  rw [hFL] at this
  exact this.trans (Nat.le_succ _)
theorem card_sites_in_cell_le {L : ℕ} (hLodd : Odd F.blockSide) (hs2 : ∀ i, 2 ≤ F.extent i) (hFL : F.blockSide = L)
    (hSi : SitesPerCellLePow) (z : F.Cell) :
    (Finset.univ.filter fun y : ↥(sitesOfCells (finiteCells F) F.depth) => enclosingCell y.1 = z).card ≤ 4 * L ^ 4 + 1 := by
  have := hSi F (finiteCells F) hLodd hs2 z
  rw [hFL] at this
  have h : ∀ n : ℕ, n ≤ 4 * n + 1 := fun n => by omega
  exact this.trans (h _)
theorem card_cells_eq_le {L : ℕ} (z : F.Cell) :
    (Finset.univ.filter fun Y : ↥(finiteCells F) => Y.1 = z).card ≤ 4 * L ^ 4 + 1 := by
  have : (Finset.univ.filter fun Y : ↥(finiteCells F) => Y.1 = z).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact Subtype.ext (ha.trans hb.symm)
  exact this.trans (Nat.le_add_left 1 _)
theorem exp_neg_mul_le_exp_neg_two_mul {κ : ℝ} (hκ : 0 < κ) (A n : ℝ) (hA : 2 ≤ A) (hn' : 0 ≤ n) :
    Real.exp (-(A * κ * n)) ≤ Real.exp (-(2 * κ * n)) :=
  Real.exp_le_exp.2 (by nlinarith [mul_nonneg hκ.le hn'])
theorem exp_weight_sums_le {κ W : ℝ} {L : ℕ} (hκ : 0 < κ) (hLodd : Odd F.blockSide) (hs2 : ∀ i, 2 ≤ F.extent i)
    (hFL : F.blockSide = L) (hBd : cellBondsCardStatement) (hSi : SitesPerCellLePow)
    (hWt : ∀ (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ 4 * L ^ 4 + 1) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(2 * κ * (cellSupDist (y b) z : ℝ))) ≤ W) :
    (∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W) ∧
    (∀ z : F.Cell, ∑ Y ∈ finiteCells F, Real.exp (-(2 ^ 5 * κ * (cellSupDist Y z : ℝ))) ≤ W) ∧
    (∀ z : F.Cell, ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell y) z : ℝ))) ≤ W) ∧
    (∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W) := by
  have hWb : ∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W :=
    hWt ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1) (card_bonds_in_cell_le hLodd hs2 hFL hBd)
  have hWs₀ : ∀ z : F.Cell, ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      Real.exp (-(2 * κ * (cellSupDist (enclosingCell y) z : ℝ))) ≤ W := fun z => by
    rw [← Finset.sum_coe_sort]
    exact hWt ↥(sitesOfCells (finiteCells F) F.depth) (fun y => enclosingCell y.1)
      (card_sites_in_cell_le hLodd hs2 hFL hSi) z
  have hWc₀ : ∀ z : F.Cell, ∑ Y ∈ finiteCells F, Real.exp (-(2 * κ * (cellSupDist Y z : ℝ))) ≤ W := fun z => by
    rw [← Finset.sum_coe_sort]
    exact hWt ↥(finiteCells F) (fun Y => Y.1) card_cells_eq_le z
  refine ⟨hWb, fun z => ?_, fun z => ?_, fun z => ?_⟩
  · refine le_trans (Finset.sum_le_sum fun Y _ => ?_) (hWc₀ z)
    exact exp_neg_mul_le_exp_neg_two_mul hκ _ _ (by norm_num) (Nat.cast_nonneg _)
  · refine le_trans (Finset.sum_le_sum fun Y _ => ?_) (hWs₀ z)
    exact exp_neg_mul_le_exp_neg_two_mul hκ _ _ (by norm_num) (Nat.cast_nonneg _)
  · refine le_trans (Finset.sum_le_sum fun Y _ => ?_) (hWb z)
    exact exp_neg_mul_le_exp_neg_two_mul hκ _ _ (by norm_num) (Nat.cast_nonneg _)
theorem bondDeriv_zero_order {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : F.GaugeField F.top → E)
    (V : F.GaugeField F.top) :
    bondDeriv g V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) = g V := by apply _root_.YangMills.SharedProofs.p27916 <;> assumption
theorem extension_bounds {z g : BondVector → BondVector} {ρ u : ℝ} (hE : ∀ v : BondVector, ‖v‖ < ρ → z =ᶠ[𝓝 v] g)
    (hg : ∀ v : BondVector, ‖v‖ < ρ → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) g v ∧ ‖g v‖ ≤ u ∧ ‖fderiv ℝ g v‖ ≤ u ∧
      ∀ e e' : BondVector, ‖fderiv ℝ (fun v' => fderiv ℝ g v' e') v e‖ ≤ u * ‖e‖ * ‖e'‖) (v : BondVector) (hv : ‖v‖ < ρ) :
    ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) z v ∧ ‖z v‖ ≤ u ∧ ‖fderiv ℝ z v‖ ≤ u ∧
      ∀ e e' : BondVector, ‖fderiv ℝ (fun v' => fderiv ℝ z v' e') v e‖ ≤ u * ‖e‖ * ‖e'‖ := by
  obtain ⟨h1, h2, h3, h4⟩ := hg v hv
  have hO : IsOpen {w : BondVector | ‖w‖ < ρ} := isOpen_lt continuous_norm continuous_const
  refine ⟨h1.congr_of_eventuallyEq (hE v hv), ?_, ?_, fun e e' => ?_⟩
  · rw [(hE v hv).self_of_nhds]
    exact h2
  · rw [(hE v hv).fderiv_eq]
    exact h3
  · have e₁ : (fun v' => fderiv ℝ z v' e') =ᶠ[𝓝 v] fun v' => fderiv ℝ g v' e' := by
      filter_upwards [hO.mem_nhds hv] with w hw
      rw [(hE w hw).fderiv_eq]
    rw [e₁.fderiv_eq]
    exact h4 e e'
theorem areUnitVectors_pair {X : Fin 3 → imaginaryQuaternions} (hX : AreUnitVectors X) (π : Equiv.Perm (Fin 3)) :
    AreUnitVectors ![X (π 1), X (π 2)] := by
  intro l
  fin_cases l
  · exact hX _
  · exact hX _
set_option maxHeartbeats 4000000 in
theorem expansionThirdDerivDecompAt_of_bounds (hMove : topVariationAlongField) (hSym : ThirdDerivEqMeanOverOrders)
    (hMov : MovingFieldSecondDeriv) (hRest : MovingFieldRemainderHasSize)
    (hSl : FamilyLawExponentSlopeBounds) (hTop : fieldDerivRegularityStatement)
    (hD : SupDistCellComparison) (hCov : BlocksCoverLowerLevel)
    (hBd : cellBondsCardStatement) (hSi : SitesPerCellLePow)
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {c Cb CT W Mf : ℝ} {Kc : ℕ → ℝ} {Dc : ℕ → ℕ → ℝ}
    {Th₀ : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions}
    {CqO Cz Csc : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hodd : Odd T.L) (hE : 1 ≤ T.E) (hη₃ : 0 < T.η₃) (hη₁ : T.η₃ ≤ 1) (hκ : 0 < T.κ) (hσ : 0 < T.σ)
    (hch : T.chainParams.Admissible T.a T.L) (hcut : IsCutoff (T.σ / 64) T.p) (hc1 : 1 ≤ c)
    (hN : ExpansionParameterBounds (fun _ => Cb) (fun _ _ => W) T)
    (hK0 : ∀ k, 0 < Kc k) (hCb0 : 0 ≤ Cb) (hCT : 0 ≤ CT) (hW0 : 0 ≤ W) (hMf0 : 0 ≤ Mf)
    (hRB : ExpansionDerivBound Kc T.chainParams.κ₂ T.κ T.L Cb) (hMf : TopVariationBound Mf)
    (hUniq : ∀ w X u : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X u → u = Th₀ w X)
    (hShift : ∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th₀ w X))
    (hThs : ∀ w : imaginaryQuaternions, ‖w‖ < Real.pi → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Th₀ w)
    (hThb : ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 3 → ‖iteratedFDeriv ℝ j Th₀ w‖ ≤ CT)
    (hWt : ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ 4 * T.L ^ 4 + 1) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(2 * T.κ * (cellSupDist (y b) z : ℝ))) ≤ W)
    (hRim : CutoffMomentBound T.ballRadius T.p T.chainParams.lam T.Ct W Cr)
    (hSc : FieldScoreBound T.ballRadius T.p Cr T.chainParams.lam W (W ^ 2) Csc)
    (hk : ∀ (x : ℝ) (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ) (η : StepVariable (finiteCells F)),
      T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
      (∀ b, ‖η b‖ ≤ T.ballRadius) →
      HasInterpolationKernels s T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x) Kc Dc V η)
    (he : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
      InterpolatedExponentBounds s T.a T.chainParams.ρA T.ballRadius x T.κ c (frameRadius x) V)
    (hn : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
      InterpolatedFrameSmall s T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ (frameRadius x) V)
    (hcv : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
      (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
      (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
        (frameRadius x) d) →
      HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct d (convexCombinationExponent T.chainParams.lam x w M))
    (hob : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
      (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
      (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
        (frameRadius x) d) →
      ∀ M₀ : LawOnBondVariables ι,
        M₀.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
          (frameRadius x) d →
        ObservableSizes T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.κ c T.decayRate T.η₃ T.L t T.n₀
          (frameRadius x) T.σ T.p CqO (convexCombinationExponent T.chainParams.lam x w M) M₀)
    (hpt : InterpolatedPartsSmoothAt T)
    (hCzO : ∀ q, |CqO q| ≤ Cz q)
    (hCzM : ∀ q, |lpMomentConstant T.chainParams.lam W W q| ≤ Cz q) (hCzS : ∀ q, |Csc q| ≤ Cz q)
    (hcs : c ≤ T.Cs) (hrs : (W + 1) * (6 * (Cb * variationFieldConstant Mf CT Kc)) * W ≤ T.Cs)
    (hss : (2 * slopeConstant c W + 4) * (variationFieldConstant Mf CT Kc + CT) ≤ T.Cs) :
    expansionThirdDerivDecompAt T Cz := by
  classical
  intro t x s φ h₀ F V c₃ X Th hx hs0 hs1 hφ hh hTF hV hX hTh
  have hρ : 0 < T.ballRadius := by
    have := hσ
    unfold StepParameters.ballRadius
    positivity
  have hρ' : T.ballRadius = T.σ / 64 := rfl
  have hcut' : IsCutoff T.ballRadius T.p := hcut
  have hcl := hch.classical.1
  have hρA : T.chainParams.ρA ≤ 1 := hcl.2.1
  have hlam : 0 < T.chainParams.lam := hch.positivity.2.2.1
  obtain ⟨hFL, hFt, n', hside, hn₀⟩ := id hTF
  have hn64 : 64 ≤ n' := hN.n₀_large.trans hn₀
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hsd : ∀ i, 0 < F.extent i := fun i => by have := hs2 i; omega
  have hsne : ∀ i, F.extent i ≠ 0 := fun i => (hsd i).ne'
  have hLodd : Odd F.blockSide := hFL ▸ hodd
  have hper : ∀ i, F.period F.top i ≠ 0 := by
    intro i
    have h2 : F.blockSide ≠ 0 := by have := hLodd.pos; omega
    simp [BlockFrame.period, hsne i]
  have hx1 : 1 ≤ x := hN.one_le_coupling.trans hx
  have hx0 : 0 < x := by linarith
  have hκ₂ : 2 ^ 9 * T.κ ≤ T.chainParams.κ₂ := by
    have h1 := hcl.2.2.2.2.1
    have h2 := hN.rate_le
    have h3 := hcl.2.2.2.1
    nlinarith
  have hr₂ : 0 ≤ T.chainParams.κ₂ := by nlinarith
  have hK : ∀ k, 0 ≤ Kc k := fun k => (hK0 k).le
  have hE0 : 0 < T.E := by linarith
  have hE₃ : T.E ≤ T.energyRatio := by
    change T.E ≤ T.E / T.η₃
    rw [le_div_iff₀ hη₃]
    nlinarith
  have hE₃0 : 0 ≤ T.energyRatio := by linarith
  have hcub : IsLargeCubicTorus F := ⟨n', hn64, hside⟩
  have hlow : IsCubicTorusAbove T.L F.depth T.n₀ F := by
    refine ⟨hFL, rfl, n', hside, ?_⟩
    have hLpos : 1 ≤ T.L := hodd.pos
    calc T.n₀ ≤ n' := hn₀
      _ ≤ n' * T.L := Nat.le_mul_of_pos_right _ hLpos
  have hsm := fun (V' : F.GaugeField F.top) (hV' : IsSmallCurvature (5 / 4 * T.σ) V') => hn t x hx F V' s hTF hV' hs0 hs1
  have hkr := fun (V' : F.GaugeField F.top) (η : StepVariable (finiteCells F)) (hV' : IsSmallCurvature (5 / 4 * T.σ) V')
      (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) => hk x t F V' s η hx hTF hV' hs0 hs1 hη
  have h0ball : ∀ b : ↥(chordBonds (finiteCells F)), ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.ballRadius := fun b => by
    simpa using hρ.le
  have hroom : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' → ∀ b ∈ chordBonds (finiteCells F),
      ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b V'‖ + T.ballRadius ≤ 1 := fun V' hV' b hb => by
    have := (hsm V' hV').norm_add_le b hb
    rw [hρ']
    linarith
  have hkV := hkr V 0 hV h0ball
  have hroom2 : ∀ b ∈ chordBonds (finiteCells F),
      ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b V‖ + 2 * T.ballRadius < 1 := by
    intro b hb
    have h1 := (hsm V hV).norm_le b hb
    have h2 := hN.σ_small
    rw [hρ']
    nlinarith
  have hcoldF : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' → ∀ η : StepVariable (finiteCells F),
      (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature T.σ (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V' η) := by
    intro V' hV' η hη pl hpl
    have := (hsm V' hV').small_curvature_nearby η (fun b => by rw [← hρ']; exact hη b) pl hpl
    linarith
  have habove : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) → ∀ x' i, ¬ IsAxialTreeBond (x', i) →
      ‖interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V η x' i‖ ≤ 1 := by
    intro η hη x' i ht
    have hchm : (x', i) ∈ chordBonds (finiteCells F) := by
      unfold chordBonds innerBonds
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨⟨hCov F hLodd hsd x', hCov F hLodd hsd _⟩, ht⟩
    have h1 := hroom V hV (x', i) hchm
    have e1 : stepCoordinates η x' i = toImaginary (η ⟨(x', i), hchm⟩) := by
      unfold stepCoordinates
      rw [dif_pos hchm]
    have h2 := hη ⟨(x', i), hchm⟩
    have h4 : interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V η x' i =
        interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (x', i) V + stepCoordinates η x' i := rfl
    rw [h4, e1]
    have h5 := norm_add_le (interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (x', i) V)
      (toImaginary (η ⟨(x', i), hchm⟩))
    have h6 : ‖toImaginary (η ⟨(x', i), hchm⟩)‖ = ‖η ⟨(x', i), hchm⟩‖ := norm_toImaginary _
    rw [h6] at h5
    linarith
  have standingConstraints : ∀ (ε ε₃ : ℝ) (f : LocalFamily) (y : F.Site F.depth), 0 < ε → ε ≤ ε₃ →
      IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε ε₃ f →
      JointlyContDiffOnBalls T.ballRadius V (fun ζ V' => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) f y ζ V') ∧
      ∀ (η : StepVariable (finiteCells F)) (l k : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
        (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions),
        (∀ b, ‖η b‖ ≤ T.ballRadius) → (∀ i, ‖u i‖ = 1) → AreUnitVectors X' → 1 ≤ l + k → l + k ≤ 3 →
        |jointMixedDeriv (fun ζ V' => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) f y ζ V') η V b u c' X'| ≤
          Cb * runningMax (fun i => if i = 3 then ε₃ else ε) (l + k) *
            Real.exp (-(2 ^ 7 * T.κ * cellSetDiameter (insert (enclosingCell y) (chordBondCells b ∪ topBondCells c')))) := by
    intro ε ε₃ f y hε h3 hfam
    have he0 : ∀ i, 0 ≤ (fun i => if i = 3 then ε₃ else ε) i := by
      intro i
      simp only
      split_ifs
      · linarith
      · exact hε.le
    have hfam' : IsNormBoundedLocalFamily T.L F.depth T.n₀ T.σ T.decayRate ε ε₃ f := by
      rw [hFt]
      exact hfam
    have hHas : HasBoundedDerivatives T.L F.depth T.n₀ T.σ (T.κ / 2 ^ 10) 3 (fun i => if i = 3 then ε₃ else ε) f :=
      ⟨fun F' hF' y' W' hW j' c' X' => by simpa using hfam'.smooth F' hF' y' W' hW j' c' X',
        hfam'.gauge_invariant, fun F' hF' y' W' j' c' X' hW h1 h3' hX' => hfam'.decay F' hF' y' W' j' c' X' hW h1 h3' hX'⟩
    exact hRB F T.n₀ (frameRadius x) T.σ s T.a T.chainParams.ρA T.ballRadius _ f V y hFL hcub hlow he0 hHas (hcoldF V hV)
      habove hkV.analytic hkV.frame_deriv
  set Fam : StepVariable (finiteCells F) → ℝ := familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V with hFam
  set d : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ := fun b b' =>
    (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ) with hdd
  have hM₀ : (singleLaw F V Fam).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
      T.L t T.n₀ (frameRadius x) d :=
    ⟨hTF, hV, IsIntermediateLaw.ofFamily s φ hs0 hs1 hφ, Function.injective_id, fun _ _ => rfl⟩
  have hw : IsConvexWeights (fun _ : Fin 1 => (1 : ℝ)) := ⟨fun _ => zero_le_one, by simp⟩
  have hconvF := hcv t x hx _ d 1 _ _ hw (fun _ => hM₀)
  rw [convexCombinationExponent_single] at hconvF
  obtain ⟨Ψ, K, ag, hconvex, hsl0, hsl⟩ := hconvF
  have hdens : ballDensity (cutoffFactor T.ballRadius T.p) Fam = ballDensity (cutoffFactor T.ballRadius T.p) Ψ :=
    ballDensity_congr fun η hη => (ag η hη).symm
  have hopen : IsOpen {ζ : StepVariable (finiteCells F) | ∀ b, ‖ζ b‖ < T.ballRadius} := isOpen_ball_set _
  have hd : IsPseudoMetricOnBonds d := isPseudoMetricOnBonds_cellSupDist hD
  obtain ⟨hWb, hWc, hWs, hWb₆⟩ := exp_weight_sums_le hκ hLodd hs2 hFL hBd hSi (hWt F)
  have hWd : ∀ b₀, ∑ b, Real.exp (-(2 * T.κ * d b b₀)) ≤ W := fun b₀ => hWb _
  have hlaw : HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct d Ψ :=
    ⟨Ψ, K, fun _ _ => rfl, hconvex, hsl0, hsl⟩
  have hFd := fun (π : Equiv.Perm (Fin 3)) (b : ↥(chordBonds (finiteCells F))) (v : BondVector)
      (hv : ‖v‖ < 2 * T.ballRadius) =>
    hMf F s T.a T.chainParams.ρA T.chainParams.κ₂ CT (frameRadius x) V Th₀ Kc b.1 (c₃ (π 0)) (X (π 0)) v hper hr₂ hK hCT
      hThs hThb (hkV.analytic b.1 b.2) (fun i cs Xs h1 hXs => hkV.frame_deriv b.1 b.2 i cs Xs h1 hXs)
      (by have := hroom2 b.1 b.2; linarith) (hX (π 0))
  have hExt := fun (π : Equiv.Perm (Fin 3)) (b : ↥(chordBonds (finiteCells F))) =>
    exists_bounded_extension (g := topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π b V) hρ
      (fun v hv => (hFd π b v hv).2.1)
  choose z hzF hzE using hExt
  have hρ2 : ∀ v : BondVector, ‖v‖ < T.ballRadius → ‖v‖ < 2 * T.ballRadius := fun v hv => by linarith
  have hzAgree : ∀ π b (v : BondVector), ‖v‖ < T.ballRadius → z π b v = _root_.YangMills.Construction.Interpolation.imaginaryCoords
      (topVariationField Th s T.a T.chainParams.ρA (frameRadius x) (c₃ (π 0)) (X (π 0)) b.1 (toImaginary v) V) := by
    intro π b v hv
    rw [(hzE π b v hv).self_of_nhds]
    simp only [topVariationFields, topVariationCoords, topVariationField]
    congr 2
    split_ifs with hcr
    · have h1 := hroom2 b.1 b.2
      have hn1 := norm_add_le (interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V) (toImaginary v)
      rw [norm_toImaginary] at hn1
      have hπ : ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V + toImaginary v‖ < Real.pi := by
        have := Real.pi_gt_three
        linarith
      exact (hUniq _ _ _ hπ (hTh _ _ hπ)).symm
    · rfl
  have hc0 : 0 ≤ c := by linarith
  have hCf0 : 0 ≤ variationFieldConstant Mf CT Kc := by
    unfold variationFieldConstant
    have a1 := hK 1
    have a2 := hK 2
    have a3 := hK 3
    positivity
  have hA0 : 0 ≤ slopeConstant c W := by
    unfold slopeConstant
    positivity
  have hq : (Cb * T.E * W) ^ 2 ≤ T.coupling := hN.slope_le
  have hsq : Cb * T.E * W ≤ Real.sqrt x := le_trans (le_abs_self _) (Real.abs_le_sqrt (hq.trans hx))
  have hrimB : ∀ (j q N : ℕ) (b' : ↥(chordBonds (finiteCells F))), 1 ≤ j → 1 ≤ q →
      Integrable (fun η => |iteratedDeriv j T.p ‖η b'‖| ^ q * ballDensity (cutoffFactor T.ballRadius T.p) Ψ η) ∧
      ballExpectation (cutoffFactor T.ballRadius T.p) Ψ (fun η => |iteratedDeriv j T.p ‖η b'‖| ^ q) ≤ Cr j q N * (x ^ N)⁻¹ :=
    fun j q N b' hj hq' => hRim j q N hj hq' _ x T.κ d Ψ K hx1 hκ.le hd hconvex hWd hsl0 hsl b'
  have rφ := fun y => standingConstraints T.E T.energyRatio φ y hE0 hE₃ hφ
  have rh := fun y => standingConstraints T.E T.energyRatio h₀ y hE0 hE₃ hh
  have slope := hSl F s T.a T.chainParams.ρA T.ballRadius x T.κ c Cb T.E W (frameRadius x) V φ hρ hx1 hκ hc0 hCb0
    hE0.le hW0 (he t x hx F V s hTF hV hs0 hs1) (hpt t x F V s hx hTF hV hs0 hs1) (fun y => (rφ y).1)
    (fun y η l b u hη hu h1 h2 => ((rφ y).2 η l 0 b u Fin.elim0 Fin.elim0 (fun b => (hη b).le) hu (fun l => l.elim0)
      (by omega) (by omega)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (runningMax_le_of_le_two hE0 _ (by omega)) hCb0) (Real.exp_pos _).le)) hWc hWs hWb₆ hsq
  have hscore : ∀ (π : Equiv.Perm (Fin 3)) (b : ↥(chordBonds (finiteCells F))),
      ContDiffOn ℝ 1 (fieldScore T.p Ψ b (z π b)) {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
      HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ Cz x T.κ
        (T.Cs * Real.sqrt x * Real.exp (-(2 ^ 6 * T.κ * bondDistToTopBond b (c₃ (π 0)))))
        (fun b' => (cellSupDist (enclosingCell b'.1.1) (enclosingCell b.1.1) : ℝ)) (fieldScore T.p Ψ b (z π b)) := by
    intro π b
    obtain ⟨w, hw0, hwsum, hP1, hP2⟩ := slope b
    have hP1' : ∀ (η : StepVariable (finiteCells F)) (e : BondVector), (∀ b, ‖η b‖ < T.ballRadius) →
        |bondPartialDeriv Ψ b η e| ≤ slopeConstant c W * Real.sqrt x * (x * ∑ b', w b' * ‖η b'‖ ^ 2 + 1) * ‖e‖ := by
      intro η e hη
      have e1 : Ψ =ᶠ[𝓝 η] Fam := by
        filter_upwards [hopen.mem_nhds hη] with ζ hζ
        exact ag ζ hζ
      unfold bondPartialDeriv
      rw [e1.fderiv_eq]
      exact hP1 η e hη
    have hP2' : ∀ (η : StepVariable (finiteCells F)) (b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
        (∀ b, ‖η b‖ < T.ballRadius) →
        |secondDerivAlong Ψ η (bondVariation b e) (bondVariation b' e')| ≤
          slopeConstant c W * x * Real.exp (-(2 * T.κ * d b' b)) * ‖e‖ * ‖e'‖ := by
      intro η b' e e' hη
      have e2 : (fun ζ => fderiv ℝ Ψ ζ (bondVariation b e)) =ᶠ[𝓝 η] fun ζ => fderiv ℝ Fam ζ (bondVariation b e) := by
        filter_upwards [hopen.mem_nhds hη] with ζ hζ
        have e1 : Ψ =ᶠ[𝓝 ζ] Fam := by
          filter_upwards [hopen.mem_nhds hζ] with ζ' hζ'
          exact ag ζ' hζ'
        rw [e1.fderiv_eq]
      unfold secondDerivAlong
      rw [e2.fderiv_eq]
      exact hP2 η b' e e' hη
    set E₂ : ℝ := Real.exp (-(T.chainParams.κ₂ * (cellSupDist (enclosingCell b.1.1) (c₃ (π 0)).1 : ℝ))) with hE₂
    have hE₂0 : 0 < E₂ := Real.exp_pos _
    have hu0 : 0 ≤ (variationFieldConstant Mf CT Kc + CT) * E₂ := by positivity
    have elist : (bondListDistance (enclosingCell b.1.1) (Fin.cons (c₃ (π 0)) (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) :
        Fin (0 + 1) → F.Site F.top × Fin 4) : ℕ) = cellSupDist (enclosingCell b.1.1) (c₃ (π 0)).1 := by
      simp [bondListDistance]
    have hfacts : ∀ v : BondVector, ‖v‖ < T.ballRadius →
        ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π b V) v ∧
        ‖topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π b V v‖ ≤
          (variationFieldConstant Mf CT Kc + CT) * E₂ ∧
        ‖fderiv ℝ (topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π b V) v‖ ≤
          (variationFieldConstant Mf CT Kc + CT) * E₂ ∧
        ∀ e e' : BondVector, ‖fderiv ℝ (fun v' => fderiv ℝ
          (topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π b V) v' e') v e‖ ≤
          (variationFieldConstant Mf CT Kc + CT) * E₂ * ‖e‖ * ‖e'‖ := by
      intro v hv
      obtain ⟨h0, h2, h3⟩ := hFd π b v (hρ2 v hv)
      obtain ⟨-, -, k1, k2⟩ := h0 0 Fin.elim0 Fin.elim0 (by omega) (fun l => l.elim0)
      have eg : (fun v' => bondDeriv (fun V' => topVariationCoords Th₀ s T.a T.chainParams.ρA (frameRadius x) (c₃ (π 0))
          (X (π 0)) b.1 V' v') V
          (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) =
          topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π b V := by
        funext v'
        exact bondDeriv_zero_order _ V
      rw [eg] at k2
      rw [bondDeriv_zero_order] at k1
      rw [elist] at k1 k2
      have hCT₂ : variationFieldConstant Mf CT Kc * E₂ ≤ (variationFieldConstant Mf CT Kc + CT) * E₂ :=
        mul_le_mul_of_nonneg_right (by linarith) hE₂0.le
      refine ⟨h2, k1.trans hCT₂, k2.trans hCT₂, fun e e' => (h3 e e').trans ?_⟩
      have : CT * E₂ ≤ (variationFieldConstant Mf CT Kc + CT) * E₂ := mul_le_mul_of_nonneg_right (by linarith) hE₂0.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (norm_nonneg _)) (norm_nonneg _)
    have r := hSc _ x T.κ T.Ct (slopeConstant c W) ((variationFieldConstant Mf CT Kc + CT) * E₂) d Ψ b w (z π b) hx1
      hκ.le hA0 hu0 hd hconvex.smooth hlaw hWd hrimB hw0 hwsum hP1' hP2' (extension_bounds (hzE π b) hfacts)
    refine ⟨r.1, hasLocalSize_mono hx0.le (by positivity) ?_ hCzS r.2⟩
    have hrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    have hE6 : E₂ ≤ Real.exp (-(2 ^ 6 * T.κ * bondDistToTopBond b (c₃ (π 0)))) := by
      refine Real.exp_le_exp.2 ?_
      have a0 : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1.1) (c₃ (π 0)).1 := Nat.cast_nonneg _
      have a1 := mul_le_mul_of_nonneg_right hκ₂ a0
      have e : bondDistToTopBond b (c₃ (π 0)) = (cellSupDist (enclosingCell b.1.1) (c₃ (π 0)).1 : ℝ) := rfl
      rw [e]
      nlinarith [mul_nonneg hκ.le a0]
    calc (2 * slopeConstant c W + 4) * Real.sqrt x * ((variationFieldConstant Mf CT Kc + CT) * E₂)
        = ((2 * slopeConstant c W + 4) * (variationFieldConstant Mf CT Kc + CT)) * (Real.sqrt x * E₂) := by ring
      _ ≤ T.Cs * (Real.sqrt x * Real.exp (-(2 ^ 6 * T.κ * bondDistToTopBond b (c₃ (π 0))))) :=
          mul_le_mul hss (mul_le_mul_of_nonneg_left hE6 hrt) (by positivity)
            ((mul_nonneg (by positivity) (by linarith)).trans hss)
      _ = _ := by ring
  have hlow' : IsCubicTorusAbove T.L t T.n₀ F := by
    rw [← hFt]
    exact hlow
  have hxh : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hrest : ∀ (y : F.Site F.depth) (π : Equiv.Perm (Fin 3)),
      ContDiffOn ℝ 1 (movingFieldRemainder (fun ζ V' => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y ζ V')
        (topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π) V ![c₃ (π 1), c₃ (π 2)] ![X (π 1), X (π 2)])
        {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
      HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ Cz x T.κ
        (T.Cs * T.energyRatio * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) c₃)))
        (bondDistToCell (enclosingCell y))
        (movingFieldRemainder (fun ζ V' => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y ζ V')
          (topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π) V ![c₃ (π 1), c₃ (π 2)]
          ![X (π 1), X (π 2)]) := by
    intro y π
    have hX' := areUnitVectors_pair hX π
    have r := hRest F T.ballRadius x T.chainParams.lam T.κ W T.Ct Cb (variationFieldConstant Mf CT Kc) T.energyRatio d Ψ T.p
      (fun ζ V' => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y ζ V')
      (topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π) V (enclosingCell y) (c₃ (π 0))
      ![c₃ (π 1), c₃ (π 2)]
      ![X (π 1), X (π 2)] hρ hx1 hlam hκ hW0 hCb0 hCf0 hE₃0 hcut' hd hlaw hWd (hWb _) hX'
      (fun η k c' X' hη _ => contDiffAt_rotatedEval (rh y).1 c' X' η fun b => (hη b).le)
      (fun η l k b e c' X' hη h1 h2 hu hX'' => ((rh y).2 η l k b e c' X' (fun b => (hη b).le) hu hX'' (by omega) h2).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (runningMax_le_of_le_three hE0 hE₃ _ h2) hCb0)
          (Real.exp_pos _).le))
      (fun b v l hv => by
        obtain ⟨h0, -, -⟩ := hFd π b v (hρ2 v hv)
        obtain ⟨-, k1, k2, k3⟩ := h0 1 (fun _ => ![c₃ (π 1), c₃ (π 2)] l) (fun _ => ![X (π 1), X (π 2)] l) (by omega)
          (fun _ => hX' l)
        have hb := mul_le_mul_of_nonneg_left (exp_neg_listDist_le hD hκ hκ₂
          (cellSupDist_le_listDist_two (enclosingCell b.1.1) (c₃ (π 0)) (![c₃ (π 1), c₃ (π 2)] l))) hCf0
        exact ⟨k1, k2.trans hb, k3.trans hb⟩)
      (fun b v hv => by
        obtain ⟨h0, -, -⟩ := hFd π b v (hρ2 v hv)
        obtain ⟨-, k1, k2, k3⟩ := h0 2 ![c₃ (π 1), c₃ (π 2)] ![X (π 1), X (π 2)] le_rfl hX'
        have hb := mul_le_mul_of_nonneg_left (exp_neg_listDist_le hD hκ hκ₂
          (cellSupDist_le_listDist_three (enclosingCell b.1.1) (c₃ (π 0)) ![c₃ (π 1), c₃ (π 2)])) hCf0
        exact ⟨k1, k2.trans hb, k3.trans hb⟩)
    refine ⟨r.1, hasLocalSize_mono hx0.le (by positivity) ?_ hCzM r.2⟩
    set Nc : Finset F.Cell := {enclosingCell y, (c₃ (π 0)).1, (![c₃ (π 1), c₃ (π 2)] 0).1,
      (![c₃ (π 1), c₃ (π 2)] 1).1} with hNc
    have hmem : ∀ l, (c₃ l).1 ∈ Nc := by
      intro l
      obtain ⟨i, rfl⟩ := π.surjective l
      fin_cases i <;> simp [hNc]
    have hsp : (bondSpan (enclosingCell y) c₃ : ℝ) ≤ cellSetDiameter Nc := by
      exact_mod_cast bondSpan_le_diameter (by simp [hNc]) hmem
    have hE4 : Real.exp (-(2 ^ 4 * T.κ * (cellSetDiameter Nc : ℝ))) ≤
        Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) c₃)) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hsp (by positivity : 0 ≤ 2 ^ 4 * T.κ)
      linarith
    have hE40 := Real.exp_pos (-(2 ^ 4 * T.κ * (cellSetDiameter Nc : ℝ)))
    calc (W + 1) * (6 * (Cb * T.energyRatio * variationFieldConstant Mf CT Kc) * W *
          Real.exp (-(2 ^ 4 * T.κ * (cellSetDiameter Nc : ℝ)))) * x ^ (-(1 / 2 : ℝ))
        = ((W + 1) * (6 * (Cb * variationFieldConstant Mf CT Kc)) * W) *
          (T.energyRatio * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 ^ 4 * T.κ * (cellSetDiameter Nc : ℝ)))) := by ring
      _ ≤ T.Cs * (T.energyRatio * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) c₃))) :=
          mul_le_mul hrs (mul_le_mul_of_nonneg_left hE4 (by positivity)) (by positivity)
            ((by positivity : 0 ≤ (W + 1) * (6 * (Cb * variationFieldConstant Mf CT Kc)) * W).trans hrs)
      _ = _ := by ring
  have hobs : ∀ (y : F.Site F.depth) (π : Equiv.Perm (Fin 3)),
      HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ Cz x T.κ
        (T.Cs * T.energyRatio * x ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) ![c₃ (π 1), c₃ (π 2)])))
        (bondDistToCell (enclosingCell y))
        (fun ζ => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y ζ) V ![c₃ (π 1), c₃ (π 2)]
          ![X (π 1), X (π 2)]) := by
    intro y π
    have key := (hob t x hx _ d 1 _ _ hw (fun _ => hM₀) (singleLaw F V Fam) hM₀).expansion_deriv s T.E h₀ y 2
      ![c₃ (π 1), c₃ (π 2)] ![X (π 1), X (π 2)] hs0 hs1 hE0 hh (by norm_num) (areUnitVectors_pair hX π)
    rw [convexCombinationExponent_single] at key
    have e1 : (fun ζ : StepVariable (finiteCells F) => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x)
        h₀ y (_root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ ζ)) V ![c₃ (π 1), c₃ (π 2)] ![X (π 1), X (π 2)]) =
        fun ζ => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y ζ) V ![c₃ (π 1), c₃ (π 2)]
          ![X (π 1), X (π 2)] := by
      funext ζ
      rw [extendByZero_id]
    have hcancelled' : HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Fam CqO x T.κ
        (c * T.energyRatio * x ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) ![c₃ (π 1), c₃ (π 2)])))
        (bondDistToCell (enclosingCell y))
        (fun ζ => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y ζ) V ![c₃ (π 1), c₃ (π 2)]
          ![X (π 1), X (π 2)]) := by
      rw [← e1]
      exact key
    refine hasLocalSize_mono hx0.le (by positivity) ?_ hCzO (hasLocalSize_of_ballDensity_eq hdens hcancelled')
    have hpos : 0 ≤ x ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) ![c₃ (π 1), c₃ (π 2)])) := by positivity
    have h1 : c * T.energyRatio ≤ T.Cs * T.energyRatio := mul_le_mul_of_nonneg_right hcs hE₃0
    calc _ = c * T.energyRatio * (x ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) ![c₃ (π 1), c₃ (π 2)]))) := by ring
      _ ≤ T.Cs * T.energyRatio * (x ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) ![c₃ (π 1), c₃ (π 2)]))) :=
          mul_le_mul_of_nonneg_right h1 hpos
      _ = _ := by ring
  refine ⟨Ψ, K, z, fun y π ζ => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y ζ) V
      ![c₃ (π 1), c₃ (π 2)] ![X (π 1), X (π 2)],
    fun y π => movingFieldRemainder (fun ζ V' => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y ζ V')
      (topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π) V ![c₃ (π 1), c₃ (π 2)] ![X (π 1), X (π 2)],
    hs2, ag, hconvex, hsl0, fun π b => ⟨hzF π b, hzAgree π b, (hscore π b).1, (hscore π b).2⟩,
    fun y => ⟨fun η hη => ?_, fun π => ⟨(hTop F T.ballRadius V).contDiffOn _ 2 _ _ (rh y).1 le_rfl, (hrest y π).1,
      hobs y π, (hrest y π).2⟩⟩⟩
  have hηc : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
  have hDq : ∀ π : Equiv.Perm (Fin 3), ∀ᶠ r in 𝓝 (0 : Fin 2 → ℝ),
      bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y η)
        (translateAlongPair V ![c₃ (π 1), c₃ (π 2)] ![X (π 1), X (π 2)] r) (fun _ : Fin 1 => c₃ (π 0)) (fun _ => X (π 0)) =
        ∑ b, bondPartialDeriv (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y ζ
          (translateAlongPair V ![c₃ (π 1), c₃ (π 2)] ![X (π 1), X (π 2)] r)) b η
          (topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X π b
            (translateAlongPair V ![c₃ (π 1), c₃ (π 2)] ![X (π 1), X (π 2)] r) (η b)) := by
    intro π
    filter_upwards [eventually_smallCurvature_bondSpread hsne _ V hV ![c₃ (π 1), c₃ (π 2)] ![X (π 1), X (π 2)]]
      with r hr
    exact hMove F s T.a T.chainParams.ρA T.ballRadius (frameRadius x) _ (fun w X' => Th₀ w X') hLodd hs2 hρ hShift
      (hkr _ 0 hr h0ball).analytic (hroom _ hr) (subtractTrivial h₀ F y) η (c₃ (π 0)) (X (π 0)) hη
      (fun k c' X' => ((hh.smooth F hlow' y _ (hcoldF _ hr η hηc)) k c' X').sub contDiffAt_const)
  have h3 := bondDeriv_three_eq_mean hSym hMov
    (G := fun ζ V' => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h₀ y ζ V')
    (topVariationFields Th₀ s T.a T.chainParams.ρA (frameRadius x) c₃ X) c₃ X η hper hη hopen (rh y).1
    (fun π b => ((hFd π b (η b) (hρ2 _ (hη b))).1 2 _ _ le_rfl (areUnitVectors_pair hX π)).1) hDq
  refine h3.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold fieldDerivative
  rw [(hzE π b (η b) (hη b)).self_of_nhds]
end Core
end ExpansionThirdDeriv
open ExpansionThirdDeriv in
set_option maxHeartbeats 1600000 in
theorem expansionThirdDerivDecompStatement_holds (hJ : joinAtLoweredSmallnessConstantStatement)
    (hJoin : EventuallyInParametersCombines)
    (hKern : interpolationKernelBoundsStatement) (hEB : interpolatedExponentBoundsStatement)
    (hNear : interpolatedFramesControlled) (hConv : mixturesOfIntermediateLawsConvex)
    (hObs : observableSizesStatement) (hParts : interpolatedPartsSmoothStatement)
    (hMove : topVariationAlongField) (hField : TopVariationCoordsSmooth)
    (hRS : rightTranslationSmooth) (hSym : ThirdDerivEqMeanOverOrders)
    (hMov : MovingFieldSecondDeriv) (hRest : MovingFieldRemainderHasSize)
    (hScore : fieldScoreSizeStatement) (hSl : FamilyLawExponentSlopeBounds)
    (hRim : cutoffDerivMomentsStatement) (hRow : expansionAboveFrameStatement)
    (hTop : fieldDerivRegularityStatement) (hS : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded)
    (hD : SupDistCellComparison) (hCov : BlocksCoverLowerLevel)
    (hBd : cellBondsCardStatement) (hSi : SitesPerCellLePow) :
    expansionThirdDerivDecompStatement := by
  classical
  obtain ⟨K, Dk, hKp, -, hKt⟩ := hKern
  obtain ⟨CqO, hObsT⟩ := hObs
  obtain ⟨Mf, hMf0, hMf⟩ := hField
  obtain ⟨Th₀, CT, hCT, hUniq, hShift, hThs, hThb⟩ := hRS
  have hWe : ∀ (N : ℕ) (κ : ℝ), ∃ Wv : ℝ, 0 ≤ Wv ∧ (0 < κ → ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) ≤ Wv) := by
    intro N κ
    by_cases h : 0 < κ
    · obtain ⟨Wv, h1, h2⟩ := hS N κ h
      exact ⟨Wv, h1, fun _ => h2⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' h⟩
  choose Wf hWf0 hWf using hWe
  set Wl : ℕ → ℝ → ℝ := fun L κ => Wf (4 * L ^ 4 + 1) (2 * κ) with hWl
  have hWl0 : ∀ L κ, 0 ≤ Wl L κ := fun L κ => hWf0 _ _
  have hCbE : ∀ U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters, ∃ C : ℝ, 0 ≤ C ∧ (0 < U.κ → 2 ^ 9 * U.κ ≤ U.chainParams.κ₂ → Odd U.L → 2 ^ 40 ≤ U.L →
      ExpansionDerivBound (K U) U.chainParams.κ₂ U.κ U.L C) := by
    intro U
    by_cases h : 0 < U.κ ∧ 2 ^ 9 * U.κ ≤ U.chainParams.κ₂ ∧ Odd U.L ∧ 2 ^ 40 ≤ U.L
    · obtain ⟨C, hC, hB⟩ := hRow (K U) U.chainParams.κ₂ U.κ U.L (fun k => (hKp U k).le) h.1 h.2.1 h.2.2.1 h.2.2.2
      exact ⟨C, hC.le, fun _ _ _ _ => hB⟩
    · exact ⟨0, le_rfl, fun a b c d => absurd ⟨a, b, c, d⟩ h⟩
  choose Cb0 hCb00 hCbB using hCbE
  have hCrE : ∀ (U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (j q N : ℕ), ∃ Cr : ℝ, (0 < U.ballRadius → IsCutoff U.ballRadius U.p →
      0 < U.chainParams.lam → 0 ≤ U.Ct → 1 ≤ j → 1 ≤ q →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x κ : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ)
        (K' : ι → ι → ℝ), 1 ≤ x → 0 ≤ κ → IsPseudoMetricOnBonds d →
        IsUniformlyConvexDecaying U.ballRadius (x * U.chainParams.lam / 4) κ d Ψ K' →
        (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ Wl U.L U.κ) →
        (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * U.chainParams.lam / 4) * ‖e‖) →
        (∀ η : BondField ι, (∀ b, ‖η b‖ < U.ballRadius) → ∀ (b : ι) (e : BondVector),
          |bondPartialDeriv Ψ b η e| ≤ U.Ct * x * ‖e‖) →
        ∀ b : ι, Integrable (fun η => |iteratedDeriv j U.p ‖η b‖| ^ q *
            ballDensity (cutoffFactor U.ballRadius U.p) Ψ η) ∧
          ballExpectation (cutoffFactor U.ballRadius U.p) Ψ (fun η => |iteratedDeriv j U.p ‖η b‖| ^ q) ≤
            Cr * (x ^ N)⁻¹) := by
    intro U j q N
    by_cases h : 0 < U.ballRadius ∧ IsCutoff U.ballRadius U.p ∧ 0 < U.chainParams.lam ∧ 0 ≤ U.Ct ∧ 1 ≤ j ∧ 1 ≤ q
    · obtain ⟨Cr, -, hs⟩ := hRim U.ballRadius U.p U.chainParams.lam U.Ct (Wl U.L U.κ) h.1 h.2.1 h.2.2.1 h.2.2.2.1
        (hWl0 _ _) j q N h.2.2.2.2.1 h.2.2.2.2.2
      exact ⟨Cr, fun _ _ _ _ _ _ => hs⟩
    · exact ⟨0, fun a b c d e f => absurd ⟨a, b, c, d, e, f⟩ h⟩
  choose Crf hCrf using hCrE
  have hScE : ∀ U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters, ∃ Cq : ℕ → ℝ, (0 < U.ballRadius → IsCutoff U.ballRadius U.p → 0 < U.chainParams.lam →
      FieldScoreBound U.ballRadius U.p (Crf U) U.chainParams.lam (Wl U.L U.κ) (Wl U.L U.κ ^ 2) Cq) := by
    intro U
    by_cases h : 0 < U.ballRadius ∧ IsCutoff U.ballRadius U.p ∧ 0 < U.chainParams.lam
    · obtain ⟨Cq, -, hs⟩ := hScore U.ballRadius U.p (Crf U) U.chainParams.lam (Wl U.L U.κ) (Wl U.L U.κ ^ 2) h.1 h.2.1
        h.2.2 (hWl0 _ _) (sq_nonneg _)
      exact ⟨Cq, fun _ _ _ => hs⟩
    · exact ⟨fun _ => 0, fun a b c => absurd ⟨a, b, c⟩ h⟩
  choose Csf hCsf using hScE
  set Cz : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun U q => |CqO U q| +
    |lpMomentConstant U.chainParams.lam (Wl U.L U.κ) (Wl U.L U.κ) q| + |Csf U q| with hCz
  set Cf : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => variationFieldConstant Mf CT (K (rateParameters U)) with hCf
  set G : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ → ℝ := fun U c => c +
    (Wl U.L U.κ + 1) * (6 * (Cb0 (rateParameters U) * Cf U)) * Wl U.L U.κ +
    (2 * slopeConstant c (Wl U.L U.κ) + 4) * (Cf U + CT) with hG
  refine ⟨Cz, fun U q => by simp only [hCz]; positivity, ?_⟩
  have hP := hJoin.1 _ _ (hJoin.1 _ _ (hJoin.1 _ _ (hJoin.1 _ _ (hJoin.1 _ _ hKt hEB) hNear) hConv) hObsT) hParts
  refine hJ _ (ExpansionParameterBounds (fun U => Cb0 U) Wl) _ G hP (eventually_expansionParameterBounds _ _) ?_
  intro T c hc1 hodd hn1 hy1 hE hη₃ hη₁ hκ hσ hch hcut hGle hP' hN'
  obtain ⟨⟨⟨⟨⟨hk, he⟩, hnr⟩, hcv⟩, hob⟩, hpt⟩ := hP'
  have hρ : 0 < T.ballRadius := by
    have := hσ
    unfold StepParameters.ballRadius
    positivity
  have hlam : 0 < T.chainParams.lam := hch.positivity.2.2.1
  have hcl := hch.classical.1
  have hκ₂ : 2 ^ 9 * T.κ ≤ T.chainParams.κ₂ := by
    have h1 := hcl.2.2.2.2.1
    have h2 : 2 ^ 10 * T.κ ≤ T.chainParams.δ₂ := hN'.rate_le
    have h3 := hcl.2.2.2.1
    nlinarith
  have hCt0 : 0 ≤ T.Ct := hN'.Ct_nonneg
  have hN : ExpansionParameterBounds (fun _ => Cb0 (rateParameters T)) (fun _ _ => Wl T.L T.κ) T :=
    ⟨hN'.side_large, hN'.n₀_large, hN'.rate_le, hN'.one_le_coupling, hN'.Ct_nonneg, hN'.σ_small, hN'.slope_le⟩
  have hRB := hCbB (rateParameters T) hκ hκ₂ hodd hN'.side_large
  have hc0 : 0 ≤ c := by linarith
  have hCf0 : 0 ≤ Cf T := by
    simp only [hCf]
    unfold variationFieldConstant
    have a1 := (hKp (rateParameters T) 1).le
    have a2 := (hKp (rateParameters T) 2).le
    have a3 := (hKp (rateParameters T) 3).le
    positivity
  have hW0 := hWl0 T.L T.κ
  have hCb := hCb00 (rateParameters T)
  have hAs : 0 ≤ slopeConstant c (Wl T.L T.κ) := by
    unfold slopeConstant
    positivity
  have g1 : 0 ≤ (Wl T.L T.κ + 1) * (6 * (Cb0 (rateParameters T) * Cf T)) * Wl T.L T.κ := by positivity
  have g2 : 0 ≤ (2 * slopeConstant c (Wl T.L T.κ) + 4) * (Cf T + CT) := by positivity
  have hGle' : c + (Wl T.L T.κ + 1) * (6 * (Cb0 (rateParameters T) * Cf T)) * Wl T.L T.κ +
      (2 * slopeConstant c (Wl T.L T.κ) + 4) * (Cf T + CT) ≤ T.Cs := hGle
  refine expansionThirdDerivDecompAt_of_bounds (Kc := K (rateParameters T)) (Dc := Dk (rateParameters T)) (Th₀ := Th₀)
    (Mf := Mf) (CT := CT)
    (W := Wl T.L T.κ) (Cb := Cb0 (rateParameters T)) (c := c)
    (CqO := CqO { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 })
    (Csc := Csf { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 })
    (Cr := Crf { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 })
    hMove hSym hMov hRest hSl hTop hD hCov hBd hSi hodd hE hη₃ hη₁ hκ hσ hch hcut hc1 hN
    (fun k => hKp _ k) hCb hCT hW0 hMf0 hRB hMf hUniq hShift hThs hThb
    (fun F ι _ y hy z => hWf _ _ (by positivity) F ι y hy z)
    (fun j q N hj hq => hCrf { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } j q N hρ hcut hlam hCt0 hj hq)
    (hCsf { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } hρ hcut hlam) hk he
    (fun t x hx F V s h1 h2 h3 h4 => ((hnr t x hx).single F V s h1 h2 h3 h4).2) hcv hob hpt
    (fun q => ?_) (fun q => ?_) (fun q => ?_) (by linarith) (by linarith) (by linarith)
  · simp only [hCz]
    have a := abs_nonneg (lpMomentConstant T.chainParams.lam (Wl T.L T.κ) (Wl T.L T.κ) q)
    have b := abs_nonneg (Csf { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } q)
    linarith
  · simp only [hCz]
    have a := abs_nonneg (CqO { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } q)
    have b := abs_nonneg (Csf { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } q)
    linarith
  · simp only [hCz]
    have a := abs_nonneg (CqO { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } q)
    have b := abs_nonneg (lpMomentConstant T.chainParams.lam (Wl T.L T.κ) (Wl T.L T.κ) q)
    linarith
end Interpolation
end YangMills.Construction
end
