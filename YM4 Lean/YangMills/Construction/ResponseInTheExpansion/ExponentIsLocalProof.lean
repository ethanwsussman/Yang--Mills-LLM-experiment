import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfTheMeanProof
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesAcrossTwoVariables
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.SizeOfASumOfObservables
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import YangMills.Construction.SummableBoundsOfTheFlow.ParametersMatchAtRaisedConstants
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open MeasureTheory ColdStepAtMirrorFrames Interpolation WeightedResponses FamilyNorms
  ConvexObservables Calculus
open BlockAverages hiding bondSpread
namespace ResponseInTheExpansion
namespace ExponentLocality
variable {F : BlockFrame}
theorem exp_cell_weight_le {κ s d D : ℝ} (hκ : 0 ≤ κ) (hs : 0 ≤ s) (hD : D ≤ s) (hd : d ≤ s) :
    Real.exp (-(2 ^ 5 * κ * s)) * Real.exp (2 * κ * d) ≤
      Real.exp (-(2 ^ 3 * κ * D)) * Real.exp (-(6 * κ * d)) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg hκ (sub_nonneg.2 hD), mul_nonneg hκ (sub_nonneg.2 hd), mul_nonneg hκ hs]
theorem exp_site_weight_le {κ s d D : ℝ} (hκ : 0 ≤ κ) (hD : D ≤ s) (hd : d ≤ s) :
    Real.exp (-(2 ^ 4 * κ * s)) * Real.exp (2 * κ * d) ≤
      Real.exp (-(2 ^ 3 * κ * D)) * Real.exp (-(6 * κ * d)) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg hκ (sub_nonneg.2 hD), mul_nonneg hκ (sub_nonneg.2 hd)]
theorem bondListDiameter_le_bondSpan {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) :
    _root_.YangMills.Construction.BlockAverages.bondListDiameter c ≤ bondSpan Y c := le_max_right _ _
theorem cellSupDist_le_bondSpan {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) (l : Fin k) :
    cellSupDist Y (c l).1 ≤ bondSpan Y c := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.siteSupDist_le_bondSpan <;> assumption
theorem hasLocalSize_bondDeriv_exponent (hS : FiniteSumSizeBound)
    (hLaw : normalizedBallLawIsProbabilityStatement)
    (hEnds : interpolationAtEndpoints) (hTwo : IteratedFDerivParamDiff)
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hρ : 0 < T.ballRadius) (hcut : IsCutoff T.ballRadius T.p) (hκ : 0 < T.κ)
    (hη : 0 < T.η₃) (hη1 : T.η₃ ≤ 1)
    (hE : 1 ≤ T.E) (hCs : 0 < T.Cs) {Cz : ℕ → ℝ} {t : ℕ} {x : ℝ} {f : LocalFamily}
    {V : F.GaugeField F.top} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (l₀ : Fin k) (hx : 0 < x)
    (hfam : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f)
    (hsz : ObservableSizes T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.κ T.Cs T.decayRate T.η₃ T.L t T.n₀
      (frameRadius x) T.σ T.p Cz ((coldHalfLawAt T x f).exponent V)
      (lawAtTop V ((coldHalfLawAt T x f).exponent V)))
    (hconv : HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct (chordBondDist F)
      ((coldHalfLawAt T x f).exponent V))
    (hXc : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (hR : CentredExpansionBounds false T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L
      (frameRadius x) f V)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hfin : Finite F.Cell) (hk : k ≤ 2) (hX : AreUnitVectors X)
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d) {W : ℝ}
    (hWY : ∑ Y ∈ finiteCells F, Real.exp (-(6 * T.κ * cellSupDist Y (c l₀).1)) ≤ W)
    (hWy : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      Real.exp (-(6 * T.κ * cellSupDist (enclosingCell y) (c l₀).1)) ≤ W) :
    ContDiffOn ℝ 1 (fun η => bondDeriv (fun V' => (coldHalfLawAt T x f).exponent V' η) V c X)
        {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} ∧
      (coldHalfLawAt T x f).HasSize (fun q => |Cz q| + 1) V
      ((T.Cs * W + T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * W) *
        Real.exp (-(2 ^ 3 * T.κ * _root_.YangMills.Construction.BlockAverages.bondListDiameter c))) (c l₀).1
      fun η => bondDeriv (fun V' => (coldHalfLawAt T x f).exponent V' η) V c X := by
  classical
  set Q := coldHalfLawAt T x f with hQ
  set Sv := StepVariable (finiteCells F) with hSv
  set m := frameRadius x with hm
  set Z : F.Cell := (c l₀).1 with hZ
  set D : ℝ := (_root_.YangMills.Construction.BlockAverages.bondListDiameter c : ℝ) with hD
  obtain ⟨Ψ', K', hΨ', hconvex, -, -⟩ := hconv
  have hΨc : Continuous Ψ' := hconvex.smooth.continuous
  obtain ⟨-, -, -, -, -, -, -, -, -, hnz, -⟩ := hLaw _ T.ballRadius T.p Ψ' hρ hcut hΨc
  have hdens : ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' := by
    funext η
    by_cases hη' : ∀ b, ‖η b‖ < T.ballRadius
    · unfold ballDensity
      rw [hΨ' η hη']
    · have h0 : ballDensity (cutoffFactor T.ballRadius T.p) Ψ' η = 0 := by
        by_contra hne
        exact hη' ((hnz η).1 hne)
      have h1 : radialWeightProd (cutoffFactor T.ballRadius T.p) η = 0 := by
        unfold ballDensity at h0
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      rw [h0]
      unfold ballDensity
      rw [h1, zero_mul]
  have hbe : ∀ (V' : F.GaugeField F.top) (Y : F.Cell) (η : Sv),
      interpolatedBlockExponent 1 T.a T.chainParams.ρA x m Y V' η =
        cellExponent false T.a T.chainParams.ρA x m Y V' η := fun V' Y η => by
    have := (hEnds F false T.a T.chainParams.ρA T.chainParams.lam x 0 m V').2.2.2.2.1 Y η
    simpa [segmentEnd] using this
  have hrb : ∀ (V' : F.GaugeField F.top) (y : F.Site F.depth) (η : Sv),
      interpolatedExpansion 1 T.a T.chainParams.ρA m f y η V' = centredExpansion false T.a T.chainParams.ρA m f y η V' :=
    fun V' y η => by
    have := (hEnds F false T.a T.chainParams.ρA T.chainParams.lam x 0 m V').2.2.2.1 f y η
    simpa [segmentEnd] using this
  have hfe : ∀ (V' : F.GaugeField F.top) (η : Sv), Q.exponent V' η =
      stepExponent false T.a T.chainParams.ρA x m f 1 V' η := fun V' η => by
    have := (hEnds F false T.a T.chainParams.ρA T.chainParams.lam x 0 m V').2.2.2.2.2.1 f η
    exact show familyLawExponent 1 T.a T.chainParams.ρA x m f V' η =
        stepExponent false T.a T.chainParams.ρA x m f 1 V' η from by
      simpa [segmentEnd] using this
  have hsplit : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' → ∀ η : Sv,
      (∀ b, ‖η b‖ < T.ballRadius) →
      Q.exponent V' η = ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x m Y V' η -
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false T.a T.chainParams.ρA m f y η V' :=
    fun V' hV' η hη => by
    rw [hfe, ← (hXc V' hV').sum_eq η hη]
    simp [stepExponent]
  let Hb : F.Cell → Sv → ℝ := fun Y ζ =>
    bondDeriv (fun V' => cellExponent false T.a T.chainParams.ρA x m Y V' ζ) V c X
  let Hr : F.Site F.depth → Sv → ℝ := fun y ζ =>
    bondDeriv (fun V' => centredExpansion false T.a T.chainParams.ρA m f y ζ V') V c X
  let sb : F.Cell → ℝ := fun Y => (bondSpan Y c : ℝ)
  let hb : F.Cell → ℝ := fun Y => T.Cs * Real.exp (-(2 ^ 5 * T.κ * sb Y))
  let hr : F.Site F.depth → ℝ := fun y =>
    T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * Real.exp (-(2 ^ 4 * T.κ * sb (enclosingCell y)))
  have hE₃ : T.E ≤ T.energyRatio := by
    have : T.energyRatio = T.E / T.η₃ := rfl
    rw [this, le_div_iff₀ hη]
    nlinarith
  have hE₃0 : 0 < T.energyRatio := by linarith
  have hCq1 : ∀ q, |Cz q| ≤ |Cz q| + 1 := fun q => by linarith
  have sizeb : ∀ Y, HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ' (fun q => |Cz q| + 1) x T.κ
      (hb Y) (fun b : ↥(chordBonds (finiteCells F)) => (cellSupDist (enclosingCell b.1.1) Y : ℝ)) (Hb Y) :=
    fun Y => by
    have h1 : HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) (Q.exponent V) Cz x T.κ
        (T.Cs * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)))
        (embeddedCellDist id Y) (fun ζ => bondDeriv (fun V' => interpolatedBlockExponent 1 T.a T.chainParams.ρA x m Y V'
          (extendByZero id Finset.univ ζ)) V c X) :=
      hsz.exponent_deriv 1 Y k c X zero_le_one le_rfl (by omega) hX
    simp only [extendByZero_id, hbe] at h1
    exact hasLocalSize_mono hCq1 (by positivity) le_rfl (hasLocalSize_congr_density hdens h1)
  have sizer : ∀ y, HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ' (fun q => |Cz q| + 1) x T.κ
      (hr y) (fun b : ↥(chordBonds (finiteCells F)) =>
        (cellSupDist (enclosingCell b.1.1) (enclosingCell y) : ℝ)) (Hr y) := fun y => by
    have h1 : HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) (Q.exponent V) Cz x T.κ
        (T.Cs * (if k = 2 then T.E / T.η₃ else T.E) * x ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(2 ^ 4 * T.κ * bondSpan (enclosingCell y) c)))
        (embeddedCellDist id (enclosingCell y)) (fun ζ => bondDeriv (interpolatedExpansion 1 T.a T.chainParams.ρA m f y
          (extendByZero id Finset.univ ζ)) V c X) :=
      hsz.expansion_deriv 1 T.E f y k c X zero_le_one le_rfl (by linarith) hfam hk hX
    simp only [extendByZero_id] at h1
    have e : (fun ζ : Sv => bondDeriv (interpolatedExpansion 1 T.a T.chainParams.ρA m f y ζ) V c X) = Hr y := by
      funext ζ
      have : interpolatedExpansion 1 T.a T.chainParams.ρA m f y ζ =
          fun V' => centredExpansion false T.a T.chainParams.ρA m f y ζ V' := by
        funext V'
        exact hrb V' y ζ
      simp only [Hr, this]
    rw [e] at h1
    have hif : (if k = 2 then T.E / T.η₃ else T.E) ≤ T.energyRatio := by
      split_ifs
      · exact le_rfl
      · exact hE₃
    refine hasLocalSize_mono hCq1 (by positivity) ?_ (hasLocalSize_congr_density hdens h1)
    have h2 := Real.exp_pos (-(2 ^ 4 * T.κ * (bondSpan (enclosingCell y) c : ℝ)))
    simp only [hr, sb]
    gcongr
  have hO : IsOpen {η : Sv | ∀ b, ‖η b‖ < T.ballRadius} := by
    have : {η : Sv | ∀ b, ‖η b‖ < T.ballRadius} = ⋂ b, {η : Sv | ‖η b‖ < T.ballRadius} := by
      ext η; simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have hcb : ∀ Y, ContDiffOn ℝ 1 (Hb Y) {η : Sv | ∀ b, ‖η b‖ < T.ballRadius} := fun Y η hη => by
    have hs := (hXc V hV).smooth Y η k c X (fun b => (hη b).le)
    have h1 := (hTwo (Fin k → ℝ) Sv k (fun q => cellExponent false T.a T.chainParams.ρA x m Y
      (leftTranslate (bondSpread c X q.1) V) q.2) η (fun l => Pi.single l 1)
      (hs.of_le (by exact_mod_cast (by omega : k + 1 ≤ 3)))).1
    exact (show ContDiffAt ℝ 1 (Hb Y) η from h1).contDiffWithinAt
  have hcr : ∀ y, ContDiffOn ℝ 1 (Hr y) {η : Sv | ∀ b, ‖η b‖ < T.ballRadius} := fun y η hη => by
    have hs := hR.smooth y η k c X (fun b => (hη b).le)
    have h1 := (hTwo (Fin k → ℝ) Sv k (fun q => centredExpansion false T.a T.chainParams.ρA m f y q.2
      (leftTranslate (bondSpread c X q.1) V)) η (fun l => Pi.single l 1)
      (hs.of_le (by exact_mod_cast (by omega : k + 1 ≤ 3)))).1
    exact (show ContDiffAt ℝ 1 (Hr y) η from h1).contDiffWithinAt
  have hκ0 := hκ.le
  have hDs : ∀ Y : F.Cell, D ≤ sb Y := fun Y => Nat.cast_le.2 (bondListDiameter_le_bondSpan Y c)
  have hds : ∀ Y : F.Cell, (cellSupDist Y Z : ℝ) ≤ sb Y := fun Y => Nat.cast_le.2 (cellSupDist_le_bondSpan Y c l₀)
  have hs0 : ∀ Y : F.Cell, 0 ≤ sb Y := fun Y => Nat.cast_nonneg _
  have hbB : ∀ Y : F.Cell, hb Y * Real.exp (2 * T.κ * cellSupDist Y Z) ≤
      T.Cs * Real.exp (-(2 ^ 3 * T.κ * D)) * Real.exp (-(6 * T.κ * cellSupDist Y Z)) := fun Y => by
    have := exp_cell_weight_le hκ0 (hs0 Y) (hDs Y) (hds Y)
    calc hb Y * Real.exp (2 * T.κ * cellSupDist Y Z) =
          T.Cs * (Real.exp (-(2 ^ 5 * T.κ * sb Y)) * Real.exp (2 * T.κ * cellSupDist Y Z)) := by
          simp only [hb]; ring
      _ ≤ T.Cs * (Real.exp (-(2 ^ 3 * T.κ * D)) * Real.exp (-(6 * T.κ * cellSupDist Y Z))) :=
          mul_le_mul_of_nonneg_left this hCs.le
      _ = _ := by ring
  have hrB : ∀ y : F.Site F.depth, hr y * Real.exp (2 * T.κ * cellSupDist (enclosingCell y) Z) ≤
      T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * Real.exp (-(2 ^ 3 * T.κ * D)) *
        Real.exp (-(6 * T.κ * cellSupDist (enclosingCell y) Z)) := fun y => by
    have := exp_site_weight_le hκ0 (hDs (enclosingCell y)) (hds (enclosingCell y))
    calc hr y * Real.exp (2 * T.κ * cellSupDist (enclosingCell y) Z) =
          T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) *
          (Real.exp (-(2 ^ 4 * T.κ * sb (enclosingCell y))) *
            Real.exp (2 * T.κ * cellSupDist (enclosingCell y) Z)) := by
          simp only [hr]; ring
      _ ≤ T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * (Real.exp (-(2 ^ 3 * T.κ * D)) *
          Real.exp (-(6 * T.κ * cellSupDist (enclosingCell y) Z))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  set B : ℝ := (T.Cs * W + T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * W) * Real.exp (-(2 ^ 3 * T.κ * D))
    with hB
  have hsumY : ∑ Y ∈ finiteCells F, hb Y * Real.exp (2 * T.κ * cellSupDist Y Z) ≤
      T.Cs * W * Real.exp (-(2 ^ 3 * T.κ * D)) := by
    calc _ ≤ ∑ Y ∈ finiteCells F, T.Cs * Real.exp (-(2 ^ 3 * T.κ * D)) *
            Real.exp (-(6 * T.κ * cellSupDist Y Z)) :=
          Finset.sum_le_sum fun Y _ => hbB Y
      _ = T.Cs * Real.exp (-(2 ^ 3 * T.κ * D)) *
            ∑ Y ∈ finiteCells F, Real.exp (-(6 * T.κ * cellSupDist Y Z)) := by
          rw [Finset.mul_sum]
      _ ≤ T.Cs * Real.exp (-(2 ^ 3 * T.κ * D)) * W := mul_le_mul_of_nonneg_left hWY (by positivity)
      _ = _ := by ring
  have hsumy : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      hr y * Real.exp (2 * T.κ * cellSupDist (enclosingCell y) Z) ≤
      T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * W * Real.exp (-(2 ^ 3 * T.κ * D)) := by
    calc _ ≤ ∑ y ∈ sitesOfCells (finiteCells F) F.depth, T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) *
            Real.exp (-(2 ^ 3 * T.κ * D)) * Real.exp (-(6 * T.κ * cellSupDist (enclosingCell y) Z)) :=
          Finset.sum_le_sum fun y _ => hrB y
      _ = T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * Real.exp (-(2 ^ 3 * T.κ * D)) *
            ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
              Real.exp (-(6 * T.κ * cellSupDist (enclosingCell y) Z)) := by
          rw [Finset.mul_sum]
      _ ≤ T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * Real.exp (-(2 ^ 3 * T.κ * D)) * W :=
          mul_le_mul_of_nonneg_left hWy (by positivity)
      _ = _ := by ring
  let H : F.Cell ⊕ F.Site F.depth → Sv → ℝ := Sum.elim Hb fun y ζ => - Hr y ζ
  let h : F.Cell ⊕ F.Site F.depth → ℝ := Sum.elim hb hr
  let dZ : F.Cell ⊕ F.Site F.depth → ↥(chordBonds (finiteCells F)) → ℝ :=
    Sum.elim (fun Y b => (cellSupDist (enclosingCell b.1.1) Y : ℝ)) fun y b =>
      (cellSupDist (enclosingCell b.1.1) (enclosingCell y) : ℝ)
  let S : Finset (F.Cell ⊕ F.Site F.depth) := (finiteCells F).disjSum (sitesOfCells (finiteCells F) F.depth)
  have hall := hS _ (F.Cell ⊕ F.Site F.depth) S T.ballRadius x T.κ B T.p Ψ' (fun q => |Cz q| + 1) H h dZ
    (fun b => (cellSupDist (enclosingCell b.1.1) Z : ℝ)) hρ hcut hΨc hx (fun q => by positivity)
    (fun j => by
      rcases j with Y | y
      · simp only [h, Sum.elim_inl, hb]; positivity
      · simp only [h, Sum.elim_inr, hr]; positivity)
    (fun j => by
      rcases j with Y | y
      · exact hcb Y
      · exact (hcr y).neg)
    (fun j _ => by
      rcases j with Y | y
      · exact sizeb Y
      · exact hasLocalSize_neg (sizer y))
    (by
      rw [Finset.sum_disjSum]
      simp only [h, Sum.elim_inl, Sum.elim_inr]
      have a1 : ∑ Y ∈ finiteCells F, hb Y ≤
          ∑ Y ∈ finiteCells F, hb Y * Real.exp (2 * T.κ * cellSupDist Y Z) :=
        Finset.sum_le_sum fun Y _ => le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
      have a2 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth, hr y ≤
          ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
            hr y * Real.exp (2 * T.κ * cellSupDist (enclosingCell y) Z) :=
        Finset.sum_le_sum fun y _ => le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
      refine (add_le_add a1 a2).trans ((add_le_add hsumY hsumy).trans (le_of_eq ?_))
      rw [hB]; ring)
    (fun b => by
      rw [Finset.sum_disjSum]
      simp only [h, dZ, Sum.elim_inl, Sum.elim_inr]
      have tri : ∀ Y' : F.Cell, Real.exp (-(2 * T.κ * cellSupDist (enclosingCell b.1.1) Y')) ≤
          Real.exp (2 * T.κ * cellSupDist Y' Z) *
            Real.exp (-(2 * T.κ * cellSupDist (enclosingCell b.1.1) Z)) := fun Y' => by
        rw [← Real.exp_add, Real.exp_le_exp]
        have := htri (enclosingCell b.1.1) Y' Z
        have h' : (cellSupDist (enclosingCell b.1.1) Z : ℝ) ≤
            cellSupDist (enclosingCell b.1.1) Y' + cellSupDist Y' Z := by
          exact_mod_cast this
        nlinarith
      have a1 : ∑ Y ∈ finiteCells F, hb Y * Real.exp (-(2 * T.κ * cellSupDist (enclosingCell b.1.1) Y)) ≤
          (∑ Y ∈ finiteCells F, hb Y * Real.exp (2 * T.κ * cellSupDist Y Z)) *
            Real.exp (-(2 * T.κ * cellSupDist (enclosingCell b.1.1) Z)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun Y _ => ?_
        rw [mul_assoc (hb Y)]
        exact mul_le_mul_of_nonneg_left (tri Y) (by simp only [hb]; positivity)
      have a2 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
            hr y * Real.exp (-(2 * T.κ * cellSupDist (enclosingCell b.1.1) (enclosingCell y))) ≤
          (∑ y ∈ sitesOfCells (finiteCells F) F.depth,
            hr y * Real.exp (2 * T.κ * cellSupDist (enclosingCell y) Z)) *
            Real.exp (-(2 * T.κ * cellSupDist (enclosingCell b.1.1) Z)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun y _ => ?_
        rw [mul_assoc (hr y)]
        exact mul_le_mul_of_nonneg_left (tri _) (by simp only [hr]; positivity)
      have e0 := Real.exp_pos (-(2 * T.κ * cellSupDist (enclosingCell b.1.1) Z))
      have : B = T.Cs * W * Real.exp (-(2 ^ 3 * T.κ * D)) +
          T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * W * Real.exp (-(2 ^ 3 * T.κ * D)) := by rw [hB]; ring
      rw [this, add_mul]
      exact add_le_add (a1.trans (mul_le_mul_of_nonneg_right hsumY e0.le))
        (a2.trans (mul_le_mul_of_nonneg_right hsumy e0.le)))
  have hall' := hasLocalSize_congr_density hdens.symm hall
  have hz : ∀ η : BondField ↥(chordBonds (finiteCells F)), ¬ (∀ b, ‖η b‖ < T.ballRadius) →
      ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent V) η = 0 := fun η hη => by
    rw [hdens]
    by_contra hne
    exact hη ((hnz η).1 hne)
  have heqf : ∀ η : Sv, (∀ b, ‖η b‖ < T.ballRadius) → ∑ j ∈ S, H j η =
      bondDeriv (fun V' => Q.exponent V' η) V c X := ?heq
  refine ⟨?_, hasLocalSize_congr_of_eqOn_balls hO hz heqf hall'⟩
  · have hc' : ContDiffOn ℝ 1 (fun η => ∑ j ∈ S, H j η) {η : Sv | ∀ b, ‖η b‖ < T.ballRadius} :=
      ContDiffOn.sum fun j _ => by
        rcases j with Y | y
        · exact hcb Y
        · exact (hcr y).neg
    exact hc'.congr fun η hη => (heqf η hη).symm
  case heq =>
  intro η hη
  rw [Finset.sum_disjSum]
  simp only [H, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
  symm
  have hev : (fun τ : Fin k → ℝ => Q.exponent (leftTranslate (bondSpread c X τ) V) η) =ᶠ[𝓝 0]
      fun τ => ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x m Y
          (leftTranslate (bondSpread c X τ) V) η -
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
          centredExpansion false T.a T.chainParams.ρA m f y η (leftTranslate (bondSpread c X τ) V) := by
    filter_upwards [eventually_isSmallCurvature_leftTranslate hfin c X hV] with τ hτ
    exact hsplit _ hτ η hη
  have hline : ∀ {G : (Fin k → ℝ) × Sv → ℝ}, ContDiffAt ℝ 3 G (0, η) →
      ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (τ, η)) 0 := fun {G} hG => by
    have h1 : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => G (τ, η)) 0 :=
      ContDiffAt.comp (g := G) (f := fun τ : Fin k → ℝ => (τ, η)) 0 hG
        ((contDiff_id.prodMk contDiff_const).contDiffAt)
    exact h1.of_le (by exact_mod_cast (by omega : k ≤ 3))
  have sY : ∀ Y ∈ finiteCells F, ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      cellExponent false T.a T.chainParams.ρA x m Y (leftTranslate (bondSpread c X τ) V) η) 0 := fun Y _ =>
    hline ((hXc V hV).smooth Y η k c X fun b => (hη b).le)
  have sy : ∀ y ∈ sitesOfCells (finiteCells F) F.depth, ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      centredExpansion false T.a T.chainParams.ρA m f y η (leftTranslate (bondSpread c X τ) V)) 0 := fun y _ =>
    hline (hR.smooth y η k c X fun b => (hη b).le)
  have e1 := (Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds
  have hA : ContDiffAt ℝ k (fun τ : Fin k → ℝ => ∑ Y ∈ finiteCells F,
      cellExponent false T.a T.chainParams.ρA x m Y (leftTranslate (bondSpread c X τ) V) η) 0 := ContDiffAt.sum sY
  have hBd : ContDiffAt ℝ k (fun τ : Fin k → ℝ => ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      centredExpansion false T.a T.chainParams.ρA m f y η (leftTranslate (bondSpread c X τ) V)) 0 := ContDiffAt.sum sy
  show iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => Q.exponent (leftTranslate (bondSpread c X τ) V) η) 0
      (fun l => Pi.single l 1) = _
  rw [e1]
  have e2 := iteratedFDeriv_sub_apply (i := k) hA hBd
  have e3 : (fun τ : Fin k → ℝ => ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x m Y
      (leftTranslate (bondSpread c X τ) V) η - ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      centredExpansion false T.a T.chainParams.ρA m f y η (leftTranslate (bondSpread c X τ) V)) =
      (fun τ : Fin k → ℝ => ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x m Y
      (leftTranslate (bondSpread c X τ) V) η) - fun τ => ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      centredExpansion false T.a T.chainParams.ρA m f y η (leftTranslate (bondSpread c X τ) V) := rfl
  rw [e3, e2]
  simp only [ContinuousMultilinearMap.sub_apply]
  rw [iteratedFDeriv_finsetSum_apply _ k _ 0 sY, iteratedFDeriv_finsetSum_apply _ k _ 0 sy]
  simp only [Hb, Hr, bondDeriv, sub_eq_add_neg]
theorem sum_sites_le_sum_fineBonds (r : ℝ) (Z : F.Cell) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, Real.exp (-(r * cellSupDist (enclosingCell y) Z)) ≤
      ∑ b ∈ fineBonds F, Real.exp (-(r * cellSupDist (enclosingCell b.1) Z)) := by
  unfold fineBonds
  rw [Finset.sum_product]
  refine Finset.sum_le_sum fun y _ => ?_
  exact Finset.single_le_sum (f := fun _ : Fin 4 => Real.exp (-(r * cellSupDist (enclosingCell y) Z)))
    (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ (0 : Fin 4))
theorem sum_cells_le_sum_sites (hL : Odd F.blockSide) (r : ℝ) (Z : F.Cell) :
    ∑ Y ∈ finiteCells F, Real.exp (-(r * cellSupDist Y Z)) ≤
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, Real.exp (-(r * cellSupDist (enclosingCell y) Z)) := by
  classical
  have h0 : ∀ M : ℕ, Odd M → (0 : Fin 4 → ℤ) ∈ centredCube M := fun M hM => by
    unfold centredCube
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨q, rfl⟩ := hM
    simp only [Finset.mem_Icc, Pi.zero_apply]
    push_cast
    constructor <;> omega
  have hM : Odd (F.blockSide ^ (F.top - F.depth)) := hL.pow
  have hc : ∀ Y : F.Cell,
      enclosingCell (cellCentre F.depth Y + siteOfCoords F.depth 0 : F.Site F.depth) = Y := fun Y =>
    BlockTrees.enclosingCell_cellCentre_add hL Y 0 (h0 _ hM)
  let φ : F.Cell → F.Site F.depth := fun Y => cellCentre F.depth Y + siteOfCoords F.depth 0
  have hinj : Set.InjOn φ (finiteCells F : Set F.Cell) := fun a _ b _ hab => by
    have := congrArg enclosingCell hab
    simpa only [φ, hc] using this
  calc ∑ Y ∈ finiteCells F, Real.exp (-(r * cellSupDist Y Z))
      = ∑ Y ∈ finiteCells F, Real.exp (-(r * cellSupDist (enclosingCell (φ Y)) Z)) := by
        refine Finset.sum_congr rfl fun Y _ => ?_
        simp only [φ, hc]
    _ = ∑ y ∈ (finiteCells F).image φ, Real.exp (-(r * cellSupDist (enclosingCell y) Z)) :=
        (Finset.sum_image
          (f := fun y : F.Site F.depth => Real.exp (-(r * cellSupDist (enclosingCell y) Z))) hinj).symm
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => (Real.exp_pos _).le
        intro y hy
        obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hy
        unfold sitesOfCells
        exact Finset.mem_biUnion.2 ⟨Y, hY, Finset.mem_image.2 ⟨0, h0 _ hM, rfl⟩⟩
end ExponentLocality
open ExponentLocality in
theorem exponentLocality_holds (hS : FiniteSumSizeBound) (hLaw : normalizedBallLawIsProbabilityStatement)
    (hEnds : interpolationAtEndpoints) (hTwo : IteratedFDerivParamDiff)
    (hFB : interpolatedFramesStatement) (hB : CellExponentsBounded)
    (hRw : CentredExpansionsBounded) (hG : CubicTorusCellGeometry)
    (hJ : EventuallyInParametersCombines) (hJr : SummableBounds.joinAtLoweredConstantsStatement) :
    exponentLocalityStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cz, Cr, hP⟩ := hFB
  obtain ⟨hg1, hg2⟩ := hG
  choose! Wc hWc0 hWc using hg2
  have h64 : EventuallyInParameters fun T => 1 ≤ T.Cs ∧ 64 ≤ T.n₀ ∧ 1 ≤ T.coupling :=
    fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨1, fun _ hCs _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨hCs, h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨fun T q => |Cz T q| + 1, fun U => |2 * U.Cs * (1 + U.energyRatio) * (Wc (6 * U.κ) * (U.L : ℝ) ^ 4)|,
    fun T q => by positivity, fun T => abs_nonneg _, ?_⟩
  refine weaken _ _ ?_ (join _ _ hP (join _ _ h64 (join _ _ hB hRw)))
  rintro T hDr ⟨hPT, ⟨hc, h64', hy1⟩, hXb, hRb⟩
  intro t x f F V k cc X l₀ hst hrow hk hX
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx1 : 1 ≤ x := hy1.trans hfl
  have hx : 0 < x := by linarith
  have hPT' := hPT t x hfl
  set Q := coldHalfLawAt T x f with hQ
  let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) := lawAtTop V (Q.exponent V)
  have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
      (frameRadius x) (chordBondDist F) :=
    ⟨hst.torus, hst.small_curvature, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded,
      Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨hconv, -, hsizes⟩ := hPT'.laws _ (chordBondDist F) 1 (fun _ => 1) (fun _ => M)
    ⟨fun _ => zero_le_one, by simp⟩ (fun _ => hadm)
  have hsz := hsizes M hadm
  rw [convexCombinationExponent_lawAtTop] at hconv hsz
  obtain ⟨hLF, -, n, hside, hn⟩ := hst.torus
  have hnpos : 64 ≤ n := h64'.trans hn
  have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  have hcub : IsLargeCubicTorus F := ⟨n, hnpos, hside⟩
  have hfin : Finite F.Cell := by
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  obtain ⟨-, -, -, htri, -⟩ := hg1 F hoddF hcub
  have hκ : 0 < T.κ := hDr.κ_pos
  have hr6 : 0 < 6 * T.κ := by positivity
  have hWb := hWc (6 * T.κ) hr6 F hoddF hcub (cc l₀).1
  rw [hLF] at hWb
  have hWy := (sum_sites_le_sum_fineBonds (F := F) (6 * T.κ) (cc l₀).1).trans hWb
  have hWY := (sum_cells_le_sum_sites hoddF (6 * T.κ) (cc l₀).1).trans hWy
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hE : 1 ≤ T.E := hDr.one_le_E
  have hη := hDr.η₃_pos
  have hres := hasLocalSize_bondDeriv_exponent hS hLaw hEnds hTwo T hρ hDr.cutoff hκ hη hDr.η₃_le_one hE
    (lt_of_lt_of_le one_pos hc) (Cz := Cz (momentParameters T)) (t := t) (x := x) (f := f) (V := V) (c := cc)
    (X := X) l₀ hx hst.family_bounded hsz hconv
    (fun V' hV' => (hXb t x F V' false hfl ⟨hLF, hst.torus.2.1, n, hside, hn⟩ hV').1)
    (hRb t x f F V false hfl hrow ⟨hLF, hst.torus.2.1, n, hside, hn⟩ hst.small_curvature)
    hst.small_curvature hfin hk hX htri hWY hWy
  set W := Wc (6 * T.κ) * (T.L : ℝ) ^ 4 with hW
  have hW0 : 0 ≤ W := by
    have := hWc0 (6 * T.κ) hr6
    positivity
  have hE₃ : 0 ≤ T.energyRatio := by
    show 0 ≤ T.E / T.η₃
    positivity
  have hxp : x ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hxp0 : 0 ≤ x ^ (-(1 / 2) : ℝ) := (Real.rpow_pos_of_pos hx _).le
  have hc0 : 0 ≤ T.Cs := by linarith
  have hle : T.Cs * W + T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * W ≤
      |2 * T.Cs * (1 + T.energyRatio) * (Wc (6 * T.κ) * (T.L : ℝ) ^ 4)| := by
    refine le_trans ?_ (le_abs_self _)
    have a1 : T.Cs * T.energyRatio * x ^ (-(1 / 2) : ℝ) * W ≤ T.Cs * T.energyRatio * 1 * W := by gcongr
    have a2 : 0 ≤ T.Cs * T.energyRatio * W := by positivity
    have a3 : 0 ≤ T.Cs * W := by positivity
    nlinarith
  have hexp := Real.exp_pos (-(2 ^ 3 * T.κ * (_root_.YangMills.Construction.BlockAverages.bondListDiameter cc : ℝ)))
  refine ⟨hres.1, hasLocalSize_mono (fun q => le_of_eq (abs_of_nonneg (by positivity))) (by positivity) ?_ hres.2⟩
  exact mul_le_mul_of_nonneg_right hle hexp.le
end ResponseInTheExpansion
end YangMills.Construction
end
