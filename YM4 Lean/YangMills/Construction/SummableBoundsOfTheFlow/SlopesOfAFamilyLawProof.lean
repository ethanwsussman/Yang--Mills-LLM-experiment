import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongTheFieldsOfTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.RestAlongAFieldHasItsSizeProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.IteratedDerivative YangMills.Construction.Estimates
namespace YangMills.Construction.Interpolation
namespace FamilyLawSlope
section Slopes
variable {F : BlockFrame} {k : ℕ}
theorem bondDeriv_slopes (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 1) (η : StepVariable (finiteCells F))
    (hf : ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (ζ, 0)) :
    ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun ζ => bondDeriv (G ζ) V c X) η ∧
    (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      fderiv ℝ (fun ζ => bondDeriv (G ζ) V c X) η (bondVariation b e) = jointMixedDeriv G η V ![b] ![e] c X) ∧
    ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      (fderiv ℝ (fderiv ℝ fun ζ => bondDeriv (G ζ) V c X) η (bondVariation b' e')) (bondVariation b e) =
        jointMixedDeriv G η V ![b', b] ![e', e] c X := by apply _root_.YangMills.Construction.IteratedDerivative.MovingFieldRemainderSize.bondDeriv_slopes <;> assumption
end Slopes
section Forms
variable {F : BlockFrame} {ρ : ℝ} {V : F.GaugeField F.top}
  {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem leftTranslate_bondSpread_elim0 (τ : Fin 0 → ℝ) (V : F.GaugeField F.top) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions) τ) V = V := by
  funext y i
  simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, expUnit_zero]
theorem bondDeriv_elim0 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : F.GaugeField F.top → E)
    (V : F.GaugeField F.top) :
    bondDeriv g V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) = g V := by apply _root_.YangMills.SharedProofs.p27916 <;> assumption
theorem rotatedEval_contDiffAt (hJ : JointlyContDiffOnBalls ρ V G) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0) := by apply _root_.YangMills.Construction.Interpolation.ExpansionThirdDeriv.contDiffAt_rotatedEval <;> assumption
theorem contDiffAt_slice (hJ : JointlyContDiffOnBalls ρ V G) (η : StepVariable (finiteCells F))
    (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun ζ => G ζ V) η := by
  have h := ContDiffAt.comp (g := rotatedEval G V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions))
    (f := fun ζ => ((ζ, 0) : StepVariable (finiteCells F) × (Fin 0 → ℝ))) η (rotatedEval_contDiffAt hJ _ _ η hη)
    (contDiff_id.prodMk contDiff_const).contDiffAt
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ => ?_)
  simp [rotatedEval, leftTranslate_bondSpread_elim0]
theorem cellSupDist_le_bondSpanWithCell (hD : SupDistCellComparison) {k : ℕ} (Y z : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) :
    cellSupDist z Y ≤ bondSpanWithCell Y z c := by
  have e : ∀ y w : F.Cell, siteSupDist y w = cellSupDist y w := fun _ _ => rfl
  unfold bondSpanWithCell
  set c' : Fin (k + 1) → F.Site F.top × Fin 4 := Fin.cons (z, 0) c with hc'
  have hone : ∀ l, cellSupDist Y (c' l).1 ≤ bondSpan Y c' := fun l =>
    (Finset.le_sup (f := fun l => cellSupDist Y (c' l).1) (Finset.mem_univ l)).trans (le_max_left _ _)
  have h1 := (hD.1 F F.top z Y Y).2.1
  rw [e, e] at h1
  rw [h1]
  simpa [hc'] using hone 0
theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
theorem mul_sqrt_add_one_le {x u : ℝ} (hx : 1 ≤ x) (hu : 0 ≤ u) :
    x * Real.sqrt u + 1 ≤ 2 * Real.sqrt x * (x * u + 1) := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.mul_sqrt_add_one_le <;> assumption
theorem abs_bondVariation_le {ι : Type} [Fintype ι] [DecidableEq ι] (L : BondField ι →L[ℝ] ℝ) (b : ι) {D : ℝ}
    (hD0 : 0 ≤ D) (h : ∀ e : BondVector, ‖e‖ = 1 → |L (bondVariation b e)| ≤ D) (w : BondVector) :
    |L (bondVariation b w)| ≤ D * ‖w‖ := by
  have h1 : ‖L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)‖ ≤ D :=
    ContinuousLinearMap.opNorm_le_of_unit_norm hD0 fun e he => by
      rw [Real.norm_eq_abs]
      exact h e he
  have h2 := (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)).le_opNorm w
  rw [Real.norm_eq_abs] at h2
  exact h2.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
theorem fderiv_fderiv_apply_eq_secondDerivAlong {ι : Type} [Fintype ι] [DecidableEq ι] {Ψ : BondField ι → ℝ}
    {η : BondField ι} (hΨ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Ψ η) (u v : BondField ι) :
    (fderiv ℝ (fderiv ℝ Ψ) η v) u = secondDerivAlong Ψ η u v := by
  have d1 : DifferentiableAt ℝ (fderiv ℝ Ψ) η :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have h := (d1.hasFDerivAt.clm_apply (hasFDerivAt_const u η)).fderiv
  unfold secondDerivAlong
  rw [h]
  simp
end Forms
end FamilyLawSlope
open FamilyLawSlope in
set_option maxHeartbeats 2000000 in
theorem familyLawExponentSlopeBounds_holds (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hD : SupDistCellComparison) : FamilyLawExponentSlopeBounds := by
  classical
  intro F s a ρA ρ x κ C Cb Ef W m V φ hρ hx hκ hC hCb hEf hW hB hP hJ hG hWc hWs hWb hsq b
  have hx0 : 0 < x := by linarith
  set r := Real.sqrt x with hr
  have hr1 : 1 ≤ r := by
    rw [hr, Real.one_le_sqrt]
    exact hx
  have hrr : r * r = x := Real.mul_self_sqrt hx0.le
  have hrx : r ≤ x := by nlinarith
  set U : Set (StepVariable (finiteCells F)) := {η | ∀ b, ‖η b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η | ‖η b‖ < ρ} := by
      ext η
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const
  have eD : ∀ y w : F.Cell, siteSupDist y w = cellSupDist y w := fun _ _ => rfl
  have sym : ∀ u v : F.Cell, (cellSupDist u v : ℝ) = cellSupDist v u := fun u v => by
    have := (hD.1 F F.top u v v).2.1
    rw [eD, eD] at this
    exact_mod_cast this
  set ψ : F.Cell → StepVariable (finiteCells F) → ℝ :=
    fun Y => interpolatedBlockExponent s a ρA x m Y V with hψd
  set row : F.Site F.depth → StepVariable (finiteCells F) → ℝ :=
    fun y ζ => interpolatedExpansion s a ρA m φ y ζ V with hrowd
  set Fam : StepVariable (finiteCells F) → ℝ := familyLawExponent s a ρA x m φ V with hFam
  have hJψ : ∀ Y, JointlyContDiffOnBalls ρ V (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) :=
    fun Y k c X η hη => hP.smooth Y η k c X hη
  have cψ : ∀ Y, ∀ η ∈ U, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (ψ Y) η := fun Y η hη =>
    contDiffAt_slice (hJψ Y) η fun b => (hη b).le
  have crow : ∀ y, ∀ η ∈ U, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (row y) η := fun y η hη =>
    contDiffAt_slice (hJ y) η fun b => (hη b).le
  have ev : ∀ η ∈ U, Fam =ᶠ[𝓝 η] fun ζ =>
      (∑ Y ∈ finiteCells F, ψ Y ζ) - ∑ y ∈ sitesOfCells (finiteCells F) F.depth, row y ζ := by
    intro η hη
    filter_upwards [hUo.mem_nhds hη] with ζ hζ
    simp only [hFam, familyLawExponent, hψd, hrowd]
    rw [hP.sum_eq ζ hζ]
  have cFam : ∀ η ∈ U, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Fam η := by
    intro η hη
    have h1 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun ζ =>
        (∑ Y ∈ finiteCells F, ψ Y ζ) - ∑ y ∈ sitesOfCells (finiteCells F) F.depth, row y ζ) η :=
      (ContDiffAt.sum fun Y _ => (cψ Y η hη).of_le (by norm_num)).sub
        (ContDiffAt.sum fun y _ => (crow y η hη).of_le (by norm_num))
    exact h1.congr_of_eventuallyEq (ev η hη)
  have hd1 : ∀ η ∈ U, ∀ u, fderiv ℝ Fam η u = (∑ Y ∈ finiteCells F, fderiv ℝ (ψ Y) η u) -
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, fderiv ℝ (row y) η u := by
    intro η hη u
    rw [(ev η hη).fderiv_eq]
    have h1 := HasFDerivAt.fun_sum (u := finiteCells F) fun Y _ =>
      ((cψ Y η hη).differentiableAt (by simp)).hasFDerivAt
    have h2 := HasFDerivAt.fun_sum (u := sitesOfCells (finiteCells F) F.depth) fun y _ =>
      ((crow y η hη).differentiableAt (by simp)).hasFDerivAt
    have h3 : HasFDerivAt (fun ζ =>
        (∑ Y ∈ finiteCells F, ψ Y ζ) - ∑ y ∈ sitesOfCells (finiteCells F) F.depth, row y ζ) _ η := h1.sub h2
    rw [h3.fderiv]
    simp
  have hd2 : ∀ η ∈ U, ∀ u v, secondDerivAlong Fam η u v =
      (∑ Y ∈ finiteCells F, secondDerivAlong (ψ Y) η u v) -
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, secondDerivAlong (row y) η u v := by
    intro η hη u v
    have e : (fun ζ => fderiv ℝ Fam ζ u) =ᶠ[𝓝 η] fun ζ => (∑ Y ∈ finiteCells F, fderiv ℝ (ψ Y) ζ u) -
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, fderiv ℝ (row y) ζ u := by
      filter_upwards [hUo.mem_nhds hη] with ζ hζ
      exact hd1 ζ hζ u
    unfold secondDerivAlong
    rw [e.fderiv_eq]
    have dψ : ∀ Y, DifferentiableAt ℝ (fun ζ => fderiv ℝ (ψ Y) ζ u) η := fun Y =>
      (((cψ Y η hη).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).clm_apply
        (differentiableAt_const u)
    have dr : ∀ y, DifferentiableAt ℝ (fun ζ => fderiv ℝ (row y) ζ u) η := fun y =>
      (((crow y η hη).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).clm_apply
        (differentiableAt_const u)
    have h1 := HasFDerivAt.fun_sum (u := finiteCells F) fun Y _ => (dψ Y).hasFDerivAt
    have h2 := HasFDerivAt.fun_sum (u := sitesOfCells (finiteCells F) F.depth) fun y _ => (dr y).hasFDerivAt
    have h3 : HasFDerivAt (fun ζ => (∑ Y ∈ finiteCells F, fderiv ℝ (ψ Y) ζ u) -
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, fderiv ℝ (row y) ζ u) _ η := h1.sub h2
    rw [h3.fderiv]
    simp
  set c₉ : Fin 0 → F.Site F.top × Fin 4 := Fin.elim0 with hc₉
  set X₉ : Fin 0 → imaginaryQuaternions := Fin.elim0 with hX₉
  have slopes := fun (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (hη : η ∈ U) =>
    bondDeriv_slopes hL hA (fun ζ V' => interpolatedExpansion s a ρA m φ y ζ V') V c₉ X₉ (Nat.zero_le 1) η (by
      filter_upwards [hUo.mem_nhds hη] with ζ hζ
      exact rotatedEval_contDiffAt (hJ y) c₉ X₉ ζ fun b => (hζ b).le)
  have eRow : ∀ y, (fun ζ => bondDeriv (interpolatedExpansion s a ρA m φ y ζ) V c₉ X₉) = row y := fun y => by
    funext ζ
    exact bondDeriv_elim0 _ V
  set E : F.Cell → ℝ := fun Y => Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) with hE
  have hE0 : ∀ Y, 0 ≤ E Y := fun Y => (Real.exp_pos _).le
  have hEsum : ∑ Y ∈ finiteCells F, E Y ≤ W := by
    refine (Finset.sum_le_sum fun Y _ => ?_).trans (hWc (enclosingCell b.1.1))
    refine Real.exp_le_exp.2 ?_
    rw [sym]
    have a0 : (0 : ℝ) ≤ cellSupDist Y (enclosingCell b.1.1) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hκ.le a0]
  set w : ↥(chordBonds (finiteCells F)) → ℝ := fun b' => ∑ Y ∈ finiteCells F, E Y *
    Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b'.1.1) Y : ℝ))) with hw
  have hw0 : ∀ b', 0 ≤ w b' := fun b' =>
    Finset.sum_nonneg fun Y _ => mul_nonneg (hE0 Y) (Real.exp_pos _).le
  have hwsum : ∑ b', w b' ≤ W ^ 2 := by
    simp only [hw]
    rw [Finset.sum_comm]
    have h1 : ∀ Y ∈ finiteCells F, ∑ b' : ↥(chordBonds (finiteCells F)), E Y *
        Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b'.1.1) Y : ℝ))) ≤ E Y * W := fun Y _ => by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hWb Y) (hE0 Y)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_mul, sq]
    exact mul_le_mul_of_nonneg_right hEsum hW
  have hS : ∀ η : StepVariable (finiteCells F),
      ∑ Y ∈ finiteCells F, E Y * localSqNorm κ Y η = ∑ b', w b' * ‖η b'‖ ^ 2 := by
    intro η
    simp only [localSqNorm, hw, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun Y _ => by ring
  have sq0 : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), 0 ≤ localSqNorm κ Y η := fun Y η =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hN0 : 0 ≤ slopeConstant C W := by
    unfold slopeConstant
    positivity
  have hCE : 0 ≤ Cb * Ef := mul_nonneg hCb hEf
  have p1 : ∀ η ∈ U, ∀ e : BondVector, ‖e‖ = 1 → |fderiv ℝ Fam η (bondVariation b e)| ≤
      slopeConstant C W * r * (x * ∑ b', w b' * ‖η b'‖ ^ 2 + 1) := by
    intro η hη e he
    have hSq : 0 ≤ ∑ b', w b' * ‖η b'‖ ^ 2 :=
      Finset.sum_nonneg fun b' _ => mul_nonneg (hw0 b') (sq_nonneg _)
    set M : ℝ := x * ∑ b', w b' * ‖η b'‖ ^ 2 + 1 with hM
    have hM1 : 1 ≤ M := by
      simp only [hM]
      nlinarith
    rw [hd1 η hη]
    have tψ : |∑ Y ∈ finiteCells F, fderiv ℝ (ψ Y) η (bondVariation b e)| ≤ 2 * C * (W + 1) * r * M := by
      have each : ∀ Y ∈ finiteCells F, |fderiv ℝ (ψ Y) η (bondVariation b e)| ≤
          2 * C * r * (x * (E Y * localSqNorm κ Y η) + E Y) := by
        intro Y _
        have h := hB.deriv_top_partial Y η b e 0 c₉ X₉ hη (by omega) (fun l => l.elim0) he
        rw [bondDeriv_elim0] at h
        refine h.trans ?_
        have hE' : Real.exp (-(2 ^ 6 * κ * (bondSpanWithCell Y (enclosingCell b.1.1) c₉ : ℝ))) ≤ E Y := by
          refine Real.exp_le_exp.2 ?_
          have a1 : ((cellSupDist (enclosingCell b.1.1) Y : ℕ) : ℝ) ≤
              bondSpanWithCell Y (enclosingCell b.1.1) c₉ := by
            exact_mod_cast cellSupDist_le_bondSpanWithCell hD Y (enclosingCell b.1.1) c₉
          have := mul_le_mul_of_nonneg_left a1 (by positivity : 0 ≤ 2 ^ 6 * κ)
          linarith
        have h2 := mul_sqrt_add_one_le hx (sq0 Y η)
        calc _ ≤ C * (2 * r * (x * localSqNorm κ Y η + 1)) * E Y := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) hE' (Real.exp_pos _).le ?_
              have := sq0 Y η
              positivity
          _ = _ := by ring
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum each).trans ?_)
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hS η]
      have h3 : x * ∑ b', w b' * ‖η b'‖ ^ 2 + ∑ Y ∈ finiteCells F, E Y ≤ (W + 1) * M := by
        simp only [hM]
        nlinarith [mul_nonneg hx0.le hSq]
      calc _ ≤ 2 * C * r * ((W + 1) * M) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
    have trow : |∑ y ∈ sitesOfCells (finiteCells F) F.depth, fderiv ℝ (row y) η (bondVariation b e)| ≤
        Cb * Ef * W := by
      have each : ∀ y ∈ sitesOfCells (finiteCells F) F.depth, |fderiv ℝ (row y) η (bondVariation b e)| ≤
          Cb * Ef * Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell y) (enclosingCell b.1.1) : ℝ))) := by
        intro y _
        have h1 := (slopes y η hη).2.1 b e
        rw [eRow y] at h1
        rw [h1]
        refine (hG y η 1 ![b] ![e] hη (fun i => by fin_cases i; simpa using he) le_rfl (by omega)).trans ?_
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCE
        have a1 : ((cellSupDist (enclosingCell y) (enclosingCell b.1.1) : ℕ) : ℝ) ≤
            cellSetDiameter (insert (enclosingCell y)
            (chordBondCells ![b] ∪ topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) := by
          have m1 : enclosingCell y ∈ insert (enclosingCell y) (chordBondCells ![b] ∪
              topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)) := Finset.mem_insert_self _ _
          have m2 : enclosingCell b.1.1 ∈ insert (enclosingCell y) (chordBondCells ![b] ∪
              topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)) :=
            Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_image.2 ⟨0, Finset.mem_univ _, by simp⟩))
          exact_mod_cast cellSupDist_le_diameter m1 m2
        have a0 : (0 : ℝ) ≤ cellSupDist (enclosingCell y) (enclosingCell b.1.1) := Nat.cast_nonneg _
        nlinarith [mul_nonneg hκ.le a0, mul_le_mul_of_nonneg_left a1 hκ.le]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum each).trans ?_)
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hWs _) hCE
    refine (abs_sub _ _).trans ((add_le_add tψ trow).trans ?_)
    have h4 : Cb * Ef * W ≤ r * M := hsq.trans (le_mul_of_one_le_right (by linarith) hM1)
    simp only [slopeConstant]
    nlinarith
  have p2 : ∀ η ∈ U, ∀ (b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector), ‖e‖ = 1 → ‖e'‖ = 1 →
      |secondDerivAlong Fam η (bondVariation b e) (bondVariation b' e')| ≤
        slopeConstant C W * x * Real.exp (-(2 * κ * chordBondDist b' b)) := by
    intro η hη b' e e' he he'
    set D : ℝ := (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ) with hDd
    have hD0 : 0 ≤ D := Nat.cast_nonneg _
    have hDb : chordBondDist b' b = D := sym _ _
    rw [hd2 η hη, hDb]
    set ee : ℝ := Real.exp (-(2 * κ * D)) with hee
    have hee0 : 0 < ee := Real.exp_pos _
    have e5 : Real.exp (-(2 ^ 5 * κ * D)) ≤ ee := Real.exp_le_exp.2 (by nlinarith [mul_nonneg hκ.le hD0])
    have e6 : Real.exp (-(2 ^ 6 * κ * D)) ≤ ee := Real.exp_le_exp.2 (by nlinarith [mul_nonneg hκ.le hD0])
    have tψ : |∑ Y ∈ finiteCells F, secondDerivAlong (ψ Y) η (bondVariation b e) (bondVariation b' e')| ≤
        C * x * W * ee := by
      have each : ∀ Y ∈ finiteCells F, |secondDerivAlong (ψ Y) η (bondVariation b e) (bondVariation b' e')| ≤
          C * x * ee * Real.exp (-(2 ^ 5 * κ * (cellSupDist Y (enclosingCell b.1.1) : ℝ))) := by
        intro Y _
        have h := hB.second_deriv Y η b b' e e' hη he he'
        have hcast : ((max (cellSupDist Y (enclosingCell b.1.1)) (max (cellSupDist Y (enclosingCell b'.1.1))
            (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1))) : ℕ) : ℝ) =
            max (cellSupDist Y (enclosingCell b.1.1) : ℝ) (max (cellSupDist Y (enclosingCell b'.1.1) : ℝ) D) := by
          rw [hDd]
          push_cast
          rfl
        rw [hcast] at h
        refine h.trans ?_
        have hsum : Real.exp (-(2 ^ 6 * κ * max (cellSupDist Y (enclosingCell b.1.1) : ℝ)
            (max (cellSupDist Y (enclosingCell b'.1.1) : ℝ) D))) ≤
            ee * Real.exp (-(2 ^ 5 * κ * (cellSupDist Y (enclosingCell b.1.1) : ℝ))) := by
          have m1 : (cellSupDist Y (enclosingCell b.1.1) : ℝ) ≤ max (cellSupDist Y (enclosingCell b.1.1) : ℝ)
              (max (cellSupDist Y (enclosingCell b'.1.1) : ℝ) D) :=
            le_max_left _ _
          have m2 : D ≤ max (cellSupDist Y (enclosingCell b.1.1) : ℝ)
              (max (cellSupDist Y (enclosingCell b'.1.1) : ℝ) D) :=
            (le_max_right _ _).trans (le_max_right _ _)
          refine le_trans ?_ (mul_le_mul_of_nonneg_right e5 (Real.exp_pos _).le)
          rw [← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have a1 := mul_le_mul_of_nonneg_left m1 (by positivity : 0 ≤ 2 ^ 5 * κ)
          have a2 := mul_le_mul_of_nonneg_left m2 (by positivity : 0 ≤ 2 ^ 5 * κ)
          nlinarith
        calc _ ≤ C * x * (ee * Real.exp (-(2 ^ 5 * κ * (cellSupDist Y (enclosingCell b.1.1) : ℝ)))) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = _ := by ring
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum each).trans ?_)
      rw [← Finset.mul_sum]
      calc _ ≤ C * x * ee * W := mul_le_mul_of_nonneg_left (hWc _) (by positivity)
        _ = _ := by ring
    have trow : |∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        secondDerivAlong (row y) η (bondVariation b e) (bondVariation b' e')| ≤ Cb * Ef * W * ee := by
      have each : ∀ y ∈ sitesOfCells (finiteCells F) F.depth,
          |secondDerivAlong (row y) η (bondVariation b e) (bondVariation b' e')| ≤
          Cb * Ef * ee * Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell y) (enclosingCell b.1.1) : ℝ))) := by
        intro y _
        have h1 := (slopes y η hη).2.2 b b' e e'
        rw [eRow y] at h1
        rw [← fderiv_fderiv_apply_eq_secondDerivAlong ((crow y η hη).of_le (by norm_num)), h1]
        refine (hG y η 2 ![b', b] ![e', e] hη (fun i => by
          fin_cases i
          · simpa using he'
          · simpa using he) (by omega) le_rfl).trans ?_
        set Pc : Finset F.Cell := insert (enclosingCell y) (chordBondCells ![b', b] ∪
          topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)) with hPc
        have m1 : enclosingCell y ∈ Pc := Finset.mem_insert_self _ _
        have m2 : enclosingCell b.1.1 ∈ Pc :=
          Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.2 ⟨1, Finset.mem_univ _, by simp⟩))
        have m3 : enclosingCell b'.1.1 ∈ Pc :=
          Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.2 ⟨0, Finset.mem_univ _, by simp⟩))
        have a1 : ((cellSupDist (enclosingCell y) (enclosingCell b.1.1) : ℕ) : ℝ) ≤ cellSetDiameter Pc := by
          exact_mod_cast cellSupDist_le_diameter m1 m2
        have a2 : D ≤ cellSetDiameter Pc := by
          rw [hDd]
          exact_mod_cast cellSupDist_le_diameter m2 m3
        have hsum : Real.exp (-(2 ^ 7 * κ * (cellSetDiameter Pc : ℝ))) ≤
            ee * Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell y) (enclosingCell b.1.1) : ℝ))) := by
          refine le_trans ?_ (mul_le_mul_of_nonneg_right e6 (Real.exp_pos _).le)
          rw [← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have b1 := mul_le_mul_of_nonneg_left a1 (by positivity : 0 ≤ 2 ^ 6 * κ)
          have b2 := mul_le_mul_of_nonneg_left a2 (by positivity : 0 ≤ 2 ^ 6 * κ)
          nlinarith
        calc _ ≤ Cb * Ef * (ee * Real.exp (-(2 ^ 6 * κ *
              (cellSupDist (enclosingCell y) (enclosingCell b.1.1) : ℝ)))) :=
              mul_le_mul_of_nonneg_left hsum hCE
          _ = _ := by ring
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum each).trans ?_)
      rw [← Finset.mul_sum]
      calc _ ≤ Cb * Ef * ee * W := mul_le_mul_of_nonneg_left (hWs _) (by positivity)
        _ = _ := by ring
    refine (abs_sub _ _).trans ((add_le_add tψ trow).trans ?_)
    have h4 : Cb * Ef * W ≤ x := hsq.trans hrx
    have h5 : C * W ≤ 2 * C * (W + 1) := by nlinarith
    have hx00 : 0 ≤ x * ee := by positivity
    simp only [slopeConstant]
    nlinarith [mul_le_mul_of_nonneg_right h5 hx00, mul_le_mul_of_nonneg_right h4 hee0.le]
  refine ⟨w, hw0, hwsum, fun η e hη => ?_, fun η b' e e' hη => ?_⟩
  · have hSq : 0 ≤ ∑ b', w b' * ‖η b'‖ ^ 2 :=
      Finset.sum_nonneg fun b' _ => mul_nonneg (hw0 b') (sq_nonneg _)
    exact abs_bondVariation_le (fderiv ℝ Fam η) b (by positivity) (p1 η hη) e
  · have hc2 := cFam η hη
    have hE2 := Real.exp_pos (-(2 * κ * chordBondDist b' b))
    have hD₀ : 0 ≤ slopeConstant C W * x * Real.exp (-(2 * κ * chordBondDist b' b)) := by positivity
    rw [← fderiv_fderiv_apply_eq_secondDerivAlong hc2]
    have s1 : ∀ e' : BondVector, ‖e'‖ = 1 → ∀ e : BondVector,
        |fderiv ℝ (fderiv ℝ Fam) η (bondVariation b' e') (bondVariation b e)| ≤
        slopeConstant C W * x * Real.exp (-(2 * κ * chordBondDist b' b)) * ‖e‖ := fun e' he' e =>
      abs_bondVariation_le _ b hD₀ (fun e₁ he₁ => by
        rw [fderiv_fderiv_apply_eq_secondDerivAlong hc2]
        exact p2 η hη b' e₁ e' he₁ he') e
    have s2 := abs_bondVariation_le ((ContinuousLinearMap.apply ℝ ℝ
      (bondVariation b e : StepVariable (finiteCells F))).comp
      (fderiv ℝ (fderiv ℝ Fam) η)) b' (mul_nonneg hD₀ (norm_nonneg e)) (fun e₁ he₁ => s1 e₁ he₁ e) e'
    exact s2
end YangMills.Construction.Interpolation
end
