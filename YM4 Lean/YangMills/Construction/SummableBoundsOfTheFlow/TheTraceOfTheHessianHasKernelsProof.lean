import YangMills.Construction.RunningCouplingSlope.TraceAtTheLeastFieldHasKernelsProof
import YangMills.Construction.SummableBoundsOfTheFlow.LeastChartEnergyIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheHessianHasKernels
import YangMills.Construction.SummableBoundsOfTheFlow.TheTraceOfTheHessianHasKernels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open Set
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.IteratedDerivative YangMills.Construction.Interpolation YangMills.Construction.CellCounting YangMills.Construction.Estimates YangMills.Construction.RenormalizationStepParameters
namespace YangMills.Construction.ReferenceDensity
variable {F : BlockFrame}
section Distances
private theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
private theorem cellSetDiameter_le_add_of_cover {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (A B : List (Fin k)) (Y z : F.Cell) (hAB : ∀ l, l ∈ A ∨ l ∈ B) :
    cellSetDiameter ({Y} ∪ topBondCells c) ≤
      cellSetDiameter ({Y, z} ∪ topBondCells (restrictToList c A)) +
        cellSetDiameter ({z, Y} ∪ topBondCells (restrictToList c B)) := by apply _root_.YangMills.SharedProofs.p23886 <;> assumption
end Distances
section Matrices
variable {ι P : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup P] [NormedSpace ℝ P]
private theorem inv_entry_contDiffAt (N : P → Matrix ι ι ℝ) (p₀ : P) (n : WithTop ℕ∞)
    (h : ∀ i j, ContDiffAt ℝ n (fun p => N p i j) p₀) (hd : (N p₀).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ n (fun p => (N p)⁻¹ i j) p₀ := by apply _root_.YangMills.SharedProofs.p5216 <;> assumption
end Matrices
section Floor
private def coordUnit (i : ChartCoord F) : StepVariable (finiteCells F) :=
  bondVariation i.1 (EuclideanSpace.single i.2 1)
private def coordProj (i : ChartCoord F) : StepVariable (finiteCells F) →L[ℝ] ℝ :=
  (EuclideanSpace.proj i.2).comp (ContinuousLinearMap.proj i.1)
private theorem coordProj_apply (i : ChartCoord F) (ζ : StepVariable (finiteCells F)) :
    coordProj i ζ = ζ i.1 i.2 := rfl
private theorem coord_bondVariation (i : ChartCoord F) (b : ↥(chordBonds (finiteCells F))) (e : BondVector) :
    (bondVariation b e : StepVariable (finiteCells F)) i.1 i.2 = if i.1 = b then e i.2 else 0 := by
  unfold bondVariation
  split_ifs with h
  · rw [h, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h]
    rfl
abbrev _root_.YangMills.SharedProofs.p54563 := @coord_bondVariation
private theorem coordProj_coordUnit (i j : ChartCoord F) :
    coordProj i (coordUnit j) = if i = j then 1 else 0 := by
  rw [coordProj_apply]
  unfold coordUnit
  rw [coord_bondVariation]
  by_cases h1 : i.1 = j.1
  · by_cases h2 : i.2 = j.2
    · have : i = j := Prod.ext h1 h2
      subst this
      simp
    · have hne : i ≠ j := fun h => h2 (congrArg Prod.snd h)
      rw [if_pos h1, if_neg hne]
      simp [h2]
  · have hne : i ≠ j := fun h => h1 (congrArg Prod.fst h)
    rw [if_neg h1, if_neg hne]
private theorem eq_sum_coordUnit (ζ : StepVariable (finiteCells F)) :
    ζ = ∑ i, ζ i.1 i.2 • coordUnit i := by
  funext b
  ext k
  show coordProj (b, k) ζ = coordProj (b, k) (∑ i, ζ i.1 i.2 • coordUnit i)
  rw [map_sum]
  simp only [map_smul, coordProj_coordUnit, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rfl
private theorem secondDerivAlong_eq_fderiv {X : Type} [Fintype X] [DecidableEq X] (E : BondField X → ℝ)
    (z u w : BondField X) (hz : DifferentiableAt ℝ (fderiv ℝ E) z) :
    secondDerivAlong E z u w = fderiv ℝ (fderiv ℝ E) z w u := by
  unfold secondDerivAlong
  have h : HasFDerivAt (fun ζ => fderiv ℝ E ζ u)
      ((ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ E) z)) z :=
    ((ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt).comp z hz.hasFDerivAt
  rw [h.fderiv]
  rfl
abbrev _root_.YangMills.SharedProofs.p7378 := @secondDerivAlong_eq_fderiv
private theorem secondDerivAlong_zero_eq_sum (a ρ : ℝ) (V : F.GaugeField F.top)
    (hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0)
    (u v : StepVariable (finiteCells F)) :
    secondDerivAlong (chartedEnergyAtMinimizer a ρ V) 0 u v =
      ∑ i, ∑ j, chartedHessian a ρ V 0 i j * (u i.1 i.2 * v j.1 j.2) := by
  have hM : ∀ i j, chartedHessian a ρ V 0 i j =
      fderiv ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0 (coordUnit j) (coordUnit i) := by
    intro i j
    exact secondDerivAlong_eq_fderiv _ _ _ _ hd
  rw [secondDerivAlong_eq_fderiv _ _ _ _ hd]
  conv_lhs => rw [eq_sum_coordUnit u, eq_sum_coordUnit v]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hM]
  ring
abbrev _root_.YangMills.SharedProofs.p21715 := @secondDerivAlong_zero_eq_sum
private theorem interpolated_hessian_det_ne_zero (a ρ lam τ : ℝ) (V : F.GaugeField F.top) (hlam : 0 < lam)
    (h0 : 0 ≤ τ)
    (hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0)
    (hfl : ∀ u : StepVariable (finiteCells F),
      lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong (chartedEnergyAtMinimizer a ρ V) 0 u u) :
    (τ • chartedHessian a ρ V 0 + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hN⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  let ζ : StepVariable (finiteCells F) := fun b => WithLp.toLp 2 fun d => v (b, d)
  have hc : ∀ i : ChartCoord F, ζ i.1 i.2 = v i := fun _ => rfl
  have hform := hfl ζ
  rw [secondDerivAlong_zero_eq_sum a ρ V hd] at hform
  simp only [hc] at hform
  have e3 : ∑ b, ‖ζ b‖ ^ 2 = ∑ i : ChartCoord F, v i ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [EuclideanSpace.real_norm_sq_eq]
  rw [e3] at hform
  set M := chartedHessian a ρ V 0
  have e1 : ∑ i, v i * ((τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).mulVec v) i = 0 := by
    simp [hN]
  have e2 : ∑ i, v i * ((τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).mulVec v) i =
      τ * ∑ i, ∑ j, M i j * (v i * v j) + (1 - τ) * lam * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ((τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).mulVec v) i =
        τ * ∑ j, M i j * v j + (1 - τ) * lam * v i := by
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      ring
    rw [this, Finset.mul_sum]
    simp only [mul_add, Finset.mul_sum]
    have hs : ∑ j, v i * (τ * (M i j * v j)) = ∑ j, τ * (M i j * (v i * v j)) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    ring
  have hpos : 0 < ∑ i, v i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
    have : v i ≠ 0 := hi
    positivity
  rw [e1] at e2
  nlinarith [mul_le_mul_of_nonneg_left hform h0, mul_pos hlam hpos]
end Floor
private theorem eventually_rate_small :
    EventuallyInParameters fun T => 0 < T.chainParams.δ₂ ∧ T.κ ≤ T.chainParams.δ₂ / 2 ^ 14 ∧ 2 ≤ T.n₀ := by
  intro a _
  refine ⟨0, fun L _ _ c hc => ⟨0, fun Ct _ => ?_⟩⟩
  obtain ⟨⟨-, -, -, hδ, -⟩, -⟩ := hc.classical
  refine ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ _ hκ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun m _ =>
    ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨2, fun n₀ hn => ⟨0, fun CE _ => ⟨0, fun y₁ _ =>
      ⟨hδ, hκ, hn⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
theorem hessianTraceDecay_of_resolventDecay (hR : ResolventDecay)
    (hH : HessianDecay) (hS : chartedEnergyAtMinimizerRegular)
    (hI : IntervalIntegralSmoothFamily) (hA : DerivAlongRulesHold)
    (hP : BondDerivSumProductRules) (hB : cellBondsCardStatement)
    (hW : ExpDecaySumBounded) : HessianTraceDecay := by
  obtain ⟨D, hDpos, hH⟩ := hH
  have h₀ := EventuallyOrdered.and hR hS
  unfold EventuallyOrdered at h₀
  unfold HessianTraceDecay EventuallyOrdered
  refine EventuallyInParameters.mono (EventuallyInParameters.and h₀
    (EventuallyInParameters.and hH eventually_rate_small)) ?_
  rintro T ⟨g₀, gH, hδ, hκ, hn₂⟩ hT hn₁
  obtain ⟨⟨Cr, gR⟩, gS⟩ := g₀ hT hn₁
  have hκ0 : 0 < T.κ := hT.κ_pos
  obtain ⟨W, hW0, hWb⟩ := hW (12 * T.L ^ 4) (2 ^ 7 * T.κ) (by positivity)
  set Dm : ℝ := ∑ a ∈ Finset.range 7, D (rateParameters T) a with hDm
  set Cm : ℝ := ∑ a ∈ Finset.range 7, |Cr a| with hCm
  have hDa : ∀ a, a ≤ 6 → D (rateParameters T) a ≤ Dm := fun a ha =>
    Finset.single_le_sum (f := fun b => D (rateParameters T) b) (fun b _ => (hDpos _ b).le)
      (Finset.mem_range.2 (by omega))
  have hCa : ∀ a, a ≤ 6 → |Cr a| ≤ Cm := fun a ha =>
    Finset.single_le_sum (f := fun b => |Cr b|) (fun b _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  have hDm0 : 0 ≤ Dm := Finset.sum_nonneg fun b _ => (hDpos _ b).le
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun b _ => abs_nonneg _
  have hrate : 2 ^ 8 * T.κ ≤ T.chainParams.δ₂ := by
    have : T.chainParams.δ₂ / 2 ^ 14 ≤ T.chainParams.δ₂ / 2 ^ 8 := by
      apply div_le_div_of_nonneg_left hδ.le (by norm_num) (by norm_num)
    have h2 : T.κ ≤ T.chainParams.δ₂ / 2 ^ 8 := hκ.trans this
    rw [le_div_iff₀ (by norm_num)] at h2
    linarith
  refine ⟨12 * (T.L : ℝ) ^ 4 * (64 * (Dm * Cm) * W + |T.lam| * Cm), ?_⟩
  intro t F V Y k c X hF hV hk hX
  classical
  have hF' := hF
  obtain ⟨hFL, -, n, hside, hnn⟩ := hF'
  have hside2 : ∀ i, 2 ≤ F.extent i := by
    intro i
    rw [hside i]
    omega
  have hodd : Odd F.blockSide := hFL ▸ hT.odd_L
  have hcardB := hB F hodd hside2
  have hcard : ∀ z : F.Cell, (Finset.univ.filter fun j : ChartCoord F => enclosingCell j.1.1.1 = z).card ≤
      12 * T.L ^ 4 := by
    intro z
    have e : (Finset.univ.filter fun j : ChartCoord F => enclosingCell j.1.1.1 = z) =
        (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z) ×ˢ Finset.univ := by
      ext j
      simp
    rw [e, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have h1 := hcardB z
    rw [hFL] at h1
    convert Nat.mul_le_mul_right 3 h1 using 1
    ring
  have hWj : ∀ z : F.Cell, ∑ j : ChartCoord F,
      Real.exp (-(2 ^ 7 * T.κ * (cellSupDist (enclosingCell j.1.1.1) z : ℝ))) ≤ W :=
    hWb F (ChartCoord F) (fun j => enclosingCell j.1.1.1) (fun z => by convert hcard z)
  obtain ⟨hC, -, -, hlam, hfloor⟩ := gS t F V hF hV
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hBo : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} =
        ⋂ b, {η : StepVariable (finiteCells F) | ‖η b‖ < T.ballRadius} := by
      ext η
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have h0B : (0 : StepVariable (finiteCells F)) ∈
      {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
    intro b
    simpa using hρ
  have hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer T.a T.ρA V)) 0 :=
    ((hC.contDiffAt (hBo.mem_nhds h0B)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdet : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → (τ • chartedHessian T.a T.ρA V 0 +
      (1 - τ) • T.lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).det ≠ 0 := fun τ h0 _ =>
    interpolated_hessian_det_ne_zero _ _ _ τ V hlam h0 hd fun u => hfloor 0 u h0B
  let Msf : (Fin k → ℝ) → Matrix (ChartCoord F) (ChartCoord F) ℝ := fun σ =>
    chartedHessian T.a T.ρA (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ) V) 0
  have hMs : ∀ (i j : ChartCoord F) (m : ℕ), ContDiffAt ℝ (m : WithTop ℕ∞) (fun σ => Msf σ i j) 0 :=
    fun i j m => (gH t F V i j k c X hF hV hX).1 m
  let Nm : ℝ × (Fin k → ℝ) → Matrix (ChartCoord F) (ChartCoord F) ℝ := fun p =>
    p.1 • Msf p.2 + (1 - p.1) • T.lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)
  have hMp : ∀ (v : ℝ) (i j : ChartCoord F), ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun p : ℝ × (Fin k → ℝ) => Msf p.2 i j) (v, 0) := fun v i j =>
    ContDiffAt.comp (v, (0 : Fin k → ℝ)) (hMs i j k) contDiffAt_snd
  have hNs : ∀ (v : ℝ) (i j : ChartCoord F), ContDiffAt ℝ (k : WithTop ℕ∞) (fun p => Nm p i j) (v, 0) := by
    intro v i j
    have e : (fun p => Nm p i j) = fun p : ℝ × (Fin k → ℝ) => p.1 * Msf p.2 i j +
        (1 - p.1) * (T.lam * (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ) i j) := by
      funext p
      simp [Nm, Matrix.add_apply, Matrix.smul_apply]
    rw [e]
    exact (contDiffAt_fst.mul (hMp v i j)).add ((contDiffAt_const.sub contDiffAt_fst).mul contDiffAt_const)
  have hNdet : ∀ v ∈ Icc (0 : ℝ) 1, (Nm (v, 0)).det ≠ 0 := by
    intro v hv
    simp only [Nm, Msf, leftTranslate_bondSpread_zero]
    exact hdet v hv.1 hv.2
  have hRs : ∀ v ∈ Icc (0 : ℝ) 1, ∀ i j : ChartCoord F, ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun p => (Nm p)⁻¹ i j) (v, 0) := fun v hv i j =>
    inv_entry_contDiffAt Nm _ _ (hNs v) (hNdet v hv) i j
  have hform : ∀ (V' : F.GaugeField F.top) (τ : ℝ), hessianCellShare T.a T.ρA T.lam Y V' τ =
      ∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then
        ((∑ j, chartedHessian T.a T.ρA V' 0 i j * hessianResolvent T.a T.ρA T.lam τ V' j i) -
          T.lam * hessianResolvent T.a T.ρA T.lam τ V' i i) else 0 := by
    intro V' τ
    unfold hessianCellShare
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : enclosingCell i.1.1.1 = Y
    · rw [if_pos h, if_pos h, Matrix.sub_mul, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]
      rfl
    · rw [if_neg h, if_neg h]
  let Af : ℝ × (Fin k → ℝ) → ℝ := fun p =>
    hessianCellShare T.a T.ρA T.lam Y (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X p.2) V) p.1
  have hAf : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (k : WithTop ℕ∞) Af (v, 0) := by
    intro v hv
    have e : Af = fun p => ∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then
        ((∑ j, Msf p.2 i j * (Nm p)⁻¹ j i) - T.lam * (Nm p)⁻¹ i i) else 0 := by
      funext p
      exact hform _ _
    rw [e]
    refine ContDiffAt.sum fun i _ => ?_
    by_cases h : enclosingCell i.1.1.1 = Y
    · simp only [if_pos h]
      exact (ContDiffAt.sum fun j _ => (hMp v i j).mul (hRs v hv j i)).sub
        (contDiffAt_const.mul (hRs v hv i i))
    · simp only [if_neg h]
      exact contDiffAt_const
  obtain ⟨hI1, hI2⟩ := hI (Fin k → ℝ) Af 0 k fun v hv => hAf v hv
  refine ⟨hI1, ?_⟩
  have hrl := hA.1 (Fin k → ℝ) ℝ
  set S : ℕ := cellSetDiameter ({Y} ∪ topBondCells c) with hSdef
  set E : ℝ := Real.exp (-(2 ^ 7 * T.κ * S)) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have key : ∀ v ∈ Icc (0 : ℝ) 1,
      |bondDeriv (fun V' => hessianCellShare T.a T.ρA T.lam Y V' v) V c X| ≤
        12 * (T.L : ℝ) ^ 4 * (64 * (Dm * Cm) * W + |T.lam| * Cm) * E := by
    intro v hv
    let Gm : ChartCoord F → ChartCoord F → F.GaugeField F.top → ℝ := fun i j V' =>
      chartedHessian T.a T.ρA V' 0 i j
    let Rm : ChartCoord F → ChartCoord F → F.GaugeField F.top → ℝ := fun i j V' =>
      hessianResolvent T.a T.ρA T.lam v V' i j
    obtain ⟨hsum, hsmul, hprod⟩ := hP F V k c X
    have sG : ∀ i j, ContDiffAlongBonds k (Gm i j) V c X := fun i j => hMs i j k
    have sR : ∀ i j, ContDiffAlongBonds k (Rm i j) V c X := fun i j =>
      ((gR t F V v i j k c X hF hV hv.1 hv.2 hk hX).1).of_le (by exact_mod_cast hk)
    have sGR : ∀ i j, ContDiffAlongBonds k (fun V' => Gm i j V' * Rm j i V') V c X := fun i j =>
      ContDiffAt.mul (sG i j) (sR j i)
    have sIn : ∀ i, ContDiffAlongBonds k (fun V' => ∑ j, Gm i j V' * Rm j i V') V c X := fun i =>
      ContDiffAt.sum fun j _ => sGR i j
    have sLam : ∀ i, ContDiffAlongBonds k (fun V' => (-T.lam) * Rm i i V') V c X := fun i =>
      contDiffAt_const.mul (sR i i)
    have add2 : ∀ G H : F.GaugeField F.top → ℝ, ContDiffAlongBonds k G V c X →
        ContDiffAlongBonds k H V c X →
        bondDeriv (fun V' => G V' + H V') V c X = bondDeriv G V c X + bondDeriv H V c X := by
      intro G H hG hH
      have h := hsum Bool Finset.univ (fun b => if b then G else H) (by
        intro b _
        cases b
        · simpa using hH
        · simpa using hG)
      simpa [Fintype.sum_bool] using h
    let Ej : ChartCoord F → ℝ := fun j =>
      Real.exp (-(2 ^ 7 * T.κ * (cellSupDist (enclosingCell j.1.1.1) Y : ℝ)))
    have hprodb : ∀ i j, enclosingCell i.1.1.1 = Y →
        |bondDeriv (fun V' => Gm i j V' * Rm j i V') V c X| ≤ 2 ^ k * (Dm * Cm * E * Ej j) := by
      intro i j hi
      refine hprod _ _ _ (sG i j) (sR j i) fun A B hAB hcov => ?_
      have xA : AreUnitVectors (restrictToList X A) := fun l => hX _
      have xB : AreUnitVectors (restrictToList X B) := fun l => hX _
      have hA6 : A.length ≤ 6 := by omega
      have hB6 : B.length ≤ 6 := by omega
      have b1 := (gH t F V i j A.length (restrictToList c A) (restrictToList X A) hF hV xA).2
      have b2 := (gR t F V v j i B.length (restrictToList c B) (restrictToList X B) hF hV hv.1 hv.2 hB6 xB).2
      rw [hi] at b1 b2
      set s₁ : ℕ := cellSetDiameter ({Y, enclosingCell j.1.1.1} ∪ topBondCells (restrictToList c A)) with hs₁
      set s₂ : ℕ := cellSetDiameter ({enclosingCell j.1.1.1, Y} ∪ topBondCells (restrictToList c B)) with hs₂
      have hs₁0 : (0 : ℝ) ≤ s₁ := Nat.cast_nonneg _
      have hs₂0 : (0 : ℝ) ≤ s₂ := Nat.cast_nonneg _
      have hSle : (S : ℝ) ≤ s₁ + s₂ := by exact_mod_cast cellSetDiameter_le_add_of_cover c A B Y _ hcov
      have hdle : (cellSupDist (enclosingCell j.1.1.1) Y : ℝ) ≤ s₁ + s₂ := by
        have h1 : cellSupDist (enclosingCell j.1.1.1) Y ≤ s₁ := cellSupDist_le_diameter (by simp) (by simp)
        have h2 : (cellSupDist (enclosingCell j.1.1.1) Y : ℝ) ≤ s₁ := by exact_mod_cast h1
        linarith
      have c1 : |bondDeriv (Gm i j) V (restrictToList c A) (restrictToList X A)| ≤
          Dm * Real.exp (-(2 ^ 8 * T.κ * s₁)) := by
        refine b1.trans (mul_le_mul (hDa _ hA6) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hDm0)
        have := mul_le_mul_of_nonneg_right hrate hs₁0
        linarith
      have c2 : |bondDeriv (Rm j i) V (restrictToList c B) (restrictToList X B)| ≤
          Cm * Real.exp (-(2 ^ 8 * T.κ * s₂)) :=
        b2.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hCa _ hB6)) (Real.exp_pos _).le)
      have hexp : Real.exp (-(2 ^ 8 * T.κ * s₁)) * Real.exp (-(2 ^ 8 * T.κ * s₂)) ≤ E * Ej j := by
        show _ ≤ Real.exp _ * Real.exp _
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have a1 := mul_le_mul_of_nonneg_left hSle (by positivity : (0 : ℝ) ≤ 2 ^ 7 * T.κ)
        have a2 := mul_le_mul_of_nonneg_left hdle (by positivity : (0 : ℝ) ≤ 2 ^ 7 * T.κ)
        linarith
      calc _ ≤ (Dm * Real.exp (-(2 ^ 8 * T.κ * s₁))) * (Cm * Real.exp (-(2 ^ 8 * T.κ * s₂))) :=
            mul_le_mul c1 c2 (abs_nonneg _) (by positivity)
        _ = Dm * Cm * (Real.exp (-(2 ^ 8 * T.κ * s₁)) * Real.exp (-(2 ^ 8 * T.κ * s₂))) := by ring
        _ ≤ Dm * Cm * (E * Ej j) := mul_le_mul_of_nonneg_left hexp (mul_nonneg hDm0 hCm0)
        _ = Dm * Cm * E * Ej j := by ring
    have hone : ∀ i, enclosingCell i.1.1.1 = Y → |bondDeriv (Rm i i) V c X| ≤ Cm * E := by
      intro i hi
      have b := (gR t F V v i i k c X hF hV hv.1 hv.2 hk hX).2
      rw [hi, Finset.pair_eq_singleton] at b
      refine b.trans (mul_le_mul ((le_abs_self _).trans (hCa _ hk)) (Real.exp_le_exp.2 ?_)
        (Real.exp_pos _).le hCm0)
      have h1 : (0 : ℝ) ≤ T.κ * S := mul_nonneg hκ0.le (Nat.cast_nonneg _)
      nlinarith
    have hfun : (fun V' => hessianCellShare T.a T.ρA T.lam Y V' v) = fun V' =>
        ∑ i ∈ Finset.univ.filter (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y),
          ((∑ j, Gm i j V' * Rm j i V') + (-T.lam) * Rm i i V') := by
      funext V'
      rw [hform, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : enclosingCell i.1.1.1 = Y
      · rw [if_pos h, if_pos h]
        simp only [Gm, Rm]
        ring
      · rw [if_neg h, if_neg h]
    have sT : ∀ i, ContDiffAlongBonds k
        (fun V' => (∑ j, Gm i j V' * Rm j i V') + (-T.lam) * Rm i i V') V c X :=
      fun i => ContDiffAt.add (sIn i) (sLam i)
    rw [hfun, hsum _ _ _ (fun i _ => sT i)]
    have h2k : (2 : ℝ) ^ k ≤ 64 := by
      have : (2 : ℝ) ^ k ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) hk
      linarith
    have hterm : ∀ i ∈ Finset.univ.filter (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y),
        |bondDeriv (fun V' => (∑ j, Gm i j V' * Rm j i V') + (-T.lam) * Rm i i V') V c X| ≤
          (64 * (Dm * Cm) * W + |T.lam| * Cm) * E := by
      intro i hi
      have hi' : enclosingCell i.1.1.1 = Y := (Finset.mem_filter.1 hi).2
      rw [add2 _ _ (sIn i) (sLam i), hsmul _ _ (sR i i), hsum _ _ _ (fun j _ => sGR i j)]
      have hP0 : 0 ≤ Dm * Cm * E := mul_nonneg (mul_nonneg hDm0 hCm0) hE0
      have t1 : |∑ j, bondDeriv (fun V' => Gm i j V' * Rm j i V') V c X| ≤ 64 * (Dm * Cm) * W * E := by
        calc _ ≤ ∑ j, |bondDeriv (fun V' => Gm i j V' * Rm j i V') V c X| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j, 2 ^ k * (Dm * Cm * E * Ej j) := Finset.sum_le_sum fun j _ => hprodb i j hi'
          _ = 2 ^ k * (Dm * Cm * E) * ∑ j, Ej j := by
            have hq : ∀ q : ℝ, ∑ j, q * Ej j = q * ∑ j, Ej j := fun q => (Finset.mul_sum _ _ _).symm
            rw [← hq]
            exact Finset.sum_congr rfl fun j _ => by ring
          _ ≤ 2 ^ k * (Dm * Cm * E) * W := mul_le_mul_of_nonneg_left (hWj Y) (by positivity)
          _ ≤ 64 * (Dm * Cm * E) * W := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2k hP0) hW0
          _ = 64 * (Dm * Cm) * W * E := by ring
      have t2 : |(-T.lam) * bondDeriv (Rm i i) V c X| ≤ |T.lam| * (Cm * E) := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul_of_nonneg_left (hone i hi') (abs_nonneg _)
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ 64 * (Dm * Cm) * W * E + |T.lam| * (Cm * E) := add_le_add t1 t2
        _ = _ := by ring
    have hB0 : 0 ≤ (64 * (Dm * Cm) * W + |T.lam| * Cm) * E := by positivity
    have hcY : (((Finset.univ.filter (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y)).card : ℕ) : ℝ) ≤
        12 * (T.L : ℝ) ^ 4 := by exact_mod_cast hcard Y
    calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y),
          (64 * (Dm * Cm) * W + |T.lam| * Cm) * E := Finset.sum_le_sum hterm
      _ = ((Finset.univ.filter (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y)).card : ℝ) *
          ((64 * (Dm * Cm) * W + |T.lam| * Cm) * E) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 12 * (T.L : ℝ) ^ 4 * ((64 * (Dm * Cm) * W + |T.lam| * Cm) * E) :=
        mul_le_mul_of_nonneg_right hcY hB0
      _ = _ := by ring
  have s1 : bondDeriv (fun V' => ∫ τ in (0 : ℝ)..1, hessianCellShare T.a T.ρA T.lam Y V' τ) V c X =
      ∫ v in (0 : ℝ)..1, bondDeriv (fun V' => hessianCellShare T.a T.ρA T.lam Y V' v) V c X := by
    show iteratedFDeriv ℝ k (fun p => ∫ v in (0 : ℝ)..1, Af (v, p)) 0 _ = _
    rw [hrl.iteratedFDeriv_eq _ 0 k _ hI1, hI2 _ (by simp)]
    refine intervalIntegral.integral_congr fun v hv => ?_
    have hv' : v ∈ Icc (0 : ℝ) 1 := by
      rwa [uIcc_of_le zero_le_one] at hv
    have hsm : ContDiffAt ℝ (k : WithTop ℕ∞) (fun p => Af (v, p)) 0 :=
      ContDiffAt.comp (g := Af) (f := fun p : Fin k → ℝ => (v, p)) (0 : Fin k → ℝ) (hAf v hv')
        (contDiff_const.prodMk contDiff_id).contDiffAt
    exact (hrl.iteratedFDeriv_eq _ 0 k _ hsm).symm
  rw [s1]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun v => bondDeriv (fun V' => hessianCellShare T.a T.ρA T.lam Y V' v) V c X)
    (C := 12 * (T.L : ℝ) ^ 4 * (64 * (Dm * Cm) * W + |T.lam| * Cm) * E) (fun v hv => by
      rw [uIoc_of_le zero_le_one] at hv
      exact key v ⟨hv.1.le, hv.2⟩)
  simpa using hb
end YangMills.Construction.ReferenceDensity
end
