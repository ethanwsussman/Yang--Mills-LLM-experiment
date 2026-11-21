import YangMills.Construction.RunningCouplingSlope.HaarDensityAtTheLeastFieldHasKernelsProof
import YangMills.Construction.RunningCouplingSlope.HessianAtTheLeastFieldHasKernels
import YangMills.Construction.RunningCouplingSlope.ResolventAtTheLeastFieldHasKernels
import YangMills.Construction.RunningCouplingSlope.TraceAtTheLeastFieldHasKernels
import YangMills.Construction.SummableBoundsOfTheFlow.BondsOfACellAreFew
import YangMills.Construction.SummableBoundsOfTheFlow.IntegralOfASmoothFamily
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open Set
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation IteratedDerivative ReferenceDensity
namespace RunningCouplingSlope
variable {F : BlockFrame}
section Distances
private theorem cellSupDist_triangle (x y z : F.Cell) :
    cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
private theorem cellSupDist_le_diameter {P : Finset F.Cell} {x y : F.Cell} (hx : x ∈ P) (hy : y ∈ P) :
    cellSupDist x y ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
private theorem cellSetDiameter_le {P : Finset F.Cell} {m : ℕ}
    (h : ∀ x ∈ P, ∀ y ∈ P, cellSupDist x y ≤ m) : cellSetDiameter P ≤ m :=
  Finset.sup_le fun x hx => Finset.sup_le fun y hy => h x hx y hy
private theorem cellSetDiameter_le_add_of_cover {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (A B : List (Fin k)) (Y z : F.Cell) (hAB : ∀ l, l ∈ A ∨ l ∈ B) :
    cellSetDiameter ({Y} ∪ topBondCells c) ≤
      cellSetDiameter ({Y, z} ∪ topBondCells (restrictToList c A)) +
        cellSetDiameter ({z, Y} ∪ topBondCells (restrictToList c B)) := by
  set P₁ := ({Y, z} ∪ topBondCells (restrictToList c A) : Finset F.Cell)
  set P₂ := ({z, Y} ∪ topBondCells (restrictToList c B) : Finset F.Cell)
  have hY₁ : Y ∈ P₁ := by simp [P₁]
  have hY₂ : Y ∈ P₂ := by simp [P₂]
  have hw : ∀ w ∈ ({Y} ∪ topBondCells c : Finset F.Cell), w ∈ P₁ ∨ w ∈ P₂ := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · rw [Finset.mem_singleton.1 h]
      exact Or.inl hY₁
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 h
      rcases hAB l with hl | hl
      · left
        obtain ⟨i, hi, e⟩ := List.getElem_of_mem hl
        refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩)
        simp [restrictToList, e]
      · right
        obtain ⟨i, hi, e⟩ := List.getElem_of_mem hl
        refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩)
        simp [restrictToList, e]
  refine cellSetDiameter_le fun x hx y hy => ?_
  rcases hw x hx with h1 | h1 <;> rcases hw y hy with h2 | h2
  · exact (cellSupDist_le_diameter h1 h2).trans (Nat.le_add_right _ _)
  · exact (cellSupDist_triangle x Y y).trans
      (Nat.add_le_add (cellSupDist_le_diameter h1 hY₁) (cellSupDist_le_diameter hY₂ h2))
  · have := (cellSupDist_triangle x Y y).trans
      (Nat.add_le_add (cellSupDist_le_diameter h1 hY₂) (cellSupDist_le_diameter hY₁ h2))
    omega
  · exact (cellSupDist_le_diameter h1 h2).trans (Nat.le_add_left _ _)
abbrev _root_.YangMills.SharedProofs.p23886 := @cellSetDiameter_le_add_of_cover
end Distances
section Matrices
variable {ι P : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup P] [NormedSpace ℝ P]
private theorem det_contDiffAt (N : P → Matrix ι ι ℝ) (p₀ : P) (n : WithTop ℕ∞)
    (h : ∀ i j, ContDiffAt ℝ n (fun p => N p i j) p₀) : ContDiffAt ℝ n (fun p => (N p).det) p₀ := by
  simp only [Matrix.det_apply']
  refine ContDiffAt.sum fun σ _ => ?_
  exact contDiffAt_const.mul (contDiffAt_prod fun i _ => h _ _)
private theorem inv_apply_contDiffAt (N : P → Matrix ι ι ℝ) (p₀ : P) (n : WithTop ℕ∞)
    (h : ∀ i j, ContDiffAt ℝ n (fun p => N p i j) p₀) (hd : (N p₀).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ n (fun p => (N p)⁻¹ i j) p₀ := by
  have e : (fun p => (N p)⁻¹ i j) = fun p => ((N p).det)⁻¹ * (N p).adjugate i j := by
    funext p
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  rw [e]
  refine (ContDiffAt.inv (det_contDiffAt N p₀ n h) hd).mul ?_
  simp only [Matrix.adjugate_apply]
  refine det_contDiffAt _ p₀ n fun a b => ?_
  by_cases hab : a = j
  · subst hab
    simp only [Matrix.updateRow_self]
    exact contDiffAt_const
  · simp only [Matrix.updateRow_ne hab]
    exact h a b
abbrev _root_.YangMills.SharedProofs.p5216 := @inv_apply_contDiffAt
end Matrices
private theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
theorem traceKernelBounds_holds (hR : MinimizerResolventDecay)
    (hH : hessianDerivBoundStatement) (hI : IntervalIntegralSmoothFamily)
    (hA : DerivAlongRulesHold) (hP : BondDerivSumProductRules)
    (hB : Estimates.cellBondsCardStatement) (hW : CellCounting.ExpDecaySumBounded) :
    TraceKernelBounds := by
  intro a L cn ha hL hL40 hcn
  obtain ⟨r₃, Cr, hr₃, hCr, gD, gR⟩ := hR a L cn ha hL hL40 hcn
  obtain ⟨D, hDpos, gH⟩ := hH a L cn ha hL hL40 hcn
  have hδ : 0 < cn.δ₁ := hcn.positivity.1
  have hL0 : 0 < L := hL.pos
  set κ : ℝ := min r₃ (cn.δ₁ / 4) / 2 ^ 8 with hκd
  have hκ0 : 0 < κ := by
    have : 0 < min r₃ (cn.δ₁ / 4) := lt_min hr₃ (by positivity)
    positivity
  have hκ₁ : 2 ^ 8 * κ ≤ r₃ := by
    have : 2 ^ 8 * κ = min r₃ (cn.δ₁ / 4) := by
      rw [hκd]
      ring
    rw [this]
    exact min_le_left _ _
  have hrate : 2 ^ 8 * κ ≤ cn.δ₁ / 4 := by
    have : 2 ^ 8 * κ = min r₃ (cn.δ₁ / 4) := by
      rw [hκd]
      ring
    rw [this]
    exact min_le_right _ _
  obtain ⟨W, hW0, hWb⟩ := hW (12 * L ^ 4) (2 ^ 7 * κ) (by positivity)
  set Dm : ℝ := ∑ a ∈ Finset.range 7, D a with hDm
  set Cm : ℝ := ∑ a ∈ Finset.range 7, |Cr a| with hCm
  have hDa : ∀ a, a ≤ 6 → D a ≤ Dm := fun a ha =>
    Finset.single_le_sum (f := fun b => D b) (fun b _ => (hDpos b).le)
      (Finset.mem_range.2 (by omega))
  have hCa : ∀ a, a ≤ 6 → |Cr a| ≤ Cm := fun a ha =>
    Finset.single_le_sum (f := fun b => |Cr b|) (fun b _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  have hDm0 : 0 ≤ Dm := Finset.sum_nonneg fun b _ => (hDpos b).le
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun b _ => abs_nonneg _
  refine ⟨2 ^ 7 * κ, 12 * (L : ℝ) ^ 4 * (64 * (Dm * Cm) * W + |cn.lam| * Cm) + 1, by positivity, by positivity, ?_⟩
  intro F s V Y k c X hF hs hV hk hX
  classical
  have hFL := hF.1
  obtain ⟨n, hn64, hside⟩ := hF.2
  have hside2 : ∀ i, 2 ≤ F.extent i := by
    intro i
    rw [hside i]
    omega
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hcardB := hB F hodd hside2
  have hcard : ∀ z : F.Cell, (Finset.univ.filter fun j : ChartCoord F => enclosingCell j.1.1.1 = z).card ≤
      12 * L ^ 4 := by
    intro z
    have e : (Finset.univ.filter fun j : ChartCoord F => enclosingCell j.1.1.1 = z) =
        (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z) ×ˢ
          Finset.univ := by
      ext j
      simp
    rw [e, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have h1 := hcardB z
    rw [hFL] at h1
    convert Nat.mul_le_mul_right 3 h1 using 1
    ring
  have hWj : ∀ z : F.Cell, ∑ j : ChartCoord F,
      Real.exp (-(2 ^ 7 * κ * (cellSupDist (enclosingCell j.1.1.1) z : ℝ))) ≤ W :=
    hWb F (ChartCoord F) (fun j => enclosingCell j.1.1.1) (fun z => by convert hcard z)
  have hdet : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → (τ • chartedHessian a cn.ρA V 0 +
      (1 - τ) • cn.lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).det ≠ 0 := fun τ h0 h1 =>
    gD F s V τ hF hs hV h0 h1
  let Msf : (Fin k → ℝ) → Matrix (ChartCoord F) (ChartCoord F) ℝ := fun σ =>
    chartedHessian a cn.ρA (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ) V) 0
  have hMs : ∀ (i j : ChartCoord F) (m : ℕ), ContDiffAt ℝ (m : WithTop ℕ∞) (fun σ => Msf σ i j) 0 :=
    fun i j m => (gH F s V i j k c X hF hs hV hX).1 m
  let Nm : ℝ × (Fin k → ℝ) → Matrix (ChartCoord F) (ChartCoord F) ℝ := fun p =>
    p.1 • Msf p.2 + (1 - p.1) • cn.lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)
  have hMp : ∀ (v : ℝ) (i j : ChartCoord F), ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun p : ℝ × (Fin k → ℝ) => Msf p.2 i j) (v, 0) := fun v i j =>
    ContDiffAt.comp (v, (0 : Fin k → ℝ)) (hMs i j k) contDiffAt_snd
  have hNs : ∀ (v : ℝ) (i j : ChartCoord F), ContDiffAt ℝ (k : WithTop ℕ∞) (fun p => Nm p i j) (v, 0) := by
    intro v i j
    have e : (fun p => Nm p i j) = fun p : ℝ × (Fin k → ℝ) => p.1 * Msf p.2 i j +
        (1 - p.1) * (cn.lam * (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ) i j) := by
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
    inv_apply_contDiffAt Nm _ _ (hNs v) (hNdet v hv) i j
  have hform : ∀ (V' : F.GaugeField F.top) (τ : ℝ), hessianCellShare a cn.ρA cn.lam Y V' τ =
      ∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then
        ((∑ j, chartedHessian a cn.ρA V' 0 i j * hessianResolvent a cn.ρA cn.lam τ V' j i) -
          cn.lam * hessianResolvent a cn.ρA cn.lam τ V' i i) else 0 := by
    intro V' τ
    unfold hessianCellShare
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : enclosingCell i.1.1.1 = Y
    · rw [if_pos h, if_pos h, Matrix.sub_mul, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]
      rfl
    · rw [if_neg h, if_neg h]
  let Af : ℝ × (Fin k → ℝ) → ℝ := fun p =>
    hessianCellShare a cn.ρA cn.lam Y (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X p.2) V) p.1
  have hAf : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (k : WithTop ℕ∞) Af (v, 0) := by
    intro v hv
    have e : Af = fun p => ∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then
        ((∑ j, Msf p.2 i j * (Nm p)⁻¹ j i) - cn.lam * (Nm p)⁻¹ i i) else 0 := by
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
  set E : ℝ := Real.exp (-(2 ^ 7 * κ * S)) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have key : ∀ v ∈ Icc (0 : ℝ) 1, |bondDeriv (fun V' => hessianCellShare a cn.ρA cn.lam Y V' v) V c X| ≤
      12 * (L : ℝ) ^ 4 * (64 * (Dm * Cm) * W + |cn.lam| * Cm) * E := by
    intro v hv
    let Gm : ChartCoord F → ChartCoord F → F.GaugeField F.top → ℝ := fun i j V' =>
      chartedHessian a cn.ρA V' 0 i j
    let Rm : ChartCoord F → ChartCoord F → F.GaugeField F.top → ℝ := fun i j V' =>
      hessianResolvent a cn.ρA cn.lam v V' i j
    obtain ⟨hsum, hsmul, hprod⟩ := hP F V k c X
    have sG : ∀ i j, ContDiffAlongBonds k (Gm i j) V c X := fun i j => hMs i j k
    have sR : ∀ i j, ContDiffAlongBonds k (Rm i j) V c X := fun i j =>
      ((gR F s V v i j k c X hF hs hV hv.1 hv.2 hk hX).1).of_le (by exact_mod_cast hk)
    have sGR : ∀ i j, ContDiffAlongBonds k (fun V' => Gm i j V' * Rm j i V') V c X := fun i j =>
      ContDiffAt.mul (sG i j) (sR j i)
    have sIn : ∀ i, ContDiffAlongBonds k (fun V' => ∑ j, Gm i j V' * Rm j i V') V c X := fun i =>
      ContDiffAt.sum fun j _ => sGR i j
    have sLam : ∀ i, ContDiffAlongBonds k (fun V' => (-cn.lam) * Rm i i V') V c X := fun i =>
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
      Real.exp (-(2 ^ 7 * κ * (cellSupDist (enclosingCell j.1.1.1) Y : ℝ)))
    have hprodb : ∀ i j, enclosingCell i.1.1.1 = Y →
        |bondDeriv (fun V' => Gm i j V' * Rm j i V') V c X| ≤ 2 ^ k * (Dm * Cm * E * Ej j) := by
      intro i j hi
      refine hprod _ _ _ (sG i j) (sR j i) fun A B hAB hcov => ?_
      have xA : AreUnitVectors (restrictToList X A) := fun l => hX _
      have xB : AreUnitVectors (restrictToList X B) := fun l => hX _
      have hA6 : A.length ≤ 6 := by omega
      have hB6 : B.length ≤ 6 := by omega
      have b1 := (gH F s V i j A.length (restrictToList c A) (restrictToList X A) hF hs hV xA).2
      have b2 := (gR F s V v j i B.length (restrictToList c B) (restrictToList X B) hF hs hV hv.1 hv.2 hB6
        xB).2
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
          Dm * Real.exp (-(2 ^ 8 * κ * s₁)) := by
        refine b1.trans (mul_le_mul (hDa _ hA6) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hDm0)
        have := mul_le_mul_of_nonneg_right hrate hs₁0
        linarith
      have c2 : |bondDeriv (Rm j i) V (restrictToList c B) (restrictToList X B)| ≤
          Cm * Real.exp (-(2 ^ 8 * κ * s₂)) :=
        b2.trans (mul_le_mul ((le_abs_self _).trans (hCa _ hB6)) (Real.exp_le_exp.2 (by
          have := mul_le_mul_of_nonneg_right hκ₁ hs₂0
          linarith)) (Real.exp_pos _).le hCm0)
      have hexp : Real.exp (-(2 ^ 8 * κ * s₁)) * Real.exp (-(2 ^ 8 * κ * s₂)) ≤ E * Ej j := by
        show _ ≤ Real.exp _ * Real.exp _
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have a1 := mul_le_mul_of_nonneg_left hSle (by positivity : (0 : ℝ) ≤ 2 ^ 7 * κ)
        have a2 := mul_le_mul_of_nonneg_left hdle (by positivity : (0 : ℝ) ≤ 2 ^ 7 * κ)
        linarith
      calc _ ≤ (Dm * Real.exp (-(2 ^ 8 * κ * s₁))) * (Cm * Real.exp (-(2 ^ 8 * κ * s₂))) :=
            mul_le_mul c1 c2 (abs_nonneg _) (by positivity)
        _ = Dm * Cm * (Real.exp (-(2 ^ 8 * κ * s₁)) * Real.exp (-(2 ^ 8 * κ * s₂))) := by ring
        _ ≤ Dm * Cm * (E * Ej j) := mul_le_mul_of_nonneg_left hexp (mul_nonneg hDm0 hCm0)
        _ = Dm * Cm * E * Ej j := by ring
    have hone : ∀ i, enclosingCell i.1.1.1 = Y → |bondDeriv (Rm i i) V c X| ≤ Cm * E := by
      intro i hi
      have b := (gR F s V v i i k c X hF hs hV hv.1 hv.2 hk hX).2
      rw [hi, Finset.pair_eq_singleton] at b
      refine b.trans (mul_le_mul ((le_abs_self _).trans (hCa _ hk)) (Real.exp_le_exp.2 ?_)
        (Real.exp_pos _).le hCm0)
      have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ κ * S := mul_nonneg hκ0.le hS0
      have h2 := mul_le_mul_of_nonneg_right hκ₁ hS0
      linarith
    have hfun : (fun V' => hessianCellShare a cn.ρA cn.lam Y V' v) = fun V' =>
        ∑ i ∈ Finset.univ.filter (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y),
          ((∑ j, Gm i j V' * Rm j i V') + (-cn.lam) * Rm i i V') := by
      funext V'
      rw [hform, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : enclosingCell i.1.1.1 = Y
      · rw [if_pos h, if_pos h]
        simp only [Gm, Rm]
        ring
      · rw [if_neg h, if_neg h]
    have sT : ∀ i, ContDiffAlongBonds k
        (fun V' => (∑ j, Gm i j V' * Rm j i V') + (-cn.lam) * Rm i i V') V c X :=
      fun i => ContDiffAt.add (sIn i) (sLam i)
    rw [hfun, hsum _ _ _ (fun i _ => sT i)]
    have h2k : (2 : ℝ) ^ k ≤ 64 := by
      have : (2 : ℝ) ^ k ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) hk
      linarith
    have hterm : ∀ i ∈ Finset.univ.filter (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y),
        |bondDeriv (fun V' => (∑ j, Gm i j V' * Rm j i V') + (-cn.lam) * Rm i i V') V c X| ≤
          (64 * (Dm * Cm) * W + |cn.lam| * Cm) * E := by
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
      have t2 : |(-cn.lam) * bondDeriv (Rm i i) V c X| ≤ |cn.lam| * (Cm * E) := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul_of_nonneg_left (hone i hi') (abs_nonneg _)
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ 64 * (Dm * Cm) * W * E + |cn.lam| * (Cm * E) := add_le_add t1 t2
        _ = _ := by ring
    have hB0 : 0 ≤ (64 * (Dm * Cm) * W + |cn.lam| * Cm) * E := by positivity
    have hcY : (((Finset.univ.filter (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y)).card : ℕ) : ℝ) ≤
        12 * (L : ℝ) ^ 4 := by exact_mod_cast hcard Y
    calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y),
          (64 * (Dm * Cm) * W + |cn.lam| * Cm) * E := Finset.sum_le_sum hterm
      _ = ((Finset.univ.filter (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y)).card : ℝ) *
          ((64 * (Dm * Cm) * W + |cn.lam| * Cm) * E) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 12 * (L : ℝ) ^ 4 * ((64 * (Dm * Cm) * W + |cn.lam| * Cm) * E) :=
        mul_le_mul_of_nonneg_right hcY hB0
      _ = _ := by ring
  have s1 : bondDeriv (fun V' => ∫ τ in (0 : ℝ)..1, hessianCellShare a cn.ρA cn.lam Y V' τ) V c X =
      ∫ v in (0 : ℝ)..1, bondDeriv (fun V' => hessianCellShare a cn.ρA cn.lam Y V' v) V c X := by
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
    (f := fun v => bondDeriv (fun V' => hessianCellShare a cn.ρA cn.lam Y V' v) V c X)
    (C := 12 * (L : ℝ) ^ 4 * (64 * (Dm * Cm) * W + |cn.lam| * Cm) * E) (fun v hv => by
      rw [uIoc_of_le zero_le_one] at hv
      exact key v ⟨hv.1.le, hv.2⟩)
  have hb' : |∫ v in (0 : ℝ)..1, bondDeriv (fun V' => hessianCellShare a cn.ρA cn.lam Y V' v) V c X| ≤
      12 * (L : ℝ) ^ 4 * (64 * (Dm * Cm) * W + |cn.lam| * Cm) * E := by
    simpa using hb
  exact hb'.trans (mul_le_mul_of_nonneg_right (by linarith) hE0)
end RunningCouplingSlope
end YangMills.Construction
end
