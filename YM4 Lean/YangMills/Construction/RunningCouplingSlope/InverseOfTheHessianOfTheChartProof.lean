import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbers
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyAboutAChartPoint
import YangMills.Construction.LawInAState.DecayOverATorusProof
import YangMills.Construction.RunningCouplingSlope.InverseOfTheHessianOfTheChart
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames RenormalizationStepParameters ReferenceDensity
namespace RunningCouplingSlope
namespace ChartHessianInverse
section Calculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
private theorem differentiableAt_fderiv_apply {f : P → ℝ} (hf : ContDiffAt ℝ 3 f 0) (v : P) :
    DifferentiableAt ℝ (fun ζ => fderiv ℝ f ζ v) 0 := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  exact (h2.differentiableAt (by norm_num)).clm_apply (differentiableAt_const v)
private theorem deriv_deriv_line {f : P → ℝ} (hf : ContDiffAt ℝ 3 f 0) (u : P) :
    deriv (deriv fun τ : ℝ => f (τ • u)) 0 = fderiv ℝ (fun ζ => fderiv ℝ f ζ u) 0 u := by
  have hc : ContinuousAt (fun s : ℝ => s • u) 0 := by fun_prop
  have hev : ∀ᶠ s : ℝ in 𝓝 0, ContDiffAt ℝ 3 f (s • u) := by
    have h1 : ∀ᶠ ζ in 𝓝 ((fun s : ℝ => s • u) 0), ContDiffAt ℝ 3 f ζ := by
      simp only [zero_smul]
      exact hf.eventually (by simp)
    exact hc.eventually h1
  have hl : ∀ τ : ℝ, HasDerivAt (fun s : ℝ => s • u) u τ := fun τ => by
    simpa using (hasDerivAt_id τ).smul_const u
  have hd : (deriv fun τ : ℝ => f (τ • u)) =ᶠ[𝓝 0] fun τ => fderiv ℝ f (τ • u) u := by
    filter_upwards [hev] with τ hτ
    have h1 : DifferentiableAt ℝ f ((fun s : ℝ => s • u) τ) := hτ.differentiableAt (by norm_num)
    exact (h1.hasFDerivAt.comp_hasDerivAt τ (hl τ)).deriv
  rw [hd.deriv_eq]
  have h4 : DifferentiableAt ℝ (fun ζ => fderiv ℝ f ζ u) ((fun s : ℝ => s • u) 0) := by
    simpa using differentiableAt_fderiv_apply hf u
  have h5 := (h4.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hl 0)).deriv
  simpa [Function.comp_def] using h5
abbrev _root_.YangMills.SharedProofs.p4878 := @deriv_deriv_line
private theorem fderiv_fderiv_apply_eq {f : P → ℝ} (hf : ContDiffAt ℝ 3 f 0) (u v : P) :
    fderiv ℝ (fun ζ => fderiv ℝ f ζ v) 0 u = fderiv ℝ (fderiv ℝ f) 0 u v := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  have h3 := ((h2.differentiableAt (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const v (0 : P))).fderiv
  rw [h3]
  simp
abbrev _root_.YangMills.SharedProofs.p13960 := @fderiv_fderiv_apply_eq
private theorem fderiv_fderiv_symm {f : P → ℝ} (hf : ContDiffAt ℝ 3 f 0) (u v : P) :
    fderiv ℝ (fderiv ℝ f) 0 u v = fderiv ℝ (fderiv ℝ f) 0 v u :=
  (hf.isSymmSndFDerivAt (by simp; norm_num)).eq u v
end Calculus
section Matrices
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem abs_inv_le_of_weighted_rows {lam r : ℝ} (hlam : 0 < lam) (d : ι → ι → ℝ) (A : Matrix ι ι ℝ)
    (hsymm : ∀ a b, A a b = A b a) (hd0 : ∀ a, d a a = 0)
    (hds : ∀ a b, d a b = d b a) (hdt : ∀ a b c, d a c ≤ d a b + d b c) (hr : 0 ≤ r)
    (hfloor : ∀ v : ι → ℝ, lam * ∑ a, v a ^ 2 ≤ ∑ a, ∑ b, v a * A a b * v b)
    (hrow : ∀ a, ∑ b, |A a b| * (Real.exp (r * d a b) - 1) ≤ lam / 2)
    (hinv : IsUnit A) (i j : ι) :
    |A⁻¹ i j| ≤ 2 / lam * Real.exp (-(r * d i j)) := by
  set φ : ι → ℝ := fun x => r * d x j with hφ
  set g : ι → ℝ := fun x => A⁻¹ x j with hg
  have hAg : ∀ x, ∑ y, A x y * g y = if x = j then 1 else 0 := by
    intro x
    have hh : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hinv)
    have := congrFun (congrFun hh x) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  set v : ι → ℝ := fun x => Real.exp (φ x) * g x with hv
  have hlip : ∀ x y, |φ x - φ y| ≤ r * d x y := by
    intro x y
    have h1 := hdt x y j
    have h2 := hdt y x j
    rw [hds y x] at h2
    simp only [hφ]
    rw [abs_le]
    constructor <;> nlinarith
  have hE : ∀ x y, |Real.exp (φ x - φ y) - 1| ≤ Real.exp (r * d x y) - 1 := by
    intro x y
    have h1 := hlip x y
    have hmono := abs_le.1 h1
    rw [abs_le]
    have h2 : Real.exp (φ x - φ y) ≤ Real.exp (r * d x y) := Real.exp_le_exp.2 hmono.2
    have h3 : Real.exp (-(r * d x y)) ≤ Real.exp (φ x - φ y) := Real.exp_le_exp.2 hmono.1
    have h4 : 2 ≤ Real.exp (r * d x y) + Real.exp (-(r * d x y)) := by
      have := Real.add_one_le_exp (r * d x y)
      have h5 := Real.add_one_le_exp (-(r * d x y))
      linarith
    constructor <;> linarith
  have hform : ∑ a, ∑ b, v a * (A a b * Real.exp (φ a - φ b)) * v b = v j * Real.exp (φ j) := by
    have h1 : ∀ a, ∑ b, v a * (A a b * Real.exp (φ a - φ b)) * v b =
        v a * Real.exp (φ a) * ∑ b, A a b * g b := by
      intro a
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : Real.exp (φ a - φ b) * Real.exp (φ b) = Real.exp (φ a) := by
        rw [← Real.exp_add, sub_add_cancel]
      simp only [hv]
      calc v a * (A a b * Real.exp (φ a - φ b)) * (Real.exp (φ b) * g b)
          = v a * (Real.exp (φ a - φ b) * Real.exp (φ b)) * (A a b * g b) := by
            simp only [hv]; ring
        _ = _ := by rw [this]
    simp only [h1, hAg]
    simp
  have hφj : φ j = 0 := by simp [hφ, hd0]
  have hsplit : ∑ a, ∑ b, v a * (A a b * Real.exp (φ a - φ b)) * v b =
      ∑ a, ∑ b, v a * A a b * v b +
        ∑ a, ∑ b, v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have herr : |∑ a, ∑ b, v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b| ≤
      lam / 2 * ∑ a, v a ^ 2 := by
    have hterm : ∀ a b, |v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b| ≤
        (v a ^ 2 + v b ^ 2) / 2 * (|A a b| * (Real.exp (r * d a b) - 1)) := by
      intro a b
      have h1 : |v a * v b| ≤ (v a ^ 2 + v b ^ 2) / 2 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (v a - v b), sq_nonneg (v a + v b)]
      have h2 : |A a b * (Real.exp (φ a - φ b) - 1)| ≤
          |A a b| * (Real.exp (r * d a b) - 1) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hE a b) (abs_nonneg _)
      calc |v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b|
          = |v a * v b| * |A a b * (Real.exp (φ a - φ b) - 1)| := by
            rw [← abs_mul]; congr 1; ring
        _ ≤ _ := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    set w : ι → ι → ℝ := fun a b => |A a b| * (Real.exp (r * d a b) - 1) with hw
    have hws : ∀ a b, w a b = w b a := by
      intro a b
      simp only [hw]
      rw [hsymm a b, hds a b]
    have hwrow : ∀ a, ∑ b, w a b ≤ lam / 2 := hrow
    calc |∑ a, ∑ b, v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b|
        ≤ ∑ a, ∑ b, |v a * (A a b * (Real.exp (φ a - φ b) - 1)) * v b| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          exact Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, (v a ^ 2 + v b ^ 2) / 2 * w a b :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
      _ = ∑ a, ∑ b, v a ^ 2 * w a b := by
          have h1 : ∑ a, ∑ b, v b ^ 2 * w a b = ∑ a, ∑ b, v a ^ 2 * w a b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [hws]
          have h2 : ∑ a, ∑ b, (v a ^ 2 + v b ^ 2) / 2 * w a b =
              (∑ a, ∑ b, v a ^ 2 * w a b + ∑ a, ∑ b, v b ^ 2 * w a b) / 2 := by
            rw [← Finset.sum_add_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Finset.sum_add_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl fun b _ => ?_
            ring
          rw [h2, h1]
          ring
      _ = ∑ a, v a ^ 2 * ∑ b, w a b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ a, v a ^ 2 * (lam / 2) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hwrow a) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hlow : lam / 2 * ∑ a, v a ^ 2 ≤ v j := by
    have h1 := hfloor v
    have h2 := (abs_le.1 herr).1
    have h3 := hform
    rw [hsplit, hφj, Real.exp_zero, mul_one] at h3
    linarith
  have hvv : v i ^ 2 ≤ ∑ a, v a ^ 2 :=
    Finset.single_le_sum (f := fun a => v a ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hvj2 : v j ^ 2 ≤ ∑ a, v a ^ 2 :=
    Finset.single_le_sum (f := fun a => v a ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  set s := ∑ a, v a ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs1 : lam / 2 * s ≤ Real.sqrt s := by
    refine hlow.trans ?_
    exact (le_abs_self _).trans (Real.abs_le_sqrt hvj2)
  have hs2 : Real.sqrt s ≤ 2 / lam := by
    by_cases hz : Real.sqrt s = 0
    · rw [hz]; positivity
    · have hpos : 0 < Real.sqrt s := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      have h1 : lam / 2 * (Real.sqrt s * Real.sqrt s) ≤ Real.sqrt s := by
        rw [Real.mul_self_sqrt hs0]; exact hs1
      rw [le_div_iff₀ hlam]
      have h2 : lam / 2 * Real.sqrt s ≤ 1 := by
        by_contra hc
        rw [not_le] at hc
        nlinarith
      linarith
  have hvi : |v i| ≤ 2 / lam := (Real.abs_le_sqrt hvv).trans hs2
  have hgi : |g i| = Real.exp (-(φ i)) * |v i| := by
    simp only [hv]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
    simp
  have : A⁻¹ i j = g i := rfl
  rw [this, hgi, mul_comm]
  exact mul_le_mul_of_nonneg_right hvi (Real.exp_pos _).le
private theorem isUnit_of_coercive {lam : ℝ} (hlam : 0 < lam) (A : Matrix ι ι ℝ)
    (hfloor : ∀ v : ι → ℝ, lam * ∑ a, v a ^ 2 ≤ ∑ a, ∑ b, v a * A a b * v b) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := hfloor v
  have h2 : ∑ a, ∑ b, v a * A a b * v b = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have h3 : ∑ b, A a b * v b = 0 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hAv a
    calc ∑ b, v a * A a b * v b = v a * ∑ b, A a b * v b := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [h3, mul_zero]
  rw [h2] at h1
  have h3 : ∑ a, v a ^ 2 ≤ 0 := by
    by_contra h
    rw [not_le] at h
    have := mul_pos hlam h
    linarith
  refine hv (funext fun a => ?_)
  have h4 : v a ^ 2 ≤ ∑ a, v a ^ 2 :=
    Finset.single_le_sum (f := fun a => v a ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm (h4.trans h3) (sq_nonneg _))
end Matrices
section Cells
variable {F : BlockFrame}
private theorem supDist_self (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
private theorem supDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
private theorem supDist_triangle (x y z : F.Cell) :
    cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
private def expLineSum (δ : ℝ) : ℝ := ∑' t : ℤ, Real.exp (-(δ * |(t : ℝ)|))
private theorem expLineSum_nonneg (δ : ℝ) : 0 ≤ expLineSum δ :=
  tsum_nonneg fun _ => (Real.exp_pos _).le
private theorem expLineSum_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable fun t : ℤ => Real.exp (-(δ * |(t : ℝ)|)) := by apply _root_.YangMills.SharedProofs.p3695 <;> assumption
private theorem sum_zmod_exp_le {m : ℕ} [NeZero m] {δ : ℝ} (hδ : 0 < δ) (y₀ : ZMod m) :
    ∑ y : ZMod m, Real.exp (-(δ * |(((y₀ - y).valMinAbs : ℤ) : ℝ)|)) ≤ expLineSum δ := by
  have hinj : Function.Injective fun y : ZMod m => (y₀ - y).valMinAbs := by
    intro u v h
    have h' : (((y₀ - u).valMinAbs : ℤ) : ZMod m) = (((y₀ - v).valMinAbs : ℤ) : ZMod m) := by
      simpa using congrArg (fun t : ℤ => (t : ZMod m)) h
    rw [ZMod.coe_valMinAbs, ZMod.coe_valMinAbs] at h'
    exact sub_right_injective h'
  have := (expLineSum_summable hδ).sum_le_tsum (Finset.univ.image fun y : ZMod m => (y₀ - y).valMinAbs)
    (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_image (fun u _ v _ h => hinj h)] at this
  exact this
private theorem mem_finiteCells_of_ne (hF : ∀ i, F.period F.top i ≠ 0) (z : F.Cell) : z ∈ finiteCells F := by
  have : ∀ i, NeZero (F.period F.top i) := fun i => ⟨hF i⟩
  have : Finite F.Cell := inferInstance
  simp [finiteCells, this]
private theorem sum_cells_exp_le (hF : ∀ i, F.period F.top i ≠ 0) {δ : ℝ} (hδ : 0 < δ) (y₀ : F.Cell) :
    ∑ z ∈ finiteCells F, Real.exp (-(4 * δ * (cellSupDist y₀ z : ℝ))) ≤ expLineSum δ ^ 4 := by
  have : ∀ i, NeZero (F.period F.top i) := fun i => ⟨hF i⟩
  have hS : finiteCells F = Finset.univ := by
    ext z
    simp [mem_finiteCells_of_ne hF z]
  rw [hS]
  have hterm : ∀ z : F.Cell, Real.exp (-(4 * δ * (cellSupDist y₀ z : ℝ))) ≤
      ∏ i, Real.exp (-(δ * |(((y₀ i - z i).valMinAbs : ℤ) : ℝ)|)) := by
    intro z
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, neg_le_neg_iff,
      show 4 * δ * (cellSupDist y₀ z : ℝ) = δ * (4 * (cellSupDist y₀ z : ℝ)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hδ.le
    have h1 : ∀ i, |(((y₀ i - z i).valMinAbs : ℤ) : ℝ)| ≤ (cellSupDist y₀ z : ℝ) := by
      intro i
      have : ((y₀ i - z i).valMinAbs).natAbs ≤ cellSupDist y₀ z :=
        Finset.le_sup (f := fun i => ((y₀ i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      exact_mod_cast this
    calc ∑ i, |(((y₀ i - z i).valMinAbs : ℤ) : ℝ)| ≤ ∑ _i : Fin 4, (cellSupDist y₀ z : ℝ) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = 4 * (cellSupDist y₀ z : ℝ) := by simp
  refine (Finset.sum_le_sum fun z _ => hterm z).trans ?_
  have hprod := Finset.prod_univ_sum (fun i : Fin 4 => (Finset.univ : Finset (ZMod (F.period F.top i))))
    (fun i y => Real.exp (-(δ * |(((y₀ i - y).valMinAbs : ℤ) : ℝ)|)))
  rw [Fintype.piFinset_univ] at hprod
  rw [← hprod]
  calc ∏ i : Fin 4, ∑ y : ZMod (F.period F.top i), Real.exp (-(δ * |(((y₀ i - y).valMinAbs : ℤ) : ℝ)|))
      ≤ ∏ _i : Fin 4, expLineSum δ :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
          fun i _ => sum_zmod_exp_le hδ (y₀ i)
    _ = expLineSum δ ^ 4 := by simp
private def chartSumBound (L : ℕ) (ε : ℝ) : ℝ := 12 * ((centredCube L).card : ℝ) * expLineSum (ε / 4) ^ 4
private theorem chartSumBound_nonneg (L : ℕ) (ε : ℝ) : 0 ≤ chartSumBound L ε := by
  have := expLineSum_nonneg (ε / 4)
  unfold chartSumBound
  positivity
private theorem sum_chartCoord_le (hS : SiteDecomposition) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (hF : ∀ i, F.period F.top i ≠ 0) (f : F.Cell → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ e : ChartCoord F, f (enclosingCell e.1.1.1) ≤
      12 * ((centredCube F.blockSide).card : ℝ) * ∑ z ∈ finiteCells F, f z := by
  obtain ⟨-, h2, -, -⟩ := hS F hL hs
  have hsum3 : ∑ e : ChartCoord F, f (enclosingCell e.1.1.1) =
      3 * ∑ b ∈ chordBonds (finiteCells F), f (enclosingCell b.1) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_coe_sort (chordBonds (finiteCells F)) (fun b => f (enclosingCell b.1))]
    norm_num
  rw [hsum3]
  set ψ : F.Site F.depth × Fin 4 → F.Cell × (Fin 4 → ℤ) × Fin 4 :=
    fun b => (enclosingCell b.1, cellOffset b.1, b.2) with hψ
  have hinj : Function.Injective ψ := by
    intro b b' h
    simp only [hψ, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    refine Prod.ext ?_ h₃
    rw [← (h2 b.1).1, ← (h2 b'.1).1, h₁, h₂]
  set g : F.Cell × (Fin 4 → ℤ) × Fin 4 → ℝ := fun p => f p.1 with hg
  have h1 : ∑ b ∈ chordBonds (finiteCells F), f (enclosingCell b.1) =
      ∑ p ∈ (chordBonds (finiteCells F)).image ψ, g p := by
    rw [Finset.sum_image (fun u _ v _ h => hinj h)]
  have hsub : (chordBonds (finiteCells F)).image ψ ⊆
      finiteCells F ×ˢ (centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))) := by
    intro p hp
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hp
    simp only [hψ, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨mem_finiteCells_of_ne hF _, (h2 b.1).2⟩
  have h3 : ∑ p ∈ (chordBonds (finiteCells F)).image ψ, g p ≤
      ∑ p ∈ finiteCells F ×ˢ (centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))), g p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hf _
  have h4 : ∑ p ∈ finiteCells F ×ˢ (centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))), g p =
      4 * ((centredCube F.blockSide).card : ℝ) * ∑ z ∈ finiteCells F, f z := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [hg, Finset.sum_const, Finset.card_product, mul_comm]
  rw [h1]
  calc 3 * ∑ p ∈ (chordBonds (finiteCells F)).image ψ, g p
      ≤ 3 * (4 * ((centredCube F.blockSide).card : ℝ) * ∑ z ∈ finiteCells F, f z) := by
        rw [← h4]; linarith
    _ = _ := by ring
end Cells
section Rates
private theorem exp_mul_exp_sub_one_le {δ r d : ℝ} (hδ : 0 < δ) (hr0 : 0 ≤ r) (hr : r ≤ δ / 2) (hd : 0 ≤ d) :
    Real.exp (-(δ * d)) * (Real.exp (r * d) - 1) ≤ r * (4 / δ) * Real.exp (-(δ / 4 * d)) := by
  have h1 : Real.exp (r * d) - 1 ≤ r * d * Real.exp (r * d) := by
    have h2 := Real.add_one_le_exp (-(r * d))
    have h3 : Real.exp (-(r * d)) * Real.exp (r * d) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (r * d)).le
    rw [h3] at h4
    nlinarith
  have h5 : d ≤ 4 / δ * Real.exp (δ / 4 * d) := by
    have h6 := Real.add_one_le_exp (δ / 4 * d)
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    nlinarith
  have h7 : Real.exp (-(δ * d)) * (Real.exp (δ / 4 * d) * Real.exp (r * d)) ≤
      Real.exp (-(δ / 4 * d)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  calc Real.exp (-(δ * d)) * (Real.exp (r * d) - 1)
      ≤ Real.exp (-(δ * d)) * (r * d * Real.exp (r * d)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ ≤ Real.exp (-(δ * d)) * (r * (4 / δ * Real.exp (δ / 4 * d)) * Real.exp (r * d)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left h5 hr0
    _ = r * (4 / δ) * (Real.exp (-(δ * d)) * (Real.exp (δ / 4 * d) * Real.exp (r * d))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h7 (by positivity)
private def decayRate (δ₂ lam D0 Sv : ℝ) : ℝ := min (δ₂ / 2) (lam * δ₂ / (8 * D0 * (Sv + 1)))
private theorem decayRate_spec {δ₂ lam D0 Sv : ℝ} (hδ : 0 < δ₂) (hlam : 0 < lam) (hD : 0 < D0) (hS : 0 ≤ Sv) :
    0 < decayRate δ₂ lam D0 Sv ∧ decayRate δ₂ lam D0 Sv ≤ δ₂ / 2 ∧
      D0 * (decayRate δ₂ lam D0 Sv * (4 / δ₂)) * Sv ≤ lam / 2 := by
  have hden : 0 < 8 * D0 * (Sv + 1) := by positivity
  have hpos : 0 < decayRate δ₂ lam D0 Sv := lt_min (by positivity) (by positivity)
  refine ⟨hpos, min_le_left _ _, ?_⟩
  set r := decayRate δ₂ lam D0 Sv with hr
  have h1 : r * (8 * D0 * (Sv + 1)) ≤ lam * δ₂ := by
    have : r ≤ lam * δ₂ / (8 * D0 * (Sv + 1)) := min_le_right _ _
    rwa [le_div_iff₀ hden] at this
  have h2 : D0 * (r * (4 / δ₂)) * Sv = 4 * D0 * r * Sv / δ₂ := by
    field_simp
  rw [h2, div_le_iff₀ hδ]
  have h3 : 0 ≤ r * D0 := by positivity
  nlinarith
end Rates
section Frames
variable {F : BlockFrame}
private theorem norm_toImaginary' (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem toImaginary_zero' : toImaginary (0 : BondVector) = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
abbrev _root_.YangMills.SharedProofs.p2840 := @toImaginary_zero'
private theorem stepCoordinates_smul' (τ : ℝ) (U : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (τ • U) x i = τ • stepCoordinates U x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_smul <;> assumption
private theorem stepCoordinates_zero' (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · simp only [dif_pos h, Pi.zero_apply]
    exact toImaginary_zero'
  · simp [dif_neg h]
private def unitVariation (p : ChartCoord F) : StepVariable (finiteCells F) :=
  ColdStepAtMirrorFrames.bondVariation p.1 (EuclideanSpace.single (𝕜 := ℝ) p.2 1)
open Classical in
private theorem unitVariation_apply (p : ChartCoord F) (b : ↥(chordBonds (finiteCells F))) (i : Fin 3) :
    unitVariation p b i = if (b, i) = p then 1 else 0 := by
  unfold unitVariation ColdStepAtMirrorFrames.bondVariation
  by_cases hb : b = p.1
  · subst hb
    simp only [Pi.single_eq_same, EuclideanSpace.single_apply]
    by_cases hi : i = p.2
    · subst hi
      simp
    · have : ¬ ((p.1, i) = p) := fun h => hi (congrArg Prod.snd h)
      simp [hi, this]
  · have : ¬ ((b, i) = p) := fun h => hb (congrArg Prod.fst h)
    simp [Pi.single_eq_of_ne hb, this]
open Classical in
private theorem sum_smul_unitVariation (x : ChartCoord F → ℝ) (b : ↥(chordBonds (finiteCells F))) (i : Fin 3) :
    (∑ p, x p • unitVariation p) b i = x (b, i) := by
  let ev : StepVariable (finiteCells F) →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).toLinearMap.comp (LinearMap.proj b)
  have h : ev (∑ p, x p • unitVariation p) = ∑ p, x p * ev (unitVariation p) := by
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have h2 : ∀ p, ev (unitVariation p) = if (b, i) = p then 1 else 0 := fun p => unitVariation_apply p b i
  have h3 : ev (∑ p, x p • unitVariation p) = (∑ p, x p • unitVariation p) b i := rfl
  rw [← h3, h]
  simp [h2]
private theorem shiftCoordinates_zero' (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    shiftCoordinates w (0 : StepVariable (finiteCells F)) = w := by
  funext x i
  unfold shiftCoordinates
  rw [stepCoordinates_zero', add_zero]
abbrev _root_.YangMills.SharedProofs.p71543 := @shiftCoordinates_zero'
private theorem chartHessian_eq_fderiv {a : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} (hf : ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0) (i j : ChartCoord F) :
    chartHessian a w V i j =
      fderiv ℝ (fderiv ℝ (chartedEnergyAt a w V)) 0 (unitVariation i) (unitVariation j) :=
  (fderiv_fderiv_apply_eq hf (unitVariation j) (unitVariation i)).trans (fderiv_fderiv_symm hf _ _)
private theorem chartHessian_symm' {a : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} (hf : ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0) (i j : ChartCoord F) :
    chartHessian a w V i j = chartHessian a w V j i := by
  rw [chartHessian_eq_fderiv hf, chartHessian_eq_fderiv hf, fderiv_fderiv_symm hf]
private theorem chartHessian_form {a : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} (hf : ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0) (x : ChartCoord F → ℝ) :
    ∑ p, ∑ q, x p * chartHessian a w V p q * x q =
      fderiv ℝ (fderiv ℝ (chartedEnergyAt a w V)) 0 (∑ p, x p • unitVariation p)
        (∑ p, x p • unitVariation p) := by
  have h1 : fderiv ℝ (fderiv ℝ (chartedEnergyAt a w V)) 0 (∑ p, x p • unitVariation p)
      (∑ p, x p • unitVariation p) =
      ∑ p, ∑ q, x p * (x q * fderiv ℝ (fderiv ℝ (chartedEnergyAt a w V)) 0 (unitVariation p)
        (unitVariation q)) := by
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [h1]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [chartHessian_eq_fderiv hf]
  ring
private theorem chartHessian_coercive {a lam ρ σ : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (hfl : HasCoerciveHessian a lam ρ σ (finiteCells F) V) (hw : IsBaseCoordinate ρ σ V w)
    (hf : ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0) (x : ChartCoord F → ℝ) :
    lam * ∑ p, x p ^ 2 ≤ ∑ p, ∑ q, x p * chartHessian a w V p q * x q := by
  set U : StepVariable (finiteCells F) := ∑ p, x p • unitVariation p with hU
  have hdz : ∀ b : F.Site F.depth × Fin 4, b ∉ chordBonds (finiteCells F) →
      stepCoordinates U b.1 b.2 = 0 := by
    intro b hb
    unfold stepCoordinates
    rw [dif_neg hb]
  have h1 := hfl w (stepCoordinates U) hw.vanish_off hdz hw.norm_le hw.cold
  have e1 : (fun τ : ℝ => blockEnergy a (finiteCells F) F.depth
      (chartedField (fun z i => w z i + τ • stepCoordinates U z i) V) V) =
      fun τ : ℝ => chartedEnergyAt a w V (τ • U) := by
    funext τ
    unfold chartedEnergyAt chartedEnergy
    simp only [stepCoordinates_smul']
  rw [e1, deriv_deriv_line hf, fderiv_fderiv_apply_eq hf] at h1
  rw [chartHessian_form hf, ← hU]
  have e2 : ∑ b ∈ chordBonds (finiteCells F), ‖stepCoordinates U b.1 b.2‖ ^ 2 = ∑ p, x p ^ 2 := by
    rw [← Finset.sum_coe_sort, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb : stepCoordinates U b.1.1 b.1.2 = toImaginary (U b) := by
      unfold stepCoordinates
      rw [dif_pos b.2]
    rw [hb, norm_toImaginary', EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hU, sum_smul_unitVariation]
  rwa [e2] at h1
private theorem weighted_row_sum_le (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hF : ∀ i, F.period F.top i ≠ 0) {C δ r : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hr0 : 0 ≤ r) (hr : r ≤ δ / 2)
    (A : Matrix (ChartCoord F) (ChartCoord F) ℝ)
    (hA : ∀ a b, a ≠ b → |A a b| ≤ C * Real.exp (-(δ * (coordDist a b : ℝ))))
    (a : ChartCoord F) :
    ∑ b, |A a b| * (Real.exp (r * (coordDist a b : ℝ)) - 1) ≤
      C * (r * (4 / δ)) * chartSumBound F.blockSide (δ / 4) := by
  have hK : 0 ≤ C * (r * (4 / δ)) := by positivity
  have hterm : ∀ b, |A a b| * (Real.exp (r * (coordDist a b : ℝ)) - 1) ≤
      C * (r * (4 / δ)) * Real.exp (-(4 * (δ / 4 / 4) *
        (cellSupDist (enclosingCell a.1.1.1) (enclosingCell b.1.1.1) : ℝ))) := by
    intro b
    have e : -(4 * (δ / 4 / 4) * (cellSupDist (enclosingCell a.1.1.1) (enclosingCell b.1.1.1) : ℝ)) =
        -(δ / 4 * (coordDist a b : ℝ)) := by
      unfold coordDist
      ring
    rw [e]
    have hd0 : (0 : ℝ) ≤ (coordDist a b : ℝ) := Nat.cast_nonneg _
    by_cases hab : a = b
    · subst hab
      have hz : (coordDist a a : ℝ) = 0 := by
        unfold coordDist
        rw [supDist_self]
        simp
      rw [hz]
      simp only [mul_zero, Real.exp_zero, sub_self, neg_zero]
      simpa using hK
    · have hE : 0 ≤ Real.exp (r * (coordDist a b : ℝ)) - 1 := by
        have := Real.one_le_exp (mul_nonneg hr0 hd0)
        linarith
      calc |A a b| * (Real.exp (r * (coordDist a b : ℝ)) - 1)
          ≤ C * Real.exp (-(δ * (coordDist a b : ℝ))) * (Real.exp (r * (coordDist a b : ℝ)) - 1) :=
            mul_le_mul_of_nonneg_right (hA a b hab) hE
        _ = C * (Real.exp (-(δ * (coordDist a b : ℝ))) * (Real.exp (r * (coordDist a b : ℝ)) - 1)) := by ring
        _ ≤ C * (r * (4 / δ) * Real.exp (-(δ / 4 * (coordDist a b : ℝ)))) :=
            mul_le_mul_of_nonneg_left (exp_mul_exp_sub_one_le hδ hr0 hr hd0) hC
        _ = _ := by ring
  refine (Finset.sum_le_sum fun b _ => hterm b).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hK
  have h1 := sum_chartCoord_le hS hL hs hF
    (fun z => Real.exp (-(4 * (δ / 4 / 4) * (cellSupDist (enclosingCell a.1.1.1) z : ℝ))))
    (fun z => (Real.exp_pos _).le)
  have h2 := sum_cells_exp_le hF (δ := δ / 4 / 4) (by positivity) (enclosingCell a.1.1.1)
  refine h1.trans ?_
  unfold chartSumBound
  exact mul_le_mul_of_nonneg_left h2 (by positivity)
end Frames
section Parameters
private def IsChartEnergyBound (l : ChainParameters) (C : ℝ) : Prop :=
  ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
    IsBlockTorus l.side F →
    IsAdmissibleChartPoint l.side l.σA w V → ContDiffAt ℝ 3 (chartedEnergyAt l.coupling w V) 0 ∧
      ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
        |secondDerivAlong (chartedEnergyAt l.coupling w V) 0 (ColdStepAtMirrorFrames.bondVariation b e)
          (ColdStepAtMirrorFrames.bondVariation b' e')| ≤
          C * Real.exp (-(l.δ₁ * chordBondDist F b b')) * ‖e‖ * ‖e'‖
open Classical in
private def chartEnergyConstant (l : ChainParameters) : ℝ :=
  if h : ∃ C : ℝ, 0 < C ∧ IsChartEnergyBound l C then h.choose else 1
private theorem chartEnergyConstant_pos (l : ChainParameters) : 0 < chartEnergyConstant l := by
  unfold chartEnergyConstant
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_pos
private theorem chartEnergyConstant_spec {l : ChainParameters} (h : ∃ C : ℝ, 0 < C ∧ IsChartEnergyBound l C) :
    IsChartEnergyBound l (chartEnergyConstant l) := by
  unfold chartEnergyConstant
  rw [dif_pos h]
  exact h.choose_spec.2
open Classical in
private def inverseDecayRate (l : ChainParameters) : ℝ :=
  if 0 < l.δ₁ ∧ 0 < l.lam then
    min (l.δ₁ / 8) (decayRate l.δ₁ l.lam (chartEnergyConstant l) (chartSumBound l.side (l.δ₁ / 4)) / 2)
  else 1
private theorem inverseDecayRate_pos (l : ChainParameters) : 0 < inverseDecayRate l := by
  unfold inverseDecayRate
  split_ifs with h
  · have := (decayRate_spec h.1 h.2 (chartEnergyConstant_pos l) (chartSumBound_nonneg l.side (l.δ₁ / 4))).1
    exact lt_min (by linarith [h.1]) (by linarith)
  · exact one_pos
private theorem inverseDecayRate_spec {l : ChainParameters} (hδ : 0 < l.δ₁) (hlam : 0 < l.lam) :
    inverseDecayRate l ≤ l.δ₁ / 8 ∧ 2 * inverseDecayRate l ≤ l.δ₁ / 2 ∧
      chartEnergyConstant l * (2 * inverseDecayRate l * (4 / l.δ₁)) * chartSumBound l.side (l.δ₁ / 4) ≤
        l.lam / 2 := by
  have hS := chartSumBound_nonneg l.side (l.δ₁ / 4)
  have hC := chartEnergyConstant_pos l
  obtain ⟨h0, h1, h2⟩ := decayRate_spec hδ hlam hC hS
  have e : inverseDecayRate l =
      min (l.δ₁ / 8) (decayRate l.δ₁ l.lam (chartEnergyConstant l) (chartSumBound l.side (l.δ₁ / 4)) / 2) := by
    unfold inverseDecayRate
    rw [if_pos ⟨hδ, hlam⟩]
  have ha : inverseDecayRate l ≤ l.δ₁ / 8 := by
    rw [e]
    exact min_le_left _ _
  have hb : 2 * inverseDecayRate l ≤
      decayRate l.δ₁ l.lam (chartEnergyConstant l) (chartSumBound l.side (l.δ₁ / 4)) := by
    have : inverseDecayRate l ≤
        decayRate l.δ₁ l.lam (chartEnergyConstant l) (chartSumBound l.side (l.δ₁ / 4)) / 2 := by
      rw [e]
      exact min_le_right _ _
    linarith
  refine ⟨ha, by linarith, le_trans ?_ h2⟩
  have h4 : 0 ≤ 4 / l.δ₁ := by positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb h4) hC.le) hS
end Parameters
end ChartHessianInverse
open ChartHessianInverse in
set_option maxHeartbeats 1000000 in
theorem chartHessianInverseDecay_holds (hEn : ChartEnergyDerivBounds)
    (hCl : AdmissibleParametersExist) (hcov : BlocksCoverLowerLevel)
    (hSites : SiteDecomposition) : ChartHessianInverseDecay := by
  refine ⟨chartEnergyConstant, inverseDecayRate, chartEnergyConstant_pos, inverseDecayRate_pos, fun T hD => ?_⟩
  obtain ⟨hδ, -, hlam, -, -, -, -, -, -⟩ := hD.chain
  obtain ⟨c, eδ, -, elam, eρ, eσA, -, -, hHo⟩ :=
    hCl T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N hD.a_ge hD.L_odd hD.chain
  obtain ⟨C, hC, hE⟩ := hEn T.coupling T.side c hD.a_ge hD.L_odd hD.L_ge hHo
  have hb : IsChartEnergyBound T.toChainParameters C := by
    intro F w V hF hS
    have hS' : IsAdmissibleChartPoint T.side c.σA
        (shiftCoordinates w (0 : StepVariable (finiteCells F))) V := by
      rw [shiftCoordinates_zero', eσA]
      exact hS
    obtain ⟨h1, -, h3, -⟩ := hE F w 0 V hF hS'
    refine ⟨h1, fun b b' e e' => ?_⟩
    have h4 := h3 b b' e e'
    rw [eδ] at h4
    exact h4
  have hspec := chartEnergyConstant_spec ⟨C, hC, hb⟩
  obtain ⟨hκ₁, hκ₂, hκ₃⟩ := inverseDecayRate_spec (l := T.toChainParameters) hδ hlam
  have hκ₀ := inverseDecayRate_pos T.toChainParameters
  have hCS := chartEnergyConstant_pos T.toChainParameters
  refine ⟨hκ₁, fun F hFL hcub s V w hs hsσ hcoldV hfl => ?_⟩
  have hF : IsBlockTorus T.side F := ⟨hFL, hcub⟩
  have hodd : Odd F.blockSide := hFL ▸ hD.L_odd
  obtain ⟨n, hn, hside⟩ := hcub
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside i]
    omega
  have hall := hcov F hodd fun i => by
    have := hs2 i
    omega
  have hper : ∀ i, F.period F.top i ≠ 0 := by
    intro i
    have hL0 : F.blockSide ≠ 0 := fun h => by simp [h] at hodd
    simp only [BlockFrame.period, hside]
    simp
    omega
  have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨hper i⟩
  have hw : ∀ z : F.Cell, z ∈ finiteCells F := mem_finiteCells_of_ne hper
  have hst : ∀ z : F.Cell, z ∈ sitesOfCells (finiteCells F) F.top := fun z => by
    unfold sitesOfCells
    rw [Finset.mem_biUnion]
    refine ⟨z, hw z, ?_⟩
    rw [Finset.mem_image]
    refine ⟨0, ?_, ?_⟩
    · unfold centredCube
      rw [Fintype.mem_piFinset]
      intro i
      simp
    · funext i
      have := hne i
      simp only [cellCentre, siteOfCoords, Nat.sub_self, pow_zero, one_mul, Pi.add_apply, Pi.zero_apply,
        Int.cast_zero, add_zero]
      exact ZMod.intCast_zmod_cast (z i)
  have hVe : IsSmallCurvature s V := fun p hp => hcoldV p (by
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hst _, hp, fun y _ => hst y⟩)
  have hWe : IsSmallCurvature T.σA (chartedField w V) := fun p hp => hfl.cold p (by
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hall _, hp, fun y _ => hall y⟩)
  have hsmall : IsAdmissibleChartPoint T.side T.σA w V := ⟨fun b hb => by
    have := hfl.norm_le_inv_side b hb
    rwa [hFL] at this, hWe⟩
  obtain ⟨hf, hsec⟩ := hspec F w V hF hsmall
  have hcl := hHo.estimates F s V hF hs (by rw [eσA]; exact hsσ) hVe
  have hfloor : HasCoerciveHessian T.coupling T.lam T.ρA T.σA (finiteCells F) V := by
    have h := hcl.hessian
    rwa [elam, eρ, eσA] at h
  have hentry : ∀ i j, |chartHessian T.coupling w V i j| ≤
      chartEnergyConstant T.toChainParameters * Real.exp (-(T.δ₁ * (coordDist i j : ℝ))) := by
    intro i j
    have h := hsec i.1 j.1 (EuclideanSpace.single (𝕜 := ℝ) i.2 1) (EuclideanSpace.single (𝕜 := ℝ) j.2 1)
    have e₁ : ‖EuclideanSpace.single (𝕜 := ℝ) i.2 (1 : ℝ)‖ = 1 := by simp
    have e₂ : ‖EuclideanSpace.single (𝕜 := ℝ) j.2 (1 : ℝ)‖ = 1 := by simp
    rw [e₁, e₂, mul_one, mul_one] at h
    exact h
  refine ⟨hentry, fun u hu0 hu1 => ?_⟩
  set A : Matrix (ChartCoord F) (ChartCoord F) ℝ :=
    u • chartHessian T.coupling w V + (1 - u) • T.lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ) with hA
  have hAe : ∀ a b, A a b =
      u * chartHessian T.coupling w V a b + (1 - u) * (T.lam * if a = b then 1 else 0) := by
    intro a b
    simp [hA, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  have hsymm : ∀ a b, A a b = A b a := by
    intro a b
    rw [hAe, hAe, chartHessian_symm' hf a b]
    by_cases hab : a = b
    · rw [hab]
    · rw [if_neg hab, if_neg (Ne.symm hab)]
  have hAfloor : ∀ v : ChartCoord F → ℝ, T.lam * ∑ a, v a ^ 2 ≤ ∑ a, ∑ b, v a * A a b * v b := by
    intro v
    have h1 := chartHessian_coercive hfloor hfl hf v
    have h2 : ∑ a, ∑ b, v a * A a b * v b =
        u * ∑ a, ∑ b, v a * chartHessian T.coupling w V a b * v b + (1 - u) * (T.lam * ∑ a, v a ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h3 : ∑ b, v a * A a b * v b = ∑ b, (u * (v a * chartHessian T.coupling w V a b * v b) +
          (1 - u) * T.lam * (if a = b then v a * v b else 0)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hAe]
        by_cases hab : a = b
        · simp only [if_pos hab]
          ring
        · simp only [if_neg hab]
          ring
      rw [h3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    rw [h2]
    have h4 := mul_le_mul_of_nonneg_left h1 hu0
    nlinarith
  have hAoff : ∀ a b, a ≠ b → |A a b| ≤
      chartEnergyConstant T.toChainParameters * Real.exp (-(T.δ₁ * (coordDist a b : ℝ))) := by
    intro a b hab
    rw [hAe, if_neg hab, mul_zero, mul_zero, add_zero, abs_mul, abs_of_nonneg hu0]
    calc u * |chartHessian T.coupling w V a b| ≤ 1 * |chartHessian T.coupling w V a b| :=
          mul_le_mul_of_nonneg_right hu1 (abs_nonneg _)
      _ = |chartHessian T.coupling w V a b| := one_mul _
      _ ≤ _ := hentry a b
  have hrow : ∀ a, ∑ b, |A a b| *
      (Real.exp (2 * inverseDecayRate T.toChainParameters * (coordDist a b : ℝ)) - 1) ≤ T.lam / 2 := by
    intro a
    have h := weighted_row_sum_le hSites hodd hs2 hper hCS.le hδ (by positivity) hκ₂ A hAoff a
    rw [hFL] at h
    exact h.trans hκ₃
  have hunit : IsUnit A := isUnit_of_coercive hlam A hAfloor
  refine ⟨hunit, fun i j => ?_⟩
  refine abs_inv_le_of_weighted_rows hlam (fun a b => (coordDist a b : ℝ)) A hsymm ?_ ?_ ?_ (by positivity)
    hAfloor hrow hunit i j
  · intro a
    simp [coordDist, supDist_self]
  · intro a b
    simp only [coordDist]
    rw [supDist_comm]
  · intro a b c'
    simp only [coordDist]
    exact_mod_cast supDist_triangle _ _ _
end RunningCouplingSlope
end YangMills.Construction
end
