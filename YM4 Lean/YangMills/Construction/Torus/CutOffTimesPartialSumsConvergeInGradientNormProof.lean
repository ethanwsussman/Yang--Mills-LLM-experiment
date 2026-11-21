import YangMills.Construction.Torus.CutOffTimesPartialSumsConvergeInGradientNorm
import YangMills.Construction.Torus.GradientNormLipschitzConstantAndSharpNormProof
import YangMills.Construction.Torus.PartialSumsConvergeOnTheBox
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.AmbientPoints.CutoffFourierSum
open YangMills.Construction.Torus.FourierBox
variable {s : Conventions.StandingParameters}
abbrev flatIndex (μ : Fin 4) : Fin (4 * 1) := Fin.cast (by norm_num) μ
def liftOne (g : Pt s .euclidean → ℂ) : (Fin (4 * 1) → ℝ) → ℂ :=
  ofSinglePoint g ∘ tupleProj s .euclidean 1
theorem tupleProj_apply_zero (w : Fin (4 * 1) → ℝ) :
    tupleProj s .euclidean 1 w 0 = (w : Pt s .euclidean) := by
  change (fun μ : Fin 4 => (flattenCoords 1).symm w 0 μ) = fun μ : Fin 4 => w (flatIndex μ)
  funext μ
  have hlt : 4 * ((0 : Fin 1) : ℕ) + (μ : ℕ) < 4 * 1 := by
    have := μ.2
    simp only [Fin.val_zero]
    omega
  rw [flattenCoords_symm_apply w 0 μ hlt]
  exact congrArg w (Fin.ext (by simp))
theorem tupleProj_eq_const (w : Fin (4 * 1) → ℝ) :
    tupleProj s .euclidean 1 w = fun _ => (w : Pt s .euclidean) := by
  funext i
  rw [Subsingleton.elim i 0]
  exact tupleProj_apply_zero w
theorem liftOne_apply (g : Pt s .euclidean → ℂ) (w : Fin (4 * 1) → ℝ) :
    liftOne g w = g (w : Pt s .euclidean) :=
  congrArg g (tupleProj_apply_zero w)
theorem iteratedPartial_single {D : ℕ} (j : Fin D) (G : (Fin D → ℝ) → ℂ) :
    iteratedPartial (Pi.single j 1 : PowerSeries.MultiIndex D) G = partialDeriv j G := by apply _root_.YangMills.Construction.AmbientPoints.GradientC1Bounds.iteratedPartial_single <;> assumption
theorem iteratedPartial_basis (μ : Fin 4) (G : (Fin (4 * 1) → ℝ) → ℂ) :
    iteratedPartial (basisMultiIndex μ) G = partialDeriv (flatIndex μ) G :=
  iteratedPartial_single _ _
theorem isCnOn_univ_one_iff_contDiff
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    (G : (Fin (4 * 1) → ℝ) → ℂ) : IsCnOn univ 1 G ↔ ContDiff ℝ 1 G := by apply _root_.YangMills.Construction.AmbientPoints.GradientC1Bounds.isCnOn_univ_one_iff_contDiff <;> assumption
theorem isCnAtPoint_one_of_isSmoothFn {g : Pt s .euclidean → ℂ}
    (hg : IsSmoothFn (ofSinglePoint g)) : IsCnAtPoint 1 g :=
  ⟨hg.1, fun n _ => hg.2 n le_top⟩
theorem multiDeriv_basis (hT : TupleDerivProps s .euclidean 1) {g : Pt s .euclidean → ℂ}
    (hg : IsCnAtPoint 1 g) (μ : Fin 4) (w : Fin (4 * 1) → ℝ) :
    multiDeriv (basisMultiIndex μ) (ofSinglePoint g) (tupleProj s .euclidean 1 w) =
      partialDeriv (flatIndex μ) (liftOne g) w := by
  have hord : (((basisMultiIndex μ).order : ℕ) : ℕ∞) ≤ 1 := by
    rw [basisMultiIndex_order]
    simp
  obtain ⟨H, hH, -⟩ := ((hT 1 (ofSinglePoint g) hg).1 (basisMultiIndex μ) hord).1
  have hd := multiDeriv_comp_tupleProj (α := basisMultiIndex μ) (F := ofSinglePoint g) ⟨H, hH⟩
  exact (congrFun hd w).trans (congrFun (iteratedPartial_basis μ _) w)
theorem contDiff_fourierPartialSum (P : ℝ) (F : Tuple s .euclidean 1 → ℂ) (t : ℕ+) :
    ContDiff ℝ 1 (fourierPartialSum (n := 1) P F t) := by
  unfold fourierPartialSum
  exact ContDiff.sum fun k _ => contDiff_const.mul ((contDiff_fourierMode P k).of_le (by simp))
theorem partialDeriv_fourierPartialSum (P : ℝ) (F : Tuple s .euclidean 1 → ℂ) (t : ℕ+)
    (j : Fin (4 * 1)) (u : Fin (4 * 1) → ℝ) :
    partialDeriv j (fourierPartialSum (n := 1) P F t) u =
      ∑ k ∈ modesWithin (t : ℕ), fourierCoeff P F k * partialDeriv j (fourierMode P k) u := by
  have hd : ∀ k : Fin (4 * 1) → ℤ, DifferentiableAt ℝ (fourierMode P k) u :=
    fun k => ((contDiff_fourierMode P k).differentiable (by simp)) u
  have hs : HasFDerivAt (fourierPartialSum (n := 1) P F t)
      (∑ k ∈ modesWithin (t : ℕ), fourierCoeff P F k • fderiv ℝ (fourierMode P k) u) u := by
    unfold fourierPartialSum
    exact HasFDerivAt.fun_sum fun k _ => (hd k).hasFDerivAt.const_mul (fourierCoeff P F k)
  have hl := (hs.hasLineDerivAt (Pi.single j 1)).lineDeriv
  rw [partialDeriv, hl, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_apply, smul_eq_mul, partialDeriv,
    (hd k).lineDeriv_eq_fderiv]
def partialSumError (P : ℝ) (h : Pt s .euclidean → ℂ) (t : ℕ+) : Pt s .euclidean → ℂ :=
  fun x => fourierPartialSum (n := 1) P (ofSinglePoint h) t x - h x
theorem liftOne_partialSumError (P : ℝ) (h : Pt s .euclidean → ℂ) (t : ℕ+) :
    liftOne (partialSumError P h t) =
      fun u => fourierPartialSum (n := 1) P (ofSinglePoint h) t u - liftOne h u := by
  funext w
  rw [liftOne_apply, liftOne_apply]
  rfl
theorem isCnAtPoint_partialSumError
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    (P : ℝ) {h : Pt s .euclidean → ℂ} (hh : IsCnAtPoint 1 h) (t : ℕ+) :
    IsCnAtPoint 1 (partialSumError P h t) := by
  have hL : ContDiff ℝ 1 (liftOne h) := (isCnOn_univ_one_iff_contDiff hC _).mp hh
  have hd : ContDiff ℝ 1 (liftOne (partialSumError P h t)) := by
    rw [liftOne_partialSumError]
    exact (contDiff_fourierPartialSum P _ t).sub hL
  exact (isCnOn_univ_one_iff_contDiff hC _).mpr hd
theorem partialAt_partialSumError (hT : TupleDerivProps s .euclidean 1)
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    (P : ℝ) {h : Pt s .euclidean → ℂ} (hh : IsCnAtPoint 1 h) (t : ℕ+) (μ : Fin 4)
    (w : Fin (4 * 1) → ℝ) :
    partialAt μ (partialSumError P h t) (w : Pt s .euclidean) =
      (∑ k ∈ modesWithin (t : ℕ), fourierCoeff P (ofSinglePoint h) k *
          iteratedPartial (basisMultiIndex μ) (fourierMode P k) w) -
        multiDeriv (basisMultiIndex μ) (ofSinglePoint h)
          (tupleProj s .euclidean 1 w) := by
  have hL : DifferentiableAt ℝ (liftOne h) w :=
    (((isCnOn_univ_one_iff_contDiff hC _).mp hh).differentiable (by simp)) w
  have hG : DifferentiableAt ℝ (fourierPartialSum (n := 1) P (ofSinglePoint h) t) w :=
    ((contDiff_fourierPartialSum P _ t).differentiable (by simp)) w
  have hsub := ((hG.hasFDerivAt.fun_sub hL.hasFDerivAt).hasLineDerivAt
    (Pi.single (flatIndex μ) 1)).lineDeriv
  have h1 : partialAt μ (partialSumError P h t) (w : Pt s .euclidean) =
      partialDeriv (flatIndex μ) (liftOne (partialSumError P h t)) w := by
    rw [← multiDeriv_basis hT (isCnAtPoint_partialSumError hC P hh t) μ w, tupleProj_eq_const]
    rfl
  rw [h1, liftOne_partialSumError, partialDeriv, hsub, sub_apply,
    ← hG.lineDeriv_eq_fderiv, ← hL.lineDeriv_eq_fderiv, multiDeriv_basis hT hh μ w]
  change partialDeriv (flatIndex μ) _ w - partialDeriv (flatIndex μ) (liftOne h) w = _
  rw [partialDeriv_fourierPartialSum]
  simp only [iteratedPartial_basis]
def cubeError (P : ℝ) (h : Pt s .euclidean → ℂ) (α : PowerSeries.MultiIndex (4 * 1)) (t : ℕ+) :
    ℝ≥0∞ :=
  ⨆ u ∈ fundamentalCube (4 * 1) P, ENNReal.ofReal
    ‖(∑ k ∈ modesWithin (t : ℕ), fourierCoeff P (ofSinglePoint h) k *
        iteratedPartial α (fourierMode P k) u) -
      multiDeriv α (ofSinglePoint h) (tupleProj s .euclidean 1 u)‖
theorem partialSumError_le_cubeError (P : ℝ) (h : Pt s .euclidean → ℂ) (t : ℕ+)
    {w : Fin (4 * 1) → ℝ} (hw : w ∈ fundamentalCube (4 * 1) P) :
    ENNReal.ofReal ‖partialSumError P h t (w : Pt s .euclidean)‖ ≤ cubeError P h 0 t := by
  have hterm : (∑ k ∈ modesWithin (t : ℕ), fourierCoeff P (ofSinglePoint h) k *
        iteratedPartial (0 : PowerSeries.MultiIndex (4 * 1)) (fourierMode P k) w) -
      multiDeriv (0 : PowerSeries.MultiIndex (4 * 1)) (ofSinglePoint h)
        (tupleProj s .euclidean 1 w) = partialSumError P h t (w : Pt s .euclidean) := by
    simp only [iteratedPartial_zero, multiDeriv_zero]
    exact congrArg (fun z => fourierPartialSum (n := 1) P (ofSinglePoint h) t w - z)
      (liftOne_apply h w)
  rw [← hterm]
  exact le_iSup₂ (f := fun (u : Fin (4 * 1) → ℝ) (_ : u ∈ fundamentalCube (4 * 1) P) =>
    ENNReal.ofReal
    ‖(∑ k ∈ modesWithin (t : ℕ), fourierCoeff P (ofSinglePoint h) k *
        iteratedPartial (0 : PowerSeries.MultiIndex (4 * 1)) (fourierMode P k) u) -
      multiDeriv (0 : PowerSeries.MultiIndex (4 * 1)) (ofSinglePoint h)
        (tupleProj s .euclidean 1 u)‖) w hw
theorem partialAt_partialSumError_le_cubeError (hT : TupleDerivProps s .euclidean 1)
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    (P : ℝ) {h : Pt s .euclidean → ℂ} (hh : IsCnAtPoint 1 h) (t : ℕ+) (μ : Fin 4)
    {w : Fin (4 * 1) → ℝ} (hw : w ∈ fundamentalCube (4 * 1) P) :
    ENNReal.ofReal ‖partialAt μ (partialSumError P h t) (w : Pt s .euclidean)‖ ≤
      cubeError P h (basisMultiIndex μ) t := by
  rw [partialAt_partialSumError hT hC P hh t μ w]
  exact le_iSup₂ (f := fun (u : Fin (4 * 1) → ℝ) (_ : u ∈ fundamentalCube (4 * 1) P) =>
    ENNReal.ofReal
    ‖(∑ k ∈ modesWithin (t : ℕ), fourierCoeff P (ofSinglePoint h) k *
        iteratedPartial (basisMultiIndex μ) (fourierMode P k) u) -
      multiDeriv (basisMultiIndex μ) (ofSinglePoint h)
        (tupleProj s .euclidean 1 u)‖) w hw
theorem gradNorm_eq_zero_of_notMem_tsupport (hT : TupleDerivProps s .euclidean 1)
    {χ : Pt s .euclidean → ℝ}
    (hχ : IsCnAtPoint 1 fun x => (χ x : ℂ)) {x : Pt s .euclidean}
    (hx : x ∉ tsupport χ) : gradNorm (fun y => (χ y : ℂ)) x = 0 := by
  have hz : ∀ μ, partialAt μ (fun y => (χ y : ℂ)) x = 0 := by
    intro μ
    by_contra hne
    have hord : (((basisMultiIndex μ).order : ℕ) : ℕ∞) ≤ 1 := by
      rw [basisMultiIndex_order]
      simp
    have hsub := ((hT 1 _ hχ).1 (basisMultiIndex μ) hord).2.2.1
    have hmem : (fun _ => x : Tuple s .euclidean 1) ∈
        closedSupport (asFunctionOnOnePoint χ) := hsub (subset_closure hne)
    rw [closedSupport_asFunctionOnOnePoint] at hmem
    exact hx hmem
  simp [gradNorm, AmbientPoints.gradient, hz]
theorem cutoffTimesFourierSumsConverge (hF : FourierPartialSums.Statement)
    (hS : GradientC1Bounds.Statement)
    (hTop : TupleTopology.Holds)
    (hC : PeriodicSpace.ContPartialsIffContDiff) :
    CutoffTimesFourierSumsConverge := by
  intro s P hP χ h hχ hh
  have hT : TupleDerivProps s .euclidean 1 := ((hTop s .euclidean).1 1 le_rfl).2.2.2.2
  obtain ⟨hprod, hreal⟩ := hS s .euclidean
  have hχ1 : IsCnAtPoint 1 fun x => (χ x : ℂ) := isCnAtPoint_one_of_isSmoothFn hχ.1
  have hh1 : IsCnAtPoint 1 h := isCnAtPoint_one_of_isSmoothFn hh.1
  have hAfin : c1GradNorm (fun x => (χ x : ℂ)) < ⊤ :=
    (hreal ⟨1, Set.mem_Ici.mpr le_rfl⟩ χ hχ1 hχ.2.1).1
  obtain ⟨A, hA⟩ : ∃ A, A = c1GradNorm (fun x => (χ x : ℂ)) := ⟨_, rfl⟩
  rw [← hA] at hAfin
  have hA0 : ∀ x, ENNReal.ofReal ‖(χ x : ℂ)‖ ≤ A := fun x => by
    rw [hA]
    refine le_trans ?_ (le_max_left _ _)
    rw [tupleSupNorm_ofSinglePoint]
    exact le_iSup (fun y => ENNReal.ofReal ‖(χ y : ℂ)‖) x
  have hA1 : ∀ x, ENNReal.ofReal (gradNorm (fun y => (χ y : ℂ)) x) ≤ A := fun x => by
    rw [hA]
    refine le_trans ?_ (le_max_right _ _)
    exact le_iSup (fun y => ENNReal.ofReal (gradNorm (fun y => (χ y : ℂ)) y)) x
  let ε : ℕ+ → ℝ≥0∞ := fun t => cubeError P h 0 t + ∑ μ, cubeError P h (basisMultiIndex μ) t
  have hε : Tendsto ε atTop (𝓝 0) := by
    have h0 : Tendsto (cubeError P h 0) atTop (𝓝 0) := hF s 1 le_rfl P hP _ hh 0
    have h1 : ∀ μ : Fin 4, Tendsto (cubeError P h (basisMultiIndex μ)) atTop (𝓝 0) :=
      fun μ => hF s 1 le_rfl P hP _ hh (basisMultiIndex μ)
    simpa using h0.add (tendsto_finsetSum Finset.univ fun μ _ => h1 μ)
  have hbound : ∀ t, c1GradNorm (fun x : Pt s .euclidean =>
      (χ x : ℂ) * fourierPartialSum (n := 1) P (ofSinglePoint h) t x - (χ x : ℂ) * h x) ≤
      3 * A * ε t := by
    intro t
    have hg1 := isCnAtPoint_partialSumError hC P hh1 t
    have hleib := (hprod (fun x => (χ x : ℂ)) (partialSumError P h t) hχ1 hg1).2.2.1
    have hgrad := (hprod (partialSumError P h t) (fun x => (χ x : ℂ)) hg1 hχ1).1
    have hfun : (fun x : Pt s .euclidean =>
        (χ x : ℂ) * fourierPartialSum (n := 1) P (ofSinglePoint h) t x - (χ x : ℂ) * h x) =
        fun y => (χ y : ℂ) * partialSumError P h t y :=
      funext fun x => (mul_sub _ _ _).symm
    rw [hfun]
    have hpt : ∀ x, ENNReal.ofReal ‖(χ x : ℂ) * partialSumError P h t x‖ ≤ 3 * A * ε t ∧
        ENNReal.ofReal (gradNorm (fun y => (χ y : ℂ) * partialSumError P h t y) x) ≤
          3 * A * ε t := by
      intro x
      by_cases hx : x ∈ tsupport χ
      · have hxs : (fun _ => x : Tuple s .euclidean 1) ∈
            closedSupport (asFunctionOnOnePoint χ) := by
          rw [closedSupport_asFunctionOnOnePoint]
          exact hx
        have hxQ := hχ.2.2 hxs
        have hw : (x : Fin (4 * 1) → ℝ) ∈ fundamentalCube (4 * 1) P := by
          refine (tupleProj_mem_fundamentalBoxPow_iff s 1 P x).mp ?_
          exact Eq.mpr (congrArg (· ∈ fundamentalBoxPow s 1 P) (tupleProj_eq_const (s := s) x)) hxQ
        have hg0 : ENNReal.ofReal ‖partialSumError P h t x‖ ≤ ε t :=
          (partialSumError_le_cubeError P h t hw).trans le_self_add
        have hgμ : ∀ μ, ENNReal.ofReal ‖partialAt μ (partialSumError P h t) x‖ ≤ ε t := fun μ =>
          (partialAt_partialSumError_le_cubeError hT hC P hh1 t μ hw).trans
            ((Finset.single_le_sum (f := fun μ => cubeError P h (basisMultiIndex μ) t)
              (fun _ _ => zero_le) (Finset.mem_univ μ)).trans le_add_self)
        have hgl : ENNReal.ofReal (gradNorm (partialSumError P h t) x) ≤ 2 * ε t := by
          obtain ⟨μ₀, hμ₀⟩ := exists_eq_ciSup_of_finite
            (f := fun μ : Fin 4 => ‖partialAt μ (partialSumError P h t) x‖)
          refine (ENNReal.ofReal_le_ofReal (hgrad x)).trans ?_
          have h2 : ENNReal.ofReal 2 = 2 := by simp
          rw [← hμ₀, ENNReal.ofReal_mul (by norm_num), h2]
          gcongr
          exact hgμ μ₀
        constructor
        · rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
          calc ENNReal.ofReal ‖(χ x : ℂ)‖ * ENNReal.ofReal ‖partialSumError P h t x‖
              ≤ A * ε t := mul_le_mul' (hA0 x) hg0
            _ ≤ 3 * (A * ε t) := le_mul_of_one_le_left' (by norm_num)
            _ = 3 * A * ε t := (mul_assoc _ _ _).symm
        · refine (ENNReal.ofReal_le_ofReal (hleib x)).trans ?_
          have hlen : ∀ (g : Pt s .euclidean → ℂ) (y : Pt s .euclidean),
              0 ≤ gradNorm g y := fun _ _ => Real.sqrt_nonneg _
          rw [ENNReal.ofReal_add (mul_nonneg (norm_nonneg _) (hlen _ _))
              (mul_nonneg (norm_nonneg _) (hlen _ _)),
            ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _)]
          calc _ ≤ A * (2 * ε t) + ε t * A :=
                add_le_add (mul_le_mul' (hA0 x) hgl) (mul_le_mul' hg0 (hA1 x))
            _ = 3 * A * ε t := by ring
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        have hzero := gradNorm_eq_zero_of_notMem_tsupport hT hχ1 hx
        constructor
        · simp [hχx]
        · have hle := hleib x
          rw [hzero] at hle
          simp only [hχx, Complex.ofReal_zero, norm_zero, zero_mul, mul_zero, add_zero] at hle
          rw [ENNReal.ofReal_of_nonpos hle]
          exact zero_le
    refine max_le ?_ (iSup_le fun x => (hpt x).2)
    rw [tupleSupNorm_ofSinglePoint]
    exact iSup_le fun x => (hpt x).1
  have hlim : Tendsto (fun t => 3 * A * ε t) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hε
      (Or.inr (ENNReal.mul_lt_top (by simp) hAfin).ne : (0 : ℝ≥0∞) ≠ 0 ∨ 3 * A ≠ ⊤)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    hbound
end YangMills.Construction.AmbientPoints.CutoffFourierSum
