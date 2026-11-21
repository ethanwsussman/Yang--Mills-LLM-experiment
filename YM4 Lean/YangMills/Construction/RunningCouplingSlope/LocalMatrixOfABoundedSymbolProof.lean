import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.PeriodicOperators.BoundOfTheKernelOfAMatrixFunctionProof
import YangMills.Construction.PeriodicOperators.ImaginaryShiftOfASymbol
import YangMills.Construction.PeriodicOperators.SymbolAtAPoint
import YangMills.Construction.PeriodicOperators.TorusKernelOfAPeriodicOperator
import YangMills.Construction.RunningCouplingSlope.DistanceOfTwoCellsProof
import YangMills.Construction.RunningCouplingSlope.LocalMatrixOfABoundedSymbol
import YangMills.Construction.RunningCouplingSlope.RateOfASymbolOnAStrip
import YangMills.Construction.Towers.SumsProductsAndTransposesOfDescendingKernelsProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator ENNReal
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.BoundedSymbolLocalMatrixProof
open Tower PeriodicOperators
open Tower.FreeStrip (SymbolBoundedOn)
open LocalKernels.Periodisation (periodSide)
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec l1NormVec)
private def finL2 {α : Type} [Fintype α] (f : α → ℂ) : ℝ := Real.sqrt (∑ p, ‖f p‖ ^ 2)
private theorem finL2_nonneg {α : Type} [Fintype α] (f : α → ℂ) : 0 ≤ finL2 f := Real.sqrt_nonneg _
private theorem opNorm_le_of_bilinear_le {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    (A : Matrix ι' ι ℂ) (X : ℝ) (hX : 0 ≤ X)
    (h : ∀ (f : ι → ℂ) (g : ι' → ℂ), ‖∑ u, ∑ v, g u * A u v * f v‖ ≤ X * finL2 f * finL2 g) :
    ‖A‖ ≤ X := by
  classical
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hX fun x => ?_
  set yv : ι' → ℂ := A.mulVec (WithLp.ofLp x) with hyv
  have e1 : ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := ι') (n := ι)).trans
      LinearMap.toContinuousLinearMap A) x = WithLp.toLp 2 yv := by
    simp [Matrix.toEuclideanLin_apply, hyv]
  rw [e1]
  have nx : ‖x‖ = finL2 (WithLp.ofLp x) := by
    rw [EuclideanSpace.norm_eq]; rfl
  have ny : ‖(WithLp.toLp 2 yv : EuclideanSpace ℂ ι')‖ = finL2 yv := by
    rw [EuclideanSpace.norm_eq]; rfl
  rw [nx, ny]
  have hc := h (WithLp.ofLp x) fun u => (starRingEnd ℂ) (yv u)
  have e2 : ∑ u, ∑ v, (starRingEnd ℂ) (yv u) * A u v * (WithLp.ofLp x) v =
      ((∑ u, ‖yv u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    have : yv u = ∑ v, A u v * (WithLp.ofLp x) v := by
      simp [hyv, Matrix.mulVec, dotProduct]
    calc ∑ v, (starRingEnd ℂ) (yv u) * A u v * (WithLp.ofLp x) v
        = (starRingEnd ℂ) (yv u) * ∑ v, A u v * (WithLp.ofLp x) v := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ = (starRingEnd ℂ) (yv u) * yv u := by rw [← this]
      _ = (‖yv u‖ : ℂ) ^ 2 := Complex.conj_mul' _
  have n3 : finL2 (fun u => (starRingEnd ℂ) (yv u)) = finL2 yv := by
    simp [finL2]
  rw [e2, n3, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)] at hc
  have hsq : ∑ u, ‖yv u‖ ^ 2 = finL2 yv ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)).symm
  rw [hsq] at hc
  by_cases hz : finL2 yv = 0
  · rw [hz]
    exact mul_nonneg hX (finL2_nonneg _)
  · have hp : 0 < finL2 yv := lt_of_le_of_ne (finL2_nonneg _) (Ne.symm hz)
    have : finL2 yv * finL2 yv ≤ (X * finL2 (WithLp.ofLp x)) * finL2 yv := by nlinarith
    exact le_of_mul_le_mul_right this hp
private theorem norm_torusAverage_le (g : AmbientSpace → ℂ) (X : ℝ) (hX : 0 ≤ X)
    (h : ∀ κ, ‖g κ‖ ≤ X) : ‖torusAverage g‖ ≤ X := by
  have hpi := Real.pi_pos
  unfold torusAverage
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < ((2 * Real.pi) ^ 4)⁻¹)]
  have hfin : volume (Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) < ∞ := by
    rw [Real.volume_Icc_pi]
    exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) hfin (f := g)
    (C := X) fun x _ => h x
  have hv : volume.real (Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) =
      (2 * Real.pi) ^ 4 := by
    rw [Measure.real, Real.volume_Icc_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ Real.pi - -Real.pi)]
    congr 1
    ring
  rw [hv] at hb
  calc ((2 * Real.pi) ^ 4)⁻¹ * ‖∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), g κ‖
      ≤ ((2 * Real.pi) ^ 4)⁻¹ * (X * (2 * Real.pi) ^ 4) := by gcongr
    _ = X := by field_simp
private theorem bilinDot_toComplexVec (κ v : AmbientSpace) :
    bilinDot (toComplexVec κ) (toComplexVec v) = ((∑ μ, κ μ * v μ : ℝ) : ℂ) := by
  simp [bilinDot, toComplexVec]
private theorem norm_exp_I_mul_ofReal (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.norm_exp_I_mul_ofReal <;> assumption
private theorem norm_exp_neg_I_mul_ofReal (r : ℝ) :
    ‖Complex.exp (-Complex.I * (r : ℂ))‖ = 1 := by
  have : -Complex.I * (r : ℂ) = ((-r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]
  exact Complex.norm_exp_ofReal_mul_I _
private theorem continuous_matFunIntegrand {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hAt : SymbolPointwise.Properties)
    (S : I'.Carrier → I.Carrier → ℂ) (hS : IsPeriodicKernel I I' S)
    (hF : ∀ κ : AmbientSpace, SymbolSummableAt I I' S (toComplexVec κ)) (ι' : I'.Carrier)
    (ι : I.Carrier) :
    Continuous (matFunIntegrand I I' (symbolHom I I' S) ι' ι) := by
  have e : matFunIntegrand I I' (symbolHom I I' S) ι' ι = fun κ =>
      (∑' n, symbolSummand I I' S (toComplexVec κ) ι' ι n) *
        Complex.exp (-Complex.I * bilinDot (toComplexVec κ)
          (toComplexVec (I.pos ι - I'.pos ι'))) := by
    funext κ
    have h := (hAt I I' hI hI' S (toComplexVec κ) hS (hF κ)).2.2.1 ι' ι
    simp only [matFunIntegrand]
    rw [h]
    rfl
  rw [e]
  have hn : ∀ (κ : AmbientSpace) n, ‖symbolSummand I I' S (toComplexVec κ) ι' ι n‖ =
      ‖S ι' (I.translate n ι)‖ := by
    intro κ n
    rw [symbolSummand, norm_mul, bilinDot_toComplexVec, norm_exp_I_mul_ofReal, mul_one]
  have hsum : Summable fun n => ‖S ι' (I.translate n ι)‖ := by
    have := hF 0 ι' ι
    simpa only [hn] using this
  have hdot : ∀ v : AmbientSpace,
      Continuous fun κ : AmbientSpace => bilinDot (toComplexVec κ) (toComplexVec v) := by
    intro v
    simp only [bilinDot, toComplexVec]
    fun_prop
  refine Continuous.mul ?_ ?_
  · refine continuous_tsum (fun n => ?_) hsum fun n κ => (hn κ n).le
    simp only [symbolSummand]
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (hdot _)))
  · exact Complex.continuous_exp.comp (continuous_const.mul (hdot _))
private theorem sum_comp_le_sum_of_injective {α J : Type} [Fintype α] [Fintype J] (cl : α → J)
    (hinj : Function.Injective cl) (F : J → ℝ) (hF : ∀ j, 0 ≤ F j) :
    ∑ p, F (cl p) ≤ ∑ j, F j := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := cl) (f := F) fun a _ b _ e => hinj e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hF j
abbrev _root_.YangMills.SharedProofs.p12339 := @sum_comp_le_sum_of_injective
private theorem quotWeight_eq_of_const {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hQ : Quotients.QuotientTransposeNorm) {w : ℝ}
    (hw : ∀ i, I.weightOf i = w) (c : I.UnitQuot) : I.quotWeight 1 c = w := by
  obtain ⟨ι, rfl⟩ := Quot.exists_rep c
  have h := ((hQ I I' hI hI' 1 one_pos).2.1 1 (Or.inl rfl)).1.2 ι
  exact h.trans (hw ι)
private theorem wNorm_of_const {J : Type} [Fintype J] (wt : J → ℝ) (a : ℝ) (hw : ∀ c, wt c = a)
    (h : J → ℂ) : wNorm wt h = Real.sqrt (a * ∑ c, ‖h c‖ ^ 2) := by
  simp [wNorm, tsum_fintype, Finset.mul_sum, hw]
private theorem quotHom_sq_sum_le {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hQ : Quotients.QuotientTransposeNorm) {w w' C : ℝ}
    (hw : 0 < w) (hwI : ∀ i, I.weightOf i = w) (hwI' : ∀ i, I'.weightOf i = w') (hC : 0 < C)
    [Fintype I.UnitQuot] [Fintype I'.UnitQuot] (M : QuotHom I I')
    (hM : quotHomNorm M ≤ ENNReal.ofReal C) (φ : I.UnitQuot → ℂ) :
    w' * ∑ c, ‖M φ c‖ ^ 2 ≤ C ^ 2 * (w * ∑ c, ‖φ c‖ ^ 2) := by
  have cw := quotWeight_eq_of_const hI hI' hQ hwI
  have cw' := quotWeight_eq_of_const hI' hI hQ hwI'
  set N := ∑ c, ‖φ c‖ ^ 2 with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => by positivity
  by_cases hz : N = 0
  · have hφ : φ = 0 := by
      funext c
      have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).1 hz c (Finset.mem_univ c)
      simpa using this
    simp [hφ, hz]
  set t : ℝ := (Real.sqrt (w * N))⁻¹ with ht
  have ht2 : t ^ 2 * (w * N) = 1 := by
    rw [ht, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  set ψ : I.UnitQuot → ℂ := (t : ℂ) • φ with hψ
  have hnψ : ∑ c, ‖ψ c‖ ^ 2 = t ^ 2 * N := by
    simp only [hψ, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, mul_pow, hN,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp
  have hball : ψ ∈ wUnitBall (I.quotWeight 1) (univ : Set (I.UnitQuot → ℂ)) := by
    refine ⟨mem_univ _, (hasSum_fintype _).summable, ?_⟩
    rw [wNorm_of_const _ w cw, hnψ]
    have : w * (t ^ 2 * N) = 1 := by linarith
    rw [this]
    simp
  have hb : ENNReal.ofReal (wNorm (I'.quotWeight 1) (M ψ)) ≤ quotHomNorm M := by
    unfold quotHomNorm wOpNorm
    exact le_iSup₂_of_le ψ hball le_rfl
  have hle := (ENNReal.ofReal_le_ofReal_iff hC.le).1 (hb.trans hM)
  rw [wNorm_of_const _ w' cw'] at hle
  have hsq := (Real.sqrt_le_iff.1 hle).2
  have hMψ : ∑ c, ‖M ψ c‖ ^ 2 = t ^ 2 * ∑ c, ‖M φ c‖ ^ 2 := by
    have : M ψ = (t : ℂ) • M φ := by rw [hψ, map_smul]
    rw [this]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, mul_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp
  rw [hMψ] at hsq
  calc w' * ∑ c, ‖M φ c‖ ^ 2 = (w' * (t ^ 2 * ∑ c, ‖M φ c‖ ^ 2)) * (w * N) := by
        have : w' * (t ^ 2 * ∑ c, ‖M φ c‖ ^ 2) * (w * N) =
            w' * (∑ c, ‖M φ c‖ ^ 2) * (t ^ 2 * (w * N)) := by ring
        rw [this, ht2, mul_one]
    _ ≤ C ^ 2 * (w * N) := by gcongr
private theorem bilinear_le_of_symbol_bound {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hQ : Quotients.QuotientTransposeNorm)
    (hAt : SymbolPointwise.Properties) (hK : SymbolKernel.KernelOfSymbol)
    {w w' C : ℝ} (hw : 0 < w) (hw' : 0 < w') (hwI : ∀ i, I.weightOf i = w)
    (hwI' : ∀ i, I'.weightOf i = w') (hC : 0 < C)
    (S : I'.Carrier → I.Carrier → ℂ) (hS : IsPeriodicKernel I I' S)
    (hF : ∀ κ : AmbientSpace, SymbolSummableAt I I' S (toComplexVec κ))
    (hB : ∀ κ : AmbientSpace, quotHomNorm (symbolHom I I' S (toComplexVec κ)) ≤ ENNReal.ofReal C)
    {α α' : Type} [Fintype α] [Fintype α'] (a : α → I.Carrier) (a' : α' → I'.Carrier)
    (ha : Function.Injective fun p => I.mkQuot 1 (a p))
    (ha' : Function.Injective fun p => I'.mkQuot 1 (a' p))
    (f : α → ℂ) (g : α' → ℂ) :
    ‖∑ p', ∑ p, g p' * S (a' p') (a p) * f p‖ ≤ C * Real.sqrt (w / w') * finL2 f * finL2 g := by
  classical
  have hfin : Finite I.UnitQuot := hI.finite_quot
  have hfin' : Finite I'.UnitQuot := hI'.finite_quot
  let _ : Fintype I.UnitQuot := Fintype.ofFinite _
  let _ : Fintype I'.UnitQuot := Fintype.ofFinite _
  set Φ : AmbientSpace → ℂ := fun κ => ∑ p', ∑ p, g p' *
    matFunIntegrand I I' (symbolHom I I' S) (a' p') (a p) κ * f p with hΦ
  have hcont := continuous_matFunIntegrand hI hI' hAt S hS hF
  have hint : ∀ p' p, IntegrableOn (matFunIntegrand I I' (symbolHom I I' S) (a' p') (a p))
      (Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) := fun p' p =>
    (hcont _ _).continuousOn.integrableOn_compact isCompact_Icc
  have e1 : ∑ p', ∑ p, g p' * S (a' p') (a p) * f p = torusAverage Φ := by
    have hS' : ∀ p' p, S (a' p') (a p) =
        torusAverage (matFunIntegrand I I' (symbolHom I I' S) (a' p') (a p)) := by
      intro p' p
      conv_lhs => rw [← hK I I' hI hI' S hS]
      rfl
    unfold torusAverage
    simp only [hΦ]
    rw [integral_finsetSum _ fun p' _ => integrable_finsetSum _ fun p _ =>
      ((hint p' p).const_mul (g p')).mul_const (f p)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [integral_finsetSum _ fun p _ => ((hint p' p).const_mul (g p')).mul_const (f p)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hS', integral_mul_const, integral_const_mul]
    unfold torusAverage
    ring
  rw [e1]
  refine norm_torusAverage_le _ _ (by positivity [finL2_nonneg f, finL2_nonneg g]) fun κ => ?_
  set M := symbolHom I I' S (toComplexVec κ) with hM
  let cl : α → I.UnitQuot := fun p => I.mkQuot 1 (a p)
  let cl' : α' → I'.UnitQuot := fun p => I'.mkQuot 1 (a' p)
  let e : α → ℂ := fun p => Complex.exp (-Complex.I *
    bilinDot (toComplexVec κ) (toComplexVec (I.pos (a p))))
  let e' : α' → ℂ := fun p => Complex.exp (Complex.I *
    bilinDot (toComplexVec κ) (toComplexVec (I'.pos (a' p))))
  have he : ∀ p, ‖e p‖ = 1 := fun p => by
    simp only [e]
    rw [bilinDot_toComplexVec, norm_exp_neg_I_mul_ofReal]
  have he' : ∀ p, ‖e' p‖ = 1 := fun p => by
    simp only [e']
    rw [bilinDot_toComplexVec, norm_exp_I_mul_ofReal]
  let φ : I.UnitQuot → ℂ := ∑ p, (f p * e p) • (Pi.single (cl p) (1 : ℂ) : I.UnitQuot → ℂ)
  have hMφ : ∀ c', M φ c' = ∑ p, f p * e p * M (Pi.single (cl p) 1) c' := by
    intro c'
    simp only [φ, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hΦκ : Φ κ = ∑ p', (g p' * e' p') * M φ (cl' p') := by
    simp only [hΦ]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [hMφ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hexp : Complex.exp (-Complex.I * bilinDot (toComplexVec κ)
        (toComplexVec (I.pos (a p) - I'.pos (a' p')))) = e p * e' p' := by
      simp only [e, e']
      rw [← Complex.exp_add]
      congr 1
      simp only [bilinDot, toComplexVec, Pi.sub_apply, Complex.ofReal_sub, mul_sub,
        Finset.sum_sub_distrib]
      ring
    simp only [matFunIntegrand, carrierEntry, linearMapEntry]
    rw [hexp]
    simp only [cl, cl', ← hM]
    ring
  have hφ1 : ∀ p, φ (cl p) = f p * e p := by
    intro p
    simp only [φ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single p]
    · simp
    · intro b _ hb
      have : cl p ≠ cl b := fun h => hb (ha h).symm
      simp [Pi.single_apply, this]
    · simp
  have hφ0 : ∀ c, c ∉ Finset.image cl Finset.univ → φ c = 0 := by
    intro c hc
    simp only [φ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun p _ => ?_
    have : c ≠ cl p := fun h => hc (h ▸ Finset.mem_image_of_mem cl (Finset.mem_univ p))
    simp [Pi.single_apply, this]
  have hNφ : ∑ c, ‖φ c‖ ^ 2 = ∑ p, ‖f p‖ ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.image cl Finset.univ))
      fun c _ hc => by simp [hφ0 c hc]]
    rw [Finset.sum_image fun x _ y _ h => ha h]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hφ1, norm_mul, he, mul_one]
  have hsq := quotHom_sq_sum_le hI hI' hQ hw hwI hwI' hC M (hB κ) φ
  rw [hNφ] at hsq
  set N' := ∑ c, ‖M φ c‖ ^ 2 with hN'
  have hcs : ‖Φ κ‖ ≤ finL2 g * Real.sqrt N' := by
    rw [hΦκ]
    calc ‖∑ p', (g p' * e' p') * M φ (cl' p')‖
        ≤ ∑ p', ‖g p'‖ * ‖M φ (cl' p')‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p' _ => ?_)
          rw [norm_mul, norm_mul, he', mul_one]
      _ ≤ Real.sqrt (∑ p', ‖g p'‖ ^ 2) * Real.sqrt (∑ p', ‖M φ (cl' p')‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ finL2 g * Real.sqrt N' := by
          refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (finL2_nonneg g)
          exact sum_comp_le_sum_of_injective cl' ha' (fun c => ‖M φ c‖ ^ 2) fun _ => by positivity
  have hroot : Real.sqrt N' ≤ C * Real.sqrt (w / w') * finL2 f := by
    have hN'0 : 0 ≤ ∑ p, ‖f p‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    refine Real.sqrt_le_iff.2 ⟨by positivity [finL2_nonneg f], ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), finL2, Real.sq_sqrt hN'0]
    have : N' = (w' * N') / w' := by field_simp
    rw [this, div_le_iff₀ hw']
    calc w' * N' ≤ C ^ 2 * (w * ∑ p, ‖f p‖ ^ 2) := hsq
      _ = C ^ 2 * (w / w') * (∑ p, ‖f p‖ ^ 2) * w' := by field_simp
  calc ‖Φ κ‖ ≤ finL2 g * Real.sqrt N' := hcs
    _ ≤ finL2 g * (C * Real.sqrt (w / w') * finL2 f) :=
        mul_le_mul_of_nonneg_left hroot (finL2_nonneg g)
    _ = C * Real.sqrt (w / w') * finL2 f * finL2 g := by ring
private theorem euclidNormVec_le_l1NormVec (v : Fin 4 → ℝ) : euclidNormVec v ≤ l1NormVec v := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.euclidNormVec_le_l1NormVec <;> assumption
private theorem bilinear_le_exp_decay {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hQ : Quotients.QuotientTransposeNorm)
    (hAt : SymbolPointwise.Properties) (hK : SymbolKernel.KernelOfSymbol)
    (hRate : DecayFromStripSymbol) (hIm : SymbolImShift.Claim)
    {w w' C υ : ℝ} (hυ : 0 < υ) (hw : 0 < w) (hw' : 0 < w') (hwI : ∀ i, I.weightOf i = w)
    (hwI' : ∀ i, I'.weightOf i = w') (hC : 0 < C)
    (T : I'.Carrier → I.Carrier → ℂ) (hT : IsPeriodicKernel I I' T)
    (hB : SymbolBoundedOn I I' T (imStrip υ) C) (θ : AmbientSpace) (hθ : ∀ μ, |θ μ| = υ / 4)
    {α α' : Type} [Fintype α] [Fintype α'] (a : α → I.Carrier) (a' : α' → I'.Carrier)
    (ha : Function.Injective fun p => I.mkQuot 1 (a p))
    (ha' : Function.Injective fun p => I'.mkQuot 1 (a' p))
    (z z' : AmbientSpace) (hz : ∀ p μ, |I.pos (a p) μ - z μ| ≤ 1)
    (hz' : ∀ p μ, |I'.pos (a' p) μ - z' μ| ≤ 1) (f : α → ℂ) (g : α' → ℂ) :
    ‖∑ p', ∑ p, g p' * T (a' p') (a p) * f p‖ ≤
      Real.exp (2 * υ) * Real.exp (-(∑ μ, θ μ * (z' μ - z μ))) *
        (C * Real.sqrt (w / w') * finL2 f * finL2 g) := by
  obtain ⟨C₁, hC₁, hb⟩ := hRate I I' hI hI' T υ hυ hT.1 hB.1
  have hrate : IsDecayRate I I' T υ := by
    refine ⟨hυ, C₁, hC₁, fun ι' ι => (hb ι' ι).trans ?_⟩
    refine mul_le_mul_of_nonneg_left ?_ hC₁.le
    refine Real.exp_le_exp.2 ?_
    have := euclidNormVec_le_l1NormVec (I'.pos ι' - I.pos ι)
    nlinarith
  have hE : euclidNormVec θ = υ / 2 := by
    have : ∑ μ, θ μ ^ 2 = (υ / 2) ^ 2 := by
      simp only [← sq_abs (θ _), hθ, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
      ring
    rw [euclidNormVec, this, Real.sqrt_sq (by positivity)]
  have hshift : ∀ κ : AmbientSpace, IsPeriodicKernel I I' (expConj I I' θ T) ∧
      SymbolSummableAt I I' (expConj I I' θ T) (toComplexVec κ) ∧
      fourierSymbol I I' (expConj I I' θ T) (toComplexVec κ) =
        fourierSymbol I I' T (addIVec (toComplexVec κ) θ) := by
    intro κ
    refine hIm I I' hI hI' T υ hT hrate θ (by rw [hE]; linarith) (toComplexVec κ) ?_
    have : imVec (toComplexVec κ) = 0 := by
      funext μ
      simp [imVec, toComplexVec]
    simp only [strictImStrip, mem_setOf_eq, this, hE]
    simp [euclidNormVec]
    linarith
  set S := expConj I I' θ T with hSdef
  have hBS : ∀ κ : AmbientSpace, quotHomNorm (symbolHom I I' S (toComplexVec κ)) ≤
      ENNReal.ofReal C := by
    intro κ
    have e : symbolHom I I' S (toComplexVec κ) =
        symbolHom I I' T (addIVec (toComplexVec κ) θ) := by
      unfold symbolHom
      rw [(hshift κ).2.2]
    rw [e]
    refine hB.2 _ fun μ => ?_
    simp only [addIVec, toComplexVec, Complex.add_im, Complex.ofReal_im, zero_add,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul]
    simp only [add_zero, hθ μ]
    linarith
  let r : AmbientSpace → ℝ := fun u => ∑ μ, θ μ * u μ
  have hST : ∀ ι' ι, S ι' ι =
      ((Real.exp (r (I'.pos ι') - r (I.pos ι)) : ℝ) : ℂ) * T ι' ι := by
    intro ι' ι
    simp only [hSdef, expConj]
    congr 1
    rw [bilinDot_toComplexVec, Complex.ofReal_exp]
    congr 2
    simp only [r, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hTS : ∀ ι' ι, T ι' ι =
      ((Real.exp (-(r (I'.pos ι') - r (I.pos ι))) : ℝ) : ℂ) * S ι' ι := by
    intro ι' ι
    rw [hST, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hwidth : ∀ (x y : AmbientSpace), (∀ μ, |x μ - y μ| ≤ 1) → |r x - r y| ≤ υ := by
    intro x y h
    have e : r x - r y = ∑ μ, θ μ * (x μ - y μ) := by
      simp only [r, mul_sub, Finset.sum_sub_distrib]
    rw [e]
    calc |∑ μ, θ μ * (x μ - y μ)| ≤ ∑ μ, |θ μ * (x μ - y μ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _μ : Fin 4, υ / 4 := by
          refine Finset.sum_le_sum fun μ _ => ?_
          rw [abs_mul, hθ]
          have := h μ
          nlinarith
      _ = υ := by simp; ring
  let f₁ : α → ℂ := fun p => ((Real.exp (r (I.pos (a p)) - r z) : ℝ) : ℂ) * f p
  let g₁ : α' → ℂ := fun p => ((Real.exp (-(r (I'.pos (a' p)) - r z')) : ℝ) : ℂ) * g p
  have hn : ∀ {β : Type} [Fintype β] (b : β → ℂ) (d : β → ℝ), (∀ p, |d p| ≤ υ) →
      finL2 (fun p => ((Real.exp (d p) : ℝ) : ℂ) * b p) ≤ Real.exp υ * finL2 b := by
    intro β _ b d h
    have : Real.exp υ = Real.sqrt (Real.exp υ ^ 2) := (Real.sqrt_sq (Real.exp_pos _).le).symm
    rw [this, finL2, finL2, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have : Real.exp (d p) ≤ Real.exp υ := Real.exp_le_exp.2 (le_of_abs_le (h p))
    gcongr
  have hf₁ : finL2 f₁ ≤ Real.exp υ * finL2 f := hn f _ fun p => hwidth _ _ (hz p)
  have hg₁ : finL2 g₁ ≤ Real.exp υ * finL2 g := hn g _ fun p => by
    rw [abs_neg]
    exact hwidth _ _ (hz' p)
  have hform := bilinear_le_of_symbol_bound hI hI' hQ hAt hK hw hw' hwI hwI' hC S (hshift 0).1
    (fun κ => (hshift κ).2.1) hBS a a' ha ha' f₁ g₁
  have hid : ∑ p', ∑ p, g p' * T (a' p') (a p) * f p =
      ((Real.exp (-(r z' - r z)) : ℝ) : ℂ) * ∑ p', ∑ p, g₁ p' * S (a' p') (a p) * f₁ p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hTS]
    simp only [f₁, g₁]
    have : Real.exp (-(r (I'.pos (a' p')) - r (I.pos (a p)))) =
        Real.exp (-(r z' - r z)) * Real.exp (-(r (I'.pos (a' p')) - r z')) *
          Real.exp (r (I.pos (a p)) - r z) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [this]
    push_cast
    ring
  have hrz : r z' - r z = ∑ μ, θ μ * (z' μ - z μ) := by
    simp only [r, mul_sub, Finset.sum_sub_distrib]
  rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, hrz]
  have hs : 0 ≤ C * Real.sqrt (w / w') := by positivity
  have hexp2 : Real.exp (2 * υ) = Real.exp υ * Real.exp υ := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmain : ‖∑ p', ∑ p, g₁ p' * S (a' p') (a p) * f₁ p‖ ≤
      Real.exp (2 * υ) * (C * Real.sqrt (w / w') * finL2 f * finL2 g) := by
    refine hform.trans ?_
    calc C * Real.sqrt (w / w') * finL2 f₁ * finL2 g₁
        ≤ C * Real.sqrt (w / w') * (Real.exp υ * finL2 f) * (Real.exp υ * finL2 g) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hf₁ hs) hg₁ (finL2_nonneg _)
            (mul_nonneg hs (mul_nonneg (Real.exp_pos _).le (finL2_nonneg _)))
      _ = Real.exp (2 * υ) * (C * Real.sqrt (w / w') * finL2 f * finL2 g) := by
          rw [hexp2]
          ring
  calc Real.exp (-∑ μ, θ μ * (z' μ - z μ)) * ‖∑ p', ∑ p, g₁ p' * S (a' p') (a p) * f₁ p‖
      ≤ Real.exp (-∑ μ, θ μ * (z' μ - z μ)) *
        (Real.exp (2 * υ) * (C * Real.sqrt (w / w') * finL2 f * finL2 g)) :=
        mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
    _ = _ := by ring
private theorem cellOfCoords_coe (L n k : ℕ) (hL : 0 < L) (z : Fin 4 → ℤ) (μ : Fin 4) :
    ((cellOfCoords L n k z : Tower.Vertex L n k k) : PeriodicLattice.FourTorus L n) μ =
      (((z μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.CellDistance.coe_cellOfCoords <;> assumption
private theorem torusSide_eq_periodSide (L n : ℕ) :
    PeriodicLattice.torusSide L n = (periodSide L n : ℝ) := by
  simp [PeriodicLattice.torusSide, periodSide]
private theorem exists_period_of_cellOfCoords_eq {L n k : ℕ} (hL : 0 < L) {z z' : Fin 4 → ℤ}
    (h : cellOfCoords L n k z = cellOfCoords L n k z') :
    ∃ m : Fin 4 → ℤ, z' = z + periodSide L n • m := by
  have hμ : ∀ μ, ∃ t : ℤ, z' μ = z μ + periodSide L n * t := by
    intro μ
    have e := congrFun (congrArg (fun y : Tower.Vertex L n k k =>
      (y : PeriodicLattice.FourTorus L n)) h) μ
    simp only [cellOfCoords_coe L n k hL] at e
    have e2 : (((z' μ - z μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) = 0 := by
      rw [AddCircle.coe_sub, e, sub_self]
    obtain ⟨t, ht⟩ := (AddCircle.coe_eq_zero_iff _).1 e2
    refine ⟨t, ?_⟩
    rw [torusSide_eq_periodSide] at ht
    have : ((z' μ : ℤ) : ℝ) = ((z μ + periodSide L n * t : ℤ) : ℝ) := by
      push_cast
      simp only [zsmul_eq_mul] at ht
      linarith
    exact_mod_cast this
  choose m hm using hμ
  refine ⟨m, ?_⟩
  funext μ
  simp [hm μ]
private theorem cellDist_le_lift {L n k : ℕ} (hL : 0 < L) (z z' m : Fin 4 → ℤ) :
    cellDist (cellOfCoords L n k z') (cellOfCoords L n k z) ≤
      euclidNormVec (castVec (z' - z - periodSide L n • m)) := by
  unfold cellDist TorusMetric.torusEuclidNorm
  refine csInf_le ⟨0, ?_⟩ ⟨castVec (z' - z - periodSide L n • m), ?_, rfl⟩
  · rintro _ ⟨v, -, rfl⟩
    exact Real.sqrt_nonneg _
  · simp only [mem_preimage, mem_singleton_iff]
    funext μ
    rw [Pi.sub_apply, cellOfCoords_coe L n k hL, cellOfCoords_coe L n k hL]
    simp only [TorusMetric.torusProj, castVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    have hper : (((periodSide L n • m μ : ℤ) : ℝ) :
        AddCircle (PeriodicLattice.torusSide L n)) = 0 := by
      refine (AddCircle.coe_eq_zero_iff _).2 ⟨m μ, ?_⟩
      rw [torusSide_eq_periodSide, zsmul_eq_mul]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    rw [AddCircle.coe_sub, AddCircle.coe_sub, hper, sub_zero]
private theorem exists_translate_of_mkQuot_eq {I : PeriodicData} (hI : IsPeriodic I) (s : ℕ)
    {ι ι' : I.Carrier} (e : I.mkQuot s ι = I.mkQuot s ι') :
    ∃ n : Fin 4 → ℤ, ι' = I.translate (s • n) ι := by apply _root_.YangMills.Construction.LocalKernels.DescendingKernels.exists_translate_of_mkQuot_eq <;> assumption
private theorem exists_separated_lifts {L n k : ℕ} (hL : 0 < L) {I : PeriodicData}
    (hI : IsPeriodic I) {ι : Type} {q : I.Carrier → ι} {c : ι → Tower.Vertex L n k k}
    (hq : IsCellQuotient L n k I q c) (y : Tower.Vertex L n k k) (z : Fin 4 → ℤ)
    (hz : cellOfCoords L n k z = y) :
    ∃ l : {p // c p = y} → I.Carrier, (∀ p, q (l p) = p.1) ∧
      (∀ p μ, |I.pos (l p) μ - (z μ : ℝ)| ≤ 1) ∧
      Function.Injective fun p => I.mkQuot 1 (l p) := by
  have h1 : ∀ p : {p // c p = y}, ∃ i, q i = p.1 ∧ ∀ μ, |I.pos i μ - (z μ : ℝ)| ≤ 1 := by
    rintro ⟨p, hp⟩
    obtain ⟨i, rfl⟩ := hq.surjective p
    obtain ⟨zi, hzi, hnear⟩ := hq.exists_near_cell i
    obtain ⟨m, hm⟩ := exists_period_of_cellOfCoords_eq hL (hz.trans (hp.symm.trans hzi.symm))
    refine ⟨I.translate (periodSide L n • (-m)) i,
      ((hq.image_eq_iff _ _).2 ⟨-m, rfl⟩).symm, fun μ => ?_⟩
    rw [hI.pos_translate]
    have := hnear μ
    rw [hm] at this
    have e : (I.pos i + castVec (periodSide L n • (-m))) μ - (z μ : ℝ) =
        I.pos i μ - (((z + periodSide L n • m) μ : ℤ) : ℝ) := by
      have hsm : ∀ (t : Fin 4 → ℤ) (ν : Fin 4), (periodSide L n • t) ν =
          (periodSide L n : ℤ) * t ν := fun t ν => by rw [Pi.smul_apply, nsmul_eq_mul]
      simp only [castVec, Pi.add_apply, hsm, Pi.neg_apply]
      push_cast
      ring
    rw [e]
    exact this
  choose l hl hnear using h1
  refine ⟨l, hl, hnear, fun p p₂ e => ?_⟩
  obtain ⟨m, hm⟩ := exists_translate_of_mkQuot_eq hI 1 e
  simp only [one_smul] at hm
  have h2 : c (q (l p)) = c (q (I.translate m (l p))) := by
    rw [← hm, hl, hl, p.2, p₂.2]
  have h3 := hq.eq_of_same_cell (l p) m h2
  rw [← hm, hl, hl] at h3
  exact Subtype.ext h3
private theorem block_bilinear_le {υ : ℝ} (hυ : 0 < υ) (hQ : Quotients.QuotientTransposeNorm)
    (hAt : SymbolPointwise.Properties) (hK : SymbolKernel.KernelOfSymbol)
    (hRate : DecayFromStripSymbol) (hIm : SymbolImShift.Claim)
    (hTorus : Periodized.Claim) (hSum : ExponentialSums.Bounds)
    {L n k : ℕ} (hL : 0 < L) (hn : 0 < periodSide L n) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {w w' C : ℝ}
    (hw : 0 < w) (hw' : 0 < w') (hwI : ∀ i, I.weightOf i = w) (hwI' : ∀ i, I'.weightOf i = w')
    {ι ι' : Type} {q : I.Carrier → ι} {q' : I'.Carrier → ι'} {c : ι → Tower.Vertex L n k k}
    {c' : ι' → Tower.Vertex L n k k} (hq : IsCellQuotient L n k I q c)
    (hq' : IsCellQuotient L n k I' q' c')
    (T : I'.Carrier → I.Carrier → ℂ) (hC : 0 < C) (hT : IsPeriodicKernel I I' T)
    (hB : SymbolBoundedOn I I' T (imStrip υ) C) (M : ι' → ι → ℂ)
    (hM : ∀ i' i, M (q' i') (q i) = periodization I I' T (periodSide L n) i' i)
    (y' y : Tower.Vertex L n k k) [Fintype {p // c p = y}] [Fintype {p // c' p = y'}]
    (f : {p // c p = y} → ℂ) (g : {p // c' p = y'} → ℂ) :
    ‖∑ p', ∑ p, g p' * M p'.1 p.1 * f p‖ ≤
      (Real.exp (2 * υ) * (Real.exp (2 * (υ / 8)) * expHalfSum (υ / 8) ^ 4)) * C *
        Real.sqrt (w / w') * Real.exp (-((υ / 8) * cellDist y' y)) * finL2 f * finL2 g := by
  have hc₀ : 0 < υ / 8 := by positivity
  obtain ⟨-, hS, -⟩ := hSum (υ / 8) hc₀
  rcases isEmpty_or_nonempty {p // c p = y} with hE | ⟨⟨p₀⟩⟩
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, norm_zero]
    have := finL2_nonneg f
    have := finL2_nonneg g
    positivity
  rcases isEmpty_or_nonempty {p // c' p = y'} with hE | ⟨⟨p₀'⟩⟩
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    have := finL2_nonneg f
    have := finL2_nonneg g
    positivity
  obtain ⟨i₀, hi₀⟩ := hq.surjective p₀.1
  obtain ⟨z, hzc, -⟩ := hq.exists_near_cell i₀
  have hzy : cellOfCoords L n k z = y := by rw [hzc, hi₀, p₀.2]
  obtain ⟨i₀', hi₀'⟩ := hq'.surjective p₀'.1
  obtain ⟨z', hzc', -⟩ := hq'.exists_near_cell i₀'
  have hzy' : cellOfCoords L n k z' = y' := by rw [hzc', hi₀', p₀'.2]
  obtain ⟨l, hl, hnear, hinj⟩ := exists_separated_lifts hL hI hq y z hzy
  obtain ⟨l', hl', hnear', hinj'⟩ := exists_separated_lifts hL hI' hq' y' z' hzy'
  set s := periodSide L n with hs
  obtain ⟨δ, hδ⟩ : ∃ δ, IsDecayRate I I' T δ := by
    obtain ⟨hcov, C₁, δ, hC₁, hδ, hb⟩ := hT
    exact ⟨δ, hδ, C₁, hC₁, hb⟩
  have hfacts := hTorus I I' hI hI' T δ hT hδ
  let a : (Fin 4 → ℤ) → {p // c p = y} → I.Carrier := fun m p => I.translate (s • m) (l p)
  let G : (Fin 4 → ℤ) → ℂ := fun m => ∑ p', ∑ p, g p' * T (l' p') (a m p) * f p
  have hG : HasSum G (∑ p', ∑ p, g p' * M p'.1 p.1 * f p) := by
    refine hasSum_sum fun p' _ => hasSum_sum fun p _ => ?_
    have h1 : HasSum (fun m => T (l' p') (a m p)) (M p'.1 p.1) := by
      have e := hM (l' p') (l p)
      rw [hl', hl] at e
      rw [e]
      exact (hfacts.summable s hn (l' p') (l p)).of_norm.hasSum
    exact (h1.mul_left (g p')).mul_right (f p)
  set F := Real.exp (2 * υ) * (C * Real.sqrt (w / w') * finL2 f * finL2 g) with hF
  have hF0 : 0 ≤ F := by
    have := finL2_nonneg f
    have := finL2_nonneg g
    positivity
  set d := cellDist y' y with hd
  let yv : AmbientSpace := castVec (z - z')
  let u : (Fin 4 → ℤ) → ℝ := fun m =>
    Real.exp (-(υ / 8) * euclidNormVec (yv + castVec (s • m)))
  have hsm : Function.Injective fun m : Fin 4 → ℤ => s • m := by
    intro m m' e
    funext μ
    have := congrFun e μ
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    simpa [nsmul_eq_mul, hs0, hn.ne'] using this
  have hu : Summable u := (hS yv).1.comp_injective hsm
  have huV : ∑' m, u m ≤ Real.exp (2 * (υ / 8)) * expHalfSum (υ / 8) ^ 4 := by
    refine le_trans ?_ (hS yv).2
    refine hu.tsum_le_of_sum_le fun t => ?_
    classical
    have e : ∑ m ∈ t, u m =
        ∑ v ∈ t.image fun m : Fin 4 → ℤ => s • m,
          Real.exp (-(υ / 8) * euclidNormVec (yv + castVec v)) := by
      rw [Finset.sum_image fun x _ y _ h => hsm h]
    rw [e]
    exact (hS yv).1.sum_le_tsum _ fun _ _ => (Real.exp_pos _).le
  have hbound : ∀ m, ‖G m‖ ≤ (F * Real.exp (-((υ / 8) * d))) * u m := by
    intro m
    set v : Fin 4 → ℤ := z' - z - s • m with hv
    let θ : AmbientSpace := fun μ => if 0 ≤ v μ then υ / 4 else -(υ / 4)
    have hθ : ∀ μ, |θ μ| = υ / 4 := by
      intro μ
      simp only [θ]
      split_ifs <;> simp [abs_of_pos (by positivity : 0 < υ / 4)]
    have hinjm : Function.Injective fun p => I.mkQuot 1 (a m p) := by
      intro p p₂ e
      have hcl : ∀ p, I.mkQuot 1 (a m p) = I.mkQuot 1 (l p) := fun p =>
        (Quot.sound ⟨s • m, by rw [one_smul]⟩ : I.mkQuot 1 (l p) = I.mkQuot 1 (a m p)).symm
      refine hinj ?_
      simpa only [hcl] using e
    have hform := bilinear_le_exp_decay hI hI' hQ hAt hK hRate hIm hυ hw hw' hwI hwI' hC T hT
      hB θ hθ (a m) l' hinjm hinj' (castVec z + castVec (s • m)) (castVec z')
      (fun p μ => by
        simp only [a]
        rw [hI.pos_translate]
        have := hnear p μ
        simp only [castVec, Pi.add_apply] at this ⊢
        rwa [add_sub_add_right_eq_sub])
      (fun p μ => hnear' p μ) f g
    have hsum : ∑ μ, θ μ * (castVec z' μ - (castVec z + castVec (s • m)) μ) =
        (υ / 4) * l1NormVec (castVec v) := by
      simp only [l1NormVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      have e : castVec z' μ - (castVec z + castVec (s • m)) μ = castVec v μ := by
        simp [castVec, hv]
        ring
      rw [e]
      simp only [θ]
      by_cases h : 0 ≤ v μ
      · have h' : 0 ≤ castVec v μ := by simpa [castVec] using h
        rw [if_pos h, abs_of_nonneg h']
      · have h' : castVec v μ < 0 := by simpa [castVec] using not_le.1 h
        rw [if_neg h, abs_of_neg h']
        ring
    rw [hsum] at hform
    have hE : euclidNormVec (yv + castVec (s • m)) = euclidNormVec (castVec v) := by
      have : ∀ μ, (yv + castVec (s • m)) μ = -(castVec v μ) := by
        intro μ
        simp [yv, castVec, hv]
        ring
      simp only [euclidNormVec, this, neg_sq]
    have hdE : d ≤ euclidNormVec (castVec v) := by
      rw [hd, ← hzy, ← hzy']
      exact cellDist_le_lift hL z z' m
    have hl1 := euclidNormVec_le_l1NormVec (castVec v)
    refine hform.trans ?_
    have hexp : Real.exp (-((υ / 4) * l1NormVec (castVec v))) ≤
        Real.exp (-((υ / 8) * d)) * u m := by
      simp only [u]
      rw [hE, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith
    calc Real.exp (2 * υ) * Real.exp (-((υ / 4) * l1NormVec (castVec v))) *
          (C * Real.sqrt (w / w') * finL2 f * finL2 g)
        = F * Real.exp (-((υ / 4) * l1NormVec (castVec v))) := by rw [hF]; ring
      _ ≤ F * (Real.exp (-((υ / 8) * d)) * u m) := mul_le_mul_of_nonneg_left hexp hF0
      _ = F * Real.exp (-((υ / 8) * d)) * u m := by ring
  have htot := hG.norm_le_of_bounded (hu.hasSum.mul_left (F * Real.exp (-((υ / 8) * d)))) hbound
  refine htot.trans ?_
  calc F * Real.exp (-((υ / 8) * d)) * ∑' m, u m
      ≤ F * Real.exp (-((υ / 8) * d)) * (Real.exp (2 * (υ / 8)) * expHalfSum (υ / 8) ^ 4) :=
        mul_le_mul_of_nonneg_left huV (mul_nonneg hF0 (Real.exp_pos _).le)
    _ = _ := by rw [hF]; ring
private theorem sum_ite_eq_sum_subtype {J : Type} [Fintype J] (P : J → Prop) [DecidablePred P]
    [Fintype {u // P u}] (F : J → ℂ) :
    ∑ u, (if P u then F u else 0) = ∑ p : {u // P u}, F p.1 :=
  (Finset.sum_filter P F).symm.trans (Finset.sum_subtype _ (by simp) F)
private theorem finL2_restrict_le {J : Type} [Fintype J] (P : J → Prop) [Fintype {u // P u}]
    (f : J → ℂ) : finL2 (fun p : {u // P u} => f p.1) ≤ finL2 f :=
  Real.sqrt_le_sqrt (sum_comp_le_sum_of_injective (fun p : {u // P u} => p.1)
    Subtype.val_injective (fun u => ‖f u‖ ^ 2) fun _ => by positivity)
theorem boundedSymbolLocalMatrix_holds (hQ : Quotients.QuotientTransposeNorm)
    (hAt : SymbolPointwise.Properties) (hK : SymbolKernel.KernelOfSymbol)
    (hRate : DecayFromStripSymbol) (hIm : SymbolImShift.Claim)
    (hTorus : Periodized.Claim) (hSum : ExponentialSums.Bounds) :
    BoundedSymbolLocalMatrix := by
  intro υ hυ
  refine ⟨Real.exp (2 * υ) * (Real.exp (2 * (υ / 8)) * expHalfSum (υ / 8) ^ 4) + 1, υ / 8,
    by positivity, by positivity, ?_⟩
  intro L n k hL hn I I' hI hI' w w' hw hw' hwI hwI' ι ι' _ _ _ q q' c c' hq hq' T C hC hT hB M hM y' y
  classical
  have hL0 : 0 < L := by have := hL.2; omega
  have hs : 0 < periodSide L n := by
    simp only [periodSide]
    positivity
  set K₀ := Real.exp (2 * υ) * (Real.exp (2 * (υ / 8)) * expHalfSum (υ / 8) ^ 4) with hK₀
  set X := K₀ * C * Real.sqrt (w / w') * Real.exp (-((υ / 8) * cellDist y' y)) with hX
  have hX0 : 0 ≤ X := by positivity
  have hnorm : ‖blockBetween c c' M y' y‖ ≤ X := by
    refine opNorm_le_of_bilinear_le _ X hX0 fun f g => ?_
    have e : ∑ u, ∑ v, g u * blockBetween c c' M y' y u v * f v =
        ∑ p' : {u // c' u = y'}, ∑ p : {v // c v = y},
          (g p'.1) * M p'.1 p.1 * (f p.1) := by
      rw [← sum_ite_eq_sum_subtype (fun u => c' u = y')
        (fun u => ∑ p : {v // c v = y}, g u * M u p.1 * f p.1)]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : c' u = y'
      · rw [if_pos hu, ← sum_ite_eq_sum_subtype (fun v => c v = y) (fun v => g u * M u v * f v)]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : c v = y <;> simp [blockBetween, hu, hv]
      · rw [if_neg hu]
        refine Finset.sum_eq_zero fun v _ => ?_
        simp [blockBetween, hu]
    rw [e]
    have hb := block_bilinear_le hυ hQ hAt hK hRate hIm hTorus hSum hL0 hs hI hI' hw hw' hwI
      hwI' hq hq' T hC hT hB M hM y' y (fun p => f p.1) (fun p => g p.1)
    refine hb.trans ?_
    have h1 := finL2_restrict_le (fun v => c v = y) f
    have h2 := finL2_restrict_le (fun u => c' u = y') g
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hX0) h2 (finL2_nonneg _)
      (mul_nonneg hX0 (finL2_nonneg _))
  refine hnorm.trans ?_
  have hsq : 0 ≤ C * Real.sqrt (w / w') * Real.exp (-((υ / 8) * cellDist y' y)) := by positivity
  have : (K₀ + 1) * C * Real.sqrt (w / w') * Real.exp (-((υ / 8) * cellDist y' y)) * 1 =
      X + C * Real.sqrt (w / w') * Real.exp (-((υ / 8) * cellDist y' y)) := by
    rw [hX]
    ring
  rw [this]
  linarith
end YangMills.Construction.RunningCouplingSlope.BoundedSymbolLocalMatrixProof
end
