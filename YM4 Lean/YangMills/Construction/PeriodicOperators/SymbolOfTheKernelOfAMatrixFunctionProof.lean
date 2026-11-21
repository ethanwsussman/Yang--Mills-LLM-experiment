import YangMills.Construction.PeriodicOperators.RiemannSumsAndShiftsProof
import YangMills.Construction.PeriodicOperators.BoundOfTheKernelOfAMatrixFunctionProof
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.SymbolOfAnOperatorWithDecayProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.PeriodicOperators.KernelSymbol
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec l1NormVec)
open YangMills.Construction.PeriodicOperators.RiemannSums
  (periodLattice HolomorphicNearStrip PeriodicOnStrip BoundedOnStrip)
variable {P Q : PeriodicData}
theorem bilinDot_add_left (a b w : Fin 4 → ℂ) : bilinDot (a + b) w = bilinDot a w + bilinDot b w := by
  simp [bilinDot, add_mul, Finset.sum_add_distrib]
theorem bilinDot_add_right (z a b : Fin 4 → ℂ) : bilinDot z (a + b) = bilinDot z a + bilinDot z b := by
  simp [bilinDot, mul_add, Finset.sum_add_distrib]
theorem bilinDot_comm (a b : Fin 4 → ℂ) : bilinDot a b = bilinDot b a := by
  simp [bilinDot, mul_comm]
theorem toComplexVec_add (u v : AmbientSpace) :
    toComplexVec (u + v) = toComplexVec u + toComplexVec v := by apply _root_.YangMills.Construction.PeriodicOperators.CovariantFiniteRangeProof.toComplexVec_add <;> assumption
theorem continuous_toComplexVec : Continuous toComplexVec := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
theorem re_I_mul_bilinDot (z : Fin 4 → ℂ) (v : AmbientSpace) :
    (Complex.I * bilinDot z (toComplexVec v)).re = -∑ μ, (z μ).im * v μ := by
  simp [bilinDot, toComplexVec, Complex.im_sum]
theorem abs_sum_im_mul_le {z : Fin 4 → ℂ} {s : ℝ} (hs : ∀ μ, |(z μ).im| ≤ s) (v : AmbientSpace) :
    |∑ μ, (z μ).im * v μ| ≤ s * l1NormVec v := by
  calc |∑ μ, (z μ).im * v μ| ≤ ∑ μ, |(z μ).im * v μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ μ, s * |v μ| := Finset.sum_le_sum fun μ _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hs μ) (abs_nonneg _)
    _ = s * l1NormVec v := by rw [l1NormVec, Finset.mul_sum]
theorem euclidNormVec_le_l1NormVec (v : AmbientSpace) : euclidNormVec v ≤ l1NormVec v := by apply _root_.YangMills.Construction.PeriodicOperators.ExpDecaySymbol.euclidNormVec_le_l1NormVec <;> assumption
theorem mkQuot_translate (n : Fin 4 → ℤ) (i : P.Carrier) :
    P.mkQuot 1 (P.translate n i) = P.mkQuot 1 i :=
  (Quot.sound ⟨n, by simp⟩).symm
theorem carrierEntry_translate (A : QuotHom P Q) (j : Q.Carrier) (n : Fin 4 → ℤ) (i : P.Carrier) :
    carrierEntry A j (P.translate n i) = carrierEntry A j i := by
  unfold carrierEntry
  rw [mkQuot_translate]
def pointPhase (P : PeriodicData) (e : Fin 4 → ℤ) (i : P.Carrier) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    bilinDot (toComplexVec (castVec e)) (toComplexVec (P.pos i)))
theorem pointPhase_translate (hP : IsPeriodic P) (e n : Fin 4 → ℤ) (i : P.Carrier) :
    pointPhase P e (P.translate n i) = pointPhase P e i := by
  have h : bilinDot (toComplexVec (castVec e)) (toComplexVec (castVec n)) =
      ((∑ μ, e μ * n μ : ℤ) : ℂ) := by
    simp [bilinDot, toComplexVec, castVec]
  have h1 : Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec (castVec n))) = 1 := by
    rw [h, Complex.exp_eq_one_iff]
    exact ⟨∑ μ, e μ * n μ, by ring⟩
  unfold pointPhase
  rw [hP.pos_translate, toComplexVec_add, bilinDot_add_right, mul_add, Complex.exp_add, h1, mul_one]
theorem phaseOn_mkQuot (hP : IsPeriodic P) (e : Fin 4 → ℤ) (i : P.Carrier) :
    phaseOn P e (P.mkQuot 1 i) = pointPhase P e i := by
  have hL : ∀ i₁ i₂ : P.Carrier, P.mkQuot 1 i₁ = P.mkQuot 1 i₂ →
      pointPhase P e i₁ = pointPhase P e i₂ := by
    intro i₁ i₂ hc
    let L : P.QuotMod 1 → ℂ := Quot.lift (pointPhase P e) (by
      rintro a _ ⟨n, rfl⟩
      exact (pointPhase_translate hP e _ a).symm)
    exact congrArg L hc
  have hex : ∃ w, ∀ j, P.mkQuot 1 j = P.mkQuot 1 i →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (P.pos j))) = w :=
    ⟨pointPhase P e i, fun j h => hL j i h⟩
  exact ((Classical.epsilon_spec hex) i rfl).symm
theorem quotHomInverse_phaseMul_apply (hP : IsPeriodic P) (e : Fin 4 → ℤ)
    (g : P.UnitQuot → ℂ) (c : P.UnitQuot) :
    quotHomInverse (phaseMul P e) g c = (phaseOn P e c)⁻¹ * g c := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.quotHomInverse_phaseMul_apply <;> assumption
open Classical in
theorem carrierEntry_conj (hP : IsPeriodic P) (hQ : IsPeriodic Q)
    (A : QuotHom P Q) (e : Fin 4 → ℤ) (j : Q.Carrier) (i : P.Carrier) :
    carrierEntry ((quotHomInverse (phaseMul Q e)).comp
        (A.comp (phaseMul P e))) j i =
      (pointPhase Q e j)⁻¹ * carrierEntry A j i * pointPhase P e i := by
  have hs : phaseMul P e (Pi.single (P.mkQuot 1 i) 1) =
      phaseOn P e (P.mkQuot 1 i) • (Pi.single (P.mkQuot 1 i) 1 : P.UnitQuot → ℂ) := by
    funext c
    show phaseOn P e c * (Pi.single (P.mkQuot 1 i) 1 : P.UnitQuot → ℂ) c = _
    by_cases hc : c = P.mkQuot 1 i
    · subst hc
      simp
    · simp [hc]
  unfold carrierEntry linearMapEntry
  simp only [LinearMap.comp_apply]
  rw [quotHomInverse_phaseMul_apply hQ, hs, map_smul, Pi.smul_apply, smul_eq_mul,
    phaseOn_mkQuot hP, phaseOn_mkQuot hQ]
  ring
def kernelIntegrand (M : (Fin 4 → ℂ) → QuotHom P Q) (j : Q.Carrier) (k : P.Carrier)
    (z : Fin 4 → ℂ) : ℂ :=
  carrierEntry (M z) j k *
    Complex.exp (-Complex.I * bilinDot z (toComplexVec (P.pos k - Q.pos j)))
theorem kernelIntegrand_holomorphic {r : ℝ} {M : (Fin 4 → ℂ) → QuotHom P Q}
    (hHol : IsHolomorphicNbhd (imStrip r) M) (j : Q.Carrier) (k : P.Carrier) :
    HolomorphicNearStrip r (kernelIntegrand M j k) := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.shiftedIntegrand_holomorphic <;> assumption
theorem kernelIntegrand_periodic (hP : IsPeriodic P) (hQ : IsPeriodic Q) {r : ℝ}
    {M : (Fin 4 → ℂ) → QuotHom P Q} (hM : IsQuasiPeriodic (imStrip r) M) (j : Q.Carrier)
    (k : P.Carrier) : PeriodicOnStrip r (kernelIntegrand M j k) := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.shiftedIntegrand_periodic <;> assumption
theorem kernelIntegrand_bounded {r : ℝ} {M : (Fin 4 → ℂ) → QuotHom P Q}
    (hB : QuotHomFamilyBoundedOn (imStrip r) M) (j : Q.Carrier) (k : P.Carrier) :
    BoundedOnStrip r (kernelIntegrand M j k) := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.shiftedIntegrand_bounded <;> assumption
def charWave (n : Fin 4 → ℤ) (z : Fin 4 → ℂ) : ℂ :=
  Complex.exp (-(Complex.I * bilinDot (toComplexVec (castVec n)) z))
theorem charWave_add (n : Fin 4 → ℤ) (z z' : Fin 4 → ℂ) :
    charWave n (z + z') = charWave n z * charWave n z' := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.expChar_add <;> assumption
def periodicCoeff (W : AmbientSpace → ℂ) (n : Fin 4 → ℤ) : ℂ :=
  torusAverage fun x => W x * charWave n (toComplexVec x)
theorem torusAverage_const_mul (c : ℂ) (f : AmbientSpace → ℂ) :
    torusAverage (fun x => c * f x) = c * torusAverage f := by
  unfold torusAverage
  rw [integral_const_mul]
  ring
def torusProj : AmbientSpace → UnitAddTorus (Fin 4) := fun x μ => (x μ : UnitAddCircle)
theorem isOpenQuotientMap_torusProj : IsOpenQuotientMap torusProj := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.isOpenQuotientMap_toUnitTorus <;> assumption
theorem mFourier_torusProj (n : Fin 4 → ℤ) (x : AmbientSpace) :
    UnitAddTorus.mFourier (-n) (torusProj x) = charWave n (toComplexVec ((2 * Real.pi) • x)) := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.mFourier_toUnitTorus <;> assumption
theorem exists_torus_lift {W : AmbientSpace → ℂ} (hc : Continuous W)
    (hp : ∀ (m : Fin 4 → ℤ) (x : AmbientSpace), W (x + (2 * Real.pi) • castVec m) = W x) :
    ∃ F : C(UnitAddTorus (Fin 4), ℂ), ∀ x : AmbientSpace, F (torusProj x) = W ((2 * Real.pi) • x) := by
  have hc' : Continuous fun x : AmbientSpace => W ((2 * Real.pi) • x) :=
    hc.comp (continuous_const_smul _)
  have hf : Function.FactorsThrough (fun x : AmbientSpace => W ((2 * Real.pi) • x)) torusProj := by
    intro x y hxy
    have hm : ∀ μ, ∃ m : ℤ, y μ = x μ + m := by
      intro μ
      have h1 : (x μ : UnitAddCircle) = y μ := congrFun hxy μ
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h1)
      refine ⟨m, ?_⟩
      simp only [zsmul_eq_mul, mul_one] at hm
      linarith
    choose m hm using hm
    show W _ = W _
    rw [← hp m ((2 * Real.pi) • x)]
    congr 1
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, hm μ, castVec]
    ring
  let q : C(AmbientSpace, UnitAddTorus (Fin 4)) := ⟨torusProj, isOpenQuotientMap_torusProj.continuous⟩
  have hq : Topology.IsQuotientMap q := isOpenQuotientMap_torusProj.isQuotientMap
  exact ⟨hq.lift ⟨_, hc'⟩ hf, fun x => DFunLike.congr_fun (hq.lift_comp ⟨_, hc'⟩ hf) x⟩
theorem mFourierCoeff_eq_periodicCoeff {W : AmbientSpace → ℂ} {F : C(UnitAddTorus (Fin 4), ℂ)}
    (hF : ∀ x : AmbientSpace, F (torusProj x) = W ((2 * Real.pi) • x)) (n : Fin 4 → ℤ) :
    UnitAddTorus.mFourierCoeff F n = periodicCoeff W n := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral F n (fun _ => -(1 / 2))]
  let Ψ : AmbientSpace → ℂ := fun z => W z * charWave n (toComplexVec z)
  have e1 : ∀ x : AmbientSpace, UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle)) •
      F (fun i => (x i : UnitAddCircle)) = Ψ ((2 * Real.pi) • x) := by
    intro x
    show UnitAddTorus.mFourier (-n) (torusProj x) • F (torusProj x) = _
    rw [hF x, mFourier_torusProj, smul_eq_mul, mul_comm]
  simp only [e1]
  have hpos : 0 < 2 * Real.pi := by positivity
  rw [Measure.setIntegral_comp_smul_of_pos volume Ψ _ hpos]
  have hset : (2 * Real.pi) • {x : Fin 4 → ℝ | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + 1)} =
      Set.pi univ fun i : Fin 4 => Ioc ((fun _ : Fin 4 => -Real.pi) i) ((fun _ => Real.pi) i) := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hpos.ne']
    simp only [Set.mem_ofPred_eq, Set.mem_pi, mem_univ, true_imp_iff, Pi.smul_apply, smul_eq_mul,
      mem_Ioc]
    refine forall_congr' fun i => ?_
    have e : x i = (2 * Real.pi) * ((2 * Real.pi)⁻¹ * x i) := by field_simp
    generalize (2 * Real.pi)⁻¹ * x i = t at e ⊢
    rw [e]
    have hπ := Real.pi_pos
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  rw [hset, Module.finrank_fin_fun, volume_pi, setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc,
    ← volume_pi]
  unfold periodicCoeff torusAverage
  rw [Complex.real_smul]
theorem hasSum_periodicCoeff {W : AmbientSpace → ℂ} (hc : Continuous W)
    (hp : ∀ (m : Fin 4 → ℤ) (x : AmbientSpace), W (x + (2 * Real.pi) • castVec m) = W x)
    (hs : Summable (periodicCoeff W)) : HasSum (periodicCoeff W) (W 0) := by
  obtain ⟨F, hF⟩ := exists_torus_lift hc hp
  have hco : UnitAddTorus.mFourierCoeff F = periodicCoeff W := funext (mFourierCoeff_eq_periodicCoeff hF)
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := F)
    (by rw [hco]; exact hs) (torusProj 0)
  have e : ∀ i : Fin 4 → ℤ, UnitAddTorus.mFourier i (torusProj 0) = 1 := by
    intro i
    have := mFourier_torusProj (-i) 0
    rw [neg_neg] at this
    rw [this]
    simp [charWave, bilinDot, toComplexVec]
  rw [hF, smul_zero, hco] at h
  simpa only [e, smul_eq_mul, mul_one] using h
theorem claim_of_bounds (hBound : MatrixFunctionKernel.DecayBound)
    (hRiemann : RiemannSums.Claim) (hSums : ExponentialSums.Bounds) :
    MatFunKernelSymbol.Claim := by
  intro P Q hP hQ r hr M hHol hBdd hM z hz
  have hzs : z ∈ imStrip r := fun μ => (hz μ).le
  have hnear : ∀ x : AmbientSpace, toComplexVec x + z ∈ imStrip r := fun x μ => by
    simpa [toComplexVec] using hzs μ
  have hT : ∀ j k, matFunKernel P Q M j k =
      torusAverage fun x => kernelIntegrand M j k (toComplexVec x + z) := fun j k =>
    ((hRiemann 1 r _ one_pos hr (kernelIntegrand_holomorphic hHol j k)
      (kernelIntegrand_periodic hP hQ hM j k) (kernelIntegrand_bounded hBdd j k)).2 z hzs).symm
  obtain ⟨μ₀, hμ₀⟩ := Finite.exists_max fun μ => |(z μ).im|
  have hlt : |(z μ₀).im| < r := hz μ₀
  have hc : 0 < r - |(z μ₀).im| := sub_pos.2 hlt
  have key : ∀ j i, Summable (fun n => ‖symbolSummand P Q (matFunKernel P Q M) z j i n‖) ∧
      fourierSymbol P Q (matFunKernel P Q M) z j i = carrierEntry (M z) j i := by
    intro j i
    set y : AmbientSpace := P.pos i - Q.pos j with hy
    have hpos : ∀ n : Fin 4 → ℤ, P.pos (P.translate n i) - Q.pos j = y + castVec n := by
      intro n
      rw [hP.pos_translate, hy]
      abel
    let W : AmbientSpace → ℂ := fun x => kernelIntegrand M j i (toComplexVec x + z)
    have hsplit : ∀ (n : Fin 4 → ℤ) (w : Fin 4 → ℂ),
        kernelIntegrand M j (P.translate n i) w = kernelIntegrand M j i w * charWave n w := by
      intro n w
      unfold kernelIntegrand charWave
      rw [carrierEntry_translate, hpos, toComplexVec_add, bilinDot_add_right, mul_assoc,
        ← Complex.exp_add, bilinDot_comm (toComplexVec (castVec n)) w]
      congr 2
      ring
    have hcoef : ∀ n, matFunKernel P Q M j (P.translate n i) =
        charWave n z * periodicCoeff W n := by
      intro n
      rw [hT, periodicCoeff, ← torusAverage_const_mul]
      congr 1
      funext x
      rw [hsplit, charWave_add]
      ring
    have hwave : ∀ n, charWave n z *
        Complex.exp (Complex.I * bilinDot z (toComplexVec (castVec n))) = 1 := by
      intro n
      rw [charWave, ← Complex.exp_add, bilinDot_comm, neg_add_cancel, Complex.exp_zero]
    have hterm : ∀ n, symbolSummand P Q (matFunKernel P Q M) z j i n =
        periodicCoeff W n * Complex.exp (Complex.I * bilinDot z (toComplexVec y)) := by
      intro n
      unfold symbolSummand
      rw [hcoef, hpos, toComplexVec_add, bilinDot_add_right, mul_add, Complex.exp_add]
      calc _ = (charWave n z * Complex.exp (Complex.I * bilinDot z (toComplexVec (castVec n)))) *
            (periodicCoeff W n * Complex.exp (Complex.I * bilinDot z (toComplexVec y))) := by ring
        _ = _ := by rw [hwave, one_mul]
    set B : ℝ := sSup ((fun w => ‖carrierEntry (M w) j i‖) '' imStrip r) with hBdef
    have hB0 : 0 ≤ B := Real.sSup_nonneg (by
      rintro _ ⟨w, -, rfl⟩
      exact norm_nonneg _)
    have hle : ∀ n, ‖symbolSummand P Q (matFunKernel P Q M) z j i n‖ ≤
        B * Real.exp (-(r - |(z μ₀).im|) * euclidNormVec (y + castVec n)) := by
      intro n
      have h1 := (hBound P Q hP hQ r hr M hHol hBdd hM).2 j (P.translate n i)
      simp only [carrierEntry_translate] at h1
      rw [hpos] at h1
      have h2 : ‖Complex.exp (Complex.I * bilinDot z (toComplexVec (y + castVec n)))‖ ≤
          Real.exp (|(z μ₀).im| * l1NormVec (y + castVec n)) := by
        rw [Complex.norm_exp, re_I_mul_bilinDot]
        exact Real.exp_le_exp.2 ((neg_le_abs _).trans (abs_sum_im_mul_le (fun μ => hμ₀ μ) _))
      have hL := euclidNormVec_le_l1NormVec (y + castVec n)
      unfold symbolSummand
      rw [norm_mul, hpos]
      calc _ ≤ (B * Real.exp (-r * l1NormVec (y + castVec n))) *
            Real.exp (|(z μ₀).im| * l1NormVec (y + castVec n)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hB0 (Real.exp_pos _).le)
        _ = B * Real.exp (-(r - |(z μ₀).im|) * l1NormVec (y + castVec n)) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB0
            nlinarith
    have hsum : Summable fun n =>
        ‖symbolSummand P Q (matFunKernel P Q M) z j i n‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle
        ((((hSums _ hc).2.1 y).1).mul_left B)
    refine ⟨hsum, ?_⟩
    have hE : Complex.exp (Complex.I * bilinDot z (toComplexVec y)) ≠ 0 := Complex.exp_ne_zero _
    have hWc : Continuous W := by
      have hcont : ContinuousOn (kernelIntegrand M j i) (imStrip r) := by
        obtain ⟨O, hS, -, hcO, -⟩ := kernelIntegrand_holomorphic hHol (r := r) j i
        exact (continuousOn_pi.1 hcO 0).mono hS
      exact hcont.comp_continuous (continuous_toComplexVec.add continuous_const) hnear
    have hWp : ∀ (m : Fin 4 → ℤ) (x : AmbientSpace), W (x + (2 * Real.pi) • castVec m) = W x := by
      intro m x
      have hp : (2 * Real.pi) • castVec m ∈ periodLattice :=
        ⟨m, fun μ => by simp [castVec, mul_comm]⟩
      have h := kernelIntegrand_periodic hP hQ hM j i (toComplexVec x + z) (hnear x) _ hp
      have e : toComplexVec (x + (2 * Real.pi) • castVec m) + z =
          toComplexVec x + z + toComplexVec ((2 * Real.pi) • castVec m) := by
        rw [toComplexVec_add]
        abel
      exact (congrArg (kernelIntegrand M j i) e).trans h
    have hcs : Summable (periodicCoeff W) := by
      have h := (hsum.of_norm).mul_right (Complex.exp (Complex.I * bilinDot z (toComplexVec y)))⁻¹
      refine h.congr fun n => ?_
      rw [hterm, mul_inv_cancel_right₀ hE]
    have hs := (hasSum_periodicCoeff hWc hWp hcs).mul_right
      (Complex.exp (Complex.I * bilinDot z (toComplexVec y)))
    have hW0 : W 0 * Complex.exp (Complex.I * bilinDot z (toComplexVec y)) =
        carrierEntry (M z) j i := by
      have h0 : toComplexVec (0 : AmbientSpace) + z = z := by
        funext μ
        simp [toComplexVec]
      show kernelIntegrand M j i _ * _ = _
      rw [h0]
      unfold kernelIntegrand
      rw [mul_assoc, ← Complex.exp_add, ← hy, neg_mul, neg_add_cancel, Complex.exp_zero, mul_one]
    rw [hW0] at hs
    unfold fourierSymbol
    simp only [hterm]
    exact hs.tsum_eq
  exact ⟨fun j i => (key j i).1, fun j i => (key j i).2⟩
end YangMills.Construction.PeriodicOperators.KernelSymbol
end
