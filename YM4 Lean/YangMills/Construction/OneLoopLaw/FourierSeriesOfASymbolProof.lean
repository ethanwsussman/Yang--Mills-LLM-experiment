import YangMills.Construction.Dirichlet.CrossingChainSumEstimate
import YangMills.Construction.OneLoopLaw.DecayOfTheKernelsOfASymbol
import YangMills.Construction.OneLoopLaw.FourierSeriesOfASymbol
import YangMills.Construction.PeriodicOperators.RiemannSumsAndShiftsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.OneLoopLaw.SymbolFourierSeries
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.RiemannSums YangMills.Construction.OneLoopLaw.TemperedStiffness
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (l1NormVec)
def torusProj : AmbientSpace → UnitAddTorus (Fin 4) := fun x μ => (x μ : UnitAddCircle)
theorem isOpenQuotientMap_torusProj : IsOpenQuotientMap torusProj := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.isOpenQuotientMap_toUnitTorus <;> assumption
theorem continuous_toComplexVec : Continuous toComplexVec := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
theorem toComplexVec_add (x y : AmbientSpace) :
    toComplexVec (x + y) = toComplexVec x + toComplexVec y := by apply _root_.YangMills.Construction.PeriodicOperators.CovariantFiniteRangeProof.toComplexVec_add <;> assumption
theorem toComplexVec_mem_imStrip {δ : ℝ} (hδ : 0 ≤ δ) (x : AmbientSpace) :
    toComplexVec x ∈ imStrip δ := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.toComplexVec_mem_imStrip <;> assumption
theorem mFourier_torusProj (n : Fin 4 → ℤ) (x : AmbientSpace) :
    UnitAddTorus.mFourier n (torusProj x) =
      Complex.exp (Complex.I * bilinDot (toComplexVec ((2 * Real.pi) • x))
        (toComplexVec (castVec n))) := by
  rw [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  simp only [torusProj, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [bilinDot, toComplexVec, castVec, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [div_one]
  ring
theorem exists_torus_descent {g : (Fin 4 → ℂ) → ℂ}
    (hc : Continuous fun x : AmbientSpace => g (toComplexVec x))
    (hper : ∀ x p : AmbientSpace, p ∈ periodLattice →
      g (toComplexVec x + toComplexVec p) = g (toComplexVec x)) :
    ∃ F : C(UnitAddTorus (Fin 4), ℂ), ∀ x : AmbientSpace,
      F (torusProj x) = g (toComplexVec ((2 * Real.pi) • x)) := by
  have hc' : Continuous fun x : AmbientSpace => g (toComplexVec ((2 * Real.pi) • x)) :=
    hc.comp (continuous_const_smul _)
  have hf : Function.FactorsThrough (fun x : AmbientSpace => g (toComplexVec ((2 * Real.pi) • x)))
      torusProj := by
    intro x y hxy
    have hm : ∀ μ, ∃ m : ℤ, y μ = x μ + m := by
      intro μ
      have h1 : (x μ : UnitAddCircle) = y μ := congrFun hxy μ
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h1)
      refine ⟨m, ?_⟩
      simp only [zsmul_eq_mul, mul_one] at hm
      linarith
    choose m hm using hm
    have hp : (fun μ => (m μ : ℝ) * (2 * Real.pi) : AmbientSpace) ∈ periodLattice := ⟨m, fun μ => rfl⟩
    have h := hper ((2 * Real.pi) • x) _ hp
    show g _ = g _
    rw [← h, ← toComplexVec_add]
    congr 2
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, hm μ]
    ring
  let q : C(AmbientSpace, UnitAddTorus (Fin 4)) := ⟨torusProj, isOpenQuotientMap_torusProj.continuous⟩
  have hq : Topology.IsQuotientMap q := isOpenQuotientMap_torusProj.isQuotientMap
  exact ⟨hq.lift ⟨_, hc'⟩ hf, fun x => DFunLike.congr_fun (hq.lift_comp ⟨_, hc'⟩ hf) x⟩
theorem mFourierCoeff_neg_eq_symbolKernel {g : (Fin 4 → ℂ) → ℂ} {F : C(UnitAddTorus (Fin 4), ℂ)}
    (hF : ∀ x : AmbientSpace, F (torusProj x) = g (toComplexVec ((2 * Real.pi) • x)))
    (u : Fin 4 → ℤ) :
    UnitAddTorus.mFourierCoeff F (-u) = symbolKernel g u := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral F (-u) (fun _ => -(1 / 2))]
  let Ψ : AmbientSpace → ℂ := fun κ => g (toComplexVec κ) *
    Complex.exp (Complex.I * bilinDot (toComplexVec κ) (toComplexVec (castVec u)))
  have e1 : ∀ x : AmbientSpace, UnitAddTorus.mFourier (-(-u)) (fun i => (x i : UnitAddCircle)) •
      F (fun i => (x i : UnitAddCircle)) = Ψ ((2 * Real.pi) • x) := by
    intro x
    rw [neg_neg]
    show UnitAddTorus.mFourier u (torusProj x) • F (torusProj x) = _
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
  unfold symbolKernel torusAverage
  rw [Complex.real_smul]
theorem summable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℤ => Real.exp (-c * |(m : ℝ)|) := by apply _root_.YangMills.Construction.Dirichlet.ChainSumEstimate.summable_exp_neg_mul_abs <;> assumption
theorem summable_prod_mul_of_nonneg {α β : Type} {f : α → ℝ} {g : β → ℝ} (hf : ∀ m, 0 ≤ f m)
    (hg : ∀ m, 0 ≤ g m) (h1 : Summable f) (h2 : Summable g) :
    Summable fun x : α × β => f x.1 * g x.2 :=
  summable_mul_of_summable_norm
    (h1.congr fun m => by rw [Real.norm_of_nonneg (hf m)])
    (h2.congr fun m => by rw [Real.norm_of_nonneg (hg m)])
theorem summable_pi_prod_of_nonneg (a : ℤ → ℝ) (ha : ∀ m, 0 ≤ a m) (hs : Summable a) (d : ℕ) :
    Summable fun n : Fin d → ℤ => ∏ i, a (n i) := by
  induction d with
  | zero => exact (hasSum_unique _).summable
  | succ d ih =>
    have hprod : Summable fun x : ℤ × (Fin d → ℤ) => a x.1 * ∏ i, a (x.2 i) :=
      summable_prod_mul_of_nonneg (f := a) (g := fun n : Fin d → ℤ => ∏ i, a (n i)) ha
        (fun n => Finset.prod_nonneg fun i _ => ha _) hs ih
    refine ((Fin.consEquiv fun _ => ℤ).symm.summable_iff.2 hprod).congr fun n => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]
theorem summable_symbolKernel
    (hdecay : YangMills.Construction.OneLoopLaw.SymbolKernelDecay.SymbolKernelDecayClaim) {δ : ℝ}
    {g : (Fin 4 → ℂ) → ℂ} (hδ : 0 < δ) (hh : HolomorphicNearStrip δ g)
    (hp : PeriodicOnStrip δ g) (hb : BoundedOnStrip δ g) : Summable (symbolKernel g) := by
  have hA := summable_pi_prod_of_nonneg (fun m : ℤ => Real.exp (-δ * |(m : ℝ)|))
    (fun _ => (Real.exp_pos _).le) (summable_exp_neg_mul_abs hδ) 4
  refine Summable.of_norm_bounded (hA.mul_left (stripSup δ g)) fun u => ?_
  refine (hdecay δ g hδ hh hp hb u).trans (le_of_eq ?_)
  rw [← Real.exp_sum]
  congr 2
  simp only [l1NormVec, castVec, Finset.mul_sum]
theorem fourierExpansionOfSymbol_holds
    (hdecay : YangMills.Construction.OneLoopLaw.SymbolKernelDecay.SymbolKernelDecayClaim) :
    FourierExpansionOfSymbol := by
  intro δ g hδ hh hp hb p
  have hc : Continuous fun x : AmbientSpace => g (toComplexVec x) := by
    obtain ⟨O, hO, -, hcO, -⟩ := hh
    exact ((continuousOn_pi.1 hcO 0).mono hO).comp_continuous continuous_toComplexVec
      fun x => toComplexVec_mem_imStrip hδ.le x
  obtain ⟨F, hF⟩ := exists_torus_descent hc fun x q hq =>
    hp _ (toComplexVec_mem_imStrip hδ.le x) q hq
  have hco : ∀ u, UnitAddTorus.mFourierCoeff F (-u) = symbolKernel g u :=
    mFourierCoeff_neg_eq_symbolKernel hF
  have hsum : Summable (UnitAddTorus.mFourierCoeff F) := by
    have h := summable_symbolKernel hdecay hδ hh hp hb
    refine ((Equiv.neg (Fin 4 → ℤ)).summable_iff.1 ?_)
    exact h.congr fun u => by simp [hco]
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum
    (torusProj ((2 * Real.pi)⁻¹ • p))
  have hne : 2 * Real.pi ≠ 0 := by positivity
  have hy : (2 * Real.pi) • ((2 * Real.pi)⁻¹ • p) = p := smul_inv_smul₀ hne p
  rw [hF, hy] at h
  have e : ∀ u : Fin 4 → ℤ, UnitAddTorus.mFourier (-u) (torusProj ((2 * Real.pi)⁻¹ • p)) =
      Complex.exp (-(Complex.I * bilinDot (toComplexVec p) (toComplexVec (castVec u)))) := by
    intro u
    rw [mFourier_torusProj, hy]
    congr 1
    simp only [bilinDot, toComplexVec, castVec, Pi.neg_apply]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring
  have h' := (Equiv.neg (Fin 4 → ℤ)).hasSum_iff.2 h
  convert h' using 1
  funext u
  simp only [Function.comp, Equiv.neg_apply, hco, e, smul_eq_mul]
end YangMills.Construction.OneLoopLaw.SymbolFourierSeries
end
