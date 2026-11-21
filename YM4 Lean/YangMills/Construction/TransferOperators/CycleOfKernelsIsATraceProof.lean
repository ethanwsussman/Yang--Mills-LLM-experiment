import YangMills.Construction.Matrices.PartialCoefficientsOfASquareIntegrableFunctionProof
import YangMills.Construction.TransferOperators.ConfigurationsOfACubicTorusByLayers
import YangMills.Construction.TransferOperators.CycleOfKernelsIsATrace
import YangMills.Construction.TransferOperators.EnergyOfTheOrbitsOfACubicTorus
import YangMills.Construction.TransferOperators.FactsOfTheOperatorsOfACubicTorus
import YangMills.Construction.TransferOperators.IntegralOverAPairOfVariablesIsAMatrixElement
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsBoundedContinuousAndASeries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory SpinHarmonics InfiniteLattice
open TransferOperators.SandwichConditions
namespace TransferOperators
namespace KernelCycleTrace
theorem hasSum_fin_prod_of_summable_norm {R K : Type*} [NormedCommRing R] [CompleteSpace R]
    (n : ℕ) (f : Fin n → K → R) (F : Fin n → R) (hs : ∀ j, Summable fun p => ‖f j p‖)
    (hf : ∀ j, HasSum (f j) (F j)) :
    (Summable fun a : Fin n → K => ‖∏ j, f j (a j)‖) ∧
      HasSum (fun a : Fin n → K => ∏ j, f j (a j)) (∏ j, F j) := by
  induction n with
  | zero => exact ⟨(hasSum_unique _).summable, by simp [hasSum_unique]⟩
  | succ n ih =>
    obtain ⟨h₁, h₂⟩ := ih (fun j => f j.succ) (fun j => F j.succ) (fun j => hs j.succ)
      fun j => hf j.succ
    constructor
    · refine ((Fin.consEquiv fun _ => K).summable_iff).1 ?_
      refine (Summable.mul_norm (hs 0) h₁).congr fun x => ?_
      simp [Function.comp, Fin.consEquiv, Fin.prod_univ_succ]
    · rw [Fin.prod_univ_succ]
      refine ((Fin.consEquiv fun _ => K).hasSum_iff).1 ?_
      have hEq : ((fun a : Fin (n + 1) → K => ∏ j, f j (a j)) ∘ (Fin.consEquiv fun _ => K)) =
          fun x : K × (Fin n → K) => f 0 x.1 * ∏ j : Fin n, f j.succ (x.2 j) := by
        funext x
        simp [Function.comp, Fin.consEquiv, Fin.prod_univ_succ]
      rw [hEq]
      exact HasSum.mul (f := f 0) (g := fun b : Fin n → K => ∏ j : Fin n, f j.succ (b j))
        (s := F 0) (t := ∏ j : Fin n, F j.succ) (hf 0) h₂
        (summable_mul_of_summable_norm (f := f 0)
          (g := fun b : Fin n → K => ∏ j : Fin n, f j.succ (b j)) (hs 0) h₁)
theorem countable_peterWeylLabel : Countable PeterWeylLabel := by apply _root_.YangMills.Construction.SpinHarmonics.PartialCoeffL2.countable_peterWeylLabel <;> assumption
theorem natCast_finRotate {s : ℕ} (k : Fin s) :
    (((finRotate s k : Fin s) : ℕ) : ZMod s) = (k : ℕ) + 1 := by
  cases s with
  | zero => exact k.elim0
  | succ n =>
    rw [finRotate_apply, Fin.val_add, ZMod.natCast_mod, Nat.cast_add]
    congr 1
    rw [Fin.val_one', ZMod.natCast_mod]
    simp
end KernelCycleTrace
namespace CubicPeriodSublattice
variable (Γ : CubicPeriodSublattice) (μ : Fin 4)
def indexLevel (k : Fin Γ.side) : ZMod Γ.side := Γ.levelClass ((k : ℕ) + 1)
theorem indexLevel_finRotate (k : Fin Γ.side) :
    Γ.indexLevel (finRotate Γ.side k) = Γ.indexLevel k + 1 := by
  simp only [indexLevel, levelClass]
  push_cast
  rw [KernelCycleTrace.natCast_finRotate]
theorem indexLevel_bijective : Function.Bijective Γ.indexLevel := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun k k' h => ?_, by simp [ZMod.card]⟩
  have h' : ((k : ℕ) : ZMod Γ.side) = ((k' : ℕ) : ZMod Γ.side) := by
    simpa [indexLevel, levelClass] using h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  rw [Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2] at h'
  exact Fin.ext h'
variable {μ}
theorem continuous_sliceField (c : ZMod Γ.side) :
    Continuous fun U : Γ.lattice.QuotientField => Γ.sliceField (μ := μ) U c :=
  continuous_pi fun _ => continuous_apply _
theorem continuous_orbitGaugeAct_pair :
    Continuous fun p : (Γ.VertexOrbits μ → Matrices.ComplexMatrix2.specialUnitary) ×
        (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) =>
      Γ.orbitGaugeAct p.1 p.2 :=
  continuous_pi fun e => by
    unfold orbitGaugeAct
    fun_prop
def kernelLeftArg (U : Γ.lattice.QuotientField) (k : Fin Γ.side) :
    Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary :=
  Γ.sliceField (μ := μ) U (Γ.indexLevel k)
def kernelRightArg (U : Γ.lattice.QuotientField) (k : Fin Γ.side) :
    Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary :=
  Γ.orbitGaugeAct (Γ.temporalSliceField (μ := μ) U (Γ.indexLevel k))
    (Γ.sliceField (μ := μ) U (Γ.indexLevel k + 1))
theorem continuous_kernelLeftArg (k : Fin Γ.side) :
    Continuous fun U : Γ.lattice.QuotientField => Γ.kernelLeftArg (μ := μ) U k :=
  Γ.continuous_sliceField _
theorem continuous_kernelRightArg (k : Fin Γ.side) :
    Continuous fun U : Γ.lattice.QuotientField => Γ.kernelRightArg (μ := μ) U k := by
  refine continuous_pi fun e => ?_
  simp only [kernelRightArg, orbitGaugeAct, temporalSliceField, sliceField]
  fun_prop
def cycleTerm (β : ℝ) (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ)
    (k : Fin Γ.side) (p : PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ))
    (U : Γ.lattice.QuotientField) : ℂ :=
  Complex.exp (-Γ.sliceEnergy (μ := μ) β (Γ.kernelLeftArg U k)) *
    ((sqrtPeterWeylCoeff β p.1 : ℂ) * (sqrtPeterWeylCoeff β p.2 : ℂ) *
      peterWeylEntry (X k) p.1 p.2 * peterWeylFn p.1 (Γ.kernelLeftArg (μ := μ) U k) *
      star (peterWeylFn p.2 (Γ.kernelRightArg (μ := μ) U k)))
def cycleTermBound (β : ℝ) (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ)
    (k : Fin Γ.side) (p : PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ)) :
    ℝ :=
  sqrtPeterWeylCoeff β p.1 * sqrtPeterWeylCoeff β p.2 *
    ‖peterWeylEntry (X k) p.1 p.2‖ * ‖peterWeylFn p.1‖ * ‖peterWeylFn p.2‖
theorem cycleTermBound_nonneg (β : ℝ)
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ) (k : Fin Γ.side)
    (p : PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ)) :
    0 ≤ Γ.cycleTermBound β X k p := by
  have h₁ : 0 ≤ sqrtPeterWeylCoeff β p.1 := Real.sqrt_nonneg _
  have h₂ : 0 ≤ sqrtPeterWeylCoeff β p.2 := Real.sqrt_nonneg _
  unfold cycleTermBound
  positivity
theorem norm_exp_neg_sliceEnergy_le {β : ℝ}
    (hV : ∀ u, 0 ≤ (Γ.sliceEnergy (μ := μ) β u).re)
    (u : Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) :
    ‖Complex.exp (-Γ.sliceEnergy β u)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simpa using hV u
theorem norm_cycleTerm_le {β : ℝ} (hV : ∀ u, 0 ≤ (Γ.sliceEnergy (μ := μ) β u).re)
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ) (k : Fin Γ.side)
    (p : PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ))
    (U : Γ.lattice.QuotientField) :
    ‖Γ.cycleTerm β X k p U‖ ≤ Γ.cycleTermBound β X k p := by
  have h₁ : 0 ≤ sqrtPeterWeylCoeff β p.1 := Real.sqrt_nonneg _
  have h₂ : 0 ≤ sqrtPeterWeylCoeff β p.2 := Real.sqrt_nonneg _
  have hE := Γ.norm_exp_neg_sliceEnergy_le hV (Γ.kernelLeftArg U k)
  have hψ₁ : ‖peterWeylFn p.1 (Γ.kernelLeftArg U k)‖ ≤ ‖peterWeylFn p.1‖ :=
    (peterWeylFn p.1).norm_coe_le_norm _
  have hψ₂ : ‖peterWeylFn p.2 (Γ.kernelRightArg U k)‖ ≤ ‖peterWeylFn p.2‖ :=
    (peterWeylFn p.2).norm_coe_le_norm _
  unfold cycleTerm cycleTermBound
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) hE).trans ?_
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h₁,
    abs_of_nonneg h₂]
  gcongr
theorem continuous_cycleTerm {β : ℝ} (hVc : Continuous (Γ.sliceEnergy (μ := μ) β))
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ) (k : Fin Γ.side)
    (p : PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ)) :
    Continuous (Γ.cycleTerm β X k p) := by
  have h₁ := Γ.continuous_kernelLeftArg (μ := μ) k
  have h₂ := Γ.continuous_kernelRightArg (μ := μ) k
  unfold cycleTerm
  exact (Complex.continuous_exp.comp (hVc.comp h₁).neg).mul
    ((continuous_const.mul ((peterWeylFn p.1).continuous.comp h₁)).mul
      (continuous_star.comp ((peterWeylFn p.2).continuous.comp h₂)))
theorem continuous_pairIntegrand {β : ℝ}
    (hVc : Continuous (Γ.sliceEnergy (μ := μ) β)) (α' α : PeterWeylIndex (Γ.LinkOrbits μ)) :
    Continuous (Γ.pairIntegrand β α' α) := by
  unfold pairIntegrand
  exact ((continuous_star.comp ((peterWeylFn α').continuous.comp
    (Γ.continuous_orbitGaugeAct_pair (μ := μ)))).mul
      (Complex.continuous_exp.comp (hVc.comp continuous_snd).neg)).mul
    ((peterWeylFn α).continuous.comp continuous_snd)
theorem prod_cycleTerm (β : ℝ)
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ)
    (a : Fin Γ.side → PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ))
    (U : Γ.lattice.QuotientField) :
    ∏ k, Γ.cycleTerm β X k (a k) U =
      (∏ k, (sqrtPeterWeylCoeff β (a k).1 : ℂ) * (sqrtPeterWeylCoeff β (a k).2 : ℂ) *
          peterWeylEntry (X k) (a k).1 (a k).2) *
        ∏ k, Γ.pairIntegrand β (a k).2 (a (finRotate _ k)).1
          (Γ.slicePairs μ U (Γ.indexLevel k)) := by
  have hrot := Equiv.prod_comp (finRotate Γ.side) fun k =>
    Complex.exp (-Γ.sliceEnergy (μ := μ) β (Γ.kernelLeftArg (μ := μ) U k)) *
      peterWeylFn (a k).1 (Γ.kernelLeftArg (μ := μ) U k)
  have hsec : ∀ k, Γ.kernelLeftArg (μ := μ) U (finRotate _ k) =
      Γ.sliceField (μ := μ) U (Γ.indexLevel k + 1) := fun k => by
    rw [kernelLeftArg, indexLevel_finRotate]
  calc ∏ k, Γ.cycleTerm β X k (a k) U
      = ∏ k, ((sqrtPeterWeylCoeff β (a k).1 : ℂ) * (sqrtPeterWeylCoeff β (a k).2 : ℂ) *
            peterWeylEntry (X k) (a k).1 (a k).2) *
          (Complex.exp (-Γ.sliceEnergy β (Γ.kernelLeftArg U k)) *
            peterWeylFn (a k).1 (Γ.kernelLeftArg U k)) *
          star (peterWeylFn (a k).2 (Γ.kernelRightArg U k)) :=
        Finset.prod_congr rfl fun k _ => by unfold cycleTerm; ring
    _ = (∏ k, (sqrtPeterWeylCoeff β (a k).1 : ℂ) * (sqrtPeterWeylCoeff β (a k).2 : ℂ) *
            peterWeylEntry (X k) (a k).1 (a k).2) *
          (∏ k, Complex.exp (-Γ.sliceEnergy β (Γ.kernelLeftArg U k)) *
            peterWeylFn (a k).1 (Γ.kernelLeftArg U k)) *
          ∏ k, star (peterWeylFn (a k).2 (Γ.kernelRightArg U k)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = _ := by
        rw [← hrot, mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [hsec]
        simp only [pairIntegrand, slicePairs, kernelRightArg]
        ring
theorem integral_prod_cycleTerm {β : ℝ} (hVc : Continuous (Γ.sliceEnergy (μ := μ) β))
    (hMP : MeasurePreserving (Γ.slicePairs μ) Γ.lattice.quotientHaar
      (Measure.pi fun _ : ZMod Γ.side =>
        (Matrices.ComplexMatrix2.haarPi (Γ.VertexOrbits μ)).prod
          (Matrices.ComplexMatrix2.haarPi (Γ.LinkOrbits μ))))
    (hPair : ∀ α' α : PeterWeylIndex (Γ.LinkOrbits μ),
      (sqrtPeterWeylCoeff β α' : ℂ) * (sqrtPeterWeylCoeff β α : ℂ) *
          ∫ p, Γ.pairIntegrand β α' α p
            ∂(Matrices.ComplexMatrix2.haarPi (Γ.VertexOrbits μ)).prod
              (Matrices.ComplexMatrix2.haarPi (Γ.LinkOrbits μ)) =
        peterWeylEntry (Γ.transfer μ β) α' α)
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ)
    (a : Fin Γ.side → PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ)) :
    ∫ U, ∏ k, Γ.cycleTerm β X k (a k) U ∂Γ.lattice.quotientHaar =
      traceExpansionTerm X (Γ.transfer μ β) a := by
  let m := (Matrices.ComplexMatrix2.haarPi (Γ.VertexOrbits μ)).prod
    (Matrices.ComplexMatrix2.haarPi (Γ.LinkOrbits μ))
  let F : Fin Γ.side → (Γ.VertexOrbits μ → Matrices.ComplexMatrix2.specialUnitary) ×
      (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) → ℂ :=
    fun k => Γ.pairIntegrand β (a k).2 (a (finRotate _ k)).1
  have hF : ∀ k, Continuous (F k) := fun k => Γ.continuous_pairIntegrand hVc _ _
  let e : Fin Γ.side ≃ ZMod Γ.side := Equiv.ofBijective _ Γ.indexLevel_bijective
  have hG : Continuous fun w : ZMod Γ.side →
      (Γ.VertexOrbits μ → Matrices.ComplexMatrix2.specialUnitary) ×
        (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) =>
      ∏ c, F (e.symm c) (w c) :=
    continuous_finsetProd _ fun c _ => (hF _).comp (continuous_apply c)
  have hfac : ∀ U : Γ.lattice.QuotientField,
      ∏ k, F k (Γ.slicePairs μ U (Γ.indexLevel k)) =
        ∏ c, F (e.symm c) (Γ.slicePairs μ U c) := fun U => by
    rw [← Equiv.prod_comp e fun c => F (e.symm c) (Γ.slicePairs μ U c)]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Equiv.symm_apply_apply]
    rfl
  have hint : ∫ U, ∏ k, F k (Γ.slicePairs μ U (Γ.indexLevel k)) ∂Γ.lattice.quotientHaar =
      ∏ k, ∫ x, F k x ∂m := by
    have h := integral_map (μ := Γ.lattice.quotientHaar) hMP.aemeasurable
      (f := fun w => ∏ c, F (e.symm c) (w c)) (by rw [hMP.map_eq]; exact hG.aestronglyMeasurable)
    rw [hMP.map_eq, integral_fintype_prod_eq_prod (fun c => F (e.symm c))] at h
    rw [funext hfac, ← h, ← Equiv.prod_comp e fun c => ∫ x, F (e.symm c) x ∂m]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Equiv.symm_apply_apply]
  have hterm : (fun U => ∏ k, Γ.cycleTerm β X k (a k) U) = fun U =>
      (∏ k, (sqrtPeterWeylCoeff β (a k).1 : ℂ) * (sqrtPeterWeylCoeff β (a k).2 : ℂ) *
          peterWeylEntry (X k) (a k).1 (a k).2) *
        ∏ k, F k (Γ.slicePairs μ U (Γ.indexLevel k)) :=
    funext fun U => Γ.prod_cycleTerm β X a U
  have hp : ∀ j, peterWeylEntry (Γ.transfer μ β) (a j).2 (a (finRotate _ j)).1 =
      (sqrtPeterWeylCoeff β (a j).2 : ℂ) *
        (sqrtPeterWeylCoeff β (a (finRotate _ j)).1 : ℂ) * ∫ x, F j x ∂m :=
    fun j => (hPair _ _).symm
  have hrot := Equiv.prod_comp (finRotate Γ.side) fun k =>
    (sqrtPeterWeylCoeff β (a k).1 : ℂ)
  have hmain : ∏ j, peterWeylEntry (X j) (a j).1 (a j).2 *
        peterWeylEntry (Γ.transfer μ β) (a j).2 (a (finRotate _ j)).1 =
      ∏ j, peterWeylEntry (X j) (a j).1 (a j).2 * ((sqrtPeterWeylCoeff β (a j).2 : ℂ) *
        (sqrtPeterWeylCoeff β (a (finRotate _ j)).1 : ℂ) * ∫ x, F j x ∂m) :=
    Finset.prod_congr rfl fun j _ => by rw [hp j]
  rw [hterm, integral_const_mul, hint]
  unfold traceExpansionTerm
  rw [hmain]
  simp only [Finset.prod_mul_distrib]
  rw [hrot]
  ring
theorem hasSum_prod_cycleTerm {β : ℝ} (hV : ∀ u, 0 ≤ (Γ.sliceEnergy (μ := μ) β u).re)
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ)
    (hK : ∀ k, KernelBoundedContinuousSeries β (X k)) (U : Γ.lattice.QuotientField) :
    HasSum (fun a : Fin Γ.side → PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ) =>
      ∏ k, Γ.cycleTerm β X k (a k) U) (Γ.kernelCycle μ β X U) := by
  have hterm : ∀ k, HasSum (fun p => Γ.cycleTerm β X k p U)
      (Complex.exp (-Γ.sliceEnergy β (Γ.kernelLeftArg (μ := μ) U k)) *
        sqrtKernelSandwich β (X k) (Γ.kernelLeftArg U k) (Γ.kernelRightArg U k)) :=
    fun k => ((hK k).2.2.2.1 _ _).mul_left _
  have hnorm : ∀ k, Summable fun p => ‖Γ.cycleTerm β X k p U‖ := fun k =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => Γ.norm_cycleTerm_le hV X k p U) (hK k).2.2.2.2
  exact (KernelCycleTrace.hasSum_fin_prod_of_summable_norm Γ.side
    (fun k p => Γ.cycleTerm β X k p U) _ hnorm hterm).2
theorem summable_norm_prod_cycleTermBound {β : ℝ}
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ)
    (hK : ∀ k, KernelBoundedContinuousSeries β (X k)) :
    Summable fun a : Fin Γ.side → PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ) =>
      ‖∏ k, Γ.cycleTermBound β X k (a k)‖ := by
  have hb : ∀ k, Summable (Γ.cycleTermBound β X k) := fun k => (hK k).2.2.2.2
  exact (KernelCycleTrace.hasSum_fin_prod_of_summable_norm Γ.side
    (fun k p => Γ.cycleTermBound β X k p)
    (fun k => ∑' p, Γ.cycleTermBound β X k p)
    (fun k => (hb k).congr fun p =>
      (Real.norm_of_nonneg (Γ.cycleTermBound_nonneg β X k p)).symm)
    fun k => (hb k).hasSum).1
theorem norm_prod_cycleTerm_le {β : ℝ} (hV : ∀ u, 0 ≤ (Γ.sliceEnergy (μ := μ) β u).re)
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ)
    (a : Fin Γ.side → PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ))
    (U : Γ.lattice.QuotientField) :
    ‖∏ k, Γ.cycleTerm β X k (a k) U‖ ≤ ‖∏ k, Γ.cycleTermBound β X k (a k)‖ := by
  rw [norm_prod, Real.norm_of_nonneg
    (Finset.prod_nonneg fun k _ => Γ.cycleTermBound_nonneg β X k _)]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    fun k _ => Γ.norm_cycleTerm_le hV X k _ U
theorem integrable_prod_cycleTerm {β : ℝ} (hVc : Continuous (Γ.sliceEnergy (μ := μ) β))
    (hV : ∀ u, 0 ≤ (Γ.sliceEnergy (μ := μ) β u).re)
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ)
    (a : Fin Γ.side → PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ)) :
    Integrable (fun U => ∏ k, Γ.cycleTerm β X k (a k) U) Γ.lattice.quotientHaar := by
  have : IsProbabilityMeasure Γ.lattice.quotientHaar := haarPi_isProbabilityMeasure _
  have hc : Continuous fun U => ∏ k, Γ.cycleTerm β X k (a k) U :=
    continuous_finsetProd _ fun k _ => Γ.continuous_cycleTerm hVc X k _
  exact Integrable.of_bound hc.aestronglyMeasurable _
    (Filter.Eventually.of_forall (Γ.norm_prod_cycleTerm_le hV X a))
theorem integrable_kernelCycle {β : ℝ} (hVc : Continuous (Γ.sliceEnergy (μ := μ) β))
    (hV : ∀ u, 0 ≤ (Γ.sliceEnergy (μ := μ) β u).re)
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ) (hX : ∀ k, ‖X k‖ ≤ 1)
    (hK : ∀ k, KernelBoundedContinuousSeries β (X k)) :
    Integrable (Γ.kernelCycle μ β X) Γ.lattice.quotientHaar := by
  have : IsProbabilityMeasure Γ.lattice.quotientHaar := haarPi_isProbabilityMeasure _
  have hfac : ∀ k, Continuous fun U : Γ.lattice.QuotientField =>
      Complex.exp (-Γ.sliceEnergy β (Γ.kernelLeftArg (μ := μ) U k)) *
        sqrtKernelSandwich β (X k) (Γ.kernelLeftArg U k) (Γ.kernelRightArg U k) := fun k => by
    have h₁ := Γ.continuous_kernelLeftArg (μ := μ) k
    have h₂ := Γ.continuous_kernelRightArg (μ := μ) k
    have h₃ : Continuous fun U : Γ.lattice.QuotientField =>
        sqrtKernelSandwich β (X k) (Γ.kernelLeftArg (μ := μ) U k) (Γ.kernelRightArg U k) :=
      Continuous.comp
        (g := fun p : (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) ×
            (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) =>
          sqrtKernelSandwich β (X k) p.1 p.2)
        (f := fun U : Γ.lattice.QuotientField =>
          (Γ.kernelLeftArg (μ := μ) U k, Γ.kernelRightArg (μ := μ) U k))
        (hK k).2.1 (h₁.prodMk h₂)
    have h₄ : Continuous fun U : Γ.lattice.QuotientField =>
        Complex.exp (-Γ.sliceEnergy β (Γ.kernelLeftArg (μ := μ) U k)) :=
      Complex.continuous_exp.comp (hVc.comp h₁).neg
    exact h₄.mul h₃
  have hcc : Continuous (Γ.kernelCycle μ β X) := continuous_finsetProd _ fun k _ => hfac k
  have hone : ∀ U, ‖Γ.kernelCycle μ β X U‖ ≤ 1 := fun U => by
    unfold kernelCycle
    rw [norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (Γ.norm_exp_neg_sliceEnergy_le hV _) (norm_nonneg _)
      (((hK k).2.2.1 _ _).trans (hX k))
  exact Integrable.of_bound hcc.aestronglyMeasurable 1 (Filter.Eventually.of_forall hone)
theorem hasSum_integral_prod_cycleTerm {β : ℝ} (hVc : Continuous (Γ.sliceEnergy (μ := μ) β))
    (hV : ∀ u, 0 ≤ (Γ.sliceEnergy (μ := μ) β u).re)
    (X : Fin Γ.side → Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ)
    (hK : ∀ k, KernelBoundedContinuousSeries β (X k)) :
    HasSum (fun a : Fin Γ.side → PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ) =>
      ∫ U, ∏ k, Γ.cycleTerm β X k (a k) U ∂Γ.lattice.quotientHaar)
      (∫ U, Γ.kernelCycle μ β X U ∂Γ.lattice.quotientHaar) := by
  have : Countable PeterWeylLabel := KernelCycleTrace.countable_peterWeylLabel
  have : IsProbabilityMeasure Γ.lattice.quotientHaar := haarPi_isProbabilityMeasure _
  have hsummable : Summable fun a : Fin Γ.side →
      PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ) =>
      ∫ U, ‖∏ k, Γ.cycleTerm β X k (a k) U‖ ∂Γ.lattice.quotientHaar :=
    Summable.of_nonneg_of_le (fun a => integral_nonneg fun _ => norm_nonneg _)
      (fun a => (integral_mono (Γ.integrable_prod_cycleTerm hVc hV X a).norm
        (integrable_const _) (Γ.norm_prod_cycleTerm_le hV X a)).trans (by simp))
      (Γ.summable_norm_prod_cycleTermBound X hK)
  have hI := hasSum_integral_of_summable_integral_norm
    (Γ.integrable_prod_cycleTerm hVc hV X) hsummable
  have htsum : (fun U => ∑' a : Fin Γ.side →
      PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ),
      ∏ k, Γ.cycleTerm β X k (a k) U) = Γ.kernelCycle μ β X :=
    funext fun U => (Γ.hasSum_prod_cycleTerm hV X hK U).tsum_eq
  rw [htsum] at hI
  exact hI
end CubicPeriodSublattice
theorem KernelCycleTrace.axis_add_one_ne (μ : Fin 4) : μ + 1 ≠ μ := by
  revert μ
  decide
theorem KernelCycleTrace.statement_holds
    (hTrace : ContractionTraceBound.Statement)
    (hFacts : CubicTorusOperators.Statement)
    (hKernel : SandwichKernelBoundedStatement)
    (hEnergy : SliceEnergyProperties.Statement)
    (hLayers : SliceDecomposition.Statement)
    (hPair : PairIntegralMatrixEntry.Statement) :
    KernelCycleTrace.Statement := by
  intro β hβ Γ μ X hX
  have hne : Nonempty (Γ.LinkOrbits μ) :=
    ⟨Γ.linkClass (SliceLink.ofAxis 0 (μ + 1) (KernelCycleTrace.axis_add_one_ne μ))⟩
  obtain ⟨hVc, hVr, -⟩ := hEnergy β hβ Γ μ
  have hV : ∀ u, 0 ≤ (Γ.sliceEnergy (μ := μ) β u).re := fun u => (hVr u).2
  have hL := ((hFacts β hβ).1 Γ μ).2.2.2
  obtain ⟨hT₁, -, hT₃, -⟩ := (hTrace Γ.side Γ.one_le_side).2 (Γ.LinkOrbits μ)
    (Γ.transfer μ β) X hL.transfer_nonneg hL.entry_summable hX
  have hK : ∀ k, KernelBoundedContinuousSeries β (X k) := fun k =>
    hKernel β hβ (Γ.LinkOrbits μ) (X k)
  have hfun : (fun a : Fin Γ.side → PeterWeylIndex (Γ.LinkOrbits μ) × PeterWeylIndex (Γ.LinkOrbits μ) =>
      ∫ U, ∏ k, Γ.cycleTerm β X k (a k) U ∂Γ.lattice.quotientHaar) =
      traceExpansionTerm X (Γ.transfer μ β) :=
    funext fun a => Γ.integral_prod_cycleTerm hVc (hLayers Γ μ).2
      (fun α' α => (hPair β hβ Γ μ α' α).2) X a
  have hI := Γ.hasSum_integral_prod_cycleTerm hVc hV X hK
  rw [hfun] at hI
  refine ⟨hT₁, Γ.integrable_kernelCycle hVc hV X hX hK, ?_⟩
  rw [hT₃]
  exact hI.tsum_eq.symm
end TransferOperators
end YangMills.Construction
end
