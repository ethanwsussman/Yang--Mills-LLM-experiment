import YangMills.Construction.FormHilbert.JointSpectralCalculus
import YangMills.Construction.InfiniteLattice.PeriodsFoldCompactnessAndLimitsOfToriProof
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamilyProof
import YangMills.Construction.ReflectionPositivity.ClassesAndMatrixElementsAtASpacing
import YangMills.Construction.ReflectionPositivity.CoarseStepsAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseSteps
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint axisStep shift IsBoundedObservable
  pointOfUnit pointOfUnit_axisStep)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet coordinateReflect)
open YangMills.Construction.JointSpectrum (CommutingFamily SpectralDomain spectralMonomial torusMonomial)
open YangMills.Construction.FormHilbert
open YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
section Family
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : Type*} [Fintype J] [Nonempty J] [DecidableEq J]
omit [Fintype J] [Nonempty J] [DecidableEq J] in
private theorem noncommProd_eq_of_eq_one_off {G : Type*} [Monoid G] (f : J → G) (α : J)
    (hf : ∀ β, β ≠ α → f β = 1) (t : Finset J) (comm) (hα : α ∈ t) :
    t.noncommProd f comm = f α := by
  classical
  have hrest : ∀ (s : Finset J) (c), α ∉ s → s.noncommProd f c = 1 := fun s c h =>
    Finset.noncommProd_induction _ _ _ (fun u => u = 1)
      (fun a b ha hb => by rw [ha, hb, one_mul]) rfl
      (fun β hβ => hf β fun e => h (e ▸ hβ))
  obtain ⟨s, hs, rfl⟩ : ∃ s, α ∉ s ∧ t = insert α s :=
    ⟨t.erase α, Finset.notMem_erase α t, (Finset.insert_erase hα).symm⟩
  rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hs, hrest _ _ hs, mul_one]
private theorem unitaryMonomial_single (S : CommutingFamily H J) (i : J) (m : ℤ) :
    S.unitaryMonomial (Pi.single i m) = ((S.B i ^ m : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
  have h₁ : Finset.univ.noncommProd (fun β => S.B β ^ (Pi.single i m : J → ℤ) β)
      (fun β _ β' _ _ => S.commute_zpow_unitary (Pi.single i m) β β') = S.B i ^ m := by
    refine (noncommProd_eq_of_eq_one_off _ i (fun β hβ => by simp [Pi.single_eq_of_ne hβ]) _ _
      (Finset.mem_univ i)).trans ?_
    simp
  exact congrArg Subtype.val h₁
private def shiftPowerOp (S : CommutingFamily H J) (i : J) (n : ℕ) (m : ℤ) : H →L[ℂ] H :=
  S.A ^ n * ((S.B i ^ m : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
omit [DecidableEq J] in
private theorem five_term_expansion (S : CommutingFamily H J) (i : J) (k : ℕ) :
    (1 - S.A ^ k) ^ 2 - S.A ^ k * ((2 : ℂ) • 1 - (S.B i : H →L[ℂ] H) ^ k -
        star (S.B i : H →L[ℂ] H) ^ k) =
      shiftPowerOp S i 0 0 - (4 : ℂ) • shiftPowerOp S i k 0 + shiftPowerOp S i (2 * k) 0 +
        shiftPowerOp S i k k + shiftPowerOp S i k (-k) := by
  have h₁ : ((S.B i ^ (k : ℤ) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = (S.B i : H →L[ℂ] H) ^ k := by
    rw [zpow_natCast]
    rfl
  have h₂ : ((S.B i ^ (-(k : ℤ)) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      star (S.B i : H →L[ℂ] H) ^ k := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, ← Unitary.star_eq_inv]
    rfl
  have h₀ : ((S.B i ^ (0 : ℤ) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = 1 := by
    rw [zpow_zero]
    rfl
  simp only [shiftPowerOp, h₀, h₁, h₂, pow_zero, mul_one, pow_mul']
  generalize S.A ^ k = T
  generalize (S.B i : H →L[ℂ] H) ^ k = P
  generalize star (S.B i : H →L[ℂ] H) ^ k = Q
  have h₄ : (4 : ℂ) • T = (4 : ℕ) • T := by
    simpa using Nat.cast_smul_eq_nsmul ℂ 4 T
  rw [two_smul, h₄]
  noncomm_ring
omit [Nonempty J] [DecidableEq J] in
private theorem isBddMeasurable_spectralMonomial (n : ℕ) (y : J → ℤ) :
    IsBddMeasurable (spectralMonomial n y : SpectralDomain J → ℂ) := by
  refine ⟨?_, 1, fun p => ?_⟩
  · have h₁ : Continuous fun p : SpectralDomain J => (((p.1 : ℝ)) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    have h₂ : ∀ α, Continuous fun p : SpectralDomain J => ((p.2 α : Circle) : ℂ) := fun α =>
      continuous_subtype_val.comp ((continuous_apply α).comp continuous_snd)
    have h₃ : Continuous (spectralMonomial n y : SpectralDomain J → ℂ) := by
      refine (h₁.pow n).mul (continuous_finsetProd _ fun α _ => ?_)
      exact (h₂ α).zpow₀ (y α) fun p => Or.inl (Circle.coe_ne_zero _)
    exact h₃.measurable
  · have h₁ : ‖(((p.1 : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
      exact p.1.2.2
    have h₂ : ‖torusMonomial p.2 y‖ = 1 := by
      simp [torusMonomial, norm_zpow, Circle.norm_coe]
    rw [spectralMonomial, norm_mul, norm_pow, h₂, mul_one]
    exact pow_le_one₀ (norm_nonneg _) h₁
omit [Fintype J] [Nonempty J] [DecidableEq J] in
private theorem isBddMeasurable_add_mul {φ φ' : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ)
    (hφ' : IsBddMeasurable φ') (c : ℂ) : IsBddMeasurable fun p => φ p + c * φ' p := by
  obtain ⟨m, C, hC⟩ := hφ
  obtain ⟨m', C', hC'⟩ := hφ'
  refine ⟨m.add (m'.const_mul c), C + ‖c‖ * C', fun p => ?_⟩
  refine (norm_add_le _ _).trans (add_le_add (hC p) ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC' p) (norm_nonneg _)
private def fiveTermFunction (i : J) (k : ℕ) : SpectralDomain J → ℂ := fun p =>
  spectralMonomial 0 (Pi.single i 0) p + (-4) * spectralMonomial k (Pi.single i 0) p +
    1 * spectralMonomial (2 * k) (Pi.single i 0) p + 1 * spectralMonomial k (Pi.single i (k : ℤ)) p +
    1 * spectralMonomial k (Pi.single i (-(k : ℤ))) p
private theorem inner_fiveTerm_eq_integral {S : CommutingFamily H J}
    {E : BorelPVM J H} (hcalc : BoundedFunctionalCalculus S E) (i : J) (k : ℕ)
    (ψ : H) :
    inner ℂ ψ ((shiftPowerOp S i 0 0 - (4 : ℂ) • shiftPowerOp S i k 0 + shiftPowerOp S i (2 * k) 0 +
        shiftPowerOp S i k k + shiftPowerOp S i k (-k)) ψ) =
      ∫ p, fiveTermFunction i k p ∂(E.quadMeasure ψ) := by
  have hm : ∀ (n : ℕ) (m : ℤ), E.spectralOp (spectralMonomial n (Pi.single i m)) = shiftPowerOp S i n m :=
    fun n m => by rw [hcalc.spectralOp_monomial, unitaryMonomial_single, shiftPowerOp]
  have hb : ∀ (n : ℕ) (m : ℤ), IsBddMeasurable (spectralMonomial n (Pi.single i m) :
      SpectralDomain J → ℂ) := fun n m => isBddMeasurable_spectralMonomial n _
  have b₁ := isBddMeasurable_add_mul (hb 0 0) (hb k 0) (-4)
  have b₂ := isBddMeasurable_add_mul b₁ (hb (2 * k) 0) 1
  have b₃ := isBddMeasurable_add_mul b₂ (hb k k) 1
  have b₄ := isBddMeasurable_add_mul b₃ (hb k (-k)) 1
  have hop : E.spectralOp (fiveTermFunction i k) =
      shiftPowerOp S i 0 0 - (4 : ℂ) • shiftPowerOp S i k 0 + shiftPowerOp S i (2 * k) 0 +
        shiftPowerOp S i k k + shiftPowerOp S i k (-k) := by
    unfold fiveTermFunction
    rw [hcalc.spectralOp_add_smul _ _ b₃ (hb k (-k)), hcalc.spectralOp_add_smul _ _ b₂ (hb k k),
      hcalc.spectralOp_add_smul _ _ b₁ (hb (2 * k) 0),
      hcalc.spectralOp_add_smul _ _ (hb 0 0) (hb k 0), hm, hm, hm, hm, hm]
    simp only [one_smul, neg_smul, sub_eq_add_neg]
  rw [← hop]
  have hI : E.IsSpectralIntegral (fiveTermFunction i k) (E.spectralOp (fiveTermFunction i k)) := by
    have hex : ∃ A, E.IsSpectralIntegral (fiveTermFunction i k) A := hcalc.exists_spectralOp _ b₄
    unfold BorelPVM.spectralOp
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact hI ψ
end Family
section Coordinates
variable {μ : Fin 4}
private theorem expDecayAt_energyOfUnit {n : ℕ} (hn : 1 ≤ n) (t : unitInterval) :
    expDecayAt n (energyOfUnit t) = (t : ℝ) ^ n := by
  by_cases h : (t : ℝ) = 0
  · rw [h, zero_pow (by omega)]
    simp [expDecayAt, energyOfUnit, h]
  · have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm h)
    have hnn : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos t.2.1 t.2.2)
    have hE : energyOfUnit t = ENNReal.ofReal (-Real.log t) := by simp [energyOfUnit, h]
    rw [expDecayAt, hE, if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hnn]
    have : -((n : ℝ) * -Real.log t) = (n : ℝ) * Real.log t := by ring
    rw [this, Real.exp_nat_mul, Real.exp_log hpos]
private theorem two_cos_mul_arg (ζ : Circle) (k : ℕ) :
    ((2 * Real.cos ((k : ℝ) * Complex.arg ζ) : ℝ) : ℂ) =
      (ζ : ℂ) ^ (k : ℤ) + (ζ : ℂ) ^ (-(k : ℤ)) := by
  have hζ : (ζ : ℂ) = Complex.exp ((Complex.arg ζ : ℝ) * Complex.I) := by
    rw [← Circle.coe_exp, Circle.exp_arg]
  generalize Complex.arg (ζ : ℂ) = θ at hζ ⊢
  push_cast
  rw [Complex.two_cos, hζ, zpow_neg, zpow_natCast, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  ring_nf
private theorem pullToSpectrum_coarseSpectralBracket (l : TransverseAxis μ) {k : ℕ} (hk : 1 ≤ k)
    (q : SpectralDomain (TransverseAxis μ)) :
    pullToSpectrum μ (fun x => ((coarseSpectralBracket l k x : ℝ) : ℂ)) q =
      fiveTermFunction l k q := by
  have hz : ∀ m : ℤ, torusMonomial q.2 (Pi.single l m) = (q.2 l : ℂ) ^ m := fun m => by
    unfold torusMonomial
    rw [Fintype.prod_eq_single l fun β hβ => by rw [Pi.single_eq_of_ne hβ, zpow_zero]]
    rw [Pi.single_eq_same]
  have hc := two_cos_mul_arg (q.2 l) k
  simp only [pullToSpectrum, Function.comp_apply, coarseSpectralBracket, fromSpectrum,
    fiveTermFunction, spectralMonomial, hz, expDecayAt_energyOfUnit hk,
    expDecayAt_energyOfUnit (show 1 ≤ 2 * k by omega)]
  have h2 : (((2 * Real.cos ((k : ℝ) * Complex.arg (q.2 l)) : ℝ)) : ℂ) =
      2 * ((Real.cos ((k : ℝ) * Complex.arg (q.2 l)) : ℝ) : ℂ) := by push_cast; ring
  rw [h2] at hc
  push_cast at hc ⊢
  simp only [zpow_zero, pow_zero, mul_one, one_mul]
  linear_combination (((q.1 : ℝ) : ℂ) ^ k) * hc
private theorem coarseSpectralBracket_of_ne_top (l : TransverseAxis μ) (k : ℕ)
    (x : ℝ≥0∞ × (TransverseAxis μ → ℝ)) (hx : x.1 ≠ ⊤) :
    coarseSpectralBracket l k x =
      2 * expDecayAt k x.1 *
        (Real.cosh ((k : ℝ) * x.1.toReal) + Real.cos ((k : ℝ) * x.2 l) - 2) := by
  set u : ℝ := (k : ℝ) * x.1.toReal with hu
  have h₁ : expDecayAt k x.1 = Real.exp (-u) := by rw [expDecayAt, if_neg hx]
  have h₂ : expDecayAt (2 * k) x.1 = Real.exp (-u) * Real.exp (-u) := by
    rw [expDecayAt, if_neg hx, ← Real.exp_add]
    congr 1
    rw [hu]
    push_cast
    ring
  have h₃ : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  rw [coarseSpectralBracket, h₁, h₂, Real.cosh_eq]
  linear_combination -h₃
end Coordinates
section Lattice
variable {a : ℝ}
private theorem pointOfUnit_single (a : ℝ) (μ l : Fin 4) (n : ℕ) (m : ℤ) :
    pointOfUnit a (n • axisStep 1 μ + intPoint (Pi.single l m)) =
      n • axisStep a μ + m • axisStep a l := by
  have h : intPoint (Pi.single l m) = m • axisStep 1 l := by
    refine Subtype.ext (funext fun i => ?_)
    by_cases hi : i = l
    · subst hi
      simp [intPoint, axisStep]
    · simp [intPoint, axisStep, Pi.single_eq_of_ne hi]
  rw [h, map_add, map_nsmul, map_zsmul, pointOfUnit_axisStep, pointOfUnit_axisStep]
private theorem isBoundedObservable_conj {G : GaugeField a → ℂ} (hG : IsBoundedObservable G) :
    IsBoundedObservable fun U => conj (G U) := by apply _root_.YangMills.Construction.NormalFamilies.ReflectionIdentities.isBoundedObservable_conj <;> assumption
private theorem isBoundedObservable_mul {G G' : GaugeField a → ℂ} (hG : IsBoundedObservable G)
    (hG' : IsBoundedObservable G') : IsBoundedObservable fun U => G U * G' U := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.isBoundedObservable_mul <;> assumption
private theorem isBoundedObservable_integrable {G : GaugeField a → ℂ} (hG : IsBoundedObservable G)
    (ν : Measure (GaugeField a)) [IsFiniteMeasure ν] : Integrable G ν := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsFoldAndCompactness.integrable_of_isBoundedObservable <;> assumption
private theorem isAffineInMeasure_of_isBoundedObservable {G : GaugeField a → ℂ}
    (hG : IsBoundedObservable G) : IsAffineInMeasure G := by
  refine ⟨hG, fun ν₁ ν₂ t => ?_⟩
  have f₁ : IsFiniteMeasure ν₁.1 := by
    have := ν₁.2
    infer_instance
  have f₂ : IsFiniteMeasure ν₂.1 := by
    have := ν₂.2
    infer_instance
  have hs : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  have i₁ : Integrable G (ENNReal.ofReal t • ν₁.1) :=
    (isBoundedObservable_integrable hG ν₁.1).smul_measure ENNReal.ofReal_ne_top
  have i₂ : Integrable G (ENNReal.ofReal (1 - t) • ν₂.1) :=
    (isBoundedObservable_integrable hG ν₂.1).smul_measure ENNReal.ofReal_ne_top
  change ∫ U, G U ∂(ENNReal.ofReal t • ν₁.1 + ENNReal.ofReal (1 - (t : ℝ)) • ν₂.1) =
    ((t : ℝ) : ℂ) * ∫ U, G U ∂ν₁.1 + ((1 - (t : ℝ) : ℝ) : ℂ) * ∫ U, G U ∂ν₂.1
  rw [integral_add_measure i₁ i₂, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal t.2.1, ENNReal.toReal_ofReal hs]
  simp [Complex.real_smul]
private abbrev pictureFamily (ν : BorelProb a) (μ : Fin 4) :
    CommutingFamily (ScaledPair.Hilb ν.1 μ) (TransverseAxis μ) :=
  ReflectionPair.site.opFamily (unitRepresentative ν.1) μ
private theorem inner_shiftPowerOp_eq (hsame : ScaledClassesTheorem)
    (ha : 0 < a) {ν : BorelProb a} (hν : ν ∈ reflectionPositiveSet a) (μ : Fin 4)
    (l : TransverseAxis μ) {F : GaugeField a → ℂ} (hF : F ∈ localHalfSpaceObs a μ)
    (n : ℕ) (m : ℤ) :
    inner ℂ (ScaledPair.obsClass ν.1 μ ha F)
        (shiftPowerOp (pictureFamily ν μ) l n m (ScaledPair.obsClass ν.1 μ ha F)) =
      CoarseStepsInverseSquare.reflectedCorrelation ν μ F (n • axisStep a μ + m • axisStep a l.1) := by
  have hF' : F ∈ halfSpaceLocalAtMesh a μ :=
    (mem_halfSpaceLocalAtMesh_iff a μ F).mpr hF
  have h := (hsame a ha ν hν μ).2.1.1 F hF' F hF' n (Pi.single l.1 m)
    (by rw [Pi.single_eq_of_ne (Ne.symm l.2)])
  have hw : (fun l' : TransverseAxis μ => (Pi.single l.1 m : Fin 4 → ℤ) l'.1) = Pi.single l m := by
    funext l'
    by_cases hl : l' = l
    · subst hl
      simp
    · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne fun e => hl (Subtype.ext e)]
  have hp : ScaledPair.shiftMonomial ν.1 μ (Pi.single l.1 m) =
      (((pictureFamily ν μ).B l ^ m : unitary _) : _ →L[ℂ] _) := by
    change (pictureFamily ν μ).unitaryMonomial _ = _
    rw [hw, unitaryMonomial_single]
  rw [hp, pointOfUnit_single] at h
  exact h
private theorem energy_sub_momentum_eq (ν : BorelProb a) (μ : Fin 4) (l : TransverseAxis μ) (k : ℕ) :
    energyOpCoarse ν μ k - momentumOpCoarse ν μ l k =
      shiftPowerOp (pictureFamily ν μ) l 0 0 - (4 : ℂ) • shiftPowerOp (pictureFamily ν μ) l k 0 +
        shiftPowerOp (pictureFamily ν μ) l (2 * k) 0 + shiftPowerOp (pictureFamily ν μ) l k k +
        shiftPowerOp (pictureFamily ν μ) l k (-k) :=
  five_term_expansion (pictureFamily ν μ) l k
private theorem fivePointCombination_eq_inner (hsame : ScaledClassesTheorem)
    (ha : 0 < a) {ν : BorelProb a} (hν : ν ∈ reflectionPositiveSet a) (μ : Fin 4)
    (l : TransverseAxis μ) (k : ℕ) {F : GaugeField a → ℂ}
    (hF : F ∈ localHalfSpaceObs a μ) :
    fivePointCombination ν μ l k F =
      inner ℂ (ScaledPair.obsClass ν.1 μ ha F)
        ((energyOpCoarse ν μ k - momentumOpCoarse ν μ l k)
          (ScaledPair.obsClass ν.1 μ ha F)) := by
  rw [energy_sub_momentum_eq]
  simp only [add_apply, sub_apply, smul_apply, inner_add_right, inner_sub_right, inner_smul_right]
  simp only [inner_shiftPowerOp_eq hsame ha hν μ l hF]
  simp [fivePointCombination, sub_eq_add_neg]
end Lattice
theorem coarseStepsEveryMesh_holds (hsite : SiteReflectionPair.Conclusion)
    (hsame : ScaledClassesTheorem)
    (hpict : ReflectionPairTheorem)
    (hspec : JointSpectralCalculusTheorem) : CoarseStepsEveryMesh := by
  intro a ha ν hν μ l k hk
  have hc : CoarseOpInequality ν μ l k :=
    ((hsite (unitRepresentative ν.1) μ 1).2.2.1 l k hk).1
  have hle : momentumOpCoarse ν μ l k ≤ energyOpCoarse ν μ k := hc
  have hpos : (energyOpCoarse ν μ k - momentumOpCoarse ν μ l k).IsPositive :=
    (ContinuousLinearMap.le_def _ _).mp hle
  have hfive : FivePointNonneg ν μ l k := fun F hF => by
    rw [fivePointCombination_eq_inner hsame ha hν μ l k hF]
    exact hpos.inner_nonneg_right _
  have hcalc : BoundedFunctionalCalculus (pictureFamily ν μ) (ScaledPair.jointPVM ν.1 μ) :=
    ((hspec _ _ (pictureFamily ν μ)).2.2 _
      (hpict (unitRepresentative ν.1) μ ReflectionPair.site).2.2.2.2.1).2.1
  refine ⟨hc, hfive, fun F hF v _ => ?_,
    ⟨fun F hF => ?_, fun x hx => coarseSpectralBracket_of_ne_top l k x hx⟩,
    iff_of_true hfive hc, fun F hF => fivePointCombination_eq_inner hsame ha hν μ l k hF,
    hpos.isSelfAdjoint, ?_⟩
  · have hO : IsBoundedObservable F := hF.1.1
    exact isAffineInMeasure_of_isBoundedObservable (isBoundedObservable_mul
      (isBoundedObservable_conj (IsBoundedObservable.actOn hO _))
      (IsBoundedObservable.actOn hO _))
  · rw [fivePointCombination_eq_inner hsame ha hν μ l k hF, energy_sub_momentum_eq,
      inner_fiveTerm_eq_integral hcalc]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q =>
      (pullToSpectrum_coarseSpectralBracket l hk q).symm)
  · obtain ⟨f, hf, hd⟩ := (hsame a ha ν hν μ).1.2.1
    have himage : ScaledPair.obsClass ν.1 μ ha '' localHalfSpaceObs a μ =
        Set.range f := by
      ext ψ
      constructor
      · rintro ⟨F, hF, rfl⟩
        exact ⟨⟨F, (mem_halfSpaceLocalAtMesh_iff a μ F).mpr hF⟩, hf _⟩
      · rintro ⟨F, rfl⟩
        exact ⟨F, F.2, (hf F).symm⟩
    rw [himage]
    exact hd
end YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseSteps
