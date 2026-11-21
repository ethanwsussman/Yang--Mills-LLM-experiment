import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.Cumulants.MultilinearityShiftsAndMomentsOfJointCumulants
import YangMills.Construction.InfiniteLattice.RegularConditionalProbabilitiesByIntegrals
import YangMills.Construction.InfiniteLattice.TorusConfigurationsAndMeasuresThroughTheCoveringMapOfACutoff
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfTheFamilyAreLimitsAlongSequences
import YangMills.Construction.LawByMomentsOfTheFlow.HullsInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.LatticeNumberNearTheCyclicFormula
import YangMills.Construction.LawByMomentsOfTheFlow.LawAtLimitPointsProof
import YangMills.Construction.LawByMomentsOfTheFlow.LawInTheComponents
import YangMills.Construction.LawByMomentsOfTheFlow.PointsOfTheLawAtTheHulls
import YangMills.Construction.ParameterData.ScaleSequenceData
import YangMills.Construction.SystemsWithFiveBounds.CanonicalDecompositionAlongStatesProof
import YangMills.Construction.TotalDensitiesGiveASystem.DensitySystemDefs
import YangMills.Construction.TotalDensitiesGiveASystem.EveryComponentIsALimitOfStates
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheCouplingsGiveTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheExpansionFlowIsTheTotalFlow
import YangMills.Construction.TotalDensitiesGiveASystem.TheLawAtEightPointsInAVolumeFirstLimit
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped Topology
namespace YangMills.Construction.TotalDensitySystem
private abbrev E4 : Type := TestFunctions.EuclideanFourSpace
section CyclicFormulaScaling
private theorem inversionMatrix_smul {r : ℝ} (hr : 0 < r) (x : E4) : CyclicFormula.inversionMatrix (r • x) = CyclicFormula.inversionMatrix x := by
  unfold CyclicFormula.inversionMatrix
  by_cases hx : ‖x‖ = 0
  · have h0 : x = 0 := norm_eq_zero.mp hx
    simp [h0]
  · ext i j
    have hn : ‖r • x‖ = r * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, hn, PiLp.smul_apply]
    field_simp
variable {n : ℕ} [NeZero n]
private theorem cycleKernel_smul {r : ℝ} (hr : 0 < r) (σ : Equiv.Perm (Fin n)) (x : Fin n → E4) :
    CyclicFormula.cycleKernel σ (r • x) = ((r ^ 4) ^ n)⁻¹ * CyclicFormula.cycleKernel σ x := by
  unfold CyclicFormula.cycleKernel
  have e1 : ∀ c : Fin n, (Real.pi ^ 2 * ‖(r • x) (σ c) - (r • x) (σ (c + 1))‖ ^ 4)⁻¹ =
      (r ^ 4)⁻¹ * (Real.pi ^ 2 * ‖x (σ c) - x (σ (c + 1))‖ ^ 4)⁻¹ := by
    intro c
    rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, norm_smul, Real.norm_of_nonneg hr.le, mul_pow, mul_inv, mul_inv]
    ring
  have e2 : ∀ c : Fin n, CyclicFormula.inversionMatrix ((r • x) (σ c) - (r • x) (σ (c + 1))) = CyclicFormula.inversionMatrix (x (σ c) - x (σ (c + 1))) := by
    intro c
    rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, inversionMatrix_smul hr]
  simp only [e1, e2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [inv_pow]
  ring
private theorem cyclicMomentFormula_dilate {r : ℝ} (hr : 0 < r) (φ : Fin n → E4 → ℝ) :
    CyclicFormula.cyclicMomentFormula n (fun i x => φ i (r • x)) = CyclicFormula.cyclicMomentFormula n φ := by
  unfold CyclicFormula.cyclicMomentFormula
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  let G : (Fin n → E4) → ℝ := fun z => (∏ i, φ i (z i)) * CyclicFormula.cycleKernel σ z
  have hG : ∀ x : Fin n → E4, (∏ i, φ i (r • x i)) * CyclicFormula.cycleKernel σ x = (r ^ 4) ^ n * G (r • x) := by
    intro x
    have hp : (r ^ 4) ^ n ≠ 0 := by positivity
    show _ = (r ^ 4) ^ n * ((∏ i, φ i ((r • x) i)) * CyclicFormula.cycleKernel σ (r • x))
    rw [cycleKernel_smul hr]
    simp only [Pi.smul_apply]
    field_simp
  have hf : Module.finrank ℝ (Fin n → E4) = 4 * n := by
    rw [Module.finrank_pi_fintype]
    simp [mul_comm]
  calc ∫ x : Fin n → E4, (∏ i, φ i (r • x i)) * CyclicFormula.cycleKernel σ x = ∫ x : Fin n → E4, (r ^ 4) ^ n * G (r • x) :=
        integral_congr_ae (Eventually.of_forall hG)
    _ = (r ^ 4) ^ n * ∫ x : Fin n → E4, G (r • x) := integral_const_mul _ _
    _ = (r ^ 4) ^ n * ((r ^ Module.finrank ℝ (Fin n → E4))⁻¹ • ∫ x : Fin n → E4, G x) := by
        rw [Measure.integral_comp_smul_of_nonneg volume G r (hR := hr.le)]
    _ = ∫ x : Fin n → E4, G x := by
        rw [hf, pow_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
private theorem cyclicMomentFormula_const_mul (c : ℝ) (φ : Fin n → E4 → ℝ) :
    CyclicFormula.cyclicMomentFormula n (fun i x => c * φ i x) = c ^ n * CyclicFormula.cyclicMomentFormula n φ := by
  unfold CyclicFormula.cyclicMomentFormula
  have h : ∀ σ : Equiv.Perm (Fin n), ∫ x : Fin n → E4, (∏ i, c * φ i (x i)) * CyclicFormula.cycleKernel σ x =
      c ^ n * ∫ x : Fin n → E4, (∏ i, φ i (x i)) * CyclicFormula.cycleKernel σ x := by
    intro σ
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  simp only [h, ← Finset.mul_sum]
  ring
end CyclicFormulaScaling
private def toElementaryPlaquette (a : ℝ) (Q : MomentLaw.IntPlaquette) : InfiniteLattice.ElementaryPlaquette a :=
  ⟨TorusLimits.latticePointOfInt a Q.1, Q.2.1.1, Q.2.1.2, Q.2.2⟩
private theorem bijective_toElementaryPlaquette {a : ℝ} (ha : a ≠ 0) : Function.Bijective (toElementaryPlaquette a) := by
  constructor
  · rintro ⟨n, ⟨⟨μ, ν⟩, h⟩⟩ ⟨n', ⟨⟨μ', ν'⟩, h'⟩⟩ e
    simp only [toElementaryPlaquette, InfiniteLattice.ElementaryPlaquette.mk.injEq] at e
    obtain ⟨e1, e2, e3⟩ := e
    subst e2 e3
    have hn : n = n' := by
      funext i
      have h3 := congrFun (congrArg Subtype.val e1) i
      simp only [TorusLimits.latticePointOfInt] at h3
      exact_mod_cast mul_right_cancel₀ ha h3
    subst hn
    rfl
  · intro p
    obtain ⟨n, hn⟩ := p.corner.2
    refine ⟨(n, ⟨(p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩), ?_⟩
    apply InfiniteLattice.ElementaryPlaquette.ext
    · exact Subtype.ext (funext fun i => (hn i).symm)
    · rfl
    · rfl
private theorem center_toElementaryPlaquette (a : ℝ) (Q : MomentLaw.IntPlaquette) (c : Fin 4) :
    (toElementaryPlaquette a Q).center c = a * MomentLaw.intBarycenter Q c := by
  have hb : (toElementaryPlaquette a Q).center c = (Q.1 c : ℝ) * a + (if c = Q.2.1.1 then a / 2 else 0) +
      (if c = Q.2.1.2 then a / 2 else 0) := by
    simp [InfiniteLattice.ElementaryPlaquette.center, toElementaryPlaquette, TorusLimits.latticePointOfInt, Pi.single_apply]
  rw [hb]
  show _ = a * ((Q.1 c : ℝ) + (if c = Q.2.1.1 then 1 / 2 else 0) + (if c = Q.2.1.2 then 1 / 2 else 0))
  split_ifs <;> ring
private theorem rescaled_center {L : ℕ} (hL : L ≠ 0) (K s : ℕ) (φ : E4 → ℝ) (Q : MomentLaw.IntPlaquette) :
    DensitySupply.rescaled L K s φ (toElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) Q).center = MomentLaw.scaledWeight L s φ Q := by
  unfold DensitySupply.rescaled MomentLaw.scaledWeight
  refine congrArg φ ?_
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have hK : (L : ℝ) ^ K ≠ 0 := pow_ne_zero _ hL'
  have hS : (L : ℝ) ^ s ≠ 0 := pow_ne_zero _ hL'
  have ha : PeriodicLattice.meshSize L (K : ℤ) = ((L : ℝ) ^ K)⁻¹ := by
    simp [PeriodicLattice.meshSize, zpow_neg]
  ext c
  simp only [center_toElementaryPlaquette, ha, PiLp.smul_apply, smul_eq_mul]
  field_simp
private theorem smearedEnergy_eq_sum {a : ℝ} (ha : a ≠ 0) (f : InfiniteLattice.AmbientSpace → ℝ) {E : Finset MomentLaw.IntPlaquette}
    (hE : ∀ Q, f (toElementaryPlaquette a Q).center ≠ 0 → Q ∈ E) (U : InfiniteLattice.GaugeField a) :
    InfiniteLattice.smearedEnergy f U =
      ∑ Q ∈ E, InfiniteLattice.faceEnergy U (toElementaryPlaquette a Q) * f (toElementaryPlaquette a Q).center := by
  unfold InfiniteLattice.smearedEnergy
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (bijective_toElementaryPlaquette ha))]
  simp only [Equiv.ofBijective_apply]
  rw [finsum_eq_sum_of_support_subset]
  · exact Finset.sum_congr rfl fun P _ => by rw [smul_eq_mul]
  · intro P hP
    have hP' : InfiniteLattice.faceEnergy U (toElementaryPlaquette a P) • f (toElementaryPlaquette a P).center ≠ 0 := hP
    rw [smul_eq_mul] at hP'
    exact Finset.mem_coe.mpr (hE P (right_ne_zero_of_mul hP'))
private theorem abs_faceEnergy_le {a : ℝ} (U : InfiniteLattice.GaugeField a) (p : InfiniteLattice.ElementaryPlaquette a) :
    |InfiniteLattice.faceEnergy U p| ≤ 2 := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.abs_faceEnergy_le <;> assumption
private theorem cutoffEnergy_isBounded {L K : ℕ} (hsp : PeriodicLattice.meshSize L (K : ℤ) ≠ 0) (f : InfiniteLattice.AmbientSpace → ℝ)
    {E : Finset MomentLaw.IntPlaquette} (hE : ∀ Q, f (toElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) Q).center ≠ 0 → Q ∈ E) :
    Probability.IsBoundedRealRV
      (fun U : InfiniteLattice.RefinedGaugeField L K => InfiniteLattice.cutoffSmearedEnergyRe f U) := by
  have e : (fun U : InfiniteLattice.RefinedGaugeField L K => InfiniteLattice.cutoffSmearedEnergyRe f U) =
      fun U : InfiniteLattice.RefinedGaugeField L K =>
      ∑ Q ∈ E, InfiniteLattice.faceEnergy U (toElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) Q) *
        f (toElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) Q).center :=
    funext fun U => (InfiniteLattice.cutoffSmearedEnergyRe_eq_smearedEnergy f U).trans (smearedEnergy_eq_sum hsp f hE U)
  rw [e]
  refine ⟨?_, ∑ Q ∈ E, 2 * |f (toElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) Q).center|, fun U => ?_⟩
  · refine (continuous_finsetSum _ fun Q _ => ?_).measurable
    exact (InfiniteLattice.continuous_faceEnergy _).mul continuous_const
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun Q _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_faceEnergy_le U _) (abs_nonneg _)
private theorem cutoffEnergy_const_mul {L K : ℕ} (hsp : PeriodicLattice.meshSize L (K : ℤ) ≠ 0) (c : ℝ) (f : InfiniteLattice.AmbientSpace → ℝ)
    {E : Finset MomentLaw.IntPlaquette} (hE : ∀ Q, f (toElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) Q).center ≠ 0 → Q ∈ E)
    (U : InfiniteLattice.RefinedGaugeField L K) :
    InfiniteLattice.cutoffSmearedEnergyRe (fun x => c * f x) U = c * InfiniteLattice.cutoffSmearedEnergyRe f U := by
  have hE' : ∀ Q, (fun x => c * f x) (toElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) Q).center ≠ 0 → Q ∈ E :=
    fun Q h => hE Q (right_ne_zero_of_mul h)
  rw [InfiniteLattice.cutoffSmearedEnergyRe_eq_smearedEnergy, InfiniteLattice.cutoffSmearedEnergyRe_eq_smearedEnergy,
    smearedEnergy_eq_sum hsp _ hE' U, smearedEnergy_eq_sum hsp _ hE U, Finset.mul_sum]
  exact Finset.sum_congr rfl fun Q _ => by ring
private theorem mixedCumulant_smul (hCum : Cumulants.MomentCumulantRelations.Holds) {Ω : Type} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {n : ℕ} (hn : 1 ≤ n) (X : Fin n → Ω → ℝ)
    (hX : ∀ l, Probability.IsBoundedRealRV (X l)) (t : Fin n → ℝ) :
    Cumulants.mixedCumulant ν (fun l ω => t l * X l ω) = ((∏ l, t l : ℝ) : ℂ) * Cumulants.mixedCumulant ν X := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := (hCum Ω ν).1 (Fin n) X n (fun l p => if p = l then t l else 0) hX hn
  have e : (fun (l : Fin n) (ω : Ω) => ∑ p, (if p = l then t l else 0) * X p ω) = fun l ω => t l * X l ω := by
    funext l ω
    simp
  rw [e] at h
  rw [h, Finset.sum_eq_single (id : Fin n → Fin n)]
  · simp
  · intro r _ hr
    obtain ⟨l, hl⟩ : ∃ l, r l ≠ l := by
      by_contra hc
      push Not at hc
      exact hr (funext hc)
    have h0 : (∏ l, (if r l = l then t l else 0)) = 0 := Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl])
    simp only [h0]
    simp
  · intro hc
    exact absurd (Finset.mem_univ _) hc
private theorem intBarycenter_bounds (P : MomentLaw.IntPlaquette) (i : Fin 4) :
    (P.1 i : ℝ) ≤ MomentLaw.intBarycenter P i ∧ MomentLaw.intBarycenter P i ≤ (P.1 i : ℝ) + 1 := by
  show _ ≤ (P.1 i : ℝ) + (if i = P.2.1.1 then 1 / 2 else 0) + (if i = P.2.1.2 then 1 / 2 else 0) ∧
    (P.1 i : ℝ) + (if i = P.2.1.1 then 1 / 2 else 0) + (if i = P.2.1.2 then 1 / 2 else 0) ≤ _
  split_ifs <;> constructor <;> linarith
private theorem mem_plaquetteBox {L s : ℕ} (hL : 0 < L) {φ : E4 → ℝ} {R : ℝ}
    (hR : ∀ x ∈ tsupport φ, ∀ a, |x a| ≤ R) {Q : MomentLaw.IntPlaquette} (hQ : MomentLaw.scaledWeight L s φ Q ≠ 0) :
    Q ∈ MomentLaw.plaquetteBox (⌈R * (L : ℝ) ^ s⌉₊ + 2) := by
  have hS : (0 : ℝ) < (L : ℝ) ^ s := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    positivity
  have h := hR _ (subset_tsupport _ hQ)
  have hc : R * (L : ℝ) ^ s ≤ (⌈R * (L : ℝ) ^ s⌉₊ : ℝ) := Nat.le_ceil _
  have hb : ∀ a, |MomentLaw.intBarycenter Q a| ≤ (⌈R * (L : ℝ) ^ s⌉₊ : ℝ) := fun a => by
    have h' : |((L : ℝ) ^ s)⁻¹ * MomentLaw.intBarycenter Q a| ≤ R := h a
    rw [abs_mul, abs_of_pos (inv_pos.mpr hS), inv_mul_le_iff₀ hS] at h'
    rw [mul_comm] at h'
    exact h'.trans hc
  unfold MomentLaw.plaquetteBox
  refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun a => Finset.mem_Icc.mpr ?_, Finset.mem_univ _⟩
  obtain ⟨e1, e2⟩ := intBarycenter_bounds Q a
  obtain ⟨f1, f2⟩ := abs_le.mp (hb a)
  constructor
  · have : -((⌈R * (L : ℝ) ^ s⌉₊ : ℝ) + 2) ≤ (Q.1 a : ℝ) := by linarith
    exact_mod_cast this
  · have : (Q.1 a : ℝ) ≤ (⌈R * (L : ℝ) ^ s⌉₊ : ℝ) + 2 := by linarith
    exact_mod_cast this
private theorem meshSize_ne_zero {L : ℕ} (hL : 0 < L) (K : ℕ) : PeriodicLattice.meshSize L (K : ℤ) ≠ 0 := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  exact zpow_ne_zero _ hL'
private theorem exists_finset_of_support {L K s : ℕ} (hL : 0 < L) {φ : E4 → ℝ} {R : ℝ}
    (hR : ∀ x ∈ tsupport φ, ∀ a, |x a| ≤ R) :
    ∃ E : Finset MomentLaw.IntPlaquette, ∀ Q, DensitySupply.rescaled L K s φ (toElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) Q).center ≠ 0 → Q ∈ E := by
  refine ⟨MomentLaw.plaquetteBox (⌈R * (L : ℝ) ^ s⌉₊ + 2), fun Q hQ => ?_⟩
  rw [rescaled_center hL.ne'] at hQ
  exact mem_plaquetteBox hL hR hQ
private lemma rpow_neg_tenth_nonneg (x : ℝ) : 0 ≤ x ^ (-(1 / 10) : ℝ) := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.rpow_def_of_neg h]
    refine mul_nonneg (Real.exp_nonneg _) (Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_) <;> nlinarith [Real.pi_pos]
  · subst h
    exact Real.rpow_nonneg le_rfl _
  · exact (Real.rpow_pos_of_pos h _).le
private lemma abs_sub_le_supDist (x y : E4) (a : Fin 4) : |x a - y a| ≤ MomentLaw.supDist x y :=
  le_ciSup (f := fun a => |x a - y a|) (Set.finite_range _).bddAbove a
private lemma dist_ofLp_le_supDist (x y : E4) : dist (WithLp.ofLp x) (WithLp.ofLp y) ≤ MomentLaw.supDist x y := by
  have h0 : 0 ≤ MomentLaw.supDist x y := (abs_nonneg _).trans (abs_sub_le_supDist x y 0)
  refine (dist_pi_le_iff h0).2 fun a => ?_
  rw [Real.dist_eq]
  exact abs_sub_le_supDist x y a
private def levelDataAt {n : ℕ} (K s m : ℕ) (φ : Fin n → E4 → ℝ) : LevelTestFunctions.LevelData n where
  fn := φ
  windowLevel := K
  scaleLevel := s
  sideExponent := m
  center := fun _ => 0
private theorem circleRep_eq {c d b : ℝ} {t : ℤ} (hc : 0 < c) (hd : d = b + c * t) (hb : 2 * |b| < c) : LevelTestFunctions.circleRep c d = b := by apply _root_.YangMills.SharedProofs.p85907 <;> assumption
private theorem zmod_val_intCast_real {N : ℕ} [NeZero N] (z : ℤ) :
    (((z : ZMod N).val : ℕ) : ℝ) = (z : ℝ) - N * ((z / (N : ℤ) : ℤ) : ℝ) := by
  have h : (((z : ZMod N).val : ℕ) : ℤ) = z - N * (z / (N : ℤ)) := by
    rw [ZMod.val_intCast, Int.emod_def]
  exact_mod_cast congrArg (fun k : ℤ => (k : ℝ)) h
private theorem supAdmissible_of_test {n : ℕ} {L K s m : ℕ} (hL : 1 < L) {R d : ℝ} {φ : Fin n → E4 → ℝ} (hφ : MomentLaw.IsSupTestFamily R d φ)
    (hs : s ≤ K) (hR : 0 ≤ R) (hm : 4 * (R + 1) ≤ (L : ℝ) ^ m) (hlive : ∀ i, ∃ Q, MomentLaw.scaledWeight L s (φ i) Q ≠ 0) :
    (levelDataAt K s m φ).SupAdmissible L R d := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL.le
  have hSp : (0 : ℝ) < (L : ℝ) ^ s := by positivity
  have hKp : (0 : ℝ) < (L : ℝ) ^ K := by positivity
  have hsK : (L : ℝ) ^ s ≤ (L : ℝ) ^ K := pow_le_pow_right₀ hL1 hs
  refine ⟨hφ, hs, ?_, ⟨0, fun a => ?_⟩, fun i => ?_⟩
  · show 2 * R * (L : ℝ) ^ s ≤ ((2 * L ^ m : ℕ) : ℝ) / 4 * (L : ℝ) ^ K
    push_cast
    have h1 : 2 * R ≤ 2 * (L : ℝ) ^ m / 4 := by linarith
    calc 2 * R * (L : ℝ) ^ s ≤ 2 * R * (L : ℝ) ^ K := mul_le_mul_of_nonneg_left hsK (by positivity)
      _ ≤ 2 * (L : ℝ) ^ m / 4 * (L : ℝ) ^ K := mul_le_mul_of_nonneg_right h1 hKp.le
  · simp [levelDataAt]
  · obtain ⟨Q, hQ⟩ := hlive i
    have hN0 : (levelDataAt K s m φ).period L * L ^ (levelDataAt K s m φ).windowLevel ≠ 0 := by
      show 2 * L ^ m * L ^ K ≠ 0
      positivity
    have : NeZero ((levelDataAt K s m φ).period L * L ^ (levelDataAt K s m φ).windowLevel) := ⟨hN0⟩
    refine ⟨⟨(TorusFields.siteOfInt Q.1, Q.2.1.1, Q.2.1.2), Q.2.2⟩, ?_⟩
    have hw : (levelDataAt K s m φ).testWeight L i ((levelDataAt K s m φ).period L * L ^ (levelDataAt K s m φ).windowLevel)
        (TorusFields.siteOfInt Q.1, Q.2.1.1, Q.2.1.2) = MomentLaw.scaledWeight L s (φ i) Q := by
      unfold LevelTestFunctions.LevelData.testWeight MomentLaw.scaledWeight
      refine congrArg (φ i) ?_
      ext a
      have htop : (((levelDataAt K s m φ).period L : ℕ) : ℝ) = 2 * (L : ℝ) ^ m := by
        show ((2 * L ^ m : ℕ) : ℝ) = _
        push_cast
        ring
      have hNr : (((levelDataAt K s m φ).period L * L ^ (levelDataAt K s m φ).windowLevel : ℕ) : ℝ) = 2 * (L : ℝ) ^ m * (L : ℝ) ^ K := by
        show ((2 * L ^ m * L ^ K : ℕ) : ℝ) = _
        push_cast
        ring
      set N : ℕ := (levelDataAt K s m φ).period L * L ^ (levelDataAt K s m φ).windowLevel with hNdef
      have ebar : LevelTestFunctions.barycenterCoord ((TorusFields.siteOfInt Q.1, Q.2.1.1, Q.2.1.2) : TorusFields.TorusPlaquette N) a =
          MomentLaw.intBarycenter Q a - N * ((Q.1 a / (N : ℤ) : ℤ) : ℝ) := by
        have e1 : LevelTestFunctions.barycenterCoord ((TorusFields.siteOfInt Q.1, Q.2.1.1, Q.2.1.2) : TorusFields.TorusPlaquette N) a =
            (((TorusFields.siteOfInt Q.1 : TorusFields.TorusSite N) a).val : ℝ) + (if a = Q.2.1.1 then 1 / 2 else 0) + (if a = Q.2.1.2 then 1 / 2 else 0) := rfl
        have e2 : (((TorusFields.siteOfInt Q.1 : TorusFields.TorusSite N) a).val : ℝ) = (Q.1 a : ℝ) - N * ((Q.1 a / (N : ℤ) : ℤ) : ℝ) :=
          zmod_val_intCast_real _
        have e3 : MomentLaw.intBarycenter Q a =
            (Q.1 a : ℝ) + (if a = Q.2.1.1 then 1 / 2 else 0) + (if a = Q.2.1.2 then 1 / 2 else 0) := rfl
        rw [e1, e2, e3]
        ring
      have hbd : |MomentLaw.intBarycenter Q a / (L : ℝ) ^ K| ≤ R := by
        have h1 : |(((L : ℝ) ^ s)⁻¹ • MomentLaw.intBarycenter Q) a| ≤ R := hφ.abs_coord_le i _ (subset_tsupport _ hQ) a
        have e : (((L : ℝ) ^ s)⁻¹ • MomentLaw.intBarycenter Q) a = MomentLaw.intBarycenter Q a / (L : ℝ) ^ s := by
          simp [div_eq_inv_mul]
        rw [e] at h1
        have e5 : MomentLaw.intBarycenter Q a / (L : ℝ) ^ K =
            MomentLaw.intBarycenter Q a / (L : ℝ) ^ s * ((L : ℝ) ^ s / (L : ℝ) ^ K) := by
          field_simp
        rw [e5, abs_mul, abs_of_pos (div_pos hSp hKp)]
        have h6 : (L : ℝ) ^ s / (L : ℝ) ^ K ≤ 1 := (div_le_one hKp).mpr hsK
        calc _ ≤ |MomentLaw.intBarycenter Q a / (L : ℝ) ^ s| * 1 := mul_le_mul_of_nonneg_left h6 (abs_nonneg _)
          _ ≤ R := by linarith
      have hcirc : LevelTestFunctions.circleRep (((levelDataAt K s m φ).period L : ℕ) : ℝ)
          (LevelTestFunctions.barycenterCoord ((TorusFields.siteOfInt Q.1, Q.2.1.1, Q.2.1.2) : TorusFields.TorusPlaquette N) a / (L : ℝ) ^ K - 0) =
          MomentLaw.intBarycenter Q a / (L : ℝ) ^ K := by
        refine circleRep_eq (t := -(Q.1 a / (N : ℤ))) ?_ ?_ ?_
        · rw [htop]
          positivity
        · rw [ebar, hNr, htop]
          push_cast
          field_simp
          ring
        · rw [htop]
          linarith
      show (L : ℝ) ^ K / (L : ℝ) ^ s * LevelTestFunctions.circleRep (((levelDataAt K s m φ).period L : ℕ) : ℝ)
          (LevelTestFunctions.barycenterCoord ((TorusFields.siteOfInt Q.1, Q.2.1.1, Q.2.1.2) : TorusFields.TorusPlaquette N) a / (L : ℝ) ^ K - 0) =
          ((L : ℝ) ^ s)⁻¹ * MomentLaw.intBarycenter Q a
      rw [hcirc]
      field_simp
    show (levelDataAt K s m φ).testWeight L i _ (TorusFields.siteOfInt Q.1, Q.2.1.1, Q.2.1.2) ≠ 0
    rw [hw]
    exact hQ
private def SatisfiesMomentBound (Λ : MomentLaw.MomentParameters) (C : ℝ) {K : ℕ} (β : ℝ)
    (ρ : Measure (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K)) : Prop :=
  ∀ S : MomentLaw.MomentPoint Λ, S.data.windowLevel = K → S.β = β →
    ‖(S.scaleCoupling : ℂ) ^ Λ.k * S.stateUrsell ρ - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤ C * S.scaleCoupling ^ (-(1 / 10) : ℝ)
private theorem vanishing_of_dead (hCum : Cumulants.MomentCumulantRelations.Holds) {L K s n : ℕ} [NeZero n] (hL : 0 < L)
    {R : ℝ} {φ : Fin n → E4 → ℝ} (hR : ∀ i, ∀ x ∈ tsupport (φ i), ∀ a, |x a| ≤ R) {i₀ : Fin n}
    (hi : ∀ Q, MomentLaw.scaledWeight L s (φ i₀) Q = 0) {ν : Measure (InfiniteLattice.RefinedGaugeField L K)}
    (hν : IsProbabilityMeasure ν) (b : ℕ) :
    InfiniteLattice.ursellFunctionOfFamily (L := L) (K := K) ν (fun i => DensitySupply.rescaled L K s (φ i)) = 0 ∧
      MomentLaw.latticeCycleSum L s b φ = 0 := by
  classical
  have hsp := meshSize_ne_zero hL K
  have hk1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  let X : Fin n → InfiniteLattice.RefinedGaugeField L K → ℝ :=
    fun j U => InfiniteLattice.cutoffSmearedEnergyRe (DensitySupply.rescaled L K s (φ j)) U
  have hX : ∀ l, Probability.IsBoundedRealRV (X l) := fun l => by
    obtain ⟨E, hE⟩ := exists_finset_of_support (K := K) (s := s) hL (hR l)
    exact cutoffEnergy_isBounded hsp _ hE
  have h0 : ∀ U, X i₀ U = 0 := fun U => by
    have hE : ∀ Q, DensitySupply.rescaled L K s (φ i₀) (toElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) Q).center ≠ 0 → Q ∈ (∅ : Finset MomentLaw.IntPlaquette) :=
      fun Q hQ => by
        rw [rescaled_center hL.ne', hi] at hQ
        exact absurd rfl hQ
    show InfiniteLattice.cutoffSmearedEnergyRe _ U = 0
    rw [InfiniteLattice.cutoffSmearedEnergyRe_eq_smearedEnergy, smearedEnergy_eq_sum hsp _ hE U]
    simp
  let t : Fin n → ℝ := fun l => if l = i₀ then 0 else 1
  have e : (fun l U => t l * X l U) = X := by
    funext l U
    by_cases h : l = i₀
    · subst h
      simp [t, h0]
    · simp [t, h]
  have hs := mixedCumulant_smul hCum ν hk1 X hX t
  rw [e] at hs
  have hp : (∏ l, t l) = 0 := Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [t])
  rw [hp] at hs
  refine ⟨?_, ?_⟩
  · have h1 : InfiniteLattice.ursellFunctionOfFamily (L := L) (K := K) ν (fun i => DensitySupply.rescaled L K s (φ i)) =
      Cumulants.mixedCumulant ν X := rfl
    rw [h1, hs]
    simp
  · unfold MomentLaw.latticeCycleSum
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun σ _ => Finset.sum_eq_zero fun p _ => ?_)
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) (hi _), zero_mul]
private theorem moment_bound_of_state (hCum : Cumulants.MomentCumulantRelations.Holds) {T : RenormalizationStepParameters.ParameterAssignment} {Kr : WeightedResponses.ResponseParameters}
    {y g : ℝ} (hL : 1 < T.side) (hpts : DensitySupply.MomentPointsExist T Kr y) (hg : 0 < g) (hyg : y ≤ (g ^ 2)⁻¹) {n : ℕ} [NeZero n] (h2 : 2 ≤ n)
    (h8 : n ≤ 8) {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) {C : ℝ} (hC : 0 ≤ C) {K s : ℕ} (hs : s ≤ K) {β : ℝ}
    (hβ : WeightedResponses.couplingWindowTop (T.stepParameters y) g ≤ β)
    (hp : WeightedResponses.IsFirstPassage (T.stepParameters y) (WeightedResponses.couplingWindowTop (T.stepParameters y) g) β K)
    {φ : Fin n → E4 → ℝ} (hφ : MomentLaw.IsSupTestFamily R d φ) {ρ : Measure (InfiniteLattice.RefinedGaugeField T.side K)}
    (h1 : IsProbabilityMeasure ρ) (hρ : SatisfiesMomentBound ⟨T, Kr, y, g, n, R, d⟩ C β ρ) :
    ‖((DensitySupply.flowSequence T y β s : ℝ) : ℂ) ^ n * InfiniteLattice.ursellFunctionOfFamily (L := T.side) (K := K) ρ (fun i => DensitySupply.rescaled T.side K s (φ i)) -
        ((MomentLaw.latticeCycleSum T.side s (⌈R * (T.side : ℝ) ^ s⌉₊ + 2) φ : ℝ) : ℂ)‖ ≤ C * DensitySupply.flowSequence T y β s ^ (-(1 / 10) : ℝ) := by
  classical
  have hL0 : 0 < T.side := by omega
  by_cases hdead : ∃ i, ∀ Q, MomentLaw.scaledWeight T.side s (φ i) Q = 0
  · obtain ⟨i₀, hi⟩ := hdead
    obtain ⟨e1, e2⟩ := vanishing_of_dead hCum hL0 hφ.abs_coord_le hi h1 (⌈R * (T.side : ℝ) ^ s⌉₊ + 2)
    rw [e1, e2]
    simpa using mul_nonneg hC (rpow_neg_tenth_nonneg _)
  · push Not at hdead
    have hL1 : (1 : ℝ) < (T.side : ℝ) := by exact_mod_cast hL
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (max (4 * (R + 1)) ((T.side : ℝ) * T.n₀)) hL1
    have hpage := supAdmissible_of_test (K := K) (m := m) hL hφ hs hR ((le_max_left _ _).trans hm.le) hdead
    have hside : (T.stepParameters y).side * (T.stepParameters y).n₀ ≤ (levelDataAt K s m φ).period (T.stepParameters y).side := by
      have h1 : (T.side : ℝ) * T.n₀ ≤ (T.side : ℝ) ^ m := (le_max_right _ _).trans hm.le
      have h1' : T.side * T.n₀ ≤ T.side ^ m := by exact_mod_cast h1
      show T.side * T.n₀ ≤ 2 * T.side ^ m
      omega
    obtain ⟨S, hP, hSβ⟩ := hpts g hg hyg n h2 h8 R d hd (levelDataAt K s m φ) β hpage hside hβ hp
    have hb := hρ S (congrArg LevelTestFunctions.LevelData.windowLevel hP) hSβ
    have hSs : S.data.scaleLevel = s := congrArg LevelTestFunctions.LevelData.scaleLevel hP
    have hSK : S.data.windowLevel = K := congrArg LevelTestFunctions.LevelData.windowLevel hP
    have hSφ : S.data.fn = φ := congrArg LevelTestFunctions.LevelData.fn hP
    have hSx : S.data.center = fun _ => 0 := congrArg LevelTestFunctions.LevelData.center hP
    have hxs : S.scaleCoupling = DensitySupply.flowSequence T y β s := by
      show (TorusLumps.couplingFlow _ S.β S.data.scaleLevel).1 = (TorusLumps.couplingFlow _ β s).1
      rw [hSβ, hSs]
    have hgam : S.latticeCycleSumAt S.data.scaleLevel = MomentLaw.latticeCycleSum T.side s (⌈R * (T.side : ℝ) ^ s⌉₊ + 2) φ := by
      show MomentLaw.latticeCycleSum T.side S.data.scaleLevel (⌈R * (T.side : ℝ) ^ S.data.scaleLevel⌉₊ + 2) S.data.fn = _
      rw [hSs, hSφ]
    have hbare : ∀ i, S.rescaledTestFunction i = DensitySupply.rescaled T.side K s (φ i) := by
      intro i
      funext x
      show S.data.fn i (WithLp.toLp 2 fun a => (T.side : ℝ) ^ S.data.windowLevel / (T.side : ℝ) ^ S.data.scaleLevel * (x a - S.data.center a)) = _
      rw [hSφ, hSK, hSs, hSx]
      simp [DensitySupply.rescaled]
    have hcum : S.stateUrsell ρ = InfiniteLattice.ursellFunctionOfFamily (L := T.side) (K := K) ρ (fun i => DensitySupply.rescaled T.side K s (φ i)) := by
      show InfiniteLattice.ursellFunctionOfFamily ρ (fun i => S.rescaledTestFunction i) = _
      simp only [hbare]
    rw [hxs, hgam, hcum] at hb
    exact hb
private def scaledFamily {n : ℕ} (c r : ℝ) (f : Fin n → (Fin 4 → ℝ) → ℝ) : Fin n → E4 → ℝ :=
  fun i x => c * f i (r • WithLp.ofLp x)
private theorem continuous_smul_ofLp (r : ℝ) : Continuous fun x : E4 => r • WithLp.ofLp x := by
  fun_prop
private theorem tsupport_scaledFamily {n : ℕ} {c r : ℝ} {f : Fin n → (Fin 4 → ℝ) → ℝ} {i : Fin n} {x : E4}
    (hx : x ∈ tsupport (scaledFamily c r f i)) : r • WithLp.ofLp x ∈ tsupport (f i) := by
  have hcl : IsClosed ((fun x : E4 => r • WithLp.ofLp x) ⁻¹' tsupport (f i)) :=
    (isClosed_tsupport _).preimage (continuous_smul_ofLp r)
  refine closure_minimal (fun y hy => ?_) hcl hx
  exact subset_tsupport _ (right_ne_zero_of_mul hy)
private theorem exists_scaling_constants {n : ℕ} [NeZero n] (X : TestSpaces.SepTupleOfCard n) {L : ℝ} (hL : 1 ≤ L) :
    ∃ c R d : ℝ, 0 < c ∧ 0 ≤ R ∧ 0 < d ∧ ∀ r : ℝ, 1 / L ≤ r → r ≤ 1 → MomentLaw.IsSupTestFamily R d (scaledFamily c r X.1) := by
  classical
  have hcpt : ∀ k, HasCompactSupport (X.1 k) := fun k => (X.2.1 k).2.1
  have hcd : ∀ k, ContDiff ℝ 1 (X.1 k) := fun k => (X.2.1 k).1.of_le (by simp)
  have hdis : ∀ k l, k ≠ l → Disjoint (tsupport (X.1 k)) (tsupport (X.1 l)) := fun k l h => X.2.2 h
  choose Lp hLp using fun k => ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) (hcpt k) (hcd k) one_ne_zero
  choose M hM using fun k => (hcpt k).exists_bound_of_continuous (hcd k).continuous
  let W : ℝ := 1 + ∑ k, ((Lp k : ℝ) + |M k|)
  have hterm : ∀ k, 0 ≤ (Lp k : ℝ) + |M k| := fun k => add_nonneg (NNReal.coe_nonneg _) (abs_nonneg _)
  have hW1 : 1 ≤ W := by
    have : 0 ≤ ∑ k, ((Lp k : ℝ) + |M k|) := Finset.sum_nonneg fun k _ => hterm k
    show 1 ≤ 1 + _
    linarith
  have hW0 : 0 < W := by linarith
  have hWk : ∀ k, (Lp k : ℝ) + |M k| ≤ W := fun k => by
    have : (Lp k : ℝ) + |M k| ≤ ∑ k, ((Lp k : ℝ) + |M k|) :=
      Finset.single_le_sum (f := fun k => (Lp k : ℝ) + |M k|) (fun k _ => hterm k) (Finset.mem_univ k)
    show _ ≤ 1 + _
    linarith
  obtain ⟨r₀, hr₀⟩ := (isCompact_iUnion fun k => hcpt k).isBounded.subset_closedBall (0 : Fin 4 → ℝ)
  have hsupp : ∀ k, ∀ x ∈ tsupport (X.1 k), ∀ a, |x a| ≤ max r₀ 0 := fun k x hx a => by
    have h1 : x ∈ Metric.closedBall (0 : Fin 4 → ℝ) r₀ := hr₀ (Set.mem_iUnion.2 ⟨k, hx⟩)
    have h2 : ‖x‖ ≤ r₀ := by simpa using h1
    have h3 : ‖x a‖ ≤ ‖x‖ := norm_le_pi_norm x a
    rw [Real.norm_eq_abs] at h3
    exact (h3.trans h2).trans (le_max_left _ _)
  have hgap : ∀ p : Fin n × Fin n, ∃ r : ℝ, 0 < r ∧ (p.1 ≠ p.2 → ∀ x ∈ tsupport (X.1 p.1), ∀ y ∈ tsupport (X.1 p.2), r ≤ dist x y) := by
    rintro ⟨k, l⟩
    by_cases h : k = l
    · exact ⟨1, one_pos, fun h' => absurd h h'⟩
    · obtain ⟨r, hr, hh⟩ := Metric.exists_pos_forall_lt_edist (hcpt k) (isClosed_tsupport _) (hdis k l h)
      refine ⟨r, by exact_mod_cast hr, fun _ x hx y hy => ?_⟩
      have h1 := hh x hx y hy
      rw [edist_dist] at h1
      have h2 : ENNReal.ofReal (r : ℝ) < ENNReal.ofReal (dist x y) := by simpa using h1
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 h2).le
  choose rr hrr using hgap
  obtain ⟨p₀, -, hp₀⟩ := (Finset.univ : Finset (Fin n × Fin n)).exists_min_image rr ⟨(0, 0), Finset.mem_univ _⟩
  refine ⟨W⁻¹, max r₀ 0 * L, rr p₀, inv_pos.2 hW0, mul_nonneg (le_max_right _ _) (by linarith), (hrr p₀).1, fun r hr1 hr2 => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hc1 : W⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  refine ⟨fun i x => ?_, fun i x y => ?_, fun i => ?_, fun i x hx a => ?_, fun i j hij x hx y hy => ?_⟩
  · show |W⁻¹ * X.1 i (r • WithLp.ofLp x)| ≤ 1
    have h1 : |X.1 i (r • WithLp.ofLp x)| ≤ |M i| := by
      have := hM i (r • WithLp.ofLp x)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    have h2 : |M i| ≤ W := le_trans (by linarith [NNReal.coe_nonneg (Lp i)]) (hWk i)
    rw [abs_mul, abs_of_pos (inv_pos.2 hW0), inv_mul_le_iff₀ hW0, mul_one]
    exact h1.trans h2
  · show |W⁻¹ * X.1 i (r • WithLp.ofLp x) - W⁻¹ * X.1 i (r • WithLp.ofLp y)| ≤ MomentLaw.supDist x y
    have h0 : 0 ≤ MomentLaw.supDist x y := (abs_nonneg _).trans (abs_sub_le_supDist x y 0)
    have h1 := (hLp i).dist_le_mul (r • WithLp.ofLp x) (r • WithLp.ofLp y)
    rw [dist_smul₀, Real.norm_of_nonneg hr0.le, Real.dist_eq] at h1
    have h2 : r * dist (WithLp.ofLp x) (WithLp.ofLp y) ≤ MomentLaw.supDist x y :=
      (mul_le_of_le_one_left dist_nonneg hr2).trans (dist_ofLp_le_supDist x y)
    have h3 : (Lp i : ℝ) ≤ W := le_trans (by linarith [abs_nonneg (M i)]) (hWk i)
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hW0), inv_mul_le_iff₀ hW0]
    calc _ ≤ (Lp i : ℝ) * (r * dist (WithLp.ofLp x) (WithLp.ofLp y)) := h1
      _ ≤ W * MomentLaw.supDist x y := mul_le_mul h3 h2 (by positivity) hW0.le
  · have hne : r ≠ 0 := hr0.ne'
    have h1 : HasCompactSupport (fun z : Fin 4 → ℝ => X.1 i (r • z)) :=
      (hcpt i).comp_homeomorph (Homeomorph.smulOfNeZero r hne)
    have h2 : HasCompactSupport (fun x : E4 => X.1 i (r • WithLp.ofLp x)) :=
      h1.comp_homeomorph (EuclideanSpace.equiv (Fin 4) ℝ).toHomeomorph
    exact h2.mul_left
  · have h1 := hsupp i _ (tsupport_scaledFamily hx) a
    have h2 : |r * x a| ≤ max r₀ 0 := h1
    rw [abs_mul, abs_of_pos hr0] at h2
    have hm0 : 0 ≤ max r₀ 0 := le_max_right _ _
    have hL0 : 0 < L := by linarith
    have hrL : 1 ≤ r * L := by
      rw [div_le_iff₀ hL0] at hr1
      exact hr1
    calc |x a| ≤ (r * L) * |x a| := le_mul_of_one_le_left (abs_nonneg _) hrL
      _ = (r * |x a|) * L := by ring
      _ ≤ max r₀ 0 * L := mul_le_mul_of_nonneg_right h2 hL0.le
  · have h1 := (hrr (i, j)).2 hij _ (tsupport_scaledFamily hx) _ (tsupport_scaledFamily hy)
    rw [dist_smul₀, Real.norm_of_nonneg hr0.le] at h1
    calc rr p₀ ≤ rr (i, j) := hp₀ _ (Finset.mem_univ _)
      _ ≤ r * dist (WithLp.ofLp x) (WithLp.ofLp y) := h1
      _ ≤ dist (WithLp.ofLp x) (WithLp.ofLp y) := mul_le_of_le_one_left dist_nonneg hr2
      _ ≤ MomentLaw.supDist x y := dist_ofLp_le_supDist x y
private theorem rescaled_scaledFamily {n : ℕ} {L K s m i : ℕ} (hL : 0 < L) (hK : K = s + m) (c : ℝ) (f : Fin n → (Fin 4 → ℝ) → ℝ) (k : Fin n) :
    DensitySupply.rescaled L K s (scaledFamily c ((2 : ℝ) ^ i / (L : ℝ) ^ m) f k) = fun x => c * TotalDensities.dyadicRescale i f k x := by
  funext x
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hm : (L : ℝ) ^ m ≠ 0 := pow_ne_zero _ hL'
  have hs : (L : ℝ) ^ s ≠ 0 := pow_ne_zero _ hL'
  show c * f k (((2 : ℝ) ^ i / (L : ℝ) ^ m) • fun a => (L : ℝ) ^ K / (L : ℝ) ^ s * x a) = c * f k ((2 : ℝ) ^ i • x)
  congr 2
  funext a
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hK, pow_add]
  field_simp
private theorem smearedEnergyCumulant_eq_ursell {L K n : ℕ} (ν : Measure (InfiniteLattice.RefinedGaugeField L K)) (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    InfiniteLattice.smearedEnergyCumulant ν f = InfiniteLattice.ursellFunctionOfFamily (L := L) (K := K) ν f := by
  unfold InfiniteLattice.smearedEnergyCumulant InfiniteLattice.ursellFunctionOfFamily
  congr 1
  funext j U
  exact (InfiniteLattice.cutoffSmearedEnergyRe_eq_smearedEnergy (f j) U).symm
private theorem ursell_scaledFamily (hCum : Cumulants.MomentCumulantRelations.Holds) {n : ℕ} [NeZero n] {L K s m i : ℕ}
    (hL : 0 < L) (hK : K = s + m) {c R : ℝ} (hc : c ≠ 0) {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hR : ∀ k, ∀ x ∈ tsupport (scaledFamily c ((2 : ℝ) ^ i / (L : ℝ) ^ m) f k), ∀ a, |x a| ≤ R)
    {ρ : Measure (InfiniteLattice.RefinedGaugeField L K)} (h1 : IsProbabilityMeasure ρ) :
    InfiniteLattice.ursellFunctionOfFamily (L := L) (K := K) ρ
        (fun k => DensitySupply.rescaled L K s (scaledFamily c ((2 : ℝ) ^ i / (L : ℝ) ^ m) f k)) =
      (c : ℂ) ^ n * InfiniteLattice.smearedEnergyCumulant ρ (TotalDensities.dyadicRescale i f) := by
  have hsp := meshSize_ne_zero hL K
  have hk1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  set A : Fin n → InfiniteLattice.AmbientSpace → ℝ := fun k => DensitySupply.rescaled L K s (scaledFamily c ((2 : ℝ) ^ i / (L : ℝ) ^ m) f k) with hA
  have hE : ∀ k, ∃ E : Finset MomentLaw.IntPlaquette, ∀ Q, A k (toElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) Q).center ≠ 0 → Q ∈ E :=
    fun k => exists_finset_of_support hL (hR k)
  have hD : ∀ k, TotalDensities.dyadicRescale i f k = fun x => c⁻¹ * A k x := by
    intro k
    funext x
    rw [hA]
    simp only [rescaled_scaledFamily hL hK c f k]
    field_simp
  have hd : (fun (k : Fin n) (U : InfiniteLattice.RefinedGaugeField L K) =>
      InfiniteLattice.cutoffSmearedEnergyRe (TotalDensities.dyadicRescale i f k) U) = fun k U => c⁻¹ * InfiniteLattice.cutoffSmearedEnergyRe (A k) U := by
    funext k U
    obtain ⟨E, hE'⟩ := hE k
    rw [hD k]
    exact cutoffEnergy_const_mul hsp _ _ hE' U
  have hcum := mixedCumulant_smul hCum ρ hk1 (fun k U => InfiniteLattice.cutoffSmearedEnergyRe (A k) U)
    (fun k => by
      obtain ⟨E, hE'⟩ := hE k
      exact cutoffEnergy_isBounded hsp _ hE') fun _ => c⁻¹
  rw [smearedEnergyCumulant_eq_ursell]
  have e : InfiniteLattice.ursellFunctionOfFamily (L := L) (K := K) ρ (TotalDensities.dyadicRescale i f) =
      ((∏ _l : Fin n, c⁻¹ : ℝ) : ℂ) * InfiniteLattice.ursellFunctionOfFamily (L := L) (K := K) ρ A := by
    unfold InfiniteLattice.ursellFunctionOfFamily
    rw [hd]
    exact hcum
  rw [e]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hcc, one_pow, one_mul]
private theorem cyclicMomentFormula_scaledFamily {n : ℕ} [NeZero n] {r : ℝ} (hr : 0 < r) (c : ℝ) (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    CyclicFormula.cyclicMomentFormula n (scaledFamily c r f) = c ^ n * TotalDensities.shortDistanceLimit f := by
  have e : scaledFamily c r f = fun i x => c * (fun i (x : E4) => (fun k (z : E4) => f k (WithLp.ofLp z)) i (r • x)) i x := rfl
  rw [e, cyclicMomentFormula_const_mul, cyclicMomentFormula_dilate (φ := fun k (z : E4) => f k (WithLp.ofLp z)) hr]
  rfl
private theorem law_bound_of_state (hCum : Cumulants.MomentCumulantRelations.Holds) {T : RenormalizationStepParameters.ParameterAssignment} {Kr : WeightedResponses.ResponseParameters}
    {y g : ℝ} (hL : 1 < T.side) (hpts : DensitySupply.MomentPointsExist T Kr y) (hg : 0 < g) (hyg : y ≤ (g ^ 2)⁻¹) {n : ℕ} [NeZero n] (h2 : 2 ≤ n)
    (h8 : n ≤ 8) {R d c C C₁ : ℝ} (hR : 0 ≤ R) (hd : 0 < d) (hc : 0 < c) (hC : 0 ≤ C) {K s m i : ℕ} (hK : K = s + m) {β : ℝ}
    (hβ : WeightedResponses.couplingWindowTop (T.stepParameters y) g ≤ β)
    (hp : WeightedResponses.IsFirstPassage (T.stepParameters y) (WeightedResponses.couplingWindowTop (T.stepParameters y) g) β K)
    {f : Fin n → (Fin 4 → ℝ) → ℝ} (hφ : MomentLaw.IsSupTestFamily R d (scaledFamily c ((2 : ℝ) ^ i / (T.side : ℝ) ^ m) f))
    (hr : 0 < (2 : ℝ) ^ i / (T.side : ℝ) ^ m)
    (hlat : |MomentLaw.latticeCycleSum T.side s (⌈R * (T.side : ℝ) ^ s⌉₊ + 2) (scaledFamily c ((2 : ℝ) ^ i / (T.side : ℝ) ^ m) f) -
      CyclicFormula.cyclicMomentFormula n (scaledFamily c ((2 : ℝ) ^ i / (T.side : ℝ) ^ m) f)| ≤ C₁ * (T.side : ℝ) ^ (-(s : ℝ)))
    {ρ : Measure (InfiniteLattice.RefinedGaugeField T.side K)}
    (h1 : IsProbabilityMeasure ρ) (hρ : SatisfiesMomentBound ⟨T, Kr, y, g, n, R, d⟩ C β ρ) :
    ‖((DensitySupply.flowSequence T y β s : ℝ) : ℂ) ^ n * InfiniteLattice.smearedEnergyCumulant ρ (TotalDensities.dyadicRescale i f) - ((TotalDensities.shortDistanceLimit f : ℝ) : ℂ)‖ ≤
      (c ^ n)⁻¹ * (C * DensitySupply.flowSequence T y β s ^ (-(1 / 10) : ℝ) + C₁ * (T.side : ℝ) ^ (-(s : ℝ))) := by
  have hL0 : 0 < T.side := by omega
  have hs : s ≤ K := by omega
  have hb := moment_bound_of_state hCum hL hpts hg hyg h2 h8 hR hd hC hs hβ hp hφ h1 hρ
  rw [ursell_scaledFamily hCum hL0 hK hc.ne' (fun k x hx a => hφ.abs_coord_le k x hx a) h1] at hb
  rw [cyclicMomentFormula_scaledFamily hr] at hlat
  set x := DensitySupply.flowSequence T y β s with hx
  set Z := InfiniteLattice.smearedEnergyCumulant ρ (TotalDensities.dyadicRescale i f) with hZ
  set lat := MomentLaw.latticeCycleSum T.side s (⌈R * (T.side : ℝ) ^ s⌉₊ + 2) (scaledFamily c ((2 : ℝ) ^ i / (T.side : ℝ) ^ m) f) with hlatd
  set Ln := TotalDensities.shortDistanceLimit f with hLn
  have hcn : 0 < c ^ n := by positivity
  have hcc : ((c : ℂ)) ^ n ≠ 0 := by exact_mod_cast hcn.ne'
  have e : (x : ℂ) ^ n * Z - (Ln : ℂ) = (((c ^ n)⁻¹ : ℝ) : ℂ) *
      (((x : ℂ) ^ n * ((c : ℂ) ^ n * Z) - (lat : ℂ)) + (((lat - c ^ n * Ln : ℝ)) : ℂ)) := by
    push_cast
    field_simp
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hcn).le]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hb ?_)) (inv_pos.2 hcn).le
  rw [Complex.norm_real]
  exact hlat
private theorem bound_of_limit {n : ℕ} {xs : ℕ → ℝ} {z : ℕ → ℂ} {s : ℕ → ℕ} {x D C C₁ Ln L : ℝ} {w : ℂ} (hL : 1 < L) (hx : 0 < x)
    (hxs : Tendsto xs atTop (𝓝 x)) (hz : Tendsto z atTop (𝓝 w)) (hs : Tendsto s atTop atTop)
    (hb : ∀ᶠ l in atTop, ‖((xs l : ℝ) : ℂ) ^ n * z l - ((Ln : ℝ) : ℂ)‖ ≤
      D * (C * xs l ^ (-(1 / 10) : ℝ) + C₁ * L ^ (-(s l : ℝ)))) :
    ‖((x : ℝ) : ℂ) ^ n * w - ((Ln : ℝ) : ℂ)‖ ≤ D * (C * x ^ (-(1 / 10) : ℝ)) := by
  have h1 : Tendsto (fun l => ‖((xs l : ℝ) : ℂ) ^ n * z l - ((Ln : ℝ) : ℂ)‖) atTop (𝓝 ‖((x : ℝ) : ℂ) ^ n * w - ((Ln : ℝ) : ℂ)‖) := by
    have hc : Tendsto (fun l => ((xs l : ℝ) : ℂ)) atTop (𝓝 ((x : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto x).comp hxs
    exact (((hc.pow n).mul hz).sub_const _).norm
  have h2 : Tendsto (fun l => L ^ (-(s l : ℝ))) atTop (𝓝 0) := by
    have e : (fun l => L ^ (-(s l : ℝ))) = fun l => (L ^ (s l))⁻¹ := by
      funext l
      rw [Real.rpow_neg (by linarith), Real.rpow_natCast]
    rw [e]
    exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop_atTop_of_one_lt hL).comp hs)
  have h3 : Tendsto (fun l => D * (C * xs l ^ (-(1 / 10) : ℝ) + C₁ * L ^ (-(s l : ℝ)))) atTop
      (𝓝 (D * (C * x ^ (-(1 / 10) : ℝ) + C₁ * 0))) :=
    (((hxs.rpow_const (Or.inl hx.ne')).const_mul C).add (h2.const_mul C₁)).const_mul D
  simpa using le_of_tendsto_of_tendsto h1 h3 hb
private theorem exists_common_subseq (a : ℕ → ℕ → ℝ) (hi : ℕ → ℝ) (h : ∀ i, 1 ≤ i → ∀ᶠ j in atTop, a i j ∈ Set.Icc 0 (hi i)) :
    ∃ (φ : ℕ → ℕ) (x : ℕ → ℝ), StrictMono φ ∧ ∀ i, 1 ≤ i → Tendsto (fun l => a i (φ l)) atTop (𝓝 (x i)) := by
  let top : ℕ → ℝ := fun i => max (hi i) 0
  let b : ℕ → ℕ → ℝ := fun j i => max 0 (min (top i) (a i j))
  have hb : ∀ j, b j ∈ Set.pi Set.univ fun i => Set.Icc 0 (top i) := fun j i _ =>
    ⟨le_max_left _ _, max_le (le_max_right _ _) (min_le_left _ _)⟩
  obtain ⟨x, -, φ, hφ, hx⟩ := (isCompact_univ_pi fun i => isCompact_Icc (a := (0 : ℝ)) (b := top i)).tendsto_subseq hb
  refine ⟨φ, x, hφ, fun i hi₁ => ?_⟩
  have h1 : Tendsto (fun l => b (φ l) i) atTop (𝓝 (x i)) := (tendsto_pi_nhds.1 hx) i
  refine h1.congr' ?_
  filter_upwards [hφ.tendsto_atTop.eventually (h i hi₁)] with l hl
  show max 0 (min (top i) (a i (φ l))) = a i (φ l)
  rw [min_eq_right (hl.2.trans (le_max_left _ _)), max_eq_right hl.1]
private theorem clog_dyadic_bounds {L : ℕ} (hL : 1 < L) {i : ℕ} (hi : 1 ≤ i) :
    1 ≤ Nat.clog L (2 ^ i) ∧ (2 : ℝ) ^ i ≤ (L : ℝ) ^ Nat.clog L (2 ^ i) ∧ (L : ℝ) ^ Nat.clog L (2 ^ i) < L * 2 ^ i := by
  have h2 : 2 ≤ 2 ^ i := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  have hm : 0 < Nat.clog L (2 ^ i) := Nat.clog_pos hL h2
  refine ⟨hm, ?_, ?_⟩
  · exact_mod_cast Nat.le_pow_clog hL (2 ^ i)
  · have h := Nat.pow_pred_clog_lt_self hL (by omega : 1 < 2 ^ i)
    have e : L ^ Nat.clog L (2 ^ i) = L * L ^ (Nat.clog L (2 ^ i)).pred := by
      have e0 : (Nat.clog L (2 ^ i)).pred + 1 = Nat.clog L (2 ^ i) := Nat.succ_pred_eq_of_pos hm
      rw [← pow_succ', e0]
    have h' : L ^ Nat.clog L (2 ^ i) < L * 2 ^ i := by
      rw [e]
      exact Nat.mul_lt_mul_of_pos_left h (by omega)
    exact_mod_cast h'
private theorem torusLimit_of_infiniteVolume (hP : InfiniteLattice.CutoffCovering.CoveringIdentification)
    (hW : InfiniteLattice.PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits) {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (K : ℕ+) {β : ℝ} (hβ : 0 < β) {ν : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (((K : ℕ)) : ℤ)))}
    (hv : InfiniteLattice.IsInfiniteVolumeLimit L K β ν) : ∃ ms, TorusLimits.IsTorusLimitAlong L K β ν ms := by
  have h₁ := (hP ⟨⟨L, hL, K, ⟨1, one_pos⟩⟩, β, hβ⟩).2.2.2
  have h₂ := (hW L K hL K.pos β hβ).2.1
  have hmem : ν ∈ InfiniteLattice.weakLimitsAlongSides L K β := (Set.ext_iff.1 (h₁.trans h₂.symm) ν).1 hv
  obtain ⟨-, n, hn, hside, hconv⟩ := hmem
  obtain ⟨φ, hφ, hφ'⟩ := strictMono_subseq_of_tendsto_atTop hside
  refine ⟨fun i => n (φ i), fun i => hn _, ?_, fun A hA => (hconv A hA).comp hφ.tendsto_atTop⟩
  intro i j hij
  by_contra hc
  have h1 := hφ' hij
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (le_trans (by norm_num) hL.2 : 1 ≤ L)
  have h2 : (L : ℝ) ^ n (φ j) ≤ (L : ℝ) ^ n (φ i) := pow_le_pow_right₀ hL1 (not_lt.mp hc)
  simp only [Function.comp, PeriodicLattice.torusSide] at h1
  linarith
section KernelsOfComponents
variable {L K : ℕ}
private theorem periodicSigma_one (L K : ℕ) :
    TorusLimits.periodicSigma L K 1 = InfiniteLattice.shiftInvariantSigma (PeriodicLattice.meshSize L (K : ℤ)) := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le fun I hI => ⟨hI.1, fun v => ?_⟩
    obtain ⟨n, hn⟩ := v.2
    have hv : v = TorusLimits.latticePointOfInt (PeriodicLattice.meshSize L (K : ℤ)) n :=
      Subtype.ext (funext hn)
    have h1 := hI.2 n
    have h2 : (fun i => ((1 : ℕ) : ℤ) * n i) = n := by
      funext i
      simp
    rw [h2] at h1
    rw [hv]
    exact ((InfiniteLattice.shift _).actOn_indicator_eq_iff I).mpr h1
  · intro I hI
    refine MeasurableSpace.measurableSet_generateFrom ⟨hI.1, fun h => ?_⟩
    exact ((InfiniteLattice.shift _).actOn_indicator_eq_iff I).mp (hI.2 _)
private theorem shiftInvariantSigma_le (a : ℝ) :
    InfiniteLattice.shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (InfiniteLattice.GaugeField a)) :=
  fun _ hI => hI.1
private theorem expect_indicator {a : ℝ} (ρ : InfiniteLattice.GaugeFieldProbability a)
    {B : Set (InfiniteLattice.GaugeField a)} (hB : MeasurableSet B) :
    ρ.expect (B.indicator fun _ => (1 : ℂ)) = ((ρ.1.real B : ℝ) : ℂ) := by
  unfold InfiniteLattice.GaugeFieldProbability.expect
  rw [integral_indicator_const _ hB]
  simp
private theorem isBoundedObservable_indicator {a : ℝ} {B : Set (InfiniteLattice.GaugeField a)} (hB : MeasurableSet B) :
    InfiniteLattice.IsBoundedObservable (B.indicator fun _ => (1 : ℂ)) := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isBoundedObservable_unitIndicator <;> assumption
private theorem measurable_measureReal {a : ℝ} {ν : Measure (InfiniteLattice.GaugeField a)}
    {κ : InfiniteLattice.GaugeField a → InfiniteLattice.GaugeFieldProbability a}
    (hκ : InfiniteLattice.IsRegularConditionalByIntegrals ν κ)
    {B : Set (InfiniteLattice.GaugeField a)} (hB : MeasurableSet B) :
    Measurable[InfiniteLattice.shiftInvariantSigma a] (fun U => (κ U).1.real B) := by
  have h := (hκ _ (isBoundedObservable_indicator hB)).1
  have h2 : (fun U => (κ U).1.real B) = fun U => ((κ U).expect (B.indicator fun _ => (1 : ℂ))).re := by
    funext U
    rw [expect_indicator _ hB]
    simp
  rw [h2]
  exact Complex.measurable_re.comp h
private theorem measurable_toMeasure {a : ℝ} {ν : Measure (InfiniteLattice.GaugeField a)}
    {κ : InfiniteLattice.GaugeField a → InfiniteLattice.GaugeFieldProbability a}
    (hκ : InfiniteLattice.IsRegularConditionalByIntegrals ν κ) :
    Measurable fun U => (κ U).1 := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have h := (measurable_measureReal hκ hB).mono (shiftInvariantSigma_le a) le_rfl
  have h2 : (fun U => (κ U).1 B) = fun U => ENNReal.ofReal ((κ U).1.real B) := by
    funext U
    have := (κ U).2
    simp [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [h2]
  exact h.ennreal_ofReal
private theorem exists_periodic_kernel {ν : Measure (TorusLimits.FineField L K)} [IsProbabilityMeasure ν]
    {κ : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) →
      InfiniteLattice.GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))}
    (hκ : InfiniteLattice.IsRegularConditionalByIntegrals ν κ) :
    ∃ κ' : Kernel (TorusLimits.FineField L K) (TorusLimits.FineField L K),
      TorusLimits.IsPeriodicConditionalKernel L K ν 1 κ' ∧ ∀ U, κ' U = (κ U).1 := by
  refine ⟨⟨fun U => (κ U).1, measurable_toMeasure hκ⟩, ⟨⟨fun U => (κ U).2⟩, fun B hB => ?_⟩, fun _ => rfl⟩
  rw [periodicSigma_one]
  have hm := shiftInvariantSigma_le (PeriodicLattice.meshSize L (K : ℤ))
  have hgm := measurable_measureReal hκ hB
  have hg : Measurable fun U => (κ U).1.real B := hgm.mono hm le_rfl
  have hbd : ∀ U, ‖(κ U).1.real B‖ ≤ 1 := fun U => by
    have := (κ U).2
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hgi : Integrable (fun U => (κ U).1.real B) ν :=
    Integrable.of_bound hg.aestronglyMeasurable 1 (Eventually.of_forall hbd)
  have hfi : Integrable (B.indicator fun _ => (1 : ℝ)) ν :=
    (integrable_const (1 : ℝ)).indicator hB
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hfi (fun I _ _ => hgi.integrableOn) (fun I hI _ => ?_)
    hgm.stronglyMeasurable.aestronglyMeasurable
  have hIb : MeasurableSet I := hm _ hI
  have hJ : Measurable[InfiniteLattice.shiftInvariantSigma (PeriodicLattice.meshSize L (K : ℤ))]
      (I.indicator fun _ => (1 : ℂ)) := (@measurable_const _ _ _ (InfiniteLattice.shiftInvariantSigma _) _).indicator hI
  have hk := (hκ _ (isBoundedObservable_indicator hB)).2 _ hJ ⟨1, fun U => by by_cases h : U ∈ I <;> simp [h]⟩
  have e1 : (fun U => (I.indicator fun _ => (1 : ℂ)) U * (κ U).expect (B.indicator fun _ => (1 : ℂ))) =
      fun U => ((I.indicator (fun U => (κ U).1.real B) U : ℝ) : ℂ) := by
    funext U
    rw [expect_indicator _ hB]
    by_cases h : U ∈ I <;> simp [h]
  have e2 : (fun U => (I.indicator fun _ => (1 : ℂ)) U * (B.indicator fun _ => (1 : ℂ)) U) =
      fun U => ((I.indicator (B.indicator fun _ => (1 : ℝ)) U : ℝ) : ℂ) := by
    funext U
    by_cases h : U ∈ I <;> by_cases h' : U ∈ B <;> simp [h, h']
  rw [e1, e2, integral_complex_ofReal, integral_complex_ofReal, integral_indicator hIb, integral_indicator hIb] at hk
  exact_mod_cast hk
end KernelsOfComponents
private lemma eventuallyInParameters_and {P Q : RenormalizationStepParameters.ParameterAssignment → WeightedResponses.ResponseParameters → ℝ → Prop}
    (hP : HullTrees.EventuallyInParameters P) (hQ : HullTrees.EventuallyInParameters Q) :
    HullTrees.EventuallyInParameters fun T K y => P T K y ∧ Q T K y := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, h₁, f₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, h₂, f₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (h₁ c) (h₂ c),
    fun L hodd hL T hTa hTL hD hC hH hr hCd => ?_⟩
  obtain ⟨M₁, g₁⟩ := f₁ L hodd (le_trans (le_max_left _ _) hL) T hTa hTL hD hC hH (le_trans hr (min_le_left _ _))
    (le_trans (le_max_left _ _) hCd)
  obtain ⟨M₂, g₂⟩ := f₂ L hodd (le_trans (le_max_right _ _) hL) T hTa hTL hD hC hH (le_trans hr (min_le_right _ _))
    (le_trans (le_max_right _ _) hCd)
  refine ⟨max M₁ M₂, fun K hK hη hN hf hret => ?_⟩
  obtain ⟨y₁, k₁⟩ := g₁ K (le_trans (le_max_left _ _) hK) hη hN hf hret
  obtain ⟨y₂, k₂⟩ := g₂ K (le_trans (le_max_right _ _) hK) hη hN hf hret
  exact ⟨max y₁ y₂, fun y hy hr' hw => ⟨k₁ y (le_trans (le_max_left _ _) hy) hr' hw,
    k₂ y (le_trans (le_max_right _ _) hy) hr' hw⟩⟩
private lemma eventuallyInParameters_mono {P Q : RenormalizationStepParameters.ParameterAssignment → WeightedResponses.ResponseParameters → ℝ → Prop}
    (hP : HullTrees.EventuallyInParameters P) (hi : ∀ T K y, P T K y → Q T K y) : HullTrees.EventuallyInParameters Q := by apply _root_.YangMills.SharedProofs.p60552 <;> assumption
private structure MomentBounds (T : RenormalizationStepParameters.ParameterAssignment) (Kr : WeightedResponses.ResponseParameters) (y : ℝ) : Prop where
  points : DensitySupply.MomentPointsExist T Kr y
  law : ∀ g : ℝ, 0 < g → y ≤ (g ^ 2)⁻¹ → ∀ (n : ℕ) [NeZero n], 2 ≤ n → n ≤ 8 → ∀ R d : ℝ, 0 < d → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (K : ℕ) (β : ℝ), WeightedResponses.couplingWindowTop (T.stepParameters y) g ≤ β →
      WeightedResponses.IsFirstPassage (T.stepParameters y) (WeightedResponses.couplingWindowTop (T.stepParameters y) g) β K →
      ∀ ν : Measure (InfiniteLattice.RefinedGaugeField T.side K), (∃ ms, TorusLimits.IsTorusLimitAlong T.side K β ν ms) →
        SatisfiesMomentBound ⟨T, Kr, y, g, n, R, d⟩ C β ν ∧
        ∀ κ : Kernel (InfiniteLattice.RefinedGaugeField T.side K) (InfiniteLattice.RefinedGaugeField T.side K),
          TorusLimits.IsPeriodicConditionalKernel T.side K ν 1 κ →
            ∀ᵐ U ∂ν, SatisfiesMomentBound ⟨T, Kr, y, g, n, R, d⟩ C β (κ U)
private theorem eventually_momentBounds (hAt : MomentLaw.limitPointCumulantStatement) (hIn : MomentLaw.periodicComponentCumulantStatement)
    (hPts : MomentLaw.momentPointsExistStatement) : HullTrees.EventuallyInParameters MomentBounds := by
  refine eventuallyInParameters_mono (eventuallyInParameters_and hAt (eventuallyInParameters_and hIn hPts)) fun T Kr y h => ?_
  obtain ⟨hA, hI, hP⟩ := h
  refine ⟨hP, fun g hg hyg n _ h2 h8 R d hd => ?_⟩
  obtain ⟨C, c, X₀, -, -, hC⟩ := hA g hg hyg n h2 h8 R d hd
  obtain ⟨C', hC'⟩ := hI g hg hyg n h2 h8 R d hd
  refine ⟨max (max (C 0) C') 0, le_max_right _ _, fun K β hβ hp ν hν => ⟨fun S hK hb => ?_, fun κ hκ => ?_⟩⟩
  · subst hK hb
    exact ((hC S).2 ν hν).trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (rpow_neg_tenth_nonneg _))
  · filter_upwards [hC' K β hβ hp ν hν 1 le_rfl κ hκ] with U hU S hK hb
    exact (hU S hK hb).trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (rpow_neg_tenth_nonneg _))
private theorem momentBounds_at_trajectory_couplings (hH : HullTrees.EventuallyInParameters MomentBounds)
    (hRet : WeightedResponses.responseReturnsStatement) :
    SystemOfAdmissibleConstants.ForAllTrajectoryCouplings fun T y _ _ => ∃ Kr : WeightedResponses.ResponseParameters, MomentBounds T Kr y := by
  intro a ha
  obtain ⟨Lh, rth, Cq, hrth, fq⟩ := hH a ha
  obtain ⟨LR, rtR, hrtR, fR⟩ := hRet a ha
  refine ⟨max Lh LR, fun c => min (rth c) (rtR c), Cq, fun c => lt_min (hrth c) (hrtR c), fun L ho hge T h1 h2 hD hC hH' hr hc => ?_⟩
  obtain ⟨M, fM⟩ := fq L ho (le_trans (le_max_left _ _) hge) T h1 h2 hD hC hH' (hr.trans (min_le_left _ _)) hc
  obtain ⟨Kr, hKc, hη, hN, hfit, Cs, yR, hCs, hret₀⟩ := fR T h1 (by rw [h2]; exact le_trans (le_max_right _ _) hge) hD hC hH'
    (hr.trans (min_le_right _ _)) M
  obtain ⟨y₀, g₀⟩ := fM Kr hKc hη hN hfit ⟨Cs, yR, hCs, hret₀⟩
  exact ⟨y₀, fun y hy hR hW D hDh g hg hfl => ⟨Kr, g₀ y hy hR hW⟩⟩
private def CouplingAtScaleHolds (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop :=
  ∀ Bs : ℝ, 2 * T.B ≤ Bs → TotalDensities.ForSmallCoupling fun g => ∃ e : ℝ → ℝ, Tendsto e (𝓝[>] 0) (𝓝 0) ∧
    ∀ (K : ℕ) (β : ℝ), 2 ≤ K → TotalDensities.IsFirstPassagePoint (T.stepParameters y) Bs g K β → ∀ k ≤ K, ∀ d : ℝ, d < 1 →
      1 ≤ d / ((T.stepParameters y).side : ℝ) ^ ((k : ℤ) - (K : ℤ)) →
      d / ((T.stepParameters y).side : ℝ) ^ ((k : ℤ) - (K : ℤ)) ≤ ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β k →
      |ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β k / (TrajectoryData.logSlope * Real.log (1 / d)) - 1| ≤ e d
private theorem couplingAtScaleHolds_of (hD : TrajectoryData.trajectoryDataStatement) :
    TotalDensities.HoldsAtAdmissibleParameters CouplingAtScaleHolds := by
  obtain ⟨Qc, hQ, floorL, ceilRt, ceilσ, floorN, floorCs, C₀, h1, h2, hT⟩ := hD
  refine ⟨⟨Qc, floorL, fun _ => C₀, ceilRt, ceilσ, floorN, floorCs, fun _ => 0⟩, ⟨hQ, h1, h2⟩, fun T hDr hM => ?_⟩
  obtain ⟨y₀, f⟩ := hT T hDr hM.side_ge hM.rt_le hM.threshold_le hM.n₀_ge hM.Cs_ge hM.derivBound_ge hM.holds
  refine ⟨y₀, fun y hy Bs hBs => ?_⟩
  obtain ⟨D, hData⟩ := f y hy
  have hlam : 0 < D.rateBound := by
    have hL : (1 : ℝ) < T.side := by
      have h : 2 ^ 40 ≤ T.side := hDr.L_ge
      have h' : 1 < T.side := lt_of_lt_of_le (by norm_num) h
      exact_mod_cast h'
    have hlog := Real.log_pos hL
    have hpi := Real.pi_pos
    show 0 < 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
    positivity
  obtain ⟨-, hHas⟩ := hData Bs D.rateBound hBs hlam le_rfl
  refine ⟨(D.withShift Bs D.rateBound).floorStar, fun g hg hy₂ => ?_⟩
  obtain ⟨e, he, h⟩ := hHas.distance g hg hy₂ 1 zero_le_one
  refine ⟨e, he, fun K β hK hp k hk d hd h₁ h₂ => h K β hK hp k hk d hd h₁ ?_⟩
  rw [Real.rpow_one]
  exact h₂
section AtAdmissibleParameters
private theorem couplingWindowTop_eq {T : RenormalizationStepParameters.ParameterAssignment} {y g : ℝ} :
    WeightedResponses.couplingWindowTop (T.stepParameters y) g = SequencePassage.passageThreshold (2 * T.B) g := by
  show (g ^ 2)⁻¹ + 2 * T.B = g ^ (-2 : ℤ) + 2 * T.B
  rw [zpow_neg]
  norm_cast
private theorem firstPassage_of_mem_window {T : RenormalizationStepParameters.ParameterAssignment} {y g β : ℝ} {K : ℕ}
    (h : β ∈ SequencePassage.passageWindow (2 * T.B) g (ClusterExpansionOfAStep.flowCoupling (T.stepParameters y)) K) :
    WeightedResponses.couplingWindowTop (T.stepParameters y) g ≤ β ∧
      WeightedResponses.IsFirstPassage (T.stepParameters y) (WeightedResponses.couplingWindowTop (T.stepParameters y) g) β K := by
  rw [couplingWindowTop_eq]
  exact ⟨h.1, h.2.1, h.2.2⟩
private theorem abs_le_of_norm_le {x w Ln B : ℝ} {n : ℕ} (h : ‖((x : ℝ) : ℂ) ^ n * ((w : ℝ) : ℂ) - ((Ln : ℝ) : ℂ)‖ ≤ B) :
    |x ^ n * w - Ln| ≤ B := by
  have e : ((x : ℝ) : ℂ) ^ n * ((w : ℝ) : ℂ) - ((Ln : ℝ) : ℂ) = ((x ^ n * w - Ln : ℝ) : ℂ) := by
    push_cast
    ring
  rwa [e, Complex.norm_real, Real.norm_eq_abs] at h
private theorem tendsto_succPNat_atTop : Tendsto Nat.succPNat atTop atTop := by apply _root_.YangMills.SharedProofs.p14344 <;> assumption
private theorem tendsto_natPred_atTop : Tendsto PNat.natPred atTop atTop := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicExtensions.tendsto_pnatNatPred_atTop <;> assumption
private theorem rpow_tenth_le_hundredth {x : ℝ} (hx : 1 ≤ x) {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) :
    D * (C * x ^ (-(1 / 10) : ℝ)) ≤ D * C * x ^ (-(1 / 100) : ℝ) := by
  have h := Real.rpow_le_rpow_of_exponent_le hx (show (-(1 / 10) : ℝ) ≤ -(1 / 100) by norm_num)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left h (mul_nonneg hD hC)
private theorem law_at_admissible_parameters (hCum : Cumulants.MomentCumulantRelations.Holds)
    (hLat : MomentLaw.latticeCycleSumApproxStatement) {T : RenormalizationStepParameters.ParameterAssignment} {Kr : WeightedResponses.ResponseParameters} {y g : ℝ}
    (hDr : T.Admissible) (hlaw : MomentBounds T Kr y) (hg : 0 < g) (hyg : y ≤ (g ^ 2)⁻¹) (hLg : (T.side : ℝ) ≤ g ^ (-2 : ℤ))
    (hvol : ∀ (K : ℕ+) (β : ℝ) (ν : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize T.side (((K : ℕ)) : ℤ)))), 0 < β →
      InfiniteLattice.IsInfiniteVolumeLimit T.side K β ν → ∃ ms, TorusLimits.IsTorusLimitAlong T.side K β ν ms)
    (hrow : TotalDensities.ExpansionFlowEqTotalFlowAt (T.stepParameters y) (2 * T.B) g) {e : ℝ → ℝ}
    (hdist : ∀ (K : ℕ) (β : ℝ), 2 ≤ K → TotalDensities.IsFirstPassagePoint (T.stepParameters y) (2 * T.B) g K β → ∀ k ≤ K, ∀ d : ℝ, d < 1 →
      1 ≤ d / ((T.stepParameters y).side : ℝ) ^ ((k : ℤ) - (K : ℤ)) →
      d / ((T.stepParameters y).side : ℝ) ^ ((k : ℤ) - (K : ℤ)) ≤ ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β k →
      |ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β k / (TrajectoryData.logSlope * Real.log (1 / d)) - 1| ≤ e d)
    (hch : ∀ Z : ∀ K : ℕ+, ℝ → Set (Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize (T.stepParameters y).side (((K : ℕ)) : ℤ)))),
      TotalDensities.ContainsPairStates (T.stepParameters y) (2 * T.B) g Z →
      ∀ (Q : SystemsWithFiveBounds.PairSequence (T.stepParameters y).side (IsFirstPassagePair (T.stepParameters y) (2 * T.B) g))
        (S : LimitTheorem.CumulantFamily),
        Q.Defines S → ∀ A : SeparatedTuples.DecompositionData, A.IsCanonical (LimitTheorem.centredOf S) →
          ∀ (ξ : A.space) (n : ℕ), 2 ≤ n → ∀ X : TestSpaces.SepTupleOfCard n, ∃ (φ : ℕ → ℕ+)
            (ρ : ∀ l, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize (T.stepParameters y).side (((Q.cutoff (φ l) : ℕ)) : ℤ)))),
            Tendsto φ atTop atTop ∧ (∀ l, ρ l ∈ Z (Q.cutoff (φ l)) (Q.coupling (φ l))) ∧ (∀ l, IsProbabilityMeasure (ρ l)) ∧
            Tendsto (fun l => InfiniteLattice.smearedEnergyCumulant (ρ l) X.1) atTop (𝓝 ((LimitTheorem.connectedFn (A.comp ξ) X : ℝ) : ℂ)))
    (Q : SystemsWithFiveBounds.PairSequence (T.stepParameters y).side (IsFirstPassagePair (T.stepParameters y) (2 * T.B) g))
    (S : LimitTheorem.CumulantFamily)
    (hQ : Q.Defines S) (n : ℕ) [NeZero n] (hn : 2 ≤ n) (h8 : n ≤ 8) (X : TestSpaces.SepTupleOfCard n) :
    ∃ (δ C : ℝ) (i₁ : ℕ) (x : ℕ → ℝ), 0 < δ ∧
      (∀ i, i₁ ≤ i → IsCouplingAtScale (T.stepParameters y) Q (δ / 2 ^ i) (x i)) ∧
      (∀ i, i₁ ≤ i → ∀ Y : TestSpaces.SepTupleOfCard n, Y.1 = TotalDensities.dyadicRescale i X.1 →
        |x i ^ n * S n hn Y - TotalDensities.shortDistanceLimit X.1| ≤ C * x i ^ (-(1 / 100) : ℝ)) ∧
      ∀ A : SeparatedTuples.DecompositionData, A.IsCanonical (LimitTheorem.centredOf S) → ∀ᵐ ξ ∂A.law,
        ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → ∀ Y : TestSpaces.SepTupleOfCard n, Y.1 = TotalDensities.dyadicRescale i X.1 →
          |x i ^ n * LimitTheorem.connectedFn (A.comp ξ) Y - TotalDensities.shortDistanceLimit X.1| ≤ C * x i ^ (-(1 / 100) : ℝ) := by
  classical
  have hL2 : 2 ^ 40 ≤ T.side := hDr.L_ge
  have hL : 1 < T.side := lt_of_lt_of_le (by norm_num) hL2
  have hLr : (1 : ℝ) < (T.side : ℝ) := by exact_mod_cast hL
  have hLp : (0 : ℝ) < (T.side : ℝ) := by linarith
  have hB : 0 < T.B := lt_of_lt_of_le one_pos hDr.B_ge
  obtain ⟨c, R, d, hc, hR, hd, hT⟩ := exists_scaling_constants X hLr.le
  obtain ⟨C, hC, hlawC⟩ := hlaw.law g hg hyg n hn h8 R d hd
  obtain ⟨C₁, hC₁⟩ := hLat n hn R d hR hd
  let m : ℕ → ℕ := fun i => Nat.clog T.side (2 ^ i)
  let r : ℕ → ℝ := fun i => (2 : ℝ) ^ i / (T.side : ℝ) ^ m i
  have hm : ∀ i, 1 ≤ i → 1 ≤ m i ∧ (2 : ℝ) ^ i ≤ (T.side : ℝ) ^ m i ∧ (T.side : ℝ) ^ m i < T.side * 2 ^ i :=
    fun i hi => clog_dyadic_bounds hL hi
  have hLm : ∀ i, 0 < (T.side : ℝ) ^ m i := fun i => by positivity
  have hr0 : ∀ i, 0 < r i := fun i => div_pos (by positivity) (hLm i)
  have hr1 : ∀ i, 1 ≤ i → r i ≤ 1 := fun i hi => (div_le_one (hLm i)).2 (hm i hi).2.1
  have hr2 : ∀ i, 1 ≤ i → 1 / (T.side : ℝ) ≤ r i := fun i hi => by
    show 1 / (T.side : ℝ) ≤ (2 : ℝ) ^ i / (T.side : ℝ) ^ m i
    rw [div_le_div_iff₀ hLp (hLm i)]
    linarith [(hm i hi).2.2]
  have hwin : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β →
      β ∈ SequencePassage.passageWindow (2 * T.B) g (ClusterExpansionOfAStep.flowCoupling (T.stepParameters y)) K ∧
        ∀ k ≤ (K : ℕ), TotalDensityFlow.coupling (T.stepParameters y) β k = ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β k := fun K β h => by
    have h1 := hrow K
    have h2 : β ∈ SequencePassage.passageWindow (2 * T.B) g (ClusterExpansionOfAStep.flowCoupling (T.stepParameters y)) K := h1.1 ▸ h
    exact ⟨h2, h1.2 β h2⟩
  have hlow : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β → ∀ k < (K : ℕ),
      (T.side : ℝ) < ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β k := fun K β h k hk => by
    have h1 : SequencePassage.passageThreshold (2 * T.B) g < ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β k := (hwin K β h).1.2.2 k hk
    have h2 : SequencePassage.passageThreshold (2 * T.B) g = g ^ (-2 : ℤ) + 2 * T.B := rfl
    linarith
  have hβ0 : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β → 0 < β := fun K β h => by
    have h1 : SequencePassage.passageThreshold (2 * T.B) g ≤ β := (hwin K β h).1.1
    have h2 : SequencePassage.passageThreshold (2 * T.B) g = g ^ (-2 : ℤ) + 2 * T.B := rfl
    linarith
  have key : ∀ i, 1 ≤ i → ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β → m i < (K : ℕ) →
      ∀ ρ : Measure (InfiniteLattice.RefinedGaugeField T.side K), IsProbabilityMeasure ρ →
        SatisfiesMomentBound ⟨T, Kr, y, g, n, R, d⟩ C β ρ →
        ‖((DensitySupply.flowSequence T y β ((K : ℕ) - m i) : ℝ) : ℂ) ^ n * InfiniteLattice.smearedEnergyCumulant ρ (TotalDensities.dyadicRescale i X.1) -
            ((TotalDensities.shortDistanceLimit X.1 : ℝ) : ℂ)‖ ≤
          (c ^ n)⁻¹ * (C * DensitySupply.flowSequence T y β ((K : ℕ) - m i) ^ (-(1 / 10) : ℝ) +
            C₁ * (T.side : ℝ) ^ (-(((K : ℕ) - m i : ℕ) : ℝ))) := by
    intro i hi K β hp hK ρ h1 hρ
    obtain ⟨ht, hpass⟩ := firstPassage_of_mem_window (hwin K β hp).1
    have hφ := hT (r i) (hr2 i hi) (hr1 i hi)
    exact law_bound_of_state hCum hL hlaw.points hg hyg hn h8 hR hd hc hC (K := K) (s := (K : ℕ) - m i) (m := m i) (i := i)
      (by omega) ht hpass hφ (hr0 i) (hC₁ _ T.side _ hL.le hφ).2 h1 hρ
  have hratio : ∀ i (K k : ℕ), k + m i = K → ((1 : ℝ) / 2 ^ i) / (T.side : ℝ) ^ ((k : ℤ) - (K : ℤ)) = (T.side : ℝ) ^ m i / 2 ^ i := by
    intro i K k h
    have e1 : (k : ℤ) - (K : ℤ) = -((m i : ℕ) : ℤ) := by omega
    rw [e1, zpow_neg, zpow_natCast]
    field_simp
  have hrat1 : ∀ i, 1 ≤ i → 1 ≤ (T.side : ℝ) ^ m i / 2 ^ i := fun i hi =>
    (one_le_div (by positivity)).2 (hm i hi).2.1
  have hrat2 : ∀ i, 1 ≤ i → (T.side : ℝ) ^ m i / 2 ^ i < T.side := fun i hi =>
    (div_lt_iff₀ (by positivity)).2 (hm i hi).2.2
  have hd1 : ∀ i, 1 ≤ i → (1 : ℝ) / 2 ^ i < 1 := fun i hi => by
    have h1 : (1 : ℝ) < 2 ^ i := one_lt_pow₀ (by norm_num) (by omega)
    rw [div_lt_one (by positivity)]
    exact h1
  let J : ℕ → ℕ+ := Nat.succPNat
  have hJ : Tendsto J atTop atTop := tendsto_succPNat_atTop
  let a : ℕ → ℕ → ℝ := fun i j => DensitySupply.flowSequence T y (Q.coupling (J j)) ((Q.cutoff (J j) : ℕ) - m i)
  let top : ℕ → ℝ := fun i => (1 + |e (1 / 2 ^ i)|) * (TrajectoryData.logSlope * Real.log (1 / (1 / 2 ^ i)))
  have hb0 : 0 < TrajectoryData.logSlope := by
    unfold TrajectoryData.logSlope
    positivity
  have hfacts : ∀ i, 1 ≤ i → ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β → m i < (K : ℕ) →
      1 ≤ ((1 : ℝ) / 2 ^ i) / ((T.stepParameters y).side : ℝ) ^ ((((K : ℕ) - m i : ℕ) : ℤ) - ((K : ℕ) : ℤ)) ∧
      ((1 : ℝ) / 2 ^ i) / ((T.stepParameters y).side : ℝ) ^ ((((K : ℕ) - m i : ℕ) : ℤ) - ((K : ℕ) : ℤ)) ≤
        ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β ((K : ℕ) - m i) ∧ (T.side : ℝ) < ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β ((K : ℕ) - m i) := by
    intro i hi K β hp hK
    have hk : (K : ℕ) - m i + m i = K := by omega
    have hx₀ : (T.side : ℝ) < ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β ((K : ℕ) - m i) := hlow K β hp _ (by have := (hm i hi).1; omega)
    have e₁ : ((1 : ℝ) / 2 ^ i) / ((T.stepParameters y).side : ℝ) ^ ((((K : ℕ) - m i : ℕ) : ℤ) - ((K : ℕ) : ℤ)) = (T.side : ℝ) ^ m i / 2 ^ i :=
      hratio i K ((K : ℕ) - m i) hk
    rw [e₁]
    exact ⟨hrat1 i hi, ((hrat2 i hi).trans hx₀).le, hx₀⟩
  have hbound : ∀ i, 1 ≤ i → ∀ᶠ j in atTop, a i j ∈ Set.Icc 0 (top i) := by
    intro i hi
    have hKJ : Tendsto (fun j => (Q.cutoff (J j) : ℕ)) atTop atTop := Q.tendsto_cutoff.comp hJ
    filter_upwards [hKJ.eventually_gt_atTop (m i + 2)] with j hj
    have hp := Q.pair (J j)
    obtain ⟨h₁, h₂, hx₀⟩ := hfacts i hi _ _ hp (by omega)
    have h₃ := hdist (Q.cutoff (J j)) (Q.coupling (J j)) (by omega) (hwin _ _ hp).1 ((Q.cutoff (J j) : ℕ) - m i) (Nat.sub_le _ _) _ (hd1 i hi) h₁ h₂
    have hlog : 0 < Real.log (1 / (1 / 2 ^ i)) := by
      have h1 : (1 : ℝ) < 1 / (1 / 2 ^ i) := by
        rw [one_div_one_div]
        exact one_lt_pow₀ (by norm_num) (by omega)
      exact Real.log_pos h1
    have hA : 0 < TrajectoryData.logSlope * Real.log (1 / (1 / 2 ^ i)) := mul_pos hb0 hlog
    refine ⟨by show 0 ≤ ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) (Q.coupling (J j)) ((Q.cutoff (J j) : ℕ) - m i); linarith, ?_⟩
    show ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) (Q.coupling (J j)) ((Q.cutoff (J j) : ℕ) - m i) ≤ top i
    have h₄ : ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) (Q.coupling (J j)) ((Q.cutoff (J j) : ℕ) - m i) /
        (TrajectoryData.logSlope * Real.log (1 / (1 / 2 ^ i))) - 1 ≤ |e (1 / 2 ^ i)| :=
      ((le_abs_self _).trans h₃).trans (le_abs_self _)
    have h₅ : ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) (Q.coupling (J j)) ((Q.cutoff (J j) : ℕ) - m i) /
        (TrajectoryData.logSlope * Real.log (1 / (1 / 2 ^ i))) ≤ 1 + |e (1 / 2 ^ i)| := by linarith
    exact (div_le_iff₀ hA).1 h₅
  obtain ⟨φ, x, hφ, hx⟩ := exists_common_subseq a top hbound
  let ψ : ℕ → ℕ+ := fun l => J (φ l)
  have hψ : Tendsto ψ atTop atTop := hJ.comp hφ.tendsto_atTop
  have hKψ : ∀ N : ℕ, ∀ᶠ l in atTop, N < (Q.cutoff (ψ l) : ℕ) := fun N => (Q.tendsto_cutoff.comp hψ).eventually_gt_atTop N
  have hx₁ : ∀ i, 1 ≤ i → (T.side : ℝ) ≤ x i := by
    intro i hi
    refine ge_of_tendsto (hx i hi) ?_
    filter_upwards [hKψ (m i)] with l hl
    exact (hfacts i hi _ _ (Q.pair (ψ l)) hl).2.2.le
  have hx1 : ∀ i, 1 ≤ i → 1 ≤ x i := fun i hi => hLr.le.trans (hx₁ i hi)
  let ψ' : ℕ+ → ℕ+ := fun p => ψ p.natPred
  have hψ' : Tendsto ψ' atTop atTop := hψ.comp tendsto_natPred_atTop
  have hQ' : (Q.subseq ψ' hψ').Defines S := fun k hk Y => (hQ k hk Y).comp hψ'
  let Z : ∀ K : ℕ+, ℝ → Set (Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize (T.stepParameters y).side (((K : ℕ)) : ℤ)))) :=
    fun K β => {ρ | SatisfiesMomentBound (K := K) ⟨T, Kr, y, g, n, R, d⟩ C β ρ}
  have hZ : TotalDensities.ContainsPairStates (T.stepParameters y) (2 * T.B) g Z := by
    refine ⟨fun K β hp ν hv => ?_, fun K β hp hLs hβ ν hv κ hκ => ?_⟩
    · obtain ⟨ht, hpass⟩ := firstPassage_of_mem_window (hwin K β hp).1
      exact (hlawC K β ht hpass ν (hvol K β ν (hβ0 K β hp) hv)).1
    · obtain ⟨ht, hpass⟩ := firstPassage_of_mem_window (hwin K β hp).1
      have hprob : IsProbabilityMeasure ν.1 := hv.1
      obtain ⟨κ', hc', hk⟩ := @exists_periodic_kernel T.side K ν.1 hprob κ hκ
      have h := (hlawC K β ht hpass ν.1 (hvol K β ν.1 (hβ0 K β hp) hv)).2 κ' hc'
      filter_upwards [h] with U hU
      have e₂ : κ' U = (κ U).toMeasure := hk U
      show SatisfiesMomentBound (K := K) ⟨T, Kr, y, g, n, R, d⟩ C β (κ U).toMeasure
      rw [← e₂]
      exact hU
  have hD0 : 0 ≤ (c ^ n)⁻¹ := (inv_pos.2 (pow_pos hc n)).le
  refine ⟨1, (c ^ n)⁻¹ * C, 1, x, one_pos, fun i hi => ?_, fun i hi Y hY => ?_, fun A hA => ?_⟩
  · intro ε hε
    have hev : ∀ᶠ l in atTop, ∃ k : ℕ, k ≤ (Q.cutoff (ψ l) : ℕ) ∧
        1 ≤ ((1 : ℝ) / 2 ^ i) / ((T.stepParameters y).side : ℝ) ^ ((k : ℤ) - ((Q.cutoff (ψ l) : ℕ) : ℤ)) ∧
        ((1 : ℝ) / 2 ^ i) / ((T.stepParameters y).side : ℝ) ^ ((k : ℤ) - ((Q.cutoff (ψ l) : ℕ) : ℤ)) ≤
          TotalDensityFlow.coupling (T.stepParameters y) (Q.coupling (ψ l)) k ∧
        |TotalDensityFlow.coupling (T.stepParameters y) (Q.coupling (ψ l)) k - x i| ≤ ε := by
      filter_upwards [hKψ (m i), Metric.tendsto_nhds.1 (hx i hi) ε hε] with l hl hl2
      have hp := Q.pair (ψ l)
      obtain ⟨h₁, h₂, -⟩ := hfacts i hi _ _ hp hl
      have heq := (hwin _ _ hp).2 ((Q.cutoff (ψ l) : ℕ) - m i) (Nat.sub_le _ _)
      refine ⟨(Q.cutoff (ψ l) : ℕ) - m i, Nat.sub_le _ _, h₁, ?_, ?_⟩
      · rw [heq]
        exact h₂
      · rw [heq, ← Real.dist_eq]
        exact hl2.le
    exact hψ.frequently hev.frequently
  · have hz : Tendsto (fun l => InfiniteLattice.smearedEnergyCumulant (Q.state (ψ l)) (TotalDensities.dyadicRescale i X.1)) atTop (𝓝 ((S n hn Y : ℝ) : ℂ)) := by
      have h := (hQ n hn Y).comp hψ
      simp only [Function.comp_def, hY] at h
      exact h
    have hs : Tendsto (fun l => (Q.cutoff (ψ l) : ℕ) - m i) atTop atTop :=
      (tendsto_sub_atTop_nat (m i)).comp (Q.tendsto_cutoff.comp hψ)
    have hb := bound_of_limit (n := n) (D := (c ^ n)⁻¹) (C := C) (C₁ := C₁) (Ln := TotalDensities.shortDistanceLimit X.1) hLr
      (lt_of_lt_of_le one_pos (hx1 i hi)) (hx i hi) hz hs (by
        filter_upwards [hKψ (m i)] with l hl
        exact key i hi _ _ (Q.pair (ψ l)) hl _ (Q.isLimit (ψ l)).1
          (hZ.limitPoint_mem _ _ (Q.pair (ψ l)) _ (Q.isLimit (ψ l))))
    exact (abs_le_of_norm_le hb).trans (rpow_tenth_le_hundredth (hx1 i hi) hD0 hC)
  · refine Eventually.of_forall fun ξ => ⟨1, fun i hi Y hY => ?_⟩
    obtain ⟨φ₂, ρ, hφ₂, hρ, hprob, hlim⟩ := hch Z hZ (Q.subseq ψ' hψ') S hQ' A hA ξ n hn Y
    have hpn : Tendsto (fun l => (φ₂ l).natPred) atTop atTop := tendsto_natPred_atTop.comp hφ₂
    have hz : Tendsto (fun l => InfiniteLattice.smearedEnergyCumulant (ρ l) (TotalDensities.dyadicRescale i X.1)) atTop
        (𝓝 ((LimitTheorem.connectedFn (A.comp ξ) Y : ℝ) : ℂ)) := by
      rw [← hY]
      exact hlim
    have hs : Tendsto (fun l => (Q.cutoff (ψ' (φ₂ l)) : ℕ) - m i) atTop atTop :=
      (tendsto_sub_atTop_nat (m i)).comp ((Q.tendsto_cutoff.comp hψ').comp hφ₂)
    have hb := bound_of_limit (n := n) (D := (c ^ n)⁻¹) (C := C) (C₁ := C₁) (Ln := TotalDensities.shortDistanceLimit X.1)
      (xs := fun l => a i (φ (φ₂ l).natPred)) hLr (lt_of_lt_of_le one_pos (hx1 i hi)) ((hx i hi).comp hpn) hz hs (by
        filter_upwards [hpn.eventually (hKψ (m i))] with l hl
        exact key i hi (Q.cutoff (ψ' (φ₂ l))) _ (Q.pair (ψ' (φ₂ l))) hl (ρ l) (hprob l) (hρ l))
    exact (abs_le_of_norm_le hb).trans (rpow_tenth_le_hundredth (hx1 i hi) hD0 hC)
end AtAdmissibleParameters
theorem ShortDistanceLawAtFewPoints.holds (hG : TotalDensities.TrajectoryCouplingsGiveWindow.Statement)
    (hD : TrajectoryData.trajectoryDataStatement) (hRR : TotalDensities.expansionFlowEqTotalFlow)
    (hRet : WeightedResponses.responseReturnsStatement) (hPts : MomentLaw.momentPointsExistStatement) (hAt : MomentLaw.limitPointCumulantStatement)
    (hIn : MomentLaw.periodicComponentCumulantStatement) (hLat : MomentLaw.latticeCycleSumApproxStatement)
    (hCum : Cumulants.MomentCumulantRelations.Holds)
    (hP : InfiniteLattice.CutoffCovering.CoveringIdentification)
    (hW : InfiniteLattice.PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits)
    (hCh : TotalDensities.ComponentsAreLimitsOfStates) : ShortDistanceLawAtFewPoints.Statement := by
  have h₁ := hG _ (momentBounds_at_trajectory_couplings (eventually_momentBounds hAt hIn hPts) hRet)
  have h₂ := TotalDensities.HoldsAtAdmissibleParameters.and (TotalDensities.HoldsAtAdmissibleParameters.and h₁ hRR)
    (TotalDensities.HoldsAtAdmissibleParameters.and (couplingAtScaleHolds_of hD) hCh)
  refine TotalDensities.HoldsAtAdmissibleParameters.mono h₂ fun T y hDr h => ?_
  obtain ⟨⟨a₁, a₂⟩, a₃, a₄⟩ := h
  obtain ⟨y₁, f₁⟩ := a₁ (2 * T.B) le_rfl
  obtain ⟨y₂, f₂⟩ := a₂ (2 * T.B) le_rfl
  obtain ⟨y₃, f₃⟩ := a₃ (2 * T.B) le_rfl
  obtain ⟨y₄, f₄⟩ := a₄
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max y (T.side : ℝ)), fun g hg hy Q S hQ n _ hn h8 X => ?_⟩
  have b₀ : max (max y₁ y₂) (max y₃ y₄) ≤ g ^ (-2 : ℤ) := (le_max_left _ _).trans hy
  have b₁ : y₁ ≤ g ^ (-2 : ℤ) := ((le_max_left _ _).trans (le_max_left _ _)).trans b₀
  have b₂ : y₂ ≤ g ^ (-2 : ℤ) := ((le_max_right _ _).trans (le_max_left _ _)).trans b₀
  have b₃ : y₃ ≤ g ^ (-2 : ℤ) := ((le_max_left _ _).trans (le_max_right _ _)).trans b₀
  have b₄ : y₄ ≤ g ^ (-2 : ℤ) := ((le_max_right _ _).trans (le_max_right _ _)).trans b₀
  have b₅ : y ≤ g ^ (-2 : ℤ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have b₆ : (T.side : ℝ) ≤ g ^ (-2 : ℤ) := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hgy : y ≤ (g ^ 2)⁻¹ := by
    have e : g ^ (-2 : ℤ) = (g ^ 2)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rwa [e] at b₅
  obtain ⟨-, -, Kr, hKr⟩ := f₁ g hg b₁
  obtain ⟨e, -, hdist⟩ := f₃ g hg b₃
  have hS : Conventions.IsAdmissibleBlockingFactor T.side := ⟨hDr.L_odd, le_trans (by norm_num) hDr.L_ge⟩
  exact law_at_admissible_parameters hCum hLat hDr hKr hg hgy b₆ (fun K β ν hβ hv => torusLimit_of_infiniteVolume hP hW hS K hβ hv) (f₂ g hg b₂)
    hdist (f₄ g hg b₄) Q S hQ n hn h8 X
end YangMills.Construction.TotalDensitySystem
end
