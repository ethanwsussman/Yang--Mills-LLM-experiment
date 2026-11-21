import YangMills.Construction.Lattice.AveragesAndContourVariablesOfTheIdentityConfigurationProof
import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.FirstDerivativeOfTheAverageLogarithm
import YangMills.Construction.Lattice.FirstDerivativeOfTheContourVariables
import YangMills.Construction.Matrices.ExpLogEstimates
import Mathlib
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BlockAverageLogDeriv
open Matrices
variable {L m K n : ℕ}
private theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
private theorem logSeries_hasFDerivAt_one (hE : ComplexMatrix2.ExpLogEstimates) :
    HasFDerivAt ComplexMatrix2.logSeries (ContinuousLinearMap.id ℂ ComplexMatrix2) 1 := by
  have key : ∀ h : ComplexMatrix2, ‖h‖ < 1 →
      ‖ComplexMatrix2.logSeries (1 + h) - h‖ ≤ ‖h‖ / (1 - ‖h‖) * ‖h‖ := by
    intro h hh
    have hA : (1 + h) - 1 = h := add_sub_cancel_left 1 h
    have hb := (hE.2.2.2.2.2.2.2.2.1 ‖h‖ (1 + h) 1 (norm_nonneg _) hh
      (by rw [ComplexMatrix2.operatorNorm, hA])
      (by rw [ComplexMatrix2.operatorNorm, sub_self, norm_zero]; exact norm_nonneg _)).2.2.1
    rw [logSeries_one, sub_zero, hA] at hb
    exact hb
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.isLittleO_iff.mpr fun ε hε => ?_
  have hr : 0 < min (1 / 2 : ℝ) (ε / 2) := lt_min (by norm_num) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ComplexMatrix2) hr] with h hh
  rw [mem_ball_zero_iff] at hh
  have h1 : ‖h‖ < 1 / 2 := lt_of_lt_of_le hh (min_le_left _ _)
  have h2 : ‖h‖ < ε / 2 := lt_of_lt_of_le hh (min_le_right _ _)
  have hb := key h (by linarith)
  have hq : ‖h‖ / (1 - ‖h‖) ≤ ε := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg h]
  simp only [logSeries_one, sub_zero, ContinuousLinearMap.id_apply]
  exact hb.trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
private theorem logSeries_comp_hasDerivAt (hE : ComplexMatrix2.ExpLogEstimates)
    {f : ℂ → ComplexMatrix2} {D : ComplexMatrix2} (h0 : f 0 = 1) (hf : HasDerivAt f D 0) :
    HasDerivAt (fun t => ComplexMatrix2.logSeries (f t)) D 0 := by
  have h1 : HasFDerivAt ComplexMatrix2.logSeries
      (ContinuousLinearMap.id ℂ ComplexMatrix2) (f 0) := by
    rw [h0]
    exact logSeries_hasFDerivAt_one hE
  exact (h1.comp_hasDerivAt (0 : ℂ) hf).congr_deriv (by simp)
private theorem matExp_comp_hasDerivAt {f : ℂ → ComplexMatrix2} {D : ComplexMatrix2}
    (h0 : f 0 = 0) (hf : HasDerivAt f D 0) :
    HasDerivAt (fun t => ComplexMatrix2.matExp (f t)) D 0 := by
  have h1 : HasFDerivAt (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2)
      (1 : ComplexMatrix2 →L[ℂ] ComplexMatrix2) (f 0) := by
    rw [h0]
    exact hasFDerivAt_exp_zero
  exact (h1.comp_hasDerivAt (0 : ℂ) hf).congr_deriv (by simp)
private theorem inv_comp_hasDerivAt {f : ℂ → ComplexMatrix2} {D : ComplexMatrix2}
    (h0 : f 0 = 1) (hf : HasDerivAt f D 0) :
    HasDerivAt (fun t => (f t)⁻¹) (-D) 0 := by
  have h1 : HasFDerivAt (Ring.inverse : ComplexMatrix2 → ComplexMatrix2)
      (-ContinuousLinearMap.mulLeftRight ℂ ComplexMatrix2 1 1) (f 0) := by
    rw [h0]
    simpa using hasFDerivAt_ringInverse (𝕜 := ℂ) (1 : ComplexMatrix2ˣ)
  have h2 := h1.comp_hasDerivAt (0 : ℂ) hf
  have h3 : (fun t => (f t)⁻¹) = Ring.inverse ∘ f := by
    funext t
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [h3]
  simpa using h2
private theorem defect_hasDerivAt {f g u v : ℂ → ComplexMatrix2} {f' g' u' v' : ComplexMatrix2}
    (f0 : f 0 = 1) (g0 : g 0 = 1) (u0 : u 0 = 1) (v0 : v 0 = 1) (hf : HasDerivAt f f' 0)
    (hg : HasDerivAt g g' 0) (hu : HasDerivAt u u' 0) (hv : HasDerivAt v v' 0) :
    HasDerivAt (fun t => f t * g t * (u t)⁻¹ * (v t)⁻¹) (f' + g' - u' - v') 0 := by
  have h1 := ((hf.mul hg).mul (inv_comp_hasDerivAt u0 hu)).mul (inv_comp_hasDerivAt v0 hv)
  refine h1.congr_deriv ?_
  simp only [Pi.mul_apply, f0, g0, u0, v0, inv_one, mul_one, one_mul]
  abel
private theorem eval_smul {P : SymmetricBondSet L m K n} (t : ℂ) (a : LieBondField P)
    (b : BondAtLevel L m K n) : ((t • a).eval b : ComplexMatrix2) = t • (a.eval b : ComplexMatrix2) := by
  simp only [LieBondField.eval]
  split_ifs <;> simp
private theorem eval_of_not_positive {P : SymmetricBondSet L m K n} (a : LieBondField P)
    {b : BondAtLevel L m K n} (h : ¬ b.IsPositivelyOriented) : a.eval b = -a.eval b.opposite := by
  have hr : b.opposite.IsPositivelyOriented := Bond.opposite_isPositivelyOriented h
  have hrr : b.opposite.opposite = b := rfl
  by_cases hp : b.opposite ∈ P.bonds
  · have h1 : a.eval b.opposite = a ⟨b.opposite, hp, hr⟩ := a.eval_of_positive ⟨b.opposite, hp, hr⟩
    have h2 : a.eval b = -a ⟨b.opposite, hp, hr⟩ := by
      simp only [LieBondField.eval]
      rw [dif_neg (fun x => h x.2), dif_pos ⟨hp, hr⟩]
    rw [h1, h2]
  · have h1 : a.eval b = 0 := by
      simp only [LieBondField.eval]
      rw [dif_neg (fun x => h x.2), dif_neg (fun x => hp x.1)]
    have h2 : a.eval b.opposite = 0 := by
      simp only [LieBondField.eval]
      rw [dif_neg (fun x => hp x.1), dif_neg (fun x => h (hrr ▸ x.2))]
    rw [h1, h2, neg_zero]
private theorem eval_zero_smul {P : SymmetricBondSet L m K n} (a : LieBondField P)
    (b : BondAtLevel L m K n) : (((0 : ℂ) • a).eval b : ComplexMatrix2) = 0 := by
  rw [eval_smul, zero_smul]
private theorem expBondField_zero (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) :
    expBondField c ((0 : ℂ) • a) = trivialGaugeField := by
  funext b
  have he : ComplexMatrix2.matExp 0 = 1 := NormedSpace.exp_zero
  simp only [expBondField, twistedConfig, expTwist, eval_zero_smul,
    trivialGaugeField, smul_zero, mul_one, he, inv_one, ite_self]
private theorem expBondField_hasDerivAt (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (b : BondAtLevel L m K n) :
    HasDerivAt (fun t : ℂ => expBondField c (t • a) b) (Complex.I • (a.eval b : ComplexMatrix2)) 0 := by
  have line : ∀ b' : BondAtLevel L m K n, HasDerivAt (fun t : ℂ =>
      ComplexMatrix2.matExp (Complex.I • ((t • a).eval b' : ComplexMatrix2)) * trivialGaugeField b')
      (Complex.I • (a.eval b' : ComplexMatrix2)) 0 := by
    intro b'
    have hf : HasDerivAt (fun t : ℂ => t • (Complex.I • (a.eval b' : ComplexMatrix2)))
        (Complex.I • (a.eval b' : ComplexMatrix2)) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const (Complex.I • (a.eval b' : ComplexMatrix2))
    have h1 := matExp_comp_hasDerivAt
      (f := fun t : ℂ => t • (Complex.I • (a.eval b' : ComplexMatrix2))) (by simp) hf
    have h2 : (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • ((t • a).eval b' : ComplexMatrix2)) *
        trivialGaugeField b') =
        fun t : ℂ => ComplexMatrix2.matExp (t • (Complex.I • (a.eval b' : ComplexMatrix2))) := by
      funext t
      rw [eval_smul, smul_comm]
      simp [trivialGaugeField]
    rw [h2]
    exact h1
  by_cases hb : b.IsPositivelyOriented
  · simp only [expBondField, twistedConfig, expTwist, if_pos hb]
    exact line b
  · simp only [expBondField, twistedConfig, expTwist, if_neg hb]
    have h1 := inv_comp_hasDerivAt (by
      simp only [eval_zero_smul, smul_zero, trivialGaugeField, mul_one]
      exact NormedSpace.exp_zero) (line b.opposite)
    refine h1.congr_deriv ?_
    rw [eval_of_not_positive a hb]
    simp
private theorem pathHolonomy_trivial {j : ℤ} (Γ : List (Bond L m j)) :
    pathHolonomy trivialGaugeField Γ = 1 := by apply _root_.YangMills.SharedProofs.p62034 <;> assumption
private theorem pathHolonomy_hasDerivAt {j : ℤ} {W : ℂ → Bond L m j → ComplexMatrix2}
    {D : Bond L m j → ComplexMatrix2} (h0 : W 0 = trivialGaugeField)
    (hd : ∀ b, HasDerivAt (fun t => W t b) (D b) 0) (Γ : List (Bond L m j)) :
    HasDerivAt (fun t => pathHolonomy (W t) Γ) (bondFormSumAlong D Γ) 0 := by
  induction Γ with
  | nil => simpa [pathHolonomy, bondFormSumAlong] using hasDerivAt_const (0 : ℂ) (1 : ComplexMatrix2)
  | cons b Γ ih =>
    have h1 := (hd b).mul ih
    have hb : W 0 b = 1 := by rw [h0]; rfl
    have hΓ : pathHolonomy (W 0) Γ = 1 := by rw [h0]; exact pathHolonomy_trivial Γ
    refine h1.congr_deriv ?_
    simp only [hb, hΓ, mul_one, one_mul, bondFormSumAlong, List.map_cons, List.sum_cons]
private theorem bondFormSumAlong_smul {j : ℤ} (z : ℂ) (A : Bond L m j → ComplexMatrix2)
    (Γ : List (Bond L m j)) :
    bondFormSumAlong (fun b => z • A b) Γ = z • bondFormSumAlong A Γ := by
  induction Γ with
  | nil => simp [bondFormSumAlong]
  | cons b Γ ih =>
    simp only [bondFormSumAlong, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, smul_add]
private theorem complexLogMean_const_one (hM : Averaging.IdentityFamilyMeanIsOne) {ι : Type*}
    [Fintype ι] [Nonempty ι] : complexLogMean (fun _ : ι => (1 : ComplexMatrix2)) = 1 := by apply _root_.YangMills.SharedProofs.p63807 <;> assumption
private theorem contourHolonomy_trivial (hM : Averaging.IdentityFamilyMeanIsOne)
    (s : AveragingScheme) {j j' : ℤ} (y : Site L m j) (x : Site L m j') :
    contourHolonomy s trivialGaugeField y x = 1 := by
  cases s with
  | centred =>
    have hne : Nonempty (AxisOrdering y x) := ⟨(Finset.equivFin _).symm⟩
    have hv : contourHolonomies (trivialGaugeField : Bond L m j' → ComplexMatrix2) y x =
        fun _ => 1 := by
      funext σ
      exact pathHolonomy_trivial _
    change complexLogMean (contourHolonomies trivialGaugeField y x) = 1
    rw [hv]
    exact complexLogMean_const_one hM
  | cornered => exact pathHolonomy_trivial _
private theorem ncard_sitesInBlock (hP : BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j j' : ℤ} (hj : -(m : ℤ) ≤ j)
    (hj' : j' = j + ((1 : ℕ) : ℤ)) (y : Site L m j) : (sitesInBlock j' y).ncard = L ^ 4 := by
  subst hj'
  have himg : Subtype.val '' (sitesInBlock (j + ((1 : ℕ) : ℤ)) y) = refinedBlock 1 y := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hp.2⟩, hp, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
  simpa using ((hP L m hL hm j 1 0 hj).1 y).2.2
private theorem shiftAcross_mem (hL : 0 < L) {j j' : ℤ} (hj' : j' = j + ((1 : ℕ) : ℤ))
    (c : Bond L m j) {x : Site L m j'} (hx : x ∈ sitesInBlock j' c.source) :
    shiftAcross c x ∈ sitesInBlock j' c.target := by
  subst hj'
  have hle : j ≤ j + ((1 : ℕ) : ℤ) := by simp
  have hcoe : (((c.target - c.source).toSublattice (j + ((1 : ℕ) : ℤ)) :
      Site L m (j + ((1 : ℕ) : ℤ))) : FourTorus L m) =
      ((c.target - c.source : Site L m j) : FourTorus L m) :=
    Classical.epsilon_spec (p := fun z : Site L m (j + ((1 : ℕ) : ℤ)) => (z : FourTorus L m) =
      ((c.target - c.source : Site L m j) : FourTorus L m))
      ⟨⟨_, sublattice_mono hL m hle (c.target - c.source).2⟩, rfl⟩
  have hdiff : ((shiftAcross c x : Site L m (j + ((1 : ℕ) : ℤ))) : FourTorus L m) -
      (c.target : FourTorus L m) = (x : FourTorus L m) - (c.source : FourTorus L m) := by
    simp only [shiftAcross, AddSubgroup.coe_add, hcoe, AddSubgroup.coe_sub]
    abel
  refine ⟨?_, (shiftAcross c x).2⟩
  change TorusMetric.torusSupNorm (_ - _) ≤ _
  rw [hdiff]
  exact hx.1
theorem hasDerivBlockAverageLogAtZero (hC : ContourHolonomyDerivative.Statement)
    (hM : Averaging.IdentityFamilyMeanIsOne) (hP : BlockPartition.Properties)
    (hE : ComplexMatrix2.ExpLogEstimates) : HasDerivBlockAverageLogAtZero := by
  intro L hL m K n hm hn s c hc a
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hd : levelDepth K n = levelDepth K (n + 1) + ((1 : ℕ) : ℤ) := by
    simp only [levelDepth]
    push_cast
    ring
  have hj : -(m : ℤ) ≤ levelDepth K (n + 1) := by
    simp only [levelDepth]
    push_cast
    omega
  have hN' : (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)).ncard = L ^ 4 :=
    ncard_sitesInBlock hP hL hm hj hd c.source
  have hfin : (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hN']; positivity)
  have hN : hfin.toFinset.card = L ^ 4 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hN'
  have hwN : inverseFourthPowerWeight L * ((hfin.toFinset.card : ℕ) : ℂ) = 1 := by
    have hne : (L : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
    have h1 : ((L : ℝ) ^ (-4 : ℤ)) * (L : ℝ) ^ 4 = 1 := by
      rw [zpow_neg]
      have : ((L : ℝ) ^ (4 : ℤ)) = (L : ℝ) ^ 4 := by norm_cast
      rw [this]
      exact inv_mul_cancel₀ (pow_ne_zero _ hne)
    rw [hN, inverseFourthPowerWeight]
    exact_mod_cast h1
  have W0 : expBondField c ((0 : ℂ) • a) = trivialGaugeField := expBondField_zero c a
  have hol : ∀ Γ : List (BondAtLevel L m K n),
      HasDerivAt (fun t : ℂ => pathHolonomy (expBondField c (t • a)) Γ)
        (Complex.I • bondFormSumAlong (LieBondField.matrixValues a) Γ) 0 := by
    intro Γ
    have h1 := pathHolonomy_hasDerivAt (W := fun t : ℂ => expBondField c (t • a))
      (D := fun b => Complex.I • (a.eval b : ComplexMatrix2)) W0 (expBondField_hasDerivAt c a) Γ
    exact h1.congr_deriv (bondFormSumAlong_smul Complex.I (LieBondField.matrixValues a) Γ)
  have hol0 : ∀ Γ : List (BondAtLevel L m K n),
      pathHolonomy (expBondField c ((0 : ℂ) • a)) Γ = 1 := by
    intro Γ
    rw [W0]
    exact pathHolonomy_trivial Γ
  have con0 : ∀ (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n),
      contourHolonomy s (expBondField c ((0 : ℂ) • a)) y x = 1 := by
    intro y x
    rw [W0]
    exact contourHolonomy_trivial hM s y x
  set aT : ComplexMatrix2 := bondFormSumAlong (LieBondField.matrixValues a)
    (axialPath (schemeBaseSite s (levelDepth K n) c.source)
      (schemeBaseSite s (levelDepth K n) c.target)) with haT
  have hT : HasDerivAt (fun t : ℂ => baseTransport s (expBondField c (t • a)) c)
      (Complex.I • aT) 0 := hol _
  have hT0 : baseTransport s (expBondField c ((0 : ℂ) • a)) c = 1 := hol0 _
  have elt0 : ∀ x : SiteAtLevel L m K n,
      localDefect s (expBondField c ((0 : ℂ) • a)) c x = 1 := by
    intro x
    simp only [localDefect, con0, hol0, hT0, inv_one, mul_one]
  have elt : ∀ x ∈ hfin.toFinset, HasDerivAt
      (fun t : ℂ => ComplexMatrix2.logSeries (localDefect s (expBondField c (t • a)) c x))
      (Complex.I • ((contourFormMean s (LieBondField.matrixValues a) c.source x +
        bondFormSumAlong (LieBondField.matrixValues a) (crossingPath c x) -
        contourFormMean s (LieBondField.matrixValues a) c.target (shiftAcross c x)) - aT)) 0 := by
    intro x hx
    have hx' : x ∈ sitesInBlock (levelDepth K n) c.source := hfin.mem_toFinset.mp hx
    have hx'' : shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target :=
      shiftAcross_mem hLpos hd c hx'
    have h1 := defect_hasDerivAt (con0 c.source x) (hol0 (crossingPath c x))
      (con0 c.target (shiftAcross c x)) hT0
      (hC L hL m K n hm hn s c hc a c.source (Or.inl rfl) x hx') (hol (crossingPath c x))
      (hC L hL m K n hm hn s c hc a c.target (Or.inr rfl) (shiftAcross c x) hx'') hT
    refine logSeries_comp_hasDerivAt hE (elt0 x) (h1.congr_deriv ?_)
    simp only [smul_sub, smul_add]
    rfl
  have hsum := HasDerivAt.fun_sum elt
  have hexp := matExp_comp_hasDerivAt (f := fun t : ℂ => inverseFourthPowerWeight L •
    ∑ x ∈ hfin.toFinset, ComplexMatrix2.logSeries (localDefect s (expBondField c (t • a)) c x))
    (by simp only [elt0, logSeries_one, Finset.sum_const_zero, smul_zero])
    (hsum.const_smul (inverseFourthPowerWeight L))
  have hexp0 : ComplexMatrix2.matExp (inverseFourthPowerWeight L • ∑ x ∈ hfin.toFinset,
      ComplexMatrix2.logSeries (localDefect s (expBondField c ((0 : ℂ) • a)) c x)) = 1 := by
    simp only [elt0, logSeries_one, Finset.sum_const_zero, smul_zero]
    simp
  have hav0 : schemeBlockAverage s (expBondField c ((0 : ℂ) • a)) c = 1 := by
    simp only [schemeBlockAverage, if_pos hc, positiveBondAverage,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [hexp0, hT0, one_mul]
  have hav := hexp.mul hT
  have hav' : (fun t : ℂ => schemeBlockAverage s (expBondField c (t • a)) c) =
      (fun t : ℂ => ComplexMatrix2.matExp (inverseFourthPowerWeight L • ∑ x ∈ hfin.toFinset,
        ComplexMatrix2.logSeries (localDefect s (expBondField c (t • a)) c x))) *
      fun t : ℂ => baseTransport s (expBondField c (t • a)) c := by
    funext t
    simp only [schemeBlockAverage, if_pos hc, positiveBondAverage,
      finsum_mem_eq_finite_toFinset_sum _ hfin, Pi.mul_apply]
  rw [← hav'] at hav
  have hlog := logSeries_comp_hasDerivAt hE
    (f := fun t : ℂ => schemeBlockAverage s (expBondField c (t • a)) c) hav0 hav
  refine (hlog.const_smul Complex.I⁻¹).congr_deriv ?_
  rw [hexp0, hT0, mul_one, one_mul]
  set S := ∑ x ∈ hfin.toFinset, (contourFormMean s (LieBondField.matrixValues a) c.source x +
    bondFormSumAlong (LieBondField.matrixValues a) (crossingPath c x) -
    contourFormMean s (LieBondField.matrixValues a) c.target (shiftAcross c x)) with hS
  have e1 : ∑ x ∈ hfin.toFinset,
      Complex.I • ((contourFormMean s (LieBondField.matrixValues a) c.source x +
      bondFormSumAlong (LieBondField.matrixValues a) (crossingPath c x) -
      contourFormMean s (LieBondField.matrixValues a) c.target (shiftAcross c x)) - aT) =
      Complex.I • (S - ((hfin.toFinset.card : ℕ) : ℂ) • aT) := by
    rw [← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have e2 : inverseFourthPowerWeight L • ((hfin.toFinset.card : ℕ) : ℂ) • aT = aT := by
    rw [smul_smul, hwN, one_smul]
  have e3 : linearSchemeAverage s (LieBondField.matrixValues a) c =
      inverseFourthPowerWeight L • S := by
    rw [linearSchemeAverage, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [e1, e3, smul_comm (inverseFourthPowerWeight L) Complex.I,
    smul_sub (inverseFourthPowerWeight L), e2, ← smul_add,
    sub_add_cancel, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
end YangMills.Construction.PeriodicLattice.BlockAverageLogDeriv
