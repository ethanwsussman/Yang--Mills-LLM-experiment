import YangMills.Construction.InfiniteLattice.PropertiesOfTheSixteenFamiliesProof
import YangMills.Construction.Towers.SecondDerivativesOfTheLogarithmicDensity
import YangMills.Construction.Towers.SquareSummableFunctionsOnTheUnitLatticeProof
import YangMills.Construction.Towers.TheSumOverThePointsOfTheSecondDerivativesOfTheLogarithmicDensity
import YangMills.Construction.Towers.VariationsOfALocalFamily
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity
open YangMills.Construction.Tower.LocalFamilies YangMills.Construction.OneLoopNotation
open YangMills.Construction.TorusMetric (euclidNormVec)
open Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
namespace HessianSum
variable {J : Type}
theorem matrixEntry_comp (hE : MatrixEntryProperties J) (A B : BddOp (IndexL2 J))
    (ι' ι : J) : matrixEntry (A.comp B) ι' ι = ∑' κ, matrixEntry A ι' κ * matrixEntry B κ ι :=
  ((hE A).2 (B (basisVec ι)) ι').2
def SupportedOn (S : Finset J) (Y : BddOp (IndexL2 J)) : Prop :=
  ∀ i j, (i ∉ S ∨ j ∉ S) → matrixEntry Y i j = 0
theorem matrixEntry_sandwich (hE : MatrixEntryProperties J) {S : Finset J}
    {Y : BddOp (IndexL2 J)} (hY : SupportedOn S Y)
    (E F : BddOp (IndexL2 J)) (ι' ι : J) :
    matrixEntry (E.comp (Y.comp F)) ι' ι =
      ∑ i ∈ S, ∑ j ∈ S, matrixEntry E ι' i * matrixEntry Y i j * matrixEntry F j ι := by
  have hYF : ∀ i, matrixEntry (Y.comp F) i ι = ∑ j ∈ S, matrixEntry Y i j * matrixEntry F j ι := by
    intro i
    rw [matrixEntry_comp hE, tsum_eq_sum (s := S) fun j hj => by rw [hY i j (Or.inr hj), zero_mul]]
  rw [matrixEntry_comp hE, tsum_eq_sum (s := S) fun i hi => by
    rw [hYF, Finset.sum_eq_zero (fun j _ => by rw [hY i j (Or.inl hi), zero_mul]), mul_zero]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hYF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
def entryCLM (j i : J) : BddOp (IndexL2 J) →L[ℂ] ℂ :=
  (innerSL ℂ (basisVec j : IndexL2 J)).comp
    (ContinuousLinearMap.apply ℂ (IndexL2 J) (basisVec i : IndexL2 J))
theorem entryCLM_apply (hE : MatrixEntryProperties J) (G : BddOp (IndexL2 J))
    (j i : J) : entryCLM j i G = matrixEntry G j i := by
  rw [((hE G).1 j i).1]
  simp [entryCLM]
def entryPairing (S : Finset J) (Y : BddOp (IndexL2 J)) :
    BddOp (IndexL2 J) →L[ℂ] ℂ :=
  ∑ i ∈ S, ∑ j ∈ S, matrixEntry Y i j • entryCLM j i
theorem entryPairing_apply (hE : MatrixEntryProperties J) (S : Finset J)
    (Y G : BddOp (IndexL2 J)) :
    entryPairing S Y G = ∑ i ∈ S, ∑ j ∈ S, matrixEntry Y i j * matrixEntry G j i := by
  simp [entryPairing, entryCLM_apply hE]
def entryMass (S : Finset J) (Y : BddOp (IndexL2 J)) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, ‖matrixEntry Y i j‖
theorem entryMass_nonneg (S : Finset J) (Y : BddOp (IndexL2 J)) : 0 ≤ entryMass S Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem norm_entryPairing_le (hE : MatrixEntryProperties J) (S : Finset J)
    (Y G : BddOp (IndexL2 J)) : ‖entryPairing S Y G‖ ≤ entryMass S Y * ‖G‖ := by
  rw [entryPairing_apply hE, entryMass, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((hE G).1 j i).2 (norm_nonneg _)
theorem finset_sum_four_comm (S : Finset J) (f : J → J → J → J → ℂ) :
    ∑ i ∈ S, ∑ j ∈ S, ∑ k ∈ S, ∑ l ∈ S, f i j k l =
      ∑ k ∈ S, ∑ l ∈ S, ∑ i ∈ S, ∑ j ∈ S, f i j k l := by
  calc _ = ∑ i ∈ S, ∑ k ∈ S, ∑ j ∈ S, ∑ l ∈ S, f i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ S, ∑ i ∈ S, ∑ j ∈ S, ∑ l ∈ S, f i j k l := Finset.sum_comm
    _ = ∑ k ∈ S, ∑ i ∈ S, ∑ l ∈ S, ∑ j ∈ S, f i j k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun k _ => Finset.sum_comm
theorem entryPairing_cyclic (hE : MatrixEntryProperties J) {S : Finset J}
    {Y Y' : BddOp (IndexL2 J)} (hY : SupportedOn S Y) (hY' : SupportedOn S Y')
    (G G' : BddOp (IndexL2 J)) :
    entryPairing S Y (G.comp (Y'.comp G')) = entryPairing S Y' (G'.comp (Y.comp G)) := by
  rw [entryPairing_apply hE, entryPairing_apply hE]
  simp only [matrixEntry_sandwich hE hY, matrixEntry_sandwich hE hY', Finset.mul_sum]
  rw [finset_sum_four_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
theorem hasSum_norm_sq (v : IndexL2 J) : HasSum (fun ι => ‖v ι‖ ^ 2) (‖v‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) v
  simpa using h
theorem norm_basisVec (i : J) : ‖(basisVec i : IndexL2 J)‖ = 1 := by apply _root_.YangMills.Construction.Tower.UnitLatticeL2.L2Steps.norm_basisVec <;> assumption
theorem norm_matrixEntry_eq_adjoint (hE : MatrixEntryProperties J)
    (F : BddOp (IndexL2 J)) (j ι : J) :
    ‖matrixEntry F j ι‖ = ‖(ContinuousLinearMap.adjoint F (basisVec j)) ι‖ := by
  classical
  rw [((hE F).1 j ι).1, ← ContinuousLinearMap.adjoint_inner_left]
  unfold basisVec
  rw [lp.inner_single_right]
  simp
theorem summable_mul_norm_entries (hE : MatrixEntryProperties J)
    (E F : BddOp (IndexL2 J)) (i j : J) :
    Summable (fun ι => ‖matrixEntry E ι i‖ * ‖matrixEntry F j ι‖) ∧
      ∑' ι, ‖matrixEntry E ι i‖ * ‖matrixEntry F j ι‖ ≤ (‖E‖ ^ 2 + ‖F‖ ^ 2) / 2 := by
  obtain ⟨u, hu⟩ : ∃ u : IndexL2 J, u = E (basisVec i) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : IndexL2 J, v = ContinuousLinearMap.adjoint F (basisVec j) := ⟨_, rfl⟩
  have hs : HasSum (fun ι => (‖u ι‖ ^ 2 + ‖v ι‖ ^ 2) / 2) ((‖u‖ ^ 2 + ‖v‖ ^ 2) / 2) :=
    ((hasSum_norm_sq u).add (hasSum_norm_sq v)).div_const 2
  have hle : ∀ ι, ‖matrixEntry E ι i‖ * ‖matrixEntry F j ι‖ ≤ (‖u ι‖ ^ 2 + ‖v ι‖ ^ 2) / 2 := by
    intro ι
    rw [norm_matrixEntry_eq_adjoint hE F j ι, ← hv]
    have h1 : matrixEntry E ι i = u ι := by rw [hu]; rfl
    rw [h1]
    nlinarith [sq_nonneg (‖u ι‖ - ‖v ι‖)]
  have h0 : ∀ ι, 0 ≤ ‖matrixEntry E ι i‖ * ‖matrixEntry F j ι‖ := fun _ => by positivity
  have hS := Summable.of_nonneg_of_le h0 hle hs.summable
  refine ⟨hS, (hS.tsum_le_tsum hle hs.summable).trans ?_⟩
  rw [hs.tsum_eq]
  have hun : ‖u‖ ≤ ‖E‖ := by
    have := E.le_opNorm (basisVec i)
    rwa [norm_basisVec, mul_one, ← hu] at this
  have hvn : ‖v‖ ≤ ‖F‖ := by
    have := (ContinuousLinearMap.adjoint F).le_opNorm (basisVec j)
    rwa [norm_basisVec, mul_one, ← hv, LinearIsometryEquiv.norm_map] at this
  have h1 : ‖u‖ ^ 2 ≤ ‖E‖ ^ 2 := by gcongr
  have h2 : ‖v‖ ^ 2 ≤ ‖F‖ ^ 2 := by gcongr
  linarith
theorem diag_sandwich (hE : MatrixEntryProperties J) {S : Finset J}
    {Y : BddOp (IndexL2 J)} (hY : SupportedOn S Y)
    (E F : BddOp (IndexL2 J)) :
    HasSum (fun ι => matrixEntry (E.comp (Y.comp F)) ι ι) (entryPairing S Y (F.comp E)) ∧
      Summable (fun ι => ‖matrixEntry (E.comp (Y.comp F)) ι ι‖) ∧
      ∑' ι, ‖matrixEntry (E.comp (Y.comp F)) ι ι‖ ≤ entryMass S Y * ((‖E‖ ^ 2 + ‖F‖ ^ 2) / 2) := by
  have hterm : ∀ i j, HasSum (fun ι => matrixEntry E ι i * matrixEntry Y i j * matrixEntry F j ι)
      (matrixEntry Y i j * matrixEntry (F.comp E) j i) := by
    intro i j
    have h1 : Summable fun ι => matrixEntry F j ι * matrixEntry E ι i :=
      Summable.of_norm ((hE F).2 (E (basisVec i)) j).1
    have h2 := h1.hasSum.mul_left (matrixEntry Y i j)
    rw [← matrixEntry_comp hE] at h2
    have e : (fun ι => matrixEntry E ι i * matrixEntry Y i j * matrixEntry F j ι) =
        fun ι => matrixEntry Y i j * (matrixEntry F j ι * matrixEntry E ι i) := funext fun ι => by ring
    rw [e]
    exact h2
  have hsum : HasSum (fun ι => matrixEntry (E.comp (Y.comp F)) ι ι) (entryPairing S Y (F.comp E)) := by
    rw [entryPairing_apply hE]
    simp only [matrixEntry_sandwich hE hY]
    exact hasSum_sum fun i _ => hasSum_sum fun j _ => hterm i j
  have hD : HasSum (fun ι => ∑ i ∈ S, ∑ j ∈ S, ‖matrixEntry Y i j‖ * (‖matrixEntry E ι i‖ * ‖matrixEntry F j ι‖))
      (∑ i ∈ S, ∑ j ∈ S, ‖matrixEntry Y i j‖ * ∑' ι, ‖matrixEntry E ι i‖ * ‖matrixEntry F j ι‖) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ => (summable_mul_norm_entries hE E F i j).1.hasSum.mul_left _
  have hle : ∀ ι, ‖matrixEntry (E.comp (Y.comp F)) ι ι‖ ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖matrixEntry Y i j‖ * (‖matrixEntry E ι i‖ * ‖matrixEntry F j ι‖) := by
    intro ι
    rw [matrixEntry_sandwich hE hY]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul]
    exact le_of_eq (by ring)
  have hS := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hD.summable
  refine ⟨hsum, hS, (hS.tsum_le_tsum hle hD.summable).trans ?_⟩
  rw [hD.tsum_eq, entryMass, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (summable_mul_norm_entries hE E F i j).2 (norm_nonneg _)
theorem castVec_injective : Function.Injective PeriodicOperators.castVec := by apply _root_.YangMills.Construction.NormalFamilies.Properties.castVec_injective <;> assumption
theorem traceAt_eq_tsum {position : J → InfiniteLattice.AmbientSpace} {p : J → Fin 4 → ℤ}
    (hp : ∀ ι, position ι = PeriodicOperators.castVec (p ι))
    (hfin : ∀ y, {ι | position ι = y}.Finite) (d : BddOp (IndexL2 J))
    (n : Fin 4 → ℤ) :
    traceAt position d (PeriodicOperators.castVec n) =
      ∑' ι : p ⁻¹' {n}, matrixEntry d ι ι := by
  classical
  have hset : {ι | position ι = PeriodicOperators.castVec n} = p ⁻¹' {n} := by
    ext ι
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, hp]
    exact castVec_injective.eq_iff
  have hf := hfin (PeriodicOperators.castVec n)
  unfold traceAt
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  have h2 : (p ⁻¹' {n}) = (↑hf.toFinset : Set J) := by
    rw [← hset]
    simp
  rw [h2]
  exact (Finset.tsum_subtype' _ _).symm
theorem hasSum_traceAt {position : J → InfiniteLattice.AmbientSpace} {p : J → Fin 4 → ℤ}
    (hp : ∀ ι, position ι = PeriodicOperators.castVec (p ι))
    (hfin : ∀ y, {ι | position ι = y}.Finite) (d : BddOp (IndexL2 J)) {t : ℂ}
    (ht : HasSum (fun ι => matrixEntry d ι ι) t) :
    HasSum (fun n => traceAt position d (PeriodicOperators.castVec n)) t := by
  have h := ht.tsum_fiberwise p
  simpa only [traceAt_eq_tsum hp hfin] using h
theorem sum_norm_traceAt_le {position : J → InfiniteLattice.AmbientSpace} {p : J → Fin 4 → ℤ}
    (hp : ∀ ι, position ι = PeriodicOperators.castVec (p ι))
    (hfin : ∀ y, {ι | position ι = y}.Finite) (d : BddOp (IndexL2 J))
    (hs : Summable fun ι => ‖matrixEntry d ι ι‖) (s : Finset (Fin 4 → ℤ)) :
    ∑ n ∈ s, ‖traceAt position d (PeriodicOperators.castVec n)‖ ≤
      ∑' ι, ‖matrixEntry d ι ι‖ := by
  have h := hs.hasSum.tsum_fiberwise p
  refine (Finset.sum_le_sum fun n _ => ?_).trans
    (sum_le_hasSum s (fun _ _ => tsum_nonneg fun _ => norm_nonneg _) h)
  rw [traceAt_eq_tsum hp hfin]
  exact norm_tsum_le_tsum_norm (hs.subtype _)
structure IsResolventCurve (R : ℝ → BddOp (IndexL2 J)) (a : ℝ) : Prop where
  pos : 0 < a
  norm_le : ∀ w, 0 ≤ w → ‖R w‖ ≤ (a + w)⁻¹
  resolvent_eq : ∀ w w', 0 ≤ w → 0 ≤ w' → R w' - R w = (w - w') • (R w' * R w)
theorem inverseOp_sub_inverseOp (X : BddOp (IndexL2 J)) (w w' : ℝ)
    (h : IsTwoSidedInverse (addScalar X w) (inverseOp (addScalar X w)))
    (h' : IsTwoSidedInverse (addScalar X w') (inverseOp (addScalar X w'))) :
    inverseOp (addScalar X w') - inverseOp (addScalar X w) =
      (w - w') • (inverseOp (addScalar X w') * inverseOp (addScalar X w)) := by
  obtain ⟨M, hM⟩ : ∃ M, M = addScalar X w := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M', M' = addScalar X w' := ⟨_, rfl⟩
  have hd : M - M' = (w - w') • (1 : BddOp (IndexL2 J)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [hM, hM']
    simp only [addScalar, scalarOp, sub_apply, add_apply, smul_apply, one_apply_eq_self,
      Complex.coe_smul, sub_smul]
    abel
  rw [← hM] at h
  rw [← hM'] at h'
  rw [← hM, ← hM']
  obtain ⟨R, hR⟩ : ∃ R, R = inverseOp M := ⟨_, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R', R' = inverseOp M' := ⟨_, rfl⟩
  rw [← hR] at h ⊢
  rw [← hR'] at h' ⊢
  calc R' - R = R' * (M * R) - (R' * M') * R := by rw [h.1, h'.2]; simp
    _ = R' * (M - M') * R := by noncomm_ring
    _ = _ := by rw [hd]; simp
theorem IsResolventCurve.continuousOn {R : ℝ → BddOp (IndexL2 J)} {a : ℝ}
    (h : IsResolventCurve R a) : ContinuousOn R (Set.Ici 0) := by
  have hb : ∀ w, 0 ≤ w → ‖R w‖ ≤ a⁻¹ := fun w hw =>
    (h.norm_le w hw).trans (inv_anti₀ h.pos (by linarith))
  have ha : 0 ≤ a⁻¹ := (inv_pos.2 h.pos).le
  refine (LipschitzOnWith.of_dist_le' (K := a⁻¹ * a⁻¹) fun x hx y hy => ?_).continuousOn
  rw [dist_eq_norm, h.resolvent_eq y x hy hx, norm_smul, Real.dist_eq, Real.norm_eq_abs, mul_comm,
    abs_sub_comm y x]
  exact mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
    (mul_le_mul (hb x hx) (hb y hy) (norm_nonneg _) ha)) (abs_nonneg _)
theorem IsResolventCurve.hasDerivAt {R : ℝ → BddOp (IndexL2 J)} {a : ℝ}
    (h : IsResolventCurve R a) {w : ℝ} (hw : 0 < w) : HasDerivAt R (-(R w * R w)) w := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : ContinuousAt R w := (h.continuousOn w hw.le).continuousAt (Ici_mem_nhds hw)
  have h1 : Tendsto (fun y => -(R y * R w)) (𝓝[≠] w) (𝓝 (-(R w * R w))) :=
    ((hc.tendsto.mul_const (R w)).neg).mono_left nhdsWithin_le_nhds
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hw)] with y hy hy0
  have hyw : y - w ≠ 0 := sub_ne_zero.2 hy
  have e : (y - w)⁻¹ * (w - y) = -1 := by
    field_simp
    ring
  rw [slope_def_module, h.resolvent_eq w y hw.le (le_of_lt hy0), smul_smul, e]
  simp
def resolventTrace (S : Finset J) (A V V' : BddOp (IndexL2 J))
    (R : ℝ → BddOp (IndexL2 J)) (w : ℝ) : ℂ :=
  entryPairing S A (R w) - entryPairing S V (R w * (V' * R w))
def secondResolventTrace (S : Finset J) (A V V' R : BddOp (IndexL2 J)) : ℂ :=
  entryPairing S A (R * R) - entryPairing S V (R * (V' * (R * R))) - entryPairing S V (R * R * (V' * R))
theorem hasDerivAt_resolventTrace {S : Finset J} (A V V' : BddOp (IndexL2 J))
    {R : ℝ → BddOp (IndexL2 J)} {a : ℝ} (h : IsResolventCurve R a) {w : ℝ}
    (hw : 0 < w) :
    HasDerivAt (resolventTrace S A V V' R) (-secondResolventTrace S A V V' (R w)) w := by
  have hR := h.hasDerivAt hw
  have hVR : HasDerivAt (fun y => V' * R y) (V' * -(R w * R w)) w := hR.const_mul V'
  have hP := hR.fun_mul hVR
  have h1 := ((entryPairing S A).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt w hR
  have h2 := ((entryPairing S V).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt w hP
  have h3 := h1.fun_sub h2
  refine HasDerivAt.congr_deriv (f := resolventTrace S A V V' R) h3 ?_
  simp only [secondResolventTrace, ContinuousLinearMap.coe_restrictScalars', map_add, map_neg,
    mul_neg, neg_mul]
  ring
theorem continuousOn_secondResolventTrace (S : Finset J) (A V V' : BddOp (IndexL2 J))
    {R : ℝ → BddOp (IndexL2 J)} {a : ℝ} (h : IsResolventCurve R a) :
    ContinuousOn (fun w => secondResolventTrace S A V V' (R w)) (Set.Ici 0) := by
  have hc := h.continuousOn
  have hRR := hc.mul hc
  have hVR : ContinuousOn (fun w => V' * R w) (Set.Ici 0) := continuousOn_const.mul hc
  have hVRR : ContinuousOn (fun w => V' * (R w * R w)) (Set.Ici 0) := continuousOn_const.mul hRR
  exact (((entryPairing S A).continuous.comp_continuousOn hRR).sub
    ((entryPairing S V).continuous.comp_continuousOn (hc.mul hVRR))).sub
    ((entryPairing S V).continuous.comp_continuousOn (hRR.mul hVR))
theorem continuousOn_resolventTrace (S : Finset J) (A V V' : BddOp (IndexL2 J))
    {R : ℝ → BddOp (IndexL2 J)} {a : ℝ} (h : IsResolventCurve R a) :
    ContinuousOn (resolventTrace S A V V' R) (Set.Ici 0) := by
  have hc := h.continuousOn
  have hVR : ContinuousOn (fun w => V' * R w) (Set.Ici 0) := continuousOn_const.mul hc
  exact ((entryPairing S A).continuous.comp_continuousOn hc).sub
    ((entryPairing S V).continuous.comp_continuousOn (hc.mul hVR))
theorem tendsto_resolventTrace (hE : MatrixEntryProperties J) (S : Finset J)
    (A V V' : BddOp (IndexL2 J)) {R : ℝ → BddOp (IndexL2 J)} {a : ℝ}
    (h : IsResolventCurve R a) : Tendsto (resolventTrace S A V V' R) atTop (𝓝 0) := by
  have hr : Tendsto (fun w : ℝ => (a + w)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop a tendsto_id)
  have hb : Tendsto (fun w : ℝ => entryMass S A * (a + w)⁻¹ +
      entryMass S V * ((a + w)⁻¹ * (‖V'‖ * (a + w)⁻¹))) atTop (𝓝 0) := by
    simpa using (hr.const_mul (entryMass S A)).add
      (((hr.mul (hr.const_mul ‖V'‖))).const_mul (entryMass S V))
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop 0] with w hw
  have hp : 0 ≤ (a + w)⁻¹ := inv_nonneg.2 (by linarith [h.pos])
  have hn := h.norm_le w hw
  have h1 : ‖entryPairing S A (R w)‖ ≤ entryMass S A * (a + w)⁻¹ :=
    (norm_entryPairing_le hE S A _).trans (mul_le_mul_of_nonneg_left hn (entryMass_nonneg _ _))
  have h3 : ‖R w * (V' * R w)‖ ≤ (a + w)⁻¹ * (‖V'‖ * (a + w)⁻¹) :=
    (norm_mul_le _ _).trans (mul_le_mul hn ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg _))) (norm_nonneg _) hp)
  have h2 : ‖entryPairing S V (R w * (V' * R w))‖ ≤
      entryMass S V * ((a + w)⁻¹ * (‖V'‖ * (a + w)⁻¹)) :=
    (norm_entryPairing_le hE S V _).trans (mul_le_mul_of_nonneg_left h3 (entryMass_nonneg _ _))
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)
def secondResolventOp (A V V' R : BddOp (IndexL2 J)) : BddOp (IndexL2 J) :=
  R.comp (A.comp R) - R.comp (V.comp (R.comp (V'.comp R))) - R.comp (V'.comp (R.comp (V.comp R)))
theorem matrixEntry_sub (A B : BddOp (IndexL2 J)) (ι' ι : J) :
    matrixEntry (A - B) ι' ι = matrixEntry A ι' ι - matrixEntry B ι' ι := by
  simp [matrixEntry]
theorem diag_secondResolventOp (hE : MatrixEntryProperties J) {S : Finset J}
    {A V V' : BddOp (IndexL2 J)} (hA : SupportedOn S A) (hV : SupportedOn S V)
    (hV' : SupportedOn S V') (R : BddOp (IndexL2 J)) :
    HasSum (fun ι => matrixEntry (secondResolventOp A V V' R) ι ι) (secondResolventTrace S A V V' R) ∧
      Summable (fun ι => ‖matrixEntry (secondResolventOp A V V' R) ι ι‖) ∧
      ∑' ι, ‖matrixEntry (secondResolventOp A V V' R) ι ι‖ ≤
        entryMass S A * ((‖R‖ ^ 2 + ‖R‖ ^ 2) / 2) +
        entryMass S V * ((‖R‖ ^ 2 + ‖R.comp (V'.comp R)‖ ^ 2) / 2) +
        entryMass S V' * ((‖R‖ ^ 2 + ‖R.comp (V.comp R)‖ ^ 2) / 2) := by
  obtain ⟨s1, n1, b1⟩ := diag_sandwich hE hA R R
  obtain ⟨s2, n2, b2⟩ := diag_sandwich hE hV R (R.comp (V'.comp R))
  obtain ⟨s3, n3, b3⟩ := diag_sandwich hE hV' R (R.comp (V.comp R))
  have hsplit : ∀ ι, matrixEntry (secondResolventOp A V V' R) ι ι = matrixEntry (R.comp (A.comp R)) ι ι -
      matrixEntry (R.comp (V.comp (R.comp (V'.comp R)))) ι ι -
      matrixEntry (R.comp (V'.comp (R.comp (V.comp R)))) ι ι := fun ι => by
    unfold secondResolventOp
    rw [matrixEntry_sub, matrixEntry_sub]
  have hc : entryPairing S V' ((R.comp (V.comp R)).comp R) =
      entryPairing S V ((R * R).comp (V'.comp R)) := (entryPairing_cyclic hE hV hV' (R * R) R).symm
  have hs : HasSum (fun ι => matrixEntry (secondResolventOp A V V' R) ι ι) (secondResolventTrace S A V V' R) := by
    simp only [hsplit]
    have h := (s1.sub s2).sub s3
    rw [hc] at h
    exact h
  have hle : ∀ ι, ‖matrixEntry (secondResolventOp A V V' R) ι ι‖ ≤ ‖matrixEntry (R.comp (A.comp R)) ι ι‖ +
      ‖matrixEntry (R.comp (V.comp (R.comp (V'.comp R)))) ι ι‖ +
      ‖matrixEntry (R.comp (V'.comp (R.comp (V.comp R)))) ι ι‖ := fun ι => by
    rw [hsplit]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
  have hD := (n1.hasSum.add n2.hasSum).add n3.hasSum
  have hS := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hD.summable
  refine ⟨hs, hS, (hS.tsum_le_tsum hle hD.summable).trans ?_⟩
  rw [hD.tsum_eq]
  exact add_le_add (add_le_add b1 b2) b3
theorem integrableOn_inv_add_sq {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun w : ℝ => ((a + w)⁻¹) ^ 2) (Set.Ioi 0) := by
  have hd : ∀ w ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun w : ℝ => -(a + w)⁻¹) (((a + w)⁻¹) ^ 2) w := by
    intro w hw
    have hpos : 0 < a + w := by
      have := Set.mem_Ici.1 hw
      linarith
    have h1 : HasDerivAt (fun w : ℝ => a + w) 1 w := by
      simpa using (hasDerivAt_id w).const_add a
    have h2 := (h1.fun_inv hpos.ne').fun_neg
    have e : -(-1 / (a + w) ^ 2) = ((a + w)⁻¹) ^ 2 := by
      rw [inv_pow, neg_div, neg_neg, one_div]
    rw [e] at h2
    exact h2
  have hp : ∀ w ∈ Set.Ioi (0 : ℝ), 0 ≤ ((a + w)⁻¹) ^ 2 := fun _ _ => sq_nonneg _
  have ht : Tendsto (fun w : ℝ => -(a + w)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun w : ℝ => a + w) atTop atTop :=
      tendsto_atTop_add_const_left atTop a tendsto_id
    simpa using (tendsto_inv_atTop_zero.comp h1).neg
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hd hp ht
theorem sq_norm_comp_comp_le {R Y : BddOp (IndexL2 J)} {r ρ : ℝ} (hr0 : 0 ≤ r)
    (hr : ‖R‖ ≤ r) (hρ : ‖R‖ ≤ ρ) :
    ‖R.comp (Y.comp R)‖ ^ 2 ≤ r ^ 2 * (‖Y‖ * ρ) ^ 2 := by
  have h : ‖R.comp (Y.comp R)‖ ≤ r * (‖Y‖ * ρ) :=
    (R.opNorm_comp_le _).trans (mul_le_mul hr ((Y.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left hρ (norm_nonneg _))) (norm_nonneg _) hr0)
  calc _ ≤ (r * (‖Y‖ * ρ)) ^ 2 := by gcongr
    _ = _ := by ring
theorem tsum_norm_diag_secondResolventOp_le (hE : MatrixEntryProperties J) {S : Finset J}
    {A V V' : BddOp (IndexL2 J)} (hA : SupportedOn S A) (hV : SupportedOn S V)
    (hV' : SupportedOn S V') {R : ℝ → BddOp (IndexL2 J)} {a : ℝ}
    (h : IsResolventCurve R a) {w : ℝ} (hw : 0 ≤ w) :
    ∑' ι, ‖matrixEntry (secondResolventOp A V V' (R w)) ι ι‖ ≤
      (entryMass S A + entryMass S V * ((1 + (‖V'‖ * a⁻¹) ^ 2) / 2) +
        entryMass S V' * ((1 + (‖V‖ * a⁻¹) ^ 2) / 2)) * ((a + w)⁻¹) ^ 2 := by
  have hpos := h.pos
  have hr0 : 0 ≤ (a + w)⁻¹ := inv_nonneg.2 (by linarith)
  have hn := h.norm_le w hw
  have hρ : ‖R w‖ ≤ a⁻¹ := hn.trans (inv_anti₀ hpos (by linarith))
  obtain ⟨r, hr⟩ : ∃ r, r = ((a + w)⁻¹) ^ 2 := ⟨_, rfl⟩
  have hsq : ‖R w‖ ^ 2 ≤ r := by
    rw [hr]
    gcongr
  have h1 := sq_norm_comp_comp_le (Y := V') hr0 hn hρ
  have h2 := sq_norm_comp_comp_le (Y := V) hr0 hn hρ
  rw [← hr] at h1 h2
  refine (diag_secondResolventOp hE hA hV hV' (R w)).2.2.trans ?_
  rw [← hr]
  have m1 := mul_le_mul_of_nonneg_left (show (‖R w‖ ^ 2 + ‖R w‖ ^ 2) / 2 ≤ r by linarith)
    (entryMass_nonneg S A)
  have m2 := mul_le_mul_of_nonneg_left
    (show (‖R w‖ ^ 2 + ‖(R w).comp (V'.comp (R w))‖ ^ 2) / 2 ≤
      (1 + (‖V'‖ * a⁻¹) ^ 2) / 2 * r by linarith) (entryMass_nonneg S V)
  have m3 := mul_le_mul_of_nonneg_left
    (show (‖R w‖ ^ 2 + ‖(R w).comp (V.comp (R w))‖ ^ 2) / 2 ≤
      (1 + (‖V‖ * a⁻¹) ^ 2) / 2 * r by linarith) (entryMass_nonneg S V')
  calc _ ≤ _ := add_le_add (add_le_add m1 m2) m3
    _ = _ := by ring
theorem hasSum_integral_traceAt (hE : MatrixEntryProperties J) {S : Finset J}
    {A V V' : BddOp (IndexL2 J)} (hA : SupportedOn S A) (hV : SupportedOn S V)
    (hV' : SupportedOn S V') {R : ℝ → BddOp (IndexL2 J)} {a : ℝ}
    (h : IsResolventCurve R a) {position : J → InfiniteLattice.AmbientSpace} {p : J → Fin 4 → ℤ}
    (hp : ∀ ι, position ι = PeriodicOperators.castVec (p ι))
    (hfin : ∀ y, {ι | position ι = y}.Finite)
    (hint : ∀ n : Fin 4 → ℤ, MeasureTheory.IntegrableOn
      (fun w => traceAt position (secondResolventOp A V V' (R w)) (PeriodicOperators.castVec n))
      (Set.Ioi 0)) :
    HasSum (fun n : Fin 4 → ℤ => ∫ w in Set.Ioi (0 : ℝ),
        traceAt position (secondResolventOp A V V' (R w)) (PeriodicOperators.castVec n))
      (resolventTrace S A V V' R 0) := by
  obtain ⟨K, hK⟩ : ∃ K, K = entryMass S A + entryMass S V * ((1 + (‖V'‖ * a⁻¹) ^ 2) / 2) +
      entryMass S V' * ((1 + (‖V‖ * a⁻¹) ^ 2) / 2) := ⟨_, rfl⟩
  have hg : MeasureTheory.IntegrableOn (fun w : ℝ => K * ((a + w)⁻¹) ^ 2) (Set.Ioi 0) :=
    (integrableOn_inv_add_sq h.pos).const_mul K
  have hb : ∀ w, 0 ≤ w → ∑' ι, ‖matrixEntry (secondResolventOp A V V' (R w)) ι ι‖ ≤ K * ((a + w)⁻¹) ^ 2 :=
    fun w hw => by
      rw [hK]
      exact tsum_norm_diag_secondResolventOp_le hE hA hV hV' h hw
  have hsum : Summable fun n : Fin 4 → ℤ => ∫ w in Set.Ioi (0 : ℝ),
      ‖traceAt position (secondResolventOp A V V' (R w)) (PeriodicOperators.castVec n)‖ := by
    refine summable_of_sum_le (c := ∫ w in Set.Ioi (0 : ℝ), K * ((a + w)⁻¹) ^ 2)
      (fun n => MeasureTheory.integral_nonneg fun _ => norm_nonneg _) fun s => ?_
    rw [← MeasureTheory.integral_finsetSum s fun n _ => (hint n).norm]
    refine MeasureTheory.setIntegral_mono_on
      (MeasureTheory.integrable_finsetSum s fun n _ => (hint n).norm) hg measurableSet_Ioi
      fun w hw => ?_
    have hw0 : 0 ≤ w := (Set.mem_Ioi.1 hw).le
    exact (sum_norm_traceAt_le hp hfin _
      (diag_secondResolventOp hE hA hV hV' (R w)).2.1 s).trans (hb w hw0)
  have hmain := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum
  have e1 : ∫ w in Set.Ioi (0 : ℝ), ∑' n : Fin 4 → ℤ,
      traceAt position (secondResolventOp A V V' (R w)) (PeriodicOperators.castVec n) =
      ∫ w in Set.Ioi (0 : ℝ), secondResolventTrace S A V V' (R w) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun w _ =>
      (hasSum_traceAt hp hfin _ (diag_secondResolventOp hE hA hV hV' (R w)).1).tsum_eq
  rw [e1] at hmain
  have hD : MeasureTheory.IntegrableOn (fun w => secondResolventTrace S A V V' (R w)) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono' hg
      (((continuousOn_secondResolventTrace S A V V' h).mono Set.Ioi_subset_Ici_self).aestronglyMeasurable
        measurableSet_Ioi) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
    have hw0 : 0 ≤ w := (Set.mem_Ioi.1 hw).le
    obtain ⟨t1, t2, -⟩ := diag_secondResolventOp hE hA hV hV' (R w)
    rw [← t1.tsum_eq]
    exact (norm_tsum_le_tsum_norm t2).trans (hb w hw0)
  have hI := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := resolventTrace S A V V' R) (f' := fun w => -secondResolventTrace S A V V' (R w)) (a := 0) (m := 0)
    ((continuousOn_resolventTrace S A V V' h) 0 Set.self_mem_Ici)
    (fun w hw => hasDerivAt_resolventTrace A V V' h hw) hD.neg (tendsto_resolventTrace hE S A V V' h)
  rw [MeasureTheory.integral_neg, zero_sub, neg_inj] at hI
  rw [hI] at hmain
  exact hmain
theorem euclidNormVec_sub_le (x y u : Fin 4 → ℝ) :
    euclidNormVec (x - u) ≤ euclidNormVec (x - y) + euclidNormVec (y - u) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_le <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem finite_near {position : J → InfiniteLattice.AmbientSpace} {m : ℕ}
    (h : IsIntegerPlacement position m) (y : Fin 4 → ℤ) :
    {ι | euclidNormVec (PeriodicOperators.castVec y - position ι) ≤ 4}.Finite := by
  classical
  let D : Finset (Fin 4 → ℤ) := Fintype.piFinset fun μ => Finset.Icc (y μ - 4) (y μ + 4)
  let F : (Fin 4 → ℤ) → Finset J := fun d => (h.fibre_bounded (PeriodicOperators.castVec d)).1.toFinset
  have hsub : {ι | euclidNormVec (PeriodicOperators.castVec y - position ι) ≤ 4} ⊆
      ((D.biUnion F : Finset J) : Set J) := by
    intro ι hι
    obtain ⟨k, hk⟩ := h.on_lattice ι
    have hmem : k ∈ D := by
      refine Fintype.mem_piFinset.2 fun μ => ?_
      have h1 := (abs_apply_le_euclidNormVec _ μ).trans hι
      rw [hk] at h1
      have h2 : |((y μ - k μ : ℤ) : ℝ)| ≤ 4 := by
        simpa [PeriodicOperators.castVec] using h1
      have h3 : |y μ - k μ| ≤ 4 := by exact_mod_cast h2
      have h4 := abs_le.1 h3
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨k, hmem, ?_⟩)
    simp [F, hk]
  exact (Finset.finite_toSet _).subset hsub
theorem supportedOn_of_near {position : J → InfiniteLattice.AmbientSpace} {S : Finset J}
    {t : Fin 4 → ℝ} (hS : ∀ ι, euclidNormVec (t - position ι) ≤ 4 → ι ∈ S)
    {Y : BddOp (IndexL2 J)}
    (hr : ∀ ι' ι, ¬ euclidNormVec (position ι' - position ι) ≤ 2 → matrixEntry Y ι' ι = 0)
    (hn : ∀ ι' ι, ¬ euclidNormVec (t - position ι') ≤ 2 → matrixEntry Y ι' ι = 0) : SupportedOn S Y := by
  intro i j hij
  by_contra hne
  have h1 : euclidNormVec (t - position i) ≤ 2 := by
    by_contra hc
    exact hne (hn i j hc)
  have h2 : euclidNormVec (position i - position j) ≤ 2 := by
    by_contra hc
    exact hne (hr i j hc)
  have h3 := euclidNormVec_sub_le t (position i) (position j)
  rcases hij with h | h
  · exact h (hS i (by linarith))
  · exact h (hS j (by linarith))
end HessianSum
open HessianSum in
theorem logDensityHessianSum_holds
    (hH : LogTraceSecondDerivative.IntegralFormula)
    (hV : LocalFamilyVariations) :
    LogDensityHessianSum := by
  classical
  intro J B position tail m m' z C T hz hC hset b b'
  have hE := hset.space.entryFacts
  have hL := hset.space.placement
  choose p hp using hL.on_lattice
  have hfin : ∀ y, {ι | position ι = y}.Finite := fun y => (hL.fibre_bounded y).1
  obtain ⟨y, hy⟩ := hset.edges.on_lattice b
  obtain ⟨y', hy'⟩ := hset.edges.on_lattice b'
  obtain ⟨-, -, hr1, hn1, -, -, -⟩ := hV J B position tail m m' z C T hz hC hset b b'
  obtain ⟨-, -, hr1', hn1', -, -, -⟩ := hV J B position tail m m' z C T hz hC hset b' b
  obtain ⟨S, hS⟩ : ∃ S : Finset J, S = (finite_near hL y).toFinset := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Finset J, S' = S ∪ (finite_near hL y').toFinset := ⟨_, rfl⟩
  have hin : ∀ ι, euclidNormVec (tail b - position ι) ≤ 4 → ι ∈ S' := fun ι h => by
    rw [hS', hS]
    exact Finset.mem_union_left _ ((finite_near hL y).mem_toFinset.2 (by rw [← hy]; exact h))
  have hin' : ∀ ι, euclidNormVec (tail b' - position ι) ≤ 4 → ι ∈ S' := fun ι h => by
    rw [hS']
    exact Finset.mem_union_right _ ((finite_near hL y').mem_toFinset.2 (by rw [← hy']; exact h))
  have vA : SupportedOn S' (secondVar T b b') :=
    supportedOn_of_near hin (fun κ κ' h => (hr1 κ κ' h).2) fun κ κ' h => (hn1 κ κ' h).2
  have vV : SupportedOn S' (firstVar T b) :=
    supportedOn_of_near hin (fun κ κ' h => (hr1 κ κ' h).1) fun κ κ' h => (hn1 κ κ' h).1
  have vV' : SupportedOn S' (firstVar T b') :=
    supportedOn_of_near hin' (fun κ κ' h => (hr1' κ κ' h).1) fun κ κ' h => (hn1' κ κ' h).1
  have hlow : IsBoundedBelowBy (addScalar (T fun _ => 0) z) (z / 2) := by
    obtain ⟨r, hr, hsm⟩ := hset.lower_bound
    exact hsm _ fun _ => by simpa using hr.le
  have hlog := (hset.space.logShifted (T fun _ => 0) ⟨hset.family.selfAdjoint _, hlow⟩).1
  have hfam : IsResolventCurve (baseResolvent T z) (z / 2) :=
    ⟨by positivity, fun w hw => (hlog w hw).2, fun w w' hw hw' =>
      inverseOp_sub_inverseOp _ w w' (hlog w hw).1 (hlog w' hw').1⟩
  have hmain := hasSum_integral_traceAt hE vA vV vV' hfam hp hfin fun n =>
    (hH J B position tail m m' z C T hz hC hset n b b').2.1
  have e1 : (fun n : Fin 4 → ℤ => logTraceHessian position T z (PeriodicOperators.castVec n) b b') =
      fun n => ∫ w in Set.Ioi (0 : ℝ), traceAt position
        (secondResolventOp (secondVar T b b') (firstVar T b) (firstVar T b')
          (baseResolvent T z w)) (PeriodicOperators.castVec n) :=
    funext fun n => (hH J B position tail m m' z C T hz hC hset n b b').2.2
  have e2 : variationTrace T z b b' = resolventTrace S' (secondVar T b b')
      (firstVar T b) (firstVar T b') (baseResolvent T z) 0 := by
    have t1 := (diag_sandwich hE vA (baseResolvent T z 0) (ContinuousLinearMap.id ℂ _)).1.tsum_eq
    have t2 := (diag_sandwich hE vV (baseResolvent T z 0)
      ((baseResolvent T z 0).comp (firstVar T b'))).1.tsum_eq
    unfold variationTrace diagTrace resolventTrace
    simp only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] at t1
    rw [t1, t2]
    rfl
  rw [e1, e2]
  exact hmain
end YangMills.Construction.Tower.LocalFamilies
end
