import YangMills.Construction.EnergyMomentum.SemigroupGenerators
import YangMills.Construction.ReflectionPositiveLimits.LAdicDataAreLatticeDataOfFineLattices
import YangMills.Construction.ReflectionPositiveLimits.LimitsOfLatticeStates
import YangMills.Construction.ReflectionPositiveLimits.MovingTestFunctions
import YangMills.Construction.ReflectionPositiveLimits.RepresentativesOfSeparatedTuples
import YangMills.Construction.ReflectionPositivity.WhatIsTakenFromOneLattice
import Mathlib
set_option autoImplicit false
open Filter Set Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeLimits
open EuclidIsometry
section Limits
variable {L : ℕ} (A : LatticeSequence L) {σ : Tuple → ℝ}
theorem euclidIsometry_ext {r r' : EuclidIsometry} (h : r.toFun = r'.toFun) : r = r' := by
  obtain ⟨a, ha⟩ := r
  obtain ⟨b, hb⟩ := r'
  have e : a = b := h
  subst e
  rfl
theorem isPermInvariant_of_hasLimit (hl : A.HasLimit σ) (h : ∀ j, IsPermInvariant (A.mean j)) :
    IsPermInvariant σ := fun X Y hXY =>
  tendsto_nhds_unique (hl.2 X) ((hl.2 Y).congr fun j => (h j Y X hXY.symm))
theorem isSlotLinear_of_hasLimit (hl : A.HasLimit σ) (h : ∀ j, IsSlotLinear (A.mean j)) :
    IsSlotLinear σ := by
  intro pre post f f' α α' hf hf'
  refine tendsto_nhds_unique (hl.2 _) ?_
  have e := (((hl.2 ⟨_, hf⟩).const_mul α).add ((hl.2 ⟨_, hf'⟩).const_mul α'))
  exact e.congr fun j => (h j pre post f f' α α' hf hf').symm
theorem mean_push_eq (j : ℕ+) (hc : A.RepCommutesWithSymmetries j)
    (ho : A.RepContinuousLocal j)
    (hi : ∀ F : A.Fields j → ℂ, InfiniteLattice.IsBoundedObservable F →
      ∀ s : InfiniteLattice.LatticeSymmetry (A.mesh j),
        (A.measure j).integral (s.actOn F) = (A.measure j).integral F)
    (s : InfiniteLattice.LatticeSymmetry (A.mesh j)) (X : Tuple) :
    A.mean j (push (latticeSymmetryToEuclid s) X) = A.mean j X := by
  have e := hc s (basisOf X)
  have hb : pushComb (latticeSymmetryToEuclid s) (basisOf X) =
      basisOf (push (latticeSymmetryToEuclid s) X) := by
    simp [pushComb, basisOf]
  have e₁ : ∀ Y : Tuple, A.repComb j (basisOf Y) =
      A.complexRep j Y := fun Y => by
    funext U
    exact A.repComb_basisOf j Y U
  rw [hb, e₁, e₁] at e
  have e₂ := hi _ (ho X).2.1 s
  rw [e] at e₂
  have e₃ := A.integral_rep j X
  have e₄ := A.integral_rep j (push (latticeSymmetryToEuclid s) X)
  have : ((A.mean j (push (latticeSymmetryToEuclid s) X) : ℝ) : ℂ) =
      ((A.mean j X : ℝ) : ℂ) := by
    rw [← e₃, ← e₄]
    exact e₂
  exact_mod_cast this
end Limits
section Invariance
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (A : LatticeSequence L)
  (hA : A.IsRP) {σ : Tuple → ℝ} (hl : A.HasLimit σ) (hσ : IsAdmissiblyContinuous σ)
  (hRep : TupleRepresentatives.Statement)
  (hOne : DirectionPictures.singleLatticeInputs)
  (hAdic : FineLatticeAdicData.AdicDataLatticeData) (hMov : MovingTestFunctions.statement)
include hL in
theorem mesh_pos (j : ℕ+) : 0 < A.mesh j := by
  have : (0 : ℝ) < L := by
    have := hL.2
    positivity
  exact zpow_pos this _
include hL hA hl hRep hOne in
theorem isIsomInvariant_of_eventually_latticeSymmetry (r : EuclidIsometry)
    (h : ∀ᶠ j : ℕ+ in atTop,
      ∃ s : InfiniteLattice.LatticeSymmetry (A.mesh j), s.toFun = r.toFun) :
    IsIsomInvariant r σ := fun X => by
  refine tendsto_nhds_unique (hl.2 (push r X)) ((hl.2 X).congr' ?_)
  filter_upwards [h] with j hj
  obtain ⟨s, hs⟩ := hj
  obtain ⟨h₁, h₂, -, h₄, -⟩ := hRep L hL.1 hL.2 A j
  have e := mean_push_eq A j h₄ h₂
    ((hOne _ (mesh_pos hL A j) (A.measure j) (hA j)).1) s X
  have e' : latticeSymmetryToEuclid s = r := euclidIsometry_ext hs
  rw [e'] at e
  exact e.symm
include hL hA hl hRep hOne hAdic in
theorem isIsomInvariant_translate_adic (v : Space)
    (hv : ∀ μ, v μ ∈ PeriodicLattice.adicGridPoints L) : IsIsomInvariant (translate v) σ := by
  refine isIsomInvariant_of_eventually_latticeSymmetry hL A hA hl hRep hOne _ ?_
  obtain ⟨-, -, h, -⟩ := hAdic L hL A.level A.level_strictMono
  obtain ⟨j₀, hj₀⟩ := h v hv
  filter_upwards [eventually_ge_atTop j₀] with j hj
  exact ⟨InfiniteLattice.shift ⟨v, hj₀ j hj⟩, rfl⟩
include hL hA hl hσ hRep hOne hAdic hMov in
theorem isTranslInvariant_of_hasLimit : IsTranslInvariant σ := by
  intro v X
  obtain ⟨-, hd, -⟩ := (hAdic L hL A.level A.level_strictMono).1
  have hdense : Dense (Set.pi univ fun _ : Fin 4 => PeriodicLattice.adicGridPoints L) :=
    dense_pi _ fun _ _ => hd
  obtain ⟨w, hw, hwv⟩ := mem_closure_iff_seq_limit.1 (hdense v)
  obtain ⟨n₀, -, hc⟩ := hMov.2.2.1 X w v hwv
  refine tendsto_nhds_unique (hσ _ _ _ hc) (tendsto_const_nhds.congr fun n => ?_)
  exact (isIsomInvariant_translate_adic hL A hA hl hRep hOne hAdic _
    (fun μ => hw _ μ (mem_univ μ)) X).symm
include hL hA hl hσ hRep hOne hAdic hMov in
theorem exists_isIsomInvariant_of_mem_group (g : Equiv.Perm Space)
    (hg : g ∈ translationHyperoctahedralGroup) :
    ∃ r : EuclidIsometry, r.toPerm = g ∧ IsIsomInvariant r σ := by
  have ht := isTranslInvariant_of_hasLimit hL A hA hl hσ hRep hOne hAdic hMov
  induction hg using Subgroup.closure_induction with
  | mem g h =>
    rcases h with ⟨v, rfl⟩ | h
    · exact ⟨_, rfl, ht v⟩
    · obtain ⟨s, hs, -⟩ := (hRep L hL.1 hL.2 A 1).2.2.2.2.2.2.2.2.1 g h
      refine ⟨latticeSymmetryToEuclid s, Equiv.ext fun x => congrFun hs x, ?_⟩
      refine isIsomInvariant_of_eventually_latticeSymmetry hL A hA hl hRep hOne _
        (Eventually.of_forall fun j => ?_)
      obtain ⟨s', hs', -⟩ := (hRep L hL.1 hL.2 A j).2.2.2.2.2.2.2.2.1 g h
      exact ⟨s', hs'.trans hs.symm⟩
  | one =>
    exact ⟨EuclidIsometry.translate 0, Equiv.ext fun x => by
      simp [EuclidIsometry.toPerm, EuclidIsometry.translate], ht 0⟩
  | mul g g' _ _ h h' =>
    obtain ⟨r, rfl, hr⟩ := h
    obtain ⟨r', rfl, hr'⟩ := h'
    refine ⟨r.comp r', Equiv.ext fun x => rfl, fun X => ?_⟩
    rw [hMov.1 X X r r' |>.1, hr, hr']
  | inv g _ h =>
    obtain ⟨r, rfl, hr⟩ := h
    refine ⟨r.symm, Equiv.ext fun x => rfl, fun X => ?_⟩
    have e : r.comp r.symm = EuclidIsometry.translate 0 :=
      euclidIsometry_ext (funext fun x => by
        simp [EuclidIsometry.comp, toFun_symm, EuclidIsometry.translate])
    have e₁ := (hMov.1 X X r r.symm).1
    rw [e] at e₁
    rw [← hr, ← e₁, ht 0]
theorem mirrorPair_reflect_toFun (M : NormalMirror) {a : ℝ} (P : MirrorHyperplanes.MirrorPair a)
    (hn : P.normal = M.normal) (ho : P.height = M.offset) :
    P.reflect.toFun = M.reflectIso.toFun := by
  funext x
  rw [LatticeAtSpacing.reflect_apply]
  change _ = M.reflectPt x
  rw [NormalMirror.reflectPt, euclidNormVec_sq, hn, ho]
  congr 2
  change 2 * (euclidInner M.normal M.normal)⁻¹ * (euclidInner M.normal x - M.offset) = _
  ring
include hL hA hl hRep hOne hAdic in
theorem isIsomInvariant_adicMirror (M : NormalMirror) (hM : IsAdicMirror L M) :
    IsIsomInvariant M.reflectIso σ := by
  refine isIsomInvariant_of_eventually_latticeSymmetry hL A hA hl hRep hOne _ ?_
  obtain ⟨-, -, -, -, h, -⟩ := hAdic L hL A.level A.level_strictMono
  obtain ⟨j₀, hj₀⟩ := h M hM
  filter_upwards [eventually_ge_atTop j₀] with j hj
  obtain ⟨⟨P, hn, ho⟩, -⟩ := hj₀ j hj
  exact ⟨P.reflect, mirrorPair_reflect_toFun M P hn ho⟩
theorem zero_mem_adicGridPoints : (0 : ℝ) ∈ PeriodicLattice.adicGridPoints L :=
  (PeriodicLattice.mem_adicGridPoints_iff L 0).2 ⟨0, 0, by simp⟩
theorem isAdicMirror_of_offset_mem {M : NormalMirror}
    (h : M.offset ∈ PeriodicLattice.adicGridPoints L) : IsAdicMirror L M := by
  rcases M.normal_mem with hn | ⟨μ, lam, hne, hn⟩
  · refine Or.inl ⟨hn, 2 * M.offset, ?_, by ring⟩
    obtain ⟨k, n, e⟩ := (PeriodicLattice.mem_adicGridPoints_iff L _).1 h
    refine (PeriodicLattice.mem_adicGridPoints_iff L _).2 ⟨k, 2 * n, ?_⟩
    rw [e]
    push_cast
    ring
  · exact Or.inr ⟨⟨μ, lam, hne, hn⟩, h⟩
include hL hA hl hσ hRep hOne hAdic hMov in
theorem isIsomInvariant_reflectIso (M : NormalMirror) : IsIsomInvariant M.reflectIso σ := by
  have ht := isTranslInvariant_of_hasLimit hL A hA hl hσ hRep hOne hAdic hMov
  have h₀ : IsIsomInvariant (M.atOffset 0).reflectIso σ :=
    isIsomInvariant_adicMirror hL A hA hl hRep hOne hAdic _
      (isAdicMirror_of_offset_mem (M := M.atOffset 0) zero_mem_adicGridPoints)
  have e : M.reflectIso =
      (EuclidIsometry.translate
        ((2 * M.offset / TorusMetric.euclidNormVec M.normal ^ 2) • M.normal)).comp
        (M.atOffset 0).reflectIso := by
    refine euclidIsometry_ext (funext fun x => ?_)
    funext μ
    change (x - (2 * (euclidInner M.normal x - M.offset) /
        TorusMetric.euclidNormVec M.normal ^ 2) • M.normal) μ =
      (x - (2 * (euclidInner M.normal x - 0) /
        TorusMetric.euclidNormVec M.normal ^ 2) • M.normal) μ +
        ((2 * M.offset / TorusMetric.euclidNormVec M.normal ^ 2) • M.normal) μ
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  intro X
  rw [e, (hMov.1 X X _ _).1, ht, h₀]
include hL in
theorem eventually_mesh_le {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ j : ℕ+ in atTop, A.mesh j ≤ δ := by
  have hL1 : (1 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 1 < L)
  have hi : (L : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hi
  filter_upwards [eventually_ge_atTop k.succPNat] with j hj
  have h₁ : j ≤ A.level j := A.level_strictMono.le_apply
  have h₂ : k ≤ (A.level j : ℕ) := by
    have h₃ : k.succPNat ≤ A.level j := hj.trans h₁
    have h₄ : (k.succPNat : ℕ) ≤ (A.level j : ℕ) := h₃
    simp at h₄
    omega
  have e : A.mesh j = (L : ℝ)⁻¹ ^ (A.level j : ℕ) := by
    change (L : ℝ) ^ (-(((A.level j : ℕ) : ℤ))) = _
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [e]
  exact ((pow_le_pow_of_le_one (by positivity) hi.le h₂).trans hk.le)
omit hL in
theorem exists_adicGridPoints_seq_le (hd : Dense (PeriodicLattice.adicGridPoints L)) (c : ℝ) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ PeriodicLattice.adicGridPoints L) ∧ (∀ n, u n ≤ c) ∧
      Tendsto u atTop (𝓝 c) := by
  have h : ∀ n : ℕ, ∃ z ∈ PeriodicLattice.adicGridPoints L,
      z ∈ Ioo (c - 1 / ((n : ℝ) + 1)) c := fun n =>
    hd.exists_between (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
  choose u hu hu' using h
  refine ⟨u, hu, fun n => (hu' n).2.le, ?_⟩
  have h₁ : Tendsto (fun n : ℕ => c - 1 / ((n : ℝ) + 1)) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h₁ tendsto_const_nhds
    (fun n => (hu' n).1.le) (fun n => (hu' n).2.le)
theorem abs_euclidInner_le_two_maxNorm {n : Space} (hn : n ∈ admissibleNormals) (d : Space) :
    |euclidInner n d| ≤ 2 * maxNorm d := by
  have hc : ∀ μ, |d μ| ≤ maxNorm d := fun μ =>
    Finset.le_sup' (fun μ => |d μ|) (Finset.mem_univ μ)
  have h0 : 0 ≤ maxNorm d := (abs_nonneg _).trans (hc 0)
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, lam, -, rfl | rfl⟩
  · rw [euclidInner_coordVec]
    linarith [hc μ]
  · have e : euclidInner (PeriodicLattice.coordVec μ + PeriodicLattice.coordVec lam) d =
        d μ + d lam := by
      rw [← euclidInner_coordVec μ d, ← euclidInner_coordVec lam d]
      simp only [euclidInner, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [e]
    exact (abs_add_le _ _).trans (by linarith [hc μ, hc lam])
  · have e : euclidInner (PeriodicLattice.coordVec μ - PeriodicLattice.coordVec lam) d =
        d μ - d lam := by
      rw [← euclidInner_coordVec μ d, ← euclidInner_coordVec lam d]
      simp only [euclidInner, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [e]
    exact (abs_sub _ _).trans (by linarith [hc μ, hc lam])
theorem exists_bounded_nbhd_closedSide (M : NormalMirror) {K : Set Space} (hK : IsCompact K)
    (hs : K ⊆ M.posSide) :
    ∃ δ > 0, ∃ S : Set Space, Bornology.IsBounded S ∧
      S ⊆ {x | M.offset ≤ euclidInner M.normal x} ∧
      ∀ (T : Set Space) (a : ℝ), T ⊆ K → T.Nonempty → 0 < a → a ≤ δ →
        {x | maxNormInfDist x T ≤ a / 2} ⊆ S := by
  have hcont : Continuous fun x : Space => euclidInner M.normal x := by
    unfold euclidInner
    fun_prop
  obtain ⟨δ, hδ, hlow⟩ : ∃ δ > 0, ∀ x ∈ K, M.offset + 2 * δ ≤ euclidInner M.normal x := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, by simp⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
      have h₀ : M.offset < euclidInner M.normal x₀ := hs hx₀
      refine ⟨(euclidInner M.normal x₀ - M.offset) / 2, by linarith, fun x hx => ?_⟩
      have := hmin hx
      change euclidInner M.normal x₀ ≤ euclidInner M.normal x at this
      linarith
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  refine ⟨δ, hδ, {x | M.offset ≤ euclidInner M.normal x} ∩ Metric.closedBall 0 (B + 2 * δ),
    Metric.isBounded_closedBall.subset inter_subset_right, inter_subset_left, ?_⟩
  intro T a hT hne ha haδ x hx
  have hx' : maxNormInfDist x T ≤ a / 2 := hx
  have hlt : sInf ((fun x' => maxNorm (x - x')) '' T) < a / 2 + δ / 2 := by
    have : maxNormInfDist x T < a / 2 + δ / 2 := by linarith
    exact this
  obtain ⟨_, ⟨y, hy, rfl⟩, hyl⟩ := exists_lt_of_csInf_lt (hne.image _) hlt
  have hyl' : maxNorm (x - y) < a / 2 + δ / 2 := hyl
  have hyK := hT hy
  refine ⟨?_, ?_⟩
  · have e := abs_euclidInner_le_two_maxNorm M.normal_mem (x - y)
    rw [euclidInner_sub_right] at e
    have h₁ := (abs_le.1 e).1
    have h₂ := hlow y hyK
    change M.offset ≤ euclidInner M.normal x
    linarith
  · rw [mem_closedBall_zero_iff]
    rw [maxNorm_eq_norm] at hyl'
    have h₃ := hB y hyK
    have : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      simpa using norm_add_le (x - y) y
    linarith
theorem measurable_finset_sum_mul {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (α : ι → ℂ)
    (G : ι → Ω → ℂ) (h : ∀ b, Measurable (G b)) : Measurable fun U => ∑ b, α b * G b U :=
  Finset.measurable_fun_sum _ fun b _ => (h b).const_mul _
theorem sum_mul_mem_regionObservables {a : ℝ} {ι : Type*} [Fintype ι] {S : Set Space} (α : ι → ℂ)
    (G : ι → InfiniteLattice.GaugeField a → ℂ)
    (h : ∀ b, G b ∈ InfiniteLattice.regionObservables a S) :
    (fun U => ∑ b, α b * G b U) ∈ InfiniteLattice.regionObservables a S := by
  refine ⟨⟨measurable_finset_sum_mul α G fun b => (h b).1.1, ?_⟩,
    @measurable_finset_sum_mul _ _ (InfiniteLattice.regionSigma S) _ α G fun b => (h b).2⟩
  choose C hC using fun b => (h b).1.2
  refine ⟨∑ b, ‖α b‖ * C b, fun U => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC b U) (norm_nonneg _)
theorem repComb_sum_smul_basisOf {L : ℕ} (A : LatticeSequence L) {ι : Type*} [Fintype ι]
    (j : ℕ+) (α : ι → ℂ) (X : ι → Tuple) (U : A.Fields j) :
    A.repComb j (∑ b, α b • basisOf (X b)) U =
      ∑ b, α b * A.complexRep j (X b) U := by
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun b _ => by
    rw [A.repComb_basisOf]
    rfl
theorem integrable_complexRep {L : ℕ} (A : LatticeSequence L) (j : ℕ+)
    (ho : A.RepContinuousLocal j) (X : Tuple) :
    Integrable (A.complexRep j X) (A.measure j).1 := by
  have := (A.measure j).2
  obtain ⟨-, ⟨hm, C, hC⟩, -⟩ := ho X
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
theorem integral_conj_reflect_mul {L : ℕ} (A : LatticeSequence L) (j : ℕ+)
    (ho : A.RepContinuousLocal j)
    (hc : A.RepConcatEqMul j)
    (hm : A.RepCommutesWithMirrors j)
    (P : MirrorHyperplanes.MirrorPair (A.mesh j)) (M : NormalMirror)
    (hP : P.reflect.toFun = M.reflectIso.toFun) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → Tuple) (α : ι → ℂ) (Y : κ → Tuple) (β : κ → ℂ)
    (hd : ∀ b c, Concatenable (push M.reflectIso (X b)) (Y c)) :
    (A.measure j).integral (fun U =>
        conj (P.reflect.actOn
          (A.repComb j (∑ b, α b • basisOf (X b))) U) *
          A.repComb j (∑ c, β c • basisOf (Y c)) U) =
      ∑ b, ∑ c, conj (α b) * β c *
        ((A.mean j (concat (push M.reflectIso (X b)) (Y c) (hd b c)) : ℝ) : ℂ) := by
  have hiso : latticeSymmetryToEuclid P.reflect = M.reflectIso := euclidIsometry_ext hP
  have point : ∀ U : A.Fields j,
      conj (P.reflect.actOn
          (A.repComb j (∑ b, α b • basisOf (X b))) U) *
          A.repComb j (∑ c, β c • basisOf (Y c)) U =
        ∑ b, ∑ c, conj (α b) * β c *
          A.complexRep j (concat (push M.reflectIso (X b)) (Y c) (hd b c)) U := by
    intro U
    change conj (A.repComb j (∑ b, α b • basisOf (X b))
      (P.reflect.pullbackField U)) * _ = _
    rw [repComb_sum_smul_basisOf, repComb_sum_smul_basisOf, map_sum,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    have e := congrFun (hm P (X b)) U
    rw [hiso] at e
    have e₁ : A.rep j (X b) (P.reflect.pullbackField U) =
        A.rep j (push M.reflectIso (X b)) U := e
    have e₂ := congrFun (hc _ _ (hd b c)) U
    simp only [Pi.mul_apply] at e₂
    simp only [LatticeSequence.complexRep, map_mul, Complex.conj_ofReal, e₁, e₂]
    push_cast
    ring
  change ∫ U, _ ∂(A.measure j).1 = _
  simp_rw [point]
  have hI : ∀ b c, Integrable (fun U => conj (α b) * β c *
      A.complexRep j (concat (push M.reflectIso (X b)) (Y c) (hd b c)) U)
      (A.measure j).1 := fun b c => (integrable_complexRep A j ho _).const_mul _
  rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun c _ => hI b c]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finsetSum _ fun c _ => hI b c]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_const_mul]
  congr 1
  exact integral_ofReal
theorem reflForm_sum_sum (σ : Tuple → ℝ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → Tuple) (α : ι → ℂ) (Y : κ → Tuple) (β : κ → ℂ)
    (hX : ∀ b, X b ∈ tuplesSupportedIn timeZeroMirror.posSide)
    (hY : ∀ c, Y c ∈ tuplesSupportedIn timeZeroMirror.posSide)
    (Z W : combsSupportedIn upperHalfSpace) (hZ : (Z : TupleComb) = ∑ b, α b • basisOf (X b))
    (hW : (W : TupleComb) = ∑ c, β c • basisOf (Y c)) :
    reflForm σ Z W = ∑ b, ∑ c, conj (α b) * β c *
      ((σ (concat (push timeZeroMirror.reflectIso (X b)) (Y c)
        (NormalMirror.concatenable_reflectIso (hX b) (hY c))) : ℝ) : ℂ) := by
  change linearExt σ (concatBilin
    (pushComb timeZeroMirror.reflectIso (conjComb (Z : TupleComb))) (W : TupleComb)) = _
  rw [hZ, hW, conjComb_sum]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  have hm : pushComb timeZeroMirror.reflectIso (basisOf (X b)) =
      basisOf (push timeZeroMirror.reflectIso (X b)) := by
    simp [pushComb, basisOf]
  have hd := NormalMirror.concatenable_reflectIso (hX b) (hY c)
  have hc : concatBilin (basisOf (push timeZeroMirror.reflectIso (X b)))
      (basisOf (Y c)) = basisOf (concat _ _ hd) := by
    simp [concatBilin, basisOf, concatBasis, hd]
  have he : ∀ Y, linearExt σ (basisOf Y) = (σ Y : ℂ) := fun Y => by
    simp [linearExt, basisOf]
  rw [hm, hc, he]
  ring
theorem exists_finite_expansion (Z : combsSupportedIn upperHalfSpace) :
    ∃ (ι : Type) (_ : Fintype ι) (X : ι → Tuple) (α : ι → ℂ),
      (∀ b, X b ∈ tuplesSupportedIn timeZeroMirror.posSide) ∧
        (Z : TupleComb) = ∑ b, α b • basisOf (X b) := by
  have hs := mem_combsSupportedIn_iff.1 Z.2
  refine ⟨(Z : TupleComb).support, inferInstance, fun b => b, fun b => (Z : TupleComb) b,
    fun b => by rw [timeZeroMirror_posSide]; exact hs b.2, ?_⟩
  rw [Finset.sum_coe_sort (Z : TupleComb).support fun X => (Z : TupleComb) X • basisOf X]
  conv_lhs => rw [← Finsupp.sum_single (Z : TupleComb)]
  refine Finset.sum_congr rfl fun X _ => ?_
  simp [basisOf]
theorem tendsto_reflForm_mean {L : ℕ} (A : LatticeSequence L) {σ : Tuple → ℝ}
    (hl : A.HasLimit σ) (Z W : combsSupportedIn upperHalfSpace) :
    Tendsto (fun j => reflForm (A.mean j) Z W) atTop (𝓝 (reflForm σ Z W)) := by
  unfold reflForm linearExt
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
  refine tendsto_finsetSum _ fun Y _ => Tendsto.const_mul _ ?_
  exact (Complex.continuous_ofReal.tendsto _).comp (hl.2 Y)
include hL hRep in
theorem exists_local_repComb (M : NormalMirror) {ι : Type*} [Fintype ι] (X : ι → Tuple)
    (hX : ∀ b, X b ∈ tuplesSupportedIn M.posSide) :
    ∃ δ > 0, ∃ S : Set Space, Bornology.IsBounded S ∧
      S ⊆ {x | M.offset ≤ euclidInner M.normal x} ∧
      ∀ (j : ℕ+), A.mesh j ≤ δ → ∀ α : ι → ℂ,
        A.repComb j (∑ b, α b • basisOf (X b)) ∈
          InfiniteLattice.regionObservables (A.mesh j) S := by
  set K : Set Space := ⋃ b, ⋃ f ∈ (X b).1, tsupport f with hK
  have hKc : IsCompact K := isCompact_iUnion fun b =>
    (List.finite_toSet (X b).1).isCompact_biUnion fun f hf => ((X b).2.1 f hf).2.1
  have hKs : K ⊆ M.posSide := iUnion_subset fun b => iUnion₂_subset fun f hf => hX b f hf
  obtain ⟨δ, hδ, S, hSb, hSs, hS⟩ := exists_bounded_nbhd_closedSide M hKc hKs
  refine ⟨δ, hδ, S, hSb, hSs, fun j hj α => ?_⟩
  have hG : ∀ b, A.complexRep j (X b) ∈ InfiniteLattice.regionObservables (A.mesh j) S := by
    intro b
    obtain ⟨-, ho, hloc, -⟩ := hRep L hL.1 hL.2 A j
    by_cases hne : (⋃ f ∈ (X b).1, tsupport f).Nonempty
    · have h₁ := (hloc (X b)).1 hne
      refine ⟨h₁.1, Measurable.mono h₁.2 (InfiniteLattice.regionSigma_mono ?_) le_rfl⟩
      exact hS _ _ (subset_iUnion (fun b => ⋃ f ∈ (X b).1, tsupport f) b) hne
        (mesh_pos hL A j) hj
    · obtain ⟨c, hc⟩ := (hloc (X b)).2 (not_nonempty_iff_eq_empty.1 hne)
      refine ⟨(ho (X b)).2.1, ?_⟩
      have e : A.complexRep j (X b) = fun _ => ((c : ℝ) : ℂ) := by
        funext U
        simp [LatticeSequence.complexRep, hc U]
      rw [e]
      exact measurable_const
  have e : A.repComb j (∑ b, α b • basisOf (X b)) =
      fun U => ∑ b, α b * A.complexRep j (X b) U :=
    funext fun U => repComb_sum_smul_basisOf A j α X U
  rw [e]
  exact sum_mul_mem_regionObservables α _ hG
include hL hA hl hRep hAdic in
theorem reflectionPositiveAt_adicMirror (M : NormalMirror) (hM : IsAdicMirror L M) :
    ReflectionPositiveAt M σ := by
  intro ι _ X α hX
  obtain ⟨δ, hδ, S, hSb, hSs, hS⟩ := exists_local_repComb hL A hRep M X hX
  obtain ⟨-, -, -, -, h, -⟩ := hAdic L hL A.level A.level_strictMono
  obtain ⟨j₀, hj₀⟩ := h M hM
  have ht : Tendsto (fun j => ∑ b, ∑ b', conj (α b) * α b' *
      ((A.mean j (concat (push M.reflectIso (X b)) (X b')
        (NormalMirror.concatenable_reflectIso (hX b) (hX b'))) : ℝ) : ℂ)) atTop
      (𝓝 (∑ b, ∑ b', conj (α b) * α b' *
        ((σ (concat (push M.reflectIso (X b)) (X b')
          (NormalMirror.concatenable_reflectIso (hX b) (hX b'))) : ℝ) : ℂ))) :=
    tendsto_finsetSum _ fun b _ => tendsto_finsetSum _ fun b' _ => Tendsto.const_mul _
      ((Complex.continuous_ofReal.tendsto _).comp (hl.2 _))
  refine ge_of_tendsto ht ?_
  filter_upwards [eventually_mesh_le hL A hδ, eventually_ge_atTop j₀] with j hj hj'
  obtain ⟨⟨P, hn, ho⟩, -⟩ := hj₀ j hj'
  obtain ⟨-, hobs, -, -, hcc, -, -, hmir, -⟩ := hRep L hL.1 hL.2 A j
  rw [← integral_conj_reflect_mul A j hobs hcc hmir P M (mirrorPair_reflect_toFun M P hn ho)
    X α X α fun b c => NormalMirror.concatenable_reflectIso (hX b) (hX c)]
  have hF := hS j hj α
  refine (hA j).2 P _ ⟨S, hSb, hF.2⟩
    ⟨hF.1, Measurable.mono hF.2 (InfiniteLattice.regionSigma_mono ?_) le_rfl⟩
  intro x hx
  have := hSs hx
  change P.height ≤ P.normal ⬝ᵥ x
  rw [hn, ho]
  exact this
include hL hA hl hσ hRep hAdic hMov in
theorem reflectionPositiveAt_of_hasLimit (M : NormalMirror) : ReflectionPositiveAt M σ := by
  intro ι _ X α hX
  obtain ⟨-, hd, -⟩ := (hAdic L hL A.level A.level_strictMono).1
  obtain ⟨u, hu, hle, hlim⟩ := exists_adicGridPoints_seq_le hd M.offset
  have hXn : ∀ n b, X b ∈ tuplesSupportedIn (M.atOffset (u n)).posSide := fun n b f hf x hx =>
    lt_of_le_of_lt (hle n) (hX b f hf hx)
  have hpos : ∀ n, 0 ≤ ∑ b, ∑ b', conj (α b) * α b' *
      ((σ (concatOrNil (push (M.atOffset (u n)).reflectIso (X b)) (X b')) : ℝ) : ℂ) := by
    intro n
    have h₁ := reflectionPositiveAt_adicMirror hL A hA hl hRep hAdic (M.atOffset (u n))
      (isAdicMirror_of_offset_mem (M := M.atOffset (u n)) (hu n)) ι X α (hXn n)
    convert h₁ using 7 with b _ b' _
    exact dif_pos (NormalMirror.concatenable_reflectIso (hXn n b) (hXn n b'))
  refine ge_of_tendsto' (f := fun n => ∑ b, ∑ b', conj (α b) * α b' *
      ((σ (concatOrNil (push (M.atOffset (u n)).reflectIso (X b)) (X b')) : ℝ) : ℂ))
    (x := atTop) (tendsto_finsetSum _ fun b _ => tendsto_finsetSum _ fun b' _ =>
      Tendsto.const_mul _ ((Complex.continuous_ofReal.tendsto _).comp ?_)) hpos
  obtain ⟨-, -, -, n₀, -, hc⟩ :=
    hMov.2.2.2 M (X b) (X b') (hX b) (hX b') u (fun n _ => hle n) hlim
  have h₂ := (hσ _ _ _ hc).comp tendsto_natCast_atTop_atTop
  refine h₂.congr fun n => ?_
  simp
theorem reflForm_mean_eq_reflCorr (j : ℕ+)
    (ho : A.RepContinuousLocal j)
    (hc : A.RepConcatEqMul j)
    (hm : A.RepCommutesWithMirrors j) (Z W : combsSupportedIn upperHalfSpace) :
    reflForm (A.mean j) Z W =
      DirectionPictures.reflCorr (A.measure j) timeAxis
        (A.repComb j Z) (A.repComb j W) := by
  obtain ⟨ι, _, X, α, hX, hZ⟩ := exists_finite_expansion Z
  obtain ⟨κ, _, Y, β, hY, hW⟩ := exists_finite_expansion W
  rw [reflForm_sum_sum _ X α Y β hX hY Z W hZ hW, hZ, hW]
  exact (integral_conj_reflect_mul A j ho hc hm (LatticeAtSpacing.coordinateMirror _ timeAxis)
    timeZeroMirror (mirrorPair_reflect_toFun timeZeroMirror _ rfl rfl) X α Y β
    fun b c => NormalMirror.concatenable_reflectIso (hX b) (hY c)).symm
theorem shiftedReflCorr_eq_reflForm (j : ℕ+)
    (ho : A.RepContinuousLocal j)
    (hc : A.RepConcatEqMul j)
    (hm : A.RepCommutesWithMirrors j)
    (hi : A.RepCommutesWithSymmetries j) (Z : combsSupportedIn upperHalfSpace)
    (s : InfiniteLattice.LatticePoint (A.mesh j)) (v : Space) (hs : (s : Space) = v)
    (hv : 0 ≤ v timeAxis) :
    DirectionPictures.shiftedReflCorr (A.measure j) timeAxis
        (A.repComb j Z) s =
      reflForm (A.mean j) Z (translateComb v hv Z) := by
  rw [reflForm_mean_eq_reflCorr A j ho hc hm]
  unfold DirectionPictures.shiftedReflCorr
  congr 1
  have e : latticeSymmetryToEuclid (InfiniteLattice.shift s) = EuclidIsometry.translate v :=
    euclidIsometry_ext (funext fun x => by
      change x + (s : Space) = x + v
      rw [hs])
  rw [hi (InfiniteLattice.shift s) Z, e]
  rfl
theorem translateComb_zero (Z : combsSupportedIn upperHalfSpace)
    (hv : 0 ≤ (0 : Space) timeAxis) : translateComb 0 hv Z = Z := by
  have e : push (translate 0) = id := by
    funext X
    apply Subtype.ext
    rw [push_translate]
    simp
  apply Subtype.ext
  change Finsupp.lmapDomain ℂ ℂ (push (translate 0)) (Z : TupleComb) = Z
  rw [e]
  simp
theorem coe_nsmul_axisStep (a : ℝ) (μ : Fin 4) (m : ℕ) :
    (((m • InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a)) : Space) =
      ((m : ℝ) * a) • PeriodicLattice.coordVec μ := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [InfiniteLattice.axisStep, PeriodicLattice.coordVec]
  · simp [InfiniteLattice.axisStep, PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
theorem embedSpatial_smul_single (c : ℝ) (i : Fin 3) :
    embedSpatial (c • EuclideanSpace.single i (1 : ℝ)) =
      c • PeriodicLattice.coordVec (spaceAxis i) := by
  funext μ
  induction μ using Fin.lastCases with
  | last =>
    have h := embedSpatial_timeAxis (c • EuclideanSpace.single i (1 : ℝ))
    rw [show Fin.last 3 = timeAxis from rfl, h]
    have ne : timeAxis ≠ spaceAxis i := (Fin.castSucc_lt_last i).ne'
    change 0 = c * (Pi.single (spaceAxis i) (1 : ℝ) : Space) timeAxis
    rw [Pi.single_eq_of_ne ne, mul_zero]
  | cast l =>
    have h := embedSpatial_spaceAxis (c • EuclideanSpace.single i (1 : ℝ)) l
    rw [show l.castSucc = spaceAxis l from rfl, h]
    by_cases e : l = i
    · subst e
      simp [PeriodicLattice.coordVec]
    · have e' : spaceAxis l ≠ spaceAxis i := fun h' =>
        e (Fin.castSucc_injective _ h')
      simp [PeriodicLattice.coordVec, Pi.single_eq_of_ne e', e]
theorem unitaryMonomial_zero {𝒦 : Type*} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦]
    [CompleteSpace 𝒦] {J : Type*} [Fintype J] [Nonempty J] (S : JointSpectrum.CommutingFamily 𝒦 J) :
    S.unitaryMonomial (fun _ => 0) = 1 := by
  unfold JointSpectrum.CommutingFamily.unitaryMonomial
  have h := Finset.noncommProd_eq_pow_card Finset.univ (fun α => S.B α ^ ((fun _ : J => (0 : ℤ)) α))
    (fun α _ α' _ _ => S.commute_zpow_unitary (fun _ => 0) α α') 1 (fun α _ => zpow_zero _)
  exact (congrArg (fun u : unitary (𝒦 →L[ℂ] 𝒦) => (u : 𝒦 →L[ℂ] 𝒦)) h).trans (by simp)
theorem inner_pow_two_mul_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) (h₀ : 0 ≤ T) (h₁ : T ≤ 1) (n : ℕ) (ψ : H) :
    inner ℂ ψ ((T ^ (2 * n)) ψ) ≤ inner ℂ ψ ψ := by
  have hs : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg h₀
  have hn : ‖T‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg T h₀).2 h₁
  have hp : ∀ (m : ℕ) (x : H), ‖(T ^ m) x‖ ≤ ‖x‖ := by
    intro m x
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ']
      calc ‖(T * T ^ m) x‖ = ‖T ((T ^ m) x)‖ := rfl
        _ ≤ ‖T‖ * ‖(T ^ m) x‖ := T.le_opNorm _
        _ ≤ 1 * ‖x‖ := mul_le_mul hn ih (norm_nonneg _) zero_le_one
        _ = ‖x‖ := one_mul _
  have e : inner ℂ ψ ((T ^ (2 * n)) ψ) = ((‖(T ^ n) ψ‖ ^ 2 : ℝ) : ℂ) := by
    have e₁ : (T ^ (2 * n)) ψ = (T ^ n) ((T ^ n) ψ) := by
      rw [two_mul, pow_add]
      rfl
    have hsym : ∀ x y, inner ℂ ((T ^ n) x) y = inner ℂ x ((T ^ n) y) := fun x y =>
      (hs.pow n).isSymmetric x y
    rw [e₁, ← hsym, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have e₂ : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [e, e₂, Complex.real_le_real]
  exact pow_le_pow_left₀ (norm_nonneg _) (hp n ψ) 2
theorem coe_pointOfUnit_nsmul (a : ℝ) (μ : Fin 4) (m : ℕ) :
    ((InfiniteLattice.pointOfUnit a
        (m • InfiniteLattice.axisStep 1 μ + DirectionPictures.intPoint 0) :
        InfiniteLattice.LatticePoint a) : Space) =
      ((m : ℝ) * a) • PeriodicLattice.coordVec μ := by
  have h := coe_nsmul_axisStep 1 μ m
  change a • (((m • InfiniteLattice.axisStep 1 μ + DirectionPictures.intPoint 0 :
    InfiniteLattice.LatticePoint 1)) : Space) = _
  rw [AddSubgroup.coe_add, h]
  funext ν
  simp [DirectionPictures.intPoint]
  ring
include hOne in
theorem reflForm_timeShift_le_of_mesh_mul (j : ℕ+) (ha : 0 < A.mesh j)
    (hν : A.measure j ∈ LatticeAtSpacing.reflectionPositiveSet (A.mesh j))
    (ho : A.RepContinuousLocal j)
    (hc : A.RepConcatEqMul j)
    (hm : A.RepCommutesWithMirrors j)
    (hi : A.RepCommutesWithSymmetries j) (Z : combsSupportedIn upperHalfSpace)
    (hloc : InfiniteLattice.IsLocalObservable (A.repComb j Z))
    (hF : A.repComb j Z ∈ InfiniteLattice.regionObservables (A.mesh j)
      (InfiniteLattice.closedHalfSpace timeAxis))
    (t : ℝ≥0) (n : ℕ) (ht : (t : ℝ) = (n : ℝ) * A.mesh j) :
    reflForm (A.mean j) Z (timeShiftComb (2 * t) Z) ≤
      reflForm (A.mean j) Z Z := by
  have hb := (hOne _ ha _ hν).2.1 timeAxis
  have e₂ := hb.1 _ _ hloc hF hloc hF (2 * n) 0 rfl
  have e₀ := hb.1 _ _ hloc hF hloc hF 0 0 rfl
  have hU : DirectionPictures.ScaledPair.shiftMonomial (A.measure j).1 timeAxis 0 = 1 :=
    unitaryMonomial_zero _
  rw [hU, mul_one] at e₂ e₀
  have f₂ := shiftedReflCorr_eq_reflForm A j ho hc hm hi Z
    (InfiniteLattice.pointOfUnit _
      ((2 * n) • InfiniteLattice.axisStep 1 timeAxis + DirectionPictures.intPoint 0))
    (timeShiftVec (2 * t))
    (by
      rw [coe_pointOfUnit_nsmul]
      change _ = (((2 * t : ℝ≥0) : ℝ)) • _
      push_cast
      rw [ht]
      congr 1
      ring)
    (by rw [timeShiftVec_timeAxis]; exact (2 * t).2)
  have f₀ := shiftedReflCorr_eq_reflForm A j ho hc hm hi Z
    (InfiniteLattice.pointOfUnit _
      (0 • InfiniteLattice.axisStep 1 timeAxis + DirectionPictures.intPoint 0)) 0
    (by rw [coe_pointOfUnit_nsmul]; simp) le_rfl
  rw [translateComb_zero] at f₀
  change reflForm (A.mean j) Z (translateComb (timeShiftVec (2 * t)) _ Z) ≤ _
  rw [← f₂, ← f₀]
  unfold DirectionPictures.shiftedReflCorr
  rw [← e₂, ← e₀]
  simpa using inner_pow_two_mul_le _ hb.2.1 hb.2.2 n _
include hL hA hl hRep hOne hAdic in
theorem contractsAtTime_of_mem_posAdicTimes (t : ℝ≥0) (ht : t ∈ posAdicTimes L) :
    ContractsAtTime σ t := by
  intro Z
  obtain ⟨ι, _, X, α, hX, hZ⟩ := exists_finite_expansion Z
  obtain ⟨δ, hδ, S, hSb, hSs, hS⟩ := exists_local_repComb hL A hRep timeZeroMirror X hX
  obtain ⟨-, -, -, h, -⟩ := hAdic L hL A.level A.level_strictMono
  obtain ⟨j₀, hj₀⟩ := h _ ht
  refine le_of_tendsto_of_tendsto (tendsto_reflForm_mean A hl Z _)
    (tendsto_reflForm_mean A hl Z Z) ?_
  filter_upwards [eventually_mesh_le hL A hδ, eventually_ge_atTop j₀] with j hj hj'
  obtain ⟨n, -, hn⟩ := hj₀ j hj'
  obtain ⟨-, hobs, -, hiso, hcc, -, -, hmir, -⟩ := hRep L hL.1 hL.2 A j
  have ha := mesh_pos hL A j
  have hF := hS j hj α
  rw [← hZ] at hF
  refine reflForm_timeShift_le_of_mesh_mul A hOne j ha (hA j) hobs hcc hmir hiso Z ⟨S, hSb, hF.2⟩
    ⟨hF.1, Measurable.mono hF.2 (InfiniteLattice.regionSigma_mono ?_) le_rfl⟩ t n ?_
  · intro x hx
    have h₁ := hSs hx
    change (0 : ℝ) ≤ euclidInner (PeriodicLattice.coordVec timeAxis) x at h₁
    rw [euclidInner_coordVec] at h₁
    exact h₁
  · have := (div_eq_iff ha.ne').1 hn
    exact this
include hOne in
theorem fivePointExpr_mean_nonneg (j : ℕ+) (ha : 0 < A.mesh j)
    (hν : A.measure j ∈ LatticeAtSpacing.reflectionPositiveSet (A.mesh j))
    (ho : A.RepContinuousLocal j)
    (hc : A.RepConcatEqMul j)
    (hm : A.RepCommutesWithMirrors j)
    (hi : A.RepCommutesWithSymmetries j) (Z : combsSupportedIn upperHalfSpace)
    (hloc : InfiniteLattice.IsLocalObservable (A.repComb j Z))
    (hF : A.repComb j Z ∈ InfiniteLattice.regionObservables (A.mesh j)
      (InfiniteLattice.closedHalfSpace timeAxis))
    (i : Fin 3) (t : ℝ≥0) (k : ℕ+) (ht : (t : ℝ) = ((k : ℕ) : ℝ) * A.mesh j) :
    0 ≤ fivePointExpr (A.mean j) i Z t := by
  have hne : spaceAxis i ≠ timeAxis := (Fin.castSucc_lt_last i).ne
  have h5 := (((hOne _ ha _ hν).2.2.1 timeAxis ⟨spaceAxis i, hne⟩ k).2 _ hloc hF).1
  have hs₁ : (((k : ℕ) • InfiniteLattice.axisStep (A.mesh j) timeAxis :
      InfiniteLattice.LatticePoint (A.mesh j)) : Space) = timeShiftVec t := by
    rw [coe_nsmul_axisStep, ← ht]
    rfl
  have hs₂ : (((2 * (k : ℕ)) • InfiniteLattice.axisStep (A.mesh j) timeAxis :
      InfiniteLattice.LatticePoint (A.mesh j)) : Space) = timeShiftVec (2 * t) := by
    rw [coe_nsmul_axisStep]
    change _ = (((2 * t : ℝ≥0) : ℝ)) • _
    push_cast
    rw [ht]
    congr 1
    ring
  have hs₃ : (((k : ℕ) • InfiniteLattice.axisStep (A.mesh j) (spaceAxis i) :
      InfiniteLattice.LatticePoint (A.mesh j)) : Space) =
      embedSpatial ((t : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by
    rw [coe_nsmul_axisStep, embedSpatial_smul_single, ← ht]
  have e₀ := shiftedReflCorr_eq_reflForm A j ho hc hm hi Z 0 0 rfl le_rfl
  have e₁ := shiftedReflCorr_eq_reflForm A j ho hc hm hi Z _ _ hs₁
    (by rw [timeShiftVec_timeAxis]; exact t.2)
  have e₂ := shiftedReflCorr_eq_reflForm A j ho hc hm hi Z _ _ hs₂
    (by rw [timeShiftVec_timeAxis]; exact (2 * t).2)
  have e₃ := shiftedReflCorr_eq_reflForm A j ho hc hm hi Z
    ((k : ℕ) • InfiniteLattice.axisStep (A.mesh j) timeAxis +
      (k : ℕ) • InfiniteLattice.axisStep (A.mesh j) (spaceAxis i))
    (timeShiftVec t + embedSpatial ((t : ℝ) • EuclideanSpace.single i (1 : ℝ)))
    (by rw [AddSubgroup.coe_add, hs₁, hs₃])
    (timeShiftVec_add_embedSpatial_timeAxis_nonneg t _)
  have e₄ := shiftedReflCorr_eq_reflForm A j ho hc hm hi Z
    ((k : ℕ) • InfiniteLattice.axisStep (A.mesh j) timeAxis -
      (k : ℕ) • InfiniteLattice.axisStep (A.mesh j) (spaceAxis i))
    (timeShiftVec t + embedSpatial ((-(t : ℝ)) • EuclideanSpace.single i (1 : ℝ)))
    (by
      rw [AddSubgroup.coe_sub, hs₁, hs₃, embedSpatial_smul_single, embedSpatial_smul_single,
        neg_smul, sub_eq_add_neg])
    (timeShiftVec_add_embedSpatial_timeAxis_nonneg t _)
  unfold DirectionPictures.fivePointCombination at h5
  rw [e₀, e₁, e₂, e₃, e₄] at h5
  exact h5
theorem tendsto_fivePointExpr_mean (hl : A.HasLimit σ) (i : Fin 3)
    (Z : combsSupportedIn upperHalfSpace) (t : ℝ≥0) :
    Tendsto (fun j => fivePointExpr (A.mean j) i Z t) atTop
      (𝓝 (fivePointExpr σ i Z t)) := by
  unfold fivePointExpr shiftedPairing
  exact ((((tendsto_reflForm_mean A hl _ _).sub
    ((tendsto_reflForm_mean A hl _ _).const_mul _)).add
    (tendsto_reflForm_mean A hl _ _)).add (tendsto_reflForm_mean A hl _ _)).add
    (tendsto_reflForm_mean A hl _ _)
include hL hA hl hRep hOne hAdic in
theorem fivePointPositive_of_hasLimit (i : Fin 3) :
    FivePointPositive σ i (posAdicTimes L) := by
  intro Z t ht
  obtain ⟨ι, _, X, α, hX, hZ⟩ := exists_finite_expansion Z
  obtain ⟨δ, hδ, S, hSb, hSs, hS⟩ := exists_local_repComb hL A hRep timeZeroMirror X hX
  obtain ⟨-, -, -, h, -⟩ := hAdic L hL A.level A.level_strictMono
  obtain ⟨j₀, hj₀⟩ := h _ ht
  refine ge_of_tendsto (tendsto_fivePointExpr_mean A hl i Z t) ?_
  filter_upwards [eventually_mesh_le hL A hδ, eventually_ge_atTop j₀] with j hj hj'
  obtain ⟨n, hn₀, hn⟩ := hj₀ j hj'
  obtain ⟨-, hobs, -, hiso, hcc, -, -, hmir, -⟩ := hRep L hL.1 hL.2 A j
  have ha := mesh_pos hL A j
  have hF := hS j hj α
  rw [← hZ] at hF
  refine fivePointExpr_mean_nonneg A hOne j ha (hA j) hobs hcc hmir hiso Z ⟨S, hSb, hF.2⟩
    ⟨hF.1, Measurable.mono hF.2 (InfiniteLattice.regionSigma_mono ?_) le_rfl⟩ i t ⟨n, hn₀⟩ ?_
  · intro x hx
    have h₁ := hSs hx
    change (0 : ℝ) ≤ euclidInner (PeriodicLattice.coordVec timeAxis) x at h₁
    rw [euclidInner_coordVec] at h₁
    exact h₁
  · exact (div_eq_iff ha.ne').1 hn
end Invariance
theorem exists_mem_posAdicTimes_between {L : ℕ} (hd : Dense (PeriodicLattice.adicGridPoints L))
    {lo hi : ℝ} (h₀ : 0 ≤ lo) (h : lo < hi) :
    ∃ t ∈ posAdicTimes L, lo < (t : ℝ) ∧ (t : ℝ) < hi := by
  obtain ⟨z, hz, h₁, h₂⟩ := hd.exists_between h
  have hp : 0 < z := lt_of_le_of_lt h₀ h₁
  exact ⟨⟨z, hp.le⟩, ⟨hz, hp⟩, h₁, h₂⟩
theorem Ioi_subset_closure_posAdicTimes {L : ℕ} (hd : Dense (PeriodicLattice.adicGridPoints L)) :
    Ioi 0 ⊆ closure (posAdicTimes L) := by
  intro t _
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  have hlt : max 0 ((t : ℝ) - ε) < (t : ℝ) + ε :=
    max_lt (by have := t.2; linarith) (by linarith)
  obtain ⟨b, hb, h₁, h₂⟩ := exists_mem_posAdicTimes_between hd (le_max_left _ _) hlt
  refine ⟨b, hb, ?_⟩
  rw [NNReal.dist_eq, abs_lt]
  have := lt_of_le_of_lt (le_max_right _ _) h₁
  constructor <;> linarith
theorem accPt_zero_posAdicTimes {L : ℕ} (hd : Dense (PeriodicLattice.adicGridPoints L)) :
    AccPt (0 : ℝ≥0) (𝓟 (posAdicTimes L)) := by
  refine accPt_iff_nhds.2 fun U hU => ?_
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨t, ht, h₁, h₂⟩ := exists_mem_posAdicTimes_between (L := L) hd le_rfl hε
  refine ⟨t, ⟨hb ?_, ht⟩, fun e => ?_⟩
  · rw [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_pos h₁]
    exact h₂
  · rw [e] at h₁
    simp at h₁
theorem isInvariant_of_mem_kernel_energy
    (hRec : DenseTimeReconstruction.DenseTimeReconstructionHolds)
    (hGen : EnergyMomentum.Generators.GeneratorsTheorem)
    (hSpec : EnergyMomentum.JointSpectral.JointSpectralMeasureTheorem)
    {σ : Tuple → ℝ} (hσ : FunctionalReconstruction.ReconstructionData σ)
    (hfix : ∀ i, FivePointCone.KernelTranslationInvariant σ hσ i)
    (ψ : ReconstructionSpace σ hσ.reflectionPositive)
    (hψ : ψ ∈ EuclideanSpectral.pmapKernel (FunctionalReconstruction.hamiltonianOp σ hσ)) :
    FunctionalReconstruction.IsInvariant σ hσ ψ := by
  obtain ⟨-, -, hc⟩ := hRec.2 σ hσ.reconstructionHypotheses
  obtain ⟨hT, hU, -, -, hJ⟩ := hc hσ.contractsOnDenseTimes
  have hsg : EnergyMomentum.IsContractionSemigroupWithUnitaryGroup
      (transferSemigroup σ hσ.reflectionPositive)
      (spatialTranslationRep σ hσ.reflectionPositive) :=
    { isSelfAdjoint := fun t => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y =>
        (hT.isSelfAdjoint t x y).symm
      norm_le_one := hT.isContraction
      semigroup_zero := hT.zero
      semigroup_add := hT.add
      isUnitary := fun y => ⟨(hU.isUnitary y).bijective, (hU.isUnitary y).norm_map⟩
      group_add := hU.add
      semigroup_mul_group := hU.commutes
      continuous_semigroup := hT.isStronglyContinuous
      continuous_group := hU.isStronglyContinuous }
  obtain ⟨-, -, -, hK, -⟩ := hGen _ _ _ hsg
  have hEq := (hSpec _ _ _ hsg).1.2.1 _ hJ.isJointSpectralMeasure
  have hψ' : ψ ∈ EuclideanSpectral.pmapKernel (EnergyMomentum.Generators.hamiltonian
      (transferSemigroup σ hσ.reflectionPositive)
      (spatialTranslationRep σ hσ.reflectionPositive)) := by
    unfold EnergyMomentum.Generators.hamiltonian
    rw [← hEq]
    exact hψ
  refine ⟨((hK.tfae ψ).out 0 1).1 hψ', fun v => ?_⟩
  have hi : ∀ (i : Fin 3) (u : ℝ), spatialTranslationRep σ hσ.reflectionPositive
      (u • EuclideanSpace.single i (1 : ℝ)) ψ = ψ := by
    intro i u
    have e := hJ.isJointSpectralMeasure 0 (u • EuclideanSpace.single i (1 : ℝ))
    rw [hT.zero, one_mul] at e
    have e₁ : EnergyMomentum.laplaceFourierExp 0 (u • EuclideanSpace.single i (1 : ℝ)) =
        EnergyMomentum.expCoordMomentum i u := by
      funext p
      have hdot : EnergyMomentum.spatialDot (u • EuclideanSpace.single i (1 : ℝ)) p.2 =
          u * p.2 i := by
        simp [EnergyMomentum.spatialDot, Finset.sum_ite_eq']
      simp only [EnergyMomentum.laplaceFourierExp, EnergyMomentum.expCoordMomentum, hdot]
      simp
    rw [e, e₁]
    exact hfix i ψ hψ u
  have hv : v = v 0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      (v 1 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
        v 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
    ext l
    fin_cases l <;> simp
  rw [hv, ← hU.add, ← hU.add]
  change spatialTranslationRep σ hσ.reflectionPositive _
    (spatialTranslationRep σ hσ.reflectionPositive _
      (spatialTranslationRep σ hσ.reflectionPositive _ ψ)) = ψ
  rw [hi, hi, hi]
theorem latticeLimitProperties_holds (hAdic : FineLatticeAdicData.AdicDataLatticeData)
    (hCone : FivePointCone.FivePointConeTheorem)
    (hGen : EnergyMomentum.Generators.GeneratorsTheorem)
    (hSpec : EnergyMomentum.JointSpectral.JointSpectralMeasureTheorem)
    (hMov : MovingTestFunctions.statement)
    (hOne : DirectionPictures.singleLatticeInputs)
    (hRec : DenseTimeReconstruction.DenseTimeReconstructionHolds)
    (hRep : TupleRepresentatives.Statement) : LatticeLimitProperties := by
  intro L hLo hL13 A σ hA hl hσ
  have hL : Conventions.IsAdmissibleBlockingFactor L := ⟨hLo, hL13⟩
  have hd : Dense (PeriodicLattice.adicGridPoints L) :=
    (hAdic L hL A.level A.level_strictMono).1.2.1
  have hsym : IsPermInvariant σ := isPermInvariant_of_hasLimit A hl fun j =>
    (hRep L hL.1 hL.2 A j).2.2.2.2.2.2.2.2.2.1
  have hmul : IsSlotLinear σ := isSlotLinear_of_hasLimit A hl fun j =>
    (hRep L hL.1 hL.2 A j).2.2.2.2.2.2.2.2.2.2.1
  have hmir := isIsomInvariant_reflectIso hL A hA hl hσ hRep hOne hAdic hMov
  have hrp := reflectionPositiveAt_of_hasLimit hL A hA hl hσ hRep hAdic hMov
  have hT := isTranslInvariant_of_hasLimit hL A hA hl hσ hRep hOne hAdic hMov
  have hcon := contractsAtTime_of_mem_posAdicTimes hL A hA hl hRep hOne hAdic
  have hrec : FunctionalReconstruction.ReconstructionData σ :=
    ⟨⟨hl.1, hσ, hsym, hT, hmir timeZeroMirror, hrp timeZeroMirror⟩,
      ⟨posAdicTimes L, fun t ht => ht.2, Ioi_subset_closure_posAdicTimes hd, hcon⟩⟩
  have hfive := fivePointPositive_of_hasLimit hL A hA hl hRep hOne hAdic
  have hcone := fun i => (hCone σ hrec i).1 (posAdicTimes L) (fun t ht => ht.2)
    (accPt_zero_posAdicTimes hd) (hfive i)
  have hdom : ∀ i, FunctionalReconstruction.EnergyDominatesMomentum σ hrec i := fun i =>
    (hcone i).2.2.1.energyDominates
  refine ⟨⟨hsym, hmul, fun r hr => ?_, hmir, hrp⟩, hcon, hfive,
    ⟨hrec, hdom, fun ψ hψ => isInvariant_of_mem_kernel_energy hRec hGen hSpec hrec
      (fun i => (hcone i).2.2.2.2) ψ hψ⟩, ⟨hrec, hdom⟩⟩
  obtain ⟨r', he, hi⟩ :=
    exists_isIsomInvariant_of_mem_group hL A hA hl hσ hRep hOne hAdic hMov _ hr
  have e : r' = r :=
    euclidIsometry_ext (funext fun x => congrArg (fun g : Equiv.Perm Space => g x) he)
  rw [← e]
  exact hi
end YangMills.Construction.ReflectionPositivity.LatticeLimits
