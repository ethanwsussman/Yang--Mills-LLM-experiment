import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheFineCaseProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.InfiniteLattice.CoveringMapAndThePeriodicExtensionAtACutoff
import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.InfiniteLattice.PeriodisationAndThreeIdentitiesOfTheCovering
import YangMills.Construction.Lattice.ConnectedFunctionsAreAFiniteSumOverPlaquettes
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotionsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
namespace YangMills.Construction.PeriodizationIdentities
open InfiniteLattice (IsBoundedBorelCompactlySupported AmbientSpace liftCompactField smearedEnergyCumulant
  smearedEnergy)
open InfiniteLattice.PeriodicLiftAtCutoff (cutoffConnectedFunction periodizeTuple)
open InfiniteLattice.PeriodicTorusMeasures (measureConnectedFunction pushforwardWilsonMeasure)
open TestFunctions (latticeTranslate periodicSum periodize)
open TorusMetric (torusProj torusEuclidNorm euclidNormVec)
section IndexBound
variable {ℓ : ℝ}
lemma exists_finset_index_bound {S : Set AmbientSpace} (hS : Bornology.IsBounded S) (hℓ : 0 < ℓ)
    (r : ℝ) :
    ∃ B : Finset (Fin 4 → ℤ), ∀ y : AmbientSpace, (∀ μ, |y μ| ≤ r) → ∀ k,
      y + latticeTranslate ℓ k ∈ S → k ∈ B := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  refine ⟨Fintype.piFinset fun _ => Finset.Icc (-⌈(R + r) / ℓ⌉) ⌈(R + r) / ℓ⌉, ?_⟩
  intro y hy k hk
  rw [Fintype.mem_piFinset]
  intro μ
  have hnorm : |(y + latticeTranslate ℓ k) μ| ≤ R := (norm_le_pi_norm _ μ).trans (hR _ hk)
  obtain ⟨lo, hi⟩ := abs_le.mp hnorm
  obtain ⟨ylo, yhi⟩ := abs_le.mp (hy μ)
  have hcoord : (y + latticeTranslate ℓ k) μ = y μ + ℓ * (k μ : ℝ) := rfl
  rw [hcoord] at lo hi
  have upper : (k μ : ℝ) ≤ (R + r) / ℓ := by
    rw [le_div_iff₀ hℓ]
    linarith
  have lower : -((R + r) / ℓ) ≤ (k μ : ℝ) := by
    rw [neg_le, le_div_iff₀ hℓ]
    linarith
  have upper' : (k μ : ℝ) ≤ (⌈(R + r) / ℓ⌉ : ℝ) := upper.trans (Int.le_ceil _)
  have lower' : -(⌈(R + r) / ℓ⌉ : ℝ) ≤ (k μ : ℝ) := (neg_le_neg (Int.le_ceil _)).trans lower
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast lower'
  · exact_mod_cast upper'
variable {E : Type*} [NormedAddCommGroup E]
lemma finite_support_translates (hℓ : 0 < ℓ) {v : AmbientSpace → E} (hc : HasCompactSupport v)
    (x : AmbientSpace) :
    {k : Fin 4 → ℤ | v (x + latticeTranslate ℓ k) ≠ 0}.Finite := by
  obtain ⟨B, hB⟩ := exists_finset_index_bound hc.isCompact.isBounded hℓ ‖x‖
  refine B.finite_toSet.subset fun k hk => ?_
  exact hB x (fun μ => norm_le_pi_norm x μ) k (subset_tsupport v hk)
lemma periodicSum_norm_bounded (hℓ : 0 < ℓ) {v : AmbientSpace → E}
    (hb : ∃ C : ℝ, ∀ x, ‖v x‖ ≤ C) (hc : HasCompactSupport v) :
    ∃ C : ℝ, ∀ x, ‖periodicSum ℓ v x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨B, hB⟩ := exists_finset_index_bound hc.isCompact.isBounded hℓ ℓ
  refine ⟨B.card • C, fun x => ?_⟩
  set n : Fin 4 → ℤ := fun μ => -⌊x μ / ℓ⌋ with hn
  have hy : ∀ μ, |(x + latticeTranslate ℓ n) μ| ≤ ℓ := by
    intro μ
    have hfract : (x + latticeTranslate ℓ n) μ = ℓ * Int.fract (x μ / ℓ) := by
      have : x μ = ℓ * (x μ / ℓ) := by field_simp
      simp only [Pi.add_apply, latticeTranslate, hn, Int.fract, Int.cast_neg]
      nth_rewrite 1 [this]
      ring
    rw [hfract, abs_of_nonneg (mul_nonneg hℓ.le (Int.fract_nonneg _))]
    nlinarith [Int.fract_lt_one (x μ / ℓ)]
  rw [← TestFunctions.periodicSum_add_latticeTranslate ℓ v x n]
  have hz : ∀ k ∉ B, v (x + latticeTranslate ℓ n + latticeTranslate ℓ k) = 0 := by
    intro k hk
    by_contra h
    exact hk (hB _ hy k (subset_tsupport v h))
  unfold periodicSum
  rw [tsum_eq_sum hz]
  refine (norm_sum_le_of_le B fun k _ => hC _).trans_eq ?_
  simp
end IndexBound
lemma torusSide_pos {L m : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    0 < PeriodicLattice.torusSide L m := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.torusSide_pos <;> assumption
lemma periodicSumDescends_holds {L m : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    PeriodicSumDescends L m := by
  intro v hv
  obtain ⟨-, hb, hc⟩ := hv
  have hℓ := torusSide_pos (m := m) hL
  refine ⟨finite_support_translates hℓ hc, periodicSum_norm_bounded hℓ hb hc,
    TestFunctions.periodicSum_add_latticeTranslate _ v,
    ⟨periodize _ v, funext (TestFunctions.periodize_torusProj _ v), fun g hg => funext fun y => ?_⟩,
    funext (TestFunctions.periodize_torusProj _ v), ?_⟩
  · obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ y
    rw [TestFunctions.periodize_torusProj]
    exact congrFun hg x
  · rintro ⟨D, -, hD, hdiam⟩
    exact ⟨fun x hx y hy => (hdiam x hx y hy).trans hD.le, subset_tsupport v⟩
section FaceSum
open InfiniteLattice.CutoffCoverLift
variable {L m K : ℕ}
lemma latticeTranslate_mem_latticeSubgroup (ℓ : ℝ) (k : Fin 4 → ℤ) :
    latticeTranslate ℓ k ∈ InfiniteLattice.latticeSubgroup ℓ :=
  ⟨k, fun _ => mul_comm _ _⟩
lemma finsum_faces_eq_finsum_torus_faces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : PointsAndLinks L m K) (hP : FacesCovered L m K) (hℓ : 0 < PeriodicLattice.torusSide L m)
    (c : PeriodicLattice.Plaquette L m (K : ℤ) → ℝ) (v : AmbientSpace → E)
    (hfin : {p : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) |
      v p.center ≠ 0}.Finite)
    (hk : ∀ x : AmbientSpace, {k : Fin 4 → ℤ |
      v (x + latticeTranslate (PeriodicLattice.torusSide L m) k) ≠ 0}.Finite) :
    ∑ᶠ p : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)),
        c (CutoffLattice.projectFace L m K p) • v p.center =
      ∑ᶠ q : PeriodicLattice.Plaquette L m (K : ℤ),
        c q • periodize (PeriodicLattice.torusSide L m) v q.barycenter := by
  classical
  obtain ⟨hP1, hP2, hP3⟩ := hP
  choose lift hlift using hP2
  let shift : (Fin 4 → ℤ) → InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L (K : ℤ)) :=
    fun k => ⟨latticeTranslate (PeriodicLattice.torusSide L m) k,
      hS.1 (latticeTranslate_mem_latticeSubgroup _ k)⟩
  let Φ : PeriodicLattice.Plaquette L m (K : ℤ) × (Fin 4 → ℤ) →
      InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) := fun qk =>
    ⟨(lift qk.1).corner + shift qk.2, (lift qk.1).lowAxis, (lift qk.1).highAxis,
      (lift qk.1).lowAxis_lt_highAxis⟩
  have hcenter : ∀ q k, (Φ (q, k)).center =
      (lift q).center + latticeTranslate (PeriodicLattice.torusSide L m) k := by
    intro q k
    simp only [InfiniteLattice.ElementaryPlaquette.center, Φ, shift, AddSubgroup.coe_add]
    abel
  have hproj : ∀ q k, CutoffLattice.projectFace L m K (Φ (q, k)) = q := by
    intro q k
    refine ((hP3 (lift q) (Φ (q, k))).2 ⟨rfl, ?_⟩).symm.trans (hlift q)
    have : ((Φ (q, k)).corner : AmbientSpace) - ((lift q).corner : AmbientSpace) =
        latticeTranslate (PeriodicLattice.torusSide L m) k := by
      simp [Φ, shift]
    rw [this]
    exact latticeTranslate_mem_latticeSubgroup _ k
  have hinj : Function.Injective Φ := by
    rintro ⟨q, k⟩ ⟨q', k'⟩ h
    have hq : q = q' := by rw [← hproj q k, ← hproj q' k', h]
    subst hq
    have hshift : (shift k : AmbientSpace) = shift k' := by
      have hc := congrArg (fun p => (p.corner : AmbientSpace)) h
      simpa [Φ] using hc
    have hkk : k = k' := by
      funext μ
      have hμ := congrFun hshift μ
      have hmul : PeriodicLattice.torusSide L m * (k μ : ℝ) =
          PeriodicLattice.torusSide L m * (k' μ : ℝ) := hμ
      exact_mod_cast mul_left_cancel₀ hℓ.ne' hmul
    rw [hkk]
  have hsurj : Function.Surjective Φ := by
    intro p
    obtain ⟨hdir, n, hn⟩ := (hP3 (lift (CutoffLattice.projectFace L m K p)) p).1 (hlift _)
    have hd1 := congrArg Prod.fst hdir
    have hd2 := congrArg Prod.snd hdir
    refine ⟨(CutoffLattice.projectFace L m K p, n), ?_⟩
    refine InfiniteLattice.ElementaryPlaquette.ext ?_ hd1 hd2
    refine Subtype.ext (funext fun μ => ?_)
    have hnμ := hn μ
    simp only [Pi.sub_apply] at hnμ
    show ((lift (CutoffLattice.projectFace L m K p)).corner : AmbientSpace) μ +
      PeriodicLattice.torusSide L m * (n μ : ℝ) = (p.corner : AmbientSpace) μ
    rw [mul_comm, ← hnμ]
    ring
  let e := Equiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hsupp : (Function.support fun qk : PeriodicLattice.Plaquette L m (K : ℤ) × (Fin 4 → ℤ) =>
      c (CutoffLattice.projectFace L m K (e qk)) • v (e qk).center).Finite := by
    refine (hfin.preimage hinj.injOn).subset fun qk hqk => ?_
    intro h0
    apply hqk
    show c _ • v (Φ qk).center = 0
    have : v (Φ qk).center = 0 := by simpa using h0
    rw [this, smul_zero]
  rw [← finsum_comp_equiv e, finsum_curry _ hsupp]
  refine finsum_congr fun q => ?_
  have hq : q.barycenter = torusProj (PeriodicLattice.torusSide L m) (lift q).center := by
    have hb := (hP1 (lift q)).2
    rw [hlift q] at hb
    exact hb
  rw [hq, TestFunctions.periodize_torusProj, periodicSum, tsum_eq_finsum (hk _), smul_finsum]
  refine finsum_congr fun k => ?_
  show c (CutoffLattice.projectFace L m K (Φ (q, k))) • v (Φ (q, k)).center = _
  rw [hproj, hcenter]
end FaceSum
section SmearedEnergies
open FieldsAtSpacing
variable {a : ℝ}
lemma finite_faces_center_support {E : Type*} [NormedAddCommGroup E]
    (hR : FaceFunctionProperties a) {v : AmbientSpace → E} (hc : HasCompactSupport v) :
    {p : InfiniteLattice.ElementaryPlaquette a | v p.center ≠ 0}.Finite :=
  (hR.2.1 _ hc.isCompact.isBounded).subset fun _ hp => subset_tsupport v hp
lemma smearedEnergy_ofReal (hR : FaceFunctionProperties a) {f : AmbientSpace → ℝ}
    (hc : HasCompactSupport f) (U : InfiniteLattice.GaugeField a) :
    ((smearedEnergy f U : ℝ) : ℂ) = smearedEnergy (fun x => (f x : ℂ)) U := by
  have hfin : (Function.support fun p : InfiniteLattice.ElementaryPlaquette a =>
      InfiniteLattice.faceEnergy U p • f p.center).Finite := by
    refine (finite_faces_center_support hR hc).subset fun p hp h0 => hp ?_
    show _ • f p.center = 0
    rw [h0, smul_zero]
  have h := (Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.map_finsum hfin
  refine h.trans (finsum_congr fun p => ?_)
  simp
end SmearedEnergies
lemma isBoundedObservable_of_mem {a : ℝ} (ha : 0 < a)
    (hR : FieldsAtSpacing.LinkFunctionsStatement)
    {F : InfiniteLattice.GaugeField a → ℂ}
    (hF : F ∈ FieldsAtSpacing.continuousFiniteLinkFunctions a) :
    InfiniteLattice.IsBoundedObservable F := by
  obtain ⟨-, -, hc, hd, -, -⟩ := hR a ha ∅ (empty_subset _)
  rw [hd.2.2.2] at hF
  obtain ⟨⟨S, -, hS⟩, -⟩ := hF
  rw [(hc.1 S).2.1] at hS
  exact hS.1
lemma smearedEnergy_real_measurable_bounded {a : ℝ} (ha : 0 < a)
    (hR : FieldsAtSpacing.LinkFunctionsStatement)
    {f : AmbientSpace → ℝ} (hf : IsBoundedBorelCompactlySupported f) :
    Measurable (smearedEnergy (a := a) f) ∧
      ∃ C : ℝ, ∀ U, |smearedEnergy (a := a) f U| ≤ C := by
  obtain ⟨hm, ⟨C, hC⟩, hc⟩ := hf
  have hP := (hR a ha ∅ (empty_subset _)).2.2.2.2.2
  have hv : IsBoundedBorelCompactlySupported (fun x => (f x : ℂ)) :=
    ⟨Complex.measurable_ofReal.comp hm, ⟨C, fun x => by simpa using hC x⟩,
      hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)⟩
  obtain ⟨hO, C', hC'⟩ := isBoundedObservable_of_mem ha hR (hP.2.2.1 _ hv).2.1
  have he : ∀ U, smearedEnergy (a := a) f U =
      (smearedEnergy (a := a) (fun x => (f x : ℂ)) U).re := by
    intro U
    rw [← smearedEnergy_ofReal hP hc, Complex.ofReal_re]
  refine ⟨?_, C', fun U => ?_⟩
  · have : smearedEnergy (a := a) f = fun U =>
        (smearedEnergy (a := a) (fun x => (f x : ℂ)) U).re := funext he
    rw [this]
    exact Complex.measurable_re.comp hO
  · rw [he]
    exact (Complex.abs_re_le_norm _).trans (hC' U)
section GibbsMeasures
variable {L m K : ℕ}
lemma measurable_compactGaugeField_val {j : ℤ} :
    Measurable (fun U : PeriodicLattice.CompactGaugeField L m j => U.1) :=
  measurable_pi_iff.2 fun b =>
    (continuous_subtype_val.comp (continuous_iInf_dom continuous_induced_dom :
      Continuous fun U : PeriodicLattice.CompactGaugeField L m j => U.linkValue b)).measurable
lemma pushforwardWilson_eq_map_lift {β : ℝ}
    (h : (PeriodicLattice.normalizedActionMeasure L m K β).map (fun U => U.1) =
      PeriodicLattice.wilsonGibbsMeasure L m K β) :
    pushforwardWilsonMeasure L m K β =
      (PeriodicLattice.normalizedActionMeasure L m K β).map liftCompactField := by
  show (PeriodicLattice.wilsonGibbsMeasure L m K β).map (InfiniteLattice.liftField L m (K : ℤ)) = _
  rw [← h, Measure.map_map (InfiniteLattice.measurable_liftField L m (K : ℤ))
    measurable_compactGaugeField_val]
  rfl
lemma integral_pushforwardWilson {β : ℝ}
    (h : (PeriodicLattice.normalizedActionMeasure L m K β).map (fun U => U.1) =
      PeriodicLattice.wilsonGibbsMeasure L m K β)
    {F : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ} (hF : Measurable F) :
    ∫ U, F U ∂pushforwardWilsonMeasure L m K β =
      ∫ U, F (liftCompactField U) ∂PeriodicLattice.normalizedActionMeasure L m K β := by
  rw [pushforwardWilson_eq_map_lift h]
  exact integral_map InfiniteLattice.continuous_liftCompactField.measurable.aemeasurable
    hF.aestronglyMeasurable
variable [Fintype (PeriodicLattice.Plaquette L m (K : ℤ))]
omit [Fintype (PeriodicLattice.Plaquette L m (K : ℤ))] in
lemma plaquetteEnergy_eq_ofReal
    (hA : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (K : ℤ))
    (p : PeriodicLattice.Plaquette L m (K : ℤ)) (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    PeriodicLattice.plaquetteEnergy U.1 p = (PeriodicLattice.plaquetteCost U.1 p : ℂ) := by
  obtain ⟨t, -, ht⟩ := (hA p).2 U
  have h : PeriodicLattice.plaquetteCost U.1 p = (PeriodicLattice.plaquetteEnergy U.1 p).re := by
    simp [PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteEnergy]
  rw [h, ← ht]
  simp
lemma barycenterWeightedEnergy_eq_sum (c : PeriodicLattice.FourTorus L m → ℂ)
    (U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2) :
    PeriodicLattice.barycenterWeightedEnergy c U = ∑ p : PeriodicLattice.Plaquette L m (K : ℤ),
      c p.barycenter * PeriodicLattice.plaquetteEnergy U p :=
  finsum_eq_sum_of_fintype _
def totalEnergy (β : ℝ) (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) : ℝ :=
  ∑ p : PeriodicLattice.Plaquette L m (K : ℤ), β * PeriodicLattice.plaquetteCost U.1 p
lemma barycenterWeightedEnergy_const
    (hA : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (K : ℤ))
    (β : ℝ) (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    PeriodicLattice.barycenterWeightedEnergy (fun _ => (β : ℂ)) U.1 = (totalEnergy β U : ℂ) := by
  rw [barycenterWeightedEnergy_eq_sum, totalEnergy, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [plaquetteEnergy_eq_ofReal hA, Complex.ofReal_mul]
lemma neg_weightedEnergy_sub
    (hA : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (K : ℤ))
    (β : ℝ) (w : PeriodicLattice.FourTorus L m → ℂ)
    (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    -PeriodicLattice.barycenterWeightedEnergy (fun y => (β : ℂ) - w y) U.1 =
      -(totalEnergy β U : ℂ) + PeriodicLattice.smearedObservable w U.1 := by
  rw [← barycenterWeightedEnergy_const hA, barycenterWeightedEnergy_eq_sum,
    barycenterWeightedEnergy_eq_sum, PeriodicLattice.smearedObservable,
    finsum_eq_sum_of_fintype, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [plaquetteEnergy_eq_ofReal hA, Complex.real_smul]
  ring
lemma boltzmannFactor_re
    (hA : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (K : ℤ))
    (β : ℝ) (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    (Complex.exp (-PeriodicLattice.barycenterWeightedEnergy (fun _ => (β : ℂ)) U.1)).re =
      Real.exp (-totalEnergy β U) := by
  rw [barycenterWeightedEnergy_const hA, ← Complex.ofReal_neg, Complex.exp_ofReal_re]
lemma continuous_totalEnergy
    (hA : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (K : ℤ)) (β : ℝ) :
    Continuous (totalEnergy β : PeriodicLattice.CompactGaugeField L m (K : ℤ) → ℝ) := by
  refine continuous_finsetSum _ fun p _ => continuous_const.mul ?_
  have h : (fun U : PeriodicLattice.CompactGaugeField L m (K : ℤ) =>
      PeriodicLattice.plaquetteCost U.1 p) =
      fun U => (PeriodicLattice.plaquetteEnergy U.1 p).re := by
    funext U
    rw [plaquetteEnergy_eq_ofReal hA, Complex.ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp (hA p).1
lemma integral_boltzmannMeasure
    (hA : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (K : ℤ))
    {β : ℝ} (hZ : 0 < (PeriodicLattice.sourcedPartitionFunction L m K β 0).re)
    (F : PeriodicLattice.CompactGaugeField L m (K : ℤ) → ℂ) :
    ∫ U, F U ∂PeriodicLattice.normalizedActionMeasure L m K β =
      (((PeriodicLattice.sourcedPartitionFunction L m K β 0).re : ℝ) : ℂ)⁻¹ *
        ∫ U, (Real.exp (-totalEnergy β U) : ℂ) * F U
          ∂PeriodicLattice.gaugeFieldMeasure L m (K : ℤ) := by
  have hfun : (fun U : PeriodicLattice.CompactGaugeField L m (K : ℤ) => ENNReal.ofReal
      (Complex.exp (-PeriodicLattice.barycenterWeightedEnergy (fun _ => (β : ℂ)) U.1)).re) =
      fun U => ENNReal.ofReal (Real.exp (-totalEnergy β U)) := by
    funext U
    rw [boltzmannFactor_re hA]
  have hmeas : Measurable (fun U : PeriodicLattice.CompactGaugeField L m (K : ℤ) =>
      ENNReal.ofReal (Real.exp (-totalEnergy β U))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_totalEnergy hA β).neg).measurable
  unfold PeriodicLattice.normalizedActionMeasure
  rw [hfun, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun U => ENNReal.ofReal_lt_top),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le, Complex.real_smul, Complex.ofReal_inv]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only []
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, Complex.ofReal_exp]
end GibbsMeasures
section LiftIdentities
open InfiniteLattice.CutoffCoverLift ConnectedFunctionExpansion
variable {L m K : ℕ}
lemma smearedEnergy_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : PointsAndLinks L m K) (hP : FacesCovered L m K)
    (hE : ∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ), LiftOfField L m K U)
    (hR : FieldsAtSpacing.FaceFunctionProperties (PeriodicLattice.meshSize L (K : ℤ)))
    (hℓ : 0 < PeriodicLattice.torusSide L m) {v : AmbientSpace → E} (hc : HasCompactSupport v)
    (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    smearedEnergy v (liftCompactField U) =
      PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide L m) v) U.1 := by
  refine (finsum_congr fun p => ?_).trans (finsum_faces_eq_finsum_torus_faces hS hP hℓ
    (fun q => PeriodicLattice.plaquetteCost U.1 q) v (finite_faces_center_support hR hc)
    (finite_support_translates hℓ hc))
  rw [((hE U).2.1 p).2]
lemma expMomentRatio_holds [Fintype (PeriodicLattice.Plaquette L m (K : ℤ))] {β : ℝ}
    (hA : GaugeFieldProduct.PlaquetteEnergyContinuousBounded L m (K : ℤ))
    (hZre : 0 < (PeriodicLattice.sourcedPartitionFunction L m K β 0).re)
    (hZim : (PeriodicLattice.sourcedPartitionFunction L m K β 0).im = 0)
    (hZ : PeriodicLattice.sourcedPartitionFunction L m K β 0 =
      (PeriodicLattice.partitionFunction L m K β : ℂ))
    (hW : (PeriodicLattice.normalizedActionMeasure L m K β).map (fun U => U.1) =
      PeriodicLattice.wilsonGibbsMeasure L m K β)
    (hO : ∀ v : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported v →
      ∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
        smearedEnergy v (liftCompactField U) =
          PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide L m) v) U.1)
    (hM : ∀ v : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported v → Measurable
      (smearedEnergy (a := PeriodicLattice.meshSize L (K : ℤ)) v)) :
    ExpMomentRatio L m K β := by
  have hpos : 0 < PeriodicLattice.partitionFunction L m K β := by
    rw [hZ, Complex.ofReal_re] at hZre
    exact hZre
  refine ⟨hZ, hpos, fun v hv => ?_⟩
  rw [integral_pushforwardWilson hW (F := fun U => Complex.exp (smearedEnergy v U))
    (Complex.measurable_exp.comp (hM v hv)), integral_boltzmannMeasure hA hZre]
  have hzero : InfiniteLattice.weightedPartitionFn L m K β 0 =
      (((PeriodicLattice.sourcedPartitionFunction L m K β 0).re : ℝ) : ℂ) :=
    Complex.ext (by simp [InfiniteLattice.weightedPartitionFn_eq_sourced])
      (by simpa [InfiniteLattice.weightedPartitionFn_eq_sourced])
  rw [hzero, div_eq_inv_mul]
  congr 1
  unfold InfiniteLattice.weightedPartitionFn
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  show (Real.exp (-totalEnergy β U) : ℂ) * Complex.exp (smearedEnergy v (liftCompactField U)) =
    Complex.exp (-PeriodicLattice.barycenterWeightedEnergy
      (fun y => (β : ℂ) - periodize (PeriodicLattice.torusSide L m) v y) U.1)
  rw [hO v hv U, neg_weightedEnergy_sub hA, Complex.exp_add, Complex.ofReal_exp,
    Complex.ofReal_neg]
lemma isBoundedOnTorus_of_bound {g : PeriodicLattice.FourTorus L m → ℝ} {C : ℝ}
    (h : ∀ y, ‖g y‖ ≤ C) : ConnectedFunctionExpansion.IsBoundedOnTorus g := by
  unfold ConnectedFunctionExpansion.IsBoundedOnTorus PeriodicLattice.torusSupNorm
  exact ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C))
    (iSup_le fun y => ENNReal.ofReal_le_ofReal (h y))
lemma periodize_norm_bounded {ℓ : ℝ} (hℓ : 0 < ℓ) {f : AmbientSpace → ℝ}
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ y, ‖periodize ℓ f y‖ ≤ C := by
  obtain ⟨C, hC⟩ := periodicSum_norm_bounded hℓ hb hc
  refine ⟨C, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective ℓ y
  rw [TestFunctions.periodize_torusProj]
  exact hC x
lemma liftCumulants_holds {β : ℝ} (hK : 0 < K) (hβ : 0 < β)
    (hℓ : 0 < PeriodicLattice.torusSide L m)
    (hI : IsProbabilityMeasure (pushforwardWilsonMeasure L m K β))
    (hC : ConnectedFunctionEqCumulant L m K)
    (hW : (PeriodicLattice.normalizedActionMeasure L m K β).map (fun U => U.1) =
      PeriodicLattice.wilsonGibbsMeasure L m K β)
    (hO : ∀ f : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported f →
      ∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
        smearedEnergy f (liftCompactField U) =
          PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide L m) f) U.1)
    (hM : ∀ f : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported f →
      Measurable (smearedEnergy (a := PeriodicLattice.meshSize L (K : ℤ)) f) ∧
        ∃ C : ℝ, ∀ U, |smearedEnergy (a := PeriodicLattice.meshSize L (K : ℤ)) f U| ≤ C) :
    LiftCumulants L m K β := by
  intro n f hn hf
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hbd : ∀ i, ConnectedFunctionExpansion.IsBoundedOnTorus (periodizeTuple L m f i) := by
    intro i
    obtain ⟨C, hCb⟩ := periodize_norm_bounded hℓ (hf i).2.1 (hf i).2.2
    exact isBoundedOnTorus_of_bound hCb
  have hre := (hC.1 β).1
  have hmem : (β : ℂ) ∈ PeriodicLattice.nonvanishingCouplings L m K := by
    intro h0
    rw [h0] at hre
    simp at hre
  have hcum := hC.2 n (β : ℂ) (periodizeTuple L m f) hmem hbd
  have hgibbs : PeriodicLattice.observableCumulant L m K (β : ℂ) (periodizeTuple L m f) =
      PeriodicLattice.gibbsCumulant L m K β
        (fun i U => PeriodicLattice.smearedObservable (periodizeTuple L m f i) U) := by
    unfold PeriodicLattice.observableCumulant
    rw [if_pos ⟨hK, by simpa using hβ, by simp⟩]
    simp only [Complex.ofReal_re]
  have hmixed := ((hC.1 β).2.2.2.1 n (periodizeTuple L m f) hbd).2
  have hmgf : Cumulants.momentGeneratingFunction (pushforwardWilsonMeasure L m K β)
      (fun i U => smearedEnergy (f i) U) =
      Cumulants.momentGeneratingFunction (PeriodicLattice.normalizedActionMeasure L m K β)
        (fun i => PeriodicLattice.observableOnFields (J := K) (periodizeTuple L m f i)) := by
    funext t
    unfold Cumulants.momentGeneratingFunction
    rw [integral_pushforwardWilson hW
      (F := fun U => Complex.exp (∑ i, t i * ((smearedEnergy (f i) U : ℝ) : ℂ)))
      (Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ =>
        measurable_const.mul (Complex.measurable_ofReal.comp (hM _ (hf i)).1)))]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    simp only [hO _ (hf _) U]
    rfl
  have hfirst : smearedEnergyCumulant (pushforwardWilsonMeasure L m K β) f =
      PeriodicLattice.connectedFunction L m K β (periodizeTuple L m f) := by
    rw [hmixed]
    unfold smearedEnergyCumulant Cumulants.mixedCumulant
    rw [hmgf]
  have hsecond : PeriodicLattice.gibbsCumulant L m K β
      (fun i U => PeriodicLattice.smearedObservable (periodizeTuple L m f i) U) =
      cutoffConnectedFunction L m K β (periodizeTuple L m f) := hgibbs.symm.trans hcum
  exact ⟨hI, fun i => hM _ (hf i), hfirst.trans hsecond.symm, hsecond, fun _ => rfl⟩
end LiftIdentities
section Separation
variable {ℓ : ℝ}
lemma abs_apply_le_euclidNormVec (w : AmbientSpace) (μ : Fin 4) : |w μ| ≤ euclidNormVec w := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
lemma euclidNormVec_le_torusEuclidNorm (hℓ : 0 < ℓ) {w : AmbientSpace}
    (hw : euclidNormVec w < ℓ / 2) :
    euclidNormVec w ≤ torusEuclidNorm (torusProj ℓ w) := by
  unfold torusEuclidNorm
  refine le_csInf ⟨_, w, rfl, rfl⟩ ?_
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨k, rfl⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
    (show torusProj ℓ u = torusProj ℓ w from hu)
  by_cases hk : k = 0
  · subst hk
    have : latticeTranslate ℓ 0 = 0 := by
      funext μ
      simp [latticeTranslate]
    rw [this, add_zero]
  · obtain ⟨μ, hμ⟩ := Function.ne_iff.mp hk
    have hw1 := abs_apply_le_euclidNormVec w μ
    have hw2 := abs_apply_le_euclidNormVec (w + latticeTranslate ℓ k) μ
    have hcoord : (w + latticeTranslate ℓ k) μ = w μ + ℓ * (k μ : ℝ) := rfl
    rw [hcoord] at hw2
    obtain ⟨lo, hi⟩ := abs_le.mp hw1
    have hk1 : (1 : ℝ) ≤ k μ ∨ (k μ : ℝ) ≤ -1 := by
      have hne : k μ ≠ 0 := hμ
      rcases lt_or_gt_of_ne hne with h | h
      · right
        exact_mod_cast (by omega : k μ ≤ -1)
      · left
        exact_mod_cast (by omega : 1 ≤ k μ)
    rcases hk1 with h | h
    · have : ℓ ≤ ℓ * (k μ : ℝ) := by nlinarith
      have := le_abs_self (w μ + ℓ * (k μ : ℝ))
      linarith
    · have : ℓ * (k μ : ℝ) ≤ -ℓ := by nlinarith
      have := neg_abs_le (w μ + ℓ * (k μ : ℝ))
      linarith
lemma continuous_torusProj : Continuous (torusProj ℓ) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
lemma torusProj_sub (x y : AmbientSpace) : torusProj ℓ x - torusProj ℓ y = torusProj ℓ (x - y) := by apply _root_.YangMills.DeltaSharedProofs.p500829 <;> assumption
lemma tsupport_periodize_subset {f : AmbientSpace → ℝ} (hc : HasCompactSupport f) :
    tsupport (periodize ℓ f) ⊆ torusProj ℓ '' tsupport f := by
  have hclosed : IsClosed (torusProj ℓ '' tsupport f) :=
    (hc.isCompact.image continuous_torusProj).isClosed
  refine closure_minimal ?_ hclosed
  intro y hy
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective ℓ y
  rw [Function.mem_support, TestFunctions.periodize_torusProj] at hy
  obtain ⟨k, hk⟩ : ∃ k, f (x + latticeTranslate ℓ k) ≠ 0 := by
    by_contra h
    push Not at h
    apply hy
    simp [periodicSum, h]
  exact ⟨x + latticeTranslate ℓ k, subset_tsupport f hk,
    TestFunctions.torusProj_add_latticeTranslate ℓ x k⟩
lemma measurable_periodize (hℓ : 0 < ℓ) {f : AmbientSpace → ℝ} (hm : Measurable f)
    (hc : HasCompactSupport f) : Measurable (periodize ℓ f) := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  have hper : Measurable (periodicSum ℓ f) := by
    have hs : ∀ x, HasSum (fun k => f (x + latticeTranslate ℓ k)) (periodicSum ℓ f x) :=
      fun x => (summable_of_hasFiniteSupport (finite_support_translates hℓ hc x)).hasSum
    refine measurable_of_tendsto_metrizable' (u := (atTop : Filter (Finset (Fin 4 → ℤ))))
      (f := fun s x => ∑ k ∈ s, f (x + latticeTranslate ℓ k)) (fun s => ?_)
      (tendsto_pi_nhds.2 fun x => hs x)
    exact Finset.measurable_sum _ fun k _ => hm.comp (measurable_id.add_const _)
  let section' : TorusMetric.Torus4 ℓ → AmbientSpace := fun x μ =>
    ((AddCircle.measurableEquivIco ℓ 0 (x μ) : Ico 0 (0 + ℓ)) : ℝ)
  have hsection : ∀ x, torusProj ℓ (section' x) = x := by
    intro x
    funext μ
    exact (AddCircle.equivIco ℓ 0).symm_apply_apply (x μ)
  have hmeas : Measurable section' := measurable_pi_lambda _ fun μ =>
    measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco ℓ 0).measurable.comp (measurable_pi_apply μ))
  have heq : periodize ℓ f = periodicSum ℓ f ∘ section' := by
    funext x
    simp only [Function.comp]
    rw [← TestFunctions.periodize_torusProj, hsection]
  rw [heq]
  exact hper.comp hmeas
lemma exists_uniform_separation {n : ℕ} (hn : 2 ≤ n) (f : Fin n → AmbientSpace → ℝ)
    (h : ∀ i k, i ≠ k → 0 < TestFunctions.setDistR4 (tsupport (f i)) (tsupport (f k))) :
    ∃ d : ℝ, 0 < d ∧ ∀ i k, i ≠ k →
      ENNReal.ofReal d ≤ TestFunctions.setDistR4 (tsupport (f i)) (tsupport (f k)) := by
  have hpair : ∀ q : Fin n × Fin n, ∃ d : ℝ, 0 < d ∧ (q.1 ≠ q.2 → ENNReal.ofReal d ≤
      TestFunctions.setDistR4 (tsupport (f q.1)) (tsupport (f q.2))) := by
    intro q
    by_cases hq : q.1 = q.2
    · exact ⟨1, one_pos, fun h' => absurd hq h'⟩
    · obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (h q.1 q.2 hq)
      refine ⟨r, by exact_mod_cast hr0, fun _ => ?_⟩
      rw [ENNReal.ofReal_coe_nnreal]
      exact hr.le
  choose d hd hdle using hpair
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨q₀, -, hq₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n × Fin n)) d
    Finset.univ_nonempty
  exact ⟨d q₀, hd q₀, fun i k hik =>
    (ENNReal.ofReal_le_ofReal (hq₀ (i, k) (Finset.mem_univ _))).trans (hdle (i, k) hik)⟩
end Separation
lemma liftCumulantsAreSchwinger_holds {L m K : ℕ} {β : ℝ} (hℓ : 0 < PeriodicLattice.torusSide L m)
    (hD : LiftCumulants L m K β) :
    LiftCumulantsAreSchwinger L m K β := by
  rintro n f hn hf hsep ⟨A, ⟨D, -, hDlt, hdiam⟩, hA⟩
  obtain ⟨d, hd, hdsep⟩ := exists_uniform_separation hn f hsep
  refine ⟨⟨fun i => (hf i).2.2, ⟨d, hd, hdsep⟩, A, fun i =>
      ⟨fun x hx y hy => (hdiam x hx y hy).trans hDlt.le, (subset_tsupport _).trans (hA i)⟩⟩,
    rfl, ⟨fun i => periodize_norm_bounded hℓ (hf i).2.1 (hf i).2.2,
      fun i => measurable_periodize hℓ (hf i).1 (hf i).2.2, d, hd, fun i k hik => ?_⟩,
    (hD n f (by omega) hf).2.2.1⟩
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  obtain ⟨x', hx', rfl⟩ := tsupport_periodize_subset (hf i).2.2 hx
  obtain ⟨y', hy', rfl⟩ := tsupport_periodize_subset (hf k).2.2 hy
  rw [torusProj_sub]
  have h1 : ENNReal.ofReal d ≤ ENNReal.ofReal (euclidNormVec (x' - y')) :=
    (hdsep i k hik).trans (iInf₂_le_of_le x' hx' (iInf₂_le y' hy'))
  exact h1.trans (ENNReal.ofReal_le_ofReal (euclidNormVec_le_torusEuclidNorm hℓ
    ((hdiam x' (hA i hx') y' (hA k hy')).trans_lt hDlt)))
theorem statement_holds (hLifts : InfiniteLattice.CutoffCoverLift.Statement)
    (hReads : FieldsAtSpacing.LinkFunctionsStatement)
    (hPlaq : ConnectedFunctionExpansion.Statement)
    (hProd : GaugeFieldProduct.Statement) : Statement := by
  intro L m K hL hm hK β hβ
  have hℓ : 0 < PeriodicLattice.torusSide L m := torusSide_pos hL
  have hl : InfiniteLattice.CutoffCoverLift.PointsAndLinks L m K ∧
      InfiniteLattice.CutoffCoverLift.FacesCovered L m K ∧
      (∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
        InfiniteLattice.CutoffCoverLift.LiftOfField L m K U) ∧
      Continuous (liftCompactField :
        PeriodicLattice.CompactGaugeField L m (K : ℤ) →
          InfiniteLattice.GaugeField (CutoffLattice.spacingAt L K)) ∧
      InfiniteLattice.CutoffCoverLift.PushforwardWilson L m K β :=
    hLifts ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ β hβ
  obtain ⟨hS, hP, hE, -, hI, -⟩ := hl
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) := by
    have h : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
    unfold PeriodicLattice.meshSize
    positivity
  have hR := (hReads _ ha ∅ (empty_subset _)).2.2.2.2.2
  obtain ⟨-, -, -, -, hC⟩ := hPlaq L m K hL hm
  obtain ⟨-, ⟨-, -, hfinP, -⟩, -, hA⟩ := hProd.1 L m (K : ℤ) hL hm (Int.natCast_nonneg K)
  have := hfinP
  let := Fintype.ofFinite (PeriodicLattice.Plaquette L m (K : ℤ))
  obtain ⟨hZre, hZim, -, -, hdata⟩ := hC.1 β
  obtain ⟨hZ, hW⟩ := hdata hK hβ
  have hOc : ∀ v : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported v →
      ∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
        smearedEnergy v (liftCompactField U) =
          PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide L m) v) U.1 :=
    fun v hv U => smearedEnergy_lift hS hP hE hR hℓ hv.2.2 U
  have hOr : ∀ f : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported f →
      ∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
        smearedEnergy f (liftCompactField U) =
          PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide L m) f) U.1 :=
    fun v hv U => smearedEnergy_lift hS hP hE hR hℓ hv.2.2 U
  have hMc : ∀ v : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported v → Measurable
      (smearedEnergy (a := PeriodicLattice.meshSize L (K : ℤ)) v) :=
    fun v hv => (isBoundedObservable_of_mem ha hReads (hR.2.2.1 v hv).2.1).1
  have hD : LiftCumulants L m K β :=
    liftCumulants_holds hK hβ hℓ hI hC hW hOr
      (fun f hf => smearedEnergy_real_measurable_bounded ha hReads hf)
  exact ⟨periodicSumDescends_holds hL, hOc,
    expMomentRatio_holds hA hZre hZim hZ hW hOc hMc, hD, liftCumulantsAreSchwinger_holds hℓ hD⟩
end YangMills.Construction.PeriodizationIdentities
