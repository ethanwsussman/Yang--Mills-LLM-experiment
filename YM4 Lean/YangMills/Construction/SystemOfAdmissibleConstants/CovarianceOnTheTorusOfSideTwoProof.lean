import YangMills.Construction.Cumulants.MomentGeneratingFunctionStatement
import YangMills.Construction.InfiniteLattice.PeriodisationAndThreeIdentitiesOfTheCovering
import YangMills.Construction.LawInAState.WilsonsLawIsAProbability
import YangMills.Construction.SourcesOnAFlow.MeanInAPeriodicExtensionProof
import YangMills.Construction.SystemOfAdmissibleConstants.CovarianceOnTheTorusOfSideTwo
import YangMills.Construction.Towers.WilsonActionIsRealAnalyticOnTheConfigurationsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
namespace SideTwoTorus
open InfiniteLattice (Link ElementaryPlaquette LatticePoint AmbientSpace IsBoundedBorelCompactlySupported projectLink
  projectPoint projectPoint_axisStep liftField liftCompactField liftCompactField_apply liftedWilsonMeasure faceEnergy
  faceHolonomy latticeSubgroup smearedEnergy axisStep)
open TestFunctions (latticeTranslate periodicSum periodize)
open TorusMetric (torusProj)
open Matrices (ComplexMatrix2)
variable {L m K : ℕ} {j : ℤ}
private theorem projectPoint_add (x y : LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j (x + y) = projectPoint L m j x + projectPoint L m j y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_add <;> assumption
private theorem projectLink_forwardFrom (x : LatticePoint (PeriodicLattice.meshSize L j)) (κ : Fin 4) :
    projectLink L m j (Link.forwardFrom x κ) =
      PeriodicLattice.Bond.forwardFrom (projectPoint L m j x) κ := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectLink_forwardFrom <;> assumption
private theorem faceEnergy_liftCompactField (p : ElementaryPlaquette (CutoffLattice.spacingAt L K))
    (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    faceEnergy (liftCompactField U) p =
      PeriodicLattice.plaquetteCost U.1 (CutoffLattice.projectFace L m K p) := by
  have e : ∀ (x : LatticePoint (CutoffLattice.spacingAt L K)) (κ : Fin 4),
      liftCompactField U (Link.forwardFrom x κ) =
        U.linkValue (PeriodicLattice.Bond.forwardFrom (projectPoint L m (K : ℤ) x) κ) := fun x κ => by
    rw [liftCompactField_apply, projectLink_forwardFrom]
  have hv : ((faceHolonomy (liftCompactField U) p : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      PeriodicLattice.plaquetteHolonomy U.1 (CutoffLattice.projectFace L m K p) := by
    have hr : ∀ b : PeriodicLattice.Bond L m (K : ℤ),
        (((U.linkValue b)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = U.1 b.opposite := fun b => by
      rw [← U.linkValue_opposite b]
      rfl
    simp only [faceHolonomy, e, projectPoint_add, projectPoint_axisStep,
      PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy, PeriodicLattice.Plaquette.boundaryBonds,
      CutoffLattice.projectFace, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, Submonoid.coe_mul, hr]
    simp only [mul_assoc]
    rfl
  simp only [faceEnergy, PeriodicLattice.plaquetteCost, hv]
private theorem torusProj_eq_iff (x y : AmbientSpace) :
    torusProj (PeriodicLattice.torusSide L m) x = torusProj (PeriodicLattice.torusSide L m) y ↔
      x - y ∈ latticeSubgroup (PeriodicLattice.torusSide L m) := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_eq_iff <;> assumption
private theorem latticeTranslate_mem_points (hL : 0 < L) (k : Fin 4 → ℤ) :
    latticeTranslate (PeriodicLattice.torusSide L m) k ∈ latticeSubgroup (PeriodicLattice.meshSize L (K : ℤ)) := by
  refine ⟨fun μ => k μ * (2 * (L : ℤ) ^ (m + K)), fun μ => ?_⟩
  simp only [latticeTranslate, PeriodicLattice.torusSide, PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
private theorem torusProj_add (x y : AmbientSpace) :
    torusProj (PeriodicLattice.torusSide L m) (x + y) =
      torusProj (PeriodicLattice.torusSide L m) x + torusProj (PeriodicLattice.torusSide L m) y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_add <;> assumption
private theorem torusProj_single (κ : Fin 4) (t : ℝ) :
    torusProj (PeriodicLattice.torusSide L m) (Pi.single κ t) = PeriodicLattice.pointOnAxis L m κ t := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_single <;> assumption
private theorem barycenter_projectFace (p : ElementaryPlaquette (CutoffLattice.spacingAt L K)) :
    (CutoffLattice.projectFace L m K p).barycenter =
      torusProj (PeriodicLattice.torusSide L m) p.center := by apply _root_.YangMills.Construction.PeriodicExtension.barycenter_projectFace <;> assumption
private theorem projectFace_surjective :
    Function.Surjective (CutoffLattice.projectFace L m K) := by
  rintro ⟨⟨z, hz⟩, μ, lam, h⟩
  have hz' := hz
  rw [PeriodicLattice.sublattice_eq_map_latticeSubgroup] at hz'
  obtain ⟨x, hx, rfl⟩ := hz'
  exact ⟨⟨⟨x, hx⟩, μ, lam, h⟩, rfl⟩
private theorem projectFace_eq_iff (p p' : ElementaryPlaquette (CutoffLattice.spacingAt L K)) :
    CutoffLattice.projectFace L m K p = CutoffLattice.projectFace L m K p' ↔
      (p.lowAxis, p.highAxis) = (p'.lowAxis, p'.highAxis) ∧
        (p'.corner : AmbientSpace) - (p.corner : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) := by
  constructor
  · intro h
    have hb : projectPoint L m (K : ℤ) p.corner = projectPoint L m (K : ℤ) p'.corner :=
      congrArg PeriodicLattice.Plaquette.origin h
    exact ⟨Prod.ext (congrArg PeriodicLattice.Plaquette.firstAxis h)
      (congrArg PeriodicLattice.Plaquette.secondAxis h),
      (torusProj_eq_iff _ _).mp (congrArg Subtype.val hb).symm⟩
  · rcases p with ⟨x, μ, lam, h⟩
    rcases p' with ⟨x', μ', lam', h'⟩
    rintro ⟨e, hd⟩
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have hb : projectPoint L m (K : ℤ) x = projectPoint L m (K : ℤ) x' :=
      Subtype.ext ((torusProj_eq_iff _ _).mpr hd).symm
    simp only [CutoffLattice.projectFace, hb]
private theorem latticeTranslate_mem (ℓ : ℝ) (k : Fin 4 → ℤ) :
    latticeTranslate ℓ k ∈ latticeSubgroup ℓ :=
  ⟨k, fun _ => mul_comm _ _⟩
private theorem finsum_faces_eq_finsum_torusFaces (hL : 0 < L) (hℓ : 0 < PeriodicLattice.torusSide L m)
    (c : PeriodicLattice.Plaquette L m (K : ℤ) → ℝ) (v : AmbientSpace → ℝ)
    (hfin : {p : ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) | v p.center ≠ 0}.Finite)
    (hk : ∀ x : AmbientSpace, {k : Fin 4 → ℤ | v (x + latticeTranslate (PeriodicLattice.torusSide L m) k) ≠ 0}.Finite) :
    ∑ᶠ p : ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)),
        c (CutoffLattice.projectFace L m K p) • v p.center =
      ∑ᶠ q : PeriodicLattice.Plaquette L m (K : ℤ),
        c q • periodize (PeriodicLattice.torusSide L m) v q.barycenter := by
  classical
  choose lift hlift using projectFace_surjective (L := L) (m := m) (K := K)
  let t : (Fin 4 → ℤ) → LatticePoint (PeriodicLattice.meshSize L (K : ℤ)) := fun k =>
    ⟨latticeTranslate (PeriodicLattice.torusSide L m) k, latticeTranslate_mem_points hL k⟩
  let Φ : PeriodicLattice.Plaquette L m (K : ℤ) × (Fin 4 → ℤ) →
      ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) := fun qk =>
    ⟨(lift qk.1).corner + t qk.2, (lift qk.1).lowAxis, (lift qk.1).highAxis,
      (lift qk.1).lowAxis_lt_highAxis⟩
  have hbary : ∀ q k, (Φ (q, k)).center =
      (lift q).center + latticeTranslate (PeriodicLattice.torusSide L m) k := by
    intro q k
    simp only [ElementaryPlaquette.center, Φ, t, AddSubgroup.coe_add]
    abel
  have hcover : ∀ q k, CutoffLattice.projectFace L m K (Φ (q, k)) = q := by
    intro q k
    refine ((projectFace_eq_iff (lift q) (Φ (q, k))).2 ⟨rfl, ?_⟩).symm.trans (hlift q)
    have : ((Φ (q, k)).corner : AmbientSpace) - ((lift q).corner : AmbientSpace) =
        latticeTranslate (PeriodicLattice.torusSide L m) k := by
      simp [Φ, t]
    rw [this]
    exact latticeTranslate_mem _ k
  have hinj : Function.Injective Φ := by
    rintro ⟨q, k⟩ ⟨q', k'⟩ h
    have hq : q = q' := by rw [← hcover q k, ← hcover q' k', h]
    subst hq
    have hb : (t k : AmbientSpace) = t k' := by
      have h1 := congrArg (fun p => (p.corner : AmbientSpace)) h
      simpa [Φ] using h1
    have hkk : k = k' := by
      funext μ
      have h2 := congrFun hb μ
      have h3 : PeriodicLattice.torusSide L m * (k μ : ℝ) = PeriodicLattice.torusSide L m * (k' μ : ℝ) := h2
      exact_mod_cast mul_left_cancel₀ hℓ.ne' h3
    rw [hkk]
  have hsurj : Function.Surjective Φ := by
    intro p
    obtain ⟨hdir, n, hn⟩ := (projectFace_eq_iff (lift (CutoffLattice.projectFace L m K p)) p).1
      (hlift _)
    have hd1 := congrArg Prod.fst hdir
    have hd2 := congrArg Prod.snd hdir
    refine ⟨(CutoffLattice.projectFace L m K p, n), ?_⟩
    refine ElementaryPlaquette.ext ?_ hd1 hd2
    refine Subtype.ext (funext fun μ => ?_)
    have h4 := hn μ
    simp only [Pi.sub_apply] at h4
    show ((lift (CutoffLattice.projectFace L m K p)).corner : AmbientSpace) μ +
      PeriodicLattice.torusSide L m * (n μ : ℝ) = (p.corner : AmbientSpace) μ
    rw [mul_comm, ← h4]
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
    have h5 := barycenter_projectFace (m := m) (lift q)
    rw [hlift q] at h5
    exact h5
  rw [hq, TestFunctions.periodize_torusProj, periodicSum, tsum_eq_finsum (hk _), smul_finsum]
  refine finsum_congr fun k => ?_
  show c (CutoffLattice.projectFace L m K (Φ (q, k))) • v (Φ (q, k)).center = _
  rw [hcover, hbary]
private theorem finite_translates {ℓ : ℝ} (hℓ : 0 < ℓ) {v : AmbientSpace → ℝ} (hc : HasCompactSupport v)
    (x : AmbientSpace) :
    {k : Fin 4 → ℤ | v (x + latticeTranslate ℓ k) ≠ 0}.Finite := by apply _root_.YangMills.Construction.PeriodicExtension.finite_translates_of_hasCompactSupport <;> assumption
private theorem smearedEnergy_liftCompactField (hL : 0 < L)
    (hR : FieldsAtSpacing.FaceFunctionProperties (PeriodicLattice.meshSize L (K : ℤ)))
    (hℓ : 0 < PeriodicLattice.torusSide L m) {v : AmbientSpace → ℝ} (hc : HasCompactSupport v)
    (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    smearedEnergy v (liftCompactField U) =
      PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide L m) v) U.1 := by
  refine (finsum_congr fun p => ?_).trans (finsum_faces_eq_finsum_torusFaces hL hℓ
    (fun q => PeriodicLattice.plaquetteCost U.1 q) v
    ((hR.2.1 _ hc.isCompact.isBounded).subset fun _ hp => subset_tsupport v hp)
    (finite_translates hℓ hc))
  rw [faceEnergy_liftCompactField p U]
private theorem inv_mem_specialUnitary {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) :
    V⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem positive_or_opposite (b : PeriodicLattice.Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
private theorem not_positive_and_opposite {K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K)
    (b : PeriodicLattice.Bond L m (K : ℤ)) (h₁ : b.IsPositivelyOriented) (h₂ : b.opposite.IsPositivelyOriented) :
    False := by
  obtain ⟨μ, h⟩ := h₁
  obtain ⟨ν, h'⟩ := h₂
  have h' : b.source - b.target = PeriodicLattice.unitStep L m (K : ℤ) ν := h'
  have hz : projectPoint L m (K : ℤ) (axisStep _ μ + axisStep _ ν) = projectPoint L m (K : ℤ) 0 := by
    rw [projectPoint_add, projectPoint_axisStep, projectPoint_axisStep, ← h, ← h']
    refine Subtype.ext ?_
    simp only [projectPoint, AddSubgroup.coe_add, sub_add_sub_cancel, sub_self, AddSubgroup.coe_zero]
    funext κ
    simp [torusProj]
  have hmem : ((axisStep (PeriodicLattice.meshSize L (K : ℤ)) μ + axisStep (PeriodicLattice.meshSize L (K : ℤ)) ν :
      LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) : AmbientSpace) - (0 : AmbientSpace) ∈
        latticeSubgroup (PeriodicLattice.torusSide L m) := by
    refine (torusProj_eq_iff _ _).mp ?_
    exact congrArg Subtype.val hz
  obtain ⟨n, hn⟩ := hmem
  have hnμ := hn μ
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hLK : (13 : ℝ) ≤ (L : ℝ) ^ K := by
    calc (13 : ℝ) ≤ L := hL13
      _ = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ K := pow_le_pow_right₀ (by linarith) hK
  have ha0 : 0 < PeriodicLattice.meshSize L (K : ℤ) := by
    simp only [PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
    positivity
  have ha1 : PeriodicLattice.meshSize L (K : ℤ) ≤ 1 / 2 := by
    simp only [PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hside : (2 : ℝ) ≤ PeriodicLattice.torusSide L m := by
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ m := one_le_pow₀ (by linarith)
    unfold PeriodicLattice.torusSide
    linarith
  have hval : ((axisStep (PeriodicLattice.meshSize L (K : ℤ)) μ + axisStep (PeriodicLattice.meshSize L (K : ℤ)) ν :
      LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) : AmbientSpace) μ = PeriodicLattice.meshSize L (K : ℤ) ∨
      ((axisStep (PeriodicLattice.meshSize L (K : ℤ)) μ + axisStep (PeriodicLattice.meshSize L (K : ℤ)) ν :
      LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) : AmbientSpace) μ = 2 * PeriodicLattice.meshSize L (K : ℤ) := by
    by_cases hμν : ν = μ
    · subst hμν
      right
      simp [axisStep, two_mul]
    · left
      simp [axisStep, Pi.single_eq_of_ne (Ne.symm hμν)]
  have hpos : (n μ : ℝ) * PeriodicLattice.torusSide L m = ((axisStep (PeriodicLattice.meshSize L (K : ℤ)) μ +
      axisStep (PeriodicLattice.meshSize L (K : ℤ)) ν : LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) :
        AmbientSpace) μ := by
    have := hnμ
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero] at this
    exact this.symm
  have hb : 0 < (n μ : ℝ) * PeriodicLattice.torusSide L m ∧
      (n μ : ℝ) * PeriodicLattice.torusSide L m < PeriodicLattice.torusSide L m := by
    rw [hpos]
    rcases hval with e | e <;> rw [e] <;> constructor <;> linarith
  have hsp : 0 < PeriodicLattice.torusSide L m := by linarith
  have n0 : (0 : ℝ) < n μ := (mul_pos_iff_of_pos_right hsp).1 hb.1
  have n1 : (n μ : ℝ) < 1 := by nlinarith [hb.2]
  have n0' : 0 < n μ := by exact_mod_cast n0
  have n1' : n μ < 1 := by exact_mod_cast n1
  omega
private theorem gaugeFieldOfPositive_mem {K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) :
    PeriodicLattice.gaugeFieldOfPositive v ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ) := by
  classical
  have hval : ∀ b, PeriodicLattice.gaugeFieldOfPositive v b ∈ ComplexMatrix2.specialUnitary := by
    intro b
    unfold PeriodicLattice.gaugeFieldOfPositive
    split_ifs with h h'
    · exact (v _).2
    · exact inv_mem_specialUnitary (v _).2
    · exact one_mem _
  refine ⟨fun b _ => hval b, fun b _ => ?_⟩
  rcases positive_or_opposite b with h | h
  · have hn : ¬ b.opposite.IsPositivelyOriented := fun h' => not_positive_and_opposite hL hK b h h'
    have e₁ : PeriodicLattice.gaugeFieldOfPositive v b = (v ⟨b, h⟩ : ComplexMatrix2) := dif_pos h
    have e₂ : PeriodicLattice.gaugeFieldOfPositive v b.opposite = ((v ⟨b, h⟩ : ComplexMatrix2))⁻¹ := by
      unfold PeriodicLattice.gaugeFieldOfPositive
      rw [dif_neg hn, dif_pos (show b.opposite.opposite.IsPositivelyOriented from h)]
      rfl
    rw [e₁, e₂]
  · have hn : ¬ b.IsPositivelyOriented := fun h' => not_positive_and_opposite hL hK b h' h
    have e₁ : PeriodicLattice.gaugeFieldOfPositive v b.opposite = (v ⟨b.opposite, h⟩ : ComplexMatrix2) := dif_pos h
    have e₂ : PeriodicLattice.gaugeFieldOfPositive v b = ((v ⟨b.opposite, h⟩ : ComplexMatrix2))⁻¹ := by
      unfold PeriodicLattice.gaugeFieldOfPositive
      rw [dif_neg hn, dif_pos h]
    rw [e₁, e₂, ← InfiniteLattice.specialUnitary_coe_inv, ← InfiniteLattice.specialUnitary_coe_inv, inv_inv]
private theorem measurable_gaugeFieldOfPositive :
    Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond L m j → ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
private theorem ae_mem_compactGaugeFields {K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K)
    (β : ℝ) :
    ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure L m K β, U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ) := by
  have : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hR : MeasurableSet (PeriodicLattice.compactGaugeFields L m (K : ℤ)) :=
    (PeriodicLattice.isClosed_compactGaugeFields L m (K : ℤ)).measurableSet
  have h1 : ∀ᵐ U ∂PeriodicLattice.productHaarMeasure L m (K : ℤ),
      U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ) := by
    unfold PeriodicLattice.productHaarMeasure
    exact (ae_map_iff measurable_gaugeFieldOfPositive.aemeasurable hR).2
      (Filter.Eventually.of_forall fun v => gaugeFieldOfPositive_mem hL hK v)
  have hac : PeriodicLattice.wilsonGibbsMeasure L m K β ≪ PeriodicLattice.productHaarMeasure L m (K : ℤ) := by
    unfold PeriodicLattice.wilsonGibbsMeasure
    exact (Measure.smul_absolutelyContinuous).trans (withDensity_absolutelyContinuous _ _)
  exact hac.ae_le h1
end SideTwoTorus
open SideTwoTorus in
theorem sideTwoTorusCovariance_holds (hGen : Cumulants.MomentGeneratingFunctionRegularity)
    (hCov : PeriodizationIdentities.Statement)
    (hProb : WilsonLaw.LiftedWilsonMeasureIsProbability)
    (hReads : FieldsAtSpacing.LinkFunctionsStatement) :
    SideTwoTorusCovariance := by
  intro L K hL hK β hβ f h bf bh
  have hL0 : 0 < L := by have := hL.2; omega
  have hL1 : 1 < L := by have := hL.2; omega
  have hb : ∀ i, InfiniteLattice.IsBoundedBorelCompactlySupported (![f, h] i) := by
    intro i
    fin_cases i
    · exact bf
    · exact bh
  have hmb := ((hCov L 1 K hL one_pos hK β hβ).2.2.2.1 2 ![f, h] (by norm_num) hb).2.1
  have hμ : IsProbabilityMeasure (InfiniteLattice.liftedWilsonMeasure L 0 K β) := hProb L 0 K β hL1
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) := by
    simp only [PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
    positivity
  have hR := (hReads _ ha ∅ (empty_subset _)).2.2.2.2.2
  have hℓ : 0 < PeriodicLattice.torusSide L 0 := by
    unfold PeriodicLattice.torusSide
    positivity
  have hext := InfiniteLattice.measurable_liftField L 0 (K : ℤ)
  have hG : Cumulants.momentGeneratingFunction (PeriodicLattice.wilsonGibbsMeasure L 0 K β)
        (fun j U => PeriodicLattice.smearedObservable (![TestFunctions.periodize (PeriodicLattice.torusSide L 0) f,
          TestFunctions.periodize (PeriodicLattice.torusSide L 0) h] j) U) =
      Cumulants.momentGeneratingFunction (InfiniteLattice.liftedWilsonMeasure L 0 K β)
        ![InfiniteLattice.smearedEnergy f, InfiniteLattice.smearedEnergy h] := by
    funext t
    unfold Cumulants.momentGeneratingFunction InfiniteLattice.liftedWilsonMeasure
    have hm : Measurable fun U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
        Complex.exp (∑ i, t i * ((![InfiniteLattice.smearedEnergy f,
          InfiniteLattice.smearedEnergy h] i U : ℝ) : ℂ)) := by
      refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ => ?_)
      refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
      fin_cases i
      · exact (hmb 0).1
      · exact (hmb 1).1
    rw [integral_map hext.aemeasurable hm.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_compactGaugeFields (m := 0) hL hK β] with U hU
    have e₁ := smearedEnergy_liftCompactField hL0 hR hℓ bf.2.2
      (⟨U, hU⟩ : PeriodicLattice.CompactGaugeField L 0 (K : ℤ))
    have e₂ := smearedEnergy_liftCompactField hL0 hR hℓ bh.2.2
      (⟨U, hU⟩ : PeriodicLattice.CompactGaugeField L 0 (K : ℤ))
    have e₁' : InfiniteLattice.smearedEnergy f (InfiniteLattice.liftField L 0 (K : ℤ) U) =
        PeriodicLattice.smearedObservable (TestFunctions.periodize (PeriodicLattice.torusSide L 0) f) U := e₁
    have e₂' : InfiniteLattice.smearedEnergy h (InfiniteLattice.liftField L 0 (K : ℤ) U) =
        PeriodicLattice.smearedObservable (TestFunctions.periodize (PeriodicLattice.torusSide L 0) h) U := e₂
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₁', e₂']
  have hmm : IsProbabilityMeasure (StateLaws.unitTorusMeasure L K β) := hμ
  have hcum : PeriodicLattice.torusUrsellFunction L 0 K β
      ![TestFunctions.periodize (PeriodicLattice.torusSide L 0) f,
        TestFunctions.periodize (PeriodicLattice.torusSide L 0) h] =
      Cumulants.mixedCumulant (InfiniteLattice.liftedWilsonMeasure L 0 K β)
        ![InfiniteLattice.smearedEnergy f, InfiniteLattice.smearedEnergy h] := by
    unfold PeriodicLattice.torusUrsellFunction PeriodicLattice.gibbsCumulant Cumulants.mixedCumulant
    rw [hG]
  rw [hcum, (hGen _ (InfiniteLattice.liftedWilsonMeasure L 0 K β)).2 (InfiniteLattice.smearedEnergy f)
    (InfiniteLattice.smearedEnergy h) (hmb 0).1 (hmb 1).1 (hmb 0).2 (hmb 1).2]
  obtain ⟨C, hC⟩ := (hmb 0).2
  obtain ⟨C', hC'⟩ := (hmb 1).2
  have m1 : MemLp (StateLaws.smearedObservable L K f) 2 (StateLaws.unitTorusMeasure L K β) :=
    MemLp.of_bound (hmb 0).1.aestronglyMeasurable C (ae_of_all _ hC)
  have m2 : MemLp (StateLaws.smearedObservable L K h) 2 (StateLaws.unitTorusMeasure L K β) :=
    MemLp.of_bound (hmb 1).1.aestronglyMeasurable C' (ae_of_all _ hC')
  rw [covariance_eq_sub m1 m2]
  rfl
end YangMills.Construction.AdmissibleConstants
end
