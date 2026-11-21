import YangMills.Construction.InfiniteLattice.CoveringMapAndThePeriodicExtensionAtACutoff
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeAtOneSpacingProof
import YangMills.Construction.InfiniteLattice.CoveringOnBondsAndPlaquettes
import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.LargeField.StateSpaceMeasures
import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.Lattice.WilsonActionAsAPlaquetteSumAndSymmetriesOfProductHaarProof
import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import YangMills.Construction.SourcesOnAFlow.MeanInAPeriodicExtension
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice InfiniteLattice.PeriodicExtensions
namespace PeriodicExtension
open InfiniteLattice.CutoffCoverLift
open TestFunctions (latticeTranslate periodicSum periodize)
open TorusMetric (torusProj)
open CutoffLattice
section Sites
variable {L m : ℕ} {j : ℤ}
theorem projectPoint_add (x y : LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j (x + y) = projectPoint L m j x + projectPoint L m j y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_add <;> assumption
theorem projectLink_forwardFrom (x : LatticePoint (PeriodicLattice.meshSize L j)) (κ : Fin 4) :
    projectLink L m j (Link.forwardFrom x κ) =
      PeriodicLattice.Bond.forwardFrom (projectPoint L m j x) κ := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectLink_forwardFrom <;> assumption
end Sites
theorem projectsPlaquetteEdges_of (L m K : ℕ) : Covering.ProjectsPlaquetteEdges L m K := by
  intro p
  refine ⟨projectLink_forwardFrom _ _, ?_, ?_, projectLink_forwardFrom _ _⟩
  · refine (projectLink_forwardFrom _ _).trans ?_
    rw [projectPoint_add, projectPoint_axisStep]
    rfl
  · refine (projectLink_forwardFrom _ _).trans ?_
    rw [projectPoint_add, projectPoint_axisStep]
    rfl
theorem faceEnergyOfLift_of (L m K : ℕ) :
    Covering.FaceEnergyOfLift L m K := by
  intro p U
  have e : ∀ (x : LatticePoint (CutoffLattice.spacingAt L K)) (κ : Fin 4),
      liftCompactField U (Link.forwardFrom x κ) =
        U.linkValue (PeriodicLattice.Bond.forwardFrom (projectPoint L m (K : ℤ) x) κ) := fun x κ => by
    rw [liftCompactField_apply, projectLink_forwardFrom]
  have hv : ((faceHolonomy (liftCompactField U) p : Matrices.ComplexMatrix2.specialUnitary) :
      Matrices.ComplexMatrix2) =
      PeriodicLattice.plaquetteHolonomy U.1 (CutoffLattice.projectFace L m K p) := by
    have hr : ∀ b : PeriodicLattice.Bond L m (K : ℤ),
        (((U.linkValue b)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
          U.1 b.opposite := fun b => by
      rw [← U.linkValue_opposite b]
      rfl
    simp only [faceHolonomy, e, projectPoint_add, projectPoint_axisStep,
      PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds,
      CutoffLattice.projectFace, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, Submonoid.coe_mul, hr]
    simp only [mul_assoc]
    rfl
  simp only [faceEnergy, PeriodicLattice.plaquetteCost, hv]
theorem periodLattice_le_of (hA : QuotientLattices.TorusAndSpaceLatticeProperties) {L m K : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 1 ≤ m) :
    Covering.PeriodLattice_le L m K := by
  obtain ⟨-, ⟨-, -, -, -, -, -, h, -⟩, -⟩ := hA L hL m 0 K hm (Nat.zero_le K)
  have hi : QuotientLattices.refinementIndex K 0 = (K : ℤ) := by
    simp [QuotientLattices.refinementIndex]
  rw [hi] at h
  exact h
variable {L m K : ℕ}
theorem torusCover_eq_iff (x y : AmbientSpace) :
    torusCover L m x = torusCover L m y ↔ x - y ∈ latticeSubgroup (PeriodicLattice.torusSide L m) := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_eq_iff <;> assumption
theorem torusCover_add (x y : AmbientSpace) :
    torusCover L m (x + y) = torusCover L m x + torusCover L m y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_add <;> assumption
theorem torusCover_single (κ : Fin 4) (t : ℝ) :
    torusCover L m (Pi.single κ t) = PeriodicLattice.pointOnAxis L m κ t := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_single <;> assumption
theorem barycenter_projectFace (p : ElementaryPlaquette (CutoffLattice.spacingAt L K)) :
    (projectFace L m K p).barycenter = torusCover L m p.center := by
  simp only [ElementaryPlaquette.center, torusCover_add, torusCover_single]
  rfl
theorem facesCovered_of (hf : Covering.ProjectsPlaquetteEdges L m K) :
    FacesCovered L m K := by
  refine ⟨fun p => ⟨?_, barycenter_projectFace p⟩, ?_, fun p p' => ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hf p
    simp only [List.map_cons, List.map_nil, h₁, h₂, h₃, h₄]
  · rintro ⟨⟨z, hz⟩, μ, lam, h⟩
    have hz' := hz
    rw [PeriodicLattice.sublattice_eq_map_latticeSubgroup] at hz'
    obtain ⟨x, hx, rfl⟩ := hz'
    exact ⟨⟨⟨x, hx⟩, μ, lam, h⟩, rfl⟩
  · constructor
    · intro h
      have hb : projectPoint L m (K : ℤ) p.corner = projectPoint L m (K : ℤ) p'.corner :=
        congrArg PeriodicLattice.Plaquette.origin h
      exact ⟨Prod.ext (congrArg PeriodicLattice.Plaquette.firstAxis h)
        (congrArg PeriodicLattice.Plaquette.secondAxis h),
        (torusCover_eq_iff _ _).mp (congrArg Subtype.val hb).symm⟩
    · rcases p with ⟨x, μ, lam, h⟩
      rcases p' with ⟨x', μ', lam', h'⟩
      rintro ⟨e, hd⟩
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have hb : projectPoint L m (K : ℤ) x = projectPoint L m (K : ℤ) x' :=
        Subtype.ext ((torusCover_eq_iff _ _).mpr hd).symm
      simp only [projectFace, hb]
theorem latticeTranslate_mem_latticeSubgroup (ℓ : ℝ) (k : Fin 4 → ℤ) :
    latticeTranslate ℓ k ∈ InfiniteLattice.latticeSubgroup ℓ :=
  ⟨k, fun _ => mul_comm _ _⟩
theorem finsum_projectFace_eq_finsum_periodize
    (hS : Covering.PeriodLattice_le L m K)
    (hP : FacesCovered L m K) (hℓ : 0 < PeriodicLattice.torusSide L m)
    (c : PeriodicLattice.Plaquette L m (K : ℤ) → ℝ) (v : AmbientSpace → ℝ)
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
  let t : (Fin 4 → ℤ) → InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L (K : ℤ)) := fun k =>
    ⟨latticeTranslate (PeriodicLattice.torusSide L m) k, hS (latticeTranslate_mem_latticeSubgroup _ k)⟩
  let Φ : PeriodicLattice.Plaquette L m (K : ℤ) × (Fin 4 → ℤ) →
      InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) := fun qk =>
    ⟨(lift qk.1).corner + t qk.2, (lift qk.1).lowAxis, (lift qk.1).highAxis,
      (lift qk.1).lowAxis_lt_highAxis⟩
  have hbary : ∀ q k, (Φ (q, k)).center =
      (lift q).center + latticeTranslate (PeriodicLattice.torusSide L m) k := by
    intro q k
    simp only [InfiniteLattice.ElementaryPlaquette.center, Φ, t, AddSubgroup.coe_add]
    abel
  have hcover : ∀ q k, CutoffLattice.projectFace L m K (Φ (q, k)) = q := by
    intro q k
    refine ((hP3 (lift q) (Φ (q, k))).2 ⟨rfl, ?_⟩).symm.trans (hlift q)
    have : ((Φ (q, k)).corner : AmbientSpace) - ((lift q).corner : AmbientSpace) =
        latticeTranslate (PeriodicLattice.torusSide L m) k := by
      simp [Φ, t]
    rw [this]
    exact latticeTranslate_mem_latticeSubgroup _ k
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
      have h3 : PeriodicLattice.torusSide L m * (k μ : ℝ) =
          PeriodicLattice.torusSide L m * (k' μ : ℝ) := h2
      exact_mod_cast mul_left_cancel₀ hℓ.ne' h3
    rw [hkk]
  have hsurj : Function.Surjective Φ := by
    intro p
    obtain ⟨hdir, n, hn⟩ := (hP3 (lift (CutoffLattice.projectFace L m K p)) p).1
      (hlift _)
    have hd1 := congrArg Prod.fst hdir
    have hd2 := congrArg Prod.snd hdir
    refine ⟨(CutoffLattice.projectFace L m K p, n), ?_⟩
    refine InfiniteLattice.ElementaryPlaquette.ext ?_ hd1 hd2
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
    have h5 := (hP1 (lift q)).2
    rw [hlift q] at h5
    exact h5
  rw [hq, TestFunctions.periodize_torusProj, periodicSum, tsum_eq_finsum (hk _), smul_finsum]
  refine finsum_congr fun k => ?_
  show c (CutoffLattice.projectFace L m K (Φ (q, k))) • v (Φ (q, k)).center = _
  rw [hcover, hbary]
theorem finite_translates_of_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) {v : AmbientSpace → ℝ}
    (hc : HasCompactSupport v) (x : AmbientSpace) :
    {k : Fin 4 → ℤ | v (x + latticeTranslate ℓ k) ≠ 0}.Finite := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  refine (Fintype.piFinset fun _ : Fin 4 =>
    Finset.Icc (-⌈(R + ‖x‖) / ℓ⌉) ⌈(R + ‖x‖) / ℓ⌉).finite_toSet.subset fun k hk => ?_
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro μ
  have h1 : |(x + latticeTranslate ℓ k) μ| ≤ R :=
    (norm_le_pi_norm _ μ).trans (hR _ (subset_tsupport v hk))
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp ((norm_le_pi_norm x μ : |x μ| ≤ ‖x‖))
  have e : (x + latticeTranslate ℓ k) μ = x μ + ℓ * (k μ : ℝ) := rfl
  rw [e] at a1 a2
  have c1 : (k μ : ℝ) ≤ (R + ‖x‖) / ℓ := by
    rw [le_div_iff₀ hℓ]
    linarith
  have c2 : -((R + ‖x‖) / ℓ) ≤ (k μ : ℝ) := by
    rw [neg_le, le_div_iff₀ hℓ]
    linarith
  have d1 : (k μ : ℝ) ≤ (⌈(R + ‖x‖) / ℓ⌉ : ℝ) := c1.trans (Int.le_ceil _)
  have d2 : -(⌈(R + ‖x‖) / ℓ⌉ : ℝ) ≤ (k μ : ℝ) := (neg_le_neg (Int.le_ceil _)).trans c2
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast d2
  · exact_mod_cast d1
section Positive
open PeriodicLattice (gaugeFieldOfPositive PositivelyOrientedBond gaugeFieldHaar)
variable {j : ℤ}
theorem coe_inv_specialUnitary (g : Matrices.ComplexMatrix2.specialUnitary) :
    (g : Matrices.ComplexMatrix2)⁻¹ = ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.WilsonPlaquetteSum.coe_inv_specialUnitary <;> assumption
theorem measurable_gaugeFieldOfPositive :
    Measurable (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
theorem gaugeFieldOfPositive_mem_compactGaugeFields
    (hx : ∀ b : PeriodicLattice.Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (v : PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) :
    gaugeFieldOfPositive v ∈ PeriodicLattice.compactGaugeFields L m j := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · unfold PeriodicLattice.gaugeFieldOfPositive
    split_ifs with h h'
    · exact (v _).2
    · rw [coe_inv_specialUnitary]
      exact ((v _)⁻¹ : Matrices.ComplexMatrix2.specialUnitary).2
    · exact one_mem _
  · rcases hx b with ⟨h, h'⟩ | ⟨h, h'⟩
    · have hrev : b.opposite.opposite.IsPositivelyOriented := h
      have e1 : gaugeFieldOfPositive v b = (v ⟨b, h⟩ : Matrices.ComplexMatrix2) := by
        unfold PeriodicLattice.gaugeFieldOfPositive
        rw [dif_pos h]
      have e2 : gaugeFieldOfPositive v b.opposite = (v ⟨b, h⟩ : Matrices.ComplexMatrix2)⁻¹ := by
        unfold PeriodicLattice.gaugeFieldOfPositive
        rw [dif_neg h', dif_pos hrev]
        rfl
      rw [e1, e2]
    · have e1 : gaugeFieldOfPositive v b = (v ⟨b.opposite, h⟩ : Matrices.ComplexMatrix2)⁻¹ := by
        unfold PeriodicLattice.gaugeFieldOfPositive
        rw [dif_neg h', dif_pos h]
      have e2 : gaugeFieldOfPositive v b.opposite = (v ⟨b.opposite, h⟩ : Matrices.ComplexMatrix2) := by
        unfold PeriodicLattice.gaugeFieldOfPositive
        rw [dif_pos h]
      rw [e1, e2, coe_inv_specialUnitary, coe_inv_specialUnitary, inv_inv]
theorem continuous_pathHolonomy (Γ : List (PeriodicLattice.Bond L m j)) :
    Continuous fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.pathHolonomy U Γ := by
  induction Γ with
  | nil => simpa [PeriodicLattice.pathHolonomy] using continuous_const
  | cons b Γ ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons]
    exact (continuous_apply b).matrix_mul ih
theorem continuous_plaquetteCost (p : PeriodicLattice.Plaquette L m j) :
    Continuous fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.plaquetteCost U p := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.continuous_plaquetteCost <;> assumption
end Positive
end PeriodicExtension
open PeriodicExtension InfiniteLattice.CutoffCoverLift TestFunctions in
theorem PeriodicExtension.liftedMeanEqTorusMean_proof
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hR : FieldsAtSpacing.LinkFunctionsStatement)
    (hProd : GaugeFieldProduct.Statement) : PeriodicExtension.LiftedMeanEqTorusMean := by
  intro L m K β hL hm hβ f hf
  have hLp : 0 < L := by have := hL.2; omega
  have hℓ : 0 < PeriodicLattice.torusSide L m := by
    unfold PeriodicLattice.torusSide
    have : (0 : ℝ) < L := by exact_mod_cast hLp
    positivity
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) := by
    unfold PeriodicLattice.meshSize
    exact zpow_pos (by exact_mod_cast hLp) _
  set a := PeriodicLattice.meshSize L (K : ℤ) with hadef
  obtain ⟨-, -, hc, hd, -, hP⟩ := hR a ha ∅ (empty_subset _)
  obtain ⟨hSp, ⟨-, -, hfinP, -⟩, -, -⟩ := hProd.1 L m (K : ℤ) hL hm (Int.natCast_nonneg K)
  have hx := hSp.2.2.2.2.2
  have hfinF : {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite :=
    (hP.2.1 _ hf.2.2.isCompact.isBounded).subset fun _ hp => subset_tsupport f hp
  have hkey : ∀ U (hU : U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ)),
      smearedEnergy f (liftField L m (K : ℤ) U) =
        PeriodicLattice.smearedObservable (j := (K : ℤ)) (periodize (PeriodicLattice.torusSide L m) f) U := by
    intro U hU
    let W : PeriodicLattice.CompactGaugeField L m (K : ℤ) := ⟨U, hU⟩
    show smearedEnergy f (liftCompactField W) = _
    refine (finsum_congr fun p => ?_).trans
      (finsum_projectFace_eq_finsum_periodize (periodLattice_le_of hA hL hm)
        (facesCovered_of (projectsPlaquetteEdges_of L m K)) hℓ
        (fun q => PeriodicLattice.plaquetteCost U q) f hfinF
        (finite_translates_of_hasCompactSupport hℓ hf.2.2))
    rw [faceEnergyOfLift_of L m K p W]
  set v : AmbientSpace → ℂ := fun x => (f x : ℂ) with hv
  have hvB : IsBoundedBorelCompactlySupported v := by
    refine ⟨Complex.measurable_ofReal.comp hf.1, ?_, hf.2.2.comp_left Complex.ofReal_zero⟩
    obtain ⟨C, hC⟩ := hf.2.1
    exact ⟨C, fun x => by simpa [hv] using hC x⟩
  have hmem := (hP.2.2.1 v hvB).2.1
  rw [hd.2.2.2] at hmem
  obtain ⟨⟨S, -, hS⟩, -⟩ := hmem
  rw [(hc.1 S).2.1] at hS
  have hmeasv := hS.1.1
  have hreal : ∀ U : GaugeField a, smearedEnergy v U = ((smearedEnergy f U : ℝ) : ℂ) := by
    intro U
    have hfin : (Function.support fun p : ElementaryPlaquette a => faceEnergy U p • f p.center).Finite :=
      hfinF.subset fun p hp h0 => hp (by simp [h0])
    have h := (Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.map_finsum hfin
    refine Eq.trans (finsum_congr fun p => ?_) h.symm
    simp [hv]
  have hmeas : Measurable (smearedEnergy f : GaugeField a → ℝ) := by
    have e : (smearedEnergy f : GaugeField a → ℝ) = fun U => (smearedEnergy v U).re := by
      funext U
      rw [hreal, Complex.ofReal_re]
    rw [e]
    exact Complex.measurable_re.comp hmeasv
  have := hfinP
  let _ := Fintype.ofFinite (PeriodicLattice.Plaquette L m (K : ℤ))
  have hobs : Measurable fun U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2 =>
      (PeriodicLattice.smearedObservable (j := (K : ℤ))
        (periodize (PeriodicLattice.torusSide L m) f) U : ℝ) := by
    have e : (fun U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2 =>
        (PeriodicLattice.smearedObservable (j := (K : ℤ))
          (periodize (PeriodicLattice.torusSide L m) f) U : ℝ)) =
        fun U => ∑ p : PeriodicLattice.Plaquette L m (K : ℤ), PeriodicLattice.plaquetteCost U p •
          periodize (PeriodicLattice.torusSide L m) f p.barycenter := by
      funext U
      exact finsum_eq_sum_of_fintype _
    rw [e]
    exact (continuous_finsetSum _ fun p _ =>
      (continuous_plaquetteCost p).smul continuous_const).measurable
  have hS' : MeasurableSet {U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2 |
      smearedEnergy f (liftField L m (K : ℤ) U) =
        PeriodicLattice.smearedObservable (j := (K : ℤ))
          (periodize (PeriodicLattice.torusSide L m) f) U} :=
    measurableSet_eq_fun (hmeas.comp (measurable_liftField L m (K : ℤ))) hobs
  have hμ : PeriodicLattice.productHaarMeasure L m (K : ℤ) {U |
      smearedEnergy f (liftField L m (K : ℤ) U) =
        PeriodicLattice.smearedObservable (j := (K : ℤ))
          (periodize (PeriodicLattice.torusSide L m) f) U}ᶜ = 0 := by
    unfold PeriodicLattice.productHaarMeasure
    rw [Measure.map_apply measurable_gaugeFieldOfPositive hS'.compl]
    have e : PeriodicLattice.gaugeFieldOfPositive ⁻¹' {U |
        smearedEnergy f (liftField L m (K : ℤ) U) =
          PeriodicLattice.smearedObservable (j := (K : ℤ))
            (periodize (PeriodicLattice.torusSide L m) f) U}ᶜ = ∅ := by
      ext w
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not,
        Set.mem_ofPred_eq]
      exact hkey _ (gaugeFieldOfPositive_mem_compactGaugeFields hx w)
    rw [e, measure_empty]
  have hν : PeriodicLattice.wilsonGibbsMeasure L m K β {U |
      smearedEnergy f (liftField L m (K : ℤ) U) =
        PeriodicLattice.smearedObservable (j := (K : ℤ))
          (periodize (PeriodicLattice.torusSide L m) f) U}ᶜ = 0 := by
    unfold PeriodicLattice.wilsonGibbsMeasure
    rw [Measure.smul_apply, withDensity_absolutelyContinuous _ _ hμ, smul_zero]
  unfold liftedWilsonMeasure
  rw [integral_map (measurable_liftField L m (K : ℤ)).aemeasurable hmeas.aestronglyMeasurable]
  exact integral_congr_ae (mem_ae_iff.mpr hν)
end YangMills.Construction
