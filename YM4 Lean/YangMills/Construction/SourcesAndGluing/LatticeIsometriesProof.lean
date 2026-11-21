import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheFineCaseProof
import YangMills.Construction.Lattice.IsometriesOfALevelWithoutFloorsWrittenOut
import YangMills.Construction.Lattice.SpaceOfTheConfigurationsAndPlaquetteEnergies
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.LinearAlgebra.NormIsometryOfEuclideanFourSpaceIsAffine
import YangMills.Construction.SourcesAndGluing.LatticeIsometries
import YangMills.Construction.SourcesAndGluing.PropertiesOfLatticeSimilaritiesForm
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.IsometryInvariance
open YangMills.Construction.InfiniteLattice (AmbientSpace)
variable {D : GluingSetup}
theorem onSpace_trivialExponent (Φ : ScaledLatticeMotion D.trivialExponent) (x : AmbientSpace) :
    Φ.onSpace x = Φ.rotation x + Φ.offset := by
  change (D.L : ℝ) ^ (0 : ℤ) • Φ.rotation x + Φ.offset = _
  rw [zpow_zero, one_smul]
def toTorusLatticeIsometry (Φ : ScaledLatticeMotion D.trivialExponent)
    (h : Φ.IsDilatingBijectionOfTori) : D.TorusLatticeIsometry where
  toFun := Φ.onTorus
  isIsometry := ⟨h.1, fun x y => (h.2.1 x y).trans (by
    change (D.L : ℝ) ^ (0 : ℤ) * _ = _
    rw [zpow_zero, one_mul]
    rfl)⟩
  image_eq := h.2.2.2.2
def toR4LatticeIsometry (Φ : ScaledLatticeMotion D.trivialExponent)
    (h : Φ.IsDilatingBijectionOfSpace) : D.R4LatticeIsometry where
  toFun := Φ.onSpace
  isIsometry := ⟨h.1, fun x y => (h.2.1 x y).trans (by
    change (D.L : ℝ) ^ (0 : ℤ) * _ = _
    rw [zpow_zero, one_mul]
    rfl)⟩
  image_eq := h.2.2.2.2
theorem exists_motion_onTorus_eq
    (hiso : PeriodicLattice.LevelIsometryPropertiesExpanded)
    (r : D.TorusLatticeIsometry) :
    ∃ Φ : ScaledLatticeMotion D.trivialExponent, Φ.onTorus = r.toFun := by
  have hK := D.K.pos
  have hm := D.m.pos
  have hd : PeriodicLattice.levelDepth (D.K : ℕ) 0 = ((D.K : ℕ) : ℤ) := by
    simp [PeriodicLattice.levelDepth]
  have hS := hiso.2 D.L D.m D.K 0 0 D.isAdmissible hm hK (Nat.zero_le _)
    (by simp only [PeriodicLattice.levelDepth]; omega)
  obtain ⟨σ, ⟨ρ, v, hv, hρ⟩, hσ⟩ := hS.2.1 r.toFun (Or.inr (Or.inr r.isIsometry.2))
    (by rw [hd]; exact r.image_eq)
  rw [hd] at hv
  refine ⟨⟨TorusLifts.signedCoordinateEquiv ρ.1 ρ.2, ⟨_, _, rfl⟩, v, ?_⟩, ?_⟩
  · obtain ⟨n, hn⟩ := hv
    exact ⟨n, hn⟩
  · funext u
    obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
    rw [ScaledLatticeMotion.onTorus_torusProj, onSpace_trivialExponent, ← hσ]
    exact (hρ x).symm
def euclidSeminorm : Seminorm ℝ AmbientSpace :=
  (normSeminorm ℝ (EuclideanSpace ℝ (Fin 4))).comp
    (WithLp.linearEquiv 2 ℝ AmbientSpace).symm.toLinearMap
theorem euclidSeminorm_apply (x : AmbientSpace) :
    euclidSeminorm x = TorusMetric.euclidNormVec x := by
  change ‖(WithLp.linearEquiv 2 ℝ AmbientSpace).symm x‖ = _
  rw [EuclideanSpace.norm_eq]
  simp [TorusMetric.euclidNormVec]
theorem exists_signedCoordinateEquiv_eq {S : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hinj : Function.Injective S) {τ : Fin 4 → Fin 4} {ε : Fin 4 → ℤˣ}
    (hε : ∀ μ, S (Pi.single μ 1) = (((ε μ : ℤˣ) : ℤ) : ℝ) • (Pi.single (τ μ) 1 : AmbientSpace)) :
    ∃ (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ),
      ∀ x, S x = TorusLifts.signedCoordinateEquiv π s x := by
  have hτ : Function.Injective τ := by
    intro μ μ' h
    by_contra hne
    have h3 : S ((((ε μ' : ℤˣ) : ℤ) : ℝ) • (Pi.single μ 1 : AmbientSpace) -
        (((ε μ : ℤˣ) : ℤ) : ℝ) • (Pi.single μ' 1 : AmbientSpace)) = 0 := by
      rw [map_sub, map_smul, map_smul, hε, hε, h, smul_smul, smul_smul, mul_comm, sub_self]
    have h4 := hinj (h3.trans (map_zero S).symm)
    have h5 := congrFun h4 μ
    rcases Int.units_eq_one_or (ε μ') with e | e <;>
      simp [e, Pi.single_eq_of_ne hne] at h5
  let π : Equiv.Perm (Fin 4) := Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hτ)
  have hπ : ∀ ν, τ (π.symm ν) = ν := fun ν => π.apply_symm_apply ν
  refine ⟨π.symm, fun ν => ε (π.symm ν), fun x => ?_⟩
  have hx : x = ∑ μ, x μ • (Pi.single μ 1 : AmbientSpace) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun μ _ => ?_
    funext ν
    by_cases h : ν = μ
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  funext ν
  have hS : S x ν =
      ∑ μ, x μ * ((((ε μ : ℤˣ) : ℤ) : ℝ) * (Pi.single (τ μ) 1 : AmbientSpace) ν) := by
    conv_lhs => rw [hx, map_sum]
    simp [Finset.sum_apply, hε]
  rw [hS, Finset.sum_eq_single (π.symm ν)]
  · change _ = (((ε (π.symm ν) : ℤˣ) : ℤ) : ℝ) * x (π.symm ν)
    rw [hπ]
    simp [mul_comm]
  · intro μ _ hμ
    have : ν ≠ τ μ := fun e => hμ (by rw [e]; exact (π.symm_apply_apply μ).symm)
    simp [Pi.single_eq_of_ne this]
  · simp
theorem exists_motion_onSpace_eq
    (hIsometryAffine : LinearAlgebra.NormIsometry.BijectiveNormIsometryIsAffine)
    (r : D.R4LatticeIsometry) :
    ∃ Φ : ScaledLatticeMotion D.trivialExponent, Φ.onSpace = r.toFun := by
  have hL : 0 < D.L := ScaleExponent.L_pos
  have ha : 0 < D.mesh := meshSize_pos hL _
  have hdist : ∀ x y, TorusMetric.euclidNormVec (r.toFun x - r.toFun y) =
      TorusMetric.euclidNormVec (x - y) := r.isIsometry.2
  obtain ⟨g, hg⟩ := hIsometryAffine euclidSeminorm (fun x hx => by
      have h : ‖(WithLp.linearEquiv 2 ℝ AmbientSpace).symm x‖ = 0 := hx
      exact (WithLp.linearEquiv 2 ℝ AmbientSpace).symm.map_eq_zero_iff.1 (norm_eq_zero.1 h))
    r.toFun r.isIsometry.1 (fun x y => by
      rw [euclidSeminorm_apply, euclidSeminorm_apply]
      exact hdist x y)
  have hS : ∀ x, g.linear x = r.toFun x - r.toFun 0 := fun x => by
    have h := congrFun g.decomp x
    simp only [Pi.add_apply] at h
    rw [← hg, h, add_sub_cancel_right]
  have hmem : ∀ x ∈ InfiniteLattice.latticeSubgroup D.mesh,
      r.toFun x ∈ InfiniteLattice.latticeSubgroup D.mesh := fun x hx => by
    have h : r.toFun x ∈ r.toFun '' (D.gridPoints : Set AmbientSpace) := ⟨x, hx, rfl⟩
    rw [r.image_eq] at h
    exact h
  have h0 : r.toFun 0 ∈ InfiniteLattice.latticeSubgroup D.mesh := hmem 0 (zero_mem _)
  have hinj : Function.Injective g.linear := fun x y h => r.isIsometry.1.1 (by
    rw [hS, hS] at h
    exact sub_left_injective h)
  have key : ∀ μ, ∃ (ν : Fin 4) (ε : ℤˣ),
      g.linear (Pi.single μ 1) = (((ε : ℤˣ) : ℤ) : ℝ) • (Pi.single ν 1 : AmbientSpace) := by
    intro μ
    have hp : (Pi.single μ D.mesh : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup D.mesh :=
      (InfiniteLattice.axisStep D.mesh μ).2
    obtain ⟨n, hn⟩ : g.linear (Pi.single μ D.mesh) ∈ InfiniteLattice.latticeSubgroup D.mesh := by
      rw [hS]
      exact sub_mem (hmem _ hp) h0
    have hsc : (Pi.single μ D.mesh : AmbientSpace) = D.mesh • (Pi.single μ 1 : AmbientSpace) := by
      funext ν
      by_cases h : ν = μ
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    have hnorm : TorusMetric.euclidNormVec (g.linear (Pi.single μ D.mesh)) = D.mesh := by
      rw [hS, hdist, sub_zero, InfiniteLattice.euclidNormVec_single, abs_of_pos ha]
    have hval : ∀ κ, g.linear (Pi.single μ 1) κ = n κ := fun κ => by
      have h := hn κ
      rw [hsc, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm] at h
      exact mul_right_cancel₀ ha.ne' h
    have hsum : ∑ κ, n κ ^ 2 = 1 := by
      have h1 : Real.sqrt ((∑ κ, (n κ : ℝ) ^ 2) * D.mesh ^ 2) = D.mesh := by
        have e : (∑ κ, (n κ : ℝ) ^ 2) * D.mesh ^ 2 =
            ∑ κ, g.linear (Pi.single μ D.mesh) κ ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun κ _ => by rw [hn κ, mul_pow]
        rw [e]
        exact hnorm
      have h2 : (∑ κ, (n κ : ℝ) ^ 2) * D.mesh ^ 2 = D.mesh ^ 2 := by
        have h3 : Real.sqrt ((∑ κ, (n κ : ℝ) ^ 2) * D.mesh ^ 2) ^ 2 = D.mesh ^ 2 := by rw [h1]
        rwa [Real.sq_sqrt (by positivity)] at h3
      have h4 : ∑ κ, (n κ : ℝ) ^ 2 = 1 :=
        mul_right_cancel₀ (by positivity) (h2.trans (one_mul _).symm)
      exact_mod_cast h4
    obtain ⟨ν, h | h⟩ := InfiniteLattice.int_vec_unit_of_sum_sq_eq_one n hsum
    · refine ⟨ν, 1, funext fun κ => ?_⟩
      rw [hval, h]
      by_cases hκ : κ = ν
      · subst hκ
        simp
      · simp [Pi.single_eq_of_ne hκ]
    · refine ⟨ν, -1, funext fun κ => ?_⟩
      rw [hval, h]
      by_cases hκ : κ = ν
      · subst hκ
        simp
      · simp [Pi.single_eq_of_ne hκ]
  choose τ ε hε using key
  obtain ⟨π, s, hπ⟩ := exists_signedCoordinateEquiv_eq hinj hε
  refine ⟨⟨TorusLifts.signedCoordinateEquiv π s, ⟨π, s, rfl⟩, r.toFun 0, h0⟩,
    funext fun x => ?_⟩
  rw [onSpace_trivialExponent]
  change TorusLifts.signedCoordinateEquiv π s x + r.toFun 0 = r.toFun x
  rw [← hπ, hS, sub_add_cancel]
section Torus
variable (r r' : D.TorusLatticeIsometry) {Φ : ScaledLatticeMotion D.trivialExponent}
theorem torus_pointMap_eq (h : Φ.onTorus = r.toFun)
    (x : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)) :
    r.pointMap x = Φ.onTorusSite x :=
  Subtype.ext (congrFun h x).symm
theorem torus_linkMap_eq (h : Φ.onTorus = r.toFun) (b : D.PeriodicLink) :
    r.linkMap b = Φ.onTorusLink b :=
  PeriodicLattice.Bond.ext (torus_pointMap_eq r h _) (torus_pointMap_eq r h _)
theorem torus_pullbackField_eq (h : Φ.onTorus = r.toFun)
    (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    r.pullbackField U = Φ.pullTorusField U :=
  funext fun b => congrArg U (torus_linkMap_eq r h b)
theorem torus_invFun_eq : Function.invFun r.toFun = r.invFun :=
  funext fun v => r.isIsometry.1.1 ((Function.rightInverse_invFun r.isIsometry.1.2 v).trans
    (r.toEquiv.apply_symm_apply v).symm)
end Torus
section FourSpace
variable (r r' : D.R4LatticeIsometry) {Φ : ScaledLatticeMotion D.trivialExponent}
theorem space_pointMap_eq (h : Φ.onSpace = r.toFun)
    (x : InfiniteLattice.LatticePoint D.mesh) :
    r.toLatticeSymmetry.pointMap x = Φ.onPoint x :=
  Subtype.ext (congrFun h x).symm
theorem space_linkMap_eq (h : Φ.onSpace = r.toFun) (b : InfiniteLattice.Link D.mesh) :
    r.linkMap b = Φ.onLink b :=
  InfiniteLattice.Link.ext (space_pointMap_eq r h _) (space_pointMap_eq r h _)
theorem space_pullbackField_eq (h : Φ.onSpace = r.toFun) (U : D.GridField) :
    r.pullbackField U = Φ.pullField U :=
  Subtype.ext (funext fun b => congrArg U.1 (space_linkMap_eq r h b))
theorem space_invFun_eq : Function.invFun r.toFun = r.invFun :=
  funext fun v => r.isIsometry.1.1 ((Function.rightInverse_invFun r.isIsometry.1.2 v).trans
    (r.asEquiv.apply_symm_apply v).symm)
end FourSpace
section Plaquettes
variable {L m : ℕ} {j : ℤ}
theorem measurable_pathHolonomy (Γ : List (PeriodicLattice.Bond L m j)) :
    Measurable fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.pathHolonomy U Γ := by apply _root_.YangMills.SharedProofs.p124 <;> assumption
theorem measurable_fullTrace_plaquetteHolonomy (p : PeriodicLattice.Plaquette L m j) :
    Measurable fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      Matrices.ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy U p) :=
  (continuous_id.matrix_trace.measurable).comp (measurable_pathHolonomy _)
theorem measurable_plaquetteEnergy_complex (p : PeriodicLattice.Plaquette L m j) :
    Measurable fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.plaquetteEnergy U p :=
  ((measurable_fullTrace_plaquetteHolonomy p).const_mul _).const_sub _
theorem measurable_plaquetteEnergy (p : PeriodicLattice.Plaquette L m j) :
    Measurable fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.plaquetteCost U p :=
  ((Complex.measurable_re.comp (measurable_fullTrace_plaquetteHolonomy p)).const_mul _).const_sub _
theorem measurable_sourcedBoltzmannWeight [Finite (PeriodicLattice.Plaquette L m j)] (β : ℝ)
    (w : PeriodicLattice.FourTorus L m → ℂ) :
    Measurable (PeriodicLattice.sourcedBoltzmannWeight β w :
      (PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) → ℂ) := by
  let _ := Fintype.ofFinite (PeriodicLattice.Plaquette L m j)
  have h : (fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
        PeriodicLattice.barycenterWeightedEnergy (fun x => (β : ℂ) - w x) U) =
      fun U => ∑ p : PeriodicLattice.Plaquette L m j,
        ((β : ℂ) - w p.barycenter) * PeriodicLattice.plaquetteEnergy U p :=
    funext fun U => finsum_eq_sum_of_fintype _
  have h' : Measurable fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.barycenterWeightedEnergy (fun x => (β : ℂ) - w x) U := by
    rw [h]
    exact Finset.measurable_sum _ fun p _ => (measurable_plaquetteEnergy_complex p).const_mul _
  exact Complex.measurable_exp.comp h'.neg
theorem measurable_smearedObservable [Finite (PeriodicLattice.Plaquette L m j)]
    (f : PeriodicLattice.FourTorus L m → ℝ) :
    Measurable (PeriodicLattice.smearedObservable f :
      (PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) → ℝ) := by apply _root_.YangMills.DeltaSharedProofs.p502502 <;> assumption
end Plaquettes
section Space
variable (hSpace : PeriodicLattice.CutoffData.ConfigSpace.BasicStructure)
include hSpace
theorem finite_periodicPlaquette (D : GluingSetup) :
    Finite (PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)) :=
  (hSpace (PeriodicLattice.CutoffData.atCutoff D.toStandingParameters)).1.2.2.1
theorem plaquetteEnergy_complex_eq_ofReal {U : D.PeriodicLink → Matrices.ComplexMatrix2}
    (hU : U ∈ D.gaugeFields) (p : D.PeriodicPlaquette) :
    PeriodicLattice.plaquetteEnergy U p = (PeriodicLattice.plaquetteCost U p : ℂ) := by
  obtain ⟨t, -, ht⟩ :=
    ((hSpace (PeriodicLattice.CutoffData.atCutoff D.toStandingParameters)).2.2.1 p).2 ⟨U, hU⟩
  have ht' : PeriodicLattice.plaquetteEnergy U p = (t : ℂ) := ht
  have hre : PeriodicLattice.plaquetteCost U p = t := by
    have h := congrArg Complex.re ht'
    simpa [PeriodicLattice.plaquetteEnergy, PeriodicLattice.plaquetteCost] using h
  rw [hre, ht']
theorem barycenterWeightedEnergy_eq_smeared {U : D.PeriodicLink → Matrices.ComplexMatrix2}
    (hU : U ∈ D.gaugeFields) (c : D.Torus → ℂ) :
    PeriodicLattice.barycenterWeightedEnergy c U = D.smeared c U := by
  change ∑ᶠ p : D.PeriodicPlaquette, c p.barycenter * PeriodicLattice.plaquetteEnergy U p =
    ∑ᶠ p : D.PeriodicPlaquette, PeriodicLattice.plaquetteCost U p • c p.barycenter
  refine finsum_congr fun p => ?_
  rw [plaquetteEnergy_complex_eq_ofReal hSpace hU p, Complex.real_smul, mul_comm]
theorem isPeriodicObservable_sourcedBoltzmannWeight (D : GluingSetup) (β : ℝ) (w : D.Torus → ℂ) :
    InfiniteLattice.IsPeriodicObservable
      (PeriodicLattice.sourcedBoltzmannWeight β w :
        (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) := by
  have := finite_periodicPlaquette hSpace D
  refine ⟨measurable_sourcedBoltzmannWeight β w,
    Real.exp (2 * ∑ᶠ p : D.PeriodicPlaquette, ‖(β : ℂ) - w p.barycenter‖), fun U hU => ?_⟩
  exact ((hSpace (PeriodicLattice.CutoffData.atCutoff D.toStandingParameters)).2.2.2.2
    (fun x => (β : ℂ) - w x)).2.2.2.1 ⟨U, hU⟩
end Space
section Observables
variable (r : D.TorusLatticeIsometry)
theorem smeared_pullbackField {E : Type} [AddCommMonoid E] [Module ℝ E]
    {Φ : ScaledLatticeMotion D.trivialExponent} (h : Φ.onTorus = r.toFun)
    (hO : Φ.PullsObservablesOfTori E) (f : D.Torus → E)
    {U : D.PeriodicLink → Matrices.ComplexMatrix2} (hU : U ∈ D.gaugeFields) :
    D.smeared f (r.pullbackField U) = D.smeared (f ∘ r.invFun) U := by
  rw [torus_pullbackField_eq r h, ← torus_invFun_eq r, ← h]
  exact hO f U hU
end Observables
section Measures
variable (hlat : ScaledMotionPropertiesClaim)
  (hiso : PeriodicLattice.LevelIsometryPropertiesExpanded)
  (hWeight : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
  (hSpace : PeriodicLattice.CutoffData.ConfigSpace.BasicStructure)
  (r : D.TorusLatticeIsometry)
include hlat hiso
theorem expectation_actOn {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : InfiniteLattice.IsPeriodicObservable F) :
    D.expectation (r.actOn F) = D.expectation F := by
  obtain ⟨Φ, h⟩ := exists_motion_onTorus_eq hiso r
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hM, -⟩ := hlat D _ Φ
  have e : r.actOn F = F ∘ Φ.pullTorusField :=
    funext fun U => congrArg F (torus_pullbackField_eq r h U)
  rw [e]
  exact (hM F hF D.β D.beta_pos).2
theorem integral_pullbackField {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : InfiniteLattice.IsPeriodicObservable F) :
    ∫ U, F (r.pullbackField U) ∂PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ) =
      ∫ U, F U ∂PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ) := by
  obtain ⟨Φ, h⟩ := exists_motion_onTorus_eq hiso r
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hM, -⟩ := hlat D _ Φ
  simp only [torus_pullbackField_eq r h]
  exact (hM F hF D.β D.beta_pos).1
include hWeight
theorem integral_pullbackOnGaugeFields {G : D.gaugeFields → ℂ} (hG : Measurable G) {C : ℝ}
    (hC : ∀ u, ‖G u‖ ≤ C) :
    ∫ u, G (r.pullbackOnGaugeFields u) ∂D.wilsonOnGaugeFields =
      ∫ u, G u ∂D.wilsonOnGaugeFields := by
  classical
  have hs : MeasurableSet D.gaugeFields := by
    have : SecondCountableTopology Matrices.ComplexMatrix2 :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
    exact (PeriodicLattice.isClosed_compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)).measurableSet
  let F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ := fun U =>
    if h : U ∈ D.gaugeFields then G ⟨U, h⟩ else 0
  have hFval : ∀ u : D.gaugeFields, F u.1 = G u := fun u => dif_pos u.2
  have hF : InfiniteLattice.IsPeriodicObservable F :=
    ⟨Measurable.dite hG measurable_const hs, C, fun U hU => by
      have e : F U = G ⟨U, hU⟩ := hFval ⟨U, hU⟩
      rw [e]
      exact hC _⟩
  have hL : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  obtain ⟨-, -, -, -, -, -, -, -, hnull, -⟩ := hWeight D.L D.m D.K D.β hL D.m.pos D.K.pos
  have hrestr : D.gibbsMeasure.restrict D.gaugeFields = D.gibbsMeasure :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hnull)
  have hcomap : ∀ H : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ,
      ∫ u, H u.1 ∂D.wilsonOnGaugeFields = ∫ U, H U ∂D.gibbsMeasure := fun H => by
    conv_rhs => rw [← hrestr]
    exact integral_subtype_comap hs H
  have h1 : ∫ u, G u ∂D.wilsonOnGaugeFields = D.expectation F := by
    rw [← funext hFval]
    exact hcomap F
  have h2 : ∫ u, G (r.pullbackOnGaugeFields u) ∂D.wilsonOnGaugeFields =
      D.expectation (r.actOn F) := by
    rw [← funext fun u => hFval (r.pullbackOnGaugeFields u)]
    exact hcomap (r.actOn F)
  rw [h1, h2]
  exact expectation_actOn hlat hiso r hF
theorem cumulant_pullbackOnGaugeFields {n : ℕ} (X : Fin n → D.gaugeFields → ℝ)
    (hX : ∀ i, Probability.IsBoundedRealRV (X i)) :
    cumulant D.wilsonOnGaugeFields (fun i => X i ∘ r.pullbackOnGaugeFields) =
      cumulant D.wilsonOnGaugeFields X := by
  have hΓ : ∀ z : Fin n → ℂ,
      Cumulants.momentGeneratingFunction D.wilsonOnGaugeFields
          (fun i => X i ∘ r.pullbackOnGaugeFields) z =
        Cumulants.momentGeneratingFunction D.wilsonOnGaugeFields X z := fun z => by
    choose C hC using fun i => (hX i).bounded
    have hmeas : Measurable fun u => Complex.exp (∑ i, z i * (X i u : ℂ)) :=
      Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ =>
        (Complex.measurable_ofReal.comp (hX i).measurable).const_mul _)
    refine integral_pullbackOnGaugeFields hlat hiso hWeight r hmeas
      (C := Real.exp (∑ i, ‖z i‖ * C i)) fun u => ?_
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC i u) (norm_nonneg _)
  unfold cumulant
  simp only [hΓ]
omit hlat hiso in
include hSpace in
theorem isBoundedRealRV_smearedOnGaugeFields (f : D.Torus → ℝ) :
    Probability.IsBoundedRealRV (D.smearedOnGaugeFields f) := by
  have := finite_periodicPlaquette hSpace D
  let _ := Fintype.ofFinite D.PeriodicPlaquette
  have hL : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  refine ⟨(measurable_smearedObservable f).comp measurable_subtype_coe,
    ∑ p : D.PeriodicPlaquette, 2 * |f p.barycenter|, fun U => ?_⟩
  have e : D.smearedOnGaugeFields f U =
      ∑ p : D.PeriodicPlaquette, PeriodicLattice.plaquetteCost U.1 p • f p.barycenter :=
    finsum_eq_sum_of_fintype _
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  obtain ⟨h0, h2⟩ := ((hWeight D.L D.m D.K D.β hL D.m.pos D.K.pos).1 U.1 U.2 p).1
  rw [smul_eq_mul, abs_mul, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
include hSpace
theorem generatingFunctionOfSource_comp_invFun (w : D.Torus → ℂ) :
    PeriodicLattice.generatingFunctionOfSource D.L D.m D.K D.β (w ∘ r.invFun) =
      PeriodicLattice.generatingFunctionOfSource D.L D.m D.K D.β w := by
  obtain ⟨Φ, h⟩ := exists_motion_onTorus_eq hiso r
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, -, -, -⟩ := hlat D _ Φ
  have hL : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  obtain ⟨-, -, -, -, -, -, hnull, -⟩ := hWeight D.L D.m D.K D.β hL D.m.pos D.K.pos
  have hreal : ∀ᵐ U ∂PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ),
      U ∈ D.gaugeFields := mem_ae_iff.mpr hnull
  have hpt : ∀ U ∈ D.gaugeFields,
      PeriodicLattice.sourcedBoltzmannWeight D.β (w ∘ r.invFun) U =
        PeriodicLattice.sourcedBoltzmannWeight D.β w (r.pullbackField U) := fun U hU => by
    change Complex.exp (-PeriodicLattice.barycenterWeightedEnergy
        ((fun x => (D.β : ℂ) - w x) ∘ r.invFun) U) =
      Complex.exp (-PeriodicLattice.barycenterWeightedEnergy
        (fun x => (D.β : ℂ) - w x) (r.pullbackField U))
    rw [barycenterWeightedEnergy_eq_smeared hSpace hU,
      barycenterWeightedEnergy_eq_smeared hSpace (r.pullbackField_mem hU),
      smeared_pullbackField r h hO _ hU]
  unfold PeriodicLattice.generatingFunctionOfSource
  rw [integral_congr_ae (hreal.mono hpt)]
  exact integral_pullbackField hlat hiso r
    (isPeriodicObservable_sourcedBoltzmannWeight hSpace D D.β w)
theorem cumulantsInvariantOnTorus : CumulantsInvariantOnTorus r := by
  intro n _
  refine ⟨fun X hX => cumulant_pullbackOnGaugeFields hlat hiso hWeight r X hX, fun f _ => ?_⟩
  obtain ⟨Φ, h⟩ := exists_motion_onTorus_eq hiso r
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hO, -, -, -, -⟩ := hlat D _ Φ
  have e : (fun i => D.smearedOnGaugeFields (f i ∘ r.invFun)) =
      fun i => D.smearedOnGaugeFields (f i) ∘ r.pullbackOnGaugeFields :=
    funext fun i => funext fun U => (smeared_pullbackField r h hO (f i) U.2).symm
  unfold GluingSetup.torusConnected
  rw [e]
  exact cumulant_pullbackOnGaugeFields hlat hiso hWeight r _
    fun i => isBoundedRealRV_smearedOnGaugeFields hWeight hSpace (f i)
theorem expectationInvariantOnTorus : ExpectationInvariantOnTorus r :=
  ⟨fun _ hF => expectation_actOn hlat hiso r hF,
    fun w _ => generatingFunctionOfSource_comp_invFun hlat hiso hWeight hSpace r w⟩
end Measures
theorem mapsStructureOnTorus (hlat : ScaledMotionPropertiesClaim)
    (hiso : PeriodicLattice.LevelIsometryPropertiesExpanded)
    (r : D.TorusLatticeIsometry) : MapsStructureOnTorus r := by
  refine ⟨?_, fun U hU => r.pullbackField_mem hU, fun Φ h => ?_⟩
  · obtain ⟨Φ₀, h₀⟩ := exists_motion_onTorus_eq hiso r
    obtain ⟨-, -, -, -, -, -, hLinks, -⟩ := hlat D _ Φ₀
    intro c
    obtain ⟨b, hb⟩ := hLinks.1.2 c
    exact ⟨b, (torus_linkMap_eq r h₀ b).trans hb⟩
  · obtain ⟨-, -, -, -, -, -, -, -, hP, -, hC, -⟩ := hlat D _ Φ
    have e : r.pointMap = Φ.onTorusSite := funext (torus_pointMap_eq r h)
    refine ⟨hP.2.1.2, fun p => ?_, fun p => ?_, fun U hU p => ?_⟩
    · rw [e]
      exact hP.1 p
    · rw [← h]
      exact hP.2.2.2 p
    · rw [torus_pullbackField_eq r h]
      exact hC.2.2.2.2.2 p U hU
theorem mapsStructureOnSpace (hlat : ScaledMotionPropertiesClaim)
    (hIsometryAffine : LinearAlgebra.NormIsometry.BijectiveNormIsometryIsAffine)
    (r : D.R4LatticeIsometry) : MapsStructureOnSpace r := by
  refine ⟨?_, fun Φ h => ?_⟩
  · obtain ⟨Φ₀, h₀⟩ := exists_motion_onSpace_eq hIsometryAffine r
    obtain ⟨-, -, -, -, -, hLinks, -⟩ := hlat D _ Φ₀
    intro c
    obtain ⟨b, hb⟩ := hLinks.1.2 c
    exact ⟨b, (space_linkMap_eq r h₀ b).trans hb⟩
  · obtain ⟨-, -, -, -, -, -, -, hP, -, hC, -⟩ := hlat D _ Φ
    have e : r.toLatticeSymmetry.pointMap = Φ.onPoint := funext (space_pointMap_eq r h)
    refine ⟨hP.2.1.2, fun p => ?_, fun p => ?_, fun U p => ?_⟩
    · rw [e]
      exact hP.1 p
    · rw [← h]
      exact hP.2.2.2 p
    · rw [space_pullbackField_eq r h]
      exact hC.2.2.2.2 p U
theorem expSmearedOnSpace (hlat : ScaledMotionPropertiesClaim)
    (hIsometryAffine : LinearAlgebra.NormIsometry.BijectiveNormIsometryIsAffine)
    (r : D.R4LatticeIsometry) : ExpSmearedOnSpace r := by
  intro w hw U
  obtain ⟨Φ, h⟩ := exists_motion_onSpace_eq hIsometryAffine r
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hO, -⟩ := hlat D _ Φ
  change Complex.exp (InfiniteLattice.smearedEnergy w (r.pullbackField U)) =
    Complex.exp (InfiniteLattice.smearedEnergy (w ∘ r.invFun) U)
  rw [space_pullbackField_eq r h, ← space_invFun_eq r, ← h]
  exact congrArg Complex.exp (hO w hw U)
theorem expSmearedOnTorus (hlat : ScaledMotionPropertiesClaim)
    (hiso : PeriodicLattice.LevelIsometryPropertiesExpanded)
    (r : D.TorusLatticeIsometry) : ExpSmearedOnTorus r := by
  intro w _ U hU
  obtain ⟨Φ, h⟩ := exists_motion_onTorus_eq hiso r
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, -, -, -⟩ := hlat D _ Φ
  exact congrArg Complex.exp (smeared_pullbackField r h hO w hU)
theorem isometryInvarianceHolds (hlat : ScaledMotionPropertiesClaim)
    (hiso : PeriodicLattice.LevelIsometryPropertiesExpanded)
    (hIsometryAffine : LinearAlgebra.NormIsometry.BijectiveNormIsometryIsAffine)
    (hWeight : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hSpace : PeriodicLattice.CutoffData.ConfigSpace.BasicStructure) :
    IsometryInvarianceHolds := by
  intro D
  refine ⟨fun f => ⟨?_, ?_⟩, fun f => ⟨?_, ?_⟩, fun r => ⟨mapsStructureOnTorus hlat hiso r,
    expSmearedOnTorus hlat hiso r, expectationInvariantOnTorus hlat hiso hWeight hSpace r,
    cumulantsInvariantOnTorus hlat hiso hWeight hSpace r⟩, fun r r' F _ U _ => rfl,
    fun r => ⟨mapsStructureOnSpace hlat hIsometryAffine r, expSmearedOnSpace hlat hIsometryAffine r⟩,
    fun r r' F _ => rfl⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨Φ, h⟩ := exists_motion_onTorus_eq hiso r
    exact ⟨Φ.rotation, Φ, rfl, h⟩
  · rintro ⟨S, Φ, -, rfl⟩
    obtain ⟨-, hS, -⟩ := hlat D _ Φ
    exact ⟨toTorusLatticeIsometry Φ hS, rfl⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨Φ, h⟩ := exists_motion_onSpace_eq hIsometryAffine r
    exact ⟨Φ.rotation, Φ, rfl, h⟩
  · rintro ⟨S, Φ, -, rfl⟩
    obtain ⟨hS, -⟩ := hlat D _ Φ
    exact ⟨toR4LatticeIsometry Φ hS, rfl⟩
end YangMills.Construction.SourcesAndGluing.IsometryInvariance
end
