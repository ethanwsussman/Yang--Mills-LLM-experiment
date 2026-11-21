import YangMills.Construction.InfiniteLattice.FunctionsOfASetOfBonds
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLattice
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Towers.IsometriesOfATowerAreHypercubicMotionsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction.LatticeCovering
open YangMills.Construction.FixedSpacing (Params)
open YangMills.Construction.InfiniteLattice (AmbientSpace projectLink projectPoint hypercubicGroup
  latticeMotions liftField liftCompactField liftedWilsonMeasure)
open YangMills.Construction.TestFunctions (latticeTranslate)
open YangMills.Construction.TorusMetric (torusProj euclidNormVec torusEuclidNorm)
section Numbers
variable (D : Params)
theorem one_le_blockFactor : (1 : ℝ) ≤ D.L := by
  have := D.isAdmissible.2
  exact_mod_cast (by omega : 1 ≤ D.L)
theorem mesh_pos : 0 < mesh D := by apply _root_.YangMills.Construction.InfiniteLattice.LinkSetFunctions.mesh_pos <;> assumption
theorem two_le_period : 2 ≤ period D := by
  have h : (1 : ℝ) ≤ (D.L : ℝ) ^ (D.m : ℕ) := one_le_pow₀ (one_le_blockFactor D)
  simp only [period, PeriodicLattice.torusSide]
  linarith
theorem period_pos : 0 < period D := by linarith [two_le_period D]
theorem mesh_le_one : mesh D ≤ 1 := by
  have h : (1 : ℝ) ≤ (D.L : ℝ) ^ (D.K : ℕ) := one_le_pow₀ (one_le_blockFactor D)
  simp only [mesh, PeriodicLattice.meshSize, spacingIndex, zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ h
theorem mesh_lt_period : mesh D < period D := by
  linarith [two_le_period D, mesh_le_one D]
theorem exists_period_eq_int_mul_mesh : ∃ S : ℤ, period D = (S : ℝ) * mesh D := by
  refine ⟨2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)), ?_⟩
  have h := PeriodicLattice.pointsPerAxis_eq D.L D.m D.K
  rw [PeriodicLattice.pointsPerAxis, div_eq_iff (mesh_pos D).ne'] at h
  simpa using h
end Numbers
section EuclideanNorm
theorem euclidNormVec_sub_comm (x y : AmbientSpace) :
    euclidNormVec (x - y) = euclidNormVec (y - x) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem euclidNormVec_add_le (x y : AmbientSpace) :
    euclidNormVec (x + y) ≤ euclidNormVec x + euclidNormVec y := by apply _root_.YangMills.SharedProofs.p2091 <;> assumption
theorem euclidNormVec_sub_le_add (x y z : AmbientSpace) :
    euclidNormVec (x - z) ≤ euclidNormVec (x - y) + euclidNormVec (y - z) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_le <;> assumption
theorem le_euclidNormVec_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ euclidNormVec (latticeTranslate ℓ k) := by apply _root_.YangMills.Construction.TestPairs.le_euclidNormVec_latticeTranslate <;> assumption
end EuclideanNorm
section Fibers
theorem torusProj_add (ℓ : ℝ) (x y : AmbientSpace) :
    torusProj ℓ (x + y) = torusProj ℓ x + torusProj ℓ y := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_add' <;> assumption
theorem torusProj_sub (ℓ : ℝ) (x y : AmbientSpace) :
    torusProj ℓ (x - y) = torusProj ℓ x - torusProj ℓ y := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_sub' <;> assumption
theorem torusProj_eq_iff (ℓ : ℝ) (x y : AmbientSpace) :
    torusProj ℓ x = torusProj ℓ y ↔ ∃ k : Fin 4 → ℤ, x - y = latticeTranslate ℓ k := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq h
    exact ⟨k, by rw [hk]; abel⟩
  · rintro ⟨k, hk⟩
    have h : x = y + latticeTranslate ℓ k := by rw [← hk]; abel
    rw [h]
    exact TestFunctions.torusProj_add_latticeTranslate ℓ y k
theorem eq_zero_of_linfNorm_latticeTranslate_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ}
    (h : GibbsAtFixedSpacing.linfNorm (latticeTranslate ℓ k) < ℓ) : k = 0 := by
  funext μ
  have h1 : |latticeTranslate ℓ k μ| ≤ GibbsAtFixedSpacing.linfNorm (latticeTranslate ℓ k) :=
    Finset.le_sup' (fun μ => |latticeTranslate ℓ k μ|) (Finset.mem_univ μ)
  have h2 : ℓ * |(k μ : ℝ)| < ℓ := by
    simp only [latticeTranslate, abs_mul, abs_of_pos hℓ] at h1
    linarith
  have h3 : |(k μ : ℝ)| < 1 := by nlinarith
  have h4 : |k μ| < 1 := by exact_mod_cast h3
  simpa using Int.abs_lt_one_iff.mp h4
theorem fibersOfProjection (D : Params) : FibersOfProjection D := by
  refine ⟨torusProj_eq_iff _, ?_, ?_⟩
  · intro S hS x hx y hy hxy
    obtain ⟨k, hk⟩ := (torusProj_eq_iff _ x y).mp hxy
    have h := hS x hx y hy
    rw [hk] at h
    have h0 := eq_zero_of_linfNorm_latticeTranslate_lt (period_pos D) h
    rw [h0] at hk
    have : latticeTranslate (period D) 0 = 0 := by
      funext μ
      simp [latticeTranslate]
    rw [this] at hk
    exact sub_eq_zero.mp hk
  · ext x
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨S, hS⟩ := exists_period_eq_int_mul_mesh D
      have hc : torusProj (period D) x = torusProj (period D) fun μ => (n μ : ℝ) * mesh D := by
        funext μ
        exact hn μ
      obtain ⟨k, hk⟩ := (torusProj_eq_iff _ _ _).mp hc
      refine ⟨fun μ => n μ + S * k μ, fun μ => ?_⟩
      have h := congrFun hk μ
      simp only [Pi.sub_apply, latticeTranslate, hS] at h
      push_cast
      linarith
    · rintro ⟨n, hn⟩
      exact ⟨n, fun μ => by simp [torusProj, hn μ]⟩
end Fibers
section Links
variable {L m : ℕ} {j : ℤ}
theorem torusProj_single (L m : ℕ) (κ : Fin 4) (t : ℝ) :
    torusProj (PeriodicLattice.torusSide L m) (Pi.single κ t) =
      PeriodicLattice.pointOnAxis L m κ t := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_single <;> assumption
theorem projectPoint_add (x y : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j (x + y) = projectPoint L m j x + projectPoint L m j y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_add <;> assumption
theorem projectPoint_axisStep_eq_unitStep (κ : Fin 4) :
    projectPoint L m j (InfiniteLattice.axisStep (PeriodicLattice.meshSize L j) κ) =
      PeriodicLattice.unitStep L m j κ := by apply _root_.YangMills.Construction.InfiniteLattice.projectPoint_axisStep <;> assumption
theorem projectLink_forwardFrom (x : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j))
    (κ : Fin 4) :
    projectLink L m j (InfiniteLattice.Link.forwardFrom x κ) =
      PeriodicLattice.Bond.forwardFrom (projectPoint L m j x) κ := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectLink_forwardFrom <;> assumption
theorem projectPoint_surjective : Surjective (projectPoint L m j) := by
  rintro ⟨z, hz⟩
  have hz' := hz
  rw [PeriodicLattice.sublattice_eq_map_latticeSubgroup] at hz'
  obtain ⟨x, hx, rfl⟩ := hz'
  exact ⟨⟨x, hx⟩, rfl⟩
end Links
section LinksAtParams
variable (D : Params)
theorem forwardFrom_injective :
    Injective fun q : PeriodicLattice.Site D.L D.m (spacingIndex D) × Fin 4 =>
      PeriodicLattice.Bond.forwardFrom q.1 q.2 := by
  rintro ⟨z, κ⟩ ⟨z', κ'⟩ h
  have ht : z = z' := congrArg PeriodicLattice.Bond.source h
  subst ht
  have hh : z + PeriodicLattice.unitStep D.L D.m (spacingIndex D) κ =
      z + PeriodicLattice.unitStep D.L D.m (spacingIndex D) κ' :=
    congrArg PeriodicLattice.Bond.target h
  have hs := add_left_cancel hh
  have hv : PeriodicLattice.pointOnAxis D.L D.m κ (mesh D) =
      PeriodicLattice.pointOnAxis D.L D.m κ' (mesh D) := congrArg Subtype.val hs
  by_contra hne
  have hκ : κ ≠ κ' := fun hc => hne (by rw [hc])
  have h0 := congrFun hv κ
  simp only [PeriodicLattice.pointOnAxis, Pi.single_eq_same, Pi.single_eq_of_ne hκ] at h0
  rw [AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨n, hn⟩ := h0
  have hn' : (n : ℝ) * period D = mesh D := by simpa using hn
  have hpos := mesh_pos D
  have hlt := mesh_lt_period D
  have hs0 := period_pos D
  have hn1 : (0 : ℝ) < n := by
    by_contra hc
    have : (n : ℝ) * period D ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) hs0.le
    linarith
  have hn2 : (n : ℝ) < 1 := by nlinarith
  have a1 : 0 < n := by exact_mod_cast hn1
  have a2 : n < 1 := by exact_mod_cast hn2
  omega
theorem linksAndPlaquettesUnderProjection
    (hlift : TorusLifts.ProjectionOfLattice D.L D.m (D.K : ℕ)) :
    LinksAndPlaquettesUnderProjection D := by
  refine ⟨⟨fun _ _ => ⟨_, _, rfl⟩, (forwardFrom_injective D).injOn, ?_⟩, projectLink_forwardFrom,
    fun p => ⟨rfl, rfl, rfl⟩, ?_, hlift.2.2.2.2.1, ?_, hlift.2.2.2.2.2⟩
  · rintro _ ⟨z, κ, rfl⟩
    exact ⟨(z, κ), mem_univ _, rfl⟩
  · ext b
    constructor
    · rintro ⟨_, ⟨x, κ, rfl⟩, rfl⟩
      exact ⟨_, κ, projectLink_forwardFrom x κ⟩
    · rintro ⟨z, κ, rfl⟩
      obtain ⟨x, rfl⟩ := projectPoint_surjective z
      exact ⟨_, ⟨x, κ, rfl⟩, projectLink_forwardFrom x κ⟩
  · intro p
    ext b
    simp only [PeriodicLattice.Plaquette.edges, InfiniteLattice.ElementaryPlaquette.sideLinks,
      TorusLifts.projectPlaquette, mem_insert_iff, mem_singleton_iff, mem_image, mem_ofPred_eq,
      List.mem_cons, List.not_mem_nil, or_false]
    have e1 := projectLink_forwardFrom (L := D.L) (m := D.m) (j := spacingIndex D) p.corner p.lowAxis
    have e2 := projectLink_forwardFrom (L := D.L) (m := D.m) (j := spacingIndex D)
      (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis
    have e3 := projectLink_forwardFrom (L := D.L) (m := D.m) (j := spacingIndex D)
      (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis
    have e4 := projectLink_forwardFrom (L := D.L) (m := D.m) (j := spacingIndex D) p.corner p.highAxis
    rw [projectPoint_add, projectPoint_axisStep_eq_unitStep] at e2 e3
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨_, Or.inl rfl, e1⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), e2⟩
      · exact ⟨_, Or.inr (Or.inl rfl), e3⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), e4⟩
    · rintro ⟨_, (rfl | rfl | rfl | rfl), rfl⟩
      · exact Or.inl e1
      · exact Or.inr (Or.inr (Or.inl e3))
      · exact Or.inr (Or.inr (Or.inr e4))
      · exact Or.inr (Or.inl e2)
end LinksAtParams
section Lift
variable (D : Params)
theorem faceEnergy_liftCompactField {L m : ℕ} {j : ℤ}
    (U : PeriodicLattice.CompactGaugeField L m j)
    (p : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L j)) :
    InfiniteLattice.faceEnergy (liftCompactField U) p =
      PeriodicLattice.plaquetteCost U.1 (TorusLifts.projectPlaquette L m j p) := by
  have e : ∀ (x : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j)) (κ : Fin 4),
      liftCompactField U (InfiniteLattice.Link.forwardFrom x κ) =
        U.linkValue (PeriodicLattice.Bond.forwardFrom (projectPoint L m j x) κ) := fun x κ => by
    rw [InfiniteLattice.liftCompactField_apply, projectLink_forwardFrom]
  have hv : ((InfiniteLattice.faceHolonomy (liftCompactField U) p :
      Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      PeriodicLattice.plaquetteHolonomy U.1 (TorusLifts.projectPlaquette L m j p) := by
    have hr : ∀ b : PeriodicLattice.Bond L m j,
        (((U.linkValue b)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
          U.1 b.opposite := fun b => by
      rw [← U.linkValue_opposite b]
      rfl
    simp only [InfiniteLattice.faceHolonomy, e, projectPoint_add, projectPoint_axisStep_eq_unitStep,
      PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds, TorusLifts.projectPlaquette, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, Submonoid.coe_mul, hr]
    simp only [mul_assoc]
    rfl
  simp only [InfiniteLattice.faceEnergy, PeriodicLattice.plaquetteCost, hv]
theorem liftAndLiftedMeasure
    (hw : IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure D.L D.m (D.K : ℕ) D.β)) :
    LiftAndLiftedMeasure D := by
  have hm := InfiniteLattice.measurable_liftField D.L D.m (spacingIndex D)
  refine ⟨InfiniteLattice.continuous_liftCompactField,
    fun U b _ => InfiniteLattice.liftCompactField_apply U b,
    fun U p => faceEnergy_liftCompactField U p, fun F hF => ?_,
    fun E hE => InfiniteLattice.continuous_liftCompactField.measurable hE,
    Measure.isProbabilityMeasure_map hm.aemeasurable⟩
  exact integral_map hm.aemeasurable hF.1.aestronglyMeasurable
end Lift
section Motions
variable {a : ℝ}
theorem descendedMap_eq_of_descends {ℓ : ℝ} {f : AmbientSpace → AmbientSpace}
    {Φ : TorusMetric.Torus4 ℓ → TorusMetric.Torus4 ℓ}
    (h : TorusLifts.Descends ℓ ℓ f Φ) : TorusLifts.descendedMap ℓ ℓ f = Φ := by
  funext u
  have h1 := congrFun h (TestFunctions.liftPoint u)
  simp only [comp_apply, TestFunctions.torusProj_liftPoint] at h1
  exact h1.symm
theorem frameLinearMap_apply (f : PeriodicLattice.SignedFrame) (x : AmbientSpace) (μ : Fin 4) :
    InfiniteLattice.frameLinearMap f x μ = ((f.2 μ : ℤ) : ℝ) * x (f.1 μ) := rfl
theorem intUnit_mul_self (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]
def invFrame (f : PeriodicLattice.SignedFrame) : PeriodicLattice.SignedFrame :=
  (f.1⁻¹, fun ν => f.2 (f.1.symm ν))
theorem frameLinearMap_invFrame_frameLinearMap (f : PeriodicLattice.SignedFrame) (x : AmbientSpace) :
    InfiniteLattice.frameLinearMap (invFrame f) (InfiniteLattice.frameLinearMap f x) = x := by
  funext ν
  simp only [frameLinearMap_apply, invFrame]
  have h : f.1 (f.1⁻¹ ν) = ν := by simp
  rw [h, ← mul_assoc]
  have h' : f.1⁻¹ ν = f.1.symm ν := rfl
  rw [h', intUnit_mul_self, one_mul]
theorem frameLinearMap_frameLinearMap_invFrame (f : PeriodicLattice.SignedFrame) (x : AmbientSpace) :
    InfiniteLattice.frameLinearMap f (InfiniteLattice.frameLinearMap (invFrame f) x) = x := by
  funext μ
  simp only [frameLinearMap_apply, invFrame]
  have h : f.1⁻¹ (f.1 μ) = μ := by simp
  have h' : f.1.symm (f.1 μ) = μ := by simp
  rw [h, h', ← mul_assoc, intUnit_mul_self, one_mul]
theorem exists_motion_add_latticeTranslate {r : AmbientSpace → AmbientSpace}
    (hr : r ∈ latticeMotions a) (ℓ : ℝ) (x : AmbientSpace) (k : Fin 4 → ℤ) :
    ∃ k' : Fin 4 → ℤ, r (x + latticeTranslate ℓ k) = r x + latticeTranslate ℓ k' := by
  obtain ⟨w, hw, v, -, h⟩ := hr
  obtain ⟨f, rfl⟩ := InfiniteLattice.exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
  refine ⟨fun μ => (f.2 μ : ℤ) * k (f.1 μ), ?_⟩
  rw [h, h, map_add]
  funext μ
  simp only [Pi.add_apply, frameLinearMap_apply, latticeTranslate]
  push_cast
  ring
theorem descends_of_mem_latticeMotions {r : AmbientSpace → AmbientSpace}
    (hr : r ∈ latticeMotions a) (ℓ : ℝ) :
    TorusLifts.Descends ℓ ℓ r (TorusLifts.descendedMap ℓ ℓ r) := by
  funext x
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
    (TestFunctions.torusProj_liftPoint (torusProj ℓ x))
  obtain ⟨k', hk'⟩ := exists_motion_add_latticeTranslate hr ℓ x k
  simp only [comp_apply, TorusLifts.descendedMap]
  rw [hk, hk']
  exact TestFunctions.torusProj_add_latticeTranslate ℓ _ _
theorem descendedMap_torusProj {r : AmbientSpace → AmbientSpace} (hr : r ∈ latticeMotions a)
    (ℓ : ℝ) (x : AmbientSpace) :
    TorusLifts.descendedMap ℓ ℓ r (torusProj ℓ x) = torusProj ℓ (r x) :=
  congrFun (descends_of_mem_latticeMotions hr ℓ) x
theorem exists_inverse_mem_latticeMotions {r : AmbientSpace → AmbientSpace}
    (hr : r ∈ latticeMotions a) :
    ∃ t ∈ latticeMotions a, LeftInverse t r ∧ RightInverse t r := by
  obtain ⟨w, hw, v, hv, h⟩ := hr
  obtain ⟨f, rfl⟩ := InfiniteLattice.exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
  set w' := InfiniteLattice.frameLinearMap (invFrame f) with hw'
  have hw'm : w' ∈ hypercubicGroup := InfiniteLattice.frameLinearMap_mem_hypercubicGroup _
  have hmot : (w' : AmbientSpace → AmbientSpace) ∈ latticeMotions a :=
    ⟨w', hw'm, 0, zero_mem _, fun x => by simp⟩
  have hsite : w' v ∈ InfiniteLattice.latticeSubgroup a := by
    have h1 : w' v ∈ (w' : AmbientSpace → AmbientSpace) ''
        (InfiniteLattice.latticeSubgroup a : Set AmbientSpace) := ⟨v, hv, rfl⟩
    rw [InfiniteLattice.LatticeMotion.image_latticeSubgroup hmot] at h1
    exact h1
  refine ⟨fun x => w' x + -w' v, ⟨w', hw'm, -w' v, neg_mem hsite, fun _ => rfl⟩, fun x => ?_,
    fun x => ?_⟩
  · simp only [h, map_add, hw', frameLinearMap_invFrame_frameLinearMap]
    abel
  · simp only [h, map_add, map_neg, hw', frameLinearMap_frameLinearMap_invFrame]
    abel
theorem coe_sublattice (L m : ℕ) (j : ℤ) :
    (PeriodicLattice.sublattice L m j : Set (PeriodicLattice.FourTorus L m)) =
      torusProj (PeriodicLattice.torusSide L m) ''
        (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L j) : Set AmbientSpace) := by apply _root_.YangMills.Construction.Tower.HypercubicMotions.sublattice_eq_image <;> assumption
theorem isTorusIsometry_descendedMap {L m : ℕ} {r : AmbientSpace → AmbientSpace}
    (hr : r ∈ latticeMotions a) :
    PeriodicLattice.IsTorusIsometry (L := L) (m := m)
      (TorusLifts.descendedMap (PeriodicLattice.torusSide L m) (PeriodicLattice.torusSide L m) r) := by
  intro u u'
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  obtain ⟨y, rfl⟩ := TestFunctions.torusProj_surjective _ u'
  rw [descendedMap_torusProj hr, descendedMap_torusProj hr,
    PeriodicLattice.torusEuclidDist_torusProj, PeriodicLattice.torusEuclidDist_torusProj]
  congr 1
  obtain ⟨t, ht, hl, hrt⟩ := exists_inverse_mem_latticeMotions hr
  ext c
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := exists_motion_add_latticeTranslate ht (PeriodicLattice.torusSide L m) (r y) k
    rw [hl y] at hk'
    refine ⟨k', ?_⟩
    have h1 := InfiniteLattice.LatticeMotion.euclidNormVec_sub hr x
      (y + latticeTranslate (PeriodicLattice.torusSide L m) k')
    have h2 : r (y + latticeTranslate (PeriodicLattice.torusSide L m) k') =
        r y + latticeTranslate (PeriodicLattice.torusSide L m) k := by rw [← hk', hrt]
    rw [h2, sub_add_eq_sub_sub, sub_add_eq_sub_sub] at h1
    exact h1.symm
  · rintro ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := exists_motion_add_latticeTranslate hr (PeriodicLattice.torusSide L m) y k
    refine ⟨k', ?_⟩
    have h1 := InfiniteLattice.LatticeMotion.euclidNormVec_sub hr x
      (y + latticeTranslate (PeriodicLattice.torusSide L m) k)
    rw [hk', sub_add_eq_sub_sub, sub_add_eq_sub_sub] at h1
    exact h1
variable (D : Params)
theorem descentOfMotion (r : latticeMotions (mesh D)) : DescentOfMotion D r := by
  have hr := r.2
  have hind := descends_of_mem_latticeMotions hr (period D)
  have hcov : ∀ x, descend D r.1 (proj D x) = proj D (r.1 x) :=
    fun x => descendedMap_torusProj hr (period D) x
  refine ⟨hind, fun σ hσ => (descendedMap_eq_of_descends hσ).symm, isTorusIsometry_descendedMap hr,
    ?_, fun t ht => ?_, ?_, ?_, ?_⟩
  · rw [coe_sublattice, image_image]
    simp only [hcov]
    conv_rhs => rw [← InfiniteLattice.LatticeMotion.image_latticeSubgroup hr]
    rw [image_image]
  · refine descendedMap_eq_of_descends ?_
    funext x
    simp only [comp_apply, InfiniteLattice.latticeMotionMul, descend]
    rw [descendedMap_torusProj ht, descendedMap_torusProj hr]
  · obtain ⟨t, ht, hl, hrt⟩ := exists_inverse_mem_latticeMotions hr
    refine ⟨t, ht, hl, hrt, fun u => ?_, fun u => ?_⟩
    · obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
      simp only [descend]
      rw [descendedMap_torusProj hr, descendedMap_torusProj ht, hl x]
    · obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
      simp only [descend]
      rw [descendedMap_torusProj ht, descendedMap_torusProj hr, hrt x]
  · intro w _ v _ hwv z κ
    obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ z
    simp only [descend, PeriodicLattice.translateByVector]
    rw [← torusProj_add, descendedMap_torusProj hr, descendedMap_torusProj hr, ← torusProj_add, hwv,
      hwv, map_add, map_smul]
    congr 1
    abel
  · intro s hs U
    refine Subtype.ext (funext fun b => ?_)
    change liftCompactField U ((InfiniteLattice.latticeMotionSymmetry r).linkMap b) =
      liftCompactField (s.pullback U) b
    rw [InfiniteLattice.liftCompactField_apply]
    refine Eq.trans ?_ (InfiniteLattice.liftCompactField_apply (L := D.L) (m := D.m)
      (j := spacingIndex D) (s.pullback U) b).symm
    have himg : s.IsBondImage (projectLink D.L D.m (spacingIndex D) b)
        (projectLink D.L D.m (spacingIndex D) ((InfiniteLattice.latticeMotionSymmetry r).linkMap b)) := by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change proj D (r.1 b.initial) = s.toFun (proj D b.initial)
        rw [hs, hcov]
      · change proj D (r.1 b.terminal) = s.toFun (proj D b.terminal)
        rw [hs, hcov]
    have key : projectLink D.L D.m (spacingIndex D)
        ((InfiniteLattice.latticeMotionSymmetry r).linkMap b) =
        s.bondMap (projectLink D.L D.m (spacingIndex D) b) := by
      classical
      have h : ∃ b', s.IsBondImage (projectLink D.L D.m (spacingIndex D) b) b' := ⟨_, himg⟩
      have e : s.bondMap (projectLink D.L D.m (spacingIndex D) b) = h.choose := dif_pos h
      rw [e]
      exact s.isBondImage_unique himg h.choose_spec
    rw [key]
    rfl
theorem descentOfBasicMotions : DescentOfBasicMotions D := by
  refine ⟨fun v => descendedMap_eq_of_descends ?_, fun w _ π ε hw => descendedMap_eq_of_descends ?_,
    fun P => descendedMap_eq_of_descends ?_⟩
  · funext x
    simp only [comp_apply]
    rw [torusProj_add]
  · funext x
    simp only [comp_apply]
    funext μ
    change ((ε μ : ℤˣ) : ℤ) • ((x (π μ) : ℝ) : AddCircle (period D)) =
      ((w x μ : ℝ) : AddCircle (period D))
    rw [hw x μ]
    rcases Int.units_eq_one_or (ε μ) with h | h <;> simp [h]
  · funext x
    exact P.reflectEquiv_torusProj x
end Motions
section Periodization
open YangMills.Construction.InfiniteLattice (IsPeriodizableInBall torusPeriodize)
open YangMills.Construction.TestFunctions (closedBallR4)
variable {D : Params} {ρ : ℝ} {f : AmbientSpace → ℂ}
theorem latticeTranslate_sub (ℓ : ℝ) (k k' : Fin 4 → ℤ) :
    latticeTranslate ℓ (k - k') = latticeTranslate ℓ k - latticeTranslate ℓ k' := by
  funext μ
  simp [latticeTranslate, mul_sub]
theorem latticeTranslate_zero (ℓ : ℝ) : latticeTranslate ℓ 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.latticeTranslate_zero <;> assumption
theorem mem_closedBallR4_of_ne_zero (h : IsPeriodizableInBall D.toStandingParameters ρ f)
    {x : AmbientSpace} (hx : f x ≠ 0) : x ∈ closedBallR4 0 ρ :=
  h.2.2.2 (subset_tsupport f hx)
theorem four_mul_lt_period (h : IsPeriodizableInBall D.toStandingParameters ρ f) :
    4 * ρ < period D := by
  have h1 : 4 * ρ + 4 ≤ period D := InfiniteLattice.le_periodizationRadius_iff.mp h.2.1
  linarith
theorem eq_zero_of_sub_eq_latticeTranslate (h : IsPeriodizableInBall D.toStandingParameters ρ f)
    {x y : AmbientSpace} (hx : x ∈ closedBallR4 0 ρ) (hy : y ∈ closedBallR4 0 ρ)
    {k : Fin 4 → ℤ} (hk : x - y = latticeTranslate (period D) k) : k = 0 := by
  by_contra hne
  have h1 := le_euclidNormVec_latticeTranslate (period_pos D) hne
  have h2 := InfiniteLattice.euclidNormVec_sub_le_of_mem_closedBallR4 hx hy
  rw [hk] at h2
  have h3 := four_mul_lt_period h
  linarith [h.1]
theorem subsingleton_nonzero_terms (h : IsPeriodizableInBall D.toStandingParameters ρ f)
    (x : AmbientSpace) :
    {k : Fin 4 → ℤ | f (x + latticeTranslate (period D) k) ≠ 0}.Subsingleton := by
  intro k hk k' hk'
  have h0 := eq_zero_of_sub_eq_latticeTranslate h (mem_closedBallR4_of_ne_zero h hk)
    (mem_closedBallR4_of_ne_zero h hk') (k := k - k') (by rw [latticeTranslate_sub]; abel)
  exact sub_eq_zero.mp h0
theorem torusPeriodize_proj_of_mem (h : IsPeriodizableInBall D.toStandingParameters ρ f)
    {x : AmbientSpace} (hx : x ∈ closedBallR4 0 ρ) :
    torusPeriodize D.toStandingParameters f (proj D x) = f x := by
  change TestFunctions.periodize (period D) f (torusProj (period D) x) = f x
  rw [TestFunctions.periodize_torusProj, TestFunctions.periodicSum,
    tsum_eq_single (0 : Fin 4 → ℤ), latticeTranslate_zero, add_zero]
  intro k hk
  by_contra hne
  exact hk (eq_zero_of_sub_eq_latticeTranslate h (mem_closedBallR4_of_ne_zero h hne) hx (by abel))
theorem torusPeriodize_eq_zero_of_notMem (h : IsPeriodizableInBall D.toStandingParameters ρ f)
    {u : PeriodicLattice.FourTorus D.L D.m} (hu : u ∉ proj D '' closedBallR4 0 ρ) :
    torusPeriodize D.toStandingParameters f u = 0 := by
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  change TestFunctions.periodize (period D) f (torusProj (period D) x) = 0
  rw [TestFunctions.periodize_torusProj, TestFunctions.periodicSum]
  have h0 : ∀ k : Fin 4 → ℤ, f (x + latticeTranslate (period D) k) = 0 := fun k => by
    by_contra hne
    exact hu ⟨_, mem_closedBallR4_of_ne_zero h hne, TestFunctions.torusProj_add_latticeTranslate _ _ _⟩
  simp only [h0, tsum_zero]
theorem isPeriodizationOn_torusPeriodize (h : IsPeriodizableInBall D.toStandingParameters ρ f) :
    IsPeriodizationOn D ρ f (torusPeriodize D.toStandingParameters f) :=
  ⟨fun _ hx => torusPeriodize_proj_of_mem h hx, fun _ hu => torusPeriodize_eq_zero_of_notMem h hu⟩
theorem eq_torusPeriodize_of_isPeriodizationOn
    (h : IsPeriodizableInBall D.toStandingParameters ρ f)
    {g : PeriodicLattice.FourTorus D.L D.m → ℂ} (hg : IsPeriodizationOn D ρ f g) :
    g = torusPeriodize D.toStandingParameters f := by
  funext u
  by_cases hu : u ∈ proj D '' closedBallR4 0 ρ
  · obtain ⟨x, hx, rfl⟩ := hu
    rw [hg.1 x hx, torusPeriodize_proj_of_mem h hx]
  · rw [hg.2 u hu, torusPeriodize_eq_zero_of_notMem h hu]
theorem im_torusPeriodize_eq_zero (h : IsPeriodizableInBall D.toStandingParameters ρ f)
    (hf : ∀ x, (f x).im = 0) (u : PeriodicLattice.FourTorus D.L D.m) :
    (torusPeriodize D.toStandingParameters f u).im = 0 := by
  by_cases hu : u ∈ proj D '' closedBallR4 0 ρ
  · obtain ⟨x, hx, rfl⟩ := hu
    rw [torusPeriodize_proj_of_mem h hx]
    exact hf x
  · rw [torusPeriodize_eq_zero_of_notMem h hu]
    simp
theorem torusEuclidNorm_nonneg {ℓ : ℝ} (u : TorusMetric.Torus4 ℓ) : 0 ≤ torusEuclidNorm u := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
theorem norm_torusPeriodize_sub_le_of_ne_zero (hmin : TorusLifts.TorusDistEqMinOverLifts (period D))
    (h : IsPeriodizableInBall D.toStandingParameters ρ f) {C : ℝ}
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y)
    {u u' : PeriodicLattice.FourTorus D.L D.m} (hu : torusPeriodize D.toStandingParameters f u ≠ 0) :
    ‖torusPeriodize D.toStandingParameters f u - torusPeriodize D.toStandingParameters f u'‖ ≤
      C * torusEuclidNorm (u - u') := by
  have himg : u ∈ proj D '' closedBallR4 0 ρ := by
    by_contra hc
    exact hu (torusPeriodize_eq_zero_of_notMem h hc)
  obtain ⟨x, hx, rfl⟩ := himg
  obtain ⟨y, hy, hdist⟩ := (hmin (proj D x) u' x (TestFunctions.liftPoint u') rfl
    (TestFunctions.torusProj_liftPoint u')).2.2.2
  have hleast : ∀ y', torusProj (period D) y' = u' →
      euclidNormVec (x - y) ≤ euclidNormVec (x - y') := by
    intro y' hy'
    have h1 := (hmin (proj D x) u' x y' rfl hy').1.2 ⟨0, rfl⟩
    simp only [latticeTranslate_zero, sub_zero] at h1
    rw [hdist]
    exact h1
  have hval : torusPeriodize D.toStandingParameters f u' = f y := by
    by_cases hb : y ∈ closedBallR4 0 ρ
    · rw [← hy]
      exact torusPeriodize_proj_of_mem h hb
    · have hfy : f y = 0 := by
        by_contra hne
        exact hb (mem_closedBallR4_of_ne_zero h hne)
      rw [hfy]
      by_contra hT
      have himg : u' ∈ proj D '' closedBallR4 0 ρ := by
        by_contra hc
        exact hT (torusPeriodize_eq_zero_of_notMem h hc)
      obtain ⟨y', hy'B, hy'⟩ := himg
      obtain ⟨k, hk⟩ := (torusProj_eq_iff (period D) y' y).mp (hy'.trans hy.symm)
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [latticeTranslate_zero] at hk
        exact hb (sub_eq_zero.mp hk ▸ hy'B)
      have h1 := le_euclidNormVec_latticeTranslate (period_pos D) hk0
      rw [← hk] at h1
      have h2 := euclidNormVec_sub_le_add y' x y
      have h3 := hleast y' hy'
      have h4 := InfiniteLattice.euclidNormVec_sub_le_of_mem_closedBallR4 hx hy'B
      have h5 := euclidNormVec_sub_comm y' x
      have h6 := four_mul_lt_period h
      linarith
  rw [torusPeriodize_proj_of_mem h hx, hval, ← hdist]
  exact hC x y
theorem norm_torusPeriodize_sub_le (hmin : TorusLifts.TorusDistEqMinOverLifts (period D))
    (hmet : TorusLifts.TorusDistIsMetric (period D))
    (h : IsPeriodizableInBall D.toStandingParameters ρ f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y)
    (u u' : PeriodicLattice.FourTorus D.L D.m) :
    ‖torusPeriodize D.toStandingParameters f u - torusPeriodize D.toStandingParameters f u'‖ ≤
      C * TestFunctions.euclidDistTorus u u' := by
  by_cases hu : torusPeriodize D.toStandingParameters f u = 0
  · by_cases hu' : torusPeriodize D.toStandingParameters f u' = 0
    · rw [hu, hu', sub_zero, norm_zero]
      exact mul_nonneg hC0 (torusEuclidNorm_nonneg _)
    · have h1 := norm_torusPeriodize_sub_le_of_ne_zero hmin h hC (u' := u) hu'
      rw [norm_sub_rev]
      obtain ⟨M, hM, -, -⟩ := hmet
      have h2 : torusEuclidNorm (u' - u) = torusEuclidNorm (u - u') := by
        rw [← hM, ← hM]
        exact @dist_comm _ M.toPseudoMetricSpace _ _
      rw [h2] at h1
      exact h1
  · exact norm_torusPeriodize_sub_le_of_ne_zero hmin h hC hu
theorem bijOn_projectPlaquette (hlift : TorusLifts.ProjectionOfLattice D.L D.m (D.K : ℕ))
    (h : IsPeriodizableInBall D.toStandingParameters ρ f) :
    BijOn (TorusLifts.projectPlaquette D.L D.m (spacingIndex D))
      {p : InfiniteLattice.ElementaryPlaquette (mesh D) | f p.center ≠ 0}
      {p' : PeriodicLattice.Plaquette D.L D.m (spacingIndex D) |
        torusPeriodize D.toStandingParameters f p'.barycenter ≠ 0} := by
  have hbary := hlift.2.2.2.2.2
  refine ⟨fun p hp => ?_, fun p hp p' hp' hpp => ?_, fun p' hp' => ?_⟩
  · change torusPeriodize D.toStandingParameters f
      (TorusLifts.projectPlaquette D.L D.m (spacingIndex D) p).barycenter ≠ 0
    rw [hbary p]
    have hB := mem_closedBallR4_of_ne_zero h hp
    rw [torusPeriodize_proj_of_mem h hB]
    exact hp
  · have hc : torusProj (period D) p.center = torusProj (period D) p'.center := by
      rw [← hbary p, ← hbary p', hpp]
    obtain ⟨k, hk⟩ := (torusProj_eq_iff _ _ _).mp hc
    have hk0 := eq_zero_of_sub_eq_latticeTranslate h (mem_closedBallR4_of_ne_zero h hp)
      (mem_closedBallR4_of_ne_zero h hp') hk
    rw [hk0, latticeTranslate_zero] at hk
    have he := sub_eq_zero.mp hk
    have hf : p.lowAxis = p'.lowAxis := congrArg PeriodicLattice.Plaquette.firstAxis hpp
    have hs : p.highAxis = p'.highAxis := congrArg PeriodicLattice.Plaquette.secondAxis hpp
    refine InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext ?_) hf hs
    simp only [InfiniteLattice.ElementaryPlaquette.center, hf, hs] at he
    exact add_right_cancel (add_right_cancel he)
  · have himg : p'.barycenter ∈ proj D '' closedBallR4 0 ρ := by
      by_contra hc
      exact hp' (torusPeriodize_eq_zero_of_notMem h hc)
    obtain ⟨y, hy, hyc⟩ := himg
    have hfy : f y ≠ 0 := by
      intro h0
      apply hp'
      rw [← hyc, torusPeriodize_proj_of_mem h hy, h0]
    set z : AmbientSpace :=
      y - Pi.single p'.firstAxis (mesh D / 2) - Pi.single p'.secondAxis (mesh D / 2) with hz
    have hcz : torusProj (period D) z = (p'.origin : PeriodicLattice.FourTorus D.L D.m) := by
      have hb : torusProj (period D) y = p'.barycenter := hyc
      rw [hz, torusProj_sub, torusProj_sub, hb, torusProj_single, torusProj_single]
      simp only [PeriodicLattice.Plaquette.barycenter]
      abel
    have hzs : z ∈ InfiniteLattice.latticeSubgroup (mesh D) := by
      have h1 : z ∈ torusProj (period D) ⁻¹' (PeriodicLattice.sublattice D.L D.m (spacingIndex D) :
          Set (PeriodicLattice.FourTorus D.L D.m)) := by
        change torusProj (period D) z ∈ PeriodicLattice.sublattice D.L D.m (spacingIndex D)
        rw [hcz]
        exact p'.origin.2
      have h2 := (fibersOfProjection D).2.2
      rw [show proj D = torusProj (period D) from rfl] at h2
      rw [h2] at h1
      exact h1
    refine ⟨⟨⟨z, hzs⟩, p'.firstAxis, p'.secondAxis, p'.firstAxis_lt_secondAxis⟩, ?_, ?_⟩
    · change f (z + Pi.single p'.firstAxis (mesh D / 2) + Pi.single p'.secondAxis (mesh D / 2)) ≠ 0
      have : z + Pi.single p'.firstAxis (mesh D / 2) + Pi.single p'.secondAxis (mesh D / 2) = y := by
        rw [hz]
        abel
      rw [this]
      exact hfy
    · rcases p' with ⟨b, κ, l, hκ⟩
      simp only [TorusLifts.projectPlaquette]
      congr 1
      exact Subtype.ext hcz
theorem smearedEnergy_liftCompactField (hlift : TorusLifts.ProjectionOfLattice D.L D.m (D.K : ℕ))
    (h : IsPeriodizableInBall D.toStandingParameters ρ f)
    (U : PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D)) :
    InfiniteLattice.boundedSupportObservable f (liftCompactField U) =
      PeriodicLattice.smearedObservable (torusPeriodize D.toStandingParameters f) U.1 := by
  set g : PeriodicLattice.Plaquette D.L D.m (spacingIndex D) → ℂ := fun p' =>
    PeriodicLattice.plaquetteCost U.1 p' • torusPeriodize D.toStandingParameters f p'.barycenter
    with hg
  have hbary := hlift.2.2.2.2.2
  have e1 : InfiniteLattice.boundedSupportObservable f (liftCompactField U) =
      ∑ᶠ p' ∈ {p' : PeriodicLattice.Plaquette D.L D.m (spacingIndex D) |
        torusPeriodize D.toStandingParameters f p'.barycenter ≠ 0}, g p' := by
    refine finsum_mem_eq_of_bijOn _ (bijOn_projectPlaquette hlift h) fun p hp => ?_
    simp only [hg]
    rw [hbary p, torusPeriodize_proj_of_mem h (mem_closedBallR4_of_ne_zero h hp),
      faceEnergy_liftCompactField, Complex.real_smul, mul_comm]
  have e2 : ∑ᶠ p' ∈ {p' : PeriodicLattice.Plaquette D.L D.m (spacingIndex D) |
      torusPeriodize D.toStandingParameters f p'.barycenter ≠ 0}, g p' = ∑ᶠ p' ∈ univ, g p' := by
    refine finsum_mem_inter_support_eq g _ _ ?_
    ext p'
    simp only [mem_inter_iff, mem_univ, true_and, and_iff_right_iff_imp, mem_support]
    intro hne h0
    apply hne
    simp only [hg]
    rw [h0, smul_zero]
  rw [e1, e2, finsum_mem_univ]
  rfl
theorem periodizationProperties (hl : TorusLifts.TorusDistEqMinOverLifts (period D))
    (hmet : TorusLifts.TorusDistIsMetric (period D))
    (hlift : TorusLifts.ProjectionOfLattice D.L D.m (D.K : ℕ))
    (h : IsPeriodizableInBall D.toStandingParameters ρ f) : PeriodizationProperties D ρ f := by
  refine ⟨subsingleton_nonzero_terms h, isPeriodizationOn_torusPeriodize h,
    fun g hg => eq_torusPeriodize_of_isPeriodizationOn h hg,
    fun ρ' h' => isPeriodizationOn_torusPeriodize h', im_torusPeriodize_eq_zero h, ?_,
    smearedEnergy_liftCompactField hlift h⟩
  rintro ⟨C, hC0, hC⟩
  refine ⟨⟨C, hC0, norm_torusPeriodize_sub_le hl hmet h hC0 hC⟩, ?_⟩
  refine le_csInf ⟨C, hC0, hC⟩ fun C' hC' => ?_
  exact csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hC'.1, norm_torusPeriodize_sub_le hl hmet h hC'.1 hC'.2⟩
end Periodization
theorem coveringStatement_holds (hLifts : TorusLifts.LiftsAndDescendedMaps.Statement)
    (hWilson : PeriodicLattice.WilsonWeightGaugeInvariance.statement) : CoveringStatement := by
  intro D
  have hl := hLifts D.toStandingParameters
  have hL : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  have hw := (hWilson D.L D.m D.K D.β hL D.m.pos D.K.pos).2.2.2.2.2.2.2.1
  exact ⟨fibersOfProjection D, linksAndPlaquettesUnderProjection D hl.2.2.2.2.2,
    liftAndLiftedMeasure D hw, fun r => descentOfMotion D r, descentOfBasicMotions D,
    fun ρ => InfiniteLattice.le_periodizationRadius_iff,
    fun ρ f h => periodizationProperties hl.1 hl.2.1 hl.2.2.2.2.2 h⟩
end YangMills.Construction.LatticeCovering
end
