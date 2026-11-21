import YangMills.Construction.InfiniteLattice.SitesLinksAndPlaquettesOfTheLatticeProof
import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import YangMills.Construction.InfiniteLattice.CoveringOnSitesBondsPlaquettesAndCorners
import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import YangMills.Construction.Towers.StepsOfTheIteratedAveragesNearTheFreeStepsOnASideProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LatticeCovering
open Set CutoffLattice
section Numbers
variable {L : ℕ}
theorem one_le_factor_cast (hL : Conventions.IsAdmissibleBlockingFactor L) : (1 : ℝ) ≤ L := by apply _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.one_le_factor <;> assumption
theorem two_le_torusSide (hL : Conventions.IsAdmissibleBlockingFactor L) (m : ℕ) :
    2 ≤ PeriodicLattice.torusSide L m := by
  have h : (1 : ℝ) ≤ (L : ℝ) ^ m := one_le_pow₀ (one_le_factor_cast hL)
  simp only [PeriodicLattice.torusSide]
  linarith
theorem spacingAt_eq_inv_pow (L K : ℕ) : CutoffLattice.spacingAt L K = ((L : ℝ) ^ K)⁻¹ := by
  simp only [CutoffLattice.spacingAt, PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
theorem spacingAt_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) :
    CutoffLattice.spacingAt L K ≤ 1 := by
  rw [spacingAt_eq_inv_pow]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_factor_cast hL))
theorem one_eq_intCast_mul_spacingAt (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) :
    (1 : ℝ) = (((L : ℤ) ^ K : ℤ) : ℝ) * CutoffLattice.spacingAt L K := by
  have h : (L : ℝ) ^ K ≠ 0 := (pow_pos (by linarith [one_le_factor_cast hL]) K).ne'
  rw [spacingAt_eq_inv_pow]
  push_cast
  field_simp
theorem torusSide_eq_intCast_mul_spacingAt (hL : Conventions.IsAdmissibleBlockingFactor L) (m K : ℕ) :
    PeriodicLattice.torusSide L m =
      ((2 * (L : ℤ) ^ (m + K) : ℤ) : ℝ) * CutoffLattice.spacingAt L K := by
  have h : (L : ℝ) ^ K ≠ 0 := (pow_pos (by linarith [one_le_factor_cast hL]) K).ne'
  rw [spacingAt_eq_inv_pow, PeriodicLattice.torusSide]
  push_cast
  rw [pow_add]
  field_simp
end Numbers
theorem latticeSubgroup_le_of_eq_mul {c a : ℝ} (z : ℤ) (h : c = (z : ℝ) * a) :
    latticeSubgroup c ≤ latticeSubgroup a := by
  rintro x ⟨n, hn⟩
  refine ⟨fun μ => n μ * z, fun μ => ?_⟩
  rw [hn μ, h]
  push_cast
  ring
theorem addCircle_coe_eq_coe_iff (S x y : ℝ) :
    ((x : AddCircle S) = (y : AddCircle S)) ↔ ∃ n : ℤ, y - x = (n : ℝ) * S := by
  change (QuotientAddGroup.mk x : ℝ ⧸ AddSubgroup.zmultiples S) = QuotientAddGroup.mk y ↔ _
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul] at hk
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul]
    linarith
theorem torusProj_eq_iff (S : ℝ) (x y : AmbientSpace) :
    TorusMetric.torusProj S x = TorusMetric.torusProj S y ↔ y - x ∈ latticeSubgroup S := by
  constructor
  · intro h
    have h' : ∀ μ, ∃ n : ℤ, y μ - x μ = (n : ℝ) * S := fun μ =>
      (addCircle_coe_eq_coe_iff S (x μ) (y μ)).mp (congrFun h μ)
    choose n hn using h'
    exact ⟨n, fun μ => by simpa using hn μ⟩
  · rintro ⟨n, hn⟩
    funext μ
    exact (addCircle_coe_eq_coe_iff S (x μ) (y μ)).mpr ⟨n μ, by simpa using hn μ⟩
theorem torusProj_add (S : ℝ) (x y : AmbientSpace) :
    TorusMetric.torusProj S (x + y) = TorusMetric.torusProj S x + TorusMetric.torusProj S y := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_add' <;> assumption
theorem sitesCover {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (m K : ℕ) :
    SitesCover L m K := by
  refine ⟨latticeSubgroup_le_of_eq_mul _ (one_eq_intCast_mul_spacingAt hL K),
    latticeSubgroup_le_of_eq_mul _ (torusSide_eq_intCast_mul_spacingAt hL m K),
    fun x y => torusProj_eq_iff _ x y, fun x y => torusProj_add _ x y, ?_⟩
  ext y
  constructor
  · rintro ⟨x, ⟨n, hn⟩, rfl⟩
    exact ⟨n, fun μ => by simp [TorusMetric.torusProj, hn]⟩
  · rintro ⟨n, hn⟩
    refine ⟨fun μ => (n μ : ℝ) * PeriodicLattice.meshSize L (K : ℤ), ⟨n, fun μ => rfl⟩, ?_⟩
    funext μ
    exact (hn μ).symm
theorem projectLink_translateLink (L m : ℕ) (j : ℤ) (b : Link (PeriodicLattice.meshSize L j))
    (v : LatticePoint (PeriodicLattice.meshSize L j))
    (hv : (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m)) :
    projectLink L m j (translateLink b v) = projectLink L m j b := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectLink_translateLink <;> assumption
theorem liftCompactField_coe {L m : ℕ} {j : ℤ} (U : PeriodicLattice.CompactGaugeField L m j)
    (b : Link (PeriodicLattice.meshSize L j)) :
    ((liftCompactField U b : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      U.1 (projectLink L m j b) := by
  simp only [liftCompactField]
  rw [liftField_of_mem U.2]
theorem single_sub_single_not_mem {a S : ℝ} (ha : 0 < a) (haS : a < S) {μ κ : Fin 4} (h : μ ≠ κ)
    (hm : (Pi.single κ a - Pi.single μ a : AmbientSpace) ∈ latticeSubgroup S) : False := by
  obtain ⟨n, hn⟩ := hm
  have h1 := hn κ
  simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h.symm, sub_zero] at h1
  rcases le_or_gt (n κ) 0 with h0 | h0
  · have : ((n κ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h0
    nlinarith
  · have : (1 : ℝ) ≤ ((n κ : ℤ) : ℝ) := by exact_mod_cast h0
    nlinarith
theorem linksCover {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (m K : ℕ) :
    LinksCover L m K := by
  have ha : 0 < CutoffLattice.spacingAt L K := spacingAt_pos hL K
  have haS : CutoffLattice.spacingAt L K < PeriodicLattice.torusSide L m := by
    linarith [spacingAt_le_one hL K, two_le_torusSide hL m]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, μ, rfl⟩ _ ⟨y, κ, rfl⟩
    constructor
    · intro h
      have ht : TorusMetric.torusProj (PeriodicLattice.torusSide L m) (x : AmbientSpace) =
          TorusMetric.torusProj (PeriodicLattice.torusSide L m) (y : AmbientSpace) :=
        congrArg Subtype.val (congrArg PeriodicLattice.Bond.source h)
      have hh : TorusMetric.torusProj (PeriodicLattice.torusSide L m)
            ((x + axisStep _ μ : LatticePoint _) : AmbientSpace) =
          TorusMetric.torusProj (PeriodicLattice.torusSide L m)
            ((y + axisStep _ κ : LatticePoint _) : AmbientSpace) :=
        congrArg Subtype.val (congrArg PeriodicLattice.Bond.target h)
      have ht' := (torusProj_eq_iff _ _ _).mp ht
      have hh' := (torusProj_eq_iff _ _ _).mp hh
      have hd := (latticeSubgroup (PeriodicLattice.torusSide L m)).sub_mem hh' ht'
      have hμ : μ = κ := by
        by_contra hne
        refine single_sub_single_not_mem ha haS hne ?_
        convert hd using 1
        funext ν
        simp only [Pi.sub_apply, AddSubgroup.coe_add, Pi.add_apply, axisStep]
        ring
      subst hμ
      refine ⟨y - x, by simpa using ht', ?_⟩
      exact Link.ext (by simp [translateLink, Link.forwardFrom])
        (by simp only [translateLink, Link.forwardFrom]; abel)
    · rintro ⟨v, hv, h⟩
      rw [h]
      exact (projectLink_translateLink L m K _ v hv).symm
  · intro U b v hv
    refine Subtype.ext ?_
    rw [liftCompactField_coe, liftCompactField_coe, projectLink_translateLink L m K b v hv]
theorem projectPoint_add (L m : ℕ) (j : ℤ) (x y : LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j (x + y) = projectPoint L m j x + projectPoint L m j y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_add <;> assumption
theorem projectLink_forwardFrom (L m : ℕ) (j : ℤ) (x : LatticePoint (PeriodicLattice.meshSize L j))
    (μ : Fin 4) :
    projectLink L m j (Link.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (projectPoint L m j x) μ := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectLink_forwardFrom <;> assumption
theorem torusProj_single (L m : ℕ) (μ : Fin 4) (t : ℝ) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L m) (Pi.single μ t) =
      PeriodicLattice.pointOnAxis L m μ t := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_single <;> assumption
theorem faceHolonomy_coe_eq {L m K : ℕ} (U : PeriodicLattice.CompactGaugeField L m (K : ℤ))
    (p : ElementaryPlaquette (CutoffLattice.spacingAt L K)) :
    ((faceHolonomy (liftCompactField U) p : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2) =
      PeriodicLattice.plaquetteHolonomy U.1 (projectFace L m K p) := by
  have hrev : ∀ b : PeriodicLattice.Bond L m (K : ℤ), U.1 b.opposite = (U.1 b)⁻¹ := fun b =>
    U.2.2 b (mem_univ _)
  simp only [faceHolonomy, PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, projectFace, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, Submonoid.coe_mul, specialUnitary_coe_inv,
    liftCompactField_coe, projectLink_forwardFrom, hrev, projectPoint_add, projectPoint_axisStep,
    mul_assoc]
theorem plaquettesCover (L m K : ℕ) : PlaquettesCover L m K := by
  intro p
  refine ⟨fun U => ⟨faceHolonomy_coe_eq U p, ?_⟩, ?_⟩
  · rw [InfiniteLattice.faceEnergy, PeriodicLattice.plaquetteCost, faceHolonomy_coe_eq U p]
  · simp only [ElementaryPlaquette.center, PeriodicLattice.Plaquette.barycenter, torusCover,
      torusProj_add, torusProj_single]
    rfl
section Corners
variable {a : ℝ}
theorem sub_corner_bounds (ha : 0 ≤ a) (p : ElementaryPlaquette a) {y : LatticePoint a}
    (hy : y ∈ NormalFamilies.plaquetteCorners p) (μ : Fin 4) :
    0 ≤ (y : AmbientSpace) μ - (p.corner : AmbientSpace) μ ∧
      (y : AmbientSpace) μ - (p.corner : AmbientSpace) μ ≤ a := by
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  simp only [NormalFamilies.plaquetteCorners, mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · simp [ha]
  · by_cases h : μ = p.lowAxis
    · subst h; simp [axisStep, ha]
    · simp [axisStep, Pi.single_eq_of_ne h, ha]
  · by_cases h : μ = p.lowAxis
    · subst h; simp [axisStep, Pi.single_eq_of_ne hne, ha]
    · by_cases h' : μ = p.highAxis
      · subst h'; simp [axisStep, Pi.single_eq_of_ne h, ha]
      · simp [axisStep, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h', ha]
  · by_cases h : μ = p.highAxis
    · subst h; simp [axisStep, ha]
    · simp [axisStep, Pi.single_eq_of_ne h, ha]
theorem abs_sub_le_of_mem_plaquetteCorners (ha : 0 ≤ a) (p : ElementaryPlaquette a)
    {y y' : LatticePoint a} (hy : y ∈ NormalFamilies.plaquetteCorners p)
    (hy' : y' ∈ NormalFamilies.plaquetteCorners p) (μ : Fin 4) :
    |(y : AmbientSpace) μ - (y' : AmbientSpace) μ| ≤ a := by
  obtain ⟨h1, h2⟩ := sub_corner_bounds ha p hy μ
  obtain ⟨h3, h4⟩ := sub_corner_bounds ha p hy' μ
  rw [abs_le]
  constructor <;> linarith
theorem endpoints_mem_plaquetteCorners (p : ElementaryPlaquette a) {b : Link a}
    (hb : b ∈ p.edges) :
    b.initial ∈ NormalFamilies.plaquetteCorners p ∧
      b.terminal ∈ NormalFamilies.plaquetteCorners p := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeGeometry.endpoints_mem_cornerSet <;> assumption
theorem exists_forwardFrom_mem_edges (x : LatticePoint a) (μ : Fin 4) :
    ∃ p : ElementaryPlaquette a, Link.forwardFrom x μ ∈ p.edges := by
  by_cases h : μ = 0
  · subst h
    exact ⟨⟨x, 0, 1, by decide⟩, by simp [ElementaryPlaquette.edges]⟩
  · exact ⟨⟨x, 0, μ, Fin.pos_of_ne_zero h⟩, by simp [ElementaryPlaquette.edges]⟩
end Corners
theorem supNormVec_le {v : AmbientSpace} {r : ℝ} (h : ∀ μ, |v μ| ≤ r) :
    TorusMetric.supNormVec v ≤ r :=
  Finset.sup'_le _ _ fun μ _ => h μ
theorem abs_apply_le_supNormVec (v : AmbientSpace) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.supNormVec v := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.abs_le_supNormVec <;> assumption
theorem windowCorners {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) :
    WindowCorners L K := by
  have ha : 0 ≤ CutoffLattice.spacingAt L K := (spacingAt_pos hL K).le
  refine ⟨fun p y hy y' hy' μ => abs_sub_le_of_mem_plaquetteCorners ha p hy hy' μ, ?_, ?_⟩
  · rintro p ⟨b, hb, hbW⟩ y hy
    have hb' := (Set.Finite.mem_toFinset _).mp hbW
    have htail : TorusMetric.supNormVec (b.initial : AmbientSpace) ≤ (K : ℝ) := hb'.2.1
    refine supNormVec_le fun μ => ?_
    have h1 := abs_sub_le_of_mem_plaquetteCorners ha p hy (endpoints_mem_plaquetteCorners p hb).1 μ
    have h2 := abs_apply_le_supNormVec (b.initial : AmbientSpace) μ
    have h3 : |(y : AmbientSpace) μ| ≤
        |(y : AmbientSpace) μ - (b.initial : AmbientSpace) μ| + |(b.initial : AmbientSpace) μ| := by
      simpa using abs_add_le ((y : AmbientSpace) μ - (b.initial : AmbientSpace) μ)
        ((b.initial : AmbientSpace) μ)
    linarith
  · intro b hb x hx
    have key : ∃ p ∈ (cutoffWindow L K).faces, b ∈ p.edges := by
      rcases hb with hb | hb
      · obtain ⟨μ, hμ⟩ := (cutoffWindow L K).isPositive b hb
        have hbf : b = Link.forwardFrom b.initial μ :=
          Link.ext rfl (by simp only [Link.forwardFrom]; rw [← hμ]; abel)
        obtain ⟨p, hp⟩ := exists_forwardFrom_mem_edges b.initial μ
        rw [← hbf] at hp
        exact ⟨p, ⟨b, hp, hb⟩, hp⟩
      · exact hb.1
    obtain ⟨p, hp, hbp⟩ := key
    refine ⟨p, hp, ?_⟩
    rcases hx with rfl | rfl
    · exact (endpoints_mem_plaquetteCorners p hbp).1
    · exact (endpoints_mem_plaquetteCorners p hbp).2
theorem coveringStatement_holds : CoveringStatement := fun s =>
  ⟨sitesCover s.isAdmissible s.m s.K,
    linksCover s.isAdmissible s.m s.K,
    plaquettesCover s.L s.m s.K,
    windowCorners s.isAdmissible s.K⟩
end YangMills.Construction.InfiniteLattice.LatticeCovering
