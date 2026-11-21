import YangMills.Construction.InfiniteLattice.MovesOfBondsSupportsAndPlaquettes
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionSeesNeitherCornerNorSense
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import YangMills.Construction.LawInAState.CovarianceBelowTheAveragesProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing
namespace SymmetryTransport
variable {a : ℝ}
section Values
variable {𝓢 : Set (Link a)} (h : HasNoOppositePairs 𝓢) (V : LinkVariables 𝓢)
  (U : GaugeField a)
theorem overwriteLinks_apply_of_mem {b : Link a} (hb : b ∈ 𝓢) :
    (overwriteLinks h V U).1 b = V ⟨b, hb⟩ :=
  dif_pos hb
theorem overwriteLinks_apply_of_opposite_mem {b : Link a} (hb : b ∉ 𝓢) (hr : b.opposite ∈ 𝓢) :
    (overwriteLinks h V U).1 b = (V ⟨b.opposite, hr⟩)⁻¹ :=
  (dif_neg hb).trans (dif_pos hr)
theorem overwriteLinks_apply_of_not_mem {b : Link a} (hb : b ∉ 𝓢) (hr : b.opposite ∉ 𝓢) :
    (overwriteLinks h V U).1 b = U b :=
  (dif_neg hb).trans (dif_neg hr)
end Values
section Moves
variable (r : LatticeSymmetry a) (hinj : Function.Injective r.linkMap)
  (hrev : ∀ b : Link a, r.linkMap b.opposite = (r.linkMap b).opposite)
include hinj
theorem transportFamily_apply {𝓢 : Set (Link a)} (V : LinkVariables 𝓢) (c : r.linkSetImage 𝓢)
    (b : 𝓢) (hc : c.1 = r.linkMap b.1) : r.transportFamily V c = V b := by
  have h : ∃ b', b' ∈ 𝓢 ∧ r.linkMap b' = c.1 := c.2
  change V ⟨h.choose, h.choose_spec.1⟩ = V b
  exact congrArg V (Subtype.ext (hinj (h.choose_spec.2.trans hc)))
theorem exists_transportFamily_eq {𝓢 : Set (Link a)} (W : LinkVariables (r.linkSetImage 𝓢)) :
    ∃ V : LinkVariables 𝓢, r.transportFamily V = W := by
  refine ⟨fun b => W ⟨r.linkMap b.1, mem_image_of_mem _ b.2⟩, ?_⟩
  funext c
  obtain ⟨c, b, hb, rfl⟩ := c
  exact transportFamily_apply r hinj _ _ ⟨b, hb⟩ rfl
include hrev
theorem hasNoOppositePairs_linkImage {𝓢 : Set (Link a)} (h : HasNoOppositePairs 𝓢) :
    HasNoOppositePairs (r.linkSetImage 𝓢) := by
  rintro _ ⟨b, hb, rfl⟩ ⟨b', hb', e⟩
  rw [← hrev] at e
  exact h b hb (hinj e ▸ hb')
theorem pullbackField_overwriteLinks {𝓢 : Set (Link a)} (h : HasNoOppositePairs 𝓢)
    (h' : HasNoOppositePairs (r.linkSetImage 𝓢)) (V : LinkVariables 𝓢)
    (U : GaugeField a) :
    r.pullbackField (overwriteLinks h' (r.transportFamily V) U) =
      overwriteLinks h V (r.pullbackField U) := by
  apply Subtype.ext
  funext b
  change (overwriteLinks h' (r.transportFamily V) U).1 (r.linkMap b) =
    (overwriteLinks h V (r.pullbackField U)).1 b
  by_cases hb : b ∈ 𝓢
  · have hc : r.linkMap b ∈ r.linkSetImage 𝓢 := mem_image_of_mem _ hb
    rw [overwriteLinks_apply_of_mem h' _ U hc, overwriteLinks_apply_of_mem h V _ hb]
    exact transportFamily_apply r hinj V _ ⟨b, hb⟩ rfl
  · have hnot : r.linkMap b ∉ r.linkSetImage 𝓢 := fun ⟨b', hb', e⟩ => hb (hinj e ▸ hb')
    by_cases hr : b.opposite ∈ 𝓢
    · have hc : (r.linkMap b).opposite ∈ r.linkSetImage 𝓢 := by
        rw [← hrev]
        exact mem_image_of_mem _ hr
      rw [overwriteLinks_apply_of_opposite_mem h' _ U hnot hc,
        overwriteLinks_apply_of_opposite_mem h V _ hb hr]
      exact congrArg _ (transportFamily_apply r hinj V _ ⟨b.opposite, hr⟩ (hrev b).symm)
    · have hcn : (r.linkMap b).opposite ∉ r.linkSetImage 𝓢 := by
        rw [← hrev]
        exact fun ⟨b', hb', e⟩ => hr (hinj e ▸ hb')
      rw [overwriteLinks_apply_of_not_mem h' _ U hnot hcn, overwriteLinks_apply_of_not_mem h V _ hb hr]
      rfl
theorem isIndependentOfLinks_iff (hsurj : Function.Surjective r.pullbackField)
    {𝓢 : Set (Link a)} (h : HasNoOppositePairs 𝓢)
    (h' : HasNoOppositePairs (r.linkSetImage 𝓢)) {E : Type*} (F : GaugeField a → E) :
    IsIndependentOfLinks h F ↔ IsIndependentOfLinks h' (r.actOn F) := by
  constructor
  · intro hF W U
    obtain ⟨V, rfl⟩ := exists_transportFamily_eq r hinj W
    change F (r.pullbackField _) = F (r.pullbackField U)
    rw [pullbackField_overwriteLinks r hinj hrev h h', hF]
  · intro hF V U
    obtain ⟨U', rfl⟩ := hsurj U
    rw [← pullbackField_overwriteLinks r hinj hrev h h' V U']
    exact hF (r.transportFamily V) U'
end Moves
theorem isIndependentOfLinks_congr {𝓢 𝓣 : Set (Link a)} (e : 𝓢 = 𝓣)
    (h₁ : HasNoOppositePairs 𝓢) (h₂ : HasNoOppositePairs 𝓣)
    {E : Type*} (F : GaugeField a → E) :
    IsIndependentOfLinks h₁ F ↔ IsIndependentOfLinks h₂ F := by
  subst e
  rfl
theorem dependsOnLink_iff (ha : 0 < a) (r : LatticeSymmetry a) (hinj : Function.Injective r.linkMap)
    (hrev : ∀ b : Link a, r.linkMap b.opposite = (r.linkMap b).opposite)
    (hsurj : Function.Surjective r.pullbackField) {E : Type*} (F : GaugeField a → E)
    (b : Link a) : DependsOnLink ha F b ↔ DependsOnLink ha (r.actOn F) (r.linkMap b) := by
  have hs : r.linkSetImage ({b} : Set (Link a)) = {r.linkMap b} := image_singleton
  exact not_congr ((isIndependentOfLinks_iff r hinj hrev hsurj (hasNoOppositePairs_singleton ha b)
    (hasNoOppositePairs_linkImage r hinj hrev (hasNoOppositePairs_singleton ha b)) F).trans
      (isIndependentOfLinks_congr hs _ _ _))
theorem shift_linkMap_forwardFrom (v x : LatticePoint a) (κ : Fin 4) :
    (shift v).linkMap (Link.forwardFrom x κ) = Link.forwardFrom (x + v) κ := by apply _root_.YangMills.SharedProofs.p433 <;> assumption
theorem shift_linkImage_positiveLinks (v : LatticePoint a) :
    (shift v).linkSetImage (positiveLinkSet a) = positiveLinkSet a := by
  ext b
  constructor
  · rintro ⟨_, ⟨x, κ, rfl⟩, rfl⟩
    exact ⟨x + v, κ, shift_linkMap_forwardFrom v x κ⟩
  · rintro ⟨x, κ, rfl⟩
    refine ⟨Link.forwardFrom (x - v) κ, ⟨x - v, κ, rfl⟩, ?_⟩
    rw [shift_linkMap_forwardFrom, sub_add_cancel]
def JoinsCorners (p : ElementaryPlaquette a) (b : Link a) : Prop :=
  b.initial ∈ p.cornerSet ∧ b.terminal ∈ p.cornerSet
theorem mem_plaquettesTouching_iff (𝓛 : Finset (Link a)) (p : ElementaryPlaquette a) :
    p ∈ plaquettesTouching 𝓛 ↔ ∃ b, JoinsCorners p b ∧ (b ∈ 𝓛 ∨ b.opposite ∈ 𝓛) := by
  constructor
  · rintro ⟨b, ⟨-, h1, h2⟩, hb⟩
    exact ⟨b, ⟨h1, h2⟩, hb⟩
  · rintro ⟨b, ⟨h1, h2⟩, hb⟩
    rcases mem_positiveLinks_or_opposite_mem b with hp | hp
    · exact ⟨b, ⟨hp, h1, h2⟩, hb⟩
    · exact ⟨b.opposite, ⟨hp, h2, h1⟩, hb.symm⟩
theorem joinsCorners_linkMap (r : LatticeSymmetry a) (hs : Function.Injective r.pointMap)
    {p : ElementaryPlaquette a} (hcorn : (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet)
    (b : Link a) :
    JoinsCorners (r.plaquetteMap p) (r.linkMap b) ↔ JoinsCorners p b := by
  unfold JoinsCorners
  rw [hcorn]
  exact and_congr hs.mem_set_image hs.mem_set_image
theorem plaquettesTouching_linkImage (r : LatticeSymmetry a)
    (hbij : Function.Bijective r.linkMap)
    (hrev : ∀ b : Link a, r.linkMap b.opposite = (r.linkMap b).opposite)
    (hs : Function.Injective r.pointMap) (hpb : Function.Bijective r.plaquetteMap)
    (hcorn : ∀ p : ElementaryPlaquette a, (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet)
    (𝓛 𝓛' : Finset (Link a)) (hL : (𝓛' : Set (Link a)) = r.linkSetImage (𝓛 : Set (Link a))) :
    plaquettesTouching 𝓛' = r.plaquetteMap '' plaquettesTouching 𝓛 := by
  have hmem : ∀ b, r.linkMap b ∈ 𝓛' ↔ b ∈ 𝓛 := by
    intro b
    have h : r.linkMap b ∈ (𝓛' : Set (Link a)) ↔ b ∈ (𝓛 : Set (Link a)) := by
      rw [hL]
      exact hbij.1.mem_set_image
    simpa using h
  have key : ∀ p, r.plaquetteMap p ∈ plaquettesTouching 𝓛' ↔ p ∈ plaquettesTouching 𝓛 := by
    intro p
    rw [mem_plaquettesTouching_iff, mem_plaquettesTouching_iff]
    constructor
    · rintro ⟨c, hc, hcL⟩
      obtain ⟨b, rfl⟩ := hbij.2 c
      refine ⟨b, (joinsCorners_linkMap r hs (hcorn p) b).mp hc, ?_⟩
      rw [← hrev, hmem, hmem] at hcL
      exact hcL
    · rintro ⟨b, hb, hbL⟩
      refine ⟨r.linkMap b, (joinsCorners_linkMap r hs (hcorn p) b).mpr hb, ?_⟩
      rw [← hrev, hmem, hmem]
      exact hbL
  ext q
  constructor
  · intro hq
    obtain ⟨p, rfl⟩ := hpb.2 q
    exact ⟨p, (key p).mp hq, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact (key p).mpr hp
def cycleImage (r : LatticeSymmetry a) {p : ElementaryPlaquette a}
    (hcorn : (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) (c : BoundaryCycle p) :
    BoundaryCycle (r.plaquetteMap p) where
  v₁ := r.pointMap c.v₁
  v₂ := r.pointMap c.v₂
  v₃ := r.pointMap c.v₃
  v₄ := r.pointMap c.v₄
  corners_eq := by
    rw [hcorn, ← c.corners_eq]
    simp only [image_insert_eq, image_singleton]
  adj₁₂ := (r.linkMap ⟨c.v₁, c.v₂, c.adj₁₂⟩).isAdjacent
  adj₂₃ := (r.linkMap ⟨c.v₂, c.v₃, c.adj₂₃⟩).isAdjacent
  adj₃₄ := (r.linkMap ⟨c.v₃, c.v₄, c.adj₃₄⟩).isAdjacent
  adj₄₁ := (r.linkMap ⟨c.v₄, c.v₁, c.adj₄₁⟩).isAdjacent
theorem holonomy_cycleImage (r : LatticeSymmetry a) {p : ElementaryPlaquette a}
    (hcorn : (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) (c : BoundaryCycle p)
    (U : GaugeField a) :
    (cycleImage r hcorn c).holonomy U = c.holonomy (r.pullbackField U) := rfl
theorem faceEnergy_pullbackField
    (hP : ∀ (p : ElementaryPlaquette a) (U : GaugeField a), FaceEnergyDeterminedByCorners p U)
    (r : LatticeSymmetry a) {p : ElementaryPlaquette a}
    (hcorn : (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) (U : GaugeField a) :
    faceEnergy (r.pullbackField U) p = faceEnergy U (r.plaquetteMap p) := by
  obtain ⟨-, -, ⟨c, hc⟩, -⟩ := hP p (r.pullbackField U)
  obtain ⟨hall, -, ⟨c', hc'⟩, -⟩ := hP (r.plaquetteMap p) U
  have h := hall (cycleImage r hcorn c) c'
  rw [holonomy_cycleImage] at h
  unfold faceEnergy
  rw [← hc, ← hc', h]
theorem finsum_mem_cornerSet (ha : 0 < a) (p : ElementaryPlaquette a) {M : Type*}
    [AddCommMonoid M] (f : LatticePoint a → M) :
    ∑ᶠ x ∈ p.cornerSet, f x = f p.corner + (f (p.corner + axisStep a p.lowAxis) +
      (f (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis) +
        f (p.corner + axisStep a p.highAxis))) := by
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  have hcoord : ∀ {x y : LatticePoint a} (μ : Fin 4), (x : AmbientSpace) μ ≠ (y : AmbientSpace) μ →
      x ≠ y :=
    fun μ h e => h (by rw [e])
  have hs : ∀ (x : LatticePoint a) (μ ν : Fin 4),
      ((x + axisStep a μ : LatticePoint a) : AmbientSpace) ν =
        (x : AmbientSpace) ν + (Pi.single μ a : AmbientSpace) ν :=
    fun _ _ _ => rfl
  have h12 : p.corner ∉ ({p.corner + axisStep a p.lowAxis,
      p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
      p.corner + axisStep a p.highAxis} : Set (LatticePoint a)) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨hcoord p.lowAxis ?_, hcoord p.lowAxis ?_, hcoord p.highAxis ?_⟩
    · simp [hs, ha.ne']
    · simp [hs, hne.symm, ha.ne']
    · simp [hs, ha.ne']
  have h23 : p.corner + axisStep a p.lowAxis ∉
      ({p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
        p.corner + axisStep a p.highAxis} : Set (LatticePoint a)) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨hcoord p.highAxis ?_, hcoord p.lowAxis ?_⟩
    · simp [hs, ha.ne']
    · simp [hs, ha.ne', Pi.single_eq_of_ne hne]
  have h34 : p.corner + axisStep a p.lowAxis + axisStep a p.highAxis ∉
      ({p.corner + axisStep a p.highAxis} : Set (LatticePoint a)) := by
    simp only [mem_singleton_iff]
    refine hcoord p.lowAxis ?_
    simp [hs, ha.ne', Pi.single_eq_of_ne hne]
  unfold ElementaryPlaquette.cornerSet
  rw [finsum_mem_insert _ h12 (by simp), finsum_mem_insert _ h23 (by simp),
    finsum_mem_insert _ h34 (by simp), finsum_mem_singleton]
theorem sum_corners_eq_four_smul_center (p : ElementaryPlaquette a) :
    (p.corner : AmbientSpace) + (((p.corner + axisStep a p.lowAxis : LatticePoint a) : AmbientSpace) +
      (((p.corner + axisStep a p.lowAxis + axisStep a p.highAxis : LatticePoint a) : AmbientSpace) +
        ((p.corner + axisStep a p.highAxis : LatticePoint a) : AmbientSpace))) =
      (4 : ℝ) • p.center := by
  funext μ
  change (p.corner : AmbientSpace) μ + (((p.corner : AmbientSpace) μ +
      (Pi.single p.lowAxis a : AmbientSpace) μ) +
      (((p.corner : AmbientSpace) μ + (Pi.single p.lowAxis a : AmbientSpace) μ +
        (Pi.single p.highAxis a : AmbientSpace) μ) +
        ((p.corner : AmbientSpace) μ + (Pi.single p.highAxis a : AmbientSpace) μ))) =
    4 * ((p.corner : AmbientSpace) μ + (Pi.single p.lowAxis (a / 2) : AmbientSpace) μ +
      (Pi.single p.highAxis (a / 2) : AmbientSpace) μ)
  simp only [Pi.single_apply]
  split_ifs <;> ring
theorem center_plaquetteMap (ha : 0 < a) (r : LatticeSymmetry a)
    (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) (v : LatticePoint a) (hr : r.toFun = latticeMotion w v)
    (hs : Function.Injective r.pointMap) {p : ElementaryPlaquette a}
    (hcorn : (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) :
    (r.plaquetteMap p).center = r.toFun p.center := by
  have hmap : ∀ x : LatticePoint a, ((r.pointMap x : LatticePoint a) : AmbientSpace) = w x + v :=
    fun x => congrFun hr x
  have h1 := finsum_mem_cornerSet ha (r.plaquetteMap p) (fun x : LatticePoint a => (x : AmbientSpace))
  rw [hcorn, finsum_mem_image hs.injOn, finsum_mem_cornerSet ha p] at h1
  simp only [hmap] at h1
  have h2 := sum_corners_eq_four_smul_center (r.plaquetteMap p)
  have h3 := congrArg w (sum_corners_eq_four_smul_center p)
  rw [map_add, map_add, map_add, map_smul] at h3
  rw [hr]
  change (r.plaquetteMap p).center = w p.center + v
  have h4 : (4 : ℝ) • (r.plaquetteMap p).center = (4 : ℝ) • (w p.center + v) := by
    rw [← h2, ← h1, smul_add, ← h3]
    module
  exact smul_right_injective AmbientSpace (four_ne_zero : (4 : ℝ) ≠ 0) h4
end SymmetryTransport
open SymmetryTransport in
theorem symmetriesTransportLinksSupportsAndPlaquettes_holds
    (hSpace : InfiniteLattice.FieldSpace.SymmetryProperties)
    (hPlaq : FaceEnergyIndependentOfBasepointAndOrientation) :
    SymmetriesTransportLinksSupportsAndPlaquettes := by
  intro a ha
  obtain ⟨-, hAct, -, -, hForm, ⟨G, hG⟩, -, -, hBond, -, -, hCorners, hPl⟩ := hSpace a ha
  have hP := (hPlaq.2 a ha).1
  have hSite : ∀ r : LatticeSymmetry a, Function.Injective r.pointMap := fun r x y h => by
    obtain ⟨g, -, hg⟩ := (hG r.toFun).mp ⟨r, rfl⟩
    have h' : r.toFun x = r.toFun y := congrArg Subtype.val h
    rw [← hg] at h'
    exact Subtype.ext (g.injective h')
  refine ⟨?_, ?_, ?_⟩
  · unfold SymmetriesAreLatticeMotions
    exact ⟨Set.ext hForm, G, hG⟩
  · unfold SymmetriesTransportLinksAndSupports
    have hReads : ∀ (r : LatticeSymmetry a) (E : Type) (F : GaugeField a → E) (b : Link a),
        DependsOnLink ha F b ↔ DependsOnLink ha (r.actOn F) (r.linkMap b) :=
      fun r E F b => dependsOnLink_iff ha r (hBond r).1.1 (hBond r).2
        (hAct r r).1.bijective.2 F b
    refine ⟨fun r => ⟨(hBond r).1, (hBond r).2, fun 𝓢 h => ?_, hReads r⟩, fun v => ?_⟩
    · have h' := hasNoOppositePairs_linkImage r (hBond r).1.1 (hBond r).2 h
      exact ⟨h', fun V b => transportFamily_apply r (hBond r).1.1 V _ b rfl,
        fun V U => pullbackField_overwriteLinks r (hBond r).1.1 (hBond r).2 h h' V U,
        fun E F => isIndependentOfLinks_iff r (hBond r).1.1 (hBond r).2
          (hAct r r).1.bijective.2 h h' F⟩
    · have hB := shift_linkImage_positiveLinks v
      refine ⟨hB, fun E F => ?_⟩
      ext b
      constructor
      · rintro ⟨hb, hr⟩
        rw [← hB] at hb
        obtain ⟨c, hc, rfl⟩ := hb
        exact ⟨c, ⟨hc, (hReads _ E F c).mpr hr⟩, rfl⟩
      · rintro ⟨c, ⟨hc, hr⟩, rfl⟩
        refine ⟨?_, (hReads _ E F c).mp hr⟩
        rw [← hB]
        exact mem_image_of_mem _ hc
  · unfold SymmetriesTransportPlaquettes
    intro r
    have hcorn := (hPl r).1
    have hr : r.toFun ∈ affineHyperoctahedralMaps a := (hForm _).mp ⟨r, rfl⟩
    obtain ⟨w, -, v, hwv⟩ := hr
    refine ⟨fun p => ⟨⟨r.plaquetteMap p, hcorn p, fun q hq => hCorners (hq.trans (hcorn p).symm)⟩,
      hcorn p⟩, (hPl r).2, fun r' p => ?_, fun p => ?_, fun p => ?_, fun 𝓛 𝓛' _ hL => ?_⟩
    · refine hCorners ?_
      rw [(hPl (r.comp r')).1, (hPl r).1, (hPl r').1, image_image]
      rfl
    · funext U
      exact faceEnergy_pullbackField hP r (hcorn p) U
    · exact center_plaquetteMap ha r w v hwv (hSite r) (hcorn p)
    · exact plaquettesTouching_linkImage r (hBond r).1 (hBond r).2 (hSite r) (hPl r).2 hcorn
        𝓛 𝓛' hL
end YangMills.Construction.GibbsAtFixedSpacing
