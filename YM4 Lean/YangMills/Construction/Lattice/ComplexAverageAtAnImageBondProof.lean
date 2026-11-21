import YangMills.Construction.Averaging.MeanInTheComplexGroup
import YangMills.Construction.Geometry.TorusArcs
import YangMills.Construction.Lattice.AveragesAndWeightsProof
import YangMills.Construction.Lattice.AxialPathReversal
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import Mathlib
import YangMills.Construction.Lattice.IsometryCarriesTheObjectsOfTheAverage
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import YangMills.Construction.Matrices.LogSeriesConjugateInverse
import YangMills.Construction.Matrices.OperatorNormUnderConjugation
import YangMills.Construction.Towers.WilsonActionIsRealAnalyticOnTheConfigurationsProof
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
structure ComplexAverageRelation (σ : FourTorus L m ≃ FourTorus L m) {K k : ℕ}
    (U : BondAtLevel L m K k → Matrices.ComplexMatrix2) (c c' : BondAtLevel L m K (k + 1)) : Prop where
  mem_domain_iff : c' = bondImage σ c →
    (transportGaugeField σ U ∈
        (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) ↔
      U ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)))
  mem_domain_iff_of_compact : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) U →
    (transportGaugeField σ U ∈
        (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) ↔
      U ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)))
  average_image : c' = bondImage σ c →
    U ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) →
      complexBlockAverage (transportGaugeField σ U) c' = complexBlockAverage U c
  average_opposite : c' = (bondImage σ c).opposite →
    U ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) →
    transportGaugeField σ U ∈
        (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) →
      complexBlockAverage (transportGaugeField σ U) c' = (complexBlockAverage U c)⁻¹
def ComplexAverageEquivariance : Prop :=
  ∀ (L m K k : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → k < K → i ≤ levelDepth K (k + 1) →
    ∀ (U : BondAtLevel L m K k → Matrices.ComplexMatrix2) (c c' : BondAtLevel L m K (k + 1)),
      c.IsPositivelyOriented → c'.IsPositivelyOriented →
      (c' = bondImage σ c ∨ c' = (bondImage σ c).opposite) →
      IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) U → ComplexAverageRelation σ U c c'
end PeriodicLattice
end YangMills.Construction
end
end

open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ImageBondEquivariance
variable {L m : ℕ} {j j' : ℤ}
theorem isUnit_of_det_eq_one {A : Matrices.ComplexMatrix2} (h : A.det = 1) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).2 (by rw [h]; exact isUnit_one)
theorem inv_inv_of_det_eq_one {A : Matrices.ComplexMatrix2} (h : A.det = 1) : A⁻¹⁻¹ = A :=
  Matrix.nonsing_inv_nonsing_inv A (by rw [h]; exact isUnit_one)
theorem inv_mul_of_det_eq_one {A : Matrices.ComplexMatrix2} (h : A.det = 1) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A (by rw [h]; exact isUnit_one)
theorem mul_inv_of_det_eq_one {A : Matrices.ComplexMatrix2} (h : A.det = 1) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A (by rw [h]; exact isUnit_one)
theorem det_inv_of_det_eq_one {A : Matrices.ComplexMatrix2} (h : A.det = 1) : A⁻¹.det = 1 := by
  rw [Matrix.det_nonsing_inv, h, Ring.inverse_one]
theorem conj_inv_four_factors {A B C T : Matrices.ComplexMatrix2} (hC : C.det = 1)
    (hT : T.det = 1) :
    C * B⁻¹ * A⁻¹ * T⁻¹⁻¹ = T⁻¹ * (A * B * C⁻¹ * T⁻¹)⁻¹ * T⁻¹⁻¹ := by
  simp only [Matrix.mul_inv_rev, inv_inv_of_det_eq_one hC, inv_inv_of_det_eq_one hT]
  rw [← mul_assoc T⁻¹, inv_mul_of_det_eq_one hT, one_mul]
  simp only [mul_assoc]
def negConjEquiv (S : Matrices.ComplexMatrix2) (hS : S.det = 1) :
    Matrices.ComplexMatrix2 ≃ₗ[ℂ] Matrices.ComplexMatrix2 where
  toFun Z := -(S * Z * S⁻¹)
  invFun Z := -(S⁻¹ * Z * S)
  map_add' X Z := by simp only [mul_add, add_mul, neg_add]
  map_smul' r X := by simp
  left_inv Z := by
    have h1 := inv_mul_of_det_eq_one hS
    simp only [mul_neg, neg_mul, neg_neg]
    calc S⁻¹ * (S * Z * S⁻¹) * S = (S⁻¹ * S) * Z * (S⁻¹ * S) := by simp only [mul_assoc]
      _ = Z := by rw [h1, one_mul, mul_one]
  right_inv Z := by
    have h1 := mul_inv_of_det_eq_one hS
    simp only [mul_neg, neg_mul, neg_neg]
    calc S * (S⁻¹ * Z * S) * S⁻¹ = (S * S⁻¹) * Z * (S * S⁻¹) := by simp only [mul_assoc]
      _ = Z := by rw [h1, one_mul, mul_one]
theorem negConjEquiv_apply (S : Matrices.ComplexMatrix2) (hS : S.det = 1)
    (Z : Matrices.ComplexMatrix2) :
    negConjEquiv S hS Z = -(S * Z * S⁻¹) := rfl
theorem matExp_negConjEquiv_mul (h3 : Matrices.ComplexMatrix2.OperatorNormUnderConjugation)
    (X : Matrices.ComplexMatrix2) {T : Matrices.ComplexMatrix2} (hT : T.det = 1) :
    Matrices.ComplexMatrix2.matExp (negConjEquiv T⁻¹ (det_inv_of_det_eq_one hT) X) * T⁻¹ =
      (Matrices.ComplexMatrix2.matExp X * T)⁻¹ := by
  obtain ⟨-, -, -, -, hexp, -, -⟩ := h3
  have hS := det_inv_of_det_eq_one hT
  rw [negConjEquiv_apply, Matrices.ComplexMatrix2.matExp, Matrix.exp_neg,
    ← Matrices.ComplexMatrix2.matExp, ← hexp _ _ (isUnit_of_det_eq_one hS)]
  simp only [Matrix.mul_inv_rev, inv_inv_of_det_eq_one hT]
  rw [mul_assoc, mul_assoc _ T, mul_inv_of_det_eq_one hT, mul_one]
theorem linearEquiv_map_finsum_mem {α : Type*}
    (φ : Matrices.ComplexMatrix2 ≃ₗ[ℂ] Matrices.ComplexMatrix2) (f : α → Matrices.ComplexMatrix2)
    (s : Set α) :
    φ (∑ᶠ x ∈ s, f x) = ∑ᶠ x ∈ s, φ (f x) :=
  calc φ (∑ᶠ x ∈ s, f x) = φ.toAddEquiv (∑ᶠ x, ∑ᶠ (_ : x ∈ s), f x) := rfl
    _ = ∑ᶠ x, φ.toAddEquiv (∑ᶠ (_ : x ∈ s), f x) := AddEquiv.map_finsum _ _
    _ = ∑ᶠ x ∈ s, φ (f x) := finsum_congr fun _ => AddEquiv.map_finsum _ _
theorem mem_unitaryGroup_of_mem_specialUnitary {A : Matrices.ComplexMatrix2}
    (h : A ∈ Matrices.ComplexMatrix2.specialUnitary) : A ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp h).1
theorem inv_mem_specialUnitary {A : Matrices.ComplexMatrix2}
    (h : A ∈ Matrices.ComplexMatrix2.specialUnitary) :
    A⁻¹ ∈ Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem operatorNorm_conj_inv_sub_one_lt
    (h3 : Matrices.ComplexMatrix2.OperatorNormUnderConjugation)
    {W S : Matrices.ComplexMatrix2} (hW : W ∈ Matrices.ComplexMatrix2.specialUnitary)
    (hS : S ∈ Matrices.ComplexMatrix2.specialUnitary)
    (h : Matrices.ComplexMatrix2.operatorNorm (W - 1) < 1) :
    Matrices.ComplexMatrix2.operatorNorm (S * W⁻¹ * S⁻¹ - 1) < 1 := by
  obtain ⟨-, -, hinv, -, -, -, hconj⟩ := h3
  exact hconj S W⁻¹ (mem_unitaryGroup_of_mem_specialUnitary hS)
    (by rw [hinv W (mem_unitaryGroup_of_mem_specialUnitary hW)]; exact h)
theorem isLogMean_reindex_iff {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    {V : κ → Matrices.ComplexMatrix2} {V₀ : ι → Matrices.ComplexMatrix2}
    (hV : ∀ s, V (e s) = V₀ s) (W : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.IsLogMean complexGaugeGroup V W ↔
      Matrices.ComplexMatrix2.IsLogMean complexGaugeGroup V₀ W := by
  unfold Matrices.ComplexMatrix2.IsLogMean
  refine and_congr_right fun _ => and_congr ?_ ?_
  · constructor
    · intro h s
      rw [← hV]
      exact h _
    · intro h k
      obtain ⟨s, rfl⟩ := e.surjective k
      rw [hV]
      exact h s
  · rw [← e.sum_comp]
    simp only [hV]
theorem complexLogMean_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    {V : κ → Matrices.ComplexMatrix2} {V₀ : ι → Matrices.ComplexMatrix2}
    (hV : ∀ s, V (e s) = V₀ s) : complexLogMean V = complexLogMean V₀ := by
  unfold complexLogMean
  refine congrArg Classical.epsilon (funext fun W => propext ?_)
  rw [isLogMean_reindex_iff e hV]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨k, h⟩
    obtain ⟨s, rfl⟩ := e.surjective k
    exact ⟨s, by rwa [hV] at h⟩
  · rintro ⟨s, h⟩
    exact ⟨e s, by rwa [hV]⟩
theorem familyDiameter_reindex {ι κ : Type*} (e : ι ≃ κ) {V : κ → Matrices.ComplexMatrix2}
    {V₀ : ι → Matrices.ComplexMatrix2} (hV : ∀ s, V (e s) = V₀ s) :
    Matrices.ComplexMatrix2.familyDiameter V = Matrices.ComplexMatrix2.familyDiameter V₀ := by
  have h : V₀ = V ∘ e := funext fun s => (hV s).symm
  subst h
  exact ((e.prodCongr e).iSup_comp
    (g := fun p : κ × κ =>
      Matrices.ComplexMatrix2.operatorNorm (V p.1 * (V p.2)⁻¹ - 1))).symm
theorem det_complexLogMean (hM : Averaging.ComplexLogMeanOfSmallFamilies) {ι : Type} [Fintype ι]
    [Nonempty ι] {V : ι → Matrices.ComplexMatrix2} (hV : ∀ i, V i ∈ complexGaugeGroup)
    (hd : Matrices.ComplexMatrix2.familyDiameter V < Averaging.centreOfMassDiameter) :
    (complexLogMean V).det = 1 := by
  obtain ⟨-, -, -, hMF, -⟩ := hM
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hdiam := familyDiameter_reindex e (V := V) (V₀ := V ∘ e) fun _ => rfl
  have hmean := complexLogMean_reindex e (V := V) (V₀ := V ∘ e) fun _ => rfl
  have hs : V ∘ e ∈ Averaging.smallComplexFamilies (Fintype.card ι) :=
    ⟨fun i => hV (e i), by rwa [← hdiam]⟩
  have hspec : Averaging.IsNearComplexLogMean (V ∘ e) (complexLogMean (V ∘ e)) :=
    Classical.epsilon_spec (p := fun W =>
      Matrices.ComplexMatrix2.IsLogMean complexGaugeGroup (V ∘ e) W ∧
        ∃ i, Matrices.ComplexMatrix2.operatorNorm ((V ∘ e) i * W⁻¹ - 1) ≤ complexMeanTolerance)
      ((hMF _ Fintype.card_pos).existsUnique _ hs).exists
  rw [hmean]
  exact hspec.1.1
theorem det_pathHolonomy {U : Bond L m j → Matrices.ComplexMatrix2} {Γ : List (Bond L m j)}
    (h : ∀ b ∈ Γ, U b ∈ complexGaugeGroup) : (pathHolonomy U Γ).det = 1 := by
  induction Γ with
  | nil => simp [pathHolonomy]
  | cons b Γ ih =>
    have e : pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := by simp [pathHolonomy]
    have hb : (U b).det = 1 := h b List.mem_cons_self
    rw [e, Matrix.det_mul, ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb'), hb, one_mul]
theorem pathHolonomy_mem_specialUnitary {U : Bond L m j → Matrices.ComplexMatrix2}
    {Γ : List (Bond L m j)} (h : ∀ b ∈ Γ, U b ∈ compactGaugeGroup) :
    pathHolonomy U Γ ∈ Matrices.ComplexMatrix2.specialUnitary := by
  unfold pathHolonomy
  apply Submonoid.list_prod_mem
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact h b hb
structure IsometryTransport (σ : FourTorus L m ≃ FourTorus L m) (j j' : ℤ) : Prop where
  bondImage_source : ∀ b : Bond L m j, ((bondImage σ b).source : FourTorus L m) = σ b.source
  bondImage_target : ∀ b : Bond L m j, ((bondImage σ b).target : FourTorus L m) = σ b.target
  bondImage_source_eq : ∀ b : Bond L m j, (bondImage σ b).source = sitePreimage σ.symm b.source
  bondImage_target_eq : ∀ b : Bond L m j, (bondImage σ b).target = sitePreimage σ.symm b.target
  coe_sitePreimage : ∀ x : Site L m j',
    ((sitePreimage σ.symm x : Site L m j') : FourTorus L m) = σ x
  bondPreimage_source : ∀ b : Bond L m j',
    ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source
  bondPreimage_target : ∀ b : Bond L m j',
    ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target
  transportGaugeField_bondImage : ∀ (V : Bond L m j' → Matrices.ComplexMatrix2) (b : Bond L m j'),
    transportGaugeField σ V (bondImage σ b) = V b
  mapsBlockSites : ∀ y : Site L m j, IsometryImages.MapsBlockSites σ j' y
  mapsContourIndices : ∀ (y : Site L m j) (x : Site L m j'), x ∈ sitesInBlock j' y →
    IsometryImages.MapsContourIndices σ y x
  mapsCrossing : ∀ (c : Bond L m j) (x : Site L m j'), IsometryImages.MapsCrossing σ c x
  mapsTransportPath : ∀ c : Bond L m j, IsometryImages.MapsTransportPath σ j' c
section
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem bondImage_opposite (h : IsometryTransport σ j j') (c : Bond L m j) :
    bondImage σ c.opposite = (bondImage σ c).opposite :=
  Bond.ext (Subtype.ext ((h.bondImage_source c.opposite).trans (h.bondImage_target c).symm))
    (Subtype.ext ((h.bondImage_target c.opposite).trans (h.bondImage_source c).symm))
theorem pathHolonomy_pathImage (h : IsometryTransport σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) (Γ : List (Bond L m j')) :
    pathHolonomy (transportGaugeField σ V) (pathImage σ Γ) = pathHolonomy V Γ := by
  simp only [pathHolonomy, pathImage, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => h.transportGaugeField_bondImage V b
theorem parallelTransport_bondImage (h : IsometryTransport σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) :
    parallelTransport (transportGaugeField σ V) (bondImage σ c) = parallelTransport V c :=
  (congrArg (pathHolonomy (transportGaugeField σ V)) (h.mapsTransportPath c)).symm.trans
    (pathHolonomy_pathImage h V _)
theorem crossingHolonomy_bondImage (h : IsometryTransport σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) (x : Site L m j') :
    pathHolonomy (transportGaugeField σ V)
        (crossingPath (bondImage σ c) (sitePreimage σ.symm x)) =
      pathHolonomy V (crossingPath c x) :=
  (congrArg (pathHolonomy (transportGaugeField σ V)) (h.mapsCrossing c x).2).symm.trans
    (pathHolonomy_pathImage h V _)
theorem exists_axisOrdering_equiv (h : IsometryTransport σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) {y y' : Site L m j} {x x' : Site L m j'}
    (hy : y' = sitePreimage σ.symm y) (hx : x' = sitePreimage σ.symm x)
    (hxy : x ∈ sitesInBlock j' y) :
    ∃ e : AxisOrdering y x ≃ AxisOrdering y' x',
      ∀ s, contourHolonomies (transportGaugeField σ V) y' x' (e s) =
        contourHolonomies V y x s := by
  subst hy hx
  obtain ⟨e, he⟩ := h.mapsContourIndices y x hxy
  refine ⟨e, fun s => ?_⟩
  simp only [contourHolonomies]
  rw [he]
  exact pathHolonomy_pathImage h V _
theorem complexMeanContourHolonomy_image (h : IsometryTransport σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) {y y' : Site L m j} {x x' : Site L m j'}
    (hy : y' = sitePreimage σ.symm y) (hx : x' = sitePreimage σ.symm x)
    (hxy : x ∈ sitesInBlock j' y) :
    complexMeanContourHolonomy (transportGaugeField σ V) y' x' =
      complexMeanContourHolonomy V y x := by
  obtain ⟨e, he⟩ := exists_axisOrdering_equiv h V hy hx hxy
  exact complexLogMean_reindex e he
theorem familyDiameter_contourHolonomies_image (h : IsometryTransport σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) {y y' : Site L m j} {x x' : Site L m j'}
    (hy : y' = sitePreimage σ.symm y) (hx : x' = sitePreimage σ.symm x)
    (hxy : x ∈ sitesInBlock j' y) :
    Matrices.ComplexMatrix2.familyDiameter (contourHolonomies (transportGaugeField σ V) y' x') =
      Matrices.ComplexMatrix2.familyDiameter (contourHolonomies V y x) := by
  obtain ⟨e, he⟩ := exists_axisOrdering_equiv h V hy hx hxy
  exact familyDiameter_reindex e he
theorem forall_sitesInBlock_image_iff (h : IsometryTransport σ j j') {y y' : Site L m j}
    (hy : y' = sitePreimage σ.symm y) {P' P : Site L m j' → Prop}
    (hP : ∀ x ∈ sitesInBlock j' y, (P' (sitePreimage σ.symm x) ↔ P x)) :
    (∀ x ∈ sitesInBlock j' y', P' x) ↔ ∀ x ∈ sitesInBlock j' y, P x := by
  subst hy
  have hb := h.mapsBlockSites y
  constructor
  · intro H x hx
    exact (hP x hx).1 (H _ (hb.mapsTo hx))
  · intro H x' hx'
    obtain ⟨x, hx, rfl⟩ := hb.surjOn hx'
    exact (hP x hx).2 (H x hx)
theorem bijOn_sitesInBlock_source (h : IsometryTransport σ j j') (c : Bond L m j) :
    BijOn (sitePreimage σ.symm) (sitesInBlock j' c.source)
      (sitesInBlock j' (bondImage σ c).source) := by
  rw [h.bondImage_source_eq c]
  exact h.mapsBlockSites c.source
theorem symm_mem_bondDoubleBlock (h : IsometryTransport σ j j') {c : Bond L m j}
    {s : Site L m j'} (hs : (s : FourTorus L m) ∈ bondDoubleBlock (bondImage σ c)) :
    σ.symm s ∈ bondDoubleBlock c := by
  rcases hs with hs | hs
  · have hs' : s ∈ sitesInBlock j' (sitePreimage σ.symm c.source) := by
      rw [← h.bondImage_source_eq]
      exact hs
    obtain ⟨x, hx, rfl⟩ := (h.mapsBlockSites c.source).surjOn hs'
    rw [h.coe_sitePreimage, σ.symm_apply_apply]
    exact Or.inl hx
  · have hs' : s ∈ sitesInBlock j' (sitePreimage σ.symm c.target) := by
      rw [← h.bondImage_target_eq]
      exact hs
    obtain ⟨x, hx, rfl⟩ := (h.mapsBlockSites c.target).surjOn hs'
    rw [h.coe_sitePreimage, σ.symm_apply_apply]
    exact Or.inr hx
theorem bondPreimage_mem_bondsInDoubleBlock (h : IsometryTransport σ j j') {c : Bond L m j}
    {b : Bond L m j'} (hb : b ∈ (bondsInDoubleBlock (bondImage σ c) : Set (Bond L m j'))) :
    bondPreimage σ b ∈ (bondsInDoubleBlock c : Set (Bond L m j')) := by
  refine ⟨?_, ?_⟩
  · rw [h.bondPreimage_source]
    exact symm_mem_bondDoubleBlock h hb.1
  · rw [h.bondPreimage_target]
    exact symm_mem_bondDoubleBlock h hb.2
theorem isGaugeField_transport (h : IsometryTransport σ j j') {𝒢 : Set Matrices.ComplexMatrix2}
    {c : Bond L m j} {V : Bond L m j' → Matrices.ComplexMatrix2}
    (hV : IsGaugeField 𝒢 (bondsInDoubleBlock c) V) :
    IsGaugeField 𝒢 (bondsInDoubleBlock (bondImage σ c)) (transportGaugeField σ V) := by
  refine ⟨fun b hb => hV.1 _ (bondPreimage_mem_bondsInDoubleBlock h hb), fun b hb => ?_⟩
  have e : bondPreimage σ b.opposite = (bondPreimage σ b).opposite :=
    Bond.ext (Subtype.ext ((h.bondPreimage_source b.opposite).trans (h.bondPreimage_target b).symm))
      (Subtype.ext ((h.bondPreimage_target b.opposite).trans (h.bondPreimage_source b).symm))
  show V (bondPreimage σ b.opposite) = (V (bondPreimage σ b))⁻¹
  rw [e]
  exact hV.2 _ (bondPreimage_mem_bondsInDoubleBlock h hb)
theorem coe_toSublattice (hL : 0 < L) (hj : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.SeparatedSequences.BlockAverages.coe_toSublattice <;> assumption
theorem coe_shiftAcross (hL : 0 < L) (hj : j ≤ j') (c : Bond L m j) (x : Site L m j') :
    ((shiftAcross c x : Site L m j') : FourTorus L m) =
      x + ((c.target : FourTorus L m) - c.source) := by
  unfold shiftAcross
  rw [AddSubgroup.coe_add, coe_toSublattice hL hj, AddSubgroup.coe_sub]
theorem shiftAcross_opposite_shiftAcross (hL : 0 < L) (hj : j ≤ j') (c : Bond L m j)
    (x : Site L m j') : shiftAcross c.opposite (shiftAcross c x) = x := by
  apply Subtype.ext
  rw [coe_shiftAcross hL hj, coe_shiftAcross hL hj]
  show (x : FourTorus L m) + ((c.target : FourTorus L m) - c.source) +
    ((c.source : FourTorus L m) - c.target) = x
  abel
theorem shiftAcross_mem_sitesInBlock (hL : 0 < L) (hjj : j' = j + 1) (c : Bond L m j)
    {x : Site L m j'} (hx : x ∈ sitesInBlock j' c.source) :
    shiftAcross c x ∈ sitesInBlock j' c.target := by
  subst hjj
  have hc : (x : FourTorus L m) ∈ cubeAround c.source := hx.1
  show ((shiftAcross c x : Site L m (j + 1)) : FourTorus L m) ∈ cubeAround c.target ∩ _
  refine ⟨?_, ?_⟩
  · have e : ((shiftAcross c x : Site L m (j + 1)) : FourTorus L m) - c.target =
        x - c.source := by
      rw [coe_shiftAcross hL (by omega)]
      abel
    show TorusMetric.torusSupNorm (_ - _) ≤ _
    rw [e]
    exact hc
  · simp
theorem bijOn_shiftAcross (hL : 0 < L) (hjj : j' = j + 1) (c : Bond L m j) :
    BijOn (shiftAcross c) (sitesInBlock j' c.source) (sitesInBlock j' c.target) := by
  have hj : j ≤ j' := by omega
  refine ⟨fun x hx => shiftAcross_mem_sitesInBlock hL hjj c hx, ?_, ?_⟩
  · intro x _ y _ e
    have := congrArg (shiftAcross c.opposite) e
    rwa [shiftAcross_opposite_shiftAcross hL hj, shiftAcross_opposite_shiftAcross hL hj] at this
  · intro y hy
    exact ⟨shiftAcross c.opposite y, shiftAcross_mem_sitesInBlock hL hjj c.opposite hy,
      shiftAcross_opposite_shiftAcross hL hj c.opposite y⟩
theorem toSublattice_source_mem (hL : 0 < L) (hjj : j' = j + 1) (c : Bond L m j) :
    c.source.toSublattice j' ∈ sitesInBlock j' c.source := by
  subst hjj
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hsp : 0 < meshSize L j := zpow_pos hL' _
  show ((c.source.toSublattice (j + 1) : Site L m (j + 1)) : FourTorus L m) ∈
    cubeAround c.source ∩ _
  refine ⟨?_, by simp⟩
  rw [coe_toSublattice hL (by omega)]
  show TorusMetric.torusSupNorm (_ - _) ≤ _
  rw [sub_self, TorusArcs.torusSupNorm_eq_norm, norm_zero]
  positivity
theorem shiftAcross_toSublattice_source (hL : 0 < L) (hj : j ≤ j') (c : Bond L m j) :
    shiftAcross c (c.source.toSublattice j') = c.target.toSublattice j' := by
  apply Subtype.ext
  rw [coe_shiftAcross hL hj, coe_toSublattice hL hj, coe_toSublattice hL hj]
  abel
theorem complexCrossingDefect_image (h : IsometryTransport σ j j') (hL : 0 < L)
    (hjj : j' = j + 1) (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j)
    {x : Site L m j'} (hx : x ∈ sitesInBlock j' c.source) :
    complexCrossingDefect (transportGaugeField σ V) (bondImage σ c)
        (sitePreimage σ.symm x) = complexCrossingDefect V c x := by
  unfold complexCrossingDefect
  rw [complexMeanContourHolonomy_image h V (h.bondImage_source_eq c) rfl hx,
    complexMeanContourHolonomy_image h V (h.bondImage_target_eq c) (h.mapsCrossing c x).1.symm
      (shiftAcross_mem_sitesInBlock hL hjj c hx),
    crossingHolonomy_bondImage h, parallelTransport_bondImage h]
theorem transport_mem_domain_iff (h : IsometryTransport σ j j') (hL : 0 < L)
    (hjj : j' = j + 1) (c : Bond L m j) {V : Bond L m j' → Matrices.ComplexMatrix2}
    (hV : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) V) :
    transportGaugeField σ V ∈
        (complexAveragingDomainNearOne (bondImage σ c) : Set (Bond L m j' → Matrices.ComplexMatrix2)) ↔
      V ∈ (complexAveragingDomainNearOne c : Set (Bond L m j' → Matrices.ComplexMatrix2)) := by
  have ht : (∀ x ∈ sitesInBlock j' (bondImage σ c).source, Matrices.ComplexMatrix2.familyDiameter
        (contourHolonomies (transportGaugeField σ V) (bondImage σ c).source x) <
          Averaging.centreOfMassDiameter) ↔
      ∀ x ∈ sitesInBlock j' c.source, Matrices.ComplexMatrix2.familyDiameter
        (contourHolonomies V c.source x) < Averaging.centreOfMassDiameter :=
    forall_sitesInBlock_image_iff h (h.bondImage_source_eq c) fun x hx => by
      rw [familyDiameter_contourHolonomies_image h V (h.bondImage_source_eq c) rfl hx]
  have hh : (∀ x ∈ sitesInBlock j' (bondImage σ c).target, Matrices.ComplexMatrix2.familyDiameter
        (contourHolonomies (transportGaugeField σ V) (bondImage σ c).target x) <
          Averaging.centreOfMassDiameter) ↔
      ∀ x ∈ sitesInBlock j' c.target, Matrices.ComplexMatrix2.familyDiameter
        (contourHolonomies V c.target x) < Averaging.centreOfMassDiameter :=
    forall_sitesInBlock_image_iff h (h.bondImage_target_eq c) fun x hx => by
      rw [familyDiameter_contourHolonomies_image h V (h.bondImage_target_eq c) rfl hx]
  have hw : (∀ x ∈ sitesInBlock j' (bondImage σ c).source, Matrices.ComplexMatrix2.operatorNorm
        (complexCrossingDefect (transportGaugeField σ V) (bondImage σ c) x - 1) < 1) ↔
      ∀ x ∈ sitesInBlock j' c.source,
        Matrices.ComplexMatrix2.operatorNorm (complexCrossingDefect V c x - 1) < 1 :=
    forall_sitesInBlock_image_iff h (h.bondImage_source_eq c) fun x hx => by
      rw [complexCrossingDefect_image h hL hjj V c hx]
  constructor
  · rintro ⟨⟨-, a, b⟩, d⟩
    exact ⟨⟨hV, ht.1 a, hh.1 b⟩, hw.1 d⟩
  · rintro ⟨⟨-, a, b⟩, d⟩
    exact ⟨⟨isGaugeField_transport h hV, ht.2 a, hh.2 b⟩, hw.2 d⟩
theorem complexBlockAverageOnPositive_image (h : IsometryTransport σ j j') (hL : 0 < L)
    (hjj : j' = j + 1) (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) :
    complexBlockAverageOnPositive (transportGaugeField σ V) (bondImage σ c) =
      complexBlockAverageOnPositive V c := by
  unfold complexBlockAverageOnPositive
  rw [parallelTransport_bondImage h]
  congr 3
  exact (finsum_mem_eq_of_bijOn _ (bijOn_sitesInBlock_source h c) fun x hx => by
    rw [complexCrossingDefect_image h hL hjj V c hx]).symm
end
theorem complexBlockAverage_of_positive {U : Bond L m j' → Matrices.ComplexMatrix2}
    {c : Bond L m j} (hc : c.IsPositivelyOriented) :
    complexBlockAverage U c = complexBlockAverageOnPositive U c := by
  unfold complexBlockAverage
  exact if_pos hc
section
variable {K n : ℕ}
structure OppositeBondData (c : BondAtLevel L m K (n + 1))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2) : Prop where
  crossing_opposite : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
    pathHolonomy U (crossingPath c.opposite (shiftAcross c x)) =
      (pathHolonomy U (crossingPath c x))⁻¹
  parallelTransport_opposite : parallelTransport U c.opposite = (parallelTransport U c)⁻¹
  det_crossing : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
    (pathHolonomy U (crossingPath c x)).det = 1
  exists_transport_path : ∃ Γ : List (BondAtLevel L m K n),
    parallelTransport U c = pathHolonomy U Γ ∧
      ∀ b ∈ Γ, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))
theorem levelDepth_eq_succ_add_one (K n : ℕ) : levelDepth K n = levelDepth K (n + 1) + 1 := by
  simp only [levelDepth]
  push_cast
  ring
theorem axialHolonomy_eq_inv_crossing (hR : AxialPathReversal)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    {c : BondAtLevel L m K (n + 1)} (hK : DoubleBlockBondClassification c)
    (hS : AxialPathsSpanDoubleBlock c) {U : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) U)
    {x : SiteAtLevel L m K n} (hx : x ∈ sitesInBlock (levelDepth K n) c.source) :
    pathHolonomy U (axialPath (shiftAcross c x) x) = (pathHolonomy U (crossingPath c x))⁻¹ := by
  obtain ⟨-, ⟨μ, k, hd⟩, -, -, hb⟩ := hS.1 x hx
  have hj : -(m : ℤ) ≤ levelDepth K n := by
    simp only [levelDepth]
    omega
  have hclosed := hK.2.2.1
  have hsub : ∀ b : BondAtLevel L m K n, b ∈ {b : BondAtLevel L m K n |
      b ∈ axialPath x (shiftAcross c x) ∨ b.opposite ∈ axialPath x (shiftAcross c x)} →
      b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
    rintro b (h | h)
    · exact hb b h
    · have e : b.opposite.opposite = b := Bond.ext rfl rfl
      have h2 := hclosed b.opposite (hb b.opposite h)
      rwa [e] at h2
  exact (hR L m hs hm _ hj x _ μ k hd).2.2.1 U
    ⟨fun b h => hU.1 b (hsub b h), fun b h => hU.2 b (hsub b h)⟩
theorem oppositeBondData (hR : AxialPathReversal)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    {c : BondAtLevel L m K (n + 1)} (hK : DoubleBlockBondClassification c)
    (hS : AxialPathsSpanDoubleBlock c) {U : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) U) :
    OppositeBondData c U := by
  have hL : 0 < L := by
    have := hs.2
    omega
  have hjj := levelDepth_eq_succ_add_one K n
  have hj : levelDepth K (n + 1) ≤ levelDepth K n := by omega
  have hx₀ := toSublattice_source_mem hL hjj c
  have hpath : parallelTransport U c =
      pathHolonomy U (crossingPath c (c.source.toSublattice (levelDepth K n))) := by
    unfold crossingPath parallelTransport
    rw [shiftAcross_toSublattice_source hL hj]
  refine ⟨fun x hx => ?_, ?_, fun x hx => ?_, ⟨_, hpath, (hS.1 _ hx₀).2.2.2.2⟩⟩
  · unfold crossingPath
    rw [shiftAcross_opposite_shiftAcross hL hj]
    exact axialHolonomy_eq_inv_crossing hR hs hm hn hK hS hU hx
  · have := axialHolonomy_eq_inv_crossing hR hs hm hn hK hS hU hx₀
    rw [← hpath, shiftAcross_toSublattice_source hL hj] at this
    exact this
  · exact det_pathHolonomy fun b hb => hU.1 b ((hS.1 x hx).2.2.2.2 b hb)
theorem OppositeBondData.det_parallelTransport {c : BondAtLevel L m K (n + 1)}
    {U : BondAtLevel L m K n → Matrices.ComplexMatrix2} (D : OppositeBondData c U)
    (hU : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) U) :
    (parallelTransport U c).det = 1 := by
  obtain ⟨Γ, e, hb⟩ := D.exists_transport_path
  rw [e]
  exact det_pathHolonomy fun b h => hU.1 b (hb b h)
theorem det_complexMeanContourHolonomy (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    {c : BondAtLevel L m K (n + 1)} (hC : ContoursStayInBlocks c)
    {U : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) U)
    {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target)
    {x : SiteAtLevel L m K n} (hx : x ∈ sitesInBlock (levelDepth K n) y)
    (hd : Matrices.ComplexMatrix2.familyDiameter (contourHolonomies U y x) <
      Averaging.centreOfMassDiameter) :
    (complexMeanContourHolonomy U y x).det = 1 := by
  have : Nonempty (AxisOrdering y x) := ⟨(Finset.equivFin _).symm⟩
  exact det_complexLogMean hM
    (fun s => det_pathHolonomy fun b hb => hU.1 b ((hC y hy x hx _ ⟨s, rfl⟩).2 b hb)) hd
theorem det_complexCrossingDefect {c : BondAtLevel L m K (n + 1)}
    {U : BondAtLevel L m K n → Matrices.ComplexMatrix2} (D : OppositeBondData c U)
    (hU : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) U)
    {x : SiteAtLevel L m K n} (hx : x ∈ sitesInBlock (levelDepth K n) c.source)
    (hA : (complexMeanContourHolonomy U c.source x).det = 1)
    (hC : (complexMeanContourHolonomy U c.target (shiftAcross c x)).det = 1) :
    (complexCrossingDefect U c x).det = 1 := by
  unfold complexCrossingDefect
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hA, D.det_crossing x hx,
    det_inv_of_det_eq_one hC, det_inv_of_det_eq_one (D.det_parallelTransport hU)]
  simp
theorem complexCrossingDefect_opposite (hL : 0 < L) {c : BondAtLevel L m K (n + 1)}
    {U : BondAtLevel L m K n → Matrices.ComplexMatrix2} (D : OppositeBondData c U)
    (hU : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) U) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) c.source)
    (hC : (complexMeanContourHolonomy U c.target (shiftAcross c x)).det = 1) :
    complexCrossingDefect U c.opposite (shiftAcross c x) =
      (parallelTransport U c)⁻¹ * (complexCrossingDefect U c x)⁻¹ *
        (parallelTransport U c)⁻¹⁻¹ := by
  have hj : levelDepth K (n + 1) ≤ levelDepth K n := by
    have := levelDepth_eq_succ_add_one K n
    omega
  unfold complexCrossingDefect
  rw [D.crossing_opposite x hx, D.parallelTransport_opposite,
    shiftAcross_opposite_shiftAcross hL hj]
  exact conj_inv_four_factors hC (D.det_parallelTransport hU)
theorem complexBlockAverageOnPositive_opposite
    (h1 : Matrices.ComplexMatrix2.LogSeriesConjugateInverse)
    (h3 : Matrices.ComplexMatrix2.OperatorNormUnderConjugation)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hL : 0 < L) {c : BondAtLevel L m K (n + 1)} (hC : ContoursStayInBlocks c)
    {U : BondAtLevel L m K n → Matrices.ComplexMatrix2} (D : OppositeBondData c U)
    (hU : U ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)))
    (hU' : U ∈ (complexAveragingDomainNearOne c.opposite :
      Set (BondAtLevel L m K n → Matrices.ComplexMatrix2))) :
    complexBlockAverageOnPositive U c.opposite = (complexBlockAverageOnPositive U c)⁻¹ := by
  obtain ⟨⟨hcfg, ht, hh⟩, hnorm⟩ := hU
  have hjj := levelDepth_eq_succ_add_one K n
  have hT := D.det_parallelTransport hcfg
  have hS := det_inv_of_det_eq_one hT
  have hsum : ∑ᶠ x' ∈ sitesInBlock (levelDepth K n) c.opposite.source,
        Matrices.ComplexMatrix2.logSeries (complexCrossingDefect U c.opposite x') =
      negConjEquiv _ hS
        (∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
          Matrices.ComplexMatrix2.logSeries (complexCrossingDefect U c x)) := by
    rw [linearEquiv_map_finsum_mem]
    refine (finsum_mem_eq_of_bijOn (shiftAcross c) (bijOn_shiftAcross hL hjj c)
      fun x hx => ?_).symm
    have hx' := shiftAcross_mem_sitesInBlock hL hjj c hx
    have hA := det_complexMeanContourHolonomy hM hC hcfg (Or.inl rfl) hx (ht x hx)
    have hB := det_complexMeanContourHolonomy hM hC hcfg (Or.inr rfl) hx' (hh _ hx')
    have hW := det_complexCrossingDefect D hcfg hx hA hB
    have hn' := hU'.2 _ hx'
    rw [complexCrossingDefect_opposite hL D hcfg hx hB] at hn' ⊢
    exact (h1 _ _ (isUnit_of_det_eq_one hW) (isUnit_of_det_eq_one hS) (hnorm x hx) hn').symm
  unfold complexBlockAverageOnPositive
  rw [hsum, ← map_smul, D.parallelTransport_opposite]
  exact matExp_negConjEquiv_mul h3 _ hT
theorem mem_domain_opposite_of_compact (hP : AveragingSchemeProperties)
    (hB : DoubleBlockStructure.Statement) (hR : AxialPathReversal)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (h3 : Matrices.ComplexMatrix2.OperatorNormUnderConjugation)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    {c : BondAtLevel L m K (n + 1)} (hc : c.IsPositivelyOriented)
    {W : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    (hreal : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W)
    (hW : W ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K n → Matrices.ComplexMatrix2))) :
    W ∈ (complexAveragingDomainNearOne c.opposite :
      Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)) := by
  have hL : 0 < L := by
    have := hs.2
    omega
  have hjj := levelDepth_eq_succ_add_one K n
  obtain ⟨hK, hC, hS, -, -⟩ := hB L m K n hs hm hn c
  obtain ⟨-, -, hMD, hVal, -, -⟩ := (hP L hs m K n hm hn .centred).2.1 c hc
  have hdom : W ∈ (schemeHolomorphyDomain .centred c :
      Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)) := by
    rw [hMD.domain_eq]
    exact hW
  have hV := hVal W hdom hreal
  obtain ⟨⟨hcfg, ht, hh⟩, hnorm⟩ := hW
  have D := oppositeBondData hR hs hm hn hK hS hcfg
  have hT : parallelTransport W c ∈ Matrices.ComplexMatrix2.specialUnitary := by
    obtain ⟨Γ, e, hb⟩ := D.exists_transport_path
    rw [e]
    exact pathHolonomy_mem_specialUnitary fun b h => hreal.1 b (hb b h)
  refine ⟨⟨?_, hh, ht⟩, fun x' hx' => ?_⟩
  · rw [hK.2.2.2.1]
    exact hcfg
  · obtain ⟨x, hx, rfl⟩ := (bijOn_shiftAcross hL hjj c).surjOn hx'
    have hB' := det_complexMeanContourHolonomy hM hC hcfg (Or.inr rfl)
      (shiftAcross_mem_sitesInBlock hL hjj c hx) (hh _ (shiftAcross_mem_sitesInBlock hL hjj c hx))
    rw [complexCrossingDefect_opposite hL D hcfg hx hB']
    have hWx : complexCrossingDefect W c x ∈ Matrices.ComplexMatrix2.specialUnitary := by
      rw [← hMD.defect_eq W hdom x hx]
      exact hV.defect_mem x hx
    exact operatorNorm_conj_inv_sub_one_lt h3 hWx (inv_mem_specialUnitary hT) (hnorm x hx)
end
theorem coe_sitePreimage_of_maps {σ : FourTorus L m ≃ FourTorus L m}
    (hC : MapsCellsAndCubes σ j) (y : Site L m j) :
    ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y := by
  have hex : ∃ x : Site L m j, (x : FourTorus L m) = σ.symm.symm y := by
    have hmem : σ y ∈ σ '' (sublattice L m j : Set (FourTorus L m)) := ⟨y, y.2, rfl⟩
    rw [hC.1] at hmem
    exact ⟨⟨σ y, hmem⟩, rfl⟩
  exact Classical.epsilon_spec hex
theorem isometryTransport_of_mem (hO : IsometryImages.Statement)
    (hG : LatticeIsometryGroupActionStatement) (hs : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i) {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : σ ∈ latticeIsometries L m i) (hij : i ≤ j) (hj : 0 ≤ j) (hjj : j' = j + 1) :
    IsometryTransport σ j j' := by
  have hσ' : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨H, hH⟩ := (hG L m i hs hm hi).1.1
    have h1 : σ ∈ H := by
      have : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
      exact this
    have h3 : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := H.inv_mem h1
    rw [hH] at h3
    exact h3
  have hij' : i ≤ j' := by omega
  have hC := ((hG L m i hs hm hi).2.2.2.2 σ hσ j hij).1
  have hC' := ((hG L m i hs hm hi).2.2.2.2 σ hσ j' hij').1
  have hD' := ((hG L m i hs hm hi).2.2.2.2 σ.symm hσ' j' hij').1
  have hO' := hO L m hs hm i hi σ hσ j j' hij hj hjj
  refine ⟨fun b => (hC.2.2.2.1 b).1, fun b => (hC.2.2.2.1 b).2, fun b => Subtype.ext ?_,
    fun b => Subtype.ext ?_, coe_sitePreimage_of_maps hC', fun b => (hD'.2.2.2.1 b).1,
    fun b => (hD'.2.2.2.1 b).2, fun V b => ?_, fun y => (hO'.1 y).1,
    fun y x hx => (hO'.1 y).2 x hx, fun c x => (hO'.2 c).1 x, fun c => (hO'.2 c).2.1⟩
  · rw [coe_sitePreimage_of_maps hC]
    exact (hC.2.2.2.1 b).1
  · rw [coe_sitePreimage_of_maps hC]
    exact (hC.2.2.2.1 b).2
  · have e := hC'.2.2.2.1 b
    have p := hD'.2.2.2.1 (bondImage σ b)
    have : bondPreimage σ (bondImage σ b) = b := by
      apply Bond.ext <;> apply Subtype.ext
      · refine Eq.trans p.1 ?_
        rw [e.1]
        simp
      · refine Eq.trans p.2 ?_
        rw [e.2]
        simp
    exact congrArg V this
theorem complexAverageEquivariance_holds (hO : IsometryImages.Statement)
    (hG : LatticeIsometryGroupActionStatement)
    (hB : DoubleBlockStructure.Statement)
    (hR : AxialPathReversal)
    (hP : AveragingSchemeProperties)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (h1 : Matrices.ComplexMatrix2.LogSeriesConjugateInverse)
    (h3 : Matrices.ComplexMatrix2.OperatorNormUnderConjugation) :
    ComplexAverageEquivariance := by
  intro L m K k i σ hs hm hi hσ hk hik U c c' hc hc' hor hU
  have hL : 0 < L := by
    have := hs.2
    omega
  have hjj := levelDepth_eq_succ_add_one K k
  have hj0 : 0 ≤ levelDepth K (k + 1) := by
    simp only [levelDepth]
    omega
  have h : IsometryTransport σ (levelDepth K (k + 1)) (levelDepth K k) :=
    isometryTransport_of_mem hO hG hs hm hi hσ hik hj0 hjj
  have hrev := bondImage_opposite h c
  obtain ⟨hK, hC, hS, -, -⟩ := hB L m K k hs hm hk c
  have hUrev : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c.opposite) U := by
    rw [hK.2.2.2.1]
    exact hU
  refine ⟨fun e => ?_, fun hreal => ?_, fun e hUc => ?_, fun e hUc hVc => ?_⟩
  · subst e
    exact transport_mem_domain_iff h hL hjj c hU
  · rcases hor with e | e
    · subst e
      exact transport_mem_domain_iff h hL hjj c hU
    · subst e
      constructor
      · intro hV
        have hVreal : IsGaugeField compactGaugeGroup
            (bondsInDoubleBlock (bondImage σ c).opposite) (transportGaugeField σ U) := by
          rw [(hB L m K k hs hm hk (bondImage σ c)).1.2.2.2.1]
          exact isGaugeField_transport h hreal
        exact (transport_mem_domain_iff h hL hjj c hU).1
          (mem_domain_opposite_of_compact hP hB hR hM h3 hs hm hk hc' hVreal hV)
      · intro hUc
        have := (transport_mem_domain_iff h hL hjj c.opposite hUrev).2
          (mem_domain_opposite_of_compact hP hB hR hM h3 hs hm hk hc hreal hUc)
        rwa [hrev] at this
  · subst e
    rw [complexBlockAverage_of_positive hc', complexBlockAverage_of_positive hc]
    exact complexBlockAverageOnPositive_image h hL hjj U c
  · subst e
    have hU' : U ∈ (complexAveragingDomainNearOne c.opposite :
        Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) :=
      (transport_mem_domain_iff h hL hjj c.opposite hUrev).1 (by rw [hrev]; exact hVc)
    rw [complexBlockAverage_of_positive hc', complexBlockAverage_of_positive hc, ← hrev,
      complexBlockAverageOnPositive_image h hL hjj U c.opposite]
    exact complexBlockAverageOnPositive_opposite h1 h3 hM hL hC
      (oppositeBondData hR hs hm hk hK hS hU) hUc hU'
end YangMills.Construction.PeriodicLattice.ImageBondEquivariance
