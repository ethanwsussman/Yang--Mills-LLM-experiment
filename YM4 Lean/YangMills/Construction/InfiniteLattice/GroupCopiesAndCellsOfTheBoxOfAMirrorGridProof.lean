import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGridsProof
import YangMills.Construction.ChessboardTori.ChessboardEstimateOnMirrorGridsProof
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfAGridOfMultipleReflections
import YangMills.Construction.InfiniteLattice.GroupCopiesAndCellsOfTheBoxOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.LatticeIsometriesAndPeriodicRealizationOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open scoped ComplexConjugate
namespace MultipleReflections.BoxTileFacts
open Setup.Grid
variable {D : Setup} (G : D.Grid)
theorem cornerAt_apply (k : Fin 4 → ℤ) (μ : Fin 4) :
    G.cornerAt k μ = G.shift μ + G.edge * (k μ : ℝ) := by
  simp [InfiniteLattice.ReflectionGrid.cornerAt]
theorem mem_tile {k : Fin 4 → ℤ} {x : AmbientSpace} :
    x ∈ G.tile k ↔ ∀ μ, G.shift μ + G.edge * (k μ : ℝ) ≤ x μ ∧
      x μ ≤ G.shift μ + G.edge * (k μ : ℝ) + G.edge := by
  simp only [InfiniteLattice.ReflectionGrid.tile, InfiniteLattice.cube, Set.mem_ofPred_eq,
    cornerAt_apply]
theorem mem_tileInterior {k : Fin 4 → ℤ} {x : AmbientSpace} :
    x ∈ G.tileInterior k ↔ ∀ μ, G.shift μ + G.edge * (k μ : ℝ) < x μ ∧
      x μ < G.shift μ + G.edge * (k μ : ℝ) + G.edge := by
  simp only [InfiniteLattice.ReflectionGrid.tileInterior, Set.mem_ofPred_eq, cornerAt_apply]
theorem exists_index_of_coordinateMove {α : Fin 4} {δ : ℝ → ℝ} (hδ : G.IsCoordinateMove α δ)
    (n : ℤ) :
    ∃ n' : ℤ, ∀ y : ℝ,
      ((G.shift α + G.edge * (n : ℝ) ≤ y ∧ y ≤ G.shift α + G.edge * (n : ℝ) + G.edge) ↔
        (G.shift α + G.edge * (n' : ℝ) ≤ δ y ∧
          δ y ≤ G.shift α + G.edge * (n' : ℝ) + G.edge)) ∧
      ((G.shift α + G.edge * (n : ℝ) < y ∧ y < G.shift α + G.edge * (n : ℝ) + G.edge) ↔
        (G.shift α + G.edge * (n' : ℝ) < δ y ∧
          δ y < G.shift α + G.edge * (n' : ℝ) + G.edge)) := by
  rcases hδ with ⟨t, ht⟩ | ⟨t, ht⟩
  · refine ⟨n + 2 * t, fun y => ?_⟩
    rw [ht]
    push_cast
    constructor <;> constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · refine ⟨2 * t - n - 1, fun y => ?_⟩
    rw [ht]
    push_cast
    constructor <;> constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
theorem image_eq_of_mem_iff {f : AmbientSpace → AmbientSpace} (hf : Function.Surjective f)
    {A B : Set AmbientSpace} (h : ∀ x, x ∈ A ↔ f x ∈ B) : f '' A = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, (h x).2 hy, rfl⟩
theorem exists_tile_image (hG : G.GroupEqCoordinatewiseMaps) (g : G.reflectionGroup)
    (k : Fin 4 → ℤ) :
    ∃ k' : Fin 4 → ℤ,
      (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tile k = G.tile k' ∧
      (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tileInterior k = G.tileInterior k' := by
  obtain ⟨δ, hδ, hg⟩ := hG.1 g
  choose k' hk' using fun α => exists_index_of_coordinateMove G (hδ α) (k α)
  have hsurj : Function.Surjective
      ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) :=
    (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).surjective
  refine ⟨k', image_eq_of_mem_iff hsurj fun x => ?_, image_eq_of_mem_iff hsurj fun x => ?_⟩
  · rw [mem_tile, mem_tile]
    refine forall_congr' fun α => ?_
    rw [hg]
    exact (hk' α (x α)).1
  · rw [mem_tileInterior, mem_tileInterior]
    refine forall_congr' fun α => ?_
    rw [hg]
    exact (hk' α (x α)).2
theorem coe_orientationUnit (g : G.reflectionGroup) :
    (((G.orientationUnit g : ℤˣ) : ℤ) : ℝ) = G.orientation g := by
  rcases G.orientation_eq_one_or_neg_one g with h | h
  · simp [orientationUnit, h]
  · have hne : ¬ ((-1 : ℝ) = 1) := by norm_num
    simp [orientationUnit, h, hne]
theorem orientation_mul (g h : G.reflectionGroup) :
    G.orientation (g * h) = G.orientation g * G.orientation h := by
  let φ : (AmbientSpace ≃ᵃ[ℝ] AmbientSpace) →* ℝˣ := LinearEquiv.det.comp AffineEquiv.linearHom
  have hφ : ∀ f : AmbientSpace ≃ᵃ[ℝ] AmbientSpace,
      ((φ f : ℝˣ) : ℝ) = LinearMap.det (f.linear : AmbientSpace →ₗ[ℝ] AmbientSpace) := fun f =>
    LinearEquiv.coe_det _
  have hs : ∀ f : G.reflectionGroup,
      G.orientation f = ((φ (f : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : ℝˣ) : ℝ) := fun f =>
    (hφ _).symm
  rw [hs, hs, hs, Subgroup.coe_mul, map_mul, Units.val_mul]
theorem orientationUnit_mul (g h : G.reflectionGroup) :
    G.orientationUnit (g * h) = G.orientationUnit g * G.orientationUnit h := by
  apply Units.ext
  apply Int.cast_injective (α := ℝ)
  rw [coe_orientationUnit, Units.val_mul, Int.cast_mul, coe_orientationUnit, coe_orientationUnit,
    orientation_mul]
theorem orientation_of_wallReflect (μ : Fin 4) (n : ℤ) (g : G.reflectionGroup)
    (h : (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) = G.wallReflectEquiv μ n) :
    G.orientation g = -1 := by
  have hl : ((G.wallReflectEquiv μ n).linear : AmbientSpace →ₗ[ℝ] AmbientSpace) =
      Matrix.toLin' (Matrix.diagonal (InfiniteLattice.ReflectionGrid.signFlip μ)) := rfl
  show LinearMap.det (((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).linear :
    AmbientSpace →ₗ[ℝ] AmbientSpace)) = -1
  rw [h, hl, LinearMap.det_toLin', Matrix.det_diagonal]
  fin_cases μ <;> simp [InfiniteLattice.ReflectionGrid.signFlip, Function.update]
theorem orientationIsHom : G.OrientationIsHom :=
  ⟨⟨MonoidHom.mk' G.orientationUnit (orientationUnit_mul G), fun g => coe_orientationUnit G g⟩,
    fun μ n g h => orientation_of_wallReflect G μ n g h⟩
theorem tileReflection_self (k : Fin 4 → ℤ) : G.tileReflection k k = id := by
  funext x α
  simp [tileReflection]
theorem comp_tileReflection (hU : G.UniqueElementBetweenTiles) (g : G.reflectionGroup)
    {k k' k'' : Fin 4 → ℤ} (h : (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tile k' = G.tile k'') :
    ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) ∘
      G.tileReflection k k' = G.tileReflection k k'' := by
  obtain ⟨g₁, hu₁, hm₁, -⟩ := hU k k'
  obtain ⟨g₂, hu₂, hm₂, -⟩ := hU k k''
  have h₁ : ((g₁ : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) '' G.tile k =
      G.tile k' := (hu₁ g₁).2 rfl
  have h₂ : g * g₁ = g₂ := (hu₂ (g * g₁)).1 (by
    rw [Subgroup.coe_mul, AffineEquiv.coe_mul, Set.image_comp, h₁, h])
  rw [← hm₁, ← hm₂, ← h₂, Subgroup.coe_mul, AffineEquiv.coe_mul]
theorem tileSign_mul (k k' k'' : Fin 4 → ℤ) :
    tileSign k' k'' * tileSign k k' = tileSign k k'' := by
  unfold tileSign
  rw [← zpow_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by ring
theorem tileReflectionsCompose (hU : G.UniqueElementBetweenTiles) :
    G.TileReflectionsCompose := by
  refine ⟨tileReflection_self G, fun g k k' k'' h => comp_tileReflection G hU g h,
    fun k k' k'' => ?_, tileSign_mul⟩
  obtain ⟨g, hu, hm, -⟩ := hU k' k''
  rw [← hm]
  exact comp_tileReflection G hU g ((hu g).2 rfl)
theorem orientationUnit_eq_tileSign (hU : G.UniqueElementBetweenTiles) (g : G.reflectionGroup)
    {k' k'' : Fin 4 → ℤ} (h : (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tile k' = G.tile k'') :
    G.orientationUnit g = tileSign k' k'' := by
  obtain ⟨g₁, hu, -, hs⟩ := hU k' k''
  obtain rfl : g = g₁ := (hu g).1 h
  apply Units.ext
  apply Int.cast_injective (α := ℝ)
  rw [coe_orientationUnit, hs]
section Action
variable {a : ℝ}
theorem linkMap_linkMap (r s t : InfiniteLattice.LatticeSymmetry a)
    (h : t.toFun = s.toFun ∘ r.toFun) (b : InfiniteLattice.Link a) :
    s.linkMap (r.linkMap b) = t.linkMap b := by
  apply InfiniteLattice.Link.ext
  · exact Subtype.ext (congrFun h _).symm
  · exact Subtype.ext (congrFun h _).symm
theorem pullbackField_pullbackField (r s t : InfiniteLattice.LatticeSymmetry a)
    (h : t.toFun = s.toFun ∘ r.toFun) (U : InfiniteLattice.GaugeField a) :
    r.pullbackField (s.pullbackField U) = t.pullbackField U :=
  Subtype.ext (funext fun b => congrArg U.1 (linkMap_linkMap r s t h b))
theorem pullbackField_of_toFun_eq_id (r : InfiniteLattice.LatticeSymmetry a)
    (h : r.toFun = id) (U : InfiniteLattice.GaugeField a) : r.pullbackField U = U := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGridArithmetic.pullbackField_of_eq_id <;> assumption
theorem continuous_pullbackField (r : InfiniteLattice.LatticeSymmetry a) :
    Continuous r.pullbackField := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetry.continuous_pullbackField <;> assumption
theorem isRegionMeasurable_actOn (r : InfiniteLattice.LatticeSymmetry a)
    {S S' : Set AmbientSpace} (h : ∀ x ∈ S, r.toFun x ∈ S')
    {A : InfiniteLattice.GaugeField a → ℂ} (hA : InfiniteLattice.IsRegionMeasurable S A) :
    InfiniteLattice.IsRegionMeasurable S' (r.actOn A) := by
  have hr : @Measurable _ _ (InfiniteLattice.regionSigma S') (InfiniteLattice.regionSigma S)
      r.pullbackField := by
    refine measurable_iff_comap_le.2 ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun b => ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun hb => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂_of_le (r.linkMap b) ⟨h _ hb.1, h _ hb.2⟩ le_rfl
  exact hA.comp hr
end Action
theorem signedConj_signedConj (σ τ : ℤˣ) (ξ : ℂ) :
    Conventions.signedConj σ (Conventions.signedConj τ ξ) = Conventions.signedConj (σ * τ) ξ := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions.signedConj_signedConj <;> assumption
theorem norm_signedConj (σ : ℤˣ) (ξ : ℂ) : ‖Conventions.signedConj σ ξ‖ = ‖ξ‖ := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.norm_signedConj <;> assumption
theorem tileReflection_mem_tileInterior (hG : G.GroupEqCoordinatewiseMaps)
    (hU : G.UniqueElementBetweenTiles) (k k' : Fin 4 → ℤ) :
    ∀ x ∈ G.tileInterior k, G.tileReflection k k' x ∈ G.tileInterior k' := by
  obtain ⟨g, hu, hm, -⟩ := hU k k'
  obtain ⟨k'', h1, h2⟩ := exists_tile_image G hG g k
  have h3 : G.tile k'' = G.tile k' := h1.symm.trans ((hu g).2 rfl)
  obtain rfl : k'' = k' := G.tile_injective h3
  intro x hx
  rw [← h2, ← hm]
  exact ⟨x, hx, rfl⟩
theorem actOn_mem_tileAlgebra (hG : G.GroupEqCoordinatewiseMaps)
    (hU : G.UniqueElementBetweenTiles) {k k' : Fin 4 → ℤ}
    {F : D.GaugeField → ℂ} (hF : F ∈ G.tileAlgebra k) :
    (G.tileSymmetry k k').actOn F ∈ G.tileAlgebra k' := by
  obtain ⟨⟨hm, C, hC⟩, hF'⟩ := hF
  exact ⟨⟨hm.comp (continuous_pullbackField _).measurable, C, fun U => hC _⟩,
    isRegionMeasurable_actOn _ (tileReflection_mem_tileInterior G hG hU k k') hF'⟩
theorem reflectedCopy_mem_tileAlgebra (hG : G.GroupEqCoordinatewiseMaps)
    (hU : G.UniqueElementBetweenTiles) {k k' : Fin 4 → ℤ}
    {F : D.GaugeField → ℂ} (hF : F ∈ G.tileAlgebra k) :
    G.reflectedCopy k k' F ∈ G.tileAlgebra k' := by
  have hA := actOn_mem_tileAlgebra G hG hU (k' := k') hF
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or (tileSign k k') with h | h
  · have he : G.reflectedCopy k k' F = (G.tileSymmetry k k').actOn F := by
      funext U
      simp [reflectedCopy, Conventions.signedConjFun, Conventions.signedConj, h]
    rw [he]
    exact hA
  · have he : G.reflectedCopy k k' F = star ((G.tileSymmetry k k').actOn F) := by
      funext U
      simp [reflectedCopy, Conventions.signedConjFun, Conventions.signedConj, h, hne]
    rw [he]
    exact StarSubalgebra.star_mem' (G.tileAlgebra k') hA
theorem reflectedCopy_self (k : Fin 4 → ℤ) (F : D.GaugeField → ℂ) : G.reflectedCopy k k F = F := by
  funext U
  have hs : tileSign k k = 1 := by simp [tileSign]
  have hc := pullbackField_of_toFun_eq_id (G.tileSymmetry k k) (tileReflection_self G k) U
  simp only [reflectedCopy, Conventions.signedConjFun, hs, Conventions.signedConj, if_true,
    InfiniteLattice.LatticeSymmetry.actOn, hc]
theorem supNorm_reflectedCopy (hR : D.ActOnRespectsAlgebra) (k k' : Fin 4 → ℤ)
    {F : D.GaugeField → ℂ} (hF : InfiniteLattice.IsBoundedObservable F) :
    InfiniteLattice.observableSupNorm (G.reflectedCopy k k' F) =
      InfiniteLattice.observableSupNorm F := by
  have h := (hR (G.tileSymmetry k k')).2 F F hF hF 0
  rw [← h.2.2.2.2.2]
  unfold InfiniteLattice.observableSupNorm
  exact iSup_congr fun U => norm_signedConj _ _
theorem reflectedCopy_transport (hU : G.UniqueElementBetweenTiles) (k k' k'' : Fin 4 → ℤ)
    (F : D.GaugeField → ℂ) (g : G.reflectionGroup)
    (h : (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tile k' = G.tile k'') :
    Conventions.signedConjFun (G.orientationUnit g)
        ((G.toLatticeSymmetry D.isAdmissible g).actOn (G.reflectedCopy k k' F)) =
      G.reflectedCopy k k'' F := by
  funext U
  have hc := pullbackField_pullbackField (G.tileSymmetry k k')
    (G.toLatticeSymmetry D.isAdmissible g) (G.tileSymmetry k k'')
    (comp_tileReflection G hU g h).symm U
  show Conventions.signedConj _ (Conventions.signedConj _ (F _)) = Conventions.signedConj _ (F _)
  rw [signedConj_signedConj, orientationUnit_eq_tileSign G hU g h, tileSign_mul]
  exact congrArg (fun V => Conventions.signedConj (tileSign k k'') (F V)) hc
theorem tilesPerSideEven (h : 2 * G.edge ≤ D.side) {p : ℤ} (hp : G.edge = (D.L : ℝ) ^ p) :
    G.TilesPerSideEven p := by
  obtain ⟨h1, h2⟩ := G.tilesPerSide_eq h hp
  refine ⟨h1, h2, ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, ((D.m : ℕ) : ℤ) - p = (t : ℤ) :=
    ⟨(((D.m : ℕ) : ℤ) - p).toNat, by omega⟩
  have hL : (1 : ℤ) ≤ (D.L : ℤ) := by
    have := D.isAdmissible.2
    omega
  refine ⟨2 * (D.L : ℤ) ^ t, ⟨(D.L : ℤ) ^ t, by ring⟩, ?_, ?_⟩
  · have : (1 : ℤ) ≤ (D.L : ℤ) ^ t := one_le_pow₀ hL
    linarith
  · rw [h2, ht, zpow_natCast]
    push_cast
    rfl
theorem image_add_tile (k w : Fin 4 → ℤ) (v : AmbientSpace)
    (hv : ∀ μ, v μ = G.edge * (w μ : ℝ)) :
    (fun x : AmbientSpace => x + v) '' G.tile k = G.tile (k + w) := by
  refine image_eq_of_mem_iff (fun y => ⟨y - v, by simp⟩) fun x => ?_
  rw [mem_tile, mem_tile]
  refine forall_congr' fun μ => ?_
  simp only [Pi.add_apply, hv]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
theorem periodShiftsInGroup {N : ℤ} (hN : Even N) (hc : G.tilesPerSide = N)
    (hG : G.GroupEqCoordinatewiseMaps) (hU : G.UniqueElementBetweenTiles) :
    G.PeriodShiftsInGroup := by
  have hl := G.edge_pos
  have hside : D.side = (N : ℝ) * G.edge := by
    rw [← hc, tilesPerSide, div_mul_cancel₀ _ hl.ne']
  intro v hv
  obtain ⟨n, hn⟩ := hv
  obtain ⟨M, hM⟩ := InfiniteLattice.ReflectionGrid.exists_edge_eq_natCast_mul_spacingAt G
    D.isAdmissible
  have hM' : G.edge = (M : ℝ) * D.mesh := hM
  have hv' : v ∈ InfiniteLattice.latticeSubgroup D.mesh := ⟨fun μ => n μ * N * (M : ℤ), fun μ => by
    rw [hn, hside, hM']
    push_cast
    ring⟩
  obtain ⟨e, he⟩ := hN
  let q : Fin 4 → ℤ := fun μ => N * n μ
  have hq : ∀ μ, v μ = G.edge * (q μ : ℝ) := fun μ => by
    rw [hn, hside]
    simp only [q]
    push_cast
    ring
  have hmap : G.ActsCoordinatewise fun x => x + v := by
    refine ⟨fun α y => y + v α, fun α => Or.inl ⟨e * n α, fun y => ?_⟩, fun x α => rfl⟩
    show y + v α = _
    rw [hq]
    simp only [q, he]
    push_cast
    ring
  obtain ⟨g, hg⟩ := hG.2 _ hmap
  refine ⟨hv', ⟨g, hg, ?_⟩, q, fun μ => ?_, ⟨n, fun μ => ?_⟩, fun k => ?_⟩
  · have him : (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tile 0 = G.tile (0 + q) := by
      rw [hg]
      exact image_add_tile G 0 q v hq
    have hsg := orientationUnit_eq_tileSign G hU g him
    have hev : Even (∑ α, ((0 + q) α - (0 : Fin 4 → ℤ) α)) := by
      refine Finset.even_sum _ fun α _ => ?_
      simp only [Pi.add_apply, Pi.zero_apply, zero_add, sub_zero, q, he]
      exact Even.mul_right ⟨e, rfl⟩ _
    have h1 : G.orientationUnit g = 1 := by
      rw [hsg, tileSign]
      exact hev.neg_one_zpow
    rw [← coe_orientationUnit, h1]
    simp
  · rw [hq]
    field_simp
  · rw [hc]
    simp only [q]
    push_cast
    ring
  · exact image_add_tile G k q v hq
theorem areCongruent_tile_iff {N : ℤ} (hc : G.tilesPerSide = N) (k k' : Fin 4 → ℤ) :
    G.AreCongruent (G.tile k) (G.tile k') ↔ ∃ w : Fin 4 → ℤ, ∀ μ, k' μ = k μ + N * w μ := by
  have hl := G.edge_pos
  have hside : D.side = (N : ℝ) * G.edge := by
    rw [← hc, tilesPerSide, div_mul_cancel₀ _ hl.ne']
  have him : ∀ w : Fin 4 → ℤ,
      (fun x : AmbientSpace => x + D.side • fun μ => (w μ : ℝ)) '' G.tile k =
        G.tile (k + fun μ => N * w μ) := fun w =>
    image_add_tile G k _ _ fun μ => by
      simp only [Pi.smul_apply, smul_eq_mul, hside]
      push_cast
      ring
  constructor
  · rintro ⟨-, -, w, h⟩
    rw [him] at h
    exact ⟨w, fun μ => congrFun (G.tile_injective h) μ⟩
  · rintro ⟨w, hw⟩
    refine ⟨⟨k, rfl⟩, ⟨k', rfl⟩, w, ?_⟩
    rw [him]
    congr 1
    funext μ
    exact hw μ
theorem mem_boxTileIndices {N : ℤ} (hc : G.tilesPerSide = N) (k : Fin 4 → ℤ) :
    k ∈ G.boxTileIndices ↔ ∀ μ, 0 ≤ k μ ∧ k μ < N := by
  have h : PeriodicLattice.torusSide D.L D.m / G.edge = (N : ℝ) := hc
  show (∀ μ, 0 ≤ k μ ∧ (k μ : ℝ) ≤ PeriodicLattice.torusSide D.L D.m / G.edge - 1) ↔ _
  rw [h]
  refine forall_congr' fun μ => and_congr_right fun _ => ?_
  have h1 : (k μ : ℝ) ≤ (N : ℝ) - 1 ↔ k μ ≤ N - 1 := by
    exact_mod_cast Iff.rfl
  rw [h1]
  omega
theorem existsUnique_congruent_boxTile {N : ℤ} (hN : 0 < N) (hc : G.tilesPerSide = N)
    (k₀ : Fin 4 → ℤ) (S : Set AmbientSpace) (hS : S ∈ G.tiling) :
    ∃! S' : Set AmbientSpace,
      S' ∈ G.tile '' {k | k - k₀ ∈ G.boxTileIndices} ∧ G.AreCongruent S S' := by
  obtain ⟨k, rfl⟩ := hS
  let k₁ : Fin 4 → ℤ := fun μ => k₀ μ + (k μ - k₀ μ) % N
  refine ⟨G.tile k₁, ⟨⟨k₁, ?_, rfl⟩, ?_⟩, ?_⟩
  · show k₁ - k₀ ∈ G.boxTileIndices
    rw [mem_boxTileIndices G hc]
    intro μ
    simp only [Pi.sub_apply, k₁, add_sub_cancel_left]
    exact ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN⟩
  · rw [areCongruent_tile_iff G hc]
    refine ⟨fun μ => -((k μ - k₀ μ) / N), fun μ => ?_⟩
    simp only [k₁, Int.emod_def]
    ring
  · rintro S' ⟨⟨k₂, hk₂, rfl⟩, hcong⟩
    rw [areCongruent_tile_iff G hc] at hcong
    obtain ⟨w, hw⟩ := hcong
    have hb := (mem_boxTileIndices G hc _).1 hk₂
    congr 1
    funext μ
    have h1 := hb μ
    simp only [Pi.sub_apply] at h1
    have h2 : (k₂ μ - k₀ μ) % N = k₂ μ - k₀ μ := Int.emod_eq_of_lt h1.1 h1.2
    have h3 : k₂ μ - k₀ μ = (k μ - k₀ μ) + N * w μ := by
      rw [hw]
      ring
    have h4 : (k₂ μ - k₀ μ) % N = (k μ - k₀ μ) % N := by
      rw [h3, Int.add_mul_emod_self_left]
    simp only [k₁]
    omega
theorem tilesCongruentToBoxTile {N : ℤ} (hN : 0 < N) (hc : G.tilesPerSide = N) :
    G.TilesCongruentToBoxTile := by
  refine ⟨fun k₀ S hS => existsUnique_congruent_boxTile G hN hc k₀ S hS, fun S hS => ?_⟩
  have h := existsUnique_congruent_boxTile G hN hc 0 S hS
  simpa [boxTiles] using h
def pairSwap (x : ℤ) : ℤ := if Even x then x + 1 else x - 1
theorem pairSwap_of_even {x : ℤ} (h : Even x) : pairSwap x = x + 1 := if_pos h
theorem pairSwap_of_not_even {x : ℤ} (h : ¬ Even x) : pairSwap x = x - 1 := if_neg h
theorem pairSwap_pairSwap (x : ℤ) : pairSwap (pairSwap x) = x := by
  by_cases h : Even x
  · rw [pairSwap_of_even h, pairSwap_of_not_even (by rw [Int.even_add_one]; exact not_not.2 h)]
    ring
  · rw [pairSwap_of_not_even h, pairSwap_of_even (by rw [Int.even_sub_one]; exact h)]
    ring
theorem pairSwap_mem {N x : ℤ} (hN : Even N) (h : 0 ≤ x ∧ x < N) :
    0 ≤ pairSwap x ∧ pairSwap x < N := by
  obtain ⟨b, hb⟩ := hN
  by_cases hx : Even x
  · rw [pairSwap_of_even hx]
    obtain ⟨c, hc⟩ := hx
    omega
  · rw [pairSwap_of_not_even hx]
    obtain ⟨c, hc⟩ := Int.not_even_iff_odd.1 hx
    omega
def pairSwapHead (k : Fin 4 → ℤ) : Fin 4 → ℤ := Function.update k 0 (pairSwap (k 0))
theorem pairSwapHead_pairSwapHead (k : Fin 4 → ℤ) : pairSwapHead (pairSwapHead k) = k := by
  funext μ
  by_cases h : μ = 0
  · subst h
    simp [pairSwapHead, pairSwap_pairSwap]
  · simp [pairSwapHead, Function.update_of_ne h]
theorem tileSign_pairSwapHead (k k' : Fin 4 → ℤ) :
    tileSign k (pairSwapHead k') = -tileSign k k' := by
  have e0 : pairSwapHead k' 0 = pairSwap (k' 0) := by simp [pairSwapHead]
  have e1 : pairSwapHead k' 1 = k' 1 := by simp [pairSwapHead]
  have e2 : pairSwapHead k' 2 = k' 2 := by simp [pairSwapHead]
  have e3 : pairSwapHead k' 3 = k' 3 := by simp [pairSwapHead]
  unfold tileSign
  rw [Fin.sum_univ_four, Fin.sum_univ_four, e0, e1, e2, e3]
  by_cases h : Even (k' 0)
  · rw [pairSwap_of_even h]
    have hs : k' 0 + 1 - k 0 + (k' 1 - k 1) + (k' 2 - k 2) + (k' 3 - k 3) =
        k' 0 - k 0 + (k' 1 - k 1) + (k' 2 - k 2) + (k' 3 - k 3) + 1 := by ring
    rw [hs, zpow_add_one, mul_neg_one]
  · rw [pairSwap_of_not_even h]
    have hs : k' 0 - 1 - k 0 + (k' 1 - k 1) + (k' 2 - k 2) + (k' 3 - k 3) =
        k' 0 - k 0 + (k' 1 - k 1) + (k' 2 - k 2) + (k' 3 - k 3) - 1 := by ring
    rw [hs, zpow_sub_one, inv_neg_one, mul_neg_one]
theorem pairSwapHead_mem {N : ℤ} (hN : Even N) (hc : G.tilesPerSide = N) {k : Fin 4 → ℤ}
    (h : k ∈ G.boxTileIndices) : pairSwapHead k ∈ G.boxTileIndices := by
  rw [mem_boxTileIndices G hc] at h ⊢
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simpa [pairSwapHead] using pairSwap_mem hN (h 0)
  · simpa [pairSwapHead, Function.update_of_ne hμ] using h μ
theorem ncard_boxTileIndices {N : ℤ} (h0 : 0 ≤ N) (hc : G.tilesPerSide = N) :
    (G.boxTileIndices.ncard : ℝ) = G.tilesPerSide ^ 4 := by
  have hb : G.boxTileIndices = ↑(Finset.Icc (0 : Fin 4 → ℤ) (fun _ => N - 1)) := by
    ext k'
    rw [mem_boxTileIndices G hc, Finset.mem_coe, Finset.mem_Icc, Pi.le_def, Pi.le_def]
    constructor
    · intro h
      exact ⟨fun μ => (h μ).1, fun μ => by have := (h μ).2; omega⟩
    · intro h μ
      have h1 := h.2 μ
      exact ⟨h.1 μ, by omega⟩
  have hN : ((N.toNat : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h0
  rw [hb, Set.ncard_coe_finset, Pi.card_Icc, hc]
  simp only [Pi.zero_apply, Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    sub_add_cancel, sub_zero]
  push_cast
  rw [hN]
theorem boxTilesSignBalanced {N : ℤ} (hN : Even N) (h0 : 0 ≤ N) (hc : G.tilesPerSide = N)
    (k : Fin 4 → ℤ) : G.BoxTilesSignBalanced k := by
  have hfin : G.boxTileIndices.Finite :=
    InfiniteLattice.ReflectionGrid.torusTileIndices_finite G D.m
  have hne : (1 : ℤˣ) ≠ -1 := by decide
  set A : Set (Fin 4 → ℤ) := {k' | k' ∈ G.boxTileIndices ∧ tileSign k k' = 1} with hA
  set B : Set (Fin 4 → ℤ) := {k' | k' ∈ G.boxTileIndices ∧ tileSign k k' = -1} with hB
  have hinj : Function.Injective pairSwapHead :=
    Function.Involutive.injective pairSwapHead_pairSwapHead
  have hAB : pairSwapHead '' A = B := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
      exact ⟨pairSwapHead_mem G hN hc hx, by rw [tileSign_pairSwapHead, hs]⟩
    · rintro ⟨hy, hs⟩
      refine ⟨pairSwapHead y, ⟨pairSwapHead_mem G hN hc hy, ?_⟩, pairSwapHead_pairSwapHead y⟩
      rw [tileSign_pairSwapHead, hs, neg_neg]
  have hcard : B.ncard = A.ncard := by
    rw [← hAB]
    exact Set.ncard_image_of_injective _ hinj
  have hunion : A ∪ B = G.boxTileIndices := by
    ext y
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      rcases Int.units_eq_one_or (tileSign k y) with hs | hs
      · exact Or.inl ⟨h, hs⟩
      · exact Or.inr ⟨h, hs⟩
  have hdisj : Disjoint A B :=
    Set.disjoint_left.2 fun y h1 h2 => hne (h1.2.symm.trans h2.2)
  have hsum : G.boxTileIndices.ncard = A.ncard + B.ncard := by
    rw [← hunion]
    exact Set.ncard_union_eq hdisj (hfin.subset fun _ h => h.1) (hfin.subset fun _ h => h.1)
  have hbox := ncard_boxTileIndices G h0 hc
  have hsumR : (G.boxTileIndices.ncard : ℝ) = (A.ncard : ℝ) + (B.ncard : ℝ) := by
    exact_mod_cast hsum
  have hcardR : (B.ncard : ℝ) = (A.ncard : ℝ) := by
    exact_mod_cast hcard
  refine ⟨hbox, ?_, ?_⟩
  · show (A.ncard : ℝ) = _
    linarith
  · show (B.ncard : ℝ) = _
    linarith
theorem gridGroupAndBoxTiles (hF : GridElementaryFacts)
    (hR : SymmetriesAndTorusPullback) :
    GridGroupAndBoxTiles := by
  intro D G p hp
  obtain ⟨-, -, -, hU, hG⟩ := hF D G p hp
  have hA : D.ActOnRespectsAlgebra := (hR D).2.2.2.1
  refine ⟨fun g => ⟨⟨G.toLatticeSymmetry D.isAdmissible g, rfl⟩,
      fun k => exists_tile_image G hG g k⟩,
    orientationIsHom G, tileReflectionsCompose G hU,
    fun k k' F hF' => ⟨reflectedCopy_mem_tileAlgebra G hG hU hF', reflectedCopy_self G k F,
      supNorm_reflectedCopy G hA k k' hF'.1,
      fun g k'' h => reflectedCopy_transport G hU k k' k'' F g h⟩,
    fun hside => ?_⟩
  have hev := tilesPerSideEven G hside hp
  obtain ⟨N, hNe, hN2, hc⟩ := hev.2.2
  exact ⟨hev, periodShiftsInGroup G hNe hc hG hU, tilesCongruentToBoxTile G (by omega) hc,
    fun k => boxTilesSignBalanced G hNe (by omega) hc k⟩
end MultipleReflections.BoxTileFacts
end YangMills.Construction
end
