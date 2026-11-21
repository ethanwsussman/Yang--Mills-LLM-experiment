import YangMills.Construction.Lattice.IsometryCarriesTheObjectsOfTheAverageProof
import YangMills.Construction.Lattice.LinearisedAverageOfAOneFormUnderIsometries
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set Matrices
namespace PeriodicLattice
namespace LinearAverageCovariance
variable {L m : ℕ} {j j' : ℤ}
theorem coe_shiftAcross (hL : 0 < L) (h : j ≤ j') (c : Bond L m j) (x : Site L m j') :
    ((shiftAcross c x : Site L m j') : FourTorus L m) =
      (x : FourTorus L m) + ((c.target : FourTorus L m) - (c.source : FourTorus L m)) := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.coe_shiftAcross <;> assumption
theorem bondForm_mem_traceless {A : Bond L m j → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A) (b : Bond L m j) :
    A b ∈ ComplexMatrix2.traceless := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · exact hA.1 b ⟨μ, h⟩
  · have hr : b.opposite.IsPositivelyOriented := ⟨μ, by
      show b.source - b.target = unitStep L m j μ
      rw [← neg_sub, h, neg_neg]⟩
    have h1 : A b.opposite ∈ ComplexMatrix2.traceless := hA.1 _ hr
    rw [hA.2 b] at h1
    simpa using ComplexMatrix2.traceless.neg_mem h1
theorem bondFormSumAlong_mem {A : Bond L m j → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A)
    (Γ : List (Bond L m j)) : bondFormSumAlong A Γ ∈ ComplexMatrix2.traceless := by
  refine list_sum_mem fun a ha => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
  exact bondForm_mem_traceless hA b
theorem contourFormAverage_mem {A : Bond L m j' → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A)
    (y : Site L m j) (x : Site L m j') : contourFormAverage A y x ∈ ComplexMatrix2.traceless :=
  ComplexMatrix2.traceless.smul_mem _
    (ComplexMatrix2.traceless.sum_mem fun _ _ => bondFormSumAlong_mem hA _)
theorem linearBlockSum_mem {A : Bond L m j' → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A)
    (c : Bond L m j) : linearBlockSum A c ∈ ComplexMatrix2.traceless := by
  unfold linearBlockSum
  refine finsum_mem_induction (· ∈ ComplexMatrix2.traceless) ComplexMatrix2.traceless.zero_mem
    (fun _ _ => ComplexMatrix2.traceless.add_mem) fun x _ => ?_
  exact ComplexMatrix2.traceless.sub_mem
    (ComplexMatrix2.traceless.add_mem (contourFormAverage_mem hA _ _) (bondFormSumAlong_mem hA _))
    (contourFormAverage_mem hA _ _)
theorem shiftAcross_mem_sitesInBlock (hL : 0 < L) (c : Bond L m j) {x : Site L m (j + 1)}
    (hx : x ∈ sitesInBlock (j + 1) c.source) :
    shiftAcross c x ∈ sitesInBlock (j + 1) c.target := by
  have hj : j ≤ j + 1 := by omega
  refine ⟨?_, ?_⟩
  · have h1 : (x : FourTorus L m) ∈ cubeAround c.source := hx.1
    show TorusMetric.torusSupNorm _ ≤ _
    have h2 : ((shiftAcross c x : Site L m (j + 1)) : FourTorus L m) -
        (c.target : FourTorus L m) = (x : FourTorus L m) - (c.source : FourTorus L m) := by
      rw [coe_shiftAcross hL hj]; abel
    rw [h2]
    exact h1
  · simp
theorem shiftAcross_opposite_shiftAcross (hL : 0 < L) (c : Bond L m j) (x : Site L m (j + 1)) :
    shiftAcross c.opposite (shiftAcross c x) = x := by
  have hj : j ≤ j + 1 := by omega
  apply Subtype.ext
  rw [coe_shiftAcross hL hj, coe_shiftAcross hL hj]
  show (x : FourTorus L m) + ((c.target : FourTorus L m) - c.source) +
    ((c.source : FourTorus L m) - c.target) = x
  abel
theorem shiftAcross_shiftAcross_opposite (hL : 0 < L) (c : Bond L m j) (x : Site L m (j + 1)) :
    shiftAcross c (shiftAcross c.opposite x) = x := by
  have hj : j ≤ j + 1 := by omega
  apply Subtype.ext
  rw [coe_shiftAcross hL hj, coe_shiftAcross hL hj]
  show (x : FourTorus L m) + ((c.source : FourTorus L m) - c.target) +
    ((c.target : FourTorus L m) - c.source) = x
  abel
theorem shiftAcross_bijOn (hL : 0 < L) (c : Bond L m j) :
    BijOn (shiftAcross c) (sitesInBlock (j + 1) c.source) (sitesInBlock (j + 1) c.target) :=
  InvOn.bijOn (f' := shiftAcross c.opposite)
    ⟨fun x _ => shiftAcross_opposite_shiftAcross hL c x,
      fun x _ => shiftAcross_shiftAcross_opposite hL c x⟩
    (fun _ hx => shiftAcross_mem_sitesInBlock hL c hx)
    (fun _ hx => shiftAcross_mem_sitesInBlock hL c.opposite hx)
theorem zsmul_unitStep_succ (hL : 0 < L) (μ : Fin 4) :
    (((L : ℤ) • unitStep L m (j + 1) μ : Site L m (j + 1)) : FourTorus L m) =
      ((unitStep L m j μ : Site L m j) : FourTorus L m) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryImages.coe_zsmul_unitStep_succ <;> assumption
theorem crossingPath_axial (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hj : 0 ≤ j) (c : Bond L m j) :
    ∃ (μ : Fin 4) (n : ℤ), ∀ x : Site L m (j + 1),
      IsAxialDisplacement x (shiftAcross c x) μ n := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hle : j ≤ j + 1 := by omega
  have hbound : ((|(L : ℤ)| : ℤ) : ℝ) < (L : ℝ) ^ ((m : ℤ) + (j + 1)) := by
    have h13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
    have h2 : (2 : ℤ) ≤ (m : ℤ) + (j + 1) := by omega
    have h3 : (L : ℝ) ^ (2 : ℤ) ≤ (L : ℝ) ^ ((m : ℤ) + (j + 1)) :=
      zpow_le_zpow_right₀ (by linarith) h2
    have h4 : (L : ℝ) < (L : ℝ) ^ (2 : ℤ) := by
      rw [zpow_ofNat]; nlinarith
    have h5 : ((|(L : ℤ)| : ℤ) : ℝ) = (L : ℝ) := by simp
    rw [h5]; linarith
  obtain ⟨μ, h | h⟩ := c.isNeighbour
  · refine ⟨μ, L, fun x => ⟨Subtype.ext ?_, hbound⟩⟩
    rw [AddSubgroup.coe_sub, coe_shiftAcross hL0 hle, zsmul_unitStep_succ hL0, ← h,
      AddSubgroup.coe_sub]
    abel
  · refine ⟨μ, -L, fun x => ⟨Subtype.ext ?_, by simpa using hbound⟩⟩
    rw [AddSubgroup.coe_sub, coe_shiftAcross hL0 hle, neg_smul, AddSubgroup.coe_neg,
      zsmul_unitStep_succ hL0, ← AddSubgroup.coe_neg, ← h, AddSubgroup.coe_sub]
    abel
theorem finsum_mem_neg_matrix {α : Type*} (s : Set α) (f : α → ComplexMatrix2) :
    ∑ᶠ x ∈ s, -f x = -∑ᶠ x ∈ s, f x := by
  rw [finsum_mem_def, finsum_mem_def, ← finsum_neg_distrib]
  exact finsum_congr fun x => by by_cases h : x ∈ s <;> simp [h]
theorem linearBlockSum_opposite (hstraight : AxialPathReversal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : 0 ≤ j)
    {A : Bond L m (j + 1) → ComplexMatrix2} (hA : IsBondForm complexLieAlgebra A)
    (c : Bond L m j) :
    linearBlockSum A c.opposite = -linearBlockSum A c := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨μ, n, hd⟩ := crossingPath_axial hL hm hj c
  unfold linearBlockSum
  rw [← finsum_mem_neg_matrix]
  symm
  refine finsum_mem_eq_of_bijOn (shiftAcross c) (shiftAcross_bijOn hL0 c) fun x _ => ?_
  have hx : bondFormSumAlong A (crossingPath c.opposite (shiftAcross c x)) =
      -bondFormSumAlong A (crossingPath c x) := by
    have h := (hstraight L m hL hm (j + 1) (by omega) x (shiftAcross c x) μ n (hd x)).2.2.2 A hA
    unfold crossingPath
    rw [shiftAcross_opposite_shiftAcross hL0 c x]
    exact h
  show _ = contourFormAverage A c.target (shiftAcross c x) + _ -
    contourFormAverage A c.source _
  rw [hx, shiftAcross_opposite_shiftAcross hL0 c x]
  abel
theorem bondFormSumAlong_pathImage {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : ∀ b : Bond L m j, bondPreimage σ (bondImage σ b) = b)
    (A : Bond L m j → ComplexMatrix2) (Γ : List (Bond L m j)) :
    bondFormSumAlong (transportForm σ A) (pathImage σ Γ) = bondFormSumAlong A Γ := by
  simp [bondFormSumAlong, pathImage, transportForm, List.map_map, Function.comp_def, hσ]
theorem bondPreimage_bondImage {σ : FourTorus L m ≃ FourTorus L m} (b : Bond L m j)
    (hb : ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
      ((bondImage σ b).target : FourTorus L m) = σ b.target) :
    bondPreimage σ (bondImage σ b) = b := by
  have hex : ∃ b' : Bond L m j, (b'.source : FourTorus L m) = σ.symm (bondImage σ b).source ∧
      (b'.target : FourTorus L m) = σ.symm (bondImage σ b).target :=
    ⟨b, by simp [hb.1], by simp [hb.2]⟩
  rw [bondPreimage, dif_pos hex]
  have hs := hex.choose_spec
  refine Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [hs.1, hb.1, Equiv.symm_apply_apply]
  · rw [hs.2, hb.2, Equiv.symm_apply_apply]
theorem coe_sitePreimage {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : σ '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j) (y : Site L m j) :
    ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryImages.coe_sitePreimage_symm <;> assumption
theorem contourFormAverage_image {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : ∀ b : Bond L m j', bondPreimage σ (bondImage σ b) = b)
    (A : Bond L m j' → ComplexMatrix2) (y : Site L m j) (x : Site L m j')
    (h : IsometryImages.MapsContourIndices σ y x) :
    contourFormAverage (transportForm σ A) (sitePreimage σ.symm y) (sitePreimage σ.symm x) =
      contourFormAverage A y x := by
  obtain ⟨e, he⟩ := h
  unfold contourFormAverage
  rw [← Fintype.card_congr e, ← Equiv.sum_comp e]
  simp only [he, bondFormSumAlong_pathImage hσ]
end LinearAverageCovariance
open LinearAverageCovariance in
theorem linearAverageIsometryCovariance_holds
    (hObjects : IsometryImages.Statement)
    (hGroups : LatticeIsometryGroupActionStatement)
    (hStraight : AxialPathReversal) :
    LinearAverageIsometryCovariance := by
  intro L m hL hm j j' hj hj'
  subst hj'
  have hL0 : 0 < L := by have := hL.2; omega
  refine ⟨fun A hA => ⟨⟨fun b _ => ?_, fun b => ?_⟩, ⟨fun b _ => ?_, fun b => ?_⟩⟩, ?_⟩
  · exact ComplexMatrix2.traceless.smul_mem _ (linearBlockSum_mem hA b)
  · show _ • linearBlockSum A b.opposite = -(_ • linearBlockSum A b)
    rw [linearBlockSum_opposite hStraight hL hm hj hA b, smul_neg]
  · exact ComplexMatrix2.traceless.smul_mem _ (linearBlockSum_mem hA b)
  · show _ • linearBlockSum A b.opposite = -(_ • linearBlockSum A b)
    rw [linearBlockSum_opposite hStraight hL hm hj hA b, smul_neg]
  intro i hi hij σ hσ A c
  have hC : ∀ k : ℤ, i ≤ k → MapsCellsAndCubes σ k := fun k hk =>
    ((hGroups L m i hL hm hi).2.2.2.2 σ hσ k hk).1
  have hends : ∀ (k : ℤ), i ≤ k → ∀ b : Bond L m k,
      ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
        ((bondImage σ b).target : FourTorus L m) = σ b.target :=
    fun k hk => (hC k hk).2.2.2.1
  have hpull : ∀ b : Bond L m (j + 1), bondPreimage σ (bondImage σ b) = b :=
    fun b => bondPreimage_bondImage b (hends _ (by omega) b)
  have hsite : ∀ y : Site L m j,
      ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y :=
    coe_sitePreimage (hC j hij).1
  have hsource : (bondImage σ c).source = sitePreimage σ.symm c.source :=
    Subtype.ext (by rw [(hends j hij c).1, hsite])
  have htarget : (bondImage σ c).target = sitePreimage σ.symm c.target :=
    Subtype.ext (by rw [(hends j hij c).2, hsite])
  obtain ⟨hsites, hbonds⟩ := hObjects L m hL hm i hi σ hσ j (j + 1) hij hj rfl
  have hcross := (hbonds c).1
  unfold linearBlockSum
  rw [hsource, htarget]
  symm
  refine finsum_mem_eq_of_bijOn (sitePreimage σ.symm) (hsites c.source).1 fun x hx => ?_
  have hx' : shiftAcross c x ∈ sitesInBlock (j + 1) c.target :=
    shiftAcross_mem_sitesInBlock hL0 c hx
  rw [← (hcross x).1, ← (hcross x).2, bondFormSumAlong_pathImage hpull,
    contourFormAverage_image hpull A _ _ ((hsites c.source).2 x hx),
    contourFormAverage_image hpull A _ _ ((hsites c.target).2 _ hx')]
end PeriodicLattice
end YangMills.Construction
