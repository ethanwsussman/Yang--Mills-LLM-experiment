import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import YangMills.Construction.VolumeTransfer.FactsOfLatticeSymmetries
import YangMills.Construction.VolumeTransfer.FirstPropertiesOfLatticeSymmetries
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction.VolumeTransfer
open InfiniteLattice (AmbientSpace refinedLattice refinedSpacing RefinedGaugeField LatticePoint
  LatticeSymmetry)
open LatticeGeometry (diagSign diagSign_apply diagSign_mem_latticeSubgroup)
open LatticeSymmetries
namespace ReflectionTranslations
variable {L K : ℕ}
theorem mem_periodLattice_of_mem_latticeSubgroup {ℓ : ℝ} {u : AmbientSpace}
    (hu : u ∈ InfiniteLattice.latticeSubgroup ℓ) : u ∈ periodLattice ℓ := by
  obtain ⟨n, hn⟩ := hu
  exact ⟨n, fun μ => by rw [hn μ, mul_comm]⟩
theorem mem_latticeSubgroup_of_mem_periodLattice {ℓ : ℝ} {u : AmbientSpace}
    (hu : u ∈ periodLattice ℓ) : u ∈ InfiniteLattice.latticeSubgroup ℓ := by
  obtain ⟨n, hn⟩ := hu
  exact ⟨n, fun μ => by rw [hn μ, mul_comm]⟩
theorem affineMapDescendsUniquely_of {m : ℕ} (h : TorusInducedMapUnique L m K) :
    LatticeGeometry.AffineMapDescendsUniquely L m K := by
  intro ε t ht
  obtain ⟨hex, hadd, hbij⟩ := h ε t ht
  exact ⟨fun x u hu => ⟨hadd x u (mem_periodLattice_of_mem_latticeSubgroup hu),
    mem_latticeSubgroup_of_mem_periodLattice
      (hbij.mapsTo (mem_periodLattice_of_mem_latticeSubgroup hu))⟩, hex⟩
theorem pullback_comp {Y : LatticeGeometry L K} {r r' : Y.Point → Y.Point}
    (hr : Y.MapsLinks r) (hr' : Y.MapsLinks r')
    (hrr' : Y.MapsLinks (r ∘ r')) (U : Y.Field) :
    LatticeGeometry.pullback hr' (LatticeGeometry.pullback hr U) =
      LatticeGeometry.pullback hrr' U := by
  refine Y.linkValue_injective _ _ fun b => ?_
  rw [LatticeGeometry.linkValue_pullback, LatticeGeometry.linkValue_pullback,
    LatticeGeometry.linkValue_pullback]
  congr 1
  refine Y.link_ext _ _ ?_ ?_
  · rw [LatticeGeometry.src_imageLink, LatticeGeometry.src_imageLink,
      LatticeGeometry.src_imageLink]
    rfl
  · rw [LatticeGeometry.tgt_imageLink, LatticeGeometry.tgt_imageLink,
      LatticeGeometry.tgt_imageLink]
    rfl
theorem symmetriesFormGroup_of {Y : LatticeGeometry L K} (hi : SymmetryInvertible Y)
    (hc : SymmetryComp Y) : Y.SymmetriesFormGroup := by
  rintro r ε t ⟨ht, hr⟩
  obtain ⟨honto, -, hbij, s, -, hs, hl, hri⟩ := hi ε t ht r hr
  refine ⟨honto, hbij, ⟨s, ⟨neg_mem (diagSign_mem_latticeSubgroup ε⁻¹ ht), fun x => ?_⟩, hl, hri⟩, ?_⟩
  · exact (hs x).trans (by simp only [sub_eq_add_neg])
  · rintro r' ε' t' ⟨ht', hr'⟩
    refine ⟨⟨add_mem (diagSign_mem_latticeSubgroup ε ht') ht, (hc ε ε' t ht t' ht' r r' hr hr').2⟩,
      fun h₁ h₂ h₃ F => ?_⟩
    funext U
    change F (LatticeGeometry.pullback h₂ (LatticeGeometry.pullback h₁ U)) =
      F (LatticeGeometry.pullback h₃ U)
    rw [pullback_comp]
theorem symmetriesPreserveDistances_of (h : EuclideanSymmetryIsometry L K) :
    LatticeGeometry.SymmetriesPreserveDistances L K :=
  fun r hr x y => ⟨(h r hr x y).2.2, (h r hr x y).1, (h r hr x y).2.1⟩
theorem symmetriesPreserveTorusDistances_of {m : ℕ} (h : TorusSymmetryIsometry L m K) :
    LatticeGeometry.SymmetriesPreserveTorusDistances L m K := by
  rintro r ⟨ε, t, ht, hr⟩ x y
  obtain ⟨h₁, h₂, h₃, -⟩ := h ε t ht r hr x y
  exact ⟨h₃, h₁, h₂⟩
theorem exists_int_mul_refinedSpacing {lc : ℝ} (hL : 0 < L)
    (hc : ReflectionPositivity.Chessboard.IsCellSideOf L lc) :
    ∃ p : ℤ, lc = p * refinedSpacing L K := by
  obtain ⟨i, rfl⟩ := hc
  refine ⟨(L : ℤ) ^ (i + K), ?_⟩
  rw [refinedSpacing, PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
def axisSignFlip (μ : Fin 4) : Fin 4 → ℤˣ := fun ν => if ν = μ then -1 else 1
theorem reflect_eq_sub_smul (lc : ℝ) (μ : Fin 4) (ι : ℤ) (x : AmbientSpace) :
    FaceReflections.reflect L K lc μ ι x =
      x - (2 * (x μ - (ι * lc - 1 / 2 * refinedSpacing L K))) • BoxTorus.basisVector μ := by
  unfold FaceReflections.reflect
  congr 2
  ring
theorem reflect_isReflectionTranslation {lc : ℝ} {p : ℤ} (hp : lc = p * refinedSpacing L K)
    (μ : Fin 4) (ι : ℤ) :
    (LatticeGeometry.euclidean L K).IsReflectionTranslation (FaceReflections.reflect L K lc μ ι) := by
  refine ⟨axisSignFlip μ, Pi.single μ (((2 * ι * p - 1 : ℤ) : ℝ) * refinedSpacing L K),
    ⟨Pi.single μ (2 * ι * p - 1), fun ν => ?_⟩, fun x => ?_⟩
  · by_cases h : ν = μ
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  · change FaceReflections.reflect L K lc μ ι x =
      diagSign (axisSignFlip μ) x + Pi.single μ (((2 * ι * p - 1 : ℤ) : ℝ) * refinedSpacing L K)
    funext ν
    by_cases h : ν = μ
    · subst h
      simp [FaceReflections.reflect, diagSign_apply, axisSignFlip,
        BoxTorus.basisVector, hp]
      ring
    · simp [FaceReflections.reflect, diagSign_apply, axisSignFlip,
        BoxTorus.basisVector, h]
theorem reflectEquiv_inv (lc : ℝ) (μ : Fin 4) (ι : ℤ) :
    (FaceReflections.reflectEquiv L K lc μ ι)⁻¹ =
      FaceReflections.reflectEquiv L K lc μ ι := by
  refine inv_eq_of_mul_eq_one_left ?_
  refine AffineEquiv.ext fun x => ?_
  change FaceReflections.reflect L K lc μ ι
    (FaceReflections.reflect L K lc μ ι x) = x
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [FaceReflections.reflect, BoxTorus.basisVector]
    ring
  · simp [FaceReflections.reflect, BoxTorus.basisVector, Pi.single_eq_of_ne h]
def reflectionProduct (L K : ℕ) (lc : ℝ) (l : List (Fin 4 × ℤ)) : AmbientSpace ≃ᵃ[ℝ] AmbientSpace :=
  (l.map fun p => FaceReflections.reflectEquiv L K lc p.1 p.2).prod
theorem reflectionProduct_inv (lc : ℝ) (l : List (Fin 4 × ℤ)) :
    (reflectionProduct L K lc l)⁻¹ = reflectionProduct L K lc l.reverse := by
  induction l with
  | nil => simp [reflectionProduct]
  | cons a l ih =>
    have hih : ((l.map fun p => FaceReflections.reflectEquiv L K lc p.1 p.2).prod)⁻¹ =
        (l.reverse.map fun p => FaceReflections.reflectEquiv L K lc p.1 p.2).prod := ih
    simp only [reflectionProduct, List.map_cons, List.prod_cons, mul_inv_rev, List.reverse_cons,
      List.map_append, List.prod_append, List.map_nil, List.prod_nil, mul_one, hih,
      reflectEquiv_inv]
theorem exists_list_of_mem_reflectionGroup {lc : ℝ} {r : AmbientSpace ≃ᵃ[ℝ] AmbientSpace}
    (hr : r ∈ FaceReflections.reflectionGroup L K lc) :
    ∃ l : List (Fin 4 × ℤ), r = reflectionProduct L K lc l := by
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨[p], by simp [reflectionProduct]⟩
  | one => exact ⟨[], rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨l', rfl⟩ := hy
    exact ⟨l ++ l', by simp [reflectionProduct]⟩
  | inv x _ hx =>
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l.reverse, reflectionProduct_inv lc l⟩
theorem diagSign_one_apply (x : AmbientSpace) : diagSign 1 x = x := by
  funext μ
  simp [diagSign_apply]
theorem reflectionProduct_isReflectionTranslation {lc : ℝ} {p : ℤ}
    (hp : lc = p * refinedSpacing L K)
    (hc : SymmetryComp (LatticeGeometry.euclidean L K)) (l : List (Fin 4 × ℤ)) :
    (LatticeGeometry.euclidean L K).IsReflectionTranslation
      (reflectionProduct L K lc l : AmbientSpace → AmbientSpace) := by
  induction l with
  | nil =>
    refine ⟨1, 0, zero_mem _, fun x => ?_⟩
    change x = diagSign 1 x + 0
    rw [diagSign_one_apply, add_zero]
  | cons a l ih =>
    obtain ⟨ε, t, ht, h⟩ := reflect_isReflectionTranslation (K := K) hp a.1 a.2
    obtain ⟨ε', t', ht', h'⟩ := ih
    exact (hc ε ε' t ht t' ht' _ _ h h').1
theorem reflectionGroupActsOnEuclidean_of {lc : ℝ} (hL : 0 < L)
    (hlc : ReflectionPositivity.Chessboard.IsCellSideOf L lc)
    (hc : SymmetryComp (LatticeGeometry.euclidean L K)) :
    LatticeGeometry.ReflectionGroupActsOnEuclidean L K lc := by
  obtain ⟨p, hp⟩ := exists_int_mul_refinedSpacing (K := K) hL hlc
  have ha : refinedSpacing L K ≠ 0 := by
    rw [refinedSpacing, PeriodicLattice.meshSize]
    exact zpow_ne_zero _ (by exact_mod_cast hL.ne')
  refine ⟨⟨p, by rw [hp]; field_simp⟩, fun μ ι => ⟨_, rfl, reflect_eq_sub_smul lc μ ι, by ring,
    ⟨2 * ι * p - 1, ?_⟩, reflect_isReflectionTranslation hp μ ι⟩, fun r hr => ?_⟩
  · rw [hp]
    push_cast
    ring
  · obtain ⟨l, rfl⟩ := exists_list_of_mem_reflectionGroup hr
    exact ⟨⟨l, rfl⟩, reflectionProduct_isReflectionTranslation hp hc l⟩
theorem reflectionGroupActsOnPeriodic_of {lc : ℝ} {m : ℕ} (hL : 0 < L)
    (hlc : ReflectionPositivity.Chessboard.IsCellSideOf L lc)
    (hc : SymmetryComp (LatticeGeometry.euclidean L K))
    (ht : TorusShiftsAreSymmetries L m K) :
    LatticeGeometry.ReflectionGroupActsOnPeriodic L m K lc := by
  refine ⟨?_, ht⟩
  rintro rbar ⟨r, hr, hind⟩
  obtain ⟨-, -, hsym⟩ := reflectionGroupActsOnEuclidean_of hL hlc hc
  obtain ⟨ε, t, ht', h⟩ := (hsym r hr).2
  refine ⟨ε, t, ht', fun x => ?_⟩
  have h₁ : rbar (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) (r x) := congrFun hind x
  have h₂ : r x = diagSign ε x + t := h x
  change rbar (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x) =
    TorusMetric.torusProj (PeriodicLattice.torusSide L m) (diagSign ε x + t)
  rw [← h₂]
  exact h₁
theorem latticeSymmetry_ext {a : ℝ} {s s' : LatticeSymmetry a} (h : s.toFun = s'.toFun) :
    s = s' := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem invarianceNotionsAgree_of (h : InvarianceNotionsAgree L K) :
    LatticeGeometry.InvarianceNotionsAgree L K := by
  have key : ∀ (ν : Measure (RefinedGaugeField L K)) [IsProbabilityMeasure ν]
      (r : AmbientSpace → AmbientSpace)
      (hr : (LatticeGeometry.euclidean L K).IsReflectionTranslation r)
      (s : LatticeSymmetry (refinedSpacing L K)), s.toFun = r →
      (IsInvariantUnderReflectionTranslation ν hr ↔ InfiniteLattice.IsSymmetricUnder ν s) := by
    intro ν _ r hr s hs
    obtain ⟨hb, s', hs', hiff⟩ := h r hr
    have hss : s = s' := latticeSymmetry_ext (hs.trans hs'.symm)
    subst hss
    exact hiff ν
  refine ⟨fun ν _ r hr => ?_, fun ν _ v hv => key ν _ hv _ rfl⟩
  obtain ⟨-, s, hs, -⟩ := h r hr
  exact ⟨⟨s, hs⟩, fun s' hs' => key ν r hr s' hs'⟩
theorem reflectionTranslationFacts_of_basicProperties (H : LatticeSymmetries.BasicProperties) :
    ReflectionTranslationFacts := by
  intro L hL K
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨⟨hi, hc, hiso, htr, hdet, htwo⟩, hm⟩ := H L hL K
  exact ⟨fun m => affineMapDescendsUniquely_of (hm m).1,
    ⟨symmetriesFormGroup_of hi hc, fun m => symmetriesFormGroup_of (hm m).2.1 (hm m).2.2.1⟩,
    ⟨symmetriesPreserveDistances_of hiso, fun m => symmetriesPreserveTorusDistances_of (hm m).2.2.2.1⟩,
    htr,
    fun lc hlc => ⟨reflectionGroupActsOnEuclidean_of hL0 hlc hc,
      fun m _ => reflectionGroupActsOnPeriodic_of hL0 hlc hc (hm m).2.2.2.2⟩,
    hdet, invarianceNotionsAgree_of htwo⟩
end ReflectionTranslations
end YangMills.Construction.VolumeTransfer
end
