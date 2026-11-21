import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegionsProof
import YangMills.Construction.TorusOrFourSpace.GroupOfAdicIsometriesAndItsActions
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.AdicIsometryGroup
open YangMills.Construction.PeriodicLattice (SignedFrame)
open YangMills.Construction.PeriodicSpace.SupportAdapted
open YangMills.Construction.PeriodicSpace.WellPosedness
  (QuotMapSurjectiveHomWithKernel QuotDistEqMinTranslateNorm translateNorms)
open YangMills.Construction.PeriodicSpace.AdicInducedMaps
  (shiftedFrameMap ExistsUniqueDescended FrameMovesPeriods AdicIsoEqFrameAddConst)
variable (D : Params) (E : Kind)
private theorem sf_apply (r : SignedFrame) (v : Fin 4 → ℝ) (μ : Fin 4) :
    r.actOnVector v μ = ((r.2 μ : ℤ) : ℝ) * v (r.1 μ) := rfl
private theorem sf_add (r : SignedFrame) (x y : Fin 4 → ℝ) :
    r.actOnVector (x + y) = r.actOnVector x + r.actOnVector y := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.actOnVector_add <;> assumption
private theorem sf_sub (r : SignedFrame) (x y : Fin 4 → ℝ) :
    r.actOnVector (x - y) = r.actOnVector x - r.actOnVector y := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.actOnVector_sub <;> assumption
private theorem sf_neg (r : SignedFrame) (x : Fin 4 → ℝ) :
    r.actOnVector (-x) = -r.actOnVector x := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.actOnVector_neg <;> assumption
private theorem sf_one (x : Fin 4 → ℝ) : (1 : SignedFrame).actOnVector x = x := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.actOnVector_one <;> assumption
private def sfMul (r₁ r₂ : SignedFrame) : SignedFrame :=
  (r₂.1 * r₁.1, fun μ => r₁.2 μ * r₂.2 (r₁.1 μ))
private theorem sfMul_apply (r₁ r₂ : SignedFrame) (x : Fin 4 → ℝ) :
    (sfMul r₁ r₂).actOnVector x = r₁.actOnVector (r₂.actOnVector x) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.frameComp_actOnVector <;> assumption
private theorem euclidNormVec_sf (r : SignedFrame) (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (r.actOnVector v) = TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.euclidNormVec_actOnVector <;> assumption
private theorem param_L_ne_zero : (D.L : ℝ) ≠ 0 := by
  have h13 := D.isAdmissible.2
  exact Nat.cast_ne_zero.2 (by omega)
private theorem mesh_add (k k' : ℕ) :
    PeriodicLattice.meshSize D.L ((k + k' : ℕ) : ℤ) =
      PeriodicLattice.meshSize D.L (k : ℤ) * PeriodicLattice.meshSize D.L (k' : ℤ) := by
  simp only [PeriodicLattice.meshSize]
  push_cast
  rw [neg_add, zpow_add₀ (param_L_ne_zero D)]
private theorem mesh_mul_pow (k : ℕ) :
    PeriodicLattice.meshSize D.L (k : ℤ) * (D.L : ℝ) ^ k = 1 := by
  simp only [PeriodicLattice.meshSize]
  rw [zpow_neg, zpow_natCast]
  exact inv_mul_cancel₀ (pow_ne_zero _ (param_L_ne_zero D))
private theorem grid_add {x y : ℝ} (hx : x ∈ PeriodicLattice.adicGridPoints D.L)
    (hy : y ∈ PeriodicLattice.adicGridPoints D.L) :
    x + y ∈ PeriodicLattice.adicGridPoints D.L := by
  obtain ⟨k, n, rfl⟩ := (PeriodicLattice.mem_adicGridPoints_iff D.L x).1 hx
  obtain ⟨k', n', rfl⟩ := (PeriodicLattice.mem_adicGridPoints_iff D.L y).1 hy
  refine (PeriodicLattice.mem_adicGridPoints_iff D.L _).2
    ⟨k + k', n * (D.L : ℤ) ^ k' + n' * (D.L : ℤ) ^ k, ?_⟩
  rw [mesh_add]
  have h₁ := mesh_mul_pow D k
  have h₂ := mesh_mul_pow D k'
  push_cast
  linear_combination (-(n : ℝ) * PeriodicLattice.meshSize D.L (k : ℤ)) * h₂ +
    (-(n' : ℝ) * PeriodicLattice.meshSize D.L (k' : ℤ)) * h₁
private theorem grid_mul {x y : ℝ} (hx : x ∈ PeriodicLattice.adicGridPoints D.L)
    (hy : y ∈ PeriodicLattice.adicGridPoints D.L) :
    x * y ∈ PeriodicLattice.adicGridPoints D.L := by
  obtain ⟨k, n, rfl⟩ := (PeriodicLattice.mem_adicGridPoints_iff D.L x).1 hx
  obtain ⟨k', n', rfl⟩ := (PeriodicLattice.mem_adicGridPoints_iff D.L y).1 hy
  refine (PeriodicLattice.mem_adicGridPoints_iff D.L _).2 ⟨k + k', n * n', ?_⟩
  rw [mesh_add]
  push_cast
  ring
private theorem grid_neg {x : ℝ} (hx : x ∈ PeriodicLattice.adicGridPoints D.L) :
    -x ∈ PeriodicLattice.adicGridPoints D.L := by
  obtain ⟨k, n, rfl⟩ := (PeriodicLattice.mem_adicGridPoints_iff D.L x).1 hx
  refine (PeriodicLattice.mem_adicGridPoints_iff D.L _).2 ⟨k, -n, ?_⟩
  push_cast
  ring
private theorem grid_zero : (0 : ℝ) ∈ PeriodicLattice.adicGridPoints D.L :=
  (PeriodicLattice.mem_adicGridPoints_iff D.L 0).2 ⟨0, 0, by simp⟩
private theorem grid_one : (1 : ℝ) ∈ PeriodicLattice.adicGridPoints D.L :=
  (PeriodicLattice.mem_adicGridPoints_iff D.L 1).2 ⟨0, 1, by simp [PeriodicLattice.meshSize]⟩
private theorem grid_exists_rat {x : ℝ} (hx : x ∈ PeriodicLattice.adicGridPoints D.L) :
    ∃ p : ℚ, (p : ℝ) = x := by
  obtain ⟨k, n, rfl⟩ := (PeriodicLattice.mem_adicGridPoints_iff D.L x).1 hx
  refine ⟨(n : ℚ) * ((D.L : ℚ) ^ k)⁻¹, ?_⟩
  simp only [PeriodicLattice.meshSize]
  push_cast
  rw [zpow_neg, zpow_natCast]
private def gridSubring : Subring ℚ where
  carrier := {x | (x : ℝ) ∈ PeriodicLattice.adicGridPoints D.L}
  mul_mem' {a b} ha hb := by
    show ((a * b : ℚ) : ℝ) ∈ PeriodicLattice.adicGridPoints D.L
    rw [Rat.cast_mul]
    exact grid_mul D ha hb
  one_mem' := by
    show ((1 : ℚ) : ℝ) ∈ PeriodicLattice.adicGridPoints D.L
    rw [Rat.cast_one]
    exact grid_one D
  add_mem' {a b} ha hb := by
    show ((a + b : ℚ) : ℝ) ∈ PeriodicLattice.adicGridPoints D.L
    rw [Rat.cast_add]
    exact grid_add D ha hb
  zero_mem' := by
    show ((0 : ℚ) : ℝ) ∈ PeriodicLattice.adicGridPoints D.L
    rw [Rat.cast_zero]
    exact grid_zero D
  neg_mem' {a} ha := by
    show ((-a : ℚ) : ℝ) ∈ PeriodicLattice.adicGridPoints D.L
    rw [Rat.cast_neg]
    exact grid_neg D ha
private theorem adicRationals_holds : AdicRationalsCountableSubring D := by
  refine ⟨gridSubring D, Set.to_countable _, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := grid_exists_rat D hx
    exact ⟨p, hx, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact hp
private theorem zero_mem_grid4 : (0 : Fin 4 → ℝ) ∈ adicPoints4 D.L :=
  fun _ => grid_zero D
private theorem grid4_add {a b : Fin 4 → ℝ} (ha : a ∈ adicPoints4 D.L)
    (hb : b ∈ adicPoints4 D.L) : a + b ∈ adicPoints4 D.L :=
  fun μ => grid_add D (ha μ) (hb μ)
private theorem grid4_neg {a : Fin 4 → ℝ} (ha : a ∈ adicPoints4 D.L) :
    -a ∈ adicPoints4 D.L :=
  fun μ => grid_neg D (ha μ)
private theorem grid4_sf (w : SignedFrame) {a : Fin 4 → ℝ} (ha : a ∈ adicPoints4 D.L) :
    w.actOnVector a ∈ adicPoints4 D.L := by
  intro μ
  rw [sf_apply]
  rcases Int.units_eq_one_or (w.2 μ) with h | h
  · rw [h]
    simpa using ha (w.1 μ)
  · rw [h]
    simpa using grid_neg D (ha (w.1 μ))
private theorem frameImage_holds : FrameImageAdicPoints D := by
  intro w
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact grid4_sf D w ha
  · intro a ha
    exact ⟨_, grid4_sf D (frameInv w) ha, actOnVector_actOnVector_frameInv w a⟩
private theorem grid4_exists_rat {a : Fin 4 → ℝ} (ha : a ∈ adicPoints4 D.L) :
    ∃ c : Fin 4 → ℚ, a = fun μ => (c μ : ℝ) := by
  choose c hc using fun μ => grid_exists_rat D (ha μ)
  exact ⟨c, funext fun μ => (hc μ).symm⟩
private theorem grid4_countable : (adicPoints4 D.L).Countable := by
  have hsub : adicPoints4 D.L ⊆
      Set.range (fun (c : Fin 4 → ℚ) (μ : Fin 4) => (c μ : ℝ)) := by
    intro a ha
    obtain ⟨c, rfl⟩ := grid4_exists_rat D ha
    exact ⟨c, rfl⟩
  exact (Set.countable_range _).mono hsub
private theorem shifted_apply (a : Fin 4 → ℝ) (w : SignedFrame) (x : Fin 4 → ℝ) :
    shiftedFrameMap a w x = w.actOnVector x + a := rfl
private theorem shifted_comp (a b : Fin 4 → ℝ) (w w' : SignedFrame) :
    shiftedFrameMap a w ∘ shiftedFrameMap b w' =
      shiftedFrameMap (a + w.actOnVector b) (sfMul w w') := by
  funext x
  show w.actOnVector (w'.actOnVector x + b) + a =
    (sfMul w w').actOnVector x + (a + w.actOnVector b)
  rw [sf_add, sfMul_apply]
  abel
private def invShift (a : Fin 4 → ℝ) (w : SignedFrame) : Fin 4 → ℝ :=
  -(frameInv w).actOnVector a
private theorem shifted_comp_inv (a : Fin 4 → ℝ) (w : SignedFrame) :
    shiftedFrameMap a w ∘ shiftedFrameMap (invShift a w) (frameInv w) = id := by
  funext x
  show w.actOnVector ((frameInv w).actOnVector x + invShift a w) + a = x
  rw [sf_add, invShift, sf_neg, actOnVector_actOnVector_frameInv,
    actOnVector_actOnVector_frameInv]
  abel
private theorem inv_comp_shifted (a : Fin 4 → ℝ) (w : SignedFrame) :
    shiftedFrameMap (invShift a w) (frameInv w) ∘ shiftedFrameMap a w = id := by
  funext x
  show (frameInv w).actOnVector (w.actOnVector x + a) + invShift a w = x
  rw [sf_add, invShift, actOnVector_frameInv_actOnVector]
  abel
private theorem invShift_mem {a : Fin 4 → ℝ} (ha : a ∈ adicPoints4 D.L)
    (w : SignedFrame) : invShift a w ∈ adicPoints4 D.L :=
  grid4_neg D (grid4_sf D _ ha)
private theorem isoR4_isGroup : IsEuclidIsometryGroup (adicIsometriesR4 D.L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, w, rfl⟩
    refine ⟨Function.bijective_iff_has_inverse.2
      ⟨shiftedFrameMap (invShift a w) (frameInv w),
        congrFun (inv_comp_shifted a w), congrFun (shifted_comp_inv a w)⟩, ?_⟩
    intro x y
    show TorusMetric.euclidNormVec (shiftedFrameMap a w x - shiftedFrameMap a w y) =
      TorusMetric.euclidNormVec (x - y)
    rw [← euclidNormVec_sf w (x - y), sf_sub, shifted_apply, shifted_apply,
      add_sub_add_right_eq_sub]
  · refine ⟨0, zero_mem_grid4 D, 1, ?_⟩
    funext x
    show x = (1 : SignedFrame).actOnVector x + 0
    rw [sf_one, add_zero]
  · rintro _ ⟨a, ha, w, rfl⟩ _ ⟨b, hb, w', rfl⟩
    exact ⟨_, grid4_add D ha (grid4_sf D w hb), sfMul w w', shifted_comp a b w w'⟩
  · rintro _ ⟨a, ha, w, rfl⟩
    exact ⟨_, ⟨_, invShift_mem D ha w, _, rfl⟩, shifted_comp_inv a w, inv_comp_shifted a w⟩
private theorem isoR4_countable : (adicIsometriesR4 D.L).Countable := by
  have hsub : adicIsometriesR4 D.L ⊆
      (fun p : (Fin 4 → ℝ) × SignedFrame => translateR4 p.1 ∘ p.2.actOnVector) ''
        (adicPoints4 D.L ×ˢ Set.univ) := by
    rintro _ ⟨a, ha, w, rfl⟩
    exact ⟨(a, w), ⟨ha, trivial⟩, rfl⟩
  exact (((grid4_countable D).prod Set.countable_univ).image _).mono hsub
section Descent
variable {D E}
private theorem descended_apply {s : (Fin 4 → ℝ) → Fin 4 → ℝ} {r : E.Pt D → E.Pt D}
    (h : Kind.InducedBy D E s r) (x : Fin 4 → ℝ) :
    r (E.quotMap D x) = E.quotMap D (s x) := congrFun h x
private theorem descended_of_apply {s : (Fin 4 → ℝ) → Fin 4 → ℝ} {r : E.Pt D → E.Pt D}
    (h : ∀ x, r (E.quotMap D x) = E.quotMap D (s x)) : Kind.InducedBy D E s r :=
  funext h
private theorem descended_id : Kind.InducedBy D E id id := descended_of_apply fun _ => rfl
private theorem descended_comp {s s' t : (Fin 4 → ℝ) → Fin 4 → ℝ} {r r' : E.Pt D → E.Pt D}
    (h : Kind.InducedBy D E s r) (h' : Kind.InducedBy D E s' r') (ht : s ∘ s' = t) :
    Kind.InducedBy D E t (r ∘ r') := by
  subst ht
  refine descended_of_apply fun x => ?_
  show r (r' (E.quotMap D x)) = E.quotMap D (s (s' x))
  rw [descended_apply h' x, descended_apply h]
private theorem descended_unique (hQ : QuotMapSurjectiveHomWithKernel D E)
    {s : (Fin 4 → ℝ) → Fin 4 → ℝ} {r r' : E.Pt D → E.Pt D}
    (h : Kind.InducedBy D E s r) (h' : Kind.InducedBy D E s r') : r = r' := by
  funext y
  obtain ⟨x, rfl⟩ := hQ.2.1 y
  rw [descended_apply h x, descended_apply h' x]
private theorem descendedMap_spec {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (h : ∃ r : E.Pt D → E.Pt D, Kind.InducedBy D E s r) :
    Kind.InducedBy D E s (Kind.descendedMap D E s) := by
  unfold Kind.descendedMap
  exact Classical.epsilon_spec h
end Descent
private theorem quotIso_inverse (hQ : QuotMapSurjectiveHomWithKernel D E)
    (hEx : ExistsUniqueDescended D E) {r : E.Pt D → E.Pt D}
    (hr : r ∈ Kind.adicIsometriesQ D E) :
    ∃ b ∈ adicPoints4 D.L, ∃ w' : SignedFrame, ∃ r' : E.Pt D → E.Pt D,
      Kind.InducedBy D E (shiftedFrameMap b w') r' ∧ r ∘ r' = id ∧ r' ∘ r = id := by
  obtain ⟨_, ⟨a, ha, w, rfl⟩, hsr⟩ := hr
  obtain ⟨r', hr', -⟩ := hEx _ (invShift_mem D ha w) (frameInv w)
  refine ⟨_, invShift_mem D ha w, _, r', hr', ?_, ?_⟩
  · exact descended_unique hQ (descended_comp hsr hr' (shifted_comp_inv a w)) descended_id
  · exact descended_unique hQ (descended_comp hr' hsr (inv_comp_shifted a w)) descended_id
private theorem mem_of_descended {a : Fin 4 → ℝ} (ha : a ∈ adicPoints4 D.L) {w : SignedFrame}
    {r : E.Pt D → E.Pt D} (h : Kind.InducedBy D E (shiftedFrameMap a w) r) :
    r ∈ Kind.adicIsometriesQ D E :=
  ⟨_, ⟨a, ha, w, rfl⟩, h⟩
private theorem quotIso_inverse_mem (hQ : QuotMapSurjectiveHomWithKernel D E)
    (hEx : ExistsUniqueDescended D E) {r : E.Pt D → E.Pt D}
    (hr : r ∈ Kind.adicIsometriesQ D E) :
    ∃ r' ∈ Kind.adicIsometriesQ D E, r ∘ r' = id ∧ r' ∘ r = id := by
  obtain ⟨b, hb, w', r', hr', h₁, h₂⟩ := quotIso_inverse D E hQ hEx hr
  exact ⟨r', mem_of_descended D E hb hr', h₁, h₂⟩
private theorem quotIso_bijective (hQ : QuotMapSurjectiveHomWithKernel D E)
    (hEx : ExistsUniqueDescended D E) {r : E.Pt D → E.Pt D}
    (hr : r ∈ Kind.adicIsometriesQ D E) : Function.Bijective r := by
  obtain ⟨r', -, h₁, h₂⟩ := quotIso_inverse_mem D E hQ hEx hr
  exact Function.bijective_iff_has_inverse.2 ⟨r', congrFun h₂, congrFun h₁⟩
private theorem mem_translateNorms {x x' : Fin 4 → ℝ} {ρ : ℝ} :
    ρ ∈ translateNorms D E x x' ↔
      ∃ k ∈ E.periodGroup D, ρ = TorusMetric.euclidNormVec (x - x' - k) := Iff.rfl
private theorem translateNorms_eq (hPer : FrameMovesPeriods D E) (w : SignedFrame)
    (a x x' : Fin 4 → ℝ) :
    translateNorms D E (shiftedFrameMap a w x) (shiftedFrameMap a w x') =
      translateNorms D E x x' := by
  have hkey : ∀ k : Fin 4 → ℝ,
      TorusMetric.euclidNormVec
          (shiftedFrameMap a w x - shiftedFrameMap a w x' - w.actOnVector k) =
        TorusMetric.euclidNormVec (x - x' - k) := by
    intro k
    rw [← euclidNormVec_sf w (x - x' - k), sf_sub, sf_sub, shifted_apply,
      shifted_apply, add_sub_add_right_eq_sub]
  have hmove : ∀ (v : SignedFrame) (k : Fin 4 → ℝ), k ∈ E.periodGroup D →
      v.actOnVector k ∈ E.periodGroup D :=
    fun v k hk => (hPer 0 (zero_mem_grid4 D) v 0 k hk).2
  ext ρ
  rw [mem_translateNorms, mem_translateNorms]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨_, hmove (frameInv w) k hk, ?_⟩
    rw [← hkey, actOnVector_actOnVector_frameInv]
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, hmove w k hk, (hkey k).symm⟩
private theorem quotIso_isometry (hQ : QuotMapSurjectiveHomWithKernel D E)
    (hLeast : QuotDistEqMinTranslateNorm D E) (hPer : FrameMovesPeriods D E)
    {r : E.Pt D → E.Pt D} (hr : r ∈ Kind.adicIsometriesQ D E) : IsQuotIsometry D E r := by
  obtain ⟨_, ⟨a, ha, w, rfl⟩, hs⟩ := hr
  intro y y'
  obtain ⟨x, rfl⟩ := hQ.2.1 y
  obtain ⟨x', rfl⟩ := hQ.2.1 y'
  rw [descended_apply hs x, descended_apply hs x']
  have h₁ := hLeast (shiftedFrameMap a w x) (shiftedFrameMap a w x')
  rw [translateNorms_eq D E hPer w a x x'] at h₁
  exact h₁.unique (hLeast x x')
private theorem continuous_of_isometry {r : E.Pt D → E.Pt D} (h : IsQuotIsometry D E r) :
    MetricNotions.IsContinuousWrt (Kind.quotDist D E) (Kind.quotDist D E) r := by
  intro x ε hε
  refine ⟨ε, hε, fun y hy => ?_⟩
  rw [h x y]
  exact hy
private theorem quotIso_isGroup (hQ : QuotMapSurjectiveHomWithKernel D E)
    (hLeast : QuotDistEqMinTranslateNorm D E) (hPer : FrameMovesPeriods D E)
    (hEx : ExistsUniqueDescended D E) : IsQuotIsometryGroup D E (Kind.adicIsometriesQ D E) := by
  refine ⟨fun r hr => ⟨quotIso_bijective D E hQ hEx hr, quotIso_isometry D E hQ hLeast hPer hr⟩,
    ⟨id, (isoR4_isGroup D).2.1, descended_id⟩, ?_, fun r hr => quotIso_inverse_mem D E hQ hEx hr⟩
  rintro r ⟨s, hs, hsr⟩ r' ⟨s', hs', hsr'⟩
  exact ⟨s ∘ s', (isoR4_isGroup D).2.2.1 s hs s' hs', descended_comp hsr hsr' rfl⟩
private theorem quotIso_countable (hQ : QuotMapSurjectiveHomWithKernel D E) :
    (Kind.adicIsometriesQ D E).Countable := by
  have hsub : Kind.adicIsometriesQ D E ⊆ Kind.descendedMap D E '' adicIsometriesR4 D.L := by
    rintro r ⟨s, hs, hsr⟩
    exact ⟨s, hs, descended_unique hQ (descendedMap_spec ⟨r, hsr⟩) hsr⟩
  exact ((isoR4_countable D).image _).mono hsub
private theorem quotIso_homeomorph (hQ : QuotMapSurjectiveHomWithKernel D E)
    (hLeast : QuotDistEqMinTranslateNorm D E) (hPer : FrameMovesPeriods D E)
    (hEx : ExistsUniqueDescended D E) {r : E.Pt D → E.Pt D}
    (hr : r ∈ Kind.adicIsometriesQ D E) : IsQuotHomeomorph D E r := by
  obtain ⟨r', hr', h₁, h₂⟩ := quotIso_inverse_mem D E hQ hEx hr
  exact ⟨r', h₁, h₂, continuous_of_isometry D E (quotIso_isometry D E hQ hLeast hPer hr),
    continuous_of_isometry D E (quotIso_isometry D E hQ hLeast hPer hr')⟩
private theorem shifted_zero_eq (w : SignedFrame) : shiftedFrameMap 0 w = w.actOnVector := by
  funext x
  rw [shifted_apply, add_zero]
private theorem signedFrameMap_descended (hEx : ExistsUniqueDescended D E) (w : SignedFrame) :
    Kind.InducedBy D E w.actOnVector (Kind.signedFrameMap D E w) := by
  refine descendedMap_spec ?_
  obtain ⟨r, hr, -⟩ := hEx 0 (zero_mem_grid4 D) w
  rw [shifted_zero_eq] at hr
  exact ⟨r, hr⟩
private theorem signedFrameMap_mem (hEx : ExistsUniqueDescended D E) (w : SignedFrame) :
    Kind.signedFrameMap D E w ∈ Kind.adicIsometriesQ D E := by
  refine mem_of_descended D E (zero_mem_grid4 D) (w := w) ?_
  rw [shifted_zero_eq]
  exact signedFrameMap_descended D E hEx w
private theorem translate_descended (hQ : QuotMapSurjectiveHomWithKernel D E)
    (a : Fin 4 → ℝ) :
    Kind.InducedBy D E (shiftedFrameMap a 1) (translateBy D E (E.quotMap D a)) := by
  refine descended_of_apply fun x => ?_
  rw [shifted_apply, sf_one, hQ.1]
  rfl
private theorem frameAndShifts_holds
    (hQ : QuotMapSurjectiveHomWithKernel D E) (hEx : ExistsUniqueDescended D E) :
    FrameMapsAndShiftsMem D E := by
  refine ⟨signedFrameMap_mem D E hEx, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact mem_of_descended D E ha (translate_descended D E hQ a)
private theorem descended_eq (hQ : QuotMapSurjectiveHomWithKernel D E)
    (hEx : ExistsUniqueDescended D E) {a : Fin 4 → ℝ} {w : SignedFrame} {r : E.Pt D → E.Pt D}
    (hr : Kind.InducedBy D E (shiftedFrameMap a w) r) :
    r = fun y => Kind.signedFrameMap D E w y + E.quotMap D a := by
  funext y
  obtain ⟨x, rfl⟩ := hQ.2.1 y
  rw [descended_apply hr x, descended_apply (signedFrameMap_descended D E hEx w) x,
    shifted_apply, hQ.1]
private theorem descendedShifted_holds
    (hQ : QuotMapSurjectiveHomWithKernel D E) (hEx : ExistsUniqueDescended D E) :
    DescendedShiftedFrameMap D E := by
  intro a ha w
  obtain ⟨r, hr, -⟩ := hEx a ha w
  exact descended_eq D E hQ hEx (descendedMap_spec ⟨r, hr⟩)
private theorem closure_holds (hQ : QuotMapSurjectiveHomWithKernel D E)
    (hEx : ExistsUniqueDescended D E) (hFT : AdicIsoEqFrameAddConst D E) :
    AdicIsometriesEqClosure D E := by
  have hC := frameAndShifts_holds D E hQ hEx
  apply Set.Subset.antisymm
  · intro r hr
    obtain ⟨w, b, hb, rfl⟩ := hFT r hr
    let g₁ : Equiv.Perm (E.Pt D) :=
      Equiv.ofBijective _ (quotIso_bijective D E hQ hEx (hC.1 w))
    let g₂ : Equiv.Perm (E.Pt D) :=
      Equiv.ofBijective _ (quotIso_bijective D E hQ hEx (hC.2 b hb))
    refine ⟨g₂ * g₁, ?_, ?_⟩
    · exact SetLike.mem_coe.2 (Subgroup.mul_mem _
        (Subgroup.subset_closure (Or.inr ⟨b, hb, rfl⟩))
        (Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)))
    · funext y
      rfl
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ Subgroup.closure (generators D E) := SetLike.mem_coe.1 hg
    clear hg
    show ⇑g ∈ Kind.adicIsometriesQ D E
    induction hg' using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨w, hw⟩ | ⟨a', ha', hx⟩
      · rw [hw]
        exact hC.1 w
      · rw [hx]
        exact hC.2 a' ha'
    | one => exact ⟨id, (isoR4_isGroup D).2.1, descended_id⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs, hsr⟩ := hx
      obtain ⟨s', hs', hsr'⟩ := hy
      have hxy := descended_comp hsr hsr' rfl
      exact ⟨s ∘ s', (isoR4_isGroup D).2.2.1 s hs s' hs', hxy⟩
    | inv x _ hx =>
      obtain ⟨r', hr', h₁, -⟩ := quotIso_inverse_mem D E hQ hEx hx
      have hinv : ⇑x⁻¹ = r' := by
        funext y
        apply x.injective
        exact (by simp : x (x⁻¹ y) = y).trans (congrFun h₁ y).symm
      rw [hinv]
      exact hr'
private theorem pushFnLinear_holds : PushFnLinear D E := fun _ _ =>
  { map_add := fun _ _ => rfl
    map_smul := fun _ _ => rfl }
private theorem pushFnTrans_holds : PushFnTrans D E :=
  fun _ _ _ _ _ => rfl
private theorem pushFnOfFrameMap_holds (hQ : QuotMapSurjectiveHomWithKernel D E)
    (hEx : ExistsUniqueDescended D E) : PushFnOfFrameMap D E := by
  intro w r hr f
  have hcomp : Kind.signedFrameMap D E w ∘ Kind.signedFrameMap D E (frameInv w) = id := by
    refine descended_unique hQ (descended_comp (signedFrameMap_descended D E hEx w)
      (signedFrameMap_descended D E hEx _) ?_) descended_id
    funext x
    exact actOnVector_actOnVector_frameInv w x
  funext y
  show f (r.symm y) = f (Kind.signedFrameMap D E (frameInv w) y)
  congr 1
  apply r.injective
  rw [r.apply_symm_apply, hr]
  exact (congrFun hcomp y).symm
private theorem pushFnOfTranslate_holds : PushFnOfTranslate D E := by
  intro a' _ r hr f
  funext y
  show f (r.symm y) = f (y - a')
  congr 1
  apply r.injective
  rw [r.apply_symm_apply, hr]
  exact (sub_add_cancel y a').symm
private theorem closureQ_image (r : E.Pt D ≃ E.Pt D) (hr : IsQuotIsometry D E r)
    (Z : Set (E.Pt D)) : Kind.closureQ D E (r '' Z) = r '' Kind.closureQ D E Z := by
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨r.symm x, fun ρ hρ => ?_, r.apply_symm_apply x⟩
    obtain ⟨_, ⟨z, hz, rfl⟩, hd⟩ := hx ρ hρ
    refine ⟨z, hz, ?_⟩
    rw [← hr (r.symm x) z, r.apply_symm_apply]
    exact hd
  · rintro _ ⟨x, hx, rfl⟩ ρ hρ
    obtain ⟨z, hz, hd⟩ := hx ρ hρ
    refine ⟨r z, ⟨z, hz, rfl⟩, ?_⟩
    rw [hr x z]
    exact hd
private theorem supportQ_pushFn (r : E.Pt D ≃ E.Pt D) (hr : IsQuotIsometry D E r)
    (f : E.Pt D → ℝ) :
    Kind.supportQ D E (Kind.pushFn D E r f) = r '' Kind.supportQ D E f := by
  unfold Kind.supportQ
  rw [← closureQ_image D E r hr]
  congr 1
  ext y
  constructor
  · intro h
    exact ⟨r.symm y, h, r.apply_symm_apply y⟩
  · rintro ⟨z, hz, rfl⟩
    show f (r.symm (r z)) ≠ 0
    rwa [r.symm_apply_apply]
private theorem isCompactQ_image (r : E.Pt D ≃ E.Pt D) (hr : IsQuotIsometry D E r)
    {Z : Set (E.Pt D)} (hZ : Kind.IsCompactQ D E Z) : Kind.IsCompactQ D E (r '' Z) := by
  intro U hU hcov
  obtain ⟨V, hV, hfin, hsub⟩ := hZ ((fun A => r ⁻¹' A) '' U) (by
    rintro _ ⟨A, hA, rfl⟩ x hx
    obtain ⟨ρ, hρ, hball⟩ := hU A hA (r x) hx
    refine ⟨ρ, hρ, fun y hy => hball (r y) ?_⟩
    rw [hr x y]
    exact hy) (by
    intro z hz
    obtain ⟨A, hA, hzA⟩ := hcov ⟨z, hz, rfl⟩
    exact ⟨r ⁻¹' A, ⟨A, hA, rfl⟩, hzA⟩)
  refine ⟨(fun B => r '' B) '' V, ?_, hfin.image _, ?_⟩
  · rintro _ ⟨B, hB, rfl⟩
    obtain ⟨A, hA, rfl⟩ := hV hB
    show r '' (r ⁻¹' A) ∈ U
    rwa [Set.image_preimage_eq _ r.surjective]
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨B, hB, hzB⟩ := hsub hz
    exact ⟨r '' B, ⟨B, hB, rfl⟩, z, hzB, rfl⟩
private theorem shifted_contDiff (a : Fin 4 → ℝ) (w : SignedFrame) :
    ContDiff ℝ 1 (shiftedFrameMap a w) := by
  have hw : ContDiff ℝ 1 w.actOnVector :=
    contDiff_pi.2 fun μ => contDiff_const.mul (contDiff_apply ℝ ℝ (w.1 μ))
  exact hw.add contDiff_const
private theorem pushFn_isC1 (hQ : QuotMapSurjectiveHomWithKernel D E)
    (hEx : ExistsUniqueDescended D E) (r : E.Pt D ≃ E.Pt D)
    (hr : ⇑r ∈ Kind.adicIsometriesQ D E) {f : E.Pt D → ℝ} (hf : Kind.IsC1Fn D E f) :
    Kind.IsC1Fn D E (Kind.pushFn D E r f) := by
  obtain ⟨b, -, w', r', hr', h₁, -⟩ := quotIso_inverse D E hQ hEx hr
  have hsymm : ⇑r.symm = r' := by
    funext y
    apply r.injective
    rw [r.apply_symm_apply]
    exact (congrFun h₁ y).symm
  have heq : Kind.pushFn D E r f ∘ E.quotMap D =
      (f ∘ E.quotMap D) ∘ shiftedFrameMap b w' := by
    funext x
    show f (r.symm (E.quotMap D x)) = f (E.quotMap D (shiftedFrameMap b w' x))
    rw [hsymm, descended_apply hr' x]
  unfold Kind.IsC1Fn TestFunctions.IsC1R4 at hf ⊢
  rw [heq]
  exact hf.comp (shifted_contDiff b w')
private def shiftedBox (c : Fin 4 → ℚ) (w : SignedFrame) (b : RationalBox) : RationalBox where
  lo μ := if w.2 μ = 1 then b.lo (w.1 μ) + c μ else -b.hi (w.1 μ) + c μ
  hi μ := if w.2 μ = 1 then b.hi (w.1 μ) + c μ else -b.lo (w.1 μ) + c μ
  lo_lt_hi μ := by
    have h := b.lo_lt_hi (w.1 μ)
    split_ifs <;> linarith
private theorem mem_toSet {b : RationalBox} {x : Fin 4 → ℝ} :
    x ∈ b.toSet ↔ ∀ μ, x μ ∈ Set.Icc (b.lo μ : ℝ) (b.hi μ : ℝ) := by
  unfold RationalBox.toSet
  exact Set.mem_univ_pi
private theorem shiftedBox_iff (c : Fin 4 → ℚ) (w : SignedFrame) (b : RationalBox) (μ : Fin 4)
    (t : ℝ) :
    t ∈ Set.Icc (b.lo (w.1 μ) : ℝ) (b.hi (w.1 μ) : ℝ) ↔
      ((w.2 μ : ℤ) : ℝ) * t + (c μ : ℝ) ∈
        Set.Icc ((shiftedBox c w b).lo μ : ℝ) ((shiftedBox c w b).hi μ : ℝ) := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or (w.2 μ) with h | h
  · simp only [shiftedBox, h, if_true, Set.mem_Icc]
    push_cast
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      constructor <;> linarith
  · simp only [shiftedBox, h, if_neg hne, Set.mem_Icc]
    push_cast
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      constructor <;> linarith
private theorem image_toSet (c : Fin 4 → ℚ) (w : SignedFrame) (b : RationalBox) :
    shiftedFrameMap (fun μ => (c μ : ℝ)) w '' b.toSet = (shiftedBox c w b).toSet := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_toSet.2 fun μ => (shiftedBox_iff c w b μ _).1 (mem_toSet.1 hx (w.1 μ))
  · intro z hz
    have hsx : shiftedFrameMap (fun μ => (c μ : ℝ)) w
        ((frameInv w).actOnVector (z - fun μ => (c μ : ℝ))) = z := by
      rw [shifted_apply, actOnVector_actOnVector_frameInv, sub_add_cancel]
    refine ⟨_, mem_toSet.2 fun ν => ?_, hsx⟩
    obtain ⟨μ, rfl⟩ := w.1.surjective ν
    refine (shiftedBox_iff c w b μ _).2 ?_
    have hμ := congrFun hsx μ
    rw [shifted_apply, Pi.add_apply, sf_apply] at hμ
    rw [hμ]
    exact mem_toSet.1 hz μ
private theorem diam_shiftedBox (c : Fin 4 → ℚ) (w : SignedFrame) (b : RationalBox) :
    (shiftedBox c w b).diam = b.diam := by
  unfold RationalBox.diam
  have h : (fun μ => ((shiftedBox c w b).hi μ : ℝ) - ((shiftedBox c w b).lo μ : ℝ)) =
      SignedFrame.actOnVector (w.1, 1) fun μ => (b.hi μ : ℝ) - (b.lo μ : ℝ) := by
    funext μ
    simp only [sf_apply, shiftedBox, Pi.one_apply, Units.val_one, Int.cast_one, one_mul]
    split_ifs <;> push_cast <;> ring
  rw [h, euclidNormVec_sf]
private theorem shiftedBox_admits (c : Fin 4 → ℚ) (w : SignedFrame) {b : RationalBox}
    (hb : E.AdmitsBox D b) : E.AdmitsBox D (shiftedBox c w b) := by
  cases E with
  | euclidean => trivial
  | torus =>
    show (shiftedBox c w b).diam < D.side / 2
    rw [diam_shiftedBox]
    exact hb
private theorem supportStock_holds : SupportStockInvariant D E := by
  rintro r ⟨_, ⟨a, ha, w, rfl⟩, hs⟩ Q ⟨n, b, hb, rfl⟩
  obtain ⟨c, rfl⟩ := grid4_exists_rat D ha
  refine ⟨n, fun i => shiftedBox c w (b i), fun i => shiftedBox_admits D E c w (hb i), ?_⟩
  show r '' ⋃ i, E.quotMap D '' (b i).toSet = _
  rw [Set.image_iUnion]
  refine Set.iUnion_congr fun i => ?_
  rw [← image_toSet, Set.image_image, Set.image_image]
  exact Set.image_congr fun x _ => descended_apply hs x
theorem claim_of_wellPosed (hWell : WellPosedness.WellPosed)
    (hInd : AdicInducedMaps.AdicLatticesAndInducedMaps) : Claim := by
  intro D E
  have hW := hWell D E
  have hI := hInd D E
  have hQ : QuotMapSurjectiveHomWithKernel D E := hW.1
  have hLeast : QuotDistEqMinTranslateNorm D E := hW.2.2.2.2.2.2.1
  have hPer : FrameMovesPeriods D E := hI.2.2.2.1
  have hEx : ExistsUniqueDescended D E := hI.2.2.2.2.2.1
  have hFT : AdicIsoEqFrameAddConst D E := hI.2.2.2.2.2.2.2
  have hIso : ∀ r : E.Pt D ≃ E.Pt D, ⇑r ∈ Kind.adicIsometriesQ D E → IsQuotIsometry D E r :=
    fun r hr => quotIso_isometry D E hQ hLeast hPer hr
  refine ⟨adicRationals_holds D, frameImage_holds D, ⟨isoR4_countable D, isoR4_isGroup D⟩,
    ⟨quotIso_countable D E hQ, quotIso_isGroup D E hQ hLeast hPer hEx,
      fun r hr => quotIso_homeomorph D E hQ hLeast hPer hEx hr⟩,
    frameAndShifts_holds D E hQ hEx,
    descendedShifted_holds D E hQ hEx, hFT, closure_holds D E hQ hEx hFT,
    pushFnLinear_holds D E, pushFnTrans_holds D E, pushFnOfFrameMap_holds D E hQ hEx,
    pushFnOfTranslate_holds D E, ?_, ?_, supportStock_holds D E⟩
  · exact fun r hr f => supportQ_pushFn D E r (hIso r hr) f
  · intro r hr f hf hc
    refine ⟨pushFn_isC1 D E hQ hEx r hr hf, ?_⟩
    rw [supportQ_pushFn D E r (hIso r hr) f]
    exact isCompactQ_image D E r (hIso r hr) hc
end YangMills.Construction.PeriodicSpace.AdicIsometryGroup
