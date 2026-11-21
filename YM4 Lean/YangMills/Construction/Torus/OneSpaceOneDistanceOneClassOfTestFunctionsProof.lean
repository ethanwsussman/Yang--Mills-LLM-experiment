import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.OneSpaceOneDistanceOneClassOfTestFunctions
import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsAreContinuousDifferentiability
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints.Identification
open MetricNotions
section EquivTransport
variable {X Y : Type*} {d : X → X → ℝ} {d' : Y → Y → ℝ}
theorem isOpenWrt_image_equiv (e : X ≃ Y) (h : ∀ a b, d' (e a) (e b) = d a b) (Z : Set X) :
    IsOpenWrt d' (e '' Z) ↔ IsOpenWrt d Z := by
  constructor
  · intro hZ x hx
    obtain ⟨r, hr, hy⟩ := hZ (e x) ⟨x, hx, rfl⟩
    refine ⟨r, hr, fun y hxy => ?_⟩
    obtain ⟨z, hz, hze⟩ := hy (e y) (by rwa [h])
    rwa [← e.injective hze]
  · rintro hZ _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr, hy⟩ := hZ x hx
    refine ⟨r, hr, fun y hxy => ⟨e.symm y, hy _ ?_, by simp⟩⟩
    rw [← h]
    simpa using hxy
theorem isClosedWrt_image_equiv (e : X ≃ Y) (h : ∀ a b, d' (e a) (e b) = d a b) (Z : Set X) :
    IsClosedWrt d' (e '' Z) ↔ IsClosedWrt d Z := by
  unfold IsClosedWrt
  rw [← Set.image_compl_eq e.bijective]
  exact isOpenWrt_image_equiv e h _
theorem closureWrt_image_equiv (e : X ≃ Y) (h : ∀ a b, d' (e a) (e b) = d a b) (Z : Set X) :
    closureWrt d' (e '' Z) = e '' closureWrt d Z := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, fun r hr => ?_, by simp⟩
    obtain ⟨_, ⟨z, hz, rfl⟩, hyz⟩ := hy r hr
    refine ⟨z, hz, ?_⟩
    rw [← h]
    simpa using hyz
  · rintro ⟨x, hx, rfl⟩ r hr
    obtain ⟨z, hz, hxz⟩ := hx r hr
    exact ⟨e z, ⟨z, hz, rfl⟩, by rwa [h]⟩
theorem isCompactWrt_of_image_equiv (e : X ≃ Y) (h : ∀ a b, d' (e a) (e b) = d a b) {Z : Set X}
    (hZ : IsCompactWrt d' (e '' Z)) : IsCompactWrt d Z := by
  intro 𝒰 hopen hcover
  obtain ⟨𝒱, hsub, hfin, hcov⟩ := hZ ((fun U => e '' U) '' 𝒰)
    (by
      rintro _ ⟨U, hU, rfl⟩
      exact (isOpenWrt_image_equiv e h U).2 (hopen U hU))
    (by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨U, hU, hxU⟩ := hcover hx
      exact ⟨e '' U, ⟨U, hU, rfl⟩, x, hxU, rfl⟩)
  refine ⟨(fun V => e ⁻¹' V) '' 𝒱, ?_, hfin.image _, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    obtain ⟨U, hU, rfl⟩ := hsub hV
    simpa [Set.preimage_image_eq _ e.injective] using hU
  · intro x hx
    obtain ⟨V, hV, hxV⟩ := hcov ⟨x, hx, rfl⟩
    exact ⟨e ⁻¹' V, ⟨V, hV, rfl⟩, hxV⟩
theorem isCompactWrt_image_equiv (e : X ≃ Y) (h : ∀ a b, d' (e a) (e b) = d a b) (Z : Set X) :
    IsCompactWrt d' (e '' Z) ↔ IsCompactWrt d Z := by
  refine ⟨isCompactWrt_of_image_equiv e h, fun hZ => ?_⟩
  refine isCompactWrt_of_image_equiv (d := d') (d' := d) e.symm (fun a b => ?_) (Z := e '' Z) ?_
  · rw [← h]
    simp
  · simpa [Set.image_image] using hZ
variable {d₁ d₂ : X → X → ℝ} {C : ℝ}
theorem isOpenWrt_iff_of_comparable (hC : 0 < C) (h₁ : ∀ a b, d₁ a b ≤ C * d₂ a b)
    (h₂ : ∀ a b, d₂ a b ≤ d₁ a b) (Z : Set X) : IsOpenWrt d₁ Z ↔ IsOpenWrt d₂ Z := by
  constructor
  · intro hZ x hx
    obtain ⟨r, hr, hy⟩ := hZ x hx
    refine ⟨r / C, div_pos hr hC, fun y hxy => hy y ?_⟩
    calc d₁ x y ≤ C * d₂ x y := h₁ x y
      _ < C * (r / C) := by exact mul_lt_mul_of_pos_left hxy hC
      _ = r := by field_simp
  · intro hZ x hx
    obtain ⟨r, hr, hy⟩ := hZ x hx
    exact ⟨r, hr, fun y hxy => hy y ((h₂ x y).trans_lt hxy)⟩
theorem closureWrt_eq_of_comparable (hC : 0 < C) (h₁ : ∀ a b, d₁ a b ≤ C * d₂ a b)
    (h₂ : ∀ a b, d₂ a b ≤ d₁ a b) (Z : Set X) : closureWrt d₁ Z = closureWrt d₂ Z := by
  ext x
  constructor
  · intro hx r hr
    obtain ⟨y, hy, hxy⟩ := hx r hr
    exact ⟨y, hy, (h₂ x y).trans_lt hxy⟩
  · intro hx r hr
    obtain ⟨y, hy, hxy⟩ := hx (r / C) (div_pos hr hC)
    refine ⟨y, hy, ?_⟩
    calc d₁ x y ≤ C * d₂ x y := h₁ x y
      _ < C * (r / C) := by exact mul_lt_mul_of_pos_left hxy hC
      _ = r := by field_simp
theorem isCompactWrt_iff_of_isOpenWrt_iff (h : ∀ U, IsOpenWrt d₁ U ↔ IsOpenWrt d₂ U) (Z : Set X) :
    IsCompactWrt d₁ Z ↔ IsCompactWrt d₂ Z := by
  simp only [IsCompactWrt, h]
end EquivTransport
section HeadPoint
variable {s : Conventions.StandingParameters} {E : Ambient}
def headPointHomeomorph : Tuple s E 1 ≃ₜ Pt s E := Homeomorph.funUnique (Fin 1) (Pt s E)
theorem isOpen_preimage_headPoint_iff (Z : Set (Pt s E)) : IsOpen (headPoint ⁻¹' Z) ↔ IsOpen Z :=
  headPointHomeomorph.isOpen_preimage
theorem isClosed_preimage_headPoint_iff (Z : Set (Pt s E)) :
    IsClosed (headPoint ⁻¹' Z) ↔ IsClosed Z :=
  headPointHomeomorph.isClosed_preimage
theorem isCompact_preimage_headPoint_iff (Z : Set (Pt s E)) :
    IsCompact (headPoint ⁻¹' Z) ↔ IsCompact Z :=
  headPointHomeomorph.isCompact_preimage
theorem closure_preimage_headPoint (Z : Set (Pt s E)) :
    closure (headPoint ⁻¹' Z) = headPoint ⁻¹' closure Z :=
  (headPointHomeomorph.preimage_closure Z).symm
end HeadPoint
section Projections
variable {s : Conventions.StandingParameters} {E : Ambient}
theorem quotMap_eq_proj (x : Fin 4 → ℝ) :
    (kindOf E).quotMap (paramsOf s) x = ptEquiv s E (proj s E x) := by
  cases E <;> rfl
theorem proj_surjective : Function.Surjective (proj s E) := by
  cases E
  · intro y
    obtain ⟨b, hb, -⟩ := exists_torusProj_eq_euclidNormVec_eq (S := PeriodicLattice.torusSide s.L s.m) y
    exact ⟨b, hb⟩
  · exact fun y => ⟨y, rfl⟩
theorem torusProj_sub {S : ℝ} (x x' : Fin 4 → ℝ) :
    TorusMetric.torusProj S (x - x') = TorusMetric.torusProj S x - TorusMetric.torusProj S x' := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem torusProj_add {S : ℝ} (x x' : Fin 4 → ℝ) :
    TorusMetric.torusProj S (x + x') = TorusMetric.torusProj S x + TorusMetric.torusProj S x' := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem torusProj_of_mem_latticeSubgroup {S : ℝ} {k : Fin 4 → ℝ}
    (hk : k ∈ InfiniteLattice.latticeSubgroup S) : TorusMetric.torusProj S k = 0 := by
  obtain ⟨n, hn⟩ := hk
  have hS : ((S : ℝ) : AddCircle S) = 0 := AddCircle.coe_period S
  funext μ
  simp [TorusMetric.torusProj, hn μ, hS]
theorem quotDist_euclidean (y y' : Fin 4 → ℝ) :
    PeriodicSpace.Kind.quotDist (paramsOf s) .euclidean y y' =
      TorusMetric.euclidNormVec (y - y') := by
  unfold PeriodicSpace.Kind.quotDist
  refine (congrArg sInf ?_).trans (csInf_singleton (TorusMetric.euclidNormVec (y - y')))
  ext r
  constructor
  · rintro ⟨x, x', hx, hx', k, hk, rfl⟩
    have hk0 : k = 0 := hk
    have hx1 : x = y := hx
    have hx2 : x' = y' := hx'
    simp [hk0, hx1, hx2]
  · rintro rfl
    exact ⟨y, y', rfl, rfl, 0, rfl, by simp⟩
theorem quotDist_torus (y y' : TorusMetric.Torus4 (PeriodicLattice.torusSide s.L s.m)) :
    PeriodicSpace.Kind.quotDist (paramsOf s) .torus y y' =
      TorusMetric.torusEuclidNorm (y - y') := by
  unfold PeriodicSpace.Kind.quotDist TorusMetric.torusEuclidNorm
  congr 1
  ext r
  constructor
  · rintro ⟨x, x', hx, hx', k, hk, rfl⟩
    have hx1 : TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) x = y := hx
    have hx2 : TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) x' = y' := hx'
    refine ⟨x - x' - k, ?_, rfl⟩
    change TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) (x - x' - k) = y - y'
    rw [torusProj_sub, torusProj_sub,
      torusProj_of_mem_latticeSubgroup (S := PeriodicLattice.torusSide s.L s.m) hk, hx1, hx2,
      sub_zero]
  · rintro ⟨v, hv, rfl⟩
    have hv' : TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) v = y - y' := hv
    obtain ⟨x', hx'⟩ := proj_surjective (s := s) (E := .torus) y'
    have hx'' : TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) x' = y' := hx'
    refine ⟨v + x', x', ?_, hx', 0, zero_mem _, by simp⟩
    change TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) (v + x') = y
    rw [torusProj_add, hv', hx'', sub_add_cancel]
theorem quotDist_ptEquiv (y y' : Pt s E) :
    PeriodicSpace.Kind.quotDist (paramsOf s) (kindOf E) (ptEquiv s E y)
      (ptEquiv s E y') = pointDist s E y y' := by
  cases E
  · exact quotDist_torus y y'
  · exact quotDist_euclidean y y'
theorem quotDist_ptEquiv_eq_dist (y y' : Pt s E) :
    PeriodicSpace.Kind.quotDist (paramsOf s) (kindOf E) (ptEquiv s E y)
      (ptEquiv s E y') = dist y y' := by apply _root_.YangMills.Construction.AmbientPoints.Identification.quotDist_ptEquiv <;> assumption
end Projections
section QuotientSets
variable {s : Conventions.StandingParameters} {E : Ambient}
theorem isOpenQ_image_iff (Z : Set (Pt s E)) :
    PeriodicSpace.Kind.IsOpenQ (paramsOf s) (kindOf E) (ptEquiv s E '' Z) ↔ IsOpen Z :=
  (isOpenWrt_image_equiv (d := dist) (ptEquiv s E) quotDist_ptEquiv_eq_dist Z).trans
    (isOpen_iff_isOpenWrt Z).symm
theorem isClosedQ_image_iff (Z : Set (Pt s E)) :
    PeriodicSpace.Kind.IsClosedQ (paramsOf s) (kindOf E) (ptEquiv s E '' Z) ↔ IsClosed Z :=
  (isClosedWrt_image_equiv (d := dist) (ptEquiv s E) quotDist_ptEquiv_eq_dist Z).trans
    ((isOpen_iff_isOpenWrt Zᶜ).symm.trans isOpen_compl_iff)
theorem isCompactQ_image_iff (Z : Set (Pt s E)) :
    PeriodicSpace.Kind.IsCompactQ (paramsOf s) (kindOf E) (ptEquiv s E '' Z) ↔ IsCompact Z :=
  (isCompactWrt_image_equiv (d := dist) (ptEquiv s E) quotDist_ptEquiv_eq_dist Z).trans
    (isCompact_iff_isCompactWrt Z).symm
theorem supportQ_liftFn {Z : Type*} [Zero Z] (f : Pt s E → Z) :
    PeriodicSpace.Kind.supportQ (paramsOf s) (kindOf E) (liftFn f) =
      ptEquiv s E '' tsupport f := by
  have h : {y | liftFn f y ≠ 0} = ptEquiv s E '' Function.support f := by
    ext y
    constructor
    · intro hy
      exact ⟨(ptEquiv s E).symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [liftFn] using hx
  change closureWrt _ {y | liftFn f y ≠ 0} = _
  rw [h, closureWrt_image_equiv (d := dist) (ptEquiv s E) quotDist_ptEquiv_eq_dist,
    ← closure_eq_closureWrt]
  rfl
theorem liftFn_comp_quotMap {Z : Type*} (f : Pt s E → Z) :
    liftFn f ∘ (kindOf E).quotMap (paramsOf s) = f ∘ proj s E := by
  funext x
  simp [liftFn, quotMap_eq_proj]
end QuotientSets
section Smoothness
variable {s : Conventions.StandingParameters} {E : Ambient}
theorem contPartialsUpTo_iff_univ {p : ℕ+} (ν : ℕ) (G : PeriodicSpace.Coords p → ℂ) :
    PeriodicSpace.Coords.ContPartialsUpTo ν G ↔
      ContinuousPartialsUpTo (D := 4 * (p : ℕ)) univ ν G := by
  induction ν generalizing G with
  | zero => exact continuousOn_univ.symm
  | succ ν ih =>
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₁.continuousOn, fun j => ⟨fun x _ => (h₂ j).1 x, (ih _).1 (h₂ j).2⟩⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨continuousOn_univ.1 h₁, fun j => ⟨fun x => (h₂ j).1 x (mem_univ x),
        (ih _).2 (h₂ j).2⟩⟩
theorem isCn_iff_contPartialsUpTo {p : ℕ+} (ν : ℕ) (F : Tuple s E (p : ℕ) → ℂ) :
    IsCn (ν : ℕ∞) F ↔
      PeriodicSpace.Coords.ContPartialsUpTo (p := p) ν (F ∘ tupleProj s E (p : ℕ)) :=
  (isCnOn_coe_iff _ _ _).trans
    ⟨fun h => (contPartialsUpTo_iff_univ _ _).2 h.2,
      fun h => ⟨isOpen_univ, (contPartialsUpTo_iff_univ _ _).1 h⟩⟩
theorem isC1_iff_contDiff_comp_proj
    (hpartials : PeriodicSpace.ContPartialsIffContDiff)
    (f : Pt s E → ℝ) : IsC1 f ↔ ContDiff ℝ 1 (f ∘ proj s E) := by
  have h₁ := isCn_iff_contPartialsUpTo (s := s) (E := E) (p := 1) 1 (asFunctionOnOnePoint f)
  have h₂ := hpartials 1 1 (asFunctionOnOnePoint f ∘ tupleProj s E 1)
  have h₃ : IsC1 f ↔ ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞)
      (asFunctionOnOnePoint f ∘ tupleProj s E 1 : (Fin (4 * 1) → ℝ) → ℂ) := h₁.trans h₂
  rw [Nat.cast_one] at h₃
  refine h₃.trans ?_
  have hL : ContDiff ℝ 1 (fun x : Fin (4 * 1) → ℝ => (flattenCoords 1).symm x 0) := by
    refine contDiff_pi.2 fun μ => ?_
    exact contDiff_apply ℝ ℝ _
  have hR : ContDiff ℝ 1 (fun v : Fin 4 → ℝ => flattenCoords 1 fun _ => v) := by
    refine contDiff_pi.2 fun j => ?_
    exact contDiff_apply ℝ ℝ _
  constructor
  · intro hG
    have h := Complex.reCLM.contDiff.comp (hG.comp hR)
    convert h using 1
    funext v
    simp [asFunctionOnOnePoint, tupleProj]
  · intro hg
    exact Complex.ofRealCLM.contDiff.comp (hg.comp hL)
end Smoothness
section Tuples
variable {s : Conventions.StandingParameters} {E : Ambient} {p : ℕ+}
def l2TupleDist (s : Conventions.StandingParameters) (E : Ambient) (p : ℕ+)
    (a b : Tuple s E (p : ℕ)) : ℝ :=
  PeriodicSpace.Kind.Tuple.tupleDist (paramsOf s) (kindOf E)
    (tupleEquiv s E p a) (tupleEquiv s E p b)
theorem l2TupleDist_eq (a b : Tuple s E (p : ℕ)) :
    l2TupleDist s E p a b = Real.sqrt (∑ i, dist (a i) (b i) ^ 2) := by
  unfold l2TupleDist PeriodicSpace.Kind.Tuple.tupleDist
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [show tupleEquiv s E p a i = ptEquiv s E (a i) from rfl,
      show tupleEquiv s E p b i = ptEquiv s E (b i) from rfl, quotDist_ptEquiv_eq_dist]
theorem dist_le_l2TupleDist (a b : Tuple s E (p : ℕ)) : dist a b ≤ l2TupleDist s E p a b := by
  rw [l2TupleDist_eq]
  refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun i => ?_
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun i => dist (a i) (b i) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
theorem l2TupleDist_le (a b : Tuple s E (p : ℕ)) :
    l2TupleDist s E p a b ≤ Real.sqrt (p : ℕ) * dist a b := by
  rw [l2TupleDist_eq]
  have h : ∑ i, dist (a i) (b i) ^ 2 ≤ ((p : ℕ) : ℝ) * dist a b ^ 2 := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => dist (a i) (b i) ^ 2) (dist a b ^ 2)
      fun i _ => pow_le_pow_left₀ dist_nonneg (dist_le_pi_dist a b i) 2
    simpa using this
  calc Real.sqrt (∑ i, dist (a i) (b i) ^ 2) ≤ Real.sqrt (((p : ℕ) : ℝ) * dist a b ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt (p : ℕ) * dist a b := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq dist_nonneg]
theorem sqrt_card_pos : 0 < Real.sqrt ((p : ℕ) : ℝ) :=
  Real.sqrt_pos.2 (by exact_mod_cast p.pos)
theorem isOpenWrt_l2TupleDist_iff (Z : Set (Tuple s E (p : ℕ))) :
    IsOpenWrt (l2TupleDist s E p) Z ↔ IsOpen Z :=
  (isOpenWrt_iff_of_comparable sqrt_card_pos l2TupleDist_le dist_le_l2TupleDist Z).trans
    (isOpen_iff_isOpenWrt Z).symm
theorem isOpenT_image_iff (Z : Set (Tuple s E (p : ℕ))) :
    PeriodicSpace.Kind.Tuple.IsOpenT (paramsOf s) (kindOf E) (tupleEquiv s E p '' Z) ↔ IsOpen Z :=
  (isOpenWrt_image_equiv (d := l2TupleDist s E p) (tupleEquiv s E p) (fun _ _ => rfl) Z).trans
    (isOpenWrt_l2TupleDist_iff Z)
theorem isClosedT_image_iff (Z : Set (Tuple s E (p : ℕ))) :
    PeriodicSpace.Kind.Tuple.IsClosedT (paramsOf s) (kindOf E) (tupleEquiv s E p '' Z) ↔
      IsClosed Z :=
  (isClosedWrt_image_equiv (d := l2TupleDist s E p) (tupleEquiv s E p) (fun _ _ => rfl) Z).trans
    ((isOpenWrt_l2TupleDist_iff Zᶜ).trans isOpen_compl_iff)
theorem isCompactT_image_iff (Z : Set (Tuple s E (p : ℕ))) :
    PeriodicSpace.Kind.Tuple.IsCompactT (paramsOf s) (kindOf E) (tupleEquiv s E p '' Z) ↔
      IsCompact Z :=
  (isCompactWrt_image_equiv (d := l2TupleDist s E p) (tupleEquiv s E p) (fun _ _ => rfl) Z).trans
    ((isCompactWrt_iff_of_isOpenWrt_iff
      (isOpenWrt_iff_of_comparable sqrt_card_pos l2TupleDist_le dist_le_l2TupleDist) Z).trans
      (isCompact_iff_isCompactWrt Z).symm)
theorem closureT_image (Z : Set (Tuple s E (p : ℕ))) :
    PeriodicSpace.Kind.Tuple.closureT (paramsOf s) (kindOf E) (tupleEquiv s E p '' Z) =
      tupleEquiv s E p '' closure Z := by
  change closureWrt _ _ = _
  rw [closureWrt_image_equiv (d := l2TupleDist s E p) (tupleEquiv s E p) (fun _ _ => rfl),
    closureWrt_eq_of_comparable sqrt_card_pos l2TupleDist_le dist_le_l2TupleDist,
    ← closure_eq_closureWrt]
theorem supportT_liftTupleFn (F : Tuple s E (p : ℕ) → ℂ) :
    PeriodicSpace.Kind.Tuple.supportT (paramsOf s) (kindOf E)
      (liftTupleFn F) = tupleEquiv s E p '' closedSupport F := by
  have h : {y | liftTupleFn F y ≠ 0} =
      tupleEquiv s E p '' {y | F y ≠ 0} := by
    ext y
    constructor
    · intro hy
      exact ⟨(tupleEquiv s E p).symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [liftTupleFn] using hx
  unfold PeriodicSpace.Kind.Tuple.supportT
  rw [h, closureT_image]
  rfl
theorem block_eq_flattenCoords_symm (x : PeriodicSpace.Coords p) (i : Fin (p : ℕ)) :
    x.block i = (flattenCoords (p : ℕ)).symm x i := by
  funext μ
  have h := flattenCoords_apply ((flattenCoords (p : ℕ)).symm x) i μ
    (by have := i.2; have := μ.2; omega)
  rw [Equiv.apply_symm_apply] at h
  exact h
theorem tupleQuotMap_eq (x : PeriodicSpace.Coords p) :
    PeriodicSpace.Kind.Tuple.proj (paramsOf s) (kindOf E) x =
      tupleEquiv s E p (tupleProj s E (p : ℕ) x) := by
  funext i
  change (kindOf E).quotMap (paramsOf s) (x.block i) =
    ptEquiv s E (proj s E ((flattenCoords (p : ℕ)).symm x i))
  rw [block_eq_flattenCoords_symm, quotMap_eq_proj]
theorem liftTupleFn_comp_tupleQuotMap (F : Tuple s E (p : ℕ) → ℂ) :
    liftTupleFn F ∘ PeriodicSpace.Kind.Tuple.proj (paramsOf s) (kindOf E) =
      F ∘ tupleProj s E (p : ℕ) := by
  funext x
  simp [liftTupleFn, tupleQuotMap_eq]
theorem tupleQuotMap_surjective :
    Function.Surjective (PeriodicSpace.Kind.Tuple.proj (paramsOf s) (kindOf E) (p := p)) := by
  intro y
  obtain ⟨x, hx⟩ := tupleProj_surjective s E (p : ℕ) ((tupleEquiv s E p).symm y)
  exact ⟨x, by rw [tupleQuotMap_eq, hx]; simp⟩
theorem isClassC_liftTupleFn_iff (ν : ℕ) (F : Tuple s E (p : ℕ) → ℂ) :
    PeriodicSpace.Kind.Tuple.IsClassC (paramsOf s) (kindOf E) ν
        (liftTupleFn F) ↔
      IsCn (ν : ℕ∞) F := by
  unfold PeriodicSpace.Kind.Tuple.IsClassC
  rw [liftTupleFn_comp_tupleQuotMap]
  exact (isCn_iff_contPartialsUpTo ν F).symm
theorem isSmoothT_liftTupleFn_iff (F : Tuple s E (p : ℕ) → ℂ) :
    PeriodicSpace.Kind.Tuple.IsSmoothT (paramsOf s) (kindOf E)
        (liftTupleFn F) ↔
      IsSmoothFn F :=
  (forall_congr' fun ν => isClassC_liftTupleFn_iff ν F).trans (isCnOn_top_iff _ _).symm
theorem proj_add_congr {a a' : Fin 4 → ℝ} (h : proj s E a = proj s E a')
    (b : Fin 4 → ℝ) : proj s E (a + b) = proj s E (a' + b) := by
  cases E
  · have h' : TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) a =
        TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) a' := h
    change TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) (a + b) =
      TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) (a' + b)
    rw [torusProj_add, torusProj_add, h']
  · have h' : a = a' := h
    rw [h']
theorem tupleProj_add_congr {q : ℕ} {x x' : Fin (4 * q) → ℝ}
    (h : tupleProj s E q x = tupleProj s E q x') (w : Fin (4 * q) → ℝ) :
    tupleProj s E q (x + w) = tupleProj s E q (x' + w) := by
  funext i
  exact proj_add_congr (congrFun h i) ((flattenCoords q).symm w i)
def FactorsThroughTupleProj (s : Conventions.StandingParameters) (E : Ambient) {q : ℕ}
    (G : (Fin (4 * q) → ℝ) → ℂ) : Prop :=
  ∀ x x', tupleProj s E q x = tupleProj s E q x' → G x = G x'
theorem FactorsThroughTupleProj.coordDeriv {q : ℕ} {G : (Fin (4 * q) → ℝ) → ℂ}
    (hG : FactorsThroughTupleProj s E G) (j : Fin (4 * q)) :
    FactorsThroughTupleProj s E (AmbientPoints.partialDeriv j G) := by
  intro x x' h
  unfold AmbientPoints.partialDeriv lineDeriv
  congr 1
  funext t
  exact hG _ _ (tupleProj_add_congr h _)
theorem FactorsThroughTupleProj.iterate {q : ℕ} {G : (Fin (4 * q) → ℝ) → ℂ}
    (hG : FactorsThroughTupleProj s E G) (j : Fin (4 * q)) (n : ℕ) :
    FactorsThroughTupleProj s E ((AmbientPoints.partialDeriv j)^[n] G) := by
  induction n generalizing G with
  | zero => exact hG
  | succ n ih => exact ih (hG.coordDeriv j)
theorem FactorsThroughTupleProj.iterated {q : ℕ} {G : (Fin (4 * q) → ℝ) → ℂ}
    (hG : FactorsThroughTupleProj s E G) (α : PowerSeries.MultiIndex (4 * q)) :
    FactorsThroughTupleProj s E (AmbientPoints.iteratedPartial α G) := by
  unfold AmbientPoints.iteratedPartial
  induction (List.finRange (4 * q)) with
  | nil => exact hG
  | cons j l ih => exact ih.iterate j (α j)
theorem exists_factor_iteratedPartial {q : ℕ} (α : PowerSeries.MultiIndex (4 * q))
    (F : Tuple s E q → ℂ) :
    ∃ H : Tuple s E q → ℂ,
      H ∘ tupleProj s E q =
        AmbientPoints.iteratedPartial α (F ∘ tupleProj s E q) := by
  have hG : FactorsThroughTupleProj s E (F ∘ tupleProj s E q) := fun x x' h => by
    simp only [Function.comp, h]
  have hsurj := tupleProj_surjective s E q
  refine ⟨AmbientPoints.iteratedPartial α (F ∘ tupleProj s E q) ∘ Function.surjInv hsurj, ?_⟩
  funext x
  exact hG.iterated α _ _ (Function.surjInv_eq hsurj _)
theorem partialDeriv_liftTupleFn (α : PowerSeries.MultiIndex (4 * (p : ℕ)))
    (F : Tuple s E (p : ℕ) → ℂ) :
    PeriodicSpace.Kind.Tuple.partialDeriv (paramsOf s) (kindOf E) (p := p) α
        (liftTupleFn F) =
      liftTupleFn (AmbientPoints.multiDeriv α F) := by
  have hcomp := multiDeriv_comp_tupleProj (exists_factor_iteratedPartial α F)
  have hP : liftTupleFn (AmbientPoints.multiDeriv α F) ∘
      PeriodicSpace.Kind.Tuple.proj (paramsOf s) (kindOf E) =
      PeriodicSpace.Coords.iterPartial (p := p) α
        (liftTupleFn F ∘ PeriodicSpace.Kind.Tuple.proj (paramsOf s) (kindOf E)) := by
    rw [liftTupleFn_comp_tupleQuotMap, liftTupleFn_comp_tupleQuotMap, hcomp]
    rfl
  have hspec := Classical.epsilon_spec (p := fun H =>
    H ∘ PeriodicSpace.Kind.Tuple.proj (paramsOf s) (kindOf E) =
      PeriodicSpace.Coords.iterPartial (p := p) α
        (liftTupleFn F ∘ PeriodicSpace.Kind.Tuple.proj (paramsOf s) (kindOf E))) ⟨_, hP⟩
  exact tupleQuotMap_surjective.injective_comp_right (hspec.trans hP.symm)
theorem cNorm_liftTupleFn (ν : ℕ) (F : Tuple s E (p : ℕ) → ℂ) :
    PeriodicSpace.Kind.Tuple.cNorm (paramsOf s) (kindOf E) ν
        (liftTupleFn F) =
      cnNorm ν F := by
  unfold PeriodicSpace.Kind.Tuple.cNorm cnNorm
  refine iSup_congr fun α => ?_
  refine iSup_congr_Prop Iff.rfl fun _ => ?_
  rw [partialDeriv_liftTupleFn]
  exact ((tupleEquiv s E p).symm.iSup_congr fun y => rfl)
end Tuples
section Distribs
variable {s : Conventions.StandingParameters} {E : Ambient} {p : ℕ+}
theorem liftTupleFn_mem_testFns_iff (Ω : Set (Tuple s E (p : ℕ))) (F : Tuple s E (p : ℕ) → ℂ) :
    liftTupleFn F ∈ PeriodicSpace.Kind.Tuple.testFns
        (paramsOf s) (kindOf E) (tupleEquiv s E p '' Ω) ↔
      F ∈ testFns Ω := by
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  rw [isSmoothT_liftTupleFn_iff, supportT_liftTupleFn, isCompactT_image_iff,
    image_subset_image_iff (tupleEquiv s E p).injective]
theorem liftTupleFn_injective :
    Function.Injective (liftTupleFn (s := s) (E := E) (p := p)) :=
  fun _ _ h => (tupleEquiv s E p).symm.surjective.injective_comp_right h
theorem liftTupleFn_surjective :
    Function.Surjective (liftTupleFn (s := s) (E := E) (p := p)) :=
  fun G => ⟨G ∘ tupleEquiv s E p, by
    funext y
    simp [liftTupleFn]⟩
theorem isDistrib_iff_of_agree (Ω : Set (Tuple s E (p : ℕ))) (T : testFns Ω → ℂ)
    (T' : PeriodicSpace.Kind.Tuple.testFns (paramsOf s) (kindOf E)
      (tupleEquiv s E p '' Ω) → ℂ)
    (hT : ∀ (F : testFns Ω)
      (G : PeriodicSpace.Kind.Tuple.testFns (paramsOf s) (kindOf E)
        (tupleEquiv s E p '' Ω)),
      G.1 = liftTupleFn F.1 → T' G = T F) :
    PeriodicSpace.Kind.Tuple.IsDistrib T' ↔ IsDistrib T := by
  let A : testFns Ω → PeriodicSpace.Kind.Tuple.testFns (paramsOf s)
      (kindOf E) (tupleEquiv s E p '' Ω) :=
    fun F => ⟨liftTupleFn F.1, (liftTupleFn_mem_testFns_iff Ω F.1).2 F.2⟩
  have hA : ∀ F, T' (A F) = T F := fun F => hT F (A F) rfl
  have hAsurj : Function.Surjective A := by
    intro G
    obtain ⟨F, hF⟩ := liftTupleFn_surjective G.1
    have hG : liftTupleFn F ∈ PeriodicSpace.Kind.Tuple.testFns
        (paramsOf s) (kindOf E) (tupleEquiv s E p '' Ω) := hF ▸ G.2
    exact ⟨⟨F, (liftTupleFn_mem_testFns_iff Ω F).1 hG⟩, Subtype.ext hF⟩
  have hlin : PeriodicSpace.Kind.Tuple.IsComplexLinearForm T' ↔ IsComplexLinearForm T := by
    constructor
    · rintro ⟨hadd, hsmul⟩
      refine ⟨fun F G H hH => ?_, fun c F H hH => ?_⟩
      · rw [← hA, ← hA, ← hA]
        exact hadd _ _ _ (by change liftTupleFn H.1 = _; rw [hH]; rfl)
      · rw [← hA, ← hA]
        exact hsmul _ _ _ (by change liftTupleFn H.1 = _; rw [hH]; rfl)
    · rintro ⟨hadd, hsmul⟩
      refine ⟨fun F' G' H' hH => ?_, fun c F' H' hH => ?_⟩
      · obtain ⟨F, rfl⟩ := hAsurj F'
        obtain ⟨G, rfl⟩ := hAsurj G'
        obtain ⟨H, rfl⟩ := hAsurj H'
        rw [hA, hA, hA]
        exact hadd _ _ _ (liftTupleFn_injective hH)
      · obtain ⟨F, rfl⟩ := hAsurj F'
        obtain ⟨H, rfl⟩ := hAsurj H'
        rw [hA, hA]
        exact hsmul _ _ _ (liftTupleFn_injective hH)
  have hserves : ∀ (K : Set (Tuple s E (p : ℕ))) (ν : ℕ),
      PeriodicSpace.Kind.Tuple.HasOrderBoundOn T' (tupleEquiv s E p '' K) ν ↔
        OrderBoundsOn T K ν := by
    intro K ν
    refine exists_congr fun C => ?_
    constructor
    · intro h F hF
      have := h (A F) (by
        change PeriodicSpace.Kind.Tuple.supportT _ _ (liftTupleFn F.1) ⊆ _
        rw [supportT_liftTupleFn]
        exact image_mono hF)
      rw [hA] at this
      change _ ≤ _ * PeriodicSpace.Kind.Tuple.cNorm _ _ ν
        (liftTupleFn F.1) at this
      rwa [cNorm_liftTupleFn] at this
    · intro h G hG
      obtain ⟨F, rfl⟩ := hAsurj G
      rw [hA]
      change _ ≤ _ * PeriodicSpace.Kind.Tuple.cNorm _ _ ν
        (liftTupleFn F.1)
      rw [cNorm_liftTupleFn]
      refine h F ?_
      change PeriodicSpace.Kind.Tuple.supportT _ _ (liftTupleFn F.1) ⊆ _
        at hG
      rw [supportT_liftTupleFn] at hG
      exact (image_subset_image_iff (tupleEquiv s E p).injective).1 hG
  refine and_congr hlin ?_
  constructor
  · intro h K hK hKΩ
    obtain ⟨ν, hν⟩ := h _ ((isCompactT_image_iff K).2 hK) (image_mono hKΩ)
    exact ⟨ν, (hserves K ν).1 hν⟩
  · intro h K' hK' hKΩ
    have hK : tupleEquiv s E p '' (tupleEquiv s E p ⁻¹' K') = K' :=
      image_preimage_eq _ (tupleEquiv s E p).surjective
    rw [← hK] at hK' hKΩ ⊢
    obtain ⟨ν, hν⟩ := h _ ((isCompactT_image_iff _).1 hK')
      ((image_subset_image_iff (tupleEquiv s E p).injective).1 hKΩ)
    exact ⟨ν, (hserves _ ν).2 hν⟩
end Distribs
section Singletons
variable {s : Conventions.StandingParameters} {E : Ambient}
theorem closedSupport_complexOnSingletons (φ : Pt s E → ℂ) :
    closedSupport (complexOnSingletons φ) = headPoint ⁻¹' tsupport φ := by
  have h : {y : Tuple s E 1 | complexOnSingletons φ y ≠ 0} = headPoint ⁻¹' Function.support φ := rfl
  rw [closedSupport, h, closure_preimage_headPoint]
  rfl
theorem isC1Fn_liftFn_iff (f : Pt s E → ℝ) :
    PeriodicSpace.Kind.IsC1Fn (paramsOf s) (kindOf E) (liftFn f) ↔
      ContDiff ℝ 1 (f ∘ proj s E) := by
  unfold PeriodicSpace.Kind.IsC1Fn TestFunctions.IsC1R4
  rw [liftFn_comp_quotMap]
theorem sepTuples_eq_separatedTuples
    (hpartials : PeriodicSpace.ContPartialsIffContDiff)
    (n : ℕ) : sepTuples s E n = separatedTuples s E n := by
  ext f
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨fun i => ⟨(isC1_iff_contDiff_comp_proj hpartials _).1 (h₁ i), h₂ i⟩,
      fun i j hij => h₃ i j hij⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun i => (isC1_iff_contDiff_comp_proj hpartials _).2 (h₁ i).1,
      fun i => (h₁ i).2, fun i j hij => h₂ hij⟩
theorem liftTuple_mem_sepC1Tuples_iff
    (hpartials : PeriodicSpace.ContPartialsIffContDiff)
    {n : ℕ} (f : Fin n → Pt s E → ℝ) :
    liftTuple f ∈ PeriodicSpace.Kind.sepC1Tuples (paramsOf s) (kindOf E) n ↔
      f ∈ sepTuples s E n := by
  change ((∀ i, _) ∧ (∀ i, _) ∧ ∀ i k, _) ↔ ((∀ i, _) ∧ (∀ i, _) ∧ ∀ i k, _)
  have hs : ∀ i, PeriodicSpace.Kind.supportQ (paramsOf s) (kindOf E) (liftTuple f i) =
      ptEquiv s E '' tsupport (f i) := fun i => supportQ_liftFn (f i)
  simp only [hs, isCompactQ_image_iff, Set.disjoint_image_iff (ptEquiv s E).injective]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  exact (isC1Fn_liftFn_iff (f i)).trans (isC1_iff_contDiff_comp_proj hpartials _).symm
theorem liftTuple_mem_sepC1TuplesWithin_iff
    (hpartials : PeriodicSpace.ContPartialsIffContDiff)
    {n : ℕ} (O : Set (Pt s E)) (f : Fin n → Pt s E → ℝ) :
    liftTuple f ∈ PeriodicSpace.Kind.sepC1TuplesWithin (paramsOf s) (kindOf E) n
        (ptEquiv s E '' O) ↔ f ∈ sepTuplesIn n O := by
  refine and_congr (liftTuple_mem_sepC1Tuples_iff hpartials f) (forall_congr' fun i => ?_)
  change PeriodicSpace.Kind.supportQ _ _ (liftFn (f i)) ⊆ _ ↔ _
  rw [supportQ_liftFn, image_subset_image_iff (ptEquiv s E).injective]
theorem origin_eq_ptEquiv :
    PeriodicSpace.Kind.origin (paramsOf s) (kindOf E) =
      ptEquiv s E (proj s E 0) :=
  quotMap_eq_proj 0
theorem centredBall_eq_of_lt_top {ρ : ℝ≥0∞} (hρ : ρ < ∞) :
    PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ρ =
      ptEquiv s E '' openBall s E (origin s E) ρ.toReal := by
  unfold PeriodicSpace.Kind.centredBall
  rw [if_neg hρ.ne]
  ext z
  obtain ⟨y, rfl⟩ := (ptEquiv s E).surjective z
  simp only [mem_ofPred_eq, (ptEquiv s E).injective.mem_set_image, openBall, origin_eq_ptEquiv,
    quotDist_ptEquiv, origin]
theorem centredBall_top :
    PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ∞ = univ := by
  simp [PeriodicSpace.Kind.centredBall]
theorem originBall_top : originBall s E ∞ = univ := by
  simp [originBall]
theorem image_originBall (ρ : ℝ≥0∞) :
    ptEquiv s E '' originBall s E ρ =
      PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ρ := by
  by_cases hρ : ρ = ∞
  · subst hρ
    rw [originBall_top, centredBall_top, image_univ, (ptEquiv s E).surjective.range_eq]
  · rw [centredBall_eq_of_lt_top (lt_top_iff_ne_top.2 hρ), originBall, if_neg hρ]
theorem isOpen_originBall (ρ : ℝ≥0∞) : IsOpen (originBall s E ρ) := by
  by_cases hρ : ρ = ∞
  · subst hρ
    rw [originBall_top]
    exact isOpen_univ
  · rw [originBall, if_neg hρ, openBall_eq_ball]
    exact Metric.isOpen_ball
theorem ballSepTensors_eq_span
    (hpartials : PeriodicSpace.ContPartialsIffContDiff)
    (q : ℕ) (ρ : ℝ≥0∞) :
    ballSepTensors s E q ρ = Submodule.span ℂ
      {F | ∃ f ∈ ballSepTuples s E q ρ, F = tensorProd fun i y => ((f i y : ℝ) : ℂ)} := by
  set L : (Tuple s E q → ℂ) →ₗ[ℂ] ((Fin q → (kindOf E).Pt (paramsOf s)) → ℂ) :=
    LinearMap.funLeft ℂ ℂ fun y i => (ptEquiv s E).symm (y i) with hL
  have hinj : Function.Injective L := by
    refine LinearMap.funLeft_injective_of_surjective ℂ ℂ _ fun y => ?_
    exact ⟨fun i => ptEquiv s E (y i), by simp⟩
  have himage : L '' {F | ∃ f ∈ ballSepTuples s E q ρ,
      F = tensorProd fun i y => ((f i y : ℝ) : ℂ)} =
      {F | ∃ h ∈ PeriodicSpace.Kind.sepC1TuplesWithin (paramsOf s) (kindOf E) q
          (PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ρ),
        F = PeriodicSpace.Kind.tensorFn (paramsOf s) (kindOf E)
          fun i y => ((h i y : ℝ) : ℂ)} := by
    ext F
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      refine ⟨liftTuple f, ?_, ?_⟩
      · rw [← image_originBall]
        exact (liftTuple_mem_sepC1TuplesWithin_iff hpartials _ f).2 hf
      · rfl
    · rintro ⟨h, hh, rfl⟩
      let f : Fin q → Pt s E → ℝ := fun i => h i ∘ ptEquiv s E
      have hfh : liftTuple f = h := by
        funext i y
        simp [f, liftTuple, liftFn]
      rw [← image_originBall, ← hfh] at hh
      refine ⟨_, ⟨f, (liftTuple_mem_sepC1TuplesWithin_iff hpartials _ f).1 hh, rfl⟩, ?_⟩
      rw [← hfh]
      rfl
  unfold ballSepTensors PeriodicSpace.Kind.sepTensorSpanOnBall
  rw [← himage, ← Submodule.map_span, ← hL, Submodule.comap_map_eq_of_injective hinj]
end Singletons
section Arithmetic
variable {s : Conventions.StandingParameters} {E : Ambient}
theorem quotMap_pickLift (y : (kindOf E).Pt (paramsOf s)) :
    (kindOf E).quotMap (paramsOf s)
      (PeriodicSpace.Kind.pickLift (paramsOf s) (kindOf E) y) = y := by
  have hex : ∃ x, PeriodicSpace.Kind.IsLift (paramsOf s) (kindOf E) y x := by
    obtain ⟨x, hx⟩ := proj_surjective (s := s) (E := E) ((ptEquiv s E).symm y)
    exact ⟨x, by
      change (kindOf E).quotMap (paramsOf s) x = y
      rw [quotMap_eq_proj, hx]
      simp⟩
  exact Classical.epsilon_spec hex
theorem addPt_ptEquiv (y v : Pt s E) :
    PeriodicSpace.Kind.addPt (paramsOf s) (kindOf E) (ptEquiv s E y)
      (ptEquiv s E v) = ptEquiv s E y + ptEquiv s E v := by
  have hy := quotMap_pickLift (s := s) (E := E) (ptEquiv s E y)
  have hv := quotMap_pickLift (s := s) (E := E) (ptEquiv s E v)
  unfold PeriodicSpace.Kind.addPt
  cases E
  · refine (torusProj_add (S := PeriodicLattice.torusSide s.L s.m) _ _).trans ?_
    exact congrArg₂ (· + ·) hy hv
  · exact congrArg₂ (· + ·) hy hv
theorem subPt_ptEquiv (y v : Pt s E) :
    PeriodicSpace.Kind.subPt (paramsOf s) (kindOf E) (ptEquiv s E y)
      (ptEquiv s E v) = ptEquiv s E y - ptEquiv s E v := by
  have hy := quotMap_pickLift (s := s) (E := E) (ptEquiv s E y)
  have hv := quotMap_pickLift (s := s) (E := E) (ptEquiv s E v)
  unfold PeriodicSpace.Kind.subPt
  cases E
  · refine (torusProj_sub (S := PeriodicLattice.torusSide s.L s.m) _ _).trans ?_
    exact congrArg₂ (· - ·) hy hv
  · exact congrArg₂ (· - ·) hy hv
theorem mem_periodGroup_iff (k : Fin 4 → ℝ) :
    k ∈ (kindOf E).periodGroup (paramsOf s) ↔
      IsTuplePeriod s E 1 (flattenCoords 1 fun _ => k) := by
  have hcoord : ∀ (μ : Fin 4) (h : 4 * ((0 : Fin 1) : ℕ) + (μ : ℕ) < 4 * 1),
      flattenCoords 1 (fun _ => k) ⟨4 * ((0 : Fin 1) : ℕ) + μ, h⟩ = k μ := fun μ h =>
    flattenCoords_apply (fun _ => k) 0 μ h
  cases E
  · constructor
    · rintro ⟨n, hn⟩
      refine ⟨fun j => n ((finProdFinEquiv.trans (finCongr (Nat.mul_comm 1 4))).symm j).2,
        fun j => ?_⟩
      change k ((finProdFinEquiv.trans (finCongr (Nat.mul_comm 1 4))).symm j).2 = _
      rw [hn, mul_comm]
      rfl
    · rintro ⟨n, hn⟩
      refine ⟨fun μ => n ⟨4 * ((0 : Fin 1) : ℕ) + μ, by have := μ.2; simp⟩, fun μ => ?_⟩
      have h := hn ⟨4 * ((0 : Fin 1) : ℕ) + μ, by have := μ.2; simp⟩
      rw [hcoord] at h
      rw [h, mul_comm]
      rfl
  · constructor
    · intro h
      have hk : k = 0 := h
      subst hk
      rfl
    · intro h
      change k = 0
      funext μ
      have h' := congrFun h ⟨4 * ((0 : Fin 1) : ℕ) + μ, by have := μ.2; simp⟩
      rw [hcoord] at h'
      exact h'
theorem partitionExpansion_eq_centredAt (S : ConnectedFamily s E) (Ψ : BallFamily s E ∞)
    (hΨ : ∀ (n : ℕ) (hn : 2 ≤ n) (g : ballSepTuples s E n ∞)
      (h : g.1 ∈ separatedTuples s E n), Ψ n hn g = S.fn n hn ⟨g.1, h⟩)
    (q : ℕ) (f : ballSepTuples s E q ∞) (h : f.1 ∈ separatedTuples s E q) :
    partitionExpansion Ψ f = S.centredAt ⟨f.1, h⟩ := by
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
  change blockTerm Ψ f J = S.blockFactor ⟨f.1, h⟩ J
  unfold blockTerm ConnectedFamily.blockFactor
  by_cases hJ : 2 ≤ J.card
  · rw [dif_pos hJ, dif_pos hJ]
    exact hΨ _ hJ _ (restrictTuple_mem h J)
  · rw [dif_neg hJ, dif_neg hJ]
theorem partitionsNoSingletons_eq (q : ℕ) :
    PeriodicSpace.partitionsNoSingletons q = SetPartition.singletonFree q := by
  ext π
  simp [PeriodicSpace.partitionsNoSingletons, SetPartition.singletonFree]
theorem centredFunc_liftTuple {ρ : ℝ≥0∞}
    (Ψ : PeriodicSpace.Kind.BallMultilinearFamily (paramsOf s) (kindOf E) ρ)
    (Ψ' : BallFamily s E ρ)
    (hΨ : ∀ (n : ℕ) (hn : 2 ≤ n) (g : ballSepTuples s E n ρ)
      (h : liftTuple g.1 ∈ PeriodicSpace.Kind.sepC1TuplesWithin (paramsOf s)
        (kindOf E) n (PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ρ)),
      Ψ' n hn g = Ψ.func n hn ⟨liftTuple g.1, h⟩)
    (q : ℕ) (f : ballSepTuples s E q ρ)
    (h : liftTuple f.1 ∈ PeriodicSpace.Kind.sepC1TuplesWithin (paramsOf s)
      (kindOf E) q (PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ρ)) :
    Ψ.centredFunc ⟨liftTuple f.1, h⟩ = partitionExpansion Ψ' f := by
  unfold PeriodicSpace.Kind.BallMultilinearFamily.centredFunc partitionExpansion
  refine Finset.sum_bij (fun ξ _ => ξ.1) (fun ξ _ => ?_) (fun _ _ _ _ h => Subtype.ext h)
    (fun π hπ => ⟨⟨π, by rw [partitionsNoSingletons_eq]; exact hπ⟩, Finset.mem_attach _ _, rfl⟩)
    (fun ξ _ => ?_)
  · rw [← partitionsNoSingletons_eq]
    exact ξ.2
  · rw [← Finset.prod_attach ξ.1.parts (fun J => blockTerm Ψ' f J)]
    refine Finset.prod_congr rfl fun J _ => ?_
    have h2 := PeriodicSpace.two_le_card_of_mem_partitionsNoSingletons ξ.2 J.2
    unfold blockTerm
    rw [dif_pos h2]
    exact (hΨ J.1.card h2 ⟨_, restrictTuple_mem_sepTuplesIn f.2 J.1⟩
      (PeriodicSpace.Kind.restrictTuple_mem_sepC1TuplesWithin _ _ h J.1)).symm
end Arithmetic
theorem allCoincide_holds
    (hpartials : PeriodicSpace.ContPartialsIffContDiff) :
    AllCoincide := fun s E =>
  { pt_torus := rfl
    pt_euclidean := rfl
    pointDist_torus := fun _ _ => rfl
    pointDist_euclidean := fun _ _ => rfl
    setDist_torus_eq := fun _ _ => rfl
    setDist_eq_iInf := fun _ _ => rfl
    setDist_empty := fun A => setDist_empty_right s E A
    proj_torus := fun _ _ _ => rfl
    supDist_single := fun y y' => by simp [supDist, headPoint]
    closure_single := closure_preimage_headPoint
    isCompact_single := isCompact_preimage_headPoint_iff
    continuous_comp_head := fun g => headPointHomeomorph.comp_continuous_iff'
    continuous_into_single := fun g => headPointHomeomorph.comp_continuous_iff.symm
    closedSupport_single := closedSupport_complexOnSingletons
    closedSupport_real_single := closedSupport_asFunctionOnOnePoint
    isC1_iff := isC1_iff_contDiff_comp_proj hpartials
    isC1Fn_iff := fun _ => Iff.rfl
    c1CompactSupportIn_eq := fun A => by
      ext f
      exact and_congr_left' (isC1_iff_contDiff_comp_proj hpartials f)
    sepTuples_eq := fun n _ => sepTuples_eq_separatedTuples hpartials n
    isOpen_originBall := fun ρ _ => isOpen_originBall ρ
    ballSepTuples_top := fun n _ => by
      change sepTuplesIn n (originBall s E ∞) = _
      rw [originBall_top, sepTuplesIn_univ]
    restrictTuple_mem_ball := fun _ _ _ _ f hf J _ => restrictTuple_mem_sepTuplesIn hf J
    blockTerm_defined := fun _ _ _ _ f hf π hπ J hJ =>
      ⟨two_le_card_of_mem_singletonFree hπ hJ, restrictTuple_mem_sepTuplesIn hf J⟩
    partitionExpansion_connected := fun S Ψ hΨ q _ f h => partitionExpansion_eq_centredAt S Ψ hΨ q f h
    quotMap_eq := quotMap_eq_proj
    isLift_lift_iff := fun y x => by
      unfold PeriodicSpace.Kind.IsLift IsLift
      rw [quotMap_eq_proj, (ptEquiv s E).apply_eq_iff_eq]
    quotDist_eq := quotDist_ptEquiv
    setInfDist_eq := fun A B => by
      unfold PeriodicSpace.Kind.setInfDist setDist
      simp only [iInf_image, quotDist_ptEquiv]
    setDiam_eq := fun A => by
      unfold PeriodicSpace.Kind.setDiam setDiam
      simp only [iSup_image, quotDist_ptEquiv]
    isOpenQ_iff := fun Z => (isOpenQ_image_iff Z).trans (isOpen_preimage_headPoint_iff Z).symm
    isClosedQ_iff := fun Z =>
      (isClosedQ_image_iff Z).trans (isClosed_preimage_headPoint_iff Z).symm
    isCompactQ_iff := fun Z =>
      (isCompactQ_image_iff Z).trans (isCompact_preimage_headPoint_iff Z).symm
    mem_periodGroup_iff := mem_periodGroup_iff
    origin_eq_proj := origin_eq_ptEquiv
    origin_eq_zero := by
      cases E
      · exact funext fun μ => by
          simp [PeriodicSpace.Kind.origin, PeriodicSpace.Kind.quotMap]
          rfl
      · rfl
    centredBall_eq := fun ρ _ hρ => centredBall_eq_of_lt_top hρ
    centredBall_top := centredBall_top
    image_originBall := fun ρ _ => image_originBall ρ
    isC1Fn_lift_iff := fun f =>
      (isC1Fn_liftFn_iff f).trans (isC1_iff_contDiff_comp_proj hpartials f).symm
    supportQ_lift := fun φ => by
      rw [supportQ_liftFn, closedSupport_complexOnSingletons]
      ext y
      simp
    supportQ_real_lift := fun f => by
      rw [supportQ_liftFn, closedSupport_asFunctionOnOnePoint]
      ext y
      simp [headPoint]
    lift_mem_c1SupportedIn_iff := fun A f => by
      change (PeriodicSpace.Kind.IsC1Fn _ _ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
      rw [supportQ_liftFn, isCompactQ_image_iff,
        image_subset_image_iff (ptEquiv s E).injective, isC1Fn_liftFn_iff,
        ← isC1_iff_contDiff_comp_proj hpartials]
    lift_mem_sepC1TuplesWithin_iff := fun n _ O _ f => liftTuple_mem_sepC1TuplesWithin_iff hpartials O f
    lift_mem_sepC1Tuples_iff := fun n _ f => by
      rw [liftTuple_mem_sepC1Tuples_iff hpartials, sepTuples_eq_separatedTuples hpartials]
    restrictTuple_lift := fun _ _ _ _ _ => rfl
    tensorFn_lift := fun n _ φ y => by
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [liftTuple, liftFn]
    partitionsNoSingletons_eq := fun q _ => partitionsNoSingletons_eq q
    ballSepTensors_eq_span := fun q _ ρ _ => ballSepTensors_eq_span hpartials q ρ
    centredFunc_lift_eq := fun ρ _ Ψ Ψ' hΨ q _ f h => centredFunc_liftTuple Ψ Ψ' hΨ q f h
    centredFunc_eq := fun _ _ _ _ _ _ => rfl
    tupleProj_eq := fun p x => tupleQuotMap_eq x
    isOpenT_iff := fun p Z => isOpenT_image_iff Z
    isClosedT_iff := fun p Z => isClosedT_image_iff Z
    isCompactT_iff := fun p Z => isCompactT_image_iff Z
    closureT_image := fun p Z => closureT_image Z
    isClassC_iff := fun p ν F => isClassC_liftTupleFn_iff ν F
    partialDeriv_lift := fun p ν F _ α _ => partialDeriv_liftTupleFn α F
    cNorm_lift := fun p ν F _ => cNorm_liftTupleFn ν F
    isSmoothT_iff := fun p F => isSmoothT_liftTupleFn_iff F
    supportT_lift := fun p F => supportT_liftTupleFn F
    lift_mem_testFns_iff := fun p Ω _ F => liftTupleFn_mem_testFns_iff Ω F
    isDistrib_iff := fun p Ω _ T T' hT => isDistrib_iff_of_agree Ω T T' hT
    pairwiseDistinct_eq := fun n => by
      ext y
      constructor
      · intro hy
        refine ⟨(tupleEquiv s E n).symm y, fun i j hij => hy ?_, by simp⟩
        exact (ptEquiv s E).symm.injective hij
      · rintro ⟨x, hx, rfl⟩ i j hij
        exact hx ((ptEquiv s E).injective hij)
    addPt_eq := addPt_ptEquiv
    subPt_eq := subPt_ptEquiv }
end YangMills.Construction.AmbientPoints.Identification
end
