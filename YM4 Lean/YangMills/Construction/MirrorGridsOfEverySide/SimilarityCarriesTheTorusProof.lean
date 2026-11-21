import YangMills.Construction.MirrorGridsOfEverySide.BoxAgainstTheTorusProof
import YangMills.Construction.MirrorGridsOfEverySide.SimilaritiesOfTheLatticesProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides.TorusScaling
open TorusMetric (torusProj)
theorem torusSide_pos (G : GridSetup) : 0 < PeriodicLattice.torusSide G.L G.m := by apply _root_.YangMills.Construction.MirrorGridsAllSides.CubeVersusTorus.torusSide_pos <;> assumption
theorem mem_sublattice_iff (G : GridSetup) (y : G.Torus) :
    y ∈ PeriodicLattice.sublattice G.L G.m ((G.K : ℕ) : ℤ) ↔
      ∃ x ∈ G.gridPoints, G.proj x = y := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨fun μ => (k μ : ℝ) * G.mesh, ⟨k, fun μ => ?_⟩, ?_⟩
    · rfl
    · funext μ
      rw [hk μ]
      rfl
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    refine ⟨k, fun μ => ?_⟩
    change ((x μ : ℝ) : AddCircle (PeriodicLattice.torusSide G.L G.m)) = _
    rw [hk μ]
    rfl
variable {G : GridSetup} (S : ScalingMap G)
theorem image_torusSide :
    PeriodicLattice.torusSide S.image.L S.image.m = S.scale * PeriodicLattice.torusSide G.L G.m := by apply _root_.YangMills.SharedProofs.p15016 <;> assumption
def circleDilation :
    AddCircle (PeriodicLattice.torusSide G.L G.m) ≃+
      AddCircle (PeriodicLattice.torusSide S.image.L S.image.m) :=
  AddCircle.equivAddCircle _ _ (torusSide_pos G).ne' (torusSide_pos S.image).ne'
theorem circleDilation_coe (t : ℝ) :
    circleDilation S (t : AddCircle (PeriodicLattice.torusSide G.L G.m)) =
      ((S.scale * t : ℝ) : AddCircle (PeriodicLattice.torusSide S.image.L S.image.m)) := by
  have hs : (PeriodicLattice.torusSide G.L G.m)⁻¹ * PeriodicLattice.torusSide S.image.L S.image.m =
      S.scale := by
    rw [image_torusSide]
    have := (torusSide_pos G).ne'
    field_simp
  rw [circleDilation, AddCircle.equivAddCircle_apply_mk, hs, mul_comm]
def torusDilation : G.Torus ≃+ S.image.Torus :=
  AddEquiv.piCongrRight fun _ => circleDilation S
theorem torusDilation_apply (y : G.Torus) (μ : Fin 4) :
    torusDilation S y μ = circleDilation S (y μ) := rfl
theorem torusDilation_proj (w : Fin 4 → ℝ) :
    torusDilation S (G.proj w) = S.image.proj fun μ => S.scale * w μ := by
  funext μ
  exact circleDilation_coe S (w μ)
theorem torusDilation_pointOnAxis (μ : Fin 4) (t : ℝ) :
    torusDilation S (PeriodicLattice.pointOnAxis G.L G.m μ t) =
      PeriodicLattice.pointOnAxis S.image.L S.image.m μ (S.scale * t) := by
  funext ν
  rw [torusDilation_apply]
  by_cases hν : ν = μ
  · subst hν
    simpa [PeriodicLattice.pointOnAxis] using circleDilation_coe S t
  · simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν]
theorem torusMap_eq_dilation_sub (y : G.Torus) :
    S.torusMap y = torusDilation S y - S.image.proj fun μ => S.scale * S.shift μ := by
  have key : ∀ x : Fin 4 → ℝ, S.image.proj (S.toFun x) =
      torusDilation S (G.proj x) - S.image.proj fun μ => S.scale * S.shift μ := by
    intro x
    rw [torusDilation_proj]
    funext μ
    change ((S.scale * (x μ - S.shift μ) : ℝ) :
      AddCircle (PeriodicLattice.torusSide S.image.L S.image.m)) = _
    rw [mul_sub, AddCircle.coe_sub]
    rfl
  have hy : G.proj (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide G.L G.m) y) = y :=
    TestFunctions.torusProj_liftPoint y
  have := key (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide G.L G.m) y)
  rw [hy] at this
  exact this
theorem isTorusLift_torusMap : S.IsTorusLift S.torusMap := by
  funext x
  simp only [Function.comp_apply]
  rw [torusMap_eq_dilation_sub, torusDilation_proj]
  funext μ
  change _ = ((S.scale * (x μ - S.shift μ) : ℝ) :
    AddCircle (PeriodicLattice.torusSide S.image.L S.image.m))
  rw [mul_sub, AddCircle.coe_sub]
  rfl
theorem torusMap_proj (x : Fin 4 → ℝ) :
    S.torusMap (G.proj x) = S.image.proj (S.toFun x) :=
  congrFun (isTorusLift_torusMap S) x
theorem torusMap_add (y z : G.Torus) : S.torusMap (y + z) = S.torusMap y + torusDilation S z := by
  rw [torusMap_eq_dilation_sub, torusMap_eq_dilation_sub, map_add]
  abel
theorem torusMap_sub (y z : G.Torus) : S.torusMap y - S.torusMap z = torusDilation S (y - z) := by
  rw [torusMap_eq_dilation_sub, torusMap_eq_dilation_sub, map_sub]
  abel
theorem torusMap_bijective : Function.Bijective S.torusMap := by
  constructor
  · intro y z hyz
    have h' := torusMap_sub S y z
    rw [hyz, sub_self] at h'
    exact sub_eq_zero.mp ((torusDilation S).map_eq_zero_iff.mp h'.symm)
  · intro y'
    refine ⟨(torusDilation S).symm (y' + S.image.proj fun μ => S.scale * S.shift μ), ?_⟩
    rw [torusMap_eq_dilation_sub, AddEquiv.apply_symm_apply]
    abel
theorem existsUnique_torusLift : ∃! T : G.Torus → S.image.Torus, S.IsTorusLift T := by
  refine ⟨S.torusMap, isTorusLift_torusMap S, fun T hT => ?_⟩
  funext y
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective (PeriodicLattice.torusSide G.L G.m) y
  exact (congrFun hT x).trans (congrFun (isTorusLift_torusMap S) x).symm
theorem euclidNormVec_const_mul {f : ℝ} (hf : 0 < f) (w : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (fun μ => f * w μ) = f * TorusMetric.euclidNormVec w := by
  unfold TorusMetric.euclidNormVec
  have : ∑ μ, (f * w μ) ^ 2 = f ^ 2 * ∑ μ, w μ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => mul_pow _ _ _
  rw [this, Real.sqrt_mul (sq_nonneg f), Real.sqrt_sq hf.le]
theorem torusEuclidNorm_torusDilation (z : G.Torus) :
    TorusMetric.torusEuclidNorm (torusDilation S z) =
      S.scale * TorusMetric.torusEuclidNorm z := by
  have hf := S.scale_pos
  have hset : TorusMetric.euclidNormVec ''
        (torusProj (PeriodicLattice.torusSide S.image.L S.image.m) ⁻¹' {torusDilation S z}) =
      S.scale • (TorusMetric.euclidNormVec '' (torusProj (PeriodicLattice.torusSide G.L G.m) ⁻¹' {z})) := by
    ext r
    constructor
    · rintro ⟨w', hw', rfl⟩
      have hw : torusProj (PeriodicLattice.torusSide G.L G.m) (fun μ => S.scale⁻¹ * w' μ) = z := by
        apply (torusDilation S).injective
        have h1 := torusDilation_proj S fun μ => S.scale⁻¹ * w' μ
        refine h1.trans (Eq.trans ?_ hw')
        congr 1
        funext μ
        field_simp
      refine ⟨_, ⟨_, hw, rfl⟩, ?_⟩
      change S.scale * _ = _
      rw [← euclidNormVec_const_mul hf]
      congr 1
      funext μ
      field_simp
    · intro hr
      rw [Set.mem_smul_set] at hr
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hr
      refine ⟨fun μ => S.scale * w μ, ?_, euclidNormVec_const_mul hf w⟩
      have h1 := torusDilation_proj S w
      have hw' : torusProj (PeriodicLattice.torusSide G.L G.m) w = z := hw
      change S.image.proj _ = torusDilation S z
      rw [← h1, ← hw']
      rfl
  unfold TorusMetric.torusEuclidNorm
  rw [hset, Real.sInf_smul_of_nonneg hf.le, smul_eq_mul]
theorem torusMap_image_sublattice :
    S.torusMap '' (PeriodicLattice.sublattice G.L G.m ((G.K : ℕ) : ℤ) : Set G.Torus) =
      (PeriodicLattice.sublattice S.image.L S.image.m ((S.image.K : ℕ) : ℤ) : Set S.image.Torus) := by
  ext y'
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_sublattice_iff G y).mp hy
    rw [torusMap_proj]
    exact (mem_sublattice_iff S.image _).mpr ⟨_, S.toFun_mem hx, rfl⟩
  · intro hy'
    obtain ⟨x', ⟨k, hk⟩, rfl⟩ := (mem_sublattice_iff S.image y').mp hy'
    obtain ⟨u, hu⟩ := S.shift_mem
    refine ⟨G.proj fun μ => ((k μ + u μ : ℤ) : ℝ) * G.mesh,
      (mem_sublattice_iff G _).mpr ⟨_, ⟨k + u, fun μ => rfl⟩, rfl⟩, ?_⟩
    rw [torusMap_proj]
    congr 1
    funext μ
    simp only [ScalingMap.toFun, hk μ, hu μ, S.image_mesh]
    push_cast
    ring
def pointMap (x : G.TorusPoint) : S.image.TorusPoint :=
  ⟨S.torusMap x, by
    have hx : S.torusMap x ∈ (PeriodicLattice.sublattice S.image.L S.image.m ((S.image.K : ℕ) : ℤ) :
        Set S.image.Torus) := by
      rw [← torusMap_image_sublattice S]
      exact mem_image_of_mem _ x.2
    exact hx⟩
theorem pointMap_bijective : Function.Bijective (pointMap S) := by
  constructor
  · intro x y hxy
    exact Subtype.ext ((torusMap_bijective S).1 (congrArg Subtype.val hxy))
  · rintro ⟨y', hy'⟩
    have hm : y' ∈ (PeriodicLattice.sublattice S.image.L S.image.m ((S.image.K : ℕ) : ℤ) :
        Set S.image.Torus) := hy'
    rw [← torusMap_image_sublattice S] at hm
    obtain ⟨y, hy, rfl⟩ := hm
    exact ⟨⟨y, hy⟩, rfl⟩
theorem torusDilation_unitStep (μ : Fin 4) :
    torusDilation S (PeriodicLattice.unitStep G.L G.m ((G.K : ℕ) : ℤ) μ : G.Torus) =
      (PeriodicLattice.unitStep S.image.L S.image.m ((S.image.K : ℕ) : ℤ) μ : S.image.Torus) := by
  change torusDilation S (PeriodicLattice.pointOnAxis G.L G.m μ G.mesh) =
    PeriodicLattice.pointOnAxis S.image.L S.image.m μ S.image.mesh
  rw [torusDilation_pointOnAxis, S.image_mesh]
theorem pointMap_sub_eq_unitStep (x y : G.TorusPoint) (μ : Fin 4) :
    pointMap S x - pointMap S y =
        PeriodicLattice.unitStep S.image.L S.image.m ((S.image.K : ℕ) : ℤ) μ ↔
      x - y = PeriodicLattice.unitStep G.L G.m ((G.K : ℕ) : ℤ) μ := by
  rw [Subtype.ext_iff, Subtype.ext_iff, ← torusDilation_unitStep]
  change S.torusMap x - S.torusMap y = _ ↔ (x : G.Torus) - y = _
  rw [torusMap_sub]
  exact (torusDilation S).injective.eq_iff
theorem pointMap_sub_eq_neg_unitStep (x y : G.TorusPoint) (μ : Fin 4) :
    pointMap S x - pointMap S y =
        -PeriodicLattice.unitStep S.image.L S.image.m ((S.image.K : ℕ) : ℤ) μ ↔
      x - y = -PeriodicLattice.unitStep G.L G.m ((G.K : ℕ) : ℤ) μ := by
  rw [← neg_eq_iff_eq_neg, ← neg_eq_iff_eq_neg, neg_sub, neg_sub, pointMap_sub_eq_unitStep]
theorem pointMap_add_unitStep (x : G.TorusPoint) (μ : Fin 4) :
    pointMap S (x + PeriodicLattice.unitStep G.L G.m ((G.K : ℕ) : ℤ) μ) =
      pointMap S x + PeriodicLattice.unitStep S.image.L S.image.m ((S.image.K : ℕ) : ℤ) μ := by
  apply Subtype.ext
  change S.torusMap ((x : G.Torus) + _) = S.torusMap x + _
  rw [torusMap_add, torusDilation_unitStep]
def linkImage (e : G.PeriodicLink) : S.image.PeriodicLink where
  source := pointMap S e.source
  target := pointMap S e.target
  isNeighbour := by
    obtain ⟨μ, hμ | hμ⟩ := e.isNeighbour
    · exact ⟨μ, Or.inl ((pointMap_sub_eq_unitStep S _ _ μ).mpr hμ)⟩
    · exact ⟨μ, Or.inr ((pointMap_sub_eq_neg_unitStep S _ _ μ).mpr hμ)⟩
theorem isLinkImage_torusLinkMap (e : G.PeriodicLink) : S.IsLinkImage e (S.torusLinkMap e) :=
  Classical.epsilon_spec (p := S.IsLinkImage e) ⟨linkImage S e, rfl, rfl⟩
theorem torusLinkMap_eq (e : G.PeriodicLink) : S.torusLinkMap e = linkImage S e := by
  obtain ⟨h1, h2⟩ := isLinkImage_torusLinkMap S e
  exact PeriodicLattice.Bond.ext (Subtype.ext h1) (Subtype.ext h2)
theorem torusLinkMap_bijective : Function.Bijective S.torusLinkMap := by
  have hfun : S.torusLinkMap = linkImage S := funext (torusLinkMap_eq S)
  rw [hfun]
  constructor
  · intro e f hef
    have h1 : pointMap S e.source = pointMap S f.source :=
      congrArg (fun r : S.image.PeriodicLink => r.source) hef
    have h2 : pointMap S e.target = pointMap S f.target :=
      congrArg (fun r : S.image.PeriodicLink => r.target) hef
    exact PeriodicLattice.Bond.ext ((pointMap_bijective S).1 h1) ((pointMap_bijective S).1 h2)
  · intro e'
    obtain ⟨s, hs⟩ := (pointMap_bijective S).2 e'.source
    obtain ⟨t, ht⟩ := (pointMap_bijective S).2 e'.target
    have hadj : ∃ μ : Fin 4, t - s = PeriodicLattice.unitStep G.L G.m ((G.K : ℕ) : ℤ) μ ∨
        t - s = -PeriodicLattice.unitStep G.L G.m ((G.K : ℕ) : ℤ) μ := by
      obtain ⟨μ, hμ | hμ⟩ := e'.isNeighbour
      · exact ⟨μ, Or.inl ((pointMap_sub_eq_unitStep S _ _ μ).mp (by rw [hs, ht]; exact hμ))⟩
      · exact ⟨μ, Or.inr ((pointMap_sub_eq_neg_unitStep S _ _ μ).mp (by rw [hs, ht]; exact hμ))⟩
    exact ⟨⟨s, t, hadj⟩, PeriodicLattice.Bond.ext hs ht⟩
theorem isPositivelyOriented_iff_torusLinkMap (e : G.PeriodicLink) :
    e.IsPositivelyOriented ↔ (S.torusLinkMap e).IsPositivelyOriented := by
  rw [torusLinkMap_eq]
  exact exists_congr fun μ => (pointMap_sub_eq_unitStep S _ _ μ).symm
def faceImage (p : G.TorusFace) : S.image.TorusFace :=
  ⟨pointMap S p.origin, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
theorem isFaceImage_torusFaceMap (p : G.TorusFace) :
    S.IsFaceImage p (S.torusFaceMap p) :=
  Classical.epsilon_spec (p := S.IsFaceImage p) ⟨faceImage S p, rfl, rfl, rfl⟩
theorem torusFaceMap_eq (p : G.TorusFace) : S.torusFaceMap p = faceImage S p := by
  obtain ⟨h1, h2, h3⟩ := isFaceImage_torusFaceMap S p
  exact PeriodicLattice.Plaquette.ext (Subtype.ext h3) h1 h2
theorem torusFaceMap_bijective : Function.Bijective S.torusFaceMap := by
  have hfun : S.torusFaceMap = faceImage S := funext (torusFaceMap_eq S)
  rw [hfun]
  constructor
  · intro p q hpq
    have h1 : pointMap S p.origin = pointMap S q.origin :=
      congrArg (fun r : S.image.TorusFace => r.origin) hpq
    have h2 : p.firstAxis = q.firstAxis := congrArg (fun r : S.image.TorusFace => r.firstAxis) hpq
    have h3 : p.secondAxis = q.secondAxis := congrArg (fun r : S.image.TorusFace => r.secondAxis) hpq
    exact PeriodicLattice.Plaquette.ext ((pointMap_bijective S).1 h1) h2 h3
  · intro p'
    obtain ⟨x, hx⟩ := (pointMap_bijective S).2 p'.origin
    exact ⟨⟨x, p'.firstAxis, p'.secondAxis, p'.firstAxis_lt_secondAxis⟩,
      PeriodicLattice.Plaquette.ext hx rfl rfl⟩
theorem torusMap_image_vertices (p : G.TorusFace) :
    S.torusMap '' (Subtype.val '' p.vertices) =
      Subtype.val '' (S.torusFaceMap p).vertices := by
  have hv : (S.torusFaceMap p).vertices = pointMap S '' p.vertices := by
    rw [torusFaceMap_eq]
    simp only [PeriodicLattice.Plaquette.vertices, Set.image_insert_eq, Set.image_singleton,
      pointMap_add_unitStep]
    rfl
  rw [hv, Set.image_image, Set.image_image]
  rfl
theorem barycenter_torusFaceMap (p : G.TorusFace) :
    (S.torusFaceMap p).barycenter = S.torusMap p.barycenter := by
  rw [torusFaceMap_eq]
  have hs : S.scale * (PeriodicLattice.meshSize G.L ((G.K : ℕ) : ℤ) / 2) =
      PeriodicLattice.meshSize S.image.L ((S.image.K : ℕ) : ℤ) / 2 := by
    have := S.image_mesh
    change PeriodicLattice.meshSize S.image.L ((S.image.K : ℕ) : ℤ) =
      S.scale * PeriodicLattice.meshSize G.L ((G.K : ℕ) : ℤ) at this
    rw [this]
    ring
  change _ = S.torusMap (((p.origin : G.Torus) + _) + _)
  rw [torusMap_add, torusMap_add, torusDilation_pointOnAxis, torusDilation_pointOnAxis, hs]
  rfl
theorem scalingPreservesTorus : ScalingPreservesTorus := by
  intro G S
  exact ⟨existsUnique_torusLift S, isTorusLift_torusMap S, torusMap_bijective S,
    fun x y => by rw [torusMap_sub, torusEuclidNorm_torusDilation], torusMap_image_sublattice S,
    isLinkImage_torusLinkMap S, torusLinkMap_bijective S, isPositivelyOriented_iff_torusLinkMap S,
    isFaceImage_torusFaceMap S, torusMap_image_vertices S, torusFaceMap_bijective S,
    barycenter_torusFaceMap S⟩
end YangMills.Construction.MirrorGridsAllSides.TorusScaling
end
