import YangMills.Construction.QuaternionicWilsonModel.TheDefaultCasesAreUnusedProof
import YangMills.Construction.ReflectionPositivity.TwoNormsOfTestFunctions
import Mathlib
set_option autoImplicit false
open Filter Function Topology
open scoped Matrix
noncomputable section
namespace YangMills.Construction.SeparatedTuples.BasicFacts
open InfiniteLattice (AmbientSpace)
open Mirrors (ReflectingHyperplane)
open SeparatedTupleFunctionals (c1CompactSuppIn c1CompactSupp HasContPartials)
open TestFunctions (partialDerivR4)
theorem hasDerivAt_coordLine_of_contDiff {f : RealValued} (hf : ContDiff ℝ 1 f) (μ : Fin 4)
    (x : AmbientSpace) :
    HasDerivAt (fun t : ℝ => f (x + t • Pi.single μ (1 : ℝ))) (fderiv ℝ f x (Pi.single μ 1)) 0 := by
  have hd : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)) x
  have hl : HasDerivAt (fun t : ℝ => x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))
      (Pi.single μ (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)).const_add x
  exact HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd.hasFDerivAt hl (by simp)
theorem hasContPartials_of_contDiff {f : RealValued} (hf : ContDiff ℝ 1 f) :
    HasContPartials f := by
  intro μ
  refine ⟨fun x => (hasDerivAt_coordLine_of_contDiff hf μ x).differentiableAt, ?_⟩
  have he : partialDerivR4 μ f = fun x => fderiv ℝ f x (Pi.single μ 1) :=
    funext fun x => (hasDerivAt_coordLine_of_contDiff hf μ x).deriv
  rw [he]
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
theorem norm_sub_sub_mul_le_along_axis {f : RealValued} {μ : Fin 4}
    (hp : ∀ x : AmbientSpace, DifferentiableAt ℝ (fun t : ℝ => f (x + t • Pi.single μ (1 : ℝ))) 0)
    (y : AmbientSpace) (a d ε : ℝ)
    (hε : ∀ t ∈ Set.uIcc 0 a, ‖partialDerivR4 μ f (y + t • Pi.single μ (1 : ℝ)) - d‖ ≤ ε) :
    ‖f (y + a • Pi.single μ (1 : ℝ)) - f y - d * a‖ ≤ ε * |a| := by
  set e : AmbientSpace := Pi.single μ (1 : ℝ) with he
  let g : ℝ → ℝ := fun t => f (y + t • e) - d * t
  have hg : ∀ t ∈ Set.uIcc 0 a,
      HasDerivWithinAt g (partialDerivR4 μ f (y + t • e) - d) (Set.uIcc 0 a) t := by
    intro t _
    have h00 : HasDerivAt (fun s : ℝ => f ((y + t • e) + s • e))
        (partialDerivR4 μ f (y + t • e)) 0 := (hp (y + t • e)).hasDerivAt
    have h0 : HasDerivAt (fun s : ℝ => f ((y + t • e) + s • e))
        (partialDerivR4 μ f (y + t • e)) (t - t) := by
      rw [sub_self]
      exact h00
    have h2 := HasDerivAt.comp_sub_const t t h0
    have h3 : HasDerivAt (fun s : ℝ => f (y + s • e)) (partialDerivR4 μ f (y + t • e)) t := by
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
      show f (y + s • e) = f ((y + t • e) + (s - t) • e)
      congr 1
      rw [sub_smul]
      abel
    have h4 : HasDerivAt (fun s : ℝ => d * s) d t := by
      simpa using (hasDerivAt_id t).const_mul d
    have h5 : HasDerivAt g (partialDerivR4 μ f (y + t • e) - d) t := h3.sub h4
    exact h5.hasDerivWithinAt
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg (fun t ht => hε t ht)
    (convex_uIcc 0 a) Set.left_mem_uIcc Set.right_mem_uIcc
  have hg0 : g 0 = f y := by simp [g]
  have hga : g a - g 0 = f (y + a • e) - f y - d * a := by
    rw [hg0]
    simp only [g]
    ring
  rw [hga] at hb
  simpa using hb
theorem hasFDerivAt_of_hasContPartials {f : RealValued}
    (hf : HasContPartials f) (x : AmbientSpace) :
    HasFDerivAt f
      (∑ μ : Fin 4, partialDerivR4 μ f x • (ContinuousLinearMap.proj μ : AmbientSpace →L[ℝ] ℝ))
      x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hε : 0 < c / 4 := by positivity
  have hall : ∀ᶠ y in 𝓝 x, ∀ μ : Fin 4,
      ‖partialDerivR4 μ f y - partialDerivR4 μ f x‖ < c / 4 := by
    refine eventually_all.2 fun μ => ?_
    have hcont := (hf μ).2.continuousAt (x := x)
    have := hcont.eventually (Metric.ball_mem_nhds _ hε)
    filter_upwards [this] with y hy
    simpa [dist_eq_norm] using hy
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hall
  filter_upwards [Metric.ball_mem_nhds (0 : AmbientSpace) hδ] with h hh
  have hnorm : ‖h‖ < δ := by simpa using hh
  let W : ℕ → AmbientSpace := fun n ν => if (ν : ℕ) < n then h ν else 0
  have hW0 : W 0 = 0 := by
    funext ν
    simp [W]
  have hW4 : W 4 = h := by
    funext ν
    simp [W, ν.2]
  have hle : ∀ ν : Fin 4, |h ν| ≤ ‖h‖ := fun ν => by
    simpa using norm_le_pi_norm h ν
  have step : ∀ (n : ℕ) (hn : n < 4),
      ‖f (x + W (n + 1)) - f (x + W n) -
        partialDerivR4 ⟨n, hn⟩ f x * h ⟨n, hn⟩‖ ≤ c / 4 * |h ⟨n, hn⟩| := by
    intro n hn
    set μ : Fin 4 := ⟨n, hn⟩ with hμ
    have hWs : W (n + 1) = W n + h μ • (Pi.single μ (1 : ℝ) : AmbientSpace) := by
      funext ν
      by_cases hν : ν = μ
      · subst hν
        simp [W, hμ]
      · have hne : (ν : ℕ) ≠ n := fun e => hν (Fin.ext e)
        have hiff : (ν : ℕ) < n + 1 ↔ (ν : ℕ) < n := by omega
        simp [W, hiff, Pi.single_eq_of_ne hν]
    have hb := norm_sub_sub_mul_le_along_axis (f := f) (μ := μ) (hf μ).1 (x + W n) (h μ)
      (partialDerivR4 μ f x) (c / 4) (fun t ht => ?_)
    · rw [hWs, ← add_assoc]
      exact hb
    · have htabs : |t| ≤ |h μ| := by
        rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact abs_le_abs h2 (by linarith [abs_nonneg (h μ), le_abs_self (h μ)])
        · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
          linarith
      refine (hball ?_ μ).le
      rw [dist_eq_norm]
      refine lt_of_le_of_lt ?_ hnorm
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg h)).2 fun ν => ?_
      by_cases hν : ν = μ
      · subst hν
        have : (x + W n + t • (Pi.single μ (1 : ℝ) : AmbientSpace) - x) μ = t := by
          simp [W, hμ]
        rw [this]
        exact htabs.trans (hle μ)
      · have : (x + W n + t • (Pi.single μ (1 : ℝ) : AmbientSpace) - x) ν = W n ν := by
          simp [Pi.single_eq_of_ne hν]
        rw [this]
        simp only [W]
        split_ifs
        · exact hle ν
        · simp
  have s0 := step 0 (by norm_num)
  have s1 := step 1 (by norm_num)
  have s2 := step 2 (by norm_num)
  have s3 := step 3 (by norm_num)
  have hval : (∑ μ : Fin 4, partialDerivR4 μ f x •
      (ContinuousLinearMap.proj μ : AmbientSpace →L[ℝ] ℝ)) h =
      ∑ μ : Fin 4, partialDerivR4 μ f x * h μ := by
    simp
  rw [hval, Fin.sum_univ_four]
  have e4 : f (x + h) - f x = (f (x + W 4) - f (x + W 3)) + (f (x + W 3) - f (x + W 2)) +
      (f (x + W 2) - f (x + W 1)) + (f (x + W 1) - f (x + W 0)) := by
    rw [hW4, hW0, add_zero]
    ring
  have b0 := hle 0
  have b1 := hle 1
  have b2 := hle 2
  have b3 := hle 3
  simp only [Real.norm_eq_abs] at s0 s1 s2 s3 ⊢
  have hnn : 0 ≤ c / 4 := hε.le
  have m0 := mul_le_mul_of_nonneg_left b0 hnn
  have m1 := mul_le_mul_of_nonneg_left b1 hnn
  have m2 := mul_le_mul_of_nonneg_left b2 hnn
  have m3 := mul_le_mul_of_nonneg_left b3 hnn
  have s0' := abs_le.1 s0
  have s1' := abs_le.1 s1
  have s2' := abs_le.1 s2
  have s3' := abs_le.1 s3
  have z0 : ((⟨0, by norm_num⟩ : Fin 4)) = 0 := rfl
  have z1 : ((⟨1, by norm_num⟩ : Fin 4)) = 1 := rfl
  have z2 : ((⟨2, by norm_num⟩ : Fin 4)) = 2 := rfl
  have z3 : ((⟨3, by norm_num⟩ : Fin 4)) = 3 := rfl
  simp only [z0, z1, z2, z3, zero_add, Nat.reduceAdd] at s0' s1' s2' s3' m0 m1 m2 m3
  rw [abs_le]
  have hcnorm : c * ‖h‖ = c / 4 * ‖h‖ + c / 4 * ‖h‖ + c / 4 * ‖h‖ + c / 4 * ‖h‖ := by ring
  rw [e4, hcnorm]
  constructor <;> linarith [s0'.1, s0'.2, s1'.1, s1'.2, s2'.1, s2'.2, s3'.1, s3'.2]
theorem contDiff_of_hasContPartials {f : RealValued}
    (hf : HasContPartials f) : ContDiff ℝ 1 f := by
  have hd := hasFDerivAt_of_hasContPartials hf
  refine contDiff_one_iff_fderiv.2 ⟨fun x => (hd x).differentiableAt, ?_⟩
  have he : fderiv ℝ f = fun x =>
      ∑ μ : Fin 4, partialDerivR4 μ f x • (ContinuousLinearMap.proj μ : AmbientSpace →L[ℝ] ℝ) :=
    funext fun x => (hd x).fderiv
  rw [he]
  exact continuous_finsetSum _ fun μ _ => (hf μ).2.smul continuous_const
theorem mem_c1CompactSupp_of_isC1c {f : RealValued} (h : IsC1c f) :
    f ∈ c1CompactSupp ℝ :=
  ⟨⟨ContDiff.continuous h.1, h.2⟩, hasContPartials_of_contDiff h.1⟩
theorem isC1c_of_mem_c1CompactSupp {f : RealValued} (h : f ∈ c1CompactSupp ℝ) :
    IsC1c f :=
  ⟨contDiff_of_hasContPartials h.2, h.1.2⟩
theorem tsupport_smul_add_smul_subset (f g : RealValued) (α α' : ℝ) :
    tsupport (α • f + α' • g) ⊆ tsupport f ∪ tsupport g := by
  refine closure_minimal (fun x hx => ?_) (isClosed_closure.union isClosed_closure)
  by_contra h
  have hf0 : f x = 0 := by
    by_contra h'
    exact h (Or.inl (subset_closure h'))
  have hg0 : g x = 0 := by
    by_contra h'
    exact h (Or.inr (subset_closure h'))
  exact hx (by simp [hf0, hg0])
theorem isC1c_smul_add_smul {f g : RealValued} (hf : IsC1c f)
    (hg : IsC1c g) (α α' : ℝ) : IsC1c (α • f + α' • g) := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ 1 f := hf.1
    have h2 : ContDiff ℝ 1 g := hg.1
    exact (h1.const_smul α).add (h2.const_smul α')
  · have h1 : IsCompact (tsupport f) := hf.2
    have h2 : IsCompact (tsupport g) := hg.2
    exact (h1.union h2).of_isClosed_subset isClosed_closure (tsupport_smul_add_smul_subset f g α α')
theorem separatedOfLinearCombinationInOneComponent : SeparatedOfLinearCombinationInOneEntry := by
  intro A B f f' α α' h h'
  have hf := h.1 f (by simp)
  have hf' := h'.1 f' (by simp)
  refine ⟨fun g hg => ?_, ?_⟩
  · rcases List.mem_append.1 hg with hg | hg
    · exact h.1 g (List.mem_append_left _ hg)
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact isC1c_smul_add_smul hf hf' α α'
      · exact h.1 g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  · have p := h.2
    have p' := h'.2
    rw [List.pairwise_append, List.pairwise_cons] at p p' ⊢
    obtain ⟨pA, ⟨pf, pB⟩, pAB⟩ := p
    obtain ⟨-, ⟨pf', -⟩, pAB'⟩ := p'
    refine ⟨pA, ⟨fun g hg => ?_, pB⟩, fun a ha b hb => ?_⟩
    · exact Disjoint.mono_left (tsupport_smul_add_smul_subset f f' α α')
        (Set.disjoint_union_left.2 ⟨pf g hg, pf' g hg⟩)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact Disjoint.mono_right (tsupport_smul_add_smul_subset f f' α α')
          (Set.disjoint_union_right.2 ⟨pAB a ha f (by simp), pAB' a ha f' (by simp)⟩)
      · exact pAB a ha b (List.mem_cons_of_mem _ hb)
structure IsRigidMotion (r : AmbientSpace → AmbientSpace) : Prop where
  continuous : Continuous r
  contDiff_invMap : ContDiff ℝ 1 (invMap r)
  right_inverse : ∀ y, r (invMap r y) = y
  left_inverse : ∀ x, invMap r (r x) = x
theorem isRigidMotion_of_isEuclidIsometry
    (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    {r : AmbientSpace → AmbientSpace} (hr : IsEuclidIsometry r) : IsRigidMotion r := by
  obtain ⟨R, hR, v, hv⟩ := hm r hr
  have h1 : R * Rᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hR
  have h2 : Rᵀ * R = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hR
  let s : AmbientSpace → AmbientSpace := fun y => Rᵀ *ᵥ (y - v)
  have hrs : ∀ y, r (s y) = y := fun y => by
    simp [s, hv, Matrix.mulVec_mulVec, h1]
  have hsr : ∀ x, s (r x) = x := fun x => by
    simp [s, hv, Matrix.mulVec_mulVec, h2]
  have hinj : Injective r := LeftInverse.injective hsr
  have hinv : invMap r = s := by
    funext y
    calc invMap r y = invMap r (r (s y)) := by rw [hrs]
      _ = s y := Function.leftInverse_invFun hinj _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he : r = fun x => R *ᵥ x + v := funext hv
    rw [he]
    exact (Continuous.matrix_mulVec continuous_const continuous_id).add continuous_const
  · rw [hinv]
    have hl : ContDiff ℝ 1 (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Rᵀ)) :=
      ContinuousLinearMap.contDiff _
    exact hl.comp (contDiff_id.sub contDiff_const)
  · intro y
    rw [hinv]
    exact hrs y
  · intro x
    rw [hinv]
    exact hsr x
variable {r : AmbientSpace → AmbientSpace}
def IsRigidMotion.toHomeomorph (h : IsRigidMotion r) : AmbientSpace ≃ₜ AmbientSpace where
  toFun := r
  invFun := invMap r
  left_inv := h.left_inverse
  right_inv := h.right_inverse
  continuous_toFun := h.continuous
  continuous_invFun := h.contDiff_invMap.continuous
theorem IsRigidMotion.injective (h : IsRigidMotion r) : Injective r :=
  LeftInverse.injective h.left_inverse
theorem IsRigidMotion.tsupport_comp_invMap (h : IsRigidMotion r) (f : RealValued) :
    tsupport (f ∘ invMap r) = r '' tsupport f := by
  have hs : Function.support (f ∘ invMap r) = r '' Function.support f := by
    ext y
    constructor
    · intro hy
      exact ⟨invMap r y, hy, h.right_inverse y⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [Function.mem_support, h.left_inverse] using hx
  rw [tsupport, hs, tsupport]
  exact (h.toHomeomorph.image_closure (Function.support f)).symm
theorem isDisjointlySupported_pushList (h : IsRigidMotion r) {X : List RealValued}
    (hX : IsDisjointlySupported X) : IsDisjointlySupported (pushList r X) := by
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    have hc := hX.1 f hf
    refine ⟨ContDiff.comp (show ContDiff ℝ 1 f from hc.1) h.contDiff_invMap, ?_⟩
    show IsCompact (tsupport (f ∘ invMap r))
    rw [h.tsupport_comp_invMap]
    exact IsCompact.image hc.2 h.continuous
  · have hp : X.Pairwise fun a b =>
        Disjoint (tsupport (a ∘ invMap r)) (tsupport (b ∘ invMap r)) :=
      hX.2.imp (by
        intro a b hab
        rw [h.tsupport_comp_invMap, h.tsupport_comp_invMap]
        exact (Set.disjoint_image_iff h.injective).2 hab)
    exact List.pairwise_map.2 hp
theorem push_val (h : IsRigidMotion r) (X : SepTuple) : (push r X).1 = pushList r X.1 := by
  unfold push
  rw [dif_pos (isDisjointlySupported_pushList h X.2)]
theorem mem_push (h : IsRigidMotion r) {X : SepTuple} {g : RealValued} :
    g ∈ (push r X).1 ↔ ∃ f ∈ X.1, f ∘ invMap r = g := by
  rw [push_val h, pushList, List.mem_map]
theorem composable_push (h : IsRigidMotion r) (X Y : SepTuple) :
    SepTuple.Composable (push r X) (push r Y) ↔ SepTuple.Composable X Y := by
  constructor
  · intro hd f hf g hg
    have hfg := hd _ ((mem_push h).2 ⟨f, hf, rfl⟩) _ ((mem_push h).2 ⟨g, hg, rfl⟩)
    rw [h.tsupport_comp_invMap, h.tsupport_comp_invMap] at hfg
    exact (Set.disjoint_image_iff h.injective).1 hfg
  · intro hd f' hf' g' hg'
    obtain ⟨f, hf, rfl⟩ := (mem_push h).1 hf'
    obtain ⟨g, hg, rfl⟩ := (mem_push h).1 hg'
    rw [h.tsupport_comp_invMap, h.tsupport_comp_invMap]
    exact (Set.disjoint_image_iff h.injective).2 (hd f hf g hg)
theorem juxt_push (h : IsRigidMotion r) (X Y : SepTuple) :
    SepTuple.juxt (push r X) (push r Y) = push r (SepTuple.juxt X Y) := by
  by_cases hd : SepTuple.Composable X Y
  · apply Subtype.ext
    rw [SepTuple.juxt_val ((composable_push h X Y).2 hd), push_val h, push_val h, push_val h,
      SepTuple.juxt_val hd]
    simp [pushList]
  · have hd' := mt (composable_push h X Y).1 hd
    have e1 : SepTuple.juxt X Y = SepTuple.nil := by simp [SepTuple.juxt, hd]
    have e2 : SepTuple.juxt (push r X) (push r Y) = SepTuple.nil := by
      simp [SepTuple.juxt, hd']
    rw [e1, e2, push_nil]
theorem componentAt_push (h : IsRigidMotion r) (X : SepTuple) {i : ℕ} (hi : i < X.size) :
    (push r X).componentAt i = X.componentAt i ∘ invMap r := by
  have hi' : i < X.1.length := hi
  simp only [SepTuple.componentAt]
  rw [push_val h, List.getD_eq_getElem _ _ (by simpa [pushList] using hi'),
    List.getD_eq_getElem _ _ hi']
  simp [pushList]
theorem isometryActionOnTuples
    (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine) :
    IsometryActionOnTuples := by
  intro r hr X Y
  have h := isRigidMotion_of_isEuclidIsometry hm hr
  refine ⟨isDisjointlySupported_pushList h X.2, fun i hi => ?_, composable_push h X Y,
    fun _ => juxt_push h X Y⟩
  rw [componentAt_push h X hi, h.tsupport_comp_invMap]
theorem isEuclidIsometry_reflect (hmf : Mirrors.UnitNormalAndLattice.Statement)
    (M : ReflectingHyperplane) : IsEuclidIsometry M.reflect := by apply _root_.YangMills.Construction.ConditionDefaults.isEuclidIsometry_reflect <;> assumption
theorem reflectedJuxtapositionAtHyperplane
    (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (hmf : Mirrors.UnitNormalAndLattice.Statement) :
    ReflectedJuxtapositionAtHyperplane := by
  intro M X Y hX hY
  have h := isRigidMotion_of_isEuclidIsometry hm (isEuclidIsometry_reflect hmf M)
  have himg := (hmf M 1 one_pos).2.2.2.1.2.2.2
  have hside : ∀ g ∈ (push M.reflect X).1,
      tsupport g ⊆ {x | M.normalVec ⬝ᵥ x < M.offset} := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := (mem_push h).1 hg
    rw [h.tsupport_comp_invMap, ← himg]
    exact Set.image_mono (hX f hf)
  refine ⟨hside, fun g hg k hk => ?_⟩
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h1 : M.normalVec ⬝ᵥ x < M.offset := hside g hg hx
  have h2 : M.normalVec ⬝ᵥ x > M.offset := hY k hk hx'
  exact lt_asymm h1 h2
theorem pushSpan_basisVec (r : AmbientSpace → AmbientSpace) (X : SepTuple) :
    pushSpan r (basisVec X) = basisVec (push r X) :=
  linearExtend_basisVec _ X
theorem formalSpan_linearMap_ext {A B : FormalSpan →ₗ[ℂ] FormalSpan}
    (h : ∀ X, A (basisVec X) = B (basisVec X)) : A = B :=
  Finsupp.lhom_ext' fun X => LinearMap.ext_ring (by simpa [basisVec] using h X)
theorem single_eq_smul_basisVec (X : SepTuple) (c : ℂ) :
    (Finsupp.single X c : FormalSpan) = c • basisVec X := by
  simp [basisVec]
theorem isEuclidIsometry_comp {r r' : AmbientSpace → AmbientSpace} (hr : IsEuclidIsometry r)
    (hr' : IsEuclidIsometry r') : IsEuclidIsometry (r ∘ r') :=
  fun _ _ => (hr _ _).trans (hr' _ _)
theorem isEuclidIsometry_invMap (h : IsRigidMotion r) (hr : IsEuclidIsometry r) :
    IsEuclidIsometry (invMap r) :=
  fun x y => by
    have hxy := hr (invMap r x) (invMap r y)
    rw [h.right_inverse, h.right_inverse] at hxy
    exact hxy.symm
theorem push_comp {r r' : AmbientSpace → AmbientSpace} (h : IsRigidMotion r)
    (h' : IsRigidMotion r') (hc : IsRigidMotion (r ∘ r')) (X : SepTuple) :
    push (r ∘ r') X = push r (push r' X) := by
  apply Subtype.ext
  rw [push_val hc, push_val h, push_val h']
  have hinv : invMap (r ∘ r') = invMap r' ∘ invMap r := by
    funext y
    have hy := hc.left_inverse (invMap r' (invMap r y))
    simpa [Function.comp, h'.right_inverse, h.right_inverse] using hy
  simp only [pushList, hinv, List.map_map]
  rfl
theorem push_translate_zero
    (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (X : SepTuple) : push (translate 0) X = X := by
  apply Subtype.ext
  rw [push_val (isRigidMotion_of_isEuclidIsometry hm (isEuclidIsometry_translate 0)),
    pushList_translate]
  simp
theorem pushSpan_comp
    (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    {r r' : AmbientSpace → AmbientSpace} (hr : IsEuclidIsometry r) (hr' : IsEuclidIsometry r')
    (F : FormalSpan) :
    pushSpan (r ∘ r') F = pushSpan r (pushSpan r' F) := by
  have h := isRigidMotion_of_isEuclidIsometry hm hr
  have h' := isRigidMotion_of_isEuclidIsometry hm hr'
  have hc := isRigidMotion_of_isEuclidIsometry hm (isEuclidIsometry_comp hr hr')
  have he : pushSpan (r ∘ r') = pushSpan r ∘ₗ pushSpan r' :=
    formalSpan_linearMap_ext fun X => by
      simp only [LinearMap.comp_apply, pushSpan_basisVec, push_comp h h' hc X]
  exact LinearMap.congr_fun he F
theorem conjugation_pushSpan (r : AmbientSpace → AmbientSpace) (F : FormalSpan) :
    conjugation (pushSpan r F) = pushSpan r (conjugation F) := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.conjugation_pushSpan <;> assumption
theorem push_image_supportedIn
    (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (hr : IsEuclidIsometry r) (O : Set AmbientSpace) :
    push r '' supportedIn O = supportedIn (r '' O) := by
  have h := isRigidMotion_of_isEuclidIsometry hm hr
  ext Y
  constructor
  · rintro ⟨X, hX, rfl⟩ g hg
    obtain ⟨f, hf, rfl⟩ := (mem_push h).1 hg
    rw [h.tsupport_comp_invMap]
    exact Set.image_mono (hX f hf)
  · intro hY
    have hi := isEuclidIsometry_invMap h hr
    have h' := isRigidMotion_of_isEuclidIsometry hm hi
    refine ⟨push (invMap r) Y, fun g hg => ?_, ?_⟩
    · obtain ⟨f, hf, rfl⟩ := (mem_push h').1 hg
      rw [h'.tsupport_comp_invMap]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hY f hf hx
      rw [h.left_inverse]
      exact hz
    · have hcomp : r ∘ invMap r = translate 0 := by
        funext y
        simp [translate, h.right_inverse]
      have hc := isRigidMotion_of_isEuclidIsometry hm (isEuclidIsometry_comp hr hi)
      rw [← push_comp h h' hc, hcomp]
      exact push_translate_zero hm Y
theorem map_pushSpan_spanIn
    (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (hr : IsEuclidIsometry r) (O : Set AmbientSpace) :
    (spanIn O).map (pushSpan r) = spanIn (r '' O) := by
  have himg := push_image_supportedIn hm hr O
  rw [spanIn, spanIn, Submodule.map_span]
  congr 1
  ext G
  constructor
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    exact ⟨⟨push r X.1, himg ▸ ⟨X.1, X.2, rfl⟩⟩, (pushSpan_basisVec r X.1).symm⟩
  · rintro ⟨Y, rfl⟩
    obtain ⟨X, hX, hXY⟩ : Y.1 ∈ push r '' supportedIn O := himg.symm ▸ Y.2
    exact ⟨basisVec X, ⟨⟨X, hX⟩, rfl⟩, by
      simp only [pushSpan_basisVec, hXY]⟩
theorem formalMul_pushSpan (h : IsRigidMotion r) (G G' : FormalSpan) :
    formalMul (pushSpan r G) (pushSpan r G') =
      pushSpan r (formalMul G G') := by
  induction G using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single X c =>
    induction G' using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single Y d =>
      rw [single_eq_smul_basisVec, single_eq_smul_basisVec]
      simp only [map_smul, LinearMap.smul_apply, pushSpan_basisVec,
        formalMul_basisVec, juxt_push h]
theorem pushSpanProperties
    (hm : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine) :
    PushSpanProperties := by
  intro r r' hr hr' v v' F
  have h := isRigidMotion_of_isEuclidIsometry hm hr
  refine ⟨pushSpan_comp hm hr hr' F, ?_, ?_, conjugation_pushSpan r F,
    fun O _ => ⟨push_image_supportedIn hm hr O, map_pushSpan_spanIn hm hr O⟩,
    fun O O' _ _ _ G _ G' _ => formalMul_pushSpan h G G'⟩
  · rw [← pushSpan_comp hm (isEuclidIsometry_translate v) (isEuclidIsometry_translate v') F]
    have he : translate v ∘ translate v' = translate (v + v') := by
      funext x
      simp only [Function.comp, translate]
      abel
    rw [he]
  · have he : pushSpan (translate 0) = LinearMap.id :=
      formalSpan_linearMap_ext fun X => by
        simp [pushSpan_basisVec, push_translate_zero hm X]
    exact LinearMap.congr_fun he F
theorem componentAt_mem {X : SepTuple} {i : ℕ} (hi : i < X.size) : X.componentAt i ∈ X.1 := by
  have hi' : i < X.1.length := hi
  simp only [SepTuple.componentAt]
  rw [List.getD_eq_getElem _ _ hi']
  exact List.getElem_mem hi'
theorem sharpNormEquivalentToC1Norm (h : TestNormComparison.NormsEquivalent) :
    SharpNormEquivalentToC1Norm := by
  intro M hM
  have hc := (h M hM).2
  have key : ∀ (r₀ : ℕ) (s : ℕ → SepTuple) (X : SepTuple), TendstoAdmissibly r₀ s X ↔
      TendstoAdmissiblyWithNorm (TestFunctions.sharpNormR4 M) r₀ s X := by
    intro r₀ s X
    have hk : 1 ≤ r₀ → (∀ r, r₀ ≤ r → (s r).size = X.size) → ∀ i : Fin X.size,
        (Tendsto (fun r => TestFunctions.c1NormR4 ((s r).componentAt i - X.componentAt i)) atTop (𝓝 0) ↔
          Tendsto (fun r => TestFunctions.sharpNormR4 M ((s r).componentAt i - X.componentAt i)) atTop
            (𝓝 0)) := by
      intro h1 hl i
      refine hc r₀ (fun r => (s r).componentAt i) (X.componentAt i) h1 (fun r hr => ?_) ?_
      · have hi : (i : ℕ) < (s r).size := by
          rw [hl r hr]
          exact i.2
        exact mem_c1CompactSupp_of_isC1c ((s r).2.1 _ (componentAt_mem hi))
      · exact mem_c1CompactSupp_of_isC1c (X.2.1 _ (componentAt_mem i.2))
    constructor
    · rintro ⟨h1, hl, A, hA, hd, hs, ht⟩
      exact ⟨h1, hl, A, hA, hd, hs, fun i => (hk h1 hl i).1 (ht i)⟩
    · rintro ⟨h1, hl, A, hA, hd, hs, ht⟩
      exact ⟨h1, hl, A, hA, hd, hs, fun i => (hk h1 hl i).2 (ht i)⟩
  refine ⟨key, fun σ => ⟨fun hσ r₀ s X hX => ?_, fun hσ r₀ s X hX => ?_⟩⟩
  · exact hσ r₀ s X ((key r₀ s X).2 hX)
  · exact hσ r₀ s X ((key r₀ s X).1 hX)
theorem exists_open_nhds_disjoint_closures {k : ℕ} (K : Fin k → Set AmbientSpace)
    (hK : ∀ j, IsCompact (K j)) (hd : ∀ j l, j ≠ l → Disjoint (K j) (K l)) :
    ∃ O : Fin k → Set AmbientSpace, (∀ j, IsOpen (O j)) ∧ (∀ j, K j ⊆ O j) ∧
      Pairwise (Disjoint on fun j => closure (O j)) := by
  have h1 : ∀ j l, ∀ᶠ δ in 𝓝[>] (0 : ℝ), j ≠ l →
      Disjoint (Metric.cthickening δ (K j)) (Metric.cthickening δ (K l)) := by
    intro j l
    by_cases hjl : j = l
    · exact Eventually.of_forall fun _ h => absurd hjl h
    · obtain ⟨δ₀, h0, hδ⟩ := Disjoint.exists_cthickenings (hd j l hjl) (hK j) (hK l).isClosed
      filter_upwards [Ioo_mem_nhdsGT h0] with δ hδ' _
      exact hδ.mono (Metric.cthickening_mono hδ'.2.le _) (Metric.cthickening_mono hδ'.2.le _)
  have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j l, j ≠ l →
      Disjoint (Metric.cthickening δ (K j)) (Metric.cthickening δ (K l)) :=
    eventually_all.2 fun j => eventually_all.2 (h1 j)
  obtain ⟨δ, hδ, hpos⟩ := (h2.and self_mem_nhdsWithin).exists
  refine ⟨fun j => Metric.thickening δ (K j), fun j => Metric.isOpen_thickening,
    fun j => Metric.self_subset_thickening hpos _, fun j l hjl => ?_⟩
  exact (hδ j l hjl).mono (Metric.closure_thickening_subset_cthickening δ _)
    (Metric.closure_thickening_subset_cthickening δ _)
theorem ofFn_update_eq_take_append_drop {k : ℕ} [DecidableEq (Fin k)] (g : Fin k → RealValued)
    (i : Fin k) (y : RealValued) :
    List.ofFn (update g i y) = (List.ofFn g).take i ++ y :: (List.ofFn g).drop (i + 1) := by
  have h : List.ofFn (update g i y) = (List.ofFn g).set i y := by
    refine List.ext_getElem (by simp) fun n h1 h2 => ?_
    by_cases hn : (i : ℕ) = n
    · simp [Function.update_apply, Fin.ext_iff, hn]
    · have hn' : n ≠ (i : ℕ) := fun e => hn e.symm
      simp [Fin.ext_iff, hn, hn']
  rw [h, List.set_eq_take_append_cons_drop, if_pos (by simp)]
theorem ofFn_update_coe_eq {k : ℕ} [DecidableEq (Fin k)] {O : Fin k → Set AmbientSpace}
    (m : (j : Fin k) → c1CompactSubmodule (O j)) (i : Fin k) (x : c1CompactSubmodule (O i)) :
    List.ofFn (fun j => ((update m i x j : c1CompactSubmodule (O j)) : RealValued)) =
      (List.ofFn fun j => (m j : RealValued)).take i ++ (x : RealValued) ::
        (List.ofFn fun j => (m j : RealValued)).drop (i + 1) := by
  have he : (fun j => ((update m i x j : c1CompactSubmodule (O j)) : RealValued)) =
      update (fun j => (m j : RealValued)) i (x : RealValued) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  rw [he]
  exact ofFn_update_eq_take_append_drop _ i _
theorem isDisjointlySupported_ofFn {k : ℕ} {O : Fin k → Set AmbientSpace}
    (hd : Pairwise (Disjoint on fun i => closure (O i)))
    (f : (i : Fin k) → c1CompactSubmodule (O i)) :
    IsDisjointlySupported (List.ofFn fun i => (f i : RealValued)) := by
  refine ⟨fun g hg => ?_, List.pairwise_ofFn.2 fun i j hij => ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    exact isC1c_of_mem_c1CompactSupp (f i).2.1
  · have hi : tsupport (f i : RealValued) ⊆ closure (O i) := (f i).2.2.trans subset_closure
    have hj : tsupport (f j : RealValued) ⊆ closure (O j) := (f j).2.2.trans subset_closure
    exact Disjoint.mono hi hj (hd (ne_of_lt hij))
theorem isMultilinearOnC1Spaces_of_isEntrywiseLinear {σ : TupleFunctional}
    (hσ : σ.IsEntrywiseLinear) {k : ℕ}
    (O : Fin k → Set AmbientSpace) (hd : Pairwise (Disjoint on fun i => closure (O i))) :
    IsMultilinearOnC1Spaces σ O := by
  let T : ((i : Fin k) → c1CompactSubmodule (O i)) → SepTuple := fun f =>
    ⟨List.ofFn fun i => (f i : RealValued), isDisjointlySupported_ofFn hd f⟩
  refine ⟨{ toFun := fun f => σ (T f), map_update_add' := ?_, map_update_smul' := ?_ },
    fun f => ⟨T f, rfl, rfl⟩⟩
  · intro inst m i x y
    have e : ((x + y : c1CompactSubmodule (O i)) : RealValued) =
        (1 : ℝ) • (x : RealValued) + (1 : ℝ) • (y : RealValued) := by simp
    have h3 := (ofFn_update_coe_eq m i (x + y)).trans (by rw [e])
    have hs := hσ _ _ (x : RealValued) (y : RealValued) 1 1 (T (update m i x))
      (T (update m i y)) (T (update m i (x + y))) (ofFn_update_coe_eq m i x)
      (ofFn_update_coe_eq m i y) h3
    rw [one_mul, one_mul] at hs
    exact hs
  · intro inst m i c x
    have e : ((c • x : c1CompactSubmodule (O i)) : RealValued) =
        c • (x : RealValued) + (0 : ℝ) • (x : RealValued) := by simp
    have h3 := (ofFn_update_coe_eq m i (c • x)).trans (by rw [e])
    have hs := hσ _ _ (x : RealValued) (x : RealValued) c 0 (T (update m i x))
      (T (update m i x)) (T (update m i (c • x))) (ofFn_update_coe_eq m i x)
      (ofFn_update_coe_eq m i x) h3
    rw [zero_mul, add_zero] at hs
    exact hs
theorem ofFn_getD_eq_self (L : List RealValued) :
    List.ofFn (fun j : Fin L.length => L.getD j 0) = L := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  simp
theorem getD_mem_of_lt {L : List RealValued} {j : ℕ} (hj : j < L.length) : L.getD j 0 ∈ L := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj
theorem disjoint_tsupport_getD {L : List RealValued}
    (h : L.Pairwise fun f g => Disjoint (tsupport f) (tsupport g)) {j l : ℕ}
    (hj : j < L.length) (hl : l < L.length) (hjl : j ≠ l) :
    Disjoint (tsupport (L.getD j 0)) (tsupport (L.getD l 0)) := by
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hl]
  rcases lt_or_gt_of_ne hjl with hlt | hlt
  · exact List.pairwise_iff_getElem.1 h _ _ hj hl hlt
  · exact (List.pairwise_iff_getElem.1 h _ _ hl hj hlt).symm
theorem getD_append_cons_eq_of_ne (A B : List RealValued) (f f' : RealValued) {j : ℕ}
    (hj : j ≠ A.length) : (A ++ f' :: B).getD j 0 = (A ++ f :: B).getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h
  · rfl
  · obtain ⟨n, hn⟩ : ∃ n, j - A.length = n + 1 := ⟨j - A.length - 1, by omega⟩
    simp [hn]
theorem isEntrywiseLinear_of_isMultilinearOnC1Spaces {σ : TupleFunctional}
    (h : ∀ k : ℕ, 1 ≤ k → ∀ O : Fin k → Set AmbientSpace, (∀ i, IsOpen (O i)) →
      Pairwise (Disjoint on fun i => closure (O i)) → IsMultilinearOnC1Spaces σ O) :
    σ.IsEntrywiseLinear := by
  classical
  intro A B f f' α α' X X' Z hX hX' hZ
  obtain ⟨L, hL⟩ : ∃ L, L = A ++ f :: B := ⟨_, rfl⟩
  obtain ⟨L', hL'⟩ : ∃ L', L' = A ++ f' :: B := ⟨_, rfl⟩
  rw [← hL] at hX
  rw [← hL'] at hX'
  have hlen : L'.length = L.length := by simp [hL, hL']
  have hk1 : 1 ≤ L.length := by
    simp [hL]
    omega
  have hi0 : A.length < L.length := by simp [hL]
  obtain ⟨i, hiv⟩ : ∃ i : Fin L.length, (i : ℕ) = A.length := ⟨⟨A.length, hi0⟩, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Fin L.length → RealValued, ∀ j, p j = L.getD j 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨p', hp'⟩ : ∃ p' : Fin L.length → RealValued, ∀ j, p' j = L'.getD j 0 :=
    ⟨_, fun _ => rfl⟩
  have hpi : p i = f := by
    rw [hp, hiv, hL]
    simp
  have hpi' : p' i = f' := by
    rw [hp', hiv, hL']
    simp
  have hpne : ∀ j, j ≠ i → p' j = p j := by
    intro j hj
    have hg := getD_append_cons_eq_of_ne A B f f' (j := j)
      fun e => hj (Fin.ext (e.trans hiv.symm))
    rw [← hL, ← hL'] at hg
    rw [hp, hp']
    exact hg
  have hpX : ∀ j, p j ∈ X.1 := fun j => by
    rw [hX, hp]
    exact getD_mem_of_lt j.2
  have hlt : ∀ j : Fin L.length, (j : ℕ) < L'.length := fun j => by
    rw [hlen]
    exact j.2
  have hpX' : ∀ j, p' j ∈ X'.1 := fun j => by
    rw [hX', hp']
    exact getD_mem_of_lt (hlt j)
  have hdp : ∀ j l, j ≠ l → Disjoint (tsupport (p j)) (tsupport (p l)) := by
    intro j l hjl
    rw [hp, hp]
    exact disjoint_tsupport_getD (hX ▸ X.2.2) j.2 l.2 fun e => hjl (Fin.ext e)
  have hdp' : ∀ j l, j ≠ l → Disjoint (tsupport (p' j)) (tsupport (p' l)) := by
    intro j l hjl
    rw [hp', hp']
    exact disjoint_tsupport_getD (hX' ▸ X'.2.2) (hlt j) (hlt l) fun e => hjl (Fin.ext e)
  have hKc : ∀ j, IsCompact (tsupport (p j) ∪ tsupport (p' j)) := fun j =>
    IsCompact.union (X.2.1 _ (hpX j)).2 (X'.2.1 _ (hpX' j)).2
  have hKd : ∀ j l, j ≠ l → Disjoint (tsupport (p j) ∪ tsupport (p' j))
      (tsupport (p l) ∪ tsupport (p' l)) := by
    intro j l hjl
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨hdp j l hjl, ?_⟩,
      Set.disjoint_union_right.2 ⟨?_, hdp' j l hjl⟩⟩
    · by_cases hl : l = i
      · have hj : j ≠ i := hl ▸ hjl
        rw [← hpne j hj]
        exact hdp' j l hjl
      · rw [hpne l hl]
        exact hdp j l hjl
    · by_cases hl : l = i
      · have hj : j ≠ i := hl ▸ hjl
        rw [hpne j hj]
        exact hdp j l hjl
      · rw [← hpne l hl]
        exact hdp' j l hjl
  obtain ⟨O, hOo, hKO, hOd⟩ := exists_open_nhds_disjoint_closures _ hKc hKd
  obtain ⟨Φ, hΦ⟩ := h L.length hk1 O hOo hOd
  obtain ⟨m, hm⟩ : ∃ m : (j : Fin L.length) → c1CompactSubmodule (O j),
      ∀ j, (m j : RealValued) = p j :=
    ⟨fun j => ⟨p j, mem_c1CompactSupp_of_isC1c (X.2.1 _ (hpX j)),
      Set.subset_union_left.trans (hKO j)⟩, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : c1CompactSubmodule (O i), (x : RealValued) = f :=
    ⟨⟨f, mem_c1CompactSupp_of_isC1c (hpi ▸ X.2.1 _ (hpX i)),
      hpi ▸ Set.subset_union_left.trans (hKO i)⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : c1CompactSubmodule (O i), (y : RealValued) = f' :=
    ⟨⟨f', mem_c1CompactSupp_of_isC1c (hpi' ▸ X'.2.1 _ (hpX' i)),
      hpi' ▸ Set.subset_union_right.trans (hKO i)⟩, rfl⟩
  have hofn : (List.ofFn fun j => (m j : RealValued)) = L := by
    simp only [hm, hp]
    exact ofFn_getD_eq_self L
  have hupd : ∀ w : c1CompactSubmodule (O i),
      List.ofFn (fun j => ((update m i w j : c1CompactSubmodule (O j)) : RealValued)) =
        A ++ (w : RealValued) :: B := by
    intro w
    rw [ofFn_update_coe_eq, hofn, hiv]
    have ht : L.take A.length = A := by simp [hL]
    have hd : L.drop (A.length + 1) = B := by simp [hL]
    rw [ht, hd]
  have val : ∀ (w : c1CompactSubmodule (O i)) (T : SepTuple), T.1 = A ++ (w : RealValued) :: B →
      Φ (update m i w) = σ T := by
    intro w T hT
    obtain ⟨T', hT', he⟩ := hΦ (update m i w)
    have hTT : T' = T := Subtype.ext (hT'.trans ((hupd w).trans hT.symm))
    rw [he, hTT]
  have e1 := val x X (by rw [hx, hX, hL])
  have e2 := val y X' (by rw [hy, hX', hL'])
  have e3 := val (α • x + α' • y) Z (by
    rw [hZ]
    simp [hx, hy])
  rw [← e1, ← e2, ← e3, Φ.map_update_add, Φ.map_update_smul, Φ.map_update_smul]
  simp [smul_eq_mul]
theorem entrywiseLinearIffMultilinearOnC1 : EntrywiseLinearIffMultilinearOnC1 := fun _ =>
  ⟨fun hσ _ _ O _ hd => isMultilinearOnC1Spaces_of_isEntrywiseLinear hσ O hd,
    isEntrywiseLinear_of_isMultilinearOnC1Spaces⟩
theorem mainFacts (h₁ : Tower.OrthogonalMotions.Classification)
    (h₂ : Mirrors.UnitNormalAndLattice.Statement)
    (h₃ : TestNormComparison.NormsEquivalent) : MainFacts :=
  ⟨isometryActionOnTuples h₁.2.1, separatedOfLinearCombinationInOneComponent,
    reflectedJuxtapositionAtHyperplane h₁.2.1 h₂, entrywiseLinearIffMultilinearOnC1,
    pushSpanProperties h₁.2.1, sharpNormEquivalentToC1Norm h₃⟩
end YangMills.Construction.SeparatedTuples.BasicFacts
end
