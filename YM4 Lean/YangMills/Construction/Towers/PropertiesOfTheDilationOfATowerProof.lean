import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrabilityProof
import YangMills.Construction.Lattice.AxialPathReversalProof
import YangMills.Construction.Lattice.AxialPathUniquenessProof
import YangMills.Construction.Towers.DilationCarriesSetsAtAStepOfTheWholeSpaceProof
import YangMills.Construction.Towers.PropertiesOfTheDilationOfATower
import Mathlib
set_option autoImplicit false
open Set
open scoped Pointwise
namespace YangMills.Construction.Tower.ScalingProperties
section Transport
variable {X Y : Type}
theorem transportsFunctionsOn_of_equiv (e : X ≃ Y) (S : Set X) : TransportsFunctionsOn e S where
  injOn := e.injective.injOn
  existsUnique := fun V f => by
    refine ⟨transportFun e S f, fun σ => transportFun_apply_image e S f σ, fun g hg => ?_⟩
    funext y
    obtain ⟨σ, rfl⟩ := (e.image S).surjective y
    rw [hg σ, transportFun_apply_image]
  bijective := fun V => (transportFun e S).bijective
theorem conjMap_apply_apply (e : X ≃ Y) (s : X → X) (x : X) :
    conjMap e s (e x) = e (s x) := by
  simp [conjMap]
theorem existsUnique_eq_conjMap (e : X ≃ Y) (s' : Y → Y) : ∃! s : X → X, s' = conjMap e s := by
  refine ⟨e.symm ∘ s' ∘ e, ?_, ?_⟩
  · funext y
    simp [conjMap]
  · rintro s rfl
    funext x
    simp [conjMap]
theorem conjMap_image_image_iff (e : X ≃ Y) (s : X → X) (A : Set X) :
    conjMap e s '' (e '' A) = e '' A ↔ s '' A = A := by
  have h : conjMap e s '' (e '' A) = e '' (s '' A) := by
    rw [image_image, image_image]
    exact image_congr fun x _ => conjMap_apply_apply e s x
  rw [h]
  exact (image_injective.2 e.injective).eq_iff
theorem transportList_image_chains (e : X ≃ Y) (R : X → X → Prop) (R' : Y → Y → Prop)
    (h : ∀ a b, R' (e a) (e b) ↔ R a b) :
    transportList e '' {Γ | Γ.IsChain R} = {Γ | Γ.IsChain R'} := by
  ext Γ'
  constructor
  · rintro ⟨Γ, hΓ, rfl⟩
    show (Γ.map e).IsChain R'
    rw [List.isChain_map]
    exact List.IsChain.imp (fun a b hab => (h a b).2 hab) hΓ
  · intro hΓ'
    have hΓ'' : Γ'.IsChain R' := hΓ'
    refine ⟨Γ'.map e.symm, ?_, ?_⟩
    · show (Γ'.map e.symm).IsChain R
      rw [List.isChain_map]
      exact List.IsChain.imp (fun a b hab => (h _ _).1 (by simpa using hab)) hΓ''
    · simp [transportList]
theorem transportList_injective (e : X ≃ Y) : Function.Injective (transportList e) :=
  List.map_injective_iff.2 e.injective
end Transport
theorem euclidNormVec_smul {c : ℝ} (hc : 0 ≤ c) (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (c • v) = c * TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.WightmanReconstruction.SmoothToolkit.euclidNormVec_smul_of_nonneg <;> assumption
theorem scaleFactor_pos {L : ℕ} (hL : 0 < L) (m : ℕ) : 0 < (L : ℝ) ^ m :=
  pow_pos (by exact_mod_cast hL) m
theorem meshAt_pos {L : ℕ} (hL : 0 < L) (k i : ℕ) : 0 < meshAt L k i := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.meshAt_pos <;> assumption
section PeriodicSteps
variable {L m : ℕ} {d : ℤ}
theorem coe_zsmul_unitStep_apply (c : ℤ) (μ ν : Fin 4) :
    ((c • PeriodicLattice.unitStep L m d μ : PeriodicLattice.Site L m d) :
        PeriodicLattice.FourTorus L m) ν =
      if ν = μ then (((c : ℝ) * PeriodicLattice.meshSize L d : ℝ) :
        AddCircle (PeriodicLattice.torusSide L m))
      else 0 := by apply _root_.YangMills.Construction.PeriodicLattice.AxialUniqueness.zsmul_unitStep_apply <;> assumption
theorem eq_zero_of_mul_meshSize_coe_eq_zero (hL : 0 < L) (t : ℤ)
    (hN : |(t : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + d))
    (h : (((t : ℝ) * PeriodicLattice.meshSize L d : ℝ) :
      AddCircle (PeriodicLattice.torusSide L m)) = 0) :
    t = 0 := by apply _root_.YangMills.Construction.PeriodicLattice.AxialReversal.int_eq_zero_of_smul_meshSize_coe_eq_zero <;> assumption
theorem zsmul_unitStep_inj (hL : 0 < L) {μ ν : Fin 4} {c c' : ℤ}
    (hN : |(c : ℝ)| + |(c' : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + d))
    (h : c • PeriodicLattice.unitStep L m d μ = c' • PeriodicLattice.unitStep L m d ν) :
    c = c' ∧ (c = 0 ∨ μ = ν) := by
  have hc : ∀ ρ, ((c • PeriodicLattice.unitStep L m d μ : PeriodicLattice.Site L m d) :
      PeriodicLattice.FourTorus L m) ρ =
      ((c' • PeriodicLattice.unitStep L m d ν : PeriodicLattice.Site L m d) :
      PeriodicLattice.FourTorus L m) ρ := fun ρ => by rw [h]
  by_cases hμν : μ = ν
  · subst hμν
    have h1 := hc μ
    rw [coe_zsmul_unitStep_apply, coe_zsmul_unitStep_apply, if_pos rfl, if_pos rfl] at h1
    have h2 : ((((c - c' : ℤ) : ℝ) * PeriodicLattice.meshSize L d : ℝ) :
        AddCircle (PeriodicLattice.torusSide L m)) = 0 := by
      rw [Int.cast_sub, sub_mul, AddCircle.coe_sub, h1, sub_self]
    have h3 := eq_zero_of_mul_meshSize_coe_eq_zero hL (c - c') (by
      rw [Int.cast_sub]
      exact (abs_sub _ _).trans_lt hN) h2
    exact ⟨by omega, Or.inr rfl⟩
  · have h1 := hc μ
    have h2 := hc ν
    rw [coe_zsmul_unitStep_apply, coe_zsmul_unitStep_apply, if_pos rfl, if_neg hμν] at h1
    rw [coe_zsmul_unitStep_apply, coe_zsmul_unitStep_apply, if_neg (Ne.symm hμν),
      if_pos rfl] at h2
    have hc0 := eq_zero_of_mul_meshSize_coe_eq_zero hL c
      (by linarith [abs_nonneg (c' : ℝ)]) h1
    have hc1 := eq_zero_of_mul_meshSize_coe_eq_zero hL c'
      (by linarith [abs_nonneg (c : ℝ)]) h2.symm
    exact ⟨hc0.trans hc1.symm, Or.inl hc0⟩
theorem axis_unique_of_eq_unitStep (hL : 0 < L) (hN : 1 < (L : ℝ) ^ ((m : ℤ) + d))
    {x : PeriodicLattice.Site L m d} {μ ν : Fin 4}
    (h₁ : x = PeriodicLattice.unitStep L m d μ ∨ x = -PeriodicLattice.unitStep L m d μ)
    (h₂ : x = PeriodicLattice.unitStep L m d ν ∨ x = -PeriodicLattice.unitStep L m d ν) :
    μ = ν := by
  have key : ∀ ε ε' : ℤ, |(ε : ℝ)| = 1 → |(ε' : ℝ)| = 1 →
      ε • PeriodicLattice.unitStep L m d μ = ε' • PeriodicLattice.unitStep L m d ν → μ = ν := by
    intro ε ε' hε hε' h
    obtain ⟨-, h0 | h1⟩ := zsmul_unitStep_inj hL (by rw [hε, hε']; linarith) h
    · rw [h0] at hε
      simp at hε
    · exact h1
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact key 1 1 (by simp) (by simp) (by simpa using h₁.symm.trans h₂)
  · exact key 1 (-1) (by simp) (by simp) (by simpa using h₁.symm.trans h₂)
  · exact key (-1) 1 (by simp) (by simp) (by simpa using h₁.symm.trans h₂)
  · exact key (-1) (-1) (by simp) (by simp) (by simpa using h₁.symm.trans h₂)
theorem axialPath_eq_flowAlong (hL : 0 < L) {x x' : PeriodicLattice.Site L m d} {μ : Fin 4}
    {c : ℤ} (h : PeriodicLattice.IsAxialDisplacement x x' μ c) :
    PeriodicLattice.axialPath x x' = PeriodicLattice.flowAlong x μ c := by apply _root_.YangMills.Construction.PeriodicLattice.AxialReversal.axialPath_eq_flowAlong <;> assumption
end PeriodicSteps
section TorusCase
variable {L k j : ℕ}
theorem scaling_torusProj (hL : 0 < L) {n : ℕ} (x : Fin 4 → ℝ) :
    scaling hL n k j (TorusMetric.torusProj (PeriodicLattice.torusSide L n) x) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L (scaledExponent n k j))
        ((L : ℝ) ^ (k - j) • x) :=
  scaling_mk hL x
theorem torusProj_surjective (S : ℝ) : Function.Surjective (TorusMetric.torusProj S) := by apply _root_.YangMills.Construction.TestFunctions.torusProj_surjective <;> assumption
theorem torusEuclidNorm_scaling (hL : 0 < L) {n : ℕ} (z : PeriodicLattice.FourTorus L n) :
    TorusMetric.torusEuclidNorm (scaling hL n k j z) =
      (L : ℝ) ^ (k - j) * TorusMetric.torusEuclidNorm z := by
  have hc : 0 < (L : ℝ) ^ (k - j) := scaleFactor_pos hL _
  have hset : TorusMetric.euclidNormVec ''
        (TorusMetric.torusProj (PeriodicLattice.torusSide L (scaledExponent n k j)) ⁻¹'
          {scaling hL n k j z}) =
      ((L : ℝ) ^ (k - j)) •
        (TorusMetric.euclidNormVec ''
          (TorusMetric.torusProj (PeriodicLattice.torusSide L n) ⁻¹' {z})) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : TorusMetric.torusProj (PeriodicLattice.torusSide L (scaledExponent n k j)) v =
          scaling hL n k j z := hv
      refine Set.mem_smul_set.2 ⟨TorusMetric.euclidNormVec (((L : ℝ) ^ (k - j))⁻¹ • v),
        ⟨((L : ℝ) ^ (k - j))⁻¹ • v, ?_, rfl⟩, ?_⟩
      · apply (scaling hL n k j).injective
        rw [scaling_torusProj, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
        exact hv'
      · rw [euclidNormVec_smul (inv_nonneg.2 hc.le), smul_eq_mul, mul_inv_cancel_left₀ hc.ne']
    · intro hr
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hr
      have hv' : TorusMetric.torusProj (PeriodicLattice.torusSide L n) v = z := hv
      refine ⟨((L : ℝ) ^ (k - j)) • v, ?_, euclidNormVec_smul hc.le v⟩
      show TorusMetric.torusProj _ _ = _
      rw [← scaling_torusProj, hv']
  rw [TorusMetric.torusEuclidNorm, TorusMetric.torusEuclidNorm, hset,
    Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
theorem mem_face_iff {m : ℕ} {d : ℤ} {p : PeriodicLattice.Plaquette L m d}
    {q : PeriodicLattice.FourTorus L m} :
    q ∈ p.face ↔ ∃ s ∈ Icc (0 : ℝ) (PeriodicLattice.meshSize L d),
      ∃ t ∈ Icc (0 : ℝ) (PeriodicLattice.meshSize L d),
        q = p.origin + PeriodicLattice.pointOnAxis L m p.firstAxis s +
          PeriodicLattice.pointOnAxis L m p.secondAxis t :=
  Iff.rfl
variable {n : ℕ}
theorem exists_scaleVertex_eq (hL : 0 < L) (hj : j ≤ k) (i : ℕ)
    (y : Vertex L (scaledExponent n k j) j i) :
    ∃ x : Vertex L n k i, scaleVertex hL hj i x = y :=
  (scaleVertex hL hj i).surjective y
theorem scalePath_forwardFlow (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (x : Vertex L n k i)
    (μ : Fin 4) (c : ℕ) :
    scalePath hL hj i (PeriodicLattice.forwardAxisPath x μ c) =
      PeriodicLattice.forwardAxisPath (scaleVertex hL hj i x) μ c := by
  induction c generalizing x with
  | zero => rfl
  | succ c ih =>
    have h := ih (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ)
    rw [AddEquiv.map_add, scaleVertex_unitStep] at h
    simp only [PeriodicLattice.forwardAxisPath, ← h]
    refine congrArg (· :: _) (PeriodicLattice.Bond.ext rfl ?_)
    show scaleVertex hL hj i (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ) =
      scaleVertex hL hj i x + PeriodicLattice.unitStep _ _ _ μ
    rw [AddEquiv.map_add, scaleVertex_unitStep]
theorem scalePath_backwardFlow (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (x : Vertex L n k i)
    (μ : Fin 4) (c : ℕ) :
    scalePath hL hj i (PeriodicLattice.backwardAxisPath x μ c) =
      PeriodicLattice.backwardAxisPath (scaleVertex hL hj i x) μ c := by
  induction c generalizing x with
  | zero => rfl
  | succ c ih =>
    have h := ih (x - PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ)
    rw [AddEquiv.map_sub, scaleVertex_unitStep] at h
    simp only [PeriodicLattice.backwardAxisPath, ← h]
    refine congrArg (· :: _) (PeriodicLattice.Bond.ext rfl ?_)
    show scaleVertex hL hj i (x - PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ) =
      scaleVertex hL hj i x - PeriodicLattice.unitStep _ _ _ μ
    rw [AddEquiv.map_sub, scaleVertex_unitStep]
theorem scalePath_flowAlong (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (x : Vertex L n k i)
    (μ : Fin 4) (c : ℤ) :
    scalePath hL hj i (PeriodicLattice.flowAlong x μ c) =
      PeriodicLattice.flowAlong (scaleVertex hL hj i x) μ c := by
  unfold PeriodicLattice.flowAlong
  split_ifs
  · exact scalePath_forwardFlow hL hj i x μ _
  · exact scalePath_backwardFlow hL hj i x μ _
theorem scaleEdge_isPositivelyOriented_iff (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (b : Edge L n k i) :
    (scaleEdge hL hj i b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  constructor
  · rintro ⟨μ, h⟩
    refine ⟨μ, (scaleVertex hL hj i).injective ?_⟩
    rw [AddEquiv.map_sub, scaleVertex_unitStep]
    exact h
  · rintro ⟨μ, h⟩
    refine ⟨μ, ?_⟩
    show scaleVertex hL hj i b.target - scaleVertex hL hj i b.source = _
    rw [← AddEquiv.map_sub, h, scaleVertex_unitStep]
theorem image_face_scaling (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (p : Face L n k i) :
    scaling hL n k j '' p.face = (scaleFace hL hj i p).face := by
  have hc : 0 < (L : ℝ) ^ (k - j) := scaleFactor_pos hL _
  have hsp := pow_mul_meshSize_levelDepth hL hj i
  have hle : ∀ s : ℝ, 0 ≤ s → 0 ≤ (L : ℝ) ^ (k - j) * s := fun s hs => mul_nonneg hc.le hs
  ext q
  constructor
  · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    refine mem_face_iff.2 ⟨(L : ℝ) ^ (k - j) * s, ⟨hle s hs.1, ?_⟩, (L : ℝ) ^ (k - j) * t,
      ⟨hle t ht.1, ?_⟩, ?_⟩
    · rw [← hsp]
      exact mul_le_mul_of_nonneg_left hs.2 hc.le
    · rw [← hsp]
      exact mul_le_mul_of_nonneg_left ht.2 hc.le
    · rw [AddEquiv.map_add, AddEquiv.map_add, scaling_pointOnAxis, scaling_pointOnAxis]
      rfl
  · intro hq
    obtain ⟨s, hs, t, ht, rfl⟩ := mem_face_iff.1 hq
    have hinv : ∀ s : ℝ,
        s ∈ Icc (0 : ℝ) (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth j i)) →
        ((L : ℝ) ^ (k - j))⁻¹ * s ∈
          Icc (0 : ℝ) (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k i)) := by
      intro s hs
      refine ⟨mul_nonneg (inv_nonneg.2 hc.le) hs.1, ?_⟩
      have := hs.2
      rw [← hsp] at this
      rw [inv_mul_le_iff₀ hc]
      exact this
    refine ⟨_, mem_face_iff.2 ⟨_, hinv s hs, _, hinv t ht, rfl⟩, ?_⟩
    rw [AddEquiv.map_add, AddEquiv.map_add, scaling_pointOnAxis, scaling_pointOnAxis,
      mul_inv_cancel_left₀ hc.ne',
      mul_inv_cancel_left₀ hc.ne']
    rfl
theorem scalingAtLevel_torus (hL : 1 < L) (hj : j ≤ k) (hn : 0 < n) {i : ℕ} (hi : i ≤ j) :
    ScalingAtLevel (Nat.zero_lt_of_lt hL) hj n i := by
  have hL0 : 0 < L := Nat.zero_lt_of_lt hL
  have hLr : (1 : ℝ) < L := by exact_mod_cast hL
  have hc : 0 < (L : ℝ) ^ (k - j) := scaleFactor_pos hL0 _
  have hsp : (L : ℝ) ^ ((i : ℤ) - (j : ℤ)) = (L : ℝ) ^ (k - j) * meshAt L k i :=
    (pow_mul_meshAt hL0 hj i).symm
  have hexp : ((scaledExponent n k j : ℕ) : ℤ) + PeriodicLattice.levelDepth j i =
      (n : ℤ) + PeriodicLattice.levelDepth k i := by
    simp only [scaledExponent, PeriodicLattice.levelDepth]
    omega
  have hcond : ∀ c : ℤ, ((|c| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L n / 2 →
      ((|c| : ℤ) : ℝ) < (L : ℝ) ^ ((n : ℤ) + PeriodicLattice.levelDepth k i) := by
    intro c h
    have hls := meshAt_pos hL0 k i
    have hz : (L : ℝ) ^ ((n : ℤ) + PeriodicLattice.levelDepth k i) * meshAt L k i =
        PeriodicLattice.torusSide L n / 2 := by
      have hL' : (L : ℝ) ≠ 0 := by linarith
      rw [meshAt, ← zpow_add₀ hL', PeriodicLattice.torusSide,
        show (n : ℤ) + PeriodicLattice.levelDepth k i + ((i : ℤ) - (k : ℤ)) = (n : ℤ) by
          simp only [PeriodicLattice.levelDepth]
          ring,
        zpow_natCast]
      ring
    rw [← hz] at h
    exact lt_of_mul_lt_mul_right h hls.le
  exact {
    image_sublattice := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (scaleVertex hL0 hj i ⟨x, hx⟩).2
      · intro hy
        obtain ⟨x, hx⟩ := exists_scaleVertex_eq hL0 hj i ⟨y, hy⟩
        exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
    injOn_sublattice := (scaling hL0 n k j).injective.injOn
    sub_eq_step_iff := fun x x' μ c => by
      rw [← AddEquiv.map_sub, ← scaleVertex_unitStep hL0 hj i μ, ← map_zsmul]
      exact (scaleVertex hL0 hj i).injective.eq_iff.symm
    edge_source := fun _ => rfl
    edge_target := fun _ => rfl
    edge_bijective := (scaleEdge hL0 hj i).bijective
    edge_axis := fun b => by
      have hN : (1 : ℝ) <
          (L : ℝ) ^ (((scaledExponent n k j : ℕ) : ℤ) + PeriodicLattice.levelDepth j i) := by
        apply one_lt_zpow₀ hLr
        simp only [scaledExponent, PeriodicLattice.levelDepth]
        omega
      have h₁ := (scaleEdge hL0 hj i b).isNeighbour.choose_spec
      have h₂ := b.isNeighbour.choose_spec
      refine axis_unique_of_eq_unitStep hL0 hN h₁ ?_
      show scaleVertex hL0 hj i b.target - scaleVertex hL0 hj i b.source = _ ∨
        scaleVertex hL0 hj i b.target - scaleVertex hL0 hj i b.source = _
      rw [← AddEquiv.map_sub]
      rcases h₂ with h₂ | h₂
      · exact Or.inl (by rw [h₂, scaleVertex_unitStep]; rfl)
      · exact Or.inr (by rw [h₂, AddEquiv.map_neg, scaleVertex_unitStep]; rfl)
    image_positive := by
      ext b'
      obtain ⟨b, rfl⟩ := (scaleEdge hL0 hj i).surjective b'
      simp only [(scaleEdge hL0 hj i).injective.mem_set_image, mem_ofPred_eq]
      exact (scaleEdge_isPositivelyOriented_iff hL0 hj i b).symm
    edge_opposite := fun b => PeriodicLattice.Bond.ext rfl rfl
    image_paths := transportList_image_chains (scaleEdge hL0 hj i) _ _ fun a b =>
      (scaleVertex hL0 hj i).injective.eq_iff
    injOn_paths := (transportList_injective (scaleEdge hL0 hj i)).injOn
    axial_condition := fun c => by
      rw [hsp, show ((|c| : ℤ) : ℝ) * ((L : ℝ) ^ (k - j) * meshAt L k i) =
          (L : ℝ) ^ (k - j) * (((|c| : ℤ) : ℝ) * meshAt L k i) by ring,
        show (L : ℝ) ^ (k - j) * PeriodicLattice.torusSide L n / 2 =
          (L : ℝ) ^ (k - j) * (PeriodicLattice.torusSide L n / 2) by ring]
      exact ⟨fun h => mul_lt_mul_of_pos_left h hc, fun h => lt_of_mul_lt_mul_left h hc.le⟩
    axialPath := fun x x' μ c hx hcnd => by
      have hb := hcond c hcnd
      have h₁ : PeriodicLattice.IsAxialDisplacement x x' μ c :=
        ⟨by rw [hx]; abel, hb⟩
      have h₂ : PeriodicLattice.IsAxialDisplacement (scaleVertex hL0 hj i x)
          (scaleVertex hL0 hj i x') μ c :=
        ⟨by rw [← AddEquiv.map_sub, h₁.1, map_zsmul, scaleVertex_unitStep], by rw [hexp]; exact hb⟩
      rw [axialPath_eq_flowAlong hL0 h₁, axialPath_eq_flowAlong hL0 h₂, scalePath_flowAlong]
    face_origin := fun _ => ⟨rfl, rfl, rfl⟩
    corners := fun p => by
      show [scaleVertex hL0 hj i p.origin,
          scaleVertex hL0 hj i (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis),
          scaleVertex hL0 hj i (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis +
            PeriodicLattice.unitStep L n _ p.secondAxis),
          scaleVertex hL0 hj i (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis)] =
        [scaleVertex hL0 hj i p.origin,
          scaleVertex hL0 hj i p.origin + PeriodicLattice.unitStep _ _ _ p.firstAxis,
          scaleVertex hL0 hj i p.origin + PeriodicLattice.unitStep _ _ _ p.firstAxis +
            PeriodicLattice.unitStep _ _ _ p.secondAxis,
          scaleVertex hL0 hj i p.origin + PeriodicLattice.unitStep _ _ _ p.secondAxis]
      simp only [AddEquiv.map_add, scaleVertex_unitStep]
    image_face := fun p => image_face_scaling hL0 hj i p
    face_determined := fun p q h => by
      rw [← image_face_scaling hL0 hj i p, ← image_face_scaling hL0 hj i q, h]
    face_bijective := (scaleFace hL0 hj i).bijective }
theorem scalingTransportsFunctions_torus (hL : 0 < L) (hj : j ≤ k) :
    ScalingTransportsFunctions hL hj n where
  points := fun S _ => transportsFunctionsOn_of_equiv _ S
  pointPairs := fun S _ => transportsFunctionsOn_of_equiv _ S
  vertices := fun _ _ S => transportsFunctionsOn_of_equiv _ S
  vertexPairs := fun _ _ _ _ S => transportsFunctionsOn_of_equiv _ S
  edges := fun _ _ S => transportsFunctionsOn_of_equiv _ S
  faces := fun _ _ S => transportsFunctionsOn_of_equiv _ S
  edgesAllLevels := fun S => transportsFunctionsOn_of_equiv _ S
  facesAllLevels := fun S => transportsFunctionsOn_of_equiv _ S
theorem scaledTowerMesh_holds (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : ScaledTowerMesh L k j i where
  meshAt_eq := rfl
  eq_mul := (pow_mul_meshAt hL hj i).symm
theorem spaceScalingProperties_holds (hL : 0 < L) : SpaceScalingProperties L k j where
  bijective := by
    have hc : (L : ℝ) ^ (k - j) ≠ 0 := (scaleFactor_pos hL _).ne'
    refine ⟨fun x y h => ?_, fun y => ⟨((L : ℝ) ^ (k - j))⁻¹ • y, ?_⟩⟩
    · have h' := congrArg (fun v : Fin 4 → ℝ => ((L : ℝ) ^ (k - j))⁻¹ • v) h
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h'
    · simp only [smul_smul, mul_inv_cancel₀ hc, one_smul]
  map_add := fun x y => smul_add _ x y
theorem mul_torusSide_mem_sideSet (hn : 0 < n) :
    (L : ℝ) ^ (k - j) * PeriodicLattice.torusSide L n ∈ sideSet L :=
  ⟨scaledExponent n k j, by simp only [scaledExponent]; omega,
    (torusSide_scaledExponent L n k j).symm⟩
theorem sublattice_scaledExponent_eq (i : ℕ) :
    (PeriodicLattice.sublattice L (scaledExponent n k j) (PeriodicLattice.levelDepth j i) :
        Set (PeriodicLattice.FourTorus L (scaledExponent n k j))) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L (scaledExponent n k j)) ''
        {v | ∃ a : Fin 4 → ℤ, ∀ μ, v μ = (a μ : ℝ) * (L : ℝ) ^ ((i : ℤ) - (j : ℤ))} := by
  have hsp : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth j i) =
      (L : ℝ) ^ ((i : ℤ) - (j : ℤ)) := meshSize_levelDepth L j i
  ext x
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun μ => (a μ : ℝ) * (L : ℝ) ^ ((i : ℤ) - (j : ℤ)), ⟨a, fun _ => rfl⟩, ?_⟩
    funext μ
    rw [ha μ, hsp]
    rfl
  · rintro ⟨v, ⟨a, ha⟩, rfl⟩
    refine ⟨a, fun μ => ?_⟩
    rw [hsp, ← ha μ]
    rfl
theorem isCongruentMod_smul_iff (hL : 0 < L) (x y : Fin 4 → ℝ) :
    IsCongruentMod (PeriodicLattice.torusSide L n) x y ↔
      IsCongruentMod ((L : ℝ) ^ (k - j) * PeriodicLattice.torusSide L n)
        ((L : ℝ) ^ (k - j) • x) ((L : ℝ) ^ (k - j) • y) := by
  have hc : 0 < (L : ℝ) ^ (k - j) := scaleFactor_pos hL _
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun μ => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, ha μ]
    ring
  · rintro ⟨a, ha⟩
    refine ⟨a, fun μ => ?_⟩
    have h := ha μ
    simp only [Pi.smul_apply, smul_eq_mul] at h
    apply mul_left_cancel₀ hc.ne'
    rw [mul_sub, h]
    ring
theorem forall_torusProj_eq_iff_eq_scaling (hL : 0 < L)
    (φ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L (scaledExponent n k j)) :
    (∀ x : Fin 4 → ℝ, φ (TorusMetric.torusProj (PeriodicLattice.torusSide L n) x) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L (scaledExponent n k j))
        ((L : ℝ) ^ (k - j) • x)) ↔
      φ = scaling hL n k j := by
  constructor
  · intro h
    funext z
    obtain ⟨x, rfl⟩ := torusProj_surjective _ z
    rw [h x, scaling_torusProj]
  · rintro rfl x
    exact scaling_torusProj hL x
theorem scaling_add_torusProj (hL : 0 < L) (hj : j ≤ k) (i : ℕ)
    (x : PeriodicLattice.FourTorus L n) (w : Fin 4 → ℝ) :
    scaling hL n k j
        (x + TorusMetric.torusProj (PeriodicLattice.torusSide L n) (meshAt L k i • w)) =
      scaling hL n k j x +
        TorusMetric.torusProj (PeriodicLattice.torusSide L (scaledExponent n k j))
          ((L : ℝ) ^ ((i : ℤ) - (j : ℤ)) • w) := by
  have hsp : (L : ℝ) ^ (k - j) * meshAt L k i = (L : ℝ) ^ ((i : ℤ) - (j : ℤ)) :=
    pow_mul_meshAt hL hj i
  rw [AddEquiv.map_add, scaling_torusProj, smul_smul, hsp]
theorem torusEuclidNorm_scaling_sub (hL : 0 < L) (a b : PeriodicLattice.FourTorus L n) :
    TorusMetric.torusEuclidNorm (scaling hL n k j a - scaling hL n k j b) =
      (L : ℝ) ^ (k - j) * TorusMetric.torusEuclidNorm (a - b) := by
  rw [← AddEquiv.map_sub, torusEuclidNorm_scaling]
theorem conjMap_scaling_apply (hL : 0 < L)
    (s : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (a : PeriodicLattice.FourTorus L n) :
    conjMap (scaling hL n k j).toEquiv s (scaling hL n k j a) = scaling hL n k j (s a) := by
  simp [conjMap]
theorem isDistancePreserving_conjMap_scaling_iff (hL : 0 < L)
    (s : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) :
    IsDistancePreserving (conjMap (scaling hL n k j).toEquiv s) ↔ IsDistancePreserving s := by
  have hc : 0 < (L : ℝ) ^ (k - j) := scaleFactor_pos hL _
  constructor
  · intro h a b
    have h' := h (scaling hL n k j a) (scaling hL n k j b)
    rw [conjMap_scaling_apply, conjMap_scaling_apply, torusEuclidNorm_scaling_sub,
      torusEuclidNorm_scaling_sub] at h'
    exact mul_left_cancel₀ hc.ne' h'
  · intro h a' b'
    obtain ⟨a, rfl⟩ := (scaling hL n k j).surjective a'
    obtain ⟨b, rfl⟩ := (scaling hL n k j).surjective b'
    rw [conjMap_scaling_apply, conjMap_scaling_apply, torusEuclidNorm_scaling_sub,
      torusEuclidNorm_scaling_sub, h a b]
theorem mapsSublatticeOnto_conjMap_scaling_iff (hL : 1 < L) (hj : j ≤ k) (hn : 0 < n) {i : ℕ}
    (hi : i ≤ j) (s : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) :
    MapsSublatticeOnto j i (conjMap (scaling (Nat.zero_lt_of_lt hL) n k j).toEquiv s) ↔
      MapsSublatticeOnto k i s := by
  have himg : (scaling (Nat.zero_lt_of_lt hL) n k j).toEquiv ''
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
        Set (PeriodicLattice.FourTorus L n)) =
      (PeriodicLattice.sublattice L (scaledExponent n k j) (PeriodicLattice.levelDepth j i) :
        Set (PeriodicLattice.FourTorus L (scaledExponent n k j))) := by
    rw [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv]
    exact (scalingAtLevel_torus hL hj hn hi).image_sublattice
  unfold MapsSublatticeOnto
  rw [← himg]
  exact conjMap_image_image_iff _ s _
theorem scalingOnTorus_holds (hL : 1 < L) (hj : j ≤ k) (hn : 0 < n) :
    ScalingOnTorus (Nat.zero_lt_of_lt hL) hj n where
  side_mem := mul_torusSide_mem_sideSet hn
  side_eq := (torusSide_scaledExponent L n k j).symm
  sublattice_eq := fun i _ => sublattice_scaledExponent_eq i
  mesh := fun i _ =>
    ⟨meshSize_levelDepth L j i, scaledTowerMesh_holds (Nat.zero_lt_of_lt hL) hj i⟩
  spaceScaling := spaceScalingProperties_holds (Nat.zero_lt_of_lt hL)
  congruent_iff := isCongruentMod_smul_iff (Nat.zero_lt_of_lt hL)
  eq_scaling_iff := forall_torusProj_eq_iff_eq_scaling (Nat.zero_lt_of_lt hL)
  bijective := (scaling (Nat.zero_lt_of_lt hL) n k j).bijective
  map_add := fun a b => AddEquiv.map_add _ a b
  map_add_proj := fun i _ => scaling_add_torusProj (Nat.zero_lt_of_lt hL) hj i
  dist_eq := torusEuclidNorm_scaling_sub (Nat.zero_lt_of_lt hL)
  atLevel := fun _ hi => scalingAtLevel_torus hL hj hn hi
  distancePreserving_iff := isDistancePreserving_conjMap_scaling_iff (Nat.zero_lt_of_lt hL)
  mapsSublatticeOnto_iff := fun _ hi => mapsSublatticeOnto_conjMap_scaling_iff hL hj hn hi
  existsUnique_map := fun t => existsUnique_eq_conjMap _ t
  transports := scalingTransportsFunctions_torus (Nat.zero_lt_of_lt hL) hj
end TorusCase
end YangMills.Construction.Tower.ScalingProperties
namespace YangMills.Construction.Tower.FullSpace.ScalingProperties
open InfiniteLattice (AmbientSpace)
open YangMills.Construction.Tower.ScalingProperties
section SingleLattice
variable {a : ℝ}
theorem axisPath_eq_signedSteps (ha : a ≠ 0) {x x' : InfiniteLattice.LatticePoint a} {μ : Fin 4}
    {c : ℤ} (h : IsAxisDisplacement x x' μ c) : axisPath x x' = signedSteps x μ c := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfStepSets.axisPath_eq_signedSteps <;> assumption
theorem mem_closedFace_iff {p : InfiniteLattice.ElementaryPlaquette a} {q : AmbientSpace} :
    q ∈ closedFace p ↔ ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      q = (p.corner : AmbientSpace) + Pi.single p.lowAxis (s * a) +
        Pi.single p.highAxis (t * a) :=
  Iff.rfl
end SingleLattice
variable {L k j : ℕ}
theorem scalePath_signedSteps (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (x : Vertex L k i)
    (μ : Fin 4) (c : ℤ) :
    scalePath hL hj i (signedSteps x μ c) =
      signedSteps (scaleVertex hL hj i x) μ c := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfStepSets.map_signedSteps <;> assumption
theorem scaleEdge_orientation_iff (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (b : Edge L k i) :
    (scaleEdge hL hj i b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  constructor
  · rintro ⟨μ, h⟩
    refine ⟨μ, (scaleVertex hL hj i).injective ?_⟩
    rw [AddEquiv.map_sub, scaleVertex_axisStep]
    exact h
  · rintro ⟨μ, h⟩
    refine ⟨μ, ?_⟩
    show scaleVertex hL hj i b.terminal - scaleVertex hL hj i b.initial = _
    rw [← AddEquiv.map_sub, h, scaleVertex_axisStep]
theorem scaleEdge_linkHasAxis_iff (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (b : Edge L k i)
    (μ : Fin 4) :
    LinkHasAxis (scaleEdge hL hj i b) μ ↔ LinkHasAxis b μ := by
  have hs : (scaleEdge hL hj i b).terminal - (scaleEdge hL hj i b).initial =
      scaleVertex hL hj i (b.terminal - b.initial) := (AddEquiv.map_sub _ _ _).symm
  have hstep := scaleVertex_axisStep hL hj i μ
  unfold LinkHasAxis
  rw [hs, ← hstep, ← AddEquiv.map_neg]
  simp only [(scaleVertex hL hj i).injective.eq_iff]
theorem smul_add_single_add_single (c : ℝ) (x : AmbientSpace) (μ ν : Fin 4) (s t : ℝ) :
    c • (x + Pi.single μ s + Pi.single ν t) =
      c • x + Pi.single μ (c * s) + Pi.single ν (c * t) := by
  rw [smul_add, smul_add, ← Pi.single_smul, ← Pi.single_smul]
  rfl
theorem image_closedFace_scaling (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (p : Face L k i) :
    scaling hL k j '' closedFace p = closedFace (scaleFace hL hj i p) := by
  have hsp : (L : ℝ) ^ (k - j) * meshAt L k i = meshAt L j i :=
    pow_mul_meshAt hL hj i
  have hpt : ∀ s t : ℝ, scaling hL k j ((p.corner : AmbientSpace) +
      Pi.single p.lowAxis (s * meshAt L k i) + Pi.single p.highAxis (t * meshAt L k i)) =
      ((scaleFace hL hj i p).corner : AmbientSpace) + Pi.single p.lowAxis (s * meshAt L j i) +
        Pi.single p.highAxis (t * meshAt L j i) := by
    intro s t
    have h₁ : ∀ r : ℝ, (L : ℝ) ^ (k - j) * (r * meshAt L k i) = r * meshAt L j i :=
      fun r => by rw [← hsp]; ring
    rw [scaling_apply, smul_add_single_add_single, h₁, h₁]
    rfl
  ext q
  constructor
  · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    exact mem_closedFace_iff.2 ⟨s, hs, t, ht, hpt s t⟩
  · intro hq
    obtain ⟨s, hs, t, ht, rfl⟩ := mem_closedFace_iff.1 hq
    exact ⟨_, mem_closedFace_iff.2 ⟨s, hs, t, ht, rfl⟩, hpt s t⟩
theorem scalingAtLevel_space (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : ScalingAtLevel hL hj i where
  image_sublattice := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (scaleVertex hL hj i ⟨x, hx⟩).2
    · intro hy
      obtain ⟨x, hx⟩ := (scaleVertex hL hj i).surjective ⟨y, hy⟩
      exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
  injOn_sublattice := (scaling hL k j).injective.injOn
  sub_eq_step_iff := fun x x' μ c => by
    rw [← AddEquiv.map_sub, ← scaleVertex_axisStep hL hj i μ, ← map_zsmul]
    exact (scaleVertex hL hj i).injective.eq_iff.symm
  edge_initial := fun _ => rfl
  edge_terminal := fun _ => rfl
  edge_bijective := (scaleEdge hL hj i).bijective
  edge_axis := scaleEdge_linkHasAxis_iff hL hj i
  image_positive := by
    ext b'
    obtain ⟨b, rfl⟩ := (scaleEdge hL hj i).surjective b'
    simp only [(scaleEdge hL hj i).injective.mem_set_image, mem_ofPred_eq]
    exact (scaleEdge_orientation_iff hL hj i b).symm
  edge_opposite := fun b => InfiniteLattice.Link.ext rfl rfl
  image_paths := transportList_image_chains (scaleEdge hL hj i) _ _ fun a b =>
    (scaleVertex hL hj i).injective.eq_iff
  injOn_paths := (transportList_injective (scaleEdge hL hj i)).injOn
  axisPath := fun x x' μ c hx => by
    have h₁ : IsAxisDisplacement x x' μ c := by
      show x' - x = _
      rw [hx]
      abel
    have h₂ : IsAxisDisplacement (scaleVertex hL hj i x) (scaleVertex hL hj i x') μ c := by
      show scaleVertex hL hj i x' - scaleVertex hL hj i x = _
      rw [← AddEquiv.map_sub, show x' - x = _ from h₁, map_zsmul, scaleVertex_axisStep]
    rw [axisPath_eq_signedSteps (meshAt_pos hL k i).ne' h₁,
      axisPath_eq_signedSteps (meshAt_pos hL j i).ne' h₂, scalePath_signedSteps]
  face_corner := fun _ => ⟨rfl, rfl, rfl⟩
  corners := fun p => by
    show [scaleVertex hL hj i p.corner,
        scaleVertex hL hj i (p.corner + InfiniteLattice.axisStep _ p.lowAxis),
        scaleVertex hL hj i (p.corner + InfiniteLattice.axisStep _ p.lowAxis +
          InfiniteLattice.axisStep _ p.highAxis),
        scaleVertex hL hj i (p.corner + InfiniteLattice.axisStep _ p.highAxis)] =
      [scaleVertex hL hj i p.corner,
        scaleVertex hL hj i p.corner + InfiniteLattice.axisStep _ p.lowAxis,
        scaleVertex hL hj i p.corner + InfiniteLattice.axisStep _ p.lowAxis +
          InfiniteLattice.axisStep _ p.highAxis,
        scaleVertex hL hj i p.corner + InfiniteLattice.axisStep _ p.highAxis]
    simp only [AddEquiv.map_add, scaleVertex_axisStep]
  image_closedFace := fun p => image_closedFace_scaling hL hj i p
  closedFace_determined := fun p q h => by
    rw [← image_closedFace_scaling hL hj i p, ← image_closedFace_scaling hL hj i q, h]
  face_bijective := (scaleFace hL hj i).bijective
theorem scalingTransportsFunctions_space (hL : 0 < L) (hj : j ≤ k) :
    ScalingTransportsFunctions hL hj where
  points := fun S _ => transportsFunctionsOn_of_equiv _ S
  pointPairs := fun S _ => transportsFunctionsOn_of_equiv _ S
  vertices := fun _ _ S => transportsFunctionsOn_of_equiv _ S
  vertexPairs := fun _ _ _ _ S => transportsFunctionsOn_of_equiv _ S
  edges := fun _ _ S => transportsFunctionsOn_of_equiv _ S
  faces := fun _ _ S => transportsFunctionsOn_of_equiv _ S
  edgesAllLevels := fun S => transportsFunctionsOn_of_equiv _ S
  facesAllLevels := fun S => transportsFunctionsOn_of_equiv _ S
theorem latticeSubgroup_meshAt_eq (i : ℕ) :
    (InfiniteLattice.latticeSubgroup (meshAt L j i) : Set AmbientSpace) =
      {v | ∃ a : Fin 4 → ℤ, ∀ μ, v μ = (a μ : ℝ) * (L : ℝ) ^ ((i : ℤ) - (j : ℤ))} :=
  rfl
theorem scaling_add_smul (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (x w : AmbientSpace) :
    scaling hL k j (x + meshAt L k i • w) =
      scaling hL k j x + (L : ℝ) ^ ((i : ℤ) - (j : ℤ)) • w := by
  have hsp : (L : ℝ) ^ (k - j) * meshAt L k i = (L : ℝ) ^ ((i : ℤ) - (j : ℤ)) :=
    pow_mul_meshAt hL hj i
  rw [AddEquiv.map_add, scaling_apply hL (meshAt L k i • w), smul_smul, hsp]
theorem euclidNormVec_scaling (hL : 0 < L) (z : AmbientSpace) :
    TorusMetric.euclidNormVec (scaling hL k j z) =
      (L : ℝ) ^ (k - j) * TorusMetric.euclidNormVec z := by
  rw [scaling_apply, euclidNormVec_smul (scaleFactor_pos hL _).le]
theorem euclidNormVec_scaling_sub (hL : 0 < L) (a b : AmbientSpace) :
    TorusMetric.euclidNormVec (scaling hL k j a - scaling hL k j b) =
      (L : ℝ) ^ (k - j) * TorusMetric.euclidNormVec (a - b) := by
  rw [← AddEquiv.map_sub, euclidNormVec_scaling]
theorem conjMap_scaling_apply_space (hL : 0 < L) (s : AmbientSpace → AmbientSpace)
    (a : AmbientSpace) :
    conjMap (scaling hL k j).toEquiv s (scaling hL k j a) = scaling hL k j (s a) := by
  simp [conjMap]
theorem isDistancePreserving_conjMap_scaling_iff_space (hL : 0 < L)
    (s : AmbientSpace → AmbientSpace) :
    IsDistancePreserving (conjMap (scaling hL k j).toEquiv s) ↔ IsDistancePreserving s := by
  have hc : 0 < (L : ℝ) ^ (k - j) := scaleFactor_pos hL _
  constructor
  · intro h a b
    have h' := h (scaling hL k j a) (scaling hL k j b)
    rw [conjMap_scaling_apply_space, conjMap_scaling_apply_space, euclidNormVec_scaling_sub,
      euclidNormVec_scaling_sub] at h'
    exact mul_left_cancel₀ hc.ne' h'
  · intro h a' b'
    obtain ⟨a, rfl⟩ := (scaling hL k j).surjective a'
    obtain ⟨b, rfl⟩ := (scaling hL k j).surjective b'
    rw [conjMap_scaling_apply_space, conjMap_scaling_apply_space, euclidNormVec_scaling_sub,
      euclidNormVec_scaling_sub, h a b]
theorem mapsSublatticeOnto_conjMap_scaling_iff_space (hL : 0 < L) (hj : j ≤ k) (i : ℕ)
    (s : AmbientSpace → AmbientSpace) :
    MapsSublatticeOnto (meshAt L j i) (conjMap (scaling hL k j).toEquiv s) ↔
      MapsSublatticeOnto (meshAt L k i) s := by
  have himg : (scaling hL k j).toEquiv ''
      (InfiniteLattice.latticeSubgroup (meshAt L k i) : Set AmbientSpace) =
      (InfiniteLattice.latticeSubgroup (meshAt L j i) : Set AmbientSpace) := by
    rw [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv]
    exact (scalingAtLevel_space hL hj i).image_sublattice
  unfold MapsSublatticeOnto
  rw [← himg]
  exact conjMap_image_image_iff _ s _
theorem scalingOnSpace_holds (hL : 0 < L) (hj : j ≤ k) : ScalingOnSpace hL hj where
  sublattice_eq := fun i _ => latticeSubgroup_meshAt_eq i
  mesh := fun i _ => scaledTowerMesh_holds hL hj i
  spaceScaling := spaceScalingProperties_holds hL
  scaling_apply := fun x => scaling_apply hL x
  bijective := (scaling hL k j).bijective
  map_add := fun a b => AddEquiv.map_add _ a b
  map_add_smul := fun i _ => scaling_add_smul hL hj i
  dist_eq := euclidNormVec_scaling_sub hL
  atLevel := fun i _ => scalingAtLevel_space hL hj i
  distancePreserving_iff := isDistancePreserving_conjMap_scaling_iff_space hL
  mapsSublatticeOnto_iff := fun i _ => mapsSublatticeOnto_conjMap_scaling_iff_space hL hj i
  existsUnique_map := fun t => existsUnique_eq_conjMap _ t
  transports := scalingTransportsFunctions_space hL hj
end YangMills.Construction.Tower.FullSpace.ScalingProperties
namespace YangMills.Construction.Tower
theorem scalingProperties : ScalingPropertiesStatement := by
  intro L k j hL hj
  have hL1 : 1 < L := Nat.lt_of_lt_of_le (by norm_num) hL.2
  exact ⟨fun n hn => ScalingProperties.scalingOnTorus_holds hL1 hj hn,
    FullSpace.ScalingProperties.scalingOnSpace_holds _ hj⟩
end YangMills.Construction.Tower
