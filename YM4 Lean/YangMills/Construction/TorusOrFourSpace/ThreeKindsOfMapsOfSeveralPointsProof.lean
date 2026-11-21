import YangMills.Construction.BoundsOnEverySide.SeparatedLimitsUnderABoundProof
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FifthPartProof
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegionsProof
import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.ThreeKindsOfMapsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
open YangMills.Construction.PeriodicLattice (SignedFrame)
open YangMills.Construction.PeriodicSpace.TupleFacts
namespace TupleMapFacts
section Generic
variable {X : Type*} (d : X → X → ℝ)
theorem isOpenWrt_preimage_of_isometry {Φ : X → X} (hΦ : ∀ a b, d (Φ a) (Φ b) = d a b) {U : Set X}
    (hU : MetricNotions.IsOpenWrt d U) : MetricNotions.IsOpenWrt d (Φ ⁻¹' U) := by
  intro x hx
  obtain ⟨r, hr, h⟩ := hU (Φ x) hx
  exact ⟨r, hr, fun y hy => h _ (by rwa [hΦ])⟩
theorem closureWrt_preimage_of_isometry {Φ Φ' : X → X} (hΦ : ∀ a b, d (Φ a) (Φ b) = d a b)
    (hr : ∀ a, Φ (Φ' a) = a) (S : Set X) :
    MetricNotions.closureWrt d (Φ ⁻¹' S) = Φ ⁻¹' MetricNotions.closureWrt d S := by
  ext y
  constructor
  · intro h r hr0
    obtain ⟨z, hz, hd⟩ := h r hr0
    exact ⟨Φ z, hz, by rwa [hΦ]⟩
  · intro h r hr0
    obtain ⟨z, hz, hd⟩ := h r hr0
    refine ⟨Φ' z, by simpa [Set.mem_preimage, hr] using hz, ?_⟩
    rw [← hΦ, hr]
    exact hd
theorem isCompactWrt_image_of_isometry {Φ Φ' : X → X} (hΦ : ∀ a b, d (Φ a) (Φ b) = d a b)
    (hl : ∀ a, Φ' (Φ a) = a) (hr : ∀ a, Φ (Φ' a) = a) {K : Set X}
    (hK : MetricNotions.IsCompactWrt d K) : MetricNotions.IsCompactWrt d (Φ '' K) := by
  intro 𝒰 hU hcov
  obtain ⟨𝒱, hV, hfin, hcovV⟩ := hK ((fun U => Φ ⁻¹' U) '' 𝒰)
    (by
      rintro _ ⟨U, hu, rfl⟩
      exact isOpenWrt_preimage_of_isometry d hΦ (hU U hu))
    (by
      intro x hx
      obtain ⟨U, hu, hxU⟩ := hcov ⟨x, hx, rfl⟩
      exact ⟨_, ⟨U, hu, rfl⟩, hxU⟩)
  refine ⟨(fun V => Φ' ⁻¹' V) '' 𝒱, ?_, hfin.image _, ?_⟩
  · rintro _ ⟨V, hv, rfl⟩
    obtain ⟨U, hu, rfl⟩ := hV hv
    have : Φ' ⁻¹' (Φ ⁻¹' U) = U := by
      ext a
      simp [hr]
    simpa [this] using hu
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨V, hv, hxV⟩ := hcovV hx
    exact ⟨_, ⟨V, hv, rfl⟩, by simpa [Set.mem_preimage, hl] using hxV⟩
end Generic
section Points
variable {D : Params} {E : Kind}
theorem actOnVector_sub (w : SignedFrame) (x x' : Fin 4 → ℝ) :
    w.actOnVector (x - x') = w.actOnVector x - w.actOnVector x' := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.actOnVector_sub <;> assumption
theorem actOnVector_mem_periodGroup (w : SignedFrame) {x : Fin 4 → ℝ} (hx : x ∈ E.periodGroup D) :
    w.actOnVector x ∈ E.periodGroup D := by
  cases E with
  | euclidean =>
    have h0 : x = 0 := by
      change x ∈ (⊥ : AddSubgroup (Fin 4 → ℝ)) at hx
      simpa using hx
    subst h0
    change w.actOnVector 0 ∈ (⊥ : AddSubgroup (Fin 4 → ℝ))
    have : w.actOnVector 0 = 0 := by
      funext μ
      simp [SignedFrame.actOnVector]
    simp [this]
  | torus =>
    obtain ⟨m, hm⟩ := hx
    refine ⟨fun μ => ((w.2 μ : ℤˣ) : ℤ) * m (w.1 μ), fun μ => ?_⟩
    simp only [SignedFrame.actOnVector, hm]
    push_cast
    ring
theorem frameInv_frameInv (w : SignedFrame) : frameInv (frameInv w) = w := by
  ext <;> simp [frameInv, Equiv.Perm.inv_def]
variable (hq : WellPosedness.QuotMapSurjectiveHomWithKernel D E)
include hq
theorem quotMap_zero_eq : E.quotMap D 0 = 0 := by
  have h := hq.1 0 0
  simpa using h
theorem quotMap_sub_eq (x x' : Fin 4 → ℝ) :
    E.quotMap D (x - x') = E.quotMap D x - E.quotMap D x' := by
  have h := hq.1 (x - x') x'
  rw [sub_add_cancel] at h
  rw [h]
  abel
theorem quotMap_pickLift (y : E.Pt D) : E.quotMap D (pickLift D E y) = y :=
  Classical.epsilon_spec (p := IsLift D E y) (hq.2.1 y)
theorem addPt_eq_add (y v : E.Pt D) : addPt D E y v = y + v := by
  unfold addPt
  rw [hq.1, quotMap_pickLift hq, quotMap_pickLift hq]
theorem subPt_eq_sub (y v : E.Pt D) : subPt D E y v = y - v := by
  unfold subPt
  rw [quotMap_sub_eq hq, quotMap_pickLift hq, quotMap_pickLift hq]
theorem quotMap_actOnVector_congr (w : SignedFrame) {x x' : Fin 4 → ℝ}
    (h : E.quotMap D x = E.quotMap D x') :
    E.quotMap D (w.actOnVector x) = E.quotMap D (w.actOnVector x') := by
  have h0 : x - x' ∈ E.periodGroup D := by
    rw [← hq.2.2, quotMap_sub_eq hq, h, sub_self]
  have h1 := (hq.2.2 _).2 (actOnVector_mem_periodGroup w h0)
  rw [actOnVector_sub, quotMap_sub_eq hq] at h1
  exact sub_eq_zero.1 h1
theorem frameAct_quotMap (w : SignedFrame) (x : Fin 4 → ℝ) :
    frameAct D E w (E.quotMap D x) = E.quotMap D (w.actOnVector x) :=
  quotMap_actOnVector_congr hq w (quotMap_pickLift hq _)
theorem liftIndependent_holds : LiftIndependent D E := by
  refine ⟨?_, ?_⟩
  · rintro w _ x rfl
    exact frameAct_quotMap hq w x
  · rintro _ _ x b rfl rfl
    rw [addPt_eq_add hq, subPt_eq_sub hq, hq.1, quotMap_sub_eq hq]
    exact ⟨rfl, rfl⟩
theorem frameAct_frameInv_frameAct (w : SignedFrame) (y : E.Pt D) :
    frameAct D E (frameInv w) (frameAct D E w y) = y := by
  obtain ⟨x, rfl⟩ := hq.2.1 y
  rw [frameAct_quotMap hq, frameAct_quotMap hq, frameInv_actOnVector_actOnVector]
theorem tupleMap_symm_symm {n : ℕ+} (ψ : TupleMap D E n) : ψ.symm.symm = ψ := by
  cases ψ with
  | permute ς => simp [TupleMap.symm]
  | frameDiag w => simp [TupleMap.symm, frameInv_frameInv]
  | translate v =>
    simp only [TupleMap.symm, subPt_eq_sub hq, quotMap_zero_eq hq]
    simp
theorem symm_actPts_actPts {n : ℕ+} (ψ : TupleMap D E n) (y : E.Tuple D n) :
    ψ.symm.actPts (ψ.actPts y) = y := by
  cases ψ with
  | permute ς =>
    funext i
    simp [TupleMap.symm, TupleMap.actPts, Equiv.Perm.inv_def]
  | frameDiag w =>
    funext i
    simp only [TupleMap.symm, TupleMap.actPts]
    exact frameAct_frameInv_frameAct hq w (y i)
  | translate v =>
    funext i
    simp only [TupleMap.symm, TupleMap.actPts, addPt_eq_add hq, subPt_eq_sub hq,
      quotMap_zero_eq hq]
    abel
theorem actPts_symm_actPts {n : ℕ+} (ψ : TupleMap D E n) (y : E.Tuple D n) :
    ψ.actPts (ψ.symm.actPts y) = y := by
  have h := symm_actPts_actPts hq ψ.symm y
  rwa [tupleMap_symm_symm hq] at h
end Points
section Signed
def pairIndex (n : ℕ+) : Fin (n : ℕ) × Fin 4 ≃ Fin (4 * (n : ℕ)) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm _ _))
theorem block_apply {n : ℕ+} (x : Coords n) (i : Fin (n : ℕ)) (μ : Fin 4) :
    x.block i μ = x (pairIndex n (i, μ)) := by
  unfold Coords.block
  congr 1
  ext
  simp [pairIndex, finProdFinEquiv, Nat.add_comm]
theorem coords_ext_block {n : ℕ+} {x x' : Coords n} (h : ∀ i, x.block i = x'.block i) : x = x' := by
  funext j
  obtain ⟨⟨i, μ⟩, rfl⟩ := (pairIndex n).surjective j
  rw [← block_apply x, ← block_apply x', h]
theorem block_add_eq {n : ℕ+} (x x' : Coords n) (i : Fin (n : ℕ)) :
    (x + x').block i = x.block i + x'.block i := rfl
theorem intUnit_cast_mul_self (u : ℤˣ) : (((u : ℤˣ) : ℤ) : ℝ) * (((u : ℤˣ) : ℤ) : ℝ) = 1 := by
  exact_mod_cast Int.units_coe_mul_self u
def signedPermMap {N : ℕ} (σ : Equiv.Perm (Fin N)) (ε : Fin N → ℤˣ) :
    (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun x k := (((ε (σ.symm k) : ℤˣ) : ℤ) : ℝ) * x (σ.symm k)
  map_add' x y := by
    funext k
    simp [mul_add]
  map_smul' c x := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem signedPermMap_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (ε : Fin N → ℤˣ) (x : Fin N → ℝ)
    (k : Fin N) : signedPermMap σ ε x k = (((ε (σ.symm k) : ℤˣ) : ℤ) : ℝ) * x (σ.symm k) := rfl
theorem signedPermMap_single {N : ℕ} (σ : Equiv.Perm (Fin N)) (ε : Fin N → ℤˣ) (j : Fin N) :
    signedPermMap σ ε (Pi.single j 1) = (((ε j : ℤˣ) : ℤ) : ℝ) • Pi.single (σ j) (1 : ℝ) := by
  funext k
  rw [signedPermMap_apply]
  by_cases h : k = σ j
  · subst h
    simp
  · have h' : σ.symm k ≠ j := fun e => h (by rw [← e]; simp)
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
theorem signedPermMap_sqrt_sum_sq {N : ℕ} (σ : Equiv.Perm (Fin N)) (ε : Fin N → ℤˣ) (x : Fin N → ℝ) :
    Real.sqrt (∑ j, signedPermMap σ ε x j ^ 2) = Real.sqrt (∑ j, x j ^ 2) := by
  congr 1
  rw [← Equiv.sum_comp σ.symm (fun j => x j ^ 2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [signedPermMap_apply, mul_pow, sq (((ε (σ.symm k) : ℤˣ) : ℤ) : ℝ), intUnit_cast_mul_self, one_mul]
def permOfPairs {n : ℕ+} (τ : Equiv.Perm (Fin (n : ℕ) × Fin 4)) :
    Equiv.Perm (Fin (4 * (n : ℕ))) :=
  (pairIndex n).permCongr τ
def blockPermCoords {n : ℕ+} (ς : Equiv.Perm (Fin (n : ℕ))) : Equiv.Perm (Fin (4 * (n : ℕ))) :=
  permOfPairs (ς.prodCongr (Equiv.refl _))
def framePermCoords (n : ℕ+) (w : SignedFrame) : Equiv.Perm (Fin (4 * (n : ℕ))) :=
  permOfPairs ((Equiv.refl _).prodCongr (axisPerm w))
def frameSignsCoords (n : ℕ+) (w : SignedFrame) (j : Fin (4 * (n : ℕ))) : ℤˣ :=
  axisSign w ((pairIndex n).symm j).2
def blockPermMap {n : ℕ+} (ς : Equiv.Perm (Fin (n : ℕ))) : Coords n →ₗ[ℝ] Coords n :=
  signedPermMap (blockPermCoords ς) fun _ => 1
def frameLinMap (n : ℕ+) (w : SignedFrame) : Coords n →ₗ[ℝ] Coords n :=
  signedPermMap (framePermCoords n w) (frameSignsCoords n w)
theorem permOfPairs_symm_apply {n : ℕ+} (τ : Equiv.Perm (Fin (n : ℕ) × Fin 4))
    (a : Fin (n : ℕ) × Fin 4) :
    (permOfPairs τ).symm (pairIndex n a) = pairIndex n (τ.symm a) := by
  rw [Equiv.symm_apply_eq]
  simp [permOfPairs, Equiv.permCongr_apply]
theorem block_blockPermMap {n : ℕ+} (ς : Equiv.Perm (Fin (n : ℕ))) (x : Coords n)
    (i : Fin (n : ℕ)) : (blockPermMap ς x).block i = x.block (ς.symm i) := by
  funext μ
  rw [block_apply, block_apply, blockPermMap, signedPermMap_apply]
  simp [blockPermCoords, permOfPairs_symm_apply]
theorem block_frameLinMap (n : ℕ+) (w : SignedFrame) (x : Coords n) (i : Fin (n : ℕ)) :
    (frameLinMap n w x).block i = w.actOnVector (x.block i) := by
  funext μ
  rw [block_apply, frameLinMap, signedPermMap_apply, SignedFrame.actOnVector, block_apply]
  simp [framePermCoords, frameSignsCoords, permOfPairs_symm_apply, axisSign, axisPerm]
end Signed
section Lift
variable {D : Params} {E : Kind} {n : ℕ+}
theorem blockPermMap_inv_apply (ς : Equiv.Perm (Fin (n : ℕ))) (x : Coords n) :
    blockPermMap ς (blockPermMap ς⁻¹ x) = x :=
  coords_ext_block fun i => by
    rw [block_blockPermMap, block_blockPermMap]
    simp [Equiv.Perm.inv_def]
theorem frameLinMap_frameInv_apply (w : SignedFrame) (x : Coords n) :
    frameLinMap n w (frameLinMap n (frameInv w) x) = x :=
  coords_ext_block fun i => by
    rw [block_frameLinMap, block_frameLinMap]
    have h := frameInv_actOnVector_actOnVector (frameInv w) (x.block i)
    rwa [frameInv_frameInv] at h
theorem liftsToSignedPerm_holds
    (hq : WellPosedness.QuotMapSurjectiveHomWithKernel D E)
    (ψ : TupleMap D E n) : LiftsToSignedPerm ψ := by
  cases ψ with
  | permute ς =>
    refine ⟨blockPermCoords ς, fun _ => 1, 0, blockPermMap ς, fun j => signedPermMap_single _ _ j,
      fun x => ?_, fun x => signedPermMap_sqrt_sum_sq _ _ x, ?_⟩
    · funext i
      rw [add_zero]
      change E.quotMap D (x.block (ς.symm i)) = E.quotMap D ((blockPermMap ς x).block i)
      rw [block_blockPermMap]
    · apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩ i
        rw [block_blockPermMap]
        exact hx _
      · intro z hz
        exact ⟨blockPermMap ς⁻¹ z, fun i => by rw [block_blockPermMap]; exact hz _,
          blockPermMap_inv_apply ς z⟩
  | frameDiag w =>
    refine ⟨framePermCoords n w, frameSignsCoords n w, 0, frameLinMap n w,
      fun j => signedPermMap_single _ _ j, fun x => ?_, fun x => signedPermMap_sqrt_sum_sq _ _ x, ?_⟩
    · funext i
      rw [add_zero]
      change frameAct D E w (E.quotMap D (x.block i)) =
        E.quotMap D ((frameLinMap n w x).block i)
      rw [block_frameLinMap, frameAct_quotMap hq]
    · apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩ i
        rw [block_frameLinMap]
        exact actOnVector_mem_periodGroup w (hx _)
      · intro z hz
        exact ⟨frameLinMap n (frameInv w) z,
          fun i => by rw [block_frameLinMap]; exact actOnVector_mem_periodGroup _ (hz _),
          frameLinMap_frameInv_apply w z⟩
  | translate v =>
    have hb : ∀ i, Coords.block (p := n)
        (fun j => pickLift D E v ((pairIndex n).symm j).2) i = pickLift D E v := by
      intro i
      funext μ
      rw [block_apply]
      simp
    refine ⟨1, fun _ => 1, fun j => pickLift D E v ((pairIndex n).symm j).2, LinearMap.id,
      fun j => by simp, fun x => ?_, fun x => rfl, by simp⟩
    funext i
    change addPt D E (E.quotMap D (x.block i)) v =
      E.quotMap D ((x + fun j => pickLift D E v ((pairIndex n).symm j).2).block i)
    rw [block_add_eq, hb, addPt_eq_add hq, hq.1, quotMap_pickLift hq]
theorem tupleDist_of_affineLift (h2 : DistEqMinTranslateNorm D E n)
    (hs : Function.Surjective (Tuple.proj D E (p := n)))
    {Ψ : E.Tuple D n → E.Tuple D n} {A : Coords n →ₗ[ℝ] Coords n}
    {b : Coords n}
    (hπ : ∀ x, Ψ (Tuple.proj D E x) = Tuple.proj D E (A x + b))
    (hn : ∀ x, Real.sqrt (∑ j, A x j ^ 2) = Real.sqrt (∑ j, x j ^ 2))
    (hper : A '' Tuple.periodSet D E n = Tuple.periodSet D E n)
    (y y' : E.Tuple D n) :
    Tuple.tupleDist D E (Ψ y) (Ψ y') = Tuple.tupleDist D E y y' := by
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨x', rfl⟩ := hs y'
  rw [hπ, hπ]
  have hd : ∀ k, A x + b - (A x' + b) - A k = A (x - x' - k) := by
    intro k
    simp only [map_sub]
    abel
  have sets : translateNorms D E n (A x + b) (A x' + b) =
      translateNorms D E n x x' := by
    ext r
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [← hper] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      refine ⟨k', hk', ?_⟩
      rw [hd]
      exact hn _
    · rintro ⟨k, hk, rfl⟩
      refine ⟨A k, by rw [← hper]; exact ⟨k, hk, rfl⟩, ?_⟩
      rw [hd]
      exact (hn _).symm
  have h1 := (h2 (A x + b) (A x' + b)).1
  rw [sets] at h1
  exact h1.unique (h2 x x').1
end Lift
section Derivatives
variable {n : ℕ+}
theorem hasLineDerivAt_const_mul_left (c : ℂ) {G : Coords n → ℂ} {L : ℂ} {x v : Coords n}
    (h : HasLineDerivAt ℝ G L x v) : HasLineDerivAt ℝ (fun z => c * G z) (c * L) x v :=
  HasDerivAt.const_mul c h
variable {A : Coords n →ₗ[ℝ] Coords n} {b : Coords n}
  {σ : Equiv.Perm (Fin (4 * (n : ℕ)))} {ε : Fin (4 * (n : ℕ)) → ℤˣ}
theorem hasLineDerivAt_comp_affine
    (hA : ∀ j, A (Pi.single j 1) = (((ε j : ℤˣ) : ℤ) : ℝ) • Pi.single (σ j) (1 : ℝ))
    (G : Coords n → ℂ) (x : Coords n) (j : Fin (4 * (n : ℕ)))
    (h : LineDifferentiableAt ℝ G (A x + b) (Pi.single (σ j) 1)) :
    HasLineDerivAt ℝ (fun z => G (A z + b))
      ((((((ε j : ℤˣ) : ℤ) : ℝ)) : ℂ) * lineDeriv ℝ G (A x + b) (Pi.single (σ j) 1)) x
      (Pi.single j 1) := by
  have h1 := h.hasLineDerivAt.smul ((((ε j : ℤˣ) : ℤ) : ℝ))
  rw [Complex.real_smul] at h1
  unfold HasLineDerivAt at h1 ⊢
  convert h1 using 1
  funext t
  change G (A (x + t • Pi.single j 1) + b) = _
  congr 1
  rw [map_add, map_smul, hA]
  abel
theorem contPartialsUpTo_comp_affine
    (hA : ∀ j, A (Pi.single j 1) = (((ε j : ℤˣ) : ℤ) : ℝ) • Pi.single (σ j) (1 : ℝ)) :
    ∀ (ν : ℕ) (G : Coords n → ℂ), Coords.ContPartialsUpTo ν G →
      ∀ c : ℂ, Coords.ContPartialsUpTo ν (fun x => c * G (A x + b)) := by
  have hT : Continuous fun x => A x + b :=
    A.continuous_of_finiteDimensional.add continuous_const
  intro ν
  induction ν with
  | zero =>
    intro G hG c
    exact continuous_const.mul (Continuous.comp hG hT)
  | succ ν ih =>
    intro G hG c
    obtain ⟨hc, hp⟩ := hG
    refine ⟨continuous_const.mul (hc.comp hT), fun j => ?_⟩
    obtain ⟨hd, hn⟩ := hp (σ j)
    have key := fun x =>
      hasLineDerivAt_const_mul_left c (hasLineDerivAt_comp_affine (b := b) hA G x j (hd _))
    refine ⟨fun x => (key x).lineDifferentiableAt, ?_⟩
    have h : Coords.partialAlong j (fun x => c * G (A x + b)) = fun x =>
        (c * (((((ε j : ℤˣ) : ℤ) : ℝ)) : ℂ)) * Coords.partialAlong (σ j) G (A x + b) := by
      funext x
      rw [Coords.partialAlong, (key x).lineDeriv, Coords.partialAlong, mul_assoc]
    rw [h]
    exact ih _ hn _
theorem iterPartial_single_eq (j : Fin (4 * (n : ℕ))) (G : Coords n → ℂ) :
    Coords.iterPartial (Pi.single j 1) G = Coords.partialAlong j G := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.iterPartial_single <;> assumption
theorem iterPartial_zero_eq (G : Coords n → ℂ) :
    Coords.iterPartial (0 : CoordIndex n) G = G := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.iterPartial_zero <;> assumption
theorem coordIndex_degree_single (j : Fin (4 * (n : ℕ))) :
    CoordIndex.degree (Pi.single j 1 : CoordIndex n) = 1 := by
  simp [CoordIndex.degree]
theorem coordIndex_degree_add (α β : CoordIndex n) :
    CoordIndex.degree (α + β) = α.degree + β.degree := by
  simp [CoordIndex.degree, Finset.sum_add_distrib]
theorem coordIndex_degree_comp_perm (α : CoordIndex n) (τ : Equiv.Perm (Fin (4 * (n : ℕ)))) :
    CoordIndex.degree (α ∘ τ) = α.degree :=
  Equiv.sum_comp τ α
theorem norm_intUnit_cast (u : ℤˣ) : ‖(((((u : ℤˣ) : ℤ) : ℝ)) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp
variable {D : Params} {E : Kind} {Ψ : E.Tuple D n → E.Tuple D n}
theorem isClassC_const_mul_comp
    (hA : ∀ j, A (Pi.single j 1) = (((ε j : ℤˣ) : ℤ) : ℝ) • Pi.single (σ j) (1 : ℝ))
    (hπ : ∀ x, Ψ (Tuple.proj D E x) = Tuple.proj D E (A x + b))
    {ν : ℕ} {F : E.Tuple D n → ℂ} (hF : Tuple.IsClassC D E ν F) (c : ℂ) :
    Tuple.IsClassC D E ν (fun y => c * F (Ψ y)) := by
  have h : (fun y => c * F (Ψ y)) ∘ Tuple.proj D E =
      fun x => c * (F ∘ Tuple.proj D E) (A x + b) := by
    funext x
    simp [hπ]
  unfold Tuple.IsClassC
  rw [h]
  exact contPartialsUpTo_comp_affine hA ν _ hF c
theorem isClassC_comp
    (hA : ∀ j, A (Pi.single j 1) = (((ε j : ℤˣ) : ℤ) : ℝ) • Pi.single (σ j) (1 : ℝ))
    (hπ : ∀ x, Ψ (Tuple.proj D E x) = Tuple.proj D E (A x + b))
    {ν : ℕ} {F : E.Tuple D n → ℂ} (hF : Tuple.IsClassC D E ν F) :
    Tuple.IsClassC D E ν (F ∘ Ψ) := by
  simpa [Function.comp_def] using isClassC_const_mul_comp hA hπ hF 1
variable (hD : DerivFacts D E n)
  (hs : Function.Surjective (Tuple.proj D E (p := n)))
include hD hs
theorem partialDeriv_zero_eq {ν : ℕ} {F : E.Tuple D n → ℂ}
    (hF : Tuple.IsClassC D E ν F) : Tuple.partialDeriv D E 0 F = F := by
  have h := (hD ν F hF 0 (by simp [CoordIndex.degree])).2.1
  rw [iterPartial_zero_eq] at h
  exact hs.injective_comp_right h
theorem partialDeriv_single_const_mul_comp
    (hA : ∀ j, A (Pi.single j 1) = (((ε j : ℤˣ) : ℤ) : ℝ) • Pi.single (σ j) (1 : ℝ))
    (hπ : ∀ x, Ψ (Tuple.proj D E x) = Tuple.proj D E (A x + b))
    {ν : ℕ} (hν : 1 ≤ ν) {F : E.Tuple D n → ℂ} (hF : Tuple.IsClassC D E ν F)
    (c : ℂ) (j : Fin (4 * (n : ℕ))) :
    Tuple.partialDeriv D E (Pi.single j 1) (fun y => c * F (Ψ y)) = fun y =>
      (c * (((((ε j : ℤˣ) : ℤ) : ℝ)) : ℂ)) *
        Tuple.partialDeriv D E (Pi.single (σ j) 1) F (Ψ y) := by
  have hK := isClassC_const_mul_comp hA hπ hF c
  apply hs.injective_comp_right
  change Tuple.partialDeriv D E (Pi.single j 1) (fun y => c * F (Ψ y)) ∘
      Tuple.proj D E = _
  rw [(hD ν _ hK _ (by rw [coordIndex_degree_single]; exact hν)).2.1, iterPartial_single_eq]
  funext x
  have hline : LineDifferentiableAt ℝ (F ∘ Tuple.proj D E) (A x + b)
      (Pi.single (σ j) 1) := by
    obtain ⟨ν', rfl⟩ : ∃ ν', ν = ν' + 1 := ⟨ν - 1, by omega⟩
    exact (hF.2 (σ j)).1 _
  have key := hasLineDerivAt_const_mul_left c (hasLineDerivAt_comp_affine (b := b) hA _ x j hline)
  have hc := congrFun ((hD ν F hF (Pi.single (σ j) 1)
    (by rw [coordIndex_degree_single]; exact hν)).2.1) (A x + b)
  rw [iterPartial_single_eq] at hc
  have hfun : (fun y => c * F (Ψ y)) ∘ Tuple.proj D E =
      fun z => c * (F ∘ Tuple.proj D E) (A z + b) := by
    funext z
    simp [hπ]
  rw [hfun, Coords.partialAlong, key.lineDeriv]
  simp only [Function.comp_apply, hπ] at hc ⊢
  rw [hc, Coords.partialAlong, mul_assoc]
theorem partialDeriv_comp
    (hA : ∀ j, A (Pi.single j 1) = (((ε j : ℤˣ) : ℤ) : ℝ) • Pi.single (σ j) (1 : ℝ))
    (hπ : ∀ x, Ψ (Tuple.proj D E x) = Tuple.proj D E (A x + b)) :
    ∀ (m : ℕ) (α : CoordIndex n), α.degree = m →
      ∀ (ν : ℕ) (F : E.Tuple D n → ℂ), Tuple.IsClassC D E ν F → m ≤ ν →
        ∃ c : ℂ, ‖c‖ = 1 ∧ Tuple.partialDeriv D E α (F ∘ Ψ) = fun y =>
          c * Tuple.partialDeriv D E (α ∘ σ.symm) F (Ψ y) := by
  intro m
  induction m with
  | zero =>
    intro α hα ν F hF _
    have h0 : α = 0 := by
      funext k
      exact (Finset.sum_eq_zero_iff.1 hα) k (Finset.mem_univ k)
    subst h0
    refine ⟨1, by simp, ?_⟩
    have h1 : (0 : CoordIndex n) ∘ σ.symm = 0 := rfl
    rw [h1, partialDeriv_zero_eq hD hs (isClassC_comp hA hπ hF), partialDeriv_zero_eq hD hs hF]
    funext y
    simp
  | succ m ih =>
    intro α hα ν F hF hm
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      have : α.degree = 0 := Finset.sum_eq_zero fun k _ => hcon k
      omega
    have hsplit : (α - Pi.single j 1) + Pi.single j 1 = α := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
        omega
      · simp [Pi.single_eq_of_ne hk]
    set α' : CoordIndex n := α - Pi.single j 1 with hα'
    have hord : α'.degree = m := by
      have := coordIndex_degree_add α' (Pi.single j 1)
      rw [hsplit, coordIndex_degree_single] at this
      omega
    obtain ⟨c, hc, hder⟩ := ih α' hord ν F hF (by omega)
    have hK := isClassC_comp hA hπ hF
    have hcomm := (hD ν (F ∘ Ψ) hK α' (by omega)).2.2.2.2.1 (Pi.single j 1)
      (by rw [coordIndex_degree_single]; omega)
    have hordσ : CoordIndex.degree (α' ∘ σ.symm) = m := by rw [coordIndex_degree_comp_perm, hord]
    have hG := (hD ν F hF (α' ∘ σ.symm) (by omega)).2.2.2.1
    have hcomm' := (hD ν F hF (α' ∘ σ.symm) (by omega)).2.2.2.2.1 (Pi.single (σ j) 1)
      (by rw [coordIndex_degree_single]; omega)
    refine ⟨c * (((((ε j : ℤˣ) : ℤ) : ℝ)) : ℂ), by rw [norm_mul, hc, norm_intUnit_cast, one_mul], ?_⟩
    have hindex : α' ∘ σ.symm + Pi.single (σ j) 1 = α ∘ σ.symm := by
      funext k
      have : (Pi.single (σ j) 1 : CoordIndex n) k =
          (Pi.single j 1 : CoordIndex n) (σ.symm k) := by
        by_cases hk : k = σ j
        · subst hk
          simp
        · have hk' : σ.symm k ≠ j := fun e => hk (by rw [← e]; simp)
          simp [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk']
      rw [Pi.add_apply, this, Function.comp_apply, Function.comp_apply]
      exact congrFun hsplit _
    rw [← hindex, ← hcomm', ← hsplit, ← hcomm, hder]
    exact partialDeriv_single_const_mul_comp hD hs hA hπ (by omega) hG c j
theorem cNorm_comp
    (hA : ∀ j, A (Pi.single j 1) = (((ε j : ℤˣ) : ℤ) : ℝ) • Pi.single (σ j) (1 : ℝ))
    (hπ : ∀ x, Ψ (Tuple.proj D E x) = Tuple.proj D E (A x + b))
    (hΨ : Function.Surjective Ψ) {ν : ℕ} {F : E.Tuple D n → ℂ}
    (hF : Tuple.IsClassC D E ν F) :
    Tuple.cNorm D E ν (F ∘ Ψ) = Tuple.cNorm D E ν F := by
  unfold Tuple.cNorm
  apply le_antisymm
  · refine iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_
    obtain ⟨c, hc, h⟩ := partialDeriv_comp hD hs hA hπ _ α rfl ν F hF hα
    rw [h]
    simp only [norm_mul, hc, one_mul]
    exact le_iSup_of_le (α ∘ σ.symm) (le_iSup_of_le (by rw [coordIndex_degree_comp_perm]; exact hα)
      (le_iSup_of_le (Ψ y) le_rfl))
  · refine iSup_le fun β => iSup_le fun hβ => iSup_le fun y => ?_
    obtain ⟨y', rfl⟩ := hΨ y
    have hα : CoordIndex.degree (β ∘ σ) ≤ ν := by rw [coordIndex_degree_comp_perm]; exact hβ
    obtain ⟨c, hc, h⟩ := partialDeriv_comp hD hs hA hπ _ (β ∘ σ) rfl ν F hF hα
    have hβ' : (β ∘ σ) ∘ σ.symm = β := by
      funext k
      simp
    rw [hβ'] at h
    have hnorm : ‖Tuple.partialDeriv D E (β ∘ σ) (F ∘ Ψ) y'‖ =
        ‖Tuple.partialDeriv D E β F (Ψ y')‖ := by
      rw [h]
      simp [hc]
    rw [← hnorm]
    exact le_iSup_of_le (β ∘ σ) (le_iSup_of_le hα (le_iSup_of_le y' le_rfl))
end Derivatives
section Assembly
variable {D : Params} {E : Kind} {n : ℕ+}
def onlyIndex : Fin ((1 : ℕ+) : ℕ) := ⟨0, (1 : ℕ+).pos⟩
theorem eq_onlyIndex (i : Fin ((1 : ℕ+) : ℕ)) : i = onlyIndex :=
  Fin.ext (by have := i.2; simp only [PNat.one_coe] at this; simp only [onlyIndex]; omega)
theorem quotDist_nonneg (a b : E.Pt D) : 0 ≤ quotDist D E a b := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_nonneg <;> assumption
theorem tupleDist_single (y y' : E.Tuple D 1) :
    Tuple.tupleDist D E y y' = quotDist D E (y onlyIndex) (y' onlyIndex) := by
  have h : ∑ i : Fin ((1 : ℕ+) : ℕ), quotDist D E (y i) (y' i) ^ 2 =
      quotDist D E (y onlyIndex) (y' onlyIndex) ^ 2 := by
    rw [Finset.sum_eq_single onlyIndex]
    · intro i _ hi
      exact absurd (eq_onlyIndex i) hi
    · intro hi
      exact absurd (Finset.mem_univ _) hi
  rw [Tuple.tupleDist, h, Real.sqrt_sq (quotDist_nonneg _ _)]
theorem quotDist_eq_zero_iff (hM : DistIsMetric D E 1) (a b : E.Pt D) :
    quotDist D E a b = 0 ↔ a = b := by
  have h := hM.2.1 (fun _ => a) (fun _ => b)
  rw [tupleDist_single] at h
  refine h.trans ⟨fun e => congrFun e onlyIndex, fun e => by rw [e]⟩
theorem exists_pos_le_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ f i := by apply _root_.YangMills.Construction.BoundsOnEverySide.SubsequentialLimits.exists_pos_lower_bound <;> assumption
theorem isOpenT_pairwiseDistinct (hM : DistIsMetric D E 1)
    (hc : FactorDistContinuous D E n) :
    Tuple.IsOpenT D E (pairwiseDistinct D E n) := by
  intro y hy
  have hy' : Function.Injective y := hy
  have hpair : ∀ a : Fin (n : ℕ) × Fin (n : ℕ), ∃ δ : ℝ, 0 < δ ∧
      ∀ z, Tuple.tupleDist D E y z < δ → a.1 ≠ a.2 → z a.1 ≠ z a.2 := by
    rintro ⟨i, k⟩
    by_cases hik : i = k
    · exact ⟨1, one_pos, fun _ _ h => absurd hik h⟩
    · have hpos : 0 < quotDist D E (y i) (y k) :=
        lt_of_le_of_ne (quotDist_nonneg _ _)
          (fun e => hik (hy' ((quotDist_eq_zero_iff hM _ _).1 e.symm)))
      obtain ⟨δ, hδ, h⟩ := hc i k hik y _ hpos
      refine ⟨δ, hδ, fun z hz _ e => ?_⟩
      have h1 : dist (quotDist D E (y i) (y k)) (quotDist D E (z i) (z k)) <
          quotDist D E (y i) (y k) := h z hz
      have h2 : quotDist D E (z i) (z k) = 0 := (quotDist_eq_zero_iff hM _ _).2 e
      rw [h2, Real.dist_eq, sub_zero, abs_of_pos hpos] at h1
      exact lt_irrefl _ h1
  choose δ hδ hpr using hpair
  obtain ⟨r, hr, hle⟩ := exists_pos_le_of_finite δ hδ
  refine ⟨r, hr, fun z hz i k e => ?_⟩
  by_contra hik
  exact hpr (i, k) z (lt_of_lt_of_le hz (hle _)) hik e
theorem actPts_mem_pairwiseDistinct
    (hq : WellPosedness.QuotMapSurjectiveHomWithKernel D E)
    (ψ : TupleMap D E n) {y : E.Tuple D n} (hy : y ∈ pairwiseDistinct D E n) :
    ψ.actPts y ∈ pairwiseDistinct D E n := by
  have hy' : Function.Injective y := hy
  cases ψ with
  | permute ς => exact hy'.comp ς.symm.injective
  | frameDiag w =>
    intro i k hik
    have h := congrArg (frameAct D E (frameInv w)) hik
    simp only [TupleMap.actPts, frameAct_frameInv_frameAct hq] at h
    exact hy' h
  | translate v =>
    intro i k hik
    simp only [TupleMap.actPts, addPt_eq_add hq] at hik
    exact hy' (add_right_cancel hik)
theorem isIsometricEquiv_holds
    (hq : WellPosedness.QuotMapSurjectiveHomWithKernel D E)
    (hs : Function.Surjective (Tuple.proj D E (p := n)))
    (hL : DistEqMinTranslateNorm D E n) (ψ : TupleMap D E n) : IsIsometricEquiv ψ := by
  obtain ⟨σ, ε, b, A, hA, hπ, hn, hper⟩ := liftsToSignedPerm_holds hq ψ
  refine ⟨⟨Function.LeftInverse.injective (symm_actPts_actPts hq ψ),
    Function.RightInverse.surjective (actPts_symm_actPts hq ψ)⟩,
    tupleDist_of_affineLift hL hs hπ hn hper, symm_actPts_actPts hq ψ, actPts_symm_actPts hq ψ, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact actPts_mem_pairwiseDistinct hq ψ hy
  · intro z hz
    exact ⟨ψ.symm.actPts z, actPts_mem_pairwiseDistinct hq ψ.symm hz, actPts_symm_actPts hq ψ z⟩
theorem preservesFunctionClasses_holds
    (hq : WellPosedness.QuotMapSurjectiveHomWithKernel D E)
    (hs : Function.Surjective (Tuple.proj D E (p := n)))
    (hL : DistEqMinTranslateNorm D E n) (hM : DistIsMetric D E 1)
    (hc : FactorDistContinuous D E n)
    (hD : DerivFacts D E n) (ψ : TupleMap D E n) :
    PreservesFunctionClasses ψ := by
  obtain ⟨σ, ε, b, A, hA, hπ, -, -⟩ := liftsToSignedPerm_holds hq ψ
  have hiso := isIsometricEquiv_holds hq hs hL ψ
  have hiso' := isIsometricEquiv_holds hq hs hL ψ.symm
  have hsupp : ∀ F : E.Tuple D n → ℂ,
      Tuple.supportT D E (F ∘ ψ.actPts) =
        ψ.actPts ⁻¹' Tuple.supportT D E F := fun F =>
    closureWrt_preimage_of_isometry _ hiso.2.1 (actPts_symm_actPts hq ψ) {y | F y ≠ 0}
  refine ⟨hsupp, fun ν F hF => ⟨isClassC_comp hA hπ hF,
    cNorm_comp hD hs hA hπ hiso.1.2 hF⟩, isOpenT_pairwiseDistinct hM hc, ?_,
    fun _ _ => rfl, fun _ _ => rfl⟩
  rintro F ⟨hsm, hcpt, hsub⟩
  refine ⟨fun ν => isClassC_comp hA hπ (hsm ν), ?_, ?_⟩
  · rw [hsupp]
    have himage : ψ.actPts ⁻¹' Tuple.supportT D E F =
        ψ.symm.actPts '' Tuple.supportT D E F := by
      ext y
      constructor
      · intro hy
        exact ⟨_, hy, symm_actPts_actPts hq ψ y⟩
      · rintro ⟨z, hz, rfl⟩
        rw [Set.mem_preimage, actPts_symm_actPts hq]
        exact hz
    rw [himage]
    exact isCompactWrt_image_of_isometry _ hiso'.2.1 (actPts_symm_actPts hq ψ)
      (symm_actPts_actPts hq ψ) hcpt
  · rw [hsupp]
    intro y hy
    have h := actPts_mem_pairwiseDistinct hq ψ.symm (hsub hy)
    rwa [symm_actPts_actPts hq] at h
section Entries
variable (hq : WellPosedness.QuotMapSurjectiveHomWithKernel D E)
  (hs₁ : Function.Surjective (Tuple.proj D E (p := 1)))
  (hL₁ : DistEqMinTranslateNorm D E 1)
  (hT : SingleC1Agree D E)
  {ψ₁ : TupleMap D E 1} {ρ : E.Pt D → E.Pt D}
  (hρ : ∀ y, ψ₁.actPts y = fun i => ρ (y i))
def componentInv (ψ₁ : TupleMap D E 1) (a : E.Pt D) : E.Pt D :=
  ψ₁.symm.actPts (fun _ => a) onlyIndex
include hq hρ
theorem componentInv_apply_component (a : E.Pt D) : componentInv ψ₁ (ρ a) = a := by
  have h := symm_actPts_actPts hq ψ₁ (fun _ => a)
  rw [hρ] at h
  exact congrFun h onlyIndex
theorem entry_apply_entryInv (a : E.Pt D) : ρ (componentInv ψ₁ a) = a := by
  have h := actPts_symm_actPts hq ψ₁ (fun _ => a)
  rw [hρ] at h
  exact congrFun h onlyIndex
include hs₁ hL₁
theorem quotDist_comp_equiv (a c : E.Pt D) : quotDist D E (ρ a) (ρ c) = quotDist D E a c := by
  have h := (isIsometricEquiv_holds hq hs₁ hL₁ ψ₁).2.1 (fun _ => a) (fun _ => c)
  rw [hρ, hρ, tupleDist_single, tupleDist_single] at h
  exact h
theorem quotDist_comp_equivInv (a c : E.Pt D) :
    quotDist D E (componentInv ψ₁ a) (componentInv ψ₁ c) = quotDist D E a c := by
  rw [← quotDist_comp_equiv hq hs₁ hL₁ hρ, entry_apply_entryInv hq hρ,
    entry_apply_entryInv hq hρ]
theorem supportQ_comp_reindex {Z : Type*} [Zero Z] (u : E.Pt D → Z) :
    supportQ D E (u ∘ ρ) = ρ ⁻¹' supportQ D E u :=
  closureWrt_preimage_of_isometry _ (quotDist_comp_equiv hq hs₁ hL₁ hρ) (entry_apply_entryInv hq hρ)
    {y | u y ≠ 0}
theorem isCompactQ_preimage_component {K : Set (E.Pt D)} (hK : IsCompactQ D E K) :
    IsCompactQ D E (ρ ⁻¹' K) := by
  have himage : ρ ⁻¹' K = componentInv ψ₁ '' K := by
    ext y
    constructor
    · intro hy
      exact ⟨_, hy, componentInv_apply_component hq hρ y⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_preimage, entry_apply_entryInv hq hρ]
      exact hz
  rw [himage]
  exact isCompactWrt_image_of_isometry _ (quotDist_comp_equivInv hq hs₁ hL₁ hρ)
    (entry_apply_entryInv hq hρ) (componentInv_apply_component hq hρ) hK
omit hq hs₁ hL₁ in
theorem ofSingle_comp_point {Z : Type*} (φ : E.Pt D → Z) :
    Tuple.ofSingle D E (φ ∘ ρ) = Tuple.ofSingle D E φ ∘ ψ₁.actPts := by
  funext y
  simp [Tuple.ofSingle, hρ]
omit hs₁ hL₁ in
theorem isClassC_ofSingle_comp_component {ν : ℕ} {φ : E.Pt D → ℂ}
    (hφ : Tuple.IsClassC D E ν (Tuple.ofSingle D E φ)) :
    Tuple.IsClassC D E ν (Tuple.ofSingle D E (φ ∘ ρ)) := by
  obtain ⟨σ, ε, b, A, hA, hπ, -, -⟩ := liftsToSignedPerm_holds hq ψ₁
  rw [ofSingle_comp_point hρ]
  exact isClassC_comp hA hπ hφ
omit hs₁ hL₁ in
theorem isSmoothT_ofSingle_comp_component {φ : E.Pt D → ℂ}
    (hφ : Tuple.IsSmoothT D E (Tuple.ofSingle D E φ)) :
    Tuple.IsSmoothT D E (Tuple.ofSingle D E (φ ∘ ρ)) :=
  fun ν => isClassC_ofSingle_comp_component hq hρ (hφ ν)
omit hs₁ hL₁ in
include hT in
theorem isC1Fn_comp_component {u : E.Pt D → ℝ} (hu : IsC1Fn D E u) :
    IsC1Fn D E (u ∘ ρ) := by
  refine ((hT (u ∘ ρ)).1).1 ?_
  exact isClassC_ofSingle_comp_component hq hρ (φ := fun y => (u y : ℂ)) ((hT u).1.2 hu)
include hT in
theorem preservesTuples_of_component (ψ : TupleMap D E n) {ρi : E.Pt D → E.Pt D}
    (h2 : ∀ (Z : Type) (f : Fin (n : ℕ) → E.Pt D → Z), ψ.actFns f = fun i => f i ∘ ρ)
    (h3 : ∀ y, ψ.symm.actPts y = fun i => ρ (y i))
    (h4 : ∀ (Z : Type) (g : Fin (n : ℕ) → E.Pt D → Z),
      ψ.symm.actFns g = fun i => g i ∘ ρi)
    (h5 : ∀ a, ρ (ρi a) = a) : PreservesTuples ψ := by
  refine ⟨?_, ?_, ?_, fun f => ⟨?_, ?_⟩⟩
  · rintro f ⟨hC, hK, hdis⟩
    rw [h2]
    refine ⟨fun i => isC1Fn_comp_component hq hT hρ (hC i), fun i => ?_, fun i k hik => ?_⟩
    · rw [supportQ_comp_reindex hq hs₁ hL₁ hρ]
      exact isCompactQ_preimage_component hq hs₁ hL₁ hρ (hK i)
    · rw [supportQ_comp_reindex hq hs₁ hL₁ hρ, supportQ_comp_reindex hq hs₁ hL₁ hρ]
      exact (hdis i k hik).preimage ρ
  · intro f hf i
    rw [h2]
    exact isSmoothT_ofSingle_comp_component hq hρ (φ := fun y => (f i y : ℂ)) (hf i)
  · intro f hf i
    rw [h2]
    exact isSmoothT_ofSingle_comp_component hq hρ (hf i)
  · funext y
    rw [h2, Function.comp_apply, h3]
    rfl
  · rw [h2, h4]
    funext i y
    simp [h5]
end Entries
theorem preservesTuples_holds
    (hq : WellPosedness.QuotMapSurjectiveHomWithKernel D E)
    (hs₁ : Function.Surjective (Tuple.proj D E (p := 1)))
    (hL₁ : DistEqMinTranslateNorm D E 1) (hT : SingleC1Agree D E)
    (ψ : TupleMap D E n) : PreservesTuples ψ := by
  cases ψ with
  | permute ς =>
    refine ⟨?_, fun f hf i => hf _, fun f hf i => hf _, fun f => ⟨?_, ?_⟩⟩
    · rintro f ⟨hC, hK, hdis⟩
      exact ⟨fun i => hC _, fun i => hK _, fun i k hik => hdis _ _ (ς.symm.injective.ne hik)⟩
    · funext y
      have h := Equiv.prod_comp ς (fun j => f (ς.symm j) (y j))
      simp only [Equiv.symm_apply_apply] at h
      exact h.symm
    · funext i y
      simp [TupleMap.symm, TupleMap.actFns, Equiv.Perm.inv_def]
  | frameDiag w =>
    refine preservesTuples_of_component hq hs₁ hL₁ hT (ψ₁ := TupleMap.frameDiag (frameInv w))
      (ρ := frameAct D E (frameInv w)) (fun _ => rfl) _
      (ρi := frameAct D E (frameInv (frameInv w)))
      (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun a => ?_)
    rw [frameInv_frameInv]
    exact frameAct_frameInv_frameAct hq w a
  | translate v =>
    have hsum : ∀ y, addPt D E y (subPt D E (E.quotMap D 0) v) =
        subPt D E y v := by
      intro y
      rw [addPt_eq_add hq, subPt_eq_sub hq, subPt_eq_sub hq, quotMap_zero_eq hq]
      abel
    refine preservesTuples_of_component hq hs₁ hL₁ hT
      (ψ₁ := TupleMap.translate (subPt D E (E.quotMap D 0) v))
      (ρ := fun y => subPt D E y v)
      (fun y => by funext i; exact hsum _) _
      (ρi := fun y => subPt D E y (subPt D E (E.quotMap D 0) v))
      (fun _ _ => rfl) (fun y => by funext i; exact hsum _) (fun _ _ => rfl) (fun a => ?_)
    simp only [subPt_eq_sub hq, quotMap_zero_eq hq]
    abel
end Assembly
theorem claim_holds (h : TupleFacts.AllFacts)
    (hw : WellPosedness.WellPosed) : Claim := by
  intro D E n ψ
  have hq := (hw D E).1
  obtain ⟨hO, hL, -, -, -, -, -, -, -, -, -, -, -, hc, hD, -, hT, -⟩ := h D E n
  obtain ⟨hO₁, hL₁, hM₁, -⟩ := h D E 1
  exact ⟨liftIndependent_holds hq, liftsToSignedPerm_holds hq ψ,
    isIsometricEquiv_holds hq hO.1 hL ψ,
    preservesFunctionClasses_holds hq hO.1 hL hM₁ hc hD ψ,
    preservesTuples_holds hq hO₁.1 hL₁ hT ψ⟩
end TupleMapFacts
end YangMills.Construction.PeriodicSpace.Kind
