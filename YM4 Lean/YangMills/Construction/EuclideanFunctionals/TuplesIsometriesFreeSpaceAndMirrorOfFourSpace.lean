import YangMills.Construction.ReflectionPositivity.CentredObservableAndFunctionals
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.TorusMetric
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
abbrev R4 : Type := Fin 4 → ℝ
structure SharpScale where
  M : ℝ
  one_le : 1 ≤ M
def SharpScale.sharpNorm {E : Type*} [NormedAddCommGroup E] (c : SharpScale) (f : R4 → E) : ℝ :=
  TestFunctions.sharpNormR4 c.M f
def defaultMirrorData : MirrorData where
  L := 13
  isAdmissible := ⟨by decide, le_rfl⟩
  K := 1
  m := 1
  β := 1
  β_pos := one_pos
abbrev FnList : Type := List (R4 → ℝ)
abbrev sepN (n : ℕ) : Set FnList :=
  Ambient.separatedN defaultMirrorData Ambient.euclidean n
abbrev sepAll : Set FnList := Ambient.separatedAll defaultMirrorData Ambient.euclidean
abbrev sepIn (O : Set R4) : Set FnList :=
  Ambient.separatedWithin defaultMirrorData Ambient.euclidean O
abbrev C1c (𝕜 : Type*) [RCLike 𝕜] : Set (R4 → 𝕜) :=
  Ambient.compactC1 defaultMirrorData 𝕜 Ambient.euclidean
abbrev supp {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) : Set R4 :=
  Ambient.closedSupport defaultMirrorData Ambient.euclidean f
abbrev listAppend (X Y : FnList) : FnList :=
  Ambient.append (D := defaultMirrorData) (E := Ambient.euclidean) X Y
theorem isSeparatedList_of_mem_sepAll {X : FnList} (hX : X ∈ sepAll) :
    Ambient.IsSeparatedList defaultMirrorData Ambient.euclidean X := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hX
  exact hn.2
theorem listAppend_mem_sepIn {O O' : Set R4} (h : Disjoint O O') {X Y : FnList}
    (hX : X ∈ sepIn O) (hY : Y ∈ sepIn O') : listAppend X Y ∈ sepIn (O ∪ O') := by
  have sX := isSeparatedList_of_mem_sepAll hX.1
  have sY := isSeparatedList_of_mem_sepAll hY.1
  refine ⟨Set.mem_iUnion.2 ⟨_, rfl, ?_, ?_⟩, ?_⟩
  · intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · exact sX.1 f hf
    · exact sY.1 f hf
  · exact List.pairwise_append.2 ⟨sX.2, sY.2, fun f hf g hg => h.mono (hX.2 f hf) (hY.2 g hg)⟩
  · intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · exact (hX.2 f hf).trans Set.subset_union_left
    · exact (hY.2 f hf).trans Set.subset_union_right
abbrev FreeSep : Type := sepAll →₀ ℂ
def toFree (X : FnList) : FreeSep :=
  open Classical in if h : X ∈ sepAll then Finsupp.single ⟨X, h⟩ 1 else 0
theorem toFree_of_mem {X : FnList} (h : X ∈ sepAll) : toFree X = Finsupp.single ⟨X, h⟩ 1 := by
  simp [toFree, h]
def freeBasis : Module.Basis sepAll ℂ FreeSep := Finsupp.basisSingleOne
theorem freeBasis_apply (X : sepAll) : freeBasis X = toFree X.1 := by
  rw [toFree_of_mem X.2]
  exact congrFun Finsupp.coe_basisSingleOne X
def freeSpanIn (O : Set R4) : Submodule ℂ FreeSep := Submodule.span ℂ (toFree '' sepIn O)
def freeConj (F : FreeSep) : FreeSep := F.mapRange (starRingEnd ℂ) (map_zero _)
def liftLin {V : Type*} [AddCommMonoid V] [Module ℂ V] (φ : sepAll → V) :
    FreeSep →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ φ
theorem liftLin_toFree {V : Type*} [AddCommMonoid V] [Module ℂ V] (φ : sepAll → V)
    (X : sepAll) : liftLin φ (toFree X.1) = φ X := by
  rw [toFree_of_mem X.2]
  simp [liftLin]
def liftReal (φ : sepAll → ℝ) : FreeSep →ₗ[ℂ] ℂ := liftLin fun X => (φ X : ℂ)
def freeMul : FreeSep →ₗ[ℂ] FreeSep →ₗ[ℂ] FreeSep :=
  liftLin fun X => liftLin fun Y => toFree (listAppend X.1 Y.1)
theorem freeMul_apply (F F' : FreeSep) :
    freeMul F F' = F.sum fun X z => F'.sum fun Y z' => (z * z') • toFree (listAppend X.1 Y.1) := by
  simp only [freeMul, liftLin, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum, mul_smul]
structure EuclidMotion where
  lin : R4 →ₗ[ℝ] R4
  offset : R4
  lin_norm : ∀ x, euclidNormVec (lin x) = euclidNormVec x
namespace EuclidMotion
instance : CoeFun EuclidMotion fun _ => R4 → R4 := ⟨fun r x => r.lin x + r.offset⟩
theorem apply_def (r : EuclidMotion) (x : R4) : r x = r.lin x + r.offset := rfl
theorem ext_of_apply {r r' : EuclidMotion} (h : ∀ x, r x = r' x) : r = r' := by
  have hs : r.offset = r'.offset := by simpa [apply_def] using h 0
  have hl : r.lin = r'.lin := LinearMap.ext fun x => by
    have := h x
    rw [apply_def, apply_def, hs] at this
    exact add_right_cancel this
  cases r
  cases r'
  simp_all
theorem lin_injective (r : EuclidMotion) : Function.Injective r.lin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h := r.lin_norm x
  rw [hx] at h
  have h0 : euclidNormVec (0 : R4) = 0 := by simp [euclidNormVec]
  rw [h0] at h
  have hsum : ∑ μ, x μ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun μ _ => sq_nonneg (x μ))).1 h.symm
  funext μ
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => sq_nonneg (x μ))).1 hsum μ (Finset.mem_univ _)
  simpa using this
def linEquiv (r : EuclidMotion) : R4 ≃ₗ[ℝ] R4 :=
  LinearEquiv.ofInjectiveEndo r.lin r.lin_injective
instance : Mul EuclidMotion where
  mul r r' := ⟨r.lin ∘ₗ r'.lin, r.lin r'.offset + r.offset, fun x => by
    simp [r.lin_norm, r'.lin_norm]⟩
instance : One EuclidMotion := ⟨⟨LinearMap.id, 0, fun _ => rfl⟩⟩
instance : Inv EuclidMotion where
  inv r := ⟨r.linEquiv.symm.toLinearMap, -r.linEquiv.symm r.offset, fun x => by
    have h := r.lin_norm (r.linEquiv.symm x)
    have h' : r.lin (r.linEquiv.symm x) = x := r.linEquiv.apply_symm_apply x
    rw [h'] at h
    exact h.symm⟩
theorem mul_apply (r r' : EuclidMotion) (x : R4) : (r * r') x = r (r' x) := by
  change r.lin (r'.lin x) + (r.lin r'.offset + r.offset) =
    r.lin (r'.lin x + r'.offset) + r.offset
  rw [map_add, add_assoc]
theorem one_apply (x : R4) : (1 : EuclidMotion) x = x := add_zero x
theorem inv_apply_apply (r : EuclidMotion) (x : R4) : r⁻¹ (r x) = x := by
  change r.linEquiv.symm (r.lin x + r.offset) + -r.linEquiv.symm r.offset = x
  rw [map_add, add_neg_cancel_right]
  exact r.linEquiv.symm_apply_apply x
instance : Group EuclidMotion :=
  Group.ofLeftAxioms
    (fun a b c => ext_of_apply fun x => by simp only [mul_apply])
    (fun a => ext_of_apply fun x => by rw [mul_apply, one_apply])
    (fun a => ext_of_apply fun x => by rw [mul_apply, inv_apply_apply, one_apply])
theorem apply_inv_apply (r : EuclidMotion) (x : R4) : r (r⁻¹ x) = x := by
  rw [← mul_apply, mul_inv_cancel, one_apply]
def toPerm (r : EuclidMotion) : R4 ≃ R4 :=
  ⟨fun x => r x, fun x => r⁻¹ x, r.inv_apply_apply, r.apply_inv_apply⟩
theorem euclidNormVec_sub (r : EuclidMotion) (x y : R4) :
    euclidNormVec (r x - r y) = euclidNormVec (x - y) := by
  rw [apply_def, apply_def, add_sub_add_right_eq_sub, ← map_sub, r.lin_norm]
def transl (v : R4) : EuclidMotion := ⟨LinearMap.id, v, fun _ => rfl⟩
theorem transl_apply (v x : R4) : transl v x = x + v := rfl
def actFn {α : Type*} (r : EuclidMotion) (f : R4 → α) : R4 → α := fun x => f (r⁻¹ x)
def actList (r : EuclidMotion) (X : FnList) : FnList := X.map r.actFn
def actFree (r : EuclidMotion) : FreeSep →ₗ[ℂ] FreeSep :=
  liftLin fun X => toFree (r.actList X.1)
theorem actFn_transl {α : Type*} (v : R4) (f : R4 → α) (x : R4) :
    (transl v).actFn f x = f (x - v) := by
  have h : (transl v)⁻¹ x = x - v := by
    have h' := inv_apply_apply (transl v) (x - v)
    rw [transl_apply, sub_add_cancel] at h'
    exact h'
  simp [actFn, h]
end EuclidMotion
abbrev ConnFamily : Type := Ambient.ConnectedFamily defaultMirrorData Ambient.euclidean
abbrev centeredFn (S : ConnFamily) : sepAll → ℝ := S.centeredFunctional
def centeredFnFree (S : ConnFamily) : FreeSep →ₗ[ℂ] ℂ := liftReal (centeredFn S)
section ComplexComponents
variable {n : ℕ} (h : Fin n → R4 → ℂ)
def nonrealIdx : Finset (Fin n) :=
  open Classical in Finset.univ.filter fun k => ¬∀ x, (h k x).im = 0
def imagCount (ε : nonrealIdx h → Fin 2) : ℕ := ∑ k, (ε k : ℕ)
def realPartComponent (ε : nonrealIdx h → Fin 2) (k : Fin n) : R4 → ℝ :=
  open Classical in
  if hk : k ∈ nonrealIdx h then
    if ε ⟨k, hk⟩ = 0 then fun x => (h k x).re else fun x => (h k x).im
  else fun x => (h k x).re
def complexList : FreeSep :=
  ∑ ε : nonrealIdx h → Fin 2, (Complex.I ^ imagCount h ε) • toFree (List.ofFn (realPartComponent h ε))
end ComplexComponents
theorem complexList_ofReal {n : ℕ} (f : Fin n → R4 → ℝ) :
    complexList (fun k x => (f k x : ℂ)) = toFree (List.ofFn f) := by
  have hI : nonrealIdx (fun k x => (f k x : ℂ)) = ∅ := by
    simp [nonrealIdx]
  have hE : ∀ ε, realPartComponent (fun k x => (f k x : ℂ)) ε = f := by
    intro ε
    funext k x
    simp [realPartComponent, hI]
  have : IsEmpty (nonrealIdx (fun k x => (f k x : ℂ))) := by
    rw [hI]
    infer_instance
  have hs : ∀ ε, imagCount (fun k x => (f k x : ℂ)) ε = 0 := fun ε => Fintype.sum_empty _
  rw [complexList, Fintype.sum_unique, hs, hE, pow_zero, one_smul]
abbrev timeVec : R4 := PeriodicLattice.coordVec 3
def spatialVecs : Set R4 := {v | v 3 = 0}
def upperHalf : Set R4 := {x | 0 < x 3}
def timeFlipLin : R4 →ₗ[ℝ] R4 where
  toFun x := x - (2 * x 3) • timeVec
  map_add' x y := by
    funext μ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' c x := by
    funext μ
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, RingHom.id_apply]
    ring
def timeFlip : EuclidMotion where
  lin := timeFlipLin
  offset := 0
  lin_norm x := by
    simp only [euclidNormVec, Fin.sum_univ_four, timeFlipLin, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, PeriodicLattice.coordVec]
    congr 1
    simp
    ring
theorem timeFlip_apply (x : R4) : timeFlip x = x - (2 * x 3) • timeVec := add_zero _
def frameLin (w : PeriodicLattice.SignedFrame) : R4 →ₗ[ℝ] R4 where
  toFun := w.actOnVector
  map_add' x y := by
    funext μ
    simp [PeriodicLattice.SignedFrame.actOnVector, mul_add]
  map_smul' c x := by
    funext μ
    simp only [PeriodicLattice.SignedFrame.actOnVector, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem intUnit_mul_self (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp
def ofSignedFrame (w : PeriodicLattice.SignedFrame) : EuclidMotion where
  lin := frameLin w
  offset := 0
  lin_norm x := by
    simp only [euclidNormVec]
    congr 1
    have h : ∀ μ, (frameLin w x μ) ^ 2 = x (w.1 μ) ^ 2 := by
      intro μ
      change (((w.2 μ : ℤ) : ℝ) * x (w.1 μ)) ^ 2 = _
      rw [mul_pow, sq ((w.2 μ : ℤ) : ℝ), intUnit_mul_self, one_mul]
    simp only [h]
    exact Equiv.sum_comp w.1 fun μ => x μ ^ 2
theorem ofSignedFrame_apply (w : PeriodicLattice.SignedFrame) (x : R4) :
    ofSignedFrame w x = w.actOnVector x :=
  add_zero _
def hyperoctahedral : Subgroup EuclidMotion where
  carrier := Set.range ofSignedFrame
  mul_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    refine ⟨(w'.1 * w.1, fun μ => w.2 μ * w'.2 (w.1 μ)), EuclidMotion.ext_of_apply fun x => ?_⟩
    rw [EuclidMotion.mul_apply, ofSignedFrame_apply, ofSignedFrame_apply, ofSignedFrame_apply]
    funext μ
    simp [PeriodicLattice.SignedFrame.actOnVector, mul_assoc]
  one_mem' := by
    refine ⟨(1, fun _ => 1), EuclidMotion.ext_of_apply fun x => ?_⟩
    rw [ofSignedFrame_apply, EuclidMotion.one_apply]
    funext μ
    simp [PeriodicLattice.SignedFrame.actOnVector]
  inv_mem' := by
    rintro _ ⟨w, rfl⟩
    refine ⟨(w.1⁻¹, fun ν => w.2 (w.1⁻¹ ν)), ?_⟩
    refine (inv_eq_of_mul_eq_one_left (EuclidMotion.ext_of_apply fun x => ?_)).symm
    rw [EuclidMotion.mul_apply, ofSignedFrame_apply, ofSignedFrame_apply, EuclidMotion.one_apply]
    funext ν
    simp only [PeriodicLattice.SignedFrame.actOnVector]
    rw [← mul_assoc, intUnit_mul_self, one_mul]
    simp
def timeStabilizer : Subgroup EuclidMotion where
  carrier := {w | w ∈ hyperoctahedral ∧ w timeVec = timeVec}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨hyperoctahedral.mul_mem ha hb, by rw [EuclidMotion.mul_apply, hb', ha']⟩
  one_mem' := ⟨hyperoctahedral.one_mem, EuclidMotion.one_apply _⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨hyperoctahedral.inv_mem ha, ?_⟩
    conv_lhs => rw [← ha']
    exact EuclidMotion.inv_apply_apply a _
end YangMills.Construction.EuclideanFunctionals
