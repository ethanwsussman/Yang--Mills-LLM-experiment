import YangMills.Construction.Towers.ProductOfTheBlockAverageWithItsTransposeOnTheSidesProof
import YangMills.Construction.Towers.TransposeOfTheRestrictionOnTheWhole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open Matrices
open Set
namespace Tower.FullSpace.RestrictionTranspose
variable {L k i l : ℕ}
theorem coe_mem_latticeSubgroup_of_le (hL : 0 < L) (h : i ≤ l) (y : FullSpace.Vertex L k l) :
    (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k i) := by
  obtain ⟨m, hm⟩ := y.2
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hmesh : meshAt L k l = (L : ℝ) ^ (l - i) * meshAt L k i := by
    unfold meshAt
    rw [← zpow_natCast, ← zpow_add₀ hLne]
    congr 1
    omega
  refine ⟨fun μ => m μ * (L : ℤ) ^ (l - i), fun μ => ?_⟩
  rw [hm μ, hmesh]
  push_cast
  ring
def toFinerVertex (hL : 0 < L) (h : i ≤ l) (y : FullSpace.Vertex L k l) : FullSpace.Vertex L k i :=
  ⟨y.1, coe_mem_latticeSubgroup_of_le hL h y⟩
theorem toFinerVertex_injective (hL : 0 < L) (h : i ≤ l) :
    Function.Injective (toFinerVertex (k := k) hL h) := fun _ _ e =>
  Subtype.ext (congrArg (fun s : FullSpace.Vertex L k i => (s : AmbientSpace)) e)
theorem toFiner_eq_toFinerVertex (hL : 0 < L) (h : i ≤ l) (y : FullSpace.Vertex L k l) :
    toFiner (meshAt L k i) y = toFinerVertex hL h y := by
  apply Subtype.ext
  exact Classical.epsilon_spec
    (p := fun x : InfiniteLattice.LatticePoint (meshAt L k i) => (x : AmbientSpace) = y)
    ⟨toFinerVertex hL h y, rfl⟩
def extendByZero (g : FullSpace.Vertex L k l → ComplexMatrix2) :
    FullSpace.Vertex L k i → ComplexMatrix2 :=
  open Classical in
  fun x => if h : ∃ y : FullSpace.Vertex L k l, (y : AmbientSpace) = x then g h.choose else 0
theorem extendByZero_apply_of_coe_eq (g : FullSpace.Vertex L k l → ComplexMatrix2)
    (x : FullSpace.Vertex L k i) (y : FullSpace.Vertex L k l) (hy : (y : AmbientSpace) = x) :
    _root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero g x = g y := by
  have h : ∃ y : FullSpace.Vertex L k l, (y : AmbientSpace) = x := ⟨y, hy⟩
  have e : h.choose = y := Subtype.ext (h.choose_spec.trans hy.symm)
  simp only [_root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero, dif_pos h, e]
theorem extendByZero_apply_of_not_exists (g : FullSpace.Vertex L k l → ComplexMatrix2)
    (x : FullSpace.Vertex L k i) (h : ¬ ∃ y : FullSpace.Vertex L k l, (y : AmbientSpace) = x) :
    _root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero g x = 0 := by
  simp only [_root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero, dif_neg h]
theorem extendByZero_mem_traceless (g : FullSpace.Vertex L k l → ComplexMatrix2)
    (hg : ∀ y, g y ∈ ComplexMatrix2.traceless) (x : FullSpace.Vertex L k i) :
    _root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero g x ∈ ComplexMatrix2.traceless := by
  by_cases h : ∃ y : FullSpace.Vertex L k l, (y : AmbientSpace) = x
  · obtain ⟨y, hy⟩ := h
    rw [extendByZero_apply_of_coe_eq g x y hy]
    exact hg y
  · rw [extendByZero_apply_of_not_exists g x h]
    exact ComplexMatrix2.traceless.zero_mem
theorem extendByZero_add (g g' : FullSpace.Vertex L k l → ComplexMatrix2) :
    (_root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero (g + g') : FullSpace.Vertex L k i → ComplexMatrix2) =
      _root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero g + _root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero g' := by
  funext x
  by_cases h : ∃ y : FullSpace.Vertex L k l, (y : AmbientSpace) = x
  · obtain ⟨y, hy⟩ := h
    simp only [Pi.add_apply, extendByZero_apply_of_coe_eq _ x y hy]
  · simp only [Pi.add_apply, extendByZero_apply_of_not_exists _ x h, add_zero]
theorem extendByZero_smul (c : ℂ) (g : FullSpace.Vertex L k l → ComplexMatrix2) :
    (_root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero (c • g) : FullSpace.Vertex L k i → ComplexMatrix2) = c • _root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero g := by
  funext x
  by_cases h : ∃ y : FullSpace.Vertex L k l, (y : AmbientSpace) = x
  · obtain ⟨y, hy⟩ := h
    simp only [Pi.smul_apply, extendByZero_apply_of_coe_eq _ x y hy]
  · simp only [Pi.smul_apply, extendByZero_apply_of_not_exists _ x h, smul_zero]
def extendByZeroLinear (L k i l : ℕ) :
    (pairedFunctions (FullSpace.Vertex L k l)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (FullSpace.Vertex L k i)).complexSubmodule where
  toFun g := ⟨_root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero g.1, fun x _ =>
    extendByZero_mem_traceless g.1 (fun y => g.2 y (mem_univ _)) x⟩
  map_add' g g' := Subtype.ext (extendByZero_add g.1 g'.1)
  map_smul' c g := Subtype.ext (extendByZero_smul c g.1)
theorem pair_extendByZero (hL : 0 < L) (h : i ≤ l) (g : FullSpace.Vertex L k l → ComplexMatrix2)
    (f : FullSpace.Vertex L k i → ComplexMatrix2) :
    traceFinsumPairing (_root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero g) f =
      traceFinsumPairing g (fun y => f (toFinerVertex hL h y)) := by
  unfold traceFinsumPairing
  set F : FullSpace.Vertex L k i → ℂ :=
    fun x => ComplexMatrix2.halfTrace (_root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero g x * f x) with hF
  have hsupp : Function.support F ⊆ range (toFinerVertex (k := k) hL h) := by
    intro x hx
    by_contra hr
    apply hx
    have hno : ¬ ∃ y : FullSpace.Vertex L k l, (y : AmbientSpace) = x := by
      rintro ⟨y, hy⟩
      exact hr ⟨y, Subtype.ext hy⟩
    simp [hF, extendByZero_apply_of_not_exists g x hno, ComplexMatrix2.halfTrace,
      ComplexMatrix2.fullTrace]
  have hsum : ∑ᶠ x ∈ range (toFinerVertex (k := k) hL h), F x = ∑ᶠ x, F x := by
    rw [finsum_mem_def, indicator_eq_self.2 hsupp]
  rw [← hsum, finsum_mem_range (toFinerVertex_injective hL h)]
  refine finsum_congr fun y => ?_
  simp only [hF, extendByZero_apply_of_coe_eq g (toFinerVertex hL h y) y rfl]
theorem eq_of_halfTrace_mul_eq {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless)
    (e : ∀ Z ∈ ComplexMatrix2.traceless,
      ComplexMatrix2.halfTrace (X * Z) = ComplexMatrix2.halfTrace (Y * Z)) : X = Y := by apply _root_.YangMills.Construction.Tower.CubeAverageTranspose.eq_of_halfTrace_mul_eq <;> assumption
open Classical in
def pointMass {ι : Type} (x : ι) (Z : ComplexMatrix2) : ι → ComplexMatrix2 :=
  fun y => if y = x then Z else 0
theorem pointMass_mem_traceless {ι : Type} (x y : ι) {Z : ComplexMatrix2}
    (hZ : Z ∈ ComplexMatrix2.traceless) : pointMass x Z y ∈ ComplexMatrix2.traceless := by
  by_cases h : y = x
  · simpa [pointMass, h] using hZ
  · simp only [pointMass, if_neg h]
    exact ComplexMatrix2.traceless.zero_mem
theorem pair_pointMass {ι : Type} (h : ι → ComplexMatrix2) (x : ι) (Z : ComplexMatrix2) :
    traceFinsumPairing h (pointMass x Z) = ComplexMatrix2.halfTrace (h x * Z) := by
  unfold traceFinsumPairing
  rw [finsum_eq_single _ x]
  · simp [pointMass]
  · intro y hy
    simp [pointMass, hy, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
theorem hasFiniteSupp_pointMass {ι : Type} (x : ι) (Z : ComplexMatrix2) :
    HasFiniteSupp (pointMass x Z) := by
  refine (finite_singleton x).subset fun y hy => ?_
  by_contra hne
  exact hy (by simp [pointMass, show y ≠ x from hne])
theorem mainStatement_holds : MainStatement := by
  intro L hL k i l hil _ T hT
  have hL0 : 0 < L := by have := hL.2; omega
  have hTf : ∀ (f : (pairedFunctions (FullSpace.Vertex L k i)).complexSubmodule)
      (y : FullSpace.Vertex L k l), (T f).1 y = f.1 (toFinerVertex hL0 hil y) := fun f y =>
    (congrFun (hT f) y).trans (congrArg f.1 (toFiner_eq_toFinerVertex hL0 hil y))
  have hE : PairedFunctionSpace.IsTransposeMap T (extendByZeroLinear L k i l) := fun g f _ =>
    (pair_extendByZero hL0 hil g.1 f.1).trans
      (congrArg (traceFinsumPairing (ι := FullSpace.Vertex L k l) g.1)
        (funext fun y => (hTf f y).symm))
  have hspec : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) :=
    Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap T) ⟨_, hE⟩
  have hval : ∀ (g : (pairedFunctions (FullSpace.Vertex L k l)).complexSubmodule)
      (x : FullSpace.Vertex L k i),
      (PairedFunctionSpace.transposeMap T g).1 x = _root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.extendByZero g.1 x := by
    intro g x
    refine eq_of_halfTrace_mul_eq ((PairedFunctionSpace.transposeMap T g).2 x (mem_univ _))
      ((extendByZeroLinear L k i l g).2 x (mem_univ _)) fun Z hZ => ?_
    let p : (pairedFunctions (FullSpace.Vertex L k i)).complexSubmodule :=
      ⟨pointMass x Z, fun y _ => pointMass_mem_traceless x y hZ⟩
    have hp : (pairedFunctions (FullSpace.Vertex L k i)).IsFinitelySupported p :=
      hasFiniteSupp_pointMass x Z
    have e₃ : traceFinsumPairing (ι := FullSpace.Vertex L k i)
          (PairedFunctionSpace.transposeMap T g).1 (pointMass x Z) =
        traceFinsumPairing (ι := FullSpace.Vertex L k i)
          (extendByZeroLinear L k i l g).1 (pointMass x Z) :=
      (hspec g p hp).trans (hE g p hp).symm
    exact (pair_pointMass _ x Z).symm.trans (e₃.trans (pair_pointMass _ x Z))
  refine ⟨?_, hspec, ?_, ?_, ?_⟩
  · intro f hf
    have hf' : (Function.support (f.1 : FullSpace.Vertex L k i → ComplexMatrix2)).Finite := hf
    refine (hf'.preimage (toFinerVertex_injective hL0 hil).injOn).subset fun y hy => ?_
    show f.1 (toFinerVertex hL0 hil y) ≠ 0
    exact (hTf f y) ▸ hy
  · intro g x y hy
    exact (hval g x).trans (extendByZero_apply_of_coe_eq g.1 x y hy)
  · intro g x hx
    exact (hval g x).trans (extendByZero_apply_of_not_exists g.1 x hx)
  · intro g
    funext y
    have e : toFiner (meshAt L k i) y = toFinerVertex hL0 hil y :=
      toFiner_eq_toFinerVertex hL0 hil y
    exact (congrArg (PairedFunctionSpace.transposeMap T g).1 e).trans
      ((hval g _).trans (extendByZero_apply_of_coe_eq g.1 _ y rfl))
end Tower.FullSpace.RestrictionTranspose
end YangMills.Construction
end
