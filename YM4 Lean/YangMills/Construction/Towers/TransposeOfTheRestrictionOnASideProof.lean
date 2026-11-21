import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import YangMills.Construction.Towers.ProductOfTheBlockAverageWithItsTransposeOnTheSidesProof
import YangMills.Construction.Towers.TransposeOfTheRestrictionOnASide
import Mathlib
set_option autoImplicit false
open Function Set
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.PeriodicLattice (FourTorus)
open YangMills.Construction.Matrices (ComplexMatrix2)
namespace RestrictionTranspose
theorem mem_tracelessFunctions_iff {Z : Type} {f : Z → ComplexMatrix2} :
    f ∈ Matrices.GroupLieProduct.tracelessFunctions Z ↔ ∀ z, f z ∈ ComplexMatrix2.traceless := by
  simp [Matrices.GroupLieProduct.tracelessFunctions, Submodule.mem_pi]
theorem traceless_ext_of_halfTrace {A A' : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless)
    (hA' : A' ∈ ComplexMatrix2.traceless)
    (h : ∀ C ∈ ComplexMatrix2.traceless,
      ComplexMatrix2.halfTrace (A * C) = ComplexMatrix2.halfTrace (A' * C)) :
    A = A' := by apply _root_.YangMills.Construction.Tower.CubeAverageTranspose.eq_of_halfTrace_mul_eq <;> assumption
section Injection
variable {X Y : Type} {φ : Y → X}
def extendByZero (φ : Y → X) (g : Y → ComplexMatrix2) : X → ComplexMatrix2 :=
  Function.extend φ g 0
theorem extendByZero_apply_image (hφ : Injective φ) (g : Y → ComplexMatrix2) (y : Y) :
    _root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g (φ y) = g y :=
  hφ.extend_apply g 0 y
theorem extendByZero_apply_of_not_mem (g : Y → ComplexMatrix2) {x : X}
    (hx : ¬ ∃ y, φ y = x) : _root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g x = 0 :=
  Function.extend_apply' g (0 : X → ComplexMatrix2) x hx
theorem extendByZero_mem (hφ : Injective φ) {g : Y → ComplexMatrix2}
    (hg : g ∈ Matrices.GroupLieProduct.tracelessFunctions Y) :
    _root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g ∈ Matrices.GroupLieProduct.tracelessFunctions X := by
  refine mem_tracelessFunctions_iff.mpr fun x => ?_
  by_cases hx : ∃ y, φ y = x
  · obtain ⟨y, rfl⟩ := hx
    rw [extendByZero_apply_image hφ]
    exact mem_tracelessFunctions_iff.mp hg y
  · rw [extendByZero_apply_of_not_mem g hx]
    exact ComplexMatrix2.traceless.zero_mem
theorem traceFinsumPairing_extendByZero (hφ : Injective φ) (g : Y → ComplexMatrix2)
    (f : X → ComplexMatrix2) :
    traceFinsumPairing (_root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g) f = traceFinsumPairing g (f ∘ φ) := by
  have hsupp : Function.support
      (fun x => ComplexMatrix2.halfTrace (_root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g x * f x)) ⊆ Set.range φ := by
    intro x hx
    by_contra hr
    refine hx ?_
    have : _root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g x = 0 := extendByZero_apply_of_not_mem g (by simpa using hr)
    simp [this, ComplexMatrix2.fullTrace]
  simp only [traceFinsumPairing]
  rw [← Set.indicator_eq_self.mpr hsupp, ← finsum_mem_def, finsum_mem_range hφ]
  exact finsum_congr fun y => by simp [extendByZero_apply_image hφ]
theorem traceFinsumPairing_single [DecidableEq X] (u : X → ComplexMatrix2) (x : X)
    (C : ComplexMatrix2) :
    traceFinsumPairing u (Pi.single x C : X → ComplexMatrix2) =
      ComplexMatrix2.halfTrace (u x * C) := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.traceFinsumPairing_single <;> assumption
theorem ext_of_traceFinsumPairing {u v : X → ComplexMatrix2}
    (hu : u ∈ Matrices.GroupLieProduct.tracelessFunctions X)
    (hv : v ∈ Matrices.GroupLieProduct.tracelessFunctions X)
    (h : ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions X, HasFiniteSupp f →
      traceFinsumPairing u f = traceFinsumPairing v f) : u = v := by
  classical
  funext x
  refine traceless_ext_of_halfTrace (mem_tracelessFunctions_iff.mp hu x)
    (mem_tracelessFunctions_iff.mp hv x) fun C hC => ?_
  have hs : (Pi.single x C : X → ComplexMatrix2) ∈
      Matrices.GroupLieProduct.tracelessFunctions X := by
    refine mem_tracelessFunctions_iff.mpr fun z => ?_
    by_cases hz : z = x
    · subst hz
      simpa using hC
    · simp [Pi.single_eq_of_ne hz]
  have hsf : HasFiniteSupp (Pi.single x C : X → ComplexMatrix2) := by
    refine Set.Finite.subset (Set.finite_singleton x) fun z hz => ?_
    by_contra hne
    exact hz (Pi.single_eq_of_ne hne _)
  have c := h _ hs hsf
  rwa [traceFinsumPairing_single, traceFinsumPairing_single] at c
theorem extendByZero_add (hφ : Injective φ) (g g' : Y → ComplexMatrix2) :
    _root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ (g + g') = _root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g + _root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g' := by
  funext x
  by_cases hx : ∃ y, φ y = x
  · obtain ⟨y, rfl⟩ := hx
    simp only [Pi.add_apply, extendByZero_apply_image hφ]
  · simp only [Pi.add_apply, extendByZero_apply_of_not_mem _ hx, add_zero]
theorem extendByZero_smul (hφ : Injective φ) (c : ℂ) (g : Y → ComplexMatrix2) :
    _root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ (c • g) = c • _root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g := by
  funext x
  by_cases hx : ∃ y, φ y = x
  · obtain ⟨y, rfl⟩ := hx
    simp only [Pi.smul_apply, extendByZero_apply_image hφ]
  · simp only [Pi.smul_apply, extendByZero_apply_of_not_mem _ hx, smul_zero]
def extendByZeroLinear (hφ : Injective φ) :
    (pairedFunctions Y).complexSubmodule →ₗ[ℂ] (pairedFunctions X).complexSubmodule where
  toFun g := ⟨_root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g.1, extendByZero_mem hφ g.2⟩
  map_add' g g' := Subtype.ext (extendByZero_add hφ g.1 g'.1)
  map_smul' c g := Subtype.ext (extendByZero_smul hφ c g.1)
theorem transposeMap_of_comp_injective (hφ : Injective φ)
    (T : (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule)
    (hT : ∀ f, (T f).1 = f.1 ∘ φ) :
    PairedFunctionSpace.PreservesFiniteSupport T ∧
      PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) ∧
      ∀ g, (PairedFunctionSpace.transposeMap T g).1 = _root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g.1 := by
  classical
  have hfin : PairedFunctionSpace.PreservesFiniteSupport T := by
    intro f hf
    have hf' : (Function.support f.1).Finite := hf
    refine Set.Finite.subset (hf'.preimage hφ.injOn) fun y hy => ?_
    have hy' : (T f).1 y ≠ 0 := hy
    rw [hT] at hy'
    exact hy'
  have hE : PairedFunctionSpace.IsTransposeMap T (extendByZeroLinear hφ) := by
    intro g f _
    have e : (T f).1 = f.1 ∘ φ := hT f
    change traceFinsumPairing (_root_.YangMills.Construction.Tower.RestrictionTranspose.extendByZero φ g.1) f.1 = traceFinsumPairing g.1 (T f).1
    rw [e]
    exact traceFinsumPairing_extendByZero hφ g.1 f.1
  have hspec : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) :=
    Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap T) ⟨_, hE⟩
  refine ⟨hfin, hspec, fun g => ?_⟩
  exact ext_of_traceFinsumPairing (PairedFunctionSpace.transposeMap T g).2
    (extendByZeroLinear hφ g).2 fun f hf hfs =>
      (hspec g ⟨f, hf⟩ hfs).trans (hE g ⟨f, hf⟩ hfs).symm
end Injection
end RestrictionTranspose
open RestrictionTranspose in
theorem RestrictionTranspose.statement_holds : RestrictionTranspose.Statement := by
  intro L hL m k i l _ hil _ T hT
  have hL0 : 0 < L := by have := hL.2; omega
  have hd : PeriodicLattice.levelDepth k l ≤ PeriodicLattice.levelDepth k i := by
    simp only [PeriodicLattice.levelDepth]
    omega
  let φ : Vertex L m k l → Vertex L m k i :=
    fun y => PeriodicLattice.Site.toSublattice y (PeriodicLattice.levelDepth k i)
  have hcoe : ∀ y : Vertex L m k l, ((φ y : Vertex L m k i) : FourTorus L m) = y := fun y =>
    Classical.epsilon_spec (p := fun x : Vertex L m k i => (x : FourTorus L m) = y)
      ⟨⟨y, PeriodicLattice.sublattice_mono hL0 m hd y.2⟩, rfl⟩
  have hφ : Injective φ := fun y y' e =>
    Subtype.ext ((hcoe y).symm.trans ((congrArg Subtype.val e).trans (hcoe y')))
  obtain ⟨h₁, h₂, h₃⟩ := transposeMap_of_comp_injective hφ T fun f => hT f
  refine ⟨h₁, h₂, fun g x y e => ?_, fun g x hx => ?_, fun g => funext fun y => ?_⟩
  · have hx : φ y = x := Subtype.ext ((hcoe y).trans e)
    subst hx
    rw [h₃]
    exact extendByZero_apply_image hφ g.1 y
  · rw [h₃]
    exact extendByZero_apply_of_not_mem g.1 fun ⟨y, hy⟩ =>
      hx ⟨y, (hcoe y).symm.trans (congrArg Subtype.val hy)⟩
  · change (PairedFunctionSpace.transposeMap T g).1 (φ y) = g.1 y
    rw [h₃]
    exact extendByZero_apply_image hφ g.1 y
end YangMills.Construction.Tower
end
