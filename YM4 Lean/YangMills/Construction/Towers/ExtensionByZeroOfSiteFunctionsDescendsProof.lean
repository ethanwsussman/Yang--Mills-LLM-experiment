import YangMills.Construction.Towers.BlockAverageTimesItsTransposeAtTheSideInfinityProof
import YangMills.Construction.Towers.ExtensionByZeroOfSiteFunctionsDescends
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.ProductOfTheBlockAverageWithItsTransposeOnTheSidesProof
import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.VertexZeroExtension
open YangMills.Construction.LocalKernels.Periodisation YangMills.Construction.Tower
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators (KernelMatrix applyKernel)
def relKernel {N N' : Type} (R : N' → N → Prop) : KernelMatrix N N' :=
  open Classical in fun a' a => if R a' a then 1 else 0
theorem applyKernel_relKernel_of_unique {N N' : Type} (R : N' → N → Prop) (f : N → ℂ) (a' : N')
    (a₀ : N) (h₀ : R a' a₀) (h : ∀ a, R a' a → a = a₀) :
    applyKernel (relKernel R) f a' = f a₀ := by
  classical
  unfold applyKernel
  rw [tsum_eq_single a₀]
  · simp [relKernel, h₀]
  · intro a ha
    have hr : ¬ R a' a := fun hr => ha (h a hr)
    simp [relKernel, hr]
theorem applyKernel_relKernel_of_none {N N' : Type} (R : N' → N → Prop) (f : N → ℂ) (a' : N')
    (h : ∀ a, ¬ R a' a) : applyKernel (relKernel R) f a' = 0 := by
  classical
  simp [applyKernel, relKernel, h]
theorem finsum_eq_of_zero_off_range {α β M : Type*} [AddCommMonoid M] (u : α → β)
    (hu : Function.Injective u) (F : β → M) (h : ∀ x, x ∉ range u → F x = 0) :
    ∑ᶠ x, F x = ∑ᶠ y, F (u y) := by
  rw [← finsum_mem_range hu, finsum_mem_def]
  congr 1
  funext x
  by_cases hx : x ∈ range u
  · simp [hx]
  · simp [hx, h x hx]
theorem traceless_ext (A B : ComplexMatrix2) (hA : A ∈ ComplexMatrix2.traceless)
    (hB : B ∈ ComplexMatrix2.traceless)
    (h : ∀ t ∈ ComplexMatrix2.traceless,
      ComplexMatrix2.halfTrace (A * t) = ComplexMatrix2.halfTrace (B * t)) :
    A = B := by apply _root_.YangMills.Construction.Tower.CubeAverageTranspose.eq_of_halfTrace_mul_eq <;> assumption
theorem mem_tracelessFunctions {σ : Type} (f : σ → ComplexMatrix2) :
    f ∈ GroupLieProduct.tracelessFunctions σ ↔ ∀ i, f i ∈ ComplexMatrix2.traceless := by
  simp [GroupLieProduct.tracelessFunctions, Submodule.mem_pi]
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
section Vertices
variable {L n k : ℕ}
theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
def fullLift (hL : 0 < L) (y : FullSpace.Vertex L k k) : FullSpace.Vertex L k 0 := by
  refine ⟨y.1, ?_⟩
  obtain ⟨c, hc⟩ := y.2
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine ⟨fun μ => c μ * (L : ℤ) ^ k, fun μ => ?_⟩
  rw [hc μ, meshAt_self]
  simp only [meshAt]
  push_cast
  rw [mul_one, mul_assoc]
  have : (L : ℝ) ^ k * (L : ℝ) ^ ((0 : ℤ) - (k : ℤ)) = 1 := by
    simp [zpow_neg, hL']
  rw [this, mul_one]
def periodicLift (hL : 0 < L) (Y : Vertex L n k k) : Vertex L n k 0 :=
  ⟨Y.1, PeriodicLattice.sublattice_mono hL n (by simp [PeriodicLattice.levelDepth]) Y.2⟩
theorem periodicLift_injective (hL : 0 < L) :
    Function.Injective (periodicLift (n := n) (k := k) hL) := by
  intro Y Y' h
  exact Subtype.ext (congrArg (fun x : Vertex L n k 0 => x.1) h)
theorem projVertex_surjective (j : ℕ) (Y : Vertex L n k j) :
    ∃ y : FullSpace.Vertex L k j, FullSpace.projVertex L n k j y = Y := by
  obtain ⟨c, hc⟩ := Y.2
  refine ⟨⟨fun μ => (c μ : ℝ) * meshAt L k j, c, fun μ => rfl⟩, Subtype.ext ?_⟩
  funext μ
  simp [FullSpace.projVertex, TorusMetric.torusProj, hc μ, meshSize_levelDepth]
theorem exists_full_of_proj (x : FullSpace.Vertex L k 0) (Y : Vertex L n k k)
    (h : Y.1 = (FullSpace.projVertex L n k 0 x).1) : ∃ y : FullSpace.Vertex L k k, y.1 = x.1 := by
  obtain ⟨c, hc⟩ := Y.2
  have key : ∀ μ, ∃ z : ℤ, x.1 μ = (z : ℝ) := by
    intro μ
    have h₁ := congrFun h μ
    rw [hc μ] at h₁
    simp only [FullSpace.projVertex, TorusMetric.torusProj] at h₁
    have h₂ : ((c μ : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) : ℝ) =
        (c μ : ℝ) := by
      rw [meshSize_levelDepth, meshAt_self, mul_one]
    rw [h₂] at h₁
    obtain ⟨w, hw⟩ :=
      AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp h₁.symm)
    refine ⟨c μ + w * (2 * (L : ℤ) ^ n), ?_⟩
    simp only [PeriodicLattice.torusSide, zsmul_eq_mul] at hw
    push_cast
    linarith
  choose z hz using key
  exact ⟨⟨x.1, z, fun μ => by rw [hz μ, meshAt_self, mul_one]⟩, rfl⟩
end Vertices
section Pairs
variable (L n k : ℕ)
abbrev FullPair (j : ℕ) (h : j ≤ k) : Type := Idx L (CellClass.vertexClass k j h).colourPairs
abbrev PeriodicPair (j : ℕ) (h : j ≤ k) : Type :=
  (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n
variable {L n k}
def pairColour {j : ℕ} {h : j ≤ k} (p : FullPair L k j h) : Fin 3 := p.2.1
def pairVertex {j : ℕ} {h : j ≤ k} (p : FullPair L k j h) : FullSpace.Vertex L k j := p.2.2
def periodicColour {j : ℕ} {h : j ≤ k} (q : PeriodicPair L n k j h) : Fin 3 := q.2.1.1
def periodicVertex {j : ℕ} {h : j ≤ k} (q : PeriodicPair L n k j h) : Vertex L n k j := q.2.1.2
def mkFullPair {j : ℕ} {h : j ≤ k} (a : Fin 3) (y : FullSpace.Vertex L k j) : FullPair L k j h :=
  ⟨(), (a, y)⟩
theorem fullPair_ext {j : ℕ} {h : j ≤ k} (p : FullPair L k j h) (a : Fin 3)
    (y : FullSpace.Vertex L k j) (ha : pairColour p = a) (hy : (pairVertex p).1 = y.1) :
    p = mkFullPair a y := by
  obtain ⟨⟨⟩, b, z⟩ := p
  have h₁ : b = a := ha
  have h₂ : z = y := Subtype.ext hy
  subst h₁ h₂
  rfl
theorem periodicPair_ext {j : ℕ} {h : j ≤ k} (q q' : PeriodicPair L n k j h)
    (ha : periodicColour q = periodicColour q')
    (hy : (periodicVertex q).1 = (periodicVertex q').1) : q = q' := by
  obtain ⟨⟨⟩, ⟨b, z⟩, hz⟩ := q
  obtain ⟨⟨⟩, ⟨b', z'⟩, hz'⟩ := q'
  have h₁ : b = b' := ha
  have h₂ : z = z' := Subtype.ext hy
  subst h₁ h₂
  rfl
def mkPeriodicPair {j : ℕ} {h : j ≤ k} (a : Fin 3) (Y : Vertex L n k j) : PeriodicPair L n k j h :=
  (CellClass.vertexClass k j h).colourPairs.proj L n
    (mkFullPair a (Classical.choose (projVertex_surjective j Y)))
theorem periodicColour_mk {j : ℕ} {h : j ≤ k} (a : Fin 3) (Y : Vertex L n k j) :
    periodicColour (mkPeriodicPair (h := h) a Y) = a := rfl
theorem periodicVertex_mk {j : ℕ} {h : j ≤ k} (a : Fin 3) (Y : Vertex L n k j) :
    periodicVertex (mkPeriodicPair (h := h) a Y) = Y :=
  Classical.choose_spec (projVertex_surjective j Y)
theorem periodicVertex_proj {j : ℕ} {h : j ≤ k} (p : FullPair L k j h) :
    periodicVertex ((CellClass.vertexClass k j h).colourPairs.proj L n p) =
      FullSpace.projVertex L n k j (pairVertex p) := rfl
def fullRel (p' : FullPair L k 0 (Nat.zero_le k)) (p : FullPair L k k le_rfl) : Prop :=
  pairColour p' = pairColour p ∧ (pairVertex p').1 = (pairVertex p).1
def periodicRel (q' : PeriodicPair L n k 0 (Nat.zero_le k)) (q : PeriodicPair L n k k le_rfl) :
    Prop :=
  periodicColour q' = periodicColour q ∧ (periodicVertex q').1 = (periodicVertex q).1
theorem supNormVec_zero : TorusMetric.supNormVec 0 = 0 := by
  simp [TorusMetric.supNormVec]
end Pairs
section Maps
variable {L n k : ℕ}
theorem fullZeroExtend_of_eq (g : FullSpace.Vertex L k k → ComplexMatrix2)
    (x : FullSpace.Vertex L k 0) (y : FullSpace.Vertex L k k) (hy : y.1 = x.1) :
    fullZeroExtend L k g x = g y := by
  have h : ∃ y : FullSpace.Vertex L k k, y.1 = x.1 := ⟨y, hy⟩
  simp only [fullZeroExtend, dif_pos h]
  exact congrArg g (Subtype.ext (h.choose_spec.trans hy.symm))
theorem fullZeroExtend_of_none (g : FullSpace.Vertex L k k → ComplexMatrix2)
    (x : FullSpace.Vertex L k 0) (h : ¬ ∃ y : FullSpace.Vertex L k k, y.1 = x.1) :
    fullZeroExtend L k g x = 0 := by
  simp only [fullZeroExtend, dif_neg h]
theorem zeroExtend_of_eq (g : Vertex L n k k → ComplexMatrix2) (x : Vertex L n k 0)
    (Y : Vertex L n k k) (hY : Y.1 = x.1) : zeroExtend L n k g x = g Y := by
  have h : ∃ y : Vertex L n k k, y.1 = x.1 := ⟨Y, hY⟩
  simp only [zeroExtend, dif_pos h]
  exact congrArg g (Subtype.ext (h.choose_spec.trans hY.symm))
theorem zeroExtend_of_none (g : Vertex L n k k → ComplexMatrix2) (x : Vertex L n k 0)
    (h : ¬ ∃ y : Vertex L n k k, y.1 = x.1) : zeroExtend L n k g x = 0 := by
  simp only [zeroExtend, dif_neg h]
theorem zeroExtend_mem (g : Vertex L n k k → ComplexMatrix2)
    (hg : ∀ i, g i ∈ ComplexMatrix2.traceless) (x : Vertex L n k 0) :
    zeroExtend L n k g x ∈ ComplexMatrix2.traceless := by
  by_cases h : ∃ y : Vertex L n k k, y.1 = x.1
  · obtain ⟨Y, hY⟩ := h
    rw [zeroExtend_of_eq g x Y hY]
    exact hg Y
  · rw [zeroExtend_of_none g x h]
    exact ComplexMatrix2.traceless.zero_mem
open GroupLieProduct (tracelessFunctions)
def zeroExtendLinear :
    tracelessFunctions (Vertex L n k k) →ₗ[ℂ] tracelessFunctions (Vertex L n k 0) where
  toFun f := ⟨zeroExtend L n k f.1, (mem_tracelessFunctions _).2
    (zeroExtend_mem f.1 ((mem_tracelessFunctions _).1 f.2))⟩
  map_add' f g := by
    refine Subtype.ext (funext fun x => ?_)
    show zeroExtend L n k (f.1 + g.1) x = zeroExtend L n k f.1 x + zeroExtend L n k g.1 x
    by_cases h : ∃ y : Vertex L n k k, y.1 = x.1
    · obtain ⟨Y, hY⟩ := h
      rw [zeroExtend_of_eq _ x Y hY, zeroExtend_of_eq _ x Y hY, zeroExtend_of_eq _ x Y hY]
      rfl
    · rw [zeroExtend_of_none _ x h, zeroExtend_of_none _ x h, zeroExtend_of_none _ x h, add_zero]
  map_smul' c f := by
    refine Subtype.ext (funext fun x => ?_)
    show zeroExtend L n k (c • f.1) x = c • zeroExtend L n k f.1 x
    by_cases h : ∃ y : Vertex L n k k, y.1 = x.1
    · obtain ⟨Y, hY⟩ := h
      rw [zeroExtend_of_eq _ x Y hY, zeroExtend_of_eq _ x Y hY]
      rfl
    · rw [zeroExtend_of_none _ x h, zeroExtend_of_none _ x h, smul_zero]
def restrictLinear (hL : 0 < L) :
    tracelessFunctions (Vertex L n k 0) →ₗ[ℂ] tracelessFunctions (Vertex L n k k) where
  toFun g := ⟨fun Y => g.1 (periodicLift hL Y), (mem_tracelessFunctions _).2
    fun Y => (mem_tracelessFunctions _).1 g.2 (periodicLift hL Y)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem pairing_restrictLinear (hL : 0 < L) (g : tracelessFunctions (Vertex L n k 0))
    (f : tracelessFunctions (Vertex L n k k)) :
    traceFinsumPairing (restrictLinear hL g).1 f.1 =
      traceFinsumPairing g.1 (zeroExtendLinear f).1 := by
  show traceFinsumPairing (fun Y => g.1 (periodicLift hL Y)) f.1 =
    traceFinsumPairing g.1 (zeroExtend L n k f.1)
  unfold traceFinsumPairing
  rw [finsum_eq_of_zero_off_range (periodicLift hL) (periodicLift_injective hL)
    (fun x => ComplexMatrix2.halfTrace (g.1 x * zeroExtend L n k f.1 x))]
  · refine finsum_congr fun Y => ?_
    rw [zeroExtend_of_eq f.1 (periodicLift hL Y) Y rfl]
  · intro x hx
    have h : ¬ ∃ y : Vertex L n k k, y.1 = x.1 := by
      rintro ⟨Y, hY⟩
      exact hx ⟨Y, Subtype.ext hY⟩
    rw [zeroExtend_of_none _ x h]
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
theorem traceFinsumPairing_single {σ : Type} (A : σ → ComplexMatrix2) (Y : σ) (t : ComplexMatrix2)
    [DecidableEq σ] :
    traceFinsumPairing A (Pi.single Y t) = ComplexMatrix2.halfTrace (A Y * t) := by
  unfold traceFinsumPairing
  rw [finsum_eq_single _ Y]
  · simp
  · intro y hy
    simp [Pi.single_eq_of_ne hy, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
theorem eq_of_traceFinsumPairing {σ : Type} (A B : tracelessFunctions σ)
    (h : ∀ f : tracelessFunctions σ, HasFiniteSupp f.1 →
      traceFinsumPairing A.1 f.1 = traceFinsumPairing B.1 f.1) :
    A = B := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeAverageMulTranspose.eq_of_pair_eq <;> assumption
theorem transposeMap_unique (hL : 0 < L)
    (T' : tracelessFunctions (Vertex L n k 0) →ₗ[ℂ] tracelessFunctions (Vertex L n k k))
    (h : ∀ (g : tracelessFunctions (Vertex L n k 0)) (f : tracelessFunctions (Vertex L n k k)),
      HasFiniteSupp f.1 →
        traceFinsumPairing (T' g).1 f.1 = traceFinsumPairing g.1 (zeroExtendLinear f).1) :
    T' = restrictLinear hL :=
  LinearMap.ext fun g => eq_of_traceFinsumPairing _ _ fun f hf =>
    (h g f hf).trans (pairing_restrictLinear hL g f).symm
theorem transposeMap_zeroExtendLinear (hL : 0 < L) :
    @PairedFunctionSpace.transposeMap (pairedFunctions (Vertex L n k k))
      (pairedFunctions (Vertex L n k 0)) zeroExtendLinear = restrictLinear hL := by
  have spec := Classical.epsilon_spec (p := @PairedFunctionSpace.IsTransposeMap
    (pairedFunctions (Vertex L n k k)) (pairedFunctions (Vertex L n k 0)) zeroExtendLinear)
    ⟨restrictLinear hL, fun g f _ => pairing_restrictLinear hL g f⟩
  exact transposeMap_unique hL _ fun g f hf => spec g f hf
end Maps
section Kernels
variable {L n k : ℕ}
abbrev fullKernel (L k : ℕ) :
    KernelMatrix (FullPair L k k le_rfl) (FullPair L k 0 (Nat.zero_le k)) :=
  relKernel fullRel
abbrev periodicMatrix (L n k : ℕ) :
    KernelMatrix (PeriodicPair L n k k le_rfl) (PeriodicPair L n k 0 (Nat.zero_le k)) :=
  relKernel periodicRel
abbrev fullKernelT (L k : ℕ) :
    KernelMatrix (FullPair L k 0 (Nat.zero_le k)) (FullPair L k k le_rfl) :=
  relKernel fun p p' => fullRel p' p
abbrev periodicMatrixT (L n k : ℕ) :
    KernelMatrix (PeriodicPair L n k 0 (Nat.zero_le k)) (PeriodicPair L n k k le_rfl) :=
  relKernel fun q q' => periodicRel q' q
theorem applyKernel_fullKernel (g : FullPair L k k le_rfl → ℂ)
    (p' : FullPair L k 0 (Nat.zero_le k)) (y : FullSpace.Vertex L k k)
    (hy : y.1 = (pairVertex p').1) :
    applyKernel (fullKernel L k) g p' = g (mkFullPair (pairColour p') y) :=
  applyKernel_relKernel_of_unique _ _ _ _ ⟨rfl, hy.symm⟩
    fun p hp => fullPair_ext p _ y hp.1.symm (hp.2.symm.trans hy.symm)
theorem applyKernel_fullKernel_of_none (g : FullPair L k k le_rfl → ℂ)
    (p' : FullPair L k 0 (Nat.zero_le k))
    (h : ¬ ∃ y : FullSpace.Vertex L k k, y.1 = (pairVertex p').1) :
    applyKernel (fullKernel L k) g p' = 0 :=
  applyKernel_relKernel_of_none _ _ _ fun p hp => h ⟨pairVertex p, hp.2.symm⟩
theorem applyKernel_periodicMatrix (g : PeriodicPair L n k k le_rfl → ℂ)
    (q' : PeriodicPair L n k 0 (Nat.zero_le k)) (Y : Vertex L n k k)
    (hY : Y.1 = (periodicVertex q').1) :
    applyKernel (periodicMatrix L n k) g q' = g (mkPeriodicPair (periodicColour q') Y) :=
  applyKernel_relKernel_of_unique _ _ _ _
    ⟨(periodicColour_mk _ _).symm, by rw [periodicVertex_mk]; exact hY.symm⟩
    fun q hq => periodicPair_ext _ _ (hq.1.symm.trans (periodicColour_mk _ _).symm)
      (by rw [periodicVertex_mk]; exact hq.2.symm.trans hY.symm)
theorem applyKernel_periodicMatrix_of_none (g : PeriodicPair L n k k le_rfl → ℂ)
    (q' : PeriodicPair L n k 0 (Nat.zero_le k))
    (h : ¬ ∃ Y : Vertex L n k k, Y.1 = (periodicVertex q').1) :
    applyKernel (periodicMatrix L n k) g q' = 0 :=
  applyKernel_relKernel_of_none _ _ _ fun q hq => h ⟨periodicVertex q, hq.2.symm⟩
theorem applyKernel_fullKernelT (hL : 0 < L) (g : FullPair L k 0 (Nat.zero_le k) → ℂ)
    (p : FullPair L k k le_rfl) :
    applyKernel (fullKernelT L k) g p = g (mkFullPair (pairColour p) (fullLift hL (pairVertex p))) :=
  applyKernel_relKernel_of_unique _ _ _ _ ⟨rfl, rfl⟩
    fun p' hp => fullPair_ext p' _ _ hp.1 hp.2
theorem applyKernel_periodicMatrixT (hL : 0 < L) (g : PeriodicPair L n k 0 (Nat.zero_le k) → ℂ)
    (q : PeriodicPair L n k k le_rfl) :
    applyKernel (periodicMatrixT L n k) g q =
      g (mkPeriodicPair (periodicColour q) (periodicLift hL (periodicVertex q))) :=
  applyKernel_relKernel_of_unique _ _ _ _
    ⟨periodicColour_mk _ _, by rw [periodicVertex_mk]; rfl⟩
    fun q' hq => periodicPair_ext _ _ (hq.1.trans (periodicColour_mk _ _).symm)
      (by rw [periodicVertex_mk]; exact hq.2)
theorem fullKernel_isRLocal :
    IsRLocal L (CellClass.vertexClass k k le_rfl).colourPairs (verticesAtZero k).colourPairs 6
      (fullKernel L k) := by
  classical
  intro p' p h
  have hr : ¬ fullRel p' p := by
    intro hr
    apply h
    show TorusMetric.supNormVec ((pairVertex p).1 - (pairVertex p').1) ≤ 6
    rw [hr.2, sub_self, supNormVec_zero]
    norm_num
  simp [relKernel, hr]
theorem fullKernelT_isRLocal :
    IsRLocal L (verticesAtZero k).colourPairs (CellClass.vertexClass k k le_rfl).colourPairs 6
      (fullKernelT L k) := by
  classical
  intro p p' h
  have hr : ¬ fullRel p' p := by
    intro hr
    apply h
    show TorusMetric.supNormVec ((pairVertex p').1 - (pairVertex p).1) ≤ 6
    rw [hr.2, sub_self, supNormVec_zero]
    norm_num
  simp [relKernel, hr]
theorem kernelT_fullKernel :
    kernelT L (CellClass.vertexClass k k le_rfl).colourPairs (verticesAtZero k).colourPairs
      (fullKernel L k) = fullKernelT L k := by
  funext p p'
  show (((1 / 1 : ℝ)) : ℂ) * fullKernel L k p' p = fullKernelT L k p p'
  simp [relKernel]
theorem fullKernel_descends :
    KernelDescends L n (CellClass.vertexClass k k le_rfl).colourPairs
      (verticesAtZero k).colourPairs (fullKernel L k) (periodicMatrix L n k) := by
  refine ⟨⟨6, by norm_num, fullKernel_isRLocal⟩, fun f => funext fun p' => ?_⟩
  show applyKernel (fullKernel L k) _ p' =
    applyKernel (periodicMatrix L n k) f ((verticesAtZero k).colourPairs.proj L n p')
  by_cases h : ∃ y : FullSpace.Vertex L k k, y.1 = (pairVertex p').1
  · obtain ⟨y, hy⟩ := h
    have hY : (FullSpace.projVertex L n k k y).1 =
        (periodicVertex ((verticesAtZero k).colourPairs.proj L n p')).1 := by
      rw [periodicVertex_proj]
      show TorusMetric.torusProj _ y.1 = TorusMetric.torusProj _ (pairVertex p').1
      rw [hy]
    rw [applyKernel_fullKernel _ p' y hy, applyKernel_periodicMatrix _ _ _ hY]
    show f _ = f _
    congr 1
    exact periodicPair_ext _ _ (by rw [periodicColour_mk]; rfl) (by rw [periodicVertex_mk]; rfl)
  · rw [applyKernel_fullKernel_of_none _ p' h, applyKernel_periodicMatrix_of_none]
    rintro ⟨Y, hY⟩
    exact h (exists_full_of_proj _ Y hY)
theorem fullKernelT_descends (hL : 0 < L) :
    KernelDescends L n (verticesAtZero k).colourPairs
      (CellClass.vertexClass k k le_rfl).colourPairs (fullKernelT L k) (periodicMatrixT L n k) := by
  refine ⟨⟨6, by norm_num, fullKernelT_isRLocal⟩, fun f => funext fun p => ?_⟩
  show applyKernel (fullKernelT L k) _ p =
    applyKernel (periodicMatrixT L n k) f
      ((CellClass.vertexClass k k le_rfl).colourPairs.proj L n p)
  rw [applyKernel_fullKernelT hL, applyKernel_periodicMatrixT hL]
  show f _ = f _
  congr 1
  exact periodicPair_ext _ _ (by rw [periodicColour_mk]; rfl) (by rw [periodicVertex_mk]; rfl)
end Kernels
section Coefficients
variable {L n k : ℕ}
theorem pauliCoeff_fullZeroExtend (f : FullSpace.Vertex L k k → ComplexMatrix2)
    (p' : FullPair L k 0 (Nat.zero_le k)) :
    pauliCoeff (pairColour p') (fullZeroExtend L k f (pairVertex p')) =
      applyKernel (fullKernel L k)
        (fun p => pauliCoeff (pairColour p) (f (pairVertex p))) p' := by
  by_cases h : ∃ y : FullSpace.Vertex L k k, y.1 = (pairVertex p').1
  · obtain ⟨y, hy⟩ := h
    rw [applyKernel_fullKernel _ p' y hy, fullZeroExtend_of_eq f _ y hy]
    rfl
  · rw [applyKernel_fullKernel_of_none _ p' h, fullZeroExtend_of_none f _ h, pauliCoeff_zero]
theorem pauliCoeff_zeroExtend (f : Vertex L n k k → ComplexMatrix2)
    (q' : PeriodicPair L n k 0 (Nat.zero_le k)) :
    pauliCoeff (periodicColour q') (zeroExtend L n k f (periodicVertex q')) =
      applyKernel (periodicMatrix L n k)
        (fun q => pauliCoeff (periodicColour q) (f (periodicVertex q))) q' := by
  by_cases h : ∃ Y : Vertex L n k k, Y.1 = (periodicVertex q').1
  · obtain ⟨Y, hY⟩ := h
    rw [applyKernel_periodicMatrix _ q' Y hY, zeroExtend_of_eq f _ Y hY]
    show _ = pauliCoeff (periodicColour (mkPeriodicPair (h := le_rfl) (periodicColour q') Y))
      (f (periodicVertex (mkPeriodicPair (h := le_rfl) (periodicColour q') Y)))
    rw [periodicColour_mk, periodicVertex_mk]
  · rw [applyKernel_periodicMatrix_of_none _ q' h, zeroExtend_of_none f _ h, pauliCoeff_zero]
theorem pauliCoeff_periodicLift (hL : 0 < L) (g : Vertex L n k 0 → ComplexMatrix2)
    (q : PeriodicPair L n k k le_rfl) :
    pauliCoeff (periodicColour q) (g (periodicLift hL (periodicVertex q))) =
      applyKernel (periodicMatrixT L n k)
        (fun q' => pauliCoeff (periodicColour q') (g (periodicVertex q'))) q := by
  rw [applyKernel_periodicMatrixT hL]
  show _ = pauliCoeff
    (periodicColour (mkPeriodicPair (h := Nat.zero_le k) (periodicColour q)
      (periodicLift hL (periodicVertex q))))
    (g (periodicVertex (mkPeriodicPair (h := Nat.zero_le k) (periodicColour q)
      (periodicLift hL (periodicVertex q)))))
  rw [periodicColour_mk, periodicVertex_mk]
theorem fullZeroExtend_mem (f : FullSpace.Vertex L k k → ComplexMatrix2)
    (hf : ∀ i, f i ∈ ComplexMatrix2.traceless) (x : FullSpace.Vertex L k 0) :
    fullZeroExtend L k f x ∈ ComplexMatrix2.traceless := by
  by_cases h : ∃ y : FullSpace.Vertex L k k, y.1 = x.1
  · obtain ⟨y, hy⟩ := h
    rw [fullZeroExtend_of_eq f x y hy]
    exact hf y
  · rw [fullZeroExtend_of_none f x h]
    exact ComplexMatrix2.traceless.zero_mem
theorem zeroExtendDescends_of_pos (hL : 0 < L) : ZeroExtendDescends L n k := by
  unfold ZeroExtendDescends Periodizes DescendsToMapOnPairs
  refine ⟨fullKernel L k, zeroExtendLinear, fullKernel_isRLocal, fun f => ⟨?_, ?_⟩, fun f => rfl,
    ⟨periodicMatrix L n k, fun f => ?_, fullKernel_descends⟩,
    ⟨periodicMatrixT L n k, fun g => ?_, ?_⟩⟩
  · exact (mem_tracelessFunctions _).2
      (fullZeroExtend_mem f.1 ((mem_tracelessFunctions _).1 f.2))
  · exact funext fun p' => pauliCoeff_fullZeroExtend f.1 p'
  · exact funext fun q' => pauliCoeff_zeroExtend f.1 q'
  · refine funext fun q => ?_
    have e : (@PairedFunctionSpace.transposeMap (pairedFunctions (Vertex L n k k))
        (pairedFunctions (Vertex L n k 0)) zeroExtendLinear g).1 =
        (restrictLinear hL g).1 := by
      rw [transposeMap_zeroExtendLinear hL]
      rfl
    refine Eq.trans ?_ (pauliCoeff_periodicLift hL g.1 q)
    exact congrArg (fun v : Vertex L n k k → ComplexMatrix2 =>
      pauliCoeff (periodicColour q) (v (periodicVertex q))) e
  · rw [kernelT_fullKernel]
    exact fullKernelT_descends hL
end Coefficients
theorem claim_holds : ZeroExtensionOfVertexFunctions.Claim := by
  intro L hL k n _ _
  exact zeroExtendDescends_of_pos (by have := hL.2; omega)
end YangMills.Construction.LocalKernels.VertexZeroExtension
end
