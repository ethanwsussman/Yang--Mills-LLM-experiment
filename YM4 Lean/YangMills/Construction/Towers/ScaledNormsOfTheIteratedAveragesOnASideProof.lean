import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.Towers.ScaledNormsOfSmallIteratesAtTheSideInfinityProof
import YangMills.Construction.Towers.ScaledNormsOfTheIteratedAveragesOnASide
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.RescaledNormBounds
open YangMills.Construction.Matrices
open YangMills.Construction.Conventions (IsAdmissibleBlockingFactor)
open YangMills.Construction.PeriodicOperators (KernelMatrix applyKernel wOpNorm OpNormSummable wNorm
  NormSummable wUnitBall Represents kernelOfMap)
open YangMills.Construction.Tower.SmoothingContraction (TorusOpNormLE)
open YangMills.Construction.Tower.SmoothingStepsNearFree (MapNormLE distFromOne)
section Norms
variable {σ σ' : Type}
theorem wNorm_add_le [Finite σ] {a : ℝ} (ha : 0 < a) (f g : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a) (f + g) ≤
      wNorm (meshWeight a) f + wNorm (meshWeight a) g := by apply _root_.YangMills.SharedProofs.p20251 <;> assumption
theorem wNorm_smul [Finite σ] {a : ℝ} (ha : 0 < a) (z : ℂ) (f : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a) (z • f) = ‖z‖ * wNorm (meshWeight a) f := by apply _root_.YangMills.SharedProofs.p8315 <;> assumption
theorem wNorm_nonneg (a : ℝ) (f : Fin 3 × σ → ℂ) : 0 ≤ wNorm (meshWeight a) f :=
  Real.sqrt_nonneg _
theorem eq_zero_of_wNorm_eq_zero [Finite σ] {a : ℝ} (ha : 0 < a) {f : Fin 3 × σ → ℂ}
    (h : wNorm (meshWeight a) f = 0) : f = 0 := by apply _root_.YangMills.SharedProofs.p4646 <;> assumption
theorem normSummable_of_finite [Finite σ] (w : Fin 3 × σ → ℝ) (f : Fin 3 × σ → ℂ) :
    NormSummable w f := by apply _root_.YangMills.SharedProofs.p57614 <;> assumption
structure IsComplexLinear (M : (Fin 3 × σ → ℂ) → Fin 3 × σ' → ℂ) : Prop where
  map_add : ∀ f g, M (f + g) = M f + M g
  map_smul : ∀ (z : ℂ) f, M (z • f) = z • M f
theorem wNorm_apply_le_of_wOpNorm_le [Finite σ] [Finite σ'] {a a' c : ℝ} (ha : 0 < a)
    (ha' : 0 < a') (hc : 0 ≤ c) {M : (Fin 3 × σ → ℂ) → Fin 3 × σ' → ℂ} (hM : IsComplexLinear M)
    (h : wOpNorm (meshWeight a) (meshWeight a') univ M ≤ ENNReal.ofReal c)
    (f : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a') (M f) ≤ c * wNorm (meshWeight a) f := by
  by_cases h0 : wNorm (meshWeight a) f = 0
  · have e := eq_zero_of_wNorm_eq_zero ha h0
    have e₀ : M 0 = 0 := by
      have := hM.map_smul 0 0
      simpa using this
    have e₁ := wNorm_smul ha' (0 : ℂ) (0 : Fin 3 × σ' → ℂ)
    rw [zero_smul, norm_zero, zero_mul] at e₁
    rw [h0, mul_zero, e, e₀, e₁]
  have hpos : 0 < wNorm (meshWeight a) f := lt_of_le_of_ne (wNorm_nonneg a f) (Ne.symm h0)
  obtain ⟨t, ht⟩ : ∃ t, t = wNorm (meshWeight a) f := ⟨_, rfl⟩
  rw [← ht] at hpos ⊢
  have hu : ((t⁻¹ : ℝ) : ℂ) • f ∈ wUnitBall (meshWeight a) univ := by
    refine ⟨mem_univ _, normSummable_of_finite _ _, ?_⟩
    rw [wNorm_smul ha, ← ht, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hpos.le),
      inv_mul_cancel₀ hpos.ne']
  have h₁ : ENNReal.ofReal (wNorm (meshWeight a') (M (((t⁻¹ : ℝ) : ℂ) • f))) ≤
      ENNReal.ofReal c :=
    le_trans (le_iSup₂ (f := fun g (_ : g ∈ wUnitBall (meshWeight a) univ) =>
      ENNReal.ofReal (wNorm (meshWeight a') (M g))) _ hu) h
  have h₂ := (ENNReal.ofReal_le_ofReal_iff hc).1 h₁
  rw [hM.map_smul, wNorm_smul ha', Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 hpos.le)] at h₂
  have h₃ := mul_le_mul_of_nonneg_left h₂ hpos.le
  rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm t c] at h₃
theorem torusOpNormLE_of_bound [Finite σ'] {a a' c : ℝ} (hc : 0 ≤ c)
    {T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')}
    (hb : ∀ f, wNorm (meshWeight a') (applyKernel T f) ≤
      c * wNorm (meshWeight a) f) :
    TorusOpNormLE a a' T c := by apply _root_.YangMills.SharedProofs.p4978 <;> assumption
end Norms
structure IsFaithful (r : PauliComponentsOfSymmetricKernel) : Prop where
  finite : Finite r.Place
  mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  coeffs_ofCoeffs : ∀ c, r.coeffs (r.ofCoeffs c) = c
  ofCoeffs_coeffs : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  ofCoeffs_add : ∀ c c', r.ofCoeffs (c + c') = r.ofCoeffs c + r.ofCoeffs c'
  ofCoeffs_smul : ∀ (z : ℂ) c, r.ofCoeffs (z • c) = z • r.ofCoeffs c
theorem IsFaithful.coeffs_smul {r : PauliComponentsOfSymmetricKernel} (h : IsFaithful r) (z : ℂ)
    {f : r.space.index → ComplexMatrix2} (hf : f ∈ r.space.complexSubmodule) :
    r.coeffs (z • f) = z • r.coeffs f := by
  have e : z • f = r.ofCoeffs (z • r.coeffs f) := by
    rw [h.ofCoeffs_smul, h.ofCoeffs_coeffs f hf]
  rw [e, h.coeffs_ofCoeffs]
theorem applyKernel_kernelOfBasisImages {r r' : PauliComponentsOfSymmetricKernel} [Finite r.Place]
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hm : IsComplexLinear (r.mapOnCoeffs r' m)) (f : r.Index → ℂ) :
    applyKernel (r.kernelOfBasisImages r' m) f = r.mapOnCoeffs r' m f := by
  classical
  cases nonempty_fintype r.Place
  have hzero : r.mapOnCoeffs r' m 0 = 0 := by
    have := hm.map_smul 0 0
    simpa using this
  have hsum : ∀ s : Finset r.Index, r.mapOnCoeffs r' m (∑ ι ∈ s, f ι • Pi.single ι (1 : ℂ)) =
      ∑ ι ∈ s, f ι • r.mapOnCoeffs r' m (Pi.single ι 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert ι s hι ih =>
      rw [Finset.sum_insert hι, Finset.sum_insert hι, hm.map_add, hm.map_smul, ih]
  have hf : f = ∑ ι, f ι • Pi.single ι (1 : ℂ) := by
    funext ι
    simp [Finset.sum_apply, Pi.single_apply]
  funext ι'
  conv_rhs => rw [hf, hsum]
  unfold applyKernel PauliComponentsOfSymmetricKernel.kernelOfBasisImages
  rw [tsum_fintype, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ι _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
theorem isComplexLinear_mapOnCoeffs {r r' : PauliComponentsOfSymmetricKernel} (hr : IsFaithful r)
    (P : (r'.space.index → ComplexMatrix2) → Prop)
    (cadd : ∀ X Y, P X → P Y → r'.coeffs (X + Y) = r'.coeffs X + r'.coeffs Y)
    (csmul : ∀ (z : ℂ) X, P X → r'.coeffs (z • X) = z • r'.coeffs X)
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hP : ∀ X ∈ r.space.complexSubmodule, P (m X))
    (madd : ∀ X ∈ r.space.complexSubmodule, ∀ Y ∈ r.space.complexSubmodule,
      m (X + Y) = m X + m Y)
    (msmul : ∀ (z : ℂ), ∀ X ∈ r.space.complexSubmodule, m (z • X) = z • m X) :
    IsComplexLinear (r.mapOnCoeffs r' m) where
  map_add f g := by
    show r'.coeffs (m (r.ofCoeffs (f + g))) = r'.coeffs (m (r.ofCoeffs f)) +
      r'.coeffs (m (r.ofCoeffs g))
    rw [hr.ofCoeffs_add, madd _ (hr.mem f) _ (hr.mem g),
      cadd _ _ (hP _ (hr.mem f)) (hP _ (hr.mem g))]
  map_smul z f := by
    show r'.coeffs (m (r.ofCoeffs (z • f))) = z • r'.coeffs (m (r.ofCoeffs f))
    rw [hr.ofCoeffs_smul, msmul z _ (hr.mem f), csmul z _ (hP _ (hr.mem f))]
theorem iterate_norm_le_prod {r : ℕ → PauliComponentsOfSymmetricKernel} {a e : ℕ → ℝ} {k : ℕ} {s : ℂ}
    (hr : ∀ j ≤ k, IsFaithful (r j)) (ha : ∀ j, 0 < a j) (he : ∀ j, 0 ≤ e j)
    (w d p : ∀ j, ((r j).space.index → ComplexMatrix2) → (r (j + 1)).space.index → ComplexMatrix2)
    (It : ∀ j, ((r 0).space.index → ComplexMatrix2) → (r j).space.index → ComplexMatrix2)
    (h0 : ∀ B, It 0 B = B) (hs : ∀ j < k, ∀ B, It (j + 1) B = w j (It j B))
    (wmem : ∀ j < k, ∀ X ∈ (r j).space.complexSubmodule,
      w j X ∈ (r (j + 1)).space.complexSubmodule)
    (wsmul : ∀ j < k, ∀ (z : ℂ), ∀ X ∈ (r j).space.complexSubmodule, w j (z • X) = z • w j X)
    (hd : ∀ j < k, ∀ f, wNorm (meshWeight (a (j + 1)))
      ((r j).mapOnCoeffs (r (j + 1)) (d j) f) ≤ e j * wNorm (meshWeight (a j)) f)
    (hp : ∀ j < k, ∀ f, wNorm (meshWeight (a (j + 1)))
      ((r j).mapOnCoeffs (r (j + 1)) (p j) f) ≤ wNorm (meshWeight (a j)) f)
    (hsum : ∀ j < k, ∀ X ∈ (r j).space.complexSubmodule, (r (j + 1)).coeffs (s • w j X) =
      (r (j + 1)).coeffs (d j X) + (r (j + 1)).coeffs (p j X)) :
    ∀ j ≤ k, ∀ f : (r 0).Index → ℂ,
      It j ((r 0).ofCoeffs f) ∈ (r j).space.complexSubmodule ∧
      wNorm (meshWeight (a j)) (s ^ j • (r j).coeffs (It j ((r 0).ofCoeffs f))) ≤
        (∏ i ∈ Finset.range j, (1 + e i)) * wNorm (meshWeight (a 0)) f := by
  intro j
  induction j with
  | zero =>
    intro h f
    have h₀ := hr 0 h
    rw [h0]
    refine ⟨h₀.mem f, ?_⟩
    rw [h₀.coeffs_ofCoeffs]
    simp
  | succ j ih =>
    intro hj f
    have hj' : j < k := hj
    obtain ⟨hm, hb⟩ := ih hj'.le f
    have hrj := hr j hj'.le
    have hr' := hr (j + 1) hj
    obtain ⟨X, hXe⟩ : ∃ X, X = It j ((r 0).ofCoeffs f) := ⟨_, rfl⟩
    rw [← hXe] at hm hb
    obtain ⟨g, hg⟩ : ∃ g, g = s ^ j • (r j).coeffs X := ⟨_, rfl⟩
    rw [← hg] at hb
    have hX : (r j).ofCoeffs g = s ^ j • X := by
      rw [hg, hrj.ofCoeffs_smul, hrj.ofCoeffs_coeffs X hm]
    have hX' : s ^ j • X ∈ (r j).space.complexSubmodule := Submodule.smul_mem _ _ hm
    have e₁ : s ^ (j + 1) • (r (j + 1)).coeffs (w j X) =
        (r j).mapOnCoeffs (r (j + 1)) (d j) g + (r j).mapOnCoeffs (r (j + 1)) (p j) g := by
      show _ = (r (j + 1)).coeffs (d j ((r j).ofCoeffs g)) +
        (r (j + 1)).coeffs (p j ((r j).ofCoeffs g))
      rw [hX, ← hsum j hj' _ hX', wsmul j hj' _ X hm, smul_smul,
        hr'.coeffs_smul _ (wmem j hj' X hm), pow_succ']
    rw [hs j hj', ← hXe]
    refine ⟨wmem j hj' X hm, ?_⟩
    rw [e₁, Finset.prod_range_succ]
    have := hr'.finite
    have hg0 := wNorm_nonneg (a j) g
    have h₁ := wNorm_add_le (ha (j + 1)) ((r j).mapOnCoeffs (r (j + 1)) (d j) g)
      ((r j).mapOnCoeffs (r (j + 1)) (p j) g)
    have h₂ := hd j hj' g
    have h₃ := hp j hj' g
    have h₄ : 0 ≤ 1 + e j := by linarith [he j]
    calc _ ≤ (1 + e j) * wNorm (meshWeight (a j)) g := by nlinarith
      _ ≤ (1 + e j) * ((∏ i ∈ Finset.range j, (1 + e i)) *
          wNorm (meshWeight (a 0)) f) := mul_le_mul_of_nonneg_left hb h₄
      _ = _ := by ring
section Coefficients
theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem combination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
theorem pauliCoeff_smul (a : Fin 3) (z : ℂ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (z • X) = z * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
end Coefficients
theorem isFaithful_of {r : PauliComponentsOfSymmetricKernel} (hfin : Finite r.Place)
    (hmem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule)
    (hleft : ∀ c, r.coeffs (r.ofCoeffs c) = c)
    (hright : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f)
    (cadd : ∀ f ∈ r.space.complexSubmodule, ∀ g ∈ r.space.complexSubmodule,
      r.coeffs (f + g) = r.coeffs f + r.coeffs g)
    (csmul : ∀ (z : ℂ), ∀ f ∈ r.space.complexSubmodule, r.coeffs (z • f) = z • r.coeffs f) :
    IsFaithful r where
  finite := hfin
  mem := hmem
  coeffs_ofCoeffs := hleft
  ofCoeffs_coeffs := hright
  ofCoeffs_add c c' := by
    have e := cadd _ (hmem c) _ (hmem c')
    rw [hleft, hleft] at e
    rw [← e, hright _ (Submodule.add_mem _ (hmem c) (hmem c'))]
  ofCoeffs_smul z c := by
    have e := csmul z _ (hmem c)
    rw [hleft] at e
    rw [← e, hright _ (Submodule.smul_mem _ z (hmem c))]
section Sites
variable {σ : Type}
theorem vertex_mem_complexSubmodule_iff {f : σ → ComplexMatrix2} :
    f ∈ (vertexCoordinate σ).space.complexSubmodule ↔ ∀ x, f x ∈ ComplexMatrix2.traceless :=
  ⟨fun h x => Submodule.mem_pi.1 h x (mem_univ x), fun h => Submodule.mem_pi.2 fun x _ => h x⟩
theorem vertex_coeffs_add {f g : σ → ComplexMatrix2} (hf : ∀ x, f x ∈ ComplexMatrix2.traceless)
    (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) :
    (vertexCoordinate σ).coeffs (f + g) = (vertexCoordinate σ).coeffs f + (vertexCoordinate σ).coeffs g :=
  funext fun ι => pauliCoeff_add ι.1 (hf ι.2) (hg ι.2)
theorem vertex_coeffs_smul (z : ℂ) {f : σ → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) :
    (vertexCoordinate σ).coeffs (z • f) = z • (vertexCoordinate σ).coeffs f :=
  funext fun ι => pauliCoeff_smul ι.1 z (hf ι.2)
theorem vertexCoordinate_isFaithful [Finite σ] : IsFaithful (vertexCoordinate σ) :=
  isFaithful_of (r := vertexCoordinate σ) (inferInstanceAs (Finite σ))
    (fun c => vertex_mem_complexSubmodule_iff.2 (ofPauliCoeffs_mem_traceless c))
    (fun c => funext fun ι => pauliCoeff_combination (fun a => c (a, ι.2)) ι.1)
    (fun _ hf => funext fun x => combination_pauliCoeff (vertex_mem_complexSubmodule_iff.1 hf x))
    (fun _ hf _ hg => vertex_coeffs_add (vertex_mem_complexSubmodule_iff.1 hf)
      (vertex_mem_complexSubmodule_iff.1 hg))
    (fun z _ hf => vertex_coeffs_smul z (vertex_mem_complexSubmodule_iff.1 hf))
end Sites
section Forms
variable {L n k j : ℕ}
theorem extendOddly_of_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos h
theorem extendOddly_opposite (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hx : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.SharedProofs.p17859 <;> assumption
def TracelessOnPositive (X : Edge L n k j → ComplexMatrix2) : Prop :=
  ∀ b : Edge L n k j, b.IsPositivelyOriented → X b ∈ ComplexMatrix2.traceless
theorem edge_coeffs_add {X Y : Edge L n k j → ComplexMatrix2} (hX : TracelessOnPositive X)
    (hY : TracelessOnPositive Y) :
    (edgePauliCoordinates L n k j).coeffs (X + Y) =
      (edgePauliCoordinates L n k j).coeffs X + (edgePauliCoordinates L n k j).coeffs Y := by apply _root_.YangMills.DeltaSharedProofs.p501675 <;> assumption
theorem edge_coeffs_smul (z : ℂ) {X : Edge L n k j → ComplexMatrix2}
    (hX : TracelessOnPositive X) :
    (edgePauliCoordinates L n k j).coeffs (z • X) = z • (edgePauliCoordinates L n k j).coeffs X := by apply _root_.YangMills.DeltaSharedProofs.p501619 <;> assumption
def positiveValuesOfCoeffs (c : (edgePauliCoordinates L n k j).Index → ℂ) :
    Edge L n k j → ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
theorem edge_ofCoeffs_of_pos (c : (edgePauliCoordinates L n k j).Index → ℂ) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) :
    (edgePauliCoordinates L n k j).ofCoeffs c b = ofPauliCoeffs c ⟨b, h⟩ := by apply _root_.YangMills.SharedProofs.p19922 <;> assumption
theorem edgePauliCoordinates_isFaithful (hfin : Finite (Edge L n k j))
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    IsFaithful (edgePauliCoordinates L n k j) := by
  have hmem : ∀ c, (edgePauliCoordinates L n k j).ofCoeffs c ∈ complexEdgeForms L n k j := fun c =>
    ⟨fun b hb => by
      rw [edge_ofCoeffs_of_pos c hb]
      exact ofPauliCoeffs_mem_traceless c _,
      fun b => extendOddly_opposite (positiveValuesOfCoeffs c) (hx b)⟩
  refine isFaithful_of (r := edgePauliCoordinates L n k j) ?_ hmem ?_ ?_ ?_ ?_
  · exact (inferInstanceAs (Finite {b : Edge L n k j // b.IsPositivelyOriented}))
  · intro c
    funext ι
    have e : (edgePauliCoordinates L n k j).ofCoeffs c ι.2.1 = ofPauliCoeffs c ι.2 :=
      edge_ofCoeffs_of_pos c ι.2.2
    show pauliCoeff ι.1 ((edgePauliCoordinates L n k j).ofCoeffs c ι.2.1) = c ι
    rw [e]
    exact pauliCoeff_combination (fun a => c (a, ι.2)) ι.1
  · intro f hf
    have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
        (edgePauliCoordinates L n k j).ofCoeffs ((edgePauliCoordinates L n k j).coeffs f) b = f b := fun b hb =>
      (edge_ofCoeffs_of_pos _ hb).trans (combination_pauliCoeff (hf.1 b hb))
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact hpos b hb
    · have hrb : b.opposite.IsPositivelyOriented := by
        rcases hx b with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h hb
        · exact h
      have e₁ := (hmem ((edgePauliCoordinates L n k j).coeffs f)).2 b.opposite
      have e₂ : (b.opposite).opposite = b := rfl
      rw [e₂, hpos _ hrb, hf.2 b, neg_neg] at e₁
      exact e₁
  · exact fun _ hf _ hg => edge_coeffs_add hf.1 hg.1
  · exact fun z _ hf => edge_coeffs_smul z hf.1
theorem value_mem_traceless
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : Edge L n k j → ComplexMatrix2} (hX : X ∈ complexEdgeForms L n k j) (b : Edge L n k j) :
    X b ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.SharedProofs.p16313 <;> assumption
theorem covDiff_add (W : Edge L n k j → ComplexMatrix2) (l l' : Vertex L n k j → ComplexMatrix2) :
    covDiff W (l + l') = covDiff W l + covDiff W l' := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.covDiff_add <;> assumption
theorem covDiff_smul (W : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2)
    (z : ℂ) : covDiff W (z • l) = z • covDiff W l := by apply _root_.YangMills.SharedProofs.p24956 <;> assumption
theorem edgeFormPathSum_mem {B : Edge L n k j → ComplexMatrix2}
    (hB : ∀ b, B b ∈ ComplexMatrix2.traceless) (Γ : List (Edge L n k j)) :
    edgeFormPathSum B Γ ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.SharedProofs.p3039 <;> assumption
variable [Finite (Vertex L n k j)]
theorem crossingSmoothing_add (B B' : Edge L n k j → ComplexMatrix2) :
    crossingSmoothing L n k j (B + B') =
      crossingSmoothing L n k j B + crossingSmoothing L n k j B' := by apply _root_.YangMills.SharedProofs.p41844 <;> assumption
theorem crossingSmoothing_smul (z : ℂ) (B : Edge L n k j → ComplexMatrix2) :
    crossingSmoothing L n k j (z • B) = z • crossingSmoothing L n k j B := by apply _root_.YangMills.SharedProofs.p16432 <;> assumption
theorem crossingSmoothing_tracelessOnPositive {B : Edge L n k j → ComplexMatrix2}
    (hB : ∀ b, B b ∈ ComplexMatrix2.traceless) :
    TracelessOnPositive (crossingSmoothing L n k j B) := by apply _root_.YangMills.DeltaSharedProofs.p502043 <;> assumption
theorem vertexSmoothing_add (l l' : Vertex L n k j → ComplexMatrix2) :
    vertexSmoothing L n k j (l + l') = vertexSmoothing L n k j l + vertexSmoothing L n k j l' := by apply _root_.YangMills.SharedProofs.p8206 <;> assumption
theorem vertexSmoothing_smul (z : ℂ) (l : Vertex L n k j → ComplexMatrix2) :
    vertexSmoothing L n k j (z • l) = z • vertexSmoothing L n k j l := by apply _root_.YangMills.SharedProofs.p51938 <;> assumption
theorem vertexSmoothing_mem {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (y : Vertex L n k (j + 1)) :
    vertexSmoothing L n k j l y ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.SharedProofs.p3658 <;> assumption
end Forms
structure Hypotheses : Prop where
  nearFree : SmoothingStepsNearFree.Claim
  contraction : SmoothingContraction.Claim
  kernels : ThreeMapKernels.Claim
  linearity : StepMapsComplexLinear.Claim
  meanInGroup : ComplexMeanLiesInComplexGaugeGroup
  nearIdentity : _root_.YangMills.Construction.Tower.SmoothingNearIdentity
  conjugation : ComplexMatrix2.ConjugationPreservesTraceless
  orientation : PeriodicLattice.BondEndpointsOrientation.Statement
  finiteEdges : BondSetFields.ProductStructureHolds
section Tower
variable {L n k : ℕ}
theorem edge_xor_opposite (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) (b : Edge L n k j) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  ((G.orientation ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
theorem finite_edge (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ}
    (hj : j ≤ k) : Finite (Edge L n k j) :=
  Set.finite_univ_iff.1 ((G.finiteEdges L hL k j hj).1 n hn).2.1
theorem finite_vertex (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ}
    (hj : j ≤ k) : Finite (Vertex L n k j) :=
  have := finite_edge G hL hn hj
  Finite.of_injective (fun x : Vertex L n k j => PeriodicLattice.Bond.forwardFrom x 0)
    fun _ _ h => congrArg PeriodicLattice.Bond.source h
theorem edgePauliCoordinates_faithful (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) : IsFaithful (edgePauliCoordinates L n k j) :=
  edgePauliCoordinates_isFaithful (finite_edge G hL hn hj) (edge_xor_opposite G hL hn hk hj)
theorem vertexCoordinate_faithful (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {j : ℕ} (hj : j ≤ k) : IsFaithful (vertexCoordinate (Vertex L n k j)) :=
  have := finite_vertex G hL hn hj
  vertexCoordinate_isFaithful
theorem meshAt_pos (hL : IsAdmissibleBlockingFactor L) (k j : ℕ) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem complexBlockAverageStep_mem_unitDeterminant (G : Hypotheses)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k j)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverageStep j V c ∈ ComplexMatrix2.unitDeterminant :=
  ((G.meanInGroup.2 L k (j + 1) hL (by omega) hj).1 n hn c V hc
    (((G.nearIdentity.1 L hL).2.2.periodic n k j hn hj c hc).subset_complexDomain
      ⟨⟨fun b _ => hV.1.1 b (mem_univ b), fun b _ => hV.1.2 b (mem_univ b)⟩,
        fun b _ => hV.2 b⟩)).2
section Step
variable {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
theorem covariantSmoothingDeriv_mem (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (hV : V ∈ smallComplexFields L n k j)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    covariantSmoothingDeriv V B ∈ complexEdgeForms L n k (j + 1) := by
  obtain ⟨h₁, _, _, _⟩ := G.linearity L hL n k j hn hj V hV
  have hdrift := (h₁ B hB).2
  refine Submodule.add_mem _ (h₁ B hB).1 ⟨fun c hc => ?_, fun c => ?_⟩
  · have e : covDiff (PeriodicLattice.complexBlockAverageStep j V) (contourLogDrift V B) c =
        ComplexMatrix2.conjugateBy (PeriodicLattice.complexBlockAverageStep j V c)
            (contourLogDrift V B c.target) -
          contourLogDrift V B c.source := extendOddly_of_pos _ hc
    rw [e]
    exact ComplexMatrix2.traceless.sub_mem
      ((G.conjugation.2.2 _ (G.conjugation.1 _
        (complexBlockAverageStep_mem_unitDeterminant G hL hn hj hV hc))).2.2.2.1
        (hdrift _)) (hdrift _)
  · exact extendOddly_opposite _ (edge_xor_opposite G hL hn hk (show j + 1 ≤ k from hj) c)
theorem covariantSmoothingDeriv_add (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (hV : V ∈ smallComplexFields L n k j)
    {B B' : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) (hB' : B' ∈ complexEdgeForms L n k j) :
    covariantSmoothingDeriv V (B + B') =
      covariantSmoothingDeriv V B + covariantSmoothingDeriv V B' := by
  obtain ⟨_, h₂, _, _⟩ := G.linearity L hL n k j hn hj V hV
  obtain ⟨e₁, e₂⟩ := h₂ B hB B' hB' 1
  rw [one_smul, one_smul] at e₁ e₂
  unfold covariantSmoothingDeriv
  rw [e₁, e₂, covDiff_add]
  abel
theorem covariantSmoothingDeriv_smul (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (hV : V ∈ smallComplexFields L n k j) (z : ℂ)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    covariantSmoothingDeriv V (z • B) = z • covariantSmoothingDeriv V B := by
  obtain ⟨_, h₂, _, _⟩ := G.linearity L hL n k j hn hj V hV
  obtain ⟨e₁, e₂⟩ := h₂ B hB B hB (z - 1)
  have e : (z - 1) • B + B = z • B := by
    rw [sub_smul, one_smul, sub_add_cancel]
  have e' : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (x : E), (z - 1) • x + x = z • x := by
    intro E _ _ x
    rw [sub_smul, one_smul, sub_add_cancel]
  rw [e, e'] at e₁ e₂
  unfold covariantSmoothingDeriv
  rw [e₁, e₂, covDiff_smul, smul_add]
theorem adjointCubeAverage_add (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) (hV : V ∈ smallComplexFields L n k j) {l l' : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (hl' : ∀ x, l' x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V (l + l') = adjointCubeAverage V l + adjointCubeAverage V l' := by
  obtain ⟨_, _, _, h₄⟩ := G.linearity L hL n k j hn hj V hV
  have e := (h₄ l l' hl hl' 1).2
  rwa [one_smul, one_smul] at e
theorem adjointCubeAverage_smul (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) (hV : V ∈ smallComplexFields L n k j) (z : ℂ) {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V (z • l) = z • adjointCubeAverage V l := by
  obtain ⟨_, _, _, h₄⟩ := G.linearity L hL n k j hn hj V hV
  have e := (h₄ l l hl hl (z - 1)).2
  have e' : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (x : E), (z - 1) • x + x = z • x := by
    intro E _ _ x
    rw [sub_smul, one_smul, sub_add_cancel]
  rwa [e', e'] at e
theorem adjointCubeAverage_mem (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) (hV : V ∈ smallComplexFields L n k j) {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (y : Vertex L n k (j + 1)) :
    adjointCubeAverage V l y ∈ ComplexMatrix2.traceless := by
  obtain ⟨_, _, h₃, _⟩ := G.linearity L hL n k j hn hj V hV
  exact (h₃ l hl).2 y
abbrev freeStep (L n k j : ℕ) (B : Edge L n k j → ComplexMatrix2) :
    Edge L n k (j + 1) → ComplexMatrix2 :=
  (L : ℝ)⁻¹ • crossingSmoothing L n k j B
abbrev stepDeviation (V B : Edge L n k j → ComplexMatrix2) : Edge L n k (j + 1) → ComplexMatrix2 :=
  (L : ℝ)⁻¹ • (covariantSmoothingDeriv V B - crossingSmoothing L n k j B)
theorem ofReal_smul_fun {ι : Type} (t : ℝ) (Y : ι → ComplexMatrix2) : t • Y = (t : ℂ) • Y := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
theorem freeStep_tracelessOnPositive (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) : TracelessOnPositive (freeStep L n k j B) := fun c hc => by
  have := finite_vertex G hL hn hj.le
  unfold freeStep
  rw [ofReal_smul_fun]
  exact ComplexMatrix2.traceless.smul_mem _
    (crossingSmoothing_tracelessOnPositive
      (value_mem_traceless (edge_xor_opposite G hL hn hk hj.le) hB) c hc)
theorem stepDeviation_tracelessOnPositive (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (hV : V ∈ smallComplexFields L n k j)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    TracelessOnPositive (stepDeviation V B) := fun c hc => by
  have := finite_vertex G hL hn hj.le
  unfold stepDeviation
  rw [ofReal_smul_fun]
  exact ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.sub_mem
    ((covariantSmoothingDeriv_mem G hL hn hk hj hV hB).1 c hc)
    (crossingSmoothing_tracelessOnPositive
      (value_mem_traceless (edge_xor_opposite G hL hn hk hj.le) hB) c hc))
theorem freeStep_add [Finite (Vertex L n k j)] (X Y : Edge L n k j → ComplexMatrix2) :
    freeStep L n k j (X + Y) = freeStep L n k j X + freeStep L n k j Y := by
  unfold freeStep
  rw [crossingSmoothing_add, smul_add]
theorem freeStep_smul [Finite (Vertex L n k j)] (z : ℂ) (X : Edge L n k j → ComplexMatrix2) :
    freeStep L n k j (z • X) = z • freeStep L n k j X := by
  unfold freeStep
  rw [crossingSmoothing_smul, ofReal_smul_fun, ofReal_smul_fun, smul_comm]
theorem stepDeviation_add (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) (hV : V ∈ smallComplexFields L n k j) {X Y : Edge L n k j → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n k j) (hY : Y ∈ complexEdgeForms L n k j) :
    stepDeviation V (X + Y) = stepDeviation V X + stepDeviation V Y := by
  have := finite_vertex G hL hn hj.le
  unfold stepDeviation
  rw [covariantSmoothingDeriv_add G hL hn hj hV hX hY, crossingSmoothing_add, ← smul_add,
    add_sub_add_comm]
theorem stepDeviation_smul (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) (hV : V ∈ smallComplexFields L n k j) (z : ℂ) {X : Edge L n k j → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n k j) :
    stepDeviation V (z • X) = z • stepDeviation V X := by
  have := finite_vertex G hL hn hj.le
  unfold stepDeviation
  rw [covariantSmoothingDeriv_smul G hL hn hj hV z hX, crossingSmoothing_smul, ← smul_sub,
    ofReal_smul_fun, ofReal_smul_fun, smul_comm]
theorem vertexDeviation_add (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) (hV : V ∈ smallComplexFields L n k j) {X Y : Vertex L n k j → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (hY : ∀ x, Y x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V (X + Y) - vertexSmoothing L n k j (X + Y) =
      (adjointCubeAverage V X - vertexSmoothing L n k j X) +
        (adjointCubeAverage V Y - vertexSmoothing L n k j Y) := by
  have := finite_vertex G hL hn hj.le
  rw [adjointCubeAverage_add G hL hn hj hV hX hY, vertexSmoothing_add, add_sub_add_comm]
theorem vertexDeviation_smul (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) (hV : V ∈ smallComplexFields L n k j) (z : ℂ)
    {X : Vertex L n k j → ComplexMatrix2} (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V (z • X) - vertexSmoothing L n k j (z • X) =
      z • (adjointCubeAverage V X - vertexSmoothing L n k j X) := by
  have := finite_vertex G hL hn hj.le
  rw [adjointCubeAverage_smul G hL hn hj hV z hX, vertexSmoothing_smul, smul_sub]
theorem freeStep_isComplexLinear (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) (hj : j < k) :
    IsComplexLinear
      ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (freeStep L n k j)) := by
  have := finite_vertex G hL hn hj.le
  refine isComplexLinear_mapOnCoeffs (edgePauliCoordinates_faithful G hL hn hk hj.le)
    (fun X => TracelessOnPositive (L := L) (n := n) (k := k) X)
    (fun _ _ hX hY => edge_coeffs_add hX hY) (fun z _ hX => edge_coeffs_smul z hX)
    (fun X hX => freeStep_tracelessOnPositive G hL hn hk hj hX) ?_ ?_
  · intro X _ Y _
    exact freeStep_add X Y
  · intro z X _
    exact freeStep_smul z X
theorem stepDeviation_isComplexLinear (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (hV : V ∈ smallComplexFields L n k j) :
    IsComplexLinear
      ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (stepDeviation V)) := by
  have := finite_vertex G hL hn hj.le
  refine isComplexLinear_mapOnCoeffs (edgePauliCoordinates_faithful G hL hn hk hj.le)
    (fun X => TracelessOnPositive (L := L) (n := n) (k := k) X)
    (fun _ _ hX hY => edge_coeffs_add hX hY) (fun z _ hX => edge_coeffs_smul z hX)
    (fun X hX => stepDeviation_tracelessOnPositive G hL hn hk hj hV hX) ?_ ?_
  · intro X hX Y hY
    exact stepDeviation_add G hL hn hj hV hX hY
  · intro z X hX
    exact stepDeviation_smul G hL hn hj hV z hX
theorem vertexDeviation_isComplexLinear (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (hV : V ∈ smallComplexFields L n k j) :
    IsComplexLinear ((vertexCoordinate (Vertex L n k j)).mapOnCoeffs
      (vertexCoordinate (Vertex L n k (j + 1)))
      fun l => adjointCubeAverage V l - vertexSmoothing L n k j l) := by
  have := finite_vertex G hL hn hj.le
  refine isComplexLinear_mapOnCoeffs (vertexCoordinate_faithful G hL hn hj.le)
    (fun X : Vertex L n k (j + 1) → ComplexMatrix2 => ∀ x, X x ∈ ComplexMatrix2.traceless)
    (fun _ _ hX hY => vertex_coeffs_add hX hY) (fun z _ hX => vertex_coeffs_smul z hX)
    (fun X hX y => ComplexMatrix2.traceless.sub_mem
      (adjointCubeAverage_mem G hL hn hj hV (vertex_mem_complexSubmodule_iff.1 hX) y)
      (vertexSmoothing_mem (vertex_mem_complexSubmodule_iff.1 hX) y)) ?_ ?_
  · intro X hX Y hY
    exact vertexDeviation_add G hL hn hj hV (vertex_mem_complexSubmodule_iff.1 hX)
      (vertex_mem_complexSubmodule_iff.1 hY)
  · intro z X hX
    exact vertexDeviation_smul G hL hn hj hV z (vertex_mem_complexSubmodule_iff.1 hX)
theorem vertexSmoothing_isComplexLinear (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) :
    IsComplexLinear ((vertexCoordinate (Vertex L n k j)).mapOnCoeffs
      (vertexCoordinate (Vertex L n k (j + 1))) (vertexSmoothing L n k j)) := by
  have := finite_vertex G hL hn hj.le
  refine isComplexLinear_mapOnCoeffs (vertexCoordinate_faithful G hL hn hj.le)
    (fun X : Vertex L n k (j + 1) → ComplexMatrix2 => ∀ x, X x ∈ ComplexMatrix2.traceless)
    (fun _ _ hX hY => vertex_coeffs_add hX hY) (fun z _ hX => vertex_coeffs_smul z hX)
    (fun X hX y => vertexSmoothing_mem (vertex_mem_complexSubmodule_iff.1 hX) y) ?_ ?_
  · intro X _ Y _
    exact vertexSmoothing_add X Y
  · intro z X _
    exact vertexSmoothing_smul z X
end Step
theorem sum_meshAt_le (hL : IsAdmissibleBlockingFactor L) (k m : ℕ) :
    ∑ i ∈ Finset.range m, meshAt L k i ≤ meshAt L k m := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledNormBounds.sum_meshAt_le <;> assumption
theorem prod_one_add_le_exp (hL : IsAdmissibleBlockingFactor L) {C A : ℝ} (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hA' : A ≤ 1 / 41) {s : ℕ → ℝ} (hs : ∀ i, 0 ≤ s i)
    (hb : ∀ i < k, s i ≤ 20 * meshAt L k i * A) :
    ∏ i ∈ Finset.range k, (1 + C * s i) ≤ Real.exp (30 * C) := by
  have h₁ : ∏ i ∈ Finset.range k, (1 + C * s i) ≤ ∏ i ∈ Finset.range k, Real.exp (C * s i) := by
    refine Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_
    · have := mul_nonneg hC (hs i)
      linarith
    · have := Real.add_one_le_exp (C * s i)
      linarith
  refine h₁.trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  have h₂ : ∑ i ∈ Finset.range k, C * s i ≤
      ∑ i ∈ Finset.range k, C * (20 * A) * meshAt L k i := by
    refine Finset.sum_le_sum fun i hi => ?_
    have := mul_le_mul_of_nonneg_left (hb i (Finset.mem_range.1 hi)) hC
    nlinarith
  have h₂' := Finset.mul_sum (Finset.range k) (meshAt L k) (C * (20 * A))
  have h₃ := sum_meshAt_le hL k k
  have h₄ : meshAt L k k = 1 := by
    simp [meshAt]
  rw [h₄] at h₃
  have h₅ : 0 ≤ C * (20 * A) := by positivity
  have h₆ := mul_le_mul_of_nonneg_left h₃ h₅
  have h₇ : C * (20 * A) ≤ 30 * C := by nlinarith
  linarith
theorem smoothingStepConstant_nonneg (L : ℕ) : 0 ≤ smoothingStepConstant L := by
  unfold smoothingStepConstant
  positivity
theorem distFromOne_nonneg {j : ℕ} (V : Edge L n k j → ComplexMatrix2) : 0 ≤ _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V :=
  ENNReal.toReal_nonneg
theorem distFromOne_le {j : ℕ} {V : Edge L n k j → ComplexMatrix2} {x : ℝ} (hx : 0 ≤ x)
    (h : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) ≤ x) : _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V ≤ x :=
  ENNReal.toReal_le_of_le_ofReal hx (iSup_le fun b => ENNReal.ofReal_le_ofReal (h b))
theorem l1NormVec_zero : TorusMetric.l1NormVec (0 : Fin 4 → ℝ) = 0 := by
  simp [TorusMetric.l1NormVec]
structure IteratesSmall (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2) : Prop where
  mem_fields : ∀ j < k, PeriodicLattice.complexBlockFieldAtLevel j U ∈
    fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  norm_sub_one_lt : ∀ j < k, ∀ b : Edge L n k j,
    ComplexMatrix2.operatorNorm (PeriodicLattice.complexBlockFieldAtLevel j U b - 1) <
      polydiscRadius L / 2
theorem IteratesSmall.mem_smallComplexFields (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    {U : Edge L n k 0 → ComplexMatrix2} (h : IteratesSmall L n k U) {j : ℕ} (hj : j < k) :
    PeriodicLattice.complexBlockFieldAtLevel j U ∈ smallComplexFields L n k j := by
  refine ⟨h.mem_fields j hj, fun b => ?_⟩
  have h₁ := h.norm_sub_one_lt j hj b
  have h₂ := (G.nearIdentity.1 L hL).2.2.pos
  linarith
abbrev invScale (L : ℕ) : ℂ := (((L : ℝ)⁻¹ : ℝ) : ℂ)
theorem iterCovariantDeriv_bound (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) {U : Edge L n k 0 → ComplexMatrix2} (h : IteratesSmall L n k U)
    (f : (edgePauliCoordinates L n k 0).Index → ℂ) :
    iterCovariantDeriv L n k U k ((edgePauliCoordinates L n k 0).ofCoeffs f) ∈
        complexEdgeForms L n k k ∧
      wNorm (meshWeight (meshAt L k k))
        (invScale L ^ k • (edgePauliCoordinates L n k k).coeffs
          (iterCovariantDeriv L n k U k ((edgePauliCoordinates L n k 0).ofCoeffs f))) ≤
      (∏ i ∈ Finset.range k, (1 + smoothingStepConstant L *
        distFromOne (PeriodicLattice.complexBlockFieldAtLevel (L := L) (m := n) (K := k) i U))) *
        wNorm (meshWeight (meshAt L k 0)) f := by
  refine iterate_norm_le_prod (r := fun j => edgePauliCoordinates L n k j) (a := meshAt L k)
    (e := fun i => smoothingStepConstant L *
      distFromOne (PeriodicLattice.complexBlockFieldAtLevel (L := L) (m := n) (K := k) i U))
    (s := invScale L) (fun j hj => edgePauliCoordinates_faithful G hL hn hk hj) (meshAt_pos hL k)
    (fun i => mul_nonneg (smoothingStepConstant_nonneg L) (distFromOne_nonneg _))
    (fun j => covariantSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel j U))
    (fun j => stepDeviation (PeriodicLattice.complexBlockFieldAtLevel j U))
    (fun j => freeStep L n k j)
    (fun j => iterCovariantDeriv L n k U j)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun j hj X hX => covariantSmoothingDeriv_mem G hL hn hk hj
      (h.mem_smallComplexFields G hL hj) hX)
    (fun j hj z X hX => covariantSmoothingDeriv_smul G hL hn hj
      (h.mem_smallComplexFields G hL hj) z hX)
    ?_ ?_ ?_ k le_rfl f
  · intro j hj g
    have := (edgePauliCoordinates_faithful G hL hn hk hj.le).finite
    have := (edgePauliCoordinates_faithful G hL hn hk (show j + 1 ≤ k from hj)).finite
    have hs := G.nearFree L hL n k j hn hj _ (h.mem_fields j hj) (h.norm_sub_one_lt j hj)
    exact wNorm_apply_le_of_wOpNorm_le (meshAt_pos hL k j) (meshAt_pos hL k (j + 1))
      (mul_nonneg (smoothingStepConstant_nonneg L) (distFromOne_nonneg _))
      (stepDeviation_isComplexLinear G hL hn hk hj (h.mem_smallComplexFields G hL hj)) hs.1.2 g
  · intro j hj g
    have := (edgePauliCoordinates_faithful G hL hn hk hj.le).finite
    have := (edgePauliCoordinates_faithful G hL hn hk (show j + 1 ≤ k from hj)).finite
    have hlin := freeStep_isComplexLinear G hL hn hk hj
    have hc := (((G.contraction L hL k hk).2.1 n hn).2.1 j hj).1.2
    have e : applyKernel ((edgePauliCoordinates L n k j).kernelOfBasisImages (edgePauliCoordinates L n k (j + 1))
        (freeStep L n k j)) = (edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
        (freeStep L n k j) := funext (applyKernel_kernelOfBasisImages hlin)
    have hc' : wOpNorm (meshWeight (meshAt L k j))
        (meshWeight (meshAt L k (j + 1)))
        univ ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
          (freeStep L n k j)) ≤ ENNReal.ofReal 1 := by
      rw [← e]
      refine hc.trans (le_of_eq ?_)
      rw [l1NormVec_zero]
      simp
    have := wNorm_apply_le_of_wOpNorm_le (meshAt_pos hL k j) (meshAt_pos hL k (j + 1))
      zero_le_one hlin hc' g
    simpa using this
  · intro j hj X hX
    have e : invScale L • covariantSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel j U) X =
        stepDeviation (PeriodicLattice.complexBlockFieldAtLevel j U) X + freeStep L n k j X := by
      unfold stepDeviation freeStep
      rw [← smul_add, sub_add_cancel, ofReal_smul_fun]
    exact (congrArg (edgePauliCoordinates L n k (j + 1)).coeffs e).trans (edge_coeffs_add
      (stepDeviation_tracelessOnPositive G hL hn hk hj (h.mem_smallComplexFields G hL hj) hX)
      (freeStep_tracelessOnPositive G hL hn hk hj hX))
theorem iterAdjointCubeAverage_bound (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {U : Edge L n k 0 → ComplexMatrix2} (h : IteratesSmall L n k U)
    (f : (vertexCoordinate (Vertex L n k 0)).Index → ℂ) :
    iterAdjointCubeAverage L n k U k ((vertexCoordinate (Vertex L n k 0)).ofCoeffs f) ∈
        (vertexCoordinate (Vertex L n k k)).space.complexSubmodule ∧
      wNorm (meshWeight (meshAt L k k))
        ((1 : ℂ) ^ k • (vertexCoordinate (Vertex L n k k)).coeffs
          (iterAdjointCubeAverage L n k U k ((vertexCoordinate (Vertex L n k 0)).ofCoeffs f))) ≤
      (∏ i ∈ Finset.range k, (1 + smoothingStepConstant L *
        distFromOne (PeriodicLattice.complexBlockFieldAtLevel (L := L) (m := n) (K := k) i U))) *
        wNorm (meshWeight (meshAt L k 0)) f := by
  refine iterate_norm_le_prod (r := fun j => vertexCoordinate (Vertex L n k j)) (a := meshAt L k)
    (e := fun i => smoothingStepConstant L *
      distFromOne (PeriodicLattice.complexBlockFieldAtLevel (L := L) (m := n) (K := k) i U))
    (s := 1) (fun j hj => vertexCoordinate_faithful G hL hn hj) (meshAt_pos hL k)
    (fun i => mul_nonneg (smoothingStepConstant_nonneg L) (distFromOne_nonneg _))
    (fun j => adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U))
    (fun j l => adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U) l -
      vertexSmoothing L n k j l)
    (fun j => vertexSmoothing L n k j)
    (fun j => iterAdjointCubeAverage L n k U j)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun j hj X hX => vertex_mem_complexSubmodule_iff.2 (adjointCubeAverage_mem G hL hn hj
      (h.mem_smallComplexFields G hL hj) (vertex_mem_complexSubmodule_iff.1 hX)))
    (fun j hj z X hX => adjointCubeAverage_smul G hL hn hj (h.mem_smallComplexFields G hL hj) z
      (vertex_mem_complexSubmodule_iff.1 hX))
    ?_ ?_ ?_ k le_rfl f
  · intro j hj g
    have : Finite (vertexCoordinate (Vertex L n k j)).Place :=
      (vertexCoordinate_faithful G hL hn hj.le).finite
    have : Finite (vertexCoordinate (Vertex L n k (j + 1))).Place :=
      (vertexCoordinate_faithful G hL hn (show j + 1 ≤ k from hj)).finite
    have hs := G.nearFree L hL n k j hn hj _ (h.mem_fields j hj) (h.norm_sub_one_lt j hj)
    exact wNorm_apply_le_of_wOpNorm_le (meshAt_pos hL k j) (meshAt_pos hL k (j + 1))
      (mul_nonneg (smoothingStepConstant_nonneg L) (distFromOne_nonneg _))
      (vertexDeviation_isComplexLinear G hL hn hj (h.mem_smallComplexFields G hL hj)) hs.2.2 g
  · intro j hj g
    have : Finite (vertexCoordinate (Vertex L n k j)).Place :=
      (vertexCoordinate_faithful G hL hn hj.le).finite
    have : Finite (vertexCoordinate (Vertex L n k (j + 1))).Place :=
      (vertexCoordinate_faithful G hL hn (show j + 1 ≤ k from hj)).finite
    have hlin := vertexSmoothing_isComplexLinear G hL hn hj
    have hc := (((G.contraction L hL k hk).2.1 n hn).2.1 j hj).2.2
    have e : applyKernel ((vertexCoordinate (Vertex L n k j)).kernelOfBasisImages
        (vertexCoordinate (Vertex L n k (j + 1))) (vertexSmoothing L n k j)) =
        (vertexCoordinate (Vertex L n k j)).mapOnCoeffs (vertexCoordinate (Vertex L n k (j + 1)))
          (vertexSmoothing L n k j) := funext (applyKernel_kernelOfBasisImages hlin)
    have hc' : wOpNorm (meshWeight (meshAt L k j))
        (meshWeight (meshAt L k (j + 1)))
        univ ((vertexCoordinate (Vertex L n k j)).mapOnCoeffs (vertexCoordinate (Vertex L n k (j + 1)))
          (vertexSmoothing L n k j)) ≤ ENNReal.ofReal 1 := by
      rw [← e]
      refine hc.trans (le_of_eq ?_)
      rw [l1NormVec_zero]
      simp
    have := wNorm_apply_le_of_wOpNorm_le (meshAt_pos hL k j) (meshAt_pos hL k (j + 1))
      zero_le_one hlin hc' g
    simpa using this
  · intro j hj X hX
    have hX' := vertex_mem_complexSubmodule_iff.1 hX
    have e : (1 : ℂ) • adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U) X =
        (adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U) X -
          vertexSmoothing L n k j X) + vertexSmoothing L n k j X := by
      rw [one_smul, sub_add_cancel]
    have := finite_vertex (k := k) G hL hn hj.le
    exact (congrArg (vertexCoordinate (Vertex L n k (j + 1))).coeffs e).trans (vertex_coeffs_add
      (fun y => ComplexMatrix2.traceless.sub_mem
        (adjointCubeAverage_mem G hL hn hj (h.mem_smallComplexFields G hL hj) hX' y)
        (vertexSmoothing_mem hX' y))
      (vertexSmoothing_mem hX'))
theorem finestMesh_eq_invScale_pow :
    ((finestMesh L k : ℝ) : ℂ) = invScale L ^ k := by apply _root_.YangMills.DeltaSharedProofs.p502271 <;> assumption
theorem torusOpNormLE_Q (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) {U : Edge L n k 0 → ComplexMatrix2} (h : IteratesSmall L n k U) {c : ℝ}
    (hc : 0 ≤ c)
    (hprod : ∏ i ∈ Finset.range k, (1 + smoothingStepConstant L *
      distFromOne (PeriodicLattice.complexBlockFieldAtLevel (L := L) (m := n) (K := k) i U)) ≤ c) :
    TorusOpNormLE (finestMesh L k) (meshAt L k k) (rescaledOperators L n k U).Q c := by
  have hUs : U ∈ smallIterateFields L n k :=
    ⟨h.mem_fields 0 (by omega), fun j hj => h.mem_smallComplexFields G hL hj⟩
  have hK := (((G.kernels L hL k hk).1 n hn).2.2.2 U hUs).1
  have hcol : ∀ g, (edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
      (fun B => finestMesh L k • iterCovariantDeriv L n k U k B) g =
      invScale L ^ k • (edgePauliCoordinates L n k k).coeffs
        (iterCovariantDeriv L n k U k ((edgePauliCoordinates L n k 0).ofCoeffs g)) := by
    intro g
    have hm := (iterCovariantDeriv_bound G hL hn hk h g).1
    have e₁ := edge_coeffs_smul ((finestMesh L k : ℝ) : ℂ) hm.1
    rw [← ofReal_smul_fun, finestMesh_eq_invScale_pow] at e₁
    exact e₁
  have hg : Represents (((finestMesh L k : ℝ) : ℂ) •
      PauliComponentsOfSymmetricKernel.kernel (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k)
        (iterCovariantDeriv L n k U k))
      ((edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
        fun B => finestMesh L k • iterCovariantDeriv L n k U k B) := by
    have h₁ := hK.smul_represents ((finestMesh L k : ℝ) : ℂ)
    have e : ((finestMesh L k : ℝ) : ℂ) • (edgePauliCoordinates L n k 0).mapOnCoeffs
        (edgePauliCoordinates L n k k) (iterCovariantDeriv L n k U k) =
        (edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
          fun B => finestMesh L k • iterCovariantDeriv L n k U k B := by
      funext g
      rw [hcol g, ← finestMesh_eq_invScale_pow]
      rfl
    rwa [e] at h₁
  have hQ : Represents (rescaledOperators L n k U).Q
      ((edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
        fun B => finestMesh L k • iterCovariantDeriv L n k U k B) :=
    Classical.epsilon_spec (⟨_, hg⟩ : ∃ T, Represents T _)
  have := (edgePauliCoordinates_faithful G hL hn hk (le_refl k)).finite
  have hfin : Finite (PositiveEdge L n k k) := this
  refine torusOpNormLE_of_bound hc fun g => ?_
  have e₃ := (hQ g).2.trans (hcol g)
  rw [e₃]
  exact (iterCovariantDeriv_bound G hL hn hk h g).2.trans
    (mul_le_mul_of_nonneg_right hprod (wNorm_nonneg _ _))
theorem torusOpNormLE_R (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) {U : Edge L n k 0 → ComplexMatrix2} (h : IteratesSmall L n k U) {c : ℝ}
    (hc : 0 ≤ c)
    (hprod : ∏ i ∈ Finset.range k, (1 + smoothingStepConstant L *
      distFromOne (PeriodicLattice.complexBlockFieldAtLevel (L := L) (m := n) (K := k) i U)) ≤ c) :
    TorusOpNormLE (finestMesh L k) (meshAt L k k) (rescaledOperators L n k U).R c := by
  have hUs : U ∈ smallIterateFields L n k :=
    ⟨h.mem_fields 0 (by omega), fun j hj => h.mem_smallComplexFields G hL hj⟩
  have hK := (((G.kernels L hL k hk).1 n hn).2.2.2 U hUs).2
  have := finite_vertex (k := k) G hL hn (le_refl k)
  refine torusOpNormLE_of_bound hc fun g => ?_
  have e₃ : applyKernel (rescaledOperators L n k U).R g = (1 : ℂ) ^ k •
      (vertexCoordinate (Vertex L n k k)).coeffs
        (iterAdjointCubeAverage L n k U k ((vertexCoordinate (Vertex L n k 0)).ofCoeffs g)) := by
    rw [one_pow, one_smul]
    exact (hK.represents g).2
  rw [e₃]
  exact (iterAdjointCubeAverage_bound G hL hn hk h g).2.trans
    (mul_le_mul_of_nonneg_right hprod (wNorm_nonneg _ _))
theorem operatorNormsBounded_of_hypotheses (G : Hypotheses) : OperatorNormsBounded := by
  intro L hL n k hn hk a _ hsup hit
  have hS : IteratesSmall L n k (remainderGaugeField a) := ⟨hit.mem_fields, hit.norm_sub_one_lt⟩
  have hA0 : 0 ≤ (maxOperatorNorm a).toReal := ENNReal.toReal_nonneg
  have hA1 : (maxOperatorNorm a).toReal ≤ 1 / 41 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) hsup
  have hprod := prod_one_add_le_exp (k := k) hL (smoothingStepConstant_nonneg L) hA0 hA1
    (s := fun i => _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne (PeriodicLattice.complexBlockFieldAtLevel (L := L) (m := n) (K := k) i
      (remainderGaugeField a)))
    (fun i => distFromOne_nonneg _)
    (fun i hi => distFromOne_le (mul_nonneg (mul_nonneg (by norm_num) (meshAt_pos hL k i).le) hA0)
      fun b => hit.norm_sub_one_le i hi b)
  exact ⟨torusOpNormLE_Q G hL hn hk hS (Real.exp_pos _).le hprod,
    torusOpNormLE_R G hL hn hk hS (Real.exp_pos _).le hprod⟩
end Tower
theorem operatorNormsBounded (h₁ : SmoothingStepsNearFree.Claim)
    (h₂ : SmoothingContraction.Claim) (h₃ : ThreeMapKernels.Claim)
    (h₄ : StepMapsComplexLinear.Claim)
    (h₅ : ComplexMeanLiesInComplexGaugeGroup)
    (h₆ : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (h₇ : ComplexMatrix2.ConjugationPreservesTraceless)
    (h₈ : PeriodicLattice.BondEndpointsOrientation.Statement)
    (h₉ : BondSetFields.ProductStructureHolds) : OperatorNormsBounded :=
  operatorNormsBounded_of_hypotheses ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
end YangMills.Construction.Tower.RescaledNormBounds
end
