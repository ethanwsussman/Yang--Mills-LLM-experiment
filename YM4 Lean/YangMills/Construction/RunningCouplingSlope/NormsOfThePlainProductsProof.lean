import YangMills.Construction.RunningCouplingSlope.LogarithmsOfThePlainIteratesProof
import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProducts
import YangMills.Construction.RunningCouplingSlope.PlainAverageNearOne
import YangMills.Construction.RunningCouplingSlope.PlainDifferentialIsLinear
import YangMills.Construction.RunningCouplingSlope.PlainStepNearTheFreeStep
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOnTheSidesProof
import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanKernelNormProof
open Matrices
open Tower
open PeriodicOperators (KernelMatrix applyKernel wOpNorm wNorm NormSummable wUnitBall Represents)
open Tower.SmoothingContraction (TorusOpNormLE)
open Tower.SmoothingStepsNearFree (MapNormLE distFromOne)
section Norms
variable {σ σ' : Type}
private def toEuclidean (f : Fin 3 × σ → ℂ) : EuclideanSpace ℂ (Fin 3 × σ) := WithLp.toLp 2 f
private theorem wNorm_eq [Fintype σ] {a : ℝ} (ha : 0 < a) (f : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a) f = a ^ 2 * ‖toEuclidean f‖ := by
  unfold PeriodicOperators.wNorm
  rw [tsum_fintype, EuclideanSpace.norm_eq]
  have e : ∑ i, meshWeight a i * ‖f i‖ ^ 2 = (a ^ 2) ^ 2 * ∑ i, ‖toEuclidean f i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e₁ : toEuclidean f i = f i := rfl
    rw [e₁]
    simp only [meshWeight]
    ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
private theorem wNorm_add_le [Finite σ] {a : ℝ} (ha : 0 < a) (f g : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a) (f + g) ≤ wNorm (meshWeight a) f + wNorm (meshWeight a) g := by
  cases nonempty_fintype σ
  rw [wNorm_eq ha, wNorm_eq ha, wNorm_eq ha, ← mul_add]
  have e : toEuclidean (f + g) = toEuclidean f + toEuclidean g := rfl
  rw [e]
  exact mul_le_mul_of_nonneg_left (_root_.norm_add_le _ _) (by positivity)
abbrev _root_.YangMills.SharedProofs.p20251 := @wNorm_add_le
private theorem wNorm_smul [Finite σ] {a : ℝ} (ha : 0 < a) (z : ℂ) (f : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a) (z • f) = ‖z‖ * wNorm (meshWeight a) f := by
  cases nonempty_fintype σ
  rw [wNorm_eq ha, wNorm_eq ha]
  have e : toEuclidean (z • f) = z • toEuclidean f := rfl
  rw [e, _root_.norm_smul]
  ring
abbrev _root_.YangMills.SharedProofs.p8315 := @wNorm_smul
private theorem wNorm_nonneg (a : ℝ) (f : Fin 3 × σ → ℂ) : 0 ≤ wNorm (meshWeight a) f :=
  Real.sqrt_nonneg _
private theorem eq_zero_of_wNorm_eq_zero [Finite σ] {a : ℝ} (ha : 0 < a) {f : Fin 3 × σ → ℂ}
    (h : wNorm (meshWeight a) f = 0) : f = 0 := by
  cases nonempty_fintype σ
  rw [wNorm_eq ha] at h
  have h₂ : a ^ 2 ≠ 0 := by positivity
  have e := (mul_eq_zero.1 h).resolve_left h₂
  have e' : toEuclidean f = 0 := norm_eq_zero.1 e
  funext i
  exact congrArg (fun x : EuclideanSpace ℂ (Fin 3 × σ) => x i) e'
abbrev _root_.YangMills.SharedProofs.p4646 := @eq_zero_of_wNorm_eq_zero
private theorem normSummable_of_finite [Finite σ] (w : Fin 3 × σ → ℝ) (f : Fin 3 × σ → ℂ) :
    NormSummable w f := by
  classical
  cases nonempty_fintype σ
  exact (hasSum_fintype _).summable
abbrev _root_.YangMills.SharedProofs.p57614 := @normSummable_of_finite
private structure IsComplexLinear (M : (Fin 3 × σ → ℂ) → Fin 3 × σ' → ℂ) : Prop where
  map_add' : ∀ f g, M (f + g) = M f + M g
  map_smul' : ∀ (z : ℂ) f, M (z • f) = z • M f
private theorem le_of_wOpNorm_le [Finite σ] [Finite σ'] {a a' c : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (hc : 0 ≤ c) {M : (Fin 3 × σ → ℂ) → Fin 3 × σ' → ℂ} (hM : IsComplexLinear M)
    (h : wOpNorm (meshWeight a) (meshWeight a') univ M ≤ ENNReal.ofReal c)
    (f : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a') (M f) ≤ c * wNorm (meshWeight a) f := by
  by_cases h0 : wNorm (meshWeight a) f = 0
  · have e := eq_zero_of_wNorm_eq_zero ha h0
    have e₀ : M 0 = 0 := by
      have := hM.map_smul' 0 0
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
  rw [hM.map_smul', wNorm_smul ha', Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 hpos.le)] at h₂
  have h₃ := mul_le_mul_of_nonneg_left h₂ hpos.le
  rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm t c] at h₃
private theorem opNormLE_of_bound [Finite σ'] {a a' c : ℝ} (hc : 0 ≤ c)
    {T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')}
    (hb : ∀ f, wNorm (meshWeight a') (applyKernel T f) ≤ c * wNorm (meshWeight a) f) :
    TorusOpNormLE a a' T c := by
  refine ⟨fun f _ => normSummable_of_finite _ _, iSup₂_le fun f hf => ?_⟩
  refine ENNReal.ofReal_le_ofReal ((hb f).trans ?_)
  exact (mul_le_mul_of_nonneg_left hf.2.2 hc).trans (by simp)
abbrev _root_.YangMills.SharedProofs.p4978 := @opNormLE_of_bound
end Norms
private structure ReadsFaithfully (r : PauliComponentsOfSymmetricKernel) : Prop where
  finite : Finite r.Place
  mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  coeffs_ofCoeffs : ∀ c, r.coeffs (r.ofCoeffs c) = c
  ofCoeffs_coeffs : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  ofCoeffs_add : ∀ c c', r.ofCoeffs (c + c') = r.ofCoeffs c + r.ofCoeffs c'
  ofCoeffs_smul : ∀ (z : ℂ) c, r.ofCoeffs (z • c) = z • r.ofCoeffs c
private theorem ReadsFaithfully.coeffs_smul {r : PauliComponentsOfSymmetricKernel} (h : ReadsFaithfully r) (z : ℂ)
    {f : r.space.index → ComplexMatrix2} (hf : f ∈ r.space.complexSubmodule) :
    r.coeffs (z • f) = z • r.coeffs f := by
  have e : z • f = r.ofCoeffs (z • r.coeffs f) := by
    rw [h.ofCoeffs_smul, h.ofCoeffs_coeffs f hf]
  rw [e, h.coeffs_ofCoeffs]
private theorem applyKernel_basisImages {r r' : PauliComponentsOfSymmetricKernel} [Finite r.Place]
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hm : IsComplexLinear (r.mapOnCoeffs r' m)) (f : r.Index → ℂ) :
    applyKernel (r.kernelOfBasisImages r' m) f = r.mapOnCoeffs r' m f := by
  classical
  cases nonempty_fintype r.Place
  have hzero : r.mapOnCoeffs r' m 0 = 0 := by
    have := hm.map_smul' 0 0
    simpa using this
  have hsum : ∀ s : Finset r.Index, r.mapOnCoeffs r' m (∑ ι ∈ s, f ι • Pi.single ι (1 : ℂ)) =
      ∑ ι ∈ s, f ι • r.mapOnCoeffs r' m (Pi.single ι 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert ι s hι ih =>
      rw [Finset.sum_insert hι, Finset.sum_insert hι, hm.map_add', hm.map_smul', ih]
  have hf : f = ∑ ι, f ι • Pi.single ι (1 : ℂ) := by
    funext ι
    simp [Finset.sum_apply, Pi.single_apply]
  funext ι'
  conv_rhs => rw [hf, hsum]
  unfold PeriodicOperators.applyKernel PauliComponentsOfSymmetricKernel.kernelOfBasisImages
  rw [tsum_fintype, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ι _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
private theorem isComplexLinear_of {r r' : PauliComponentsOfSymmetricKernel} (hr : ReadsFaithfully r)
    (P : (r'.space.index → ComplexMatrix2) → Prop)
    (cadd : ∀ X Y, P X → P Y → r'.coeffs (X + Y) = r'.coeffs X + r'.coeffs Y)
    (csmul : ∀ (z : ℂ) X, P X → r'.coeffs (z • X) = z • r'.coeffs X)
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hP : ∀ X ∈ r.space.complexSubmodule, P (m X))
    (madd : ∀ X ∈ r.space.complexSubmodule, ∀ Y ∈ r.space.complexSubmodule, m (X + Y) = m X + m Y)
    (msmul : ∀ (z : ℂ), ∀ X ∈ r.space.complexSubmodule, m (z • X) = z • m X) :
    IsComplexLinear (r.mapOnCoeffs r' m) where
  map_add' f g := by
    show r'.coeffs (m (r.ofCoeffs (f + g))) = r'.coeffs (m (r.ofCoeffs f)) +
      r'.coeffs (m (r.ofCoeffs g))
    rw [hr.ofCoeffs_add, madd _ (hr.mem f) _ (hr.mem g),
      cadd _ _ (hP _ (hr.mem f)) (hP _ (hr.mem g))]
  map_smul' z f := by
    show r'.coeffs (m (r.ofCoeffs (z • f))) = z • r'.coeffs (m (r.ofCoeffs f))
    rw [hr.ofCoeffs_smul, msmul z _ (hr.mem f), csmul z _ (hP _ (hr.mem f))]
private theorem wNorm_product_le {r : ℕ → PauliComponentsOfSymmetricKernel} {a e : ℕ → ℝ} {k : ℕ} {s : ℂ}
    (hr : ∀ j ≤ k, ReadsFaithfully (r j)) (ha : ∀ j, 0 < a j) (he : ∀ j, 0 ≤ e j)
    (w d p : ∀ j, ((r j).space.index → ComplexMatrix2) → (r (j + 1)).space.index → ComplexMatrix2)
    (It : ∀ j, ((r 0).space.index → ComplexMatrix2) → (r j).space.index → ComplexMatrix2)
    (h0 : ∀ B, It 0 B = B) (hs : ∀ j < k, ∀ B, It (j + 1) B = w j (It j B))
    (wmem : ∀ j < k, ∀ X ∈ (r j).space.complexSubmodule, w j X ∈ (r (j + 1)).space.complexSubmodule)
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
private theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
private theorem pauliCombination_pauliCoeff {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by
  unfold pauliCoeff
  rw [dif_pos hX, dif_pos hY, dif_pos (ComplexMatrix2.traceless.add_mem hX hY)]
  exact congrFun (map_add OneLoop.pauliCoordinateEquiv ⟨X, hX⟩ ⟨Y, hY⟩) a
abbrev _root_.YangMills.SharedProofs.p106 := @pauliCoeff_add
private theorem pauliCoeff_smul (a : Fin 3) (z : ℂ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (z • X) = z * pauliCoeff a X := by
  unfold pauliCoeff
  rw [dif_pos hX, dif_pos (ComplexMatrix2.traceless.smul_mem z hX)]
  exact congrFun (map_smul OneLoop.pauliCoordinateEquiv z ⟨X, hX⟩) a
abbrev _root_.YangMills.SharedProofs.p5172 := @pauliCoeff_smul
private theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
private theorem real_smul_eq_complex_smul (t : ℝ) (X : ComplexMatrix2) : t • X = (t : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
end Coefficients
private theorem readsFaithfully_of {r : PauliComponentsOfSymmetricKernel} (fin : Finite r.Place)
    (mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule)
    (left : ∀ c, r.coeffs (r.ofCoeffs c) = c)
    (right : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f)
    (cadd : ∀ f ∈ r.space.complexSubmodule, ∀ g ∈ r.space.complexSubmodule,
      r.coeffs (f + g) = r.coeffs f + r.coeffs g)
    (csmul : ∀ (z : ℂ), ∀ f ∈ r.space.complexSubmodule, r.coeffs (z • f) = z • r.coeffs f) :
    ReadsFaithfully r where
  finite := fin
  mem := mem
  coeffs_ofCoeffs := left
  ofCoeffs_coeffs := right
  ofCoeffs_add c c' := by
    have e := cadd _ (mem c) _ (mem c')
    rw [left, left] at e
    rw [← e, right _ (Submodule.add_mem _ (mem c) (mem c'))]
  ofCoeffs_smul z c := by
    have e := csmul z _ (mem c)
    rw [left] at e
    rw [← e, right _ (Submodule.smul_mem _ z (mem c))]
section Sites
variable {σ : Type}
private theorem vertex_mem_iff {f : σ → ComplexMatrix2} :
    f ∈ (vertexCoordinate σ).space.complexSubmodule ↔ ∀ x, f x ∈ ComplexMatrix2.traceless :=
  ⟨fun h x => Submodule.mem_pi.1 h x (mem_univ x), fun h => Submodule.mem_pi.2 fun x _ => h x⟩
private theorem vertex_coeffs_add {f g : σ → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) :
    (vertexCoordinate σ).coeffs (f + g) = (vertexCoordinate σ).coeffs f + (vertexCoordinate σ).coeffs g :=
  funext fun ι => pauliCoeff_add ι.1 (hf ι.2) (hg ι.2)
private theorem vertex_coeffs_smul (z : ℂ) {f : σ → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) :
    (vertexCoordinate σ).coeffs (z • f) = z • (vertexCoordinate σ).coeffs f :=
  funext fun ι => pauliCoeff_smul ι.1 z (hf ι.2)
private theorem vertexCoordinate_faithful [Finite σ] : ReadsFaithfully (vertexCoordinate σ) :=
  readsFaithfully_of (r := vertexCoordinate σ) (inferInstanceAs (Finite σ))
    (fun c => vertex_mem_iff.2 (ofPauliCoeffs_mem c))
    (fun c => funext fun ι => pauliCoeff_combination (fun a => c (a, ι.2)) ι.1)
    (fun _ hf => funext fun x => pauliCombination_pauliCoeff (vertex_mem_iff.1 hf x))
    (fun _ hf _ hg => vertex_coeffs_add (vertex_mem_iff.1 hf) (vertex_mem_iff.1 hg))
    (fun z _ hf => vertex_coeffs_smul z (vertex_mem_iff.1 hf))
end Sites
section Forms
variable {L n k j : ℕ}
private theorem extendOddly_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos h
private theorem extendOddly_neg (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : ¬ b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := if_neg h
private theorem extendOddly_opposite (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hx : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    extendOddly f b.opposite = -extendOddly f b := by
  rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [extendOddly_neg f h₂, extendOddly_pos f h₁]
    rfl
  · rw [extendOddly_pos f h₁, extendOddly_neg f h₂, neg_neg]
abbrev _root_.YangMills.SharedProofs.p17859 := @extendOddly_opposite
private def TracelessOnPositive (X : Edge L n k j → ComplexMatrix2) : Prop :=
  ∀ b : Edge L n k j, b.IsPositivelyOriented → X b ∈ ComplexMatrix2.traceless
private theorem edge_coeffs_add {X Y : Edge L n k j → ComplexMatrix2} (hX : TracelessOnPositive X)
    (hY : TracelessOnPositive Y) :
    (edgePauliCoordinates L n k j).coeffs (X + Y) =
      (edgePauliCoordinates L n k j).coeffs X + (edgePauliCoordinates L n k j).coeffs Y :=
  funext fun ι => pauliCoeff_add ι.1 (hX _ ι.2.2) (hY _ ι.2.2)
abbrev _root_.YangMills.DeltaSharedProofs.p501675 := @edge_coeffs_add
private theorem edge_coeffs_smul (z : ℂ) {X : Edge L n k j → ComplexMatrix2}
    (hX : TracelessOnPositive X) :
    (edgePauliCoordinates L n k j).coeffs (z • X) = z • (edgePauliCoordinates L n k j).coeffs X :=
  funext fun ι => pauliCoeff_smul ι.1 z (hX _ ι.2.2)
abbrev _root_.YangMills.DeltaSharedProofs.p501619 := @edge_coeffs_smul
private theorem tracelessOnPositive_of_mem {X : Edge L n k j → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n k j) : TracelessOnPositive X := hX.1
private def positiveValuesOfCoeffs (c : (edgePauliCoordinates L n k j).Index → ℂ) :
    Edge L n k j → ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
private theorem edge_ofCoeffs_eq (c : (edgePauliCoordinates L n k j).Index → ℂ) (b : Edge L n k j) :
    (edgePauliCoordinates L n k j).ofCoeffs c b = extendOddly (positiveValuesOfCoeffs c) b := rfl
private theorem edge_ofCoeffs_pos (c : (edgePauliCoordinates L n k j).Index → ℂ) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) :
    (edgePauliCoordinates L n k j).ofCoeffs c b = ofPauliCoeffs c ⟨b, h⟩ :=
  (edge_ofCoeffs_eq c b).trans ((extendOddly_pos _ h).trans (dif_pos h))
abbrev _root_.YangMills.SharedProofs.p19922 := @edge_ofCoeffs_pos
private theorem edgePauliCoordinates_faithful (hfin : Finite (Edge L n k j))
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    ReadsFaithfully (edgePauliCoordinates L n k j) := by
  have hmem : ∀ c, (edgePauliCoordinates L n k j).ofCoeffs c ∈ complexEdgeForms L n k j := fun c =>
    ⟨fun b hb => by
      rw [edge_ofCoeffs_pos c hb]
      exact ofPauliCoeffs_mem c _, fun b => extendOddly_opposite (positiveValuesOfCoeffs c) (hx b)⟩
  refine readsFaithfully_of (r := edgePauliCoordinates L n k j) ?_ hmem ?_ ?_ ?_ ?_
  · exact (inferInstanceAs (Finite {b : Edge L n k j // b.IsPositivelyOriented}))
  · intro c
    funext ι
    have e : (edgePauliCoordinates L n k j).ofCoeffs c ι.2.1 = ofPauliCoeffs c ι.2 :=
      edge_ofCoeffs_pos c ι.2.2
    show pauliCoeff ι.1 ((edgePauliCoordinates L n k j).ofCoeffs c ι.2.1) = c ι
    rw [e]
    exact pauliCoeff_combination (fun a => c (a, ι.2)) ι.1
  · intro f hf
    have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
        (edgePauliCoordinates L n k j).ofCoeffs ((edgePauliCoordinates L n k j).coeffs f) b = f b := fun b hb =>
      (edge_ofCoeffs_pos _ hb).trans (pauliCombination_pauliCoeff (hf.1 b hb))
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
private theorem edgeForm_value_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : Edge L n k j → ComplexMatrix2} (hX : X ∈ complexEdgeForms L n k j) (b : Edge L n k j) :
    X b ∈ ComplexMatrix2.traceless := by
  rcases hx b with ⟨h, _⟩ | ⟨h, _⟩
  · exact hX.1 b h
  · have e := hX.2 b
    have h₁ := hX.1 _ h
    rw [e] at h₁
    simpa using ComplexMatrix2.traceless.neg_mem h₁
abbrev _root_.YangMills.SharedProofs.p16313 := @edgeForm_value_mem
private theorem conjugateBy_smul (V A : ComplexMatrix2) (z : ℂ) :
    ComplexMatrix2.conjugateBy V (z • A) = z • ComplexMatrix2.conjugateBy V A := by
  simp only [ComplexMatrix2.conjugateBy, mul_smul_comm, smul_mul_assoc]
private theorem covDiff_add (W : Edge L n k j → ComplexMatrix2)
    (l l' : Vertex L n k j → ComplexMatrix2) :
    covDiff W (l + l') = covDiff W l + covDiff W l' := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.covDiff_add <;> assumption
private theorem covDiff_smul (W : Edge L n k j → ComplexMatrix2)
    (l : Vertex L n k j → ComplexMatrix2) (z : ℂ) :
    covDiff W (z • l) = z • covDiff W l := by
  funext b
  unfold covDiff
  by_cases h : b.IsPositivelyOriented
  · simp only [Pi.smul_apply, extendOddly_pos _ h, conjugateBy_smul, smul_sub]
  · simp only [Pi.smul_apply, extendOddly_neg _ h, conjugateBy_smul, smul_sub, smul_neg]
abbrev _root_.YangMills.SharedProofs.p24956 := @covDiff_smul
private theorem edgeFormPathSum_add (B B' : Edge L n k j → ComplexMatrix2)
    (Γ : List (Edge L n k j)) :
    edgeFormPathSum (B + B') Γ = edgeFormPathSum B Γ + edgeFormPathSum B' Γ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIterateLogs.bondFormSumAlong_add <;> assumption
abbrev _root_.YangMills.SharedProofs.p16344 := @edgeFormPathSum_add
private theorem edgeFormPathSum_smul (z : ℂ) (B : Edge L n k j → ComplexMatrix2)
    (Γ : List (Edge L n k j)) :
    edgeFormPathSum (z • B) Γ = z • edgeFormPathSum B Γ := by
  unfold edgeFormPathSum PeriodicLattice.bondFormSumAlong
  induction Γ with
  | nil => simp
  | cons b Γ ih => simp only [List.map_cons, List.sum_cons, ih, Pi.smul_apply, smul_add]
abbrev _root_.YangMills.SharedProofs.p18157 := @edgeFormPathSum_smul
private theorem edgeFormPathSum_mem {B : Edge L n k j → ComplexMatrix2}
    (hB : ∀ b, B b ∈ ComplexMatrix2.traceless) (Γ : List (Edge L n k j)) :
    edgeFormPathSum B Γ ∈ ComplexMatrix2.traceless := by
  unfold edgeFormPathSum PeriodicLattice.bondFormSumAlong
  induction Γ with
  | nil => simp
  | cons b Γ ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ComplexMatrix2.traceless.add_mem (hB b) ih
abbrev _root_.YangMills.SharedProofs.p3039 := @edgeFormPathSum_mem
variable [Finite (Vertex L n k j)]
private theorem crossingSmoothing_eq (B : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)) :
    crossingSmoothing L n k j B c = PeriodicLattice.inverseFourthPowerWeight L •
      ∑ x ∈ (Set.toFinite (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        c.source)).toFinset, edgeFormPathSum B (PeriodicLattice.crossingPath c x) := by
  unfold crossingSmoothing
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
abbrev _root_.YangMills.SharedProofs.p70531 := @crossingSmoothing_eq
private theorem crossingSmoothing_add (B B' : Edge L n k j → ComplexMatrix2) :
    crossingSmoothing L n k j (B + B') =
      crossingSmoothing L n k j B + crossingSmoothing L n k j B' := by
  funext c
  simp only [Pi.add_apply, crossingSmoothing_eq, edgeFormPathSum_add, Finset.sum_add_distrib,
    smul_add]
abbrev _root_.YangMills.SharedProofs.p41844 := @crossingSmoothing_add
private theorem crossingSmoothing_smul (z : ℂ) (B : Edge L n k j → ComplexMatrix2) :
    crossingSmoothing L n k j (z • B) = z • crossingSmoothing L n k j B := by
  funext c
  simp only [Pi.smul_apply, crossingSmoothing_eq, edgeFormPathSum_smul, ← Finset.smul_sum]
  rw [smul_comm]
abbrev _root_.YangMills.SharedProofs.p16432 := @crossingSmoothing_smul
private theorem crossingSmoothing_traceless {B : Edge L n k j → ComplexMatrix2}
    (hB : ∀ b, B b ∈ ComplexMatrix2.traceless) :
    TracelessOnPositive (crossingSmoothing L n k j B) := fun c _ => by
  rw [crossingSmoothing_eq]
  exact ComplexMatrix2.traceless.smul_mem _
    (Submodule.sum_mem _ fun x _ => edgeFormPathSum_mem hB _)
abbrev _root_.YangMills.DeltaSharedProofs.p502043 := @crossingSmoothing_traceless
private theorem vertexSmoothing_eq (l : Vertex L n k j → ComplexMatrix2) (y : Vertex L n k (j + 1)) :
    vertexSmoothing L n k j l y = PeriodicLattice.inverseFourthPowerWeight L •
      ∑ x ∈ (Set.toFinite (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        y)).toFinset, l x := by
  unfold vertexSmoothing
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
private theorem vertexSmoothing_add (l l' : Vertex L n k j → ComplexMatrix2) :
    vertexSmoothing L n k j (l + l') = vertexSmoothing L n k j l + vertexSmoothing L n k j l' := by
  funext y
  simp only [Pi.add_apply, vertexSmoothing_eq, Finset.sum_add_distrib, smul_add]
abbrev _root_.YangMills.SharedProofs.p8206 := @vertexSmoothing_add
private theorem vertexSmoothing_smul (z : ℂ) (l : Vertex L n k j → ComplexMatrix2) :
    vertexSmoothing L n k j (z • l) = z • vertexSmoothing L n k j l := by
  funext y
  simp only [Pi.smul_apply, vertexSmoothing_eq, ← Finset.smul_sum]
  rw [smul_comm]
abbrev _root_.YangMills.SharedProofs.p51938 := @vertexSmoothing_smul
private theorem vertexSmoothing_mem {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (y : Vertex L n k (j + 1)) :
    vertexSmoothing L n k j l y ∈ ComplexMatrix2.traceless := by
  rw [vertexSmoothing_eq]
  exact ComplexMatrix2.traceless.smul_mem _ (Submodule.sum_mem _ fun x _ => hl x)
abbrev _root_.YangMills.SharedProofs.p3658 := @vertexSmoothing_mem
end Forms
private structure Premises : Prop where
  meanStep : MeanStepNearFree.Claim
  smoothingSteps : Tower.SmoothingStepsNearFree.Claim
  contractions : Tower.SmoothingContraction.Claim
  stepLinear : Tower.StepMapsComplexLinear.Claim
  meanNearOne : NormalizedMeanNearOne
  holDiff : HolDifferentialLinear
  smoothingNear : Tower.SmoothingNearIdentity
  conjugation : ComplexMatrix2.ConjugationPreservesTraceless
  orientation : PeriodicLattice.BondEndpointsOrientation.Statement
  finiteEdges : Tower.BondSetFields.ProductStructureHolds
private theorem opNormLE_of_map {r r' : PauliComponentsOfSymmetricKernel} (hr : ReadsFaithfully r)
    (hr' : ReadsFaithfully r') {a a' c : ℝ} (ha : 0 < a) (ha' : 0 < a') (hc : 0 ≤ c)
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hlin : IsComplexLinear (r.mapOnCoeffs r' m))
    (hb : ∀ f, wNorm (meshWeight a') (r.mapOnCoeffs r' m f) ≤ c * wNorm (meshWeight a) f) :
    TorusOpNormLE a a' (r.kernel r' m) c := by
  have := hr.finite
  have := hr'.finite
  have hT : Represents (r.kernelOfBasisImages r' m) (r.mapOnCoeffs r' m) := fun f =>
    ⟨fun ι' => Summable.of_finite, applyKernel_basisImages hlin f⟩
  have hK : Represents (r.kernel r' m) (r.mapOnCoeffs r' m) :=
    Classical.epsilon_spec (⟨_, hT⟩ : ∃ T, Represents T (r.mapOnCoeffs r' m))
  refine opNormLE_of_bound hc fun g => ?_
  rw [(hK g).2]
  exact hb g
private theorem iterate_complexLinear {r : ℕ → PauliComponentsOfSymmetricKernel} {k : ℕ}
    (w : ∀ j, ((r j).space.index → ComplexMatrix2) → (r (j + 1)).space.index → ComplexMatrix2)
    (It : ∀ j, ((r 0).space.index → ComplexMatrix2) → (r j).space.index → ComplexMatrix2)
    (h0 : ∀ B, It 0 B = B) (hs : ∀ j < k, ∀ B, It (j + 1) B = w j (It j B))
    (wmem : ∀ j < k, ∀ X ∈ (r j).space.complexSubmodule, w j X ∈ (r (j + 1)).space.complexSubmodule)
    (wadd : ∀ j < k, ∀ X ∈ (r j).space.complexSubmodule, ∀ Y ∈ (r j).space.complexSubmodule,
      w j (X + Y) = w j X + w j Y)
    (wsmul : ∀ j < k, ∀ (z : ℂ), ∀ X ∈ (r j).space.complexSubmodule, w j (z • X) = z • w j X) :
    ∀ j ≤ k, (∀ X ∈ (r 0).space.complexSubmodule, It j X ∈ (r j).space.complexSubmodule) ∧
      (∀ X ∈ (r 0).space.complexSubmodule, ∀ Y ∈ (r 0).space.complexSubmodule,
        It j (X + Y) = It j X + It j Y) ∧
      (∀ (z : ℂ), ∀ X ∈ (r 0).space.complexSubmodule, It j (z • X) = z • It j X) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨fun X hX => by rwa [h0], fun X _ Y _ => by rw [h0, h0, h0],
      fun z X _ => by rw [h0, h0]⟩
  | succ j ih =>
    intro hj
    have hj' : j < k := hj
    obtain ⟨h₁, h₂, h₃⟩ := ih hj'.le
    refine ⟨fun X hX => ?_, fun X hX Y hY => ?_, fun z X hX => ?_⟩
    · rw [hs j hj']
      exact wmem j hj' _ (h₁ X hX)
    · rw [hs j hj', hs j hj', hs j hj', h₂ X hX Y hY, wadd j hj' _ (h₁ X hX) _ (h₁ Y hY)]
    · rw [hs j hj', hs j hj', h₃ z X hX, wsmul j hj' z _ (h₁ X hX)]
abbrev _root_.YangMills.SharedProofs.p68818 := @iterate_complexLinear
section Tower
variable {L n k : ℕ}
private theorem edge_orientation_xor (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) (b : Edge L n k j) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  ((G.orientation ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
private theorem edge_finite (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) : Finite (Edge L n k j) :=
  Set.finite_univ_iff.1 ((G.finiteEdges L hL k j hj).1 n hn).2.1
private theorem vertex_finite (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) : Finite (Vertex L n k j) :=
  have := edge_finite G hL hn hj
  Finite.of_injective (fun x : Vertex L n k j => PeriodicLattice.Bond.forwardFrom x 0)
    fun _ _ h => congrArg PeriodicLattice.Bond.source h
private theorem edgePauliCoordinates_faithful_of (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ}
    (hj : j ≤ k) : ReadsFaithfully (edgePauliCoordinates L n k j) :=
  edgePauliCoordinates_faithful (edge_finite G hL hn hj) (edge_orientation_xor G hL hn hk hj)
private theorem vertexCoordinate_faithful_of (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) :
    ReadsFaithfully (vertexCoordinate (Vertex L n k j)) :=
  have := vertex_finite G hL hn hj
  vertexCoordinate_faithful
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private structure StepHypotheses (L n k j : ℕ) (C : ℝ) (V : Edge L n k j → ComplexMatrix2) :
    Prop where
  small : V ∈ smallComplexFields L n k j
  mem_group : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup
  diff_traceless : ∀ (B : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)),
    c.IsPositivelyOriented → holLeftDifferential normalizedMean V B c ∈ ComplexMatrix2.traceless
  diff_linear : ∀ (z : ℂ) (B B' : Edge L n k j → ComplexMatrix2),
    holLeftDifferential normalizedMean V (z • B + B') =
      z • holLeftDifferential normalizedMean V B + holLeftDifferential normalizedMean V B'
  edge_near : MapNormLE (meshAt L k j) (meshAt L k (j + 1))
    (edgePauliCoordinates L n k j) (edgePauliCoordinates L n k (j + 1))
    (fun B => (L : ℝ)⁻¹ • (meanCovariantStep V B - crossingSmoothing L n k j B))
    (C * distFromOne V)
  vertex_near : MapNormLE (meshAt L k j) (meshAt L k (j + 1))
    (vertexCoordinate (Vertex L n k j)) (vertexCoordinate (Vertex L n k (j + 1)))
    (fun l => adjointCubeAverage V l - vertexSmoothing L n k j l)
    (C * distFromOne V)
section Step
variable {j : ℕ} {C : ℝ} {V : Edge L n k j → ComplexMatrix2}
private theorem meanCovariantStep_mem (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (h : StepHypotheses L n k j C V)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    meanCovariantStep V B ∈ complexEdgeForms L n k (j + 1) := by
  obtain ⟨h₁, _, _, _⟩ := G.stepLinear L hL n k j hn hj V h.small
  have hdrift := (h₁ B hB).2
  have hdiff : holLeftDifferential normalizedMean V B ∈ complexEdgeForms L n k (j + 1) :=
    ⟨fun c hc => h.diff_traceless B c hc,
      fun c => extendOddly_opposite _ (edge_orientation_xor G hL hn hk (show j + 1 ≤ k from hj) c)⟩
  refine Submodule.add_mem _ hdiff ⟨fun c hc => ?_, fun c => ?_⟩
  · have e : covDiff (normalizedMean V) (contourLogDrift V B) c =
        ComplexMatrix2.conjugateBy (normalizedMean V c) (contourLogDrift V B c.target) -
          contourLogDrift V B c.source := extendOddly_pos _ hc
    rw [e]
    exact ComplexMatrix2.traceless.sub_mem
      ((G.conjugation.2.2 _ (G.conjugation.1 _ (h.mem_group c hc))).2.2.2.1 (hdrift _)) (hdrift _)
  · exact extendOddly_opposite _ (edge_orientation_xor G hL hn hk (show j + 1 ≤ k from hj) c)
private theorem meanCovariantStep_add (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (h : StepHypotheses L n k j C V) {B B' : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) (hB' : B' ∈ complexEdgeForms L n k j) :
    meanCovariantStep V (B + B') = meanCovariantStep V B + meanCovariantStep V B' := by
  obtain ⟨_, h₂, _, _⟩ := G.stepLinear L hL n k j hn hj V h.small
  have e₂ := (h₂ B hB B' hB' 1).2
  have e₁ := h.diff_linear 1 B B'
  rw [one_smul, one_smul] at e₁ e₂
  unfold meanCovariantStep
  rw [e₁, e₂, covDiff_add]
  abel
private theorem meanCovariantStep_smul (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (h : StepHypotheses L n k j C V) (z : ℂ) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    meanCovariantStep V (z • B) = z • meanCovariantStep V B := by
  obtain ⟨_, h₂, _, _⟩ := G.stepLinear L hL n k j hn hj V h.small
  have e₂ := (h₂ B hB B hB (z - 1)).2
  have e₁ := h.diff_linear (z - 1) B B
  have e : (z - 1) • B + B = z • B := by
    rw [sub_smul, one_smul, sub_add_cancel]
  have e' : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (x : E), (z - 1) • x + x = z • x := by
    intro E _ _ x
    rw [sub_smul, one_smul, sub_add_cancel]
  rw [e, e'] at e₁ e₂
  unfold meanCovariantStep
  rw [e₁, e₂, covDiff_smul, smul_add]
private theorem adjointCubeAverage_add (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (h : StepHypotheses L n k j C V) {l l' : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (hl' : ∀ x, l' x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V (l + l') = adjointCubeAverage V l + adjointCubeAverage V l' := by
  obtain ⟨_, _, _, h₄⟩ := G.stepLinear L hL n k j hn hj V h.small
  have e := (h₄ l l' hl hl' 1).2
  rwa [one_smul, one_smul] at e
private theorem adjointCubeAverage_smul (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (h : StepHypotheses L n k j C V) (z : ℂ) {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V (z • l) = z • adjointCubeAverage V l := by
  obtain ⟨_, _, _, h₄⟩ := G.stepLinear L hL n k j hn hj V h.small
  have e := (h₄ l l hl hl (z - 1)).2
  have e' : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (x : E), (z - 1) • x + x = z • x := by
    intro E _ _ x
    rw [sub_smul, one_smul, sub_add_cancel]
  rwa [e', e'] at e
private theorem adjointCubeAverage_mem (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (h : StepHypotheses L n k j C V) {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (y : Vertex L n k (j + 1)) :
    adjointCubeAverage V l y ∈ ComplexMatrix2.traceless := by
  obtain ⟨_, _, h₃, _⟩ := G.stepLinear L hL n k j hn hj V h.small
  exact (h₃ l hl).2 y
private abbrev freeEdgeStep (L n k j : ℕ) (B : Edge L n k j → ComplexMatrix2) :
    Edge L n k (j + 1) → ComplexMatrix2 :=
  (L : ℝ)⁻¹ • crossingSmoothing L n k j B
private abbrev edgeStepDeviation (V B : Edge L n k j → ComplexMatrix2) :
    Edge L n k (j + 1) → ComplexMatrix2 :=
  (L : ℝ)⁻¹ • (meanCovariantStep V B - crossingSmoothing L n k j B)
private theorem real_smul_eq_complex_smul_fun {ι : Type} (t : ℝ) (Y : ι → ComplexMatrix2) :
    t • Y = (t : ℂ) • Y :=
  funext fun b => real_smul_eq_complex_smul t (Y b)
abbrev _root_.YangMills.SharedProofs.p7664 := @real_smul_eq_complex_smul_fun
private theorem freeEdgeStep_traceless (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) : TracelessOnPositive (freeEdgeStep L n k j B) :=
  fun c hc => by
  have := vertex_finite G hL hn hj.le
  unfold freeEdgeStep
  rw [real_smul_eq_complex_smul_fun]
  exact ComplexMatrix2.traceless.smul_mem _
    (crossingSmoothing_traceless (edgeForm_value_mem (edge_orientation_xor G hL hn hk hj.le) hB) c hc)
private theorem edgeStepDeviation_traceless (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k)
    (h : StepHypotheses L n k j C V) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) : TracelessOnPositive (edgeStepDeviation V B) :=
  fun c hc => by
  have := vertex_finite G hL hn hj.le
  unfold edgeStepDeviation
  rw [real_smul_eq_complex_smul_fun]
  exact ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.sub_mem
    ((meanCovariantStep_mem G hL hn hk hj h hB).1 c hc)
    (crossingSmoothing_traceless (edgeForm_value_mem (edge_orientation_xor G hL hn hk hj.le) hB) c hc))
private theorem freeEdgeStep_add [Finite (Vertex L n k j)] (X Y : Edge L n k j → ComplexMatrix2) :
    freeEdgeStep L n k j (X + Y) = freeEdgeStep L n k j X + freeEdgeStep L n k j Y := by
  unfold freeEdgeStep
  rw [crossingSmoothing_add, smul_add]
private theorem freeEdgeStep_smul [Finite (Vertex L n k j)] (z : ℂ)
    (X : Edge L n k j → ComplexMatrix2) :
    freeEdgeStep L n k j (z • X) = z • freeEdgeStep L n k j X := by
  unfold freeEdgeStep
  rw [crossingSmoothing_smul, real_smul_eq_complex_smul_fun, real_smul_eq_complex_smul_fun,
    smul_comm]
private theorem edgeStepDeviation_add (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (h : StepHypotheses L n k j C V) {X Y : Edge L n k j → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n k j) (hY : Y ∈ complexEdgeForms L n k j) :
    edgeStepDeviation V (X + Y) = edgeStepDeviation V X + edgeStepDeviation V Y := by
  have := vertex_finite G hL hn hj.le
  unfold edgeStepDeviation
  rw [meanCovariantStep_add G hL hn hj h hX hY, crossingSmoothing_add, ← smul_add,
    add_sub_add_comm]
private theorem edgeStepDeviation_smul (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (h : StepHypotheses L n k j C V) (z : ℂ) {X : Edge L n k j → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n k j) :
    edgeStepDeviation V (z • X) = z • edgeStepDeviation V X := by
  have := vertex_finite G hL hn hj.le
  unfold edgeStepDeviation
  rw [meanCovariantStep_smul G hL hn hj h z hX, crossingSmoothing_smul, ← smul_sub,
    real_smul_eq_complex_smul_fun, real_smul_eq_complex_smul_fun, smul_comm]
private theorem vertexStepDeviation_add (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (h : StepHypotheses L n k j C V) {X Y : Vertex L n k j → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (hY : ∀ x, Y x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V (X + Y) - vertexSmoothing L n k j (X + Y) =
      (adjointCubeAverage V X - vertexSmoothing L n k j X) +
        (adjointCubeAverage V Y - vertexSmoothing L n k j Y) := by
  have := vertex_finite G hL hn hj.le
  rw [adjointCubeAverage_add G hL hn hj h hX hY, vertexSmoothing_add, add_sub_add_comm]
private theorem vertexStepDeviation_smul (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (h : StepHypotheses L n k j C V) (z : ℂ) {X : Vertex L n k j → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V (z • X) - vertexSmoothing L n k j (z • X) =
      z • (adjointCubeAverage V X - vertexSmoothing L n k j X) := by
  have := vertex_finite G hL hn hj.le
  rw [adjointCubeAverage_smul G hL hn hj h z hX, vertexSmoothing_smul, smul_sub]
private theorem freeEdgeStep_linear (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) :
    IsComplexLinear
      ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (freeEdgeStep L n k j)) := by
  have := vertex_finite G hL hn hj.le
  refine isComplexLinear_of (edgePauliCoordinates_faithful_of G hL hn hk hj.le)
    (fun X => TracelessOnPositive (L := L) (n := n) (k := k) X)
    (fun _ _ hX hY => edge_coeffs_add hX hY) (fun z _ hX => edge_coeffs_smul z hX)
    (fun X hX => freeEdgeStep_traceless G hL hn hk hj hX) ?_ ?_
  · intro X _ Y _
    exact freeEdgeStep_add X Y
  · intro z X _
    exact freeEdgeStep_smul z X
private theorem edgeStepDeviation_linear (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k)
    (h : StepHypotheses L n k j C V) :
    IsComplexLinear
      ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (edgeStepDeviation V)) := by
  have := vertex_finite G hL hn hj.le
  refine isComplexLinear_of (edgePauliCoordinates_faithful_of G hL hn hk hj.le)
    (fun X => TracelessOnPositive (L := L) (n := n) (k := k) X)
    (fun _ _ hX hY => edge_coeffs_add hX hY) (fun z _ hX => edge_coeffs_smul z hX)
    (fun X hX => edgeStepDeviation_traceless G hL hn hk hj h hX) ?_ ?_
  · intro X hX Y hY
    exact edgeStepDeviation_add G hL hn hj h hX hY
  · intro z X hX
    exact edgeStepDeviation_smul G hL hn hj h z hX
private theorem vertexStepDeviation_linear (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (h : StepHypotheses L n k j C V) :
    IsComplexLinear ((vertexCoordinate (Vertex L n k j)).mapOnCoeffs
      (vertexCoordinate (Vertex L n k (j + 1)))
      fun l => adjointCubeAverage V l - vertexSmoothing L n k j l) := by
  have := vertex_finite G hL hn hj.le
  refine isComplexLinear_of (vertexCoordinate_faithful_of G hL hn hj.le)
    (fun X : Vertex L n k (j + 1) → ComplexMatrix2 => ∀ x, X x ∈ ComplexMatrix2.traceless)
    (fun _ _ hX hY => vertex_coeffs_add hX hY) (fun z _ hX => vertex_coeffs_smul z hX)
    (fun X hX y => ComplexMatrix2.traceless.sub_mem
      (adjointCubeAverage_mem G hL hn hj h (vertex_mem_iff.1 hX) y)
      (vertexSmoothing_mem (vertex_mem_iff.1 hX) y)) ?_ ?_
  · intro X hX Y hY
    exact vertexStepDeviation_add G hL hn hj h (vertex_mem_iff.1 hX) (vertex_mem_iff.1 hY)
  · intro z X hX
    exact vertexStepDeviation_smul G hL hn hj h z (vertex_mem_iff.1 hX)
private theorem vertexSmoothing_linear (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k) :
    IsComplexLinear ((vertexCoordinate (Vertex L n k j)).mapOnCoeffs
      (vertexCoordinate (Vertex L n k (j + 1))) (vertexSmoothing L n k j)) := by
  have := vertex_finite G hL hn hj.le
  refine isComplexLinear_of (vertexCoordinate_faithful_of G hL hn hj.le)
    (fun X : Vertex L n k (j + 1) → ComplexMatrix2 => ∀ x, X x ∈ ComplexMatrix2.traceless)
    (fun _ _ hX hY => vertex_coeffs_add hX hY) (fun z _ hX => vertex_coeffs_smul z hX)
    (fun X hX y => vertexSmoothing_mem (vertex_mem_iff.1 hX) y) ?_ ?_
  · intro X _ Y _
    exact vertexSmoothing_add X Y
  · intro z X _
    exact vertexSmoothing_smul z X
private theorem l1NormVec_zero : TorusMetric.l1NormVec (0 : Fin 4 → ℝ) = 0 := by
  simp [TorusMetric.l1NormVec]
private theorem distFromOne_nonneg (V : Edge L n k j → ComplexMatrix2) : 0 ≤ distFromOne V :=
  ENNReal.toReal_nonneg
private theorem edgeStepDeviation_bound (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k)
    (hC : 0 ≤ C) (h : StepHypotheses L n k j C V) (g : (edgePauliCoordinates L n k j).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (j + 1)))
      ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (edgeStepDeviation V) g) ≤
      (C * distFromOne V) * wNorm (meshWeight (meshAt L k j)) g := by
  have := (edgePauliCoordinates_faithful_of G hL hn hk hj.le).finite
  have := (edgePauliCoordinates_faithful_of G hL hn hk (show j + 1 ≤ k from hj)).finite
  exact le_of_wOpNorm_le (meshAt_pos hL k j) (meshAt_pos hL k (j + 1))
    (mul_nonneg hC (distFromOne_nonneg _)) (edgeStepDeviation_linear G hL hn hk hj h)
    h.edge_near.2 g
private theorem freeEdgeStep_bound (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (g : (edgePauliCoordinates L n k j).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (j + 1)))
      ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (freeEdgeStep L n k j) g) ≤
      wNorm (meshWeight (meshAt L k j)) g := by
  have := (edgePauliCoordinates_faithful_of G hL hn hk hj.le).finite
  have := (edgePauliCoordinates_faithful_of G hL hn hk (show j + 1 ≤ k from hj)).finite
  have hlin := freeEdgeStep_linear G hL hn hk hj
  have hc := (((G.contractions L hL k hk).2.1 n hn).2.1 j hj).1.2
  have e : applyKernel ((edgePauliCoordinates L n k j).kernelOfBasisImages (edgePauliCoordinates L n k (j + 1))
      (freeEdgeStep L n k j)) = (edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
      (freeEdgeStep L n k j) := funext (applyKernel_basisImages hlin)
  have hc' : wOpNorm (meshWeight (meshAt L k j)) (meshWeight (meshAt L k (j + 1)))
      univ ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (freeEdgeStep L n k j)) ≤
      ENNReal.ofReal 1 := by
    rw [← e]
    refine hc.trans (le_of_eq ?_)
    rw [l1NormVec_zero]
    simp
  have := le_of_wOpNorm_le (meshAt_pos hL k j) (meshAt_pos hL k (j + 1)) zero_le_one hlin hc' g
  simpa using this
private theorem edgeStep_split (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (h : StepHypotheses L n k j C V)
    {X : Edge L n k j → ComplexMatrix2} (hX : X ∈ complexEdgeForms L n k j) :
    (edgePauliCoordinates L n k (j + 1)).coeffs ((((L : ℝ)⁻¹ : ℝ) : ℂ) • meanCovariantStep V X) =
      (edgePauliCoordinates L n k (j + 1)).coeffs (edgeStepDeviation V X) +
        (edgePauliCoordinates L n k (j + 1)).coeffs (freeEdgeStep L n k j X) := by
  have e : (((L : ℝ)⁻¹ : ℝ) : ℂ) • meanCovariantStep V X =
      edgeStepDeviation V X + freeEdgeStep L n k j X := by
    unfold edgeStepDeviation freeEdgeStep
    rw [← smul_add, sub_add_cancel, real_smul_eq_complex_smul_fun]
  exact (congrArg (edgePauliCoordinates L n k (j + 1)).coeffs e).trans (edge_coeffs_add
    (edgeStepDeviation_traceless G hL hn hk hj h hX) (freeEdgeStep_traceless G hL hn hk hj hX))
private theorem vertexStepDeviation_bound (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k) (hC : 0 ≤ C)
    (h : StepHypotheses L n k j C V) (g : (vertexCoordinate (Vertex L n k j)).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (j + 1)))
      ((vertexCoordinate (Vertex L n k j)).mapOnCoeffs (vertexCoordinate (Vertex L n k (j + 1)))
        (fun l => adjointCubeAverage V l - vertexSmoothing L n k j l) g) ≤
      (C * distFromOne V) * wNorm (meshWeight (meshAt L k j)) g := by
  have : Finite (vertexCoordinate (Vertex L n k j)).Place :=
    (vertexCoordinate_faithful_of G hL hn hj.le).finite
  have : Finite (vertexCoordinate (Vertex L n k (j + 1))).Place :=
    (vertexCoordinate_faithful_of G hL hn (show j + 1 ≤ k from hj)).finite
  exact le_of_wOpNorm_le (meshAt_pos hL k j) (meshAt_pos hL k (j + 1))
    (mul_nonneg hC (distFromOne_nonneg _)) (vertexStepDeviation_linear G hL hn hj h)
    h.vertex_near.2 g
private theorem vertexSmoothing_bound (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (g : (vertexCoordinate (Vertex L n k j)).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (j + 1)))
      ((vertexCoordinate (Vertex L n k j)).mapOnCoeffs (vertexCoordinate (Vertex L n k (j + 1)))
        (vertexSmoothing L n k j) g) ≤
      wNorm (meshWeight (meshAt L k j)) g := by
  have : Finite (vertexCoordinate (Vertex L n k j)).Place :=
    (vertexCoordinate_faithful_of G hL hn hj.le).finite
  have : Finite (vertexCoordinate (Vertex L n k (j + 1))).Place :=
    (vertexCoordinate_faithful_of G hL hn (show j + 1 ≤ k from hj)).finite
  have hlin := vertexSmoothing_linear G hL hn hj
  have hc := (((G.contractions L hL k hk).2.1 n hn).2.1 j hj).2.2
  have e : applyKernel ((vertexCoordinate (Vertex L n k j)).kernelOfBasisImages
      (vertexCoordinate (Vertex L n k (j + 1))) (vertexSmoothing L n k j)) =
      (vertexCoordinate (Vertex L n k j)).mapOnCoeffs (vertexCoordinate (Vertex L n k (j + 1)))
        (vertexSmoothing L n k j) := funext (applyKernel_basisImages hlin)
  have hc' : wOpNorm (meshWeight (meshAt L k j)) (meshWeight (meshAt L k (j + 1)))
      univ ((vertexCoordinate (Vertex L n k j)).mapOnCoeffs (vertexCoordinate (Vertex L n k (j + 1)))
        (vertexSmoothing L n k j)) ≤ ENNReal.ofReal 1 := by
    rw [← e]
    refine hc.trans (le_of_eq ?_)
    rw [l1NormVec_zero]
    simp
  have := le_of_wOpNorm_le (meshAt_pos hL k j) (meshAt_pos hL k (j + 1)) zero_le_one hlin hc' g
  simpa using this
private theorem vertexStep_split (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (h : StepHypotheses L n k j C V)
    {X : Vertex L n k j → ComplexMatrix2} (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) :
    (vertexCoordinate (Vertex L n k (j + 1))).coeffs ((1 : ℂ) • adjointCubeAverage V X) =
      (vertexCoordinate (Vertex L n k (j + 1))).coeffs
          (adjointCubeAverage V X - vertexSmoothing L n k j X) +
        (vertexCoordinate (Vertex L n k (j + 1))).coeffs (vertexSmoothing L n k j X) := by
  have e : (1 : ℂ) • adjointCubeAverage V X =
      (adjointCubeAverage V X - vertexSmoothing L n k j X) + vertexSmoothing L n k j X := by
    rw [one_smul, sub_add_cancel]
  have := vertex_finite (k := k) G hL hn hj.le
  exact (congrArg (vertexCoordinate (Vertex L n k (j + 1))).coeffs e).trans (vertex_coeffs_add
    (fun y => ComplexMatrix2.traceless.sub_mem (adjointCubeAverage_mem G hL hn hj h hX y)
      (vertexSmoothing_mem hX y))
    (vertexSmoothing_mem hX))
end Step
private theorem meshAt_succ (hL : Conventions.IsAdmissibleBlockingFactor L) (k m : ℕ) :
    meshAt L k (m + 1) = L * meshAt L k m := by
  have h0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    have : 0 < L := by omega
    exact_mod_cast this.ne'
  unfold meshAt
  rw [← zpow_one_add₀ h0]
  congr 1
  push_cast
  ring
abbrev _root_.YangMills.SharedProofs.p23229 := @meshAt_succ
private theorem two_le_side (hL : Conventions.IsAdmissibleBlockingFactor L) : (2 : ℝ) ≤ L := by
  have := hL.2
  have : 2 ≤ L := by omega
  exact_mod_cast this
private theorem sum_meshAt_le (hL : Conventions.IsAdmissibleBlockingFactor L) (k s m : ℕ) :
    ∑ i ∈ Finset.range m, meshAt L k (s + i) ≤ meshAt L k (s + m) := by
  induction m with
  | zero => simpa using (meshAt_pos hL k s).le
  | succ m ih =>
    rw [Finset.sum_range_succ, show s + (m + 1) = s + m + 1 from rfl, meshAt_succ hL]
    have := two_le_side hL
    nlinarith [meshAt_pos hL k (s + m)]
private theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
private theorem meshAt_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (hj : j ≤ k) :
    meshAt L k j ≤ 1 := by
  have h : ∀ m, meshAt L k j ≤ meshAt L k (j + m) := by
    intro m
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
      rw [show j + (m + 1) = j + m + 1 from rfl, meshAt_succ hL]
      have := two_le_side hL
      nlinarith [meshAt_pos hL k (j + m)]
  have h₁ := h (k - j)
  rwa [show j + (k - j) = k by omega, meshAt_self] at h₁
abbrev _root_.YangMills.SharedProofs.p8023 := @meshAt_le_one
private theorem prod_one_add_le_exp (hL : Conventions.IsAdmissibleBlockingFactor L) {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (ht' : t ≤ 1 / 41) {s m : ℕ} (hsm : s + m = k) {d : ℕ → ℝ}
    (hd : ∀ i, 0 ≤ d i) (hb : ∀ i < m, d i ≤ 20 * meshAt L k (s + i) * t) :
    ∏ i ∈ Finset.range m, (1 + C * d i) ≤ Real.exp (30 * C) := by
  have h₁ : ∏ i ∈ Finset.range m, (1 + C * d i) ≤ ∏ i ∈ Finset.range m, Real.exp (C * d i) := by
    refine Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_
    · have := mul_nonneg hC (hd i)
      linarith
    · have := Real.add_one_le_exp (C * d i)
      linarith
  refine h₁.trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  have h₂ : ∑ i ∈ Finset.range m, C * d i ≤
      ∑ i ∈ Finset.range m, C * (20 * t) * meshAt L k (s + i) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have := mul_le_mul_of_nonneg_left (hb i (Finset.mem_range.1 hi)) hC
    nlinarith
  have h₂' := Finset.mul_sum (Finset.range m) (fun i => meshAt L k (s + i)) (C * (20 * t))
  have h₃ := sum_meshAt_le hL k s m
  rw [hsm, meshAt_self] at h₃
  have h₅ : 0 ≤ C * (20 * t) := by positivity
  have h₆ := mul_le_mul_of_nonneg_left h₃ h₅
  have h₇ : C * (20 * t) ≤ 30 * C := by nlinarith
  linarith
private theorem smoothingStepConstant_nonneg (L : ℕ) : 0 ≤ smoothingStepConstant L := by
  unfold smoothingStepConstant
  positivity
private theorem distFromOne_le {j : ℕ} {V : Edge L n k j → ComplexMatrix2} {x : ℝ} (hx : 0 ≤ x)
    (h : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) ≤ x) : distFromOne V ≤ x :=
  ENNReal.toReal_le_of_le_ofReal hx (iSup_le fun b => ENNReal.ofReal_le_ofReal (h b))
private abbrev invSide (L : ℕ) : ℂ := (((L : ℝ)⁻¹ : ℝ) : ℂ)
private theorem finestMesh_eq_pow : ((finestMesh L k : ℝ) : ℂ) = invSide L ^ k := by
  have e : finestMesh L k = ((L : ℝ)⁻¹) ^ k := by
    unfold finestMesh meshAt
    simp [zpow_neg, zpow_natCast, inv_pow]
  rw [e]
  push_cast
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p502271 := @finestMesh_eq_pow
private theorem inv_pow_eq_invSide_pow (m : ℕ) :
    (((((L : ℝ) ^ m)⁻¹ : ℝ)) : ℂ) = invSide L ^ m := by
  push_cast
  rw [inv_pow]
variable {C : ℝ} {U : Edge L n k 0 → ComplexMatrix2}
private theorem meanCovariant_coeffs_bound (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hC : 0 ≤ C)
    (h : ∀ j < k, StepHypotheses L n k j C (meanIterate U j))
    (f : (edgePauliCoordinates L n k 0).Index → ℂ) :
    wNorm (meshWeight (meshAt L k k))
        (invSide L ^ k • (edgePauliCoordinates L n k k).coeffs
          (meanCovariant U k ((edgePauliCoordinates L n k 0).ofCoeffs f))) ≤
      (∏ i ∈ Finset.range k, (1 + C * distFromOne (meanIterate U i))) *
        wNorm (meshWeight (meshAt L k 0)) f :=
  (wNorm_product_le (r := fun j => edgePauliCoordinates L n k j) (a := meshAt L k)
    (e := fun i => C * distFromOne (meanIterate U i))
    (s := invSide L) (fun j hj => edgePauliCoordinates_faithful_of G hL hn hk hj) (meshAt_pos hL k)
    (fun i => mul_nonneg hC (distFromOne_nonneg _))
    (fun j => meanCovariantStep (meanIterate U j))
    (fun j => edgeStepDeviation (meanIterate U j))
    (fun j => freeEdgeStep L n k j)
    (fun j => meanCovariant U j)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun j hj X hX => meanCovariantStep_mem G hL hn hk hj (h j hj) hX)
    (fun j hj z X hX => meanCovariantStep_smul G hL hn hj (h j hj) z hX)
    (fun j hj g => edgeStepDeviation_bound G hL hn hk hj hC (h j hj) g)
    (fun j hj g => freeEdgeStep_bound G hL hn hk hj g)
    (fun j hj X hX => edgeStep_split G hL hn hk hj (h j hj) hX) k le_rfl f).2
private theorem meanCovariant_complexLinear (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    (h : ∀ j < k, StepHypotheses L n k j C (meanIterate U j)) :
    (∀ X ∈ complexEdgeForms L n k 0, meanCovariant U k X ∈ complexEdgeForms L n k k) ∧
    (∀ X ∈ complexEdgeForms L n k 0, ∀ Y ∈ complexEdgeForms L n k 0,
      meanCovariant U k (X + Y) = meanCovariant U k X + meanCovariant U k Y) ∧
    (∀ (z : ℂ), ∀ X ∈ complexEdgeForms L n k 0,
      meanCovariant U k (z • X) = z • meanCovariant U k X) :=
  iterate_complexLinear (r := fun j => edgePauliCoordinates L n k j) (k := k)
    (fun j => meanCovariantStep (meanIterate U j)) (fun j => meanCovariant U j)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun j hj X hX => meanCovariantStep_mem G hL hn hk hj (h j hj) hX)
    (fun j hj X hX Y hY => meanCovariantStep_add G hL hn hj (h j hj) hX hY)
    (fun j hj z X hX => meanCovariantStep_smul G hL hn hj (h j hj) z hX) k le_rfl
private theorem scaled_complexLinear {s e : ℕ} (hs : ReadsFaithfully (edgePauliCoordinates L n k s)) (a : ℝ)
    {M : (Edge L n k s → ComplexMatrix2) → Edge L n k e → ComplexMatrix2}
    (hm : ∀ X ∈ complexEdgeForms L n k s, M X ∈ complexEdgeForms L n k e)
    (ha : ∀ X ∈ complexEdgeForms L n k s, ∀ Y ∈ complexEdgeForms L n k s, M (X + Y) = M X + M Y)
    (hz : ∀ (z : ℂ), ∀ X ∈ complexEdgeForms L n k s, M (z • X) = z • M X) :
    IsComplexLinear ((edgePauliCoordinates L n k s).mapOnCoeffs (edgePauliCoordinates L n k e) fun B => a • M B) := by
  have hz' : ∀ (z : ℂ), ∀ X ∈ complexEdgeForms L n k s, a • M (z • X) = z • a • M X := by
    intro z X hX
    rw [hz z X hX, real_smul_eq_complex_smul_fun, real_smul_eq_complex_smul_fun, smul_comm]
  refine isComplexLinear_of hs (fun X => TracelessOnPositive (L := L) (n := n) (k := k) X)
    (fun _ _ hX hY => edge_coeffs_add hX hY) (fun z _ hX => edge_coeffs_smul z hX) ?_ ?_ ?_
  · intro X hX
    have : (a : ℂ) • M X ∈ complexEdgeForms L n k e := Submodule.smul_mem _ _ (hm X hX)
    rw [real_smul_eq_complex_smul_fun]
    exact tracelessOnPositive_of_mem this
  · intro X hX Y hY
    exact (congrArg (fun x => a • x) (ha X hX Y hY)).trans (smul_add a _ _)
  · intro z X hX
    exact hz' z X hX
private theorem meanKernelQ_opNormLE (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hC : 0 ≤ C)
    (h : ∀ j < k, StepHypotheses L n k j C (meanIterate U j)) {c : ℝ} (hc : 0 ≤ c)
    (hprod : ∏ i ∈ Finset.range k, (1 + C * distFromOne (meanIterate U i)) ≤ c) :
    TorusOpNormLE (finestMesh L k) (meshAt L k k) (meanKernelQ L n k U) c := by
  obtain ⟨hm, ha, hz⟩ := meanCovariant_complexLinear G hL hn hk h
  refine opNormLE_of_map (edgePauliCoordinates_faithful_of G hL hn hk (Nat.zero_le k))
    (edgePauliCoordinates_faithful_of G hL hn hk le_rfl) (meshAt_pos hL k 0) (meshAt_pos hL k k) hc
    (scaled_complexLinear (edgePauliCoordinates_faithful_of G hL hn hk (Nat.zero_le k)) _ hm ha hz)
    fun g => ?_
  have hg : (edgePauliCoordinates L n k 0).ofCoeffs g ∈ complexEdgeForms L n k 0 :=
    (edgePauliCoordinates_faithful_of G hL hn hk (Nat.zero_le k)).mem g
  have e : (edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
      (fun B => finestMesh L k • meanCovariant U k B) g =
      invSide L ^ k • (edgePauliCoordinates L n k k).coeffs
        (meanCovariant U k ((edgePauliCoordinates L n k 0).ofCoeffs g)) := by
    have e₁ := edge_coeffs_smul ((finestMesh L k : ℝ) : ℂ) (hm _ hg).1
    rw [← real_smul_eq_complex_smul_fun, finestMesh_eq_pow] at e₁
    exact e₁
  rw [e]
  exact (meanCovariant_coeffs_bound G hL hn hk hC h g).trans
    (mul_le_mul_of_nonneg_right hprod (wNorm_nonneg _ _))
private theorem meanCovariantFrom_coeffs_bound (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hC : 0 ≤ C)
    (h : ∀ j < k, StepHypotheses L n k j C (meanIterate U j)) {s m : ℕ} (hsm : s + m = k)
    (f : (edgePauliCoordinates L n k s).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (s + m)))
        (invSide L ^ m • (edgePauliCoordinates L n k (s + m)).coeffs
          (meanCovariantFrom U s m ((edgePauliCoordinates L n k s).ofCoeffs f))) ≤
      (∏ i ∈ Finset.range m, (1 + C * distFromOne (meanIterate U (s + i)))) *
        wNorm (meshWeight (meshAt L k s)) f :=
  (wNorm_product_le (r := fun j => edgePauliCoordinates L n k (s + j)) (a := fun j => meshAt L k (s + j))
    (e := fun i => C * distFromOne (meanIterate U (s + i)))
    (s := invSide L) (k := m) (fun j hj => edgePauliCoordinates_faithful_of G hL hn hk (by omega))
    (fun j => meshAt_pos hL k (s + j))
    (fun i => mul_nonneg hC (distFromOne_nonneg _))
    (fun j => meanCovariantStep (meanIterate U (s + j)))
    (fun j => edgeStepDeviation (meanIterate U (s + j)))
    (fun j => freeEdgeStep L n k (s + j))
    (fun j => meanCovariantFrom U s j)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun j hj X hX => meanCovariantStep_mem G hL hn hk (by omega) (h (s + j) (by omega)) hX)
    (fun j hj z X hX => meanCovariantStep_smul G hL hn (by omega) (h (s + j) (by omega)) z hX)
    (fun j hj g => edgeStepDeviation_bound G hL hn hk (by omega) hC (h (s + j) (by omega)) g)
    (fun j hj g => freeEdgeStep_bound G hL hn hk (by omega) g)
    (fun j hj X hX => edgeStep_split G hL hn hk (by omega) (h (s + j) (by omega)) hX)
    m le_rfl f).2
private theorem meanCovariantFrom_complexLinear (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    (h : ∀ j < k, StepHypotheses L n k j C (meanIterate U j)) {s m : ℕ} (hsm : s + m = k) :
    (∀ X ∈ complexEdgeForms L n k s,
      meanCovariantFrom U s m X ∈ complexEdgeForms L n k (s + m)) ∧
    (∀ X ∈ complexEdgeForms L n k s, ∀ Y ∈ complexEdgeForms L n k s,
      meanCovariantFrom U s m (X + Y) = meanCovariantFrom U s m X + meanCovariantFrom U s m Y) ∧
    (∀ (z : ℂ), ∀ X ∈ complexEdgeForms L n k s,
      meanCovariantFrom U s m (z • X) = z • meanCovariantFrom U s m X) :=
  iterate_complexLinear (r := fun j => edgePauliCoordinates L n k (s + j)) (k := m)
    (fun j => meanCovariantStep (meanIterate U (s + j))) (fun j => meanCovariantFrom U s j)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun j hj X hX => meanCovariantStep_mem G hL hn hk (by omega) (h (s + j) (by omega)) hX)
    (fun j hj X hX Y hY => meanCovariantStep_add G hL hn (by omega) (h (s + j) (by omega)) hX hY)
    (fun j hj z X hX => meanCovariantStep_smul G hL hn (by omega) (h (s + j) (by omega)) z hX)
    m le_rfl
private theorem meanKernelFrom_opNormLE (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hC : 0 ≤ C)
    (h : ∀ j < k, StepHypotheses L n k j C (meanIterate U j)) {s m : ℕ} (hsm : s + m = k)
    {c : ℝ} (hc : 0 ≤ c)
    (hprod : ∏ i ∈ Finset.range m, (1 + C * distFromOne (meanIterate U (s + i))) ≤ c) :
    TorusOpNormLE (meshAt L k s) (meshAt L k k) (meanKernelFrom L n k U s m) c := by
  obtain ⟨hm, ha, hz⟩ := meanCovariantFrom_complexLinear G hL hn hk h hsm
  have hs : s ≤ k := by omega
  have hl : meshAt L k k = meshAt L k (s + m) := by rw [hsm]
  rw [hl]
  refine opNormLE_of_map (edgePauliCoordinates_faithful_of G hL hn hk hs)
    (edgePauliCoordinates_faithful_of G hL hn hk hsm.le) (meshAt_pos hL k s) (meshAt_pos hL k (s + m)) hc
    (scaled_complexLinear (edgePauliCoordinates_faithful_of G hL hn hk hs) _ hm ha hz) fun g => ?_
  have hg : (edgePauliCoordinates L n k s).ofCoeffs g ∈ complexEdgeForms L n k s :=
    (edgePauliCoordinates_faithful_of G hL hn hk hs).mem g
  have e : (edgePauliCoordinates L n k s).mapOnCoeffs (edgePauliCoordinates L n k (s + m))
      (fun B => ((L : ℝ) ^ m)⁻¹ • meanCovariantFrom U s m B) g =
      invSide L ^ m • (edgePauliCoordinates L n k (s + m)).coeffs
        (meanCovariantFrom U s m ((edgePauliCoordinates L n k s).ofCoeffs g)) := by
    have e₁ := edge_coeffs_smul ((((L : ℝ) ^ m)⁻¹ : ℝ) : ℂ) (hm _ hg).1
    rw [← real_smul_eq_complex_smul_fun, inv_pow_eq_invSide_pow] at e₁
    exact e₁
  rw [e]
  exact (meanCovariantFrom_coeffs_bound G hL hn hk hC h hsm g).trans
    (mul_le_mul_of_nonneg_right hprod (wNorm_nonneg _ _))
private theorem composedCubeAverage_coeffs_bound (G : Premises)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hC : 0 ≤ C)
    (h : ∀ j < k, StepHypotheses L n k j C (meanIterate U j))
    (f : (vertexCoordinate (Vertex L n k 0)).Index → ℂ) :
    wNorm (meshWeight (meshAt L k k))
        ((1 : ℂ) ^ k • (vertexCoordinate (Vertex L n k k)).coeffs
          (composedCubeAverage (quietPoint U) k ((vertexCoordinate (Vertex L n k 0)).ofCoeffs f))) ≤
      (∏ i ∈ Finset.range k, (1 + C * distFromOne (meanIterate U i))) *
        wNorm (meshWeight (meshAt L k 0)) f :=
  (wNorm_product_le (r := fun j => vertexCoordinate (Vertex L n k j)) (a := meshAt L k)
    (e := fun i => C * distFromOne (meanIterate U i))
    (s := 1) (fun j hj => vertexCoordinate_faithful_of G hL hn hj) (meshAt_pos hL k)
    (fun i => mul_nonneg hC (distFromOne_nonneg _))
    (fun j => adjointCubeAverage (meanIterate U j))
    (fun j l => adjointCubeAverage (meanIterate U j) l - vertexSmoothing L n k j l)
    (fun j => vertexSmoothing L n k j)
    (fun j => composedCubeAverage (quietPoint U) j)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun j hj X hX => vertex_mem_iff.2
      (adjointCubeAverage_mem G hL hn hj (h j hj) (vertex_mem_iff.1 hX)))
    (fun j hj z X hX => adjointCubeAverage_smul G hL hn hj (h j hj) z (vertex_mem_iff.1 hX))
    (fun j hj g => vertexStepDeviation_bound G hL hn hj hC (h j hj) g)
    (fun j hj g => vertexSmoothing_bound G hL hn hk hj g)
    (fun j hj X hX => vertexStep_split G hL hn hj (h j hj) (vertex_mem_iff.1 hX)) k le_rfl f).2
private theorem meanKernelR_opNormLE (G : Premises) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hC : 0 ≤ C)
    (h : ∀ j < k, StepHypotheses L n k j C (meanIterate U j)) {c : ℝ} (hc : 0 ≤ c)
    (hprod : ∏ i ∈ Finset.range k, (1 + C * distFromOne (meanIterate U i)) ≤ c) :
    TorusOpNormLE (finestMesh L k) (meshAt L k k) (meanKernelR L n k U) c := by
  have hr := vertexCoordinate_faithful_of (k := k) G hL hn (Nat.zero_le k)
  have hl := iterate_complexLinear (r := fun j => vertexCoordinate (Vertex L n k j)) (k := k)
    (fun j => adjointCubeAverage (meanIterate U j))
    (fun j => composedCubeAverage (quietPoint U) j)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun j hj X hX => vertex_mem_iff.2
      (adjointCubeAverage_mem G hL hn hj (h j hj) (vertex_mem_iff.1 hX)))
    (fun j hj X hX Y hY => adjointCubeAverage_add G hL hn hj (h j hj) (vertex_mem_iff.1 hX)
      (vertex_mem_iff.1 hY))
    (fun j hj z X hX => adjointCubeAverage_smul G hL hn hj (h j hj) z (vertex_mem_iff.1 hX))
    k le_rfl
  obtain ⟨hm, ha, hz⟩ := hl
  have hlin : IsComplexLinear ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs
      (vertexCoordinate (Vertex L n k k)) (composedCubeAverage (quietPoint U) k)) := by
    have := vertex_finite (k := k) G hL hn le_rfl
    refine isComplexLinear_of hr
      (fun X : Vertex L n k k → ComplexMatrix2 => ∀ x, X x ∈ ComplexMatrix2.traceless)
      (fun _ _ hX hY => vertex_coeffs_add hX hY) (fun z _ hX => vertex_coeffs_smul z hX)
      (fun X hX => vertex_mem_iff.1 (hm X hX)) ha hz
  refine opNormLE_of_map hr (vertexCoordinate_faithful_of G hL hn le_rfl) (meshAt_pos hL k 0)
    (meshAt_pos hL k k) hc hlin fun g => ?_
  have e := composedCubeAverage_coeffs_bound G hL hn hk hC h g
  rw [one_pow, one_smul] at e
  exact e.trans (mul_le_mul_of_nonneg_right hprod (wNorm_nonneg _ _))
end Tower
private theorem of_premises (G : Premises) : MeanKernelNormBounds := by
  intro L hL
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hS⟩ := G.meanStep L hL
  obtain ⟨ρ₂, hρ₂, hN⟩ := G.meanNearOne L hL
  obtain ⟨ρ₃, hρ₃, hD⟩ := G.holDiff L hL
  have hρL := (G.smoothingNear.1 L hL).2.2.pos
  obtain ⟨r, hr, hr₁, hr₂, hr₃, hr₄⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ ρ₁ ∧ r ≤ ρ₂ ∧ r ≤ ρ₃ ∧
      r ≤ polydiscRadius L / 2 :=
    ⟨min (min ρ₁ ρ₂) (min ρ₃ (polydiscRadius L / 2)),
      lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ (by linarith)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hK₀ := smoothingStepConstant_nonneg L
  set K := C₁ + smoothingStepConstant L with hK
  have hKnn : 0 ≤ K := by positivity
  refine ⟨min (1 / 41) (r / 21), Real.exp (30 * K), lt_min (by norm_num) (by positivity),
    Real.one_le_exp (by positivity), ?_⟩
  intro n k hn hk U t ht htρ hconf hbd
  have ht₁ : t ≤ 1 / 41 := htρ.trans (min_le_left _ _)
  have ht₂ : t ≤ r / 21 := htρ.trans (min_le_right _ _)
  have hsmall : ∀ j < k, ∀ b, ComplexMatrix2.operatorNorm (meanIterate U j b - 1) < r := by
    intro j hj b
    have h₁ := hbd j hj b
    have h₂ := meshAt_le_one (k := k) hL hj.le
    have h₃ := meshAt_pos hL k j
    have h₄ : 20 * meshAt L k j * t ≤ 20 * t := by nlinarith
    linarith
  have hfacts : ∀ j < k, StepHypotheses L n k j K (meanIterate U j) := by
    intro j hj
    have hb := hsmall j hj
    have hV := hconf j hj
    have hd₀ := distFromOne_nonneg (meanIterate U j)
    have hD' := hD n k j hn hj _ hV fun b => (hb b).trans_le hr₃
    have hA := (G.smoothingSteps L hL n k j hn hj _ hV fun b => (hb b).trans_le hr₄).2
    have hB := hS n k j hn hj _ hV fun b => (hb b).trans_le hr₁
    refine ⟨⟨hV, fun b => ?_⟩, fun c hc => ?_, hD'.1, hD'.2, ⟨hB.1, hB.2.trans ?_⟩,
      ⟨hA.1, hA.2.trans ?_⟩⟩
    · linarith [hb b]
    · exact (hN n k j hn hj _ hV (fun b => (hb b).trans_le hr₂) c hc).2.2.2.1
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hd₀)
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hd₀)
  have hdist : ∀ j < k, distFromOne (meanIterate U j) ≤ 20 * meshAt L k j * t :=
    fun j hj => distFromOne_le (mul_nonneg (mul_nonneg (by norm_num) (meshAt_pos hL k j).le) ht)
      (hbd j hj)
  have hprod : ∀ s m : ℕ, s + m = k →
      ∏ i ∈ Finset.range m, (1 + K * distFromOne (meanIterate U (s + i))) ≤
        Real.exp (30 * K) := fun s m hsm =>
    prod_one_add_le_exp hL hKnn ht ht₁ hsm (fun i => distFromOne_nonneg _)
      (fun i hi => hdist (s + i) (by omega))
  have hprod₀ : ∏ i ∈ Finset.range k, (1 + K * distFromOne (meanIterate U i)) ≤
      Real.exp (30 * K) :=
    prod_one_add_le_exp hL hKnn ht ht₁ (s := 0) (m := k) (Nat.zero_add k)
      (d := fun i => distFromOne (meanIterate U i)) (fun i => distFromOne_nonneg _)
      (fun i hi => by rw [Nat.zero_add]; exact hdist i hi)
  exact ⟨meanKernelQ_opNormLE G hL hn hk hKnn hfacts (Real.exp_pos _).le hprod₀,
    meanKernelR_opNormLE G hL hn hk hKnn hfacts (Real.exp_pos _).le hprod₀,
    fun s m hsm => meanKernelFrom_opNormLE G hL hn hk hKnn hfacts hsm (Real.exp_pos _).le
      (hprod s m hsm)⟩
theorem meanKernelNormBounds (h₁ : MeanStepNearFree.Claim)
    (h₂ : Tower.SmoothingStepsNearFree.Claim)
    (h₃ : Tower.SmoothingContraction.Claim)
    (h₄ : Tower.StepMapsComplexLinear.Claim)
    (h₅ : NormalizedMeanNearOne) (h₆ : HolDifferentialLinear)
    (h₇ : Tower.SmoothingNearIdentity)
    (h₈ : ComplexMatrix2.ConjugationPreservesTraceless)
    (h₉ : PeriodicLattice.BondEndpointsOrientation.Statement)
    (h₁₀ : Tower.BondSetFields.ProductStructureHolds) : MeanKernelNormBounds :=
  of_premises ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
end YangMills.Construction.RunningCouplingSlope.MeanKernelNormProof
end
