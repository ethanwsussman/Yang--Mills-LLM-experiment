import YangMills.Construction.PeriodicOperators.TorusKernelOfAPeriodicOperator
import YangMills.Construction.PeriodicOperators.TraceAndDeterminantOnATorus
import YangMills.Construction.PeriodicOperators.WaveSpacesOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TorusTraceDet
open InfiniteLattice (AmbientSpace)
open RiemannSums (DualClasses)
theorem trace_det_of_conj_blockDiagonal {C D Q : Type} [Fintype C] [DecidableEq C] [Fintype D]
    [DecidableEq D] [Fintype Q] [DecidableEq Q] (A : Matrix C C ℂ) (B : Q → Matrix D D ℂ)
    (e : (D × Q → ℂ) ≃ₗ[ℂ] (C → ℂ))
    (he : ∀ f, A.mulVec (e f) = e ((Matrix.blockDiagonal B).mulVec f)) :
    A.trace = ∑ q, (B q).trace ∧ A.det = ∏ q, (B q).det := by
  have hconj : Matrix.toLin' A = e.conj (Matrix.toLin' (Matrix.blockDiagonal B)) := by
    apply LinearMap.ext
    intro v
    obtain ⟨f, rfl⟩ := e.surjective v
    simp [LinearEquiv.conj_apply, he]
  constructor
  · rw [← Matrix.trace_toLin'_eq, hconj, LinearMap.trace_conj', Matrix.trace_toLin'_eq,
      Matrix.trace_blockDiagonal]
  · have hdet : LinearMap.det (e.conj (Matrix.toLin' (Matrix.blockDiagonal B))) =
        LinearMap.det (Matrix.toLin' (Matrix.blockDiagonal B)) := by
      rw [LinearEquiv.conj_apply, LinearMap.comp_assoc]
      exact LinearMap.det_conj _ e
    rw [← LinearMap.det_toLin', hconj, hdet, LinearMap.det_toLin', Matrix.det_blockDiagonal]
theorem applyKernel_eq_mulVec {J J' : Type} [Fintype J] (M : J' → J → ℂ) (f : J → ℂ) :
    applyKernel M f = (Matrix.of M).mulVec f := by
  funext i
  simp [applyKernel, Matrix.mulVec, dotProduct, tsum_fintype]
theorem mkQuot_surjective (I : PeriodicData) (s : ℕ) : Function.Surjective (I.mkQuot s) :=
  fun c => Quot.exists_rep c
def quotWave (I : PeriodicData) (s : ℕ) (κ : AmbientSpace) :
    (I.UnitQuot → ℂ) →ₗ[ℂ] (I.QuotMod s → ℂ) where
  toFun φ c := blochWave I (toComplexVec κ) φ (Function.surjInv (mkQuot_surjective I s) c)
  map_add' φ ψ := by
    funext c
    simp [blochWave, mul_add]
  map_smul' z φ := by
    funext c
    simp only [blochWave, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem quotWave_mk {I : PeriodicData} (F : BlochDecomposition.Facts I) {s : ℕ} (hs : 0 < s)
    {κ : AmbientSpace} (hκ : κ ∈ dualLattice s) (φ : I.UnitQuot → ℂ) (x : I.Carrier) :
    quotWave I s κ φ (I.mkQuot s x) = blochWave I (toComplexVec κ) φ x := by
  obtain ⟨g, hg⟩ := F.blochWave_descends s hs κ hκ φ
  change blochWave I (toComplexVec κ) φ
    (Function.surjInv (mkQuot_surjective I s) (I.mkQuot s x)) = _
  rw [← hg, ← hg, Function.surjInv_eq (mkQuot_surjective I s) (I.mkQuot s x)]
def waveSum (I : PeriodicData) (s : ℕ) {Q : Type} [Fintype Q] (r : Q → AmbientSpace) :
    (I.UnitQuot × Q → ℂ) →ₗ[ℂ] (I.QuotMod s → ℂ) :=
  ∑ q, (quotWave I s (r q)) ∘ₗ LinearMap.funLeft ℂ ℂ (fun d : I.UnitQuot => (d, q))
theorem waveSum_apply (I : PeriodicData) (s : ℕ) {Q : Type} [Fintype Q] (r : Q → AmbientSpace)
    (f : I.UnitQuot × Q → ℂ) :
    waveSum I s r f = ∑ q, quotWave I s (r q) (fun d => f (d, q)) := by
  simp only [waveSum, LinearMap.sum_apply, LinearMap.comp_apply]
  rfl
theorem waveSum_bijective {I : PeriodicData} (F : BlochDecomposition.Facts I) {s : ℕ} (hs : 0 < s)
    [Fintype (DualClasses s)] (r : DualClasses s → dualLattice s) (hr : IsDualSection s r) :
    Function.Bijective (waveSum I s (fun q => (r q : AmbientSpace))) := by
  classical
  obtain ⟨hind, htop⟩ := F.internal_sum s hs r hr
  have hmem : ∀ q (φ : I.UnitQuot → ℂ),
      quotWave I s (r q) φ ∈ blochWaveSubspace I s (r q) := fun q φ =>
    ⟨φ, fun x => quotWave_mk F hs (r q).2 φ x⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f hf
    have hzero : ∀ q₀, quotWave I s (r q₀) (fun d => f (d, q₀)) = 0 := by
      intro q₀
      rw [waveSum_apply] at hf
      have hx : quotWave I s (r q₀) (fun d => f (d, q₀)) =
          -∑ q ∈ Finset.univ.erase q₀, quotWave I s (r q) (fun d => f (d, q)) := by
        rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _
          (fun q => quotWave I s (r q) (fun d => f (d, q))) (Finset.mem_univ q₀)]
        exact hf
      have hin : quotWave I s (r q₀) (fun d => f (d, q₀)) ∈
          ⨆ j, ⨆ (_ : j ≠ q₀), blochWaveSubspace I s (r j) := by
        rw [hx]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun q hq => ?_)
        exact Submodule.mem_iSup_of_mem q
          (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hq) (hmem q _))
      exact Submodule.disjoint_def.1 (hind q₀) _ (hmem q₀ _) hin
    funext ⟨d, q₀⟩
    have hφ : (fun d => f (d, q₀)) = 0 := by
      refine F.blochWave_injective (toComplexVec (r q₀)) _ fun x => ?_
      rw [← quotWave_mk F hs (r q₀).2, hzero q₀]
      rfl
    exact congrFun hφ d
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← htop]
    refine iSup_le fun q g hg => ?_
    obtain ⟨φ, hφ⟩ := hg
    refine ⟨fun p => if p.2 = q then φ p.1 else 0, ?_⟩
    rw [waveSum_apply, Finset.sum_eq_single q]
    · funext c
      obtain ⟨x, rfl⟩ := mkQuot_surjective I s c
      simp only [if_true]
      rw [quotWave_mk F hs (r q).2, hφ]
    · intro q' _ hq'
      have : (fun d : I.UnitQuot => if q' = q then φ d else 0) = 0 := by
        funext d
        simp [hq']
      simp only [this, map_zero]
    · simp
theorem blockDiagonal_mulVec_slice {D Q : Type} [Fintype D] [DecidableEq D] [Fintype Q]
    [DecidableEq Q] (B : Q → Matrix D D ℂ) (f : D × Q → ℂ) (q : Q) :
    (fun d => (Matrix.blockDiagonal B).mulVec f (d, q)) = (B q).mulVec (fun d => f (d, q)) := by
  funext d
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]
  rw [Finset.sum_comm, Finset.sum_eq_single q]
  · simp
  · intro q' _ hq'
    simp [Ne.symm hq']
  · simp
theorem trace_det_periodicMatrix {I : PeriodicData} {T : I.Carrier → I.Carrier → ℂ}
    (F : BlochDecomposition.Facts I) (K : Periodized.Properties I I T) {s : ℕ}
    (hs : 0 < s) [Fintype I.UnitQuot] [DecidableEq I.UnitQuot] [Fintype (I.QuotMod s)]
    [DecidableEq (I.QuotMod s)] [Fintype (DualClasses s)]
    (r : DualClasses s → dualLattice s) (hr : IsDualSection s r) :
    Matrix.trace (Matrix.of (periodicMatrix I I T s)) =
        ∑ q, Matrix.trace (Matrix.of (quotSymbol I I T (toComplexVec (r q)))) ∧
      Matrix.det (Matrix.of (periodicMatrix I I T s)) =
        ∏ q, Matrix.det (Matrix.of (quotSymbol I I T (toComplexVec (r q)))) := by
  classical
  refine trace_det_of_conj_blockDiagonal _ _
    (LinearEquiv.ofBijective _ (waveSum_bijective F hs r hr)) fun f => ?_
  have hact : ∀ q (φ : I.UnitQuot → ℂ),
      (Matrix.of (periodicMatrix I I T s)).mulVec (quotWave I s (r q) φ) =
        quotWave I s (r q)
          ((Matrix.of (quotSymbol I I T (toComplexVec (r q)))).mulVec φ) := by
    intro q φ
    funext c
    obtain ⟨y, rfl⟩ := mkQuot_surjective I s c
    have h := K.acts_by_symbol s hs (r q) (r q).2 φ (quotWave I s (r q) φ)
      (fun x => quotWave_mk F hs (r q).2 φ x) y
    rw [applyKernel_eq_mulVec, applyKernel_eq_mulVec] at h
    rw [h, quotWave_mk F hs (r q).2]
  simp only [LinearEquiv.ofBijective_apply, waveSum_apply, Matrix.mulVec_sum, hact]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [blockDiagonal_mulVec_slice]
theorem holds (hWaves : BlochDecomposition.Claim)
    (hKernel : Periodized.Claim) : Claim := by
  intro I hI T δ hT hδ
  have F := hWaves I hI
  have K := hKernel I I hI hI T δ hT hδ
  refine ⟨?_, ?_⟩
  · intro s hs _ _ _ r hr
    classical
    exact (trace_det_periodicMatrix F K hs r hr).1
  · intro s hs _ _ _ _ _ r hr
    exact (trace_det_periodicMatrix F K hs r hr).2
end YangMills.Construction.PeriodicOperators.TorusTraceDet
end
