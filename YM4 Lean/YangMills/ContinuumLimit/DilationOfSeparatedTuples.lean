import Mathlib
import YangMills.Construction.FourPointCondition.CutoffNamesTheUnitOfLength
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Conventions.StandingParameters
set_option autoImplicit false

noncomputable section

open scoped Pointwise

open Set

namespace YangMills.ContinuumLimit

open YangMills.Construction
open TorusMetric TestFunctions PeriodicLattice FourPointBounds SchwingerFunctions Conventions
open AmbientPoints (IsC1Fn)
open ReflectionPositivity.AxisMirror (Ambient)

def shiftSide (s : StandingParameters) (r : ℕ) : StandingParameters :=
  ⟨s.L, s.isAdmissible, s.K, ⟨(s.m : ℕ) + r, Nat.lt_of_lt_of_le s.m.pos (Nat.le_add_right _ _)⟩⟩

@[simp] theorem shiftSide_L (s : StandingParameters) (r : ℕ) : (shiftSide s r).L = s.L := rfl

@[simp] theorem shiftSide_K (s : StandingParameters) (r : ℕ) : (shiftSide s r).K = s.K := rfl

@[simp] theorem coe_shiftSide_m (s : StandingParameters) (r : ℕ) :
    ((shiftSide s r).m : ℕ) = (s.m : ℕ) + r := rfl

namespace DilationOfSeparatedTuples

private def torusDilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) : Torus4 T ≃ₜ Torus4 S :=
  Homeomorph.piCongrRight fun _ => AddCircle.homeomorphAddCircle T S hT.ne' hS.ne'

private theorem torusDilation_torusProj {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (v : Fin 4 → ℝ) :
    torusDilation hS hT (torusProj T v) = torusProj S ((S / T) • v) := by
  funext i
  have h : torusDilation hS hT (torusProj T v) i = ((v i * (T⁻¹ * S) : ℝ) : AddCircle S) := rfl
  rw [h]
  have h' : v i * (T⁻¹ * S) = ((S / T) • v) i := by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h']
  rfl

private theorem torusDilation_sub {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (a b : Torus4 T) :
    torusDilation hS hT (a - b) = torusDilation hS hT a - torusDilation hS hT b := by
  funext i
  exact map_sub (AddCircle.equivAddCircle T S hT.ne' hS.ne') (a i) (b i)

private theorem euclidNormVec_smul_of_pos {c : ℝ} (hc : 0 < c) (v : Fin 4 → ℝ) :
    euclidNormVec (c • v) = c * euclidNormVec v := by
  have h : ∑ μ, (c • v) μ ^ 2 = c ^ 2 * ∑ μ, v μ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [euclidNormVec, euclidNormVec, h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]

private theorem torusEuclidNorm_torusDilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (w : Torus4 T) :
    torusEuclidNorm (torusDilation hS hT w) = (S / T) * torusEuclidNorm w := by
  have hc : 0 < S / T := div_pos hS hT
  have hset : euclidNormVec '' (torusProj S ⁻¹' {torusDilation hS hT w}) =
      (S / T) • (euclidNormVec '' (torusProj T ⁻¹' {w})) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : torusProj S v = torusDilation hS hT w := hv
      have hback : (S / T) • ((T / S) • v) = v := by
        rw [smul_smul, div_mul_div_comm, mul_comm S T, div_self (mul_pos hT hS).ne', one_smul]
      refine Set.mem_smul_set.mpr ⟨euclidNormVec ((T / S) • v), ⟨(T / S) • v, ?_, rfl⟩, ?_⟩
      · apply (torusDilation hS hT).injective
        show torusDilation hS hT (torusProj T ((T / S) • v)) = torusDilation hS hT w
        rw [torusDilation_torusProj, hback, hv']
      · rw [smul_eq_mul, ← euclidNormVec_smul_of_pos hc, hback]
    · intro hr
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hr
      have hv' : torusProj T v = w := hv
      refine ⟨(S / T) • v, ?_, euclidNormVec_smul_of_pos hc v⟩
      show torusProj S ((S / T) • v) = torusDilation hS hT w
      rw [← hv', torusDilation_torusProj]
  rw [torusEuclidNorm, torusEuclidNorm, hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]

private theorem euclidDistTorus_torusDilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (x y : Torus4 T) :
    euclidDistTorus (torusDilation hS hT x) (torusDilation hS hT y) = (S / T) * euclidDistTorus x y := by
  rw [euclidDistTorus, euclidDistTorus, ← torusDilation_sub, torusEuclidNorm_torusDilation]

private theorem dilateToSide_eq_comp (L m M : ℕ) (hS : 0 < torusSide L m) (hT : 0 < torusSide L M)
    (f : FourTorus L m → ℝ) :
    dilateToSide L m M f = f ∘ torusDilation hS hT := by
  funext y
  have h : torusDilation hS hT y =
      torusProj (torusSide L m) ((torusSide L m / torusSide L M) • liftPoint y) := by
    conv_lhs => rw [← torusProj_liftPoint y]
    exact torusDilation_torusProj hS hT _
  simp only [Function.comp, dilateToSide]
  rw [h]
  rfl

private theorem torusSide_pos {L : ℕ} (hL : IsAdmissibleBlockingFactor L) (m : ℕ) :
    0 < torusSide L m := by
  have h : (0 : ℝ) < L := Nat.cast_pos.mpr (by have := hL.2; omega)
  simp only [torusSide]
  exact mul_pos two_pos (pow_pos h m)

private theorem comp_mem_separatedTuples {s₁ s₂ : StandingParameters} {c : ℝ} (hc : 0 < c)
    (e : AmbientPoints.Pt s₂ .torus ≃ AmbientPoints.Pt s₁ .torus)
    (hproj : ∀ v, e (AmbientPoints.proj s₂ .torus v) = AmbientPoints.proj s₁ .torus (c • v))
    (hdist : ∀ x y, dist (e x) (e y) = c * dist x y) {n : ℕ}
    {X : Fin n → AmbientPoints.Pt s₁ .torus → ℝ} (hX : X ∈ AmbientPoints.separatedTuples s₁ .torus n) :
    (fun i => X i ∘ ⇑e) ∈ AmbientPoints.separatedTuples s₂ .torus n := by
  simp only [AmbientPoints.separatedTuples, Set.mem_setOf_eq] at hX ⊢
  have hcont : Continuous ⇑e := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal c) (f := ⇑e) fun x y => ?_).continuous
    simp only [hdist, Real.coe_toNNReal _ hc.le, le_refl]
  have hcont' : Continuous ⇑e.symm := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal c⁻¹) (f := ⇑e.symm) fun x y => ?_).continuous
    have h := hdist (e.symm x) (e.symm y)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    simp only [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), h, inv_mul_cancel_left₀ hc.ne', le_refl]
  have hsupp : ∀ i, tsupport (X i ∘ ⇑e) ⊆ ⇑e ⁻¹' tsupport (X i) :=
    fun i => tsupport_comp_subset_preimage (X i) hcont
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · show ContDiff ℝ 1 ((X i ∘ ⇑e) ∘ AmbientPoints.proj s₂ .torus)
    have h : (X i ∘ ⇑e) ∘ AmbientPoints.proj s₂ .torus =
        (X i ∘ AmbientPoints.proj s₁ .torus) ∘ fun v => c • v := by
      funext v
      exact congrArg (X i) (hproj v)
    rw [h]
    exact ContDiff.comp (hX.1 i).1 (contDiff_const_smul c)
  · exact ((hX.1 i).2.image hcont').of_isClosed_subset (isClosed_tsupport _)
      fun x hx => ⟨e x, hsupp i hx, e.symm_apply_apply x⟩
  · exact ((hX.2 hij).preimage ⇑e).mono (hsupp i) (hsupp j)

end DilationOfSeparatedTuples

open DilationOfSeparatedTuples

theorem dilateToSide_mem_separatedTuples (L : ℕ) (h₁ h₂ : IsAdmissibleBlockingFactor L)
    (K₁ K₂ m₁ m₂ : ℕ+) {n : ℕ} {X : Fin n → FourTorus L m₁ → ℝ}
    (hX : X ∈ AmbientPoints.separatedTuples ⟨L, h₁, K₁, m₁⟩ .torus n) :
    (fun i => dilateToSide L m₁ m₂ (X i)) ∈ AmbientPoints.separatedTuples ⟨L, h₂, K₂, m₂⟩ .torus n := by
  have hS := torusSide_pos h₁ m₁
  have hT := torusSide_pos h₂ m₂
  have hc : 0 < torusSide L m₁ / torusSide L m₂ := div_pos hS hT
  have hfun : (fun i => dilateToSide L m₁ m₂ (X i)) = fun i => X i ∘ ⇑(torusDilation hS hT) :=
    funext fun i => dilateToSide_eq_comp L m₁ m₂ hS hT (X i)
  rw [hfun]
  exact comp_mem_separatedTuples (s₁ := ⟨L, h₁, K₁, m₁⟩) (s₂ := ⟨L, h₂, K₂, m₂⟩) hc
    (torusDilation hS hT).toEquiv (fun v => torusDilation_torusProj hS hT v)
    (fun x y => euclidDistTorus_torusDilation hS hT x y) hX

theorem dilate_up_mem (s : StandingParameters) (r : ℕ) {n : ℕ}
    {X : Fin n → AmbientPoints.Pt s .torus → ℝ} (hX : X ∈ AmbientPoints.separatedTuples s .torus n) :
    (fun i => dilateToSide s.L s.m ((s.m : ℕ) + r) (X i)) ∈
      AmbientPoints.separatedTuples (shiftSide s r) .torus n := by
  obtain ⟨L, h, K, m⟩ := s
  exact dilateToSide_mem_separatedTuples L h h K K m (shiftSide ⟨L, h, K, m⟩ r).m hX

theorem dilate_down_mem (s : StandingParameters) (r : ℕ) {n : ℕ}
    {X : Fin n → AmbientPoints.Pt (shiftSide s r) .torus → ℝ}
    (hX : X ∈ AmbientPoints.separatedTuples (shiftSide s r) .torus n) :
    (fun i => dilateToSide s.L ((s.m : ℕ) + r) s.m (X i)) ∈ AmbientPoints.separatedTuples s .torus n := by
  obtain ⟨L, h, K, m⟩ := s
  exact dilateToSide_mem_separatedTuples L h h K K (shiftSide ⟨L, h, K, m⟩ r).m m hX

theorem connectedSchwinger_dilate_up (hR : CutoffRescalingInvariance) {L : ℕ} (hL : 3 ≤ L)
    (m K r : ℕ) (hr : r ≤ K) (β : ℝ) {n : ℕ} (f : Fin n → FourTorus L m → ℝ) :
    connectedSchwinger L m K β f =
      connectedSchwinger L (m + r) (K - r) β (fun i => dilateToSide L m (m + r) (f i)) :=
  hR L m K (m + r) (K - r) n β hL (by omega) f

theorem connectedSchwinger_dilate_down (hR : CutoffRescalingInvariance) {L : ℕ} (hL : 3 ≤ L)
    (m K r : ℕ) (hr : r ≤ K) (β : ℝ) {n : ℕ} (f : Fin n → FourTorus L (m + r) → ℝ) :
    connectedSchwinger L (m + r) (K - r) β f =
      connectedSchwinger L m K β (fun i => dilateToSide L (m + r) m (f i)) :=
  hR L (m + r) (K - r) m K n β hL (by omega) f

end YangMills.ContinuumLimit
