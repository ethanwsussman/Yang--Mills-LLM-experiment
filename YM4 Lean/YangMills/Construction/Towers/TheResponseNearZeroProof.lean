import YangMills.Construction.Towers.ExistenceOfTheBoundOfTheResponseProof
import YangMills.Construction.Towers.StabilityOfTheSaddleSystemNearZero
import YangMills.Construction.Towers.TheResponseNearZero
import YangMills.Construction.Towers.TheSaddleSystemOfTheResponseAtAPoint
import YangMills.Construction.Towers.TheTrialFormOfTheResponseNearZero
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.ResponseAtSmallMomentum
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.PlaneWaveCalculus (EdgeCoeffFacts topEdgeComponent)
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.Tower.PlaneWaves
open YangMills.Construction.Tower.ResponseProperties
open YangMills.Construction.Tower.FreeStrip (halfSupRate)
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem edgeFourierCoeff_mem_traceless (L k : ℕ) [Finite (VertexClass L k)]
    (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k b μ m ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.edgeFourierCoeff_mem <;> assumption
theorem topEdgeComponent_mem_traceless (L k : ℕ) (z : (colourEdges L k k).UnitQuot → ℂ)
    (μ : Fin 4) : topEdgeComponent L k z μ ∈ Matrices.ComplexMatrix2.traceless :=
  ofPauliCoeffs_mem_traceless _ _
theorem pauliCoeff_add {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
def pauliVector (F : Fin 4 → Matrices.ComplexMatrix2) : EuclideanSpace ℂ (Fin 4 × Fin 3) :=
  WithLp.toLp 2 fun i => pauliCoeff i.2 (F i.1)
theorem pauliFamilyNorm_eq_norm (F : Fin 4 → Matrices.ComplexMatrix2) :
    pauliFamilyNorm F = ‖pauliVector F‖ := by
  rw [EuclideanSpace.norm_eq, pauliFamilyNorm]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [pauliNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rfl
theorem pauliFamilyNorm_sub_le {F G H : Fin 4 → Matrices.ComplexMatrix2}
    (hF : ∀ μ, F μ ∈ Matrices.ComplexMatrix2.traceless)
    (hG : ∀ μ, G μ ∈ Matrices.ComplexMatrix2.traceless)
    (hH : ∀ μ, H μ ∈ Matrices.ComplexMatrix2.traceless) :
    pauliFamilyNorm (fun μ => F μ - H μ) ≤
      pauliFamilyNorm (fun μ => F μ - G μ) + pauliFamilyNorm (fun μ => G μ - H μ) := by
  have e : pauliVector (fun μ => F μ - H μ) =
      pauliVector (fun μ => F μ - G μ) + pauliVector (fun μ => G μ - H μ) := by
    ext i
    have h := pauliCoeff_add (Submodule.sub_mem _ (hF i.1) (hG i.1))
      (Submodule.sub_mem _ (hG i.1) (hH i.1)) i.2
    rw [sub_add_sub_cancel] at h
    simpa [pauliVector] using h
  rw [pauliFamilyNorm_eq_norm, pauliFamilyNorm_eq_norm, pauliFamilyNorm_eq_norm, e]
  exact norm_add_le _ _
theorem pauliFamilyNorm_topEdgeComponent_zero (L k : ℕ) :
    pauliFamilyNorm (topEdgeComponent L k 0) = 0 := by
  have e : ∀ μ, topEdgeComponent L k 0 μ = 0 := fun μ => by
    simp [topEdgeComponent, ofPauliCoeffs]
  have z : pauliNorm (0 : Matrices.ComplexMatrix2) = 0 := by
    have h : ∀ a : Fin 3, pauliCoeff a (0 : Matrices.ComplexMatrix2) = 0 := fun a => by
      have h := pauliCoeff_add (Submodule.zero_mem Matrices.ComplexMatrix2.traceless)
        (Submodule.zero_mem Matrices.ComplexMatrix2.traceless) a
      rw [add_zero] at h
      exact left_eq_add.1 h
    simp [pauliNorm, h]
  simp [pauliFamilyNorm, e, z]
theorem finite_vertexClass {L k : ℕ} (h : Finite (colourVertices L k 0).UnitQuot) :
    Finite (VertexClass L k) := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.finite_vertexClass <;> assumption
theorem edgeFourierCoeff_sub (L k : ℕ) [Finite (VertexClass L k)]
    (b b' : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k (b - b') μ m =
      edgeFourierCoeff L k b μ m - edgeFourierCoeff L k b' μ m := by
  have := Fintype.ofFinite (VertexClass L k)
  have e : ∀ β, edgeFieldOfClasses L k (b - b') β =
      edgeFieldOfClasses L k b β - edgeFieldOfClasses L k b' β := by
    intro β
    simp [edgeFieldOfClasses, ofPauliCoeffs, sub_smul, Finset.sum_sub_distrib]
  simp only [edgeFourierCoeff, PlaneWaves.fourierCoeff, e, smul_sub]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.sum_sub_distrib, smul_sub]
theorem pauliFamilyNorm_le_wNorm {L k : ℕ} (hC : EdgeCoeffFacts L k)
    (c : (colourEdges L k 0).UnitQuot → ℂ) {m : Fin 4 → ℤ} (hm : m ∈ freqBox L k) :
    pauliFamilyNorm (fun μ => edgeFourierCoeff L k c μ m) ≤
      wNorm ((colourEdges L k 0).quotWeight 1) c := by
  rw [pauliFamilyNorm]
  refine Real.sqrt_le_iff.2 ⟨Real.sqrt_nonneg _, ?_⟩
  rw [hC.norm_sq c]
  exact Finset.single_le_sum
    (f := fun m => ∑ μ, pauliNorm (edgeFourierCoeff L k c μ m) ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hm
theorem wNorm_neg {J : Type} (w : J → ℝ) (f : J → ℂ) : wNorm w (-f) = wNorm w f := by
  simp [wNorm]
theorem zero_mem_freqBox (L k : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) :
    (0 : Fin 4 → ℤ) ∈ freqBox L k := by
  rw [mem_freqBox]
  intro ν
  have h₀ : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have h₁ : (1 : ℝ) ≤ (finestMesh L k)⁻¹ := by
    have e : (finestMesh L k)⁻¹ = (L : ℝ) ^ k := by
      simp [finestMesh, meshAt, zpow_neg]
    rw [e]
    exact one_le_pow₀ h₀
  simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
  linarith
theorem continuous_euclidNorm : Continuous euclidNorm := by
  unfold euclidNorm
  fun_prop
theorem holds (hI : PeriodicOperators.TowerIndexSets.Claim)
    (hC : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hA : ResponseSaddleSystem.Claim)
    (hB : SaddleStability.UniformBoundNearZero)
    (hT : TrialResponse.TrialFieldNearZero) : Statement := by
  intro δ₀ hδ L hL k hk
  obtain ⟨pS, -, -⟩ := hI L hL k 0 (Nat.zero_le k)
  have hfin : Finite (VertexClass L k) := finite_vertexClass pS.finite_quot
  have hcoef : EdgeCoeffFacts L k := (hC L hL k hk).2.2.1
  obtain ⟨C₁, N₁, hN₁, h₁⟩ := hB L hL k hk
  obtain ⟨C₂, N₂, hN₂, h₂⟩ := hT δ₀ hδ L hL k hk
  have hN₃ : {p : Fin 4 → ℂ | euclidNorm p < 1} ∈ nhds (0 : Fin 4 → ℂ) := by
    refine (isOpen_lt continuous_euclidNorm continuous_const).mem_nhds ?_
    simp [euclidNorm]
  refine ⟨|C₁| * |C₂| + |C₂|, N₁ ∩ N₂ ∩ {p | euclidNorm p < 1},
    inter_mem (inter_mem hN₁ hN₂) hN₃, ?_⟩
  rintro p ⟨⟨hp₁, hp₂⟩, hp₃⟩ hpt ε
  obtain ⟨b₀, ⟨hc₀, hcm⟩, hQ, hX, hE⟩ := h₂ p hp₂ hpt ε
  obtain ⟨hs₁, hs₂⟩ := hA δ₀ hδ L hL k hk p hpt ε
  set e := pauliFamilyNorm (topEdgeComponent L k ε) with he
  set r := euclidNorm p with hr
  have he₀ : 0 ≤ e := Real.sqrt_nonneg _
  have hr₀ : 0 ≤ r := Real.sqrt_nonneg _
  have hr₁ : r < 1 := hp₃
  have key := h₁ p hp₁ (responseSymbolForm L k p ε - b₀) (defectSymbol L k p ε)
  rw [map_sub, map_sub, hs₁, hs₂, hQ, sub_self, pauliFamilyNorm_topEdgeComponent_zero, add_zero,
    sub_sub_cancel_left, wNorm_neg] at key
  have hb₀ : 0 ≤ wNorm ((colourEdges L k 0).quotWeight 1) (responseSymbolForm L k p ε - b₀) :=
    Real.sqrt_nonneg _
  have hn₀ : 0 ≤ pauliFamilyNorm (topEdgeComponent L k (defectSymbol L k p ε)) :=
    Real.sqrt_nonneg _
  have hA₀ : 0 ≤ r ^ 2 * e := by positivity
  have hXabs : wNorm ((colourEdges L k 0).quotWeight 1)
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X p b₀) ≤
      |C₂| * (r ^ 2 * e) := hX.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hA₀)
  have hsum : wNorm ((colourEdges L k 0).quotWeight 1) (responseSymbolForm L k p ε - b₀) +
      pauliFamilyNorm (topEdgeComponent L k (defectSymbol L k p ε)) ≤
      |C₁| * |C₂| * (r ^ 2 * e) := by
    refine key.trans ?_
    have hx₀ : 0 ≤ wNorm ((colourEdges L k 0).quotWeight 1)
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X p b₀) :=
      Real.sqrt_nonneg _
    calc C₁ * _ ≤ |C₁| * _ := mul_le_mul_of_nonneg_right (le_abs_self _) hx₀
      _ ≤ |C₁| * (|C₂| * (r ^ 2 * e)) := mul_le_mul_of_nonneg_left hXabs (abs_nonneg _)
      _ = _ := by ring
  have hD : 0 ≤ |C₁| * |C₂| := by positivity
  have hC₂ : 0 ≤ |C₂| := abs_nonneg _
  have hDA : |C₁| * |C₂| * (r ^ 2 * e) ≤ (|C₁| * |C₂| + |C₂|) * (r ^ 2 * e) := by nlinarith
  refine ⟨fun m hm hm₀ => ?_, ?_, ?_⟩
  · have h := pauliFamilyNorm_le_wNorm hcoef (responseSymbolForm L k p ε - b₀) hm
    have e₁ : (fun μ => edgeFourierCoeff L k (responseSymbolForm L k p ε - b₀) μ m) =
        fun μ => edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m := by
      funext μ
      rw [edgeFourierCoeff_sub, hcm m hm hm₀ μ, sub_zero]
    rw [e₁] at h
    linarith
  · have hm₀ := zero_mem_freqBox L k hL
    have h := pauliFamilyNorm_le_wNorm hcoef (responseSymbolForm L k p ε - b₀) hm₀
    have e₁ : (fun μ => edgeFourierCoeff L k (responseSymbolForm L k p ε - b₀) μ 0) =
        fun μ => edgeFourierCoeff L k (responseSymbolForm L k p ε) μ 0 -
          edgeFourierCoeff L k b₀ μ 0 := by
      funext μ
      rw [edgeFourierCoeff_sub]
    rw [e₁] at h
    have tri := pauliFamilyNorm_sub_le
      (F := fun μ => edgeFourierCoeff L k (responseSymbolForm L k p ε) μ 0)
      (G := fun μ => edgeFourierCoeff L k b₀ μ 0) (H := topEdgeComponent L k ε)
      (fun μ => edgeFourierCoeff_mem_traceless L k _ μ 0)
      (fun μ => edgeFourierCoeff_mem_traceless L k _ μ 0)
      (topEdgeComponent_mem_traceless L k ε)
    have hEabs : pauliFamilyNorm (fun μ => edgeFourierCoeff L k b₀ μ 0 - topEdgeComponent L k ε μ) ≤
        |C₂| * (r * e) := hE.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hsq : r ^ 2 * e ≤ r * e := by
      have : r ^ 2 ≤ r := by nlinarith
      exact mul_le_mul_of_nonneg_right this he₀
    have h₃ : |C₁| * |C₂| * (r ^ 2 * e) ≤ |C₁| * |C₂| * (r * e) :=
      mul_le_mul_of_nonneg_left hsq hD
    have : pauliFamilyNorm (fun μ => edgeFourierCoeff L k (responseSymbolForm L k p ε) μ 0 -
        topEdgeComponent L k ε μ) ≤ |C₁| * |C₂| * (r * e) + |C₂| * (r * e) := by linarith
    calc _ ≤ _ := this
      _ = _ := by ring
  · linarith
end YangMills.Construction.Tower.ResponseAtSmallMomentum
end
