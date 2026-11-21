import YangMills.Construction.FourPointCondition.ConnectedFunctionsAreHomogeneousProof
import YangMills.Construction.FourPointCondition.TuplesOfAQuadrupleOfTheClass
import YangMills.Construction.Torus.GeometryOfASeparatedQuadruple
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TestFunctions PeriodicLattice ResponseInTheExpansion TorusLumps TorusMetric
namespace FourPointCondition
private theorem torusEuclidNorm_sub_le_add {S : ℝ} (u v : Torus4 S) :
    torusEuclidNorm (u - v) ≤ torusEuclidNorm u + torusEuclidNorm v := by
  rw [AmbientPoints.torusEuclidNorm_eq_norm, AmbientPoints.torusEuclidNorm_eq_norm u,
    AmbientPoints.torusEuclidNorm_eq_norm v, WithLp.toLp_sub]
  exact norm_sub_le _ _
private theorem isLipschitzFor_const_mul {X : Type*} {dist : X → X → ℝ} (c : ℝ) {φ : X → ℝ}
    (h : IsLipschitzFor dist φ) :
    IsLipschitzFor dist (fun x => c * φ x) := by apply _root_.YangMills.SharedProofs.p11306 <;> assumption
private theorem bestLipschitzConstant_const_mul_le {X : Type*} {dist : X → X → ℝ} {c : ℝ} (hc : 0 < c)
    {φ : X → ℝ} (h : IsLipschitzFor dist φ) :
    bestLipschitzConstant dist (fun x => c * φ x) ≤ c * bestLipschitzConstant dist φ := by
  have hb : BddBelow {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖c * φ x - c * φ y‖ ≤ C * dist x y} :=
    ⟨0, fun C hC => hC.1⟩
  have hne : {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖φ x - φ y‖ ≤ C * dist x y}.Nonempty := by
    obtain ⟨C, hC, hφ⟩ := h
    exact ⟨C, hC, hφ⟩
  have key : bestLipschitzConstant dist (fun x => c * φ x) / c ≤ bestLipschitzConstant dist φ := by
    refine le_csInf hne fun C hC => ?_
    rw [div_le_iff₀ hc]
    refine csInf_le hb ⟨by have := hC.1; positivity, fun x y => ?_⟩
    have e : ‖c * φ x - c * φ y‖ = c * ‖φ x - φ y‖ := by
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_pos hc]
    rw [e, mul_comm C c, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC.2 x y) hc.le
  rw [div_le_iff₀ hc] at key
  linarith
private theorem tsupport_const_mul {X : Type*} [TopologicalSpace X] {c : ℝ} (hc : c ≠ 0) (φ : X → ℝ) :
    tsupport (fun x => c * φ x) = tsupport φ := by
  unfold tsupport
  congr 1
  ext x
  simp [Function.mem_support, hc]
private theorem uniformNorm_const_mul {X : Type*} {c : ℝ} (hc : 0 ≤ c) (φ : X → ℝ) :
    uniformNorm (fun x => c * φ x) = c * uniformNorm φ := by
  unfold uniformNorm
  rw [Real.mul_iSup_of_nonneg hc]
  congr 1
  funext x
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc]
private theorem isSeparatedTestTuple_comp {P : StepParameters} {m : ℕ} {r θ : ℝ} {p q : ℕ}
    {g : Fin p → FourTorus P.side m → ℝ}
    (h : IsSeparatedTestTuple P m r θ g) (σ : Fin q → Fin p) (hσ : Function.Injective σ) :
    IsSeparatedTestTuple P m r θ (fun t => g (σ t)) where
  uniformNorm_eq := fun i => h.uniformNorm_eq (σ i)
  lipschitz := fun i => h.lipschitz (σ i)
  lipConst_le := fun i => h.lipConst_le (σ i)
  separated := ⟨h.separated.1, fun i k hik => h.separated.2 (σ i) (σ k) (fun hh => hik (hσ hh))⟩
  dist_le := fun i j => h.dist_le (σ i) (σ j)
theorem normalizedQuadrupleIsTestTuple_of_multilinearity
    (hM : TorusCumulants.Multilinearity.claim)
    (hG : QuadrupleGeometry.QuadrupleGeometryStatement) : normalizedQuadrupleIsTestTuple := by
  intro P K m hs d θ f hf
  obtain ⟨hsc, h40, hfL, hpairs⟩ := id hf
  have hne : ∀ i : Fin 4, i ≠ i + 1 := by decide
  have hd : 0 < d := hsc.1
  have hθ : 0 < θ := hsc.2.1
  obtain ⟨-, ⟨-, hbd⟩, -⟩ := hM.2 ⟨P.side, hs, K, m⟩ 1 1 one_pos le_rfl
  have hpos : ∀ i, 0 < uniformNorm (f i) := by
    intro i
    obtain ⟨x₁, x₂, hb₁, -, -, -⟩ := hpairs i (i + 1) (hne i)
    obtain ⟨y, hy⟩ := hb₁.2.2.1
    obtain ⟨C, hC⟩ := hbd (f i) (hfL i).1
    have hbdd : BddAbove (Set.range fun x => ‖f i x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
    have h1 : ‖f i y‖ ≤ uniformNorm (f i) := le_ciSup hbdd y
    have h2 : 0 < ‖f i y‖ := norm_pos_iff.2 hy
    linarith
  have htuple : IsSeparatedTestTuple P m d θ (fun i x => (uniformNorm (f i))⁻¹ * f i x) := by
    have hc : ∀ i, 0 < (uniformNorm (f i))⁻¹ := fun i => inv_pos.2 (hpos i)
    refine ⟨fun i => ?_, fun i => isLipschitzFor_const_mul _ (hfL i).1, fun i => ?_, ⟨hd, fun i k hik => ?_⟩,
      fun i j x hx z hz => ?_⟩
    · rw [uniformNorm_const_mul (hc i).le, inv_mul_cancel₀ (hpos i).ne']
    · obtain ⟨x₁, x₂, hb₁, -, -, -⟩ := hpairs i (i + 1) (hne i)
      have h1 : bestLipschitzConstant euclidDistTorus (f i) ≤ uniformNorm (f i) / (θ * d) := hb₁.2.2.2.2.2
      have h2 := bestLipschitzConstant_const_mul_le (dist := euclidDistTorus) (hc i) (hfL i).1
      have h3 : (uniformNorm (f i))⁻¹ * bestLipschitzConstant euclidDistTorus (f i) ≤ 1 / (θ * d) := by
        calc (uniformNorm (f i))⁻¹ * bestLipschitzConstant euclidDistTorus (f i)
            ≤ (uniformNorm (f i))⁻¹ * (uniformNorm (f i) / (θ * d)) := mul_le_mul_of_nonneg_left h1 (hc i).le
          _ = 1 / (θ * d) := by
              have := (hpos i).ne'
              field_simp
      exact h2.trans h3
    · obtain ⟨x₁, x₂, -, -, hl, -⟩ := hpairs i k hik
      simp only [tsupport_const_mul (hc i).ne', tsupport_const_mul (hc k).ne']
      exact hl
    · simp only [tsupport_const_mul (hc i).ne', tsupport_const_mul (hc j).ne'] at hx hz
      by_cases hij : i = j
      · subst hij
        obtain ⟨x₁, x₂, hb₁, -, -, -⟩ := hpairs i (i + 1) (hne i)
        have hs' := hb₁.2.2.2.1
        have hx' : torusEuclidNorm (x - x₁) ≤ d := hs' hx
        have hz' : torusEuclidNorm (z - x₁) ≤ d := hs' hz
        have e : x - z = (x - x₁) - (z - x₁) := by abel
        have h2 : torusEuclidNorm (x - z) ≤ torusEuclidNorm (x - x₁) + torusEuclidNorm (z - x₁) := by
          rw [e]
          exact torusEuclidNorm_sub_le_add _ _
        change torusEuclidNorm (x - z) ≤ 10 * d
        linarith
      · exact ((hG.2 ⟨P.side, hs, K, m⟩ d θ hsc.1 hsc.2 h40 f hf).2.1.1 i j hij x hx z hz).2
  refine ⟨hpos, htuple, fun i j hij => ?_⟩
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hcomp := isSeparatedTestTuple_comp htuple ![i, j] hinj
  convert hcomp using 1
  funext t
  fin_cases t <;> rfl
end FourPointCondition
end YangMills.Construction
end
