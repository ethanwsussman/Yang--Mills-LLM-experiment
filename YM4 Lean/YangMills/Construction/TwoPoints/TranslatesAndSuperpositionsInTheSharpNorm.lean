import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def TranslateModulusBound (σ : FixedScale) : Prop :=
  ∀ f ∈ compactC1Complex,
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f ∧
      TestFunctions.lipConstR4 f ≤ gradSup f ∧
      gradSupENN f < ∞ ∧
      (∀ δ : ℝ, 0 ≤ δ → gradOscENNReal f δ < ∞) ∧
      (∀ a b : AmbientSpace, σ.sharpNorm (translateFun a f - translateFun b f) ≤
        σ.translationModulus f (euclidNorm (a - b))) ∧
      Tendsto (σ.translationModulus f) (𝓝[>] 0) (𝓝 0)
def RiemannSumConvApprox (σ : FixedScale) : Prop :=
  ∀ k ∈ ccIn (univ : Set AmbientSpace), ∀ φ ∈ compactC1Complex, ∀ δ : ℝ, 0 < δ →
    convolve k φ ∈ compactC1Complex ∧
      tsupport (convolve k φ) ⊆ minkowskiSum (tsupport k) (tsupport φ) ∧
      {j : Fin 4 → ℤ | setIntegralOf (gridCube δ j) k • translateFun (gridCenter δ j) φ ≠ 0}.Finite ∧
      σ.sharpNorm (convolve k φ - cubeRiemannSum δ k φ) ≤
        l1Norm k * σ.translationModulus φ δ ∧
      σ.sharpNorm (cubeRiemannSum δ k φ) ≤ l1Norm k * σ.sharpNorm φ ∧
      σ.sharpNorm (convolve k φ) ≤ l1Norm k * σ.sharpNorm φ ∧
      ((∀ x, IsRealNonneg (k x)) → lebesgueIntegral k = 1 →
        tsupport k ⊆ euclidClosedBall (0 : AmbientSpace) δ →
        σ.sharpNorm (convolve k φ - φ) ≤ σ.translationModulus φ δ)
def FormConvDoubleIntegral (σ : FixedScale) : Prop :=
  ∀ S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ, IsDisjointForm S → IsAdmissibleForm σ S →
    ∀ ε : ℝ, 0 < ε → ∀ φ₁ ∈ cc1NearZero ε, ∀ φ₂ ∈ cc1NearZero ε,
      (∀ z ∈ farShifts ε,
        translateFun z φ₂ ∈ compactC1Complex ∧ DisjointSupports φ₁ (translateFun z φ₂)) ∧
      ContinuousOn (shiftPairing S φ₁ φ₂) {z | 2 * ε < euclidNorm z} ∧
      ∀ k₁ ∈ ccIn (univ : Set AmbientSpace),
        ∀ k₂ ∈ ccIn (univ : Set AmbientSpace),
          (∀ z₁ ∈ tsupport k₁, ∀ z₂ ∈ tsupport k₂, 2 * ε < euclidNorm (z₂ - z₁)) →
            DisjointSupports (convolve k₁ φ₁) (convolve k₂ φ₂) ∧
              complexifyForm S (convolve k₁ φ₁) (convolve k₂ φ₂) =
                lebesgueIntegral fun z₂ : AmbientSpace => lebesgueIntegral fun z₁ : AmbientSpace =>
                  k₁ z₁ * k₂ z₂ * shiftPairing S φ₁ φ₂ (z₂ - z₁)
def FormMollifierLimit (σ : FixedScale) : Prop :=
  ∀ S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ, IsDisjointForm S → IsAdmissibleForm σ S →
    ∀ f ∈ compactC1Complex, ∀ h ∈ compactC1Complex, DisjointSupports f h →
      ∀ ρ : ℕ → AmbientSpace → ℂ, IsMollifierSeq ρ →
        (∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          DisjointSupports (convolve (ρ n) f) (convolve (ρ n) h)) ∧
        Tendsto (fun n : ℕ => complexifyForm S (convolve (ρ n) f) (convolve (ρ n) h)) atTop
          (𝓝 (complexifyForm S f h))
def SharpNormTranslates : Prop :=
  ∀ σ : FixedScale,
    TranslateModulusBound σ ∧ RiemannSumConvApprox σ ∧
      FormConvDoubleIntegral σ ∧ FormMollifierLimit σ
end YangMills.Construction.TwoPoints
end
