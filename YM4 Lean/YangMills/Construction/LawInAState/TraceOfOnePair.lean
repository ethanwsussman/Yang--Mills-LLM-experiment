import YangMills.Construction.LawInAState.KernelNearTwoSites
import YangMills.Construction.LawInAState.SizeOfTheBoundOfOneTrace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TraceBounds
structure IsSiteKernelFamily {N : ℕ} [NeZero N] (o : TorusFields.TorusSite N) (n R M err : ℝ)
    (Y : Finset (TorusFields.TorusSite N))
    (κ : TorusFields.TorusSite N → TorusFields.TorusPlaquette N → TorusFields.TorusPlaquette N → ℝ)
    (α : TorusFields.TorusSite N → ℝ) : Prop where
  supDist_le : ∀ y ∈ Y, (TorusFields.supDist y o : ℝ) ≤ R / 8 - n + 2
  card_le : (Y.card : ℝ) ≤ (15 * n) ^ 4
  kernel_eq_zero : ∀ y, y ∉ Y → ∀ p p', κ y p p' = 0
  diag_eq_zero : ∀ y, y ∉ Y → α y = 0
  weighted_sum_le : ∀ y ∈ Y, ∑ p ∈ TorusFields.plaquettesIn Finset.univ, ∑ p' ∈ TorusFields.plaquettesIn Finset.univ,
    |κ y p p'| * (StateLaws.siteWeight y p * StateLaws.siteWeight y p') ≤ M
  plane_sums : ∀ y ∈ Y, ∀ A ∈ ReflectionKernel.orientedPlanes, ∀ B ∈ ReflectionKernel.orientedPlanes,
    |∑ p ∈ (TorusFields.plaquettesIn Finset.univ).filter (fun p : TorusFields.TorusPlaquette N => p.2 = A),
      ∑ p' ∈ (TorusFields.plaquettesIn Finset.univ).filter (fun p' : TorusFields.TorusPlaquette N => p'.2 = B),
      κ y p p' - (if A = B then α y else 0)| ≤ err
def PairTraceApprox : Prop :=
  ∀ {N : ℕ} [NeZero N] (T : TorusFields.TorusPlaquette N → TorusFields.TorusPlaquette N → ℝ) (Ck cT n err M : ℝ) (R : ℕ)
    (o : TorusFields.TorusSite N) (Y Z : Finset (TorusFields.TorusSite N))
    (κ κ' : TorusFields.TorusSite N → TorusFields.TorusPlaquette N → TorusFields.TorusPlaquette N → ℝ)
    (α β : TorusFields.TorusSite N → ℝ), 64 ≤ n → 64 * n ≤ N → 8 ≤ R → 0 ≤ err → 0 ≤ M →
    (∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o ((R : ℝ) / 8)),
      ∀ p' ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o ((R : ℝ) / 8)),
      ∀ z : Fin 4 → ℤ, (∀ i, z i = ((p.1 - p'.1) i).valMinAbs) → z ≠ 0 →
        |T p p' - LimitForms.maxwellKernel z p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
          Ck * ((1 + Real.sqrt (LimitForms.intNormSq z)) ^ 5)⁻¹ + Ck * ((R : ℝ) ^ 4)⁻¹) →
    (∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * (R : ℝ))),
      ∀ p' ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * (R : ℝ))), |T p p'| ≤ cT) →
    (∀ p p', T p p' = T p' p) →
    IsSiteKernelFamily o n R M err Y κ α → IsSiteKernelFamily o n R M err Z κ' β →
    (∀ y ∈ Y, ∀ z ∈ Z, (∀ i, |(StateLaws.minimalSiteDiff y z i : ℝ)| ≤ 13 * n) ∧
      n ^ 2 / 4 ≤ ReflectionKernel.normSq fun i => (StateLaws.minimalSiteDiff y z i : ℝ)) →
    |∑ p₁ ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * (R : ℝ))),
        ∑ p₂ ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * (R : ℝ))),
        ∑ p₃ ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * (R : ℝ))),
        ∑ p₄ ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * (R : ℝ))),
        (∑ y, κ y p₁ p₂) * T p₂ p₃ * (∑ z, κ' z p₃ p₄) * T p₄ p₁ -
      6 / Real.pi ^ 4 * ∑ y, ∑ z, α y * β z *
        (ReflectionKernel.normSq (fun i => (StateLaws.minimalSiteDiff y z i : ℝ)) ^ 4)⁻¹| ≤
    pairTraceBound n R (1024 * |Ck| + 192000 + (|cT| + 1) * 16 ^ 5) M err
end YangMills.Construction.TraceBounds
end
