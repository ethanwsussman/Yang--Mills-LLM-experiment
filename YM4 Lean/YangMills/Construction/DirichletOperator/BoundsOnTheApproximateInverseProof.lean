import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.InequalitiesOnCubesOfTheFirstKindProof
import YangMills.Construction.DirichletOperator.BlockNumbersOfTheAdjointTermsProof
import YangMills.Construction.DirichletOperator.BoundsOfTheLocalOperatorsOnEnlargedCubesProof
import YangMills.Construction.DirichletOperator.BoundsOnTheApproximateInverse
import YangMills.Construction.DirichletOperator.CubeNearASiteProof
import YangMills.Construction.DirichletOperator.CubeTermsVanishAwayFromASite
import YangMills.Construction.DirichletOperator.NormBoundsOfACubeTermOfADivergence
import YangMills.Construction.DirichletOperator.TermOfACubeInNorm
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes ApproxInverseScales
open CubeOperators (cutoffSize sourceSize)
open ApproxInverseTerms (TermsVanishAt)
noncomputable section
namespace ApproxInverseBounds
structure IsSubadditiveZero {E : Type} [Add E] [Zero E] (N : E → ℝ) : Prop where
  zero : N 0 = 0
  add : ∀ a b, N (a + b) ≤ N a + N b
structure IsAddZeroHom {E E' : Type} [Add E] [Zero E] [Add E'] [Zero E'] (Λ : E → E') : Prop where
  zero : Λ 0 = 0
  add : ∀ a b, Λ (a + b) = Λ a + Λ b
theorem IsSubadditiveZero.const_mul {E : Type} [Add E] [Zero E] {N : E → ℝ}
    (h : IsSubadditiveZero N) {a : ℝ} (ha : 0 ≤ a) :
    IsSubadditiveZero fun x => a * N x where
  zero := by simp [h.zero]
  add x y := by
    have := mul_le_mul_of_nonneg_left (h.add x y) ha
    simpa only [mul_add] using this
theorem IsAddZeroHom.comp {E E' E'' : Type} [Add E] [Zero E] [Add E'] [Zero E'] [Add E''] [Zero E'']
    {f : E' → E''} {g : E → E'} (hf : IsAddZeroHom f) (hg : IsAddZeroHom g) :
    IsAddZeroHom fun x => f (g x) where
  zero := by simp only [hg.zero, hf.zero]
  add x y := by simp only [hg.add, hf.add]
variable {𝒮 : NestedRegions}
theorem finite_fineBond (𝒮 : NestedRegions) : Finite 𝒮.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
theorem supBond_nonneg (f : 𝒮.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem supSite_nonneg (f : 𝒮.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem supTensor_nonneg {r : ℕ} (J : 𝒮.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem le_supBond (f : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond) : ‖f b‖ ≤ supBond f := by
  have := finite_fineBond 𝒮
  exact le_ciSup (f := fun b => ‖f b‖) (finite_range _).bddAbove b
theorem holderBond_nonneg (α lam : ℝ) (f : 𝒮.FineBond → ℝ) :
    0 ≤ holderBond α lam f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderBond_nonneg <;> assumption
theorem holderTensor_nonneg {r : ℕ} (α lam : ℝ) (J : 𝒮.Tensor r) :
    0 ≤ holderTensor α lam J :=
  Real.iSup_nonneg fun _ => holderBond_nonneg α lam _
theorem le_holderBond (α lam : ℝ) (f : 𝒮.FineBond → ℝ) (b b' : 𝒮.FineBond)
    (hd : b.dir = b'.dir) (h0 : 0 < siteLOneDist b.source b'.source)
    (hle : siteLOneDist b.source b'.source ≤ lam) :
    (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖ ≤ holderBond α lam f := by
  have := finite_fineBond 𝒮
  refine le_csSup ?_ ⟨b, b', hd, h0, hle, rfl⟩
  refine (finite_range fun p : 𝒮.FineBond × 𝒮.FineBond =>
    (lam / siteLOneDist p.1.source p.2.source) ^ α * ‖f p.2 - f p.1‖).bddAbove.mono ?_
  rintro r ⟨c, c', -, -, -, rfl⟩
  exact ⟨(c, c'), rfl⟩
theorem ltwoBond_nonneg (f : 𝒮.FineBond → ℝ) : 0 ≤ ltwoBond f := Real.sqrt_nonneg _
theorem ltwoTensor_nonneg {r : ℕ} (J : 𝒮.Tensor r) : 0 ≤ ltwoTensor J := by apply _root_.YangMills.Construction.CornerGreen.ltwoTensor_nonneg' <;> assumption
theorem levelScale_nonneg (y : 𝒮.Point) : 0 ≤ 𝒮.levelScale y := by apply _root_.YangMills.Construction.RemainderAdjoint.levelScale_nonneg <;> assumption
theorem mem_centresAt_level {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) :
    y ∈ 𝒮.centresAt (𝒮.level y) := by apply _root_.YangMills.Construction.CubeNearSite.mem_centresAt_level <;> assumption
theorem expWeight_nonneg (y y' : 𝒮.Point) : 0 ≤ expWeight y y' := (Real.exp_pos _).le
theorem sourceSize_nonneg {r : ℕ} (ε lam : ℝ) (J : 𝒮.Tensor r) :
    0 ≤ sourceSize ε lam J := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.sourceNormSum_nonneg <;> assumption
end ApproxInverseBounds
end
end YangMills.Construction
