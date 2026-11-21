import YangMills.Construction.TorusOrFourSpace.FactsOnTheEffectiveConstants
import YangMills.Construction.TorusOrFourSpace.FromTheFamilyToAllSeparatedTuples
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesInBallsAndTheirSeparation
import YangMills.Construction.TorusOrFourSpace.TheTwoKindsOfSequencesOfC1Forms
import YangMills.Construction.TorusOrFourSpace.UniformApproximationOnHierarchiesObeyingABoundFunction
import YangMills.Construction.TorusOrFourSpace.ZeroFamilyObeysEveryBoundFunction
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.UniformHierarchyApprox
open Kind
private theorem cappedGap_spec (D : Params) (E : Kind) {n : ℕ} (f : FnTuple D E n)
    (h : 0 < supportGap D E f) :
    0 < cappedGap D E f ∧ cappedGap D E f ≤ 1 ∧
      ENNReal.ofReal (cappedGap D E f) ≤ supportGap D E f := by
  have hfin : min 1 (supportGap D E f) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
  have hmin : 0 < min 1 (supportGap D E f) := lt_min zero_lt_one h
  refine ⟨ENNReal.toReal_pos hmin.ne' hfin, ?_, ?_⟩
  · exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)
  · rw [cappedGap, ENNReal.ofReal_toReal hfin]
    exact min_le_right _ _
private theorem tendsto_inv_pnat_nhdsGT :
    Filter.Tendsto (fun k : ℕ+ => 1 / ((k : ℕ) : ℝ)) Filter.atTop (𝓝[>] 0) := by
  have hk : Filter.Tendsto (fun k : ℕ+ => (k : ℕ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨Nat.succPNat b, fun a ha => by
      have hle : ((Nat.succPNat b : ℕ+) : ℕ) ≤ (a : ℕ) := ha
      rw [Nat.succPNat_coe] at hle
      omega⟩
  refine tendsto_nhdsWithin_iff.2
    ⟨tendsto_one_div_atTop_nhds_zero_nat.comp hk, Filter.Eventually.of_forall fun k => ?_⟩
  exact Set.mem_Ioi.2 (one_div_pos.2 (by exact_mod_cast k.pos))
private theorem func_sub_func_le_of_approximant
    (hExt : SeparatedExtension.Statement)
    (hSeq : C1FormSeqKinds.Statement)
    (D : Params) (E : Kind) {θ : RadiusRatio} (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E) (C : BoundFamily) {n : ℕ} (hn : 2 ≤ n) {f : FnTuple D E n}
    {r : ℝ} (hr : 0 < r) (hf : f ∈ sepC1TuplesInBall D E n (ENNReal.ofReal r))
    {d : ℝ} (hd : 0 < d) (hgap : ENNReal.ofReal d ≤ supportGap D E f) {ε : ℝ} (hε : 0 < ε)
    {φ : FnTuple D E n}
    (hφ : DiagonalLimits.IsFamilyApproximant D E f hf.1 d hd F ε φ)
    (Φ : Hierarchy D E) (hΦ : Φ ∈ boundedHierarchies D E C) :
    ∃ hφ' : φ ∈ sepC1Tuples D E n,
      |Φ.func n hn ⟨f, hf.1⟩ - Φ.func n hn ⟨φ, hφ'⟩| ≤
        effConstAt P E C n (d / 3) (r + d / 3) *
          DiagonalLimits.approxDefect D E f ε := by
  obtain ⟨Ψ, hΨ, -⟩ := (hSeq D θ E C).2.2.2 Φ hΦ
  have hfamily : Ψ.IsHierarchyFamily := hΨ.isHierarchyFamily fun _ => hΦ
  obtain ⟨hnear, hunit, -⟩ := hExt D E θ P F C
  have hserves := hunit _ Ψ hfamily n hn r hr f hf d hd hgap
  obtain ⟨hfk, hφk, hle⟩ :=
    (hnear _ _ Ψ n hn r hr f hf d hd hgap).2 1 hserves ε hε φ hφ ⟨1, Set.mem_univ _⟩ (by simp)
  refine ⟨hφk.1, ?_⟩
  rw [hΨ.2 _ n hn ⟨f, hfk⟩, hΨ.2 _ n hn ⟨φ, hφk⟩] at hle
  exact hle
private theorem uniformOnHierarchies_of
    (hApprox : DiagonalLimits.FamilyApproximation.Statement)
    (hExt : SeparatedExtension.Statement)
    (hSeq : C1FormSeqKinds.Statement)
    (hBasics : SeparatedTupleFacts.SeparatedTupleBasics)
    (hConst : EffectiveConstantFacts.Claim)
    (hZero : ZeroFamily.ZeroHierarchyExists)
    (D : Params) (E : Kind) (θ : RadiusRatio) (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E) (C : BoundFamily) : UniformOnHierarchies D E P F C := by
  intro n hn f hf r hr hfr
  obtain ⟨-, hgapf, -⟩ := hBasics D E n hn f hf
  obtain ⟨hd, hd1, hdgap⟩ := cappedGap_spec D E f hgapf.1.1
  have hε : ∀ k : ℕ+, (0 : ℝ) < 1 / ((k : ℕ) : ℝ) := fun k =>
    one_div_pos.2 (by exact_mod_cast k.pos)
  refine ⟨hd, hd1, hdgap, fun k => (hApprox D E F n hn f hf _ hd hdgap _ (hε k)).2.1, ?_,
    fun φ hφ => ⟨fun k => ⟨(hφ k).1, hn⟩, fun k => ?_, ?_⟩⟩
  · exact hConst.2.2.1 D θ P E C n hn _ _ (div_pos hd three_pos)
      (add_pos hr (div_pos hd three_pos))
  · obtain ⟨Φ₀, hΦ₀, -⟩ := hZero D E C
    obtain ⟨hφ', -⟩ :=
      func_sub_func_le_of_approximant hExt hSeq D E P F C hn hr hfr hd hdgap (hε k) (hφ k) Φ₀ hΦ₀
    refine ⟨hφ', fun Φ hΦ => ?_⟩
    obtain ⟨_, hle⟩ :=
      func_sub_func_le_of_approximant hExt hSeq D E P F C hn hr hfr hd hdgap (hε k) (hφ k) Φ hΦ
    exact hle
  · have hlim := (hApprox D E F n hn f hf _ hd hdgap 1 one_pos).2.2.2
    simpa using (hlim.comp tendsto_inv_pnat_nhdsGT).const_mul (tupleConstant D E P C f r)
private theorem tupleConstantDependence_holds : TupleConstantDependence := by
  intro D D' E E' θ θ' P P' C n _ f f' r _ _ _ hgap hallowed hradii hpart
  have hcap : cappedGap D E f = cappedGap D' E' f' := by
    simp only [cappedGap, hgap]
  unfold tupleConstant effConstAt effConst
  rw [hcap]
  by_cases h : r + cappedGap D' E' f' / 3 ∈ allowedRadii D' E'
  · rw [if_pos (hallowed.symm ▸ h), if_pos h]
  · rw [if_neg (hallowed.symm ▸ h), if_neg h, hpart, hradii]
private theorem allowedRadiiDependence_holds : AllowedRadiiDependence := by
  intro D D' E hL hm
  cases E with
  | euclidean => rfl
  | torus => simp only [allowedRadii, Params.side, hL, hm]
private theorem defectDependence_holds : DefectDependence := by
  intro D D' E E' n _ f f' _ _ hM hnorm k
  simp only [DiagonalLimits.approxDefect, sharpNormReal, hnorm, hM]
theorem claim_holds
    (hApprox : DiagonalLimits.FamilyApproximation.Statement)
    (hExt : SeparatedExtension.Statement)
    (hSeq : C1FormSeqKinds.Statement)
    (hBasics : SeparatedTupleFacts.SeparatedTupleBasics)
    (hConst : EffectiveConstantFacts.Claim)
    (hZero : ZeroFamily.ZeroHierarchyExists) : Claim :=
  ⟨fun D E θ P F C =>
      uniformOnHierarchies_of hApprox hExt hSeq hBasics hConst hZero D E θ P F C,
    tupleConstantDependence_holds, allowedRadiiDependence_holds, hConst.2.2.2.2,
    defectDependence_holds⟩
end YangMills.Construction.PeriodicSpace.UniformHierarchyApprox
