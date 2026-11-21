import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStepAreFiniteProof
import YangMills.Construction.ClusterExpansionOfAStep.TopFamiliesOnTori
import YangMills.Construction.SummableBoundsOfTheFlow.TiltOfTheImageProof
import YangMills.Construction.SummableBoundsOfTheFlow.TopFamilyHasANorm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusLumps TorusFields
namespace FamilyNorms
private theorem stepWeight_pos (p : StepParameters) (k : ℕ) : 0 < p.weight k := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem unitPlaneCurvature_eq_constant :
    unitPlaneCurvature = constantPlaneCurvature quaternionI 0 1 := rfl
private theorem unitPlaneCurvature_antisymm (μ ν : Fin 4) :
    unitPlaneCurvature μ ν = - unitPlaneCurvature ν μ := by apply _root_.YangMills.SharedProofs.p4715 <;> assumption
private theorem isLinearPotential_unitPlane :
    IsLinearPotential (constantPlaneCurvature quaternionI 0 1) (linearPotential unitPlaneCurvature) := by
  refine ⟨fun μ ν => (1 / 2 : ℝ) • unitPlaneCurvature ν μ, fun _ => 0, ?_, ?_⟩
  · intro x μ
    simp only [linearPotential, add_zero, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_comm]
  · intro μ ν
    rw [← unitPlaneCurvature_eq_constant]
    beta_reduce
    rw [unitPlaneCurvature_antisymm ν μ]
    module
private theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
private theorem bddAbove_expansionWeight_mul_exp {rt n₁ : ℝ} (hrt : 0 < rt) (hn₁ : 0 < n₁) :
    BddAbove (Set.range fun k : ℕ =>
      expansionWeight rt n₁ k * Real.exp (-(2 * (rt / 2 ^ 10) * k))) := by apply _root_.YangMills.Construction.TorusLumps.PotentialSums.bddAbove_expansionWeight_mul_exp <;> assumption
theorem topFamilyNorm_of_topFamilyOnTori (htop : TopFamilyOnTori) : topFamilyNormStatement := by
  intro p hp
  refine ⟨?_, ?_, ?_⟩
  · intro t s s' ε ε₃ g e e' hs hs' hd hdec hcomp he he'
    obtain ⟨h₁, h₂, -, -, -⟩ := htop p hp t s g hs
    obtain ⟨-, -, -, h₄, -⟩ := htop p hp t s' g hs'
    refine ⟨h₁ hd, ?_, ?_⟩
    · intro n _ hn y W hW k c X k1 k3 hX
      exact (h₂ e hdec n hn y W hW k c X k1 k3 hX).trans (he _ _ k1 k3)
    · intro n n' _ _ hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
      exact (h₄ e' hcomp n n' hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX).trans (he' m)
  · intro t g c ⟨q, hq, hv⟩
    obtain ⟨-, -, -, -, h₅⟩ := htop p hp t p.threshold g le_rfl
    have hlim : ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions), Filter.Tendsto
        (fun n : ℕ => mixedDeriv (densityOfTopFamily p.side t g n 0) (trivialField n)
          ![bondFrom 0 b, bondFrom 0 b'] ![X, X']) Filter.atTop
        (𝓝 (q b b' X X')) := by
      intro b b' X X'
      refine (hq b b' X X').congr' ?_
      filter_upwards [Filter.eventually_ge_atTop p.n₀] with n hn
      exact (h₅ b b' X X' n hn).symm
    obtain ⟨v, hs, hle⟩ := hv quaternionI 0 1 (linearPotential unitPlaneCurvature) norm_quaternionI
      (by decide) isLinearPotential_unitPlane
    refine ⟨v, ⟨fun b b' X X' => ⟨_, hlim b b' X X'⟩, ?_⟩, hle⟩
    have hterm : limitFormTerm (densityOfTopFamily p.side t g) unitPlaneCurvature unitPlaneCurvature =
        fun cc => q cc.1 cc.2 (linearPotential unitPlaneCurvature cc.1)
          (linearPotential unitPlaneCurvature cc.2) := by
      funext cc
      exact (hlim _ _ _ _).limUnder_eq
    rw [hterm]
    exact hs
  · intro m
    have hrt := hp.rt_pos
    have hn₁ := hp.n₁_pos
    have hbdd := bddAbove_expansionWeight_mul_exp hrt hn₁
    have hle : expansionWeight p.rt p.n₁ m * Real.exp (-(2 * (p.rt / 2 ^ 10) * m)) ≤
        weightGrowthSup p.rt p.n₁ :=
      le_ciSup hbdd m
    have hw : p.weight m = expansionWeight p.rt p.n₁ m := rfl
    rw [le_div_iff₀ (stepWeight_pos p m), hw]
    refine le_trans ?_ hle
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ ((hw ▸ stepWeight_pos p m).le)
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) ≤ p.rt * m := by positivity
    apply le_of_eq
    ring
end FamilyNorms
end YangMills.Construction
end
