import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetNormsAffine
open JetQuad
def affinePath {X : PeriodicData} (A B : JetQuad X X) (t : ℝ) : JetQuad X X :=
  add A (smul (t : ℂ) B)
def Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    ∀ X X' : PeriodicData, IsPeriodic X → IsPeriodic X' →
      (∀ T : JetQuad X X', IsJet δ p T → jetNorm δ p T < ∞) ∧
      ∀ A B : JetQuad X X, IsJet δ p A → IsJet δ p B →
        ∀ J : Set ℝ, IsCompact J → J.OrdConnected → J.Nontrivial →
          (∀ t ∈ J, IsInvertibleJet δ p (affinePath A B t)) →
          (∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t ∈ J,
            (⨆ κ ∈ imStrip (2 * δ),
              quotHomNorm (quotHomInverse ((affinePath A B t).f00 κ))) ≤ C) →
          (⨆ t ∈ J, jetNorm δ p (invJet p (affinePath A B t))) < ∞ ∧
          (∃ L : ℝ≥0, ∀ t ∈ J, ∀ t' ∈ J,
            jetNorm δ p
                (add (invJet p (affinePath A B t'))
                  (smul (-1) (invJet p (affinePath A B t)))) ≤
              L * ENNReal.ofReal |t' - t|) ∧
          (∀ C : JetQuad X X, IsJet δ p C →
            ContinuousOn (fun t => traceNumber (mul p C (invJet p (affinePath A B t)))) J) ∧
          ContinuousOn (fun t => traceNumber (mul p (invJet p (affinePath A B t)) B)) J ∧
          (∀ t ∈ J, HasDerivWithinAt (fun s => logNumber p (affinePath A B s))
            (traceNumber (mul p (invJet p (affinePath A B t)) B)) J t) ∧
          ∀ t₀ ∈ J, ∀ t₁ ∈ J,
            logNumber p (affinePath A B t₁) - logNumber p (affinePath A B t₀) =
              ∫ t in t₀..t₁, traceNumber (mul p (invJet p (affinePath A B t)) B)
end YangMills.Construction.PeriodicOperators.JetNormsAffine
end
