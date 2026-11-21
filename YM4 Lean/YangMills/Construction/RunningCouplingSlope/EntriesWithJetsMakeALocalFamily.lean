import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
structure HasSecondOrderJet (g : ℝ → ℝ → ℂ) (v a b c : ℂ) : Prop where
  contDiff : ContDiff ℝ 2 (fun w : ℝ × ℝ => g w.1 w.2)
  apply_zero : g 0 0 = v
  deriv_fst : deriv (fun s => g s 0) 0 = a
  deriv_snd : deriv (fun t => g 0 t) 0 = b
  deriv_mixed : deriv (fun s => deriv (fun t => g s t) 0) 0 = c
structure SecondOrderJetClosure : Prop where
  const : ∀ w : ℂ, HasSecondOrderJet (fun _ _ => w) w 0 0 0
  add : ∀ {g h : ℝ → ℝ → ℂ} {v a b c v' a' b' c' : ℂ}, HasSecondOrderJet g v a b c →
    HasSecondOrderJet h v' a' b' c' →
    HasSecondOrderJet (fun s t => g s t + h s t) (v + v') (a + a') (b + b') (c + c')
  mul : ∀ {g h : ℝ → ℝ → ℂ} {v a b c v' a' b' c' : ℂ}, HasSecondOrderJet g v a b c →
    HasSecondOrderJet h v' a' b' c' →
    HasSecondOrderJet (fun s t => g s t * h s t) (v * v') (a * v' + v * a') (b * v' + v * b')
      (c * v' + a * b' + b * a' + v * c')
  sum : ∀ {κ : Type} (S : Finset κ) {g : κ → ℝ → ℝ → ℂ} {v a b c : κ → ℂ},
    (∀ i ∈ S, HasSecondOrderJet (g i) (v i) (a i) (b i) (c i)) →
    HasSecondOrderJet (fun s t => ∑ i ∈ S, g i s t) (∑ i ∈ S, v i) (∑ i ∈ S, a i) (∑ i ∈ S, b i)
      (∑ i ∈ S, c i)
  comp_linear : ∀ {G : ℝ → ℂ} (α β : ℝ), ContDiff ℝ 2 G →
    HasSecondOrderJet (fun s t => G (s * α + t * β)) (G 0) (α * deriv G 0) (β * deriv G 0)
      (α * β * deriv (deriv G) 0)
structure IsBoundedSparsityOnCells {L n k : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι']
    (c : ι → PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k))
    (c' : ι' → PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k))
    (S : ι' → ι → Prop) (R C : ℕ) (r : ℝ) : Prop where
  row_card_le : ∀ p, Nat.card {q // S p q} ≤ R
  col_card_le : ∀ q, Nat.card {p // S p q} ≤ C
  cellDist_le : ∀ p q, S p q → cellDist (c' p) (c q) ≤ r
def LocalFamilyOfJetEntries : Prop :=
  SecondOrderJetClosure ∧
  ∀ {L n k : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    (c : ι → PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k))
    (c' : ι' → PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k))
    (T : ℝ → ℝ → Matrix ι' ι ℂ) (z : Fin 4 → ℤ) (θ K r : ℝ) (R C : ℕ)
    (S : ι' → ι → Prop) (v a b d : ι' → ι → ℂ),
    0 ≤ θ → 0 ≤ K → IsBoundedSparsityOnCells c c' S R C r →
    (∀ p q, HasSecondOrderJet (fun s t => T s t p q) (v p q) (a p q) (b p q) (d p q)) →
    (∀ p q, ¬ S p q → v p q = 0 ∧ a p q = 0 ∧ b p q = 0 ∧ d p q = 0) →
    (∀ p q, ‖v p q‖ ≤ K) →
    (∀ p q, ‖a p q‖ ≤ K * cellDecayWeight θ (cellOfCoords L n k 0) (c' p)) →
    (∀ p q, ‖b p q‖ ≤ K * cellDecayWeight θ (cellOfCoords L n k z) (c' p)) →
    (∀ p q, ‖d p q‖ ≤
      K * (cellDecayWeight θ (cellOfCoords L n k 0) (c' p) *
        cellDecayWeight θ (cellOfCoords L n k z) (c' p))) →
    IsLocalAlongBackground c c' T z (Real.sqrt ((R : ℝ) * C) * K * Real.exp (θ * r)) θ
end YangMills.Construction.RunningCouplingSlope
end
