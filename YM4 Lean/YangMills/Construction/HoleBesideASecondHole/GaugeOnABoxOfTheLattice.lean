import YangMills.Construction.HoleBesideASecondHole.LinesAndStripsOfALatticeField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BoxGauge
open LatticeGauge
open BlockAverages (UnitQuaternion)
def exitHolonomy (X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (lo hi w a : Fin 4 → ℤ) : UnitQuaternion :=
  if w 0 < a 0 then lineHolonomy X a 0 (hi 0 + 1 - a 0).toNat
  else (lineHolonomy X (Function.update a 0 (lo 0 - 1)) 0 (a 0 - lo 0 + 1).toNat)⁻¹
open Classical in
def boxGaugeTransform (A B : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (lo hi w a : Fin 4 → ℤ) : UnitQuaternion :=
  if a ∈ box lo hi then exitHolonomy B lo hi w a * (exitHolonomy A lo hi w a)⁻¹ else 1
def firstAxisPlaquettes (kl kh : Fin 4 → ℤ) : Set ((Fin 4 → ℤ) × Fin 4) :=
  {q | q.2 ≠ 0 ∧ q.1 ∈ box kl kh ∧ q.1 + unitVec 0 ∈ box kl kh ∧
    q.1 + unitVec q.2 ∈ box kl kh ∧ q.1 + unitVec 0 + unitVec q.2 ∈ box kl kh}
def GaugeFixedNearBox : Prop :=
  ∀ (A B : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (lo hi w kl kh : Fin 4 → ℤ) (M : ℕ) (E : ℝ),
    (∀ i, lo i ≤ hi i ∧ hi i - lo i + 3 ≤ M) → 0 ≤ E →
    lo 0 - 1 ≤ w 0 → w 0 ≤ hi 0 → lo 1 - 1 ≤ w 1 → w 1 ≤ hi 1 →
    (hi 0 + 1 ≤ kh 0 ∨ kh 0 ≤ w 0) → (kl 0 ≤ lo 0 - 1 ∨ w 0 < kl 0) →
    (hi 1 + 1 ≤ kh 1 ∨ kh 1 ≤ w 1) → (kl 1 ≤ lo 1 - 1 ∨ w 1 < kl 1) →
    (∀ a i, a ∈ box kl kh → a + unitVec i ∈ box kl kh →
      a ∈ box (lo - 1) (hi + 1) → a + unitVec i ∈ box (lo - 1) (hi + 1) →
      a ∉ box lo hi → a + unitVec i ∉ box lo hi → A a i = B a i) →
    (∀ Q : Finset ((Fin 4 → ℤ) × Fin 4), (∀ q ∈ Q, q ∈ firstAxisPlaquettes kl kh) →
      ∑ q ∈ Q, LatticeGauge.plaquetteDefect A q.1 0 q.2 ^ 2 ≤ E ^ 2) →
    (∀ Q : Finset ((Fin 4 → ℤ) × Fin 4), (∀ q ∈ Q, q ∈ firstAxisPlaquettes kl kh) →
      ∑ q ∈ Q, LatticeGauge.plaquetteDefect B q.1 0 q.2 ^ 2 ≤ E ^ 2) →
    ∀ a i, a ∈ box kl kh → a + unitVec i ∈ box kl kh →
      a ∈ box (lo - 1) (hi + 1) → a + unitVec i ∈ box (lo - 1) (hi + 1) →
      quatDist (boxGaugeTransform A B lo hi w a * A a i *
          (boxGaugeTransform A B lo hi w (a + unitVec i))⁻¹) (B a i) ≤
        2 * M * E
end YangMills.Construction.BoxGauge
end
