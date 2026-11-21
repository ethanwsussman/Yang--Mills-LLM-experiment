import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStep
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction
namespace LimitForms
open WeightedResponses ResponseInTheExpansion TorusFields TorusLumps
abbrev IntBond : Type := (Fin 4 → ℤ) × Fin 4
def cubeEntry (a : ℝ) (L k N : ℕ) (b b' : IntBond) : ℝ :=
  haveI : NeZero (16 * (N + 1)) := ⟨by omega⟩
  mixedDeriv (actionAtLevel a L k (supBall (0 : TorusSite (16 * (N + 1))) N)) (trivialField (16 * (N + 1)))
    ![bondFrom 0 b, bondFrom 0 b'] ![quaternionI, quaternionI]
def bondImage (g : TorusIsometry) (b : IntBond) : IntBond × ℝ :=
  if g.axisSign (g.axisPerm.symm b.2) = 1 then
    ((fun i => g.axisSign i * b.1 (g.axisPerm i) + g.offset i, g.axisPerm.symm b.2), 1)
  else
    (((fun i => g.axisSign i * b.1 (g.axisPerm i) + g.offset i) - Pi.single (g.axisPerm.symm b.2) 1, g.axisPerm.symm b.2), -1)
def bondSupDist (b b' : IntBond) : ℕ := Finset.univ.sup fun i => (b.1 i - b'.1 i).natAbs
def intCurl (v : IntBond → ℝ) (p : (Fin 4 → ℤ) × Fin 4 × Fin 4) : ℝ :=
  v (p.1, p.2.1) + v (p.1 + Pi.single p.2.1 1, p.2.2) - v (p.1 + Pi.single p.2.2 1, p.2.1) - v (p.1, p.2.2)
structure IsLimitForm (a cK c C : ℝ) (L k : ℕ) (Q : IntBond → IntBond → ℝ) : Prop where
  tendsto : ∀ b b', Filter.Tendsto (fun N => cubeEntry a L k N b b') Filter.atTop (nhds (Q b b'))
  invariant : ∀ (g : TorusIsometry) (b b' : IntBond),
    (bondImage g b).2 * (bondImage g b').2 * Q (bondImage g b).1 (bondImage g b').1 = Q b b'
  decay : ∀ b b', |Q b b'| ≤ C * Real.exp (-(c * bondSupDist b b'))
  kills_gradients : ∀ (b : IntBond) (φ : (Fin 4 → ℤ) →₀ ℝ),
    HasSum (fun b' : IntBond => Q b b' * (φ b'.1 - φ (b'.1 + Pi.single b'.2 1))) 0
  coercive : ∀ (v : IntBond →₀ ℝ) (P : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4)), (∀ p ∈ P, p.2.1 < p.2.2) →
    2 * cK * ∑ p ∈ P, intCurl v p ^ 2 ≤ ∑ b ∈ v.support, ∑ b' ∈ v.support, v b * Q b b' * v b'
def gaugeFixedKernel (Q : IntBond → IntBond → ℝ) (b b' : IntBond) : ℝ :=
  Q b b' + ((if b.1 = b'.1 then 1 else 0) - (if b.1 = b'.1 + Pi.single b'.2 1 then 1 else 0) -
    (if b.1 + Pi.single b.2 1 = b'.1 then 1 else 0) +
    (if b.1 + Pi.single b.2 1 = b'.1 + Pi.single b'.2 1 then 1 else 0))
def midpointSymbol (Q : IntBond → IntBond → ℝ) (i j : Fin 4) (p : Fin 4 → ℝ) : ℂ :=
  ∑' z : Fin 4 → ℤ, (gaugeFixedKernel Q (0, i) (z, j) : ℂ) *
    Complex.exp (Complex.I * ((∑ l, p l * ((z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0)) : ℝ) : ℂ))
def momentumNormSq (p : Fin 4 → ℝ) : ℝ := ∑ l, p l ^ 2
def brillouinBox : Set (Fin 4 → ℝ) := Set.Icc (fun _ => -Real.pi) (fun _ => Real.pi)
def intNormSq (z : Fin 4 → ℤ) : ℝ := ∑ l, (z l : ℝ) ^ 2
def reflectionEntry (z : Fin 4 → ℤ) (m r : Fin 4) : ℝ :=
  (if m = r then 1 else 0) - 2 * (z m : ℝ) * (z r : ℝ) / intNormSq z
def maxwellKernel (z : Fin 4 → ℤ) (m n' r s : Fin 4) : ℝ :=
  (reflectionEntry z m r * reflectionEntry z n' s - reflectionEntry z m s * reflectionEntry z n' r) /
    (Real.pi ^ 2 * intNormSq z ^ 2)
end LimitForms
end YangMills.Construction
end
