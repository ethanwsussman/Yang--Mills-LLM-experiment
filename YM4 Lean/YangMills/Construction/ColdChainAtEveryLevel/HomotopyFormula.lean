import YangMills.Construction.ColdChainAtEveryLevel.FractionalIntegrationOnTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeFractionalIntegration
def basisVector (i : Fin 4) : Lattice4 := Pi.single i 1
section Forms
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def lineSum (w : Lattice4 → Fin 4 → E) (y : Lattice4) (i : Fin 4) (n : ℤ) : E :=
  ∑ r ∈ Finset.Ico (0 : ℤ) n, w (y + r • basisVector i) i - ∑ r ∈ Finset.Ico n (0 : ℤ), w (y + r • basisVector i) i
def staircasePoint (u v : Lattice4) (s : ℕ) : Lattice4 := fun i => if (i : ℕ) < s then v i else u i
def staircaseSum (w : Lattice4 → Fin 4 → E) (u v : Lattice4) : E :=
  ∑ s : Fin 4, lineSum w (staircasePoint u v s) s (v s - u s)
def plaquetteCurl (w : Lattice4 → Fin 4 → E) (y : Lattice4) (μ ν : Fin 4) : E :=
  w y μ + w (y + basisVector μ) ν - w (y + basisVector ν) μ - w y ν
end Forms
abbrev StaircaseSample : Type := Fin 4 → ℤ × ℤ
def dyadicDepth (l : ℕ) : ℕ := Nat.clog 2 (81 * l)
def sampleBox (l : ℕ) (c : Lattice4) : Finset StaircaseSample :=
  Fintype.piFinset fun i => Finset.Ico (c i) (c i + l) ×ˢ Finset.Ico (0 : ℤ) (2 ^ dyadicDepth l)
def dyadicPathPoint (K : ℕ) (x : Lattice4) (ω : StaircaseSample) : ℕ → Lattice4
  | 0 => x
  | m + 1 => fun i => x i + (2 ^ m * ((ω i).1 - x i) + (ω i).2) / 2 ^ K
section Means
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def dyadicPathSum (K : ℕ) (w : Lattice4 → Fin 4 → E) (x : Lattice4) (ω : StaircaseSample) : E :=
  ∑ m ∈ Finset.range (K + 1), staircaseSum w (dyadicPathPoint K x ω m) (dyadicPathPoint K x ω (m + 1))
def randomPathMean (l : ℕ) (c : Lattice4) (w : Lattice4 → Fin 4 → E) (x : Lattice4) : E :=
  (1 / ((sampleBox l c).card : ℝ)) • ∑ ω ∈ sampleBox l c, dyadicPathSum (dyadicDepth l) w x ω
def endpointMean (l : ℕ) (c : Lattice4) (φ : Lattice4 → E) : E :=
  (1 / ((sampleBox l c).card : ℝ)) • ∑ ω ∈ sampleBox l c, φ fun i => (ω i).1
def latticeDifference (φ : Lattice4 → E) : Lattice4 → Fin 4 → E := fun y i => φ (y + basisVector i) - φ y
end Means
def cornerCube (l : ℕ) (c : Lattice4) : Finset Lattice4 := Fintype.piFinset fun i => Finset.Ico (c i) (c i + l)
def IsFilledToward (l : ℕ) (c : Lattice4) (P : Finset Lattice4) : Prop :=
  (∀ q ∈ cornerCube l c, q ∈ P) ∧ (∀ x ∈ P, ∀ i, |x i - c i| ≤ 40 * (l : ℤ)) ∧
    ∀ x ∈ P, ∀ q ∈ cornerCube l c, ∀ y : Lattice4,
      (∀ i, min (x i) (q i) ≤ y i ∧ y i ≤ max (x i) (q i)) → y ∈ P
def bondsOf (P : Finset Lattice4) : Finset (Lattice4 × Fin 4) :=
  (P ×ˢ Finset.univ).filter fun b => b.1 + basisVector b.2 ∈ P
def orientedPlaquettesOf (P : Finset Lattice4) : Finset (Lattice4 × Fin 4 × Fin 4) :=
  (P ×ˢ Finset.univ ×ˢ Finset.univ).filter fun p =>
    p.2.1 ≠ p.2.2 ∧ p.1 + basisVector p.2.1 ∈ P ∧ p.1 + basisVector p.2.2 ∈ P ∧
      p.1 + basisVector p.2.1 + basisVector p.2.2 ∈ P
def randomStaircaseHomotopyStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (c : Lattice4) (P : Finset Lattice4), 1 ≤ l → IsFilledToward l c P →
    ∃ (H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ) (G : Lattice4 → Lattice4 × Fin 4 → ℝ),
      (∀ b p, |H b p| ≤ C * cubicKernel (b.1 - p.1)) ∧ (∀ x b, |G x b| ≤ C * cubicKernel (x - b.1)) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E],
        (∀ (w : Lattice4 → Fin 4 → E), ∀ x ∈ P, randomPathMean l c w x = ∑ b ∈ bondsOf P, G x b • w b.1 b.2) ∧
        (∀ (w : Lattice4 → Fin 4 → E) (x : Lattice4) (i : Fin 4), x ∈ P → x + basisVector i ∈ P →
          w x i + (randomPathMean l c w (x + basisVector i) - randomPathMean l c w x) =
            ∑ p ∈ orientedPlaquettesOf P, H (x, i) p • plaquetteCurl w p.1 p.2.1 p.2.2) ∧
        ∀ (φ : Lattice4 → E), ∀ x ∈ P, φ x - endpointMean l c φ = - randomPathMean l c (latticeDifference φ) x
end LatticeFractionalIntegration
end YangMills.Construction
end
