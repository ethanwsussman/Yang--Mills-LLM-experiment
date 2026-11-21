import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def meshSize (L : ℕ) (j : ℤ) : ℝ := (L : ℝ) ^ (-j)
def torusSide (L m : ℕ) : ℝ := 2 * (L : ℝ) ^ m
def torusSides (L : ℕ) : Set ℝ := {ℓ | ∃ m : ℕ, 0 < m ∧ ℓ = torusSide L m}
abbrev FourTorus (L m : ℕ) : Type := Fin 4 → AddCircle (torusSide L m)
def pointOnAxis (L m : ℕ) (μ : Fin 4) (t : ℝ) : FourTorus L m :=
  Pi.single μ (t : AddCircle (torusSide L m))
def sublattice (L m : ℕ) (j : ℤ) : AddSubgroup (FourTorus L m) where
  carrier := {x | ∃ n : Fin 4 → ℤ, ∀ μ, x μ = (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))}
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨n', hn'⟩
    refine ⟨n + n', fun μ => ?_⟩
    simp only [Pi.add_apply, hn, hn', Int.cast_add, add_mul, AddCircle.coe_add]
  zero_mem' := ⟨0, fun μ => by simp⟩
  neg_mem' := by
    rintro x ⟨n, hn⟩
    refine ⟨-n, fun μ => ?_⟩
    simp only [Pi.neg_apply, hn, Int.cast_neg, neg_mul, AddCircle.coe_neg]
abbrev Site (L m : ℕ) (j : ℤ) : Type := ↥(sublattice L m j)
theorem sublattice_mono {L : ℕ} (hL : 0 < L) (m : ℕ) {j j' : ℤ} (hjj' : j ≤ j') :
    sublattice L m j ≤ sublattice L m j' := by
  rintro x ⟨n, hn⟩
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hjj')
  obtain rfl : j' = j + d := by omega
  refine ⟨fun μ => n μ * (L : ℤ) ^ d, fun μ => ?_⟩
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [hn μ]
  congr 1
  simp only [meshSize, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [neg_add, zpow_add₀ hL', zpow_neg _ (d : ℤ), zpow_natCast]
  field_simp
def unitStep (L m : ℕ) (j : ℤ) (μ : Fin 4) : Site L m j :=
  ⟨pointOnAxis L m μ (meshSize L j), ⟨Pi.single μ 1, fun ν => by
    by_cases hνμ : ν = μ
    · subst hνμ; simp [pointOnAxis]
    · simp [pointOnAxis, Pi.single_eq_of_ne hνμ]⟩⟩
@[ext]
structure Bond (L m : ℕ) (j : ℤ) where
  source : Site L m j
  target : Site L m j
  isNeighbour : ∃ μ : Fin 4, target - source = unitStep L m j μ ∨ target - source = -unitStep L m j μ
variable {L m : ℕ} {j : ℤ}
namespace Bond
def IsPositivelyOriented (b : Bond L m j) : Prop := ∃ μ : Fin 4, b.target - b.source = unitStep L m j μ
def opposite (b : Bond L m j) : Bond L m j where
  source := b.target
  target := b.source
  isNeighbour := by
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · exact ⟨μ, Or.inr (by rw [← h]; abel)⟩
    · exact ⟨μ, Or.inl (by rw [← neg_eq_iff_eq_neg.mpr h]; abel)⟩
def forwardFrom (x : Site L m j) (μ : Fin 4) : Bond L m j :=
  ⟨x, x + unitStep L m j μ, μ, Or.inl (by abel)⟩
def backwardFrom (x : Site L m j) (μ : Fin 4) : Bond L m j :=
  ⟨x, x - unitStep L m j μ, μ, Or.inr (by abel)⟩
def axis (b : Bond L m j) : Fin 4 := b.isNeighbour.choose
def orientedLength (b : Bond L m j) : ℝ :=
  open Classical in
  if b.target - b.source = unitStep L m j b.axis then meshSize L j else -meshSize L j
def edgeSet (b : Bond L m j) : Set (FourTorus L m) :=
  {p | ∃ t ∈ Icc (0 : ℝ) 1, p = b.source + pointOnAxis L m b.axis (t * b.orientedLength)}
def centre (b : Bond L m j) : FourTorus L m :=
  b.source + pointOnAxis L m b.axis (b.orientedLength / 2)
end Bond
@[ext]
structure Plaquette (L m : ℕ) (j : ℤ) where
  origin : Site L m j
  firstAxis : Fin 4
  secondAxis : Fin 4
  firstAxis_lt_secondAxis : firstAxis < secondAxis
namespace Plaquette
def vertices (p : Plaquette L m j) : Set (Site L m j) :=
  {p.origin, p.origin + unitStep L m j p.firstAxis,
    p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis,
    p.origin + unitStep L m j p.secondAxis}
def barycenter (p : Plaquette L m j) : FourTorus L m :=
  p.origin + pointOnAxis L m p.firstAxis (meshSize L j / 2) + pointOnAxis L m p.secondAxis (meshSize L j / 2)
def face (p : Plaquette L m j) : Set (FourTorus L m) :=
  {q | ∃ s ∈ Icc (0 : ℝ) (meshSize L j), ∃ t ∈ Icc (0 : ℝ) (meshSize L j),
    q = p.origin + pointOnAxis L m p.firstAxis s + pointOnAxis L m p.secondAxis t}
def boundaryBonds (p : Plaquette L m j) : List (Bond L m j) :=
  [Bond.forwardFrom p.origin p.firstAxis,
    Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis,
    (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis).opposite,
    (Bond.forwardFrom p.origin p.secondAxis).opposite]
end Plaquette

namespace ConjugationReality
instance finite_plaquette (L m : ℕ) (j : ℤ) [Finite (Site L m j)] : Finite (Plaquette L m j) :=
  Finite.of_injective (fun p : Plaquette L m j => (p.origin, p.firstAxis, p.secondAxis)) fun _ _ h =>
    Plaquette.ext (congrArg Prod.fst h) (congrArg (fun y => y.2.1) h) (congrArg (fun y => y.2.2) h)
end ConjugationReality

def IsBondPath (Γ : List (Bond L m j)) : Prop := Γ.IsChain fun b b' => b.target = b'.source
def IsBondPathFromTo (Γ : List (Bond L m j)) (x x' : Site L m j) : Prop :=
  IsBondPath Γ ∧ (Γ = [] → x = x') ∧ (∀ b ∈ Γ.head?, b.source = x) ∧ (∀ b ∈ Γ.getLast?, b.target = x')
def reversePath (Γ : List (Bond L m j)) : List (Bond L m j) := (Γ.map Bond.opposite).reverse
def forwardAxisPath (x : Site L m j) (μ : Fin 4) : ℕ → List (Bond L m j)
  | 0 => []
  | n + 1 => Bond.forwardFrom x μ :: forwardAxisPath (x + unitStep L m j μ) μ n
def backwardAxisPath (x : Site L m j) (μ : Fin 4) : ℕ → List (Bond L m j)
  | 0 => []
  | n + 1 => Bond.backwardFrom x μ :: backwardAxisPath (x - unitStep L m j μ) μ n
def flowAlong (x : Site L m j) (μ : Fin 4) (n : ℤ) : List (Bond L m j) :=
  if 0 ≤ n then forwardAxisPath x μ n.toNat else backwardAxisPath x μ (-n).toNat
def IsAxialDisplacement (x x' : Site L m j) (μ : Fin 4) (n : ℤ) : Prop :=
  x' - x = n • unitStep L m j μ ∧ ((|n| : ℤ) : ℝ) < (L : ℝ) ^ ((m : ℤ) + j)
def axialPath (x x' : Site L m j) : List (Bond L m j) :=
  open Classical in
  if h : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x x' q.1 q.2 then
    flowAlong x h.choose.1 h.choose.2
  else []
abbrev levelDepth (K k : ℕ) : ℤ := (K : ℤ) - (k : ℤ)
abbrev SiteAtLevel (L m K k : ℕ) : Type := Site L m (levelDepth K k)
abbrev BondAtLevel (L m K k : ℕ) : Type := Bond L m (levelDepth K k)
abbrev PlaquetteAtLevel (L m K k : ℕ) : Type := Plaquette L m (levelDepth K k)
def toLevelUnits (L K k : ℕ) (r : ℝ) : ℝ := (L : ℝ) ^ levelDepth K k * r
def finestMeshInLevelUnits (L k : ℕ) : ℝ := (L : ℝ) ^ (-(k : ℤ))
def sitesIn (X : Set (FourTorus L m)) : Set (Site L m j) := {x | (x : FourTorus L m) ∈ X}
def bondsMeeting (X : Set (FourTorus L m)) : Set (Bond L m j) :=
  {b | (b.source : FourTorus L m) ∈ X ∨ (b.target : FourTorus L m) ∈ X}
def bondsInside (X : Set (FourTorus L m)) : Set (Bond L m j) :=
  {b | (b.source : FourTorus L m) ∈ X ∧ (b.target : FourTorus L m) ∈ X}
def plaquettesMeeting (X : Set (FourTorus L m)) : Set (Plaquette L m j) :=
  {p | ∃ c ∈ p.vertices, (c : FourTorus L m) ∈ X}
def plaquettesInside (X : Set (FourTorus L m)) : Set (Plaquette L m j) :=
  {p | ∀ c ∈ p.vertices, (c : FourTorus L m) ∈ X}
end PeriodicLattice
end YangMills.Construction
