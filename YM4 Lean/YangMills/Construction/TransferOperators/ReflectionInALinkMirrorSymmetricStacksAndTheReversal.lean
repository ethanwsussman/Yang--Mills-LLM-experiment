import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import YangMills.Construction.TransferOperators.GaugeAverageAndExchangeOfLayers
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice SpinHarmonics
namespace TransferOperators
def linkMirrorReflection (μ : Fin 4) (i : ℤ) : AmbientSpace → AmbientSpace :=
  NormalFamilies.reflectAcross (PeriodicLattice.coordVec μ) ((i : ℝ) + 1 / 2)
def reflectedLevel (i j : ℤ) : ℤ := 2 * i + 1 - j
theorem reflectedLevel_reflectedLevel (i j : ℤ) : reflectedLevel i (reflectedLevel i j) = j := by
  simp only [reflectedLevel]
  ring
theorem linkMirrorReflection_apply (μ : Fin 4) (i : ℤ) (x : AmbientSpace) :
    linkMirrorReflection μ i x =
      x - (2 * (x μ - i - 1 / 2)) • PeriodicLattice.coordVec μ := by
  have hdot : dotProduct (PeriodicLattice.coordVec μ) x = x μ := by
    simp [PeriodicLattice.coordVec]
  have hnorm : NormalFamilies.normSq (PeriodicLattice.coordVec μ) = 1 := by
    rw [NormalFamilies.normSq_eq_dotProduct]
    simp [PeriodicLattice.coordVec]
  simp only [linkMirrorReflection, NormalFamilies.reflectAcross, NormalFamilies.dualVector, hdot,
    hnorm, inv_one, one_smul]
  congr 2
  ring
theorem linkMirrorReflection_pointAtLevel (μ : Fin 4) (i j : ℤ) (y : SliceSite μ) :
    linkMirrorReflection μ i (pointAtLevel μ j y : LatticePoint 1) =
      (pointAtLevel μ (reflectedLevel i j) y : LatticePoint 1) := by
  have hcoe : ∀ l : ℤ, ((pointAtLevel μ l y : LatticePoint 1) : AmbientSpace) =
      (l : ℝ) • PeriodicLattice.coordVec μ + ((y : LatticePoint 1) : AmbientSpace) := by
    intro l
    have hl : ((pointAtLevel μ l y : LatticePoint 1) : AmbientSpace) =
        l • (Pi.single μ (1 : ℝ) : AmbientSpace) + ((y : LatticePoint 1) : AmbientSpace) := rfl
    rw [hl, ← Int.cast_smul_eq_zsmul ℝ]
    rfl
  have hy : ((y : LatticePoint 1) : AmbientSpace) μ = 0 := y.2
  rw [linkMirrorReflection_apply, hcoe, hcoe]
  ext ν
  by_cases hν : ν = μ
  · subst hν
    simp [PeriodicLattice.coordVec, reflectedLevel, hy]
    ring
  · simp [PeriodicLattice.coordVec, Pi.single_eq_of_ne hν]
def centeredStack (i k : ℤ) (hk : 1 ≤ k) : Stack where
  lower := i - k + 1
  upper := i + k
  lower_lt_upper := by omega
variable {μ : Fin 4}
def centeredLinkPairs (i k : ℤ) (v : Set (SliceSite μ)) : Set (ℤ × SliceLink μ) :=
  {p | i - k + 1 ≤ p.1 ∧ p.1 ≤ i + k ∧ p.2 ∈ linksWithin v}
theorem snd_mem_linksWithin (i k : ℤ) (v : Set (SliceSite μ)) :
    ∀ p ∈ centeredLinkPairs i k v, p.2 ∈ linksWithin v :=
  fun _ hp => hp.2.2
theorem SliceLink.ext_of_endpoints {b c : SliceLink μ} (hs : b.source = c.source)
    (ht : b.target = c.target) : b = c := by
  obtain ⟨⟨s, t, _⟩, _⟩ := b
  obtain ⟨⟨s', t', _⟩, _⟩ := c
  have hs' : s = s' := congrArg Subtype.val hs
  have ht' : t = t' := congrArg Subtype.val ht
  subst hs' ht'
  rfl
theorem linksWithin_finite (v : Set (SliceSite μ)) [Finite v] :
    (linksWithin v).Finite := by
  have hv : v.Finite := Set.toFinite v
  refine Set.Finite.of_injOn (f := fun b : SliceLink μ => (b.source, b.target))
    (t := v ×ˢ v) (fun b hb => ⟨hb.1, hb.2⟩) ?_ (hv.prod hv)
  intro b _ c _ h
  exact SliceLink.ext_of_endpoints (congrArg Prod.fst h) (congrArg Prod.snd h)
instance finite_centeredLinkPairs (i k : ℤ) (v : Set (SliceSite μ)) [Finite v] :
    Finite (centeredLinkPairs i k v) := by
  refine Set.Finite.to_subtype
    (((Set.finite_Icc (i - k + 1) (i + k)).prod (linksWithin_finite v)).subset ?_)
  intro p hp
  exact ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩
variable (μ) in
def centeredStackClass (i k : ℤ) (hk : 1 ≤ k) : Set (GaugeField 1 → ℂ) :=
  {X | ∃ (v : Set (SliceSite μ)) (_ : Finite v)
      (Ψ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → ℂ),
    (linksWithin v).Nonempty ∧ IsRealEntryPolynomial Ψ ∧
      IsDiagonalGaugeInvariant (snd_mem_linksWithin i k v) Ψ ∧
      ∀ U : GaugeField 1, X U = Ψ fun p =>
        (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2}
def reflectPair (i k : ℤ) (v : Set (SliceSite μ)) (p : centeredLinkPairs i k v) :
    centeredLinkPairs i k v :=
  ⟨(reflectedLevel i p.1.1, p.1.2), by
    have hlo := p.2.1
    have hhi := p.2.2.1
    refine ⟨?_, ?_, p.2.2.2⟩ <;> simp only [reflectedLevel] <;> omega⟩
def reflectPairPerm (i k : ℤ) (v : Set (SliceSite μ)) : Equiv.Perm (centeredLinkPairs i k v) where
  toFun := reflectPair i k v
  invFun := reflectPair i k v
  left_inv p := Subtype.ext (Prod.ext (reflectedLevel_reflectedLevel i p.1.1) rfl)
  right_inv p := Subtype.ext (Prod.ext (reflectedLevel_reflectedLevel i p.1.1) rfl)
theorem isLevelExchange_reflectPairPerm (i k : ℤ) (v : Set (SliceSite μ)) :
    IsLevelExchange (reflectPairPerm i k v) :=
  ⟨reflectedLevel i, fun _ => rfl⟩
def levelReversal {A : Type*} (i k : ℤ) (v : Set (SliceSite μ))
    (Φ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → A)
    (u : centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) : A :=
  Φ fun p => u (reflectPair i k v p)
theorem levelReversal_eq_permuteArgs {A : Type*} (i k : ℤ) (v : Set (SliceSite μ))
    (Φ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → A) :
    levelReversal i k v Φ = permuteArgs (reflectPairPerm i k v) Φ :=
  rfl
end TransferOperators
end YangMills.Construction
end
