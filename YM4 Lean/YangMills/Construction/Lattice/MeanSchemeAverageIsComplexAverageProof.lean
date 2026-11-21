import YangMills.Construction.Lattice.MeanSchemeAverageIsComplexAverage
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CentredAverage
private theorem coe_toSublattice {L m : ℕ} {j j' : ℤ} (h : sublattice L m j ≤ sublattice L m j')
    (y : Site L m j) : ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : Site L m j' => (x : FourTorus L m) = y) ⟨⟨y, h y.2⟩, rfl⟩
theorem centredAverage_eq_complexBlockAverage (hCoords : CoordinateDescription) :
    CentredAverageEqComplexBlockAverage := by
  intro L m K n hodd hL hm hn c _
  obtain ⟨-, hunits, -, -⟩ := hCoords L m hodd hL hm
  obtain ⟨-, -, -, hle, hshift⟩ := hunits K n (by omega) hn.le
  have hincl := hle (n + 1) (Nat.le_succ n) hn
  refine ⟨?_, ?_, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro μ hμ x
    have hends := congrArg (fun z : SiteAtLevel L m K n => (z : FourTorus L m)) (hshift hn c μ hμ)
    simp only [AddSubgroup.coe_add, coe_toSublattice hincl] at hends
    have hdiff : (c.target - c.source).toSublattice (levelDepth K n) =
        (L : ℤ) • unitStep L m (levelDepth K n) μ := by
      apply Subtype.ext
      rw [coe_toSublattice hincl, AddSubgroup.coe_sub, hends]
      abel
    simp only [shiftAcross, hdiff]
  · intro W
    constructor
    · rintro ⟨hfield, ⟨hsource, htarget⟩, hnorm⟩
      exact ⟨⟨hfield, fun x hx => (hsource x hx).2.2, fun x hx => (htarget x hx).2.2⟩, hnorm⟩
    · rintro ⟨⟨hfield, hsource, htarget⟩, hnorm⟩
      have hpart : ∀ y : SiteAtLevel L m K (n + 1), unitBlock y ⊆ bondDoubleBlock c →
          IsGaugeField complexGaugeGroup (bondsInside (unitBlock y)) W := fun y hy =>
        ⟨fun b hb => hfield.1 b ⟨hy hb.1, hy hb.2⟩, fun b hb => hfield.2 b ⟨hy hb.1, hy hb.2⟩⟩
      exact ⟨hfield, ⟨fun x hx => ⟨hx, hpart _ subset_union_left, hsource x hx⟩,
        fun x hx => ⟨hx, hpart _ subset_union_right, htarget x hx⟩⟩, hnorm⟩
end YangMills.Construction.PeriodicLattice.CentredAverage
