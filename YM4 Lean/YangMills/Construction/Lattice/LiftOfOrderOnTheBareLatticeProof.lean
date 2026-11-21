import YangMills.Construction.Lattice.BondsInsideAndOverInTermsOfBlocks
import YangMills.Construction.Lattice.LiftOfOrderOnTheBareLattice
import YangMills.Construction.Lattice.TwoCasesOfTheLiftOfOrder
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
theorem bareOrderLiftEqBareLift_holds
    (hCasesAll : OrderLiftCases)
    (hPosition : BondPositionByBlocks) :
    BareOrderLiftEqBareLift := by
  intro L m K hL hm hK k hk1 hkK C V hrev hV
  obtain ⟨-, hUnique, hNone, hCases⟩ := (hCasesAll L m K hL hm hK).1 0 k (Nat.zero_le k) hkK
  have hInside : ∀ b : BondAtLevel L m K 0, EndsInOneBlock k b → liftToFinerLevel 0 V b = 1 :=
    fun b hb => if_pos hb
  have hValue : ∀ b : BondAtLevel L m K 0, ∀ c ∈ C, CoversBond c b →
      liftToFinerLevel 0 V b = V c := by
    intro b c hc hbc
    have hb : b ∈ bondsInsideOrOverCoarse 0 C := Or.inr ⟨c, hc, hbc⟩
    exact (hCases C V hrev hV b hb).2.2.2.2.1 c hc hbc
  refine ⟨fun b => Iff.rfl, fun b hb => ⟨hInside b hb, hInside b hb⟩,
    fun b c hc hbc => ⟨hValue b c hc hbc, hValue b c hc hbc⟩, rfl, ?_, fun b _ => rfl⟩
  ext b
  constructor
  · rintro (hb | ⟨c₀, hc₀, hbc₀⟩) c hbc
    · exact absurd hbc (hNone b hb c)
    · rw [hUnique b c c₀ hbc hbc₀]
      exact hc₀
  · intro hb
    rcases (hPosition L m K hL hm hK 0 k (Nat.zero_le k) hkK b).2.2 with ⟨y, hy⟩ | ⟨c, hbc⟩
    · exact Or.inl ⟨y, hy⟩
    · exact Or.inr ⟨c, hb c hbc, hbc⟩
end YangMills.Construction.PeriodicLattice
