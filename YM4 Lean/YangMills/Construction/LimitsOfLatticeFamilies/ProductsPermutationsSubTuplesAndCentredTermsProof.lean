import YangMills.Construction.LimitTheorem.RepresentativeAndTheIdentificationsProof
import YangMills.Construction.LimitsOfLatticeFamilies.MembersOfHierarchiesOnSeparatedTuplesProof
import YangMills.Construction.LimitsOfLatticeFamilies.ProductsPermutationsSubTuplesAndCentredTerms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
namespace TupleClassesClosed
variable {s : Conventions.StandingParameters} {Y : ModelSpace}
theorem pi_mem_sepTuplesIn {n : ℕ} {ρ : ℝ≥0∞} {A : Fin n → Set (Y.Carrier s)}
    (hA : ∀ i, A i ⊆ ballAtBase s Y ρ) (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    {f : FunTuple s Y n} (hf : ∀ i, f i ∈ c1CompactSupp s Y (A i)) : f ∈ sepTuplesIn s Y n ρ := by apply _root_.YangMills.Construction.LatticeLimits.SepTupleMembers.mem_sepTuplesIn_of_pi <;> assumption
theorem pi_mem_lipSepTuplesIn {n : ℕ} {ρ : ℝ≥0∞} {A : Fin n → Set (Y.Carrier s)}
    (hA : ∀ i, A i ⊆ ballAtBase s Y ρ) (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    {f : FunTuple s Y n} (hf : ∀ i, f i ∈ lipCompactSupp s Y (A i)) :
    f ∈ lipSepTuplesIn s Y n ρ :=
  ⟨fun i => (hf i).1, fun i => (hf i).2.1,
    fun i j hij => (hdisj i j hij).mono (hf i).2.2 (hf j).2.2,
    fun i => (hf i).2.2.trans (hA i)⟩
theorem comp_perm_mem_sepTuplesIn {n : ℕ} {ρ : ℝ≥0∞} {f : FunTuple s Y n}
    (hf : f ∈ sepTuplesIn s Y n ρ) (σ : Equiv.Perm (Fin n)) :
    (fun i => f (σ i)) ∈ sepTuplesIn s Y n ρ :=
  ⟨⟨fun _ => hf.1.1 _, fun _ => hf.1.2.1 _, fun _ _ hij => hf.1.2.2 _ _ fun e => hij (σ.injective e)⟩,
    fun _ => hf.2 _⟩
theorem comp_perm_mem_lipSepTuplesIn {n : ℕ} {ρ : ℝ≥0∞} {f : FunTuple s Y n}
    (hf : f ∈ lipSepTuplesIn s Y n ρ) (σ : Equiv.Perm (Fin n)) :
    (fun i => f (σ i)) ∈ lipSepTuplesIn s Y n ρ :=
  ⟨fun _ => hf.1 _, fun _ => hf.2.1 _, fun _ _ hij => hf.2.2.1 _ _ fun e => hij (σ.injective e),
    fun _ => hf.2.2.2 _⟩
theorem restrictTuple_mem_lipSepTuplesIn {n : ℕ} {ρ : ℝ≥0∞} {f : FunTuple s Y n}
    (hf : f ∈ lipSepTuplesIn s Y n ρ) (S : Finset (Fin n)) :
    restrictTuple f S ∈ lipSepTuplesIn s Y S.card ρ :=
  ⟨fun _ => hf.1 _, fun _ => hf.2.1 _,
    fun _ _ hij => hf.2.2.1 _ _ fun e => hij ((S.orderEmbOfFin rfl).injective e),
    fun _ => hf.2.2.2 _⟩
theorem nonSingletonPartitions_one : SetPartition.nonSingletonPartitions 1 = ∅ := by apply _root_.YangMills.SharedProofs.p2697 <;> assumption
theorem centredSum_zero {ρ : ℝ≥0∞} (Φ : FunctionalSeq s Y ρ)
    (f : sepTuplesIn s Y 0 ρ) : centredSum Φ 0 f = 1 := by
  obtain ⟨P, hP, hPe⟩ := ModelSpace.nonSingletonPartitions_zero
  simp only [centredSum, hP, Finset.sum_singleton, hPe, Finset.prod_empty]
theorem centredSum_one {ρ : ℝ≥0∞} (Φ : FunctionalSeq s Y ρ)
    (f : sepTuplesIn s Y 1 ρ) : centredSum Φ 1 f = 0 := by
  simp only [centredSum, nonSingletonPartitions_one, Finset.sum_empty]
end TupleClassesClosed
open TupleClassesClosed in
theorem TupleClassesClosed.holds :
    TupleClassesClosed.Claim := fun _ _ =>
  ⟨fun _ _ _ _ =>
    ⟨fun _ hA hdisj =>
      ⟨fun _ hf => pi_mem_sepTuplesIn hA hdisj hf,
        fun _ hf => pi_mem_lipSepTuplesIn hA hdisj hf⟩,
      fun _ hf => ⟨comp_perm_mem_sepTuplesIn hf, fun S _ => restrictTuple_mem hf S⟩,
      fun _ hf => ⟨comp_perm_mem_lipSepTuplesIn hf, fun S _ => restrictTuple_mem_lipSepTuplesIn hf S⟩⟩,
    fun _ _ =>
    ⟨fun _ _ hf _ hP S hS => ⟨(Finset.mem_filter.mp hP).2 S hS, restrictTuple_mem hf S⟩,
      fun Φ _ => ⟨centredSum_zero Φ, centredSum_one Φ⟩⟩⟩
end YangMills.Construction.LatticeLimits
end
