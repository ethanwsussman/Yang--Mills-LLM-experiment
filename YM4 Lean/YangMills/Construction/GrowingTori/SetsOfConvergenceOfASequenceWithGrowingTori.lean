import YangMills.Construction.FamiliesOfLimits.BoundAndEquicontinuityWithAnAdmissibleNumber
import YangMills.Construction.GrowingTori.BoundFunctionsHierarchiesAndCentredMomentsOfFourSpace
import YangMills.Construction.GrowingTori.DataAndSequencesOfTheLimitsAlongGrowingTori
import YangMills.Construction.Sequences.DiagonalSubsequence
import YangMills.Construction.TorusOrFourSpace.EvaluationsAtDegenerateArguments
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriLimits
namespace Setup
abbrev euclidParams (D : Setup) : PeriodicSpace.Params := D.params.spaceParams 1
abbrev LimitHierarchy (D : Setup) : Type := EuclidHierarchy D.euclidParams
abbrev sepDomain (D : Setup) (n : ℕ) : Set (Fin n → RealFn) :=
  PeriodicSpace.Kind.sepC1Tuples D.euclidParams .euclidean n
end Setup
structure BoundedFamily where
  Idx : Type
  countable : Countable Idx
  start : Idx → ℤ
  seq : ∀ ι : Idx, {k : ℤ // start ι ≤ k} → ℂ
  bounded : ∀ ι, ∃ B : ℝ, ∀ k, ‖seq ι k‖ ≤ B
def BoundedFamily.empty : BoundedFamily where
  Idx := Empty
  countable := inferInstance
  start := Empty.elim
  seq := fun ι => ι.elim
  bounded := fun ι => ι.elim
namespace ToriSequence
variable {D : Setup} (S : ToriSequence D)
def Defined {n : ℕ} (f : Fin n → RealFn) (k : ℕ+) : Prop :=
  f ∈ GrowingTori.lipTuplesInBall D.L n (S.radius k)
def TendsAlong (J : Sequences.PNatIndexSet) {n : ℕ}
    (f : Fin n → RealFn) (z : ℂ) : Prop :=
  PeriodicSpace.DiagonalLimits.TendsToWhereDefined J (S.Defined f)
    (fun k _ => S.connected k f) z
def IsLimitHierarchy (J : Sequences.PNatIndexSet) (Ξ : D.LimitHierarchy) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : D.sepDomain n),
    S.TendsAlong J f.1 ((Ξ.func n hn f : ℝ) : ℂ)
variable {S}
theorem TendsAlong.unique {J : Sequences.PNatIndexSet} {n : ℕ}
    {f : Fin n → RealFn} {z z' : ℂ} (h : S.TendsAlong J f z)
    (h' : S.TendsAlong J f z') : z = z' := by
  by_contra hne
  have hpos : 0 < ‖z - z'‖ / 2 := half_pos (norm_pos_iff.2 (sub_ne_zero.2 hne))
  obtain ⟨a, ha⟩ := h _ hpos
  obtain ⟨b, hb⟩ := h' _ hpos
  obtain ⟨k, hk, hlt⟩ := J.infinite.exists_gt ⟨(max a b).toNat + 1, by omega⟩
  have hle : max a b ≤ (((k : ℕ+) : ℕ) : ℤ) := by
    have h₁ : (max a b).toNat + 1 < (k : ℕ) := hlt
    omega
  obtain ⟨g, hg⟩ := ha k hk ((le_max_left _ _).trans hle)
  obtain ⟨g', hg'⟩ := hb k hk ((le_max_right _ _).trans hle)
  have : ‖z - z'‖ < ‖z - z'‖ / 2 + ‖z - z'‖ / 2 := by
    calc ‖z - z'‖ = ‖(S.connected k f - z') - (S.connected k f - z)‖ := by congr 1; ring
      _ ≤ ‖S.connected k f - z'‖ + ‖S.connected k f - z‖ := norm_sub_le _ _
      _ < ‖z - z'‖ / 2 + ‖z - z'‖ / 2 := by linarith
  linarith
theorem IsLimitHierarchy.unique {J : Sequences.PNatIndexSet} {Ξ Ξ' : D.LimitHierarchy}
    (h : S.IsLimitHierarchy J Ξ) (h' : S.IsLimitHierarchy J Ξ') : Ξ = Ξ' := by
  refine PeriodicSpace.Kind.Hierarchy.ext ?_
  funext n hn f
  exact_mod_cast (h n hn f).unique (h' n hn f)
variable (S)
structure IsConvergenceSet (C : PeriodicSpace.BoundFamily) (J : Sequences.PNatIndexSet) :
    Prop where
  limit_exists : ∀ (n : ℕ), 2 ≤ n → ∀ f : D.sepDomain n, ∃ z, S.TendsAlong J f.1 z
  limit_hierarchy : ∃ Ξ : D.LimitHierarchy, S.IsLimitHierarchy J Ξ ∧
    Ξ ∈ boundedEuclidHierarchies D.euclidParams C ∧ Ξ.SatisfiesSepEstimate C
variable {S}
def IsConvergenceSet.lim {C : PeriodicSpace.BoundFamily} {J : Sequences.PNatIndexSet}
    (h : S.IsConvergenceSet C J) : D.LimitHierarchy :=
  h.limit_hierarchy.choose
theorem IsConvergenceSet.isLimitHierarchy_lim {C : PeriodicSpace.BoundFamily}
    {J : Sequences.PNatIndexSet} (h : S.IsConvergenceSet C J) : S.IsLimitHierarchy J h.lim :=
  h.limit_hierarchy.choose_spec.1
variable (S)
structure IsConvergenceSetWith (C : PeriodicSpace.BoundFamily) (F : BoundedFamily)
    (J : Sequences.PNatIndexSet) : Prop extends S.IsConvergenceSet C J where
  seq_tendsto : ∀ ι, PeriodicSpace.DiagonalLimits.HasLimitAlong J (F.start ι)
    (DiagonalSubsequence.restrictAlong (F.seq ι) J)
end ToriSequence
end YangMills.Construction.ToriLimits
end
