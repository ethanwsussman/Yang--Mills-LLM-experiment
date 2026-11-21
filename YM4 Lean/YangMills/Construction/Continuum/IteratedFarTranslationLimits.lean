import YangMills.Construction.Continuum.PlateauOfAFunctionOnTuples
import YangMills.Construction.Lattice.AdicRationalsPositive
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction
namespace SeparatedTuples
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
def adicGridVectors (L : ℕ) : Set AmbientSpace :=
  {v | ∀ μ, v μ ∈ PeriodicLattice.adicRationalsPositive L}
def IsShiftRange (L : ℕ) (V : Set AmbientSpace) : Prop := V = Set.univ ∨ V = adicGridVectors L
def atInfinityWithin (V : Set AmbientSpace) : Filter AmbientSpace := atInfinity ⊓ 𝓟 V
theorem atInfinityWithin_univ : atInfinityWithin Set.univ = atInfinity := by
  simp [atInfinityWithin]
theorem natCast_mem_adicRationalsPositive {L : ℕ} (hL : 1 ≤ L) (m : ℕ) :
    (m : ℝ) ∈ PeriodicLattice.adicRationalsPositive L := by
  have hL0 : (L : ℝ) ≠ 0 := by
    have : 0 < L := hL
    positivity
  refine (PeriodicLattice.mem_adicGridPointsPositive_iff L _).2 ⟨1, (m : ℤ) * (L : ℤ), ?_⟩
  simp [PeriodicLattice.meshSize, hL0]
theorem IsShiftRange.neBot {L : ℕ} {V : Set AmbientSpace} (hL : 1 ≤ L)
    (hV : IsShiftRange L V) : (atInfinityWithin V).NeBot := by
  have hmem : ∀ m : ℕ, (fun _ => (m : ℝ)) ∈ V := fun m => by
    rcases hV with rfl | rfl
    · exact Set.mem_univ _
    · exact fun _ => natCast_mem_adicRationalsPositive hL m
  have hnorm : ∀ m : ℕ, (m : ℝ) ≤ euclidNormVec fun _ => (m : ℝ) := fun m => by
    refine Real.le_sqrt_of_sq_le ?_
    have h : 0 ≤ (m : ℝ) ^ 2 := by positivity
    simp
    linarith
  refine inf_principal_neBot_iff.2 fun U hU => ?_
  obtain ⟨t, ht, htU⟩ := mem_comap.1 hU
  obtain ⟨a, ha⟩ := mem_atTop_sets.1 ht
  obtain ⟨m, hm⟩ := exists_nat_ge a
  exact ⟨fun _ => (m : ℝ), htU (ha _ (hm.trans (hnorm m))), hmem m⟩
def shiftedComponents (X : SepTuple) (P : List (SepTuple × AmbientSpace)) : List RealValued :=
  X.1 ++ P.flatMap fun p => (push (translate p.2) p.1).1
def shiftedJuxt (X : SepTuple) (P : List (SepTuple × AmbientSpace)) : SepTuple :=
  P.foldl (fun Z p => SepTuple.juxt Z (push (translate p.2) p.1)) X
theorem shiftedJuxt_val {X : SepTuple} {P : List (SepTuple × AmbientSpace)}
    (h : IsDisjointlySupported (shiftedComponents X P)) :
    (shiftedJuxt X P).1 = shiftedComponents X P := by
  induction P generalizing X with
  | nil => simp [shiftedJuxt, shiftedComponents]
  | cons p P ih =>
    have hdef : SepTuple.Composable X (push (translate p.2) p.1) := fun f hf g hg =>
      (List.pairwise_append.1 h.2).2.2 f hf g
        (List.mem_flatMap.2 ⟨p, List.mem_cons_self, hg⟩)
    have hval := SepTuple.juxt_val hdef
    have hsep : IsDisjointlySupported
        (shiftedComponents (SepTuple.juxt X (push (translate p.2) p.1)) P) := by
      have he : shiftedComponents (SepTuple.juxt X (push (translate p.2) p.1)) P =
          shiftedComponents X (p :: P) := by
        simp [shiftedComponents, hval]
      rwa [he]
    have hstep := ih hsep
    have he : shiftedComponents (SepTuple.juxt X (push (translate p.2) p.1)) P =
        shiftedComponents X (p :: P) := by
      simp [shiftedComponents, hval]
    rw [← he]
    exact hstep
theorem IsDisjointlySupported.perm {A B : List RealValued} (h : IsDisjointlySupported A)
    (hAB : A.Perm B) : IsDisjointlySupported B :=
  ⟨fun f hf => h.1 f (hAB.mem_iff.2 hf), (hAB.pairwise_iff fun hd => hd.symm).1 h.2⟩
variable (s : SepTuple → ℝ) (X : SepTuple) (Y : List SepTuple) (V : Set AmbientSpace)
def iterLimitValue : ℕ → List AmbientSpace → ℝ
  | 0, vs => s (shiftedJuxt X (Y.zip vs))
  | k + 1, vs => limUnder (atInfinityWithin V) fun v => iterLimitValue k (v :: vs)
def iterLimitDomain (k : ℕ) : Set (List AmbientSpace) :=
  {vs | vs.length + k = Y.length ∧ (∀ v ∈ vs, v ∈ V) ∧
    IsDisjointlySupported (shiftedComponents X ((Y.drop k).zip vs))}
def IterLimitsExist : Prop :=
  ∀ k < Y.length, ∀ vs ∈ iterLimitDomain X Y V (k + 1),
    ∃ c : ℝ, Tendsto (fun v => iterLimitValue s X Y V k (v :: vs)) (atInfinityWithin V) (𝓝 c)
def iteratedLimitAtInfinity : ℝ := iterLimitValue s X Y V Y.length []
theorem iterLimitDomain_length : iterLimitDomain X Y V Y.length = {[]} := by
  ext vs
  constructor
  · intro h
    have hlen : vs.length = 0 := by
      have := h.1
      omega
    simpa using List.eq_nil_of_length_eq_zero hlen
  · rintro rfl
    refine ⟨by simp, by simp, ?_⟩
    simpa [shiftedComponents] using X.2
theorem cons_mem_iterLimitDomain_of_composable {k : ℕ} (hk : k < Y.length)
    {vs : List AmbientSpace} (hvs : vs ∈ iterLimitDomain X Y V (k + 1)) {v : AmbientSpace}
    (hv : v ∈ V) (hdef : SepTuple.Composable ⟨_, hvs.2.2⟩ (push (translate v) Y[k])) :
    v :: vs ∈ iterLimitDomain X Y V k := by
  refine ⟨?_, List.forall_mem_cons.2 ⟨hv, hvs.2.1⟩, ?_⟩
  · have := hvs.1
    simp only [List.length_cons]
    omega
  · rw [List.drop_eq_getElem_cons hk, List.zip_cons_cons]
    refine (SepTuple.glue ⟨_, hvs.2.2⟩ _ hdef).2.perm ?_
    simp only [SepTuple.glue, shiftedComponents, List.flatMap_cons, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
theorem eventually_cons_mem_iterLimitDomain {k : ℕ} (hk : k < Y.length) {vs : List AmbientSpace}
    (hvs : vs ∈ iterLimitDomain X Y V (k + 1)) :
    ∀ᶠ v in atInfinityWithin V, v :: vs ∈ iterLimitDomain X Y V k := by
  filter_upwards [(eventually_composable ⟨_, hvs.2.2⟩ Y[k]).filter_mono inf_le_left,
    mem_inf_of_right (mem_principal_self V)] with v hdef hv
  exact cons_mem_iterLimitDomain_of_composable X Y V hk hvs hv hdef
theorem tendsto_iterLimitValue {s : SepTuple → ℝ} {X : SepTuple} {Y : List SepTuple}
    {V : Set AmbientSpace} (h : IterLimitsExist s X Y V) {k : ℕ} (hk : k < Y.length)
    {vs : List AmbientSpace} (hvs : vs ∈ iterLimitDomain X Y V (k + 1)) :
    Tendsto (fun v => iterLimitValue s X Y V k (v :: vs)) (atInfinityWithin V)
      (𝓝 (iterLimitValue s X Y V (k + 1) vs)) :=
  tendsto_nhds_limUnder (h k hk vs hvs)
end SeparatedTuples
end YangMills.Construction
