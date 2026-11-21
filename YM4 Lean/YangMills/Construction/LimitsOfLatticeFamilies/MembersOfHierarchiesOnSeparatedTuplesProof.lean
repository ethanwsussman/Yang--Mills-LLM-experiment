import YangMills.Construction.LimitsOfLatticeFamilies.CuttingIsometriesAndTheModulusProof
import YangMills.Construction.LimitsOfLatticeFamilies.FunctionSpacesAndTheSharpSeminorm
import YangMills.Construction.LimitsOfLatticeFamilies.MembersOfHierarchiesOnSeparatedTuples
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
namespace SepTupleMembers
theorem closureWrt_isClosed {X : Type*} {d : X → X → ℝ}
    (htri : ∀ x y w, d x y ≤ d x w + d w y) (Z : Set X) :
    MetricNotions.IsClosedWrt d (MetricNotions.closureWrt d Z) := by apply _root_.YangMills.Construction.LatticeLimits.CutoffAndSymmetry.isClosedWrt_closureWrt <;> assumption
theorem isCompactWrt_of_subset {X : Type*} {d : X → X → ℝ} {K C : Set X}
    (hK : MetricNotions.IsCompactWrt d K) (hC : MetricNotions.IsClosedWrt d C) (hCK : C ⊆ K) :
    MetricNotions.IsCompactWrt d C := by apply _root_.YangMills.SharedProofs.p5019 <;> assumption
variable {s : Conventions.StandingParameters} {Y : ModelSpace}
theorem ballAtBase_mono {ρ ρ' : ℝ≥0∞} (h : ρ ≤ ρ') : ballAtBase s Y ρ ⊆ ballAtBase s Y ρ' :=
  fun _ hy => lt_of_lt_of_le hy h
theorem mem_sepTuplesIn_of_pi {n : ℕ} {ρ : ℝ≥0∞} {A : Fin n → Set (Y.Carrier s)}
    (hA : ∀ l, A l ⊆ ballAtBase s Y ρ) (hd : ∀ l k, l ≠ k → Disjoint (A l) (A k))
    {h : FunTuple s Y n} (hh : ∀ l, h l ∈ c1CompactSupp s Y (A l)) : h ∈ sepTuplesIn s Y n ρ :=
  ⟨⟨fun l => (hh l).1, fun l => (hh l).2.1,
    fun l k hlk => (hd l k hlk).mono (hh l).2.2 (hh k).2.2⟩,
    fun l => (hh l).2.2.trans (hA l)⟩
theorem update_mem_pi {n : ℕ} {A : Fin n → Set (Y.Carrier s)} {g : FunTuple s Y n}
    (hg : ∀ l, g l ∈ c1CompactSupp s Y (A l)) {i : Fin n} {w : Y.Carrier s → ℝ}
    (hw : w ∈ c1CompactSupp s Y (A i)) : ∀ l, Function.update g i w l ∈ c1CompactSupp s Y (A l) := by
  intro l
  by_cases hl : l = i
  · subst hl
    simpa using hw
  · simpa [Function.update_of_ne hl] using hg l
theorem restrictSeq_extend_eq (P : HierarchySequence s Y) {j n : ℕ} {g : FunTuple s Y n}
    (hg : g ∈ sepTuplesIn s Y n (P.rad j)) :
    (P.restrictSeq j n).extend g = (P.phi j n).extend g :=
  TupleFunctional.extend_of_mem _ hg
end SepTupleMembers
open SepTupleMembers in
theorem SepTupleMembers.holds
    (hCompact : CompactBallsAndTorus.Claim)
    (hNorm : InvariantDistFromNorm.Claim)
    (hLipschitz : C1CompactSuppIsLipschitz)
    (hSharp : SharpSeminorm.Properties) :
    SepTupleMembers.Claim := by
  intro s Y P n hn
  have hc1lip : ∀ A : Set (Y.Carrier s), c1CompactSupp s Y A ⊆ lipCompactSupp s Y A :=
    ((hLipschitz.1 s Y).2)
  have hcompactLarge : ∀ S : Set (Y.Carrier s), IsCompactIn s Y S →
      EventuallyIn P.indices fun j => S ⊆ ballAtBase s Y (P.rad j) := by
    intro S hS
    obtain ⟨ρ, hρ, hsub⟩ := (((hCompact s).1 Y).2 S hS).1
    obtain ⟨j₀, hj₀⟩ := P.rad_eventually_ge ρ hρ
    exact ⟨j₀, fun j hj hle => hsub.trans (ballAtBase_mono (hj₀ j hj hle))⟩
  refine ⟨fun j hj => ⟨?_, ?_, ?_, ?_⟩, hcompactLarge, ?_⟩
  · intro f hf
    exact ⟨fun i => (hc1lip univ ⟨hf.1.1 i, hf.1.2.1 i, subset_univ _⟩).1, hf.1.2.1,
      hf.1.2.2, hf.2⟩
  · intro h hh p
    have hperm : (fun l => h (p l)) ∈ sepTuplesIn s Y n (P.rad j) :=
      ⟨⟨fun _ => hh.1.1 _, fun _ => hh.1.2.1 _,
        fun _ _ hik => hh.1.2.2 _ _ fun e => hik (p.injective e)⟩, fun _ => hh.2 _⟩
    have hlipTuple : h ∈ lipSepTuplesIn s Y n (P.rad j) :=
      ⟨fun i => (hc1lip univ ⟨hh.1.1 i, hh.1.2.1 i, subset_univ _⟩).1, hh.1.2.1, hh.1.2.2, hh.2⟩
    rw [restrictSeq_extend_eq P hperm, restrictSeq_extend_eq P hh]
    exact P.phi_symm j hj n hn h hlipTuple p
  · intro A hA hd g hg i u hu v hv α β
    have hM : BlockScale s := ⟨1, 0, by simp⟩
    have hcomb : α • u + β • v ∈ c1CompactSupp s Y (A i) := by
      obtain ⟨W, hW⟩ := ((hSharp s hM Y).2.1) (A i)
      have hu' : u ∈ (W : Set (Y.Carrier s → ℝ)) := hW ▸ hu
      have hv' : v ∈ (W : Set (Y.Carrier s → ℝ)) := hW ▸ hv
      have : α • u + β • v ∈ (W : Set (Y.Carrier s → ℝ)) :=
        W.add_mem (W.smul_mem α hu') (W.smul_mem β hv')
      exact hW ▸ this
    rw [restrictSeq_extend_eq P (mem_sepTuplesIn_of_pi hA hd (update_mem_pi hg hcomb)),
      restrictSeq_extend_eq P (mem_sepTuplesIn_of_pi hA hd (update_mem_pi hg hu)),
      restrictSeq_extend_eq P (mem_sepTuplesIn_of_pi hA hd (update_mem_pi hg hv))]
    exact P.phi_multilinear j hj n hn A hA hd g (fun l => hc1lip _ (hg l)) i u (hc1lip _ hu) v
      (hc1lip _ hv) α β
  · intro d R hd hR f hf hsupp
    obtain ⟨-, -, -, -, -, htri, -⟩ := hNorm s Y
    have hself : ∀ x : Y.Carrier s, ModelSpace.dist s Y x x = 0 := fun x =>
      ((hNorm s Y).2.2.2.1 x x).2 rfl
    refine ⟨hf.1, fun i => ?_, fun i k hik => ?_, hsupp⟩
    · obtain ⟨x, hx⟩ := hf.2.1 i
      exact isCompactWrt_of_subset (((hCompact s).1 Y).1 x R hR)
        (closureWrt_isClosed htri _) hx
    · refine Set.disjoint_left.2 fun x hxi hxk => ?_
      have h1 : ModelSpace.infDist s Y (supportIn s Y (f i)) (supportIn s Y (f k)) ≤
          ENNReal.ofReal (ModelSpace.dist s Y x x) :=
        iInf₂_le_of_le x hxi (iInf₂_le x hxk)
      have h2 := (hf.2.2 i k hik).trans h1
      rw [hself x, ENNReal.ofReal_zero] at h2
      exact absurd h2 (not_le.2 (ENNReal.ofReal_pos.2 hd))
  · intro f hf
    choose j₀ hj₀ using fun i => hcompactLarge (supportIn s Y (f i)) (hf.2.1 i)
    refine ⟨Finset.univ.sup j₀, fun j hj hle => ?_⟩
    have hin : ∀ i, supportIn s Y (f i) ⊆ ballAtBase s Y (P.rad j) := fun i =>
      hj₀ i j hj ((Finset.le_sup (Finset.mem_univ i)).trans hle)
    exact ⟨⟨hf, hin⟩, hj, hin⟩
end YangMills.Construction.LatticeLimits
end
