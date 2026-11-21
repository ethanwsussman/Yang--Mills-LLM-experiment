import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import YangMills.Construction.ResponseInTheExpansion.RemainderOfTheResponseReturnsProof
import YangMills.Construction.ResponseInTheExpansion.WeightsExtendToATorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps BlockAverages
namespace Extension
theorem abs_clamp_sub_clamp_le (S a b : ℝ) : |max (-S) (min S a) - max (-S) (min S b)| ≤ |a - b| := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.abs_clamp_sub_le <;> assumption
theorem exists_bounded_lipschitz_extension {P ι : Type} (D : P → P → ℝ) (hD0 : ∀ p, D p p = 0)
    (hDs : ∀ p p', D p p' = D p' p) (hDt : ∀ p p' p'', D p p'' ≤ D p p' + D p' p'') (A : Finset ι) (e : ι → P)
    (v : ι → ℝ) {S : ℝ} (hS : 0 ≤ S) (hv : ∀ q ∈ A, |v q| ≤ S)
    (hL : ∀ q ∈ A, ∀ q₂ ∈ A, v q ≤ v q₂ + S * D (e q) (e q₂)) :
    ∃ f : P → ℝ, (∀ q ∈ A, f (e q) = v q) ∧ (∀ p, |f p| ≤ S) ∧ ∀ p p', |f p - f p'| ≤ S * D p p' := by
  by_cases hA : A.Nonempty
  · obtain ⟨g, hg⟩ : ∃ g : P → ℝ, g = fun p => A.inf' hA fun q => v q + S * D p (e q) := ⟨_, rfl⟩
    have hgl : ∀ p p', g p ≤ g p' + S * D p p' := by
      intro p p'
      obtain ⟨q, hq, hq'⟩ := Finset.exists_mem_eq_inf' hA (fun q => v q + S * D p' (e q))
      have h1 : g p ≤ v q + S * D p (e q) := by
        rw [hg]
        exact Finset.inf'_le (fun q => v q + S * D p (e q)) hq
      have h3 : g p' = v q + S * D p' (e q) := by
        rw [hg]
        exact hq'
      have h4 := mul_le_mul_of_nonneg_left (hDt p p' (e q)) hS
      rw [h3]
      rw [mul_add] at h4
      linarith only [h1, h4]
    refine ⟨fun p => max (-S) (min S (g p)), ?_, ?_, ?_⟩
    · intro q hq
      have h1 : g (e q) ≤ v q := by
        have h0 := Finset.inf'_le (fun q₂ => v q₂ + S * D (e q) (e q₂)) hq
        have hself : v q + S * D (e q) (e q) = v q := by
          rw [hD0, mul_zero, add_zero]
        rw [hg]
        exact le_trans h0 (le_of_eq hself)
      have h2 : v q ≤ g (e q) := by
        rw [hg]
        exact Finset.le_inf' _ _ fun q₂ hq₂ => hL q hq q₂ hq₂
      have h3 : g (e q) = v q := le_antisymm h1 h2
      show max (-S) (min S (g (e q))) = v q
      rw [h3]
      have := abs_le.mp (hv q hq)
      rw [min_eq_right this.2, max_eq_right this.1]
    · intro p
      rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith only [hS]) (min_le_left _ _)⟩
    · intro p p'
      refine (abs_clamp_sub_clamp_le S _ _).trans ?_
      rw [abs_le]
      have h1 := hgl p p'
      have h2 := hgl p' p
      rw [hDs p' p] at h2
      constructor <;> linarith only [h1, h2]
  · refine ⟨fun _ => 0, fun q hq => absurd ⟨q, hq⟩ hA, fun _ => by simpa using hS, fun p p' => ?_⟩
    have h0 : 0 ≤ D p p' := by
      have h1 := hDt p p' p
      rw [hD0, hDs p' p] at h1
      linarith only [h1]
    simpa using mul_nonneg hS h0
def directionCount (μ ν i : Fin 4) : ℤ := (if i = μ then 1 else 0) + (if i = ν then 1 else 0)
theorem doubledBarycentre_add_apply {M : ℕ} [NeZero M] (x : TorusSite M) (z : Fin 4 → ℤ) (μ ν i : Fin 4) :
    doubledBarycentre (x + siteOfInt z, μ, ν) i =
      ((2 * (((x i).cast : ℤ) + z i) + directionCount μ ν i : ℤ) : ZMod (2 * M)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ((x i).cast : ℤ) + z i := ⟨_, rfl⟩
  have hx : (x + siteOfInt z : TorusSite M) i = ((k : ℤ) : ZMod M) := by
    rw [hk]
    simp [siteOfInt]
  have hv : ((((x + siteOfInt z : TorusSite M) i).val : ℕ) : ℤ) = k % (M : ℤ) := by
    rw [hx, ZMod.val_intCast]
  have hM : (((2 * M : ℕ) : ℤ) : ZMod (2 * M)) = 0 := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_self _
  have e : ((2 * ((x + siteOfInt z : TorusSite M) i).val + (if i = μ then 1 else 0) + (if i = ν then 1 else 0) : ℕ) : ℤ) =
      (2 * k + directionCount μ ν i) + ((2 * M : ℕ) : ℤ) * (-(k / (M : ℤ))) := by
    push_cast
    rw [hv, Int.emod_def]
    unfold directionCount
    split_ifs <;> push_cast <;> ring
  rw [← hk]
  show ((2 * ((x + siteOfInt z : TorusSite M) i).val + (if i = μ then 1 else 0) + (if i = ν then 1 else 0) : ℕ) : ZMod (2 * M)) = _
  have e2 : ((2 * ((x + siteOfInt z : TorusSite M) i).val + (if i = μ then 1 else 0) + (if i = ν then 1 else 0) : ℕ) : ZMod (2 * M)) =
      (((2 * ((x + siteOfInt z : TorusSite M) i).val + (if i = μ then 1 else 0) + (if i = ν then 1 else 0) : ℕ) : ℤ) : ZMod (2 * M)) := by
    simp
  rw [e2, e, Int.cast_add, Int.cast_mul _ (-(k / (M : ℤ))), hM, zero_mul, add_zero]
def doubledOffset (z z₂ : Fin 4 → ℤ) (μ ν μ₂ ν₂ i : Fin 4) : ℤ :=
  2 * (z i - z₂ i) + directionCount μ ν i - directionCount μ₂ ν₂ i
theorem supDist_doubledBarycentre {M : ℕ} [NeZero M] (x : TorusSite M) (z z₂ : Fin 4 → ℤ) (μ ν μ₂ ν₂ : Fin 4)
    (hs : ∀ i, |doubledOffset z z₂ μ ν μ₂ ν₂ i| < (M : ℤ)) :
    supDist (doubledBarycentre (x + siteOfInt z, μ, ν)) (doubledBarycentre (x + siteOfInt z₂, μ₂, ν₂)) =
      Finset.univ.sup fun i => (doubledOffset z z₂ μ ν μ₂ ν₂ i).natAbs := by
  haveI : NeZero (2 * M) := ⟨mul_ne_zero two_ne_zero (NeZero.ne M)⟩
  unfold supDist
  congr 1
  funext i
  have e : (doubledBarycentre (x + siteOfInt z, μ, ν) i - doubledBarycentre (x + siteOfInt z₂, μ₂, ν₂) i : ZMod (2 * M)) =
      ((doubledOffset z z₂ μ ν μ₂ ν₂ i : ℤ) : ZMod (2 * M)) := by
    rw [doubledBarycentre_add_apply, doubledBarycentre_add_apply, ← Int.cast_sub]
    congr 1
    unfold doubledOffset
    ring
  rw [e]
  have h1 := abs_lt.mp (hs i)
  have : ((doubledOffset z z₂ μ ν μ₂ ν₂ i : ℤ) : ZMod (2 * M)).valMinAbs = doubledOffset z z₂ μ ν μ₂ ν₂ i := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_, ?_⟩ <;> push_cast <;> linarith only [h1.1, h1.2]
  rw [this]
theorem directionCount_nonneg_le_one (μ ν i : Fin 4) (h : μ < ν) :
    0 ≤ directionCount μ ν i ∧ directionCount μ ν i ≤ 1 := by
  have hne : μ ≠ ν := ne_of_lt h
  unfold directionCount
  by_cases h1 : i = μ
  · subst h1
    simp [hne]
  · by_cases h2 : i = ν
    · subst h2
      simp [h1]
    · simp [h1, h2]
theorem directionCount_injective : ∀ μ ν μ₂ ν₂ : Fin 4, μ < ν → μ₂ < ν₂ →
    (∀ i, directionCount μ ν i = directionCount μ₂ ν₂ i) → μ = μ₂ ∧ ν = ν₂ := by apply _root_.YangMills.Construction.AffineTorusIsometries.axes_eq_of_axisCount <;> assumption
end Extension
open Extension in
theorem weightExtensionStatement_holds : weightExtensionStatement := by
  classical
  intro L _ hodd t n n' _ _ hn hn' y y' h
  have hLpos : (1 : ℤ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (L : ℤ) ^ t := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    exact one_le_pow₀ hLpos
  have hside : ∀ N : ℕ, 8 ≤ N → 8 * Q ≤ ((fineSide L t N : ℕ) : ℤ) := by
    intro N hN
    rw [fineSide_eq, hQ]
    push_cast
    have hN' : (8 : ℤ) ≤ N := by exact_mod_cast hN
    have hp : (0 : ℤ) ≤ (L : ℤ) ^ t := by positivity
    nlinarith only [hN', hp]
  obtain ⟨S, hS⟩ : ∃ S, S = weightNorm L t h := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
  obtain ⟨c, hc⟩ : ∃ c, c = fineCentre L t y := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = fineCentre L t y' := ⟨_, rfl⟩
  let Z : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-Q) Q
  let Qs : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4) :=
    (Z ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4))).filter fun q => IsPlaquetteAt L t y (c + siteOfInt q.1, q.2.1, q.2.2)
  have hmem : ∀ q, q ∈ Qs ↔ (∀ i, |q.1 i| ≤ Q) ∧ IsPlaquetteAt L t y (c + siteOfInt q.1, q.2.1, q.2.2) := by
    intro q
    simp only [Qs, Z, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_univ,
      and_true, abs_le]
  have hbd : BddAbove (Set.range fun p : OrientedPlaquette (fineSide L t n) => |h p.1|) := (Set.finite_range _).bddAbove
  have hbd2 : BddAbove (Set.range fun pp : OrientedPlaquette (fineSide L t n) × OrientedPlaquette (fineSide L t n) =>
      |h pp.1.1 - h pp.2.1| / barycentreDist L t pp.1.1 pp.2.1) := (Set.finite_range _).bddAbove
  have hv : ∀ q ∈ Qs, |h (c + siteOfInt q.1, q.2.1, q.2.2)| ≤ S := by
    intro q hq
    have hlt := ((hmem q).mp hq).2.1
    rw [hS]
    exact (le_ciSup hbd ⟨(c + siteOfInt q.1, q.2.1, q.2.2), hlt⟩).trans (le_max_left _ _)
  have hsm : ∀ q ∈ Qs, ∀ q₂ ∈ Qs, ∀ i, ∀ N : ℕ, 8 ≤ N →
      |doubledOffset q.1 q₂.1 q.2.1 q.2.2 q₂.2.1 q₂.2.2 i| < ((fineSide L t N : ℕ) : ℤ) := by
    intro q hq q₂ hq₂ i N hN
    have h1 := abs_le.mp (((hmem q).mp hq).1 i)
    have h2 := abs_le.mp (((hmem q₂).mp hq₂).1 i)
    have h3 := directionCount_nonneg_le_one q.2.1 q.2.2 i ((hmem q).mp hq).2.1
    have h4 := directionCount_nonneg_le_one q₂.2.1 q₂.2.2 i ((hmem q₂).mp hq₂).2.1
    have h5 := hside N hN
    unfold doubledOffset
    rw [abs_lt]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5, hQ1]
  have hdist : ∀ q ∈ Qs, ∀ q₂ ∈ Qs,
      barycentreDist L t ((c + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n)) (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) =
        barycentreDist L t ((c' + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n')) (c' + siteOfInt q₂.1, q₂.2.1, q₂.2.2) := by
    intro q hq q₂ hq₂
    unfold barycentreDist
    rw [supDist_doubledBarycentre c q.1 q₂.1 _ _ _ _ fun i => hsm q hq q₂ hq₂ i n hn,
      supDist_doubledBarycentre c' q.1 q₂.1 _ _ _ _ fun i => hsm q hq q₂ hq₂ i n' hn']
  have hLip : ∀ q ∈ Qs, ∀ q₂ ∈ Qs, h (c + siteOfInt q.1, q.2.1, q.2.2) ≤ h (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) +
      S * barycentreDist L t ((c' + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n'))
        (c' + siteOfInt q₂.1, q₂.2.1, q₂.2.2) := by
    intro q hq q₂ hq₂
    rw [← hdist q hq q₂ hq₂]
    have hlt := ((hmem q).mp hq).2.1
    have hlt₂ := ((hmem q₂).mp hq₂).2.1
    have hL1 : (0 : ℝ) < 2 * (L : ℝ) ^ t := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    by_cases hd : barycentreDist L t ((c + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n))
        (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) = 0
    · have hz : supDist (doubledBarycentre ((c + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n)))
          (doubledBarycentre (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2)) = 0 := by
        unfold barycentreDist at hd
        have := (div_eq_zero_iff.mp hd).resolve_right hL1.ne'
        exact_mod_cast this
      rw [supDist_doubledBarycentre c q.1 q₂.1 _ _ _ _ fun i => hsm q hq q₂ hq₂ i n hn] at hz
      have hg : ∀ i, doubledOffset q.1 q₂.1 q.2.1 q.2.2 q₂.2.1 q₂.2.2 i = 0 := by
        intro i
        have h1 : (doubledOffset q.1 q₂.1 q.2.1 q.2.2 q₂.2.1 q₂.2.2 i).natAbs ≤ 0 := by
          rw [← hz]
          exact Finset.le_sup (f := fun i => (doubledOffset q.1 q₂.1 q.2.1 q.2.2 q₂.2.1 q₂.2.2 i).natAbs) (Finset.mem_univ i)
        omega
      have hzz : ∀ i, q.1 i = q₂.1 i ∧ directionCount q.2.1 q.2.2 i = directionCount q₂.2.1 q₂.2.2 i := by
        intro i
        have h1 := hg i
        have h3 := directionCount_nonneg_le_one q.2.1 q.2.2 i hlt
        have h4 := directionCount_nonneg_le_one q₂.2.1 q₂.2.2 i hlt₂
        unfold doubledOffset at h1
        constructor <;> omega
      obtain ⟨e1, e2⟩ := directionCount_injective _ _ _ _ hlt hlt₂ fun i => (hzz i).2
      have e3 : q.1 = q₂.1 := funext fun i => (hzz i).1
      rw [e1, e2, e3]
      have := mul_nonneg hS0 (div_nonneg (Nat.cast_nonneg _) hL1.le :
        0 ≤ barycentreDist L t ((c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) : TorusPlaquette (fineSide L t n))
          (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2))
      exact le_add_of_nonneg_right this
    · have hpos : 0 < barycentreDist L t ((c + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n))
          (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) :=
        lt_of_le_of_ne (div_nonneg (Nat.cast_nonneg _) hL1.le) (Ne.symm hd)
      have h1 := le_ciSup hbd2 (⟨(c + siteOfInt q.1, q.2.1, q.2.2), hlt⟩, ⟨(c + siteOfInt q₂.1, q₂.2.1, q₂.2.2), hlt₂⟩)
      have h2 : weightLipschitz L t h ≤ S := by
        rw [hS]
        exact le_max_right _ _
      have h3 := h1.trans h2
      have h4 := (div_le_iff₀ hpos).mp h3
      have h5 := le_abs_self (h (c + siteOfInt q.1, q.2.1, q.2.2) - h (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2))
      linarith only [h4, h5]
  have hL0 : (0 : ℝ) < 2 * (L : ℝ) ^ t := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_bounded_lipschitz_extension (P := TorusPlaquette (fineSide L t n')) (barycentreDist L t)
    (fun p => by simp [barycentreDist, supDist_self])
    (fun p p' => by
      unfold barycentreDist
      rw [supDist_comm])
    (fun p p' p'' => by
      unfold barycentreDist
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hL0.le
      exact_mod_cast supDist_triangle _ _ _)
    Qs (fun q => ((c' + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n')))
    (fun q => h (c + siteOfInt q.1, q.2.1, q.2.2)) hS0 hv hLip
  refine ⟨f, ?_, ?_⟩
  · intro z μ ν hz hat
    rw [← hc, ← hc'] at *
    have hq : (z, μ, ν) ∈ Qs := (hmem _).mpr ⟨fun i => by rw [hQ]; exact hz i, hat⟩
    exact (hf1 _ hq).symm
  · rw [← hS]
    haveI : Nonempty (OrientedPlaquette (fineSide L t n')) :=
      ⟨⟨(0, (0 : Fin 4), (1 : Fin 4)), by show (0 : Fin 4) < 1; decide⟩⟩
    refine max_le (ciSup_le fun p => hf2 _) (ciSup_le fun pp => ?_)
    by_cases hd : barycentreDist L t pp.1.1 pp.2.1 = 0
    · rw [hd, div_zero]
      exact hS0
    · have hpos : 0 < barycentreDist L t pp.1.1 pp.2.1 :=
        lt_of_le_of_ne (div_nonneg (Nat.cast_nonneg _) hL0.le) (Ne.symm hd)
      rw [div_le_iff₀ hpos]
      exact hf3 _ _
end YangMills.Construction.WeightedResponses
end
