import YangMills.Construction.Torus.CubePartitionProperties
import YangMills.Construction.Torus.ProjSmallCubes
import Mathlib
set_option autoImplicit false
open Set Metric
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Torus.CubePartition
variable {d : ℕ} {S σ : ℝ}
theorem continuous_torusProj : Continuous (torusProj d S) :=
  continuous_pi fun μ => (AddCircle.continuous_mk' S).comp (continuous_apply μ)
theorem mem_closedBall_iff_abs_sub_le (v c : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    v ∈ closedBall c r ↔ ∀ μ, |v μ - c μ| ≤ r := by
  rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hr]
  simp [Real.norm_eq_abs]
theorem abs_sub_lt_of_mem_ball {v c : Fin d → ℝ} {r : ℝ} (h : v ∈ ball c r) (μ : Fin d) :
    |v μ - c μ| < r := by
  rw [mem_ball, dist_eq_norm] at h
  have := norm_le_pi_norm (v - c) μ
  rw [Pi.sub_apply, Real.norm_eq_abs] at this
  linarith
theorem isOpen_torusProj_image_ball (c : Fin d → ℝ) {r : ℝ} (hr : 0 < r) :
    IsOpen (torusProj d S '' ball c r) := by
  have himg : torusProj d S '' ball c r =
      pi univ fun μ => ((↑) : ℝ → AddCircle S) '' ball (c μ) r := by
    ext p
    constructor
    · rintro ⟨v, hv, rfl⟩ μ -
      rw [ball_pi _ hr] at hv
      exact ⟨v μ, hv μ (mem_univ μ), rfl⟩
    · intro hp
      choose v hv hv' using fun μ => hp μ (mem_univ μ)
      refine ⟨v, ?_, funext hv'⟩
      rw [ball_pi _ hr]
      exact fun μ _ => hv μ
  rw [himg]
  exact isOpen_set_pi finite_univ fun μ _ =>
    QuotientAddGroup.isOpenMap_coe _ isOpen_ball
theorem cubeAt_eq_image_closedBall (h : ProjCubes.ProjFacts d S) (c : Fin d → ℝ) (hσ : 0 ≤ σ) :
    cubeAt (torusProj d S c) σ = torusProj d S '' closedBall c (σ / 2) := by
  ext p
  rw [h.mem_cubeAt_iff c σ p hσ]
  constructor
  · rintro ⟨v, hv, hv'⟩
    exact ⟨v, (mem_closedBall_iff_abs_sub_le v c (by linarith)).2 hv', hv⟩
  · rintro ⟨v, hv, hv'⟩
    exact ⟨v, hv', (mem_closedBall_iff_abs_sub_le v c (by linarith)).1 hv⟩
theorem interior_cubeAt_eq_image_ball (h : ProjCubes.ProjFacts d S) (c : Fin d → ℝ)
    (hσ : 0 < σ) (hσS : 2 * σ ≤ S) :
    interior (cubeAt (torusProj d S c) σ) = torusProj d S '' ball c (σ / 2) := by
  have hr : 0 < σ / 2 := by linarith
  rw [cubeAt_eq_image_closedBall h c hσ.le]
  apply subset_antisymm
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := interior_subset hp
    by_cases hvb : v ∈ ball c (σ / 2)
    · exact mem_image_of_mem _ hvb
    exfalso
    have hnorm : ‖v - c‖ = σ / 2 := by
      rw [mem_closedBall, dist_eq_norm] at hv
      rw [mem_ball, dist_eq_norm, not_lt] at hvb
      exact le_antisymm hv hvb
    have hcont : Continuous fun t : ℝ => torusProj d S (c + t • (v - c)) :=
      continuous_torusProj.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hopen := (isOpen_interior (s := torusProj d S '' closedBall c (σ / 2))).preimage hcont
    have hone : (1 : ℝ) ∈ (fun t : ℝ => torusProj d S (c + t • (v - c))) ⁻¹'
        interior (torusProj d S '' closedBall c (σ / 2)) := by
      simpa using hp
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 1 hone
    set t : ℝ := 1 + min (ε / 2) (1 / 2) with ht
    have hm0 : 0 < min (ε / 2) (1 / 2 : ℝ) := lt_min (by linarith) (by norm_num)
    have hm1 : min (ε / 2) (1 / 2 : ℝ) ≤ ε / 2 := min_le_left _ _
    have hm2 : min (ε / 2) (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
    have htε : t ∈ ball (1 : ℝ) ε := by
      rw [mem_ball, Real.dist_eq, ht, add_sub_cancel_left, abs_of_pos hm0]
      linarith
    obtain ⟨w, hw, hwt⟩ := interior_subset (hball htε)
    have hdist : ‖(c + t • (v - c)) - c‖ = t * (σ / 2) := by
      rw [add_sub_cancel_left, norm_smul, hnorm, Real.norm_eq_abs,
        abs_of_pos (by rw [ht]; linarith)]
    have hsmall : t * (σ / 2) < S / 2 := by nlinarith
    have hinj := h.injOn_cube c S le_rfl
    have hweq : w = c + t • (v - c) := by
      refine hinj ?_ ?_ hwt
      · intro μ
        have := (mem_closedBall_iff_abs_sub_le w c hr.le).1 hw μ
        linarith
      · intro μ
        refine abs_sub_lt_of_mem_ball (r := S / 2) ?_ μ
        rw [mem_ball, dist_eq_norm, hdist]
        exact hsmall
    rw [mem_closedBall, dist_eq_norm, hweq, hdist] at hw
    nlinarith
  · exact interior_maximal (image_mono ball_subset_closedBall)
      (isOpen_torusProj_image_ball c hr)
def latticePoint (σ : ℝ) (m : Fin d → ℤ) : Fin d → ℝ := fun μ => (m μ : ℝ) * σ
theorem torusProj_latticePoint_eq {k : ℕ} (hσ : 0 < σ) (hS : S = (k : ℝ) * σ)
    {m m' : Fin d → ℤ} {v w : Fin d → ℝ} (hv : v ∈ ball (latticePoint σ m) (σ / 2))
    (hw : w ∈ closedBall (latticePoint σ m') (σ / 2))
    (hvw : torusProj d S v = torusProj d S w) :
    torusProj d S (latticePoint σ m) = torusProj d S (latticePoint σ m') := by
  funext μ
  have hμ : ((v μ : ℝ) : AddCircle S) = (w μ : ℝ) := congrFun hvw μ
  have hz : ((w μ - v μ : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_sub, hμ, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 hz
  have h1 := abs_sub_lt_of_mem_ball hv μ
  have h2 := (mem_closedBall_iff_abs_sub_le w _ (by linarith)).1 hw μ
  have hn' : w μ - v μ = (n : ℝ) * ((k : ℝ) * σ) := by
    rw [← hn, hS, zsmul_eq_mul]
  simp only [latticePoint] at h1 h2
  have he : (m' μ : ℤ) - m μ - n * k = 0 := by
    by_contra hne
    have hge : (1 : ℝ) ≤ |(((m' μ : ℤ) - m μ - n * k : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hne
    have hcast : (((m' μ : ℤ) - m μ - n * k : ℤ) : ℝ) * σ =
        ((m' μ : ℝ) * σ - w μ) + (v μ - (m μ : ℝ) * σ) * (-1) * (-1) * 1 +
          ((w μ - v μ) - (n : ℝ) * ((k : ℝ) * σ)) := by
      push_cast
      ring
    have hlt : |(((m' μ : ℤ) - m μ - n * k : ℤ) : ℝ) * σ| < σ := by
      rw [hcast, hn', sub_self, add_zero]
      have e1 := abs_le.1 h2
      have e2 := abs_lt.1 h1
      rw [abs_lt]
      constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
    rw [abs_mul, abs_of_pos hσ] at hlt
    nlinarith
  have he' : (m' μ : ℝ) = (m μ : ℝ) + (n : ℝ) * (k : ℝ) := by
    have : ((((m' μ : ℤ) - m μ - n * k : ℤ)) : ℝ) = 0 := by rw [he]; simp
    push_cast at this
    linarith
  have hdiff : (m' μ : ℝ) * σ - (m μ : ℝ) * σ = n • S := by
    rw [he', hS, zsmul_eq_mul]
    ring
  have hz' : (((m' μ : ℝ) * σ - (m μ : ℝ) * σ : ℝ) : AddCircle S) = 0 :=
    (AddCircle.coe_eq_zero_iff S).2 ⟨n, hdiff.symm⟩
  rw [AddCircle.coe_sub, sub_eq_zero] at hz'
  exact hz'.symm
theorem mem_spacingLattice_iff (c : PeriodicTorus d S) :
    c ∈ spacingLattice d S σ ↔ ∃ m : Fin d → ℤ, c = torusProj d S (latticePoint σ m) := Iff.rfl
theorem center_eq_of_mem_interior (h : ProjCubes.ProjFacts d S) {k : ℕ} (hσ : 0 < σ)
    (hk : 2 ≤ k) (hS : S = (k : ℝ) * σ) {c c' : PeriodicTorus d S} (hc : c ∈ spacingLattice d S σ)
    (hc' : c' ∈ spacingLattice d S σ) {p : PeriodicTorus d S} (hp : p ∈ interior (cubeAt c σ))
    (hp' : p ∈ cubeAt c' σ) : c = c' := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hσS : 2 * σ ≤ S := by rw [hS]; nlinarith
  obtain ⟨m, rfl⟩ := (mem_spacingLattice_iff c).1 hc
  obtain ⟨m', rfl⟩ := (mem_spacingLattice_iff c').1 hc'
  rw [interior_cubeAt_eq_image_ball h _ hσ hσS] at hp
  rw [cubeAt_eq_image_closedBall h _ hσ.le] at hp'
  obtain ⟨v, hv, rfl⟩ := hp
  obtain ⟨w, hw, hvw⟩ := hp'
  exact torusProj_latticePoint_eq hσ hS hv hw hvw.symm
theorem spacingLattice_finite {k : ℕ} (hk : 2 ≤ k) (hS : S = (k : ℝ) * σ) :
    (spacingLattice d S σ : Set (PeriodicTorus d S)).Finite := by
  refine ((Set.finite_Icc (0 : Fin d → ℤ) fun _ => (k : ℤ)).image
    fun m => torusProj d S (latticePoint σ m)).subset ?_
  rintro c ⟨m, rfl⟩
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hkpos : (0 : ℤ) < k := by exact_mod_cast (by omega : 0 < k)
  refine ⟨fun μ => m μ % k,
    ⟨fun μ => Int.emod_nonneg _ hk0, fun μ => (Int.emod_lt_of_pos _ hkpos).le⟩, ?_⟩
  funext μ
  have hsplit : (m μ : ℝ) * σ - ((m μ % k : ℤ) : ℝ) * σ = (m μ / k) • S := by
    have hz : (((m μ % k : ℤ) : ℝ)) + (k : ℝ) * ((m μ / k : ℤ) : ℝ) = (m μ : ℝ) := by
      exact_mod_cast Int.emod_add_mul_ediv (m μ) k
    rw [hS, zsmul_eq_mul, ← hz]
    ring
  have hz' : (((m μ : ℝ) * σ - ((m μ % k : ℤ) : ℝ) * σ : ℝ) : AddCircle S) = 0 :=
    (AddCircle.coe_eq_zero_iff S).2 ⟨m μ / k, hsplit.symm⟩
  rw [AddCircle.coe_sub, sub_eq_zero] at hz'
  exact hz'.symm
theorem sUnion_cubePartition_eq_univ (h : ProjCubes.ProjFacts d S) (hσ : 0 < σ) :
    ⋃₀ cubePartition d S σ = univ := by
  refine eq_univ_of_forall fun p => ?_
  choose v hv using fun μ => QuotientAddGroup.mk_surjective (p μ)
  refine ⟨cubeAt (torusProj d S (latticePoint σ fun μ => round (v μ / σ))) σ,
    ⟨_, ⟨_, rfl⟩, rfl⟩, ?_⟩
  refine (h.mem_cubeAt_iff _ σ p hσ.le).2 ⟨v, funext hv, fun μ => ?_⟩
  have hr := abs_sub_round (v μ / σ)
  have he : v μ - latticePoint σ (fun μ => round (v μ / σ)) μ =
      (v μ / σ - (round (v μ / σ) : ℝ)) * σ := by
    simp only [latticePoint]
    field_simp
  rw [he, abs_mul, abs_of_pos hσ]
  nlinarith
theorem closure_sdiff_of_closedCover {T : Type*} [TopologicalSpace T] {P : Set (Set T)}
    (hfin : P.Finite) (hcl : ∀ Q ∈ P, IsClosed Q) (hint : ∀ Q ∈ P, closure (interior Q) = Q)
    (hsep : ∀ Q ∈ P, ∀ Q' ∈ P, Q' ≠ Q → ∀ p ∈ interior Q, p ∉ Q')
    {X Y : Set T} (hX : ∃ 𝒞 ⊆ P, X = ⋃₀ 𝒞) (hY : ∃ 𝒞 ⊆ P, Y = ⋃₀ 𝒞) :
    (Y ⊆ X → closure (X \ Y) = ⋃₀ {Q ∈ P | Q ⊆ X ∧ ¬ Q ⊆ Y}) ∧
      ∀ Q ∈ P, ¬ Q ⊆ Y → Disjoint (interior Q) Y := by
  have hdisj : ∀ Q ∈ P, ¬ Q ⊆ Y → Disjoint (interior Q) Y := by
    intro Q hQ hQY
    obtain ⟨𝒞, h𝒞, rfl⟩ := hY
    rw [Set.disjoint_left]
    rintro p hp ⟨Q', hQ', hpQ'⟩
    refine hsep Q hQ Q' (h𝒞 hQ') ?_ p hp hpQ'
    rintro rfl
    exact hQY (subset_sUnion_of_mem hQ')
  refine ⟨fun _ => ?_, hdisj⟩
  apply subset_antisymm
  · have hsub : {Q ∈ P | Q ⊆ X ∧ ¬ Q ⊆ Y}.Finite := hfin.subset fun Q hQ => hQ.1
    have hZ : IsClosed (⋃₀ {Q ∈ P | Q ⊆ X ∧ ¬ Q ⊆ Y}) := by
      rw [sUnion_eq_biUnion]
      exact hsub.isClosed_biUnion fun Q hQ => hcl Q hQ.1
    refine closure_minimal ?_ hZ
    rintro p ⟨hpX, hpY⟩
    obtain ⟨𝒞, h𝒞, rfl⟩ := hX
    obtain ⟨Q, hQ, hpQ⟩ := hpX
    exact ⟨Q, ⟨h𝒞 hQ, subset_sUnion_of_mem hQ, fun hs => hpY (hs hpQ)⟩, hpQ⟩
  · rintro p ⟨Q, ⟨hQ, hQX, hQY⟩, hpQ⟩
    rw [← hint Q hQ] at hpQ
    have hsub : interior Q ⊆ X \ Y := fun x hx =>
      ⟨hQX (interior_subset hx), Set.disjoint_left.1 (hdisj Q hQ hQY) hx⟩
    exact closure_mono hsub hpQ
theorem properties_hold (cov : ProjCubes.ProjFactsHold) : PropertiesOfIntegerMultiple := by
  intro d S σ k hd hσ hk hS
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hSpos : 0 < S := by rw [hS]; nlinarith
  have hσS : 2 * σ ≤ S := by rw [hS]; nlinarith
  have : Fact (0 < S) := ⟨hSpos⟩
  have h := cov d S hSpos
  have hfin : (cubePartition d S σ).Finite := by
    refine ((spacingLattice_finite hk hS).image fun c => cubeAt c σ).subset ?_
    rintro Q ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  have hcl : ∀ Q ∈ cubePartition d S σ, IsClosed Q := by
    rintro Q ⟨c, ⟨m, rfl⟩, rfl⟩
    have himg := cubeAt_eq_image_closedBall (σ := σ) h (fun μ => (m μ : ℝ) * σ) hσ.le
    rw [himg]
    exact ((isCompact_closedBall _ _).image continuous_torusProj).isClosed
  have hint : ∀ Q ∈ cubePartition d S σ, closure (interior Q) = Q := by
    rintro Q ⟨c, ⟨m, rfl⟩, rfl⟩
    have himg := cubeAt_eq_image_closedBall (σ := σ) h (fun μ => (m μ : ℝ) * σ) hσ.le
    have hclosed : IsClosed (cubeAt (torusProj d S fun μ => (m μ : ℝ) * σ) σ) :=
      hcl _ ⟨_, ⟨m, rfl⟩, rfl⟩
    apply subset_antisymm (closure_minimal interior_subset hclosed)
    rw [interior_cubeAt_eq_image_ball h _ hσ hσS, himg,
      ← closure_ball (fun μ => (m μ : ℝ) * σ) (by linarith : σ / 2 ≠ 0)]
    exact image_closure_subset_closure_image continuous_torusProj
  have hcenter : ∀ c ∈ spacingLattice d S σ, c ∈ interior (cubeAt c σ) := by
    rintro c ⟨m, rfl⟩
    rw [interior_cubeAt_eq_image_ball h _ hσ hσS]
    exact mem_image_of_mem _ (mem_ball_self (by linarith))
  have hsep : ∀ Q ∈ cubePartition d S σ, ∀ Q' ∈ cubePartition d S σ,
      Q' ≠ Q → ∀ p ∈ interior Q, p ∉ Q' := by
    rintro Q ⟨c, hc, rfl⟩ Q' ⟨c', hc', rfl⟩ hne p hp hp'
    exact hne (by rw [center_eq_of_mem_interior h hσ hk hS hc hc' hp hp'])
  have hcov := sUnion_cubePartition_eq_univ h hσ
  have hdiff : ∀ X Y : Set (PeriodicTorus d S), IsCubeUnion σ X → IsCubeUnion σ Y →
      (Y ⊆ X → closure (X \ Y) = ⋃₀ {Q ∈ cubePartition d S σ | Q ⊆ X ∧ ¬ Q ⊆ Y}) ∧
        ∀ Q ∈ cubePartition d S σ, ¬ Q ⊆ Y → Disjoint (interior Q) Y :=
    fun X Y hX hY => closure_sdiff_of_closedCover hfin hcl hint hsep hX hY
  have hcomp : ∀ Y : Set (PeriodicTorus d S), IsCubeUnion σ Y →
      cubeComplement σ Y = closure Yᶜ := by
    intro Y hY
    have huniv : IsCubeUnion σ (univ : Set (PeriodicTorus d S)) := ⟨_, subset_rfl, hcov.symm⟩
    have := (hdiff univ Y huniv hY).1 (subset_univ Y)
    rw [← compl_eq_univ_sdiff] at this
    rw [this]
    simp [cubeComplement]
  refine
    { finite := hfin
      isClosed_cube := hcl
      closure_interior := hint
      sUnion_eq_univ := hcov
      center_mem_interior := hcenter
      cubeAt_injective := ?_
      interior_not_mem_of_ne := hsep
      closure_diff_eq := fun X Y hX hY hYX => (hdiff X Y hX hY).1 hYX
      disjoint_interior := fun X Y hX hY _ Q hQ _ hQY => (hdiff X Y hX hY).2 Q hQ hQY
      compl_subset_cubeComplement := fun Y hY => by rw [hcomp Y hY]; exact subset_closure
      frontier_subset_cubeComplement := fun Y hY => by
        rw [hcomp Y hY, frontier_eq_closure_inter_closure]
        exact inter_subset_right
      cubeComplement_antitone := ?_
      cubeComplement_eq_closure_compl := hcomp }
  · intro c hc c' hc' heq
    refine center_eq_of_mem_interior h hσ hk hS hc hc' (hcenter c hc) ?_
    rw [← heq]
    exact interior_subset (hcenter c hc)
  · rintro X Y - - hYX p ⟨Q, ⟨hQ, hQX⟩, hpQ⟩
    exact ⟨Q, ⟨hQ, fun hs => hQX (hs.trans hYX)⟩, hpQ⟩
end YangMills.Construction.Torus.CubePartition
end
