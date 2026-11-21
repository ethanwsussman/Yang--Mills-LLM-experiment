import YangMills.Construction.ChessboardTori.ChessboardEstimateOnMirrorGrids
import YangMills.Construction.ChessboardTori.ChessboardSeminormsOnATorus
import YangMills.Construction.ChessboardTori.FromTheInfiniteLatticeToTheTorus
import YangMills.Construction.MirrorGridsOfEverySide.ChessboardEstimateOnGridsOfEverySide
import YangMills.Construction.MirrorGridsOfEverySide.FactsOfAMirrorGrid
import YangMills.Construction.ReflectionPositivity.CovarianceOfTheCurvatureDensity
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
namespace ChessboardAllSides
variable {D : GridSetup} {g : ChessboardTori.ReflectionGrid D}
theorem image_bijOn (hG : TorusGroupActsOnCells g) (hK : WallPreservingSymmetries g)
    {C : Set D.Torus} (hC : C ∈ g.torusCellSet) :
    BijOn (fun r' : D.Torus → D.Torus => r' '' C) g.inducedTorusMaps g.torusCellSet := by
  have hmaps : MapsTo (fun r' : D.Torus → D.Torus => r' '' C) g.inducedTorusMaps
      g.torusCellSet := by
    intro r hr
    obtain ⟨s, hs, hf⟩ := hK.2 r hr
    have := (hK.1 s hf).1.mapsTo hC
    simpa only [hs] using this
  have htrans := hG.2.2.2.2.2.1
  refine ⟨hmaps, fun r hr s hs h => ?_, fun C' hC' => ?_⟩
  · exact (htrans C hC (r '' C) (hmaps hr)).unique ⟨hr, rfl⟩ ⟨hs, h.symm⟩
  · obtain ⟨r, ⟨hr, hrC⟩, -⟩ := htrans C hC C' hC'
    exact ⟨r, hr, hrC⟩
theorem add_mem {C : Set D.Torus} {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : F ∈ g.torusCellObservables C) (hF' : F' ∈ g.torusCellObservables C) :
    F + F' ∈ g.torusCellObservables C := by
  obtain ⟨f, hm, ⟨c, hc⟩, hr⟩ := hF
  obtain ⟨f', hm', ⟨c', hc'⟩, hr'⟩ := hF'
  refine ⟨fun u => f u + f' u, hm.add hm', ⟨c + c', fun u => ?_⟩, fun U => ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (hc u) (hc' u))
  · rw [Pi.add_apply, hr U, hr' U]
theorem smul_mem {C : Set D.Torus} {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : F ∈ g.torusCellObservables C) (z : ℂ) : z • F ∈ g.torusCellObservables C := by
  obtain ⟨f, hm, ⟨c, hc⟩, hr⟩ := hF
  refine ⟨fun u => z * f u, hm.const_mul z, ⟨‖z‖ * c, fun u => ?_⟩, fun U => ?_⟩
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hc u) (norm_nonneg _)
  · rw [Pi.smul_apply, hr U, smul_eq_mul]
theorem conj_mem {C : Set D.Torus} {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : F ∈ g.torusCellObservables C) : conjFun F ∈ g.torusCellObservables C := by
  obtain ⟨f, hm, ⟨c, hc⟩, hr⟩ := hF
  refine ⟨fun u => starRingEnd ℂ (f u), Complex.continuous_conj.measurable.comp hm,
    ⟨c, fun u => by simpa using hc u⟩, fun U => ?_⟩
  simp only [conjFun, hr U]
theorem one_mem (C : Set D.Torus) : (fun _ => (1 : ℂ)) ∈ g.torusCellObservables C :=
  ⟨fun _ => 1, measurable_const, ⟨1, fun _ => by simp⟩, fun _ => rfl⟩
theorem exists_bondImage (s : D.TorusSymmetry) (hs : Function.Bijective s.toFun)
    (b : D.PeriodicLink) : ∃ b' : D.PeriodicLink,
      PeriodicLattice.TorusLatticeSymmetry.IsBondImage s b b' := by
  let E : SourcesAndGluing.GluingSetup := ⟨D.toStandingParameters, D.β, D.beta_pos, 0⟩
  let R : SourcesAndGluing.GluingSetup.TorusLatticeIsometry E :=
    ⟨s.toFun, ⟨hs, s.dist_eq⟩, s.image_eq⟩
  exact ⟨R.linkMap b, Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)⟩
theorem imageLink_eq_bondMap (s : D.TorusSymmetry) (hs : Function.Bijective s.toFun)
    (b : D.PeriodicLink) :
    D.imageLink s.toFun b = PeriodicLattice.TorusLatticeSymmetry.bondMap s b := by
  have hex := exists_bondImage s hs b
  have e : PeriodicLattice.TorusLatticeSymmetry.bondMap s b = hex.choose := dif_pos hex
  have hsp := hex.choose_spec
  rw [e]
  have h₁ : hex.choose.source = s.pointMap b.source := congrArg Prod.fst hsp
  have h₂ : hex.choose.target = s.pointMap b.target := congrArg Prod.snd hsp
  have hp := Classical.epsilon_spec (p := fun b' : D.PeriodicLink =>
    (b'.source : D.Torus) = s.toFun b.source ∧ (b'.target : D.Torus) = s.toFun b.target)
    ⟨hex.choose, congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
  exact PeriodicLattice.Bond.ext (Subtype.ext (hp.1.trans (congrArg Subtype.val h₁).symm))
    (Subtype.ext (hp.2.trans (congrArg Subtype.val h₂).symm))
theorem precompose_eq_pullbackObservable (s : D.TorusSymmetry)
    (hs : Function.Bijective s.toFun) (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    GridSetup.TorusSymmetry.precompose s F = D.pullbackObservable s.toFun F := by
  funext U
  have hU : D.pullbackField s.toFun U = GridSetup.TorusSymmetry.pullback s U := by
    funext b
    exact congrArg U (imageLink_eq_bondMap s hs b)
  simp only [GridSetup.TorusSymmetry.precompose, ChessboardTori.ChessboardSetup.pullbackObservable,
    Function.comp, hU]
theorem hasAdmissibleSide_of_coarser {g' : ChessboardTori.ReflectionGrid D}
    (hg : g.HasAdmissibleSide) {k₀ : ℕ}
    (hk : g'.cellSide = (D.L : ℝ) ^ k₀ * g.cellSide) : g'.HasAdmissibleSide := by
  have hL : (1 : ℝ) < D.L := D.one_lt_factor
  have hpos : 0 < g.cellSide := zpow_pos (by linarith) _
  have hle : g.cellSide ≤ g'.cellSide := by
    rw [hk]
    exact le_mul_of_one_le_left hpos.le (one_le_pow₀ hL.le)
  refine ⟨⟨g'.q, rfl⟩, hg.2.trans ?_⟩
  exact div_le_div_of_nonneg_right hle (by positivity)
end ChessboardAllSides
open ChessboardAllSides in
theorem chessboardEstimate_allSides_holds
    (hM : ChessboardTori.ChessboardBoundOnReflectionGrids.Statement)
    (hS : ChessboardTori.TorusChessboardSeminorms.Statement)
    (hB : ChessboardTori.TorusReduction.Statement)
    (hF : ReflectionGridProperties)
    (hI : ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance) :
    chessboardEstimate_allSides := by
  intro D g hg hside
  obtain ⟨-, -, -, -, -, -, hT, -, -⟩ := hF D g hg
  obtain ⟨-, hG, -, -, hR, -, hK⟩ := hT hside
  have hval : ∀ {C : Set D.Torus}, C ∈ g.torusCellSet →
      ∀ F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ,
      g.cellChessboardSeminorm C F = g.torusChessboardNorm F := fun hC F =>
    g.chessboardNorm_eq_torusChessboardNorm (image_bijOn hG hK hC) F
  obtain ⟨m1, m2, m3⟩ := hM D g hside
  obtain ⟨-, -, -, -, -, b6, -⟩ := hB D g hside
  refine ⟨⟨fun F hF => ?_, fun C hC F hF => ?_⟩, fun C hC => ?_,
    fun g' hcoarse hside' Q hQ F hFam => ?_⟩
  · exact (m1 F hF).trans_eq (finprod_congr fun C => (hval C.2 _).symm)
  · rw [g.cellProduct_eq_torusProduct (image_bijOn hG hK hC) F]
    obtain ⟨p1, p2, -, -⟩ := b6 C hC F hF
    exact ⟨p1, p2⟩
  · obtain ⟨-, -, s3, s4, -⟩ := hS D g hside C hC
    refine ⟨fun F hF => ⟨fun F' hF' => ⟨add_mem hF hF', ?_⟩, fun z => ⟨smul_mem hF z, ?_⟩, ?_,
      conj_mem hF, ?_, fun C' hC' => ⟨(hR C hC C' hC' C' hC' F hF).1, ?_⟩, fun s hs => ?_⟩,
      one_mem C, ?_⟩
    · simp only [hval hC]
      exact (s3 F hF F' hF' 0).2.1
    · simp only [hval hC]
      exact (s3 F hF F hF z).1
    · simp only [hval hC]
      exact (s3 F hF F hF 0).2.2.2.1
    · simp only [hval hC]
      exact (s3 F hF F hF 0).2.2.1
    · rw [hval hC', hval hC]
      exact (b6 C hC F hF).2.2.1 C' hC'
    · have hbs : Function.Bijective s.toFun := ((hI (D.mirrors 0)).2 s).2.1
      obtain ⟨hrC, hrF, -, hv⟩ := (m2 C hC F hF 0).2.2.2.2 s.toFun
        ⟨fun u v => s.dist_eq u v, s.image_eq, hs⟩
      rw [precompose_eq_pullbackObservable s hbs F]
      refine ⟨hrC, hrF, ?_⟩
      rw [hval hrC, hval hC]
      exact hv
    · rw [hval hC]
      exact s4
  · obtain ⟨⟨k₀, hk⟩, hfp⟩ := hcoarse
    have hg' : g'.HasAdmissibleSide := hasAdmissibleSide_of_coarser hg hk
    obtain ⟨-, -, -, -, -, -, hT', -, -⟩ := hF D g' hg'
    obtain ⟨-, hG', -, -, -, -, hK'⟩ := hT' hside'
    have hwalls : ∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ),
        g'.wall μ k = g.wall μ' k' := fun μ k => by
      obtain ⟨p, hp⟩ := hfp ⟨(μ, k), rfl⟩
      exact ⟨p.1, p.2, hp.symm⟩
    obtain ⟨hm, hle⟩ := m3 k₀ g' hk hside' hwalls Q hQ F hFam
    refine ⟨hm, ?_⟩
    exact (g'.chessboardNorm_eq_torusChessboardNorm (image_bijOn hG' hK' hQ) _).trans_le
      (hle.trans_eq (finprod_congr fun C => (hval C.2.1 _).symm))
end YangMills.Construction.MirrorGridsAllSides
end
