-- RakeSieve uses a rake to implement a prime sieve.
import RakeMap
import PrimeSieve

structure RakeSieve where
  prop : Nat -> Prop
  rm: RakeMap prop
  p : NPrime               -- the current prime
  c : Nat                  -- the candidate for next prime
  hprop : ∀ n:Nat, prop n ↔ n ∈ R p
  hCinR : c ∈ R p
  hRmin : ∀ r ∈ R p, c ≤ r
  -- Future: maintain an explicit FIFO of primes < p^2 (see `ksBelowHorizon`).

namespace RakeSieve

open RakeMap

/-- Horizon after sieving primes ≤ `p`: every remaining value below this is prime
(`mem_R_lt_sq_prime`). -/
def horizon (rs : RakeSieve) : Nat := (rs.p : Nat) ^ 2

/-- Constant terms (`ks`) of the current rake that lie strictly below `p^2`.
These are exactly the primes that can be queued without further partitioning
(issue #2 / OldMain's `|q|` horizon filter). -/
def ksBelowHorizon (rs : RakeSieve) : List Nat :=
  rs.rm.rake.ks.filter (fun k => k < rs.horizon)

/-- Every constant term of the rake is in the residue `R p`. -/
theorem ks_mem_R (rs : RakeSieve) {k : Nat} (hk : k ∈ rs.rm.rake.ks) :
    k ∈ R rs.p := by
  have hterm : ∃ m, rs.rm.rake.term m = k := by
    refine (rs.rm.rake.term_iff k).mpr ?_
    exact ⟨k, hk, 0, by simp⟩
  have hprop : rs.prop k := (rs.rm.hbij k).mpr hterm
  exact (rs.hprop k).mp hprop

/-- Queued constants below the horizon are prime. -/
theorem ksBelowHorizon_prime (rs : RakeSieve) :
    ∀ k ∈ rs.ksBelowHorizon, Nat.Prime k := by
  intro k hk
  rw [ksBelowHorizon, List.mem_filter] at hk
  obtain ⟨hk_ks, hlt_dec⟩ := hk
  have hlt : k < rs.horizon := of_decide_eq_true (by simpa [horizon] using hlt_dec)
  have hinR := ks_mem_R rs hk_ks
  exact mem_R_lt_sq_prime rs.p.prop hinR hlt

def init : RakeSieve :=
  let rm : RakeMap (λn => n≥2 ∧ ¬2∣n) := rm_ge2 |>.rem 2 (by simp) (by
    use 3; use 1; simp[rm_ge2, Rake.ge2, Rake.term])
  let p := ⟨2, Nat.prime_two⟩
  { prop := rm.pred, rm := rm, p := p, c := 3,
    hprop := by
      have hrm : rm.pred = λn => n ≥ 2 ∧ ¬ 2∣n := by simp[RakeMap.pred]
      show ∀ n, rm.pred n ↔ n ∈ R p
      have hbij := rm.hbij
      unfold R; simp_all; intro n
      apply Iff.intro
      case mp =>
        intro hn
        apply And.intro
        · rw[← hbij] at hn; exact hn.left
        · intro q hq hq'
          simp[←hbij] at hn
          have hp2 : (p : Nat) = 2 := rfl
          have hq2 : 2 ≤ q := Nat.Prime.two_le hq'
          have : 2 = q := by omega
          rw[this] at hn
          omega
      case mpr =>
        simp; intro hn hn2; rw[←hbij]; simp_all
        have hp2: p.val = 2 := by rfl
        have hn2' := hn2
        set p' := p.val
        specialize hn2' p';  simp[hp2] at hn2'
        exact hn2' Nat.prime_two
    hCinR := by
      -- generic base-case fact: 3 ∈ R 2
      simpa [p] using three_mem_R_two
    hRmin := by
      -- generic base-case fact: 3 is least in R 2
      simpa [p] using three_le_of_mem_R_two }

set_option linter.hashCommand false
#guard (ksBelowHorizon init) = [3]

def next (rs₀ : RakeSieve) (hC₀: Nat.Prime rs₀.c) (hNS: nosk' rs₀.p rs₀.c): RakeSieve :=
  let h₀ := rs₀.prop
  have hh₀ : ∀n, h₀ n ↔ n ∈ R rs₀.p := rs₀.hprop
  have hCR₀ := rs₀.hCinR
  have hpgt:PrimeGt rs₀.p rs₀.c := by
    constructor
    · exact hC₀
    · exact r_gt_p (↑rs₀.p) rs₀.c hCR₀
  have hmin: ∀ q < rs₀.c, ¬PrimeGt (↑rs₀.p) q := by
    simp_all; intro q hq hq'; apply hNS at hq'; omega
  let c' : MinPrimeGt rs₀.p := { p:=rs₀.c, hpgt:=hpgt, hmin:=hmin}

  -- to call `rem`, we have to prove that it won't remove everything.
  -- so we must produce a proof that another prime besides c exists.
  have : ∃n m, ¬c'.p ∣ n ∧ rs₀.rm.term m = n := by
    have hC₀' : Nat.Prime rs₀.c := hC₀
    obtain ⟨q, hqgt, hq⟩ : ∃ q, rs₀.c.succ ≤ q ∧ Nat.Prime q := Nat.exists_infinite_primes rs₀.c.succ
    have hqR : q ∈ R rs₀.p := by
      unfold R
      constructor
      · exact Nat.Prime.two_le hq
      · intro q' hq'le hq' hdiv
        have : q' = q := Nat.prime_dvd_prime_iff_eq hq' hq |>.mp hdiv
        omega
    have hqprop : rs₀.prop q := (hh₀ q).mpr hqR
    obtain ⟨m, hm⟩ := (rs₀.rm.hbij q).mp hqprop
    refine ⟨q, m, ?_, hm⟩
    intro hdiv
    have : rs₀.c = q := Nat.prime_dvd_prime_iff_eq hC₀' hq |>.mp hdiv
    omega

  -- now we can use this fact to remove multiples of c
  let rs := rs₀.rm.rem c'.p (Nat.Prime.pos hC₀) this
  let c₁ := rs.rake.term 0
  have hc₁: ∃ i, rs.rake.term i = c₁ := by
    exact exists_apply_eq_apply (fun a => rs.rake.term a) 0
  let h₁ := rs.pred
  have hh₁ : ∀n, h₁ n ↔ h₀ n ∧ ¬(c'.p∣n) := by
    intro n
    rfl
  have hprop : ∀n, h₁ n ↔ n ∈ R c'.p := by
    intro n; exact r_next_prop (hh₀ n) (hh₁ n)
  { prop := rs.pred, rm := rs, p := ⟨c'.p, hC₀⟩, c := c₁,
    hprop := hprop
    hCinR := by
      show c₁ ∈ R c'.p
      · have : h₁ c₁ := by rw[← rs.hbij] at hc₁; exact hc₁
        specialize hprop c₁
        exact hprop.mp this
    hRmin := by
      dsimp[c₁,p,h₁] at *
      intro r hr
      have : ∃k, rs.rake.term k = r := by
        exact (rs.hbij r).mp ((hprop r).mpr hr)
      obtain ⟨k, hk⟩ := this
      rw[←hk]
      exact rs.min_term_zero k }

instance : PrimeSieveState RakeSieve where
  P x := x.p
  C x := x.c
  next := .next
  hNext := by
    intro s hC hNS s' hs'; simp_all; rw[←hs']
    unfold next at hs'; simp at hs'
    have hpc: s'.p = s.c := by simp_all
    apply And.intro
    · exact hpc
    · show s'.c > s.c
      have := s'.hCinR
      have := r_gt_p
      aesop

open PrimeSieveState

instance : PrimeSieveDriver RakeSieve where
  hCinR x := by dsimp[C]; dsimp[P]; exact x.hCinR
  hRmin x := by dsimp[C]; dsimp[P]; exact x.hRmin
