import PrimeGen

set_option autoImplicit false

abbrev nosk' P C := (¬∃ q:Nat, Nat.Prime q ∧ P < q ∧ q < C) -- no skipped prime
class PrimeSieveState (α : Type) where
  P     (s:α) : NPrime
  C     (s:α) : Nat
  next  (s:α) (hC: Nat.Prime (C s)) (hN: nosk' (P s) (C s)): α
  hNext (s:α) (hC: Nat.Prime (C s)) (hN: nosk' (P s) (C s)) {s':α}
    : (s'=(next s hC hN) → P s' = C s ∧ C s' > C s)
open PrimeSieveState

-- R: the "residue", or "remaining" nats coprime to all primes < p.
-- In a sieve, these are the numbers that haven't yet been "sifted out."
def R(P:Nat) : Set Nat := { n | n≥2 ∧ ∀q≤P, Nat.Prime q → ¬q∣n }

/-- Base case for any prime sieve: after removing multiples of 2, 3 remains in the residue. -/
theorem three_mem_R_two : (3 : Nat) ∈ R 2 := by
  unfold R
  refine ⟨by decide, ?_⟩
  intro q hqle hq'
  have : q = 2 := by
    have := Nat.Prime.two_le hq'
    omega
  subst this
  decide

/-- Base case for any prime sieve: 3 is a lower bound of `R 2` (hence its minimum with `three_mem_R_two`). -/
theorem three_le_of_mem_R_two : ∀ r ∈ R 2, (3 : Nat) ≤ r := by
  intro r ⟨hr, hrr⟩
  by_contra h
  simp at h
  have r2 : r = 2 := by omega
  have := hrr 2 (by omega) Nat.prime_two
  rw [r2] at this
  exact this (dvd_refl _)

/-- everything in R is greater than P. we use this to show C > P later. -/
lemma r_gt_p (p:Nat) : (∀r∈R p, r > p) := by
  -- argument: R and S together say ∀ p:prime ≤ P, ¬ p∣r
  intro r hrr;  unfold R at hrr
  -- if r is ≤ P, there is a contradiction.
  by_contra h; simp at h
  -- r (like all natural numbers) has a minimum prime factor f
  have : r ≠ 1 := by aesop -- R say r ≥ 2
  obtain ⟨f, hf', hfr⟩ : ∃ f, Nat.Prime f ∧ f ∣ r :=
      Nat.exists_prime_and_dvd ‹r ≠ 1›
  -- from a chain of relationships we can conclude that f≤P...
  have : 0 < r := by exact Nat.zero_lt_of_lt hrr.left
  have : f ≤ r := Nat.le_of_dvd this hfr
  have : f ≤ p := by omega
  aesop


/-- After removing multiples of all primes ≤ `P`, every remaining
`n ∈ R P` with `n < P^2` is prime. This is the fact that lets a sieve
queue primes below the horizon `P^2` without further partitioning. -/
theorem mem_R_lt_sq_prime {P n : Nat} (_hP : Nat.Prime P)
    (hn : n ∈ R P) (hlt : n < P ^ 2) : Nat.Prime n := by
  by_contra hnp
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn.left
  have hne1 : n ≠ 1 := ne_of_gt (Nat.lt_of_succ_le hn.left)
  have hsq : Nat.minFac n ^ 2 ≤ n := Nat.minFac_sq_le_self hnpos hnp
  have hmf_lt : Nat.minFac n < P := by
    have : Nat.minFac n ^ 2 < P ^ 2 := lt_of_le_of_lt hsq hlt
    exact (Nat.pow_lt_pow_iff_left (by decide : (2 : Nat) ≠ 0)).mp this
  have hmf_le : Nat.minFac n ≤ P := Nat.le_of_lt hmf_lt
  exact hn.right (Nat.minFac n) hmf_le (Nat.minFac_prime hne1) (Nat.minFac_dvd n)

/- if p₁ is the next consecutive prime after p₀ then
  R p₁ = { n:(R p₀) | ¬ p₁∣n }
  This corresponds to the idea that each time you identify
  the next prime in a sieve, you sift out all its multiples. -/
theorem r_next (p₀: Nat) (m: MinPrimeGt p₀) {n:Nat}
  : (n ∈ R p₀ ∧ ¬↑m.p ∣ n) ↔ (n ∈ R m.p) := by
    let ⟨h₁,hinc⟩ := m.hpgt; let hmin := m.hmin; set p₁ := m.p
    unfold R; simp; apply Iff.intro
    all_goals intro hn; apply And.intro; simp_all
    · show ∀ q ≤ p₁, Nat.Prime q → ¬q ∣ n
      intro q hq hq2
      by_cases hq₀: q≤p₀
      case pos => simp_all
      case neg =>
        by_contra hqn
        simp at hq₀
        have : q ≠ 1 := by aesop
        obtain ⟨f, hf', hfq⟩ := Nat.exists_prime_and_dvd ‹q ≠ 1›
        have hmin := m.hmin
        absurd hmin; simp; use f; split_ands
        · show f < m.p
          have : 0 < q := by omega
          have : f ≤ q := by exact Nat.le_of_dvd this hfq
          have : q ≠ p₁ := by aesop
          omega
        · exact hf'
        · show p₀ < f
          simp_all
          by_contra h
          have : f ≤ p₀ := by omega
          have : 2 ≤ f := by exact Nat.Prime.two_le hf'
          simp_all
          have : ¬ f ∣ n := by aesop
          have : f ∣ n := by exact Nat.dvd_trans hfq hqn
          contradiction
    · show ∀ q ≤ p₀, Nat.Prime q → ¬q ∣ n
      intro q hq hq2
      have : q ≤ p₁ := by omega
      exact (hn.right q this) hq2
    · show ¬p₁ ∣ n
      simp_all

/- A prime sieve implementation can model `R p` by providing
a bijection between `R p` and its internal data structures.

For RakeSieve, this is exposed to the type system by attaching
a predicate to the internal data structure.

Whatever the sieve does to "sift out" multiples of the next
prime `p₁` is equivalent to the expression  `∧ ¬(p₁∣n)`.

The following theorem allows us to construct a predicate for
membership in `R pₙ` by induction using predicates of this
form at each step. -/
theorem r_next_prop {p₀ n:Nat} {h₀ h₁: Nat → Prop} {m : MinPrimeGt p₀}
  (hh₀: h₀ n ↔ n ∈ R p₀) (hh₁: h₁ n ↔ h₀ n ∧ ¬(m.p ∣ n))
  : (h₁ n ↔ n ∈ R m.p) := by
  simp[hh₁, hh₀]
  exact r_next p₀ m

/--
PrimeSieveDriver provides the generic proof that a
A PrimeSieve is a PrimeGen that uses a SieveState to generate primes.
In practice, this means that it somehow models the set of natural
numbers greater than 1 that are coprime to a list of known primes,
and then repeatedly:
  - obtains the minimum of this set as the next prime
  - eliminates multiples of the new prime. -/
class PrimeSieveDriver (α : Type) [PrimeSieveState α] where
  hCinR  (g:α) : C g ∈ R (P g)            -- C is an element of R
  hRmin  (g:α) : ∀ n ∈ R (P g), C g ≤ n   -- C is min of R
open PrimeSieveDriver

theorem c_gt_p (α : Type) [PrimeSieveState α] [PrimeSieveDriver α] (g:α) : C g > P g := by
  have := hCinR g
  exact r_gt_p (↑(P g)) (C g) this

theorem no_skipped_prime (α : Type) [PrimeSieveState α] [PrimeSieveDriver α] (g:α)
  : ¬ ∃ q:Nat, Nat.Prime q ∧ P g < q ∧ q < C g := by
    intro ⟨q, ⟨hQ', hPltQ, hQltC⟩⟩ -- `intro q` on a ¬∃ goal requires we find a contradiction.
    -- hRmin tells us that that C is the min of the set R.
    have hRmin: ∀n ∈ R (P g), C g ≤ n := hRmin <| g

    -- demonstrating `q ∈ R` would show the contradiction since `q<P` and `P` is min of `R`
    suffices hQinR: q ∈ R (P g) from by apply hRmin at hQinR; omega

    -- so now we just show hQinR. q∈R means q≥2 ∧ (¬∃p∈ S g, p∣q)
    -- both of these facts follow immediately from the fact that q is prime,
    -- provided we can *also* show that q itself is not an element of s.
    unfold R; constructor
    · show q ≥ 2 ; exact Nat.Prime.two_le hQ'
    · show ∀ p ≤ ↑(P g), Nat.Prime p → ¬(p ∣ q)
      intro p hp hp' -- assume p exists and p|q. show a contradiction.
      -- since that p|q and both are prime, it follows that p=q.
      have := Nat.prime_dvd_prime_iff_eq hp' hQ'
      omega

lemma no_prime_factors_im_no_factors {c:Nat} -- c is a candidate prime
  (h2lc: 2 ≤ c)                              -- c is at least 2
  (hnpf: ∀ p < c, Nat.Prime p → ¬(p∣c))      -- c has no prime factors
  : Nat.Prime c := by
    have : ∀ m < c, m ∣ c → m=1 := by  -- c has no divisors but 1 and c
      intro m hmc hmdc  -- give names to the above assumptions
      by_contra         -- assume ¬(m=1) and show contradiction
      obtain ⟨p, hp', hpm⟩ : ∃ p, Nat.Prime p ∧ p ∣ m :=
        Nat.exists_prime_and_dvd ‹m ≠ 1›
      have : p∣c := Nat.dvd_trans hpm hmdc
      have : ¬(p∣c) := by
        have : 0 < c := by omega
        have : 0 < m := Nat.pos_of_dvd_of_pos hmdc this
        have : p ≤ m := Nat.le_of_dvd this hpm
        have : p < c := by omega
        exact hnpf p this hp'
      contradiction
    exact Nat.prime_def_lt.mpr ⟨‹2 ≤ c› , this⟩


theorem c_prime (α: Type) [PrimeSieveState α] [PrimeSieveDriver α] (g:α)
  : Nat.Prime (C g) := by
    set c := C g
    have hfac: ∀ q < C g, Nat.Prime q → ¬ q ∣ c := by
      intro q₀ hqc hPq
      set q : NPrime := ⟨q₀,hPq⟩
      by_cases hq: q ≤ (P g)
      case pos => -- ¬p∣C because C∈R and that's how R is defined
        have hCinR := hCinR g
        unfold R at hCinR; simp at hCinR
        aesop
      case neg => -- we have P < q and q < C but this can't happen
        have : (P g) < q := by exact Nat.gt_of_not_le hq
        have := no_skipped_prime α g
        absurd this; use q; aesop
    have h2c: 2 ≤ C g := by
      set p := P g
      have : p.val ≥ 2 := by exact Nat.Prime.two_le p.prop
      have : c > p.val := c_gt_p α g
      omega
    exact no_prime_factors_im_no_factors h2c hfac


-- demonstrate that a sieve generates the next consecutive prime at each step.
-- "we have a new, bigger prime, and there is no prime between them".
theorem hs_suffice (α : Type) [PrimeSieveState α] [PrimeSieveDriver α] (g:α)
  :  (Nat.Prime (C g)) ∧ (C g > P g) ∧ (¬∃ q, Nat.Prime q ∧ P g < q ∧  q < C g) := by
    split_ands
    · exact c_prime α g
    · exact c_gt_p α g
    · exact no_skipped_prime α g

def nextState {α : Type} [PrimeSieveState α] [PrimeSieveDriver α] (s: α) : α :=
  let c' := c_prime α s
  let ns := no_skipped_prime α s
  PrimeSieveState.next s c' ns

variable (α : Type) [PrimeSieveState α] [PrimeSieveDriver α]
structure PrimeSieve  where
  state  : α

def PrimeSieve.next (x:PrimeSieve α) : PrimeSieve α :=
  { state := nextState x.state }

/-- Lift a driven sieve state machine to a `PrimeGen`. -/
instance : PrimeGen (PrimeSieve α) where
  P s := PrimeSieveState.P s.state
  next := PrimeSieve.next (α := α)
  hP' s := by
    intro ⟨q, hq, hgt, hlt⟩
    have hc' := c_prime α s.state
    have hns := no_skipped_prime α s.state
    have hEq : PrimeSieveState.P (nextState (α := α) s.state) = C s.state :=
      (PrimeSieveState.hNext (α := α) s.state hc' hns rfl).left
    have hlt' : q < C s.state := by
      -- hlt : q < PrimeGen.P (next s) = PrimeSieveState.P (nextState s.state)
      change q < (PrimeSieveState.P (nextState (α := α) s.state) : Nat) at hlt
      simpa [hEq] using hlt
    have hgt' : (PrimeSieveState.P s.state : Nat) < q := hgt
    exact hns ⟨q, hq, hgt', hlt'⟩
  hP_lt s := by
    have hc' := c_prime α s.state
    have hns := no_skipped_prime α s.state
    have hEq : PrimeSieveState.P (nextState (α := α) s.state) = C s.state :=
      (PrimeSieveState.hNext (α := α) s.state hc' hns rfl).left
    have hgt := c_gt_p α s.state
    -- goal: PrimeGen.P s < PrimeGen.P (next s)
    change (PrimeSieveState.P s.state : Nat) <
      PrimeSieveState.P (nextState (α := α) s.state)
    simpa [hEq] using hgt

/-- Start a `PrimeSieve` from a concrete sieve state. -/
def PrimeSieve.start {β : Type} [PrimeSieveState β] [PrimeSieveDriver β] (s : β) :
    PrimeSieve β :=
  { state := s }
