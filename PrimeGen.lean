-- PrimeGen: a specification for algorithms that generate prime numbers.
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith.Frontend

def NPrime : Type := { n: Nat // Nat.Prime n } deriving Repr, Ord, LT, LE

@[simp] theorem NPrime.eq_iff (a b : NPrime) : a = b ↔ a.val = b.val := Subtype.ext_iff
instance : ToString NPrime where toString s := s!"{s.val}"
instance : Dvd NPrime where dvd a b := a.val ∣ b.val
instance : Coe NPrime Nat where coe n := n.val
-- interestingly, the following seems to shadow normal Nat ∈ Set Nat operations.
-- instance : Membership NPrime (Set Nat) where mem n s := n.val ∈ s

/-- A prime generator yields a strictly increasing sequence of consecutive primes.
`init` is intentionally *not* part of the class: only needed for zero-arg `primes`;
prefer `primes g₀ n` with an explicit start state (e.g. `SimpleGen.start`). -/
class PrimeGen (α : Type) where
  P : α → NPrime
  next : α → α
  /-- No prime is skipped between `P g` and `P (next g)`. -/
  hP' (g:α) : (¬∃ q, Nat.Prime q ∧ P g < q ∧  q < P (next g))
  /-- The generated prime strictly increases at each step.
  Needed for infinitude: `hP'` alone allows a constant generator. -/
  hP_lt (g:α) : (P g : Nat) < P (next g)
open PrimeGen

abbrev PrimeGt (n p:Nat) := Nat.Prime p ∧ n < p

structure MinPrimeGt (n:Nat) where
  p : Nat
  hpgt : PrimeGt n p
  hmin : ∀q:Nat, q < p → (¬ PrimeGt n q)
theorem MinPrimeGt.p' (m:MinPrimeGt n) : Nat.Prime m.p := m.hpgt.left

section simple_gen

  theorem ex_prime_gt (c:Nat) : ∃ p, PrimeGt c p := by
    let d := c + 1 -- because the line below has ≤ and we need <
    let ⟨p, hcp, hprime⟩ : ∃ (p : ℕ), d ≤ p ∧ Nat.Prime p :=
      Nat.exists_infinite_primes d
    use p; constructor
    · exact hprime
    · omega

  def min_prime_gt (n: Nat) : MinPrimeGt n :=
    let e := ex_prime_gt n
    { p:=Nat.find e,
      hpgt:=Nat.find_spec e,
      hmin:= by exact fun {q} a => Nat.find_min e a}

  structure SimpleGen where
    p : NPrime
    c : MinPrimeGt p.val

  def SimpleGen.next (g:SimpleGen) : SimpleGen :=
    { p:=⟨g.c.p, g.c.hpgt.left⟩, c:=min_prime_gt g.c.p }

  /-- Canonical start state for `SimpleGen` (replaces class-level `init`). -/
  def SimpleGen.start : SimpleGen :=
    { p := ⟨2, Nat.prime_two⟩, c := min_prime_gt 2 }

  instance : PrimeGen SimpleGen where
    P g := g.p
    next := .next
    hP' g := by  -- goal: no prime q between g.p and (g.next.p = g.c.p)
      -- why? that would imply prime_gt (g.p) q, but hmin contradicts this
      intro h
      rcases h with ⟨q, hq, hgt, hlt⟩
      exact (g.c.hmin q hlt) ⟨hq, hgt⟩
    hP_lt g := by
      -- g.next.p = g.c.p and g.c witnesses PrimeGt g.p
      simpa [SimpleGen.next] using g.c.hpgt.right

  open PrimeGen

end simple_gen

/- function power. apply f recursively n times to x₀ and collect the results.
  (!! lean has `f^[n] x` but this doesn't collect intermediate results. maybe
  another version exists?) -/
def fpow (f : α → α) (n:Nat) (x₀ : α) : List α :=
  let rec aux (n:Nat) (x:α) (acc:List α) :=
    if n = 0 then x::acc
    else aux (n-1) (f x) (x::acc)
  aux (n-1) x₀ [] |>.reverse

set_option linter.hashCommand false

#guard fpow (λn => n+1) 10 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The first `n` primes from generator state `g₀` (inclusive). -/
def primes {α : Type} [pg: PrimeGen α] (g₀ : α) (n : Nat) : List NPrime :=
  fpow (fun g => pg.next g) n g₀ |>.map fun g => pg.P g

#guard (primes SimpleGen.start 10 |>.map (·.val)) = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

/-- After `k` steps, `P` has increased by at least `k`. -/
theorem PrimeGen.P_iterate_add_le {α : Type} [PrimeGen α] (g : α) (k : Nat) :
    (P g : Nat) + k ≤ P (next^[k] g) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hlt := hP_lt (next^[k] g)
    -- ih: P g + k ≤ P (next^[k] g); hlt: P (next^[k] g) < P (next (next^[k] g))
    omega

/-- Infinitude of primes from any `PrimeGen` instance (uses `hP_lt` + inhabited start).
`hP'` alone is not enough: a constant generator satisfies `hP'`. -/
theorem exists_prime_gt_of_primeGen {α : Type} [PrimeGen α] (g₀ : α) (n : Nat) :
    ∃ p, Nat.Prime p ∧ n < p := by
  let k := n + 1
  have hle : (P g₀ : Nat) + k ≤ P (next^[k] g₀) := PrimeGen.P_iterate_add_le g₀ k
  have h2 : (P g₀ : Nat) ≥ 2 := Nat.Prime.two_le (P g₀).prop
  refine ⟨P (next^[k] g₀), (P (next^[k] g₀)).prop, ?_⟩
  omega
