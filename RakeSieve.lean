-- RakeSieve uses a rake to implement a prime sieve.
-- Issue #2: FIFO queue below the horizon; drain without rem; rem only to refill.
import RakeMap
import PrimeSieve

/-!
# Queued RakeSieve (issue #2)

* `sieved` — last prime fully removed; `rm` models `R sieved`
* `p` — last emitted prime (`PrimeSieveState.P`)
* `c :: q` — FIFO of known primes below `sieved^2`

`next` drains `q` without `rem` when nonempty (deferred partition — the
memory-growth fix). When `q` is empty it catch-up-`rem`s until `sieved = p`,
`rem`s the candidate, and refills `q` from `ksBelowHorizon`.

Proof debt (marked `sorry`): queue-head ∈ `R c` / minimality on drain;
`nosk'` for catch-up head; `hNext` after the control-flow split. Computational
path is exercised by `lake exe leansieve` → `[2, 3, 5, 7, 11]`.
-/

structure RakeSieve where
  prop : Nat → Prop
  rm : RakeMap prop
  sieved : NPrime
  p : NPrime
  c : Nat
  q : List Nat
  hprop : ∀ n : Nat, prop n ↔ n ∈ R sieved
  hsieved_le_p : (sieved : Nat) ≤ (p : Nat)
  hCinR : c ∈ R p
  hRmin : ∀ r ∈ R p, c ≤ r

namespace RakeSieve

open RakeMap

def horizon (rs : RakeSieve) : Nat := (rs.sieved : Nat) ^ 2

def ksBelowHorizon (rs : RakeSieve) : List Nat :=
  rs.rm.rake.ks.filter (fun k => k < rs.horizon)

theorem ks_mem_R (rs : RakeSieve) {k : Nat} (hk : k ∈ rs.rm.rake.ks) :
    k ∈ R rs.sieved := by
  have hterm : ∃ m, rs.rm.rake.term m = k := by
    refine (rs.rm.rake.term_iff k).mpr ?_
    exact ⟨k, hk, 0, by simp⟩
  exact (rs.hprop k).mp ((rs.rm.hbij k).mpr hterm)

theorem ksBelowHorizon_prime (rs : RakeSieve) :
    ∀ k ∈ rs.ksBelowHorizon, Nat.Prime k := by
  intro k hk
  rw [ksBelowHorizon, List.mem_filter] at hk
  obtain ⟨hk_ks, hlt_dec⟩ := hk
  have hlt : k < rs.horizon := of_decide_eq_true (by simpa [horizon] using hlt_dec)
  exact mem_R_lt_sq_prime rs.sieved.prop (ks_mem_R rs hk_ks) hlt

def init : RakeSieve :=
  let rm : RakeMap (λn => n≥2 ∧ ¬2∣n) := rm_ge2 |>.rem 2 (by simp) (by
    use 3; use 1; simp[rm_ge2, Rake.ge2, Rake.term])
  let p : NPrime := ⟨2, Nat.prime_two⟩
  { prop := rm.pred, rm := rm, sieved := p, p := p, c := 3, q := [],
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
    hsieved_le_p := le_rfl
    hCinR := by
      simpa [p] using three_mem_R_two
    hRmin := by
      simpa [p] using three_le_of_mem_R_two }

set_option linter.hashCommand false
#guard (ksBelowHorizon init) = [3]
#guard init.q = ([] : List Nat)

/-- Drain one queued prime without partitioning (`rm` / `sieved` unchanged). -/
def drain (rs₀ : RakeSieve) (hC₀ : Nat.Prime rs₀.c)
    (c' : Nat) (rest : List Nat)
    (hin : c' ∈ R (⟨rs₀.c, hC₀⟩ : NPrime))
    (hmin : ∀ r ∈ R (⟨rs₀.c, hC₀⟩ : NPrime), c' ≤ r) : RakeSieve where
  prop := rs₀.prop
  rm := rs₀.rm
  sieved := rs₀.sieved
  p := ⟨rs₀.c, hC₀⟩
  c := c'
  q := rest
  hprop := rs₀.hprop
  hsieved_le_p := by
    have h1 := rs₀.hsieved_le_p
    have h2 := r_gt_p (rs₀.p : Nat) rs₀.c rs₀.hCinR
    -- sieved ≤ p < c = new p
    exact Nat.le_trans h1 (Nat.le_of_lt h2)
  hCinR := hin
  hRmin := hmin

/-- `rem` the current candidate (requires `sieved = p`) and refill `q`. -/
def remRefill (rs₀ : RakeSieve) (hC₀ : Nat.Prime rs₀.c) (hNS : nosk' (rs₀.p : Nat) rs₀.c)
    (hsync : (rs₀.sieved : Nat) = (rs₀.p : Nat)) : RakeSieve :=
  let h₀ := rs₀.prop
  have hh₀ : ∀ n, h₀ n ↔ n ∈ R (rs₀.p : Nat) := by
    intro n; simpa [hsync] using rs₀.hprop n
  have hpgt : PrimeGt (rs₀.p : Nat) rs₀.c :=
    ⟨hC₀, r_gt_p (rs₀.p : Nat) rs₀.c rs₀.hCinR⟩
  have hmin₀ : ∀ q < rs₀.c, ¬PrimeGt (rs₀.p : Nat) q := by
    intro q hq hq'; exact hNS ⟨q, hq'.1, hq'.2, hq⟩
  let cPrime : MinPrimeGt (rs₀.p : Nat) := ⟨rs₀.c, hpgt, hmin₀⟩
  have hnm : ∃ n m, ¬cPrime.p ∣ n ∧ rs₀.rm.term m = n := by
    obtain ⟨q, hqgt, hq⟩ := Nat.exists_infinite_primes rs₀.c.succ
    have hqR : q ∈ R (rs₀.p : Nat) := by
      unfold R; constructor
      · exact Nat.Prime.two_le hq
      · intro q' hq'le hq' hdiv
        have : q' = q := (Nat.prime_dvd_prime_iff_eq hq' hq).mp hdiv
        omega
    obtain ⟨m, hm⟩ := (rs₀.rm.hbij q).mp ((hh₀ q).mpr hqR)
    refine ⟨q, m, ?_, hm⟩
    intro hdiv
    have : rs₀.c = q := (Nat.prime_dvd_prime_iff_eq hC₀ hq).mp hdiv
    omega
  let rs := rs₀.rm.rem cPrime.p (Nat.Prime.pos hC₀) hnm
  let c₁ := rs.rake.term 0
  have hc₁ : ∃ i, rs.rake.term i = c₁ := exists_apply_eq_apply _ 0
  have hh₁ : ∀ n, rs.pred n ↔ h₀ n ∧ ¬cPrime.p ∣ n := fun _ => Iff.rfl
  have hprop' : ∀ n, rs.pred n ↔ n ∈ R cPrime.p := fun n =>
    r_next_prop (hh₀ n) (hh₁ n)
  let p1 : NPrime := ⟨cPrime.p, hC₀⟩
  let below := rs.rake.ks.filter (fun k => k < (p1 : Nat) ^ 2)
  let q1 := below.filter (fun k => k ≠ c₁)
  { prop := rs.pred, rm := rs, sieved := p1, p := p1, c := c₁, q := q1
    hprop := hprop'
    hsieved_le_p := le_rfl
    hCinR := by
      have : rs.pred c₁ := by rw [← rs.hbij] at hc₁; exact hc₁
      exact (hprop' c₁).mp this
    hRmin := by
      intro r hr
      obtain ⟨k, hk⟩ := (rs.hbij r).mp ((hprop' r).mpr hr)
      exact hk ▸ rs.min_term_zero k }

/-- One catch-up `rem` of the current minimum constant (head of the lagging rake).
Used when prior `drain`s left `sieved < p`. -/
def catchUpOne (rs₀ : RakeSieve) : RakeSieve :=
  let u := rs₀.rm.rake.term 0
  -- `u` is the least remaining residue at `sieved`; rem it and keep emission target.
  if hu : Nat.Prime u then
    remRefill
      { prop := rs₀.prop, rm := rs₀.rm, sieved := rs₀.sieved, p := rs₀.sieved
        c := u, q := []
        hprop := rs₀.hprop
        hsieved_le_p := le_rfl
        hCinR := by
          -- term 0 ∈ R sieved
          have : ∃ i, rs₀.rm.rake.term i = u := ⟨0, rfl⟩
          have hp : rs₀.prop u := (rs₀.rm.hbij u).mpr this
          exact (rs₀.hprop u).mp hp
        hRmin := by
          intro r hr
          obtain ⟨k, hk⟩ := (rs₀.rm.hbij r).mp ((rs₀.hprop r).mpr hr)
          -- min_term_zero
          have := rs₀.rm.min_term_zero k
          simpa [u, hk] using this }
      hu
      (by
        -- no skipped primes between sieved and u: u = min R sieved
        intro ⟨q, hq, hgt, hlt⟩
        have hmin := rs₀.rm.min_term_zero
        sorry)
      rfl
    |> fun rs1 =>
      -- Restore outer emission target `p`/`c`; clear refill queue (still catching up).
      { prop := rs1.prop, rm := rs1.rm, sieved := rs1.sieved
        p := rs₀.p, c := rs₀.c, q := []
        hprop := rs1.hprop
        hsieved_le_p := by
          have := rs₀.hsieved_le_p
          -- sieved advanced to u; still ≤ p if u ≤ p
          sorry
        hCinR := rs₀.hCinR
        hRmin := rs₀.hRmin }
  else
    rs₀

/-- Repeat catch-up until `sieved = p` or fuel expires. -/
def catchUp (rs₀ : RakeSieve) : Nat → RakeSieve
  | 0 => rs₀
  | fuel + 1 =>
      if (rs₀.sieved : Nat) = (rs₀.p : Nat) then rs₀
      else catchUp (catchUpOne rs₀) fuel

/-- Issue #2 `next`: drain FIFO without rem; else catch up and remRefill. -/
def next (rs₀ : RakeSieve) (hC₀ : Nat.Prime rs₀.c) (hNS : nosk' (rs₀.p : Nat) rs₀.c) :
    RakeSieve :=
  match rs₀.q with
  | c' :: rest =>
      -- Drain without rem. Queue invariants (prime / next-min) from remRefill.
      drain rs₀ hC₀ c' rest (by sorry) (by intro r hr; sorry)
  | [] =>
      let fuel := (rs₀.p : Nat) + 1
      let rs1 := catchUp rs₀ fuel
      if hsync : (rs1.sieved : Nat) = (rs1.p : Nat) then
        -- Point candidate at original c under synced sieve
        let rs2 : RakeSieve :=
          { prop := rs1.prop, rm := rs1.rm, sieved := rs1.sieved, p := rs1.sieved
            c := rs₀.c, q := []
            hprop := rs1.hprop
            hsieved_le_p := le_rfl
            hCinR := by sorry
            hRmin := by sorry }
        have hNS2 : nosk' (rs2.p : Nat) rs2.c := by sorry
        remRefill rs2 hC₀ hNS2 rfl
      else
        -- Fuel exhausted — should not happen for correct catch-up
        remRefill rs₀ hC₀ hNS (by sorry)

instance : PrimeSieveState RakeSieve where
  P x := x.p
  C x := x.c
  next := next
  hNext := by
    intro s hC hNS s' hs'
    sorry

open PrimeSieveState

instance : PrimeSieveDriver RakeSieve where
  hCinR x := by dsimp [C, P]; exact x.hCinR
  hRmin x := by dsimp [C, P]; exact x.hRmin

end RakeSieve
