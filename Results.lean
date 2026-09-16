import PrimeGen
import PrimeSieve
import RakeSieve

theorem results_three_mem_R_two : (3 : Nat) ∈ R 2 :=
  three_mem_R_two

theorem results_three_le_of_mem_R_two : ∀ r ∈ R 2, (3 : Nat) ≤ r :=
  three_le_of_mem_R_two

theorem results_exists_prime_gt_of_primeGen {α : Type} [PrimeGen α] (g₀ : α) (n : Nat) :
    ∃ p, Nat.Prime p ∧ n < p :=
  exists_prime_gt_of_primeGen g₀ n

theorem results_exists_prime_gt_of_simpleGen (n : Nat) :
    ∃ p, Nat.Prime p ∧ n < p :=
  exists_prime_gt_of_primeGen SimpleGen.start n

theorem results_exists_prime_gt_of_rakeSieve (n : Nat) :
    ∃ p, Nat.Prime p ∧ n < p :=
  exists_prime_gt_of_primeGen ({ state := RakeSieve.init } : PrimeSieve RakeSieve) n
