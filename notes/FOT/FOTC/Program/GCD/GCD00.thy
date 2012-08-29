(* In Isabelle gcd 0 0 = 0 *)

theory GCD00
imports GCD Nat
begin

theorem gcd00 : "gcd (0 :: nat) 0 = 0"
apply auto
done
