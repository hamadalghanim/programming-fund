
Fixpoint eqb(n m: nat): bool :=
  match n with 
    | O => match m with
             | O => true
             | S m' => false
             end
    | S n' => match m with
                | O => false
                | S m' => eqb n' m'
                end
  end.