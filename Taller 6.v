(*
Taller 6 de logica computacional
Guido Salazar
07/11/2020
*)

Fixpoint suma (a:nat) (b:nat) :=
match a with
  | 0 => b
  | S n => S (suma n b)
end.

(*Parte 1*)

Theorem identidad : forall a:nat, suma a 0 = a.
Proof.
intro.
induction a.
simpl.
reflexivity.
simpl.
rewrite IHa.
reflexivity.
Qed.

Theorem asociativa : forall (a b c:nat), suma a (suma b c) = suma (suma a b) c.
Proof.
intros.
induction a.
simpl.
reflexivity.
simpl.
rewrite IHa.
reflexivity.
Qed.

Theorem colorario1 : forall (a b:nat), suma a (S b) = S (suma a b).
Proof.
intros.
induction a.
simpl.
reflexivity.
simpl.
rewrite IHa.
reflexivity.
Qed.

Theorem conmutativa : forall (a b:nat), suma a b = suma b a.
pose proof colorario1 as H.
Proof.
intros.
induction b.
simpl.
rewrite identidad.
reflexivity.
rewrite H. 
simpl.
rewrite IHb.
reflexivity.
Qed.

Theorem cancelativa : forall (a b c:nat), a = b -> suma a c = suma b c.
pose proof conmutativa as H.
pose proof colorario1 as H0.
intros.
rewrite H.
induction c.
simpl.
rewrite H.
simpl.
assumption.
simpl.
rewrite IHc.
rewrite <- H0.
rewrite H.
reflexivity.
Qed.

(*Parte 2*)

Fixpoint mult (a:nat) (b:nat) :=
  match a with
    | 0 => 0
    | S n => suma (mult n b) b
  end.

Theorem modulativa_mult : forall a:nat, mult a 1 = a.
Proof.
pose proof identidad as H.
pose proof colorario1 as H0.
intros.
induction a.
reflexivity.
simpl.
rewrite IHa.
rewrite <- H.
simpl.
rewrite <- H0.
reflexivity.
Qed.

Theorem producto_zero : forall a:nat, mult a  0 = 0.
Proof.
intros.
induction a.
simpl.
reflexivity.
simpl.
rewrite IHa.
simpl.
reflexivity.
Qed.

Theorem colorario2 : forall (a b:nat), mult a (S b) = suma a (mult a b).
pose proof asociativa as H0.
pose proof conmutativa as H1.
Proof.
intros.
rewrite H1.
induction a.
simpl.
reflexivity.
rewrite H1.
simpl.
rewrite H1.
simpl.
rewrite IHa.
rewrite H0 with a (mult a b) b.
rewrite H1 with (suma a (mult a b)) b.
rewrite H1 with (mult a b) a.
reflexivity.
Qed.

Theorem conmutativa_mult : forall (a b:nat), mult a b = mult b a.
pose proof colorario2 as H.
pose proof producto_zero as H0.
pose proof conmutativa as H1.
Proof.
intros.
induction b.
simpl.
rewrite H0.
reflexivity.
simpl.
rewrite H.
rewrite H1.
rewrite IHb.
reflexivity.
Qed.

Theorem distributiva_mult : forall (a b c:nat), mult a (suma b c) = suma (mult a b) (mult a c).
pose proof conmutativa as H.
pose proof producto_zero as H0.
pose proof asociativa as H1.
Proof.
intros.
induction a.
simpl.
reflexivity.
simpl.
rewrite H1.
rewrite H1 with (suma (mult a b) b) (mult a c) c.
rewrite IHa.
rewrite H with (suma (mult a b) (mult a c)) b.
rewrite H1 with b (mult a b) (mult a c).
rewrite H with (mult a b) b.
reflexivity.
Qed.

Theorem asociativa_mult : forall (a b c:nat), mult a (mult b c) = mult (mult a b) c.
pose proof conmutativa_mult as H.
pose proof distributiva_mult as H0.
Proof.
intros.
induction a.
simpl.
reflexivity.
simpl.
rewrite H with (suma (mult a b) b) c.
rewrite H0.
rewrite IHa.
rewrite H.
rewrite H with b c.
reflexivity.
Qed.







