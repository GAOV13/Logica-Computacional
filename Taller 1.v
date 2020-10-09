(*Taller 1 Lógica Computacional*)
(*Autor: Guido Salazar*)

(*Variables auxiliares*)

Definition cons1 := 5.

(*Punto 1*)

(*Funcion que me devuelve el cuadrado de un numero*)
Definition cuadrado (n : nat) := n*n.

(*Funcion que me devuelve el cubo de un numero*)
Definition cubo (n : nat) := n*n*n.

Compute cubo 5.
Compute cuadrado 5.

(*Punto 2*)

(*Funcion que me devuelve el cuadrado de de un numero sumado a una constante*)
Definition punto2 (n: nat) := cuadrado (n + cons1).

Compute punto2 0.

(*Punto 3*)

(*Funcion que me devuelve la suma de los cubos de dos numeros*)
Definition punto3 (n1 n2: nat) := (cubo n1) + (cubo n2).

Compute punto3 2 3.

(*Punto 4*)

(*Funcion que me devuelve la suma y el producto de los cuatro numeros*)
Definition punto4 (n1 n2 n3 n4: nat) := (n1+n2+n3+n4, n1*n2*n3*n4).

Compute punto4 1 2 3 4.

(*Punto 5*)

Compute Nat.leb 8 7.
Compute Nat.leb 6 7.
Compute Nat.leb 7 7.
(*La función Nat.double recibe un numero Nat y me devuelve el dobre de ese numero*)
(*La función Nat.div2 recibe un numero Nat y devuelve la mitad del numero con la forma floor(n/2)*)
(*La función Nat.leb recibe dos numero y me devuelve un balor booleano. 0 en caso de que el primer numero sea mayor que el segundo y 1 en caso contario.
  Es decir, la función leb representa x1 <= x2.*)

Print Nat.double.
Print Nat.div2.
Print Nat.leb.

(*Punto 6*)

(*Funcion que recibe un numero y me dice si el numero es par o impar*)
Definition esPar (n : nat) : bool := 
  Nat.leb (Nat.div2 (n + 1)) (Nat.div2 n).

Compute esPar 8.
Compute esPar 9.

(*Punto 7*)

Definition iter2p (f : (nat*nat) -> (nat*nat)) (p : nat*nat) := f (f p).

Compute (iter2p (fun p => (snd p, fst p)) (1, 2),
iter2p (fun p => (fst p + 1, snd p + fst p + 1)) (0,0)).


(*Punto 8*)

Definition componerFunc (f : nat -> nat) (g : (nat -> nat) -> (nat -> nat)) : nat -> nat :=
 g f.

Compute componerFunc (fun a => a + 2) (fun f => f).

Print componerFunc.

(*Punto 9*)

(*Funcion que recibe una parejar de numeros y me devuelve la suma*)
Definition sumaParejas (p : nat*nat) : nat :=
  (fst p) + (snd p).

Compute sumaParejas (5, 4).

(*Punto 10*)

(*Funcion que recibe una terna de numeros y me devuelve la suma*)
Definition sumaTernas (p : nat*nat*nat) : nat :=
  (cubo (fst (fst p))) + (cubo (snd (fst p))) + (cubo (snd p)).

Compute sumaTernas (1, 2, 3).

(*Punto 11*)

(*Funcion que recibe un numero y me devuelve el doble del numero si es par o n + 1 si es impar*)
Definition punto11 (n : nat) : nat :=
  match (esPar n) with
  | true => n + n
  | false => n + 1
  end.

Compute punto11 6.
Compute punto11 7.

(*Punto 12*)

(*Funcion que recibe una pareja y me una pareja con la suma y el producto*)
Definition punto12 (p : nat*nat) : nat*nat :=
  ((fst p) + (snd p), (fst p) * (snd p)).

Compute punto12 (3, 5).

(*Punto 13*)

Definition punto13 (f : nat -> nat -> nat) (g : nat -> nat) (p : nat*nat) : nat*nat :=
  (g (fst p), f (snd p) (fst p)).

Compute punto13 punto3 cuadrado  (3, 4). 

(*Punto 14*)

Definition punto14 (f : nat -> nat) (p : nat*nat) : nat :=
  match (Nat.leb (snd p) (fst p)) with
  | true => f ((fst p) - (snd p))
  | false => f ((snd p) + 1)
  end.

Compute punto14 (fun x => x) (4, 5).
Compute punto14 (fun x => x) (5, 4).

(*Punto 15*)

Inductive LP : Set := 
  |p : LP
  |q : LP
  |r : LP.






