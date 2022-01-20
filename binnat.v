(** Semántica y verificación 22-1
  
  Números binarios

  Script con defninición de números binarios y sus
  propiedades aditivas básicas. Este script
  fue basado de los cursos de Favio Ezquiel
  Miranda Perea y modificado en ciertos aspectos.
  
  Edición por Luis Felipe Benítez Lluis

  Contenido:
        1 Definiciones básicas 
        2 Lemas de inyectividad de operadores
        3 Lemas de inequidad de operadores
        4 Función sucesor y propiedades de sucesor
        5 Función predecesor y propiedades
        6 Funciones de conversión a representación usal de naturales
        7 Definición de suma en números binarios
        8 Seguridad de suma en nat, inversión de morfismos de representaciones

    Para acceder rápidamente a la sección deseada
    buscar la cadena ">n" donde "n" es el número de
    sección. *)
Require Import Coq.Arith.PeanoNat.
Require Import Arith.
Require Import ArithRing.
Require Import Setoid.
Require Import Omega.


(** >1 Definiciones básicas *)


(* Tido de dato que modela un número binario
    Los constructures U y D toman un natural y representan
    su doble mas 1 y 2 respectivamente. Se toma que los números 
    con D sean de la forma 2x+2 para asegurar unicidad de expresión 
    de 0. *)
Inductive BN :=
  Z: BN (* Cero*)
| U: BN -> BN (* x |-> 2x +1 *)
| D: BN -> BN. (* x |-> 2x +2 *)

Check BN_ind.
Check BN_rec.
Check BN_rect.





(** >2 Lemas de inyectividad de operadores**)
Lemma UInj: forall (a b:BN), U a = U b -> a = b.
Proof.
intros.
inversion H.
trivial.
Qed.

Lemma DInj: forall (a b:BN), D a = D b -> a = b.
Proof.
intros.
inversion H.
trivial.
Qed.
Lemma bnNonZ: forall (b:BN), b <> Z -> exists (c:BN), b = U c \/ b = D c.
Proof.
intros.
destruct b.
intuition.
exists b;left;trivial.
exists b;right;trivial.
Qed.





(** >3 Lemas de inequidad de operadores*)
Lemma ZnotU: forall (a:BN), Z <> U a.
Proof.
intros.
discriminate.
Qed.

Lemma ZnotD: forall (a:BN), Z <> D a.
Proof.
intros.
discriminate.
Qed.

Lemma UnotD: forall (a b:BN), U a <> D b.
Proof.
intros.
discriminate.
Qed.

Lemma DnotU: forall (a b:BN), D a <> U b. 
Proof.
intros.
discriminate.
Qed.

Lemma bnotU : forall (a:BN), U a <> a.
Proof.
intros.
induction a.
(*a = Z*)
intuition.
inversion H.
(*a=U a*)
intuition.
inversion H.
apply IHa in H1.
trivial.
(*a=D a*)
intuition.
inversion H.
Qed.

Lemma bnotD : forall (a:BN), D a <> a.
Proof.
intros.
induction a.
(*a = Z*)
intuition.
inversion H.
(*a=U a*)
intuition.
inversion H.
(*a=D a*)
intuition.
inversion H.
apply IHa in H1.
trivial.
Qed.
Lemma U_not: forall (i j :BN), U i <> U j -> i <> j.
Proof.
intros.
contradict H.
apply f_equal.
trivial.
Qed.

Lemma D_not: forall (i j :BN), D i <> D j -> i <> j.
Proof.
intros.
contradict H.
apply f_equal.
trivial.
Qed.

Lemma UDCase: forall (x:BN), x <> Z -> exists (b:BN), x = U b \/ x = D b.
Proof.
intros.
destruct x.
intuition.
exists x;left;trivial.
exists x;right;trivial.
Qed.

(* Decidibilidad de la igualdad*)
Theorem dec_eq_BN: forall (a b:BN), {a = b} + {a <> b}.
Proof. 
decide equality.
Qed.

(** >4 Función sucesor y propiedades de sucesor*)
Fixpoint sucBN (b:BN) : BN :=
  match b with
      Z => U Z
    | U x => D x (*S(U x) = S(2x + 1) = 2x + 2 = D x*)
    | D x => U (sucBN x) (*S(D x)= S(2x + 2) = S(S(2x + 1)) = S(2x + 1) + 1  *)
                 (* 2(S(x)) + 1 = 2(x+1) + 1 = (2x + 2) + 1 = S(2x + 1) + 1*)  
  end.
  
Lemma suc_not_zero: forall (x:BN), sucBN x <> Z.
Proof.
intros.
destruct x.
simpl;discriminate.
simpl;discriminate.
simpl;discriminate.
Qed.  

Lemma suc_DasucUa: forall (a:BN), D  a =sucBN (U a).
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma suc_Dsuca_sucsucDa: forall (a:BN), D (sucBN a) = sucBN (sucBN (D a)).
Proof.
intros. simpl. reflexivity.
Qed.

Lemma suc_sucUa: forall a:BN,   U (sucBN a)= sucBN (D a).
Proof.
intros.
simpl. reflexivity.
Qed.

Lemma ZnotSucBN: forall (a:BN), Z <> sucBN a.
Proof.
intros.
induction a.
simpl.
discriminate.
simpl.
discriminate.
simpl.
discriminate.
Qed.

Lemma SucBNisUorD: forall (a:BN),exists b:BN, 
  sucBN a = U b \/ sucBN a = D b.
Proof.  
  induction a.
  - simpl. exists Z. left. reflexivity.
  - simpl. exists a. right. reflexivity.
  - destruct IHa. destruct H.
  -- simpl. exists (sucBN a). left. reflexivity.
  -- simpl. exists (sucBN a). left. reflexivity.
Qed.

Lemma notSucBN : forall (a:BN), a <> sucBN a.
Proof.
intros.
destruct a.
simpl; discriminate.
simpl; discriminate.
simpl; discriminate.
Qed.




(** >5 Función predecesor y propiedades*)
(* Para la función predecesor se usa un valor indeterminado dado como 
    un parámetro *)
Parameter (undefBN: BN). 

Fixpoint predBN (b:BN): BN :=
 match b with
  Z => undefBN
 |U Z => Z
 |U x => D (predBN x)
 |D x => U x
 end.

Lemma predBNUD: forall (a:BN), a <> Z -> predBN (U a) = D (predBN a).
Proof.
intros.
destruct a.
contradict H.
trivial.
reflexivity.
reflexivity.
Qed.

Lemma predsucBNinv: forall (a:BN), predBN (sucBN a) = a.
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - pose proof SucBNisUorD as H.
    simpl.
    specialize H with (a:= a).
    destruct H.
    destruct H.
    -- rewrite H. rewrite <-H.
       rewrite IHa. reflexivity.
    -- rewrite H. rewrite <- H.
       rewrite IHa. reflexivity.
Qed.

Lemma sucpredBNinv: forall (a:BN), a <> Z -> sucBN (predBN a) = a.
Proof.
  induction a.
  - intro. contradict H. reflexivity.
  - destruct a.
  -- simpl. intro. reflexivity.
  -- assert (U a <> Z) as H.
     apply not_eq_sym.
     apply ZnotU.
     intro.
     apply IHa in H as H1.
     assert (predBN (U (U a))= D (predBN (U a))) as H2.
     simpl. reflexivity.
     rewrite H2.
     assert (sucBN (D (predBN (U a)))= U (sucBN (predBN (U a)))). simpl. reflexivity.
     rewrite H3.
     rewrite H1.
     reflexivity.
   -- simpl. reflexivity.
   - simpl. reflexivity.
Qed.

(** >E Rellenar este problema. Dificultad 3*)
Lemma SucBNinj: forall (a b : BN), sucBN a = sucBN b -> a = b.
Proof.
Admitted.





(** >6 Funciones de conversión a representación usal de naturales *)

(* Función que transforma números binarios BN a nat*)
Fixpoint toN (b:BN) : nat :=
  match b with 
      Z => 0
    | U x => 2*(toN x) + 1
    | D x => 2*(toN x) + 2
  end.


(* Convierte un natural nat a BN mediate iteraciones de sucesor.
    puede ser algo ineficiente.*)
Fixpoint toBN (n: nat) : BN :=
  match n with
      0 => Z
    | S x => sucBN (toBN x)
  end.

Eval compute in (toN (predBN (toBN 47))).

Eval compute in toN(D(U(U Z))).

Eval compute in toN(sucBN(D(U(U Z)))).

Eval compute in toBN 16.

(* Seguridad de funciones sucesor*)
Lemma toN_sucBN : forall (b : BN), toN(sucBN b) = S(toN b).
Proof.
induction b.
simpl.
trivial.
simpl.
ring.
simpl.
rewrite IHb.
ring.
Qed.

Lemma sucBN_toBN : forall (n : nat), sucBN (toBN n) = toBN (S n).
Proof.
destruct n.
simpl.
trivial.
simpl.
trivial.
Qed.

Lemma inverse_op : forall (n : nat), toN(toBN n) = n.
Proof.
induction n.
simpl.
trivial.
simpl.
rewrite toN_sucBN.
rewrite IHn.
trivial.
Qed.





(** >7 Definición de suma en números binarios*)

Fixpoint plusBN (a b : BN) : BN :=
  match a,b with
    | Z, b => b
    | a, Z  => a
    | U x, U y => D(plusBN x y)
    | D x, U y => U(sucBN (plusBN x y))
    | U x, D y => U(sucBN (plusBN x y))
    | D x, D y => D(sucBN (plusBN x y))                
  end.

Notation "a +_ b" := (plusBN a b) (at level 60). 

Lemma plus_neutro: forall (b:BN), b +_ Z = b.
Proof.
intros.
destruct b.
simpl;trivial.
simpl;trivial.
simpl;trivial.
Qed.

Lemma plus_sucBN_ZU: forall (b : BN),  sucBN (b) = b +_ U Z.
Proof.
  intros.
  induction b.
  - simpl. reflexivity.
  - simpl. rewrite plus_neutro. reflexivity.
  - simpl. rewrite plus_neutro. reflexivity.
Qed.

Lemma plus_sucBN_ZUU: forall (b : BN),  sucBN(sucBN (b)) = b +_ D Z.
Proof.
intros.
induction b.
- simpl. reflexivity.
- simpl. rewrite plus_neutro.
  reflexivity.
- simpl. rewrite plus_neutro.
  reflexivity.
Qed.

Lemma plus_U: forall (b : BN),  sucBN (b +_ b) = U b.
Proof.
intros.
induction b.
simpl.
trivial.
simpl.
rewrite IHb.
trivial.
simpl.
rewrite IHb.
simpl.
trivial.
Qed.

Lemma plus_D: forall (b : BN),  sucBN (sucBN b +_ b) = D b.
Proof.
intros.
induction b.
simpl.
trivial.
simpl.
rewrite plus_U.
trivial.
simpl.
rewrite IHb.
trivial.
Qed.


Lemma plusSuc_l : forall (b c: BN), sucBN (b +_ c) = sucBN b +_ c.
Proof.
  induction b;induction c;try(reflexivity).
  - simpl. 
    specialize IHb with (c:=c).
    rewrite IHb.
    reflexivity.
  - simpl.
    specialize IHb with (c:= c) as H1.
    rewrite H1.
    reflexivity.
Qed.

(** >E Rellenar este problema. Dificultad 2*)
Lemma plusComm: forall (a b:BN), (a +_ b) = (b +_ a).
Proof.
Admitted.

Lemma plusSuc_r : forall (b c: BN), sucBN (b +_ c) = b +_ sucBN c.
Proof.
intros.
rewrite plusComm.
rewrite plusSuc_l.
rewrite plusComm.
reflexivity.
Qed.

Lemma plusBN_Z_Z: forall (x y:BN), x +_ y = Z -> x = Z /\ y = Z.
Proof.
intros.
split.
induction x.
reflexivity.
  - symmetry in H.
  contradict H.
  destruct y.
  simpl.
  apply ZnotU.
  simpl. apply ZnotD with (a:= (x +_ y)).
  simpl. apply ZnotU with (a:= sucBN (x +_ y))  .
- symmetry in H.
  contradict H.
  destruct y.
  simpl.
  apply ZnotD.
  simpl. apply ZnotU with (a:= sucBN (x +_ y)).
  simpl. apply ZnotD with (a:=sucBN(x +_ y) )  .
- induction y.
  reflexivity.
  symmetry in H.
  contradict H.
  destruct x.
  simpl.
  apply ZnotU.
  simpl. apply ZnotD with (a:= (x +_ y)).
  simpl. apply ZnotU with (a:= sucBN (x +_ y))  .
  symmetry in H.
  contradict H.
  destruct x.
  simpl.
  apply ZnotD.
  simpl. apply ZnotU with (a:= sucBN (x +_ y)).
  simpl. apply ZnotD with (a:=sucBN(x +_ y) )  .
Qed.

Lemma plus_a_a : forall (a b:BN), a +_ a = b +_ b -> a = b.
Proof.
intros.
apply (f_equal sucBN) in H.
rewrite plus_U in H.
rewrite plus_U in H.
apply UInj.
trivial.
Qed.

Lemma plus_SucBNa_a : forall (a b:BN), 
  sucBN a +_ a = sucBN b +_ b -> a = b.
Proof.
intros.
rewrite <- plusSuc_l in H.
rewrite <- plusSuc_l in H.
apply SucBNinj in H.
apply (f_equal sucBN) in H.
rewrite plus_U in H.
rewrite plus_U in H.
apply UInj.
trivial.
Qed.





(** >8 Seguridad de suma en nat, inversión de morfismos de representaciones*)
Lemma plusBN_toN : forall (a b : BN), toN(a +_ b) = toN a + toN b.
Proof.
intro.
induction a.
simpl.
trivial.
intros.
destruct b.
simpl.
ring.
simpl.
rewrite IHa.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
destruct b.
simpl.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
Qed.

Lemma plus_toBN:  forall (n m: nat), toBN(n + m) = toBN n +_ toBN m.
Proof.
intros.
induction n.
simpl.
trivial.
simpl.
rewrite IHn.
rewrite <- plusSuc_l.
trivial.
Qed.

(** >E Rellenar este teorema. Dificultad 2*)
Lemma inverse_op_1 : forall (b:nat), toN(toBN b) = b.
Proof.
Admitted.


Lemma inverse_op_2 : forall (b:BN), toBN(toN b) = b.
Proof.
intros.
induction b.
- simpl. reflexivity.
- simpl.
  do 3 rewrite plus_toBN.
  simpl.
  rewrite IHb.
  rewrite plus_neutro.
  rewrite <-plus_sucBN_ZU with (b +_ b).
  rewrite plus_U. 
  reflexivity.
- simpl.  
  rewrite Nat.add_0_r.
  rewrite plus_toBN.
  rewrite plus_toBN.
  rewrite IHb.
  simpl.
  pose proof plus_D (b) .
  rewrite <-H.
  rewrite <-plusSuc_l.
  rewrite plus_sucBN_ZUU.
  reflexivity.
Qed.
